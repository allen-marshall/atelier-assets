//! This module provides the LMDB-based implementation of this crate's generic
//! storage API. Since the generic API is largely based on LMDB in the first
//! place, this implementation should be a thin, inexpensive wrapper.

use bitflags::bitflags;
use lmdb::{Cursor, Transaction};
use std::cmp::Ordering;
use std::convert::{TryFrom, TryInto};
use std::hash::{Hash, Hasher};
use std::path::Path;

/// Error type for the LMDB wrapper.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Error {
    /// Error originating in the wrapped LMDB library.
    LmdbError(lmdb::Error),

    /// Error caused by an unsupported database configuration, detected when
    /// opening a preexisting database.
    PreexistingDbConfigError(DbConfigError),
}

impl From<lmdb::Error> for Error {
    fn from(src: lmdb::Error) -> Self {
        Error::LmdbError(src)
    }
}

/// Error type related to configuration of a storage environment.
///
/// This type is used for conditions that are valid in LMDB itself, but are not
/// supported by the wrapper. (For conditions that are invalid in LMDB,
/// [`lmdb::Error`][lmdb::Error] is generally used instead.)
///
/// [lmdb::Error]: lmdb::Error
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum EnvConfigError {
    /// Error caused by enabling thread-local storage for transactions. This is
    /// disallowed by the wrapper because it would prevent some types from
    /// safely implementing [`Send`][Send].
    ///
    /// [Send]: std::marker::Send
    ThreadLocalStorageEnabled,

    /// Error caused by disabling LMDB's locking mechanisms. This is allowed in
    /// raw LMDB but disallowed by the wrapper for safety reasons.
    LocksDisabled,
}

/// Error type related to configuration of an individual database within a
/// storage environment.
///
/// This type is used for conditions that are valid in LMDB itself, but are not
/// supported by the wrapper. (For conditions that are invalid in LMDB,
/// [`lmdb::Error`][lmdb::Error] is generally used instead.) The most notable
/// example is configuring a database to allow multiple values for the same key
/// (LMDB's `MDB_DUPSORT` flag), which is allowed in LMDB but disallowed by the
/// wrapper.
///
/// [lmdb::Error]: lmdb::Error
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum DbConfigError {
    /// Error caused by enabling duplicate keys in a database.
    DupKeysEnabled,
}

bitflags! {
    /// Environment options.
    pub struct EnvironmentFlags: libc::c_uint {
        /// See [`FIXED_MAP`][FIXED_MAP] in the `lmdb` crate.
        ///
        /// [FIXED_MAP]: lmdb::EnvironmentFlags::FIXED_MAP
        const FIXED_MAP = lmdb_sys::MDB_FIXEDMAP;

        /// See [`NO_SUB_DIR`][NO_SUB_DIR] in the `lmdb` crate.
        ///
        /// [NO_SUB_DIR]: lmdb::EnvironmentFlags::NO_SUB_DIR
        const NO_SUB_DIR = lmdb_sys::MDB_NOSUBDIR;

        /// See [`WRITE_MAP`][WRITE_MAP] in the `lmdb` crate.
        ///
        /// [WRITE_MAP]: lmdb::EnvironmentFlags::WRITE_MAP
        const WRITE_MAP = lmdb_sys::MDB_WRITEMAP;

        /// See [`READ_ONLY`][READ_ONLY] in the `lmdb` crate.
        ///
        /// [READ_ONLY]: lmdb::EnvironmentFlags::READ_ONLY
        const READ_ONLY = lmdb_sys::MDB_RDONLY;

        /// See [`NO_META_SYNC`][NO_META_SYNC] in the `lmdb` crate.
        ///
        /// [NO_META_SYNC]: lmdb::EnvironmentFlags::NO_META_SYNC
        const NO_META_SYNC = lmdb_sys::MDB_NOMETASYNC;

        /// See [`NO_SYNC`][NO_SYNC] in the `lmdb` crate.
        ///
        /// [NO_SYNC]: lmdb::EnvironmentFlags::NO_SYNC
        const NO_SYNC = lmdb_sys::MDB_NOSYNC;

        /// See [`MAP_ASYNC`][MAP_ASYNC] in the `lmdb` crate.
        ///
        /// [MAP_ASYNC]: lmdb::EnvironmentFlags::MAP_ASYNC
        const MAP_ASYNC = lmdb_sys::MDB_MAPASYNC;

        /// See [`NO_READAHEAD`][NO_READAHEAD] in the `lmdb` crate.
        ///
        /// [NO_READAHEAD]: lmdb::EnvironmentFlags::NO_READAHEAD
        const NO_READAHEAD = lmdb_sys::MDB_NORDAHEAD;

        /// See [`NO_MEM_INIT`][NO_MEM_INIT] in the `lmdb` crate.
        ///
        /// [NO_MEM_INIT]: lmdb::EnvironmentFlags::NO_MEM_INIT
        const NO_MEM_INIT = lmdb_sys::MDB_NOMEMINIT;

        // Note: Some flags from the lmdb crate are omitted here because the
        // wrapper either doesn't support them or requires them to always be
        // set.
    }
}

impl Into<lmdb::EnvironmentFlags> for EnvironmentFlags {
    fn into(self) -> lmdb::EnvironmentFlags {
        // All the flags in self::EnvironmentFlags have corresponding flags in
        // lmdb::EnvironmentFlags that use the same bit positions, so most of
        // the flags can be transferred over by just copying the bit pattern.
        let mut output = lmdb::EnvironmentFlags::from_bits(self.bits()).unwrap();

        // Make sure the NO_TLS option is always used. This is necessary in
        // order to ensure the safety of some Send impls in this module.
        output |= lmdb::EnvironmentFlags::NO_TLS;

        output
    }
}

impl TryFrom<lmdb::EnvironmentFlags> for EnvironmentFlags {
    type Error = EnvConfigError;

    fn try_from(value: lmdb::EnvironmentFlags) -> Result<Self, Self::Error> {
        // Check for unsupported settings.
        if value.intersects(lmdb::EnvironmentFlags::NO_LOCK) {
            Err(EnvConfigError::LocksDisabled)
        } else if !value.intersects(lmdb::EnvironmentFlags::NO_TLS) {
            Err(EnvConfigError::ThreadLocalStorageEnabled)
        } else {
            let required_flags = value - lmdb::EnvironmentFlags::NO_TLS;

            // All the flags in self::EnvironmentFlags have corresponding flags
            // in lmdb::EnvironmentFlags that use the same bit positions, so
            // most of the flags can be transferred over by just copying the bit
            // pattern.
            Ok(Self::from_bits(required_flags.bits()).unwrap())
        }
    }
}

/// Configuration data needed to initialize the storage environment.
///
/// # Parameters
/// - `'path`: Lifetime of the held [`Path`][Path] reference that determines
///   where the data is stored on disk.
///
/// [Path]: std::path::Path
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct EnvironmentConfig<'path> {
    // See constructor for documentation of these fields.
    env_flags: EnvironmentFlags,
    max_readers: Option<libc::c_uint>,
    max_dbs: Option<libc::c_uint>,
    map_size: Option<libc::size_t>,
    open_path: &'path Path,
    open_permissions: Option<lmdb_sys::mode_t>,
}

impl<'path> EnvironmentConfig<'path> {
    /// Constructor.
    ///
    /// # Parameters
    /// - `env_flags`: Environment flags.
    /// - `max_readers`: Maximum number of concurrently active read transactions
    ///   that the environment will allow. The default is 126.
    /// - `max_dbs`: Maximum number of named databases that the environment will
    ///   allow. The default is normally very low, so this should be specified
    ///   unless you are just going to use the default unnamed database.
    /// - `map_size`: Maximum size of the storage data, in bytes. This should be
    ///   a multiple of the OS page size. The default is 10485760 bytes.
    /// - `open_path`: Path where the data is stored on disk. If this contains
    ///   the null character, environment initialization will return an error.
    /// - `open_permissions`: File permissions with which to open the database
    ///   file(s). Ignored on Windows. A value of [`None`][None] means the
    ///   default permissions, which are 644 on UNIX.
    ///
    /// [None]: std::option::Option::None
    pub fn new(
        env_flags: EnvironmentFlags,
        max_readers: Option<libc::c_uint>,
        max_dbs: Option<libc::c_uint>,
        map_size: Option<libc::size_t>,
        open_path: &'path Path,
        open_permissions: Option<lmdb_sys::mode_t>,
    ) -> Self {
        Self {
            env_flags,
            max_readers,
            max_dbs,
            map_size,
            open_path,
            open_permissions,
        }
    }

    /// Opens an LMDB environment with the specified configuration.
    fn open(&self) -> Result<lmdb::Environment, Error> {
        let mut env_builder = lmdb::Environment::new();
        env_builder.set_flags(self.env_flags.into());
        if let Some(max_readers) = self.max_readers {
            env_builder.set_max_readers(max_readers);
        }
        if let Some(max_dbs) = self.max_dbs {
            env_builder.set_max_dbs(max_dbs);
        }
        if let Some(map_size) = self.map_size {
            env_builder.set_map_size(map_size);
        }
        if let Some(open_permissions) = self.open_permissions {
            env_builder
                .open_with_permissions(self.open_path, open_permissions)
                .map_err(Into::into)
        } else {
            env_builder.open(self.open_path).map_err(Into::into)
        }
    }
}

bitflags! {
    /// Options for an individual database within a storage environment.
    pub struct DbFlags: libc::c_uint {
        /// See [`REVERSE_KEY`][REVERSE_KEY] in the `lmdb` crate.
        ///
        /// [REVERSE_KEY]: lmdb::DatabaseFlags::REVERSE_KEY
        const REVERSE_KEY = lmdb_sys::MDB_REVERSEKEY;

        /// See [`INTEGER_KEY`][INTEGER_KEY] in the `lmdb` crate.
        ///
        /// [INTEGER_KEY]: lmdb::DatabaseFlags::INTEGER_KEY
        const INTEGER_KEY = lmdb_sys::MDB_INTEGERKEY;

        // Note: Some flags from the lmdb crate are omitted here because the
        // wrapper doesn't support them.
    }
}

impl Into<lmdb::DatabaseFlags> for DbFlags {
    fn into(self) -> lmdb::DatabaseFlags {
        // All the flags in self::DbFlags have corresponding flags in
        // lmdb::DatabaseFlags that use the same bit position, so the flags can
        // be transferred over by just copying the bit pattern.
        lmdb::DatabaseFlags::from_bits(self.bits()).unwrap()
    }
}

impl TryFrom<lmdb::DatabaseFlags> for DbFlags {
    type Error = DbConfigError;

    fn try_from(value: lmdb::DatabaseFlags) -> Result<Self, Self::Error> {
        // Check for unsupported settings.
        if value.intersects(
            lmdb::DatabaseFlags::DUP_SORT
                | lmdb::DatabaseFlags::DUP_FIXED
                | lmdb::DatabaseFlags::INTEGER_DUP
                | lmdb::DatabaseFlags::REVERSE_DUP,
        ) {
            Err(DbConfigError::DupKeysEnabled)
        } else {
            // All the flags in self::DbFlags have corresponding flags in
            // lmdb::DatabaseFlags that use the same bit positions, so the flags
            // can be transferred over by just copying the bit pattern.
            Ok(Self::from_bits(value.bits()).unwrap())
        }
    }
}

/// Checks that a specified set of LMDB database flags are supported by the
/// wrapper. If the flags are not supported, a
/// [`PreexistingDbConfigError`][PreexistingDbConfigError] value is returned.
///
/// [PreexistingDbConfigError]: self::Error::PreexistingDbConfigError
fn check_db_flags(flags: lmdb::DatabaseFlags) -> Result<DbFlags, Error> {
    TryInto::<DbFlags>::try_into(flags).map_err(|err| Error::PreexistingDbConfigError(err))
}

/// Configuration type that can be passed to [`sync`][sync] to control how data
/// is flushed to disk. A value of `true` means that a synchronous flush should
/// be forced regardless of the flags with which the LMDB environment was
/// configured.
///
/// [sync]: crate::Environment::sync
pub type SyncConfig = bool;

/// Statistics about the LMDB environment.
pub type Stat = lmdb::Stat;

/// Database handle.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Database(lmdb::Database);

impl PartialOrd for Database {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        self.0.dbi().partial_cmp(&other.0.dbi())
    }
}

impl Ord for Database {
    fn cmp(&self, other: &Self) -> Ordering {
        self.0.dbi().cmp(&other.0.dbi())
    }
}

impl Hash for Database {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.0.dbi().hash(state)
    }
}

/// Main storage environment type for the LMDB wrapper.
#[derive(Debug)]
pub struct Environment(lmdb::Environment);

impl crate::EnvironmentBasic for Environment {
    type Error = Error;
    type Stat = Stat;
    type Database = Database;
}

impl<'env> crate::Environment<'env, [u8], [u8], [u8]> for Environment {
    type RoTransaction = RoTransaction<'env>;
    type RwTransaction = RwTransaction<'env>;

    fn begin_ro_txn(&'env self) -> Result<Self::RoTransaction, Self::Error>
    where
        Self: 'env,
    {
        Ok(RoTransaction(self.0.begin_ro_txn()?))
    }

    fn begin_rw_txn(&'env self) -> Result<Self::RwTransaction, Self::Error>
    where
        Self: 'env,
    {
        Ok(RwTransaction(self.0.begin_rw_txn()?))
    }
}

impl<'path, 'env, 'dbid>
    crate::EnvironmentExt<
        'env,
        EnvironmentConfig<'path>,
        Option<&'dbid str>,
        DbFlags,
        SyncConfig,
        [u8],
        [u8],
        [u8],
    > for Environment
{
    type ReturnedDbConfig = DbFlags;

    fn new(config: EnvironmentConfig<'path>) -> Result<Self, Self::Error>
    where
        Self: 'env,
    {
        Ok(Self(config.open()?))
    }

    fn open_db(&'env mut self, id: Option<&'dbid str>) -> Result<Self::Database, Self::Error>
    where
        Self: 'env,
    {
        let db = Database(self.0.open_db(id)?);

        // Make sure we aren't opening a preexisting database with an
        // unsupported configuration.
        check_db_flags(self.0.get_db_flags(db.0)?)?;

        Ok(db)
    }

    fn create_db(
        &'env mut self,
        id: Option<&'dbid str>,
        config: DbFlags,
    ) -> Result<Self::Database, Self::Error>
    where
        Self: 'env,
    {
        let db = Database(self.0.create_db(id, config.into())?);

        // Make sure we aren't opening a preexisting database with an
        // unsupported configuration.
        check_db_flags(self.0.get_db_flags(db.0)?)?;

        Ok(db)
    }

    fn db_config(&'env self, db: &Self::Database) -> Result<Self::ReturnedDbConfig, Self::Error>
    where
        Self: 'env,
    {
        check_db_flags(self.0.get_db_flags(db.0)?)
    }

    fn sync(&'env self, config: SyncConfig) -> Result<(), Self::Error>
    where
        Self: 'env,
    {
        self.0.sync(config).map_err(Into::into)
    }

    fn stat(&'env self) -> Result<Self::Stat, Self::Error>
    where
        Self: 'env,
    {
        self.0.stat().map_err(Into::into)
    }
}

/// Read-only transaction type for the LMDB wrapper.
#[derive(Debug)]
pub struct RoTransaction<'env>(lmdb::RoTransaction<'env>);

// This should be safe because we always enforce the use of the NO_TLS
// environment flag, so transactions aren't tied to thread-local storage.
// However, the guarantees provided by NO_TLS aren't strong enough to also
// implement Sync.
unsafe impl<'env> Send for RoTransaction<'env> {}

impl<'env> crate::TransactionBasic for RoTransaction<'env> {
    type Error = Error;
    type Database = Database;
    type ReturnedKey = [u8];
    type ReturnedValue = [u8];
}

impl<'env, 'txn> crate::Transaction<'txn, [u8]> for RoTransaction<'env> {
    type ReturnedDbConfig = DbFlags;
    type ReturnedValueHandle = &'txn [u8];
    type RoCursor = RoCursor<'txn>;

    fn commit(self) -> Result<(), Self::Error>
    where
        Self: 'txn,
    {
        self.0.commit().map_err(Into::into)
    }

    fn get(
        &'txn self,
        db: &Self::Database,
        key: &[u8],
    ) -> Result<Option<Self::ReturnedValueHandle>, Self::Error>
    where
        Self: 'txn,
    {
        let lmdb_result = self.0.get(db.0, &key);
        if lmdb_result == Err(lmdb::Error::NotFound) {
            Ok(None)
        } else {
            lmdb_result.map(|value| Some(value)).map_err(Into::into)
        }
    }

    fn db_config(&'txn self, db: &Self::Database) -> Result<Self::ReturnedDbConfig, Self::Error>
    where
        Self: 'txn,
    {
        check_db_flags(self.0.db_flags(db.0)?)
    }

    fn open_ro_cursor(&'txn self, db: &Self::Database) -> Result<Self::RoCursor, Self::Error>
    where
        Self: 'txn,
    {
        Ok(RoCursor(self.0.open_ro_cursor(db.0)?))
    }
}

impl<'env> crate::ActiveRenewable<InactiveRoTransaction<'env>> for RoTransaction<'env> {
    type Error = Error;

    fn deactivate(self) -> Result<InactiveRoTransaction<'env>, Self::Error> {
        Ok(InactiveRoTransaction(self.0.reset()))
    }
}

/// Inactive read-only transaction type that may be renewed to save allocation
/// overhead.
#[derive(Debug)]
pub struct InactiveRoTransaction<'env>(lmdb::InactiveTransaction<'env>);

// This should be safe because we always enforce the use of the NO_TLS
// environment flag, so transactions aren't tied to thread-local storage.
// However, the guarantees provided by NO_TLS aren't strong enough to also
// implement Sync.
unsafe impl<'env> Send for InactiveRoTransaction<'env> {}

impl<'env> crate::InactiveRenewable<RoTransaction<'env>> for InactiveRoTransaction<'env> {
    type Error = Error;

    fn renew(self) -> Result<RoTransaction<'env>, Self::Error> {
        Ok(RoTransaction(self.0.renew()?))
    }
}

/// Read-write transaction type for the LMDB wrapper.
#[derive(Debug)]
pub struct RwTransaction<'env>(lmdb::RwTransaction<'env>);

// This should be safe because we always enforce the use of the NO_TLS
// environment flag, so transactions aren't tied to thread-local storage.
// However, the guarantees provided by NO_TLS aren't strong enough to also
// implement Sync.
unsafe impl<'env> Send for RwTransaction<'env> {}

impl<'env> crate::TransactionBasic for RwTransaction<'env> {
    type Error = Error;
    type Database = Database;
    type ReturnedKey = [u8];
    type ReturnedValue = [u8];
}

impl<'env, 'txn> crate::Transaction<'txn, [u8]> for RwTransaction<'env> {
    type ReturnedDbConfig = DbFlags;
    type ReturnedValueHandle = &'txn [u8];
    type RoCursor = RoCursor<'txn>;

    fn commit(self) -> Result<(), Self::Error>
    where
        Self: 'txn,
    {
        self.0.commit().map_err(Into::into)
    }

    fn get(
        &'txn self,
        db: &Self::Database,
        key: &[u8],
    ) -> Result<Option<Self::ReturnedValueHandle>, Self::Error>
    where
        Self: 'txn,
    {
        let lmdb_result = self.0.get(db.0, &key);
        if lmdb_result == Err(lmdb::Error::NotFound) {
            Ok(None)
        } else {
            lmdb_result.map(|value| Some(value)).map_err(Into::into)
        }
    }

    fn db_config(&'txn self, db: &Self::Database) -> Result<Self::ReturnedDbConfig, Self::Error>
    where
        Self: 'txn,
    {
        check_db_flags(self.0.db_flags(db.0)?)
    }

    fn open_ro_cursor(&'txn self, db: &Self::Database) -> Result<Self::RoCursor, Self::Error>
    where
        Self: 'txn,
    {
        Ok(RoCursor(self.0.open_ro_cursor(db.0)?))
    }
}

impl<'env, 'txn> crate::ReadWriteTransaction<'txn, [u8], [u8], [u8]> for RwTransaction<'env> {
    type RwCursor = RwCursor<'txn>;
    type Nested = RwTransaction<'txn>;

    fn put(&'txn mut self, db: &Self::Database, key: &[u8], value: &[u8]) -> Result<(), Self::Error>
    where
        Self: 'txn,
    {
        self.0
            .put(db.0, &key, &value, lmdb::WriteFlags::empty())
            .map_err(Into::into)
    }

    fn put_no_overwrite(
        &'txn mut self,
        db: &Self::Database,
        key: &[u8],
        value: &[u8],
    ) -> Result<bool, Self::Error>
    where
        Self: 'txn,
    {
        let put_result = self
            .0
            .put(db.0, &key, &value, lmdb::WriteFlags::NO_OVERWRITE);
        if put_result == Err(lmdb::Error::KeyExist) {
            Ok(false)
        } else {
            put_result.map(|_| true).map_err(Into::into)
        }
    }

    fn del(&'txn mut self, db: &Self::Database, key: &[u8]) -> Result<bool, Self::Error>
    where
        Self: 'txn,
    {
        let del_result = self.0.del(db.0, &key, None);
        if del_result == Err(lmdb::Error::NotFound) {
            Ok(false)
        } else {
            del_result.map(|_| true).map_err(Into::into)
        }
    }

    fn clear_db(&'txn mut self, db: &Self::Database) -> Result<(), Self::Error>
    where
        Self: 'txn,
    {
        self.0.clear_db(db.0).map_err(Into::into)
    }

    fn open_rw_cursor(&'txn mut self, db: &Self::Database) -> Result<Self::RwCursor, Self::Error>
    where
        Self: 'txn,
    {
        Ok(RwCursor(self.0.open_rw_cursor(db.0)?))
    }

    fn begin_nested_txn(&'txn mut self) -> Result<Self::Nested, Self::Error>
    where
        Self: 'txn,
    {
        Ok(RwTransaction(self.0.begin_nested_txn()?))
    }
}

/// Data handle returned by cursor operations.
#[derive(Debug)]
pub struct CursorReturnedDataHandle<'cursor>(&'cursor [u8]);

// This trait impl should be safe, because we only ever construct
// CursorReturnedDataHandles using references that were obtained through LMDB
// cursor operations, and LMDB guarantees that data pointers returned from
// cursor operations remain valid until either the environment is mutated by the
// transaction or the transaction ends.
unsafe impl<'cursor> crate::CursorReturnedDataHandle<'cursor, [u8]>
    for CursorReturnedDataHandle<'cursor>
{
    fn get(&self) -> &'cursor [u8] {
        self.0
    }
}

/// Helper function that performs commonly needed processing on the result of an
/// LMDB cursor read operation. If the cursor read failed with
/// [`lmdb::Error::NotFound`][lmdb::Error::NotFound], the error is replaced with
/// [`Ok`][Ok]`(`[`None`][None]`)`. If a different error occurred, the error is
/// preserved. If the cursor read succeeded, the returned key is unwrapped, and
/// the key-value pair is returned inside [`Ok`][Ok]`(`[`Some`][Some]`)`.
///
/// # Panics
/// Panics if the read operation succeeded but no key data was returned. This
/// function should only be used when key data is expected.
///
/// [lmdb::Error::NotFound]: lmdb::Error::NotFound
/// [Ok]: std::result::Result::Ok
/// [None]: std::option::Option::None
/// [Some]: std::option::Option::Some
fn lmdb_cursor_result_to_kv_pair<'cursor>(
    lmdb_result: Result<(Option<&'cursor [u8]>, &'cursor [u8]), lmdb::Error>,
) -> Result<
    Option<(
        CursorReturnedDataHandle<'cursor>,
        CursorReturnedDataHandle<'cursor>,
    )>,
    Error,
> {
    if lmdb_result == Err(lmdb::Error::NotFound) {
        Ok(None)
    } else {
        lmdb_result
            .map(|(key, value)| {
                Some((
                    CursorReturnedDataHandle(key.unwrap()),
                    CursorReturnedDataHandle(value),
                ))
            })
            .map_err(Into::into)
    }
}

/// Similar to [`lmdb_cursor_result_to_kv_pair`][lmdb_cursor_result_to_kv_pair],
/// except it only returns the value data and doesn't panic if the key data is
/// absent.
///
/// [lmdb_cursor_result_to_kv_pair]: self::lmdb_cursor_result_to_kv_pair
fn lmdb_cursor_result_to_value<'cursor>(
    lmdb_result: Result<(Option<&'cursor [u8]>, &'cursor [u8]), lmdb::Error>,
) -> Result<Option<CursorReturnedDataHandle<'cursor>>, Error> {
    if lmdb_result == Err(lmdb::Error::NotFound) {
        Ok(None)
    } else {
        lmdb_result
            .map(|(_, value)| Some(CursorReturnedDataHandle(value)))
            .map_err(Into::into)
    }
}

/// Read-only cursor type for the LMDB wrapper.
#[derive(Debug)]
pub struct RoCursor<'txn>(lmdb::RoCursor<'txn>);

// This should be safe because we always enforce the use of the NO_TLS
// environment flag, so transactions aren't tied to thread-local storage.
// However, the guarantees provided by NO_TLS aren't strong enough to also
// implement Sync.
unsafe impl<'env> Send for RoCursor<'env> {}

impl<'txn> crate::CursorBasic for RoCursor<'txn> {
    type Error = Error;
    type ReturnedKey = [u8];
    type ReturnedValue = [u8];
}

impl<'txn, 'cursor> crate::Cursor<'cursor, [u8]> for RoCursor<'txn> {
    type ReturnedKeyHandle = CursorReturnedDataHandle<'cursor>;
    type ReturnedValueHandle = CursorReturnedDataHandle<'cursor>;

    fn get(
        &'cursor self,
    ) -> Result<Option<(Self::ReturnedKeyHandle, Self::ReturnedValueHandle)>, Self::Error>
    where
        Self: 'cursor,
    {
        let output =
            lmdb_cursor_result_to_kv_pair(self.0.get(None, None, lmdb_sys::MDB_GET_CURRENT));

        // When using MDB_GET_CURRENT, the LMDB API returns EINVAL if the cursor
        // is in an unpositioned state. In that case, we return Ok(None) instead
        // of the LMDB error.
        if let Err(Error::LmdbError(lmdb::Error::Other(libc::EINVAL))) = output {
            Ok(None)
        } else {
            output
        }
    }

    fn move_to_first(
        &'cursor mut self,
    ) -> Result<Option<(Self::ReturnedKeyHandle, Self::ReturnedValueHandle)>, Self::Error>
    where
        Self: 'cursor,
    {
        lmdb_cursor_result_to_kv_pair(self.0.get(None, None, lmdb_sys::MDB_FIRST))
    }

    fn move_to_last(
        &'cursor mut self,
    ) -> Result<Option<(Self::ReturnedKeyHandle, Self::ReturnedValueHandle)>, Self::Error>
    where
        Self: 'cursor,
    {
        lmdb_cursor_result_to_kv_pair(self.0.get(None, None, lmdb_sys::MDB_LAST))
    }

    fn move_to_next(
        &'cursor mut self,
    ) -> Result<Option<(Self::ReturnedKeyHandle, Self::ReturnedValueHandle)>, Self::Error>
    where
        Self: 'cursor,
    {
        lmdb_cursor_result_to_kv_pair(self.0.get(None, None, lmdb_sys::MDB_NEXT))
    }

    fn move_to_prev(
        &'cursor mut self,
    ) -> Result<Option<(Self::ReturnedKeyHandle, Self::ReturnedValueHandle)>, Self::Error>
    where
        Self: 'cursor,
    {
        lmdb_cursor_result_to_kv_pair(self.0.get(None, None, lmdb_sys::MDB_PREV))
    }

    fn move_to_key(
        &'cursor mut self,
        key: &[u8],
    ) -> Result<Option<Self::ReturnedValueHandle>, Self::Error>
    where
        Self: 'cursor,
    {
        lmdb_cursor_result_to_value(self.0.get(Some(key), None, lmdb_sys::MDB_SET))
    }

    fn move_to_key_and_get_key(
        &'cursor mut self,
        key: &[u8],
    ) -> Result<Option<(Self::ReturnedKeyHandle, Self::ReturnedValueHandle)>, Self::Error>
    where
        Self: 'cursor,
    {
        lmdb_cursor_result_to_kv_pair(self.0.get(Some(key), None, lmdb_sys::MDB_SET_KEY))
    }

    fn move_to_key_or_after(
        &'cursor mut self,
        key: &[u8],
    ) -> Result<Option<(Self::ReturnedKeyHandle, Self::ReturnedValueHandle)>, Self::Error>
    where
        Self: 'cursor,
    {
        lmdb_cursor_result_to_kv_pair(self.0.get(Some(key), None, lmdb_sys::MDB_SET_RANGE))
    }
}

/// Read-write cursor type for the LMDB wrapper.
#[derive(Debug)]
pub struct RwCursor<'txn>(lmdb::RwCursor<'txn>);

// This should be safe because we always enforce the use of the NO_TLS
// environment flag, so transactions aren't tied to thread-local storage.
// However, the guarantees provided by NO_TLS aren't strong enough to also
// implement Sync.
unsafe impl<'env> Send for RwCursor<'env> {}

impl<'txn> crate::CursorBasic for RwCursor<'txn> {
    type Error = Error;
    type ReturnedKey = [u8];
    type ReturnedValue = [u8];
}

impl<'txn, 'cursor> crate::Cursor<'cursor, [u8]> for RwCursor<'txn> {
    type ReturnedKeyHandle = CursorReturnedDataHandle<'cursor>;
    type ReturnedValueHandle = CursorReturnedDataHandle<'cursor>;

    fn get(
        &'cursor self,
    ) -> Result<Option<(Self::ReturnedKeyHandle, Self::ReturnedValueHandle)>, Self::Error>
    where
        Self: 'cursor,
    {
        let output =
            lmdb_cursor_result_to_kv_pair(self.0.get(None, None, lmdb_sys::MDB_GET_CURRENT));

        // When using MDB_GET_CURRENT, the LMDB API returns EINVAL if the cursor
        // is in an unpositioned state. In that case, we return Ok(None) instead
        // of the LMDB error.
        if let Err(Error::LmdbError(lmdb::Error::Other(libc::EINVAL))) = output {
            Ok(None)
        } else {
            output
        }
    }

    fn move_to_first(
        &'cursor mut self,
    ) -> Result<Option<(Self::ReturnedKeyHandle, Self::ReturnedValueHandle)>, Self::Error>
    where
        Self: 'cursor,
    {
        lmdb_cursor_result_to_kv_pair(self.0.get(None, None, lmdb_sys::MDB_FIRST))
    }

    fn move_to_last(
        &'cursor mut self,
    ) -> Result<Option<(Self::ReturnedKeyHandle, Self::ReturnedValueHandle)>, Self::Error>
    where
        Self: 'cursor,
    {
        lmdb_cursor_result_to_kv_pair(self.0.get(None, None, lmdb_sys::MDB_LAST))
    }

    fn move_to_next(
        &'cursor mut self,
    ) -> Result<Option<(Self::ReturnedKeyHandle, Self::ReturnedValueHandle)>, Self::Error>
    where
        Self: 'cursor,
    {
        lmdb_cursor_result_to_kv_pair(self.0.get(None, None, lmdb_sys::MDB_NEXT))
    }

    fn move_to_prev(
        &'cursor mut self,
    ) -> Result<Option<(Self::ReturnedKeyHandle, Self::ReturnedValueHandle)>, Self::Error>
    where
        Self: 'cursor,
    {
        lmdb_cursor_result_to_kv_pair(self.0.get(None, None, lmdb_sys::MDB_PREV))
    }

    fn move_to_key(
        &'cursor mut self,
        key: &[u8],
    ) -> Result<Option<Self::ReturnedValueHandle>, Self::Error>
    where
        Self: 'cursor,
    {
        lmdb_cursor_result_to_value(self.0.get(Some(key), None, lmdb_sys::MDB_SET))
    }

    fn move_to_key_and_get_key(
        &'cursor mut self,
        key: &[u8],
    ) -> Result<Option<(Self::ReturnedKeyHandle, Self::ReturnedValueHandle)>, Self::Error>
    where
        Self: 'cursor,
    {
        lmdb_cursor_result_to_kv_pair(self.0.get(Some(key), None, lmdb_sys::MDB_SET_KEY))
    }

    fn move_to_key_or_after(
        &'cursor mut self,
        key: &[u8],
    ) -> Result<Option<(Self::ReturnedKeyHandle, Self::ReturnedValueHandle)>, Self::Error>
    where
        Self: 'cursor,
    {
        lmdb_cursor_result_to_kv_pair(self.0.get(Some(key), None, lmdb_sys::MDB_SET_RANGE))
    }
}

impl<'txn, 'cursor> crate::ReadWriteCursor<'cursor, [u8], [u8], [u8]> for RwCursor<'txn> {
    fn put_and_move_to_key(&'cursor mut self, key: &[u8], value: &[u8]) -> Result<(), Self::Error>
    where
        Self: 'cursor,
    {
        self.0
            .put(&key, &value, lmdb::WriteFlags::empty())
            .map_err(Into::into)
    }

    fn put_no_overwrite_and_move_to_key(
        &'cursor mut self,
        key: &[u8],
        value: &[u8],
    ) -> Result<bool, Self::Error>
    where
        Self: 'cursor,
    {
        let lmdb_result = self.0.put(&key, &value, lmdb::WriteFlags::NO_OVERWRITE);
        if lmdb_result == Err(lmdb::Error::KeyExist) {
            Ok(false)
        } else {
            lmdb_result.map(|_| true).map_err(Into::into)
        }
    }

    fn del(&'cursor mut self) -> Result<bool, Self::Error>
    where
        Self: 'cursor,
    {
        let lmdb_result = self.0.del(lmdb::WriteFlags::empty());
        if lmdb_result == Err(lmdb::Error::NotFound) {
            Ok(false)
        } else {
            lmdb_result.map(|_| true).map_err(Into::into)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use tempfile::tempdir;

    /// Basic test that performs several operations and makes sure they don't
    /// return errors except when expected.
    #[test]
    fn basic_error_test() {
        let temp_dir = tempdir().unwrap();
        let env_cfg = EnvironmentConfig::new(
            EnvironmentFlags::empty(),
            None,
            Some(10),
            None,
            temp_dir.path(),
            None,
        );
        let db_cfg = DbFlags::empty();
        crate::test_util::binary_static_env::basic_error_test::<Environment, _, _, _>(
            env_cfg, db_cfg,
        );
    }

    /// Basic test that creates an empty storage environment, writes some data
    /// to it, then makes sure it can read the data back.
    #[test]
    fn basic_read_write_test() {
        let temp_dir = tempdir().unwrap();
        let mut env: Environment = crate::EnvironmentExt::new(EnvironmentConfig::new(
            EnvironmentFlags::empty(),
            None,
            Some(10),
            None,
            temp_dir.path(),
            None,
        ))
        .unwrap();
        crate::test_util::binary_static_env::basic_read_write_test(&mut env, DbFlags::empty());
    }
}
