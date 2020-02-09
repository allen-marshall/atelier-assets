//! This module provides the LMDB-based implementation of this crate's generic
//! storage API. Since the generic API is largely based on LMDB in the first
//! place, this implementation should be a thin, inexpensive wrapper.

use lmdb::{Cursor, Transaction};
use std::path::Path;

/// Error type for the LMDB wrapper.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Error {
    /// Error originating in the wrapped LMDB library.
    LmdbError(lmdb::Error),

    /// Error caused by an invalid or unsupported database configuration.
    DbConfigError(DbConfigError),
}

impl From<lmdb::Error> for Error {
    fn from(src: lmdb::Error) -> Self {
        Error::LmdbError(src)
    }
}

impl From<DbConfigError> for Error {
    fn from(src: DbConfigError) -> Self {
        Error::DbConfigError(src)
    }
}

/// Error type related to configuration of an individual database within an
/// environment.
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
    /// Indicates that the code using the wrapper tried to configure a database
    /// with support for duplicate keys. (This is allowed in LMDB but not
    /// supported by the wrapper.)
    DupKeysSpecified,

    /// Indicates that, when opening a preexisting database, the wrapper found
    /// that the database had been configured with support for duplicate keys.
    DupKeysDetected,
}

/// Configuration data needed to initialize the storage environment.
///
/// # Parameters
/// - `'envb`: Lifetime of the held
///   [`lmdb::EnvironmentBuilder`][lmdb::EnvironmentBuilder] reference that
///   defines most of the LMDB configuration options.
/// - `'path`: Lifetime of the held [`Path`][Path] reference that determines
///   where the data is stored on disk.
///
/// [lmdb::EnvironmentBuilder]: lmdb::EnvironmentBuilder
/// [Path]: std::path::Path
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct EnvironmentConfig<'envb, 'path> {
    // See constructor for documentation of these fields.
    env_builder: &'envb lmdb::EnvironmentBuilder,
    open_path: &'path Path,
    open_permissions: Option<lmdb_sys::mode_t>,
}

impl<'envb, 'path> EnvironmentConfig<'envb, 'path> {
    /// Constructor.
    ///
    /// # Parameters
    /// - `env_builder`: LMDB environment builder. Most of the configuration
    ///   options are stored here.
    /// - `open_path`: Path where the data is stored on disk. If this contains
    ///   the null character, environment initialization will return an error.
    /// - `open_permissions`: File permissions with which to open the database
    ///   file(s). Ignored on Windows. A value of [`None`][None] means the
    ///   default permissions, which are 644 on UNIX.
    ///
    /// [None]: std::option::Option::None
    pub fn new(
        env_builder: &'envb lmdb::EnvironmentBuilder,
        open_path: &'path Path,
        open_permissions: Option<lmdb_sys::mode_t>,
    ) -> Self {
        Self {
            env_builder,
            open_path,
            open_permissions,
        }
    }

    /// Opens an LMDB environment with the specified configuration.
    fn open(&self) -> Result<lmdb::Environment, Error> {
        if let Some(open_permissions) = self.open_permissions {
            self.env_builder
                .open_with_permissions(self.open_path, open_permissions)
                .map_err(Into::into)
        } else {
            self.env_builder.open(self.open_path).map_err(Into::into)
        }
    }
}

/// Configuration data for an individual database within an environment.
pub type DbConfig = lmdb::DatabaseFlags;

/// Configuration type that can be passed to [`sync`][sync] to control how data
/// is flushed to disk. A value of `true` means that a synchronous flush should
/// be forced regardless of the flags with which the LMDB environment was
/// configured.
///
/// [sync]: crate::Environment::sync
pub type SyncConfig = bool;

/// Handle to an individual database within an environment.
pub type Database = lmdb::Database;

/// Statistics about the LMDB environment.
pub type Stat = lmdb::Stat;

/// Main storage environment type for the LMDB wrapper.
#[derive(Debug)]
pub struct Environment {
    /// Wrapped LMDB environment.
    env: lmdb::Environment,
}

/// Checks if a database configuration has duplicate keys enabled.
fn db_config_allows_dup_keys(config: DbConfig) -> bool {
    config.intersects(
        lmdb::DatabaseFlags::DUP_SORT
            | lmdb::DatabaseFlags::DUP_FIXED
            | lmdb::DatabaseFlags::INTEGER_DUP
            | lmdb::DatabaseFlags::REVERSE_DUP,
    )
}

impl<'env, 'cfg, 'envb, 'path, 'dbid, 'kq, 'kp, 'vp, KQ, KP, VP>
    crate::Environment<
        'env,
        &'cfg EnvironmentConfig<'envb, 'path>,
        Option<&'dbid str>,
        DbConfig,
        SyncConfig,
        &'kq KQ,
        &'kp KP,
        &'vp VP,
    > for Environment
where
    KQ: AsRef<[u8]>,
    KP: AsRef<[u8]>,
    VP: AsRef<[u8]>,
{
    type Error = Error;
    type Stat = Stat;
    type Database = Database;
    type DbConfig = DbConfig;
    type RoTransaction = RoTransaction<'env>;
    type RwTransaction = RwTransaction<'env>;

    fn new(config: &'cfg EnvironmentConfig<'envb, 'path>) -> Result<Self, Self::Error>
    where
        Self: 'env,
    {
        Ok(Self {
            env: config.open()?,
        })
    }

    fn open_db(&'env self, id: Option<&'dbid str>) -> Result<Self::Database, Self::Error>
    where
        Self: 'env,
    {
        let db = self.env.open_db(id)?;

        // Make sure we aren't opening a preexisting database with an
        // unsupported configuration.
        if db_config_allows_dup_keys(self.env.get_db_flags(db)?) {
            Err(DbConfigError::DupKeysDetected.into())
        } else {
            Ok(db)
        }
    }

    fn create_db(
        &'env self,
        id: Option<&'dbid str>,
        config: DbConfig,
    ) -> Result<Self::Database, Self::Error>
    where
        Self: 'env,
    {
        // Make sure the requested configuration is supported.
        if db_config_allows_dup_keys(config) {
            Err(DbConfigError::DupKeysSpecified.into())
        } else {
            self.env.create_db(id, config).map_err(Into::into)
        }
    }

    fn db_config(&'env self, db: Self::Database) -> Result<Self::DbConfig, Self::Error>
    where
        Self: 'env,
    {
        self.env.get_db_flags(db).map_err(Into::into)
    }

    fn begin_ro_txn(&'env self) -> Result<Self::RoTransaction, Self::Error>
    where
        Self: 'env,
    {
        Ok(RoTransaction {
            txn: self.env.begin_ro_txn()?,
        })
    }

    fn begin_rw_txn(&'env self) -> Result<Self::RwTransaction, Self::Error>
    where
        Self: 'env,
    {
        Ok(RwTransaction {
            txn: self.env.begin_rw_txn()?,
        })
    }

    fn sync(&'env self, config: SyncConfig) -> Result<(), Self::Error>
    where
        Self: 'env,
    {
        self.env.sync(config).map_err(Into::into)
    }

    fn stat(&'env self) -> Result<Self::Stat, Self::Error>
    where
        Self: 'env,
    {
        self.env.stat().map_err(Into::into)
    }
}

/// Read-only transaction type for the LMDB wrapper.
#[derive(Debug)]
pub struct RoTransaction<'env> {
    /// Wrapped LMDB transaction.
    txn: lmdb::RoTransaction<'env>,
}

impl<'env, 'txn, 'kq, KQ> crate::Transaction<'txn, &'kq KQ> for RoTransaction<'env>
where
    KQ: AsRef<[u8]>,
{
    type Error = Error;
    type Database = Database;
    type DbConfig = DbConfig;
    type ReturnedValue = &'txn [u8];
    type RoCursor = RoCursor<'txn>;

    fn commit(self) -> Result<(), Self::Error>
    where
        Self: 'txn,
    {
        self.txn.commit().map_err(Into::into)
    }

    fn get(
        &'txn self,
        db: Self::Database,
        key: &'kq KQ,
    ) -> Result<Option<Self::ReturnedValue>, Self::Error>
    where
        Self: 'txn,
    {
        let lmdb_result = self.txn.get(db, key);
        if lmdb_result == Err(lmdb::Error::NotFound) {
            Ok(None)
        } else {
            lmdb_result.map(|value| Some(value)).map_err(Into::into)
        }
    }

    fn open_ro_cursor(&'txn self, db: Self::Database) -> Result<Self::RoCursor, Self::Error>
    where
        Self: 'txn,
    {
        Ok(RoCursor {
            cursor: self.txn.open_ro_cursor(db)?,
        })
    }

    fn db_config(&'txn self, db: Self::Database) -> Result<Self::DbConfig, Self::Error>
    where
        Self: 'txn,
    {
        self.txn.db_flags(db).map_err(Into::into)
    }
}

impl<'env> crate::ActiveRenewable<InactiveTransaction<'env>> for RoTransaction<'env> {
    type Error = Error;

    fn deactivate(self) -> Result<InactiveTransaction<'env>, Self::Error> {
        Ok(InactiveTransaction {
            txn: self.txn.reset(),
        })
    }
}

/// Inactive transaction type that may be renewed to save allocation overhead.
#[derive(Debug)]
pub struct InactiveTransaction<'env> {
    /// Wrapped LMDB transaction.
    txn: lmdb::InactiveTransaction<'env>,
}

impl<'env> crate::InactiveRenewable<RoTransaction<'env>> for InactiveTransaction<'env> {
    type Error = Error;

    fn renew(self) -> Result<RoTransaction<'env>, Self::Error> {
        Ok(RoTransaction {
            txn: self.txn.renew()?,
        })
    }
}

/// Read-write transaction type for the LMDB wrapper.
#[derive(Debug)]
pub struct RwTransaction<'env> {
    /// Wrapped LMDB transaction.
    txn: lmdb::RwTransaction<'env>,
}

impl<'env, 'txn, 'kq, KQ> crate::Transaction<'txn, &'kq KQ> for RwTransaction<'env>
where
    KQ: AsRef<[u8]>,
{
    type Error = Error;
    type Database = Database;
    type DbConfig = DbConfig;
    type ReturnedValue = &'txn [u8];
    type RoCursor = RoCursor<'txn>;

    fn commit(self) -> Result<(), Self::Error>
    where
        Self: 'txn,
    {
        self.txn.commit().map_err(Into::into)
    }

    fn get(
        &'txn self,
        db: Self::Database,
        key: &'kq KQ,
    ) -> Result<Option<Self::ReturnedValue>, Self::Error>
    where
        Self: 'txn,
    {
        let lmdb_result = self.txn.get(db, key);
        if lmdb_result == Err(lmdb::Error::NotFound) {
            Ok(None)
        } else {
            lmdb_result.map(|value| Some(value)).map_err(Into::into)
        }
    }

    fn open_ro_cursor(&'txn self, db: Self::Database) -> Result<Self::RoCursor, Self::Error>
    where
        Self: 'txn,
    {
        Ok(RoCursor {
            cursor: self.txn.open_ro_cursor(db)?,
        })
    }

    fn db_config(&'txn self, db: Self::Database) -> Result<Self::DbConfig, Self::Error>
    where
        Self: 'txn,
    {
        self.txn.db_flags(db).map_err(Into::into)
    }
}

impl<'env, 'txn, 'kq, 'kp, 'vp, KQ, KP, VP> crate::WriteTransaction<'txn, &'kq KQ, &'kp KP, &'vp VP>
    for RwTransaction<'env>
where
    KQ: AsRef<[u8]>,
    KP: AsRef<[u8]>,
    VP: AsRef<[u8]>,
{
    type RwCursor = RwCursor<'txn>;

    fn put(
        &'txn mut self,
        db: Self::Database,
        key: &'kp KP,
        value: &'vp VP,
    ) -> Result<(), Self::Error>
    where
        Self: 'txn,
    {
        self.txn
            .put(db, key, value, lmdb::WriteFlags::empty())
            .map_err(Into::into)
    }

    fn put_no_overwrite(
        &'txn mut self,
        db: Self::Database,
        key: &'kp KP,
        value: &'vp VP,
    ) -> Result<bool, Self::Error>
    where
        Self: 'txn,
    {
        let put_result = self.txn.put(db, key, value, lmdb::WriteFlags::NO_OVERWRITE);
        if put_result == Err(lmdb::Error::KeyExist) {
            Ok(false)
        } else {
            put_result.map(|_| true).map_err(Into::into)
        }
    }

    fn del(&'txn mut self, db: Self::Database, key: &'kq KQ) -> Result<bool, Self::Error>
    where
        Self: 'txn,
    {
        let del_result = self.txn.del(db, key, None);
        if del_result == Err(lmdb::Error::NotFound) {
            Ok(false)
        } else {
            del_result.map(|_| true).map_err(Into::into)
        }
    }

    fn clear_db(&'txn mut self, db: Self::Database) -> Result<(), Self::Error>
    where
        Self: 'txn,
    {
        self.txn.clear_db(db).map_err(Into::into)
    }

    fn open_rw_cursor(&'txn mut self, db: Self::Database) -> Result<Self::RwCursor, Self::Error>
    where
        Self: 'txn,
    {
        Ok(RwCursor {
            cursor: self.txn.open_rw_cursor(db)?,
        })
    }
}

impl<'env, 'txn, 'kq, KQ> crate::NestableTransaction<'txn, &'kq KQ> for RwTransaction<'env>
where
    KQ: AsRef<[u8]>,
{
    type Nested = RwTransaction<'txn>;

    fn begin_nested_txn(&'txn mut self) -> Result<Self::Nested, Self::Error>
    where
        Self: 'txn,
    {
        Ok(RwTransaction {
            txn: self.txn.begin_nested_txn()?,
        })
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
fn lmdb_cursor_result_to_kv_pair<'k, 'v>(
    lmdb_result: Result<(Option<&'k [u8]>, &'v [u8]), lmdb::Error>,
) -> Result<Option<(&'k [u8], &'v [u8])>, Error> {
    if lmdb_result == Err(lmdb::Error::NotFound) {
        Ok(None)
    } else {
        lmdb_result
            .map(|(key, value)| Some((key.unwrap(), value)))
            .map_err(Into::into)
    }
}

/// Similar to [`lmdb_cursor_result_to_kv_pair`], except it only returns the
/// value data and doesn't panic if the key data is absent.
///
/// [lmdb_cursor_result_to_kv_pair]: self::lmdb_cursor_result_to_kv_pair
fn lmdb_cursor_result_to_value<'k, 'v>(
    lmdb_result: Result<(Option<&'k [u8]>, &'v [u8]), lmdb::Error>,
) -> Result<Option<&'v [u8]>, Error> {
    if lmdb_result == Err(lmdb::Error::NotFound) {
        Ok(None)
    } else {
        lmdb_result
            .map(|(_, value)| Some(value))
            .map_err(Into::into)
    }
}

/// Read-only cursor type for the LMDB wrapper.
#[derive(Debug)]
pub struct RoCursor<'txn> {
    /// Wrapped LMDB cursor.
    cursor: lmdb::RoCursor<'txn>,
}

impl<'txn, 'cursor, 'kq, KQ> crate::Cursor<'cursor, &'kq KQ> for RoCursor<'txn>
where
    KQ: AsRef<[u8]>,
{
    type Error = Error;
    type ReturnedKey = &'txn [u8];
    type ReturnedValue = &'txn [u8];

    fn get(&'cursor self) -> Result<Option<(Self::ReturnedKey, Self::ReturnedValue)>, Self::Error>
    where
        Self: 'cursor,
    {
        lmdb_cursor_result_to_kv_pair(self.cursor.get(None, None, lmdb_sys::MDB_GET_CURRENT))
    }

    fn move_to_first(
        &'cursor mut self,
    ) -> Result<Option<(Self::ReturnedKey, Self::ReturnedValue)>, Self::Error>
    where
        Self: 'cursor,
    {
        lmdb_cursor_result_to_kv_pair(self.cursor.get(None, None, lmdb_sys::MDB_FIRST))
    }

    fn move_to_last(
        &'cursor mut self,
    ) -> Result<Option<(Self::ReturnedKey, Self::ReturnedValue)>, Self::Error>
    where
        Self: 'cursor,
    {
        lmdb_cursor_result_to_kv_pair(self.cursor.get(None, None, lmdb_sys::MDB_LAST))
    }

    fn move_to_next(
        &'cursor mut self,
    ) -> Result<Option<(Self::ReturnedKey, Self::ReturnedValue)>, Self::Error>
    where
        Self: 'cursor,
    {
        lmdb_cursor_result_to_kv_pair(self.cursor.get(None, None, lmdb_sys::MDB_NEXT))
    }

    fn move_to_prev(
        &'cursor mut self,
    ) -> Result<Option<(Self::ReturnedKey, Self::ReturnedValue)>, Self::Error>
    where
        Self: 'cursor,
    {
        lmdb_cursor_result_to_kv_pair(self.cursor.get(None, None, lmdb_sys::MDB_PREV))
    }

    fn move_to_key(
        &'cursor mut self,
        key: &'kq KQ,
    ) -> Result<Option<Self::ReturnedValue>, Self::Error>
    where
        Self: 'cursor,
    {
        lmdb_cursor_result_to_value(self.cursor.get(Some(key.as_ref()), None, lmdb_sys::MDB_SET))
    }

    fn move_to_key_and_get_key(
        &'cursor mut self,
        key: &'kq KQ,
    ) -> Result<Option<(Self::ReturnedKey, Self::ReturnedValue)>, Self::Error>
    where
        Self: 'cursor,
    {
        lmdb_cursor_result_to_kv_pair(self.cursor.get(
            Some(key.as_ref()),
            None,
            lmdb_sys::MDB_SET_KEY,
        ))
    }

    fn move_to_key_or_after(
        &'cursor mut self,
        key: &'kq KQ,
    ) -> Result<Option<(Self::ReturnedKey, Self::ReturnedValue)>, Self::Error>
    where
        Self: 'cursor,
    {
        lmdb_cursor_result_to_kv_pair(self.cursor.get(
            Some(key.as_ref()),
            None,
            lmdb_sys::MDB_SET_RANGE,
        ))
    }
}

/// Read-write cursor type for the LMDB wrapper.
#[derive(Debug)]
pub struct RwCursor<'txn> {
    /// Wrapped LMDB cursor.
    cursor: lmdb::RwCursor<'txn>,
}

impl<'txn, 'cursor, 'kq, KQ> crate::Cursor<'cursor, &'kq KQ> for RwCursor<'txn>
where
    KQ: AsRef<[u8]>,
{
    type Error = Error;
    type ReturnedKey = &'txn [u8];
    type ReturnedValue = &'txn [u8];

    fn get(&'cursor self) -> Result<Option<(Self::ReturnedKey, Self::ReturnedValue)>, Self::Error>
    where
        Self: 'cursor,
    {
        lmdb_cursor_result_to_kv_pair(self.cursor.get(None, None, lmdb_sys::MDB_GET_CURRENT))
    }

    fn move_to_first(
        &'cursor mut self,
    ) -> Result<Option<(Self::ReturnedKey, Self::ReturnedValue)>, Self::Error>
    where
        Self: 'cursor,
    {
        lmdb_cursor_result_to_kv_pair(self.cursor.get(None, None, lmdb_sys::MDB_FIRST))
    }

    fn move_to_last(
        &'cursor mut self,
    ) -> Result<Option<(Self::ReturnedKey, Self::ReturnedValue)>, Self::Error>
    where
        Self: 'cursor,
    {
        lmdb_cursor_result_to_kv_pair(self.cursor.get(None, None, lmdb_sys::MDB_LAST))
    }

    fn move_to_next(
        &'cursor mut self,
    ) -> Result<Option<(Self::ReturnedKey, Self::ReturnedValue)>, Self::Error>
    where
        Self: 'cursor,
    {
        lmdb_cursor_result_to_kv_pair(self.cursor.get(None, None, lmdb_sys::MDB_NEXT))
    }

    fn move_to_prev(
        &'cursor mut self,
    ) -> Result<Option<(Self::ReturnedKey, Self::ReturnedValue)>, Self::Error>
    where
        Self: 'cursor,
    {
        lmdb_cursor_result_to_kv_pair(self.cursor.get(None, None, lmdb_sys::MDB_PREV))
    }

    fn move_to_key(
        &'cursor mut self,
        key: &'kq KQ,
    ) -> Result<Option<Self::ReturnedValue>, Self::Error>
    where
        Self: 'cursor,
    {
        lmdb_cursor_result_to_value(self.cursor.get(Some(key.as_ref()), None, lmdb_sys::MDB_SET))
    }

    fn move_to_key_and_get_key(
        &'cursor mut self,
        key: &'kq KQ,
    ) -> Result<Option<(Self::ReturnedKey, Self::ReturnedValue)>, Self::Error>
    where
        Self: 'cursor,
    {
        lmdb_cursor_result_to_kv_pair(self.cursor.get(
            Some(key.as_ref()),
            None,
            lmdb_sys::MDB_SET_KEY,
        ))
    }

    fn move_to_key_or_after(
        &'cursor mut self,
        key: &'kq KQ,
    ) -> Result<Option<(Self::ReturnedKey, Self::ReturnedValue)>, Self::Error>
    where
        Self: 'cursor,
    {
        lmdb_cursor_result_to_kv_pair(self.cursor.get(
            Some(key.as_ref()),
            None,
            lmdb_sys::MDB_SET_RANGE,
        ))
    }
}

impl<'txn, 'cursor, 'kq, 'kp, 'vp, KQ, KP, VP>
    crate::WriteCursor<'cursor, &'kq KQ, &'kp KP, &'vp VP> for RwCursor<'txn>
where
    KQ: 'kq + AsRef<[u8]>,
    KP: 'kp + AsRef<[u8]>,
    VP: 'vp + AsRef<[u8]>,
{
    fn put(&'cursor mut self, value: &'vp VP) -> Result<bool, Self::Error>
    where
        Self: 'cursor,
    {
        let key = <Self as crate::Cursor<&'kq KQ>>::get(self)?;
        if let Some((key, _)) = key {
            self.cursor
                .put(&key, value, lmdb::WriteFlags::CURRENT)
                .map(|_| true)
                .map_err(Into::into)
        } else {
            Ok(false)
        }
    }

    fn put_and_move_to_key(
        &'cursor mut self,
        key: &'kp KP,
        value: &'vp VP,
    ) -> Result<(), Self::Error>
    where
        Self: 'cursor,
    {
        self.cursor
            .put(key, value, lmdb::WriteFlags::empty())
            .map_err(Into::into)
    }

    fn put_no_overwrite_and_move_to_key(
        &'cursor mut self,
        key: &'kp KP,
        value: &'vp VP,
    ) -> Result<bool, Self::Error>
    where
        Self: 'cursor,
    {
        let lmdb_result = self.cursor.put(key, value, lmdb::WriteFlags::NO_OVERWRITE);
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
        let lmdb_result = self.cursor.del(lmdb::WriteFlags::empty());
        if lmdb_result == Err(lmdb::Error::NotFound) {
            Ok(false)
        } else {
            lmdb_result.map(|_| true).map_err(Into::into)
        }
    }
}
