//! This module provides the LMDB-based implementation of this crate's generic
//! storage API. Since the generic API is largely based on LMDB in the first
//! place, this implementation should be a thin, inexpensive wrapper.

use lmdb::{Cursor, Transaction};
use std::cmp::Ordering;
use std::hash::{Hash, Hasher};
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
    /// with support for duplicate keys.
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

/// Checks if a database configuration has duplicate keys enabled.
fn db_config_allows_dup_keys(config: DbConfig) -> bool {
    config.intersects(
        lmdb::DatabaseFlags::DUP_SORT
            | lmdb::DatabaseFlags::DUP_FIXED
            | lmdb::DatabaseFlags::INTEGER_DUP
            | lmdb::DatabaseFlags::REVERSE_DUP,
    )
}

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

impl<'cfg, 'envb, 'path, 'env, 'dbid>
    crate::EnvironmentExt<
        'env,
        &'cfg EnvironmentConfig<'envb, 'path>,
        Option<&'dbid str>,
        DbConfig,
        SyncConfig,
        [u8],
        [u8],
        [u8],
    > for Environment
{
    type ReturnedDbConfig = DbConfig;

    fn new(config: &'cfg EnvironmentConfig<'envb, 'path>) -> Result<Self, Self::Error>
    where
        Self: 'env,
    {
        Ok(Self(config.open()?))
    }

    fn open_db(&'env mut self, id: Option<&'dbid str>) -> Result<Self::Database, Self::Error>
    where
        Self: 'env,
    {
        let db = self.0.open_db(id)?;

        // Make sure we aren't opening a preexisting database with an
        // unsupported configuration.
        if db_config_allows_dup_keys(self.0.get_db_flags(db)?) {
            Err(DbConfigError::DupKeysDetected.into())
        } else {
            Ok(Database(db))
        }
    }

    fn create_db(
        &'env mut self,
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
            let db = self.0.create_db(id, config)?;

            // Make sure we aren't opening a preexisting database with an
            // unsupported configuration.
            if db_config_allows_dup_keys(self.0.get_db_flags(db)?) {
                Err(DbConfigError::DupKeysDetected.into())
            } else {
                Ok(Database(db))
            }
        }
    }

    fn db_config(&'env self, db: &Self::Database) -> Result<Self::ReturnedDbConfig, Self::Error>
    where
        Self: 'env,
    {
        self.0.get_db_flags(db.0).map_err(Into::into)
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

impl<'env> crate::TransactionBasic for RoTransaction<'env> {
    type Error = Error;
    type Database = Database;
    type ReturnedKey = [u8];
    type ReturnedValue = [u8];
}

impl<'env, 'txn> crate::Transaction<'txn, [u8]> for RoTransaction<'env> {
    type ReturnedDbConfig = DbConfig;
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
        self.0.db_flags(db.0).map_err(Into::into)
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

impl<'env> crate::InactiveRenewable<RoTransaction<'env>> for InactiveRoTransaction<'env> {
    type Error = Error;

    fn renew(self) -> Result<RoTransaction<'env>, Self::Error> {
        Ok(RoTransaction(self.0.renew()?))
    }
}

/// Read-write transaction type for the LMDB wrapper.
#[derive(Debug)]
pub struct RwTransaction<'env>(lmdb::RwTransaction<'env>);

impl<'env> crate::TransactionBasic for RwTransaction<'env> {
    type Error = Error;
    type Database = Database;
    type ReturnedKey = [u8];
    type ReturnedValue = [u8];
}

impl<'env, 'txn> crate::Transaction<'txn, [u8]> for RwTransaction<'env> {
    type ReturnedDbConfig = DbConfig;
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
        self.0.db_flags(db.0).map_err(Into::into)
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
        lmdb_cursor_result_to_kv_pair(self.0.get(None, None, lmdb_sys::MDB_GET_CURRENT))
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
        lmdb_cursor_result_to_kv_pair(self.0.get(None, None, lmdb_sys::MDB_GET_CURRENT))
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
    use tempfile::{tempdir, TempDir};

    /// Creates a new empty LMDB storage environment in a temporary directory,
    /// using the specified configuration. The returned handle to the temporary
    /// directory should be kept alive as long as the environment is in use, as
    /// dropping it may delete the temporary directory.
    ///
    /// # Panics
    /// Panics if the storage environment returns an unexpected error.
    fn make_empty_env(env_builder: &lmdb::EnvironmentBuilder) -> (Environment, TempDir) {
        let temp_dir = tempdir().unwrap();
        let env = crate::EnvironmentExt::new(&EnvironmentConfig::new(
            &env_builder,
            temp_dir.path(),
            None,
        ))
        .unwrap();
        (env, temp_dir)
    }

    /// Basic test that creates an empty storage environment, writes some data
    /// to it, then makes sure it can read the data back.
    #[test]
    fn basic_read_write_test() {
        let mut env_builder = lmdb::Environment::new();
        env_builder.set_max_dbs(10);
        let (mut env, _temp_dir) = make_empty_env(&env_builder);
        crate::test_util::basic_read_write_test(&mut env, lmdb::DatabaseFlags::empty());
    }
}
