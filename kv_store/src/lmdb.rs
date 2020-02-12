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

impl<'cfg, 'envb, 'path, 'dbid, 'env, 'txn, 'kq, 'kp, 'vp, KQ, KP, VP>
    crate::StorageInterface<
        'env,
        'txn,
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
    type RoTransaction = RoTransaction<'env>;
    type RwTransaction = RwTransaction<'env>;
    type RoTxnRoCursor = RoCursor<'txn>;
    type RwTxnRoCursor = RoCursor<'txn>;
    type RwTxnRwCursor = RwCursor<'txn>;
}

impl<'cfg, 'envb, 'path, 'dbid>
    crate::Environment<
        &'cfg EnvironmentConfig<'envb, 'path>,
        Option<&'dbid str>,
        DbConfig,
        SyncConfig,
    > for Environment
{
    type Error = Error;
    type Stat = Stat;
    type Database = Database;
    type ReturnedDbConfig = DbConfig;

    fn new(config: &'cfg EnvironmentConfig<'envb, 'path>) -> Result<Self, Self::Error> {
        Ok(Self {
            env: config.open()?,
        })
    }

    fn open_db(&self, id: Option<&'dbid str>) -> Result<Self::Database, Self::Error> {
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
        &self,
        id: Option<&'dbid str>,
        config: DbConfig,
    ) -> Result<Self::Database, Self::Error> {
        // Make sure the requested configuration is supported.
        if db_config_allows_dup_keys(config) {
            Err(DbConfigError::DupKeysSpecified.into())
        } else {
            self.env.create_db(id, config).map_err(Into::into)
        }
    }

    fn db_config(&self, db: Self::Database) -> Result<Self::ReturnedDbConfig, Self::Error> {
        self.env.get_db_flags(db).map_err(Into::into)
    }

    fn sync(&self, config: SyncConfig) -> Result<(), Self::Error> {
        self.env.sync(config).map_err(Into::into)
    }

    fn stat(&self) -> Result<Self::Stat, Self::Error> {
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
    type ReturnedDbConfig = DbConfig;
    type ReturnedValue = &'txn [u8];

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

    fn db_config(&'txn self, db: Self::Database) -> Result<Self::ReturnedDbConfig, Self::Error>
    where
        Self: 'txn,
    {
        self.txn.db_flags(db).map_err(Into::into)
    }
}

impl<'cfg, 'envb, 'path, 'dbid, 'env, 'txn, 'kq, KQ>
    crate::RootTransaction<
        'env,
        'txn,
        Environment,
        &'cfg EnvironmentConfig<'envb, 'path>,
        Option<&'dbid str>,
        DbConfig,
        SyncConfig,
        &'kq KQ,
    > for RoTransaction<'env>
where
    KQ: AsRef<[u8]>,
{
    fn open(
        env: &'env Environment,
    ) -> Result<
        Self,
        <Environment as crate::Environment<
            &'cfg EnvironmentConfig<'envb, 'path>,
            Option<&'dbid str>,
            DbConfig,
            SyncConfig,
        >>::Error,
    >
    where
        Self: 'env,
        'env: 'txn,
    {
        Ok(Self {
            txn: env.env.begin_ro_txn()?,
        })
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
    type ReturnedDbConfig = DbConfig;
    type ReturnedValue = &'txn [u8];

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

    fn db_config(&'txn self, db: Self::Database) -> Result<Self::ReturnedDbConfig, Self::Error>
    where
        Self: 'txn,
    {
        self.txn.db_flags(db).map_err(Into::into)
    }
}

impl<'env, 'txn, 'kq, 'kp, 'vp, KQ, KP, VP>
    crate::ReadWriteTransaction<'txn, &'kq KQ, &'kp KP, &'vp VP> for RwTransaction<'env>
where
    KQ: AsRef<[u8]>,
    KP: AsRef<[u8]>,
    VP: AsRef<[u8]>,
{
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
}

impl<'cfg, 'envb, 'path, 'dbid, 'env, 'txn, 'kq, KQ>
    crate::RootTransaction<
        'env,
        'txn,
        Environment,
        &'cfg EnvironmentConfig<'envb, 'path>,
        Option<&'dbid str>,
        DbConfig,
        SyncConfig,
        &'kq KQ,
    > for RwTransaction<'env>
where
    KQ: AsRef<[u8]>,
{
    fn open(
        env: &'env Environment,
    ) -> Result<
        Self,
        <Environment as crate::Environment<
            &'cfg EnvironmentConfig<'envb, 'path>,
            Option<&'dbid str>,
            DbConfig,
            SyncConfig,
        >>::Error,
    >
    where
        Self: 'env,
        'env: 'txn,
    {
        Ok(Self {
            txn: env.env.begin_rw_txn()?,
        })
    }
}

impl<'env, 'parent, 'txn, 'kq, KQ>
    crate::NestedTransaction<'parent, 'txn, RwTransaction<'env>, &'kq KQ> for RwTransaction<'parent>
where
    KQ: AsRef<[u8]>,
{
    fn nest(parent: &'parent mut RwTransaction<'env>) -> Result<Self, Self::Error>
    where
        Self: 'parent,
        'parent: 'txn,
    {
        Ok(Self {
            txn: parent.txn.begin_nested_txn()?,
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

impl<'txn, 'kq, KQ> crate::Cursor<'txn, &'kq KQ> for RoCursor<'txn>
where
    KQ: AsRef<[u8]>,
{
    type Error = Error;
    type ReturnedKey = &'txn [u8];
    type ReturnedValue = &'txn [u8];

    fn get(&self) -> Result<Option<(Self::ReturnedKey, Self::ReturnedValue)>, Self::Error>
    where
        Self: 'txn,
    {
        lmdb_cursor_result_to_kv_pair(self.cursor.get(None, None, lmdb_sys::MDB_GET_CURRENT))
    }

    fn move_to_first(
        &mut self,
    ) -> Result<Option<(Self::ReturnedKey, Self::ReturnedValue)>, Self::Error>
    where
        Self: 'txn,
    {
        lmdb_cursor_result_to_kv_pair(self.cursor.get(None, None, lmdb_sys::MDB_FIRST))
    }

    fn move_to_last(
        &mut self,
    ) -> Result<Option<(Self::ReturnedKey, Self::ReturnedValue)>, Self::Error>
    where
        Self: 'txn,
    {
        lmdb_cursor_result_to_kv_pair(self.cursor.get(None, None, lmdb_sys::MDB_LAST))
    }

    fn move_to_next(
        &mut self,
    ) -> Result<Option<(Self::ReturnedKey, Self::ReturnedValue)>, Self::Error>
    where
        Self: 'txn,
    {
        lmdb_cursor_result_to_kv_pair(self.cursor.get(None, None, lmdb_sys::MDB_NEXT))
    }

    fn move_to_prev(
        &mut self,
    ) -> Result<Option<(Self::ReturnedKey, Self::ReturnedValue)>, Self::Error>
    where
        Self: 'txn,
    {
        lmdb_cursor_result_to_kv_pair(self.cursor.get(None, None, lmdb_sys::MDB_PREV))
    }

    fn move_to_key(&mut self, key: &'kq KQ) -> Result<Option<Self::ReturnedValue>, Self::Error>
    where
        Self: 'txn,
    {
        lmdb_cursor_result_to_value(self.cursor.get(Some(key.as_ref()), None, lmdb_sys::MDB_SET))
    }

    fn move_to_key_and_get_key(
        &mut self,
        key: &'kq KQ,
    ) -> Result<Option<(Self::ReturnedKey, Self::ReturnedValue)>, Self::Error>
    where
        Self: 'txn,
    {
        lmdb_cursor_result_to_kv_pair(self.cursor.get(
            Some(key.as_ref()),
            None,
            lmdb_sys::MDB_SET_KEY,
        ))
    }

    fn move_to_key_or_after(
        &mut self,
        key: &'kq KQ,
    ) -> Result<Option<(Self::ReturnedKey, Self::ReturnedValue)>, Self::Error>
    where
        Self: 'txn,
    {
        lmdb_cursor_result_to_kv_pair(self.cursor.get(
            Some(key.as_ref()),
            None,
            lmdb_sys::MDB_SET_RANGE,
        ))
    }
}

impl<'env, 'txn, 'kq, KQ> crate::ReadOnlyCursor<'txn, RoTransaction<'env>, &'kq KQ>
    for RoCursor<'txn>
where
    KQ: AsRef<[u8]>,
{
    fn open(
        txn: &'txn RoTransaction<'env>,
        db: <RoTransaction as crate::Transaction<'txn, &'kq KQ>>::Database,
    ) -> Result<Self, Self::Error>
    where
        RoTransaction<'env>: 'txn,
        Self: 'txn,
    {
        Ok(Self {
            cursor: txn.txn.open_ro_cursor(db)?,
        })
    }
}

impl<'env, 'txn, 'kq, KQ> crate::ReadOnlyCursor<'txn, RwTransaction<'env>, &'kq KQ>
    for RoCursor<'txn>
where
    KQ: AsRef<[u8]>,
{
    fn open(
        txn: &'txn RwTransaction<'env>,
        db: <RoTransaction as crate::Transaction<'txn, &'kq KQ>>::Database,
    ) -> Result<Self, Self::Error>
    where
        RoTransaction<'env>: 'txn,
        Self: 'txn,
    {
        Ok(Self {
            cursor: txn.txn.open_ro_cursor(db)?,
        })
    }
}

/// Read-write cursor type for the LMDB wrapper.
#[derive(Debug)]
pub struct RwCursor<'txn> {
    /// Wrapped LMDB cursor.
    cursor: lmdb::RwCursor<'txn>,
}

impl<'txn, 'kq, KQ> crate::Cursor<'txn, &'kq KQ> for RwCursor<'txn>
where
    KQ: AsRef<[u8]>,
{
    type Error = Error;
    type ReturnedKey = &'txn [u8];
    type ReturnedValue = &'txn [u8];

    fn get(&self) -> Result<Option<(Self::ReturnedKey, Self::ReturnedValue)>, Self::Error>
    where
        Self: 'txn,
    {
        lmdb_cursor_result_to_kv_pair(self.cursor.get(None, None, lmdb_sys::MDB_GET_CURRENT))
    }

    fn move_to_first(
        &mut self,
    ) -> Result<Option<(Self::ReturnedKey, Self::ReturnedValue)>, Self::Error>
    where
        Self: 'txn,
    {
        lmdb_cursor_result_to_kv_pair(self.cursor.get(None, None, lmdb_sys::MDB_FIRST))
    }

    fn move_to_last(
        &mut self,
    ) -> Result<Option<(Self::ReturnedKey, Self::ReturnedValue)>, Self::Error>
    where
        Self: 'txn,
    {
        lmdb_cursor_result_to_kv_pair(self.cursor.get(None, None, lmdb_sys::MDB_LAST))
    }

    fn move_to_next(
        &mut self,
    ) -> Result<Option<(Self::ReturnedKey, Self::ReturnedValue)>, Self::Error>
    where
        Self: 'txn,
    {
        lmdb_cursor_result_to_kv_pair(self.cursor.get(None, None, lmdb_sys::MDB_NEXT))
    }

    fn move_to_prev(
        &mut self,
    ) -> Result<Option<(Self::ReturnedKey, Self::ReturnedValue)>, Self::Error>
    where
        Self: 'txn,
    {
        lmdb_cursor_result_to_kv_pair(self.cursor.get(None, None, lmdb_sys::MDB_PREV))
    }

    fn move_to_key(&mut self, key: &'kq KQ) -> Result<Option<Self::ReturnedValue>, Self::Error>
    where
        Self: 'txn,
    {
        lmdb_cursor_result_to_value(self.cursor.get(Some(key.as_ref()), None, lmdb_sys::MDB_SET))
    }

    fn move_to_key_and_get_key(
        &mut self,
        key: &'kq KQ,
    ) -> Result<Option<(Self::ReturnedKey, Self::ReturnedValue)>, Self::Error>
    where
        Self: 'txn,
    {
        lmdb_cursor_result_to_kv_pair(self.cursor.get(
            Some(key.as_ref()),
            None,
            lmdb_sys::MDB_SET_KEY,
        ))
    }

    fn move_to_key_or_after(
        &mut self,
        key: &'kq KQ,
    ) -> Result<Option<(Self::ReturnedKey, Self::ReturnedValue)>, Self::Error>
    where
        Self: 'txn,
    {
        lmdb_cursor_result_to_kv_pair(self.cursor.get(
            Some(key.as_ref()),
            None,
            lmdb_sys::MDB_SET_RANGE,
        ))
    }
}

impl<'env, 'txn, 'kq, 'kp, 'vp, KQ, KP, VP>
    crate::ReadWriteCursor<'txn, RwTransaction<'env>, &'kq KQ, &'kp KP, &'vp VP> for RwCursor<'txn>
where
    KQ: 'kq + AsRef<[u8]>,
    KP: 'kp + AsRef<[u8]>,
    VP: 'vp + AsRef<[u8]>,
{
    fn open(
        txn: &'txn mut RwTransaction<'env>,
        db: <RwTransaction<'env> as crate::Transaction<'env, &'kq KQ>>::Database,
    ) -> Result<Self, Self::Error>
    where
        RwTransaction<'env>: 'txn,
        Self: 'txn,
    {
        Ok(Self {
            cursor: txn.txn.open_rw_cursor(db)?,
        })
    }

    fn put(&mut self, value: &'vp VP) -> Result<bool, Self::Error> {
        let key = <Self as crate::Cursor<'txn, &'kq KQ>>::get(self)?;
        if let Some((key, _)) = key {
            self.cursor
                .put(&key, value, lmdb::WriteFlags::CURRENT)
                .map(|_| true)
                .map_err(Into::into)
        } else {
            Ok(false)
        }
    }

    fn put_and_move_to_key(&mut self, key: &'kp KP, value: &'vp VP) -> Result<(), Self::Error> {
        self.cursor
            .put(key, value, lmdb::WriteFlags::empty())
            .map_err(Into::into)
    }

    fn put_no_overwrite_and_move_to_key(
        &mut self,
        key: &'kp KP,
        value: &'vp VP,
    ) -> Result<bool, Self::Error> {
        let lmdb_result = self.cursor.put(key, value, lmdb::WriteFlags::NO_OVERWRITE);
        if lmdb_result == Err(lmdb::Error::KeyExist) {
            Ok(false)
        } else {
            lmdb_result.map(|_| true).map_err(Into::into)
        }
    }

    fn del(&mut self) -> Result<bool, Self::Error> {
        let lmdb_result = self.cursor.del(lmdb::WriteFlags::empty());
        if lmdb_result == Err(lmdb::Error::NotFound) {
            Ok(false)
        } else {
            lmdb_result.map(|_| true).map_err(Into::into)
        }
    }
}
