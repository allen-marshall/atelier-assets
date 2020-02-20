//! This module provides a transactional key-value database/storage API with
//! semantics that are largely modeled after [LMDB][lmdb].
//!
//! There are a few ways in which this library departs from the semantics of
//! LMDB. Most notably, this library does not allow duplicate entries for the
//! same key in a database.
//!
//! Two implementations of the API are provided. One is a wrapper around LMDB,
//! and the other is an in-memory implementation with minimal dependencies. Both
//! are disabled by default, and can be enabled through Cargo features.
//!
//! [lmdb]: http://symas.com/mdb/

pub mod iter;
#[cfg(feature = "lmdb_impl")]
pub mod lmdb;
pub mod lt_trait_wrappers;

/// Supertrait for [`Environment`][Environment] containing functionality that is
/// independent of any lifetime or type parameters.
///
/// [Environment]: self::Environment
pub trait EnvironmentBasic {
    /// Error that may occur when operating on the storage environment.
    type Error;

    /// Statistics that can be obtained from the environment.
    type Stat;

    /// Handle that the environment provides for referencing a database after it
    /// has been opened.
    type Database;
}

/// Main trait for storage environment handles. A storage environment is
/// essentially a type of session that can interact with a set of databases.
/// Each database contains a key-value store.
///
/// # Transaction semantics
/// Transactions are tied to a specific environment, but not to a specific
/// database within that environment. The environment must give each
/// transaction a consistent view of its entire collection of databases.
///
/// Read-only transactions must never be blocked by other transactions, and must
/// never block other transactions. However, any active read-write transaction
/// must cause creation of other read-write transactions to block, so that there
/// is at most one active read-write transaction in the environment at any time.
/// (Exception: Read-write transactions may create nested read-write
/// transactions. Each read-write transaction may have at most one directly
/// nested child transaction at a time, though multiple indirect children are
/// possible through recursive nesting.)
///
/// # Parameters
/// - `'env`: Lifetime for environment references.
/// - `EC`: Configuration data that can be provided to initialize an
///   environment.
/// - `DI`: Unique ID associated with each database in the environment.
/// - `DC`: Configuration data that can be provided to initialize an individual
///   database.
/// - `SC`: Configuration data that can be provided when calling [`sync`][sync]
///   to flush buffered data. This controls how the flush is performed.
/// - `KQ`: Key type that can be used to query a database's key-value store.
/// - `KP`: Key type that can be used to insert an entry into a database. May or
///   may not be the same as `KQ`.
/// - `VP`: Value type that can be used to insert an entry into a database.
///
/// [sync]: self::Environment::sync
pub trait Environment<'env, EC, DI, DC, SC, KQ, KP, VP>: Sized + EnvironmentBasic {
    /// Configuration information that can be obtained for an individual
    /// database. May or may not be the same type as `DC`.
    type ReturnedDbConfig;

    /// Read-only transaction type that can be opened from the environment.
    type RoTransaction: 'env
        + TransactionBasic<Error = Self::Error, Database = Self::Database>
        + for<'txn> Transaction<'txn, KQ>;

    /// Read-write transaction type that can be opened from the environment.
    type RwTransaction: 'env
        + TransactionBasic<Error = Self::Error, Database = Self::Database>
        + for<'txn> ReadWriteTransaction<'txn, KQ, KP, VP>;

    /// Initializes an environment. To close the environment, simply drop the
    /// returned environment object.
    fn new(config: EC) -> Result<Self, Self::Error>
    where
        Self: 'env;

    /// Opens a database with the specified database ID. Always fails if the
    /// database does not already exist.
    ///
    /// The returned database handle can be used by multiple transactions
    /// concurrently.
    ///
    /// Implementations may return an error if there are active transactions.
    /// Therefore, it is recommended to get handles to all required databases
    /// before starting any transactions.
    fn open_db(&'env mut self, id: DI) -> Result<Self::Database, Self::Error>
    where
        Self: 'env;

    /// Creates and opens a database with the specified database ID and
    /// configuration. If the database already exists, its configuration may be
    /// updated to the new configuration, or it may be combined with the new
    /// configuration in some implementation-specific way.
    ///
    /// The returned database handle can be used by multiple transactions
    /// concurrently.
    ///
    /// Implementations may return an error if there are active transactions.
    /// Therefore, it is recommended to get handles to all required databases
    /// before starting any transactions.
    fn create_db(&'env mut self, id: DI, config: DC) -> Result<Self::Database, Self::Error>
    where
        Self: 'env;

    /// Gets the configuration of the specified open database.
    fn db_config(&'env self, db: Self::Database) -> Result<Self::ReturnedDbConfig, Self::Error>
    where
        Self: 'env;

    /// Flushes any buffered data owned by the environment, typically to disk.
    /// Implementations that don't have buffering can make this a no-op.
    fn sync(&'env self, config: SC) -> Result<(), Self::Error>
    where
        Self: 'env;

    /// Gets statistics about the environment.
    fn stat(&'env self) -> Result<Self::Stat, Self::Error>
    where
        Self: 'env;

    /// Starts a new read-only transaction in the environment.
    fn begin_ro_txn(&'env self) -> Result<Self::RoTransaction, Self::Error>
    where
        Self: 'env;

    /// Starts a new read-write transaction in the environment. If there is
    /// already an active read-write transaction in the environment, this
    /// function must block until there is none.
    fn begin_rw_txn(&'env self) -> Result<Self::RwTransaction, Self::Error>
    where
        Self: 'env;
}

/// Supertrait for [`Transaction`][Transaction] containing functionality that is
/// independent of any lifetime or type parameters.
///
/// [Transaction]: self::Transaction
pub trait TransactionBasic {
    /// Error that may occur when operating on the transaction.
    type Error;

    /// Handle to an open database.
    type Database;
}

/// Trait for transaction handles.
///
/// Implementations must ensure that any active transaction has no more than one
/// handle in existence at a time. Usually this means that `Transaction` types
/// should not implement [`Clone`][Clone].
///
/// A transaction can be finalized by either aborting it or committing it. If a
/// transaction is not manually committed or aborted, implementations must
/// automatically abort it when the transaction handle is dropped.
///
/// # Parameters
/// - `'txn`: Lifetime for transaction references.
/// - `KQ`: Key type that can be used to query a database's key-value store.
///
/// [Clone]: std::clone::Clone
pub trait Transaction<'txn, KQ>: Sized + TransactionBasic {
    /// Configuration information that can be obtained for an individual
    /// database.
    type ReturnedDbConfig;

    /// Value object type returned from lookup operations.
    type ReturnedValue;

    /// Read-only cursor that can be opened within the transaction.
    type RoCursor: 'txn + CursorBasic<Error = Self::Error> + for<'cursor> Cursor<'cursor, KQ>;

    /// Commits the transaction, making any data writes that it performed
    /// potentially visible to future transactions.
    fn commit(self) -> Result<(), Self::Error>
    where
        Self: 'txn;

    /// Aborts the transaction. Note that dropping the transaction handle
    /// without explicitly committing also aborts the transaction, so the only
    /// reason to call this function is for potential code clarity. The default
    /// implementation does nothing but drop the transaction handle.
    fn abort(self)
    where
        Self: 'txn,
    {
    }

    /// Gets the stored value for the specified key in the specified database.
    ///
    /// Returns [`Ok`][Ok]`(`[`None`][None]`)` if the specified key is not
    /// present (assuming no error occurs).
    ///
    /// [Ok]: std::result::Result::Ok
    /// [None]: std::option::Option::None
    fn get(
        &'txn self,
        db: &Self::Database,
        key: KQ,
    ) -> Result<Option<Self::ReturnedValue>, Self::Error>
    where
        Self: 'txn;

    /// Gets the configuration of the specified open database.
    fn db_config(&'txn self, db: Self::Database) -> Result<Self::ReturnedDbConfig, Self::Error>
    where
        Self: 'txn;

    /// Opens a new read-only cursor inside the transaction.
    fn open_ro_cursor(&'txn self, db: &Self::Database) -> Result<Self::RoCursor, Self::Error>
    where
        Self: 'txn;
}

/// Trait for transaction handles that allow writing.
///
/// # Parameters
/// - `'txn`: Lifetime for transaction references.
/// - `KQ`: Key type that can be used to query a database's key-value store.
/// - `KP`: Key type that can be used to insert an entry into a database. May or
///   may not be the same as `KQ`.
/// - `VP`: Value type that can be used to insert an entry into a database.
pub trait ReadWriteTransaction<'txn, KQ, KP, VP>: Transaction<'txn, KQ> {
    /// Read-write cursor that can be opened within the transaction.
    type RwCursor: 'txn
        + CursorBasic<Error = Self::Error>
        + for<'cursor> Cursor<'cursor, KQ>
        + for<'cursor> ReadWriteCursor<'cursor, KQ, KP, VP>;

    /// Child transaction that can be created from the parent read-write
    /// transaction.
    type Nested: 'txn
        + TransactionBasic<Error = Self::Error, Database = Self::Database>
        + for<'child_txn> ReadWriteTransaction<'child_txn, KQ, KP, VP>;

    /// Stores the specified key-value pair in the specified database. If the
    /// database already contains an entry for the specified key, the old entry
    /// will be overwritten.
    fn put(&'txn mut self, db: &Self::Database, key: KP, value: VP) -> Result<(), Self::Error>
    where
        Self: 'txn;

    /// Stores the specified key-value pair in the specified database, if the
    /// database does not already contain an entry for the specified key. On
    /// success, returns `true` if the entry was stored and `false` if there was
    /// already an entry in the database with the specified key.
    fn put_no_overwrite(
        &'txn mut self,
        db: Self::Database,
        key: KP,
        value: VP,
    ) -> Result<bool, Self::Error>
    where
        Self: 'txn;

    /// Deletes the entry for the specified key from the specified database, if
    /// there is such an entry. On success, returns `true` if a deletion was
    /// performed and `false` if the entry to delete did not exist.
    fn del(&'txn mut self, db: Self::Database, key: KQ) -> Result<bool, Self::Error>
    where
        Self: 'txn;

    /// Removes all entries from the specified database.
    fn clear_db(&'txn mut self, db: Self::Database) -> Result<(), Self::Error>
    where
        Self: 'txn;

    /// Opens a new read-write cursor inside the transaction.
    fn open_rw_cursor(&'txn mut self, db: &Self::Database) -> Result<Self::RwCursor, Self::Error>
    where
        Self: 'txn;

    /// Begins a child transaction nested inside the transaction referenced by
    /// `self`.
    ///
    /// Implementations should enforce the following restrictions.
    /// - A parent transaction may have at most one direct child transaction at
    ///   a time (though multiple indirect children can be created through
    ///   recursive nesting).
    /// - A parent transaction cannot be used directly to access databases while
    ///   it has an active child transaction.
    fn begin_nested_txn(&'txn mut self) -> Result<Self::Nested, Self::Error>
    where
        Self: 'txn;
}

/// Trait for types whose objects hold some resource which would normally be
/// released after the holder object is dropped, but might be able to be reused
/// instead in order to save allocation overhead.
///
/// If the active object is dropped without being converted to an inactive form
/// through the [`deactivate`][deactivate] function, the reusable resource
/// should generally be released immediately.
///
/// # Parameters
/// - `I`: Inactive object type that can hold onto the reusable resource after
///   the active holder is dropped.
///
/// [deactivate]: self::ActiveRenewable::deactivate
pub trait ActiveRenewable<I> {
    /// Error that can occur when deactivating the active object.
    type Error;

    /// Deactivates an active object, converting it into an inactive object that
    /// may hold onto its reusable resources.
    fn deactivate(self) -> Result<I, Self::Error>;
}

/// Trait for types whose objects hold onto some inactive resource, which would
/// normally have been deleted but might be able to be reused in order to save
/// allocation overhead.
///
/// If the inactive object is dropped without being [`renew`][renew]ed, it
/// should generally release the resources it was holding.
///
/// # Parameters
/// - `A`: Active object type that can be created by reusing the resources.
///
/// [renew]: self::InactiveRenewable::renew
pub trait InactiveRenewable<A> {
    /// Error that can occur when renewing the inactive object.
    type Error;

    /// Renews the inactive object, creating a new active object. This
    /// potentially reuses resources and therefore may be more efficient than
    /// creating a new active object from scratch.
    fn renew(self) -> Result<A, Self::Error>;
}

/// Supertrait for [`Cursor`][Cursor] containing functionality that is
/// independent of any lifetime or type parameters.
///
/// [Cursor]: self::Cursor
pub trait CursorBasic {
    /// Error that may occur when operating on the cursor.
    type Error;

    /// Type of key data returned from lookup operations.
    type ReturnedKey: ?Sized;

    /// Type of value data returned from lookup operations.
    type ReturnedValue: ?Sized;
}

/// Trait for database cursor handles. Unlike transactions, each cursor is tied
/// to a specific database within an environment and can only operate on that
/// database. This trait defines the common functionality for read-only and
/// read-write cursors.
///
/// Each cursor is initially in an unpositioned state, but may later be
/// positioned at a specific key, which we call the cursor's *position key*. It
/// is possible for a cursor to be positioned at a key that doesn't exist in the
/// database; this typically only happens for cursors that allow deletions.
///
/// The cursor API assumes that entries in the database are sorted by key using
/// an unambiguous, stable key ordering. It is recommended (but not required)
/// that key types implement [`Ord`][Ord] and that the ordering used by the
/// database be compatible with the ordering defined by [`Ord`][Ord].
///
/// # Parameters
/// - `'cursor`: Lifetime for cursor references.
/// - `KQ`: Key type that can be used to position the cursor at a specific key.
///
/// [Ord]: std::cmp::Ord
pub trait Cursor<'cursor, KQ>: CursorBasic {
    /// Key object handle type returned from lookup operations.
    type ReturnedKeyHandle: 'cursor + CursorReturnedDataHandle<'cursor, Self::ReturnedKey>;

    /// Value object handle type returned from lookup operations.
    type ReturnedValueHandle: 'cursor + CursorReturnedDataHandle<'cursor, Self::ReturnedValue>;

    /// Retrieves the key-value pair at the cursor's current position. If the
    /// cursor's position key does not exist in the database, the first entry
    /// with a key greater than the cursor's position key is returned instead.
    /// In either case, the cursor's position does not change.
    ///
    /// Assuming no error occurs, [`Ok`][Ok]`(`[`None`][None]`)` will be
    /// returned in any of the following circumstances.
    /// - The cursor is unpositioned.
    /// - The database does not contain any key greater than or equal to the
    ///   cursor's position key.
    ///
    /// [Ok]: std::result::Result::Ok
    /// [None]: std::option::Option::None
    fn get(
        &'cursor self,
    ) -> Result<Option<(Self::ReturnedKeyHandle, Self::ReturnedValueHandle)>, Self::Error>
    where
        Self: 'cursor;

    /// Repositions the cursor to the first key in the database, and retrieves
    /// the corresponding key-value pair.
    ///
    /// If the database is empty but no other error occurs, the cursor's
    /// position state is left unchanged, and [`Ok`][Ok]`(`[`None`][None]`)` is
    /// returned.
    ///
    /// [Ok]: std::result::Result::Ok
    /// [None]: std::option::Option::None
    fn move_to_first(
        &'cursor mut self,
    ) -> Result<Option<(Self::ReturnedKeyHandle, Self::ReturnedValueHandle)>, Self::Error>
    where
        Self: 'cursor;

    /// Repositions the cursor to the last key in the database, and retrieves
    /// the corresponding key-value pair.
    ///
    /// If the database is empty but no other error occurs, the cursor's
    /// position state is left unchanged, and [`Ok`][Ok]`(`[`None`][None]`)` is
    /// returned.
    ///
    /// [Ok]: std::result::Result::Ok
    /// [None]: std::option::Option::None
    fn move_to_last(
        &'cursor mut self,
    ) -> Result<Option<(Self::ReturnedKeyHandle, Self::ReturnedValueHandle)>, Self::Error>
    where
        Self: 'cursor;

    /// Repositions the cursor to the first key in the database that is greater
    /// than the cursor's current position key, and retrieves the database entry
    /// at the new key. If the cursor is unpositioned, it will be moved to the
    /// first entry in the database.
    ///
    /// In any of the following circumstances (assuming no error occurs), the
    /// cursor's position state will be left unchanged, and
    /// [`Ok`][Ok]`(`[`None`][None]`)` will be returned.
    /// - The cursor is unpositioned, and the database is empty.
    /// - The cursor has a position key, and the database does not contain any
    ///   key greater than the cursor's position key.
    ///
    /// [Ok]: std::result::Result::Ok
    /// [None]: std::option::Option::None
    fn move_to_next(
        &'cursor mut self,
    ) -> Result<Option<(Self::ReturnedKeyHandle, Self::ReturnedValueHandle)>, Self::Error>
    where
        Self: 'cursor;

    /// Repositions the cursor to the last key in the database that is less than
    /// the cursor's current position key, and retrieves the database entry
    /// at the new key. If the cursor is unpositioned, it will be moved to the
    /// last entry in the database.
    ///
    /// In any of the following circumstances (assuming no error occurs), the
    /// cursor's position state will be left unchanged, and
    /// [`Ok`][Ok]`(`[`None`][None]`)` will be returned.
    /// - The cursor is unpositioned, and the database is empty.
    /// - The cursor has a position key, and the database does not contain any
    ///   key less than the cursor's position key.
    ///
    /// [Ok]: std::result::Result::Ok
    /// [None]: std::option::Option::None
    fn move_to_prev(
        &'cursor mut self,
    ) -> Result<Option<(Self::ReturnedKeyHandle, Self::ReturnedValueHandle)>, Self::Error>
    where
        Self: 'cursor;

    /// Repositions the cursor to the specified key, and retrieves the value
    /// associated with that key in the database.
    ///
    /// This function cannot be used to position the cursor at a key that is not
    /// present in the database. Assuming no error occurs, if the specified key
    /// is not in the database, the cursor's position state will be left
    /// unchanged, and [`Ok`][Ok]`(`[`None`][None]`)` will be returned.
    ///
    /// [Ok]: std::result::Result::Ok
    /// [None]: std::option::Option::None
    fn move_to_key(
        &'cursor mut self,
        key: KQ,
    ) -> Result<Option<Self::ReturnedValueHandle>, Self::Error>
    where
        Self: 'cursor;

    /// Same as [`move_to_key`][move_to_key], except that after the reposition,
    /// it retrieves the key as well as the value. Retrieving the key is often
    /// pointless, as the caller will likely already know the key given that
    /// they specified it. However, there might be cases where this function is
    /// useful.
    ///
    /// [move_to_key]: self::Cursor::move_to_key
    fn move_to_key_and_get_key(
        &'cursor mut self,
        key: KQ,
    ) -> Result<Option<(Self::ReturnedKeyHandle, Self::ReturnedValueHandle)>, Self::Error>
    where
        Self: 'cursor;

    /// Repositions the cursor to the first key in the database that is greater
    /// than or equal to the specified key, and retrieves the corresponding
    /// key-value pair. (If the database contains an entry for the specified
    /// key, the cursor moves to that entry.)
    ///
    /// If the database contains no key that is greater than or equal to the
    /// specified key (assuming no other error occurs), the cursor's position
    /// state is left unchanged, and [`Ok`][Ok]`(`[`None`][None]`)` is returned.
    ///
    /// [Ok]: std::result::Result::Ok
    /// [None]: std::option::Option::None
    fn move_to_key_or_after(
        &'cursor mut self,
        key: KQ,
    ) -> Result<Option<(Self::ReturnedKeyHandle, Self::ReturnedValueHandle)>, Self::Error>
    where
        Self: 'cursor;
}

/// Trait for database cursor handles that allow writing.
///
/// # Parameters
/// - `'cursor`: Lifetime for cursor references.
/// - `KQ`: Key type that can be used to position the cursor at a specific key.
/// - `KP`: Key type that can be used to insert an entry into the database. May
///   or may not be the same as `KQ`.
/// - `VP`: Value type that can be used to insert an entry into the database.
pub trait ReadWriteCursor<'cursor, KQ, KP, VP>: Cursor<'cursor, KQ> {
    /// Sets the value of the database entry with the specified key (inserting
    /// the entry if it doesn't already exist), and repositions the cursor to
    /// that key.
    fn put_and_move_to_key(&'cursor mut self, key: KP, value: VP) -> Result<(), Self::Error>
    where
        Self: 'cursor;

    /// Inserts the specified key-value pair into the database *if* the database
    /// does not already contain an entry for the specified key, and repositions
    /// the cursor to the specified key. On success, the cursor will move even
    /// if no write was performed.
    ///
    /// Returns [`Ok`][Ok]`(true)` if the write was performed successfully.
    /// Returns [`Ok`][Ok]`(false)` if the database already contained the
    /// specified key, but no other error occurred.
    ///
    /// [Ok]: std::result::Result::Ok
    fn put_no_overwrite_and_move_to_key(
        &'cursor mut self,
        key: KP,
        value: VP,
    ) -> Result<bool, Self::Error>
    where
        Self: 'cursor;

    /// Deletes an entry from the database based on the cursor's position state,
    /// without modifying the position state. There are a few possible cases
    /// that determine the behavior:
    /// - If the cursor is unpositioned, no deletion is performed, and
    ///   [`Ok`][Ok]`(false)` is returned (assuming no error occurs).
    /// - If the cursor is positioned at a key that exists in the database, the
    ///   entry associated with that key is deleted. [`Ok`][Ok]`(true)` is
    ///   returned (assuming no error occurs).
    /// - If the cursor is positioned at a key that does not exist in the
    ///   database, and the database contains at least one key that is greater
    ///   than the cursor's position key, the deletion occurs at the first such
    ///   key. In other words, the first key in the database that is greater
    ///   than the cursor's position key gets its entry deleted.
    ///   [`Ok`][Ok]`(true)` is returned (assuming no error occurs).
    /// - If the cursor is positioned at a key that does not exist in the
    ///   database, and all keys in the database are less than the cursor's
    ///   position key, no deletion is performed. [`Ok`][Ok]`(false)` is
    ///   returned (assuming no error occurs).
    ///
    /// Note that, conceptually, this function does not modify the cursor's
    /// position state even if a deletion is successfully performed. This is the
    /// main way in which a cursor can end up positioned at a key that does not
    /// exist in the database.
    ///
    /// [Ok]: std::result::Result::Ok
    fn del(&'cursor mut self) -> Result<bool, Self::Error>
    where
        Self: 'cursor;
}

/// Trait for key or value data returned by cursor operations.
///
/// # Parameters
/// - `'cursor`: Lifetime for the cursor reference that was used to retrieve the
///   data.
/// - `D`: Type of wrapped data that can be retrieved from the handle.
///
/// # Safety
/// This trait is marked `unsafe` because its [`get`][get] method must uphold a
/// safety guarantee that can't be easily enforced by Rust's type system.
///
/// [get]: self::CursorReturnedDataHandle::get
pub unsafe trait CursorReturnedDataHandle<'cursor, D: ?Sized> {
    /// Gets a reference to the wrapped data.
    ///
    /// # Safety
    /// In addition to being valid for the lifetime `'cursor`, the returned
    /// pointer must also be valid at least until one of the following happens.
    /// - The cursor from which this data was retrieved is destroyed.
    /// - The cursor from which this data was retrieved is used to mutate the
    ///   database, using one of the methods from
    ///   [`ReadWriteCursor`][ReadWriteCursor].
    ///
    /// Note: The main purpose for this extra constraint is to make it possible
    /// to wrap cursors in an [`Iterator`][Iterator]. This will be unnecessary
    /// in the future if Rust gets generic associated types.
    ///
    /// [ReadWriteCursor]: self::ReadWriteCursor
    /// [Iterator]: std::iter::Iterator
    fn get(&self) -> &'cursor D;
}
