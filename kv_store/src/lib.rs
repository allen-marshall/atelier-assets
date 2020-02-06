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

/// Trait for handles to storage environments. A storage environment is
/// essentially a type of session that can interact with a set of databases.
/// Each database contains a key-value store.
///
/// # Parameters
/// - `'a`: Lifetime used for `self` references. This is a workaround for the
///   lack of lifetime-generic associated types in Rust.
/// - `C`: Configuration data that can be provided to initialize an environment.
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
pub trait Environment<'a, C, DI, DC, SC, KQ, KP, KV>: 'a + Sized
where
    for<'b> Self::RoTransaction: Transaction<
        'b,
        KQ,
        Error = Self::Error,
        Database = Self::Database,
        DbConfig = Self::DbConfig,
    >,
    for<'b> Self::RwTransaction: WriteTransaction<
        'b,
        KQ,
        KP,
        KV,
        Error = Self::Error,
        Database = Self::Database,
        DbConfig = Self::DbConfig,
    >,
{
    /// Error that may occur when operating on the storage environment.
    type Error;

    /// Statistics that can be obtained from the environment.
    type Stat;

    /// Handle that the environment provides for referencing a database after it
    /// has been opened.
    type Database;

    /// Configuration information that can be obtained for an individual
    /// database. May or may not be the same type as `DC`.
    type DbConfig;

    /// Handle to an active read-only transaction.
    type RoTransaction: 'a;

    /// Handle to an active read-write transaction.
    type RwTransaction: 'a;

    /// Initializes an environment. To close the environment, simply drop the
    /// returned environment object.
    fn new(config: C) -> Result<Self, Self::Error>;

    /// Opens a database with the specified database ID. Always fails if the
    /// database does not already exist.
    ///
    /// The returned database handle can be used by multiple transactions
    /// concurrently.
    ///
    /// Implementations may return an error in certain contexts if there are
    /// active transactions. Therefore, it is recommended to get handles to all
    /// required databases before starting any transactions.
    fn open_db(&'a self, id: DI) -> Result<Self::Database, Self::Error>;

    /// Creates and opens a database with the specified database ID and
    /// configuration. If the database already exists, its configuration may be
    /// updated to the new configuration, or it may be combined with the new
    /// configuration in some implementation-specific way.
    ///
    /// The returned database handle can be used by multiple transactions
    /// concurrently.
    ///
    /// Implementations may return an error in certain contexts if there are
    /// active transactions. Therefore, it is recommended to get handles to all
    /// required databases before starting any transactions.
    fn create_db(&'a self, id: DI, config: DC) -> Result<Self::Database, Self::Error>;

    /// Gets the configuration of the specified open database.
    fn db_config(&'a self, db: Self::Database) -> Result<Self::DbConfig, Self::Error>;

    /// Starts a new read-only transaction.
    ///
    /// Transactions are tied to a specific environment, but not to a specific
    /// database within that environment. The environment must give each
    /// transaction a consistent view of its entire collection of databases.
    ///
    /// Read-only transactions should never be blocked by other transactions,
    /// and should never block other transactions.
    fn begin_ro_txn(&'a self) -> Result<Self::RoTransaction, Self::Error>;

    /// Starts a new read-write transaction.
    ///
    /// Transactions are tied to a specific environment, but not to a specific
    /// database within that environment. The environment must give each
    /// transaction a consistent view of its entire collection of databases.
    ///
    /// Read-write transactions should never be blocked by read-only
    /// transactions. However, the `Environment` trait requires that at most one
    /// read-write transaction be active on a storage environment at a time. To
    /// enforce this, this function should block until no other read-write
    /// transaction is active.
    fn begin_rw_txn(&'a self) -> Result<Self::RwTransaction, Self::Error>;

    /// Flushes any buffered data owned by the environment, typically to disk.
    /// Implementations that don't have buffering can make this a no-op.
    fn sync(&'a self, config: SC) -> Result<(), Self::Error>;

    /// Gets statistics about the environment.
    fn stat(&'a self) -> Result<Self::Stat, Self::Error>;
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
/// - `'a`: Lifetime used for `self` references. This is a workaround for the
///   lack of lifetime-generic associated types in Rust.
/// - `KQ`: Key type that can be used to query a database's key-value store.
///
/// [Clone]: std::clone::Clone
pub trait Transaction<'a, KQ>: 'a + Sized
where
    for<'b> Self::RoCursor:
        Cursor<'b, KQ, Error = Self::Error, ReturnedValue = Self::ReturnedValue>,
{
    /// Error that can occur when operating on the transaction.
    type Error;

    /// Handle used to refer to an open database.
    type Database;

    /// Configuration information that can be obtained for an individual
    /// database.
    type DbConfig;

    /// Value object type returned from lookup operations.
    type ReturnedValue;

    /// Read-only cursor type that can be created by the transaction.
    type RoCursor: 'a;

    /// Commits the transaction, saving any data writes that it performed.
    fn commit(self) -> Result<(), Self::Error>;

    /// Aborts the transaction. Note that dropping the transaction handle
    /// without explicitly committing also aborts the transaction, so the only
    /// reason to call this function is for potential code clarity. The default
    /// implementation does nothing but drop the transaction handle.
    fn abort(self) {}

    /// Gets the stored value for the specified key in the specified database.
    ///
    /// Returns [`Ok`][Ok]`(`[`None`][None]`)` if the specified key is not
    /// present, assuming no other error occurs.
    ///
    /// [Ok]: std::result::Result::Ok
    /// [None]: std::option::Option::None
    fn get(
        &'a self,
        db: Self::Database,
        key: KQ,
    ) -> Result<Option<Self::ReturnedValue>, Self::Error>;

    /// Opens a read-only cursor for iterating over key-value pairs in the
    /// specified database.
    fn open_ro_cursor(&'a self, db: Self::Database) -> Result<Self::RoCursor, Self::Error>;

    /// Gets the configuration of the specified open database.
    fn db_config(&'a self, db: Self::Database) -> Result<Self::DbConfig, Self::Error>;
}

/// Trait for transaction handles that allow writing.
///
/// # Parameters
/// - `'a`: Lifetime used for `self` references. This is a workaround for the
///   lack of lifetime-generic associated types in Rust.
/// - `KQ`: Key type that can be used to query a database's key-value store.
/// - `KP`: Key type that can be used to insert an entry into a database. May or
///   may not be the same as `KQ`.
/// - `VP`: Value type that can be used to insert an entry into a database.
pub trait WriteTransaction<'a, KQ, KP, VP>: Transaction<'a, KQ>
where
    for<'b> Self::RwCursor:
        WriteCursor<'b, KQ, KP, VP, Error = Self::Error, ReturnedValue = Self::ReturnedValue>,
{
    /// Read-only cursor type that can be created by the transaction.
    type RwCursor: 'a;

    /// Stores the specified key-value pair in the specified database. If the
    /// database already contains an entry for the specified key, the old entry
    /// will be overwritten.
    fn put(&'a mut self, db: Self::Database, key: KP, value: VP) -> Result<(), Self::Error>;

    /// Stores the specified key-value pair in the specified database, if the
    /// database does not already contain an entry for the specified key. On
    /// success, returns `true` if the entry was stored and `false` if there was
    /// already an entry in the database with the specified key.
    fn put_no_overwrite(
        &'a mut self,
        db: Self::Database,
        key: KP,
        value: VP,
    ) -> Result<bool, Self::Error>;

    /// Deletes the entry for the specified key from the specified database, if
    /// there is such an entry. On success, returns `true` if a deletion was
    /// performed and `false` if the entry to delete did not exist.
    fn del(&'a mut self, db: Self::Database, key: KQ) -> Result<bool, Self::Error>;

    /// Removes all entries from the specified database.
    fn clear_db(&'a mut self, db: Self::Database) -> Result<(), Self::Error>;

    /// Opens a read-write cursor to operate on the specified database.
    fn open_rw_cursor(&'a mut self, db: Self::Database) -> Result<Self::RwCursor, Self::Error>;
}

/// Trait for transaction handles that allow the creation of nested
/// transactions.
///
/// This trait uses lifetimes to ensure that a parent transaction can have at
/// most one direct child transaction at a time (though multiple levels of
/// nesting are allowed), and that a parent transaction cannot be directly
/// accessed while it has an active child.
///
/// # Parameters
/// - `'a`: Lifetime used for `self` references. This is a workaround for the
///   lack of lifetime-generic associated types in Rust.
/// - `KQ`: Key type that can be used to query a database's key-value store.
pub trait NestableTransaction<'a, KQ>: Transaction<'a, KQ>
where
    for<'b> Self::Nested: Transaction<'b, KQ>,
{
    /// Child transaction type. May or may not be the same type as `Self`.
    type Nested: 'a;

    /// Begins a child transaction nested inside `self`.
    ///
    /// If the child transaction gets aborted, any database changes it performed
    /// should be invisible to the parent transaction (and all other
    /// transactions) both during and after the child transaction's lifetime.
    /// If the child transaction gets committed, its changes should become
    /// immediately visible to the parent transaction, but should *not* be
    /// visible to any other transactions until the parent transaction is
    /// committed.
    fn begin_nested_txn(&'a mut self) -> Result<Self::Nested, Self::Error>;
}

/// Trait for types whose objects hold some resource, which would normally be
/// deleted after the holder object is dropped, but might be able to be reused
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
    /// Type of error that can occur when deactivating the active object.
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
    /// Type of error that can occur when renewing the inactive object.
    type Error;

    /// Renews the inactive object, creating a new active object. This
    /// potentially reuses resources and therefore may be more efficient than
    /// creating a new active object from scratch.
    fn renew(self) -> Result<A, Self::Error>;
}

/// Trait for database cursor handles. Unlike transactions, each cursor is tied
/// to a specific database within an environment and can only operate on that
/// database.
///
/// Each cursor is initially in an unpositioned state, but may later be
/// positioned at a specific key, which we call the cursor's *position key*. It
/// is possible for a cursor to be positioned at a key that doesn't exist in the
/// database; this typically only happens for cursors that allow deletions.
///
/// Note: The cursor API assumes that entries in the database are sorted by key
/// using an unambiguous, stable key ordering. It is recommended (but not
/// required) that key types implement [`Ord`][Ord] and that the ordering used
/// by the database be compatible with the ordering defined by [`Ord`][Ord].
///
/// # Parameters
/// - `'a`: Lifetime used for `self` references. This is a workaround for the
///   lack of lifetime-generic associated types in Rust.
/// - `KQ`: Key type that can be used to point the cursor to a specific key in
///   the database.
///
/// [Ord]: std::cmp::Ord
pub trait Cursor<'a, KQ>: 'a {
    /// Type of error that may occur when operating on the cursor.
    type Error;

    /// Key object type returned from read operations. This may or may not be
    /// the same type as `KQ`.
    type ReturnedKey;

    /// Value object type returned from read operations.
    type ReturnedValue;

    /// A cursor can be wrapped in an iterator to provide an iteration-based
    /// interface to a database. This is the iterator type to use for this
    /// purpose. (The lifetime bound of `'a` ensures that the cursor cannot be
    /// used directly while the iterator is manipulating it.)
    ///
    /// If the iterator encounters an unexpected database error during
    /// iteration, it should produce one [`Err`][Err] value containing the
    /// error, then stop producing values.
    ///
    /// [Err]: std::result::Result::Err
    type Iter: 'a + Iterator<Item = Result<(Self::ReturnedKey, Self::ReturnedValue), Self::Error>>;

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
    fn get(&'a self) -> Result<Option<(Self::ReturnedKey, Self::ReturnedValue)>, Self::Error>;

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
        &'a mut self,
    ) -> Result<Option<(Self::ReturnedKey, Self::ReturnedValue)>, Self::Error>;

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
        &'a mut self,
    ) -> Result<Option<(Self::ReturnedKey, Self::ReturnedValue)>, Self::Error>;

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
        &'a mut self,
    ) -> Result<Option<(Self::ReturnedKey, Self::ReturnedValue)>, Self::Error>;

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
        &'a mut self,
    ) -> Result<Option<(Self::ReturnedKey, Self::ReturnedValue)>, Self::Error>;

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
    fn move_to_key(&'a mut self, key: KQ) -> Result<Option<Self::ReturnedValue>, Self::Error>;

    /// Same as [`move_to_key`][move_to_key], except that after the reposition,
    /// it retrieves the key as well as the value. Retrieving the key is often
    /// pointless, as the caller will likely already know the key given that
    /// they specified it. However, there might be cases where this function is
    /// useful.
    ///
    /// [move_to_key]: self::Cursor::move_to_key
    fn move_to_key_and_get_key(
        &'a mut self,
        key: KQ,
    ) -> Result<Option<(Self::ReturnedKey, Self::ReturnedValue)>, Self::Error>;

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
        &'a mut self,
        key: KQ,
    ) -> Result<Option<(Self::ReturnedKey, Self::ReturnedValue)>, Self::Error>;

    /// Wraps the cursor in an iterator that starts iteration from the cursor's
    /// current position. If the cursor is unpositioned, iteration will start
    /// with the first key in the database; the iteration will be empty if the
    /// database is empty and no errors occur. If the cursor has a position key,
    /// iteration will start with the first key in the database that is greater
    /// than (*not* equal to) that position key; the iteration will be empty if
    /// there is no such key and no error occurs.
    ///
    /// This trait does not specify whether or how the cursor's position state
    /// may be modified by the iterator. If you wish to use a cursor directly
    /// after it has been wrapped in an iterator, it is recommended to first
    /// reposition the cursor to a well-defined position.
    fn iter(&'a mut self) -> Result<Self::Iter, Self::Error>;

    /// Similar to [`iter`][iter], except iteration starts at the first key in
    /// the database regardless of the cursor's current position. The iteration
    /// will be empty if the database is empty and no errors occur.
    ///
    /// This trait does not specify whether or how the cursor's position state
    /// may be modified by the iterator. If you wish to use a cursor directly
    /// after it has been wrapped in an iterator, it is recommended to first
    /// reposition the cursor to a well-defined position.
    ///
    /// [iter]: self::Cursor::iter
    fn iter_start(&'a mut self) -> Result<Self::Iter, Self::Error>;

    /// Similar to [`iter`][iter], except iteration starts at the specified key
    /// regardless of the cursor's current position. More specifically,
    /// iteration will start with the first key in the database that is greater
    /// than *or* equal to the specified key. The iteration will be empty if
    /// there is no such key and no error occurs.
    ///
    /// This trait does not specify whether or how the cursor's position state
    /// may be modified by the iterator. If you wish to use a cursor directly
    /// after it has been wrapped in an iterator, it is recommended to first
    /// reposition the cursor to a well-defined position.
    ///
    /// [iter]: self::Cursor::iter
    fn iter_from(&'a mut self, key: KQ) -> Result<Self::Iter, Self::Error>;
}

/// Trait for database cursor handles that allow writing.
///
/// # Parameters
/// - `'a`: Lifetime used for `self` references. This is a workaround for the
///   lack of lifetime-generic associated types in Rust.
/// - `KQ`: Key type that can be used to point the cursor to a specific key in
///   the database.
/// - `KP`: Key type that can be used to insert an entry into the database. May
///   or may not be the same as `KQ`.
/// - `VP`: Value type that can be used to insert an entry into the database.
pub trait WriteCursor<'a, KQ, KP, VP>: Cursor<'a, KQ> {
    /// Overwrites a value in the database based on the cursor's position state,
    /// without modifying the position state. There are a few possible cases
    /// that determine the behavior:
    /// - If the cursor is unpositioned, no write is performed, and
    ///   [`Ok`][Ok]`(false)` is returned (assuming no error occurs).
    /// - If the cursor is positioned at a key that exists in the database, the
    ///   value associated with that key is overwritten. [`Ok`][Ok]`(true)` is
    ///   returned (assuming no error occurs).
    /// - If the cursor is positioned at a key that does not exist in the
    ///   database, and the database contains at least one key that is greater
    ///   than the cursor's position key, the write occurs at the first such
    ///   key. In other words, the first key in the database that is greater
    ///   than the cursor's position key gets its value overwritten.
    ///   [`Ok`][Ok]`(true)` is returned (assuming no error occurs).
    /// - If the cursor is positioned at a key that does not exist in the
    ///   database, and all keys in the database are less than the cursor's
    ///   position key, no write is performed. [`Ok`][Ok]`(false)` is returned
    ///   (assuming no error occurs).
    ///
    /// [Ok]: std::result::Result::Ok
    fn put(&'a mut self, value: VP) -> Result<bool, Self::Error>;

    /// Sets the value of the database entry with the specified key (inserting
    /// the entry if it doesn't already exist), and repositions the cursor to
    /// that key.
    fn put_and_move_to_key(&'a mut self, key: KP, value: VP) -> Result<(), Self::Error>;

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
        &'a mut self,
        key: KP,
        value: VP,
    ) -> Result<bool, Self::Error>;

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
    fn del(&'a mut self) -> Result<bool, Self::Error>;
}
