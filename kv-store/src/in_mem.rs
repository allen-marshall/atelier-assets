//! This module provides an in-memory implementation of this crate's generic
//! storage API. One of the goals of this implementation is to have minimal
//! dependencies.

use std::collections::BTreeMap;
use std::ops::Bound;
use std::sync::{Mutex, MutexGuard, RwLock};

// TODO: Currently, the implementation is very simple and naive, and probably
//  has very bad performance. I am waiting to fix that until I can set up some
//  benchmarks to measure progress in that direction.

/// Error that can be produced by storage operations.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Error {
    /// Occurs when attempting to open a database that has not been created.
    DbNotCreated,

    /// Occurs when an invalid database handle is provided.
    InvalidDb,
}

/// Database handle.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Database {
    /// For now, a database handle just holds the database name.
    id: Option<String>,
}

/// Full snapshot of the environment state.
type EnvSnapshot = BTreeMap<Option<String>, BTreeMap<Vec<u8>, Vec<u8>>>;

/// Main environment type for the in-memory storage implementation.
#[derive(Debug)]
pub struct Environment {
    /// Mutex that should be held by each root (i.e. non-nested) read-write
    /// transaction for its entire lifetime. This is to prevent the creation of
    /// concurrent root read-write transactions. The mutex should be acquired
    /// *before* any acquisition of the `master_snapshot` lock.
    root_write_txn_lock: Mutex<()>,

    /// Snapshot of the environment state. Contains all changes from committed
    /// transactions, and none from uncommitted transactions. Transactions
    /// should never acquire this lock for extended periods of time, such as a
    /// whole transaction lifetime or cursor lifetime.
    master_snapshot: RwLock<EnvSnapshot>,
}

impl crate::EnvironmentBasic for Environment {
    type Error = Error;
    type Stat = ();
    type Database = Database;
}

impl<'env> crate::Environment<'env, [u8], [u8], [u8]> for Environment {
    type RoTransaction = RoTransaction;
    type RwTransaction = RwTransaction<'env>;

    fn begin_ro_txn(&'env self) -> Result<Self::RoTransaction, Self::Error>
    where
        Self: 'env,
    {
        Ok(RoTransaction {
            snapshot: self.master_snapshot.read().unwrap().clone(),
        })
    }

    fn begin_rw_txn(&'env self) -> Result<Self::RwTransaction, Self::Error>
    where
        Self: 'env,
    {
        Ok(RwTransaction {
            root_or_child_info: RootOrChildRwTransactionInfo::Root(RootRwTransactionInfo {
                env: &self,
                root_write_txn_lock_guard: self.root_write_txn_lock.lock().unwrap(),
            }),
            nestable_txn_info: NestableTransactionInfo {
                snapshot: self.master_snapshot.read().unwrap().clone(),
            },
        })
    }
}

impl<'env, 'dbid> crate::EnvironmentExt<'env, (), Option<&'dbid str>, (), (), [u8], [u8], [u8]>
    for Environment
{
    type ReturnedDbConfig = ();

    fn new(_config: ()) -> Result<Self, Self::Error>
    where
        Self: 'env,
    {
        // The environment will start out with one unnamed open database, to
        // somewhat match the behavior of LMDB.
        let mut initial_snapshot = BTreeMap::new();
        initial_snapshot.insert(None, BTreeMap::new());

        Ok(Self {
            root_write_txn_lock: Mutex::new(()),
            master_snapshot: RwLock::new(initial_snapshot),
        })
    }

    fn open_db(&'env mut self, id: Option<&'dbid str>) -> Result<Self::Database, Self::Error>
    where
        Self: 'env,
    {
        if !self
            .master_snapshot
            .read()
            .unwrap()
            .contains_key(&id.map(ToString::to_string))
        {
            Err(Error::DbNotCreated)
        } else {
            Ok(Database {
                id: id.map(ToString::to_string),
            })
        }
    }

    fn create_db(
        &'env mut self,
        id: Option<&'dbid str>,
        _config: (),
    ) -> Result<Self::Database, Self::Error>
    where
        Self: 'env,
    {
        // Block until there are no active read-write transactions.
        let _root_write_txn_lock = self.root_write_txn_lock.lock();

        let id_string = id.map(ToString::to_string);

        let mut master_snapshot = self.master_snapshot.write().unwrap();
        if !master_snapshot.contains_key(&id_string) {
            master_snapshot.insert(id_string, BTreeMap::default());
        }
        Ok(Database {
            id: id.map(ToString::to_string),
        })
    }

    fn db_config(&'env self, db: &Self::Database) -> Result<Self::ReturnedDbConfig, Self::Error>
    where
        Self: 'env,
    {
        let master_snapshot = self.master_snapshot.read().unwrap();
        if master_snapshot.contains_key(&db.id) {
            Ok(())
        } else {
            Err(Error::InvalidDb)
        }
    }

    fn sync(&'env self, _config: ()) -> Result<(), Self::Error>
    where
        Self: 'env,
    {
        Ok(())
    }

    fn stat(&'env self) -> Result<Self::Stat, Self::Error>
    where
        Self: 'env,
    {
        Ok(())
    }
}

/// Read-only transaction type.
#[derive(Debug)]
pub struct RoTransaction {
    /// The transaction's snapshot of the environment state.
    snapshot: EnvSnapshot,
}

impl RoTransaction {
    /// Gets a reference to the transaction's snapshot contents for a specific
    /// database.
    fn snapshot_db_contents(&self, db: &Database) -> Result<&BTreeMap<Vec<u8>, Vec<u8>>, Error> {
        self.snapshot.get(&db.id).ok_or(Error::InvalidDb)
    }
}

impl crate::TransactionBasic for RoTransaction {
    type Error = Error;
    type Database = Database;
    type ReturnedKey = [u8];
    type ReturnedValue = [u8];
}

impl<'txn> crate::Transaction<'txn, [u8]> for RoTransaction {
    type ReturnedDbConfig = ();
    type ReturnedValueHandle = &'txn Vec<u8>;
    type RoCursor = RoCursor<'txn>;

    fn commit(self) -> Result<(), Self::Error>
    where
        Self: 'txn,
    {
        // Nothing to commit, since the transaction is read-only.
        Ok(())
    }

    fn get(
        &'txn self,
        db: &Self::Database,
        key: &[u8],
    ) -> Result<Option<Self::ReturnedValueHandle>, Self::Error>
    where
        Self: 'txn,
    {
        let db_contents = self.snapshot_db_contents(&db)?;
        Ok(db_contents.get(key))
    }

    fn db_config(&'txn self, db: &Self::Database) -> Result<Self::ReturnedDbConfig, Self::Error>
    where
        Self: 'txn,
    {
        if self.snapshot.contains_key(&db.id) {
            Ok(())
        } else {
            Err(Error::InvalidDb)
        }
    }

    fn open_ro_cursor(&'txn self, db: &Self::Database) -> Result<Self::RoCursor, Self::Error>
    where
        Self: 'txn,
    {
        let db_contents = self.snapshot_db_contents(&db)?;
        Ok(RoCursor {
            db_contents,
            position: None,
        })
    }
}

/// Minimum information that a read-write transaction must contain in order to
/// be nestable.
#[derive(Debug)]
struct NestableTransactionInfo {
    /// The transaction's snapshot of the environment state.
    snapshot: EnvSnapshot,
}

/// Information that only needs to be stored in root read-write transactions.
#[derive(Debug)]
struct RootRwTransactionInfo<'env> {
    /// Reference to the storage environment.
    env: &'env Environment,

    /// Mutex guard held by the transaction to prevent other root read-write
    /// transactions from being created.
    root_write_txn_lock_guard: MutexGuard<'env, ()>,
}

/// Information that only needs to be stored in non-root read-write
/// transactions.
#[derive(Debug)]
struct ChildRwTransactionInfo<'parent> {
    parent: &'parent mut NestableTransactionInfo,
}

/// Information held by a read-write transaction that is dependent on whether
/// the transaction is a root transaction or a child transaction.
#[derive(Debug)]
enum RootOrChildRwTransactionInfo<'parent> {
    /// Variant for root transactions.
    Root(RootRwTransactionInfo<'parent>),

    /// Variant for child (i.e. nested) transactions.
    Child(ChildRwTransactionInfo<'parent>),
}

/// Read-write transaction type.
#[derive(Debug)]
pub struct RwTransaction<'parent> {
    /// Information that is dependent on whether the transaction is a root
    /// transaction or a child transaction.
    root_or_child_info: RootOrChildRwTransactionInfo<'parent>,

    /// Internal state required for creating child transactions. Includes the
    /// transaction's snapshot of the environment state.
    nestable_txn_info: NestableTransactionInfo,
}

impl<'parent> RwTransaction<'parent> {
    /// Gets a reference to the transaction's snapshot contents for a specific
    /// database.
    fn snapshot_db_contents(&self, db: &Database) -> Result<&BTreeMap<Vec<u8>, Vec<u8>>, Error> {
        self.nestable_txn_info
            .snapshot
            .get(&db.id)
            .ok_or(Error::InvalidDb)
    }

    /// Gets a mutable reference to the transaction's snapshot contents for a
    /// specific database.
    fn snapshot_db_contents_mut(
        &mut self,
        db: &Database,
    ) -> Result<&mut BTreeMap<Vec<u8>, Vec<u8>>, Error> {
        self.nestable_txn_info
            .snapshot
            .get_mut(&db.id)
            .ok_or(Error::InvalidDb)
    }
}

impl<'parent> crate::TransactionBasic for RwTransaction<'parent> {
    type Error = Error;
    type Database = Database;
    type ReturnedKey = [u8];
    type ReturnedValue = [u8];
}

impl<'parent, 'txn> crate::Transaction<'txn, [u8]> for RwTransaction<'parent> {
    type ReturnedDbConfig = ();
    type ReturnedValueHandle = &'txn Vec<u8>;
    type RoCursor = RoCursor<'txn>;

    fn commit(self) -> Result<(), Self::Error>
    where
        Self: 'txn,
    {
        match self.root_or_child_info {
            RootOrChildRwTransactionInfo::Root(info) => {
                let mut master_snapshot = info.env.master_snapshot.write().unwrap();
                *master_snapshot = self.nestable_txn_info.snapshot;
            }
            RootOrChildRwTransactionInfo::Child(info) => {
                let parent_snapshot = &mut info.parent.snapshot;
                *parent_snapshot = self.nestable_txn_info.snapshot;
            }
        }
        Ok(())
    }

    fn get(
        &'txn self,
        db: &Self::Database,
        key: &[u8],
    ) -> Result<Option<Self::ReturnedValueHandle>, Self::Error>
    where
        Self: 'txn,
    {
        let db_contents = self.snapshot_db_contents(db)?;
        Ok(db_contents.get(key))
    }

    fn db_config(&'txn self, db: &Self::Database) -> Result<Self::ReturnedDbConfig, Self::Error>
    where
        Self: 'txn,
    {
        if self.nestable_txn_info.snapshot.contains_key(&db.id) {
            Ok(())
        } else {
            Err(Error::InvalidDb)
        }
    }

    fn open_ro_cursor(&'txn self, db: &Self::Database) -> Result<Self::RoCursor, Self::Error>
    where
        Self: 'txn,
    {
        let db_contents = self.snapshot_db_contents(db)?;
        Ok(RoCursor {
            db_contents,
            position: None,
        })
    }
}

impl<'parent, 'txn> crate::ReadWriteTransaction<'txn, [u8], [u8], [u8]> for RwTransaction<'parent> {
    type RwCursor = RwCursor<'txn>;
    type Nested = RwTransaction<'txn>;

    fn put(&'txn mut self, db: &Self::Database, key: &[u8], value: &[u8]) -> Result<(), Self::Error>
    where
        Self: 'txn,
    {
        let db_contents = self.snapshot_db_contents_mut(db)?;
        db_contents.insert(key.to_vec(), value.to_vec());
        Ok(())
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
        let db_contents = self.snapshot_db_contents_mut(db)?;
        let db_entry = db_contents.entry(key.to_vec());
        match db_entry {
            std::collections::btree_map::Entry::Vacant(entry) => {
                entry.insert(value.to_vec());
                Ok(true)
            }
            _ => Ok(false),
        }
    }

    fn del(&'txn mut self, db: &Self::Database, key: &[u8]) -> Result<bool, Self::Error>
    where
        Self: 'txn,
    {
        let db_contents = self.snapshot_db_contents_mut(db)?;
        Ok(db_contents.remove(key).is_some())
    }

    fn clear_db(&'txn mut self, db: &Self::Database) -> Result<(), Self::Error>
    where
        Self: 'txn,
    {
        let db_contents = self.snapshot_db_contents_mut(db)?;
        db_contents.clear();
        Ok(())
    }

    fn open_rw_cursor(&'txn mut self, db: &Self::Database) -> Result<Self::RwCursor, Self::Error>
    where
        Self: 'txn,
    {
        let db_contents = self.snapshot_db_contents_mut(db)?;
        Ok(RwCursor {
            db_contents,
            position: None,
        })
    }

    fn begin_nested_txn(&'txn mut self) -> Result<Self::Nested, Self::Error>
    where
        Self: 'txn,
    {
        let child_snapshot = self.nestable_txn_info.snapshot.clone();
        Ok(RwTransaction {
            root_or_child_info: RootOrChildRwTransactionInfo::Child(ChildRwTransactionInfo {
                parent: &mut self.nestable_txn_info,
            }),
            nestable_txn_info: NestableTransactionInfo {
                snapshot: child_snapshot,
            },
        })
    }
}

/// Data handle returned by cursor operations.
#[derive(Debug)]
pub struct CursorReturnedDataHandle<'cursor>(&'cursor [u8]);

// This trait impl should be safe, because we only ever construct
// CursorReturnedDataHandles using references that will remain valid until the
// transaction is finalized or used for mutation.
unsafe impl<'cursor> crate::CursorReturnedDataHandle<'cursor, [u8]>
    for CursorReturnedDataHandle<'cursor>
{
    fn get(&self) -> &'cursor [u8] {
        self.0
    }
}

/// Read-only cursor.
#[derive(Debug)]
pub struct RoCursor<'txn> {
    /// Contents of the database associated with the cursor, within the
    /// associated transaction's snapshot of the environment.
    db_contents: &'txn BTreeMap<Vec<u8>, Vec<u8>>,

    /// Cursor's current position. The cursor may be unpositioned, or may be
    /// positioned at a specific key (which may or may not exist in the
    /// database).
    position: Option<Vec<u8>>,
}

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
        if let Some(pos_key) = &self.position {
            if let Some((key, value)) = self.db_contents.get_key_value(pos_key) {
                Ok(Some((
                    CursorReturnedDataHandle(&key),
                    CursorReturnedDataHandle(&value),
                )))
            } else {
                Ok(None)
            }
        } else {
            Ok(None)
        }
    }

    fn move_to_first(
        &'cursor mut self,
    ) -> Result<Option<(Self::ReturnedKeyHandle, Self::ReturnedValueHandle)>, Self::Error>
    where
        Self: 'cursor,
    {
        if let Some((key, value)) = self.db_contents.iter().next() {
            self.position = Some(key.clone());
            Ok(Some((
                CursorReturnedDataHandle(&key),
                CursorReturnedDataHandle(&value),
            )))
        } else {
            Ok(None)
        }
    }

    fn move_to_last(
        &'cursor mut self,
    ) -> Result<Option<(Self::ReturnedKeyHandle, Self::ReturnedValueHandle)>, Self::Error>
    where
        Self: 'cursor,
    {
        if let Some((key, value)) = self.db_contents.iter().next_back() {
            self.position = Some(key.clone());
            Ok(Some((
                CursorReturnedDataHandle(&key),
                CursorReturnedDataHandle(&value),
            )))
        } else {
            Ok(None)
        }
    }

    fn move_to_next(
        &'cursor mut self,
    ) -> Result<Option<(Self::ReturnedKeyHandle, Self::ReturnedValueHandle)>, Self::Error>
    where
        Self: 'cursor,
    {
        if let Some(pos_key) = &self.position {
            if let Some((key, value)) = self
                .db_contents
                .range::<Vec<u8>, _>((Bound::Excluded(pos_key), Bound::Unbounded))
                .next()
            {
                self.position = Some(key.clone());
                Ok(Some((
                    CursorReturnedDataHandle(&key),
                    CursorReturnedDataHandle(&value),
                )))
            } else {
                Ok(None)
            }
        } else {
            self.move_to_first()
        }
    }

    fn move_to_prev(
        &'cursor mut self,
    ) -> Result<Option<(Self::ReturnedKeyHandle, Self::ReturnedValueHandle)>, Self::Error>
    where
        Self: 'cursor,
    {
        if let Some(pos_key) = &self.position {
            if let Some((key, value)) = self.db_contents.range::<Vec<u8>, _>(..pos_key).next_back()
            {
                self.position = Some(key.clone());
                Ok(Some((
                    CursorReturnedDataHandle(&key),
                    CursorReturnedDataHandle(&value),
                )))
            } else {
                Ok(None)
            }
        } else {
            self.move_to_last()
        }
    }

    fn move_to_key(
        &'cursor mut self,
        key: &[u8],
    ) -> Result<Option<Self::ReturnedValueHandle>, Self::Error>
    where
        Self: 'cursor,
    {
        if let Some((key, value)) = self.db_contents.get_key_value(key) {
            self.position = Some(key.clone());
            Ok(Some(CursorReturnedDataHandle(&value)))
        } else {
            Ok(None)
        }
    }

    fn move_to_key_and_get_key(
        &'cursor mut self,
        key: &[u8],
    ) -> Result<Option<(Self::ReturnedKeyHandle, Self::ReturnedValueHandle)>, Self::Error>
    where
        Self: 'cursor,
    {
        if let Some((key, value)) = self.db_contents.get_key_value(key) {
            self.position = Some(key.clone());
            Ok(Some((
                CursorReturnedDataHandle(&key),
                CursorReturnedDataHandle(&value),
            )))
        } else {
            Ok(None)
        }
    }

    fn move_to_key_or_after(
        &'cursor mut self,
        key: &[u8],
    ) -> Result<Option<(Self::ReturnedKeyHandle, Self::ReturnedValueHandle)>, Self::Error>
    where
        Self: 'cursor,
    {
        if let Some((key, value)) = self
            .db_contents
            .range::<[u8], _>((Bound::Included(key), Bound::Unbounded))
            .next()
        {
            self.position = Some(key.clone());
            Ok(Some((
                CursorReturnedDataHandle(&key),
                CursorReturnedDataHandle(&value),
            )))
        } else {
            Ok(None)
        }
    }
}

/// Read-write cursor.
#[derive(Debug)]
pub struct RwCursor<'txn> {
    /// Contents of the database associated with the cursor, within the
    /// associated transaction's snapshot of the environment.
    db_contents: &'txn mut BTreeMap<Vec<u8>, Vec<u8>>,

    /// Cursor's current position. The cursor may be unpositioned, or may be
    /// positioned at a specific key (which may or may not exist in the
    /// database).
    position: Option<Vec<u8>>,
}

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
        if let Some(pos_key) = &self.position {
            if let Some((key, value)) = self.db_contents.get_key_value(pos_key) {
                Ok(Some((
                    CursorReturnedDataHandle(&key),
                    CursorReturnedDataHandle(&value),
                )))
            } else {
                Ok(None)
            }
        } else {
            Ok(None)
        }
    }

    fn move_to_first(
        &'cursor mut self,
    ) -> Result<Option<(Self::ReturnedKeyHandle, Self::ReturnedValueHandle)>, Self::Error>
    where
        Self: 'cursor,
    {
        if let Some((key, value)) = self.db_contents.iter().next() {
            self.position = Some(key.clone());
            Ok(Some((
                CursorReturnedDataHandle(&key),
                CursorReturnedDataHandle(&value),
            )))
        } else {
            Ok(None)
        }
    }

    fn move_to_last(
        &'cursor mut self,
    ) -> Result<Option<(Self::ReturnedKeyHandle, Self::ReturnedValueHandle)>, Self::Error>
    where
        Self: 'cursor,
    {
        if let Some((key, value)) = self.db_contents.iter().next_back() {
            self.position = Some(key.clone());
            Ok(Some((
                CursorReturnedDataHandle(&key),
                CursorReturnedDataHandle(&value),
            )))
        } else {
            Ok(None)
        }
    }

    fn move_to_next(
        &'cursor mut self,
    ) -> Result<Option<(Self::ReturnedKeyHandle, Self::ReturnedValueHandle)>, Self::Error>
    where
        Self: 'cursor,
    {
        if let Some(pos_key) = &self.position {
            if let Some((key, value)) = self
                .db_contents
                .range::<Vec<u8>, _>((Bound::Excluded(pos_key), Bound::Unbounded))
                .next()
            {
                self.position = Some(key.clone());
                Ok(Some((
                    CursorReturnedDataHandle(&key),
                    CursorReturnedDataHandle(&value),
                )))
            } else {
                Ok(None)
            }
        } else {
            self.move_to_first()
        }
    }

    fn move_to_prev(
        &'cursor mut self,
    ) -> Result<Option<(Self::ReturnedKeyHandle, Self::ReturnedValueHandle)>, Self::Error>
    where
        Self: 'cursor,
    {
        if let Some(pos_key) = &self.position {
            if let Some((key, value)) = self.db_contents.range::<Vec<u8>, _>(..pos_key).next_back()
            {
                self.position = Some(key.clone());
                Ok(Some((
                    CursorReturnedDataHandle(&key),
                    CursorReturnedDataHandle(&value),
                )))
            } else {
                Ok(None)
            }
        } else {
            self.move_to_last()
        }
    }

    fn move_to_key(
        &'cursor mut self,
        key: &[u8],
    ) -> Result<Option<Self::ReturnedValueHandle>, Self::Error>
    where
        Self: 'cursor,
    {
        if let Some((key, value)) = self.db_contents.get_key_value(key) {
            self.position = Some(key.clone());
            Ok(Some(CursorReturnedDataHandle(&value)))
        } else {
            Ok(None)
        }
    }

    fn move_to_key_and_get_key(
        &'cursor mut self,
        key: &[u8],
    ) -> Result<Option<(Self::ReturnedKeyHandle, Self::ReturnedValueHandle)>, Self::Error>
    where
        Self: 'cursor,
    {
        if let Some((key, value)) = self.db_contents.get_key_value(key) {
            self.position = Some(key.clone());
            Ok(Some((
                CursorReturnedDataHandle(&key),
                CursorReturnedDataHandle(&value),
            )))
        } else {
            Ok(None)
        }
    }

    fn move_to_key_or_after(
        &'cursor mut self,
        key: &[u8],
    ) -> Result<Option<(Self::ReturnedKeyHandle, Self::ReturnedValueHandle)>, Self::Error>
    where
        Self: 'cursor,
    {
        if let Some((key, value)) = self
            .db_contents
            .range::<[u8], _>((Bound::Included(key), Bound::Unbounded))
            .next()
        {
            self.position = Some(key.clone());
            Ok(Some((
                CursorReturnedDataHandle(&key),
                CursorReturnedDataHandle(&value),
            )))
        } else {
            Ok(None)
        }
    }
}

impl<'txn, 'cursor> crate::ReadWriteCursor<'cursor, [u8], [u8], [u8]> for RwCursor<'txn> {
    fn put_and_move_to_key(&'cursor mut self, key: &[u8], value: &[u8]) -> Result<(), Self::Error>
    where
        Self: 'cursor,
    {
        self.db_contents.insert(key.to_vec(), value.to_vec());
        self.position = Some(key.to_vec());
        Ok(())
    }

    fn put_no_overwrite_and_move_to_key(
        &'cursor mut self,
        key: &[u8],
        value: &[u8],
    ) -> Result<bool, Self::Error>
    where
        Self: 'cursor,
    {
        let entry = self.db_contents.entry(key.to_vec());
        let output = match entry {
            std::collections::btree_map::Entry::Vacant(entry) => {
                entry.insert(value.to_vec());
                Ok(true)
            }
            _ => Ok(false),
        };
        self.position = Some(key.to_vec());
        output
    }

    fn del(&'cursor mut self) -> Result<bool, Self::Error>
    where
        Self: 'cursor,
    {
        if let Some(pos_key) = &self.position {
            Ok(self.db_contents.remove(pos_key).is_some())
        } else {
            Ok(false)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Basic test that performs several operations and makes sure they don't
    /// return errors except when expected.
    #[test]
    fn basic_error_test() {
        crate::test_util::binary_static_env::basic_error_test::<Environment, _, _, _>((), ());
    }

    /// Basic test that creates an empty storage environment, writes some data
    /// to it, then makes sure it can read the data back.
    #[test]
    fn basic_read_write_test() {
        let mut env: Environment = crate::EnvironmentExt::new(()).unwrap();
        crate::test_util::binary_static_env::basic_read_write_test(&mut env, ());
    }
}
