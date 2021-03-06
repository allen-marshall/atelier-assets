//! Utilities for testing storage implementations where the storage environment
//! is `'static` and the keys and values are byte strings.

use crate::iter::CursorIter;
use crate::{CursorReturnedDataHandle, EnvironmentExt, ReadWriteTransaction, Transaction};
use atelier_kv_store_proc_macros::{
    require_binary_cursor, require_binary_rw_cursor, require_binary_rw_txn,
    require_binary_static_env, require_binary_static_env_ext, require_binary_txn,
};
use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Debug;

/// A "snapshot" of a database's contents. Contains information about the set of
/// data entries that are expected to be present in the database at some point
/// in time, within some transaction's view.
pub(crate) struct DbTestSnapshot {
    /// Key-value entries that are expected to be in the database.
    present_entries: BTreeMap<Vec<u8>, Vec<u8>>,

    /// Optional set of suggested test keys that shouldn't be in the database.
    absent_test_keys: BTreeSet<Vec<u8>>,
}

impl DbTestSnapshot {
    /// Constructor.
    ///
    /// # Parameters
    /// - `present_entries`: Specifies all key-value entries that are expected
    ///   to be in the database.
    /// - `absent_test_keys`: Optional set of suggested test keys that shouldn't
    ///   be in the database.
    ///
    /// # Panics
    /// Panics if `absent_test_keys` overlaps with the set of keys in
    /// `present_entries`.
    pub(crate) fn new(
        present_entries: BTreeMap<Vec<u8>, Vec<u8>>,
        absent_test_keys: BTreeSet<Vec<u8>>,
    ) -> Self {
        if !absent_test_keys.is_disjoint(&present_entries.keys().map(|key| key.to_vec()).collect())
        {
            panic!("One of the suggested absent test keys was actually present in the set of expected keys.");
        }
        Self {
            present_entries,
            absent_test_keys,
        }
    }

    /// Gets the set of key-value entries that are expected to be in the
    /// database.
    pub(crate) fn present_entries(&self) -> &BTreeMap<Vec<u8>, Vec<u8>> {
        &self.present_entries
    }

    /// Gets an optional set of suggested test keys that shouldn't be in the
    /// database.
    pub(crate) fn absent_test_keys(&self) -> &BTreeSet<Vec<u8>> {
        &self.absent_test_keys
    }
}

/// A "snapshot" of an environment's database contents.
///
/// # Parameters
/// - `DB`: Type that represents a database.
pub(crate) type EnvTestSnapshot<DB> = BTreeMap<DB, DbTestSnapshot>;

/// Represents the ways in which a transaction can be finalized. This can be
/// used as a parameter to reduce duplication of testing code.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) enum TxnFinalizeMode {
    /// Commit transaction.
    Commit,

    /// Abort transaction by calling [`abort`][abort] explicitly.
    ///
    /// [abort]: crate::Transaction::abort
    Abort,

    /// Abort transaction by dropping transaction handle.
    Drop,
}

impl TxnFinalizeMode {
    /// Finalizes a transaction according to the mode represented by `self`.
    pub(crate) fn finalize_txn<T, KQ: ?Sized>(self, txn: T) -> Result<(), T::Error>
    where
        for<'txn> T: Transaction<'txn, KQ>,
    {
        match self {
            TxnFinalizeMode::Commit => txn.commit(),
            TxnFinalizeMode::Abort => Ok(txn.abort()),
            TxnFinalizeMode::Drop => Ok(std::mem::drop(txn)),
        }
    }
}

/// Tests read functionality of a newly created transaction, given that the
/// transaction's view of the environment is expected to have the specified
/// contents.
///
/// # Panics
/// Panics if a database operation returns an unexpected error or incorrect
/// data.
#[require_binary_txn(T, crate)]
pub(crate) fn test_txn_read<T>(txn: &T, env_contents: &EnvTestSnapshot<T::Database>)
where
    T::Error: Debug,
{
    // Test basic reading.
    for (db, snapshot) in env_contents {
        for (key, value) in snapshot.present_entries() {
            let returned_value = txn.get(db, key.as_ref()).unwrap().unwrap();
            assert_eq!(
                returned_value.as_ref().as_ref(),
                AsRef::<[u8]>::as_ref(value)
            );
        }
        for absent_key in snapshot.absent_test_keys() {
            assert!(txn.get(db, absent_key.as_ref()).unwrap().is_none());
        }
    }

    // Test read-only cursors.
    for (db, snapshot) in env_contents {
        let mut cursor = txn.open_ro_cursor(db).unwrap();
        test_cursor_read(&mut cursor, snapshot);
    }
}

/// Tests read functionality of a newly created transaction, given that the
/// transaction's view of the environment is expected to have the specified
/// contents. Finalizes the transaction after testing.
///
/// # Panics
/// Panics if a database operation returns an unexpected error or incorrect
/// data.
#[require_binary_txn(T, crate)]
pub(crate) fn test_txn_read_and_finalize<T>(
    txn: T,
    env_contents: &EnvTestSnapshot<T::Database>,
    finalize_mode: TxnFinalizeMode,
) where
    T::Error: Debug,
{
    test_txn_read(&txn, env_contents);
    finalize_mode.finalize_txn(txn).unwrap();
}

/// Tests read functionality of a newly created cursor, given that the cursor's
/// associated database is expected to have the specified contents.
///
/// # Panics
/// Panics if a database operation returns an unexpected error or incorrect
/// data.
#[require_binary_cursor(C, crate)]
pub(crate) fn test_cursor_read<C>(cursor: &mut C, db_contents: &DbTestSnapshot)
where
    C::Error: Debug,
{
    let db_contents_vec: Vec<_> = db_contents.present_entries().clone().into_iter().collect();

    // The cursor is assumed to be in its initial unpositioned state, so it
    // shouldn't return any data at first when we call get.
    assert!(cursor.get().unwrap().is_none());

    // Test basic functionality of move_to_first, move_to_last, and get.
    if db_contents_vec.is_empty() {
        assert!(cursor.move_to_first().unwrap().is_none());
        assert!(cursor.move_to_last().unwrap().is_none());
    } else {
        let (first_key, first_value) = cursor.move_to_first().unwrap().unwrap();
        assert_eq!(
            first_key.get().as_ref(),
            AsRef::<[u8]>::as_ref(&db_contents_vec[0].0)
        );
        assert_eq!(
            first_value.get().as_ref(),
            AsRef::<[u8]>::as_ref(&db_contents_vec[0].1)
        );
        std::mem::drop((first_key, first_value));

        let (get_first_key, get_first_value) = cursor.get().unwrap().unwrap();
        assert_eq!(
            get_first_key.get().as_ref(),
            AsRef::<[u8]>::as_ref(&db_contents_vec[0].0)
        );
        assert_eq!(
            get_first_value.get().as_ref(),
            AsRef::<[u8]>::as_ref(&db_contents_vec[0].1)
        );
        std::mem::drop((get_first_key, get_first_value));

        let (last_key, last_value) = cursor.move_to_last().unwrap().unwrap();
        assert_eq!(
            last_key.get().as_ref(),
            AsRef::<[u8]>::as_ref(&db_contents_vec[db_contents_vec.len() - 1].0)
        );
        assert_eq!(
            last_value.get().as_ref(),
            AsRef::<[u8]>::as_ref(&db_contents_vec[db_contents_vec.len() - 1].1)
        );
        std::mem::drop((last_key, last_value));

        let (get_last_key, get_last_value) = cursor.get().unwrap().unwrap();
        assert_eq!(
            get_last_key.get().as_ref(),
            AsRef::<[u8]>::as_ref(&db_contents_vec[db_contents_vec.len() - 1].0)
        );
        assert_eq!(
            get_last_value.get().as_ref(),
            AsRef::<[u8]>::as_ref(&db_contents_vec[db_contents_vec.len() - 1].1)
        );
    }

    // Test basic functionality of move_to_next.
    if !db_contents_vec.is_empty() {
        cursor.move_to_first().unwrap();
        let mut idx = 0usize;
        while idx + 1 < db_contents_vec.len() {
            let (next_key, next_value) = cursor.move_to_next().unwrap().unwrap();
            idx += 1;
            assert_eq!(
                next_key.get().as_ref(),
                AsRef::<[u8]>::as_ref(&db_contents_vec[idx].0)
            );
            assert_eq!(
                next_value.get().as_ref(),
                AsRef::<[u8]>::as_ref(&db_contents_vec[idx].1)
            );
        }
        assert!(cursor.move_to_next().unwrap().is_none());
    }

    // Test basic functionality of move_to_prev.
    if !db_contents_vec.is_empty() {
        cursor.move_to_last().unwrap();
        let mut idx = db_contents_vec.len() - 1;
        while idx > 0 {
            let (prev_key, prev_value) = cursor.move_to_prev().unwrap().unwrap();
            idx -= 1;
            assert_eq!(
                prev_key.get().as_ref(),
                AsRef::<[u8]>::as_ref(&db_contents_vec[idx].0)
            );
            assert_eq!(
                prev_value.get().as_ref(),
                AsRef::<[u8]>::as_ref(&db_contents_vec[idx].1)
            );
        }
        assert!(cursor.move_to_prev().unwrap().is_none());
    }

    // Test basic functionality of move_to_key.
    for (key, value) in &db_contents_vec {
        let returned_value = cursor.move_to_key(key.as_ref()).unwrap().unwrap();
        assert_eq!(returned_value.get().as_ref(), AsRef::<[u8]>::as_ref(&value));
    }
    for absent_key in db_contents.absent_test_keys() {
        assert!(cursor.move_to_key(absent_key).unwrap().is_none());
    }

    // Test basic functionality of move_to_key_and_get_key.
    for (key, value) in &db_contents_vec {
        let (returned_key, returned_value) = cursor
            .move_to_key_and_get_key(key.as_ref())
            .unwrap()
            .unwrap();
        assert_eq!(returned_key.get().as_ref(), AsRef::<[u8]>::as_ref(&key));
        assert_eq!(returned_value.get().as_ref(), AsRef::<[u8]>::as_ref(&value));
    }
    for absent_key in db_contents.absent_test_keys() {
        assert!(cursor
            .move_to_key_and_get_key(absent_key.as_ref())
            .unwrap()
            .is_none());
    }

    // Test basic functionality of move_to_key_or_after.
    for (key, value) in &db_contents_vec {
        let (returned_key, returned_value) =
            cursor.move_to_key_or_after(key.as_ref()).unwrap().unwrap();
        assert_eq!(returned_key.get().as_ref(), AsRef::<[u8]>::as_ref(&key));
        assert_eq!(returned_value.get().as_ref(), AsRef::<[u8]>::as_ref(&value));
    }
    for absent_key in db_contents.absent_test_keys() {
        let expected_idx = db_contents_vec
            .binary_search_by_key(&absent_key, |(key, _)| key)
            .unwrap_err();
        if expected_idx >= db_contents_vec.len() {
            assert!(cursor
                .move_to_key_or_after(absent_key.as_ref())
                .unwrap()
                .is_none());
        } else {
            let (returned_key, returned_value) = cursor
                .move_to_key_or_after(absent_key.as_ref())
                .unwrap()
                .unwrap();
            assert_eq!(
                returned_key.get().as_ref(),
                AsRef::<[u8]>::as_ref(&db_contents_vec[expected_idx].0)
            );
            assert_eq!(
                returned_value.get().as_ref(),
                AsRef::<[u8]>::as_ref(&db_contents_vec[expected_idx].1)
            );
        }
    }

    // Test iteration functionality starting from the first key.
    let iter = CursorIter::iter_start(cursor).unwrap();
    let iter_output: Vec<_> = iter
        .map(|result| result.unwrap())
        .map(|(key, value)| (key.as_ref().to_vec(), value.as_ref().to_vec()))
        .collect();
    assert_eq!(iter_output, db_contents_vec);

    // Test iteration functionality starting from the current key.
    for idx in 0..db_contents_vec.len() {
        cursor.move_to_key(db_contents_vec[idx].0.as_ref()).unwrap();
        let iter = CursorIter::iter(cursor).unwrap();
        let iter_output: Vec<_> = iter
            .map(|result| result.unwrap())
            .map(|(key, value)| (key.as_ref().to_vec(), value.as_ref().to_vec()))
            .collect();
        assert_eq!(iter_output, db_contents_vec[(idx + 1)..].to_vec());
    }

    // Test iteration functionality starting from a specified key.
    for idx in 0..db_contents_vec.len() {
        let iter = CursorIter::iter_from(cursor, db_contents_vec[idx].0.as_ref()).unwrap();
        let iter_output: Vec<_> = iter
            .map(|result| result.unwrap())
            .map(|(key, value)| (key.as_ref().to_vec(), value.as_ref().to_vec()))
            .collect();
        assert_eq!(iter_output, db_contents_vec[idx..].to_vec());
    }
    for absent_key in db_contents.absent_test_keys() {
        let expected_idx = db_contents_vec
            .binary_search_by_key(&absent_key, |(key, _)| key)
            .unwrap_err();
        let iter = CursorIter::iter_from(cursor, absent_key.as_ref()).unwrap();
        let iter_output: Vec<_> = iter
            .map(|result| result.unwrap())
            .map(|(key, value)| (key.as_ref().to_vec(), value.as_ref().to_vec()))
            .collect();
        assert_eq!(iter_output, db_contents_vec[expected_idx..].to_vec());
    }
}

/// Converts an environment snapshot with databases represented by database
/// name strings into an equivalent snapshot with databases represented by
/// active database handles. The databases mentioned in the snapshot are
/// created in the storage environment using the specified database
/// configuration.
///
/// # Parameters
/// - `E`: Storage environment type.
/// - `EC`: Environment configuration type.
/// - `DC`: Database configuration type.
/// - `SC`: Environment sync configuration type.
///
/// # Panics
/// Panics if the storage environment returns an unexpected error.
#[require_binary_static_env_ext(E, EC, DC, SC, crate)]
pub(crate) fn create_dbs_for_snapshot<E, EC, DC, SC>(
    env: &mut E,
    snapshot: EnvTestSnapshot<Option<&str>>,
    db_cfg: DC,
) -> EnvTestSnapshot<E::Database>
where
    DC: Clone,
    E::Error: Debug,
    E::Database: Ord,
{
    let mut output = BTreeMap::new();
    for (db_id, db_contents) in snapshot.into_iter() {
        let db_handle = env.create_db(db_id, db_cfg.clone()).unwrap();
        output.insert(db_handle, db_contents);
    }
    output
}

/// Tests that the specified environment contains all the key-value pairs
/// mentioned in the given snapshot, and no other key-value pairs.
///
/// # Parameters
/// - `E`: Storage environment type.
/// - `EC`: Environment configuration type.
/// - `DC`: Database configuration type.
/// - `SC`: Environment sync configuration type.
///
/// # Panics
/// Panics if the storage environment returns an unexpected error, or if the
/// environment contents do not match the snapshot.
#[require_binary_static_env(E, crate)]
pub(crate) fn test_db_contents_equal<E>(env: &E, expected: &EnvTestSnapshot<E::Database>)
where
    E::Error: Debug,
    E::Database: Ord,
{
    // Test that we can retrieve the expected contents through a read-only
    // transaction.
    test_txn_read_and_finalize(
        env.begin_ro_txn().unwrap(),
        expected,
        TxnFinalizeMode::Commit,
    );
    test_txn_read_and_finalize(
        env.begin_ro_txn().unwrap(),
        expected,
        TxnFinalizeMode::Abort,
    );
    test_txn_read_and_finalize(env.begin_ro_txn().unwrap(), expected, TxnFinalizeMode::Drop);

    // Test that we can retrieve the expected contents through a read-write
    // transaction.
    test_txn_read_and_finalize(
        env.begin_rw_txn().unwrap(),
        expected,
        TxnFinalizeMode::Commit,
    );
    test_txn_read_and_finalize(
        env.begin_rw_txn().unwrap(),
        expected,
        TxnFinalizeMode::Abort,
    );
    test_txn_read_and_finalize(env.begin_rw_txn().unwrap(), expected, TxnFinalizeMode::Drop);
}

/// Inserts all the key-value pairs from the specified snapshot into the
/// given storage environment.
///
/// # Parameters
/// - `E`: Storage environment type.
/// - `EC`: Environment configuration type.
/// - `DC`: Database configuration type.
/// - `SC`: Environment sync configuration type.
///
/// # Panics
/// Panics if the storage environment returns an unexpected error.
#[require_binary_static_env(E, crate)]
pub(crate) fn add_db_contents<E>(env: &mut E, contents_to_add: &EnvTestSnapshot<E::Database>)
where
    E::Error: Debug,
    E::Database: Ord,
{
    let mut rw_txn = env.begin_rw_txn().unwrap();
    for (db, db_contents_to_add) in contents_to_add.iter() {
        for (key, value) in db_contents_to_add.present_entries() {
            rw_txn.put(db, key.as_ref(), value.as_ref()).unwrap();
        }
    }
    rw_txn.commit().unwrap()
}

/// Performs some basic operations on a storage environment, and makes sure
/// they return errors when and only when expected. This function is mostly
/// concerned with the presence or absence of [`Err`][Err] return values,
/// rather than full correctness of returned data.
///
/// # Parameters
/// - `E`: Storage environment type.
/// - `EC`: Environment configuration type.
/// - `DC`: Database configuration type.
/// - `SC`: Environment sync configuration type.
///
/// # Panics
/// Panics if the storage environment returns an unexpected error, or fails
/// to return an error where one is expected.
///
/// [Err]: std::result::Result::Err
#[require_binary_static_env_ext(E, EC, DC, SC, crate)]
pub(crate) fn basic_error_test<E, EC, DC, SC>(env_cfg: EC, db_cfg: DC)
where
    E::Error: Debug,
    E::Database: Debug,
{
    #[require_binary_cursor(C, crate)]
    fn cursor_iter_test<C>(iter: &mut CursorIter<C, [u8]>)
    where
        C::Error: Debug,
    {
        for result in iter {
            result.unwrap();
        }
    }

    #[require_binary_cursor(C, crate)]
    fn ro_cursor_test<C>(cursor: &mut C)
    where
        C::Error: Debug,
    {
        cursor.get().unwrap();
        cursor.move_to_first().unwrap();
        cursor.move_to_last().unwrap();
        cursor.move_to_next().unwrap();
        cursor.move_to_prev().unwrap();
        cursor.move_to_key(b"test_key").unwrap();
        cursor.move_to_key_and_get_key(b"test_key").unwrap();
        cursor.move_to_key_or_after(b"test_key").unwrap();
        cursor_iter_test(&mut CursorIter::iter(cursor).unwrap());
        cursor_iter_test(&mut CursorIter::iter_start(cursor).unwrap());
        cursor_iter_test(&mut CursorIter::iter_from(cursor, b"test_key").unwrap());
    }

    #[require_binary_rw_cursor(C, crate)]
    fn rw_cursor_test<C>(cursor: &mut C)
    where
        C::Error: Debug,
    {
        ro_cursor_test(cursor);
        cursor
            .put_and_move_to_key(b"test_key", b"test_value")
            .unwrap();
        cursor
            .put_no_overwrite_and_move_to_key(b"test_key", b"test_value")
            .unwrap();
        cursor.del().unwrap();
    }

    #[require_binary_txn(T, crate)]
    fn ro_txn_test<T>(txn: &mut T, db: &T::Database)
    where
        T::Error: Debug,
    {
        txn.db_config(&db).unwrap();
        txn.get(db, b"test_key").unwrap();
        ro_cursor_test(&mut txn.open_ro_cursor(db).unwrap());
    }

    #[require_binary_txn(T, crate)]
    fn ro_txn_finalizing_test<T>(mut txn: T, db: &T::Database, finalize_mode: TxnFinalizeMode)
    where
        T::Error: Debug,
    {
        ro_txn_test(&mut txn, db);
        finalize_mode.finalize_txn(txn).unwrap();
    }

    #[require_binary_rw_txn(T, crate)]
    fn rw_txn_test<T>(txn: &mut T, db: &T::Database, nest_levels: usize)
    where
        T::Error: Debug,
    {
        ro_txn_test(txn, db);
        txn.put(db, b"test_key", b"test_value").unwrap();
        txn.put_no_overwrite(db, b"test_key", b"test_value")
            .unwrap();
        txn.del(db, b"test_key").unwrap();
        txn.clear_db(db).unwrap();
        rw_cursor_test(&mut txn.open_rw_cursor(db).unwrap());

        if nest_levels > 0 {
            rw_txn_finalizing_test(
                txn.begin_nested_txn().unwrap(),
                db,
                nest_levels - 1,
                TxnFinalizeMode::Commit,
            );
            rw_txn_finalizing_test(
                txn.begin_nested_txn().unwrap(),
                db,
                nest_levels - 1,
                TxnFinalizeMode::Abort,
            );
            rw_txn_finalizing_test(
                txn.begin_nested_txn().unwrap(),
                db,
                nest_levels - 1,
                TxnFinalizeMode::Drop,
            );
        }
    }

    #[require_binary_rw_txn(T, crate)]
    fn rw_txn_finalizing_test<T>(
        mut txn: T,
        db: &T::Database,
        nest_levels: usize,
        finalize_mode: TxnFinalizeMode,
    ) where
        T::Error: Debug,
    {
        rw_txn_test(&mut txn, db, nest_levels);
        finalize_mode.finalize_txn(txn).unwrap();
    }

    // Test environment management operations.
    let mut env: E = EnvironmentExt::new(env_cfg).unwrap();
    env.stat().unwrap();
    let db = env.create_db(Some("test_db"), db_cfg).unwrap();
    env.open_db(Some("nonexistent_db")).unwrap_err();
    env.db_config(&db).unwrap();

    // Test read-only transaction operations.
    ro_txn_finalizing_test(env.begin_ro_txn().unwrap(), &db, TxnFinalizeMode::Commit);
    ro_txn_finalizing_test(env.begin_ro_txn().unwrap(), &db, TxnFinalizeMode::Abort);
    ro_txn_finalizing_test(env.begin_ro_txn().unwrap(), &db, TxnFinalizeMode::Drop);

    // Test read-write transaction operations.
    rw_txn_finalizing_test(
        env.begin_rw_txn().unwrap(),
        &db,
        10,
        TxnFinalizeMode::Commit,
    );
    rw_txn_finalizing_test(env.begin_rw_txn().unwrap(), &db, 10, TxnFinalizeMode::Abort);
    rw_txn_finalizing_test(env.begin_rw_txn().unwrap(), &db, 10, TxnFinalizeMode::Drop);
}

/// A simple test that writes some data into an initially empty storage
/// environment, then reads the data back and checks that it matches what
/// was written.
///
/// # Parameters
/// - `E`: Storage environment type.
/// - `EC`: Environment configuration type.
/// - `DC`: Database configuration type.
/// - `SC`: Environment sync configuration type.
///
/// # Panics
/// Panics if the storage environment returns an unexpected error, or if
/// reading the database after the data insertions does not yield the
/// expected results.
#[require_binary_static_env_ext(E, EC, DC, SC, crate)]
pub(crate) fn basic_read_write_test<E, EC, DC, SC>(env: &mut E, db_cfg: DC)
where
    DC: Clone,
    E::Error: Debug,
    E::Database: Ord,
{
    // Make some test data.

    let db_0_contents: BTreeMap<_, _> = vec![
        (b"Respond with space.".to_vec(), b" ".to_vec()),
        (b"Is this the default database?".to_vec(), b"yes".to_vec()),
        (b"Is it being used for testing?".to_vec(), b"yes".to_vec()),
        (b"What is stored in it?".to_vec(), b"data".to_vec()),
    ]
    .into_iter()
    .collect();
    let db_0_absent_keys: BTreeSet<_> = vec![
        (b"Don't insert this key.".to_vec()),
        (b"What could happen if this key is inserted?".to_vec()),
    ]
    .into_iter()
    .collect();

    let db_1_contents: BTreeMap<_, _> = vec![
        (b" ".to_vec(), b"Space".to_vec()),
        (b"2 + 2".to_vec(), b"4".to_vec()),
    ]
    .into_iter()
    .collect();
    let db_1_absent_keys: BTreeSet<_> =
        vec![(b"null".to_vec()), (b"2".to_vec()), (b"2 + 4".to_vec())]
            .into_iter()
            .collect();

    let db_2_contents = BTreeMap::new();
    let db_2_absent_keys: BTreeSet<_> = vec![
        (b"the".to_vec()),
        (b"database".to_vec()),
        (b"is".to_vec()),
        (b"empty".to_vec()),
    ]
    .into_iter()
    .collect();

    let env_contents: EnvTestSnapshot<_> = vec![
        (
            Some("db0"),
            DbTestSnapshot::new(db_0_contents, db_0_absent_keys),
        ),
        (
            Some("db1"),
            DbTestSnapshot::new(db_1_contents, db_1_absent_keys),
        ),
        (
            Some("db2"),
            DbTestSnapshot::new(db_2_contents, db_2_absent_keys),
        ),
    ]
    .into_iter()
    .collect();

    let env_contents = create_dbs_for_snapshot(env, env_contents, db_cfg);
    add_db_contents(env, &env_contents);
    test_db_contents_equal(env, &env_contents);
}
