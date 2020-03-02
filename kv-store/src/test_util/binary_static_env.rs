//! Utilities for testing storage implementations where the storage environment
//! is `'static` and the keys and values are byte strings.

use crate::{EnvironmentExt, ReadWriteTransaction, Transaction};
use atelier_kv_store_proc_macros::{
    require_binary_cursor, require_binary_rw_cursor, require_binary_rw_txn,
    require_binary_static_env, require_binary_static_env_ext, require_binary_txn,
};
use std::collections::BTreeMap;
use std::fmt::Debug;

/// A "snapshot" of an environment, consisting of a mapping from database
/// handles to key-value stores.
///
/// # Parameters
/// - `DB`: Type that represents a database.
pub(crate) type EnvSnapshot<DB> = BTreeMap<DB, BTreeMap<Vec<u8>, Vec<u8>>>;

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
    snapshot: EnvSnapshot<Option<&str>>,
    db_cfg: DC,
) -> EnvSnapshot<E::Database>
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
pub(crate) fn test_db_contents_equal<E>(env: &E, expected: &EnvSnapshot<E::Database>)
where
    E::Error: Debug,
    E::Database: Ord,
{
    // Test that we can retrieve the expected contents through a read-only transaction.
    let ro_txn = env.begin_ro_txn().unwrap();
    for (db, expected_db_contents) in expected.iter() {
        for (key, value) in expected_db_contents {
            assert_eq!(
                ro_txn.get(db, key).unwrap().unwrap().as_ref().as_ref(),
                &**value
            );
        }
    }
    ro_txn.abort();

    // Test that we can retrieve the expected contents through a read-write transaction.
    let rw_txn = env.begin_rw_txn().unwrap();
    for (db, expected_db_contents) in expected.iter() {
        for (key, value) in expected_db_contents {
            assert_eq!(
                rw_txn.get(db, key).unwrap().unwrap().as_ref().as_ref(),
                &**value
            );
        }
    }
    rw_txn.abort();

    // TODO: Also test using cursors. Currently, we aren't verifying that
    //  there is no extra data.
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
pub(crate) fn add_db_contents<E>(env: &mut E, contents_to_add: &EnvSnapshot<E::Database>)
where
    E::Error: Debug,
    E::Database: Ord,
{
    let mut rw_txn = env.begin_rw_txn().unwrap();
    for (db, db_contents_to_add) in contents_to_add.iter() {
        for (key, value) in db_contents_to_add {
            rw_txn
                .put(db, AsRef::<[u8]>::as_ref(key), AsRef::<[u8]>::as_ref(value))
                .unwrap();
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
    let mut contents = BTreeMap::new();
    contents.insert(None, BTreeMap::new());
    contents.insert(Some("db0"), BTreeMap::new());
    contents.insert(Some("db1"), BTreeMap::new());
    contents
        .get_mut(&None)
        .unwrap()
        .insert(b"Respond with space.".to_vec(), b" ".to_vec());
    contents
        .get_mut(&None)
        .unwrap()
        .insert(b"Is this the default database?".to_vec(), b"yes".to_vec());
    contents
        .get_mut(&None)
        .unwrap()
        .insert(b"Is it being used for testing?".to_vec(), b"yes".to_vec());
    contents
        .get_mut(&None)
        .unwrap()
        .insert(b"What is stored in it?".to_vec(), b"data".to_vec());
    contents
        .get_mut(&Some("db0"))
        .unwrap()
        .insert(b" ".to_vec(), b"Space".to_vec());
    contents
        .get_mut(&Some("db0"))
        .unwrap()
        .insert(b"2 + 2".to_vec(), b"4".to_vec());

    let contents = create_dbs_for_snapshot(env, contents, db_cfg);
    add_db_contents(env, &contents);
    test_db_contents_equal(env, &contents);
}
