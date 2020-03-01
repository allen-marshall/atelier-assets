//! Tests procedural macros for working with LMDB-like binary storage
//! environments.

use atelier_kv_store::iter::CursorIter;
use atelier_kv_store::{EnvironmentExt, Transaction};
use atelier_kv_store_proc_macros::{
    require_binary_cursor, require_binary_rw_cursor, require_binary_rw_txn,
    require_binary_static_env, require_binary_static_env_ext, require_binary_txn,
};
use std::fmt::Debug;

#[test]
fn main_test() {
    // The main purpose of this test is to check for compilation errors when
    // using the macros. As such, this test doesn't actually do much at runtime.
    // Instead, it defines functions that could theoretically operate on a
    // storage environment but doesn't ever call those functions.

    #[require_binary_cursor(C)]
    fn _do_something_with_cursor<C>(cursor: &mut C)
    where
        C::Error: Debug,
    {
        cursor.get().unwrap();
        cursor.move_to_next().unwrap();
        cursor.move_to_key(b"test_key").unwrap();
        CursorIter::iter(cursor).unwrap().next();
    }

    #[require_binary_rw_cursor(C)]
    fn _do_something_with_rw_cursor<C>(cursor: &mut C)
    where
        C::Error: Debug,
    {
        _do_something_with_cursor(cursor);
        cursor
            .put_and_move_to_key(b"test_key", b"test_value")
            .unwrap();
        cursor.del().unwrap();
    }

    #[require_binary_txn(T)]
    fn _do_something_with_txn<T>(txn: &mut T, db: &T::Database)
    where
        T::Error: Debug,
    {
        txn.get(db, b"test_key").unwrap();
        txn.db_config(db).unwrap();
        let mut cursor = txn.open_ro_cursor(db).unwrap();
        _do_something_with_cursor(&mut cursor);
    }

    #[require_binary_txn(T)]
    fn _commit_txn<T>(txn: T)
    where
        T::Error: Debug,
    {
        txn.commit().unwrap();
    }

    #[require_binary_rw_txn(T)]
    fn _do_something_with_rw_txn<T>(txn: &mut T, db: &T::Database, nest_levels: usize)
    where
        T::Error: Debug,
    {
        _do_something_with_txn(txn, db);
        txn.put(db, b"test_key", b"test_value").unwrap();
        txn.del(db, b"test_key").unwrap();
        let mut rw_cursor = txn.open_rw_cursor(db).unwrap();
        _do_something_with_rw_cursor(&mut rw_cursor);
        std::mem::drop(rw_cursor);

        if nest_levels > 0 {
            let mut nested_txn = txn.begin_nested_txn().unwrap();
            _do_something_with_rw_txn(&mut nested_txn, db, nest_levels - 1);

            // TODO: For some reason, calling methods on a nested transaction
            //  fails to compile if the calls are made directly, but succeeds if
            //  the calls are wrapped in a function. I suspect this is a
            //  compiler bug, but haven't tracked down the details yet.

            // nested_txn.commit().unwrap();

            #[require_binary_txn(T)]
            fn commit<T>(txn: T)
            where
                T::Error: Debug,
            {
                txn.commit().unwrap();
            }
            commit(nested_txn);
        }
    }

    #[require_binary_static_env(E)]
    fn _do_something_with_env<E>(env: &mut E, db: &E::Database)
    where
        E::Error: Debug,
    {
        let mut ro_txn = env.begin_ro_txn().unwrap();
        _do_something_with_txn(&mut ro_txn, db);
        ro_txn.commit().unwrap();
        let mut rw_txn = env.begin_rw_txn().unwrap();
        _do_something_with_rw_txn(&mut rw_txn, db, 20);
        rw_txn.commit().unwrap();
    }

    #[require_binary_static_env_ext(E, EC, DC, SC)]
    fn _do_something_with_env_ext<E, EC, DC, SC>(env_cfg: EC, db_cfg: DC, sync_cfg: SC)
    where
        E::Error: Debug,
    {
        let mut env: E = EnvironmentExt::new(env_cfg).unwrap();
        let db = env.create_db(Some("test_db"), db_cfg).unwrap();
        env.db_config(&db).unwrap();
        env.sync(sync_cfg).unwrap();
        _do_something_with_env(&mut env, &db);
    }
}
