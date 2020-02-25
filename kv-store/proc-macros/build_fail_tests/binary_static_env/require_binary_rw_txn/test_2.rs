// This test code should fail to compile.

use atelier_kv_store_proc_macros::require_binary_rw_txn;

#[require_binary_rw_txn(T, self, X)]
fn do_something<T>(txn: &mut T)
where
    T: ::std::fmt::Debug,
{
}

fn main() {}
