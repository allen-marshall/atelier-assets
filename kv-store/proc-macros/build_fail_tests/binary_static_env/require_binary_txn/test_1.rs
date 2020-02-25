// This test code should fail to compile.

use atelier_kv_store_proc_macros::require_binary_txn;

#[require_binary_txn()]
fn do_something<T>(txn: &mut T)
where
    T: ::std::fmt::Debug,
{
}

fn main() {}
