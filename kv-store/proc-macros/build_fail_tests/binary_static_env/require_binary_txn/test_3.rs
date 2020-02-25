// This test code should fail to compile.

use atelier_kv_store_proc_macros::require_binary_txn;

#[require_binary_txn(T)]
const X: u32 = 0;

fn main() {}
