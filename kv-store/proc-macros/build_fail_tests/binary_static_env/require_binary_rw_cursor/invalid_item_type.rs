// This test code should fail to compile.

use atelier_kv_store_proc_macros::require_binary_rw_cursor;

#[require_binary_rw_cursor(C)]
const X: u32 = 0;

fn main() {}
