// This test code should fail to compile.

use atelier_kv_store_proc_macros::require_binary_static_env;

#[require_binary_static_env(E)]
const X: u32 = 0;

fn main() {}
