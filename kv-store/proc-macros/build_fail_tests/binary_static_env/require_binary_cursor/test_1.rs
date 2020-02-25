// This test code should fail to compile.

use atelier_kv_store_proc_macros::require_binary_cursor;

#[require_binary_cursor()]
fn do_something<C>(cursor: &mut C)
where
    C: ::std::fmt::Debug,
{
}

fn main() {}
