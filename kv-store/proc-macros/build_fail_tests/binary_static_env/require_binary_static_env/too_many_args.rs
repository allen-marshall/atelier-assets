// This test code should fail to compile.

use atelier_kv_store_proc_macros::require_binary_static_env;

#[require_binary_static_env(E, crate, X)]
fn do_something<E>(env: &mut E)
where
    E: ::std::fmt::Debug,
{
}

fn main() {}
