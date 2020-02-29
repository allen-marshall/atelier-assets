// This test code should fail to compile.

use atelier_kv_store_proc_macros::require_binary_static_env_ext;

#[require_binary_static_env_ext(E, EC, DC, SC, self, X)]
fn do_something<E, EC, DC, SC>(env: &mut E)
where
    E: ::std::fmt::Debug,
{
}

fn main() {}
