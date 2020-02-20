//! This crate provides procedural macros for use in working with the
//! `atelier-kv-store` crate.

extern crate proc_macro;

use std::collections::HashSet;

pub(crate) mod binary_static_env;

// TODO: Document the required arguments and maybe give an example.
/// Adds trait bounds to a `where` clause in order to constrain a type to be
/// usable as a `'static` key-value storage environment where the keys and
/// values are byte strings, i.e. an LMDB-like storage environment. This macro
/// exists because the required trait bounds are quite long and repetitive.
#[proc_macro_attribute]
pub fn require_binary_static_env(
    attr: proc_macro::TokenStream,
    item: proc_macro::TokenStream,
) -> proc_macro::TokenStream {
    binary_static_env::require_binary_static_env(attr.into(), item.into()).into()
}

/// Same as [`require_binary_static_env`][require_binary_static_env], except it
/// is intended for use from within the `atelier-kv-store` crate. The main
/// difference is in how items from the `atelier-kv-store` crate are referenced.
/// (This macro references them using paths that start with `crate::`, while the
/// [`require_binary_static_env`][require_binary_static_env] macro uses paths
/// that start with `::atelier_kv_store::`.)
///
/// This macro should only be needed by developers of `atelier-kv-store`. If you
/// don't know which macro to use, prefer
/// [`require_binary_static_env`][require_binary_static_env].
///
/// [require_binary_static_env]: self::require_binary_static_env
#[proc_macro_attribute]
pub fn require_binary_static_env_inside_crate(
    attr: proc_macro::TokenStream,
    item: proc_macro::TokenStream,
) -> proc_macro::TokenStream {
    binary_static_env::require_binary_static_env_inside_crate(attr.into(), item.into()).into()
}

/// Modifies the specified list of identifier names so that it contains no
/// duplicate names and no matches for any of the specified "forbidden" names.
/// The length of the provided names list is not modified; only the names
/// themselves are changed to avoid conflicts.
///
/// This function is intended for situations where a predefined number of
/// identifier names are needed, and (apart from ergonomic considerations) it
/// doesn't really matter what names are used as long as they don't conflict
/// with the specified forbidden set or with each other. It may be desirable to
/// use a specific set of meaningful names for ergonomic reasons, so this
/// function tries to use names that are similar to the pre-populated ones when
/// possible.
fn remove_ident_name_conflicts(names: &mut Vec<String>, forbidden: &HashSet<String>) {
    fn suffixed_name(name: &str, suffix_idx: u64) -> String {
        let mut output = name.to_string();
        output.push_str(&format!("_{}", suffix_idx));
        output
    }

    // next_forbidden contains both the forbidden set of names and all the final
    // selected names that have been determined so far, in order to avoid
    // duplicates.
    let mut next_forbidden = forbidden.clone();
    for name in names.iter_mut() {
        if next_forbidden.contains(name) {
            // If the preferred name is not available, choose a distinct but
            // similar name by appending a number. It is assumed here that there
            // exists a u64 suffix value that will resolve the conflict; this
            // assumption can't be violated unless the next_forbidden set is
            // ridiculously huge.
            let mut suffix_idx: u64 = 0;
            let mut new_name = suffixed_name(&name, suffix_idx);
            while next_forbidden.contains(&new_name) {
                suffix_idx += 1;
                new_name = suffixed_name(&name, suffix_idx);
            }

            // Modify the name in the names list to the non-conflicting value.
            *name = new_name;
        }

        // Add the chosen name to next_forbidden so that it can't be used for
        // later names in the list.
        next_forbidden.insert(name.clone());
    }
}
