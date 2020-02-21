//! This crate provides procedural macros for use in working with the
//! `atelier-kv-store` crate.

extern crate proc_macro;

use std::collections::HashSet;

pub(crate) mod binary_static_env;

/// Adds trait bounds to a `where` clause in order to constrain a type to be
/// usable as a `'static` key-value storage environment where the keys and
/// values are byte strings, i.e. an LMDB-like storage environment. This macro
/// exists because the required trait bounds are quite long and repetitive.
///
/// This macro attribute expects four comma-separated arguments representing the
/// following:
/// - Main storage environment type
/// - Configuration type used to initialize a storage environment
/// - Configuration type used to initialize a database within a storage
///   environment
/// - Configuration type passed to environment sync/flush operations
///
/// Usage example:
///
/// ```
/// use atelier_kv_store::{ReadWriteTransaction, Transaction};
/// use atelier_kv_store_proc_macros::require_binary_static_env;
/// use std::fmt::Debug;
///
/// #[require_binary_static_env(E, EC, DC, SC)]
/// fn do_something<E, EC, DC, SC>(env: &mut E, db_cfg: DC)
///     where
///         E::Error: Debug,
/// {
///     // Here you can manipulate the storage environment using the API defined
///     // in the atelier_kv_store crate, because the macro has added the
///     // required trait bounds to the function's where clause.
///     let db = env.create_db(Some("db_name"), db_cfg).unwrap();
///     let mut rw_txn = env.begin_rw_txn().unwrap();
///     rw_txn.put(&db, b"new_key", b"new_value").unwrap();
///     rw_txn.commit().unwrap();
/// }
/// ```
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

#[cfg(test)]
mod tests {
    use super::*;
    use std::iter::{FromIterator, IntoIterator};

    /// Simple utility that converts a collection of `ToString` objects into a
    /// collection of `String` objects.
    fn map_to_string<C0, C1>(collection: C0) -> C1
    where
        C0: IntoIterator,
        C0::Item: ToString,
        C1: FromIterator<String>,
    {
        collection.into_iter().map(|s| s.to_string()).collect()
    }

    /// Helper that executes a single test case for the
    /// `remove_ident_name_conflicts` function. The arguments provide an initial
    /// names vector to modify, a set of forbidden identifier names, and the
    /// expected contents of the names vector after the modification.
    fn remove_ident_name_conflicts_case(
        names: &mut Vec<String>,
        forbidden: &HashSet<String>,
        expected: &Vec<String>,
    ) {
        remove_ident_name_conflicts(names, forbidden);

        // Ensure that there are no conflicts.
        let output_names_set: HashSet<String> = names.clone().into_iter().collect();
        assert_eq!(names.len(), output_names_set.len());
        assert!(output_names_set.is_disjoint(forbidden));

        // Ensure that the names are as expected.
        assert_eq!(&names, &expected);
    }

    /// Tests the `remove_ident_name_conflicts` function.
    #[test]
    fn remove_ident_name_conflicts_test() {
        remove_ident_name_conflicts_case(
            &mut map_to_string(vec!["aa", "bb", "cc"]),
            &HashSet::new(),
            &map_to_string(vec!["aa", "bb", "cc"]),
        );
        remove_ident_name_conflicts_case(
            &mut map_to_string(vec!["aa", "bb", "cc"]),
            &map_to_string(vec!["dd", "ee", "ff"]),
            &map_to_string(vec!["aa", "bb", "cc"]),
        );
        remove_ident_name_conflicts_case(
            &mut map_to_string(vec!["aa", "bb", "cc"]),
            &map_to_string(vec!["aa"]),
            &map_to_string(vec!["aa_0", "bb", "cc"]),
        );
        remove_ident_name_conflicts_case(
            &mut map_to_string(vec!["aa", "bb", "cc"]),
            &map_to_string(vec!["aa", "aa_0", "aa_1"]),
            &map_to_string(vec!["aa_2", "bb", "cc"]),
        );
        remove_ident_name_conflicts_case(
            &mut map_to_string(vec!["aa", "bb", "cc"]),
            &map_to_string(vec!["aa", "aa_0", "bb"]),
            &map_to_string(vec!["aa_1", "bb_0", "cc"]),
        );
        remove_ident_name_conflicts_case(
            &mut map_to_string(vec!["aa", "bb", "cc"]),
            &map_to_string(vec!["bb", "ee", "ff"]),
            &map_to_string(vec!["aa", "bb_0", "cc"]),
        );
        remove_ident_name_conflicts_case(
            &mut map_to_string(vec!["aa", "aa", "cc"]),
            &HashSet::new(),
            &map_to_string(vec!["aa", "aa_0", "cc"]),
        );
        remove_ident_name_conflicts_case(
            &mut map_to_string(vec!["aa", "aa", "cc"]),
            &map_to_string(vec!["aa"]),
            &map_to_string(vec!["aa_0", "aa_1", "cc"]),
        );
        remove_ident_name_conflicts_case(
            &mut map_to_string(vec!["aa", "aa_0", "cc"]),
            &map_to_string(vec!["aa"]),
            &map_to_string(vec!["aa_0", "aa_0_0", "cc"]),
        );
        remove_ident_name_conflicts_case(&mut Vec::new(), &HashSet::new(), &Vec::new());
        remove_ident_name_conflicts_case(
            &mut Vec::new(),
            &map_to_string(vec!["aa", "bb", "cc"]),
            &Vec::new(),
        );
    }
}
