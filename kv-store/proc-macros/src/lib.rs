//! This crate provides procedural macros for use in working with the
//! `atelier-kv-store` crate.

extern crate proc_macro;

use proc_macro2::TokenStream;
use quote::ToTokens;
use std::collections::HashSet;
use syn::parse::{Parse, ParseStream};
use syn::punctuated::Punctuated;
use syn::visit::Visit;
use syn::{Generics, Item, Lifetime, Token, Type, WhereClause, WherePredicate};

pub(crate) mod binary_static_env;

/// Adds trait bounds to a `where` clause in order to constrain a type to be
/// usable as a `'static` key-value storage environment where the keys and
/// values are byte strings, i.e. an LMDB-like storage environment. Prefer the
/// [`require_binary_static_env_ext`][require_binary_static_env_ext]  macro if
/// you need the extra functionality of [`EnvironmentExt`][EnvironmentExt].
///
/// This macro attribute expects one to two comma-separated arguments
/// representing the following:
/// - Main storage environment type.
/// - Identifier path indicating where to find the `atelier_kv_store` crate.
///   This may be needed if you have renamed the `atelier_kv_store` crate in
///   your `Cargo.toml`. Defaults to `::atelier_kv_store`.
///
/// Usage example:
///
/// ```
/// use atelier_kv_store::{ReadWriteTransaction, Transaction};
/// use atelier_kv_store_proc_macros::require_binary_static_env;
/// use std::fmt::Debug;
///
/// #[require_binary_static_env(E)]
/// fn do_something<E>(env: &mut E, db: &E::Database)
///     where
///         E::Error: Debug,
/// {
///     // Here you can manipulate the storage environment using the API defined
///     // in the atelier_kv_store crate, because the macro has added the
///     // required trait bounds to the function's where clause.
///     let mut rw_txn = env.begin_rw_txn().unwrap();
///     rw_txn.put(db, b"new_key", b"new_value").unwrap();
///     rw_txn.commit().unwrap();
/// }
/// ```
///
/// [require_binary_static_env_ext]: self::require_binary_static_env_ext
/// [EnvironmentExt]: atelier_kv_store::EnvironmentExt
#[proc_macro_attribute]
pub fn require_binary_static_env(
    attr: proc_macro::TokenStream,
    item: proc_macro::TokenStream,
) -> proc_macro::TokenStream {
    binary_static_env::require_binary_static_env::require_binary_static_env(
        attr.into(),
        item.into(),
    )
    .into()
}

/// Adds trait bounds to a `where` clause in order to constrain a type to be
/// usable as a `'static` key-value storage environment where the keys and
/// values are byte strings, i.e. an LMDB-like storage environment. Prefer the
/// [`require_binary_static_env`][require_binary_static_env] macro if you don't
/// need the extra functionality of [`EnvironmentExt`][EnvironmentExt].
///
/// This macro attribute expects four to five comma-separated arguments
/// representing the following:
/// - Main storage environment type.
/// - Configuration type used to initialize a storage environment.
/// - Configuration type used to initialize a database within a storage
///   environment.
/// - Configuration type passed to environment sync/flush operations.
/// - Identifier path indicating where to find the `atelier_kv_store` crate.
///   This may be needed if you have renamed the `atelier_kv_store` crate in
///   your `Cargo.toml`. Defaults to `::atelier_kv_store`.
///
/// Usage example:
///
/// ```
/// use atelier_kv_store::{ReadWriteTransaction, Transaction};
/// use atelier_kv_store_proc_macros::require_binary_static_env_ext;
/// use std::fmt::Debug;
///
/// #[require_binary_static_env_ext(E, EC, DC, SC)]
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
///
/// [require_binary_static_env]: self::require_binary_static_env
/// [EnvironmentExt]: atelier_kv_store::EnvironmentExt
#[proc_macro_attribute]
pub fn require_binary_static_env_ext(
    attr: proc_macro::TokenStream,
    item: proc_macro::TokenStream,
) -> proc_macro::TokenStream {
    binary_static_env::require_binary_static_env_ext::require_binary_static_env_ext(
        attr.into(),
        item.into(),
    )
    .into()
}

/// Adds trait bounds to a `where` clause in order to constrain a type to be
/// usable as a (possibly read-only) storage transaction where the keys and
/// values are byte strings, i.e. an LMDB-like storage transaction.
///
/// This macro attribute expects one to two arguments representing the
/// following:
/// - Transaction type.
/// - Identifier path indicating where to find the `atelier_kv_store` crate.
///   This may be needed if you have renamed the `atelier_kv_store` crate in
///   your `Cargo.toml`. Defaults to `::atelier_kv_store`.
///
/// Usage example:
///
/// ```
/// use atelier_kv_store::Transaction;
/// use atelier_kv_store_proc_macros::require_binary_txn;
/// use std::fmt::Debug;
///
/// #[require_binary_txn(T)]
/// fn do_something<T>(txn: T, db: &T::Database)
///     where
///         T::Error: Debug,
/// {
///     // Here you can manipulate the transaction using the API defined in the
///     // atelier_kv_store crate, because the macro has added the required
///     // trait bounds to the function's where clause.
///     txn.get(&db, b"key_0").unwrap();
///     txn.get(&db, b"key_1").unwrap();
///     txn.commit().unwrap();
/// }
/// ```
#[proc_macro_attribute]
pub fn require_binary_txn(
    attr: proc_macro::TokenStream,
    item: proc_macro::TokenStream,
) -> proc_macro::TokenStream {
    binary_static_env::require_binary_txn::require_binary_txn(attr.into(), item.into()).into()
}

/// Adds trait bounds to a `where` clause in order to constrain a type to be
/// usable as a read-write storage transaction where the keys and values are
/// byte strings, i.e. an LMDB-like storage transaction.
///
/// This macro attribute expects one to two arguments representing the
/// following:
/// - Transaction type.
/// - Identifier path indicating where to find the `atelier_kv_store` crate.
///   This may be needed if you have renamed the `atelier_kv_store` crate in
///   your `Cargo.toml`. Defaults to `::atelier_kv_store`.
///
/// Usage example:
///
/// ```
/// use atelier_kv_store::{ReadWriteTransaction, Transaction};
/// use atelier_kv_store_proc_macros::require_binary_rw_txn;
/// use std::fmt::Debug;
///
/// #[require_binary_rw_txn(T)]
/// fn do_something<T>(mut txn: T, db: &T::Database)
///     where
///         T::Error: Debug,
/// {
///     // Here you can manipulate the transaction using the API defined in the
///     // atelier_kv_store crate, because the macro has added the required
///     // trait bounds to the function's where clause.
///     txn.get(&db, b"key_0").unwrap();
///     txn.put(&db, b"key_1", b"value_1").unwrap();
///     txn.commit().unwrap();
/// }
/// ```
#[proc_macro_attribute]
pub fn require_binary_rw_txn(
    attr: proc_macro::TokenStream,
    item: proc_macro::TokenStream,
) -> proc_macro::TokenStream {
    binary_static_env::require_binary_rw_txn::require_binary_rw_txn(attr.into(), item.into()).into()
}

/// Adds trait bounds to a `where` clause in order to constrain a type to be
/// usable as a (possibly read-only) database cursor where the keys and values
/// are byte strings, i.e. an LMDB-like database cursor.
///
/// This macro attribute expects one to two arguments representing the
/// following:
/// - Cursor type.
/// - Identifier path indicating where to find the `atelier_kv_store` crate.
///   This may be needed if you have renamed the `atelier_kv_store` crate in
///   your `Cargo.toml`. Defaults to `::atelier_kv_store`.
///
/// Usage example:
///
/// ```
/// use atelier_kv_store::{Cursor};
/// use atelier_kv_store_proc_macros::require_binary_cursor;
/// use std::fmt::Debug;
///
/// #[require_binary_cursor(C)]
/// fn do_something<C>(cursor: &mut C)
///     where
///         C::Error: Debug,
/// {
///     // Here you can manipulate the transaction using the API defined in the
///     // atelier_kv_store crate, because the macro has added the required
///     // trait bounds to the function's where clause.
///     cursor.get().unwrap();
///     cursor.move_to_next().unwrap();
///     cursor.get().unwrap();
/// }
/// ```
#[proc_macro_attribute]
pub fn require_binary_cursor(
    attr: proc_macro::TokenStream,
    item: proc_macro::TokenStream,
) -> proc_macro::TokenStream {
    binary_static_env::require_binary_cursor::require_binary_cursor(attr.into(), item.into()).into()
}

/// Adds trait bounds to a `where` clause in order to constrain a type to be
/// usable as a read-write database cursor where the keys and values are byte
/// strings, i.e. an LMDB-like database cursor.
///
/// This macro attribute expects one to two arguments representing the
/// following:
/// - Cursor type.
/// - Identifier path indicating where to find the `atelier_kv_store` crate.
///   This may be needed if you have renamed the `atelier_kv_store` crate in
///   your `Cargo.toml`. Defaults to `::atelier_kv_store`.
///
/// Usage example:
///
/// ```
/// use atelier_kv_store::{Cursor, ReadWriteCursor};
/// use atelier_kv_store_proc_macros::require_binary_rw_cursor;
/// use std::fmt::Debug;
///
/// #[require_binary_rw_cursor(C)]
/// fn do_something<C>(cursor: &mut C)
///     where
///         C::Error: Debug,
/// {
///     // Here you can manipulate the transaction using the API defined in the
///     // atelier_kv_store crate, because the macro has added the required
///     // trait bounds to the function's where clause.
///     cursor.get().unwrap();
///     cursor.put_and_move_to_key(b"key_0", b"value_0").unwrap();
///     cursor.move_to_next().unwrap();
///     cursor.del().unwrap();
/// }
/// ```
#[proc_macro_attribute]
pub fn require_binary_rw_cursor(
    attr: proc_macro::TokenStream,
    item: proc_macro::TokenStream,
) -> proc_macro::TokenStream {
    binary_static_env::require_binary_rw_cursor::require_binary_rw_cursor(attr.into(), item.into())
        .into()
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
pub(crate) fn remove_ident_name_conflicts(names: &mut Vec<String>, forbidden: &HashSet<String>) {
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

/// Gets a reference to the generics data in a parsed item. Returns an error if
/// the item is not of a type that can have generics data.
fn find_generics_mut(item: &mut Item) -> Result<&mut Generics, syn::Error> {
    match item {
        Item::Enum(item) => Ok(&mut item.generics),
        Item::Fn(item) => Ok(&mut item.sig.generics),
        Item::Impl(item) => Ok(&mut item.generics),
        Item::Struct(item) => Ok(&mut item.generics),
        Item::Trait(item) => Ok(&mut item.generics),
        Item::TraitAlias(item) => Ok(&mut item.generics),
        Item::Type(item) => Ok(&mut item.generics),
        Item::Union(item) => Ok(&mut item.generics),
        _ => Err(syn::Error::new_spanned(
            item,
            "Unexpected item type; could not modify generics.",
        )),
    }
}

/// Adds the specified predicates to a `where` clause, creating the `where`
/// clause if one is not already present. Does not add a trailing comma to the
/// `where` clause.
pub(crate) fn add_where_predicates<I>(generics: &mut Generics, predicates: I)
where
    I: IntoIterator<Item = WherePredicate>,
{
    if let Some(where_clause) = &mut generics.where_clause {
        where_clause.predicates.extend(predicates);
    } else {
        generics.where_clause = Some(WhereClause {
            where_token: <Token![where]>::default(),
            predicates: predicates.into_iter().collect(),
        });
    }
}

/// Represents a single argument extracted from a comma-separated list of
/// arguments to a macro attribute.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) enum MacroArg {
    /// Variant for arguments that are syntactically valid types.
    Type(Type),

    /// Variant for arguments that are not syntactically valid types but are
    /// syntactically valid paths.
    Path(syn::Path),
}

impl Parse for MacroArg {
    fn parse(input: ParseStream) -> Result<Self, syn::Error> {
        // Try to parse the argument as a type.
        let type_parse_result = Type::parse(input);
        if let Ok(parsed_type) = type_parse_result {
            Ok(MacroArg::Type(parsed_type))
        } else {
            // Try to parse the argument as a path.
            let path_parse_result = syn::Path::parse(input);
            if let Ok(parsed_path) = path_parse_result {
                Ok(MacroArg::Path(parsed_path))
            } else {
                Err(input
                    .error("Failed to parse argument. Arguments must be either types or paths."))
            }
        }
    }
}

impl ToTokens for MacroArg {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        match self {
            MacroArg::Type(parsed_type) => {
                parsed_type.to_tokens(tokens);
            }
            MacroArg::Path(parsed_path) => {
                parsed_path.to_tokens(tokens);
            }
        }
    }
}

/// Trait for types that can be constructed from an argument list passed to a
/// macro attribute.
pub(crate) trait MacroArgs: Sized {
    /// Number of mandatory arguments.
    const NUM_MANDATORY_ARGS: usize;

    /// Number of optional arguments.
    const NUM_OPTIONAL_ARGS: usize;

    /// Gets the default argument value for the specified optional argument.
    /// Index zero is the first optional argument, not the first argument.
    ///
    /// # Panics
    /// May panic if the index is greater than or equal to
    /// [`NUM_OPTIONAL_ARGS`][NUM_OPTIONAL_ARGS].
    ///
    /// [NUM_OPTIONAL_ARGS]: self::MacroArgs::NUM_OPTIONAL_ARGS
    fn optional_arg_default(idx: usize) -> MacroArg;

    /// Constructs `Self` from a list of mandatory arguments and a list of
    /// optional arguments. Returns an error if an argument is not valid.
    ///
    /// # Panics
    /// May panic if the number of mandatory arguments doesn't match
    /// [`NUM_MANDATORY_ARGS`][NUM_MANDATORY_ARGS], or if the number of optional
    /// arguments doesn't match [`NUM_OPTIONAL_ARGS`][NUM_OPTIONAL_ARGS].
    ///
    /// [NUM_MANDATORY_ARGS]: self::MacroArgs::NUM_MANDATORY_ARGS
    /// [NUM_OPTIONAL_ARGS]: self::MacroArgs::NUM_OPTIONAL_ARGS
    fn new<M, O>(mandatory_args: M, optional_args: O) -> Result<Self, syn::Error>
    where
        M: IntoIterator<Item = MacroArg>,
        O: IntoIterator<Item = MacroArg>;
}

/// Parses a [`MacroArgs`][MacroArgs] type.
///
/// [MacroArgs]: self::MacroArgs
fn parse_macro_args<T>(input: ParseStream) -> Result<T, syn::Error>
where
    T: MacroArgs,
{
    // Split the arguments by commas.
    let punctuated_args: Punctuated<MacroArg, Token![,]> = Punctuated::parse_terminated(input)?;

    // Make sure we have the right number of arguments.
    if punctuated_args.len() < T::NUM_MANDATORY_ARGS {
        Err(syn::Error::new_spanned(
            &punctuated_args,
            format!(
                "Expected at least {} arguments, got {}.",
                T::NUM_MANDATORY_ARGS,
                punctuated_args.len()
            ),
        ))
    } else if punctuated_args.len() > T::NUM_MANDATORY_ARGS + T::NUM_OPTIONAL_ARGS {
        Err(syn::Error::new_spanned(
            &punctuated_args,
            format!(
                "Expected at most {} arguments, got {}.",
                T::NUM_MANDATORY_ARGS + T::NUM_OPTIONAL_ARGS,
                punctuated_args.len()
            ),
        ))
    } else {
        // Separate the mandatory and optional args, and apply default values
        // for any optional args that aren't specified.
        let mut args_iter = punctuated_args.into_iter();
        let mut mandatory_args = Vec::with_capacity(T::NUM_MANDATORY_ARGS);
        for _ in 0..T::NUM_MANDATORY_ARGS {
            mandatory_args.push(args_iter.next().unwrap());
        }
        let mut optional_args = Vec::with_capacity(T::NUM_OPTIONAL_ARGS);
        optional_args.extend(args_iter);
        while optional_args.len() < T::NUM_OPTIONAL_ARGS {
            optional_args.push(T::optional_arg_default(optional_args.len()));
        }

        // Perform implementation-specific parsing.
        T::new(mandatory_args, optional_args)
    }
}

/// Type that is used to extract all lifetime names mentioned in a syntax tree
/// or collection of syntax trees. Lifetimes are recorded by visiting syntax
/// trees using the `syn` crate's visiting functionality.
#[derive(Debug, Default)]
pub(crate) struct LifetimeNameFinder {
    /// Set of lifetime names encountered so far.
    names_found: HashSet<String>,
}

impl LifetimeNameFinder {
    /// Returns all the lifetime names found in all the syntax trees that the
    /// `LifetimeNameFinder` has visited so far.
    fn names_found(&self) -> &HashSet<String> {
        &self.names_found
    }
}

impl<'ast> Visit<'ast> for LifetimeNameFinder {
    fn visit_lifetime(&mut self, i: &'ast Lifetime) {
        self.names_found.insert(i.ident.to_string());
    }
}

/// Utilities for testing.
#[cfg(test)]
pub(crate) mod test_util {
    use std::iter::FromIterator;

    /// Simple utility that converts a collection of [`ToString`][ToString]
    /// objects into a collection of [`String`][String] objects.
    ///
    /// [ToString]: std::string::ToString
    /// [String]: std::string::String
    pub(crate) fn map_to_string<C0, C1>(collection: C0) -> C1
    where
        C0: IntoIterator,
        C0::Item: ToString,
        C1: FromIterator<String>,
    {
        collection.into_iter().map(|s| s.to_string()).collect()
    }
}

#[cfg(test)]
mod tests {
    use super::test_util::map_to_string;
    use super::*;
    use syn::visit::visit_type;
    use syn::{parse2, parse_quote};

    /// Type that implements `MacroArgs` for testing.
    #[derive(Debug, Clone, PartialEq, Eq, Hash)]
    struct MacroArgsImpl {
        type_0: Type,
        type_1: Type,
        type_2: Type,
    }

    impl MacroArgs for MacroArgsImpl {
        const NUM_MANDATORY_ARGS: usize = 2;
        const NUM_OPTIONAL_ARGS: usize = 1;

        fn optional_arg_default(idx: usize) -> MacroArg {
            match idx {
                0 => parse_quote! { T2 },
                _ => panic!(),
            }
        }

        fn new<M, O>(mandatory_args: M, optional_args: O) -> Result<Self, syn::Error>
        where
            M: IntoIterator<Item = MacroArg>,
            O: IntoIterator<Item = MacroArg>,
        {
            let mandatory_args_vec: Vec<_> = mandatory_args.into_iter().collect();
            let optional_args_vec: Vec<_> = optional_args.into_iter().collect();
            Ok(MacroArgsImpl {
                type_0: parse2(mandatory_args_vec[0].to_token_stream())?,
                type_1: parse2(mandatory_args_vec[1].to_token_stream())?,
                type_2: parse2(optional_args_vec[0].to_token_stream())?,
            })
        }
    }

    impl Parse for MacroArgsImpl {
        fn parse(input: ParseStream) -> Result<Self, syn::Error> {
            parse_macro_args(input)
        }
    }

    /// Helper that executes a single test case for the
    /// `remove_ident_name_conflicts` function. The arguments provide an initial
    /// names vector to modify, a set of forbidden identifier names, and the
    /// expected contents of the names vector after the modification.
    ///
    /// # Panics
    /// Panics if the results are not as expected.
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

    /// Helper that executes a single test case for the `add_where_predicates`
    /// function. The arguments provide an initial item to modify, a list of
    /// `where` predicates to add, and the expected value of the modified item.
    ///
    /// # Panics
    /// Panics if the results are not as expected, or if the provided item is of
    /// a type that cannot have generics.
    fn add_where_predicates_case(
        item: &mut Item,
        new_predicates: Vec<WherePredicate>,
        expected: &Item,
    ) {
        add_where_predicates(find_generics_mut(item).unwrap(), new_predicates);
        assert_eq!(item, expected);
    }

    /// Tests functionality of the `MacroArg` type.
    #[test]
    fn macro_arg_test() {
        let arg: MacroArg = parse_quote! { T };
        let reparsed_arg: Type = parse2(arg.to_token_stream()).unwrap();
        assert_eq!(reparsed_arg, parse_quote! { T });
        assert_eq!(arg, parse2(arg.to_token_stream()).unwrap());

        let arg: MacroArg = parse_quote! { T<T0, T1<'a>> };
        let reparsed_arg: Type = parse2(arg.to_token_stream()).unwrap();
        assert_eq!(reparsed_arg, parse_quote! { T<T0, T1<'a>> });
        assert_eq!(arg, parse2(arg.to_token_stream()).unwrap());

        let arg: MacroArg = parse_quote! { crate::x };
        let reparsed_arg: syn::Path = parse2(arg.to_token_stream()).unwrap();
        assert_eq!(reparsed_arg, parse_quote! { crate::x });
        assert_eq!(arg, parse2(arg.to_token_stream()).unwrap());

        let arg: Result<MacroArg, _> = parse2(parse_quote! { if , 'a B });
        arg.unwrap_err();
    }

    /// Tests the `parse_macro_args` function.
    #[test]
    fn parse_macro_args_test() {
        let args: Result<MacroArgsImpl, _> = parse2(parse_quote! { T0, T1, T2 });
        args.unwrap();

        let args: Result<MacroArgsImpl, _> = parse2(parse_quote! { T0, T1, T2, });
        args.unwrap();

        let args: Result<MacroArgsImpl, _> = parse2(parse_quote! { T0<'a>, T1<A>, T2<'b, B> });
        args.unwrap();

        let args: Result<MacroArgsImpl, _> = parse2(parse_quote! { T0, T1 });
        args.unwrap();

        let args: Result<MacroArgsImpl, _> = parse2(parse_quote! { T0<'a>, T1<A> });
        args.unwrap();

        let args: Result<MacroArgsImpl, _> = parse2(parse_quote! { T0 });
        args.unwrap_err();

        let args: Result<MacroArgsImpl, _> = parse2(parse_quote! { T0, T1, T2, T3 });
        args.unwrap_err();
    }

    /// Tests functionality of the `LifetimeNameFinder` type.
    #[test]
    fn lifetime_name_finder_test() {
        let mut finder = LifetimeNameFinder::default();
        assert_eq!(finder.names_found(), &HashSet::new());

        visit_type(&mut finder, &parse_quote! { <X<'a> as Y<'b, 'c>>::Z });
        assert_eq!(
            finder.names_found(),
            &map_to_string::<_, HashSet<_>>(vec!["a", "b", "c"])
        );

        visit_type(&mut finder, &parse_quote! { <X<'a> as Y<'b, 'd>>::Z });
        assert_eq!(
            finder.names_found(),
            &map_to_string::<_, HashSet<_>>(vec!["a", "b", "c", "d"])
        );

        visit_type(&mut finder, &parse_quote! { X });
        assert_eq!(
            finder.names_found(),
            &map_to_string::<_, HashSet<_>>(vec!["a", "b", "c", "d"])
        );
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

    /// Tests the `find_generics_mut` function.
    #[test]
    fn find_generics_mut_test() {
        let mut test_case = parse_quote! { enum A {B, C} };
        let generics = find_generics_mut(&mut test_case).unwrap();
        assert!(generics.params.is_empty());
        assert_eq!(generics.where_clause, None);

        let mut test_case = parse_quote! { enum A<T0, T1> where T0: X {B(T0), C(T1)} };
        let generics = find_generics_mut(&mut test_case).unwrap();
        assert_eq!(generics.params, parse_quote! { T0, T1 });
        assert_eq!(generics.where_clause, Some(parse_quote! { where T0: X }));

        let mut test_case = parse_quote! { fn f(g: i32, h: ()) -> usize { 0 } };
        let generics = find_generics_mut(&mut test_case).unwrap();
        assert!(generics.params.is_empty());
        assert_eq!(generics.where_clause, None);

        let mut test_case = parse_quote! { fn f<T0, T1>(g: i32, h: ()) -> usize where T0: X { 0 } };
        let generics = find_generics_mut(&mut test_case).unwrap();
        assert_eq!(generics.params, parse_quote! { T0, T1 });
        assert_eq!(generics.where_clause, Some(parse_quote! { where T0: X }));

        let mut test_case = parse_quote! { impl A {} };
        let generics = find_generics_mut(&mut test_case).unwrap();
        assert!(generics.params.is_empty());
        assert_eq!(generics.where_clause, None);

        let mut test_case = parse_quote! { impl<T0, T1> A where T0: X {} };
        let generics = find_generics_mut(&mut test_case).unwrap();
        assert_eq!(generics.params, parse_quote! { T0, T1 });
        assert_eq!(generics.where_clause, Some(parse_quote! { where T0: X }));

        let mut test_case = parse_quote! { struct A {field_0: B, field_1: C} };
        let generics = find_generics_mut(&mut test_case).unwrap();
        assert!(generics.params.is_empty());
        assert_eq!(generics.where_clause, None);

        let mut test_case = parse_quote! { struct A<T0, T1> where T0: X {field_0: B, field_1: C} };
        let generics = find_generics_mut(&mut test_case).unwrap();
        assert_eq!(generics.params, parse_quote! { T0, T1 });
        assert_eq!(generics.where_clause, Some(parse_quote! { where T0: X }));

        let mut test_case = parse_quote! { trait A {fn f(g: i32) -> usize;} };
        let generics = find_generics_mut(&mut test_case).unwrap();
        assert!(generics.params.is_empty());
        assert_eq!(generics.where_clause, None);

        let mut test_case = parse_quote! { trait A<T0, T1> where T0: X {fn f(g: i32) -> usize;} };
        let generics = find_generics_mut(&mut test_case).unwrap();
        assert_eq!(generics.params, parse_quote! { T0, T1 });
        assert_eq!(generics.where_clause, Some(parse_quote! { where T0: X }));

        let mut test_case = parse_quote! { trait A = B; };
        let generics = find_generics_mut(&mut test_case).unwrap();
        assert!(generics.params.is_empty());
        assert_eq!(generics.where_clause, None);

        let mut test_case = parse_quote! { trait A<T0, T1> = B<T0, T1> where T0: X; };
        let generics = find_generics_mut(&mut test_case).unwrap();
        assert_eq!(generics.params, parse_quote! { T0, T1 });
        assert_eq!(generics.where_clause, Some(parse_quote! { where T0: X }));

        let mut test_case = parse_quote! { type A = B; };
        let generics = find_generics_mut(&mut test_case).unwrap();
        assert!(generics.params.is_empty());
        assert_eq!(generics.where_clause, None);

        let mut test_case = parse_quote! { type A<T0, T1> where T0: X = B<T0, T1>; };
        let generics = find_generics_mut(&mut test_case).unwrap();
        assert_eq!(generics.params, parse_quote! { T0, T1 });
        assert_eq!(generics.where_clause, Some(parse_quote! { where T0: X }));

        let mut test_case = parse_quote! { union A {field_0: B, field_1: C} };
        let generics = find_generics_mut(&mut test_case).unwrap();
        assert!(generics.params.is_empty());
        assert_eq!(generics.where_clause, None);

        let mut test_case = parse_quote! { union A<T0, T1> where T0: X {field_0: B, field_1: C} };
        let generics = find_generics_mut(&mut test_case).unwrap();
        assert_eq!(generics.params, parse_quote! { T0, T1 });
        assert_eq!(generics.where_clause, Some(parse_quote! { where T0: X }));

        let mut test_case = parse_quote! { const A: usize = 0; };
        find_generics_mut(&mut test_case).unwrap_err();

        let mut test_case = parse_quote! { extern crate x; };
        find_generics_mut(&mut test_case).unwrap_err();

        let mut test_case = parse_quote! { extern "C" {} };
        find_generics_mut(&mut test_case).unwrap_err();

        let mut test_case = parse_quote! { macro_rules! m {} };
        find_generics_mut(&mut test_case).unwrap_err();

        let mut test_case = parse_quote! { macro m {} };
        find_generics_mut(&mut test_case).unwrap_err();

        let mut test_case = parse_quote! { mod m {} };
        find_generics_mut(&mut test_case).unwrap_err();

        let mut test_case = parse_quote! { static A: usize = 0; };
        find_generics_mut(&mut test_case).unwrap_err();

        let mut test_case = parse_quote! { use ::std::collections::HashMap; };
        find_generics_mut(&mut test_case).unwrap_err();
    }

    /// Tests the `add_where_predicates` function.
    #[test]
    fn add_where_predicates_test() {
        add_where_predicates_case(
            &mut parse_quote! { fn do_something<A, B>() {} },
            vec![],
            &parse_quote! { fn do_something<A, B>() where {} },
        );
        add_where_predicates_case(
            &mut parse_quote! { fn do_something<A, B>() where A: T {} },
            vec![],
            &parse_quote! { fn do_something<A, B>() where A: T {} },
        );
        add_where_predicates_case(
            &mut parse_quote! { fn do_something<A, B>() {} },
            vec![parse_quote! { A: T0 }, parse_quote! { Self: T1 }],
            &parse_quote! { fn do_something<A, B>() where A: T0, Self: T1 {} },
        );
        add_where_predicates_case(
            &mut parse_quote! { fn do_something<A, B>() where A: T0 {} },
            vec![parse_quote! { Self: T1 }],
            &parse_quote! { fn do_something<A, B>() where A: T0, Self: T1 {} },
        );
    }

    /// Tests cases where compilation should fail.
    #[test]
    fn build_fail_test() {
        let build_tester = trybuild::TestCases::new();
        build_tester.compile_fail("build_fail_tests/**/*.rs");
    }
}
