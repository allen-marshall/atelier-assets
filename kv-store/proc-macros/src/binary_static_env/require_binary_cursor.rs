//! This module contains the implementation for the
//! [`require_binary_cursor`][require_binary_cursor] macro.
//!
//! [require_binary_cursor]: crate::require_binary_cursor

use crate::binary_static_env::{
    cursor_basic_trait_bound, cursor_trait_bound, TypeAndCrateRootArgs,
};
use crate::{
    add_where_predicates, find_generics_mut, remove_ident_name_conflicts, LifetimeNameFinder,
};
use proc_macro2::{Span, TokenStream};
use quote::ToTokens;
use syn::visit::{visit_path, visit_type};
use syn::{parse2, parse_quote, BoundLifetimes, Generics, Lifetime};

/// Represents the lifetime names to be used in the output of a specific
/// invocation of the [`require_binary_cursor`][require_binary_cursor] macro
/// attribute.
///
/// [require_binary_cursor]: crate::require_binary_cursor
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct BoundsLifetimeNames {
    /// Lifetime name for cursor references.
    cursor_lt: Lifetime,

    /// Lifetime name for key references used in queries.
    kq_lt: Lifetime,
}

/// Chooses names for the lifetimes to be used in the output of a specific
/// invocation of the [`require_binary_cursor`][require_binary_cursor] macro
/// attribute.
///
/// For clarity of error messages, this function tries to choose descriptive
/// names for the lifetimes. It must ensure that it does not choose names that
/// conflict with any lifetimes used in the arguments to the macro.
///
/// [require_binary_cursor]: crate::require_binary_cursor
fn name_lifetimes(args: &TypeAndCrateRootArgs) -> BoundsLifetimeNames {
    fn name_to_lifetime(name: &str) -> Lifetime {
        Lifetime::new(&format!("'{}", name), Span::call_site())
    }

    // Choose names for the lifetimes, avoiding any conflicts with lifetime
    // names used in the macro arguments.
    let mut forbidden_finder = LifetimeNameFinder::default();
    visit_type(&mut forbidden_finder, &args.type_arg);
    visit_path(&mut forbidden_finder, &args.crate_root_path);
    let mut chosen_names = vec!["cursor".to_string(), "kq".to_string()];
    remove_ident_name_conflicts(&mut chosen_names, &forbidden_finder.names_found());

    BoundsLifetimeNames {
        cursor_lt: name_to_lifetime(&chosen_names[0]),
        kq_lt: name_to_lifetime(&chosen_names[1]),
    }
}

/// Modifies the specified generics data so that its `where` clause contains the
/// bounds required to use a binary database cursor, i.e. the bounds
/// needed when using [`require_binary_cursor`][require_binary_cursor].
///
/// [require_binary_cursor]: crate::require_binary_cursor
fn add_bounds(
    generics: &mut Generics,
    args: &TypeAndCrateRootArgs,
    lt_names: &BoundsLifetimeNames,
) {
    // Bring parameters into scope so we can use them in parse_quote.
    let (cursor_lt, kq_lt, cursor_type) = (&lt_names.cursor_lt, &lt_names.kq_lt, &args.type_arg);

    let lt_quant: BoundLifetimes = parse_quote! { for<#cursor_lt, #kq_lt,> };
    let cursor_basic_trait = cursor_basic_trait_bound(&args.crate_root_path);
    let cursor_trait =
        cursor_trait_bound(&lt_names.cursor_lt, &lt_names.kq_lt, &args.crate_root_path);
    add_where_predicates(
        generics,
        vec![
            parse_quote! {
                #lt_quant #cursor_type: #cursor_trait
            },
            parse_quote! {
                <#cursor_type as #cursor_basic_trait>::ReturnedKey: ::std::convert::AsRef<[u8]>
            },
            parse_quote! {
                <#cursor_type as #cursor_basic_trait>::ReturnedValue: ::std::convert::AsRef<[u8]>
            },
        ],
    );
}

/// Helper function used to implement
/// [`require_binary_cursor`][require_binary_cursor].
///
/// [require_binary_cursor]: self::require_binary_cursor
fn require_binary_cursor_internal(
    attr: TokenStream,
    item: TokenStream,
) -> Result<TokenStream, syn::Error> {
    let args = parse2(attr)?;

    // Construct the required lifetime names in a way that won't conflict with
    // any lifetimes that might be mentioned in the arguments.
    let lt_names = name_lifetimes(&args);

    // Parse the item and augment its where clause with the required bounds.
    let mut output = parse2(item)?;
    add_bounds(find_generics_mut(&mut output)?, &args, &lt_names);
    Ok(output.into_token_stream())
}

/// Implementation for the
/// [`require_binary_cursor`][require_binary_cursor] macro. The main difference
/// between this function and the macro is that this function uses the
/// `proc_macro2` crate in its signature, so that it can be unit tested.
///
/// [require_binary_cursor]: crate::require_binary_cursor
pub(crate) fn require_binary_cursor(attr: TokenStream, item: TokenStream) -> TokenStream {
    match require_binary_cursor_internal(attr, item) {
        Ok(tokens) => tokens,
        Err(err) => err.to_compile_error(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use syn::Item;

    /// Tests the `name_lifetimes` function.
    #[test]
    fn name_lifetimes_test() {
        let lt_names = name_lifetimes(&parse_quote! { A });
        assert_eq!(
            lt_names,
            BoundsLifetimeNames {
                cursor_lt: parse_quote! { 'cursor },
                kq_lt: parse_quote! { 'kq },
            }
        );

        let lt_names = name_lifetimes(&parse_quote! { A<'a> });
        assert_eq!(
            lt_names,
            BoundsLifetimeNames {
                cursor_lt: parse_quote! { 'cursor },
                kq_lt: parse_quote! { 'kq },
            }
        );

        let lt_names = name_lifetimes(&parse_quote! { A<'cursor, 'kq> });
        assert_eq!(
            lt_names,
            BoundsLifetimeNames {
                cursor_lt: parse_quote! { 'cursor_0 },
                kq_lt: parse_quote! { 'kq_0 },
            }
        );

        let lt_names = name_lifetimes(&parse_quote! { A<'cursor, 'cursor_0, 'cursor_1>, ::akvs });
        assert_eq!(
            lt_names,
            BoundsLifetimeNames {
                cursor_lt: parse_quote! { 'cursor_2 },
                kq_lt: parse_quote! { 'kq },
            }
        );
    }

    /// Tests the `add_bounds` function.
    #[test]
    fn add_bounds_test() {
        let mut test_case =
            parse_quote! { fn do_something<C>(cursor: &mut C) where C: ::std::fmt::Debug {} };
        let generics = find_generics_mut(&mut test_case).unwrap();
        add_bounds(
            generics,
            &parse_quote! { C, crate },
            &BoundsLifetimeNames {
                cursor_lt: parse_quote! { 'cursor },
                kq_lt: parse_quote! { 'kq },
            },
        );
        assert_eq!(
            generics.where_clause,
            Some(parse_quote! {
            where C: ::std::fmt::Debug,
            for<'cursor, 'kq,> C: crate::Cursor<'cursor, &'kq [u8],>,
            <C as crate::CursorBasic>::ReturnedKey: ::std::convert::AsRef<[u8]>,
            <C as crate::CursorBasic>::ReturnedValue: ::std::convert::AsRef<[u8]>
            })
        );

        let mut test_case =
            parse_quote! { fn do_something<C>(cursor: &mut C) where C: ::std::fmt::Debug {} };
        let generics = find_generics_mut(&mut test_case).unwrap();
        add_bounds(
            generics,
            &parse_quote! { C },
            &BoundsLifetimeNames {
                cursor_lt: parse_quote! { 'cursor },
                kq_lt: parse_quote! { 'kq },
            },
        );
        assert_eq!(
            generics.where_clause,
            Some(parse_quote! {
            where C: ::std::fmt::Debug,
            for<'cursor, 'kq,> C: ::atelier_kv_store::Cursor<'cursor, &'kq [u8],>,
            <C as ::atelier_kv_store::CursorBasic>::ReturnedKey: ::std::convert::AsRef<[u8]>,
            <C as ::atelier_kv_store::CursorBasic>::ReturnedValue: ::std::convert::AsRef<[u8]>
            })
        );
    }

    /// Tests the `require_binary_cursor_internal` function.
    #[test]
    fn require_binary_cursor_internal_test() {
        let test_output: Item = parse2(
            require_binary_cursor_internal(
                parse_quote! { C, crate },
                parse_quote! { fn do_something<C>(cursor: &mut C) {} },
            )
            .unwrap(),
        )
        .unwrap();
        assert_eq!(
            test_output,
            parse_quote! {
                fn do_something<C>(cursor: &mut C) where
                    for<'cursor, 'kq,> C: crate::Cursor<'cursor, &'kq [u8],>,
                    <C as crate::CursorBasic>::ReturnedKey: ::std::convert::AsRef<[u8]>,
                    <C as crate::CursorBasic>::ReturnedValue: ::std::convert::AsRef<[u8]>
                {}
            }
        );

        let test_output: Item = parse2(
            require_binary_cursor_internal(
                parse_quote! { C, crate },
                parse_quote! { fn do_something<C>(cursor: &mut C) where C: ::std::fmt::Debug {} },
            )
            .unwrap(),
        )
        .unwrap();
        assert_eq!(
            test_output,
            parse_quote! {
                fn do_something<C>(cursor: &mut C) where
                    C: ::std::fmt::Debug,
                    for<'cursor, 'kq,> C: crate::Cursor<'cursor, &'kq [u8],>,
                    <C as crate::CursorBasic>::ReturnedKey: ::std::convert::AsRef<[u8]>,
                    <C as crate::CursorBasic>::ReturnedValue: ::std::convert::AsRef<[u8]>
                {}
            }
        );

        let test_output: Item = parse2(
            require_binary_cursor_internal(
                parse_quote! { C },
                parse_quote! { fn do_something<C>(cursor: &mut C) where C: ::std::fmt::Debug {} },
            )
            .unwrap(),
        )
        .unwrap();
        assert_eq!(
            test_output,
            parse_quote! {
                fn do_something<C>(cursor: &mut C) where
                    C: ::std::fmt::Debug,
                    for<'cursor, 'kq,> C: ::atelier_kv_store::Cursor<'cursor, &'kq [u8],>,
                    <C as ::atelier_kv_store::CursorBasic>::ReturnedKey: ::std::convert::AsRef<[u8]>,
                    <C as ::atelier_kv_store::CursorBasic>::ReturnedValue: ::std::convert::AsRef<[u8]>
                    {}
            }
        );

        require_binary_cursor_internal(
            parse_quote! {},
            parse_quote! { fn do_something<C>(cursor: &mut C) where C: ::std::fmt::Debug {} },
        )
        .unwrap_err();

        require_binary_cursor_internal(
            parse_quote! { C, self, X },
            parse_quote! { fn do_something<C>(cursor: &mut C) where C: ::std::fmt::Debug {} },
        )
        .unwrap_err();

        require_binary_cursor_internal(parse_quote! { C }, parse_quote! { const X: u32 = 0; })
            .unwrap_err();
    }

    /// Tests the `require_binary_cursor` function.
    #[test]
    fn require_binary_cursor_test() {
        let test_output: Item = parse2(require_binary_cursor(
            parse_quote! { C, crate },
            parse_quote! { fn do_something<C>(cursor: &mut C) {} },
        ))
        .unwrap();
        assert_eq!(
            test_output,
            parse_quote! {
                fn do_something<C>(cursor: &mut C) where
                    for<'cursor, 'kq,> C: crate::Cursor<'cursor, &'kq [u8],>,
                    <C as crate::CursorBasic>::ReturnedKey: ::std::convert::AsRef<[u8]>,
                    <C as crate::CursorBasic>::ReturnedValue: ::std::convert::AsRef<[u8]>
                {}
            }
        );

        let test_output: Item = parse2(require_binary_cursor(
            parse_quote! { C, crate },
            parse_quote! { fn do_something<C>(cursor: &mut C) where C: ::std::fmt::Debug {} },
        ))
        .unwrap();
        assert_eq!(
            test_output,
            parse_quote! {
                fn do_something<C>(cursor: &mut C) where
                    C: ::std::fmt::Debug,
                    for<'cursor, 'kq,> C: crate::Cursor<'cursor, &'kq [u8],>,
                    <C as crate::CursorBasic>::ReturnedKey: ::std::convert::AsRef<[u8]>,
                    <C as crate::CursorBasic>::ReturnedValue: ::std::convert::AsRef<[u8]>
                {}
            }
        );

        let test_output: Item = parse2(require_binary_cursor(
            parse_quote! { C },
            parse_quote! { fn do_something<C>(cursor: &mut C) where C: ::std::fmt::Debug {} },
        ))
        .unwrap();
        assert_eq!(
            test_output,
            parse_quote! {
                fn do_something<C>(cursor: &mut C) where
                    C: ::std::fmt::Debug,
                    for<'cursor, 'kq,> C: ::atelier_kv_store::Cursor<'cursor, &'kq [u8],>,
                    <C as ::atelier_kv_store::CursorBasic>::ReturnedKey: ::std::convert::AsRef<[u8]>,
                    <C as ::atelier_kv_store::CursorBasic>::ReturnedValue: ::std::convert::AsRef<[u8]>
                {}
            }
        );

        let test_output: Result<Item, _> = parse2(require_binary_cursor(
            parse_quote! {},
            parse_quote! { fn do_something<C>(cursor: &mut C) where C: ::std::fmt::Debug {} },
        ));
        // The output is expected to produce a compiler error, but it should
        // still parse.
        test_output.unwrap();

        let test_output: Result<Item, _> = parse2(require_binary_cursor(
            parse_quote! { C, self, X },
            parse_quote! { fn do_something<C>(cursor: &mut C) where C: ::std::fmt::Debug {} },
        ));
        // The output is expected to produce a compiler error, but it should
        // still parse.
        test_output.unwrap();

        let test_output: Result<Item, _> = parse2(require_binary_cursor(
            parse_quote! { C },
            parse_quote! { const X: u32 = 0; },
        ));
        // The output is expected to produce a compiler error, but it should
        // still parse.
        test_output.unwrap();
    }
}
