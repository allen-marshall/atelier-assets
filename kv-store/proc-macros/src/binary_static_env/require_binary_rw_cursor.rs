//! This module contains the implementation for the
//! [`require_binary_rw_cursor`][require_binary_rw_cursor] macro.
//!
//! [require_binary_rw_cursor]: crate::require_binary_rw_cursor

use crate::binary_static_env::{
    cursor_basic_trait_bound, rw_cursor_trait_bound, TypeAndCrateRootArgs,
};
use crate::{
    add_where_predicates, find_generics_mut, remove_ident_name_conflicts, LifetimeNameFinder,
};
use proc_macro2::{Span, TokenStream};
use quote::ToTokens;
use syn::visit::{visit_path, visit_type};
use syn::{parse2, parse_quote, BoundLifetimes, Lifetime};

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

    /// Lifetime name for key references used in insertions.
    kp_lt: Lifetime,

    /// Lifetime name for value references used in insertions.
    vp_lt: Lifetime,
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
    let mut chosen_names = vec![
        "cursor".to_string(),
        "kq".to_string(),
        "kp".to_string(),
        "vp".to_string(),
    ];
    remove_ident_name_conflicts(&mut chosen_names, &forbidden_finder.names_found());

    BoundsLifetimeNames {
        cursor_lt: name_to_lifetime(&chosen_names[0]),
        kq_lt: name_to_lifetime(&chosen_names[1]),
        kp_lt: name_to_lifetime(&chosen_names[2]),
        vp_lt: name_to_lifetime(&chosen_names[3]),
    }
}

/// Implementation for the
/// [`require_binary_rw_cursor`][require_binary_rw_cursor] macro. The main
/// difference between this function and the macro is that this function uses
/// the `proc_macro2` crate in its signature, so that it can be unit tested.
///
/// [require_binary_rw_cursor]: crate::require_binary_rw_cursor
pub(crate) fn require_binary_rw_cursor(attr: TokenStream, item: TokenStream) -> TokenStream {
    // Internal helper function used to enable ? for error handling.
    fn inner(attr: TokenStream, item: TokenStream) -> Result<TokenStream, syn::Error> {
        let args = parse2(attr)?;

        // Construct the required lifetime names in a way that won't conflict with
        // any lifetimes that might be mentioned in the arguments.
        let lt_names = name_lifetimes(&args);

        // Bring parameters into scope so we can use them in parse_quote.
        let (cursor_lt, kq_lt, kp_lt, vp_lt, cursor_type) = (
            &lt_names.cursor_lt,
            &lt_names.kq_lt,
            &lt_names.kp_lt,
            &lt_names.vp_lt,
            &args.type_arg,
        );

        let lt_quant: BoundLifetimes = parse_quote! { for<#cursor_lt, #kq_lt, #kp_lt, #vp_lt,> };
        let cursor_basic_trait = cursor_basic_trait_bound(&args.crate_root_path);
        let rw_cursor_trait = rw_cursor_trait_bound(
            &lt_names.cursor_lt,
            &lt_names.kq_lt,
            &lt_names.kp_lt,
            &lt_names.vp_lt,
            &args.crate_root_path,
        );

        // Parse the item and augment its where clause with the required bounds.
        let mut output = parse2(item)?;
        add_where_predicates(
            find_generics_mut(&mut output)?,
            vec![
                parse_quote! {
                    #lt_quant #cursor_type: #rw_cursor_trait
                },
                parse_quote! {
                    <#cursor_type as #cursor_basic_trait>::ReturnedKey: ::std::convert::AsRef<[u8]>
                },
                parse_quote! {
                    <#cursor_type as #cursor_basic_trait>::ReturnedValue: ::std::convert::AsRef<[u8]>
                },
            ],
        );
        Ok(output.into_token_stream())
    }
    match inner(attr, item) {
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
                kp_lt: parse_quote! { 'kp },
                vp_lt: parse_quote! { 'vp },
            }
        );

        let lt_names = name_lifetimes(&parse_quote! { A<'a> });
        assert_eq!(
            lt_names,
            BoundsLifetimeNames {
                cursor_lt: parse_quote! { 'cursor },
                kq_lt: parse_quote! { 'kq },
                kp_lt: parse_quote! { 'kp },
                vp_lt: parse_quote! { 'vp },
            }
        );

        let lt_names = name_lifetimes(&parse_quote! { A<'cursor, 'kp> });
        assert_eq!(
            lt_names,
            BoundsLifetimeNames {
                cursor_lt: parse_quote! { 'cursor_0 },
                kq_lt: parse_quote! { 'kq },
                kp_lt: parse_quote! { 'kp_0 },
                vp_lt: parse_quote! { 'vp },
            }
        );

        let lt_names = name_lifetimes(&parse_quote! { A<'cursor, 'cursor_0, 'cursor_1>, ::akvs });
        assert_eq!(
            lt_names,
            BoundsLifetimeNames {
                cursor_lt: parse_quote! { 'cursor_2 },
                kq_lt: parse_quote! { 'kq },
                kp_lt: parse_quote! { 'kp },
                vp_lt: parse_quote! { 'vp },
            }
        );
    }

    /// Tests the `require_binary_rw_cursor` function.
    #[test]
    fn require_binary_rw_cursor_test() {
        let test_output: Item = parse2(require_binary_rw_cursor(
            parse_quote! { C, crate },
            parse_quote! { fn do_something<C>(cursor: &mut C) {} },
        ))
        .unwrap();
        assert_eq!(
            test_output,
            parse_quote! {
                fn do_something<C>(cursor: &mut C) where
                    for<'cursor, 'kq, 'kp, 'vp,> C: crate::ReadWriteCursor<'cursor, &'kq [u8], &'kp [u8], &'vp [u8],>,
                    <C as crate::CursorBasic>::ReturnedKey: ::std::convert::AsRef<[u8]>,
                    <C as crate::CursorBasic>::ReturnedValue: ::std::convert::AsRef<[u8]>
                {}
            }
        );

        let test_output: Item = parse2(require_binary_rw_cursor(
            parse_quote! { &'cursor C, crate },
            parse_quote! { fn do_something<C>(cursor: &mut C) where C: ::std::fmt::Debug {} },
        ))
        .unwrap();
        assert_eq!(
            test_output,
            parse_quote! {
                fn do_something<C>(cursor: &mut C) where
                    C: ::std::fmt::Debug,
                    for<'cursor_0, 'kq, 'kp, 'vp,> &'cursor C: crate::ReadWriteCursor<'cursor_0, &'kq [u8], &'kp [u8], &'vp [u8],>,
                    <&'cursor C as crate::CursorBasic>::ReturnedKey: ::std::convert::AsRef<[u8]>,
                    <&'cursor C as crate::CursorBasic>::ReturnedValue: ::std::convert::AsRef<[u8]>
                {}
            }
        );

        let test_output: Item = parse2(require_binary_rw_cursor(
            parse_quote! { C },
            parse_quote! { fn do_something<C>(cursor: &mut C) where C: ::std::fmt::Debug {} },
        ))
        .unwrap();
        assert_eq!(
            test_output,
            parse_quote! {
                fn do_something<C>(cursor: &mut C) where
                    C: ::std::fmt::Debug,
                    for<'cursor, 'kq, 'kp, 'vp,> C: ::atelier_kv_store::ReadWriteCursor<'cursor, &'kq [u8], &'kp [u8], &'vp [u8],>,
                    <C as ::atelier_kv_store::CursorBasic>::ReturnedKey: ::std::convert::AsRef<[u8]>,
                    <C as ::atelier_kv_store::CursorBasic>::ReturnedValue: ::std::convert::AsRef<[u8]>
                {}
            }
        );

        let test_output: Result<Item, _> = parse2(require_binary_rw_cursor(
            parse_quote! {},
            parse_quote! { fn do_something<C>(cursor: &mut C) where C: ::std::fmt::Debug {} },
        ));
        // The output is expected to produce a compiler error, but it should
        // still parse.
        test_output.unwrap();

        let test_output: Result<Item, _> = parse2(require_binary_rw_cursor(
            parse_quote! { C, self, X },
            parse_quote! { fn do_something<C>(cursor: &mut C) where C: ::std::fmt::Debug {} },
        ));
        // The output is expected to produce a compiler error, but it should
        // still parse.
        test_output.unwrap();

        let test_output: Result<Item, _> = parse2(require_binary_rw_cursor(
            parse_quote! { C },
            parse_quote! { const X: u32 = 0; },
        ));
        // The output is expected to produce a compiler error, but it should
        // still parse.
        test_output.unwrap();
    }
}
