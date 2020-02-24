//! This module contains the implementation for the
//! [`require_binary_txn`][require_binary_txn] macro.
//!
//! [require_binary_txn]: crate::require_binary_txn

use crate::binary_static_env::{cursor_basic_trait_bound, txn_trait_bound, TypeAndCrateRootArgs};
use crate::{
    add_where_predicates, find_generics_mut, remove_ident_name_conflicts, LifetimeNameFinder,
};
use proc_macro2::{Span, TokenStream};
use quote::ToTokens;
use syn::visit::{visit_path, visit_type};
use syn::{parse2, parse_quote, BoundLifetimes, Generics, Lifetime, TypeParamBound};

/// Represents the lifetime names to be used in the output of a specific
/// invocation of the [`require_binary_txn`][require_binary_txn] macro
/// attribute.
///
/// [require_binary_txn]: crate::require_binary_txn
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct BoundsLifetimeNames {
    /// Lifetime name for transaction references.
    txn_lt: Lifetime,

    /// Lifetime name for key references used in queries.
    kq_lt: Lifetime,
}

/// Chooses names for the lifetimes to be used in the output of a specific
/// invocation of the [`require_binary_txn`][require_binary_txn] macro
/// attribute.
///
/// For clarity of error messages, this function tries to choose descriptive
/// names for the lifetimes. It must ensure that it does not choose names that
/// conflict with any lifetimes used in the arguments to the macro.
///
/// [require_binary_txn]: crate::require_binary_txn
fn name_lifetimes(args: &TypeAndCrateRootArgs) -> BoundsLifetimeNames {
    fn name_to_lifetime(name: &str) -> Lifetime {
        Lifetime::new(&format!("'{}", name), Span::call_site())
    }

    // Choose names for the lifetimes, avoiding any conflicts with lifetime
    // names used in the macro arguments.
    let mut forbidden_finder = LifetimeNameFinder::default();
    visit_type(&mut forbidden_finder, &args.type_arg);
    visit_path(&mut forbidden_finder, &args.crate_root_path);
    let mut chosen_names = vec!["txn".to_string(), "kq".to_string()];
    remove_ident_name_conflicts(&mut chosen_names, &forbidden_finder.names_found());

    BoundsLifetimeNames {
        txn_lt: name_to_lifetime(&chosen_names[0]),
        kq_lt: name_to_lifetime(&chosen_names[1]),
    }
}

/// Gets the trait bound that should be used to require [`AsRef`][AsRef]`<[u8]>`
/// for a type.
///
/// [AsRef]: std::convert::AsRef
fn as_ref_trait_bound(
    args: &TypeAndCrateRootArgs,
    lt_names: &BoundsLifetimeNames,
) -> TypeParamBound {
    // Bring parameters into scope so we can use them in parse_quote.
    let (crate_root_path, txn_lt, kq_lt) =
        (&args.crate_root_path, &lt_names.txn_lt, &lt_names.kq_lt);
    parse_quote! {
        #crate_root_path::lt_trait_wrappers::AsRefLt2<
            #txn_lt,
            #kq_lt,
            [u8],
        >
    }
}

/// Modifies the specified generics data so that its `where` clause contains the
/// bounds required to use a binary storage transaction, i.e. the bounds
/// needed when using [`require_binary_txn`][require_binary_txn].
///
/// [require_binary_txn]: crate::require_binary_txn
fn add_bounds(
    generics: &mut Generics,
    args: &TypeAndCrateRootArgs,
    lt_names: &BoundsLifetimeNames,
) {
    // Bring parameters into scope so we can use them in parse_quote.
    let (txn_lt, kq_lt, txn_type) = (&lt_names.txn_lt, &lt_names.kq_lt, &args.type_arg);

    let lt_quant: BoundLifetimes = parse_quote! { for<#txn_lt, #kq_lt,> };
    let txn_trait = txn_trait_bound(&lt_names.txn_lt, &lt_names.kq_lt, &args.crate_root_path);
    let cursor_basic_trait = cursor_basic_trait_bound(&args.crate_root_path);
    let as_ref_trait = as_ref_trait_bound(&args, &lt_names);
    add_where_predicates(
        generics,
        vec![
            parse_quote! {
                #lt_quant #txn_type: #txn_trait
            },
            parse_quote! {
                #lt_quant <#txn_type as #txn_trait>::ReturnedValue: #as_ref_trait
            },
            parse_quote! {
                #lt_quant <<#txn_type as #txn_trait>::RoCursor as #cursor_basic_trait>::ReturnedKey: #as_ref_trait
            },
            parse_quote! {
                #lt_quant <<#txn_type as #txn_trait>::RoCursor as #cursor_basic_trait>::ReturnedValue: #as_ref_trait
            },
        ],
    );
}

/// Helper function used to implement
/// [`require_binary_txn`][require_binary_txn].
///
/// [require_binary_txn]: self::require_binary_txn
fn require_binary_txn_internal(
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
/// [`require_binary_txn`][require_binary_txn] macro. The main difference
/// between this function and the macro is that this function uses the
/// `proc_macro2` crate in its signature, so that it can be unit tested.
///
/// [require_binary_txn]: crate::require_binary_txn
pub(crate) fn require_binary_txn(attr: TokenStream, item: TokenStream) -> TokenStream {
    match require_binary_txn_internal(attr, item) {
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
                txn_lt: parse_quote! { 'txn },
                kq_lt: parse_quote! { 'kq },
            }
        );

        let lt_names = name_lifetimes(&parse_quote! { A<'a> });
        assert_eq!(
            lt_names,
            BoundsLifetimeNames {
                txn_lt: parse_quote! { 'txn },
                kq_lt: parse_quote! { 'kq },
            }
        );

        let lt_names = name_lifetimes(&parse_quote! { A<'txn, 'kq> });
        assert_eq!(
            lt_names,
            BoundsLifetimeNames {
                txn_lt: parse_quote! { 'txn_0 },
                kq_lt: parse_quote! { 'kq_0 },
            }
        );

        let lt_names = name_lifetimes(&parse_quote! { A<'txn, 'txn_0, 'txn_1>, ::akvs });
        assert_eq!(
            lt_names,
            BoundsLifetimeNames {
                txn_lt: parse_quote! { 'txn_2 },
                kq_lt: parse_quote! { 'kq },
            }
        );
    }

    /// Tests the `as_ref_trait_bound` function.
    #[test]
    fn as_ref_trait_bound_test() {
        let bound = as_ref_trait_bound(
            &parse_quote! { A, crate },
            &BoundsLifetimeNames {
                txn_lt: parse_quote! { 'txn },
                kq_lt: parse_quote! { 'kq },
            },
        );
        assert_eq!(
            bound,
            parse_quote! {
                crate::lt_trait_wrappers::AsRefLt2<
                    'txn,
                    'kq,
                    [u8],
                >
            }
        );

        let bound = as_ref_trait_bound(
            &parse_quote! { A },
            &BoundsLifetimeNames {
                txn_lt: parse_quote! { 'txn_1 },
                kq_lt: parse_quote! { 'kq_0 },
            },
        );
        assert_eq!(
            bound,
            parse_quote! {
                ::atelier_kv_store::lt_trait_wrappers::AsRefLt2<
                    'txn_1,
                    'kq_0,
                    [u8],
                >
            }
        );
    }

    /// Tests the `add_bounds` function.
    #[test]
    fn add_bounds_test() {
        let mut test_case =
            parse_quote! { fn do_something<T>(txn: &mut T) where T: ::std::fmt::Debug {} };
        let generics = find_generics_mut(&mut test_case).unwrap();
        add_bounds(
            generics,
            &parse_quote! { T, crate },
            &BoundsLifetimeNames {
                txn_lt: parse_quote! { 'txn },
                kq_lt: parse_quote! { 'kq },
            },
        );
        assert_eq!(
            generics.where_clause,
            Some(parse_quote! {
            where T: ::std::fmt::Debug,
            for<'txn, 'kq,> T: crate::Transaction<'txn, &'kq [u8],>,
            for<'txn, 'kq,> <T as crate::Transaction<'txn, &'kq [u8],>>::ReturnedValue: crate::lt_trait_wrappers::AsRefLt2<'txn, 'kq, [u8],>,
            for<'txn, 'kq,> <<T as crate::Transaction<'txn, &'kq [u8],>>::RoCursor as crate::CursorBasic>::ReturnedKey: crate::lt_trait_wrappers::AsRefLt2<'txn, 'kq, [u8],>,
            for<'txn, 'kq,> <<T as crate::Transaction<'txn, &'kq [u8],>>::RoCursor as crate::CursorBasic>::ReturnedValue: crate::lt_trait_wrappers::AsRefLt2<'txn, 'kq, [u8],>
            })
        );

        let mut test_case =
            parse_quote! { fn do_something<T>(txn: &mut T) where T: ::std::fmt::Debug {} };
        let generics = find_generics_mut(&mut test_case).unwrap();
        add_bounds(
            generics,
            &parse_quote! { T },
            &BoundsLifetimeNames {
                txn_lt: parse_quote! { 'txn },
                kq_lt: parse_quote! { 'kq },
            },
        );
        assert_eq!(
            generics.where_clause,
            Some(parse_quote! {
            where T: ::std::fmt::Debug,
            for<'txn, 'kq,> T: ::atelier_kv_store::Transaction<'txn, &'kq [u8],>,
            for<'txn, 'kq,> <T as ::atelier_kv_store::Transaction<'txn, &'kq [u8],>>::ReturnedValue: ::atelier_kv_store::lt_trait_wrappers::AsRefLt2<'txn, 'kq, [u8],>,
            for<'txn, 'kq,> <<T as ::atelier_kv_store::Transaction<'txn, &'kq [u8],>>::RoCursor as ::atelier_kv_store::CursorBasic>::ReturnedKey: ::atelier_kv_store::lt_trait_wrappers::AsRefLt2<'txn, 'kq, [u8],>,
            for<'txn, 'kq,> <<T as ::atelier_kv_store::Transaction<'txn, &'kq [u8],>>::RoCursor as ::atelier_kv_store::CursorBasic>::ReturnedValue: ::atelier_kv_store::lt_trait_wrappers::AsRefLt2<'txn, 'kq, [u8],>
            })
        );
    }

    /// Tests the `require_binary_txn_internal` function.
    #[test]
    fn require_binary_txn_internal_test() {
        let test_output: Item = parse2(
            require_binary_txn_internal(
                parse_quote! { T, crate },
                parse_quote! { fn do_something<T>(txn: &mut T) {} },
            )
            .unwrap(),
        )
        .unwrap();
        assert_eq!(
            test_output,
            parse_quote! {
                fn do_something<T>(txn: &mut T) where
                    for<'txn, 'kq,> T: crate::Transaction<'txn, &'kq [u8],>,
                    for<'txn, 'kq,> <T as crate::Transaction<'txn, &'kq [u8],>>::ReturnedValue: crate::lt_trait_wrappers::AsRefLt2<'txn, 'kq, [u8],>,
                    for<'txn, 'kq,> <<T as crate::Transaction<'txn, &'kq [u8],>>::RoCursor as crate::CursorBasic>::ReturnedKey: crate::lt_trait_wrappers::AsRefLt2<'txn, 'kq, [u8],>,
                    for<'txn, 'kq,> <<T as crate::Transaction<'txn, &'kq [u8],>>::RoCursor as crate::CursorBasic>::ReturnedValue: crate::lt_trait_wrappers::AsRefLt2<'txn, 'kq, [u8],>
                {}
            }
        );

        let test_output: Item = parse2(
            require_binary_txn_internal(
                parse_quote! { T, crate },
                parse_quote! { fn do_something<T>(txn: &mut T) where T: ::std::fmt::Debug {} },
            )
            .unwrap(),
        )
        .unwrap();
        assert_eq!(
            test_output,
            parse_quote! {
                fn do_something<T>(txn: &mut T) where
                    T: ::std::fmt::Debug,
                    for<'txn, 'kq,> T: crate::Transaction<'txn, &'kq [u8],>,
                    for<'txn, 'kq,> <T as crate::Transaction<'txn, &'kq [u8],>>::ReturnedValue: crate::lt_trait_wrappers::AsRefLt2<'txn, 'kq, [u8],>,
                    for<'txn, 'kq,> <<T as crate::Transaction<'txn, &'kq [u8],>>::RoCursor as crate::CursorBasic>::ReturnedKey: crate::lt_trait_wrappers::AsRefLt2<'txn, 'kq, [u8],>,
                    for<'txn, 'kq,> <<T as crate::Transaction<'txn, &'kq [u8],>>::RoCursor as crate::CursorBasic>::ReturnedValue: crate::lt_trait_wrappers::AsRefLt2<'txn, 'kq, [u8],>
                {}
            }
        );

        let test_output: Item = parse2(
            require_binary_txn_internal(
                parse_quote! { T },
                parse_quote! { fn do_something<T>(txn: &mut T) where T: ::std::fmt::Debug {} },
            )
            .unwrap(),
        )
        .unwrap();
        assert_eq!(
            test_output,
            parse_quote! {
                fn do_something<T>(txn: &mut T) where
                    T: ::std::fmt::Debug,
                    for<'txn, 'kq,> T: ::atelier_kv_store::Transaction<'txn, &'kq [u8],>,
                    for<'txn, 'kq,> <T as ::atelier_kv_store::Transaction<'txn, &'kq [u8],>>::ReturnedValue: ::atelier_kv_store::lt_trait_wrappers::AsRefLt2<'txn, 'kq, [u8],>,
                    for<'txn, 'kq,> <<T as ::atelier_kv_store::Transaction<'txn, &'kq [u8],>>::RoCursor as ::atelier_kv_store::CursorBasic>::ReturnedKey: ::atelier_kv_store::lt_trait_wrappers::AsRefLt2<'txn, 'kq, [u8],>,
                    for<'txn, 'kq,> <<T as ::atelier_kv_store::Transaction<'txn, &'kq [u8],>>::RoCursor as ::atelier_kv_store::CursorBasic>::ReturnedValue: ::atelier_kv_store::lt_trait_wrappers::AsRefLt2<'txn, 'kq, [u8],>
                {}
            }
        );

        require_binary_txn_internal(
            parse_quote! {},
            parse_quote! { fn do_something<T>(txn: &mut T) where T: ::std::fmt::Debug {} },
        )
        .unwrap_err();

        require_binary_txn_internal(
            parse_quote! { T, self, X },
            parse_quote! { fn do_something<T>(txn: &mut T) where T: ::std::fmt::Debug {} },
        )
        .unwrap_err();

        require_binary_txn_internal(parse_quote! { T }, parse_quote! { const X: u32 = 0; })
            .unwrap_err();
    }

    /// Tests the `require_binary_txn` function.
    #[test]
    fn require_binary_txn_test() {
        let test_output: Item = parse2(require_binary_txn(
            parse_quote! { T, crate },
            parse_quote! { fn do_something<T>(txn: &mut T) {} },
        ))
        .unwrap();
        assert_eq!(
            test_output,
            parse_quote! {
                fn do_something<T>(txn: &mut T) where
                    for<'txn, 'kq,> T: crate::Transaction<'txn, &'kq [u8],>,
                    for<'txn, 'kq,> <T as crate::Transaction<'txn, &'kq [u8],>>::ReturnedValue: crate::lt_trait_wrappers::AsRefLt2<'txn, 'kq, [u8],>,
                    for<'txn, 'kq,> <<T as crate::Transaction<'txn, &'kq [u8],>>::RoCursor as crate::CursorBasic>::ReturnedKey: crate::lt_trait_wrappers::AsRefLt2<'txn, 'kq, [u8],>,
                    for<'txn, 'kq,> <<T as crate::Transaction<'txn, &'kq [u8],>>::RoCursor as crate::CursorBasic>::ReturnedValue: crate::lt_trait_wrappers::AsRefLt2<'txn, 'kq, [u8],>
                {}
            }
        );

        let test_output: Item = parse2(require_binary_txn(
            parse_quote! { T, crate },
            parse_quote! { fn do_something<T>(txn: &mut T) where T: ::std::fmt::Debug {} },
        ))
        .unwrap();
        assert_eq!(
            test_output,
            parse_quote! {
                fn do_something<T>(txn: &mut T) where
                    T: ::std::fmt::Debug,
                    for<'txn, 'kq,> T: crate::Transaction<'txn, &'kq [u8],>,
                    for<'txn, 'kq,> <T as crate::Transaction<'txn, &'kq [u8],>>::ReturnedValue: crate::lt_trait_wrappers::AsRefLt2<'txn, 'kq, [u8],>,
                    for<'txn, 'kq,> <<T as crate::Transaction<'txn, &'kq [u8],>>::RoCursor as crate::CursorBasic>::ReturnedKey: crate::lt_trait_wrappers::AsRefLt2<'txn, 'kq, [u8],>,
                    for<'txn, 'kq,> <<T as crate::Transaction<'txn, &'kq [u8],>>::RoCursor as crate::CursorBasic>::ReturnedValue: crate::lt_trait_wrappers::AsRefLt2<'txn, 'kq, [u8],>
                {}
            }
        );

        let test_output: Item = parse2(require_binary_txn(
            parse_quote! { T },
            parse_quote! { fn do_something<T>(txn: &mut T) where T: ::std::fmt::Debug {} },
        ))
        .unwrap();
        assert_eq!(
            test_output,
            parse_quote! {
                fn do_something<T>(txn: &mut T) where
                    T: ::std::fmt::Debug,
                    for<'txn, 'kq,> T: ::atelier_kv_store::Transaction<'txn, &'kq [u8],>,
                    for<'txn, 'kq,> <T as ::atelier_kv_store::Transaction<'txn, &'kq [u8],>>::ReturnedValue: ::atelier_kv_store::lt_trait_wrappers::AsRefLt2<'txn, 'kq, [u8],>,
                    for<'txn, 'kq,> <<T as ::atelier_kv_store::Transaction<'txn, &'kq [u8],>>::RoCursor as ::atelier_kv_store::CursorBasic>::ReturnedKey: ::atelier_kv_store::lt_trait_wrappers::AsRefLt2<'txn, 'kq, [u8],>,
                    for<'txn, 'kq,> <<T as ::atelier_kv_store::Transaction<'txn, &'kq [u8],>>::RoCursor as ::atelier_kv_store::CursorBasic>::ReturnedValue: ::atelier_kv_store::lt_trait_wrappers::AsRefLt2<'txn, 'kq, [u8],>
                {}
            }
        );

        let test_output: Result<Item, _> = parse2(require_binary_txn(
            parse_quote! {},
            parse_quote! { fn do_something<T>(txn: &mut T) where T: ::std::fmt::Debug {} },
        ));
        // The output is expected to produce a compiler error, but it should
        // still parse.
        test_output.unwrap();

        let test_output: Result<Item, _> = parse2(require_binary_txn(
            parse_quote! { T, self, X },
            parse_quote! { fn do_something<T>(txn: &mut T) where T: ::std::fmt::Debug {} },
        ));
        // The output is expected to produce a compiler error, but it should
        // still parse.
        test_output.unwrap();

        let test_output: Result<Item, _> = parse2(require_binary_txn(
            parse_quote! { T },
            parse_quote! { const X: u32 = 0; },
        ));
        // The output is expected to produce a compiler error, but it should
        // still parse.
        test_output.unwrap();
    }
}
