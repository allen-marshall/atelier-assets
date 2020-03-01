//! This module contains the implementation for the
//! [`require_binary_rw_txn`][require_binary_rw_txn] macro.
//!
//! [require_binary_rw_txn]: crate::require_binary_rw_txn

use crate::binary_static_env::{rw_txn_trait_bound, txn_basic_trait_bound, TypeAndCrateRootArgs};
use crate::{
    add_where_predicates, find_generics_mut, remove_ident_name_conflicts, LifetimeNameFinder,
};
use proc_macro2::{Span, TokenStream};
use quote::ToTokens;
use syn::visit::{visit_path, visit_type};
use syn::{parse2, parse_quote, BoundLifetimes, Lifetime};

/// Represents the lifetime names to be used in the output of a specific
/// invocation of the [`require_binary_rw_txn`][require_binary_rw_txn] macro
/// attribute.
///
/// [require_binary_rw_txn]: crate::require_binary_rw_txn
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct BoundsLifetimeNames {
    /// Lifetime name for transaction references.
    txn_lt: Lifetime,
}

/// Chooses names for the lifetimes to be used in the output of a specific
/// invocation of the [`require_binary_rw_txn`][require_binary_rw_txn] macro
/// attribute.
///
/// For clarity of error messages, this function tries to choose descriptive
/// names for the lifetimes. It must ensure that it does not choose names that
/// conflict with any lifetimes used in the arguments to the macro.
///
/// [require_binary_rw_txn]: crate::require_binary_rw_txn
fn name_lifetimes(args: &TypeAndCrateRootArgs) -> BoundsLifetimeNames {
    fn name_to_lifetime(name: &str) -> Lifetime {
        Lifetime::new(&format!("'{}", name), Span::call_site())
    }

    // Choose names for the lifetimes, avoiding any conflicts with lifetime
    // names used in the macro arguments.
    let mut forbidden_finder = LifetimeNameFinder::default();
    visit_type(&mut forbidden_finder, &args.type_arg);
    visit_path(&mut forbidden_finder, &args.crate_root_path);
    let mut chosen_names = vec!["txn".to_string()];
    remove_ident_name_conflicts(&mut chosen_names, &forbidden_finder.names_found());

    BoundsLifetimeNames {
        txn_lt: name_to_lifetime(&chosen_names[0]),
    }
}

/// Implementation for the
/// [`require_binary_rw_txn`][require_binary_txn] macro. The main difference
/// between this function and the macro is that this function uses the
/// `proc_macro2` crate in its signature, so that it can be unit tested.
///
/// [require_binary_txn]: crate::require_binary_txn
pub(crate) fn require_binary_rw_txn(attr: TokenStream, item: TokenStream) -> TokenStream {
    // Internal helper function used to enable ? for error handling.
    fn inner(attr: TokenStream, item: TokenStream) -> Result<TokenStream, syn::Error> {
        let args = parse2(attr)?;

        // Construct the required lifetime names in a way that won't conflict with
        // any lifetimes that might be mentioned in the arguments.
        let lt_names = name_lifetimes(&args);

        // Bring parameters into scope so we can use them in parse_quote.
        let (txn_lt, txn_type) = (&lt_names.txn_lt, &args.type_arg);

        let lt_quant: BoundLifetimes = parse_quote! { for<#txn_lt,> };
        let txn_basic_trait = txn_basic_trait_bound(&args.crate_root_path);
        let rw_txn_trait = rw_txn_trait_bound(&lt_names.txn_lt, &args.crate_root_path);

        // Parse the item and augment its where clause with the required bounds.
        let mut output = parse2(item)?;
        add_where_predicates(
            find_generics_mut(&mut output)?,
            vec![
                parse_quote! {
                    #lt_quant #txn_type: #rw_txn_trait
                },
                parse_quote! {
                    <#txn_type as #txn_basic_trait>::ReturnedKey: ::std::convert::AsRef<[u8]>
                },
                parse_quote! {
                    <#txn_type as #txn_basic_trait>::ReturnedValue: ::std::convert::AsRef<[u8]>
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
                txn_lt: parse_quote! { 'txn },
            }
        );

        let lt_names = name_lifetimes(&parse_quote! { A<'a> });
        assert_eq!(
            lt_names,
            BoundsLifetimeNames {
                txn_lt: parse_quote! { 'txn },
            }
        );

        let lt_names = name_lifetimes(&parse_quote! { A<'txn> });
        assert_eq!(
            lt_names,
            BoundsLifetimeNames {
                txn_lt: parse_quote! { 'txn_0 },
            }
        );

        let lt_names = name_lifetimes(&parse_quote! { A<'txn, 'txn_0, 'txn_1>, ::akvs });
        assert_eq!(
            lt_names,
            BoundsLifetimeNames {
                txn_lt: parse_quote! { 'txn_2 },
            }
        );
    }

    /// Tests the `require_binary_rw_txn` function.
    #[test]
    fn require_binary_rw_txn_test() {
        let test_output: Item = parse2(require_binary_rw_txn(
            parse_quote! { T, crate },
            parse_quote! { fn do_something<T>(txn: &mut T) {} },
        ))
        .unwrap();
        assert_eq!(
            test_output,
            parse_quote! {
                fn do_something<T>(txn: &mut T) where
                    for<'txn,> T: crate::ReadWriteTransaction<'txn, [u8], [u8], [u8],>,
                    <T as crate::TransactionBasic>::ReturnedKey: ::std::convert::AsRef<[u8]>,
                    <T as crate::TransactionBasic>::ReturnedValue: ::std::convert::AsRef<[u8]>
                {}
            }
        );

        let test_output: Item = parse2(require_binary_rw_txn(
            parse_quote! { &'txn T, crate },
            parse_quote! { fn do_something<T>(txn: &mut T) where T: ::std::fmt::Debug {} },
        ))
        .unwrap();
        assert_eq!(
            test_output,
            parse_quote! {
                fn do_something<T>(txn: &mut T) where
                    T: ::std::fmt::Debug,
                    for<'txn_0,> &'txn T: crate::ReadWriteTransaction<'txn_0, [u8], [u8], [u8],>,
                    <&'txn T as crate::TransactionBasic>::ReturnedKey: ::std::convert::AsRef<[u8]>,
                    <&'txn T as crate::TransactionBasic>::ReturnedValue: ::std::convert::AsRef<[u8]>
                {}
            }
        );

        let test_output: Item = parse2(require_binary_rw_txn(
            parse_quote! { T },
            parse_quote! { fn do_something<T>(txn: &mut T) where T: ::std::fmt::Debug {} },
        ))
        .unwrap();
        assert_eq!(
            test_output,
            parse_quote! {
                fn do_something<T>(txn: &mut T) where
                    T: ::std::fmt::Debug,
                    for<'txn,> T: ::atelier_kv_store::ReadWriteTransaction<'txn, [u8], [u8], [u8],>,
                    <T as ::atelier_kv_store::TransactionBasic>::ReturnedKey: ::std::convert::AsRef<[u8]>,
                    <T as ::atelier_kv_store::TransactionBasic>::ReturnedValue: ::std::convert::AsRef<[u8]>
                {}
            }
        );

        let test_output: Result<Item, _> = parse2(require_binary_rw_txn(
            parse_quote! {},
            parse_quote! { fn do_something<T>(txn: &mut T) where T: ::std::fmt::Debug {} },
        ));
        // The output is expected to produce a compiler error, but it should
        // still parse.
        test_output.unwrap();

        let test_output: Result<Item, _> = parse2(require_binary_rw_txn(
            parse_quote! { T, self, X },
            parse_quote! { fn do_something<T>(txn: &mut T) where T: ::std::fmt::Debug {} },
        ));
        // The output is expected to produce a compiler error, but it should
        // still parse.
        test_output.unwrap();

        let test_output: Result<Item, _> = parse2(require_binary_rw_txn(
            parse_quote! { T },
            parse_quote! { const X: u32 = 0; },
        ));
        // The output is expected to produce a compiler error, but it should
        // still parse.
        test_output.unwrap();
    }
}
