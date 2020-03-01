//! This module contains the implementation for the
//! [`require_binary_static_env`][require_binary_static_env] macro.
//!
//! [require_binary_static_env]: crate::require_binary_static_env

use crate::binary_static_env::{env_trait_bound, txn_basic_trait_bound, TypeAndCrateRootArgs};
use crate::{
    add_where_predicates, find_generics_mut, remove_ident_name_conflicts, LifetimeNameFinder,
};
use proc_macro2::{Span, TokenStream};
use quote::ToTokens;
use syn::visit::{visit_path, visit_type};
use syn::{parse2, parse_quote, BoundLifetimes, Lifetime, TypeParamBound};

/// Represents the lifetime names to be used in the output of a specific
/// invocation of the [`require_binary_static_env`][require_binary_static_env]
/// macro attribute.
///
/// [require_binary_static_env]: crate::require_binary_static_env
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct BoundsLifetimeNames {
    /// Lifetime name for environment references.
    env_lt: Lifetime,

    /// Lifetime name for transaction references.
    txn_lt: Lifetime,
}

/// Chooses names for the lifetimes to be used in the output of a specific
/// invocation of the [`require_binary_static_env`][require_binary_static_env]
/// macro attribute.
///
/// For clarity of error messages, this function tries to choose descriptive
/// names for the lifetimes. It must ensure that it does not choose names that
/// conflict with any lifetimes used in the arguments to the macro.
///
/// [require_binary_static_env]: crate::require_binary_static_env
fn name_lifetimes(args: &TypeAndCrateRootArgs) -> BoundsLifetimeNames {
    fn name_to_lifetime(name: &str) -> Lifetime {
        Lifetime::new(&format!("'{}", name), Span::call_site())
    }

    // Choose names for the lifetimes, avoiding any conflicts with lifetime
    // names used in the macro arguments.
    let mut forbidden_finder = LifetimeNameFinder::default();
    visit_type(&mut forbidden_finder, &args.type_arg);
    visit_path(&mut forbidden_finder, &args.crate_root_path);
    let mut chosen_names = vec!["env".to_string(), "txn".to_string()];
    remove_ident_name_conflicts(&mut chosen_names, &forbidden_finder.names_found());

    BoundsLifetimeNames {
        env_lt: name_to_lifetime(&chosen_names[0]),
        txn_lt: name_to_lifetime(&chosen_names[1]),
    }
}

/// Implementation for the
/// [`require_binary_static_env`][require_binary_static_env] macro. The main
/// difference between this function and the macro is that this function uses
/// the `proc_macro2` crate in its signature, so that it can be unit tested.
///
/// [require_binary_static_env]: crate::require_binary_static_env
pub(crate) fn require_binary_static_env(attr: TokenStream, item: TokenStream) -> TokenStream {
    // Internal helper function used to enable ? for error handling.
    fn inner(attr: TokenStream, item: TokenStream) -> Result<TokenStream, syn::Error> {
        let args = parse2(attr)?;

        // Construct the required lifetime names in a way that won't conflict with
        // any lifetimes that might be mentioned in the arguments.
        let lt_names = name_lifetimes(&args);

        // Bring parameters into scope so we can use them in parse_quote.
        let (env_lt, txn_lt, env_type, crate_root_path) = (
            &lt_names.env_lt,
            &lt_names.txn_lt,
            &args.type_arg,
            &args.crate_root_path,
        );

        let lt_quant_env: BoundLifetimes = parse_quote! { for<#env_lt,> };
        let lt_quant_txn: BoundLifetimes = parse_quote! { for<#env_lt, #txn_lt,> };
        let env_trait = env_trait_bound(&lt_names.env_lt, &args.crate_root_path);
        let txn_basic_trait = txn_basic_trait_bound(&args.crate_root_path);
        let as_ref_trait: TypeParamBound = parse_quote! {
            #crate_root_path::lt_trait_wrappers::AsRefLt2<#env_lt, #txn_lt, [u8],>
        };

        // Parse the item and augment its where clause with the required bounds.
        let mut output = parse2(item)?;
        add_where_predicates(
            find_generics_mut(&mut output)?,
            vec![
                parse_quote! {
                    #env_type: 'static + #lt_quant_env #env_trait
                },
                parse_quote! {
                    #lt_quant_txn <<#env_type as #env_trait>::RoTransaction as #txn_basic_trait>::ReturnedKey: #as_ref_trait
                },
                parse_quote! {
                    #lt_quant_txn <<#env_type as #env_trait>::RoTransaction as #txn_basic_trait>::ReturnedValue: #as_ref_trait
                },
                parse_quote! {
                    #lt_quant_txn <<#env_type as #env_trait>::RwTransaction as #txn_basic_trait>::ReturnedKey: #as_ref_trait
                },
                parse_quote! {
                    #lt_quant_txn <<#env_type as #env_trait>::RwTransaction as #txn_basic_trait>::ReturnedValue: #as_ref_trait
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
                env_lt: parse_quote! { 'env },
                txn_lt: parse_quote! { 'txn },
            }
        );

        let lt_names = name_lifetimes(&parse_quote! { A<'a> });
        assert_eq!(
            lt_names,
            BoundsLifetimeNames {
                env_lt: parse_quote! { 'env },
                txn_lt: parse_quote! { 'txn },
            }
        );

        let lt_names = name_lifetimes(&parse_quote! { A<'env> });
        assert_eq!(
            lt_names,
            BoundsLifetimeNames {
                env_lt: parse_quote! { 'env_0 },
                txn_lt: parse_quote! { 'txn },
            }
        );

        let lt_names = name_lifetimes(&parse_quote! { A<'env, 'env_0, 'env_1, 'txn>, ::akvs });
        assert_eq!(
            lt_names,
            BoundsLifetimeNames {
                env_lt: parse_quote! { 'env_2 },
                txn_lt: parse_quote! { 'txn_0 },
            }
        );
    }

    /// Tests the `require_binary_static_env` function.
    #[test]
    fn require_binary_static_env_test() {
        let test_output: Item = parse2(require_binary_static_env(
            parse_quote! { E, crate },
            parse_quote! { fn do_something<E>(env: &mut E) {} },
        ))
        .unwrap();
        assert_eq!(
            test_output,
            parse_quote! {
                fn do_something<E>(env: &mut E) where
                    E: 'static + for<'env,> crate::Environment<'env, [u8], [u8], [u8],>,
                    for<'env, 'txn,> <<E as crate::Environment<'env, [u8], [u8], [u8],>>::RoTransaction as crate::TransactionBasic>::ReturnedKey: crate::lt_trait_wrappers::AsRefLt2<'env, 'txn, [u8],>,
                    for<'env, 'txn,> <<E as crate::Environment<'env, [u8], [u8], [u8],>>::RoTransaction as crate::TransactionBasic>::ReturnedValue: crate::lt_trait_wrappers::AsRefLt2<'env, 'txn, [u8],>,
                    for<'env, 'txn,> <<E as crate::Environment<'env, [u8], [u8], [u8],>>::RwTransaction as crate::TransactionBasic>::ReturnedKey: crate::lt_trait_wrappers::AsRefLt2<'env, 'txn, [u8],>,
                    for<'env, 'txn,> <<E as crate::Environment<'env, [u8], [u8], [u8],>>::RwTransaction as crate::TransactionBasic>::ReturnedValue: crate::lt_trait_wrappers::AsRefLt2<'env, 'txn, [u8],>
                {}
            }
        );

        let test_output: Item = parse2(require_binary_static_env(
            parse_quote! { &'env E, crate },
            parse_quote! { fn do_something<E>(env: &mut E) where E: ::std::fmt::Debug {} },
        ))
        .unwrap();
        assert_eq!(
            test_output,
            parse_quote! {
                fn do_something<E>(env: &mut E) where
                    E: ::std::fmt::Debug,
                    &'env E: 'static + for<'env_0,> crate::Environment<'env_0, [u8], [u8], [u8],>,
                    for<'env_0, 'txn,> <<&'env E as crate::Environment<'env_0, [u8], [u8], [u8],>>::RoTransaction as crate::TransactionBasic>::ReturnedKey: crate::lt_trait_wrappers::AsRefLt2<'env_0, 'txn, [u8],>,
                    for<'env_0, 'txn,> <<&'env E as crate::Environment<'env_0, [u8], [u8], [u8],>>::RoTransaction as crate::TransactionBasic>::ReturnedValue: crate::lt_trait_wrappers::AsRefLt2<'env_0, 'txn, [u8],>,
                    for<'env_0, 'txn,> <<&'env E as crate::Environment<'env_0, [u8], [u8], [u8],>>::RwTransaction as crate::TransactionBasic>::ReturnedKey: crate::lt_trait_wrappers::AsRefLt2<'env_0, 'txn, [u8],>,
                    for<'env_0, 'txn,> <<&'env E as crate::Environment<'env_0, [u8], [u8], [u8],>>::RwTransaction as crate::TransactionBasic>::ReturnedValue: crate::lt_trait_wrappers::AsRefLt2<'env_0, 'txn, [u8],>
                {}
            }
        );

        let test_output: Item = parse2(require_binary_static_env(
            parse_quote! { E },
            parse_quote! { fn do_something<E>(env: &mut E) where E: ::std::fmt::Debug {} },
        ))
        .unwrap();
        assert_eq!(
            test_output,
            parse_quote! {
                fn do_something<E>(env: &mut E) where
                    E: ::std::fmt::Debug,
                    E: 'static + for<'env,> ::atelier_kv_store::Environment<'env, [u8], [u8], [u8],>,
                    for<'env, 'txn,> <<E as ::atelier_kv_store::Environment<'env, [u8], [u8], [u8],>>::RoTransaction as ::atelier_kv_store::TransactionBasic>::ReturnedKey: ::atelier_kv_store::lt_trait_wrappers::AsRefLt2<'env, 'txn, [u8],>,
                    for<'env, 'txn,> <<E as ::atelier_kv_store::Environment<'env, [u8], [u8], [u8],>>::RoTransaction as ::atelier_kv_store::TransactionBasic>::ReturnedValue: ::atelier_kv_store::lt_trait_wrappers::AsRefLt2<'env, 'txn, [u8],>,
                    for<'env, 'txn,> <<E as ::atelier_kv_store::Environment<'env, [u8], [u8], [u8],>>::RwTransaction as ::atelier_kv_store::TransactionBasic>::ReturnedKey: ::atelier_kv_store::lt_trait_wrappers::AsRefLt2<'env, 'txn, [u8],>,
                    for<'env, 'txn,> <<E as ::atelier_kv_store::Environment<'env, [u8], [u8], [u8],>>::RwTransaction as ::atelier_kv_store::TransactionBasic>::ReturnedValue: ::atelier_kv_store::lt_trait_wrappers::AsRefLt2<'env, 'txn, [u8],>
                {}
            }
        );

        let test_output: Result<Item, _> = parse2(require_binary_static_env(
            parse_quote! { E, self, X },
            parse_quote! { fn do_something<E>(env: &mut E) where E: ::std::fmt::Debug {} },
        ));
        // The output is expected to produce a compiler error, but it should
        // still parse.
        test_output.unwrap();

        let test_output: Result<Item, _> = parse2(require_binary_static_env(
            parse_quote! { E },
            parse_quote! { const X: u32 = 0; },
        ));
        // The output is expected to produce a compiler error, but it should
        // still parse.
        test_output.unwrap();
    }
}
