//! This module contains the implementation for the
//! [`require_binary_static_env_ext`][require_binary_static_env_ext] macro.
//!
//! [require_binary_static_env_ext]: crate::require_binary_static_env_ext

use crate::binary_static_env::{env_ext_trait_bound, env_trait_bound, txn_basic_trait_bound};
use crate::{
    add_where_predicates, find_generics_mut, parse_macro_args, remove_ident_name_conflicts,
    LifetimeNameFinder, MacroArg, MacroArgs,
};
use proc_macro2::{Span, TokenStream};
use quote::ToTokens;
use syn::parse::{Parse, ParseStream};
use syn::visit::{visit_path, visit_type};
use syn::{parse2, parse_quote, BoundLifetimes, Lifetime, Type, TypeParamBound};

/// Represents the (parsed) arguments expected by the
/// [`require_binary_static_env_ext`][require_binary_static_env_ext] macro attribute.
///
/// [require_binary_static_env_ext]: crate::require_binary_static_env_ext
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct Args {
    /// Main storage environment type.
    env_type: Type,

    /// Configuration type used to initialize a storage environment.
    env_cfg_type: Type,

    /// Configuration type used to initialize a database.
    db_cfg_type: Type,

    /// Configuration type used to configure a sync/flush operation.
    sync_cfg_type: Type,

    /// Path to use when referencing the `atelier_kv_store` crate in the macro
    /// output.
    crate_root_path: syn::Path,
}

impl MacroArgs for Args {
    const NUM_MANDATORY_ARGS: usize = 4;
    const NUM_OPTIONAL_ARGS: usize = 1;

    fn optional_arg_default(idx: usize) -> MacroArg {
        match idx {
            0 => parse_quote! { ::atelier_kv_store },
            _ => panic!("Unexpected argument index."),
        }
    }

    fn new<M, O>(mandatory_args: M, optional_args: O) -> Result<Self, syn::Error>
    where
        M: IntoIterator<Item = MacroArg>,
        O: IntoIterator<Item = MacroArg>,
    {
        let mandatory_args_vec: Vec<_> = mandatory_args.into_iter().collect();
        let optional_args_vec: Vec<_> = optional_args.into_iter().collect();
        Ok(Args {
            env_type: parse2(mandatory_args_vec[0].to_token_stream())?,
            env_cfg_type: parse2(mandatory_args_vec[1].to_token_stream())?,
            db_cfg_type: parse2(mandatory_args_vec[2].to_token_stream())?,
            sync_cfg_type: parse2(mandatory_args_vec[3].to_token_stream())?,
            crate_root_path: parse2(optional_args_vec[0].to_token_stream())?,
        })
    }
}

impl Parse for Args {
    fn parse(input: ParseStream) -> Result<Self, syn::Error> {
        parse_macro_args(input)
    }
}

/// Represents the lifetime names to be used in the output of a specific
/// invocation of the [`require_binary_static_env_ext`][require_binary_static_env_ext]
/// macro attribute.
///
/// [require_binary_static_env_ext]: crate::require_binary_static_env_ext
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct BoundsLifetimeNames {
    /// Lifetime name for environment references.
    env_lt: Lifetime,

    /// Lifetime name for transaction references.
    txn_lt: Lifetime,

    /// Lifetime name for database ID string references.
    dbid_lt: Lifetime,
}

/// Chooses names for the lifetimes to be used in the output of a specific
/// invocation of the [`require_binary_static_env_ext`][require_binary_static_env_ext]
/// macro attribute.
///
/// For clarity of error messages, this function tries to choose descriptive
/// names for the lifetimes. It must ensure that it does not choose names that
/// conflict with any lifetimes used in the arguments to the macro.
///
/// [require_binary_static_env_ext]: crate::require_binary_static_env_ext
fn name_lifetimes(args: &Args) -> BoundsLifetimeNames {
    fn name_to_lifetime(name: &str) -> Lifetime {
        Lifetime::new(&format!("'{}", name), Span::call_site())
    }

    // Choose names for the lifetimes, avoiding any conflicts with lifetime
    // names used in the macro arguments.
    let mut forbidden_finder = LifetimeNameFinder::default();
    visit_type(&mut forbidden_finder, &args.env_type);
    visit_type(&mut forbidden_finder, &args.env_cfg_type);
    visit_type(&mut forbidden_finder, &args.db_cfg_type);
    visit_type(&mut forbidden_finder, &args.sync_cfg_type);
    visit_path(&mut forbidden_finder, &args.crate_root_path);
    let mut chosen_names = vec!["env".to_string(), "txn".to_string(), "dbid".to_string()];
    remove_ident_name_conflicts(&mut chosen_names, &forbidden_finder.names_found());

    BoundsLifetimeNames {
        env_lt: name_to_lifetime(&chosen_names[0]),
        txn_lt: name_to_lifetime(&chosen_names[1]),
        dbid_lt: name_to_lifetime(&chosen_names[2]),
    }
}

/// Implementation for the
/// [`require_binary_static_env_ext`][require_binary_static_env_ext] macro. The main
/// difference between this function and the macro is that this function uses
/// the `proc_macro2` crate in its signature, so that it can be unit tested.
///
/// [require_binary_static_env_ext]: crate::require_binary_static_env_ext
pub(crate) fn require_binary_static_env_ext(attr: TokenStream, item: TokenStream) -> TokenStream {
    // Internal helper function used to enable ? for error handling.
    fn inner(attr: TokenStream, item: TokenStream) -> Result<TokenStream, syn::Error> {
        let args = parse2(attr)?;

        // Construct the required lifetime names in a way that won't conflict with
        // any lifetimes that might be mentioned in the arguments.
        let lt_names = name_lifetimes(&args);

        // Bring parameters into scope so we can use them in parse_quote.
        let (env_lt, txn_lt, dbid_lt, env_type, crate_root_path) = (
            &lt_names.env_lt,
            &lt_names.txn_lt,
            &lt_names.dbid_lt,
            &args.env_type,
            &args.crate_root_path,
        );

        let lt_quant_env_ext: BoundLifetimes = parse_quote! { for<#env_lt, #dbid_lt,> };
        let lt_quant_txn: BoundLifetimes = parse_quote! { for<#env_lt, #txn_lt,> };
        let env_trait = env_trait_bound(&lt_names.env_lt, &args.crate_root_path);
        let env_ext_trait = env_ext_trait_bound(
            &lt_names.env_lt,
            &lt_names.dbid_lt,
            &args.env_cfg_type,
            &args.db_cfg_type,
            &args.sync_cfg_type,
            &args.crate_root_path,
        );
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
                    #env_type: 'static + #lt_quant_env_ext #env_ext_trait
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

    /// Tests functionality of the `Args` type.
    #[test]
    fn args_test() {
        let args: Args = parse_quote! { A, B, C, D };
        assert_eq!(
            args,
            Args {
                env_type: parse_quote! { A },
                env_cfg_type: parse_quote! { B },
                db_cfg_type: parse_quote! { C },
                sync_cfg_type: parse_quote! { D },
                crate_root_path: parse_quote! { ::atelier_kv_store },
            }
        );

        let args: Args = parse_quote! { A, B, C, D, };
        assert_eq!(
            args,
            Args {
                env_type: parse_quote! { A },
                env_cfg_type: parse_quote! { B },
                db_cfg_type: parse_quote! { C },
                sync_cfg_type: parse_quote! { D },
                crate_root_path: parse_quote! { ::atelier_kv_store },
            }
        );

        let args: Args = parse_quote! { A, A, B<C>, D<'a, <A as E>::F> };
        assert_eq!(
            args,
            Args {
                env_type: parse_quote! { A },
                env_cfg_type: parse_quote! { A },
                db_cfg_type: parse_quote! { B<C> },
                sync_cfg_type: parse_quote! { D<'a, <A as E>::F> },
                crate_root_path: parse_quote! { ::atelier_kv_store },
            }
        );

        let args: Args = parse_quote! { A, A, B<C>, D<'a, <A as E>::F>, akvs::x };
        assert_eq!(
            args,
            Args {
                env_type: parse_quote! { A },
                env_cfg_type: parse_quote! { A },
                db_cfg_type: parse_quote! { B<C> },
                sync_cfg_type: parse_quote! { D<'a, <A as E>::F> },
                crate_root_path: parse_quote! { akvs::x },
            }
        );

        let args: Result<Args, _> = parse2(parse_quote! {});
        args.unwrap_err();

        let args: Result<Args, _> = parse2(parse_quote! { if , 'a () });
        args.unwrap_err();

        let args: Result<Args, _> = parse2(parse_quote! { 'a, if, ||, 5 });
        args.unwrap_err();

        let args: Result<Args, _> = parse2(parse_quote! { A, B, C });
        args.unwrap_err();

        let args: Result<Args, _> = parse2(parse_quote! { A, B, C, D, akvs, E });
        args.unwrap_err();
    }

    /// Tests the `name_lifetimes` function.
    #[test]
    fn name_lifetimes_test() {
        let lt_names = name_lifetimes(&parse_quote! { A, B, C, D });
        assert_eq!(
            lt_names,
            BoundsLifetimeNames {
                env_lt: parse_quote! { 'env },
                txn_lt: parse_quote! { 'txn },
                dbid_lt: parse_quote! { 'dbid },
            }
        );

        let lt_names = name_lifetimes(&parse_quote! { A<'a>, <B as T<'b>>::C, D<'a>, E });
        assert_eq!(
            lt_names,
            BoundsLifetimeNames {
                env_lt: parse_quote! { 'env },
                txn_lt: parse_quote! { 'txn },
                dbid_lt: parse_quote! { 'dbid },
            }
        );

        let lt_names = name_lifetimes(&parse_quote! { A<'env>, <B as T<'dbid>>::C, D<'a>, E });
        assert_eq!(
            lt_names,
            BoundsLifetimeNames {
                env_lt: parse_quote! { 'env_0 },
                txn_lt: parse_quote! { 'txn },
                dbid_lt: parse_quote! { 'dbid_0 },
            }
        );

        let lt_names = name_lifetimes(
            &parse_quote! { A<'env, 'env_0, 'env_1>, <B as T<'dbid>>::C, D<'a>, E, ::akvs },
        );
        assert_eq!(
            lt_names,
            BoundsLifetimeNames {
                env_lt: parse_quote! { 'env_2 },
                txn_lt: parse_quote! { 'txn },
                dbid_lt: parse_quote! { 'dbid_0 },
            }
        );
    }

    /// Tests the `require_binary_static_env_ext` function.
    #[test]
    fn require_binary_static_env_ext_test() {
        let test_output: Item = parse2(require_binary_static_env_ext(
            parse_quote! { E, EC, DC, SC, crate },
            parse_quote! { fn do_something<E, EC, DC, SC>(env: &mut E) {} },
        ))
        .unwrap();
        assert_eq!(
            test_output,
            parse_quote! {
                fn do_something<E, EC, DC, SC>(env: &mut E) where
                    E: 'static + for<'env, 'dbid,> crate::EnvironmentExt<'env, EC, ::std::option::Option<&'dbid str>, DC, SC, [u8], [u8], [u8],>,
                    for<'env, 'txn,> <<E as crate::Environment<'env, [u8], [u8], [u8],>>::RoTransaction as crate::TransactionBasic>::ReturnedKey: crate::lt_trait_wrappers::AsRefLt2<'env, 'txn, [u8],>,
                    for<'env, 'txn,> <<E as crate::Environment<'env, [u8], [u8], [u8],>>::RoTransaction as crate::TransactionBasic>::ReturnedValue: crate::lt_trait_wrappers::AsRefLt2<'env, 'txn, [u8],>,
                    for<'env, 'txn,> <<E as crate::Environment<'env, [u8], [u8], [u8],>>::RwTransaction as crate::TransactionBasic>::ReturnedKey: crate::lt_trait_wrappers::AsRefLt2<'env, 'txn, [u8],>,
                    for<'env, 'txn,> <<E as crate::Environment<'env, [u8], [u8], [u8],>>::RwTransaction as crate::TransactionBasic>::ReturnedValue: crate::lt_trait_wrappers::AsRefLt2<'env, 'txn, [u8],>
                {}
            }
        );

        let test_output: Item = parse2(require_binary_static_env_ext(
            parse_quote! { &'env E, EC, DC, SC, crate },
            parse_quote! { fn do_something<E, EC, DC, SC>(env: &mut E) where E: ::std::fmt::Debug {} },
        )).unwrap();
        assert_eq!(
            test_output,
            parse_quote! {
                fn do_something<E, EC, DC, SC>(env: &mut E) where
                    E: ::std::fmt::Debug,
                    &'env E: 'static + for<'env_0, 'dbid,> crate::EnvironmentExt<'env_0, EC, ::std::option::Option<&'dbid str>, DC, SC, [u8], [u8], [u8],>,
                    for<'env_0, 'txn,> <<&'env E as crate::Environment<'env_0, [u8], [u8], [u8],>>::RoTransaction as crate::TransactionBasic>::ReturnedKey: crate::lt_trait_wrappers::AsRefLt2<'env_0, 'txn, [u8],>,
                    for<'env_0, 'txn,> <<&'env E as crate::Environment<'env_0, [u8], [u8], [u8],>>::RoTransaction as crate::TransactionBasic>::ReturnedValue: crate::lt_trait_wrappers::AsRefLt2<'env_0, 'txn, [u8],>,
                    for<'env_0, 'txn,> <<&'env E as crate::Environment<'env_0, [u8], [u8], [u8],>>::RwTransaction as crate::TransactionBasic>::ReturnedKey: crate::lt_trait_wrappers::AsRefLt2<'env_0, 'txn, [u8],>,
                    for<'env_0, 'txn,> <<&'env E as crate::Environment<'env_0, [u8], [u8], [u8],>>::RwTransaction as crate::TransactionBasic>::ReturnedValue: crate::lt_trait_wrappers::AsRefLt2<'env_0, 'txn, [u8],>
                {}
            }
        );

        let test_output: Item = parse2(require_binary_static_env_ext(
            parse_quote! { E, EC, DC, SC },
            parse_quote! { fn do_something<E, EC, DC, SC>(env: &mut E) where E: ::std::fmt::Debug {} },
        )).unwrap();
        assert_eq!(
            test_output,
            parse_quote! {
                fn do_something<E, EC, DC, SC>(env: &mut E) where
                    E: ::std::fmt::Debug,
                    E: 'static + for<'env, 'dbid,> ::atelier_kv_store::EnvironmentExt<'env, EC, ::std::option::Option<&'dbid str>, DC, SC, [u8], [u8], [u8],>,
                    for<'env, 'txn,> <<E as ::atelier_kv_store::Environment<'env, [u8], [u8], [u8],>>::RoTransaction as ::atelier_kv_store::TransactionBasic>::ReturnedKey: ::atelier_kv_store::lt_trait_wrappers::AsRefLt2<'env, 'txn, [u8],>,
                    for<'env, 'txn,> <<E as ::atelier_kv_store::Environment<'env, [u8], [u8], [u8],>>::RoTransaction as ::atelier_kv_store::TransactionBasic>::ReturnedValue: ::atelier_kv_store::lt_trait_wrappers::AsRefLt2<'env, 'txn, [u8],>,
                    for<'env, 'txn,> <<E as ::atelier_kv_store::Environment<'env, [u8], [u8], [u8],>>::RwTransaction as ::atelier_kv_store::TransactionBasic>::ReturnedKey: ::atelier_kv_store::lt_trait_wrappers::AsRefLt2<'env, 'txn, [u8],>,
                    for<'env, 'txn,> <<E as ::atelier_kv_store::Environment<'env, [u8], [u8], [u8],>>::RwTransaction as ::atelier_kv_store::TransactionBasic>::ReturnedValue: ::atelier_kv_store::lt_trait_wrappers::AsRefLt2<'env, 'txn, [u8],>
                {}
            }
        );

        let test_output: Result<Item, _> = parse2(require_binary_static_env_ext(
            parse_quote! { E, EC, DC },
            parse_quote! { fn do_something<E, EC, DC, DC>(env: &mut E) where E: ::std::fmt::Debug {} },
        ));
        // The output is expected to produce a compiler error, but it should
        // still parse.
        test_output.unwrap();

        let test_output: Result<Item, _> = parse2(require_binary_static_env_ext(
            parse_quote! { E, EC, DC, SC, self, X },
            parse_quote! { fn do_something<E, EC, DC, SC>(env: &mut E) where E: ::std::fmt::Debug {} },
        ));
        // The output is expected to produce a compiler error, but it should
        // still parse.
        test_output.unwrap();

        let test_output: Result<Item, _> = parse2(require_binary_static_env_ext(
            parse_quote! { E, EC, DC, SC },
            parse_quote! { const X: u32 = 0; },
        ));
        // The output is expected to produce a compiler error, but it should
        // still parse.
        test_output.unwrap();
    }
}
