//! This module contains support for macros related to working with `'static`
//! storage environments where the keys and values are byte strings, i.e.
//! LMDB-like storage environments.

use crate::remove_ident_name_conflicts;
use proc_macro2::{Span, TokenStream};
use quote::ToTokens;
use std::collections::HashSet;
use syn::parse::Parser;
use syn::punctuated::Punctuated;
use syn::visit::{visit_type, Visit};
use syn::{
    parse2, parse_quote, BoundLifetimes, Generics, Item, Lifetime, Token, Type, TypeParamBound,
    WhereClause, WherePredicate,
};

/// Represents the (parsed) arguments expected by the
/// [`require_binary_static_env`][require_binary_static_env] macro attribute.
///
/// [require_binary_static_env]: crate::require_binary_static_env
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct BoundsArgs {
    /// Main storage environment type.
    env_type: Type,

    /// Configuration type used to initialize a storage environment.
    env_cfg_type: Type,

    /// Configuration type used to initialize a database.
    db_cfg_type: Type,

    /// Configuration type used to configure a sync/flush operation.
    sync_cfg_type: Type,
}

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

    /// Lifetime name for database ID string references.
    dbid_lt: Lifetime,

    /// Lifetime name for key references used in queries.
    kq_lt: Lifetime,

    /// Lifetime name for key references used in insertions.
    kp_lt: Lifetime,

    /// Lifetime name for value references used in insertions.
    vp_lt: Lifetime,
}

/// Number of comma-separated arguments expected by the
/// [`require_binary_static_env`][require_binary_static_env] macro attribute.
///
/// [require_binary_static_env]: crate::require_binary_static_env
const NUM_ARGS: usize = 4;

/// Parses the arguments passed to the
/// [`require_binary_static_env`][require_binary_static_env] macro attribute.
///
/// # Panics
/// Panics if the arguments do not have the expected syntax.
///
/// [require_binary_static_env]: crate::require_binary_static_env
fn parse_args(tokens: TokenStream) -> BoundsArgs {
    let generic_args: Punctuated<Type, Token![,]> =
        Punctuated::parse_terminated.parse2(tokens).unwrap();
    if generic_args.len() != NUM_ARGS {
        panic!(
            "Expected {} parameters, got {}.",
            NUM_ARGS,
            generic_args.len()
        );
    }
    BoundsArgs {
        env_type: generic_args[0].clone(),
        env_cfg_type: generic_args[1].clone(),
        db_cfg_type: generic_args[2].clone(),
        sync_cfg_type: generic_args[3].clone(),
    }
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
fn name_lifetimes(args: &BoundsArgs) -> BoundsLifetimeNames {
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
    let mut chosen_names = vec![
        "env".to_string(),
        "txn".to_string(),
        "dbid".to_string(),
        "kq".to_string(),
        "kp".to_string(),
        "vp".to_string(),
    ];
    remove_ident_name_conflicts(&mut chosen_names, &forbidden_finder.names_found);

    BoundsLifetimeNames {
        env_lt: name_to_lifetime(&chosen_names[0]),
        txn_lt: name_to_lifetime(&chosen_names[1]),
        dbid_lt: name_to_lifetime(&chosen_names[2]),
        kq_lt: name_to_lifetime(&chosen_names[3]),
        kp_lt: name_to_lifetime(&chosen_names[4]),
        vp_lt: name_to_lifetime(&chosen_names[5]),
    }
}

/// Type that is used to extract all lifetime names mentioned in a syntax tree.
#[derive(Debug, Default)]
struct LifetimeNameFinder {
    /// Set of lifetime names encountered so far.
    names_found: HashSet<String>,
}

impl<'ast> Visit<'ast> for LifetimeNameFinder {
    fn visit_lifetime(&mut self, i: &'ast Lifetime) {
        self.names_found.insert(i.ident.to_string());
    }
}

/// Gets the trait bound that should be used for the main storage environment
/// type.
fn env_trait_bound(
    args: &BoundsArgs,
    lt_names: &BoundsLifetimeNames,
    crate_root_path: &syn::Path,
) -> TypeParamBound {
    // Bring parameters into scope so we can use them in parse_quote.
    let (env_lt, dbid_lt, kq_lt, kp_lt, vp_lt, env_cfg_type, db_cfg_type, sync_cfg_type) = (
        &lt_names.env_lt,
        &lt_names.dbid_lt,
        &lt_names.kq_lt,
        &lt_names.kp_lt,
        &lt_names.vp_lt,
        &args.env_cfg_type,
        &args.db_cfg_type,
        &args.sync_cfg_type,
    );
    parse_quote! {
        #crate_root_path::Environment<
            #env_lt,
            #env_cfg_type,
            ::std::option::Option<& #dbid_lt str>,
            #db_cfg_type,
            #sync_cfg_type,
            & #kq_lt [u8],
            & #kp_lt [u8],
            & #vp_lt [u8],
        >
    }
}

/// Gets the trait bound that should be used for transaction types.
fn txn_trait_bound(lt_names: &BoundsLifetimeNames, crate_root_path: &syn::Path) -> TypeParamBound {
    // Bring parameters into scope so we can use them in parse_quote.
    let (txn_lt, kq_lt) = (&lt_names.txn_lt, &lt_names.kq_lt);
    parse_quote! {
        #crate_root_path::Transaction<
            #txn_lt,
            & #kq_lt [u8],
        >
    }
}

/// Gets the trait bound that should be used for read-write transaction types.
fn rw_txn_trait_bound(
    lt_names: &BoundsLifetimeNames,
    crate_root_path: &syn::Path,
) -> TypeParamBound {
    // Bring parameters into scope so we can use them in parse_quote.
    let (txn_lt, kq_lt, kp_lt, vp_lt) = (
        &lt_names.txn_lt,
        &lt_names.kq_lt,
        &lt_names.kp_lt,
        &lt_names.vp_lt,
    );
    parse_quote! {
        #crate_root_path::ReadWriteTransaction<#txn_lt, & #kq_lt [u8], & #kp_lt [u8], & #vp_lt [u8]>
    }
}

/// Gets the trait bound that should be used for cursor types.
fn cursor_basic_trait_bound(crate_root_path: &syn::Path) -> TypeParamBound {
    parse_quote! {
        #crate_root_path::CursorBasic
    }
}

/// Gets the trait bound that should be used to require [`AsRef`][AsRef]`<[u8]>`
/// for a type.
///
/// [AsRef]: std::convert::AsRef
fn as_ref_trait_bound(
    lt_names: &BoundsLifetimeNames,
    crate_root_path: &syn::Path,
) -> TypeParamBound {
    // Bring parameters into scope so we can use them in parse_quote.
    let (env_lt, txn_lt, dbid_lt, kq_lt, kp_lt, vp_lt) = (
        &lt_names.env_lt,
        &lt_names.txn_lt,
        &lt_names.dbid_lt,
        &lt_names.kq_lt,
        &lt_names.kp_lt,
        &lt_names.vp_lt,
    );
    parse_quote! {
        #crate_root_path::lt_trait_wrappers::AsRefLt6<#env_lt, #txn_lt, #dbid_lt, #kq_lt, #kp_lt, #vp_lt, [u8]>
    }
}

/// Generates the lifetime quantifiers that should be used in higher-rank trait
/// bounds in the output of the
/// [`require_binary_static_env`][require_binary_static_env] macro.
///
/// [require_binary_static_env]: crate::require_binary_static_env
fn lifetime_quantifier(lt_names: &BoundsLifetimeNames, include_txn_lt: bool) -> BoundLifetimes {
    // Bring parameters into scope so we can use them in parse_quote.
    let (env_lt, txn_lt, dbid_lt, kq_lt, kp_lt, vp_lt) = (
        &lt_names.env_lt,
        &lt_names.txn_lt,
        &lt_names.dbid_lt,
        &lt_names.kq_lt,
        &lt_names.kp_lt,
        &lt_names.vp_lt,
    );
    let mut output = BoundLifetimes::default();
    output.lifetimes.push(parse_quote! { #env_lt });
    if include_txn_lt {
        output.lifetimes.push(parse_quote! { #txn_lt });
    }
    output.lifetimes.push(parse_quote! { #dbid_lt });
    output.lifetimes.push(parse_quote! { #kq_lt });
    output.lifetimes.push(parse_quote! { #kp_lt });
    output.lifetimes.push(parse_quote! { #vp_lt });
    output
}

/// Modifies the specified generics data so that its `where` clause contains the
/// bounds required to use a binary static storage environment, i.e. the bounds
/// needed when using [`require_binary_static_env`][require_binary_static_env].
///
/// [require_binary_static_env]: crate::require_binary_static_env
fn add_bounds(
    generics: &mut Generics,
    args: &BoundsArgs,
    lt_names: &BoundsLifetimeNames,
    crate_root_path: &syn::Path,
) {
    // Bring parameters into scope so we can use them in parse_quote.
    let env_type = &args.env_type;
    let lt_quant_env = lifetime_quantifier(lt_names, false);
    let lt_quant_txn = lifetime_quantifier(lt_names, true);
    let env_trait = env_trait_bound(args, lt_names, crate_root_path);
    let txn_trait = txn_trait_bound(lt_names, crate_root_path);
    let rw_txn_trait = rw_txn_trait_bound(lt_names, crate_root_path);
    let cursor_basic_trait = cursor_basic_trait_bound(crate_root_path);
    let as_ref_trait = as_ref_trait_bound(lt_names, crate_root_path);
    let new_predicates: Vec<WherePredicate> = vec![
        parse_quote! {
            #env_type: 'static + #lt_quant_env #env_trait
        },
        parse_quote! {
            #lt_quant_txn <<#env_type as #env_trait>::RoTransaction as #txn_trait>::ReturnedValue: #as_ref_trait
        },
        parse_quote! {
            #lt_quant_txn <<#env_type as #env_trait>::RwTransaction as #txn_trait>::ReturnedValue: #as_ref_trait
        },
        parse_quote! {
            #lt_quant_txn <<<#env_type as #env_trait>::RoTransaction as #txn_trait>::RoCursor as #cursor_basic_trait>::ReturnedKey: #as_ref_trait
        },
        parse_quote! {
            #lt_quant_txn <<<#env_type as #env_trait>::RoTransaction as #txn_trait>::RoCursor as #cursor_basic_trait>::ReturnedValue: #as_ref_trait
        },
        parse_quote! {
            #lt_quant_txn <<<#env_type as #env_trait>::RwTransaction as #txn_trait>::RoCursor as #cursor_basic_trait>::ReturnedKey: #as_ref_trait
        },
        parse_quote! {
            #lt_quant_txn <<<#env_type as #env_trait>::RwTransaction as #txn_trait>::RoCursor as #cursor_basic_trait>::ReturnedValue: #as_ref_trait
        },
        parse_quote! {
            #lt_quant_txn <<<#env_type as #env_trait>::RwTransaction as #rw_txn_trait>::RwCursor as #cursor_basic_trait>::ReturnedKey: #as_ref_trait
        },
        parse_quote! {
            #lt_quant_txn <<<#env_type as #env_trait>::RwTransaction as #rw_txn_trait>::RwCursor as #cursor_basic_trait>::ReturnedValue: #as_ref_trait
        },
    ];

    if let Some(where_clause) = &mut generics.where_clause {
        where_clause.predicates.extend(new_predicates);
    } else {
        generics.where_clause = Some(WhereClause {
            where_token: <Token![where]>::default(),
            predicates: new_predicates.into_iter().collect(),
        });
    }
}

/// Gets a reference to the generics data in a parsed item.
///
/// # Panics
/// Panics if the item is not of a type that can have generics data.
fn find_generics(item: &mut Item) -> &mut Generics {
    match item {
        Item::Enum(item) => &mut item.generics,
        Item::Fn(item) => &mut item.sig.generics,
        Item::Impl(item) => &mut item.generics,
        Item::Struct(item) => &mut item.generics,
        Item::Trait(item) => &mut item.generics,
        Item::TraitAlias(item) => &mut item.generics,
        Item::Type(item) => &mut item.generics,
        Item::Union(item) => &mut item.generics,
        _ => panic!("Unexpected item type; could not modify generics."),
    }
}

/// Creates an identifier path pointing to the root of the `atelier-kv-store`
/// crate. The path to use depends on whether the macro is being invoked from
/// inside the `atelier-kv-store` crate or from a different crate.
fn make_crate_root_path(inside_crate: bool) -> syn::Path {
    if inside_crate {
        parse_quote! { crate }
    } else {
        parse_quote! { ::atelier_kv_store }
    }
}

/// Main function used to implement both
/// [`require_binary_static_env`][require_binary_static_env] and
/// [`require_binary_static_env_inside_crate`][require_binary_static_env_inside_crate].
/// It has an extra boolean argument indicating which of those two functions is
/// being called.
///
/// # Panics
/// Panics if the input token streams do not have the expected syntax.
///
/// [require_binary_static_env]: self::require_binary_static_env
/// [require_binary_static_env_inside_crate]: self::require_binary_static_env_inside_crate
fn require_binary_static_env_general(
    attr: TokenStream,
    item: TokenStream,
    inside_crate: bool,
) -> TokenStream {
    // Parse the attribute's arguments.
    let args = parse_args(attr);

    // Construct the required lifetime names in a way that won't conflict with
    // any lifetimes that might be used in the type parameters.
    let lt_names = name_lifetimes(&args);

    // Parse the item and augment its where clause with the required bounds.
    let mut output: Item = parse2(item).unwrap();
    add_bounds(
        find_generics(&mut output),
        &args,
        &lt_names,
        &make_crate_root_path(inside_crate),
    );
    output.into_token_stream()
}

/// Implementation for the
/// [`require_binary_static_env`][require_binary_static_env] macro. The main
/// difference between this function and the macro is that this function uses
/// the `proc_macro2` crate in its signature, so that it can be unit tested.
///
/// # Panics
/// Panics if the input token streams do not have the expected syntax.
///
/// [require_binary_static_env]: crate::require_binary_static_env
pub(crate) fn require_binary_static_env(attr: TokenStream, item: TokenStream) -> TokenStream {
    require_binary_static_env_general(attr, item, false)
}

/// Implementation for the
/// [`require_binary_static_env_inside_crate`][require_binary_static_env_inside_crate]
/// macro. The main difference between this function and the macro is that this
/// function uses the `proc_macro2` crate in its signature, so that it can be
/// unit tested.
///
/// # Panics
/// Panics if the input token streams do not have the expected syntax.
///
/// [require_binary_static_env_inside_crate]: crate::require_binary_static_env_inside_crate
pub(crate) fn require_binary_static_env_inside_crate(
    attr: TokenStream,
    item: TokenStream,
) -> TokenStream {
    require_binary_static_env_general(attr, item, true)
}
