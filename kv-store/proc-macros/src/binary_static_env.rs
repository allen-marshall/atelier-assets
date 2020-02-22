//! This module contains support for macros related to working with `'static`
//! storage environments where the keys and values are byte strings, i.e.
//! LMDB-like storage environments.

use crate::remove_ident_name_conflicts;
use proc_macro2::{Span, TokenStream};
use quote::ToTokens;
use std::collections::HashSet;
use std::convert::TryInto;
use syn::parse::{Parse, ParseStream};
use syn::punctuated::Punctuated;
use syn::visit::{visit_path, visit_type, Visit};
use syn::{
    parse2, parse_quote, BoundLifetimes, Generics, Item, Lifetime, Token, Type, TypeParamBound,
    WhereClause, WherePredicate,
};

/// Represents a single (parsed) argument expected by the
/// [`require_binary_static_env`][require_binary_static_env] macro attribute.
///
/// [require_binary_static_env]: crate::require_binary_static_env
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum Arg {
    /// Variant for arguments that are syntactically valid types.
    Type(Type),

    /// Variant for arguments that are not syntactically valid types but are
    /// syntactically valid paths.
    Path(syn::Path),
}

impl Parse for Arg {
    fn parse(input: ParseStream) -> Result<Self, syn::Error> {
        // Try to parse the argument as a type.
        let type_parse_result = Type::parse(input);
        if let Ok(parsed_type) = type_parse_result {
            Ok(Arg::Type(parsed_type))
        } else {
            // Try to parse the argument as a path.
            let path_parse_result = syn::Path::parse(input);
            if let Ok(parsed_path) = path_parse_result {
                Ok(Arg::Path(parsed_path))
            } else {
                Err(input
                    .error("Failed to parse argument. Arguments must be either types or paths."))
            }
        }
    }
}

impl ToTokens for Arg {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        match self {
            Arg::Type(parsed_type) => {
                parsed_type.to_tokens(tokens);
            }
            Arg::Path(parsed_path) => {
                parsed_path.to_tokens(tokens);
            }
        }
    }
}

impl TryInto<Type> for Arg {
    type Error = syn::Error;

    fn try_into(self) -> Result<Type, Self::Error> {
        // Note: This function doesn't necessarily fail if the variant isn't
        // Arg::Type; it just fails if the tokens don't form a syntactically
        // valid type.
        parse2(self.into_token_stream())
    }
}

impl TryInto<syn::Path> for Arg {
    type Error = syn::Error;

    fn try_into(self) -> Result<syn::Path, Self::Error> {
        // Note: This function doesn't necessarily fail if the variant isn't
        // Arg::Path; it just fails if the tokens don't form a syntactically
        // valid path.
        parse2(self.into_token_stream())
    }
}

/// Represents the (parsed) arguments expected by the
/// [`require_binary_static_env`][require_binary_static_env] macro attribute.
///
/// [require_binary_static_env]: crate::require_binary_static_env
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

/// Minimum number of comma-separated arguments expected by the
/// [`require_binary_static_env`][require_binary_static_env] macro attribute.
///
/// [require_binary_static_env]: crate::require_binary_static_env
const MIN_NUM_ARGS: usize = 4;

/// Maximum number of comma-separated arguments expected by the
/// [`require_binary_static_env`][require_binary_static_env] macro attribute.
///
/// [require_binary_static_env]: crate::require_binary_static_env
const MAX_NUM_ARGS: usize = 5;

impl Parse for Args {
    fn parse(input: ParseStream) -> Result<Self, syn::Error> {
        let parsed_args: Punctuated<Arg, Token![,]> = Punctuated::parse_terminated(input)?;
        if parsed_args.len() < MIN_NUM_ARGS {
            Err(input.error(format!(
                "Expected at least {} arguments, got {}.",
                MIN_NUM_ARGS,
                parsed_args.len()
            )))
        } else if parsed_args.len() > MAX_NUM_ARGS {
            Err(input.error(format!(
                "Expected at most {} arguments, got {}.",
                MAX_NUM_ARGS,
                parsed_args.len()
            )))
        } else {
            fn reparse_mandatory_arg<T>(
                parsed_args: &Punctuated<Arg, Token![,]>,
                idx: usize,
            ) -> Result<T, syn::Error>
            where
                T: Parse,
            {
                parse2(parsed_args[idx].to_token_stream())
            }
            fn reparse_optional_arg<T>(
                parsed_args: &Punctuated<Arg, Token![,]>,
                idx: usize,
                default: T,
            ) -> Result<T, syn::Error>
            where
                T: Parse,
            {
                if parsed_args.len() <= idx {
                    Ok(default)
                } else {
                    parse2(parsed_args[idx].to_token_stream())
                }
            }

            // Parse mandatory arguments.
            let (env_type, env_cfg_type, db_cfg_type, sync_cfg_type) = (
                reparse_mandatory_arg(&parsed_args, 0)?,
                reparse_mandatory_arg(&parsed_args, 1)?,
                reparse_mandatory_arg(&parsed_args, 2)?,
                reparse_mandatory_arg(&parsed_args, 3)?,
            );

            // Parse optional arguments.
            let crate_root_path =
                reparse_optional_arg(&parsed_args, 4, parse_quote! { ::atelier_kv_store })?;

            Ok(Args {
                env_type,
                env_cfg_type,
                db_cfg_type,
                sync_cfg_type,
                crate_root_path,
            })
        }
    }
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

/// Chooses names for the lifetimes to be used in the output of a specific
/// invocation of the [`require_binary_static_env`][require_binary_static_env]
/// macro attribute.
///
/// For clarity of error messages, this function tries to choose descriptive
/// names for the lifetimes. It must ensure that it does not choose names that
/// conflict with any lifetimes used in the arguments to the macro.
///
/// [require_binary_static_env]: crate::require_binary_static_env
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

/// Gets the trait bound that should be used for the main storage environment
/// type.
fn env_trait_bound(args: &Args, lt_names: &BoundsLifetimeNames) -> TypeParamBound {
    // Bring parameters into scope so we can use them in parse_quote.
    let (
        env_lt,
        dbid_lt,
        kq_lt,
        kp_lt,
        vp_lt,
        env_cfg_type,
        db_cfg_type,
        sync_cfg_type,
        crate_root_path,
    ) = (
        &lt_names.env_lt,
        &lt_names.dbid_lt,
        &lt_names.kq_lt,
        &lt_names.kp_lt,
        &lt_names.vp_lt,
        &args.env_cfg_type,
        &args.db_cfg_type,
        &args.sync_cfg_type,
        &args.crate_root_path,
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
fn txn_trait_bound(args: &Args, lt_names: &BoundsLifetimeNames) -> TypeParamBound {
    // Bring parameters into scope so we can use them in parse_quote.
    let (crate_root_path, txn_lt, kq_lt) =
        (&args.crate_root_path, &lt_names.txn_lt, &lt_names.kq_lt);
    parse_quote! {
        #crate_root_path::Transaction<
            #txn_lt,
            & #kq_lt [u8],
        >
    }
}

/// Gets the trait bound that should be used for read-write transaction types.
fn rw_txn_trait_bound(args: &Args, lt_names: &BoundsLifetimeNames) -> TypeParamBound {
    // Bring parameters into scope so we can use them in parse_quote.
    let (crate_root_path, txn_lt, kq_lt, kp_lt, vp_lt) = (
        &args.crate_root_path,
        &lt_names.txn_lt,
        &lt_names.kq_lt,
        &lt_names.kp_lt,
        &lt_names.vp_lt,
    );
    parse_quote! {
        #crate_root_path::ReadWriteTransaction<
            #txn_lt,
            & #kq_lt [u8],
            & #kp_lt [u8],
            & #vp_lt [u8],
        >
    }
}

/// Gets the trait bound that should be used for cursor types.
fn cursor_basic_trait_bound(args: &Args) -> TypeParamBound {
    // Bring parameters into scope so we can use them in parse_quote.
    let crate_root_path = &args.crate_root_path;
    parse_quote! {
        #crate_root_path::CursorBasic
    }
}

/// Gets the trait bound that should be used to require [`AsRef`][AsRef]`<[u8]>`
/// for a type.
///
/// [AsRef]: std::convert::AsRef
fn as_ref_trait_bound(args: &Args, lt_names: &BoundsLifetimeNames) -> TypeParamBound {
    // Bring parameters into scope so we can use them in parse_quote.
    let (crate_root_path, env_lt, txn_lt, dbid_lt, kq_lt, kp_lt, vp_lt) = (
        &args.crate_root_path,
        &lt_names.env_lt,
        &lt_names.txn_lt,
        &lt_names.dbid_lt,
        &lt_names.kq_lt,
        &lt_names.kp_lt,
        &lt_names.vp_lt,
    );
    parse_quote! {
        #crate_root_path::lt_trait_wrappers::AsRefLt6<
            #env_lt,
            #txn_lt,
            #dbid_lt,
            #kq_lt,
            #kp_lt,
            #vp_lt,
            [u8],
        >
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
    output.lifetimes.push_punct(<Token![,]>::default());
    output
}

/// Gets a reference to the generics data in a parsed item. Returns an error if
/// the item is not of a type that can have generics data.
fn find_generics(item: &mut Item) -> Result<&mut Generics, syn::Error> {
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

/// Modifies the specified generics data so that its `where` clause contains the
/// bounds required to use a binary static storage environment, i.e. the bounds
/// needed when using [`require_binary_static_env`][require_binary_static_env].
///
/// [require_binary_static_env]: crate::require_binary_static_env
fn add_bounds(generics: &mut Generics, args: &Args, lt_names: &BoundsLifetimeNames) {
    // Bring parameters into scope so we can use them in parse_quote.
    let env_type = &args.env_type;
    let lt_quant_env = lifetime_quantifier(lt_names, false);
    let lt_quant_txn = lifetime_quantifier(lt_names, true);
    let env_trait = env_trait_bound(args, lt_names);
    let txn_trait = txn_trait_bound(args, lt_names);
    let rw_txn_trait = rw_txn_trait_bound(args, lt_names);
    let cursor_basic_trait = cursor_basic_trait_bound(args);
    let as_ref_trait = as_ref_trait_bound(args, lt_names);
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

/// Helper function used to implement
/// [`require_binary_static_env`][require_binary_static_env].
///
/// [require_binary_static_env]: self::require_binary_static_env
fn require_binary_static_env_internal(
    attr: TokenStream,
    item: TokenStream,
) -> Result<TokenStream, syn::Error> {
    let args = parse2(attr)?;

    // Construct the required lifetime names in a way that won't conflict with
    // any lifetimes that might be mentioned in the arguments.
    let lt_names = name_lifetimes(&args);

    // Parse the item and augment its where clause with the required bounds.
    let mut output = parse2(item)?;
    add_bounds(find_generics(&mut output)?, &args, &lt_names);
    Ok(output.into_token_stream())
}

/// Implementation for the
/// [`require_binary_static_env`][require_binary_static_env] macro. The main
/// difference between this function and the macro is that this function uses
/// the `proc_macro2` crate in its signature, so that it can be unit tested.
///
/// [require_binary_static_env]: crate::require_binary_static_env
pub(crate) fn require_binary_static_env(attr: TokenStream, item: TokenStream) -> TokenStream {
    match require_binary_static_env_internal(attr, item) {
        Ok(tokens) => tokens,
        Err(err) => err.to_compile_error(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::test_util::map_to_string;

    /// Tests functionality of the `Arg` type.
    #[test]
    fn arg_test() {
        let arg: Arg = parse_quote! { T };
        assert_eq!(
            TryInto::<Type>::try_into(arg.clone()).unwrap(),
            parse_quote! { T }
        );
        assert_eq!(
            TryInto::<syn::Path>::try_into(arg.clone()).unwrap(),
            parse_quote! { T }
        );
        assert_eq!(arg, parse2(arg.to_token_stream()).unwrap());

        let arg: Arg = parse_quote! { T<T0, T1<'a>> };
        assert_eq!(
            TryInto::<Type>::try_into(arg.clone()).unwrap(),
            parse_quote! { T<T0, T1<'a>> }
        );
        assert_eq!(
            TryInto::<Type>::try_into(arg.clone()).unwrap(),
            parse_quote! { T<T0, T1<'a>> }
        );
        assert_eq!(arg, parse2(arg.to_token_stream()).unwrap());

        let arg: Arg = parse_quote! { crate::x };
        assert_eq!(
            TryInto::<Type>::try_into(arg.clone()).unwrap(),
            parse_quote! { crate::x }
        );
        assert_eq!(
            TryInto::<syn::Path>::try_into(arg.clone()).unwrap(),
            parse_quote! { crate::x }
        );
        assert_eq!(arg, parse2(arg.to_token_stream()).unwrap());

        let arg: Result<Arg, _> = parse2(parse_quote! { if , 'a B });
        arg.unwrap_err();
    }

    /// Tests functionality of the `Args` type.
    #[test]
    fn parse_args_test() {
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

    /// Tests functionality of the `LifetimeNameFinder` type.
    #[test]
    fn lifetime_name_finder_test() {
        let mut finder = LifetimeNameFinder::default();
        assert_eq!(finder.names_found, HashSet::new());

        visit_type(&mut finder, &parse_quote! { <X<'a> as Y<'b, 'c>>::Z });
        assert_eq!(finder.names_found, map_to_string(vec!["a", "b", "c"]));

        visit_type(&mut finder, &parse_quote! { <X<'a> as Y<'b, 'd>>::Z });
        assert_eq!(finder.names_found, map_to_string(vec!["a", "b", "c", "d"]));

        visit_type(&mut finder, &parse_quote! { X });
        assert_eq!(finder.names_found, map_to_string(vec!["a", "b", "c", "d"]));
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
                kq_lt: parse_quote! { 'kq },
                kp_lt: parse_quote! { 'kp },
                vp_lt: parse_quote! { 'vp }
            }
        );

        let lt_names = name_lifetimes(&parse_quote! { A<'a>, <B as T<'b>>::C, D<'a>, E });
        assert_eq!(
            lt_names,
            BoundsLifetimeNames {
                env_lt: parse_quote! { 'env },
                txn_lt: parse_quote! { 'txn },
                dbid_lt: parse_quote! { 'dbid },
                kq_lt: parse_quote! { 'kq },
                kp_lt: parse_quote! { 'kp },
                vp_lt: parse_quote! { 'vp }
            }
        );

        let lt_names = name_lifetimes(&parse_quote! { A<'env>, <B as T<'dbid>>::C, D<'a>, E });
        assert_eq!(
            lt_names,
            BoundsLifetimeNames {
                env_lt: parse_quote! { 'env_0 },
                txn_lt: parse_quote! { 'txn },
                dbid_lt: parse_quote! { 'dbid_0 },
                kq_lt: parse_quote! { 'kq },
                kp_lt: parse_quote! { 'kp },
                vp_lt: parse_quote! { 'vp }
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
                kq_lt: parse_quote! { 'kq },
                kp_lt: parse_quote! { 'kp },
                vp_lt: parse_quote! { 'vp }
            }
        );
    }

    /// Tests the `env_trait_bound` function.
    #[test]
    fn env_trait_bound_test() {
        let bound = env_trait_bound(
            &parse_quote! { E, EC, DC, SC, crate },
            &BoundsLifetimeNames {
                env_lt: parse_quote! { 'env },
                txn_lt: parse_quote! { 'txn },
                dbid_lt: parse_quote! { 'dbid },
                kq_lt: parse_quote! { 'kq },
                kp_lt: parse_quote! { 'kp },
                vp_lt: parse_quote! { 'vp },
            },
        );
        assert_eq!(
            bound,
            parse_quote! {
                crate::Environment<
                    'env,
                    EC,
                    ::std::option::Option<&'dbid str>,
                    DC,
                    SC,
                    &'kq [u8],
                    &'kp [u8],
                    &'vp [u8],
                >
            }
        );

        let bound = env_trait_bound(
            &parse_quote! { A<'a>, B<'env>, C<'c>, D<'d> },
            &BoundsLifetimeNames {
                env_lt: parse_quote! { 'env_0 },
                txn_lt: parse_quote! { 'txn_1 },
                dbid_lt: parse_quote! { 'dbid_2 },
                kq_lt: parse_quote! { 'kq_0 },
                kp_lt: parse_quote! { 'kp_1 },
                vp_lt: parse_quote! { 'vp_2 },
            },
        );
        assert_eq!(
            bound,
            parse_quote! {
                ::atelier_kv_store::Environment<
                    'env_0,
                    B<'env>,
                    ::std::option::Option<&'dbid_2 str>,
                    C<'c>,
                    D<'d>,
                    &'kq_0 [u8],
                    &'kp_1 [u8],
                    &'vp_2 [u8],
                >
            }
        );
    }

    /// Tests the `txn_trait_bound` function.
    #[test]
    fn txn_trait_bound_test() {
        let bound = txn_trait_bound(
            &parse_quote! { A, B, C, D, crate },
            &BoundsLifetimeNames {
                env_lt: parse_quote! { 'env },
                txn_lt: parse_quote! { 'txn },
                dbid_lt: parse_quote! { 'dbid },
                kq_lt: parse_quote! { 'kq },
                kp_lt: parse_quote! { 'kp },
                vp_lt: parse_quote! { 'vp },
            },
        );
        assert_eq!(
            bound,
            parse_quote! {
                crate::Transaction<
                    'txn,
                    &'kq [u8],
                >
            }
        );

        let bound = txn_trait_bound(
            &parse_quote! { A, B, C, D },
            &BoundsLifetimeNames {
                env_lt: parse_quote! { 'env_0 },
                txn_lt: parse_quote! { 'txn_1 },
                dbid_lt: parse_quote! { 'dbid_2 },
                kq_lt: parse_quote! { 'kq_0 },
                kp_lt: parse_quote! { 'kp_1 },
                vp_lt: parse_quote! { 'vp_2 },
            },
        );
        assert_eq!(
            bound,
            parse_quote! {
                ::atelier_kv_store::Transaction<
                    'txn_1,
                    &'kq_0 [u8],
                >
            }
        );
    }

    /// Tests the `rw_txn_trait_bound` function.
    #[test]
    fn rw_txn_trait_bound_test() {
        let bound = rw_txn_trait_bound(
            &parse_quote! { A, B, C, D, crate },
            &BoundsLifetimeNames {
                env_lt: parse_quote! { 'env },
                txn_lt: parse_quote! { 'txn },
                dbid_lt: parse_quote! { 'dbid },
                kq_lt: parse_quote! { 'kq },
                kp_lt: parse_quote! { 'kp },
                vp_lt: parse_quote! { 'vp },
            },
        );
        assert_eq!(
            bound,
            parse_quote! {
                crate::ReadWriteTransaction<
                    'txn,
                    &'kq [u8],
                    &'kp [u8],
                    &'vp [u8],
                >
            }
        );

        let bound = rw_txn_trait_bound(
            &parse_quote! { A, B, C, D },
            &BoundsLifetimeNames {
                env_lt: parse_quote! { 'env_0 },
                txn_lt: parse_quote! { 'txn_1 },
                dbid_lt: parse_quote! { 'dbid_2 },
                kq_lt: parse_quote! { 'kq_0 },
                kp_lt: parse_quote! { 'kp_1 },
                vp_lt: parse_quote! { 'vp_2 },
            },
        );
        assert_eq!(
            bound,
            parse_quote! {
                ::atelier_kv_store::ReadWriteTransaction<
                    'txn_1,
                    &'kq_0 [u8],
                    &'kp_1 [u8],
                    &'vp_2 [u8],
                >
            }
        );
    }

    /// Tests the `cursor_basic_trait_bound` function.
    #[test]
    fn cursor_basic_trait_bound_test() {
        let bound = cursor_basic_trait_bound(&parse_quote! { A, B, C, D, crate });
        assert_eq!(
            bound,
            parse_quote! {
                crate::CursorBasic
            }
        );

        let bound = cursor_basic_trait_bound(&parse_quote! { A, B, C, D });
        assert_eq!(
            bound,
            parse_quote! {
                ::atelier_kv_store::CursorBasic
            }
        );
    }

    /// Tests the `as_ref_trait_bound` function.
    #[test]
    fn as_ref_trait_bound_test() {
        let bound = as_ref_trait_bound(
            &parse_quote! { A, B, C, D, crate },
            &BoundsLifetimeNames {
                env_lt: parse_quote! { 'env },
                txn_lt: parse_quote! { 'txn },
                dbid_lt: parse_quote! { 'dbid },
                kq_lt: parse_quote! { 'kq },
                kp_lt: parse_quote! { 'kp },
                vp_lt: parse_quote! { 'vp },
            },
        );
        assert_eq!(
            bound,
            parse_quote! {
                crate::lt_trait_wrappers::AsRefLt6<
                    'env,
                    'txn,
                    'dbid,
                    'kq,
                    'kp,
                    'vp,
                    [u8],
                >
            }
        );

        let bound = as_ref_trait_bound(
            &parse_quote! { A, B, C, D },
            &BoundsLifetimeNames {
                env_lt: parse_quote! { 'env_0 },
                txn_lt: parse_quote! { 'txn_1 },
                dbid_lt: parse_quote! { 'dbid_2 },
                kq_lt: parse_quote! { 'kq_0 },
                kp_lt: parse_quote! { 'kp_1 },
                vp_lt: parse_quote! { 'vp_2 },
            },
        );
        assert_eq!(
            bound,
            parse_quote! {
                ::atelier_kv_store::lt_trait_wrappers::AsRefLt6<
                    'env_0,
                    'txn_1,
                    'dbid_2,
                    'kq_0,
                    'kp_1,
                    'vp_2,
                    [u8],
                >
            }
        );
    }

    /// Tests the `lifetime_quantifier` function.
    #[test]
    fn lifetime_quantifier_test() {
        let quantifier = lifetime_quantifier(
            &BoundsLifetimeNames {
                env_lt: parse_quote! { 'env },
                txn_lt: parse_quote! { 'txn },
                dbid_lt: parse_quote! { 'dbid },
                kq_lt: parse_quote! { 'kq },
                kp_lt: parse_quote! { 'kp },
                vp_lt: parse_quote! { 'vp },
            },
            false,
        );
        assert_eq!(
            quantifier,
            parse_quote! { for<'env, 'dbid, 'kq, 'kp, 'vp,> }
        );

        let quantifier = lifetime_quantifier(
            &BoundsLifetimeNames {
                env_lt: parse_quote! { 'env },
                txn_lt: parse_quote! { 'txn },
                dbid_lt: parse_quote! { 'dbid },
                kq_lt: parse_quote! { 'kq },
                kp_lt: parse_quote! { 'kp },
                vp_lt: parse_quote! { 'vp },
            },
            true,
        );
        assert_eq!(
            quantifier,
            parse_quote! { for<'env, 'txn, 'dbid, 'kq, 'kp, 'vp,> }
        );

        let quantifier = lifetime_quantifier(
            &BoundsLifetimeNames {
                env_lt: parse_quote! { 'env_0 },
                txn_lt: parse_quote! { 'txn_1 },
                dbid_lt: parse_quote! { 'dbid_2 },
                kq_lt: parse_quote! { 'kq_0 },
                kp_lt: parse_quote! { 'kp_1 },
                vp_lt: parse_quote! { 'vp_2 },
            },
            false,
        );
        assert_eq!(
            quantifier,
            parse_quote! { for<'env_0, 'dbid_2, 'kq_0, 'kp_1, 'vp_2,> }
        );

        let quantifier = lifetime_quantifier(
            &BoundsLifetimeNames {
                env_lt: parse_quote! { 'env_0 },
                txn_lt: parse_quote! { 'txn_1 },
                dbid_lt: parse_quote! { 'dbid_2 },
                kq_lt: parse_quote! { 'kq_0 },
                kp_lt: parse_quote! { 'kp_1 },
                vp_lt: parse_quote! { 'vp_2 },
            },
            true,
        );
        assert_eq!(
            quantifier,
            parse_quote! { for<'env_0, 'txn_1, 'dbid_2, 'kq_0, 'kp_1, 'vp_2,> }
        );
    }

    /// Tests the `find_generics` function.
    #[test]
    fn find_generics_test() {
        let mut test_case = parse_quote! { enum A {B, C} };
        let generics = find_generics(&mut test_case).unwrap();
        assert!(generics.params.is_empty());
        assert_eq!(generics.where_clause, None);

        let mut test_case = parse_quote! { enum A<T0, T1> where T0: X {B(T0), C(T1)} };
        let generics = find_generics(&mut test_case).unwrap();
        assert_eq!(generics.params, parse_quote! { T0, T1 });
        assert_eq!(generics.where_clause, Some(parse_quote! { where T0: X }));

        let mut test_case = parse_quote! { fn f(g: i32, h: ()) -> usize { 0 } };
        let generics = find_generics(&mut test_case).unwrap();
        assert!(generics.params.is_empty());
        assert_eq!(generics.where_clause, None);

        let mut test_case = parse_quote! { fn f<T0, T1>(g: i32, h: ()) -> usize where T0: X { 0 } };
        let generics = find_generics(&mut test_case).unwrap();
        assert_eq!(generics.params, parse_quote! { T0, T1 });
        assert_eq!(generics.where_clause, Some(parse_quote! { where T0: X }));

        let mut test_case = parse_quote! { impl A {} };
        let generics = find_generics(&mut test_case).unwrap();
        assert!(generics.params.is_empty());
        assert_eq!(generics.where_clause, None);

        let mut test_case = parse_quote! { impl<T0, T1> A where T0: X {} };
        let generics = find_generics(&mut test_case).unwrap();
        assert_eq!(generics.params, parse_quote! { T0, T1 });
        assert_eq!(generics.where_clause, Some(parse_quote! { where T0: X }));

        let mut test_case = parse_quote! { struct A {field_0: B, field_1: C} };
        let generics = find_generics(&mut test_case).unwrap();
        assert!(generics.params.is_empty());
        assert_eq!(generics.where_clause, None);

        let mut test_case = parse_quote! { struct A<T0, T1> where T0: X {field_0: B, field_1: C} };
        let generics = find_generics(&mut test_case).unwrap();
        assert_eq!(generics.params, parse_quote! { T0, T1 });
        assert_eq!(generics.where_clause, Some(parse_quote! { where T0: X }));

        let mut test_case = parse_quote! { trait A {fn f(g: i32) -> usize;} };
        let generics = find_generics(&mut test_case).unwrap();
        assert!(generics.params.is_empty());
        assert_eq!(generics.where_clause, None);

        let mut test_case = parse_quote! { trait A<T0, T1> where T0: X {fn f(g: i32) -> usize;} };
        let generics = find_generics(&mut test_case).unwrap();
        assert_eq!(generics.params, parse_quote! { T0, T1 });
        assert_eq!(generics.where_clause, Some(parse_quote! { where T0: X }));

        let mut test_case = parse_quote! { trait A = B; };
        let generics = find_generics(&mut test_case).unwrap();
        assert!(generics.params.is_empty());
        assert_eq!(generics.where_clause, None);

        let mut test_case = parse_quote! { trait A<T0, T1> = B<T0, T1> where T0: X; };
        let generics = find_generics(&mut test_case).unwrap();
        assert_eq!(generics.params, parse_quote! { T0, T1 });
        assert_eq!(generics.where_clause, Some(parse_quote! { where T0: X }));

        let mut test_case = parse_quote! { type A = B; };
        let generics = find_generics(&mut test_case).unwrap();
        assert!(generics.params.is_empty());
        assert_eq!(generics.where_clause, None);

        let mut test_case = parse_quote! { type A<T0, T1> where T0: X = B<T0, T1>; };
        let generics = find_generics(&mut test_case).unwrap();
        assert_eq!(generics.params, parse_quote! { T0, T1 });
        assert_eq!(generics.where_clause, Some(parse_quote! { where T0: X }));

        let mut test_case = parse_quote! { union A {field_0: B, field_1: C} };
        let generics = find_generics(&mut test_case).unwrap();
        assert!(generics.params.is_empty());
        assert_eq!(generics.where_clause, None);

        let mut test_case = parse_quote! { union A<T0, T1> where T0: X {field_0: B, field_1: C} };
        let generics = find_generics(&mut test_case).unwrap();
        assert_eq!(generics.params, parse_quote! { T0, T1 });
        assert_eq!(generics.where_clause, Some(parse_quote! { where T0: X }));

        let mut test_case = parse_quote! { const A: usize = 0; };
        find_generics(&mut test_case).unwrap_err();

        let mut test_case = parse_quote! { extern crate x; };
        find_generics(&mut test_case).unwrap_err();

        let mut test_case = parse_quote! { extern "C" {} };
        find_generics(&mut test_case).unwrap_err();

        let mut test_case = parse_quote! { macro_rules! m {} };
        find_generics(&mut test_case).unwrap_err();

        let mut test_case = parse_quote! { macro m {} };
        find_generics(&mut test_case).unwrap_err();

        let mut test_case = parse_quote! { mod m {} };
        find_generics(&mut test_case).unwrap_err();

        let mut test_case = parse_quote! { static A: usize = 0; };
        find_generics(&mut test_case).unwrap_err();

        let mut test_case = parse_quote! { use ::std::collections::HashMap; };
        find_generics(&mut test_case).unwrap_err();
    }

    /// Tests the `add_bounds` function.
    #[test]
    fn add_bounds_test() {
        let mut test_case = parse_quote! { fn do_something<E, EC, DC, SC>(env: &mut E) where E: ::std::fmt::Debug {} };
        let generics = find_generics(&mut test_case).unwrap();
        add_bounds(
            generics,
            &parse_quote! { E, EC, DC, SC, crate },
            &BoundsLifetimeNames {
                env_lt: parse_quote! { 'env },
                txn_lt: parse_quote! { 'txn },
                dbid_lt: parse_quote! { 'dbid },
                kq_lt: parse_quote! { 'kq },
                kp_lt: parse_quote! { 'kp },
                vp_lt: parse_quote! { 'vp },
            },
        );
        assert_eq!(
            generics.where_clause,
            Some(parse_quote! {
                where E: ::std::fmt::Debug,
                E: 'static + for<'env, 'dbid, 'kq, 'kp, 'vp,> crate::Environment<'env, EC, ::std::option::Option<&'dbid str>, DC, SC, &'kq [u8], &'kp [u8], &'vp [u8],>,
                for<'env, 'txn, 'dbid, 'kq, 'kp, 'vp,> <<E as crate::Environment<'env, EC, ::std::option::Option<&'dbid str>, DC, SC, &'kq [u8], &'kp [u8], &'vp [u8],>>::RoTransaction as crate::Transaction<'txn, &'kq [u8],>>::ReturnedValue: crate::lt_trait_wrappers::AsRefLt6<'env, 'txn, 'dbid, 'kq, 'kp, 'vp, [u8],>,
                for<'env, 'txn, 'dbid, 'kq, 'kp, 'vp,> <<E as crate::Environment<'env, EC, ::std::option::Option<&'dbid str>, DC, SC, &'kq [u8], &'kp [u8], &'vp [u8],>>::RwTransaction as crate::Transaction<'txn, &'kq [u8],>>::ReturnedValue: crate::lt_trait_wrappers::AsRefLt6<'env, 'txn, 'dbid, 'kq, 'kp, 'vp, [u8],>,
                for<'env, 'txn, 'dbid, 'kq, 'kp, 'vp,> <<<E as crate::Environment<'env, EC, ::std::option::Option<&'dbid str>, DC, SC, &'kq [u8], &'kp [u8], &'vp [u8],>>::RoTransaction as crate::Transaction<'txn, &'kq [u8],>>::RoCursor as crate::CursorBasic>::ReturnedKey: crate::lt_trait_wrappers::AsRefLt6<'env, 'txn, 'dbid, 'kq, 'kp, 'vp, [u8],>,
                for<'env, 'txn, 'dbid, 'kq, 'kp, 'vp,> <<<E as crate::Environment<'env, EC, ::std::option::Option<&'dbid str>, DC, SC, &'kq [u8], &'kp [u8], &'vp [u8],>>::RoTransaction as crate::Transaction<'txn, &'kq [u8],>>::RoCursor as crate::CursorBasic>::ReturnedValue: crate::lt_trait_wrappers::AsRefLt6<'env, 'txn, 'dbid, 'kq, 'kp, 'vp, [u8],>,
                for<'env, 'txn, 'dbid, 'kq, 'kp, 'vp,> <<<E as crate::Environment<'env, EC, ::std::option::Option<&'dbid str>, DC, SC, &'kq [u8], &'kp [u8], &'vp [u8],>>::RwTransaction as crate::Transaction<'txn, &'kq [u8],>>::RoCursor as crate::CursorBasic>::ReturnedKey: crate::lt_trait_wrappers::AsRefLt6<'env, 'txn, 'dbid, 'kq, 'kp, 'vp, [u8],>,
                for<'env, 'txn, 'dbid, 'kq, 'kp, 'vp,> <<<E as crate::Environment<'env, EC, ::std::option::Option<&'dbid str>, DC, SC, &'kq [u8], &'kp [u8], &'vp [u8],>>::RwTransaction as crate::Transaction<'txn, &'kq [u8],>>::RoCursor as crate::CursorBasic>::ReturnedValue: crate::lt_trait_wrappers::AsRefLt6<'env, 'txn, 'dbid, 'kq, 'kp, 'vp, [u8],>,
                for<'env, 'txn, 'dbid, 'kq, 'kp, 'vp,> <<<E as crate::Environment<'env, EC, ::std::option::Option<&'dbid str>, DC, SC, &'kq [u8], &'kp [u8], &'vp [u8],>>::RwTransaction as crate::ReadWriteTransaction<'txn, &'kq [u8], &'kp [u8], &'vp [u8],>>::RwCursor as crate::CursorBasic>::ReturnedKey: crate::lt_trait_wrappers::AsRefLt6<'env, 'txn, 'dbid, 'kq, 'kp, 'vp, [u8],>,
                for<'env, 'txn, 'dbid, 'kq, 'kp, 'vp,> <<<E as crate::Environment<'env, EC, ::std::option::Option<&'dbid str>, DC, SC, &'kq [u8], &'kp [u8], &'vp [u8],>>::RwTransaction as crate::ReadWriteTransaction<'txn, &'kq [u8], &'kp [u8], &'vp [u8],>>::RwCursor as crate::CursorBasic>::ReturnedValue: crate::lt_trait_wrappers::AsRefLt6<'env, 'txn, 'dbid, 'kq, 'kp, 'vp, [u8],>
            })
        );

        let mut test_case = parse_quote! { fn do_something<E, EC, DC, SC>(env: &mut E) where E: ::std::fmt::Debug {} };
        let generics = find_generics(&mut test_case).unwrap();
        add_bounds(
            generics,
            &parse_quote! { E, EC, DC, SC },
            &BoundsLifetimeNames {
                env_lt: parse_quote! { 'env },
                txn_lt: parse_quote! { 'txn },
                dbid_lt: parse_quote! { 'dbid },
                kq_lt: parse_quote! { 'kq },
                kp_lt: parse_quote! { 'kp },
                vp_lt: parse_quote! { 'vp },
            },
        );
        assert_eq!(
            generics.where_clause,
            Some(parse_quote! {
                where E: ::std::fmt::Debug,
                E: 'static + for<'env, 'dbid, 'kq, 'kp, 'vp,> ::atelier_kv_store::Environment<'env, EC, ::std::option::Option<&'dbid str>, DC, SC, &'kq [u8], &'kp [u8], &'vp [u8],>,
                for<'env, 'txn, 'dbid, 'kq, 'kp, 'vp,> <<E as ::atelier_kv_store::Environment<'env, EC, ::std::option::Option<&'dbid str>, DC, SC, &'kq [u8], &'kp [u8], &'vp [u8],>>::RoTransaction as ::atelier_kv_store::Transaction<'txn, &'kq [u8],>>::ReturnedValue: ::atelier_kv_store::lt_trait_wrappers::AsRefLt6<'env, 'txn, 'dbid, 'kq, 'kp, 'vp, [u8],>,
                for<'env, 'txn, 'dbid, 'kq, 'kp, 'vp,> <<E as ::atelier_kv_store::Environment<'env, EC, ::std::option::Option<&'dbid str>, DC, SC, &'kq [u8], &'kp [u8], &'vp [u8],>>::RwTransaction as ::atelier_kv_store::Transaction<'txn, &'kq [u8],>>::ReturnedValue: ::atelier_kv_store::lt_trait_wrappers::AsRefLt6<'env, 'txn, 'dbid, 'kq, 'kp, 'vp, [u8],>,
                for<'env, 'txn, 'dbid, 'kq, 'kp, 'vp,> <<<E as ::atelier_kv_store::Environment<'env, EC, ::std::option::Option<&'dbid str>, DC, SC, &'kq [u8], &'kp [u8], &'vp [u8],>>::RoTransaction as ::atelier_kv_store::Transaction<'txn, &'kq [u8],>>::RoCursor as ::atelier_kv_store::CursorBasic>::ReturnedKey: ::atelier_kv_store::lt_trait_wrappers::AsRefLt6<'env, 'txn, 'dbid, 'kq, 'kp, 'vp, [u8],>,
                for<'env, 'txn, 'dbid, 'kq, 'kp, 'vp,> <<<E as ::atelier_kv_store::Environment<'env, EC, ::std::option::Option<&'dbid str>, DC, SC, &'kq [u8], &'kp [u8], &'vp [u8],>>::RoTransaction as ::atelier_kv_store::Transaction<'txn, &'kq [u8],>>::RoCursor as ::atelier_kv_store::CursorBasic>::ReturnedValue: ::atelier_kv_store::lt_trait_wrappers::AsRefLt6<'env, 'txn, 'dbid, 'kq, 'kp, 'vp, [u8],>,
                for<'env, 'txn, 'dbid, 'kq, 'kp, 'vp,> <<<E as ::atelier_kv_store::Environment<'env, EC, ::std::option::Option<&'dbid str>, DC, SC, &'kq [u8], &'kp [u8], &'vp [u8],>>::RwTransaction as ::atelier_kv_store::Transaction<'txn, &'kq [u8],>>::RoCursor as ::atelier_kv_store::CursorBasic>::ReturnedKey: ::atelier_kv_store::lt_trait_wrappers::AsRefLt6<'env, 'txn, 'dbid, 'kq, 'kp, 'vp, [u8],>,
                for<'env, 'txn, 'dbid, 'kq, 'kp, 'vp,> <<<E as ::atelier_kv_store::Environment<'env, EC, ::std::option::Option<&'dbid str>, DC, SC, &'kq [u8], &'kp [u8], &'vp [u8],>>::RwTransaction as ::atelier_kv_store::Transaction<'txn, &'kq [u8],>>::RoCursor as ::atelier_kv_store::CursorBasic>::ReturnedValue: ::atelier_kv_store::lt_trait_wrappers::AsRefLt6<'env, 'txn, 'dbid, 'kq, 'kp, 'vp, [u8],>,
                for<'env, 'txn, 'dbid, 'kq, 'kp, 'vp,> <<<E as ::atelier_kv_store::Environment<'env, EC, ::std::option::Option<&'dbid str>, DC, SC, &'kq [u8], &'kp [u8], &'vp [u8],>>::RwTransaction as ::atelier_kv_store::ReadWriteTransaction<'txn, &'kq [u8], &'kp [u8], &'vp [u8],>>::RwCursor as ::atelier_kv_store::CursorBasic>::ReturnedKey: ::atelier_kv_store::lt_trait_wrappers::AsRefLt6<'env, 'txn, 'dbid, 'kq, 'kp, 'vp, [u8],>,
                for<'env, 'txn, 'dbid, 'kq, 'kp, 'vp,> <<<E as ::atelier_kv_store::Environment<'env, EC, ::std::option::Option<&'dbid str>, DC, SC, &'kq [u8], &'kp [u8], &'vp [u8],>>::RwTransaction as ::atelier_kv_store::ReadWriteTransaction<'txn, &'kq [u8], &'kp [u8], &'vp [u8],>>::RwCursor as ::atelier_kv_store::CursorBasic>::ReturnedValue: ::atelier_kv_store::lt_trait_wrappers::AsRefLt6<'env, 'txn, 'dbid, 'kq, 'kp, 'vp, [u8],>
            })
        );
    }

    /// Tests the `require_binary_static_env_internal` function.
    #[test]
    fn require_binary_static_env_internal_test() {
        let test_output: Item = parse2(
            require_binary_static_env_internal(
                parse_quote! { E, EC, DC, SC, crate },
                parse_quote! { fn do_something<E, EC, DC, SC>(env: &mut E) {} },
            )
            .unwrap(),
        )
        .unwrap();
        assert_eq!(
            test_output,
            parse_quote! {
                fn do_something<E, EC, DC, SC>(env: &mut E) where
                    E: 'static + for<'env, 'dbid, 'kq, 'kp, 'vp,> crate::Environment<'env, EC, ::std::option::Option<&'dbid str>, DC, SC, &'kq [u8], &'kp [u8], &'vp [u8],>,
                    for<'env, 'txn, 'dbid, 'kq, 'kp, 'vp,> <<E as crate::Environment<'env, EC, ::std::option::Option<&'dbid str>, DC, SC, &'kq [u8], &'kp [u8], &'vp [u8],>>::RoTransaction as crate::Transaction<'txn, &'kq [u8],>>::ReturnedValue: crate::lt_trait_wrappers::AsRefLt6<'env, 'txn, 'dbid, 'kq, 'kp, 'vp, [u8],>,
                    for<'env, 'txn, 'dbid, 'kq, 'kp, 'vp,> <<E as crate::Environment<'env, EC, ::std::option::Option<&'dbid str>, DC, SC, &'kq [u8], &'kp [u8], &'vp [u8],>>::RwTransaction as crate::Transaction<'txn, &'kq [u8],>>::ReturnedValue: crate::lt_trait_wrappers::AsRefLt6<'env, 'txn, 'dbid, 'kq, 'kp, 'vp, [u8],>,
                    for<'env, 'txn, 'dbid, 'kq, 'kp, 'vp,> <<<E as crate::Environment<'env, EC, ::std::option::Option<&'dbid str>, DC, SC, &'kq [u8], &'kp [u8], &'vp [u8],>>::RoTransaction as crate::Transaction<'txn, &'kq [u8],>>::RoCursor as crate::CursorBasic>::ReturnedKey: crate::lt_trait_wrappers::AsRefLt6<'env, 'txn, 'dbid, 'kq, 'kp, 'vp, [u8],>,
                    for<'env, 'txn, 'dbid, 'kq, 'kp, 'vp,> <<<E as crate::Environment<'env, EC, ::std::option::Option<&'dbid str>, DC, SC, &'kq [u8], &'kp [u8], &'vp [u8],>>::RoTransaction as crate::Transaction<'txn, &'kq [u8],>>::RoCursor as crate::CursorBasic>::ReturnedValue: crate::lt_trait_wrappers::AsRefLt6<'env, 'txn, 'dbid, 'kq, 'kp, 'vp, [u8],>,
                    for<'env, 'txn, 'dbid, 'kq, 'kp, 'vp,> <<<E as crate::Environment<'env, EC, ::std::option::Option<&'dbid str>, DC, SC, &'kq [u8], &'kp [u8], &'vp [u8],>>::RwTransaction as crate::Transaction<'txn, &'kq [u8],>>::RoCursor as crate::CursorBasic>::ReturnedKey: crate::lt_trait_wrappers::AsRefLt6<'env, 'txn, 'dbid, 'kq, 'kp, 'vp, [u8],>,
                    for<'env, 'txn, 'dbid, 'kq, 'kp, 'vp,> <<<E as crate::Environment<'env, EC, ::std::option::Option<&'dbid str>, DC, SC, &'kq [u8], &'kp [u8], &'vp [u8],>>::RwTransaction as crate::Transaction<'txn, &'kq [u8],>>::RoCursor as crate::CursorBasic>::ReturnedValue: crate::lt_trait_wrappers::AsRefLt6<'env, 'txn, 'dbid, 'kq, 'kp, 'vp, [u8],>,
                    for<'env, 'txn, 'dbid, 'kq, 'kp, 'vp,> <<<E as crate::Environment<'env, EC, ::std::option::Option<&'dbid str>, DC, SC, &'kq [u8], &'kp [u8], &'vp [u8],>>::RwTransaction as crate::ReadWriteTransaction<'txn, &'kq [u8], &'kp [u8], &'vp [u8],>>::RwCursor as crate::CursorBasic>::ReturnedKey: crate::lt_trait_wrappers::AsRefLt6<'env, 'txn, 'dbid, 'kq, 'kp, 'vp, [u8],>,
                    for<'env, 'txn, 'dbid, 'kq, 'kp, 'vp,> <<<E as crate::Environment<'env, EC, ::std::option::Option<&'dbid str>, DC, SC, &'kq [u8], &'kp [u8], &'vp [u8],>>::RwTransaction as crate::ReadWriteTransaction<'txn, &'kq [u8], &'kp [u8], &'vp [u8],>>::RwCursor as crate::CursorBasic>::ReturnedValue: crate::lt_trait_wrappers::AsRefLt6<'env, 'txn, 'dbid, 'kq, 'kp, 'vp, [u8],>
                {}
            }
        );

        let test_output: Item = parse2(require_binary_static_env_internal(
            parse_quote! { E, EC, DC, SC, crate },
            parse_quote! { fn do_something<E, EC, DC, SC>(env: &mut E) where E: ::std::fmt::Debug {} },
        ).unwrap()).unwrap();
        assert_eq!(
            test_output,
            parse_quote! {
                fn do_something<E, EC, DC, SC>(env: &mut E) where
                    E: ::std::fmt::Debug,
                    E: 'static + for<'env, 'dbid, 'kq, 'kp, 'vp,> crate::Environment<'env, EC, ::std::option::Option<&'dbid str>, DC, SC, &'kq [u8], &'kp [u8], &'vp [u8],>,
                    for<'env, 'txn, 'dbid, 'kq, 'kp, 'vp,> <<E as crate::Environment<'env, EC, ::std::option::Option<&'dbid str>, DC, SC, &'kq [u8], &'kp [u8], &'vp [u8],>>::RoTransaction as crate::Transaction<'txn, &'kq [u8],>>::ReturnedValue: crate::lt_trait_wrappers::AsRefLt6<'env, 'txn, 'dbid, 'kq, 'kp, 'vp, [u8],>,
                    for<'env, 'txn, 'dbid, 'kq, 'kp, 'vp,> <<E as crate::Environment<'env, EC, ::std::option::Option<&'dbid str>, DC, SC, &'kq [u8], &'kp [u8], &'vp [u8],>>::RwTransaction as crate::Transaction<'txn, &'kq [u8],>>::ReturnedValue: crate::lt_trait_wrappers::AsRefLt6<'env, 'txn, 'dbid, 'kq, 'kp, 'vp, [u8],>,
                    for<'env, 'txn, 'dbid, 'kq, 'kp, 'vp,> <<<E as crate::Environment<'env, EC, ::std::option::Option<&'dbid str>, DC, SC, &'kq [u8], &'kp [u8], &'vp [u8],>>::RoTransaction as crate::Transaction<'txn, &'kq [u8],>>::RoCursor as crate::CursorBasic>::ReturnedKey: crate::lt_trait_wrappers::AsRefLt6<'env, 'txn, 'dbid, 'kq, 'kp, 'vp, [u8],>,
                    for<'env, 'txn, 'dbid, 'kq, 'kp, 'vp,> <<<E as crate::Environment<'env, EC, ::std::option::Option<&'dbid str>, DC, SC, &'kq [u8], &'kp [u8], &'vp [u8],>>::RoTransaction as crate::Transaction<'txn, &'kq [u8],>>::RoCursor as crate::CursorBasic>::ReturnedValue: crate::lt_trait_wrappers::AsRefLt6<'env, 'txn, 'dbid, 'kq, 'kp, 'vp, [u8],>,
                    for<'env, 'txn, 'dbid, 'kq, 'kp, 'vp,> <<<E as crate::Environment<'env, EC, ::std::option::Option<&'dbid str>, DC, SC, &'kq [u8], &'kp [u8], &'vp [u8],>>::RwTransaction as crate::Transaction<'txn, &'kq [u8],>>::RoCursor as crate::CursorBasic>::ReturnedKey: crate::lt_trait_wrappers::AsRefLt6<'env, 'txn, 'dbid, 'kq, 'kp, 'vp, [u8],>,
                    for<'env, 'txn, 'dbid, 'kq, 'kp, 'vp,> <<<E as crate::Environment<'env, EC, ::std::option::Option<&'dbid str>, DC, SC, &'kq [u8], &'kp [u8], &'vp [u8],>>::RwTransaction as crate::Transaction<'txn, &'kq [u8],>>::RoCursor as crate::CursorBasic>::ReturnedValue: crate::lt_trait_wrappers::AsRefLt6<'env, 'txn, 'dbid, 'kq, 'kp, 'vp, [u8],>,
                    for<'env, 'txn, 'dbid, 'kq, 'kp, 'vp,> <<<E as crate::Environment<'env, EC, ::std::option::Option<&'dbid str>, DC, SC, &'kq [u8], &'kp [u8], &'vp [u8],>>::RwTransaction as crate::ReadWriteTransaction<'txn, &'kq [u8], &'kp [u8], &'vp [u8],>>::RwCursor as crate::CursorBasic>::ReturnedKey: crate::lt_trait_wrappers::AsRefLt6<'env, 'txn, 'dbid, 'kq, 'kp, 'vp, [u8],>,
                    for<'env, 'txn, 'dbid, 'kq, 'kp, 'vp,> <<<E as crate::Environment<'env, EC, ::std::option::Option<&'dbid str>, DC, SC, &'kq [u8], &'kp [u8], &'vp [u8],>>::RwTransaction as crate::ReadWriteTransaction<'txn, &'kq [u8], &'kp [u8], &'vp [u8],>>::RwCursor as crate::CursorBasic>::ReturnedValue: crate::lt_trait_wrappers::AsRefLt6<'env, 'txn, 'dbid, 'kq, 'kp, 'vp, [u8],>
                {}
            }
        );

        let test_output: Item = parse2(require_binary_static_env_internal(
            parse_quote! { E, EC, DC, SC },
            parse_quote! { fn do_something<E, EC, DC, SC>(env: &mut E) where E: ::std::fmt::Debug {} },
        ).unwrap()).unwrap();
        assert_eq!(
            test_output,
            parse_quote! {
                fn do_something<E, EC, DC, SC>(env: &mut E) where
                    E: ::std::fmt::Debug,
                    E: 'static + for<'env, 'dbid, 'kq, 'kp, 'vp,> ::atelier_kv_store::Environment<'env, EC, ::std::option::Option<&'dbid str>, DC, SC, &'kq [u8], &'kp [u8], &'vp [u8],>,
                    for<'env, 'txn, 'dbid, 'kq, 'kp, 'vp,> <<E as ::atelier_kv_store::Environment<'env, EC, ::std::option::Option<&'dbid str>, DC, SC, &'kq [u8], &'kp [u8], &'vp [u8],>>::RoTransaction as ::atelier_kv_store::Transaction<'txn, &'kq [u8],>>::ReturnedValue: ::atelier_kv_store::lt_trait_wrappers::AsRefLt6<'env, 'txn, 'dbid, 'kq, 'kp, 'vp, [u8],>,
                    for<'env, 'txn, 'dbid, 'kq, 'kp, 'vp,> <<E as ::atelier_kv_store::Environment<'env, EC, ::std::option::Option<&'dbid str>, DC, SC, &'kq [u8], &'kp [u8], &'vp [u8],>>::RwTransaction as ::atelier_kv_store::Transaction<'txn, &'kq [u8],>>::ReturnedValue: ::atelier_kv_store::lt_trait_wrappers::AsRefLt6<'env, 'txn, 'dbid, 'kq, 'kp, 'vp, [u8],>,
                    for<'env, 'txn, 'dbid, 'kq, 'kp, 'vp,> <<<E as ::atelier_kv_store::Environment<'env, EC, ::std::option::Option<&'dbid str>, DC, SC, &'kq [u8], &'kp [u8], &'vp [u8],>>::RoTransaction as ::atelier_kv_store::Transaction<'txn, &'kq [u8],>>::RoCursor as ::atelier_kv_store::CursorBasic>::ReturnedKey: ::atelier_kv_store::lt_trait_wrappers::AsRefLt6<'env, 'txn, 'dbid, 'kq, 'kp, 'vp, [u8],>,
                    for<'env, 'txn, 'dbid, 'kq, 'kp, 'vp,> <<<E as ::atelier_kv_store::Environment<'env, EC, ::std::option::Option<&'dbid str>, DC, SC, &'kq [u8], &'kp [u8], &'vp [u8],>>::RoTransaction as ::atelier_kv_store::Transaction<'txn, &'kq [u8],>>::RoCursor as ::atelier_kv_store::CursorBasic>::ReturnedValue: ::atelier_kv_store::lt_trait_wrappers::AsRefLt6<'env, 'txn, 'dbid, 'kq, 'kp, 'vp, [u8],>,
                    for<'env, 'txn, 'dbid, 'kq, 'kp, 'vp,> <<<E as ::atelier_kv_store::Environment<'env, EC, ::std::option::Option<&'dbid str>, DC, SC, &'kq [u8], &'kp [u8], &'vp [u8],>>::RwTransaction as ::atelier_kv_store::Transaction<'txn, &'kq [u8],>>::RoCursor as ::atelier_kv_store::CursorBasic>::ReturnedKey: ::atelier_kv_store::lt_trait_wrappers::AsRefLt6<'env, 'txn, 'dbid, 'kq, 'kp, 'vp, [u8],>,
                    for<'env, 'txn, 'dbid, 'kq, 'kp, 'vp,> <<<E as ::atelier_kv_store::Environment<'env, EC, ::std::option::Option<&'dbid str>, DC, SC, &'kq [u8], &'kp [u8], &'vp [u8],>>::RwTransaction as ::atelier_kv_store::Transaction<'txn, &'kq [u8],>>::RoCursor as ::atelier_kv_store::CursorBasic>::ReturnedValue: ::atelier_kv_store::lt_trait_wrappers::AsRefLt6<'env, 'txn, 'dbid, 'kq, 'kp, 'vp, [u8],>,
                    for<'env, 'txn, 'dbid, 'kq, 'kp, 'vp,> <<<E as ::atelier_kv_store::Environment<'env, EC, ::std::option::Option<&'dbid str>, DC, SC, &'kq [u8], &'kp [u8], &'vp [u8],>>::RwTransaction as ::atelier_kv_store::ReadWriteTransaction<'txn, &'kq [u8], &'kp [u8], &'vp [u8],>>::RwCursor as ::atelier_kv_store::CursorBasic>::ReturnedKey: ::atelier_kv_store::lt_trait_wrappers::AsRefLt6<'env, 'txn, 'dbid, 'kq, 'kp, 'vp, [u8],>,
                    for<'env, 'txn, 'dbid, 'kq, 'kp, 'vp,> <<<E as ::atelier_kv_store::Environment<'env, EC, ::std::option::Option<&'dbid str>, DC, SC, &'kq [u8], &'kp [u8], &'vp [u8],>>::RwTransaction as ::atelier_kv_store::ReadWriteTransaction<'txn, &'kq [u8], &'kp [u8], &'vp [u8],>>::RwCursor as ::atelier_kv_store::CursorBasic>::ReturnedValue: ::atelier_kv_store::lt_trait_wrappers::AsRefLt6<'env, 'txn, 'dbid, 'kq, 'kp, 'vp, [u8],>
                {}
            }
        );

        require_binary_static_env_internal(
            parse_quote! { E, EC, DC },
            parse_quote! { fn do_something<E, EC, DC, DC>(env: &mut E) where E: ::std::fmt::Debug {} },
        )
        .unwrap_err();

        require_binary_static_env_internal(
            parse_quote! { E, EC, DC, SC, self, X },
            parse_quote! { fn do_something<E, EC, DC, SC>(env: &mut E) where E: ::std::fmt::Debug {} },
        )
        .unwrap_err();

        require_binary_static_env_internal(
            parse_quote! { E, EC, DC, SC },
            parse_quote! { const x: u32 = 0; },
        )
        .unwrap_err();
    }

    /// Tests the `require_binary_static_env` function.
    #[test]
    fn require_binary_static_env_test() {
        let test_output: Item = parse2(require_binary_static_env(
            parse_quote! { E, EC, DC, SC, crate },
            parse_quote! { fn do_something<E, EC, DC, SC>(env: &mut E) {} },
        ))
        .unwrap();
        assert_eq!(
            test_output,
            parse_quote! {
                fn do_something<E, EC, DC, SC>(env: &mut E) where
                    E: 'static + for<'env, 'dbid, 'kq, 'kp, 'vp,> crate::Environment<'env, EC, ::std::option::Option<&'dbid str>, DC, SC, &'kq [u8], &'kp [u8], &'vp [u8],>,
                    for<'env, 'txn, 'dbid, 'kq, 'kp, 'vp,> <<E as crate::Environment<'env, EC, ::std::option::Option<&'dbid str>, DC, SC, &'kq [u8], &'kp [u8], &'vp [u8],>>::RoTransaction as crate::Transaction<'txn, &'kq [u8],>>::ReturnedValue: crate::lt_trait_wrappers::AsRefLt6<'env, 'txn, 'dbid, 'kq, 'kp, 'vp, [u8],>,
                    for<'env, 'txn, 'dbid, 'kq, 'kp, 'vp,> <<E as crate::Environment<'env, EC, ::std::option::Option<&'dbid str>, DC, SC, &'kq [u8], &'kp [u8], &'vp [u8],>>::RwTransaction as crate::Transaction<'txn, &'kq [u8],>>::ReturnedValue: crate::lt_trait_wrappers::AsRefLt6<'env, 'txn, 'dbid, 'kq, 'kp, 'vp, [u8],>,
                    for<'env, 'txn, 'dbid, 'kq, 'kp, 'vp,> <<<E as crate::Environment<'env, EC, ::std::option::Option<&'dbid str>, DC, SC, &'kq [u8], &'kp [u8], &'vp [u8],>>::RoTransaction as crate::Transaction<'txn, &'kq [u8],>>::RoCursor as crate::CursorBasic>::ReturnedKey: crate::lt_trait_wrappers::AsRefLt6<'env, 'txn, 'dbid, 'kq, 'kp, 'vp, [u8],>,
                    for<'env, 'txn, 'dbid, 'kq, 'kp, 'vp,> <<<E as crate::Environment<'env, EC, ::std::option::Option<&'dbid str>, DC, SC, &'kq [u8], &'kp [u8], &'vp [u8],>>::RoTransaction as crate::Transaction<'txn, &'kq [u8],>>::RoCursor as crate::CursorBasic>::ReturnedValue: crate::lt_trait_wrappers::AsRefLt6<'env, 'txn, 'dbid, 'kq, 'kp, 'vp, [u8],>,
                    for<'env, 'txn, 'dbid, 'kq, 'kp, 'vp,> <<<E as crate::Environment<'env, EC, ::std::option::Option<&'dbid str>, DC, SC, &'kq [u8], &'kp [u8], &'vp [u8],>>::RwTransaction as crate::Transaction<'txn, &'kq [u8],>>::RoCursor as crate::CursorBasic>::ReturnedKey: crate::lt_trait_wrappers::AsRefLt6<'env, 'txn, 'dbid, 'kq, 'kp, 'vp, [u8],>,
                    for<'env, 'txn, 'dbid, 'kq, 'kp, 'vp,> <<<E as crate::Environment<'env, EC, ::std::option::Option<&'dbid str>, DC, SC, &'kq [u8], &'kp [u8], &'vp [u8],>>::RwTransaction as crate::Transaction<'txn, &'kq [u8],>>::RoCursor as crate::CursorBasic>::ReturnedValue: crate::lt_trait_wrappers::AsRefLt6<'env, 'txn, 'dbid, 'kq, 'kp, 'vp, [u8],>,
                    for<'env, 'txn, 'dbid, 'kq, 'kp, 'vp,> <<<E as crate::Environment<'env, EC, ::std::option::Option<&'dbid str>, DC, SC, &'kq [u8], &'kp [u8], &'vp [u8],>>::RwTransaction as crate::ReadWriteTransaction<'txn, &'kq [u8], &'kp [u8], &'vp [u8],>>::RwCursor as crate::CursorBasic>::ReturnedKey: crate::lt_trait_wrappers::AsRefLt6<'env, 'txn, 'dbid, 'kq, 'kp, 'vp, [u8],>,
                    for<'env, 'txn, 'dbid, 'kq, 'kp, 'vp,> <<<E as crate::Environment<'env, EC, ::std::option::Option<&'dbid str>, DC, SC, &'kq [u8], &'kp [u8], &'vp [u8],>>::RwTransaction as crate::ReadWriteTransaction<'txn, &'kq [u8], &'kp [u8], &'vp [u8],>>::RwCursor as crate::CursorBasic>::ReturnedValue: crate::lt_trait_wrappers::AsRefLt6<'env, 'txn, 'dbid, 'kq, 'kp, 'vp, [u8],>
                {}
            }
        );

        let test_output: Item = parse2(require_binary_static_env(
            parse_quote! { E, EC, DC, SC, crate },
            parse_quote! { fn do_something<E, EC, DC, SC>(env: &mut E) where E: ::std::fmt::Debug {} },
        )).unwrap();
        assert_eq!(
            test_output,
            parse_quote! {
                fn do_something<E, EC, DC, SC>(env: &mut E) where
                    E: ::std::fmt::Debug,
                    E: 'static + for<'env, 'dbid, 'kq, 'kp, 'vp,> crate::Environment<'env, EC, ::std::option::Option<&'dbid str>, DC, SC, &'kq [u8], &'kp [u8], &'vp [u8],>,
                    for<'env, 'txn, 'dbid, 'kq, 'kp, 'vp,> <<E as crate::Environment<'env, EC, ::std::option::Option<&'dbid str>, DC, SC, &'kq [u8], &'kp [u8], &'vp [u8],>>::RoTransaction as crate::Transaction<'txn, &'kq [u8],>>::ReturnedValue: crate::lt_trait_wrappers::AsRefLt6<'env, 'txn, 'dbid, 'kq, 'kp, 'vp, [u8],>,
                    for<'env, 'txn, 'dbid, 'kq, 'kp, 'vp,> <<E as crate::Environment<'env, EC, ::std::option::Option<&'dbid str>, DC, SC, &'kq [u8], &'kp [u8], &'vp [u8],>>::RwTransaction as crate::Transaction<'txn, &'kq [u8],>>::ReturnedValue: crate::lt_trait_wrappers::AsRefLt6<'env, 'txn, 'dbid, 'kq, 'kp, 'vp, [u8],>,
                    for<'env, 'txn, 'dbid, 'kq, 'kp, 'vp,> <<<E as crate::Environment<'env, EC, ::std::option::Option<&'dbid str>, DC, SC, &'kq [u8], &'kp [u8], &'vp [u8],>>::RoTransaction as crate::Transaction<'txn, &'kq [u8],>>::RoCursor as crate::CursorBasic>::ReturnedKey: crate::lt_trait_wrappers::AsRefLt6<'env, 'txn, 'dbid, 'kq, 'kp, 'vp, [u8],>,
                    for<'env, 'txn, 'dbid, 'kq, 'kp, 'vp,> <<<E as crate::Environment<'env, EC, ::std::option::Option<&'dbid str>, DC, SC, &'kq [u8], &'kp [u8], &'vp [u8],>>::RoTransaction as crate::Transaction<'txn, &'kq [u8],>>::RoCursor as crate::CursorBasic>::ReturnedValue: crate::lt_trait_wrappers::AsRefLt6<'env, 'txn, 'dbid, 'kq, 'kp, 'vp, [u8],>,
                    for<'env, 'txn, 'dbid, 'kq, 'kp, 'vp,> <<<E as crate::Environment<'env, EC, ::std::option::Option<&'dbid str>, DC, SC, &'kq [u8], &'kp [u8], &'vp [u8],>>::RwTransaction as crate::Transaction<'txn, &'kq [u8],>>::RoCursor as crate::CursorBasic>::ReturnedKey: crate::lt_trait_wrappers::AsRefLt6<'env, 'txn, 'dbid, 'kq, 'kp, 'vp, [u8],>,
                    for<'env, 'txn, 'dbid, 'kq, 'kp, 'vp,> <<<E as crate::Environment<'env, EC, ::std::option::Option<&'dbid str>, DC, SC, &'kq [u8], &'kp [u8], &'vp [u8],>>::RwTransaction as crate::Transaction<'txn, &'kq [u8],>>::RoCursor as crate::CursorBasic>::ReturnedValue: crate::lt_trait_wrappers::AsRefLt6<'env, 'txn, 'dbid, 'kq, 'kp, 'vp, [u8],>,
                    for<'env, 'txn, 'dbid, 'kq, 'kp, 'vp,> <<<E as crate::Environment<'env, EC, ::std::option::Option<&'dbid str>, DC, SC, &'kq [u8], &'kp [u8], &'vp [u8],>>::RwTransaction as crate::ReadWriteTransaction<'txn, &'kq [u8], &'kp [u8], &'vp [u8],>>::RwCursor as crate::CursorBasic>::ReturnedKey: crate::lt_trait_wrappers::AsRefLt6<'env, 'txn, 'dbid, 'kq, 'kp, 'vp, [u8],>,
                    for<'env, 'txn, 'dbid, 'kq, 'kp, 'vp,> <<<E as crate::Environment<'env, EC, ::std::option::Option<&'dbid str>, DC, SC, &'kq [u8], &'kp [u8], &'vp [u8],>>::RwTransaction as crate::ReadWriteTransaction<'txn, &'kq [u8], &'kp [u8], &'vp [u8],>>::RwCursor as crate::CursorBasic>::ReturnedValue: crate::lt_trait_wrappers::AsRefLt6<'env, 'txn, 'dbid, 'kq, 'kp, 'vp, [u8],>
                {}
            }
        );

        let test_output: Item = parse2(require_binary_static_env(
            parse_quote! { E, EC, DC, SC },
            parse_quote! { fn do_something<E, EC, DC, SC>(env: &mut E) where E: ::std::fmt::Debug {} },
        )).unwrap();
        assert_eq!(
            test_output,
            parse_quote! {
                fn do_something<E, EC, DC, SC>(env: &mut E) where
                    E: ::std::fmt::Debug,
                    E: 'static + for<'env, 'dbid, 'kq, 'kp, 'vp,> ::atelier_kv_store::Environment<'env, EC, ::std::option::Option<&'dbid str>, DC, SC, &'kq [u8], &'kp [u8], &'vp [u8],>,
                    for<'env, 'txn, 'dbid, 'kq, 'kp, 'vp,> <<E as ::atelier_kv_store::Environment<'env, EC, ::std::option::Option<&'dbid str>, DC, SC, &'kq [u8], &'kp [u8], &'vp [u8],>>::RoTransaction as ::atelier_kv_store::Transaction<'txn, &'kq [u8],>>::ReturnedValue: ::atelier_kv_store::lt_trait_wrappers::AsRefLt6<'env, 'txn, 'dbid, 'kq, 'kp, 'vp, [u8],>,
                    for<'env, 'txn, 'dbid, 'kq, 'kp, 'vp,> <<E as ::atelier_kv_store::Environment<'env, EC, ::std::option::Option<&'dbid str>, DC, SC, &'kq [u8], &'kp [u8], &'vp [u8],>>::RwTransaction as ::atelier_kv_store::Transaction<'txn, &'kq [u8],>>::ReturnedValue: ::atelier_kv_store::lt_trait_wrappers::AsRefLt6<'env, 'txn, 'dbid, 'kq, 'kp, 'vp, [u8],>,
                    for<'env, 'txn, 'dbid, 'kq, 'kp, 'vp,> <<<E as ::atelier_kv_store::Environment<'env, EC, ::std::option::Option<&'dbid str>, DC, SC, &'kq [u8], &'kp [u8], &'vp [u8],>>::RoTransaction as ::atelier_kv_store::Transaction<'txn, &'kq [u8],>>::RoCursor as ::atelier_kv_store::CursorBasic>::ReturnedKey: ::atelier_kv_store::lt_trait_wrappers::AsRefLt6<'env, 'txn, 'dbid, 'kq, 'kp, 'vp, [u8],>,
                    for<'env, 'txn, 'dbid, 'kq, 'kp, 'vp,> <<<E as ::atelier_kv_store::Environment<'env, EC, ::std::option::Option<&'dbid str>, DC, SC, &'kq [u8], &'kp [u8], &'vp [u8],>>::RoTransaction as ::atelier_kv_store::Transaction<'txn, &'kq [u8],>>::RoCursor as ::atelier_kv_store::CursorBasic>::ReturnedValue: ::atelier_kv_store::lt_trait_wrappers::AsRefLt6<'env, 'txn, 'dbid, 'kq, 'kp, 'vp, [u8],>,
                    for<'env, 'txn, 'dbid, 'kq, 'kp, 'vp,> <<<E as ::atelier_kv_store::Environment<'env, EC, ::std::option::Option<&'dbid str>, DC, SC, &'kq [u8], &'kp [u8], &'vp [u8],>>::RwTransaction as ::atelier_kv_store::Transaction<'txn, &'kq [u8],>>::RoCursor as ::atelier_kv_store::CursorBasic>::ReturnedKey: ::atelier_kv_store::lt_trait_wrappers::AsRefLt6<'env, 'txn, 'dbid, 'kq, 'kp, 'vp, [u8],>,
                    for<'env, 'txn, 'dbid, 'kq, 'kp, 'vp,> <<<E as ::atelier_kv_store::Environment<'env, EC, ::std::option::Option<&'dbid str>, DC, SC, &'kq [u8], &'kp [u8], &'vp [u8],>>::RwTransaction as ::atelier_kv_store::Transaction<'txn, &'kq [u8],>>::RoCursor as ::atelier_kv_store::CursorBasic>::ReturnedValue: ::atelier_kv_store::lt_trait_wrappers::AsRefLt6<'env, 'txn, 'dbid, 'kq, 'kp, 'vp, [u8],>,
                    for<'env, 'txn, 'dbid, 'kq, 'kp, 'vp,> <<<E as ::atelier_kv_store::Environment<'env, EC, ::std::option::Option<&'dbid str>, DC, SC, &'kq [u8], &'kp [u8], &'vp [u8],>>::RwTransaction as ::atelier_kv_store::ReadWriteTransaction<'txn, &'kq [u8], &'kp [u8], &'vp [u8],>>::RwCursor as ::atelier_kv_store::CursorBasic>::ReturnedKey: ::atelier_kv_store::lt_trait_wrappers::AsRefLt6<'env, 'txn, 'dbid, 'kq, 'kp, 'vp, [u8],>,
                    for<'env, 'txn, 'dbid, 'kq, 'kp, 'vp,> <<<E as ::atelier_kv_store::Environment<'env, EC, ::std::option::Option<&'dbid str>, DC, SC, &'kq [u8], &'kp [u8], &'vp [u8],>>::RwTransaction as ::atelier_kv_store::ReadWriteTransaction<'txn, &'kq [u8], &'kp [u8], &'vp [u8],>>::RwCursor as ::atelier_kv_store::CursorBasic>::ReturnedValue: ::atelier_kv_store::lt_trait_wrappers::AsRefLt6<'env, 'txn, 'dbid, 'kq, 'kp, 'vp, [u8],>
                {}
            }
        );

        let test_output: Result<Item, _> = parse2(require_binary_static_env(
            parse_quote! { E, EC, DC },
            parse_quote! { fn do_something<E, EC, DC, DC>(env: &mut E) where E: ::std::fmt::Debug {} },
        ));
        test_output.unwrap();

        let test_output: Result<Item, _> = parse2(require_binary_static_env(
            parse_quote! { E, EC, DC, crate },
            parse_quote! { fn do_something<E, EC, DC, DC>(env: &mut E) where E: ::std::fmt::Debug {} },
        ));
        test_output.unwrap();

        let test_output: Result<Item, _> = parse2(require_binary_static_env(
            parse_quote! { E, EC, DC, SC, self, X },
            parse_quote! { fn do_something<E, EC, DC, SC>(env: &mut E) where E: ::std::fmt::Debug {} },
        ));
        test_output.unwrap();

        let test_output: Result<Item, _> = parse2(require_binary_static_env(
            parse_quote! { E, EC, DC, SC },
            parse_quote! { const x: u32 = 0; },
        ));
        test_output.unwrap();
    }
}
