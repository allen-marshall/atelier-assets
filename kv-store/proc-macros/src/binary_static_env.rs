//! This module contains support for macros related to working with `'static`
//! storage environments where the keys and values are byte strings, i.e.
//! LMDB-like storage environments.

use crate::{parse_macro_args, MacroArg, MacroArgs};
use quote::ToTokens;
use syn::parse::{Parse, ParseStream};
use syn::{parse2, parse_quote, Lifetime, Type, TypeParamBound};

pub(crate) mod require_binary_cursor;
pub(crate) mod require_binary_rw_cursor;
pub(crate) mod require_binary_rw_txn;
pub(crate) mod require_binary_static_env;
pub(crate) mod require_binary_static_env_ext;
pub(crate) mod require_binary_txn;

/// Type representing macro attribute arguments, where the following arguments
/// are expected:
/// - (mandatory) 1 argument representing a type.
/// - (optional) 1 argument representing a path to the root of the
///   `atelier_kv_store` crate. Defaults to `::atelier_kv_store`.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct TypeAndCrateRootArgs {
    /// Parsed type argument.
    type_arg: Type,

    /// Parsed path argument. Contains the default value if the argument was
    /// not provided.
    crate_root_path: syn::Path,
}

impl MacroArgs for TypeAndCrateRootArgs {
    const NUM_MANDATORY_ARGS: usize = 1;
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
        Ok(TypeAndCrateRootArgs {
            type_arg: parse2(mandatory_args_vec[0].to_token_stream())?,
            crate_root_path: parse2(optional_args_vec[0].to_token_stream())?,
        })
    }
}

impl Parse for TypeAndCrateRootArgs {
    fn parse(input: ParseStream) -> Result<Self, syn::Error> {
        parse_macro_args(input)
    }
}

/// Gets the [`Environment`][Environment] trait bound to use for the main
/// storage environment type.
///
/// [Environment]: atelier_kv_store::Environment
fn env_trait_bound(env_lt: &Lifetime, crate_root_path: &syn::Path) -> TypeParamBound {
    parse_quote! {
        #crate_root_path::Environment<
            #env_lt,
            [u8],
            [u8],
            [u8],
        >
    }
}

/// Gets the [`EnvironmentExt`][EnvironmentExt] trait bound to
/// use for the main storage environment type.
///
/// [EnvironmentExt]: atelier_kv_store::EnvironmentExt
fn env_ext_trait_bound(
    env_lt: &Lifetime,
    dbid_lt: &Lifetime,
    env_cfg_type: &Type,
    db_cfg_type: &Type,
    sync_cfg_type: &Type,
    crate_root_path: &syn::Path,
) -> TypeParamBound {
    parse_quote! {
        #crate_root_path::EnvironmentExt<
            #env_lt,
            #env_cfg_type,
            ::std::option::Option<& #dbid_lt str>,
            #db_cfg_type,
            #sync_cfg_type,
            [u8],
            [u8],
            [u8],
        >
    }
}

/// Gets the [`TransactionBasic`][TransactionBasic] trait bound to use for
/// transaction types.
///
/// [TransactionBasic]: atelier_kv_store::TransactionBasic
fn txn_basic_trait_bound(crate_root_path: &syn::Path) -> TypeParamBound {
    parse_quote! {
        #crate_root_path::TransactionBasic
    }
}

/// Gets the [`Transaction`][Transaction] trait bound to use for transaction
/// types.
///
/// [Transaction]: atelier_kv_store::Transaction
fn txn_trait_bound(txn_lt: &Lifetime, crate_root_path: &syn::Path) -> TypeParamBound {
    parse_quote! {
        #crate_root_path::Transaction<
            #txn_lt,
            [u8],
        >
    }
}

/// Gets the [`ReadWriteTransaction`][ReadWriteTransaction] trait bound to use
/// for read-write transaction types.
///
/// [ReadWriteTransaction]: atelier_kv_store::ReadWriteTransaction
fn rw_txn_trait_bound(txn_lt: &Lifetime, crate_root_path: &syn::Path) -> TypeParamBound {
    parse_quote! {
        #crate_root_path::ReadWriteTransaction<
            #txn_lt,
            [u8],
            [u8],
            [u8],
        >
    }
}

/// Gets the [`CursorBasic`][CursorBasic] trait bound to use for cursor types.
///
/// [CursorBasic]: atelier_kv_store::CursorBasic
fn cursor_basic_trait_bound(crate_root_path: &syn::Path) -> TypeParamBound {
    parse_quote! {
        #crate_root_path::CursorBasic
    }
}

/// Gets the [`Cursor`][Cursor] trait bound to use for cursor types.
///
/// [Cursor]: atelier_kv_store::Cursor
fn cursor_trait_bound(cursor_lt: &Lifetime, crate_root_path: &syn::Path) -> TypeParamBound {
    parse_quote! {
        #crate_root_path::Cursor<
            #cursor_lt,
            [u8],
        >
    }
}

/// Gets the [`ReadWriteCursor`][ReadWriteCursor] trait bound to use for
/// read-write cursor types.
///
/// [ReadWriteCursor]: atelier_kv_store::ReadWriteCursor
fn rw_cursor_trait_bound(cursor_lt: &Lifetime, crate_root_path: &syn::Path) -> TypeParamBound {
    parse_quote! {
        #crate_root_path::ReadWriteCursor<
            #cursor_lt,
            [u8],
            [u8],
            [u8],
        >
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Tests functionality of the `TypeAndCrateRootArgs` type.
    #[test]
    fn type_and_crate_root_args_test() {
        let args: TypeAndCrateRootArgs = parse_quote! { T };
        assert_eq!(
            args,
            TypeAndCrateRootArgs {
                type_arg: parse_quote! { T },
                crate_root_path: parse_quote! { ::atelier_kv_store },
            }
        );

        let args: TypeAndCrateRootArgs = parse_quote! { T, };
        assert_eq!(
            args,
            TypeAndCrateRootArgs {
                type_arg: parse_quote! { T },
                crate_root_path: parse_quote! { ::atelier_kv_store },
            }
        );

        let args: TypeAndCrateRootArgs = parse_quote! { <A<'a> as B>::C };
        assert_eq!(
            args,
            TypeAndCrateRootArgs {
                type_arg: parse_quote! { <A<'a> as B>::C },
                crate_root_path: parse_quote! { ::atelier_kv_store },
            }
        );

        let args: TypeAndCrateRootArgs = parse_quote! { <A<'a> as B>::C, akvs::x };
        assert_eq!(
            args,
            TypeAndCrateRootArgs {
                type_arg: parse_quote! { <A<'a> as B>::C },
                crate_root_path: parse_quote! { akvs::x },
            }
        );

        let args: Result<TypeAndCrateRootArgs, _> = parse2(parse_quote! {});
        args.unwrap_err();

        let args: Result<TypeAndCrateRootArgs, _> = parse2(parse_quote! { if , 'a () });
        args.unwrap_err();

        let args: Result<TypeAndCrateRootArgs, _> = parse2(parse_quote! { 'a });
        args.unwrap_err();

        let args: Result<TypeAndCrateRootArgs, _> = parse2(parse_quote! { A, akvs, B });
        args.unwrap_err();
    }

    /// Tests the `env_trait_bound` function.
    #[test]
    fn env_trait_bound_test() {
        let bound = env_trait_bound(&parse_quote! { 'env }, &parse_quote! { crate });
        assert_eq!(
            bound,
            parse_quote! {
                crate::Environment<
                    'env,
                    [u8],
                    [u8],
                    [u8],
                >
            }
        );

        let bound = env_trait_bound(
            &parse_quote! { 'env_0 },
            &parse_quote! { ::atelier_kv_store },
        );
        assert_eq!(
            bound,
            parse_quote! {
                ::atelier_kv_store::Environment<
                    'env_0,
                    [u8],
                    [u8],
                    [u8],
                >
            }
        );
    }

    /// Tests the `env_ext_trait_bound` function.
    #[test]
    fn env_ext_trait_bound_test() {
        let bound = env_ext_trait_bound(
            &parse_quote! { 'env },
            &parse_quote! { 'dbid },
            &parse_quote! { EC },
            &parse_quote! { DC },
            &parse_quote! { SC },
            &parse_quote! { crate },
        );
        assert_eq!(
            bound,
            parse_quote! {
                crate::EnvironmentExt<
                    'env,
                    EC,
                    ::std::option::Option<&'dbid str>,
                    DC,
                    SC,
                    [u8],
                    [u8],
                    [u8],
                >
            }
        );

        let bound = env_ext_trait_bound(
            &parse_quote! { 'env_0 },
            &parse_quote! { 'dbid_1 },
            &parse_quote! { A<'a> },
            &parse_quote! { B<'env> },
            &parse_quote! { C<'c> },
            &parse_quote! { ::atelier_kv_store },
        );
        assert_eq!(
            bound,
            parse_quote! {
                ::atelier_kv_store::EnvironmentExt<
                    'env_0,
                    A<'a>,
                    ::std::option::Option<&'dbid_1 str>,
                    B<'env>,
                    C<'c>,
                    [u8],
                    [u8],
                    [u8],
                >
            }
        );
    }

    /// Tests the `txn_basic_trait_bound` function.
    #[test]
    fn txn_basic_trait_bound_test() {
        let bound = txn_basic_trait_bound(&parse_quote! { crate });
        assert_eq!(
            bound,
            parse_quote! {
                crate::TransactionBasic
            }
        );

        let bound = txn_basic_trait_bound(&parse_quote! { ::atelier_kv_store });
        assert_eq!(
            bound,
            parse_quote! {
                ::atelier_kv_store::TransactionBasic
            }
        );
    }

    /// Tests the `txn_trait_bound` function.
    #[test]
    fn txn_trait_bound_test() {
        let bound = txn_trait_bound(&parse_quote! { 'txn }, &parse_quote! { crate });
        assert_eq!(
            bound,
            parse_quote! {
                crate::Transaction<
                    'txn,
                    [u8],
                >
            }
        );

        let bound = txn_trait_bound(
            &parse_quote! { 'txn_0 },
            &parse_quote! { ::atelier_kv_store },
        );
        assert_eq!(
            bound,
            parse_quote! {
                ::atelier_kv_store::Transaction<
                    'txn_0,
                    [u8],
                >
            }
        );
    }

    /// Tests the `rw_txn_trait_bound` function.
    #[test]
    fn rw_txn_trait_bound_test() {
        let bound = rw_txn_trait_bound(&parse_quote! { 'txn }, &parse_quote! { crate });
        assert_eq!(
            bound,
            parse_quote! {
                crate::ReadWriteTransaction<
                    'txn,
                    [u8],
                    [u8],
                    [u8],
                >
            }
        );

        let bound = rw_txn_trait_bound(
            &parse_quote! { 'txn_0 },
            &parse_quote! { ::atelier_kv_store },
        );
        assert_eq!(
            bound,
            parse_quote! {
                ::atelier_kv_store::ReadWriteTransaction<
                    'txn_0,
                    [u8],
                    [u8],
                    [u8],
                >
            }
        );
    }

    /// Tests the `cursor_basic_trait_bound` function.
    #[test]
    fn cursor_basic_trait_bound_test() {
        let bound = cursor_basic_trait_bound(&parse_quote! { crate });
        assert_eq!(
            bound,
            parse_quote! {
                crate::CursorBasic
            }
        );

        let bound = cursor_basic_trait_bound(&parse_quote! { ::atelier_kv_store });
        assert_eq!(
            bound,
            parse_quote! {
                ::atelier_kv_store::CursorBasic
            }
        );
    }

    /// Tests the `cursor_trait_bound` function.
    #[test]
    fn cursor_trait_bound_test() {
        let bound = cursor_trait_bound(&parse_quote! { 'cursor }, &parse_quote! { crate });
        assert_eq!(
            bound,
            parse_quote! {
                crate::Cursor<
                    'cursor,
                    [u8],
                >
            }
        );

        let bound = cursor_trait_bound(
            &parse_quote! { 'cursor_0 },
            &parse_quote! { ::atelier_kv_store },
        );
        assert_eq!(
            bound,
            parse_quote! {
                ::atelier_kv_store::Cursor<
                    'cursor_0,
                    [u8],
                >
            }
        );
    }

    /// Tests the `rw_cursor_trait_bound` function.
    #[test]
    fn rw_cursor_trait_bound_test() {
        let bound = rw_cursor_trait_bound(&parse_quote! { 'cursor }, &parse_quote! { crate });
        assert_eq!(
            bound,
            parse_quote! {
                crate::ReadWriteCursor<
                    'cursor,
                    [u8],
                    [u8],
                    [u8],
                >
            }
        );

        let bound = rw_cursor_trait_bound(
            &parse_quote! { 'cursor_0 },
            &parse_quote! { ::atelier_kv_store },
        );
        assert_eq!(
            bound,
            parse_quote! {
                ::atelier_kv_store::ReadWriteCursor<
                    'cursor_0,
                    [u8],
                    [u8],
                    [u8],
                >
            }
        );
    }
}
