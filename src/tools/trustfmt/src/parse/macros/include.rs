//! Trust (T14d, DECISION_QUEUE T14-FMT-1): the path of an `include!` the
//! module resolver can follow, which is one string literal.

use std::panic::{AssertUnwindSafe, catch_unwind};

use rustc_ast::ast;
use rustc_ast::token::TokenKind;
use rustc_parse::exp;

use crate::parse::macros::build_stream_parser;
use crate::parse::session::ParseSess;

/// The literal path of `include!("<path>")` (a trailing comma allowed), or
/// `None` for any other argument: `concat!(..)`, `env!(..)`, a constant.
pub(crate) fn parse_include_path(psess: &ParseSess, mac: &ast::MacCall) -> Option<String> {
    catch_unwind(AssertUnwindSafe(|| parse_include_path_inner(psess, mac)))
        .ok()
        .flatten()
}

fn parse_include_path_inner(psess: &ParseSess, mac: &ast::MacCall) -> Option<String> {
    let mut parser = build_stream_parser(psess.inner(), mac.args.tokens.clone());
    let expr = match parser.parse_expr() {
        Ok(expr) => expr,
        Err(error) => {
            error.cancel();
            return None;
        }
    };
    let _ = parser.eat(exp!(Comma));
    if parser.token.kind != TokenKind::Eof {
        return None;
    }
    match &expr.kind {
        ast::ExprKind::Lit(token_lit) => match ast::LitKind::from_token_lit(*token_lit) {
            Ok(ast::LitKind::Str(symbol, _)) => Some(symbol.to_string()),
            _ => None,
        },
        _ => None,
    }
}
