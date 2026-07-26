//! trust-ts-embed: the TypeScript front end of the autoformalization pipeline.
//!
//! A deterministic TypeScript fragment is lowered to one [`TsFunction`] (`TsCore`),
//! from which a [`trust_types::VerifiableFunction`] is derived — the "TS image" the
//! refinement toolchain (`trust-transval` → `trust-router` → `ay`) compares against
//! a Rust port's image. `TsCore` is the single intermediate (the same value later
//! derives a Clean term for the kernel path), so a refinement proof and a kernel
//! certificate are provably about the same TS program. Constructs outside the
//! fragment fail closed as a typed [`FragmentEscape`] — never a partial image.
//!
//! `TsCore` can be built programmatically or parsed from real `.ts` source by the
//! in-crate recursive-descent front end ([`parse_function`] / [`parse_module`],
//! `parse.rs`) — no foreign parser is vendored, and the fragment that front end
//! admits is narrower than the fragment `TsCore` can express. The audited artifact
//! either way is the lowering here, cross-checked against Node by the differential
//! bridge.
//!
//! ## Standing
//!
//! Nothing in the tree drives this crate today. The engine that did compared a
//! TypeScript reference against a TypeScript port, which is a refinement between
//! two copies of a non-authoritative language and not the fail-closed
//! TS → Rust+Lean elaboration the ratified design admits a frontend for; it was
//! removed rather than kept as a standing invitation to read its verdicts as
//! Trust proofs. What survives here is the part that direction still needs: a
//! fragment that fails closed instead of approximating, and one intermediate
//! shared by the refinement image and the kernel term. Any revival owes the
//! zero-authority firewall first — a frontend may propose an obligation, never
//! assert one.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0

mod core;
mod escape;
mod inline;
mod interp;
mod lower;
mod parse;

pub use crate::core::{TsExpr, TsFunction, TsStmt, TsTy, TsVar};
pub use crate::escape::{FragmentEscape, UnsupportedTsConstruct};
pub use crate::inline::inline_calls;
pub use crate::interp::{eval, eval_module, eval_with_arrays};
pub use crate::lower::lower_function;
pub use crate::parse::{parse_function, parse_module, ParseError};

#[cfg(test)]
mod tests {
    use super::*;
    use trust_types::BinOp;

    fn u16t() -> TsTy {
        TsTy::uint(16)
    }

    #[test]
    fn lowers_straight_line_add() {
        let f = TsFunction {
            name: "add".into(),
            def_path: "test::add".into(),
            params: vec![TsVar::new("a", u16t()), TsVar::new("b", u16t())],
            body: vec![TsStmt::Return {
                value: TsExpr::Bin {
                    op: BinOp::Add,
                    lhs: Box::new(TsExpr::Var(TsVar::new("a", u16t()))),
                    rhs: Box::new(TsExpr::Var(TsVar::new("b", u16t()))),
                    ty: u16t(),
                },
            }],
            ret: u16t(),
        };
        let vf = lower_function(&f).expect("add lowers");
        assert_eq!(vf.body.arg_count, 2);
        // param locals keep their names so the relation can align by name
        assert_eq!(vf.body.locals[1].name.as_deref(), Some("a"));
        assert_eq!(vf.body.locals[2].name.as_deref(), Some("b"));
        // straight-line: exactly one block ending in Return
        assert_eq!(vf.body.blocks.len(), 1);
    }

    #[test]
    fn lowers_if_expr_to_a_switchint_diamond() {
        // min(a, b) = if a <= b { a } else { b }
        let f = TsFunction {
            name: "min".into(),
            def_path: "test::min".into(),
            params: vec![TsVar::new("a", u16t()), TsVar::new("b", u16t())],
            body: vec![TsStmt::Return {
                value: TsExpr::min(
                    TsExpr::Var(TsVar::new("a", u16t())),
                    TsExpr::Var(TsVar::new("b", u16t())),
                    u16t(),
                ),
            }],
            ret: u16t(),
        };
        let vf = lower_function(&f).expect("min lowers");
        // a diamond: entry switch + then + else + merge(=return) = 4 blocks
        assert_eq!(vf.body.blocks.len(), 4);
        assert!(
            vf.body
                .blocks
                .iter()
                .any(|b| matches!(b.terminator, trust_types::Terminator::SwitchInt { .. })),
            "the If-expr must lower to a SwitchInt"
        );
    }

    #[test]
    fn unbound_variable_fails_closed() {
        let f = TsFunction {
            name: "bad".into(),
            def_path: "test::bad".into(),
            params: vec![],
            body: vec![TsStmt::Return { value: TsExpr::Var(TsVar::new("nope", u16t())) }],
            ret: u16t(),
        };
        let err = lower_function(&f).expect_err("unbound var must escape");
        assert!(matches!(err.reason, UnsupportedTsConstruct::UnboundVariable { .. }));
    }
}
