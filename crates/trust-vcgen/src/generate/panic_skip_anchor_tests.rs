// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: MIT OR Apache-2.0

//! PANIC-SKIP-ANCHOR-1 (2026-10-05): which call sites may leave their
//! ARGUMENTS out of the fail-closed `UnsupportedMir` collector.
//!
//! The collector skipped the arguments of every call whose RENDERING matched
//! `is_panic_intrinsic_call` (`::panicking::`, `ends_with("::panic")`, …). A
//! user `fn panic(x: u64) -> u64` that returns normally matched, so its
//! identity-less `T::LIMIT` argument lost its `ConstValue::OpaqueScalar` row and
//! `-Ztrust-policy=certify` accepted the caller (measured on the stage 1 of
//! `76a6ea45b2`; `tests/ui/trust/panic_skip_user_fn_named_panic.rs`). The skip
//! now needs what the bridge's diverging-site arm needs: no continuation, the
//! extractor's DIVERGE-ENTRY-1 stamp on the `CalleeKey`, and the name as a
//! narrowing conjunct.
//!
//! MUTANT WITNESSES (measured 2026-10-05): with the old name-only gate
//! restored, the five `keeps_*` tests about user callees and the stamped call
//! with a continuation fail; with the name conjunct dropped (the stamp alone),
//! `keeps_the_rows_of_stamped_entries_outside_the_panic_family` fails.

use trust_types::{
    BasicBlock, BlockId, CalleeKey, ConstValue, DivergingEntry, LocalDecl, Operand, Place,
    SourceSpan, Terminator, Ty, UnwindEdge, VcKind, VerifiableBody, VerifiableFunction,
};

use super::unsupported_mir_vcs;

const U64: Ty = Ty::Int { width: 64, signed: false };

/// `T::LIMIT` in a generic body: the identity-less operand the compiler
/// discloses with a `ConstValue::OpaqueScalar` row.
fn opaque_limit() -> Operand {
    Operand::Constant(ConstValue::opaque_scalar(64, false))
}

/// A key the way `callee_key_for` mints it: `real_sysroot` is the
/// artifact-residency verdict, `entry` the DIVERGE-ENTRY-1 stamp.
fn key(krate: &str, real_sysroot: bool, entry: Option<DivergingEntry>) -> CalleeKey {
    CalleeKey {
        sysroot_item: None,
        krate_is_real_sysroot: real_sysroot,
        krate_name_is_ambiguous: false,
        stable_crate_id: 7,
        krate_name: krate.to_string(),
        foreign_block_leaf: None,
        upstream_foreign_link_symbol: None,
        diverging_entry: entry,
    }
}

fn user_key() -> Option<CalleeKey> {
    Some(key("probe", false, None))
}

fn sysroot_panic_key() -> Option<CalleeKey> {
    Some(key("core", true, Some(DivergingEntry::PanicOrAbort)))
}

/// `fn caller<T: Lim>() -> u64 { <callee>(T::LIMIT) }`. `returns` gives the call
/// a normal-return target (`bb1: return`); otherwise it is a diverging call.
fn caller(callee: &str, callee_key: Option<CalleeKey>, returns: bool) -> VerifiableFunction {
    let mut blocks = vec![BasicBlock {
        id: BlockId(0),
        stmts: vec![],
        terminator: Terminator::Call {
            func: callee.into(),
            args: vec![opaque_limit()],
            dest: Place::local(0),
            target: returns.then_some(BlockId(1)),
            span: SourceSpan::default(),
            atomic: None,
            is_foreign: false,
            is_unsafe_sig: false,
            callee_identity: None,
            callee_key,
            unwind: UnwindEdge::Continue,
        },
    }];
    if returns {
        blocks.push(BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return });
    }
    function(blocks)
}

/// `fn caller<T: Lim>(_x: u64) -> u64 { become <callee>(T::LIMIT) }`.
fn tail_caller(callee: &str, callee_key: Option<CalleeKey>) -> VerifiableFunction {
    function(vec![BasicBlock {
        id: BlockId(0),
        stmts: vec![],
        terminator: Terminator::TailCall {
            func: callee.into(),
            args: vec![opaque_limit()],
            span: SourceSpan::default(),
            atomic: None,
            is_foreign: false,
            is_unsafe_sig: false,
            callee_identity: None,
            callee_key,
        },
    }])
}

fn function(blocks: Vec<BasicBlock>) -> VerifiableFunction {
    VerifiableFunction {
        name: "caller".into(),
        def_path: "probe::caller".into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: U64, name: None },
                LocalDecl { index: 1, ty: U64, name: Some("x".into()) },
            ],
            blocks,
            arg_count: 1,
            return_ty: U64,
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
        tuple_layouts: Default::default(),
    }
}

/// Does the body keep the argument's disclosure row?
fn keeps_opaque_argument_row(func: &VerifiableFunction) -> bool {
    unsupported_mir_vcs(func).iter().any(|vc| {
        matches!(
            &vc.kind,
            VcKind::UnsupportedMir { kind, detail }
                if kind == "ConstValue::OpaqueScalar" && detail.contains("args[0]")
        )
    })
}

/// The measured probe: a user `sink::panic` that RETURNS. Its rendering ends in
/// `::panic`, and that alone dropped the row.
#[test]
fn keeps_the_row_of_a_returning_user_fn_named_panic() {
    assert!(keeps_opaque_argument_row(&caller("probe::sink::panic", user_key(), true)));
    // And with no key at all (an indirect call, a frozen dump): no key, no skip.
    assert!(keeps_opaque_argument_row(&caller("probe::sink::panic", None, true)));
}

/// The broader `::panicking::` form: a fn with no `panic` in its own name, in a
/// user module named `panicking`.
#[test]
fn keeps_the_row_of_a_fn_in_a_user_module_named_panicking() {
    assert!(keeps_opaque_argument_row(&caller("probe::panicking::report", user_key(), true)));
    assert!(keeps_opaque_argument_row(&caller("probe::begin_panic_hook", user_key(), true)));
}

/// A DIVERGING user fn named `panic` (`fn panic(_: u64) -> ! { loop {} }`) has
/// no continuation, but nothing stamped it: it is not the sysroot's entry.
#[test]
fn keeps_the_row_of_a_diverging_user_fn_named_panic() {
    assert!(keeps_opaque_argument_row(&caller("probe::div::panic", user_key(), false)));
    assert!(keeps_opaque_argument_row(&caller("probe::div::panic", None, false)));
    // A stamp on a key whose crate is NOT a real sysroot crate is never read
    // (`opt_diverging_entry` requires residency; the extractor never mints it).
    let forged = Some(key("core", false, Some(DivergingEntry::PanicOrAbort)));
    assert!(keeps_opaque_argument_row(&caller("core::panicking::panic", forged, false)));
}

/// A `become` to a user fn named `panic` keeps the row: the tail-call arm reads
/// the same stamp.
#[test]
fn keeps_the_row_of_a_tail_call_to_a_user_fn_named_panic() {
    assert!(keeps_opaque_argument_row(&tail_caller("probe::sink::panic", user_key())));
    assert!(keeps_opaque_argument_row(&tail_caller("probe::sink::panic", None)));
}

/// A stamped sysroot entry that the call can RETURN from is not a site the
/// bridge charges as must-be-unreachable (its diverging-site arm requires no
/// target), so its arguments are proof input like any other call's.
#[test]
fn keeps_the_row_of_a_stamped_call_with_a_continuation() {
    assert!(keeps_opaque_argument_row(&caller(
        "std::panicking::set_hook",
        Some(key("std", true, Some(DivergingEntry::PanicOrAbort))),
        true,
    )));
}

/// The name stays a NARROWING conjunct: a stamped R177 terminal or UB entry
/// that `is_panic_intrinsic_call` never matched keeps its argument rows, as it
/// did before the anchor (DECISION_QUEUE PANIC-SKIP-ANCHOR-1).
#[test]
fn keeps_the_rows_of_stamped_entries_outside_the_panic_family() {
    assert!(keeps_opaque_argument_row(&caller(
        "core::option::expect_failed",
        sysroot_panic_key(),
        false
    )));
    assert!(keeps_opaque_argument_row(&caller(
        "core::hint::unreachable_unchecked",
        Some(key("core", true, Some(DivergingEntry::UbIfReached))),
        false,
    )));
}

/// The REAL site keeps its skip: the sysroot's own panic entry, stamped, with no
/// continuation — the shape every `assert!`/`panic!` lowers to. Without this,
/// every such site with an unrepresentable message would be wedged at Unknown.
#[test]
fn skips_the_arguments_of_a_stamped_sysroot_panic_entry() {
    for callee in [
        "core::panicking::panic",
        "core::panicking::panic_fmt",
        "std::panicking::begin_panic::<u64>",
        "core::panicking::panic_bounds_check",
    ] {
        assert!(
            !keeps_opaque_argument_row(&caller(callee, sysroot_panic_key(), false)),
            "{callee}: a real panic site's arguments are read by no proof"
        );
    }
    assert!(!keeps_opaque_argument_row(&tail_caller(
        "core::panicking::panic",
        sysroot_panic_key()
    )));
}
