//! DIVERGE-ANCHOR-1: the bridge's diverging-site arm takes its must-be-unreachable
//! encoding only for a callee DEFINED in a real sysroot crate.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0
//!
//! The arm (`lower.rs`, `Terminator::Call` with `target: None`) used to key on the
//! callee's rendered NAME alone (`is_panic_call`, `is_ub_if_reached_call`,
//! `is_diverging_panic_or_abort_terminal`). Its encoding (`Assert(false)` under the
//! path condition, a `PanicFreedom` row, then `Unreachable`) REPLACES the
//! absent-callee may-panic marker the ordinary call arms mint, and the two are not
//! equally strict: under the default policy the site row is `runtime_checked` and
//! accepted while the absent-callee row is refused. A verify-off dependency's
//! `pub mod panicking { pub fn anything(p: *mut u32) -> ! { *p = 1; exit(0) } }`
//! was therefore accepted where the same body named `boom` was refused (measured on
//! the stage 1 of `38e6c69b1c`). The arm then also required
//! `CalleeKey::opt_is_real_sysroot`.
//!
//! DIVERGE-ENTRY-1: residency was not enough. A call to a core TRAIT method is keyed
//! on the trait's DefId (`core`, real sysroot) while a dependency's impl runs, and its
//! rendering carries the user's `Self` (`<dep::panicking::V as
//! core::convert::From<*mut u32>>::from`), so a verify-off dependency's segfaulting
//! `impl From<*mut u32> for panicking::V` was accepted under default on the stage 1 of
//! `4463aeeb6d`. The arm now requires the extractor's `diverging_entry` stamp
//! (`CalleeKey::opt_diverging_entry`): a real sysroot crate, not a trait item, and
//! the name predicates on the GENERIC-FREE definition path. The KEY's stamp, not the
//! rendered name and not residency alone, decides.
//!
//! The key helpers below are shared with the older diverging-site fixtures, which
//! now carry the key the extractor mints for a real `core`/`alloc`/`std` entry.

use trust_ir::ObligationKind;
use trust_ir::inst::Inst;
use trust_types::{
    BasicBlock as TrustBlock, BlockId, CalleeKey, DivergingEntry, LocalDecl, Place, SourceSpan,
    Terminator, Ty, UnwindEdge, VerifiableBody, VerifiableFunction,
};

use crate::lower::lower_to_trust_ir;

/// The key the extractor (`callee_key_for`) mints for a callee DEFINED in the real
/// sysroot crate `krate` that is NOT a diverging entry: `krate_is_real_sysroot` is the
/// artifact-residency verdict, and there is no `diverging_entry` stamp. This is the
/// key a call to a core TRAIT method carries (`From::from`, `Default::default`,
/// `Into::into`), whatever impl runs.
pub(crate) fn sysroot_callee_key(krate: &str) -> CalleeKey {
    CalleeKey {
        sysroot_item: None,
        krate_is_real_sysroot: true,
        krate_name_is_ambiguous: false,
        stable_crate_id: 0x5157_7200,
        krate_name: krate.to_string(),
        foreign_block_leaf: None,
        upstream_foreign_link_symbol: None,
        diverging_entry: None,
    }
}

/// The key the extractor mints for one of the sysroot's OWN panic, abort or UB
/// entry points in `krate` (`diverging_entry_of`: a real sysroot crate, not a trait
/// item, the generic-free definition path): the stamp the diverging-site arm reads.
pub(crate) fn diverging_entry_callee_key(krate: &str, entry: DivergingEntry) -> CalleeKey {
    CalleeKey { diverging_entry: Some(entry), ..sysroot_callee_key(krate) }
}

/// The stamped key for a real sysroot entry spelled `callee`: the UB class for the
/// `unreachable_unchecked` / `intrinsics::unreachable` family, the panic class for
/// everything else, as `diverging_entry_of` classifies them.
pub(crate) fn entry_key_for(krate: &str, callee: &str) -> CalleeKey {
    let entry = if callee.ends_with("::unreachable_unchecked")
        || callee.ends_with("::intrinsics::unreachable")
    {
        DivergingEntry::UbIfReached
    } else {
        DivergingEntry::PanicOrAbort
    };
    diverging_entry_callee_key(krate, entry)
}

/// The key the extractor mints for a callee defined in a crate that is NOT a real
/// sysroot crate, whatever it is named (`--crate-name core` included).
pub(crate) fn non_sysroot_callee_key(krate: &str) -> CalleeKey {
    CalleeKey {
        sysroot_item: None,
        krate_is_real_sysroot: false,
        krate_name_is_ambiguous: false,
        stable_crate_id: 0xdee9_0000,
        krate_name: krate.to_string(),
        foreign_block_leaf: None,
        upstream_foreign_link_symbol: None,
        diverging_entry: None,
    }
}

/// `fn site() { callee() }` where `callee: fn(..) -> !`: one block, a `Call` with no
/// normal-return target into a `!`-typed destination, the shape the extractor emits
/// for a direct never-typed callee (`direct_callee_returns_never`).
fn diverging_site(callee: &str, callee_key: Option<CalleeKey>) -> VerifiableFunction {
    VerifiableFunction {
        name: "site".into(),
        def_path: "test::site".into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl { index: 1, ty: Ty::Never, name: None },
            ],
            blocks: vec![TrustBlock {
                id: BlockId(0),
                stmts: vec![],
                terminator: Terminator::Call {
                    func: callee.to_string(),
                    args: vec![],
                    dest: Place::local(1),
                    target: None,
                    span: SourceSpan::default(),
                    atomic: None,
                    is_foreign: false,
                    is_unsafe_sig: false,
                    unwind: UnwindEdge::Unreachable,
                    callee_identity: None,
                    callee_key,
                },
            }],
            arg_count: 0,
            return_ty: Ty::Unit,
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
        tuple_layouts: Default::default(),
    }
}

/// The names of the measured lie: every leg of the arm (the panic family, an R177
/// terminal, the UB family), each spelled as a dependency's own item.
const DEPENDENCY_SPELLINGS: &[&str] = &[
    "dep::panicking::anything",
    "dep::panic_nounwind",
    "dep::unwrap_failed",
    "dep::process::abort",
    "dep::raw_vec::handle_error",
    "dep::thread::local::panic_access_error",
    "dep::intrinsics::unreachable",
    "dep::hint::unreachable_unchecked",
];

fn site_charge_descriptions(callee: &str, key: Option<CalleeKey>) -> Vec<String> {
    let module = lower_to_trust_ir(&diverging_site(callee, key))
        .unwrap_or_else(|e| panic!("`{callee}` must lower: {e:?}"));
    module
        .proof_obligations
        .iter()
        .filter(|o| {
            o.description.contains("must be unreachable")
                || o.description.contains("must be proven unreachable")
        })
        .map(|o| o.description.clone())
        .collect()
}

fn absent_callee_rows(callee: &str, key: Option<CalleeKey>) -> usize {
    let module = lower_to_trust_ir(&diverging_site(callee, key))
        .unwrap_or_else(|e| panic!("`{callee}` must lower: {e:?}"));
    module
        .proof_obligations
        .iter()
        .filter(|o| {
            o.kind == ObligationKind::PanicFreedom
                && o.description
                    .starts_with(trust_types::assumption::ABSENT_CALLEE_ASSUMPTION_PREFIX)
                && o.description.contains(callee)
        })
        .count()
}

/// The lie, at the bridge seam: with NO key, a NON-sysroot key, or a key for a crate
/// that merely calls itself `core`, the name never selects the site encoding. The
/// call goes to the ordinary arms and keeps its absent-callee may-panic row, exactly
/// as `dep::boom` does. Before DIVERGE-ANCHOR-1 every one of these minted
/// `panic call … must be unreachable` (or the UB wording) and no absent-callee row.
#[test]
fn a_non_sysroot_diverging_name_keeps_the_absent_callee_row() {
    for callee in DEPENDENCY_SPELLINGS.iter().copied().chain(["core::panicking::panic"]) {
        for key in [None, Some(non_sysroot_callee_key("dep")), Some(non_sysroot_callee_key("core"))]
        {
            let charges = site_charge_descriptions(callee, key.clone());
            assert!(
                charges.is_empty(),
                "`{callee}` with key {key:?} took the site encoding: {charges:?}"
            );
            assert_eq!(
                absent_callee_rows(callee, key.clone()),
                1,
                "`{callee}` with key {key:?} must keep exactly one absent-callee row"
            );
        }
    }
}

/// The control the measurement used: `dep::boom` takes the absent-callee row with
/// or without a key, before and after.
#[test]
fn the_unrecognized_name_control_is_unchanged() {
    for key in [
        None,
        Some(non_sysroot_callee_key("dep")),
        Some(sysroot_callee_key("core")),
        // The rendered-name conjunct can only narrow: a stamp the extractor would
        // never mint on this name still does not select the encoding.
        Some(diverging_entry_callee_key("core", DivergingEntry::PanicOrAbort)),
    ] {
        assert!(site_charge_descriptions("dep::boom", key.clone()).is_empty());
        assert_eq!(absent_callee_rows("dep::boom", key), 1);
    }
}

/// DIVERGE-ENTRY-1, the lie at the bridge seam: a call to a core TRAIT method is
/// keyed `core`, real sysroot, with NO `diverging_entry` stamp, while a verify-off
/// dependency's impl runs; its rendering carries the user's `Self`, which spells a
/// panic module. On `integ/wave13` before this fix (residency alone) each of these
/// minted `panic call … must be unreachable` and no absent-callee row, and the
/// compiler accepted the `From`, `Default` and `Into` victims under default. Without
/// the stamp NO name takes the encoding, `core::panicking::panic` included, and a
/// stamp on a key that is not a real sysroot key (never minted) does not either.
#[test]
fn a_sysroot_key_without_the_entry_stamp_keeps_the_absent_callee_row() {
    for callee in [
        "<dep::panicking::V as core::convert::From<*mut u32>>::from",
        "<dep::panicking::V as core::default::Default>::default",
        "<*mut u32 as core::convert::Into<dep::panicking::V>>::into",
        "core::array::from_fn::<dep::panicking::V, 1, fn(usize) -> dep::panicking::V>",
        "<dep::unwrap_failed as core::default::Default>::default",
        "core::panicking::panic",
        "core::hint::unreachable_unchecked",
    ] {
        for key in [
            Some(sysroot_callee_key("core")),
            Some(sysroot_callee_key("alloc")),
            Some(CalleeKey {
                diverging_entry: Some(DivergingEntry::PanicOrAbort),
                ..non_sysroot_callee_key("core")
            }),
        ] {
            let charges = site_charge_descriptions(callee, key.clone());
            assert!(
                charges.is_empty(),
                "`{callee}` with key {key:?} took the site encoding: {charges:?}"
            );
            assert_eq!(
                absent_callee_rows(callee, key.clone()),
                1,
                "`{callee}` with key {key:?} must keep exactly one absent-callee row"
            );
        }
    }
}

/// The stamp decides, not the name: with the key the extractor mints for a real
/// sysroot entry (`diverging_entry` stamped), the site encoding stays
/// (`Assert(false)` + `NoPanic`, then `Unreachable`) and no absent-callee row is
/// minted. This is what every real `core::panicking::*` site gets. The wording is the
/// stamp's: the UB class reads as undefined behavior, the panic class as a panic.
#[test]
fn a_stamped_sysroot_key_keeps_the_site_encoding() {
    for callee in DEPENDENCY_SPELLINGS.iter().copied().chain([
        "core::panicking::panic",
        "core::panicking::panic_fmt",
        "core::option::unwrap_failed",
        "alloc::raw_vec::handle_error",
        "core::hint::unreachable_unchecked",
    ]) {
        let key = Some(entry_key_for("core", callee));
        let charges = site_charge_descriptions(callee, key.clone());
        assert_eq!(charges.len(), 1, "`{callee}` with a stamped sysroot key: {charges:?}");
        assert!(charges[0].contains(callee), "{charges:?}");
        let ub = callee.ends_with("unreachable_unchecked")
            || callee.ends_with("intrinsics::unreachable");
        assert_eq!(charges[0].contains("undefined behavior"), ub, "{charges:?}");
        assert_eq!(absent_callee_rows(callee, key.clone()), 0, "`{callee}`");
        let module = lower_to_trust_ir(&diverging_site(callee, key)).expect("lowers");
        let body = &module.functions[0].blocks[0].body;
        assert!(
            body.iter().any(|n| matches!(n.inst, Inst::Assert { .. })
                && n.proofs.contains(&trust_ir::ProofAnnotation::NoPanic)),
            "`{callee}`: the site must be asserted unreachable"
        );
        assert!(
            matches!(body.last().map(|n| &n.inst), Some(Inst::Unreachable)),
            "`{callee}`: control must not continue past the site"
        );
    }
}
