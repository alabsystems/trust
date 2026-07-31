//! trust-types: Verification IR for the Trust compiler
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

// Trust: Allow unused crate deps when compiled in compiler context
// (serde_json used by downstream, thiserror reserved for error types)
// Trust: Allow std HashMap/HashSet — FxHash lint only applies to compiler internals
#![allow(rustc::default_hash_types, rustc::potential_query_instability)]
// Trust: `?` that propagates FAIL-CLOSED (see `discharge`) needs the custom-`Try`
// feature. This is the mechanistic kernel that turns the soundness-bug class —
// "an unmodeled construct silently defaults to PROVED" — into a structural
// impossibility: a dropped/`?`'d obligation can no longer mean "safe".
//
// Gated behind the default-on `try-sugar` feature so the nightly requirement is
// opt-out: stable-only consumers depend with `default-features = false` and keep
// the full `Discharge` API minus the `?` operator (see `discharge`).
#![cfg_attr(feature = "try-sugar", feature(try_trait_v2, try_trait_v2_residual))]
// dead_code audit: crate-level suppression removed

// Deterministic hash collections for compilation reproducibility.
pub mod fx;

/// Prefix stamped onto a direct call path only after rustc's `TyCtxt` confirms
/// that the callee is one of Trust's modeled compiler intrinsics.
///
/// `@` cannot occur in a Rust identifier, so authored source cannot manufacture
/// this namespace merely by declaring a lookalike `intrinsics::ctpop` function.
/// Consumers must still validate the exact intrinsic name and call shape after
/// removing the prefix. The marker prevents source-spellable DefPath collisions
/// during compiler extraction, but is forgeable in hand-edited serialized IR;
/// artifact authority still comes from the authenticated compiler transport and
/// session that produced the IR.
pub const TRUST_RUSTC_INTRINSIC_PATH_PREFIX: &str = "@trust-rustc-intrinsic::";

/// Prefix stamped onto a direct call path only after rustc's `TyCtxt` confirms
/// that the callee is one of Trust's modeled total primitive methods.
///
/// This namespace is intentionally distinct from
/// [`TRUST_RUSTC_INTRINSIC_PATH_PREFIX`]: `wrapping_add`/`wrapping_sub`/
/// `wrapping_mul` are `core` library methods, not rustc intrinsics. As with the
/// intrinsic marker, `@` makes the prefix impossible to author as a Rust
/// identifier, while artifact authority still comes from the authenticated
/// compiler transport/session rather than from a serialized string alone.
pub const TRUST_RUSTC_TOTAL_PRIMITIVE_METHOD_PATH_PREFIX: &str =
    "@trust-rustc-total-primitive-method::";

/// Prefix stamped onto an integer wrapping call whose exact `core` method
/// identity is needed only by the full-mode assertion-refutation model.
///
/// This is deliberately separate from
/// [`TRUST_RUSTC_TOTAL_PRIMITIVE_METHOD_PATH_PREFIX`]. The E6 import lane admits
/// only unsigned `u8`/`u16`/`u32`/`u64` add/sub/mul, while the refutation-only
/// model also understands signed and pointer-sized add/sub. A refutation model
/// must not recover that broader identity from a source-spellable method suffix:
/// otherwise a user function merely named `wrapping_add` could be modeled as
/// modular arithmetic and manufacture a false counterexample.
pub const TRUST_RUSTC_WRAPPING_REFUTATION_METHOD_PATH_PREFIX: &str =
    "@trust-rustc-wrapping-refutation-method::";

/// The integer carrier authenticated for a refutation-only wrapping method.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RustcWrappingRefutationCarrier {
    Fixed { width: u32, signed: bool },
    PointerSized { signed: bool },
}

impl RustcWrappingRefutationCarrier {
    /// Whether the extracted operand width/sign agrees with this carrier.
    ///
    /// Pointer-sized integers are currently pinned to the 64-bit Trust target.
    /// Checking that width here is essential: signedness alone would let a
    /// forged pointer-sized marker authorize modular semantics for (for
    /// example) an unrelated `u8` call in serialized IR.
    #[must_use]
    pub fn matches(self, width: u32, signed: bool) -> bool {
        match self {
            Self::Fixed { width: expected, signed: expected_signed } => {
                width == expected && signed == expected_signed
            }
            Self::PointerSized { signed: expected_signed } => {
                width == 64 && signed == expected_signed
            }
        }
    }
}

/// The refutation-only wrapping operation authenticated by rustc.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RustcWrappingRefutationOp {
    Add,
    Sub,
}

/// An exact compiler-authenticated `core` integer wrapping add/sub method.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct RustcWrappingRefutationMethod {
    pub op: RustcWrappingRefutationOp,
    pub carrier: RustcWrappingRefutationCarrier,
}

impl RustcWrappingRefutationMethod {
    /// Classify a closed refutation-only method marker.
    ///
    /// Fixed signed/unsigned carriers through 128 bits and pointer-sized
    /// carriers have exact spellings. The downstream arithmetic model retains
    /// its own width cap and fails closed outside it.
    #[must_use]
    pub fn classify(callee: &str) -> Option<Self> {
        let path = callee.strip_prefix(TRUST_RUSTC_WRAPPING_REFUTATION_METHOD_PATH_PREFIX)?;
        let mut segments = path.split("::");
        let (Some(root), Some(module), Some(primitive_impl), Some(method)) =
            (segments.next(), segments.next(), segments.next(), segments.next())
        else {
            return None;
        };
        if segments.next().is_some() || root != "core" || module != "num" {
            return None;
        }
        let carrier = match primitive_impl {
            "<impl u8>" => RustcWrappingRefutationCarrier::Fixed { width: 8, signed: false },
            "<impl u16>" => RustcWrappingRefutationCarrier::Fixed { width: 16, signed: false },
            "<impl u32>" => RustcWrappingRefutationCarrier::Fixed { width: 32, signed: false },
            "<impl u64>" => RustcWrappingRefutationCarrier::Fixed { width: 64, signed: false },
            "<impl u128>" => RustcWrappingRefutationCarrier::Fixed { width: 128, signed: false },
            "<impl usize>" => RustcWrappingRefutationCarrier::PointerSized { signed: false },
            "<impl i8>" => RustcWrappingRefutationCarrier::Fixed { width: 8, signed: true },
            "<impl i16>" => RustcWrappingRefutationCarrier::Fixed { width: 16, signed: true },
            "<impl i32>" => RustcWrappingRefutationCarrier::Fixed { width: 32, signed: true },
            "<impl i64>" => RustcWrappingRefutationCarrier::Fixed { width: 64, signed: true },
            "<impl i128>" => RustcWrappingRefutationCarrier::Fixed { width: 128, signed: true },
            "<impl isize>" => RustcWrappingRefutationCarrier::PointerSized { signed: true },
            _ => return None,
        };
        let op = match method {
            "wrapping_add" => RustcWrappingRefutationOp::Add,
            "wrapping_sub" => RustcWrappingRefutationOp::Sub,
            _ => return None,
        };
        Some(Self { op, carrier })
    }
}

/// A compiler-authenticated, pure-total primitive method admitted without a
/// same-unit body.
///
/// Classification is deliberately strict even though the marker itself can
/// only be minted by the compiler in an authoritative run. Keeping the grammar
/// here gives facet inference, E6 body recognition, and TrustIr lowering one
/// fail-closed source of truth.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RustcTotalPrimitiveMethod {
    WrappingAdd(u32),
    WrappingSub(u32),
    WrappingMul(u32),
}

impl RustcTotalPrimitiveMethod {
    /// Classify an exact compiler-marked `core` primitive method path.
    ///
    /// Only the E6 machine widths are admitted. Signed integers, `u128`,
    /// `usize`, foreign roots, extra path segments, unmarked paths, and
    /// same-suffix lookalikes all decline.
    #[must_use]
    pub fn classify(callee: &str) -> Option<Self> {
        let path = callee.strip_prefix(TRUST_RUSTC_TOTAL_PRIMITIVE_METHOD_PATH_PREFIX)?;
        let mut segments = path.split("::");
        let (Some(root), Some(module), Some(primitive_impl), Some(method)) =
            (segments.next(), segments.next(), segments.next(), segments.next())
        else {
            return None;
        };
        if segments.next().is_some() || root != "core" || module != "num" {
            return None;
        }
        let width = match primitive_impl {
            "<impl u8>" => 8,
            "<impl u16>" => 16,
            "<impl u32>" => 32,
            "<impl u64>" => 64,
            _ => return None,
        };
        match method {
            "wrapping_add" => Some(Self::WrappingAdd(width)),
            "wrapping_sub" => Some(Self::WrappingSub(width)),
            "wrapping_mul" => Some(Self::WrappingMul(width)),
            _ => None,
        }
    }

    #[must_use]
    pub fn width(self) -> u32 {
        match self {
            Self::WrappingAdd(width) | Self::WrappingSub(width) | Self::WrappingMul(width) => width,
        }
    }
}

#[cfg(test)]
mod rustc_total_primitive_method_tests {
    use super::*;

    #[test]
    fn wrapping_refutation_method_classifier_is_exact_and_fail_closed() {
        assert!(
            RustcWrappingRefutationCarrier::PointerSized { signed: false }.matches(64, false)
        );
        assert!(
            !RustcWrappingRefutationCarrier::PointerSized { signed: false }.matches(8, false),
            "pointer-sized identity must validate the pinned target width as well as signedness"
        );

        for (path, op, carrier) in [
            (
                "@trust-rustc-wrapping-refutation-method::core::num::<impl u128>::wrapping_add",
                RustcWrappingRefutationOp::Add,
                RustcWrappingRefutationCarrier::Fixed { width: 128, signed: false },
            ),
            (
                "@trust-rustc-wrapping-refutation-method::core::num::<impl i32>::wrapping_sub",
                RustcWrappingRefutationOp::Sub,
                RustcWrappingRefutationCarrier::Fixed { width: 32, signed: true },
            ),
            (
                "@trust-rustc-wrapping-refutation-method::core::num::<impl usize>::wrapping_add",
                RustcWrappingRefutationOp::Add,
                RustcWrappingRefutationCarrier::PointerSized { signed: false },
            ),
            (
                "@trust-rustc-wrapping-refutation-method::core::num::<impl isize>::wrapping_sub",
                RustcWrappingRefutationOp::Sub,
                RustcWrappingRefutationCarrier::PointerSized { signed: true },
            ),
        ] {
            assert_eq!(
                RustcWrappingRefutationMethod::classify(path),
                Some(RustcWrappingRefutationMethod { op, carrier })
            );
        }

        for path in [
            "core::num::<impl i32>::wrapping_add",
            "@trust-rustc-wrapping-refutation-method::core::num::<impl f32>::wrapping_add",
            "@trust-rustc-wrapping-refutation-method::core::num::<impl i32>::wrapping_mul",
            "@trust-rustc-wrapping-refutation-method::core::num::<impl i32>::wrapping_add::suffix",
            "@trust-rustc-wrapping-refutation-method::evil::num::<impl i32>::wrapping_add",
            "@trust-rustc-total-primitive-method::core::num::<impl i32>::wrapping_add",
        ] {
            assert_eq!(RustcWrappingRefutationMethod::classify(path), None, "{path}");
        }
    }

    #[test]
    fn total_primitive_method_classifier_is_exact_and_fail_closed() {
        for (path, expected) in [
            (
                "@trust-rustc-total-primitive-method::core::num::<impl u8>::wrapping_add",
                RustcTotalPrimitiveMethod::WrappingAdd(8),
            ),
            (
                "@trust-rustc-total-primitive-method::core::num::<impl u16>::wrapping_sub",
                RustcTotalPrimitiveMethod::WrappingSub(16),
            ),
            (
                "@trust-rustc-total-primitive-method::core::num::<impl u32>::wrapping_mul",
                RustcTotalPrimitiveMethod::WrappingMul(32),
            ),
            (
                "@trust-rustc-total-primitive-method::core::num::<impl u64>::wrapping_add",
                RustcTotalPrimitiveMethod::WrappingAdd(64),
            ),
        ] {
            assert_eq!(RustcTotalPrimitiveMethod::classify(path), Some(expected));
        }

        for bad in [
            "core::num::<impl u64>::wrapping_add",
            "@trust-rustc-intrinsic::core::num::<impl u64>::wrapping_add",
            "@trust-rustc-total-primitive-method::std::num::<impl u64>::wrapping_add",
            "@trust-rustc-total-primitive-method::evil::core::num::<impl u64>::wrapping_add",
            "@trust-rustc-total-primitive-method::core::num::<impl i64>::wrapping_add",
            "@trust-rustc-total-primitive-method::core::num::<impl u128>::wrapping_add",
            "@trust-rustc-total-primitive-method::core::num::<impl usize>::wrapping_add",
            "@trust-rustc-total-primitive-method::core::num::<impl u64>::wrapping_add_signed",
            "@trust-rustc-total-primitive-method::core::num::<impl u64>::saturating_add",
            "@trust-rustc-total-primitive-method::core::num::<impl u64>::wrapping_add::suffix",
            "@trust-rustc-total-primitive-method::core::num::wrapping_add",
            "@trust-rustc-total-primitive-method::core::num::<impl u64>",
            "@trust-rustc-total-primitive-method::",
        ] {
            assert_eq!(
                RustcTotalPrimitiveMethod::classify(bad),
                None,
                "malformed or excluded marker must decline: {bad}"
            );
        }
    }
}

/// Marks a loop contract that could not be paired to a MIR loop header.
///
/// This is a semantic signal carried inside the contract BODY, matched with
/// `starts_with` by the consumers that must not treat an unpaired contract as
/// a real obligation. It lives here because producer (trust-vcgen) and
/// consumers (trust-mir-extract, trust-vcgen::termination) are separate crates:
/// while each held its own copy, a one-character drift in either would have
/// silently reclassified unpaired contracts as ordinary ones, and nothing would
/// have failed.
pub const UNPAIRED_LOOP_CONTRACT_PREFIX: &str = "__trust_unpaired_loop_contract__:";

/// The single process-global serialization point for every in-process ay solve.
///
/// ay's direct-execution path carries shared, non-reentrant state (see
/// trust-router's `in_process_ay_backend`): concurrent solves can race and yield
/// NONDETERMINISTIC verdicts — a false-`Certified` risk. Every ay solve entry
/// point (trust-router's `InProcessAyBackend` and trust-certify's
/// `AyProofBackend`) MUST hold this lock ACROSS THE RAW SOLVE ONLY, and never
/// across pure clean-kernel reconstruction — so that the dominant clean-kernel
/// certification work runs unlocked and parallelizes across verification threads.
/// A plain (non-reentrant) `Mutex` is correct because the narrowed critical
/// sections never nest.
pub fn ay_exec_lock() -> &'static std::sync::Mutex<()> {
    static LOCK: std::sync::Mutex<()> = std::sync::Mutex::new(());
    &LOCK
}

// Fail-closed-by-construction discharge result — the mechanistic prevention for
// the false-proof class (the 2026-06-19 soundness sweep found 8 instances where an
// unmodeled construct silently defaulted to PROVED). See `discharge`.
pub mod discharge;

// String interning for Formula variable names.
mod interner;
pub use interner::{Interner, Symbol};

// pub(crate) mod for modules not accessed via trust_types::module:: paths externally.
// Items from these modules are re-exported via `pub use module::*` below where needed.
pub(crate) mod annotation;
// Bitvector theory types for fixed-width integer operations.
pub(crate) mod bitvector;
pub(crate) mod boundary;
pub mod call_graph;
// MIR atomic intrinsic detection and parsing.
mod atomic_intrinsics;
mod concurrency;
mod facts;
mod formula;
// Arena-allocated formula representation for reduced heap allocation.
pub mod formula_arena;
// formula_utils.rs removed — utilities now in formula/ submodules.
pub(crate) mod generics;
pub(crate) mod lifetime;
pub(crate) mod lifetime_analysis;
mod model;
pub(crate) mod resilience;
// sort_check.rs removed — sort checking now in formula/sort.rs.
// SMT-LIB2 pretty printer for formatted solver output.
pub mod smt_printer;
// Shared matchers for modeled total core/std call summaries (bridge + vcgen must agree).
pub mod admissible_body;
pub mod facet_allowlist;
pub mod facet_inference;
pub mod facet_propagation;
pub mod structural_determinism;
pub mod structural_panic_freedom;
pub mod structural_purity;
pub mod structural_termination;
pub mod total_call_summaries;
// Trust (assumption ledger): shared markers for the compiler↔bridge assumption
// demotion contract (extern print/format/write dispatch, native-lowering gaps).
pub mod assumption;
// Trust (frontend firewall): the enforcement of "an untrusted frontend proposes,
// it never asserts". Lives here for the same reason `assumption` does — it is the
// shared dependency of the frontends that produce proposals, the lanes that admit
// them, and the repair loop that writes clauses back into source.
pub mod frontend_firewall;
// Trust (T9 contract-panic): the SINGLE source of truth that classifies whether a
// non-proved obligation is a DECLARED contract panic (a conditional pass) vs a
// genuine refutation. Every gate — the two compiler abort gates, the memory-safe
// UB counter, the transport-row rewrite, and targo's partition — projects its own
// data into `tolerance::ContractPanicView` and asks this module, so the decision
// cannot drift across the readers (the `ArrayVec::push` regression was exactly
// that drift). Owns the DECISION that reads `assumption`'s marker constants.
pub mod tolerance;
// Trust (R1 corpus): depth-tolerant JSON deserialization for compiler-emitted
// recursive formula payloads (bounded big-stack fallback past serde_json's
// default 128-level recursion limit).
pub mod json_depth;
// Trust (falsification corpus, i128/u128 ICE class): wide-integer-tolerant
// canonical JSON digest material (fast path byte-identical to
// `serde_json::to_value`; out-of-JSON-range i128/u128 become tagged decimal
// strings instead of ICEing the verifier).
pub mod json_digest;
// The one implementation of "what are the bytes of this thing, and what is
// their hash". Two subsystems that hash the same object through different code
// disagree about identity the first time either one changes; the canonical-JSON
// half additionally makes the answer independent of the
// `serde_json/preserve_order` feature, which this repo enables in the root
// workspace and not in `crates/`.
pub mod digest;
// Canonical SMT-LIB2 logic selection, free variable collection, and sort inference.
pub mod smt_logic;
// Ambient per-function verification deadline — lets every synchronous
// preprocessing choke point (extraction, VC gen, spec inference) consult the
// existing per-function budget and fail closed, closing the non-termination
// hole where the cooperative deadline only covered solver dispatch.
pub mod verify_budget;
// SMT-LIB2 string-based pretty printer for debugging and external solver interop.
mod result;
// The §7 multi-axis grade record (two-language design, R-U): the lossless
// successor to the legacy AssuranceLevel ladder.
pub mod grade;
pub mod guidance;
// The single per-obligation outcome vocabulary shared by the compiler
// transport, the report DTOs, and every consumer downstream of them.
pub mod outcome;
pub(crate) mod smtlib2_printer;
pub(crate) mod spec;
pub(crate) mod spec_attrs;
mod spec_parse;
mod spec_render;
// state_machine extraction lives in trust-temporal/extract.rs.
// Types (StateMachine, StateInfo, Transition) live in model.rs.
// Dead state_machine.rs (692 lines) removed — was never in module tree.
pub(crate) mod strengthen;
pub(crate) mod taint;
pub(crate) mod trait_resolution;
pub(crate) mod traits;
// Provenance tracking types for memory model Layer 2.
pub mod provenance;
// Unified memory model for trust-wp/trust-vc cross-function proof composition.
pub mod unified_memory;
// Legacy vulnerability-pattern prototype. The production verifier has its
// own sound VC generation/analysis lanes and nothing calls this heuristic
// scanner; keep its unit tests without compiling duplicate detectors into all
// downstream Trust crates.
#[cfg(test)]
mod patterns;
// Shared utility functions consolidated from multiple crates.
pub(crate) mod utils;
// Translation validation shared types (used by trust_vcgen and trust-transval).
pub mod translation_validation;
// ay_bindings conversion bridge for direct ay integration.
#[cfg(feature = "ay-bridge")]
pub mod ay_bridge;
// trust-wp-core PureExpr conversion bridge for native trust_wp integration.
#[cfg(feature = "trust-wp-bridge")]
pub mod trust_wp_bridge;
// serde-only lowering from `trust_types::Formula` into the
// `trust_wp.trust-formula.v1` claim envelope. Always compiled (no trust_wp_core
// dependency) so the trust-wp bridge and compiler can lower symbolic
// `trust-types.Formula@1` predicates into replayable typed pure-expr claims.
pub mod trust_formula_v1;

#[cfg(any(test, feature = "test-utils"))]
pub mod test_utils;

pub use annotation::*;
pub use atomic_intrinsics::parse_atomic_intrinsic;
pub use bitvector::*;
pub use boundary::*;
pub use concurrency::*;
pub use digest::{
    canonical_json_bytes, canonical_json_sha256, canonical_json_value,
    canonicalize_json_in_place, is_canonical_json, is_stable_sha256_hex, lowercase_hex,
    stable_sha256_hex, stable_sha256_hex_parts, stable_sha256_hex_reader,
};
pub use facts::*;
pub use formula::*;
pub use generics::*;
pub use guidance::{AgenticGuidance, SuggestedFix};
pub use json_digest::canonical_digest_json_value;
pub use lifetime::*;
pub use lifetime_analysis::*;
pub use model::*;
pub use outcome::{Outcome, UnknownOutcome};
pub use resilience::*;
pub use result::*;
// Re-export canonical SMT-LIB2 utilities.
pub use smt_logic::{
    FormulaSortError, check_formula_sort, collect_free_var_decls, infer_sort, select_logic,
};
pub use smt_printer::{PrintConfig, SmtPrinter};
pub use smtlib2_printer::{
    SmtLib2Config, SmtLib2Printer, escape_smt_string, is_valid_smt_identifier, operator_to_smt,
    sort_to_smt,
};
pub use spec::*;
pub use spec_attrs::*;
pub use spec_parse::*;
pub use spec_render::*;
pub use strengthen::*;
pub use taint::*;
pub use trait_resolution::*;
pub use traits::*;
// Re-export translation validation types at crate root.
pub use translation_validation::{
    CheckKind, RefinementVc, RefinementVcToVc, SimulationRelation, TranslationCheck,
    TranslationValidationError, block_successors_list, detect_back_edges, infer_identity_relation,
};
pub use utils::{operand_place, strip_generics};
