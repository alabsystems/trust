// trust-types/formula/vc_kind: Verification condition kind classification
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use serde::{Deserialize, Deserializer, Serialize, Serializer};

use super::ProofLevel;
use super::temporal::{FairnessConstraint, LivenessProperty};
use crate::Symbol;
use crate::model::{BinOp, Ty};

/// Hardened obligation categories for OS/path, byte/text, error, panic,
/// compatibility, process semantics, unsafe/FFI, and trust-domain boundary checks.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum HardenedVcCategory {
    RawPathApi,
    PathIdentity,
    PermissionChange,
    PermissionCreate,
    PermissionWindow,
    Utf8Reject,
    ByteLoss,
    ErrorDiscard,
    PanicBoundary,
    CompatObservable,
    ProcessSemantics,
    TrustDomain,
    TrustDomainOrder,
    UnsafeOperation,
    FfiBoundary,
    Unknown(Symbol),
}

impl HardenedVcCategory {
    #[must_use]
    pub fn as_tag(self) -> &'static str {
        match self {
            HardenedVcCategory::RawPathApi => "raw_path_api",
            HardenedVcCategory::PathIdentity => "path_identity",
            HardenedVcCategory::PermissionChange => "permission_change",
            HardenedVcCategory::PermissionCreate => "permission_create",
            HardenedVcCategory::PermissionWindow => "permission_window",
            HardenedVcCategory::Utf8Reject => "utf8_reject",
            HardenedVcCategory::ByteLoss => "byte_loss",
            HardenedVcCategory::ErrorDiscard => "error_discard",
            HardenedVcCategory::PanicBoundary => "panic_boundary",
            HardenedVcCategory::CompatObservable => "compat_observable",
            HardenedVcCategory::ProcessSemantics => "process_semantics",
            HardenedVcCategory::TrustDomain => "trust_domain",
            HardenedVcCategory::TrustDomainOrder => "trust_domain_order",
            HardenedVcCategory::UnsafeOperation => "unsafe_operation",
            HardenedVcCategory::FfiBoundary => "ffi_boundary",
            HardenedVcCategory::Unknown(tag) => tag.as_str(),
        }
    }

    #[must_use]
    pub fn from_tag(tag: &str) -> Option<Self> {
        Some(match tag {
            "raw_path_api" => HardenedVcCategory::RawPathApi,
            "path_identity" => HardenedVcCategory::PathIdentity,
            "permission_change" => HardenedVcCategory::PermissionChange,
            "permission_create" => HardenedVcCategory::PermissionCreate,
            "permission_window" => HardenedVcCategory::PermissionWindow,
            "utf8_reject" => HardenedVcCategory::Utf8Reject,
            "byte_loss" => HardenedVcCategory::ByteLoss,
            "error_discard" => HardenedVcCategory::ErrorDiscard,
            "panic_boundary" => HardenedVcCategory::PanicBoundary,
            "compat_observable" => HardenedVcCategory::CompatObservable,
            "process_semantics" => HardenedVcCategory::ProcessSemantics,
            "trust_domain" => HardenedVcCategory::TrustDomain,
            "trust_domain_order" => HardenedVcCategory::TrustDomainOrder,
            "unsafe_operation" => HardenedVcCategory::UnsafeOperation,
            "ffi_boundary" => HardenedVcCategory::FfiBoundary,
            "" => return None,
            other => HardenedVcCategory::unknown_tag(other),
        })
    }

    #[must_use]
    pub fn unknown_tag(tag: &str) -> Self {
        HardenedVcCategory::Unknown(Symbol::intern(tag))
    }

    #[must_use]
    pub fn is_unknown(self) -> bool {
        matches!(self, HardenedVcCategory::Unknown(_))
    }

    /// Whether a constant-`true` violation in this category is a DESIGN
    /// MANDATE: a profile rule the program is told to follow (no raw path API,
    /// no error discarded through `Result::ok`, an explicit process-signal
    /// policy, …), reported and graded `mandated` instead of proved.
    ///
    /// `UnsafeOperation` and `FfiBoundary` are the two L0-safety categories
    /// (`VcKind::proof_level`). Their constant-`true` violation is a vcgen
    /// MODELLING-GAP fail-close, not a rule about the program: an FFI call with no
    /// summary (`trust-vcgen` `ffi_vcgen::unmodeled_ffi_obligation`), a freed
    /// pointer whose provenance is unmodelled, an `[unsafe:unmodeled-call]` or the
    /// `[unsafe] missing SAFETY comment` stand-in minted for every undecided site.
    /// Calling those mandates labelled possible UB as a design choice, let the
    /// default policy's tolerance skip them, and let them stop blocking the
    /// coroutine-contract upgrade and the extern-call demotion (G3 review,
    /// 2026-10-27, docs/DECISION_QUEUE.md G3-MANDATE-L1-ONLY-1). Exhaustive, so a
    /// new category must decide.
    #[must_use]
    pub fn admits_design_mandate(self) -> bool {
        match self {
            HardenedVcCategory::RawPathApi
            | HardenedVcCategory::PathIdentity
            | HardenedVcCategory::PermissionChange
            | HardenedVcCategory::PermissionCreate
            | HardenedVcCategory::PermissionWindow
            | HardenedVcCategory::Utf8Reject
            | HardenedVcCategory::ByteLoss
            | HardenedVcCategory::ErrorDiscard
            | HardenedVcCategory::PanicBoundary
            | HardenedVcCategory::CompatObservable
            | HardenedVcCategory::ProcessSemantics
            | HardenedVcCategory::TrustDomain
            | HardenedVcCategory::TrustDomainOrder
            // An unrecognised profile tag (the `opaque-terminator` boundary, a
            // legacy `hardened::<tag>` row) is an L1 rule like the named ones
            // (`HardenedBoundary { .. }` is L1 in `proof_level`); kept as it was.
            | HardenedVcCategory::Unknown(_) => true,
            HardenedVcCategory::UnsafeOperation | HardenedVcCategory::FfiBoundary => false,
        }
    }
}

impl Serialize for HardenedVcCategory {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        serializer.serialize_str(self.as_tag())
    }
}

impl<'de> Deserialize<'de> for HardenedVcCategory {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        let tag = String::deserialize(deserializer)?;
        Ok(HardenedVcCategory::from_tag(&tag)
            .unwrap_or_else(|| HardenedVcCategory::unknown_tag(&tag)))
    }
}

/// The compile-time check settings that decide whether the GENERATED program
/// still carries a dynamic guard for an obligation.
///
/// [`VcKind::has_runtime_fallback`] used to take a lone `overflow_checks: bool`.
/// That signature structurally CANNOT answer for the unchecked-UB family
/// (`slice::get_unchecked`, `unchecked_{add,sub,mul}`): the guard those keep is
/// `assert_unsafe_precondition!`, which `library/core/src/ub_checks.rs` gates on
/// `intrinsics::ub_checks()` — i.e. on `Session::ub_checks()`
/// (rustc_session/src/session.rs), NOT on `-C overflow-checks`.
///
/// MEASURED, stage2 `trustc 1.99.0-dev (d6a53e72a)`, `--emit=llvm-ir -C
/// opt-level=0`, function `<usize as SliceIndex<[u32]>>::get_unchecked` and
/// `u32::unchecked_add`:
///
/// | flags | `xs[i]` | `a + b` | `get_unchecked(i)` | `unchecked_add(a,b)` |
/// | --- | --- | --- | --- | --- |
/// | `-Coverflow-checks=off -Cdebug-assertions=off` | `panic_bounds_check` | none | **none** | **none** (`add nuw`) |
/// | `-Coverflow-checks=on  -Cdebug-assertions=on`  | `panic_bounds_check` | `panic_const_add_overflow` | `precondition_check` | `precondition_check` |
/// | `-Coverflow-checks=off -Zub-checks=yes`        | `panic_bounds_check` | none | `precondition_check` | `precondition_check` |
///
/// The third row is the decisive one: with `overflow_checks` OFF the unchecked
/// family still has its guard, and `a + b` does not. The two knobs are
/// independent, and the unchecked family answers the OTHER one.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct RuntimeCheckEnv {
    /// `-C overflow-checks` (`Session::overflow_checks()`). Gates the
    /// `Assert(Overflow*)` terminator rustc inserts on CHECKED arithmetic.
    pub overflow_checks: bool,
    /// `Session::ub_checks()` (rustc_session/src/session.rs:894-896; defaults to
    /// `-C debug-assertions`, overridable with `-Z ub-checks`). Gates every
    /// `assert_unsafe_precondition!` in `core`, which is the ONLY guard the
    /// unchecked-UB family ever has.
    pub ub_checks: bool,
}

impl RuntimeCheckEnv {
    /// The full check environment.
    #[must_use]
    pub const fn new(overflow_checks: bool, ub_checks: bool) -> Self {
        Self { overflow_checks, ub_checks }
    }

    /// FAIL-CLOSED adapter for a caller that knows only `overflow_checks`.
    ///
    /// `ub_checks` is assumed OFF — the release configuration, in which every
    /// `assert_unsafe_precondition!` is compiled out. A caller that cannot
    /// establish the real value must not be able to mint the positive claim, so
    /// the unknown knob resolves to "no guard", never to "guard present".
    /// Threading the real `Session::ub_checks()` can only ADD fallbacks, never
    /// remove one, so no consumer of this adapter can be made less safe by a
    /// later migration to [`RuntimeCheckEnv::new`].
    #[must_use]
    pub const fn overflow_checks_only(overflow_checks: bool) -> Self {
        Self { overflow_checks, ub_checks: false }
    }
}

/// The rustc-inserted MIR `Assert` terminator a hardened `PanicBoundary`
/// boundary stands over, and the check environment that terminator's survival
/// depends on.
///
/// A hardened boundary is NOT itself a check — it is a hardening-profile
/// PROOF REQUIREMENT. But the `mir_assert::*` subfamily of the panic-boundary
/// lane is raised over a terminator rustc itself emitted, and that terminator is
/// what the generated program actually executes. This enum names which of the
/// two answers [`VcKind::site_retains_language_check_in`] must give for such a
/// boundary; the boundaries that stand over nothing rustc checks (`unwrap`,
/// `expect`, `std::fs::rename`, `chroot`, …) have no variant here at all and
/// answer `false` there too.
///
/// It says NOTHING about [`VcKind::has_runtime_fallback_in`], which answers
/// `false` for every hardened boundary: the terminator this enum describes is
/// the panic the boundary objects to, so its survival cannot DISCHARGE the
/// obligation. The two questions are kept apart on purpose — see
/// `site_retains_language_check_in`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MirAssertGuard {
    /// rustc emits this `Assert` unconditionally: `panic_bounds_check` for an
    /// index, and the zero-divisor asserts for `/` and `%`. Nothing in the
    /// tracked check environment can remove it, so the answer is `true`.
    Unconditional,
    /// rustc emits this `Assert` only when `-C overflow-checks` is on — the
    /// `Overflow(..)`/`OverflowNeg` family. The answer is `env.overflow_checks`,
    /// which is EXACTLY what the primary `ArithmeticOverflow` / `ShiftOverflow`
    /// / `NegationOverflow` arms answer for the same operation.
    OverflowChecked,
}

/// The exact prefix [`crate::HardenedVcCategory::PanicBoundary`] boundaries
/// carry in their `callee` when the boundary stands over a rustc-inserted MIR
/// `Assert`.
///
/// ONE PRODUCER, tree-wide: `trust_vcgen::hardened`'s assert lane, which mints
/// the field as `format!("mir_assert::{msg:?}")` over an `AssertMessage`. Every
/// other hardened boundary is a CALL_RULE match and carries a real callee path
/// (`std::option::Option::<T>::unwrap`, `std::fs::rename`, …); every
/// RECONSTRUCTED hardened row (targo's `report_vc_kind` legacy and
/// design-mandate branches) fills `callee` from the row's FUNCTION name, never
/// from this marker. So the marker's presence in a typed payload is provenance,
/// not a guess.
const MIR_ASSERT_CALLEE_PREFIX: &str = "mir_assert::";

/// The `{msg:?}` rendering of the [`crate::AssertMessage`] a hardened
/// `PanicBoundary` `callee` stands over, or `None` when the callee is not a
/// `mir_assert::` marker at all.
///
/// ANCHORED: a callee that merely CONTAINS the marker (`wrapper::mir_assert::…`)
/// answers `None`. This is the one place the prefix is spelled, so
/// [`VcKind::site_retains_language_check_in`] and any policy layer that wants to
/// name individual families read the same string.
#[must_use]
pub fn hardened_mir_assert_message(callee: &str) -> Option<&str> {
    callee.strip_prefix(MIR_ASSERT_CALLEE_PREFIX)
}

/// The `callee` a hardened `PanicBoundary` over a MIR `Assert` carries — the
/// one producer `trust_vcgen::hardened` mints it with. The inverse of
/// [`hardened_mir_assert_message`], so the marker is spelled once: here.
#[must_use]
pub fn hardened_mir_assert_callee(msg: &crate::model::AssertMessage) -> String {
    format!("{MIR_ASSERT_CALLEE_PREFIX}{msg:?}")
}

/// Recover the rustc-inserted assert a hardened `PanicBoundary` `callee` stands
/// over, or `None` when it stands over no rustc check at all.
///
/// ANCHORED and EXACT on the `{msg:?}` rendering of [`crate::AssertMessage`], so
/// a callee that merely MENTIONS the marker does not match. The recognized set
/// is deliberately the same five-variant set targo's own
/// `PanicTwinFamily`/`subsume_hardened_panic_twins` models — described there as
/// "the four `mir_assert` panic families the language inserts a runtime check
/// for and that vcgen emits a per-statement sibling for" — so the authority and
/// the subsumption pass cannot drift about which boundaries have a sibling
/// check.
///
/// EVERY OTHER `AssertMessage` ANSWERS `None`, ON PURPOSE:
///
/// * `NullPointerDereference` / `MisalignedPointerDereference` /
///   `InvalidEnumConstruction` — these are `ub_checks`-gated UB asserts, not
///   panics. `None` is the over-reported-`Unknown` direction (a lost recovery,
///   never a false safety claim), it costs nothing (`RuntimeCheckEnv.ub_checks`
///   is `false` in every lane targo can establish), and the hardened lane
///   already skips the trusted-std spans of the first two.
/// * `ResumedAfterReturn` / `ResumedAfterPanic` / `ResumedAfterDrop` — the
///   coroutine resume-state family, which this tree adjudicates through its own
///   authenticated resume contract rather than through a runtime-fallback claim.
/// * `Custom(..)` — an arbitrary message. The text is not evidence that rustc
///   emitted anything.
#[must_use]
pub fn hardened_mir_assert_guard(callee: &str) -> Option<MirAssertGuard> {
    match hardened_mir_assert_message(callee)? {
        // `panic_bounds_check` and the two zero-divisor asserts are emitted by
        // rustc whatever the check settings are — the same reason the primary
        // `IndexOutOfBounds` / `SliceBoundsCheck` / `DivisionByZero` /
        // `RemainderByZero` arms answer an unconditional `true`.
        "BoundsCheck" | "DivisionByZero" | "RemainderByZero" => Some(MirAssertGuard::Unconditional),
        // `OverflowNeg` is checked BEFORE `Overflow(` so the two cannot alias.
        "OverflowNeg" => Some(MirAssertGuard::OverflowChecked),
        // `Overflow(<BinOp>)` for every operation, including `Div`/`Rem`. Those
        // two are in fact emitted unconditionally (they guard `INT_MIN / -1`,
        // which is UB, not a wrap), so answering `env.overflow_checks` for them
        // UNDER-reports when overflow checks are off. That is deliberate: it is
        // the lost-recovery direction, and it keeps this arm byte-for-byte in
        // lock-step with the primary `ArithmeticOverflow { op }` arm, which
        // answers `env.overflow_checks` for every `op` as well. One rule, one
        // answer, no second opinion about Div/Rem.
        rest if rest.starts_with("Overflow(") && rest.ends_with(')') => {
            Some(MirAssertGuard::OverflowChecked)
        }
        _ => None,
    }
}

/// The program point at which a TINV type-invariant obligation is owed
/// (design `docs/design/2026-10-04-type-invariant-tinv.md` §P4): establishment by a
/// constructor, re-establishment before a call that receives a root, at return, on an
/// unwind edge, at a move out, and before a `Drop`.
///
/// FROZEN ORDER, APPEND ONLY. [`TypeInvariantPoint::canonical_byte`] and bincode both
/// encode the declaration index, and both enter certificate identity. Deliberately not
/// `#[non_exhaustive]`: a downstream match must break when a point is added.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum TypeInvariantPoint {
    Establish,
    Call,
    Return,
    Unwind,
    Move,
    Drop,
}

impl TypeInvariantPoint {
    /// The stable wire spelling of the point.
    #[must_use]
    pub const fn as_tag(self) -> &'static str {
        match self {
            Self::Establish => "establish",
            Self::Call => "call",
            Self::Return => "return",
            Self::Unwind => "unwind",
            Self::Move => "move",
            Self::Drop => "drop",
        }
    }

    /// The byte the canonical certificate encoding uses. These values never change.
    #[must_use]
    pub const fn canonical_byte(self) -> u8 {
        match self {
            Self::Establish => 0,
            Self::Call => 1,
            Self::Return => 2,
            Self::Unwind => 3,
            Self::Move => 4,
            Self::Drop => 5,
        }
    }
}

impl std::fmt::Display for TypeInvariantPoint {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(self.as_tag())
    }
}

/// A MIR location of a TINV obligation: a terminator site has
/// `statement_index == statements.len()`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct TypeInvariantSite {
    pub block: usize,
    pub statement_index: usize,
}

impl std::fmt::Display for TypeInvariantSite {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "bb{}[{}]", self.block, self.statement_index)
    }
}

/// What kind of property a VC checks.
///
/// Each variant maps to a specific safety or functional property. The
/// `proof_level()` method classifies VcKinds into `ProofLevel` tiers
/// used by the router for backend selection.
///
/// # Examples
///
/// ```
/// use trust_types::{VcKind, ProofLevel};
///
/// // L0Safety kinds
/// assert_eq!(VcKind::DivisionByZero.proof_level(), ProofLevel::L0Safety);
/// assert_eq!(VcKind::IndexOutOfBounds.proof_level(), ProofLevel::L0Safety);
///
/// // L1Functional kinds
/// assert_eq!(VcKind::Postcondition.proof_level(), ProofLevel::L1Functional);
///
/// // Display shows a human-readable description
/// assert_eq!(format!("{}", VcKind::DivisionByZero), "division by zero");
/// ```
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
pub enum VcKind {
    ArithmeticOverflow {
        op: BinOp,
        operand_tys: (Ty, Ty),
    },
    ShiftOverflow {
        op: BinOp,
        operand_ty: Ty,
        shift_ty: Ty,
    },
    /// `unchecked_{add,sub,mul}` — the SAME out-of-range obligation as
    /// [`VcKind::ArithmeticOverflow`], minted from the UB-on-overflow intrinsics
    /// instead of a checked `BinaryOp`.
    ///
    /// It is a SEPARATE variant for exactly one reason: the two answer
    /// [`VcKind::has_runtime_fallback`] from DIFFERENT knobs.
    /// `AddUnchecked`/`SubUnchecked`/`MulUnchecked` lower to LLVM `add nsw/nuw`
    /// (rustc_codegen_ssa/src/mir/rvalue.rs) — no `Assert`, no branch, nothing
    /// gated on `overflow_checks` at ANY value — so answering `overflow_checks`
    /// (as the shared `ArithmeticOverflow` variant does, correctly, for `a + b`
    /// and `pow`) was a positive safety claim minted from a program with no
    /// guard in it. The only guard these ever have is the `ub_checks`-gated
    /// `assert_unsafe_precondition!` in `library/core/src/num/uint_macros.rs`.
    ///
    /// Fields mirror `ArithmeticOverflow` so the shared arithmetic machinery
    /// (type-range conjoins, structural cross-check, interval discharge) can
    /// treat the two identically wherever the runtime-guard question is not
    /// being asked.
    UncheckedArithmeticOverflow {
        op: BinOp,
        operand_tys: (Ty, Ty),
    },
    DivisionByZero,
    RemainderByZero,
    IndexOutOfBounds,
    SliceBoundsCheck,
    /// `slice::get_unchecked` / `get_unchecked_mut` — the index must be `< len`,
    /// with NO language-inserted bounds check.
    ///
    /// Distinct from [`VcKind::IndexOutOfBounds`], which covers SAFE indexing
    /// (`xs[i]`) and legitimately keeps its `panic_bounds_check` in every
    /// profile. Minting this family as `IndexOutOfBounds` made it inherit that
    /// unconditional `true`, so the sole obligation on an unchecked index — the
    /// separation-engine `index >= len` row, which is also the reason the
    /// always-refuting `[unsafe] missing SAFETY comment` lint is suppressed for
    /// that block — self-reported as monitored while the emitted code held a
    /// bare `getelementptr`.
    UncheckedIndexBounds {
        /// The unchecked accessor (e.g. `core::slice::<impl [T]>::get_unchecked`).
        callee: String,
        /// Human-readable statement of the obligation.
        detail: String,
    },
    Assertion {
        message: String,
    },
    /// An authored `#[invariant(...)]` / `#[trust::invariant(...)]` clause.
    ///
    /// A SPECIFICATION obligation, exactly like its two sibling clauses
    /// (`Requires -> Precondition`, `Ensures -> Postcondition`), and it must
    /// answer [`VcKind::has_runtime_fallback`] the way they do: `false`. Routing
    /// it onto [`VcKind::Assertion`] borrowed that variant's `true`, which is
    /// earned by a rustc-inserted `Assert` terminator / `assert!` panic call —
    /// something an invariant attribute never produces. The attribute is
    /// span-only and is never lowered (trust-mir-extract reads it off
    /// `tcx.hir_attrs` for its span and snippet); MEASURED on stage2, a
    /// `#[trust::invariant(x > 0)] fn inv_fn(x: i32) -> i32 { x }` emits LLVM IR
    /// byte-identical to the unannotated function — `start: ret i32 %x`.
    ///
    /// # NOTHING IN PRODUCTION CONSTRUCTS THIS VARIANT, AND NOTHING SHOULD
    ///
    /// It is retained so the reporting, display and exhaustiveness paths keep
    /// their arms, and as the record of a fixed defect. Both former mint sites
    /// (`trust_vcgen::contracts::check_contracts_with_loop_invariant_feedback`
    /// and `trust_vcgen::spec_parser::generate_spec_vcs`) now emit the
    /// non-refutable `UnsupportedMir`/`SpecUnverifiable` row instead.
    ///
    /// The reason is that this variant was only ever paired with
    /// `formula: Not(predicate)` and NOTHING ELSE — no path condition, no
    /// pre-state, no binding of the clause's free names to program locals,
    /// because an item-position attribute names no program point to bind them
    /// at. The solver was therefore asked `is ¬P unsatisfiable`, i.e. `is P
    /// VALID`, which is a question about the predicate's text rather than about
    /// the program. MEASURED on the sealed toolchain `trust-e26541e3`, over
    /// `fn f(x: u32) -> u32 { x / 2 }`:
    ///
    /// | clause | outcome | solver |
    /// |---|---|---|
    /// | `invariant(1 == 1)` | **proved** | `clean-kernel-certified` |
    /// | `invariant(x == x)` | **proved** | `clean-kernel-certified` |
    /// | `invariant(x >= 0)` | unknown | — |
    /// | `invariant(true)` | unknown | — |
    /// | `invariant(false)` | unknown | — |
    ///
    /// The PROVED set is exactly the set of predicates that constrain nothing,
    /// and because [`VcKind::proof_level`] puts this variant at
    /// [`ProofLevel::L1Functional`] and [`VcKind::kind_str`] labels it
    /// `"invariant"`, each such row is a kernel-certified CONTRACT-KIND proof —
    /// the kind a verification ratchet reports as headline progress. A
    /// one-line `#[trust::invariant(1 == 1)]` could therefore manufacture a
    /// "first invariant proof" that means nothing.
    ///
    /// If a genuinely situated invariant is ever added, it must carry its
    /// program point and its state binding, and it must be a new variant whose
    /// formula is not merely `Not(predicate)`. The loop machinery already does
    /// this correctly via `ContractKind::LoopInvariant`, which is a different
    /// clause kind with a real MIR loop header.
    ContractInvariant {
        /// The clause source text.
        expression: String,
    },
    Precondition {
        callee: String,
    },
    Postcondition,
    CastOverflow {
        from_ty: Ty,
        to_ty: Ty,
    },
    NegationOverflow {
        ty: Ty,
    },
    Unreachable,
    /// TrustIr preserved valid rustc MIR whose precise semantics are not yet
    /// implemented. This must report as unknown/unsupported, never as proved.
    UnsupportedMir {
        kind: String,
        detail: String,
    },
    // State machine properties (ty)
    DeadState {
        state: String,
    },
    Deadlock,
    Temporal {
        property: String,
        /// Optional state-machine model the temporal backend (`ty`) checks the
        /// property against. When present, `TyBackend::extract_state_machine`
        /// converts it to a `trust_temporal::StateMachine` and model-checks the
        /// property; when absent, the VC stays fail-closed (no machine to check).
        /// Carrying it on this variant (rather than a `VerificationCondition`
        /// field) keeps the change to the few `Temporal` construction sites.
        #[serde(default)]
        machine: Option<crate::formula::contracts::StateMachineMetadata>,
    },
    // Trust: Liveness and fairness properties
    Liveness {
        property: LivenessProperty,
        /// Optional state-machine model, mirroring `Temporal::machine`: when
        /// present, the temporal backend (`ty`) checks the liveness property
        /// against it (SCC/lasso analysis); when absent, the VC stays
        /// fail-closed (no machine to check).
        #[serde(default)]
        machine: Option<crate::formula::contracts::StateMachineMetadata>,
    },
    Fairness {
        constraint: FairnessConstraint,
    },
    TaintViolation {
        source_label: String,
        sink_kind: String,
        path_length: usize,
    },
    RefinementViolation {
        spec_file: String,
        action: String,
    },
    // External dependency resilience
    ResilienceViolation {
        service: String,
        failure_mode: String,
        reason: String,
    },
    // Trust: Cross-service protocol composition
    ProtocolViolation {
        protocol: String,
        violation: String,
    },
    // Termination checking via decreases clauses
    NonTermination {
        /// "loop" or "recursion"
        context: String,
        /// Which measure failed to decrease (e.g., "n", "len - i")
        measure: String,
    },
    // Data race and memory ordering verification
    /// Two threads access the same variable without happens-before ordering,
    /// and at least one access is a write.
    DataRace {
        /// The shared variable being accessed.
        variable: String,
        /// Thread ID of the first access.
        thread_a: String,
        /// Thread ID of the second access.
        thread_b: String,
    },
    /// An atomic access uses an ordering that is insufficient for correctness.
    InsufficientOrdering {
        /// The variable being accessed.
        variable: String,
        /// The ordering actually used (e.g., "Relaxed").
        actual: String,
        /// The minimum ordering required (e.g., "Acquire").
        required: String,
    },
    // Translation validation — compiled code refines source MIR semantics.
    /// Asserts that a post-optimization (or compiled) function refines the
    /// pre-optimization MIR. UNSAT means the transformation is correct.
    TranslationValidation {
        /// Name of the optimization pass (e.g., "constant_folding", "dce").
        pass: String,
        /// Which check category this VC covers.
        check: String,
    },
    // Floating-point operation verification conditions.
    /// Float division where divisor may be zero (produces +/-Inf per IEEE 754).
    FloatDivisionByZero,
    /// Float arithmetic that may overflow to infinity (+/-Inf).
    FloatOverflowToInfinity {
        op: BinOp,
        operand_ty: Ty,
    },
    // Rvalue safety VCs for Discriminant, Aggregate, Ref, and Len.
    /// Discriminant read on a place that does not hold an enum/ADT type.
    InvalidDiscriminant {
        /// Human-readable name of the place whose discriminant was read.
        place_name: String,
    },
    /// Array aggregate constructed with a mismatched element count.
    AggregateArrayLengthMismatch {
        /// Expected number of elements from the array type.
        expected: usize,
        /// Actual number of operands provided.
        actual: usize,
    },
    // Unsafe code VC.
    /// Unsafe operation detected (raw pointer deref, transmute, FFI, etc.).
    UnsafeOperation {
        desc: String,
    },
    /// Binary stack write may overwrite the saved return address.
    SavedReturnAddressOverwrite {
        /// Number of bytes written by the memory access.
        access_width_bytes: u32,
        /// Human-readable stack return slot being protected.
        slot: String,
    },
    /// Binary or FFI printf-family call may use attacker-controlled format text.
    FormatStringViolation {
        /// Name of the printf-family callee.
        callee: String,
        /// Human-readable evidence for the unsafe format argument.
        evidence: String,
    },
    /// Binary indirect control-flow target is unresolved and therefore may be attacker-controlled.
    TaintedIndirectBranch {
        /// Control-flow sink, such as "indirect_branch" or "indirect_call".
        sink_kind: String,
        /// Human-readable target expression or unknown target marker.
        target: String,
        /// Evidence explaining why this is fail-closed rather than proof-grade.
        evidence: String,
    },
    /// Recovered binary ABI metadata contradicts proof-grade storage metadata.
    BinaryAbiContradiction {
        /// Human-readable ABI/storage fact that is contradictory.
        fact: String,
        /// Human-readable evidence for the contradiction.
        evidence: String,
    },
    /// Binary copy/copy-like sink may copy more bytes than the destination can hold.
    BinaryCopySinkLengthViolation {
        /// Name of the recovered copy sink, such as "memcpy" or "strncpy".
        callee: String,
        /// Description of the exact bad length evidence or missing proof facts.
        desc: String,
    },
    // FFI boundary verification with summary-based VCs.
    /// FFI call site where a summary-based contract was checked.
    FfiBoundaryViolation {
        /// Name of the extern callee (e.g., "malloc", "memcpy").
        callee: String,
        /// Description of the specific violation (null, range, alias, etc.).
        desc: String,
    },
    /// A raw bulk copy or pointer→slice construction
    /// (`ptr::copy[_nonoverlapping]`, `slice::from_raw_parts`) may read or write
    /// past the bounds of an allocation: the element/byte count is not provably
    /// `<=` the source (read) or destination (write) allocation size. Distinct
    /// from `IndexOutOfBounds`/`SliceBoundsCheck`, which cover *safe* indexing;
    /// this covers the unchecked raw-pointer count that the language does not
    /// guard. (Closes the gap where `from_raw_parts` only checked `len < 0`.)
    CopyBoundsViolation {
        /// The copy-like operation (e.g. "copy_nonoverlapping", "from_raw_parts").
        callee: String,
        /// Which side is unproven: "src" (read past source) or "dst" (write past destination).
        direction: String,
        /// Human-readable evidence: the bound that could not be discharged.
        detail: String,
    },
    /// A pointer/slice is derived from an allocation whose size can change
    /// *externally* — e.g. an `mmap`'d file another process can truncate, or a
    /// region a second thread can shrink — but the derived length was captured
    /// once and is not re-validated against the allocation's *live* size. A
    /// later access can then read past the valid region (SIGBUS on truncation,
    /// or an out-of-bounds read). The obligation: the captured length must be
    /// proven `<=` the live size at every use, or re-checked on each access.
    ExternallyMutableAllocationBounds {
        /// What kind of externally-mutable allocation (e.g. "mmap_file").
        allocation_kind: String,
        /// The size that may shrink out from under the derived view (e.g. "live_file_len").
        live_size: String,
        /// Human-readable detail / remediation hint.
        detail: String,
    },
    /// A bulk heap allocation (`Vec::with_capacity`/`Vec::reserve`/`<[T]>::resize`
    /// /`vec![_; n]`) is sized by a `count` that is not provably bounded — neither
    /// a constant, nor `<=` a value established by a reaching precondition/check,
    /// nor routed through a budget gateway whose over-budget branch returns
    /// *without* allocating. An adversarial or pathological `count` (e.g. an
    /// untrusted header field, or an unbounded loop-carried size) can then
    /// exhaust memory and OOM the process — an availability/DoS hazard — instead
    /// of failing closed. The obligation: `count` is provably `<= BOUND`, or the
    /// allocation site is dominated by a budget check whose failure path is the
    /// only reachable non-allocating action. This is a SAFETY invariant over the
    /// program text (where allocations sit in the CFG), NOT a termination/total-
    /// memory bound — the latter is undecidable in general. Closes the gap where
    /// `Solver::ensure_num_vars(n)` resized ~25 per-variable `Vec`s from an
    /// unbounded `n` (and computed `n * 2` with no overflow guard), letting a
    /// pathological query grow to 203 GB before the kernel killed it.
    UnboundedAllocation {
        /// The allocating operation (e.g. "Vec::with_capacity", "<[T]>::resize").
        callee: String,
        /// The size/count operand that is not provably bounded (e.g. "num_vars * 2").
        count: String,
        /// Human-readable evidence / remediation hint.
        detail: String,
    },
    // Typed ownership VcKind variants for trust_vc integration.
    /// Accessing memory after it has been freed (use-after-free).
    UseAfterFree,
    /// Freeing the same allocation twice (double-free).
    DoubleFree,
    /// Aliasing violation: &mut coexists with another &/&mut reference.
    AliasingViolation {
        /// true if the conflicting alias is &mut, false if shared &.
        mutable: bool,
    },
    /// Reference outlives its referent (dangling reference).
    LifetimeViolation,
    /// Non-Send type sent across thread boundary.
    SendViolation,
    /// Non-Sync type shared across threads.
    SyncViolation,
    // Functional correctness verification condition.
    /// The function produces an incorrect result (e.g., binary search returns
    /// wrong index on unsorted input). The `property` field describes the
    /// expected property (e.g., "result correctness"), and `context` carries
    /// domain-specific information (e.g., "binary_search: input not sorted").
    FunctionalCorrectness {
        /// High-level property being checked (e.g., "result_correctness").
        property: String,
        /// Domain context explaining the failure (e.g., "input array not sorted").
        context: String,
    },
    /// Hardened profile obligation for OS/path/byte/error/panic/unsafe/FFI/trust-domain
    /// boundary hazards. Older reports serialized these as
    /// `FunctionalCorrectness { property: "hardened::<category>", ... }`; use
    /// `hardened_category()` to classify both encodings.
    HardenedBoundary {
        category: HardenedVcCategory,
        callee: String,
        detail: String,
    },
    // trust-wp-style contract VcKinds for Horn clause lowering.
    /// Loop invariant initiation: the invariant holds on entry to the loop.
    LoopInvariantInitiation {
        /// The invariant expression that must hold at loop entry.
        invariant: String,
        /// Block ID of the loop header.
        header_block: usize,
    },
    /// Loop invariant consecution: if the invariant holds before an iteration,
    /// it holds after the iteration (inductive step).
    LoopInvariantConsecution {
        /// The invariant expression being checked inductively.
        invariant: String,
        /// Block ID of the loop header.
        header_block: usize,
    },
    /// Loop invariant sufficiency: the invariant implies the postcondition
    /// upon loop exit.
    LoopInvariantSufficiency {
        /// The invariant expression that must imply the post-loop property.
        invariant: String,
        /// Block ID of the loop header.
        header_block: usize,
    },
    /// Type refinement violation: a value does not satisfy its refinement predicate.
    TypeRefinementViolation {
        /// The variable or expression being refined.
        variable: String,
        /// The refinement predicate that was violated (e.g., "v > 0").
        predicate: String,
    },
    /// Frame condition violation: a variable not in the modifies set was changed.
    FrameConditionViolation {
        /// The variable that was modified but not in the modifies clause.
        variable: String,
        /// The function whose frame condition was violated.
        function: String,
    },
    /// TINV (design `docs/design/2026-10-04-type-invariant-tinv.md`): an inferred
    /// invariant of the struct `ty` is owed at `point`, at MIR location `site`.
    ///
    /// * The formula is SITUATED: `pc ∧ state-binding ⇒ I(σ)` at that program point
    ///   (§P4), never the bare negated clause. The `ContractInvariant` doc above is
    ///   the defect this kind must not repeat.
    /// * Only the TINV pre-pass mints it (step 7). A failed or unknown row drops a
    ///   Houdini candidate conjunct; it is not a refutation of the program.
    /// * `ty` MUST be the crate-qualified def path (the crate name prefixed even for a
    ///   local item): the string enters certificate identity and the dedup
    ///   description, and a local `def_path_str` omits the crate.
    ///
    /// APPENDED LAST ON PURPOSE: `ObligationIdentity::from_vc` is bincode, which
    /// encodes the declaration index, so a mid-enum insert re-keys every later
    /// variant's certificate identity.
    ///
    /// ROW IDENTITY. `(ty, point, site, conjunct, ordinal, edge)` names the row exactly,
    /// so a consumer (coverage match, cache, dedup, Houdini, the 7.7 authority flip)
    /// can never pair or conflate two rows by emission order:
    /// * `conjunct` is the candidate conjunct's id within `ty`;
    /// * `ordinal` distinguishes two roots owing the same point at one site;
    /// * `edge` is `Some(p)` for an EDGE PART of a point at a join block (TINV-9(a)):
    ///   the part covers exactly the executions entering `site.block` from predecessor
    ///   block `p`. A point with parts is discharged only when EVERY part is (and, since
    ///   7.7, every part is kernel-certified); one proved part discharges nothing.
    ///   `None` for an unsplit row.
    TypeInvariant {
        ty: String,
        point: TypeInvariantPoint,
        site: TypeInvariantSite,
        conjunct: u32,
        ordinal: u32,
        edge: Option<usize>,
    },
    /// A body-lowering refusal retaining the authored source predicate. The
    /// refusal query is not a proof or refutation of that predicate. Appended
    /// to preserve existing bincode-backed obligation identities.
    DeclinedContractBody(Box<super::ContractBodyDecline>),
}

impl VcKind {
    /// Return a retained typed source question for a body-lowering decline.
    /// This carries no proof or current-program authority by itself.
    #[must_use]
    pub fn declined_contract_body(&self) -> Option<&super::ContractBodyDecline> {
        match self {
            Self::DeclinedContractBody(decline) => Some(decline.as_ref()),
            _ => None,
        }
    }

    /// Stable family tag for binary copy-sink length obligations.
    pub const BINARY_COPY_SINK_LENGTH_FAMILY: &'static str = "binary_copy_sink_length_violation";
    /// Stable prefix used for machine-readable hardened report tags.
    pub const HARDENED_FAMILY_PREFIX: &'static str = "hardened";
    /// Kind prefix the native full-verification lane stamps onto an
    /// `UnsupportedMir` round-trip row (`FullVerification::<ApiKind>`, built as
    /// `format!("FullVerification::{kind:?}")` from the verifier-API obligation
    /// kind in `trust_verify.rs::legacy_unsupported_kind_detail`).
    pub const FULL_VERIFICATION_KIND_PREFIX: &'static str = "FullVerification::";
    /// Message prefix the separation engine (trust-vcgen `sep_engine.rs`, the
    /// ONLY producer) stamps on every unsafe-operation obligation it mints as a
    /// [`VcKind::Assertion`]. Rust inserts no check for any of them, so
    /// [`VcKind::has_runtime_fallback_in`] declines the whole family.
    pub const SEP_UNSAFE_ASSERTION_PREFIX: &'static str = "[unsafe:sep:";

    /// The memory-provenance lane's assertion tag (`memory_provenance.rs` —
    /// use-after-free / dangling / invalidated-pointer claims). Rust inserts NO
    /// check for any of them; see [`VcKind::has_runtime_fallback_in`].
    pub const PROVENANCE_ASSERTION_PREFIX: &'static str = "[provenance]";

    /// `UnsupportedMir { kind }` tag the compiler mints when the configured
    /// memory authority (trustd) could not admit a function BEFORE any solver
    /// ran. It is not a modelling gap: nothing was attempted. targo recognises
    /// this exact tag to turn an unreachable authority into a SETUP failure
    /// instead of one `unknown` row per function — on 2026-09-19 a 4h44m gate
    /// over ay reported 282,786 such rows in its last eight seconds after a
    /// test stub unlinked the live daemon's socket, and the census read as a
    /// verifier-completeness measurement for two days.
    pub const MEMORY_ADMISSION_UNSUPPORTED_MIR_KIND: &'static str = "MemoryAdmission";

    /// The rendered prefix such a row carries (the `Display` arm for
    /// `UnsupportedMir`), so a consumer that only sees rendered rows can still
    /// recognise the closed vocabulary without parsing free text.
    #[must_use]
    pub fn memory_admission_message_prefix() -> String {
        format!("unsupported MIR `{}`: ", Self::MEMORY_ADMISSION_UNSUPPORTED_MIR_KIND)
    }

    /// Why a kernel-checked UNSAT of this kind's violation formula is NOT a
    /// proof about the program — or `None` when it is.
    ///
    /// # The question this answers
    ///
    /// `trust_certify::certify_vc` mints a zero-trust `CleanCic` certificate on
    /// a kernel-checked UNSAT of `vc.formula`, and two compiler routes turn that
    /// certificate into a `Proved { solver: "clean-kernel-certified" }` row:
    /// `promote_kernel_certifiable` and the bridge certify-fallback (both in
    /// `rustc_mir_transform::trust_verify`). Neither inspects `vc.kind`. Their
    /// shared soundness argument is written in the fallback's comment:
    ///
    /// > a genuinely-violable obligation has a SAT violation, so it stays
    /// > undecided (never a false Proved).
    ///
    /// That argument is valid **only if `vc.formula` faithfully encodes "this
    /// obligation is violated"** — i.e. only if it conjoins the program state
    /// reaching the obligation's program point with the negated predicate. When
    /// it does, UNSAT means no reachable state violates the obligation, which is
    /// a statement about the program. When it does not, UNSAT means only that
    /// the predicate's negation is unsatisfiable — that the predicate is VALID —
    /// which is a statement about the predicate's TEXT.
    ///
    /// A row that means "P is valid" is provable exactly when P constrains
    /// nothing, so the provable set of such a kind is exactly the TAUTOLOGIES.
    /// The kernel is not at fault in that case and the certificate is not
    /// forged: the kernel is asked a true question and answers it truthfully.
    /// The defect is that the question is not about the program.
    ///
    /// # Measured
    ///
    /// On the sealed toolchain `trust-e26541e3`, via the `register_tool`
    /// surface, over `pub fn f(x: u32) -> u32 { x / 2 }`:
    ///
    /// ```text
    ///   #[trust::invariant(1 == 1)] -> proved, solver=clean-kernel-certified
    ///   #[trust::invariant(x == x)] -> proved, solver=clean-kernel-certified
    ///   #[trust::invariant(x >= 0)] -> unknown   (true of EVERY u32)
    ///   #[trust::invariant(true)]   -> unknown
    ///   #[trust::invariant(false)]  -> unknown
    /// ```
    ///
    /// The provable set is exactly the tautologies, and the proved rows carry
    /// `kind: "invariant"` at `ProofLevel::L1Functional` — the rows a ratchet
    /// counts as `proved_by_kind.invariant` and `kernel_certified`. The same
    /// battery over `ensures` on the same body proves `result <= x` and
    /// `result == 7` (on a body returning `7`) while refusing `result > x` and
    /// `result == 7` (on `x / 2`), so that kind's formula IS body-aware and is
    /// admitted here unchanged.
    ///
    /// # Why this is a total match
    ///
    /// The refusal is deliberately expressed as an exhaustive match rather than
    /// a refuse-list plus a catch-all. `VcKind` is `#[non_exhaustive]` only to
    /// DOWNSTREAM crates; in this crate a new variant makes this match fail to
    /// compile, which forces whoever adds a kind to state whether its formula
    /// binds its free names to program state before the kernel may certify it.
    /// That compile error is the point of this function.
    ///
    /// Crate-private since TINV step 7.2: every consumer asks the VC-level
    /// [`crate::VerificationCondition::kernel_authority_refusal`], which applies this
    /// gate and then the per-kind structural checks.
    #[must_use]
    pub(crate) fn kind_authority_refusal(&self) -> Option<&'static str> {
        match self {
            // ---- REFUSED -------------------------------------------------
            VcKind::DeclinedContractBody(_) => Some(
                "body lowering declined this contract: its refusal query is not a program violation; the retained source predicate requires an independently checked monitor or body proof",
            ),
            //
            // An item-position `#[invariant(..)]` names NO program point, so
            // there is nothing to bind its free names at. `trust-mir-extract`
            // reads the attribute off `tcx.hir_attrs` for its span and snippet
            // and never lowers it, and vcgen mints `formula: Not(parsed)` with
            // nothing else — no path condition, no pre-state. UNSAT of that is
            // validity of the clause text. See the measured table above.
            //
            // This is NOT the loop machinery: a `while <cond> invariant <p>`
            // clause is `ContractKind::LoopInvariant` and lowers to the
            // `LoopInvariant{Initiation,Consecution,Sufficiency}` kinds below,
            // which carry a `header_block` and conjoin the loop's state. Those
            // stay admitted, and the initiation shape certifies exactly as it
            // did before this gate existed.
            VcKind::ContractInvariant { .. } => Some(
                "item-position `invariant` names no program point, so its violation formula is \
                 the bare negated clause with none of its free names bound to program state; a \
                 kernel-checked UNSAT of it proves only that the clause text is a tautology",
            ),
            // Same defect, same shape: vcgen mints `formula: Not(parsed)` over
            // the refinement predicate with the refined variable unbound to any
            // program value, so UNSAT is validity of the predicate text rather
            // than a fact about the refined place.
            VcKind::TypeRefinementViolation { .. } => Some(
                "a type-refinement row's violation formula is the bare negated predicate with \
                 the refined variable unbound to any program value; a kernel-checked UNSAT of \
                 it proves only that the predicate text is a tautology",
            ),
            // v6/D2: `ty` owns concurrency, and its obligations must be real.
            // No producer builds either kind from a concurrency model today: the
            // memory-ordering legality row is a lone free boolean emitted after
            // Rust already decided the operation, and the data-race formula is
            // decided before emission. The router refuses both before dispatch;
            // this gate keeps the kernel lane from certifying them around it.
            VcKind::DataRace { .. } | VcKind::InsufficientOrdering { .. } => Some(
                "a concurrency obligation carries no concurrency model yet (v6/D2): its formula \
                 was decided before emission, so a kernel-checked UNSAT of it is not a fact \
                 about any interleaving",
            ),

            // ---- ADMITTED ------------------------------------------------
            //
            // Language-safety obligations. vcgen builds each of these from MIR
            // with the reaching path condition conjoined, so UNSAT of the
            // violation formula is exactly "no reachable state violates it".
            VcKind::ArithmeticOverflow { .. }
            | VcKind::ShiftOverflow { .. }
            | VcKind::UncheckedArithmeticOverflow { .. }
            | VcKind::DivisionByZero
            | VcKind::RemainderByZero
            | VcKind::IndexOutOfBounds
            | VcKind::SliceBoundsCheck
            | VcKind::UncheckedIndexBounds { .. }
            | VcKind::Assertion { .. }
            | VcKind::CastOverflow { .. }
            | VcKind::NegationOverflow { .. }
            | VcKind::Unreachable
            | VcKind::FloatDivisionByZero
            | VcKind::FloatOverflowToInfinity { .. }
            | VcKind::InvalidDiscriminant { .. }
            | VcKind::AggregateArrayLengthMismatch { .. }
            | VcKind::UnsafeOperation { .. }
            | VcKind::SavedReturnAddressOverwrite { .. }
            | VcKind::FormatStringViolation { .. }
            | VcKind::TaintedIndirectBranch { .. } => None,

            // Contract kinds whose formula IS body-aware.
            //
            // `Postcondition` is replaced by the per-`Return` body-aware rows in
            // `generate_v2_contract_vcs_impl` before dispatch, and the measured
            // battery above confirms it refuses predicates false of the body.
            // `Precondition` at a CALL SITE carries the caller's actual
            // arguments; the def-site `#[requires]` row never reaches a solver
            // as a proof request at all (it is transported as
            // `assumption:requires`), so admitting the kind does not admit it.
            VcKind::Postcondition | VcKind::Precondition { .. } => None,

            // Loop-clause obligations. Each carries a `header_block` program
            // point and conjoins the loop state with the negated invariant, so
            // UNSAT is a fact about the loop.
            VcKind::LoopInvariantInitiation { .. }
            | VcKind::LoopInvariantConsecution { .. }
            | VcKind::LoopInvariantSufficiency { .. } => None,

            // Memory, aliasing and boundary obligations: all minted from
            // MIR/analysis facts with their reaching conditions.
            VcKind::UseAfterFree { .. }
            | VcKind::DoubleFree { .. }
            | VcKind::AliasingViolation { .. }
            | VcKind::LifetimeViolation { .. }
            | VcKind::SendViolation
            | VcKind::SyncViolation
            | VcKind::Deadlock
            | VcKind::UnboundedAllocation { .. }
            | VcKind::CopyBoundsViolation { .. }
            | VcKind::ExternallyMutableAllocationBounds { .. }
            | VcKind::FfiBoundaryViolation { .. }
            | VcKind::BinaryAbiContradiction { .. }
            | VcKind::BinaryCopySinkLengthViolation { .. }
            | VcKind::HardenedBoundary { .. }
            | VcKind::FrameConditionViolation { .. } => None,

            // Model/domain obligations. These are not certified through this
            // route today (their backends own them), but their formulas are
            // built from the extracted model rather than from clause text, so
            // the gate does not refuse them.
            VcKind::DeadState { .. }
            | VcKind::Temporal { .. }
            | VcKind::Liveness { .. }
            | VcKind::Fairness { .. }
            | VcKind::TaintViolation { .. }
            | VcKind::RefinementViolation { .. }
            | VcKind::ResilienceViolation { .. }
            | VcKind::ProtocolViolation { .. }
            | VcKind::NonTermination { .. }
            | VcKind::TranslationValidation { .. }
            | VcKind::FunctionalCorrectness { .. } => None,

            // A preserved-but-unmodelled MIR sentinel. It is deliberately
            // non-refutable wherever it is minted, so it cannot reach UNSAT; the
            // gate leaves it exactly as it was.
            VcKind::UnsupportedMir { .. } => None,

            // TINV-8 / TINV step 7.7 (2026-10-05): ADMITTED BY KIND, CONDITIONALLY.
            // The step-7 pre-pass (`trust_vcgen::type_invariant`) mints every row inside
            // the ordinary safety walk with its path condition, its entry/post-call
            // facts and an obligation record. Admission here is NOT admission of the
            // row: `VerificationCondition::kernel_authority_refusal` then applies
            // `type_invariant_situatedness_refusal` (TINV-9(j)) — a record that replays
            // to the formula, a negated core conjoined last, at least one hypothesis,
            // every core name bound by one, an edge part's guard never counted — and
            // refuses every row that fails it. That check is a regression guard against
            // record-less, bare and forged rows only; it says nothing about whether the
            // hypotheses are true program facts, which is the producer's and Houdini's
            // vacuity filter's job (TINV-9(h)). MUTATION: move this arm back under
            // REFUSED and `trust-certify/tests/kernel_authority_kind_gate.rs`
            // `a_recorded_situated_type_invariant_row_mints_and_replays` fails.
            VcKind::TypeInvariant { .. } => None,
        }
    }

    /// Hardened obligation category for typed rows and legacy
    /// `FunctionalCorrectness { property: "hardened::<category>" }` rows.
    #[must_use]
    pub fn hardened_category(&self) -> Option<HardenedVcCategory> {
        match self {
            VcKind::HardenedBoundary { category, .. } => Some(*category),
            VcKind::Assertion { message } if message.starts_with("[unsafe:ffi]") => {
                Some(HardenedVcCategory::FfiBoundary)
            }
            VcKind::Assertion { message } if message.starts_with("[unsafe") => {
                Some(HardenedVcCategory::UnsafeOperation)
            }
            VcKind::UnsafeOperation { .. } => Some(HardenedVcCategory::UnsafeOperation),
            VcKind::FfiBoundaryViolation { desc, .. }
                if !desc.contains(VcKind::BINARY_COPY_SINK_LENGTH_FAMILY)
                    && !desc.contains("copy sink length") =>
            {
                Some(HardenedVcCategory::FfiBoundary)
            }
            VcKind::FunctionalCorrectness { property, .. } => {
                property.strip_prefix("hardened::").and_then(HardenedVcCategory::from_tag)
            }
            _ => None,
        }
    }

    /// Whether a VC of this kind with violation formula `formula` is a hardened
    /// DESIGN MANDATE: a hardened category that admits one
    /// ([`HardenedVcCategory::admits_design_mandate`]) and the closed tautology
    /// `Bool(true)`, a violation no engine can ever prove UNSAT.
    ///
    /// THE one predicate behind the compiler's transport `design_mandate` bit and
    /// the default policy's tolerance skip (`rustc_mir_transform::trust_verify`)
    /// and the interval augmentation's leave-alone rule (`trust-vcgen`
    /// `augment_vc_with_abstract_state`), so the three cannot drift. An L0
    /// `UnsafeOperation`/`FfiBoundary` row with a `Bool(true)` violation is a
    /// fail-closed modelling gap and answers `false`.
    #[must_use]
    pub fn is_hardened_design_mandate(&self, formula: &super::Formula) -> bool {
        matches!(formula, super::Formula::Bool(true))
            && self.hardened_category().is_some_and(HardenedVcCategory::admits_design_mandate)
    }

    /// Stable hardened family tag for reports, including legacy rows.
    #[must_use]
    pub fn hardened_family_tag(&self) -> Option<String> {
        self.hardened_category()
            .map(|category| format!("{}_{}", Self::HARDENED_FAMILY_PREFIX, category.as_tag()))
    }

    /// Stable compact tag used by compiler diagnostics and structured
    /// transport.
    ///
    /// This tag is deliberately retained for backward compatibility and human
    /// readability. It is not a lossless serialization: parameterized kinds
    /// must also travel in `TransportObligationResult::typed_kind`.
    #[must_use]
    pub fn transport_tag(&self) -> String {
        if let Some(category) = self.hardened_category() {
            return format!("hardened_{}", category.as_tag());
        }
        if let VcKind::TypeInvariant { point, .. } = self {
            return format!("type_invariant:{}", point.as_tag());
        }

        let tag = match self {
            VcKind::ArithmeticOverflow { op, .. } => match op {
                BinOp::Add => "overflow:add",
                BinOp::Sub => "overflow:sub",
                BinOp::Mul => "overflow:mul",
                // `Div`/`Rem` overflow (`MIN / -1`, `MIN % -1`) are real checked
                // arithmetic ops with their own `mir_assert::Overflow(Div|Rem)`
                // twins. Collapsing them onto the op-less `overflow` tag erased
                // the op token that same-span twin subsumption keys on, so a
                // PROVED div-overflow sibling could never discharge its twin
                // (`direct_panic_sibling_family` fails closed on op-less tags,
                // by design, to prevent cross-op discharge). Name them.
                BinOp::Div => "overflow:div",
                BinOp::Rem => "overflow:rem",
                _ => "overflow",
            },
            VcKind::ShiftOverflow { op, .. } => match op {
                BinOp::Shl => "shift:left",
                BinOp::Shr => "shift:right",
                _ => "shift",
            },
            // Deliberately NOT the `overflow:*` tags. Same-span twin subsumption
            // keys on this token, and an `unchecked_add` has no `mir_assert`
            // twin to be subsumed BY — sharing the tag would let a PROVED
            // checked-add sibling discharge it across ops.
            VcKind::UncheckedArithmeticOverflow { op, .. } => match op {
                BinOp::Add => "unchecked_overflow:add",
                BinOp::Sub => "unchecked_overflow:sub",
                BinOp::Mul => "unchecked_overflow:mul",
                _ => "unchecked_overflow",
            },
            VcKind::DivisionByZero => "divzero",
            VcKind::RemainderByZero => "remzero",
            VcKind::FloatDivisionByZero => "float_division_by_zero",
            VcKind::FloatOverflowToInfinity { .. } => "float_overflow_to_infinity",
            VcKind::IndexOutOfBounds => "bounds",
            VcKind::SliceBoundsCheck => "slice",
            // Distinct from `bounds` for the same twin-subsumption reason: an
            // unchecked index has no `panic_bounds_check` twin.
            VcKind::UncheckedIndexBounds { .. } => "unchecked_bounds",
            VcKind::Assertion { .. } => "assert",
            VcKind::ContractInvariant { .. } => "invariant",
            VcKind::Precondition { .. } => "precond",
            VcKind::Postcondition => "postcond",
            VcKind::Unreachable => "unreach",
            VcKind::DeadState { .. } => "deadstate",
            VcKind::Deadlock => "deadlock",
            VcKind::Temporal { .. } => "temporal",
            VcKind::CastOverflow { .. } => "cast",
            VcKind::NegationOverflow { .. } => "negation",
            VcKind::Liveness { .. } => "liveness",
            VcKind::Fairness { .. } => "fairness",
            VcKind::TaintViolation { .. } => "taint",
            VcKind::RefinementViolation { .. } => "refinement",
            VcKind::ResilienceViolation { .. } => "resilience",
            VcKind::ProtocolViolation { .. } => "protocol",
            VcKind::NonTermination { .. } => "termination",
            VcKind::UnboundedAllocation { .. } => "unbounded_allocation",
            _ => "unknown",
        };
        tag.to_string()
    }

    /// True for typed copy-sink length VCs and legacy FFI-tagged compatibility rows.
    ///
    /// Older artifacts emitted this family as `FfiBoundaryViolation` with a
    /// description containing "copy sink length". Keeping that compatibility
    /// classifier lets reports distinguish this security family even when they
    /// read pre-typed evidence.
    #[must_use]
    pub fn is_binary_copy_sink_length_violation(&self) -> bool {
        match self {
            VcKind::BinaryCopySinkLengthViolation { .. } => true,
            VcKind::FfiBoundaryViolation { desc, .. } => desc.contains("copy sink length"),
            _ => false,
        }
    }

    /// Stable family tag for copy-sink length rows, including legacy rows.
    #[must_use]
    pub fn binary_copy_sink_length_family_tag(&self) -> Option<&'static str> {
        self.is_binary_copy_sink_length_violation().then_some(Self::BINARY_COPY_SINK_LENGTH_FAMILY)
    }

    /// Human-readable description.
    pub fn description(&self) -> String {
        match self {
            VcKind::ArithmeticOverflow { op, .. } => {
                format!("arithmetic overflow ({op:?})")
            }
            // Prefixed, so it can never collide with the `ArithmeticSafety`
            // detail prefixes `recovered_full_lane_vc_tag` anchors on — a
            // round-tripped unchecked row must not recover as `overflow:add`
            // and thereby re-acquire the `overflow_checks` answer.
            VcKind::UncheckedArithmeticOverflow { op, .. } => {
                format!("unchecked arithmetic overflow ({op:?})")
            }
            VcKind::ShiftOverflow { op, .. } => {
                format!("shift overflow ({op:?})")
            }
            VcKind::DivisionByZero => "division by zero".to_string(),
            VcKind::RemainderByZero => "remainder by zero".to_string(),
            VcKind::IndexOutOfBounds => "index out of bounds".to_string(),
            VcKind::SliceBoundsCheck => "slice bounds check".to_string(),
            VcKind::UncheckedIndexBounds { callee, detail } => {
                format!("unchecked index bounds in `{callee}`: {detail}")
            }
            VcKind::Assertion { message } => format!("assertion: {message}"),
            VcKind::ContractInvariant { expression } => format!("invariant: {expression}"),
            VcKind::Precondition { callee } => format!("precondition of `{callee}`"),
            VcKind::Postcondition => "postcondition".to_string(),
            VcKind::CastOverflow { from_ty, to_ty } => {
                format!("cast overflow ({from_ty:?} -> {to_ty:?})")
            }
            VcKind::NegationOverflow { ty } => {
                format!("negation overflow ({ty:?})")
            }
            VcKind::Unreachable => "unreachable code reached".to_string(),
            VcKind::UnsupportedMir { kind, detail } => {
                format!("unsupported MIR `{kind}`: {detail}")
            }
            VcKind::DeclinedContractBody(decline) => match decline.cause {
                super::ContractBodyDeclineCause::UnconstrainedReturnCall => format!(
                    "postcondition body declined: unconstrained return call (source clause #{})",
                    decline.source_contract_index,
                ),
            },
            VcKind::DeadState { state } => format!("dead state `{state}`"),
            VcKind::Deadlock => "deadlock".to_string(),
            VcKind::Temporal { property, .. } => format!("temporal: {property}"),
            VcKind::Liveness { property, .. } => format!("liveness: {}", property.description()),
            VcKind::Fairness { constraint } => {
                format!("fairness: {}", constraint.description())
            }
            VcKind::TaintViolation { source_label, sink_kind, path_length } => {
                format!(
                    "taint violation: {} data reaches {} sink (path length: {})",
                    source_label, sink_kind, path_length
                )
            }
            VcKind::RefinementViolation { spec_file, action } => {
                format!(
                    "refinement violation: action `{action}` does not refine spec `{spec_file}`"
                )
            }
            VcKind::ResilienceViolation { service, failure_mode, reason } => {
                format!("resilience: {service} {failure_mode} - {reason}")
            }
            VcKind::ProtocolViolation { protocol, violation } => {
                format!("protocol `{protocol}`: {violation}")
            }
            VcKind::NonTermination { context, measure } => {
                format!("non-termination: {context} measure `{measure}` may not decrease")
            }
            // Data race and memory ordering descriptions
            VcKind::DataRace { variable, thread_a, thread_b } => {
                format!("data race on `{variable}` between threads {thread_a} and {thread_b}")
            }
            VcKind::InsufficientOrdering { variable, actual, required } => {
                format!(
                    "insufficient memory ordering on `{variable}`: {actual}, requires {required}"
                )
            }
            VcKind::TranslationValidation { pass, check } => {
                format!("translation validation ({pass}): {check}")
            }
            // Floating-point VC descriptions
            VcKind::FloatDivisionByZero => "float division by zero".to_string(),
            VcKind::FloatOverflowToInfinity { op, .. } => {
                format!("float overflow to infinity ({op:?})")
            }
            // Rvalue safety VC descriptions
            VcKind::InvalidDiscriminant { place_name } => {
                format!("invalid discriminant read on `{place_name}` (not an enum)")
            }
            VcKind::AggregateArrayLengthMismatch { expected, actual } => {
                format!(
                    "array aggregate length mismatch: expected {expected} elements, got {actual}"
                )
            }
            // Unsafe operation description.
            VcKind::UnsafeOperation { desc } => format!("unsafe operation: {desc}"),
            VcKind::SavedReturnAddressOverwrite { access_width_bytes, slot } => {
                format!(
                    "binary saved return address overwrite: {access_width_bytes}-byte write may alias {slot}"
                )
            }
            VcKind::FormatStringViolation { callee, evidence } => {
                format!("format string violation in `{callee}`: {evidence}")
            }
            VcKind::TaintedIndirectBranch { sink_kind, target, evidence } => {
                format!("tainted indirect control flow: {target} reaches {sink_kind}: {evidence}")
            }
            VcKind::BinaryAbiContradiction { fact, evidence } => {
                format!("binary ABI contradiction: {fact} ({evidence})")
            }
            VcKind::BinaryCopySinkLengthViolation { callee, desc } => {
                format!("binary copy-sink length violation in `{callee}`: {desc}")
            }
            // FFI boundary verification description.
            VcKind::FfiBoundaryViolation { callee, desc } => {
                format!("FFI boundary violation in `{callee}`: {desc}")
            }
            VcKind::CopyBoundsViolation { callee, direction, detail } => {
                format!("copy bounds violation in `{callee}` ({direction}): {detail}")
            }
            VcKind::ExternallyMutableAllocationBounds { allocation_kind, live_size, detail } => {
                format!(
                    "externally-mutable allocation bounds ({allocation_kind}, live size `{live_size}`): {detail}"
                )
            }
            VcKind::UnboundedAllocation { callee, count, detail } => {
                format!("unbounded allocation in `{callee}` (count `{count}`): {detail}")
            }
            // Ownership VcKind descriptions.
            VcKind::UseAfterFree => "use after free".to_string(),
            VcKind::DoubleFree => "double free".to_string(),
            VcKind::AliasingViolation { mutable } => {
                if *mutable {
                    "aliasing violation: &mut aliases with &mut".to_string()
                } else {
                    "aliasing violation: &mut aliases with &".to_string()
                }
            }
            VcKind::LifetimeViolation => {
                "lifetime violation: reference outlives referent".to_string()
            }
            VcKind::SendViolation => {
                "Send violation: non-Send type sent across threads".to_string()
            }
            VcKind::SyncViolation => {
                "Sync violation: non-Sync type shared across threads".to_string()
            }
            // Functional correctness description.
            VcKind::FunctionalCorrectness { property, context } => {
                format!("functional correctness ({property}): {context}")
            }
            VcKind::HardenedBoundary { category, callee, detail } => {
                format!("hardened boundary ({}): {callee}: {detail}", category.as_tag())
            }
            // trust_wp contract VC descriptions.
            VcKind::LoopInvariantInitiation { invariant, header_block } => {
                format!("loop invariant initiation (bb{header_block}): {invariant}")
            }
            VcKind::LoopInvariantConsecution { invariant, header_block } => {
                format!("loop invariant consecution (bb{header_block}): {invariant}")
            }
            VcKind::LoopInvariantSufficiency { invariant, header_block } => {
                format!("loop invariant sufficiency (bb{header_block}): {invariant}")
            }
            VcKind::TypeRefinementViolation { variable, predicate } => {
                format!("type refinement violation: {variable} does not satisfy {predicate}")
            }
            VcKind::FrameConditionViolation { variable, function } => {
                format!(
                    "frame condition violation: `{variable}` modified outside modifies clause of `{function}`"
                )
            }
            // Lossless over (ty, point, site, conjunct, ordinal, edge): `vc_dedup` and
            // targo's typed-kind check compare descriptions, so two edge parts of one
            // point (or two conjuncts of one row) must never describe alike.
            VcKind::TypeInvariant { ty, point, site, conjunct, ordinal, edge } => {
                let via = match edge {
                    Some(p) => format!(" via edge bb{p}"),
                    None => String::new(),
                };
                format!(
                    "type invariant of `{ty}` conjunct {conjunct} at {point} ({site}) ordinal \
                     {ordinal}{via}"
                )
            }
        }
    }

    /// Returns the proof level (L0, L1, L2).
    pub fn proof_level(&self) -> ProofLevel {
        match self {
            VcKind::ArithmeticOverflow { .. }
            // Same L0 safety property as its checked sibling — overflowing an
            // `unchecked_*` is UB, which is strictly worse than a panic.
            | VcKind::UncheckedArithmeticOverflow { .. }
            | VcKind::ShiftOverflow { .. }
            | VcKind::DivisionByZero
            | VcKind::RemainderByZero
            | VcKind::IndexOutOfBounds
            | VcKind::SliceBoundsCheck
            // An out-of-bounds unchecked index is UB, not a panic: L0.
            | VcKind::UncheckedIndexBounds { .. }
            | VcKind::Assertion { .. }
            | VcKind::CastOverflow { .. }
            | VcKind::NegationOverflow { .. }
            | VcKind::Unreachable
            | VcKind::UnsupportedMir { .. }
            // Discriminant on non-enum and array length mismatch are safety (L0).
            | VcKind::InvalidDiscriminant { .. }
            | VcKind::AggregateArrayLengthMismatch { .. }
            | VcKind::UnsafeOperation { .. }
            | VcKind::SavedReturnAddressOverwrite { .. }
            | VcKind::FormatStringViolation { .. }
            | VcKind::TaintedIndirectBranch { .. }
            | VcKind::BinaryAbiContradiction { .. }
            | VcKind::BinaryCopySinkLengthViolation { .. }
            // FFI boundary violations are safety (L0).
            | VcKind::FfiBoundaryViolation { .. }
            // Raw-copy bounds and externally-mutable allocation bounds are UB-class (L0).
            | VcKind::CopyBoundsViolation { .. }
            | VcKind::ExternallyMutableAllocationBounds { .. }
            // Unbounded allocation is an availability/DoS safety hazard (L0).
            | VcKind::UnboundedAllocation { .. } => ProofLevel::L0Safety,
            // An authored invariant is a contract clause, exactly like its
            // `Requires`/`Ensures` siblings: L1, not L0 safety.
            VcKind::Precondition { .. }
            | VcKind::Postcondition
            | VcKind::DeclinedContractBody(_)
            | VcKind::ContractInvariant { .. }
            | VcKind::TypeInvariant { .. } => ProofLevel::L1Functional,
            VcKind::DeadState { .. }
            | VcKind::Deadlock
            | VcKind::Temporal { .. }
            | VcKind::Liveness { .. }
            | VcKind::Fairness { .. }
            | VcKind::RefinementViolation { .. }
            | VcKind::ProtocolViolation { .. } => ProofLevel::L2Domain,
            VcKind::TaintViolation { .. } => ProofLevel::L1Functional,
            VcKind::ResilienceViolation { .. } => ProofLevel::L1Functional,
            VcKind::NonTermination { .. } => ProofLevel::L1Functional,
            // Data races are UB (L0 safety), ordering is correctness (L1).
            VcKind::DataRace { .. } => ProofLevel::L0Safety,
            VcKind::InsufficientOrdering { .. } => ProofLevel::L1Functional,
            // Translation validation is functional correctness (L1).
            VcKind::TranslationValidation { .. } => ProofLevel::L1Functional,
            // Trust (DESIGN_PHILOSOPHY §9 — defined behavior is not unsafe):
            // IEEE-754 float division-by-zero and overflow-to-infinity are DEFINED
            // (±inf/NaN, never trap, never UB), so they are NOT L0 safety
            // violations and must never fail-close a build of valid Rust. They are
            // demoted to L1 (functional/numerical-hygiene advisory): a bounded op
            // still proves, an unbounded one surfaces as a non-fatal note rather
            // than an L0 refutation. `FloatDivisionByZero` is additionally not even
            // emitted (division is total — nothing to advise); `FloatOverflowToInfinity`
            // remains emittable as the L1 advisory. See the Div arm in
            // trust-vcgen `generate.rs` and the reference generator.
            VcKind::FloatDivisionByZero | VcKind::FloatOverflowToInfinity { .. } => {
                ProofLevel::L1Functional
            }
            // Ownership violations are all UB (L0 safety).
            VcKind::UseAfterFree
            | VcKind::DoubleFree
            | VcKind::AliasingViolation { .. }
            | VcKind::LifetimeViolation
            | VcKind::SendViolation
            | VcKind::SyncViolation => ProofLevel::L0Safety,
            VcKind::HardenedBoundary {
                category: HardenedVcCategory::UnsafeOperation | HardenedVcCategory::FfiBoundary,
                ..
            } => ProofLevel::L0Safety,
            // Functional correctness is L1.
            VcKind::FunctionalCorrectness { .. } | VcKind::HardenedBoundary { .. } => {
                ProofLevel::L1Functional
            }
            // trust_wp contract VCs are L1 functional correctness.
            VcKind::LoopInvariantInitiation { .. }
            | VcKind::LoopInvariantConsecution { .. }
            | VcKind::LoopInvariantSufficiency { .. }
            | VcKind::TypeRefinementViolation { .. }
            | VcKind::FrameConditionViolation { .. } => ProofLevel::L1Functional,
        }
    }

    /// Recovers the real obligation-kind tag of a native full-verification
    /// round-trip row.
    ///
    /// The full lane re-materializes a legacy VC as
    /// `UnsupportedMir { kind: "FullVerification::<ApiKind>", detail }` (see
    /// `legacy_unsupported_kind_detail` in `trust_verify.rs`): the coarse
    /// verifier-API family survives in `kind`, and the ORIGINAL
    /// `VcKind::description()` text survives as the leading segment of `detail`
    /// (optional `; contract_id=` / `; metadata_keys=` suffixes follow it).
    ///
    /// SINGLE SOURCE OF TRUTH for the family/detail → tag mapping: the
    /// transport display recovery in `trust_verify.rs` (`format_vc_kind` /
    /// `recovered_full_lane_vc_tag`) and the effective-kind runtime fallback
    /// ([`VcKind::has_runtime_fallback`]) must both answer from this mapping —
    /// do not fork it. The recovered tag is exactly the tag `format_vc_kind`
    /// gives the pre-round-trip `VcKind` (`overflow:add`, `bounds`, `divzero`,
    /// `assert`, `unreach`, …).
    ///
    /// Each detail prefix is CROSS-CHECKED against the verifier-API family the
    /// original `VcKind` actually routes through (`vc_obligation_kind` in
    /// trust-mir-extract), so a stray description can never relabel a row
    /// across families. Every prefix is anchored at the start of `detail`, so
    /// e.g. `division by zero` can never fire on `float division by zero`.
    /// Anything unrecognized returns `None` — fail-closed.
    #[must_use]
    pub fn recovered_full_lane_vc_tag(kind: &str, detail: &str) -> Option<&'static str> {
        let family = kind.strip_prefix(Self::FULL_VERIFICATION_KIND_PREFIX)?;
        let tag = match family {
            "ArithmeticSafety" => {
                if detail.starts_with("arithmetic overflow (Add)") {
                    "overflow:add"
                } else if detail.starts_with("arithmetic overflow (Sub)") {
                    "overflow:sub"
                } else if detail.starts_with("arithmetic overflow (Mul)") {
                    "overflow:mul"
                } else if detail.starts_with("arithmetic overflow (Div)") {
                    "overflow:div"
                } else if detail.starts_with("arithmetic overflow (Rem)") {
                    "overflow:rem"
                } else if detail.starts_with("arithmetic overflow") {
                    "overflow"
                } else if detail.starts_with("shift overflow (Shl)") {
                    "shift:left"
                } else if detail.starts_with("shift overflow (Shr)") {
                    "shift:right"
                } else if detail.starts_with("shift overflow") {
                    "shift"
                } else if detail.starts_with("division by zero") {
                    "divzero"
                } else if detail.starts_with("remainder by zero") {
                    "remzero"
                } else if detail.starts_with("float division by zero") {
                    "float_division_by_zero"
                } else if detail.starts_with("float overflow to infinity") {
                    "float_overflow_to_infinity"
                } else if detail.starts_with("cast overflow") {
                    "cast"
                } else if detail.starts_with("negation overflow") {
                    "negation"
                } else {
                    return None;
                }
            }
            "BoundsCheck" => {
                if detail.starts_with("index out of bounds") {
                    "bounds"
                } else if detail.starts_with("slice bounds check") {
                    "slice"
                } else {
                    return None;
                }
            }
            "Assertion" => {
                if detail.starts_with("assertion: ") {
                    "assert"
                } else if detail.starts_with("unreachable code reached") {
                    "unreach"
                } else {
                    return None;
                }
            }
            "Precondition" if detail.starts_with("precondition of `") => "precond",
            "Postcondition" if detail.starts_with("postcondition") => "postcond",
            "TemporalSafety" => {
                if detail.starts_with("dead state `") {
                    "deadstate"
                } else if detail.starts_with("deadlock") {
                    "deadlock"
                } else if detail.starts_with("temporal: ") {
                    "temporal"
                } else if detail.starts_with("fairness: ") {
                    "fairness"
                } else {
                    return None;
                }
            }
            "Liveness" if detail.starts_with("liveness: ") => "liveness",
            "Protocol" if detail.starts_with("protocol `") => "protocol",
            "Refinement" if detail.starts_with("refinement violation: ") => "refinement",
            "Termination" if detail.starts_with("non-termination: ") => "termination",
            // Custom-routed kinds carry their precise `vc_kind_label` slug INSIDE
            // the round-trip kind string itself (`FullVerification::trust.vc::
            // <label>`) — the strongest survivor; no description cross-check is
            // needed. `trust.vc::unsupported_mir` (a genuine unsupported-MIR VC)
            // deliberately has no arm: it never had a real kind to recover.
            "trust.vc::taint_violation" => "taint",
            "trust.vc::resilience_violation" => "resilience",
            _ => return None,
        };
        Some(tag)
    }

    /// Returns whether the generated program provably RETAINS a runtime check
    /// for this VC kind — i.e. whether an unproved obligation of this kind is
    /// still dynamically guarded.
    ///
    /// CONTRACT: `true` is a POSITIVE SAFETY CLAIM, and every consumer reads it
    /// that way. `classify_runtime_disposition` (result.rs) uses it to downgrade
    /// an `Unknown`/`Timeout` row to `RuntimeChecked` under
    /// `RuntimeCheckPolicy::Auto`, which reads to the user as "covered"; the
    /// residual-gap scan in `trust_verify.rs` uses it to decide a gap is
    /// tolerable. So `true` must mean the monitor DEMONSTRABLY exists for every
    /// obligation this arm can be reached by. Answer `false` whenever the kind
    /// cannot decide that — an over-reported `Unknown` is a lost recovery, an
    /// under-reported one is a false safety claim, and only the latter is UB.
    ///
    /// `VcKind::Unreachable` is therefore `false`, despite three of its four
    /// mint sites being panic-backed. It is a UNIT variant carrying no
    /// provenance, and `v2_build_terminator_vc`
    /// (trust-vcgen/src/generate/overflow_vc.rs) mints it from four physically
    /// different terminators: a bare `Terminator::Unreachable`, which
    /// rustc_codegen_ssa lowers straight to `llvm.unreachable` with NO check
    /// emitted (`rustc_codegen_ssa/src/mir/block.rs`), plus three
    /// `Terminator::Call` panic shapes that do keep one. The two shapes are
    /// indistinguishable downstream, so this arm cannot tell them apart and
    /// fails closed for all of them.
    ///
    /// `VcKind::HardenedBoundary` answers `false` for the WHOLE family, including
    /// the `mir_assert::*` panic subfamily raised over a rustc-inserted `Assert`.
    /// That is not an under-report, because THIS predicate is not asking whether
    /// a check exists at the site — it is asking whether THE PROPERTY THIS
    /// OBLIGATION ASSERTS is enforced dynamically. A hardened panic boundary
    /// asserts that the panic is UNREACHABLE, and `panic_bounds_check` does not
    /// enforce unreachability: it IS the panic. The check surviving codegen is
    /// exactly what the boundary is complaining about, so it can never discharge
    /// it, and answering `true` here would make
    /// [`crate::classify_runtime_disposition_in`] relabel an unproved hardened
    /// row `RuntimeChecked` — "will be enforced dynamically at runtime" — about a
    /// property nothing enforces.
    ///
    /// The DIFFERENT, narrower question — "does the operation this obligation
    /// stands over still carry rustc's own dynamic check?" — is real, is MEASURED
    /// (byte-identical LLVM IR with and without `-Ztrust-verify-profile=unix_hardened`),
    /// and has its own name: [`VcKind::site_retains_language_check_in`]. Ask that
    /// one when you want the fact; ask this one when you want to know whether the
    /// obligation is covered. They are a strict superset / subset pair, and
    /// keeping them apart is what stops a factual measurement from silently
    /// becoming a safety claim in every report the tree prints.
    ///
    /// FAIL-CLOSED ADAPTER. This spelling knows only `overflow_checks`, so it
    /// answers as if `ub_checks` were OFF — see
    /// [`RuntimeCheckEnv::overflow_checks_only`]. Every kind whose guard is
    /// `ub_checks`-gated (`get_unchecked`, `unchecked_{add,sub,mul}`) therefore
    /// answers `false` here regardless of the real session setting. That is the
    /// safe direction: threading the real `Session::ub_checks()` through
    /// [`VcKind::has_runtime_fallback_in`] can only ADD fallbacks.
    #[must_use]
    pub fn has_runtime_fallback(&self, overflow_checks: bool) -> bool {
        self.has_runtime_fallback_in(RuntimeCheckEnv::overflow_checks_only(overflow_checks))
    }

    /// [`VcKind::has_runtime_fallback`] against the FULL check environment.
    ///
    /// Read the contract on `has_runtime_fallback` first — it applies verbatim.
    /// This is the spelling that can answer for the unchecked-UB family, whose
    /// guard is gated on `ub_checks` and not on `overflow_checks`; see
    /// [`RuntimeCheckEnv`] for the measured table.
    #[must_use]
    pub fn has_runtime_fallback_in(&self, env: RuntimeCheckEnv) -> bool {
        match self {
            VcKind::ArithmeticOverflow { .. }
            | VcKind::ShiftOverflow { .. }
            | VcKind::NegationOverflow { .. } => env.overflow_checks,
            // `unchecked_{add,sub,mul}` lower to `add nsw`/`nuw` with NO branch;
            // `get_unchecked` lowers to a bare `getelementptr`. Neither is gated
            // on `overflow_checks` at any value — the sole guard either can have
            // is the `ub_checks`-gated `assert_unsafe_precondition!`, which is
            // compiled out of every release build.
            VcKind::UncheckedArithmeticOverflow { .. }
            | VcKind::UncheckedIndexBounds { .. } => env.ub_checks,
            // Trust: the separation engine mints its unsafe-operation
            // obligations as `Assertion`s tagged `[unsafe:sep:<op>]`
            // (trust-vcgen/src/sep_engine.rs — the ONLY producer of this
            // prefix): double-free, `Vec::set_len` past capacity, `ptr::offset`
            // out of its allocation, `NonZero::new_unchecked(0)`,
            // `from_utf8_unchecked` on non-UTF-8, `assume_init` on uninit
            // memory, `alloc` returning null. Rust inserts NO check for ANY of
            // them; they are obligations precisely BECAUSE the language does not
            // watch them. Falling into the `Assertion => true` arm below — which
            // is earned by a rustc-inserted `Assert` terminator or an `assert!`
            // panic call — reported the whole separation-engine unsafe output as
            // monitored. It also contradicted the typed spellings of the very
            // same properties: `VcKind::DoubleFree`, `VcKind::UnsafeOperation`
            // and `VcKind::HardenedBoundary { UnsafeOperation }` all answer
            // `false`, and `hardened_category()` already classifies these rows as
            // `UnsafeOperation`. Anchored at the start, matching the mint format.
            VcKind::Assertion { message }
                if message.starts_with(Self::SEP_UNSAFE_ASSERTION_PREFIX) =>
            {
                false
            }
            // Trust (2026-09-16, refuted at targo's publication boundary): the
            // carve-out above was the ONLY one, so every other lane-tagged
            // synthetic assertion answered `true` — `[unsafe:deref]`, `[unsafe]`,
            // `[unsafe:ffi]`, `[unsafe:sep]` (no trailing colon — the
            // separation_logic mint), `[unsafe:asm]`, `[unsafe:unmodeled-call]`
            // and `[provenance]` — although rustc emits no check for any of
            // them: `hardened_category()` already classifies the whole
            // `[unsafe…]` family as UnsafeOperation/FfiBoundary, and a
            // provenance row is a use-after-free/dangling claim. A `true` here
            // is what lets an UNPROVED such row be labelled runtime-checked (the
            // compiler's wire arm and policy-B denier, and targo's policy-B
            // relabel of an evidence-free `Proved`). Answer as the typed
            // spellings of the same properties do.
            VcKind::Assertion { message }
                if self.hardened_category().is_some()
                    || message.starts_with(Self::PROVENANCE_ASSERTION_PREFIX) =>
            {
                false
            }
            VcKind::DivisionByZero
            | VcKind::RemainderByZero
            | VcKind::IndexOutOfBounds
            | VcKind::SliceBoundsCheck
            | VcKind::Assertion { .. } => true,
            // Effective-kind runtime fallback: a native full-lane round-trip
            // row (`FullVerification::<ApiKind>`) is an obligation whose
            // underlying operation KEEPS its physical runtime check — checks
            // are elided only for Proved-with-authority obligations, which an
            // `UnsupportedMir` row by construction is not. Recover the
            // effective kind through the same single-sourced mapping the
            // transport display already trusts and answer per that kind's own
            // arm above/below. Fail-closed: a detail that does not map exactly
            // — including every non-`FullVerification::` kind, such as the
            // `assumption:<tag>` rows targo folds into `UnsupportedMir`
            // precisely so they get NO fallback — keeps `false`.
            VcKind::UnsupportedMir { kind, detail } => {
                match Self::recovered_full_lane_vc_tag(kind, detail) {
                    // ArithmeticOverflow / ShiftOverflow / NegationOverflow arms.
                    Some(
                        "overflow:add" | "overflow:sub" | "overflow:mul" | "overflow:div"
                        | "overflow:rem" | "overflow" | "shift:left" | "shift:right" | "shift"
                        | "negation",
                    ) => env.overflow_checks,
                    // DivisionByZero / RemainderByZero / IndexOutOfBounds /
                    // SliceBoundsCheck arms.
                    Some("divzero" | "remzero" | "bounds" | "slice") => true,
                    // The `assert` tag must answer EXACTLY what the direct
                    // `Assertion` arm answers, INCLUDING its `[unsafe:sep:`
                    // decline — otherwise a round-trip launders a
                    // separation-engine unsafe obligation back into a fallback
                    // that arm refused. `recovered_full_lane_vc_tag` produces
                    // `assert` only from a `detail` starting `"assertion: "`,
                    // which is `VcKind::Assertion`'s own `description()`, so
                    // stripping that prefix recovers the original message.
                    // (Today `vc_obligation_kind` routes these rows through the
                    // hardened namespace instead, so this arm is belt-and-braces
                    // — it is here so the two stay in lock-step if that routing
                    // changes, exactly as the `unreach` note below requires.)
                    Some("assert") => !detail
                        .strip_prefix("assertion: ")
                        .unwrap_or(detail.as_str())
                        .starts_with(Self::SEP_UNSAFE_ASSERTION_PREFIX),
                    // Every other recovered family (`unreach`/cast/precond/
                    // postcond/float/temporal/…) answers `false` per its own arm,
                    // and an unrecovered detail stays fail-closed `false`.
                    // `unreach` belongs here and NOT above: it must answer
                    // exactly what the `VcKind::Unreachable` arm answers, or a
                    // round-tripped `FullVerification::Assertion` row would
                    // re-acquire a fallback that arm declined.
                    _ => false,
                }
            }
            // Bare `Terminator::Unreachable` compiles to `llvm.unreachable` with
            // no trap emitted, and the unit variant cannot distinguish that mint
            // from the panic-backed ones — fail closed. See the doc comment.
            VcKind::Unreachable
            | VcKind::CastOverflow { .. }
            // An authored invariant is a specification clause with no lowered
            // code behind it: `#[trust::invariant(..)]` is span-only (MEASURED —
            // byte-identical LLVM IR to the unannotated function), so it answers
            // `false` in lock-step with its `Requires`/`Ensures` siblings.
            | VcKind::ContractInvariant { .. }
            | VcKind::Precondition { .. }
            | VcKind::Postcondition
            | VcKind::ResilienceViolation { .. }
            | VcKind::DeadState { .. }
            | VcKind::Deadlock
            | VcKind::Temporal { .. }
            | VcKind::Liveness { .. }
            | VcKind::Fairness { .. }
            | VcKind::TaintViolation { .. }
            | VcKind::RefinementViolation { .. }
            | VcKind::ProtocolViolation { .. }
            | VcKind::NonTermination { .. }
            // No runtime checks for data races or ordering violations.
            | VcKind::DataRace { .. }
            | VcKind::InsufficientOrdering { .. }
            // Translation validation has no runtime fallback.
            | VcKind::TranslationValidation { .. }
            // Float ops silently produce Inf/NaN per IEEE 754 — no runtime check.
            | VcKind::FloatDivisionByZero
            | VcKind::FloatOverflowToInfinity { .. } => false,
            // No runtime checks for type-level safety VCs.
            | VcKind::InvalidDiscriminant { .. }
            | VcKind::AggregateArrayLengthMismatch { .. }
            // No runtime check for unsafe operations.
            | VcKind::UnsafeOperation { .. }
            | VcKind::SavedReturnAddressOverwrite { .. }
            | VcKind::FormatStringViolation { .. }
            | VcKind::TaintedIndirectBranch { .. }
            | VcKind::BinaryAbiContradiction { .. }
            | VcKind::BinaryCopySinkLengthViolation { .. }
            // No runtime check for FFI boundary violations.
            | VcKind::FfiBoundaryViolation { .. }
            // The language does not bounds-check raw copies or externally-mutable
            // backing sizes — that absence is exactly why these are obligations.
            | VcKind::CopyBoundsViolation { .. }
            | VcKind::ExternallyMutableAllocationBounds { .. }
            // The language does not bound bulk-allocation sizes — that absence is
            // exactly why an unbounded allocation is an obligation, not a check.
            | VcKind::UnboundedAllocation { .. }
            // Ownership violations have no runtime check (UB in unsafe code).
            | VcKind::UseAfterFree
            | VcKind::DoubleFree
            | VcKind::AliasingViolation { .. }
            | VcKind::LifetimeViolation
            | VcKind::SendViolation
            | VcKind::SyncViolation
            // Functional correctness has no runtime fallback.
            | VcKind::FunctionalCorrectness { .. }
            // A typed body decline has no language-inserted guard. Only an
            // independently certified, source-bound monitor may enforce it.
            | VcKind::DeclinedContractBody(_)
            // EVERY hardened boundary, without exception. A hardening-profile
            // boundary asserts that a panic is UNREACHABLE. For the `unwrap` /
            // `expect` / `std::fs::rename` / `chroot` half the language inserts
            // nothing at the site at all. For the `mir_assert::*` half the
            // language DOES insert a check — and that check is the panic the
            // boundary is objecting to, so it cannot discharge the obligation
            // either. Both halves answer `false` HERE; the measured fact about
            // the second half is served by
            // [`VcKind::site_retains_language_check_in`], under its own name.
            | VcKind::HardenedBoundary { .. }
            // trust_wp contract VCs have no runtime fallback.
            | VcKind::LoopInvariantInitiation { .. }
            | VcKind::LoopInvariantConsecution { .. }
            | VcKind::LoopInvariantSufficiency { .. }
            | VcKind::TypeRefinementViolation { .. }
            | VcKind::FrameConditionViolation { .. }
            // No rustc-inserted check enforces a struct invariant: an Unknown TINV row
            // must never be relabelled RuntimeChecked.
            | VcKind::TypeInvariant { .. } => false,
        }
    }

    /// Does the generated program still execute a rustc-inserted dynamic check
    /// AT THIS OBLIGATION'S SITE — whether or not that check DISCHARGES the
    /// obligation?
    ///
    /// A DIFFERENT QUESTION FROM [`VcKind::has_runtime_fallback_in`], and the
    /// distinction is the whole reason this method exists. `has_runtime_fallback_in`
    /// asks whether THE PROPERTY THE OBLIGATION ASSERTS is enforced dynamically,
    /// and its `true` is a POSITIVE SAFETY CLAIM that
    /// [`crate::classify_runtime_disposition_in`] turns into a `RuntimeChecked`
    /// label reading "will be enforced dynamically at runtime". This method asks
    /// only whether rustc's own guard is still in the binary at that spot. For
    /// every kind except one the two coincide. They come apart on
    /// `HardenedBoundary { PanicBoundary, callee: "mir_assert::…" }`:
    ///
    /// * the `Assert` rustc emitted IS still in the program — MEASURED 2026-09-18
    ///   with `trustc 1.99.0-dev (ba1b42178)`: `--emit=llvm-ir` over a fixture
    ///   with an `a + b`, a `v[i]` and an `Option::unwrap` is BYTE-IDENTICAL with
    ///   and without `-Ztrust-verify-profile=unix_hardened` (sha256
    ///   9b196065a05bc5d4c66fb763d7ebbc217a89079657d4f43ebac0b39a43d2b198 for
    ///   both), retaining `llvm.sadd.with.overflow.i32` +
    ///   `panic_const_add_overflow`, `panic_bounds_check` and `unwrap_failed`.
    ///   `-Ztrust-verify-profile` has exactly ONE consumer in the compiler
    ///   (`hardened_verification_enabled`, rustc_mir_transform/src/trust_verify.rs)
    ///   and it only decides whether vcgen EMITS obligations. So the answer HERE
    ///   is `true`;
    /// * but the obligation that boundary raises is "this panic is UNREACHABLE",
    ///   and that surviving `Assert` is the panic itself. It cannot discharge the
    ///   obligation, so `has_runtime_fallback_in` stays `false` — see its own
    ///   contract.
    ///
    /// STRICT SUPERSET, pinned by a test over every variant and every
    /// [`RuntimeCheckEnv`]: `has_runtime_fallback_in(env)` implies
    /// `site_retains_language_check_in(env)`, and the only place the implication
    /// is not an equality is that subfamily.
    ///
    /// WHO MAY ASK THIS. A caller that wants to know whether a REFUTED obligation
    /// still has the language's guard behind it, and that carries its own reason
    /// for treating the guard as sufficient. Today exactly one does: targo's
    /// `--test-target-panics=runtime-checked`, an explicit flag with no default
    /// and no environment variable, which applies only inside a cargo `["test"]`
    /// target — where the panic is the test's INTENDED failure signal, so "the
    /// panic still fires" is the answer it wants rather than the answer it
    /// refuses. It layers a narrower policy on top
    /// (`targo-trust/src/test_target_panics.rs`). Any new caller must state the
    /// same kind of reason: this method reports a FACT and confers no coverage.
    #[must_use]
    pub fn site_retains_language_check_in(&self, env: RuntimeCheckEnv) -> bool {
        if self.has_runtime_fallback_in(env) {
            return true;
        }
        match self {
            // The ONLY place the two questions come apart. Recovered through
            // [`hardened_mir_assert_guard`], never guessed from the category, and
            // the answer is EXACTLY what the underlying operation's own
            // `has_runtime_fallback_in` arm answers: unconditional for
            // `BoundsCheck` / `DivisionByZero` / `RemainderByZero`,
            // `env.overflow_checks` for `Overflow(..)` / `OverflowNeg`.
            VcKind::HardenedBoundary {
                category: HardenedVcCategory::PanicBoundary,
                callee,
                ..
            } => match hardened_mir_assert_guard(callee) {
                Some(MirAssertGuard::Unconditional) => true,
                Some(MirAssertGuard::OverflowChecked) => env.overflow_checks,
                None => false,
            },
            _ => false,
        }
    }
}

// Display delegates to description() so `.to_string()` works in tests.
impl std::fmt::Display for VcKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.description())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::model::AssertMessage;

    /// The operand type these tests use; `has_runtime_fallback_in` never reads
    /// it, so one signed 32-bit integer stands for every arithmetic row.
    const I32: Ty = Ty::Int { width: 32, signed: true };

    /// Build the hardened boundary `trust_vcgen::hardened`'s assert lane mints
    /// for `msg`, using the SAME `format!("mir_assert::{msg:?}")` spelling, so
    /// these tests pin the recognizer to the real `Debug` rendering rather than
    /// to a hand-typed copy of it. A rename of any `AssertMessage` variant
    /// breaks these tests instead of silently retiring a subfamily.
    fn hardened_assert_boundary(msg: &AssertMessage) -> VcKind {
        VcKind::HardenedBoundary {
            category: HardenedVcCategory::PanicBoundary,
            callee: format!("mir_assert::{msg:?}"),
            detail: "MIR assert can panic; hardened code needs a proved precondition".to_string(),
        }
    }

    /// A hardened boundary raised over a CALL, which is what every CALL_RULE in
    /// `trust_vcgen::hardened` produces.
    fn hardened_call_boundary(category: HardenedVcCategory, callee: &str) -> VcKind {
        VcKind::HardenedBoundary {
            category,
            callee: callee.to_string(),
            detail: "hardened boundary".to_string(),
        }
    }

    const ENVS: [RuntimeCheckEnv; 4] = [
        RuntimeCheckEnv::new(false, false),
        RuntimeCheckEnv::new(false, true),
        RuntimeCheckEnv::new(true, false),
        RuntimeCheckEnv::new(true, true),
    ];

    /// THE POSITIVE DIRECTION, family by family: for
    /// [`VcKind::site_retains_language_check_in`] — "is rustc's own guard still
    /// at this site" — a hardened panic boundary over a rustc-inserted assert
    /// answers EXACTLY what the primary obligation over the same operation
    /// answers, in every check environment.
    ///
    /// Stated as an equality against the primary arm rather than as a literal,
    /// because the claim being pinned is lock-step — if someone ever changes
    /// what `ArithmeticOverflow` answers, the twin must move with it.
    ///
    /// THE SAME LOOP PINS `has_runtime_fallback_in` AT `false` for every one of
    /// these boundaries. That is the separation this test exists to hold: the
    /// guard is there (so the flag may consult it) and the obligation is still
    /// undischarged (so no report may call it covered). Collapsing the two is
    /// the regression a reviewer MEASURED through `trust_report::build_json_report`
    /// — a `Timeout` hardened row came back as `Unknown`, with no flag involved.
    #[test]
    fn hardened_mir_assert_boundary_answers_exactly_its_primary_sibling_arm() {
        let pairs: Vec<(AssertMessage, VcKind)> = vec![
            (AssertMessage::BoundsCheck, VcKind::IndexOutOfBounds),
            (AssertMessage::BoundsCheck, VcKind::SliceBoundsCheck),
            (AssertMessage::DivisionByZero, VcKind::DivisionByZero),
            (AssertMessage::RemainderByZero, VcKind::RemainderByZero),
            (
                AssertMessage::Overflow(BinOp::Add),
                VcKind::ArithmeticOverflow { op: BinOp::Add, operand_tys: (I32, I32) },
            ),
            (
                AssertMessage::Overflow(BinOp::Sub),
                VcKind::ArithmeticOverflow { op: BinOp::Sub, operand_tys: (I32, I32) },
            ),
            (
                AssertMessage::Overflow(BinOp::Mul),
                VcKind::ArithmeticOverflow { op: BinOp::Mul, operand_tys: (I32, I32) },
            ),
            (
                AssertMessage::Overflow(BinOp::Shl),
                VcKind::ShiftOverflow { op: BinOp::Shl, operand_ty: I32, shift_ty: I32 },
            ),
            (
                AssertMessage::Overflow(BinOp::Shr),
                VcKind::ShiftOverflow { op: BinOp::Shr, operand_ty: I32, shift_ty: I32 },
            ),
            (AssertMessage::OverflowNeg, VcKind::NegationOverflow { ty: I32 }),
        ];
        for (msg, primary) in pairs {
            let boundary = hardened_assert_boundary(&msg);
            for env in ENVS {
                assert_eq!(
                    boundary.site_retains_language_check_in(env),
                    primary.site_retains_language_check_in(env),
                    "hardened `mir_assert::{msg:?}` must answer exactly as {primary:?} in {env:?}"
                );
                assert!(
                    !boundary.has_runtime_fallback_in(env),
                    "`mir_assert::{msg:?}` keeps its guard, but the guard IS the panic it \
                     objects to — it can never DISCHARGE the boundary ({env:?})"
                );
            }
        }
    }

    /// The overflow subfamily is not unconditionally `true`: with
    /// `-C overflow-checks=no` rustc emits NO overflow `Assert` (MEASURED
    /// 2026-09-18: `trustc -C overflow-checks=no --emit=llvm-ir` over `a + b`
    /// contains zero `llvm.sadd.with.overflow` / `panic_const_add_overflow`),
    /// and the boundary must answer `false` there.
    #[test]
    fn hardened_mir_assert_overflow_boundary_declines_without_overflow_checks() {
        for msg in [
            AssertMessage::Overflow(BinOp::Add),
            AssertMessage::Overflow(BinOp::Sub),
            AssertMessage::Overflow(BinOp::Mul),
            AssertMessage::Overflow(BinOp::Shl),
            AssertMessage::Overflow(BinOp::Shr),
            AssertMessage::Overflow(BinOp::Div),
            AssertMessage::Overflow(BinOp::Rem),
            AssertMessage::OverflowNeg,
        ] {
            let boundary = hardened_assert_boundary(&msg);
            assert!(
                boundary.site_retains_language_check_in(RuntimeCheckEnv::new(true, false)),
                "`mir_assert::{msg:?}` keeps its guard under overflow checks"
            );
            assert!(
                !boundary.site_retains_language_check_in(RuntimeCheckEnv::new(false, true)),
                "`mir_assert::{msg:?}` has no guard with overflow checks off"
            );
        }
    }

    /// The bounds and zero-divisor asserts are emitted whatever the check
    /// settings are, so their boundaries answer `true` in every environment.
    #[test]
    fn hardened_mir_assert_unconditional_boundaries_keep_their_guard_everywhere() {
        for msg in [
            AssertMessage::BoundsCheck,
            AssertMessage::DivisionByZero,
            AssertMessage::RemainderByZero,
        ] {
            let boundary = hardened_assert_boundary(&msg);
            for env in ENVS {
                assert!(
                    boundary.site_retains_language_check_in(env),
                    "`mir_assert::{msg:?}` keeps its guard in {env:?}"
                );
            }
        }
    }

    /// THE NEGATIVE DIRECTION 1 — a panic boundary raised over a CALL. rustc
    /// inserts no check for `unwrap`/`expect`: the panic lives in the callee,
    /// which is why these are obligations at all. They must keep answering
    /// `false`, or this change would have laundered the whole CALL_RULE lane
    /// into a monitor claim.
    #[test]
    fn hardened_call_panic_boundaries_have_no_runtime_guard() {
        for callee in [
            "std::option::Option::<T>::unwrap",
            "std::result::Result::<T, E>::unwrap",
            "std::option::Option::<T>::expect",
            "core::result::Result::ok",
            "unwrap_or_default",
        ] {
            let boundary = hardened_call_boundary(HardenedVcCategory::PanicBoundary, callee);
            for env in ENVS {
                assert!(
                    !boundary.site_retains_language_check_in(env),
                    "`{callee}` is a call, not a rustc-inserted check ({env:?})"
                );
                assert!(
                    !boundary.has_runtime_fallback_in(env),
                    "`{callee}` discharges nothing either ({env:?})"
                );
            }
        }
    }

    /// THE NEGATIVE DIRECTION 2 — the marker is ANCHORED and EXACT. A callee
    /// that merely CONTAINS `mir_assert::`, or that names an `AssertMessage`
    /// this arm does not model, claims nothing.
    /// `hardened_mir_assert_callee` is the producer spelling (vcgen and the
    /// compiler's elision seam both call it) and `hardened_mir_assert_message`
    /// its exact inverse.
    #[test]
    fn hardened_mir_assert_callee_is_the_inverse_of_the_reader() {
        use crate::model::BinOp;
        for msg in [
            AssertMessage::Overflow(BinOp::Add),
            AssertMessage::Overflow(BinOp::Shr),
            AssertMessage::OverflowNeg,
            AssertMessage::BoundsCheck,
            AssertMessage::DivisionByZero,
            AssertMessage::RemainderByZero,
        ] {
            let callee = hardened_mir_assert_callee(&msg);
            assert_eq!(callee, format!("mir_assert::{msg:?}"));
            assert_eq!(hardened_mir_assert_message(&callee), Some(format!("{msg:?}").as_str()));
            assert!(hardened_mir_assert_guard(&callee).is_some(), "{callee}");
        }
    }

    #[test]
    fn hardened_mir_assert_marker_is_anchored_and_closed() {
        let refused = [
            // Not anchored: a real callee path that happens to embed the marker.
            "wrapper::mir_assert::Overflow(Add)",
            " mir_assert::Overflow(Add)",
            // Anchored but not a modeled message.
            "mir_assert::",
            "mir_assert::Overflow",
            "mir_assert::Overflow(",
            "mir_assert::OverflowSomething",
            "mir_assert::BoundsCheckExtra",
            // UB-class asserts: `ub_checks`-gated, not panics. Declined on
            // purpose — the lost-recovery direction, never a safety claim.
            "mir_assert::NullPointerDereference",
            "mir_assert::MisalignedPointerDereference",
            "mir_assert::InvalidEnumConstruction",
            // Coroutine resume-state family: adjudicated by its own contract.
            "mir_assert::ResumedAfterReturn",
            "mir_assert::ResumedAfterPanic",
            "mir_assert::ResumedAfterDrop",
        ];
        for callee in refused {
            assert!(hardened_mir_assert_guard(callee).is_none(), "`{callee}` must not be claimed");
            let boundary = hardened_call_boundary(HardenedVcCategory::PanicBoundary, callee);
            for env in ENVS {
                assert!(
                    !boundary.site_retains_language_check_in(env),
                    "`{callee}` must claim no guard in {env:?}"
                );
                assert!(!boundary.has_runtime_fallback_in(env));
            }
        }
        // `Custom(..)` renders with the message in it and is never claimed.
        let custom = hardened_assert_boundary(&AssertMessage::Custom("anything".to_string()));
        for env in ENVS {
            assert!(!custom.site_retains_language_check_in(env));
            assert!(!custom.has_runtime_fallback_in(env));
        }
    }

    /// THE NEGATIVE DIRECTION 3 — the CATEGORY gates the arm. The same
    /// `mir_assert::Overflow(Add)` callee under any other hardened category
    /// claims nothing, so a mis-categorized row cannot borrow the panic
    /// boundary's answer. `UnsafeOperation` is called out because the
    /// `--test-target-panics` policy layer refuses it by name as well.
    #[test]
    fn hardened_non_panic_categories_claim_no_guard_even_over_an_assert() {
        for category in [
            HardenedVcCategory::UnsafeOperation,
            HardenedVcCategory::FfiBoundary,
            HardenedVcCategory::RawPathApi,
            HardenedVcCategory::PathIdentity,
            HardenedVcCategory::ByteLoss,
            HardenedVcCategory::Utf8Reject,
            HardenedVcCategory::ErrorDiscard,
            HardenedVcCategory::TrustDomain,
            HardenedVcCategory::TrustDomainOrder,
            HardenedVcCategory::PermissionChange,
            HardenedVcCategory::PermissionCreate,
            HardenedVcCategory::PermissionWindow,
            HardenedVcCategory::CompatObservable,
            HardenedVcCategory::ProcessSemantics,
        ] {
            let boundary = hardened_call_boundary(category, "mir_assert::Overflow(Add)");
            for env in ENVS {
                assert!(
                    !boundary.site_retains_language_check_in(env),
                    "{category:?} must not borrow the panic-boundary answer ({env:?})"
                );
                assert!(!boundary.has_runtime_fallback_in(env));
            }
        }
    }

    /// THE LOCK. `has_runtime_fallback_in` answers `false` for EVERY
    /// `HardenedBoundary`, over the full cross product of every
    /// [`HardenedVcCategory`], every `AssertMessage` marker, every call-shaped
    /// callee and every [`RuntimeCheckEnv`].
    ///
    /// WHY THIS TEST EXISTS, from a real regression. Commit e4ae63e373 taught
    /// this predicate to answer the `mir_assert::*` panic subfamily `true`, on
    /// the measured and CORRECT ground that the hardening profile leaves rustc's
    /// `Assert` in the program. But this predicate is not asking whether a check
    /// exists — it is the sole gate on
    /// [`crate::classify_runtime_disposition_in`]'s `RuntimeChecked` relabel, so
    /// `true` here asserts that the OBLIGATION is dynamically enforced. A
    /// hardened boundary's obligation is that the panic is UNREACHABLE, which
    /// that surviving `Assert` does not enforce — it is the panic. A reviewer
    /// MEASURED the consequence through `trust_report::build_json_report` with no
    /// flag involved: a `HardenedBoundary { PanicBoundary,
    /// "mir_assert::BoundsCheck" }` carrying `VerificationResult::Timeout` came
    /// back as `ObligationOutcome::Unknown` instead of
    /// `ObligationOutcome::Timeout` (the `RuntimeChecked` relabel fired, then
    /// `sanitize_deserialized` scrubbed it to `Unknown` with a monitor-authority
    /// reason), losing `timeout_ms` and moving the crate's `total_timeout` /
    /// `total_unknown` counts.
    ///
    /// The fact is still available — under its own name,
    /// [`VcKind::site_retains_language_check_in`], pinned by the tests above.
    #[test]
    fn no_hardened_boundary_ever_claims_a_runtime_fallback() {
        let markers: Vec<String> = [
            AssertMessage::BoundsCheck,
            AssertMessage::Overflow(BinOp::Add),
            AssertMessage::Overflow(BinOp::Sub),
            AssertMessage::Overflow(BinOp::Mul),
            AssertMessage::Overflow(BinOp::Div),
            AssertMessage::Overflow(BinOp::Rem),
            AssertMessage::Overflow(BinOp::Shl),
            AssertMessage::Overflow(BinOp::Shr),
            AssertMessage::OverflowNeg,
            AssertMessage::DivisionByZero,
            AssertMessage::RemainderByZero,
            AssertMessage::ResumedAfterReturn,
            AssertMessage::ResumedAfterPanic,
            AssertMessage::ResumedAfterDrop,
            AssertMessage::MisalignedPointerDereference,
            AssertMessage::NullPointerDereference,
            AssertMessage::InvalidEnumConstruction,
            AssertMessage::Custom("anything".to_string()),
        ]
        .iter()
        .map(|msg| format!("mir_assert::{msg:?}"))
        .chain(
            [
                "std::option::Option::<T>::unwrap",
                "std::result::Result::<T, E>::expect",
                "std::fs::rename",
                "chroot",
                "wrapper::mir_assert::Overflow(Add)",
            ]
            .iter()
            .map(|c| (*c).to_string()),
        )
        .collect();

        let categories = [
            HardenedVcCategory::RawPathApi,
            HardenedVcCategory::PathIdentity,
            HardenedVcCategory::PermissionChange,
            HardenedVcCategory::PermissionCreate,
            HardenedVcCategory::PermissionWindow,
            HardenedVcCategory::Utf8Reject,
            HardenedVcCategory::ByteLoss,
            HardenedVcCategory::ErrorDiscard,
            HardenedVcCategory::PanicBoundary,
            HardenedVcCategory::CompatObservable,
            HardenedVcCategory::ProcessSemantics,
            HardenedVcCategory::TrustDomain,
            HardenedVcCategory::TrustDomainOrder,
            HardenedVcCategory::UnsafeOperation,
            HardenedVcCategory::FfiBoundary,
            HardenedVcCategory::Unknown(Symbol::from("something_new")),
        ];

        for category in categories {
            for callee in &markers {
                let boundary = hardened_call_boundary(category, callee);
                for env in ENVS {
                    assert!(
                        !boundary.has_runtime_fallback_in(env),
                        "a hardened boundary discharges nothing: {category:?} over `{callee}` \
                         in {env:?}"
                    );
                }
                // The fail-closed adapter must agree with the full-env spelling.
                assert!(!boundary.has_runtime_fallback(true));
                assert!(!boundary.has_runtime_fallback(false));
            }
        }
    }

    /// THE SUPERSET PROPERTY, and the exact place the two queries differ.
    ///
    /// `has_runtime_fallback_in(env)` implies `site_retains_language_check_in(env)`
    /// for every kind and every environment — a discharge claim always entails
    /// that the check is there. The converse fails on EXACTLY the
    /// `HardenedBoundary { PanicBoundary, "mir_assert::<modeled>" }` subfamily,
    /// and this test names that set so a future widening of either side has to
    /// come here and say so.
    #[test]
    fn site_check_is_a_strict_superset_of_runtime_fallback() {
        let mut kinds: Vec<VcKind> = vec![
            VcKind::IndexOutOfBounds,
            VcKind::SliceBoundsCheck,
            VcKind::DivisionByZero,
            VcKind::RemainderByZero,
            VcKind::ArithmeticOverflow { op: BinOp::Add, operand_tys: (I32, I32) },
            VcKind::ShiftOverflow { op: BinOp::Shl, operand_ty: I32, shift_ty: I32 },
            VcKind::NegationOverflow { ty: I32 },
            VcKind::Unreachable,
            VcKind::Postcondition,
            VcKind::Precondition { callee: "f".into() },
            VcKind::UnsafeOperation { desc: "raw deref".into() },
            VcKind::DoubleFree,
            VcKind::UseAfterFree,
            VcKind::FloatDivisionByZero,
            VcKind::Deadlock,
            VcKind::FunctionalCorrectness { property: "p".into(), context: "c".into() },
            VcKind::Assertion { message: "assert!(x)".into() },
            unchecked_add_kind(),
            unchecked_index_kind(),
            tinv_kind("crate::S", TypeInvariantPoint::Return, 3, 1),
        ];
        for msg in [
            AssertMessage::BoundsCheck,
            AssertMessage::DivisionByZero,
            AssertMessage::RemainderByZero,
            AssertMessage::Overflow(BinOp::Add),
            AssertMessage::OverflowNeg,
            AssertMessage::NullPointerDereference,
            AssertMessage::ResumedAfterPanic,
            AssertMessage::Custom("x".to_string()),
        ] {
            kinds.push(hardened_assert_boundary(&msg));
        }
        kinds.push(hardened_call_boundary(
            HardenedVcCategory::PanicBoundary,
            "std::option::Option::<T>::unwrap",
        ));
        kinds.push(hardened_call_boundary(
            HardenedVcCategory::UnsafeOperation,
            "mir_assert::Overflow(Add)",
        ));

        let mut differ: Vec<String> = Vec::new();
        for kind in &kinds {
            for env in ENVS {
                let discharges = kind.has_runtime_fallback_in(env);
                let site = kind.site_retains_language_check_in(env);
                assert!(
                    !discharges || site,
                    "a discharge claim entails the check is there: {kind:?} in {env:?}"
                );
                if discharges != site {
                    differ.push(format!("{kind:?}"));
                }
            }
        }
        differ.sort();
        differ.dedup();
        // Every entry — and ONLY these — is a hardened panic boundary over a
        // modeled `mir_assert::` marker.
        assert!(!differ.is_empty(), "the two queries must actually differ somewhere");
        for row in &differ {
            assert!(
                row.contains("HardenedBoundary")
                    && row.contains("PanicBoundary")
                    && row.contains("mir_assert::"),
                "only the hardened mir_assert panic subfamily may differ; got {row}"
            );
        }
    }

    #[test]
    fn saved_return_address_overwrite_is_l0_without_runtime_fallback() {
        let kind = VcKind::SavedReturnAddressOverwrite {
            access_width_bytes: 8,
            slot: "saved_return_address".to_string(),
        };

        assert_eq!(kind.proof_level(), ProofLevel::L0Safety);
        assert!(!kind.has_runtime_fallback(true));
        assert!(!kind.has_runtime_fallback(false));
        assert!(kind.description().contains("saved return address overwrite"));
    }

    #[test]
    fn format_string_violation_is_l0_without_runtime_fallback() {
        let kind = VcKind::FormatStringViolation {
            callee: "printf".to_string(),
            evidence: "format argument is symbolic".to_string(),
        };

        assert_eq!(kind.proof_level(), ProofLevel::L0Safety);
        assert!(!kind.has_runtime_fallback(true));
        assert!(!kind.has_runtime_fallback(false));
        assert!(kind.description().contains("format string violation"));
    }

    #[test]
    fn tainted_indirect_branch_is_l0_without_runtime_fallback() {
        let kind = VcKind::TaintedIndirectBranch {
            sink_kind: "indirect_branch".to_string(),
            target: "unresolved_indirect_target".to_string(),
            evidence: "target taint unavailable".to_string(),
        };

        assert_eq!(kind.proof_level(), ProofLevel::L0Safety);
        assert!(!kind.has_runtime_fallback(true));
        assert!(!kind.has_runtime_fallback(false));
        assert!(kind.description().contains("tainted indirect control flow"));
    }

    #[test]
    fn binary_abi_contradiction_is_l0_without_runtime_fallback() {
        let kind = VcKind::BinaryAbiContradiction {
            fact: "parameter 0 storage".to_string(),
            evidence: "ABI says RDI, storage says RSI".to_string(),
        };

        assert_eq!(kind.proof_level(), ProofLevel::L0Safety);
        assert!(!kind.has_runtime_fallback(true));
        assert!(!kind.has_runtime_fallback(false));
        assert!(kind.description().contains("binary ABI contradiction"));
    }

    #[test]
    fn binary_copy_sink_length_violation_is_l0_without_runtime_fallback() {
        let kind = VcKind::BinaryCopySinkLengthViolation {
            callee: "memcpy".to_string(),
            desc: "copy sink length may exceed destination capacity".to_string(),
        };

        assert_eq!(kind.proof_level(), ProofLevel::L0Safety);
        assert!(!kind.has_runtime_fallback(true));
        assert!(!kind.has_runtime_fallback(false));
        assert!(kind.description().contains("binary copy-sink length violation"));
        assert_eq!(
            kind.binary_copy_sink_length_family_tag(),
            Some(VcKind::BINARY_COPY_SINK_LENGTH_FAMILY)
        );
    }

    #[test]
    fn legacy_ffi_copy_sink_rows_keep_stable_family_classifier() {
        let legacy = VcKind::FfiBoundaryViolation {
            callee: "strncpy".to_string(),
            desc: "copy sink length for `strncpy` lacks destination capacity".to_string(),
        };
        let ordinary_ffi = VcKind::FfiBoundaryViolation {
            callee: "malloc".to_string(),
            desc: "return contract may be null".to_string(),
        };

        assert!(legacy.is_binary_copy_sink_length_violation());
        assert_eq!(
            legacy.binary_copy_sink_length_family_tag(),
            Some(VcKind::BINARY_COPY_SINK_LENGTH_FAMILY)
        );
        assert!(!ordinary_ffi.is_binary_copy_sink_length_violation());
        assert_eq!(ordinary_ffi.binary_copy_sink_length_family_tag(), None);
    }

    /// Trust (2026-09-16): every lane-tagged synthetic assertion that encodes
    /// UB — the whole `[unsafe…]` family `hardened_category()` classifies, plus
    /// `[provenance]` — has NO runtime fallback at any setting; only a real
    /// panic-class assertion (a user `assert!`, the whole-function
    /// panic-freedom row) keeps one. Refuted at targo's publication boundary:
    /// `[unsafe:deref] null check for *p` answered `true` and would have been
    /// published runtime-checked under policy B.
    #[test]
    fn unsafe_tagged_synthetic_assertions_keep_no_runtime_fallback() {
        let no_fallback = [
            "[unsafe:deref] null check for *p",
            "[unsafe] null pointer check for: p",
            "[unsafe:ffi] null pointer argument check for getenv",
            "[unsafe:sep] heap precondition for unsafe block in f",
            "[unsafe:sep:double-free] x in f",
            "[unsafe:asm] inline assembly is not modeled",
            "[unsafe:unmodeled-call] callee not modeled",
            "[unsafe:transmute] layout check",
            "[provenance] use-after-free: x",
        ];
        for message in no_fallback {
            let kind = VcKind::Assertion { message: message.to_string() };
            for env in [
                RuntimeCheckEnv { overflow_checks: false, ub_checks: false },
                RuntimeCheckEnv { overflow_checks: true, ub_checks: true },
            ] {
                assert!(!kind.has_runtime_fallback_in(env), "{message} at {env:?}");
            }
        }
        // Controls: a real panic-class assertion keeps its fallback at every
        // setting, and a user message that merely CONTAINS a tag is untouched.
        for message in [
            "panic freedom: no assertion, `unreachable!`, or panic is reachable",
            "x > 0",
            "see [unsafe] docs",
        ] {
            let kind = VcKind::Assertion { message: message.to_string() };
            assert!(kind.has_runtime_fallback_in(RuntimeCheckEnv {
                overflow_checks: false,
                ub_checks: false
            }));
        }
    }

    #[test]
    fn hardened_boundary_is_l1_without_runtime_fallback() {
        let kind = VcKind::HardenedBoundary {
            category: HardenedVcCategory::RawPathApi,
            callee: "std::fs::remove_file".to_string(),
            detail: "path removal re-resolves a mutable direntry".to_string(),
        };

        assert_eq!(kind.proof_level(), ProofLevel::L1Functional);
        assert!(!kind.has_runtime_fallback(true));
        assert_eq!(kind.hardened_category(), Some(HardenedVcCategory::RawPathApi));
        assert_eq!(kind.hardened_family_tag().as_deref(), Some("hardened_raw_path_api"));
        assert!(kind.description().contains("hardened boundary"));
    }

    #[test]
    fn all_hardened_categories_roundtrip_and_classify() {
        let cases = [
            (HardenedVcCategory::RawPathApi, "raw_path_api", ProofLevel::L1Functional),
            (HardenedVcCategory::PathIdentity, "path_identity", ProofLevel::L1Functional),
            (HardenedVcCategory::PermissionChange, "permission_change", ProofLevel::L1Functional),
            (HardenedVcCategory::PermissionCreate, "permission_create", ProofLevel::L1Functional),
            (HardenedVcCategory::PermissionWindow, "permission_window", ProofLevel::L1Functional),
            (HardenedVcCategory::Utf8Reject, "utf8_reject", ProofLevel::L1Functional),
            (HardenedVcCategory::ByteLoss, "byte_loss", ProofLevel::L1Functional),
            (HardenedVcCategory::ErrorDiscard, "error_discard", ProofLevel::L1Functional),
            (HardenedVcCategory::PanicBoundary, "panic_boundary", ProofLevel::L1Functional),
            (HardenedVcCategory::CompatObservable, "compat_observable", ProofLevel::L1Functional),
            (HardenedVcCategory::ProcessSemantics, "process_semantics", ProofLevel::L1Functional),
            (HardenedVcCategory::TrustDomain, "trust_domain", ProofLevel::L1Functional),
            (HardenedVcCategory::TrustDomainOrder, "trust_domain_order", ProofLevel::L1Functional),
            (HardenedVcCategory::UnsafeOperation, "unsafe_operation", ProofLevel::L0Safety),
            (HardenedVcCategory::FfiBoundary, "ffi_boundary", ProofLevel::L0Safety),
        ];

        for (category, tag, level) in cases {
            assert_eq!(category.as_tag(), tag);
            assert_eq!(HardenedVcCategory::from_tag(tag), Some(category));

            let kind = VcKind::HardenedBoundary {
                category,
                callee: "fixture".into(),
                detail: "detail".into(),
            };
            assert_eq!(kind.hardened_category(), Some(category));
            assert_eq!(kind.hardened_family_tag(), Some(format!("hardened_{tag}")));
            assert_eq!(kind.proof_level(), level);
            assert!(!kind.has_runtime_fallback(true));
            assert!(!kind.has_runtime_fallback(false));
        }

        assert_eq!(HardenedVcCategory::from_tag(""), None);
    }

    #[test]
    fn future_hardened_category_deserializes_as_unknown() {
        let kind: VcKind = serde_json::from_str(
            r#"{
                "HardenedBoundary": {
                    "category": "future_kernel_object_identity",
                    "callee": "openat2",
                    "detail": "future hardened category should stay fail-closed"
                }
            }"#,
        )
        .expect("future hardened category should deserialize through Unknown");

        match kind {
            VcKind::HardenedBoundary { category, callee, detail } => {
                assert!(category.is_unknown());
                assert_eq!(category.as_tag(), "future_kernel_object_identity");
                assert_eq!(callee, "openat2");
                assert!(detail.contains("future hardened category"));
            }
            other => panic!("expected hardened boundary, got {other:?}"),
        }
    }

    #[test]
    fn legacy_hardened_functional_correctness_rows_classify() {
        let legacy = VcKind::FunctionalCorrectness {
            property: "hardened::byte_loss".to_string(),
            context: "to_string_lossy: lossy OS/path conversion".to_string(),
        };
        let ordinary = VcKind::FunctionalCorrectness {
            property: "result_correctness".to_string(),
            context: "binary_search postcondition".to_string(),
        };

        assert_eq!(legacy.hardened_category(), Some(HardenedVcCategory::ByteLoss));
        assert_eq!(legacy.hardened_family_tag().as_deref(), Some("hardened_byte_loss"));
        assert_eq!(ordinary.hardened_category(), None);
        assert_eq!(ordinary.hardened_family_tag(), None);
    }

    #[test]
    fn legacy_future_hardened_functional_correctness_rows_preserve_tag() {
        let legacy = VcKind::FunctionalCorrectness {
            property: "hardened::future_kernel_object_identity".to_string(),
            context: "future hardened row".to_string(),
        };

        let category = legacy.hardened_category().expect("future hardened category");
        assert!(category.is_unknown());
        assert_eq!(category.as_tag(), "future_kernel_object_identity");
        assert_eq!(
            legacy.hardened_family_tag().as_deref(),
            Some("hardened_future_kernel_object_identity")
        );
    }

    #[test]
    fn ffi_boundary_is_native_hardened_category() {
        let kind = VcKind::HardenedBoundary {
            category: HardenedVcCategory::FfiBoundary,
            callee: "extern \"C\"::strlen".to_string(),
            detail: "trusted wrapper contract required".to_string(),
        };

        assert_eq!(kind.proof_level(), ProofLevel::L0Safety);
        assert!(!kind.has_runtime_fallback(true));
        assert_eq!(kind.hardened_category(), Some(HardenedVcCategory::FfiBoundary));
        assert_eq!(kind.hardened_family_tag().as_deref(), Some("hardened_ffi_boundary"));
        assert!(kind.description().contains("ffi_boundary"));
    }

    #[test]
    fn native_unsafe_and_ffi_kinds_classify_as_hardened_categories_without_losing_l0_or_copy_sink_tags()
     {
        let unsafe_kind = VcKind::UnsafeOperation { desc: "raw pointer deref".to_string() };
        let unsafe_assertion =
            VcKind::Assertion { message: "[unsafe] missing SAFETY comment".to_string() };
        let ffi_assertion =
            VcKind::Assertion { message: "[unsafe:ffi] precondition for getenv".to_string() };
        let ffi_kind = VcKind::FfiBoundaryViolation {
            callee: "strlen".to_string(),
            desc: "trusted wrapper contract required".to_string(),
        };
        let copy_sink = VcKind::FfiBoundaryViolation {
            callee: "memcpy".to_string(),
            desc: "copy sink length may exceed destination capacity".to_string(),
        };

        assert_eq!(unsafe_kind.proof_level(), ProofLevel::L0Safety);
        assert_eq!(unsafe_assertion.proof_level(), ProofLevel::L0Safety);
        assert_eq!(ffi_assertion.proof_level(), ProofLevel::L0Safety);
        assert_eq!(ffi_kind.proof_level(), ProofLevel::L0Safety);
        assert_eq!(unsafe_kind.hardened_category(), Some(HardenedVcCategory::UnsafeOperation));
        assert_eq!(unsafe_assertion.hardened_category(), Some(HardenedVcCategory::UnsafeOperation));
        assert_eq!(ffi_assertion.hardened_category(), Some(HardenedVcCategory::FfiBoundary));
        assert_eq!(ffi_kind.hardened_category(), Some(HardenedVcCategory::FfiBoundary));
        assert_eq!(unsafe_kind.hardened_family_tag().as_deref(), Some("hardened_unsafe_operation"));
        assert_eq!(ffi_kind.hardened_family_tag().as_deref(), Some("hardened_ffi_boundary"));
        assert_eq!(copy_sink.hardened_category(), None);
        assert_eq!(
            copy_sink.binary_copy_sink_length_family_tag(),
            Some(VcKind::BINARY_COPY_SINK_LENGTH_FAMILY)
        );
    }

    /// G3-MANDATE-L1-ONLY-1 (2026-10-27): only an L1 hardened PROFILE RULE with a
    /// `Bool(true)` violation is a design mandate. Every L0 unsafe/FFI shape the
    /// vcgen mints as a constant-`true` modelling-gap fail-close is not, in every
    /// spelling `hardened_category` maps to those two categories (the native
    /// kinds, the `[unsafe…]`/`[unsafe:ffi]` assertions, a reconstructed
    /// `HardenedBoundary`, a legacy `hardened::` row).
    #[test]
    fn only_l1_hardened_rules_are_design_mandates_never_unsafe_or_ffi_gaps() {
        use crate::Formula;
        let truth = Formula::Bool(true);
        let boundary = |category| VcKind::HardenedBoundary {
            category,
            callee: "callee".to_string(),
            detail: "detail".to_string(),
        };

        // Positive: every L1 category, and the unrecognised-tag one, with `true`.
        for category in [
            HardenedVcCategory::RawPathApi,
            HardenedVcCategory::PathIdentity,
            HardenedVcCategory::PermissionChange,
            HardenedVcCategory::PermissionCreate,
            HardenedVcCategory::PermissionWindow,
            HardenedVcCategory::Utf8Reject,
            HardenedVcCategory::ByteLoss,
            HardenedVcCategory::ErrorDiscard,
            HardenedVcCategory::PanicBoundary,
            HardenedVcCategory::CompatObservable,
            HardenedVcCategory::ProcessSemantics,
            HardenedVcCategory::TrustDomain,
            HardenedVcCategory::TrustDomainOrder,
            HardenedVcCategory::unknown_tag("opaque-terminator"),
        ] {
            let kind = boundary(category);
            assert_eq!(kind.proof_level(), ProofLevel::L1Functional, "{category:?}");
            assert!(kind.is_hardened_design_mandate(&truth), "{category:?} + true is a mandate");
            assert!(
                !kind.is_hardened_design_mandate(&Formula::Bool(false)),
                "{category:?} + false is not"
            );
            assert!(
                !kind.is_hardened_design_mandate(&Formula::Var("v".into(), crate::Sort::Bool)),
                "{category:?} with a real formula is a discharge target"
            );
        }
        let legacy = VcKind::FunctionalCorrectness {
            property: "hardened::error_discard".to_string(),
            context: "Result::ok".to_string(),
        };
        assert!(legacy.is_hardened_design_mandate(&truth));

        // Negative: the L0 unsafe/FFI gaps, in every spelling.
        for kind in [
            boundary(HardenedVcCategory::UnsafeOperation),
            boundary(HardenedVcCategory::FfiBoundary),
            VcKind::UnsafeOperation { desc: "raw pointer deref".to_string() },
            VcKind::Assertion { message: "[unsafe] missing SAFETY comment".to_string() },
            VcKind::Assertion {
                message: "[unsafe:unmodeled-call] call to `ext` is not covered".to_string(),
            },
            VcKind::Assertion { message: "[unsafe:ffi] precondition for getenv".to_string() },
            VcKind::FfiBoundaryViolation {
                callee: "getpgrp".to_string(),
                desc: "no summary: behavior unmodeled, cannot prove safe".to_string(),
            },
            VcKind::FfiBoundaryViolation {
                callee: "free".to_string(),
                desc: "freed pointer must be valid allocation".to_string(),
            },
            VcKind::FunctionalCorrectness {
                property: "hardened::ffi_boundary".to_string(),
                context: "legacy".to_string(),
            },
        ] {
            assert!(kind.hardened_category().is_some(), "{kind:?} is hardened");
            assert!(
                !kind.is_hardened_design_mandate(&truth),
                "{kind:?} + true is a modelling gap, never a mandate"
            );
        }
        // And no non-hardened kind is ever one.
        assert!(!VcKind::DivisionByZero.is_hardened_design_mandate(&truth));
        assert!(!VcKind::IndexOutOfBounds.is_hardened_design_mandate(&truth));
    }

    #[test]
    fn legacy_hardened_serialized_vc_kind_still_deserializes() {
        let json = r#"{
            "FunctionalCorrectness": {
                "property": "hardened::panic_boundary",
                "context": "unwrap: success precondition is not proven"
            }
        }"#;

        let kind: VcKind = serde_json::from_str(json).expect("legacy VC kind deserializes");

        assert_eq!(kind.hardened_category(), Some(HardenedVcCategory::PanicBoundary));
        assert_eq!(kind.hardened_family_tag().as_deref(), Some("hardened_panic_boundary"));
    }

    fn full_lane(kind: &str, detail: &str) -> VcKind {
        VcKind::UnsupportedMir { kind: kind.to_string(), detail: detail.to_string() }
    }

    #[test]
    fn recovered_full_lane_vc_tag_matches_transport_tags() {
        // Detail texts mirror captured transport rows: the original
        // `VcKind::description()` prefix survives, with optional
        // `; contract_id=` / `; metadata_keys=` suffixes after it.
        let cases = [
            (
                "FullVerification::ArithmeticSafety",
                "arithmetic overflow (Add); contract_id=contract:trust-mc-typed-chc-public:cf0b9f",
                "overflow:add",
            ),
            ("FullVerification::ArithmeticSafety", "arithmetic overflow (Sub)", "overflow:sub"),
            ("FullVerification::ArithmeticSafety", "arithmetic overflow (Mul)", "overflow:mul"),
            // `Div`/`Rem` keep their op token: same-span twin subsumption keys
            // on it, and an op-less tag fails closed.
            ("FullVerification::ArithmeticSafety", "arithmetic overflow (Div)", "overflow:div"),
            ("FullVerification::ArithmeticSafety", "arithmetic overflow (Rem)", "overflow:rem"),
            ("FullVerification::ArithmeticSafety", "shift overflow (Shl)", "shift:left"),
            ("FullVerification::ArithmeticSafety", "shift overflow (Shr)", "shift:right"),
            ("FullVerification::ArithmeticSafety", "negation overflow (i32)", "negation"),
            (
                "FullVerification::ArithmeticSafety",
                "division by zero; contract_id=contract:trust-mc-typed-chc-public:4c7c39",
                "divzero",
            ),
            ("FullVerification::ArithmeticSafety", "remainder by zero", "remzero"),
            ("FullVerification::ArithmeticSafety", "cast overflow (U64 -> U32)", "cast"),
            // Prefix anchoring: the float families never fire the integer arms.
            (
                "FullVerification::ArithmeticSafety",
                "float division by zero",
                "float_division_by_zero",
            ),
            (
                "FullVerification::ArithmeticSafety",
                "float overflow to infinity (Add)",
                "float_overflow_to_infinity",
            ),
            (
                "FullVerification::BoundsCheck",
                "index out of bounds; metadata_keys=[trust.obligation_context.v1]",
                "bounds",
            ),
            ("FullVerification::BoundsCheck", "slice bounds check", "slice"),
            (
                "FullVerification::Assertion",
                "assertion: panic call: std::rt::panic_fmt; contract_id=contract:trust-mc-typed-chc-public:b4cdda",
                "assert",
            ),
            (
                "FullVerification::Assertion",
                "unreachable code reached; contract_id=contract:trust-mc-typed-chc-public:8031b9",
                "unreach",
            ),
            ("FullVerification::Precondition", "precondition of `callee`", "precond"),
            ("FullVerification::Postcondition", "postcondition", "postcond"),
            ("FullVerification::TemporalSafety", "dead state `idle`", "deadstate"),
            ("FullVerification::TemporalSafety", "deadlock", "deadlock"),
            ("FullVerification::TemporalSafety", "temporal: always ready", "temporal"),
            ("FullVerification::TemporalSafety", "fairness: WF_{q}(step)", "fairness"),
            ("FullVerification::Liveness", "liveness: termination: <>done", "liveness"),
            ("FullVerification::Protocol", "protocol `handshake`: out of order", "protocol"),
            (
                "FullVerification::Refinement",
                "refinement violation: action `pop` does not refine spec `stack.tla`",
                "refinement",
            ),
            (
                "FullVerification::Termination",
                "non-termination: loop measure `n` may not decrease",
                "termination",
            ),
            ("FullVerification::trust.vc::taint_violation", "anything", "taint"),
            ("FullVerification::trust.vc::resilience_violation", "anything", "resilience"),
        ];

        for (kind, detail, expected) in cases {
            assert_eq!(
                VcKind::recovered_full_lane_vc_tag(kind, detail),
                Some(expected),
                "kind={kind:?} detail={detail:?}"
            );
        }
    }

    #[test]
    fn recovered_full_lane_vc_tag_fails_closed_on_unmapped_rows() {
        let cases = [
            // Unrecognized detail within a known family.
            ("FullVerification::ArithmeticSafety", "some future obligation text"),
            // Cross-family mismatch: a stray description can never relabel a
            // row across families.
            ("FullVerification::BoundsCheck", "division by zero"),
            ("FullVerification::Assertion", "index out of bounds"),
            // A genuine unsupported-MIR VC never had a real kind to recover.
            ("FullVerification::trust.vc::unsupported_mir", "unsupported MIR `InlineAsm`"),
            // Unknown family.
            ("FullVerification::MemorySafety", "index out of bounds"),
            // Non-round-trip rows: no `FullVerification::` prefix at all.
            ("assumption:native-lowering", "assumption:native-lowering"),
            ("InlineAsm", "inline assembly is not modeled"),
            ("", "division by zero"),
        ];

        for (kind, detail) in cases {
            assert_eq!(
                VcKind::recovered_full_lane_vc_tag(kind, detail),
                None,
                "kind={kind:?} detail={detail:?}"
            );
        }
    }

    #[test]
    fn full_lane_effective_kind_recovers_runtime_fallback_per_family() {
        // (kind, detail, with overflow-checks, without overflow-checks) — each
        // answer matches the recovered effective kind's own arm.
        let cases = [
            // Overflow family → `overflow_checks`, per the
            // ArithmeticOverflow/ShiftOverflow/NegationOverflow arms.
            (
                "FullVerification::ArithmeticSafety",
                "arithmetic overflow (Add); contract_id=contract:trust-mc-typed-chc-public:cf0b9f",
                true,
                false,
            ),
            ("FullVerification::ArithmeticSafety", "arithmetic overflow (Sub)", true, false),
            ("FullVerification::ArithmeticSafety", "arithmetic overflow (Mul)", true, false),
            ("FullVerification::ArithmeticSafety", "arithmetic overflow (Div)", true, false),
            ("FullVerification::ArithmeticSafety", "arithmetic overflow (Rem)", true, false),
            ("FullVerification::ArithmeticSafety", "shift overflow (Shl)", true, false),
            ("FullVerification::ArithmeticSafety", "shift overflow (Shr)", true, false),
            ("FullVerification::ArithmeticSafety", "negation overflow (i32)", true, false),
            // Divzero/bounds/assert families → unconditionally true, per the
            // DivisionByZero/RemainderByZero/IndexOutOfBounds/SliceBoundsCheck/
            // Assertion arms.
            (
                "FullVerification::ArithmeticSafety",
                "division by zero; contract_id=contract:trust-mc-typed-chc-public:4c7c39",
                true,
                true,
            ),
            ("FullVerification::ArithmeticSafety", "remainder by zero", true, true),
            (
                "FullVerification::BoundsCheck",
                "index out of bounds; metadata_keys=[trust.obligation_context.v1]",
                true,
                true,
            ),
            ("FullVerification::BoundsCheck", "slice bounds check", true, true),
            (
                "FullVerification::Assertion",
                "assertion: panic call: std::rt::panic_fmt; contract_id=contract:trust-mc-typed-chc-public:b4cdda",
                true,
                true,
            ),
            // Unreach → whatever the Unreachable arm answers (false). The
            // recovered tag stays `unreach` for display; only the fallback
            // answer moved, and it must move in lock-step with the direct arm.
            (
                "FullVerification::Assertion",
                "unreachable code reached; contract_id=contract:trust-mc-typed-chc-public:8031b9",
                false,
                false,
            ),
            // Recovered families whose own arms answer false stay false.
            ("FullVerification::ArithmeticSafety", "cast overflow (U64 -> U32)", false, false),
            ("FullVerification::ArithmeticSafety", "float division by zero", false, false),
            ("FullVerification::Precondition", "precondition of `callee`", false, false),
            ("FullVerification::Postcondition", "postcondition", false, false),
            ("FullVerification::TemporalSafety", "deadlock", false, false),
        ];

        for (kind, detail, with_oc, without_oc) in cases {
            let vc_kind = full_lane(kind, detail);
            assert_eq!(
                vc_kind.has_runtime_fallback(true),
                with_oc,
                "kind={kind:?} detail={detail:?} overflow_checks=true"
            );
            assert_eq!(
                vc_kind.has_runtime_fallback(false),
                without_oc,
                "kind={kind:?} detail={detail:?} overflow_checks=false"
            );
        }
    }

    #[test]
    fn full_lane_unmapped_detail_keeps_runtime_fallback_fail_closed() {
        let cases = [
            ("FullVerification::ArithmeticSafety", "some future obligation text"),
            ("FullVerification::BoundsCheck", "division by zero"),
            ("FullVerification::trust.vc::unsupported_mir", "unsupported MIR `InlineAsm`"),
            // targo folds `assumption:<tag>` rows into `UnsupportedMir`
            // precisely so they get NO runtime fallback — must stay false.
            ("assumption:native-lowering", "assumption:native-lowering"),
            ("InlineAsm", "inline assembly is not modeled"),
        ];

        for (kind, detail) in cases {
            let vc_kind = full_lane(kind, detail);
            assert!(!vc_kind.has_runtime_fallback(true), "kind={kind:?} detail={detail:?}");
            assert!(!vc_kind.has_runtime_fallback(false), "kind={kind:?} detail={detail:?}");
        }
    }

    // ── Runtime-fallback fail-opens: the unchecked-UB family, the
    //    separation-engine unsafe assertions, and the authored invariant ──

    fn unchecked_add_kind() -> VcKind {
        VcKind::UncheckedArithmeticOverflow { op: BinOp::Add, operand_tys: (Ty::u32(), Ty::u32()) }
    }

    fn unchecked_index_kind() -> VcKind {
        VcKind::UncheckedIndexBounds {
            callee: "core::slice::<impl [u32]>::get_unchecked".into(),
            detail: "unchecked index must be < the container length".into(),
        }
    }

    /// THE decisive lock. The unchecked-UB family answers `ub_checks`, and
    /// nothing else.
    ///
    /// MEASURED, stage2 `trustc 1.99.0-dev (d6a53e72a)`, `--emit=llvm-ir -C
    /// opt-level=0`: with `-Coverflow-checks=off -Cdebug-assertions=off`,
    /// `u32::unchecked_add` is a lone `add nuw` and
    /// `<usize as SliceIndex<[u32]>>::get_unchecked` is a lone `getelementptr`;
    /// with `-Coverflow-checks=off -Zub-checks=yes` BOTH gain a
    /// `precondition_check` call, while `a + b` gains nothing.
    ///
    /// MUTATIONS THIS CATCHES, and why no other path neutralises them:
    /// * arm → `env.overflow_checks` (the pre-split behaviour, i.e. folding these
    ///   back onto `ArithmeticOverflow` / `IndexOutOfBounds`): the
    ///   `(overflow_checks: true, ub_checks: false)` row — the RELEASE
    ///   configuration — flips to `true` and fails. That row is the whole bug.
    /// * arm → `true`: both `ub_checks: false` rows fail.
    /// * arm → `false`: both `ub_checks: true` rows fail, so the fix cannot be
    ///   "widened to a blanket decline" without this test noticing.
    /// The `has_runtime_fallback_in` match is exhaustive over `VcKind` and these
    /// two variants appear in exactly one arm, so no earlier or later arm can
    /// intercept them; the guarded `Assertion` arm above cannot match a
    /// non-`Assertion` variant.
    #[test]
    fn unchecked_ub_family_answers_ub_checks_never_overflow_checks() {
        for kind in [unchecked_add_kind(), unchecked_index_kind()] {
            // (overflow_checks, ub_checks) -> expected
            let cases = [
                ((false, false), false),
                // RELEASE with overflow checks on: the guard is still gone.
                ((true, false), false),
                // The knob that actually controls the guard, with the other OFF.
                ((false, true), true),
                ((true, true), true),
            ];
            for ((oc, ub), expected) in cases {
                assert_eq!(
                    kind.has_runtime_fallback_in(RuntimeCheckEnv::new(oc, ub)),
                    expected,
                    "{kind:?} at overflow_checks={oc} ub_checks={ub}"
                );
            }
            // Both are UB, not a panic: L0, exactly like the checked siblings.
            assert_eq!(kind.proof_level(), ProofLevel::L0Safety);
        }
    }

    /// ANTI-OVER-FIX lock. A blanket `false` on `IndexOutOfBounds` /
    /// `ArithmeticOverflow` would "fix" the unchecked family by fail-closing
    /// every ordinary `xs[i]` and `a + b` in the tree — a release gate, not a
    /// fix. These rows are MEASURED to keep their guards: `xs[i]` emits
    /// `panic_bounds_check` under all three probed configurations, and `a + b`
    /// emits `panic_const_add_overflow` exactly when `-Coverflow-checks=on`.
    ///
    /// Mutation caught: changing either arm to `false` (or to `env.ub_checks`)
    /// fails here. Nothing else asserts the POSITIVE direction for these kinds
    /// across a `ub_checks: false` environment, which is where a careless
    /// "everything unchecked is unmonitored" edit would land.
    #[test]
    fn checked_indexing_and_arithmetic_keep_their_own_guards() {
        for env in [
            RuntimeCheckEnv::new(false, false),
            RuntimeCheckEnv::new(true, false),
            RuntimeCheckEnv::new(false, true),
            RuntimeCheckEnv::new(true, true),
        ] {
            assert!(
                VcKind::IndexOutOfBounds.has_runtime_fallback_in(env),
                "safe `xs[i]` keeps `panic_bounds_check` under {env:?}"
            );
            assert!(VcKind::SliceBoundsCheck.has_runtime_fallback_in(env));
            assert!(VcKind::DivisionByZero.has_runtime_fallback_in(env));
            let add =
                VcKind::ArithmeticOverflow { op: BinOp::Add, operand_tys: (Ty::i32(), Ty::i32()) };
            assert_eq!(
                add.has_runtime_fallback_in(env),
                env.overflow_checks,
                "checked `a + b` tracks overflow_checks and NOT ub_checks, under {env:?}"
            );
        }
    }

    /// The `overflow_checks`-only adapter must resolve the knob it cannot see to
    /// "no guard", for every kind.
    ///
    /// Mutation caught: flipping `RuntimeCheckEnv::overflow_checks_only` to
    /// `ub_checks: true` makes the two `assert!(!…)` rows fail. That mutation is
    /// otherwise invisible — every existing caller passes a bool, and the
    /// unchecked family is the only thing that reads the field.
    #[test]
    fn overflow_checks_only_adapter_resolves_ub_checks_to_off() {
        assert_eq!(RuntimeCheckEnv::overflow_checks_only(true), RuntimeCheckEnv::new(true, false));
        for kind in [unchecked_add_kind(), unchecked_index_kind()] {
            assert!(!kind.has_runtime_fallback(true), "{kind:?}");
            assert!(!kind.has_runtime_fallback(false), "{kind:?}");
        }
        // The adapter is exactly `has_runtime_fallback_in` with ub_checks off.
        for oc in [false, true] {
            for kind in [
                unchecked_add_kind(),
                unchecked_index_kind(),
                VcKind::IndexOutOfBounds,
                VcKind::ArithmeticOverflow { op: BinOp::Mul, operand_tys: (Ty::u32(), Ty::u32()) },
                VcKind::ContractInvariant { expression: "x > 0".into() },
            ] {
                assert_eq!(
                    kind.has_runtime_fallback(oc),
                    kind.has_runtime_fallback_in(RuntimeCheckEnv::new(oc, false)),
                    "{kind:?} at overflow_checks={oc}"
                );
            }
        }
    }

    /// An authored `#[invariant(..)]` has no code behind it in ANY configuration.
    ///
    /// MEASURED, stage2: `#[trust::invariant(x > 0)] fn inv_fn(x: i32) -> i32 { x }`
    /// emits `start: ret i32 %x` — byte-identical to the unannotated function.
    ///
    /// Mutation caught: routing the clause back onto `VcKind::Assertion` (the
    /// pre-fix mint in `contracts.rs` / `spec_parser.rs`) makes every row here
    /// answer `true`. The vcgen-side twins of this lock live next to those two
    /// mint sites, so the mutation is caught at the kind AND at both producers.
    #[test]
    fn contract_invariant_never_claims_a_runtime_fallback() {
        let kind = VcKind::ContractInvariant { expression: "x > 0".into() };
        for env in [
            RuntimeCheckEnv::new(false, false),
            RuntimeCheckEnv::new(true, false),
            RuntimeCheckEnv::new(false, true),
            RuntimeCheckEnv::new(true, true),
        ] {
            assert!(!kind.has_runtime_fallback_in(env), "{env:?}");
            // Its two sibling clauses answer identically — that symmetry is the
            // whole point of moving it off `Assertion`.
            assert!(!VcKind::Postcondition.has_runtime_fallback_in(env));
            assert!(!VcKind::Precondition { callee: "f".into() }.has_runtime_fallback_in(env));
        }
        assert_eq!(kind.proof_level(), ProofLevel::L1Functional);
        assert_eq!(kind.description(), "invariant: x > 0");
        assert_eq!(kind.transport_tag(), "invariant");
    }

    /// The separation engine's `[unsafe:sep:*]` assertions name operations Rust
    /// does not watch (double-free, `set_len` past capacity, `ptr::offset` out of
    /// its allocation, `assume_init` on uninit memory). They must not inherit the
    /// `Assertion` arm's `true`, which is earned by a rustc-inserted `Assert`
    /// terminator.
    ///
    /// Mutation caught, in BOTH directions:
    /// * deleting the guarded arm (so these fall through to `Assertion => true`)
    ///   fails the first loop;
    /// * widening the decline to all `Assertion`s fails the second loop, which
    ///   pins an ordinary `assert!` — including one whose message merely
    ///   MENTIONS the marker rather than leading with it, since the guard is
    ///   anchored with `starts_with`.
    #[test]
    fn separation_engine_unsafe_assertions_have_no_runtime_fallback() {
        let unmonitored = [
            "[unsafe:sep:free] double-free of `p` (prov#1) in f",
            "[unsafe:sep:set_len] new length must not exceed capacity in f",
            "[unsafe:sep:offset] pointer offset out of bounds for `p` in f",
            "[unsafe:sep:assume_init] the value must be fully initialized in f",
        ];
        for message in unmonitored {
            let kind = VcKind::Assertion { message: message.to_string() };
            for env in [RuntimeCheckEnv::new(true, true), RuntimeCheckEnv::new(false, false)] {
                assert!(!kind.has_runtime_fallback_in(env), "{message:?} under {env:?}");
            }
            // It already classifies as a hardened unsafe row; the typed
            // spellings of the same properties (`DoubleFree`, `UnsafeOperation`,
            // `HardenedBoundary { UnsafeOperation }`) all answer `false` too, so
            // this arm restores agreement rather than inventing a new rule.
            assert_eq!(kind.hardened_category(), Some(HardenedVcCategory::UnsafeOperation));
        }
        assert!(!VcKind::DoubleFree.has_runtime_fallback(true));
        assert!(!VcKind::UnsafeOperation { desc: "raw deref".into() }.has_runtime_fallback(true));

        // A genuine rustc `Assert` terminator / `assert!` panic call keeps its
        // fallback — the decline is anchored, not blanket.
        for message in [
            "panic call: std::rt::panic_fmt",
            "invariant holds",
            "checked that [unsafe:sep:free] cannot happen here",
        ] {
            let kind = VcKind::Assertion { message: message.to_string() };
            assert!(kind.has_runtime_fallback(true), "{message:?}");
            assert!(kind.has_runtime_fallback(false), "{message:?}");
        }
    }

    /// LAUNDERING GUARD. A full-lane round-trip must not hand an unchecked or
    /// sep-unsafe row back a fallback its direct arm declined.
    ///
    /// `recovered_full_lane_vc_tag` recovers a tag by matching `detail` — which
    /// is the original `VcKind::description()` — against per-family prefixes.
    /// Mutation caught: renaming `UncheckedArithmeticOverflow`'s description to
    /// anything starting `"arithmetic overflow ("` makes the first block recover
    /// `overflow:add` and answer `env.overflow_checks`, resurrecting HOLE B for
    /// every round-tripped row. Likewise `"index out of bounds…"` for HOLE A.
    /// The third block pins the `assert` arm's mirrored `[unsafe:sep:` decline.
    #[test]
    fn full_lane_round_trip_cannot_launder_an_unmonitored_row() {
        // Descriptions are anchored so they can never match a checked family's
        // prefix set.
        let unchecked_add_detail = unchecked_add_kind().description();
        assert_eq!(unchecked_add_detail, "unchecked arithmetic overflow (Add)");
        assert_eq!(
            VcKind::recovered_full_lane_vc_tag(
                "FullVerification::ArithmeticSafety",
                &unchecked_add_detail
            ),
            None,
        );

        let unchecked_index_detail = unchecked_index_kind().description();
        assert!(unchecked_index_detail.starts_with("unchecked index bounds in "));
        assert_eq!(
            VcKind::recovered_full_lane_vc_tag(
                "FullVerification::BoundsCheck",
                &unchecked_index_detail
            ),
            None,
        );

        for detail in [&unchecked_add_detail, &unchecked_index_detail] {
            for family in ["FullVerification::ArithmeticSafety", "FullVerification::BoundsCheck"] {
                let row = full_lane(family, detail);
                assert!(
                    !row.has_runtime_fallback_in(RuntimeCheckEnv::new(true, true)),
                    "family={family} detail={detail}"
                );
            }
        }

        // A round-tripped `[unsafe:sep:` assertion answers exactly what the
        // direct arm answers.
        let sep_row = full_lane(
            "FullVerification::Assertion",
            "assertion: [unsafe:sep:free] double-free of `p` in f; contract_id=contract:x",
        );
        assert_eq!(
            VcKind::recovered_full_lane_vc_tag(
                "FullVerification::Assertion",
                "assertion: [unsafe:sep:free] double-free of `p` in f; contract_id=contract:x",
            ),
            Some("assert"),
            "the DISPLAY tag is unchanged — only the fallback answer moved",
        );
        assert!(!sep_row.has_runtime_fallback_in(RuntimeCheckEnv::new(true, true)));

        // An ordinary round-tripped assertion still gets its fallback.
        let plain = full_lane("FullVerification::Assertion", "assertion: panic call: core::panic");
        assert!(plain.has_runtime_fallback(false));
    }

    #[test]
    fn non_unsupported_mir_runtime_fallback_arms_are_stable() {
        // The effective-kind derivation touches ONLY `UnsupportedMir`; every
        // other family keeps its existing answer.
        let cases: [(VcKind, bool, bool); 12] = [
            (
                VcKind::ArithmeticOverflow { op: BinOp::Add, operand_tys: (Ty::i32(), Ty::i32()) },
                true,
                false,
            ),
            (VcKind::DivisionByZero, true, true),
            (VcKind::RemainderByZero, true, true),
            (VcKind::IndexOutOfBounds, true, true),
            (VcKind::SliceBoundsCheck, true, true),
            (VcKind::Assertion { message: "invariant holds".into() }, true, true),
            // `Unreachable` has NO fallback: its bare-`Terminator::Unreachable`
            // mint emits no runtime trap and the unit variant cannot prove which
            // mint a given row came from.
            (VcKind::Unreachable, false, false),
            (VcKind::CastOverflow { from_ty: Ty::i32(), to_ty: Ty::u32() }, false, false),
            // The unchecked-UB family is invariant in `overflow_checks` — the
            // knob this bool-only spelling carries is simply not the one that
            // controls their guard, and the adapter pins the other knob OFF.
            (unchecked_add_kind(), false, false),
            (unchecked_index_kind(), false, false),
            // A span-only attribute has no guard under any knob.
            (VcKind::ContractInvariant { expression: "x > 0".into() }, false, false),
            // No rustc-inserted check enforces a struct invariant.
            (tinv_kind("crate::S", TypeInvariantPoint::Call, 2, 0), false, false),
        ];

        for (vc_kind, with_oc, without_oc) in cases {
            assert_eq!(vc_kind.has_runtime_fallback(true), with_oc, "{vc_kind:?}");
            assert_eq!(vc_kind.has_runtime_fallback(false), without_oc, "{vc_kind:?}");
        }
    }

    // ---- TINV step 2 (2026-10-05): `VcKind::TypeInvariant` -------------------

    const TINV_POINTS: [TypeInvariantPoint; 6] = [
        TypeInvariantPoint::Establish,
        TypeInvariantPoint::Call,
        TypeInvariantPoint::Return,
        TypeInvariantPoint::Unwind,
        TypeInvariantPoint::Move,
        TypeInvariantPoint::Drop,
    ];

    fn tinv_kind(ty: &str, point: TypeInvariantPoint, block: usize, stmt: usize) -> VcKind {
        VcKind::TypeInvariant {
            ty: ty.into(),
            point,
            site: TypeInvariantSite { block, statement_index: stmt },
            conjunct: 0,
            ordinal: 0,
            edge: None,
        }
    }

    fn with_identity(k: VcKind, c: u32, o: u32, e: Option<usize>) -> VcKind {
        match k {
            VcKind::TypeInvariant { ty, point, site, .. } => {
                VcKind::TypeInvariant { ty, point, site, conjunct: c, ordinal: o, edge: e }
            }
            other => other,
        }
    }

    #[test]
    fn type_invariant_is_l1_unrefutable_and_never_runtime_checked() {
        for point in TINV_POINTS {
            let k = tinv_kind("mycrate::Screen", point, 4, 2);
            assert_eq!(k.proof_level(), ProofLevel::L1Functional);
            for env in ENVS {
                assert!(!k.has_runtime_fallback_in(env), "{point}: {env:?}");
                assert!(!k.site_retains_language_check_in(env), "{point}: {env:?}");
            }
            assert!(!k.has_runtime_fallback(true) && !k.has_runtime_fallback(false));
            assert!(k.hardened_category().is_none());
            let tag = k.transport_tag();
            assert_eq!(tag, format!("type_invariant:{}", point.as_tag()));
            let d = k.description();
            assert!(d.contains("mycrate::Screen") && d.contains(point.as_tag()), "{d}");
            assert!(d.contains("bb4[2]"), "{d}");
            for family in ["ArithmeticSafety", "IndexSafety", "Assertion", "Postcondition"] {
                let kind = format!("{}{family}", VcKind::FULL_VERIFICATION_KIND_PREFIX);
                assert_eq!(VcKind::recovered_full_lane_vc_tag(&kind, &d), None, "{family}");
            }
        }
        // The description is lossless over (ty, point, site): dedup compares it.
        let base = tinv_kind("a::S", TypeInvariantPoint::Call, 1, 0);
        for other in [
            tinv_kind("b::S", TypeInvariantPoint::Call, 1, 0),
            tinv_kind("a::S", TypeInvariantPoint::Return, 1, 0),
            tinv_kind("a::S", TypeInvariantPoint::Call, 2, 0),
            tinv_kind("a::S", TypeInvariantPoint::Call, 1, 1),
            with_identity(base.clone(), 1, 0, None),
            with_identity(base.clone(), 0, 1, None),
            with_identity(base.clone(), 0, 0, Some(0)),
            with_identity(base.clone(), 0, 0, Some(1)),
        ] {
            assert_ne!(base.description(), other.description(), "{other:?}");
        }
        // Two edge parts of one point describe apart, and the transport tag (the
        // per-point counting bucket) is unchanged by the identity fields.
        let p0 = with_identity(base.clone(), 0, 0, Some(0));
        let p2 = with_identity(base.clone(), 0, 0, Some(2));
        assert_ne!(p0.description(), p2.description());
        assert!(p2.description().contains("via edge bb2"), "{}", p2.description());
        assert_eq!(p0.transport_tag(), base.transport_tag());
        let json = serde_json::to_string(&p2).expect("serialize");
        let back: VcKind = serde_json::from_str(&json).expect("deserialize");
        assert_eq!(back, p2);
    }

    #[test]
    fn type_invariant_point_bytes_and_tags_are_frozen() {
        let tags = ["establish", "call", "return", "unwind", "move", "drop"];
        for (i, point) in TINV_POINTS.into_iter().enumerate() {
            assert_eq!(usize::from(point.canonical_byte()), i, "{point:?}");
            assert_eq!(point.as_tag(), tags[i]);
            assert_eq!(point.to_string(), tags[i]);
            let json = serde_json::to_string(&point).expect("serialize");
            let back: TypeInvariantPoint = serde_json::from_str(&json).expect("deserialize");
            assert_eq!(back, point);
        }
        let site = TypeInvariantSite { block: 7, statement_index: 3 };
        assert_eq!(site.to_string(), "bb7[3]");
    }

    /// TINV step 7.7 (TINV-8, 2026-10-05): the kind gate ADMITS every point, and the
    /// VC-level gate decides the row: a record-less row and a bare (hypothesis-free)
    /// recorded row of every point are refused; a recorded, replaying, bound row of every
    /// point is admitted. MUTATION: move `TypeInvariant` back under REFUSED in
    /// `kind_authority_refusal` and the first and last assertions fail.
    #[test]
    fn type_invariant_kind_is_admitted_and_the_row_gate_decides() {
        use crate::{Formula, ObligationRecord, Sort, SourceSpan, VerificationCondition};
        let var = |n: &str| Formula::Var(n.to_string(), Sort::Int);
        let neg_core = Formula::Not(Box::new(Formula::Le(Box::new(var("i1")), Box::new(var("n")))));
        // The 0(b)(c) linear preservation row: `i1 = i0 + 1 ∧ i0 < n ∧ ¬(i1 <= n)`.
        let situated = Formula::And(vec![
            Formula::Eq(
                Box::new(var("i1")),
                Box::new(Formula::Add(Box::new(var("i0")), Box::new(Formula::Int(1)))),
            ),
            Formula::Lt(Box::new(var("i0")), Box::new(var("n"))),
            neg_core.clone(),
        ]);
        let row = |kind: VcKind, body: &Formula, recorded: bool| VerificationCondition {
            kind,
            function: "mycrate::S::bump".into(),
            location: SourceSpan::default(),
            formula: body.clone(),
            contract_metadata: None,
            obligation: recorded.then(|| ObligationRecord {
                body: body.clone(),
                wrappers: Vec::new(),
                subject: None,
                width: None,
            }),
        };
        for point in TINV_POINTS {
            let kind = tinv_kind("mycrate::S", point, 0, 0);
            assert_eq!(kind.kind_authority_refusal(), None, "{point}: the kind is admitted");
            let why = row(kind.clone(), &situated, false)
                .kernel_authority_refusal()
                .expect("a record-less TINV row is refused");
            assert!(why.contains("type-invariant"), "{point}: {why}");
            assert!(
                row(kind.clone(), &neg_core, true).kernel_authority_refusal().is_some(),
                "{point}: a bare negated core binds nothing"
            );
            assert_eq!(row(kind, &situated, true).kernel_authority_refusal(), None, "{point}");
        }
    }
}
