//! Per-crate verification policy bucket detector.
//!
//! Codex's review correction: "Workspace-only fast path is
//! necessary, but dangerous if phrased as 'don't verify non-workspace
//! crates.' Better: classify crates/functions into policy buckets
//! automatically. Trust-owned/spec-bearing crates get proof
//! obligations. Unspecced upstream/dependency code gets extraction
//! compatibility checks, summarized unsupported coverage, and cached
//! 'unverified external assumption' facts."
//!
//! This module answers a different question from `supportability.rs`:
//!
//! - `supportability.rs` asks: *can this function's MIR plausibly
//!   lower into trust-ir?*
//! - `policy.rs` asks: *what kind of verification entry should this
//!   crate get in the first place?*
//!
//! Together they form the two-axis classifier the reviewers wanted:
//! `(policy_bucket, supportability) → verification_entry_kind`. The
//! trust-router consumes both axes when deciding what evidence to
//! generate.
//!
//! No trait-solver calls — pure metadata. Cost is O(1) per crate for
//! [`classify_crate`]; [`classify_def`] additionally reads one def
//! path and (for inherent-impl candidates only) one `type_of` metadata
//! entry.
//!
//! # The step-4 `core::num` carve-out
//!
//! `docs/design/2026-08-19-verified-sysroot-scoping.md` §5 step 4
//! requires (verbatim): "`PolicyBucket::UpstreamRustModified`
//! (`trust-mir-extract/src/policy.rs`) must be *narrowed* for the
//! targeted modules to `TrustOwnedDefault`, or the whole exercise
//! produces assumption records rather than proofs — the exact failure
//! mode the brief calls out". §1.4 states the reason: "an assumption
//! record is still an assumption. Reaching real coverage means
//! graduating modules out of that bucket into `TrustOwnedDefault`."
//!
//! [`classify_def`] implements that narrowing. It is EXPLICIT OPT-IN
//! and per-def: with [`LibraryVerificationLane::off`] (the default for
//! every build that does not carry the bootstrap library-verification
//! opt-in) it is byte-for-byte [`classify_crate`], and even with the
//! lane on it only ever narrows a def *of the crate currently being
//! compiled* when that crate is `core` and the def is on the measured
//! step-4 target surface. Narrowing is the fail-closed direction —
//! `TrustOwnedDefault::unsupported_is_failure()` is `true` where
//! `UpstreamRustModified`'s is `false` — so the carve-out can only
//! ever turn a silent assumption into a loud failure, never the
//! reverse.
//!
//! Author: Andrew Yates | Copyright 2026 Andrew Yates | License: Apache-2.0

use rustc_hir::def::DefKind;
use rustc_hir::definitions::DefPathData;
use rustc_middle::ty::{TyCtxt, TyKind};
use rustc_span::def_id::{CrateNum, DefId, LOCAL_CRATE};

/// Policy bucket for an entire crate. Determined by the toolchain at
/// MIR-pass time from crate metadata; the user does not pick.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash)]
pub enum PolicyBucket {
    /// Trust-owned spec-bearing crate. Full obligation set; failures
    /// are blocking. `crates/`, `targo-trust/`, `first-party/*` (when
    /// the function carries `#[trust::*]` contract attributes).
    TrustOwnedSpecBearing,

    /// Trust-owned crate without spec attributes (yet). Generate the
    /// default safety obligation set (overflow, bounds, div-by-zero,
    /// cast safety). Failures are blocking. `crates/`, `targo-trust/`,
    /// `first-party/*` (when no contract attrs).
    TrustOwnedDefault,

    /// Trust-modified upstream rustc / library / stdlib code. Lowering
    /// is attempted (we want to find Trust-introduced regressions), but
    /// individual unsupported obligations become assumption records,
    /// not failures. Includes `compiler/*`, `library/*`,
    /// `src/llvm-project/*`-adjacent.
    UpstreamRustModified,

    /// Pure external dependency from `~/.cargo/registry/` or
    /// `src/tools/targo/`-adjacent. Boundary extraction only; the body
    /// becomes an opaque external assumption. The crate's *interface*
    /// (function signatures, type aliases) is still extracted so
    /// downstream Trust crates can refer to it, but no obligations are
    /// generated on the body.
    ExternalDep,

    /// Unknown bucket — defensive default. Treated like
    /// `ExternalDep` (most conservative re: avoiding spurious failure
    /// reports) but logged so the bucket map can be extended.
    Unknown,
}

impl PolicyBucket {
    /// Stable tag for the per-crate diagnostic / proof-report
    /// aggregator. Stays in lockstep with `supportability::UnsupportedReason::tag`
    /// so query filters can grep both.
    pub const fn tag(&self) -> &'static str {
        match self {
            Self::TrustOwnedSpecBearing => "trust-owned-spec-bearing",
            Self::TrustOwnedDefault => "trust-owned-default",
            Self::UpstreamRustModified => "upstream-rust-modified",
            Self::ExternalDep => "external-dep",
            Self::Unknown => "unknown-bucket",
        }
    }

    /// Should the verifier *generate proof obligations* on functions in
    /// this bucket?
    ///
    /// `TrustOwned*` buckets: yes.
    /// `UpstreamRustModified`: yes (we want to catch our own regressions).
    /// `ExternalDep`: no — boundary-extract only.
    pub const fn generate_obligations(&self) -> bool {
        matches!(
            self,
            Self::TrustOwnedSpecBearing | Self::TrustOwnedDefault | Self::UpstreamRustModified
        )
    }

    /// Should an *unsupported* lowering in this bucket be reported as
    /// a hard verification failure, or as an Assumption row?
    ///
    /// Trust-owned: failure (it's our code; we own the gap).
    /// Upstream-modified / External: Assumption (we don't yet have the
    /// trust-ir coverage to model that code; record the gap honestly
    /// without blocking the build).
    pub const fn unsupported_is_failure(&self) -> bool {
        matches!(self, Self::TrustOwnedSpecBearing | Self::TrustOwnedDefault)
    }
}

/// Per-crate policy bucket detection.
///
/// Read crate metadata (name + source path prefix) and map to a
/// bucket. The mapping is deterministic, O(1), and never invokes the
/// trait solver or anything else expensive.
pub fn classify_crate<'tcx>(tcx: TyCtxt<'tcx>, krate: CrateNum) -> PolicyBucket {
    let name = tcx.crate_name(krate);
    let name_s = name.as_str();

    // Fast path: stdlib + compiler builtins. These are upstream Rust
    // (or compiler-internal) and Trust modifies a subset of them; the
    // verifier currently treats them all as UpstreamRustModified for
    // diagnostic clarity.
    if matches!(
        name_s,
        "core"
            | "alloc"
            | "std"
            | "proc_macro"
            | "compiler_builtins"
            | "test"
            | "panic_unwind"
            | "panic_abort"
            | "unwind"
            | "rustc_std_workspace_core"
            | "rustc_std_workspace_alloc"
            | "rustc_std_workspace_std"
    ) {
        return PolicyBucket::UpstreamRustModified;
    }

    // Compiler crates carry `rustc_` prefix in upstream Rust. Trust
    // adds `// Trust:`-marked patches to a subset; bucketing them as
    // UpstreamRustModified lets verifier output flag *only* the
    // Trust-touched bits as needing per-test ledger coverage.
    if name_s.starts_with("rustc_") {
        return PolicyBucket::UpstreamRustModified;
    }

    // Trust-owned crates. The set is deliberately a fixed list rather
    // than a path prefix check — this module compiles into the rustc
    // sysroot, where filesystem paths are stripped.
    if name_s.starts_with("trust_")
        || name_s.starts_with("trust-")
        || matches!(name_s, "targo_trust" | "targo-trust" | "ay" | "ay_core")
    {
        return PolicyBucket::TrustOwnedDefault;
    }

    // Trust's first-party sibling repos (ay, trust-mc, …). They carry
    // their own contract-bearing functions but the crate names are
    // varied. Conservatively treat anything that imports trust-types
    // as Trust-owned. (Heuristic — for production we'd want a stable
    // attribute marker on the crate root; queued as a follow-up.)
    //
    // For now, fall through to ExternalDep so we don't false-positive.

    // Anything else: external dependency.
    PolicyBucket::ExternalDep
}

// ---------------------------------------------------------------------------
// Step-4 library verification lane (per-def narrowing)
// ---------------------------------------------------------------------------

/// The bootstrap library-verification lane, as visible at
/// policy-decision time.
///
/// The plan (`docs/design/2026-08-19-verified-sysroot-scoping.md` §1.2)
/// requires that a verified-std lane "carve out an explicit,
/// separately-named `Mode::Std` opt-in that does not touch the compiler
/// self-build claim". Bootstrap landed exactly that opt-in:
/// `TRUST_BOOTSTRAP_VERIFY_LIBRARY=<unit>[,<unit>...]` on the `x.py`
/// side (`src/bootstrap/src/core/builder/cargo.rs`), authorized per
/// cargo invocation for `Mode::Std` at stage >= 1 only, and transported
/// to the rustc shim as [`Self::SHIM_VERIFY_UNITS_ENV`]. The shim flips
/// exactly the named units to `-Ztrust-verify=on`
/// (`src/bootstrap/src/bin/rustc.rs`, `trust_bootstrap_verify_unit_applies`)
/// while `rustflags_request_bootstrap_verification`'s self-proof
/// refusal stays intact for every other route. This type never reads or
/// interprets `-Ztrust-verify` rustflags, so it cannot weaken that
/// refusal.
///
/// The environment variable is inherited by the `trustc` process the
/// shim spawns, which is how the authorized unit list reaches
/// policy-decision time. An ambient value in some other compile
/// changes nothing a user can observe outside the carve-out's own
/// conjuncts: [`classify_def`] additionally requires the def to belong
/// to the LOCAL crate *and* that crate to be `core` *and* the def to be
/// on the measured target surface, and the narrowing direction is
/// strictly fail-closed (assumption → failure).
///
/// Construction is split so the decision logic is unit-testable
/// without touching process environment:
/// [`Self::from_units_value`] parses a raw value; [`Self::from_env`]
/// is the thin production wrapper over it.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct LibraryVerificationLane {
    /// Normalized (`-` → `_`, trimmed) crate names of the `library/`
    /// units the bootstrap opt-in authorized for this compiler
    /// invocation. Empty means the lane is OFF, which is the state of
    /// every build that did not pass through the bootstrap opt-in.
    authorized_units: Vec<String>,
}

impl LibraryVerificationLane {
    /// Bootstrap -> rustc-shim IPC channel for the per-unit `library/`
    /// verification opt-in. Kept in lockstep with
    /// `TRUST_BOOTSTRAP_SHIM_VERIFY_UNITS_ENV` in
    /// `src/bootstrap/src/core/builder/cargo.rs` and
    /// `src/bootstrap/src/bin/rustc.rs` (the shims cannot depend on
    /// this crate, so the name is spelled in all three places).
    pub const SHIM_VERIFY_UNITS_ENV: &'static str = "TRUST_BOOTSTRAP_SHIM_VERIFY_UNITS";

    /// The lane every ordinary build is on: no narrowing anywhere.
    pub fn off() -> Self {
        Self { authorized_units: Vec::new() }
    }

    /// Parse a raw unit-list value (`"core"`, `"core,alloc"`, ...).
    ///
    /// Fail-closed: `None`, an empty value, and every degenerate entry
    /// (empty after trimming, or containing anything other than
    /// `[A-Za-z0-9_]` after `-` → `_` normalization) contribute no
    /// authorization. Degenerate input therefore yields today's
    /// behavior exactly — no narrowing — never a wider lane. Bootstrap
    /// already hard-errors on malformed values at the `x.py` boundary
    /// (`parse_trust_verify_library_request`); this parser only has to
    /// guarantee that garbage cannot authorize anything.
    pub fn from_units_value(raw: Option<&str>) -> Self {
        let Some(raw) = raw else { return Self::off() };
        let authorized_units = raw
            .split(',')
            .map(|entry| entry.trim().replace('-', "_"))
            .filter(|unit| {
                !unit.is_empty()
                    && unit.chars().all(|c| c.is_ascii_alphanumeric() || c == '_')
            })
            .collect();
        Self { authorized_units }
    }

    /// The production constructor: read the shim IPC channel from this
    /// process's environment.
    pub fn from_env() -> Self {
        match std::env::var(Self::SHIM_VERIFY_UNITS_ENV) {
            Ok(value) => Self::from_units_value(Some(&value)),
            Err(_) => Self::off(),
        }
    }

    /// Whether the lane authorizes any unit at all.
    pub fn is_active(&self) -> bool {
        !self.authorized_units.is_empty()
    }

    /// Whether the lane authorizes the named unit.
    pub fn authorizes_unit(&self, unit: &str) -> bool {
        self.authorized_units.iter().any(|authorized| authorized == unit)
    }
}

/// Per-DEF policy bucket detection: [`classify_crate`], narrowed for
/// the step-4 `core::num` target surface when — and only when — the
/// def belongs to the `core` unit this invocation was explicitly
/// authorized to verify.
///
/// With `lane` OFF this is definitionally [`classify_crate`] for every
/// def — nothing about a default build changes. With the lane ON, a
/// def is narrowed `UpstreamRustModified` → `TrustOwnedDefault` iff:
///
/// 1. the def is LOCAL (it belongs to the crate being compiled — i.e.
///    we are verifying `core` itself, not looking at `core` from a
///    user crate's dependency scope), and
/// 2. the local crate is `core` and the lane authorizes the `core`
///    unit, and
/// 3. the def is on the measured step-4 target surface
///    ([`def_is_step4_core_num_target`]).
///
/// Intended call site: `verification_decision` in
/// `compiler/rustc_mir_transform/src/trust_verify.rs`, replacing its
/// bare `classify_crate(tcx, def_id.krate)`. (Measured 2026-08-30:
/// that call site is the bucket's only live consumer;
/// `unsupported_is_failure` / `generate_obligations` have no callers
/// outside this module yet, so the step-4 gate/ratchet consumer must
/// key on the bucket via this function, not re-derive it.)
pub fn classify_def<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    lane: &LibraryVerificationLane,
) -> PolicyBucket {
    let bucket = classify_crate(tcx, def_id.krate);
    if bucket != PolicyBucket::UpstreamRustModified {
        return bucket;
    }
    if !lane_narrows_defs_of_crate(
        lane,
        def_id.krate == LOCAL_CRATE,
        tcx.crate_name(def_id.krate).as_str(),
    ) {
        return bucket;
    }
    if def_is_step4_core_num_target(tcx, def_id) {
        return PolicyBucket::TrustOwnedDefault;
    }
    bucket
}

/// The lane/locality conjunct of [`classify_def`], as a pure function
/// so its refusals are unit-testable without a `TyCtxt`.
///
/// `def_is_local` is what keeps user crates out: a user crate's
/// compile sees `core` defs as NON-local (dependency scope), and a
/// non-local def is never narrowed no matter what the environment
/// says. `crate_name == "core"` keeps the carve-out on the one unit
/// step 4 names; the plan's ladder (`core` before `alloc` before
/// `std`, §1.4) widens this deliberately, per step, never by default.
fn lane_narrows_defs_of_crate(
    lane: &LibraryVerificationLane,
    def_is_local: bool,
    crate_name: &str,
) -> bool {
    lane.is_active() && def_is_local && crate_name == "core" && lane.authorizes_unit(crate_name)
}

/// Step-4 target surface, from the plan (§5 step 4, verbatim):
/// "Target: `core::num`'s inherent integer methods — `checked_*`,
/// `wrapping_*`, `saturating_*`, `leading_zeros`/`trailing_zeros`/
/// `count_ones`, `overflowing_*`."
const STEP4_CORE_NUM_METHOD_PREFIXES: &[&str] =
    &["checked_", "wrapping_", "saturating_", "overflowing_"];

/// The three exact-name targets from the same plan sentence.
const STEP4_CORE_NUM_METHOD_EXACT: &[&str] = &["leading_zeros", "trailing_zeros", "count_ones"];

/// Helper inherent methods the targeted bodies call inside `core::num`.
///
/// MEASURED 2026-08-30 by reading every targeted body in
/// `library/core/src/num/{uint_macros,int_macros}.rs` (first-order
/// callees; intrinsics and out-of-`num` callees like
/// `Option::is_none` / `hint::assert_unchecked` excluded by design):
/// `cast_signed`/`cast_unsigned` (checked/saturating casts,
/// `checked_isqrt`), `div_euclid`/`rem_euclid`
/// (`checked_div_euclid`/`checked_rem_euclid`/`overflowing_*_euclid`),
/// `ilog2`/`ilog10` (`checked_ilog`), `is_negative`
/// (`checked_abs`/`saturating_abs`/`wrapping_abs`), `is_power_of_two`
/// and `pow` and `unsigned_abs` (`checked_ilog`/`checked_pow`/
/// `overflowing_pow`), `isqrt` (`checked_isqrt`),
/// `one_less_than_next_power_of_two`
/// (`checked_next_power_of_two`/`wrapping_next_power_of_two`),
/// `shl_exact`/`unbounded_shl` (`checked_pow`/`overflowing_pow`),
/// `unchecked_shl`/`unchecked_shr`
/// (`checked_shl`/`checked_shr`/`wrapping_shl`/`wrapping_shr`).
///
/// Second-order closure (e.g. `pow` → `strict_pow`) is deliberately
/// NOT swept in: an under-included helper stays
/// `UpstreamRustModified`, whose gap surfaces as a counted assumption
/// record in the lane run — a measurable prompt to grow this list by
/// measurement, not by guess.
const STEP4_CORE_NUM_HELPER_METHODS: &[&str] = &[
    "cast_signed",
    "cast_unsigned",
    "div_euclid",
    "rem_euclid",
    "ilog2",
    "ilog10",
    "is_negative",
    "is_power_of_two",
    "isqrt",
    "one_less_than_next_power_of_two",
    "pow",
    "shl_exact",
    "unbounded_shl",
    "unchecked_shl",
    "unchecked_shr",
    "unsigned_abs",
];

/// `NonZero` inherent methods reached from targeted bodies. MEASURED:
/// uint `checked_ilog2`/`checked_ilog10` are
/// `match NonZero::new(self) { Some(x) => Some(x.ilog2()/x.ilog10()) … }`;
/// `NonZero::ilog2` calls `NonZero::leading_zeros`; `NonZero::ilog10`
/// and `leading_zeros` call `get`.
const STEP4_CORE_NUM_NONZERO_HELPER_METHODS: &[&str] =
    &["new", "get", "ilog2", "ilog10", "leading_zeros"];

/// Free-function helper modules under `core::num::imp` reached from
/// targeted bodies. MEASURED: int `checked_ilog10` calls
/// `imp::int_log10::$ActualT` directly; `ilog2`/`ilog10` panic arms
/// call `imp::int_log10::panic_for_nonpositive_argument`; uint `isqrt`
/// (helper of `checked_isqrt`) calls `imp::int_sqrt::$ActualT`, whose
/// module also holds the private `*_stages` fns. The sibling
/// `imp::overflow_panic` is NOT reached by any targeted body (it
/// serves `strict_*`) and is NOT included.
const STEP4_CORE_NUM_IMP_HELPER_MODULES: &[&str] = &["int_log10", "int_sqrt"];

/// `core::num::traits` helper methods. MEASURED: `checked_truncate` /
/// `saturating_truncate` (swept in by the `checked_`/`saturating_`
/// prefixes) call `traits::TruncateTarget::internal_checked_truncate`
/// / `internal_saturating_truncate`, whose impls live in
/// `library/core/src/num/traits.rs`.
const STEP4_CORE_NUM_TRAIT_HELPER_METHODS: &[&str] =
    &["internal_checked_truncate", "internal_saturating_truncate"];

fn step4_targeted_or_helper_method(name: &str) -> bool {
    STEP4_CORE_NUM_METHOD_PREFIXES.iter().any(|prefix| name.starts_with(prefix))
        || STEP4_CORE_NUM_METHOD_EXACT.contains(&name)
        || STEP4_CORE_NUM_HELPER_METHODS.contains(&name)
}

/// Whether `def_id` is on the measured step-4 `core::num` target
/// surface. Pure def-path + impl-metadata shape check; no trait
/// solver, no MIR.
///
/// Shapes accepted (def-path spine relative to the crate root):
///
/// 1. `num::<inherent impl on {i,u}{8,16,32,64,128,size}>::<targeted
///    or helper method>` — the impl must be inherent and its self type
///    an integer primitive, so a targeted NAME on some other type in
///    `num` (or any trait impl) never matches.
/// 2. `num::imp::{int_log10,int_sqrt}::<any fn>` — the two measured
///    leaf helper modules, whole.
/// 3. `num::nonzero::<inherent impl>::<measured NonZero helper>`.
/// 4. `num::traits::<impl>::{internal_checked_truncate,
///    internal_saturating_truncate}`.
///
/// Nested defs (closures, anon consts) under targeted methods carry a
/// longer spine and deliberately do NOT match: they stay on the
/// lenient bucket, which is the honest under-claim.
fn def_is_step4_core_num_target<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId) -> bool {
    let def_path = tcx.def_path(def_id);
    let Some((last, spine)) = def_path.data.split_last() else { return false };
    let DefPathData::ValueNs(method) = last.data else { return false };
    let method = method.as_str();

    let spine: Vec<&DefPathData> = spine.iter().map(|component| &component.data).collect();
    match spine.as_slice() {
        // Shape 1: core::num::<impl {integer}>::{method}
        [DefPathData::TypeNs(module), DefPathData::Impl]
            if module.as_str() == "num" && step4_targeted_or_helper_method(method) =>
        {
            impl_is_inherent_on_integer_primitive(tcx, tcx.parent(def_id))
        }
        // Shape 2: core::num::imp::{int_log10,int_sqrt}::{fn}
        [
            DefPathData::TypeNs(module),
            DefPathData::TypeNs(imp_module),
            DefPathData::TypeNs(leaf),
        ] if module.as_str() == "num"
            && imp_module.as_str() == "imp"
            && STEP4_CORE_NUM_IMP_HELPER_MODULES.contains(&leaf.as_str()) =>
        {
            true
        }
        // Shape 3: core::num::nonzero::<inherent impl>::{helper}
        [
            DefPathData::TypeNs(module),
            DefPathData::TypeNs(nonzero_module),
            DefPathData::Impl,
        ] if module.as_str() == "num"
            && nonzero_module.as_str() == "nonzero"
            && STEP4_CORE_NUM_NONZERO_HELPER_METHODS.contains(&method) =>
        {
            matches!(tcx.def_kind(tcx.parent(def_id)), DefKind::Impl { of_trait: false })
        }
        // Shape 4: core::num::traits::<impl>::{internal_*_truncate}
        [
            DefPathData::TypeNs(module),
            DefPathData::TypeNs(traits_module),
            DefPathData::Impl,
        ] if module.as_str() == "num"
            && traits_module.as_str() == "traits"
            && STEP4_CORE_NUM_TRAIT_HELPER_METHODS.contains(&method) =>
        {
            true
        }
        _ => false,
    }
}

fn impl_is_inherent_on_integer_primitive<'tcx>(tcx: TyCtxt<'tcx>, impl_did: DefId) -> bool {
    if !matches!(tcx.def_kind(impl_did), DefKind::Impl { of_trait: false }) {
        return false;
    }
    let self_ty = tcx.type_of(impl_did).instantiate_identity().skip_normalization();
    matches!(self_ty.kind(), TyKind::Int(_) | TyKind::Uint(_))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn tags_are_stable() {
        for tag in [
            PolicyBucket::TrustOwnedSpecBearing.tag(),
            PolicyBucket::TrustOwnedDefault.tag(),
            PolicyBucket::UpstreamRustModified.tag(),
            PolicyBucket::ExternalDep.tag(),
            PolicyBucket::Unknown.tag(),
        ] {
            assert!(!tag.is_empty());
            assert!(tag.chars().all(|c| c.is_ascii_lowercase() || c == '-'));
        }
    }

    #[test]
    fn external_dep_is_boundary_only() {
        assert!(!PolicyBucket::ExternalDep.generate_obligations());
        assert!(!PolicyBucket::ExternalDep.unsupported_is_failure());
    }

    #[test]
    fn upstream_modified_records_assumptions_not_failures() {
        let b = PolicyBucket::UpstreamRustModified;
        assert!(b.generate_obligations());
        assert!(!b.unsupported_is_failure());
    }

    #[test]
    fn trust_owned_is_strict() {
        assert!(PolicyBucket::TrustOwnedSpecBearing.unsupported_is_failure());
        assert!(PolicyBucket::TrustOwnedDefault.unsupported_is_failure());
    }

    /// FALSIFIES: "a degenerate or absent lane value could activate the
    /// carve-out". Every non-authorizing input must parse to the OFF
    /// lane, and authorization must be per-unit exact.
    #[test]
    fn lane_parses_fail_closed() {
        assert!(!LibraryVerificationLane::off().is_active());
        assert!(!LibraryVerificationLane::from_units_value(None).is_active());
        assert!(!LibraryVerificationLane::from_units_value(Some("")).is_active());
        assert!(!LibraryVerificationLane::from_units_value(Some(",, ,")).is_active());
        // A malformed entry authorizes nothing (bootstrap hard-errors on
        // these upstream; here they must simply be inert).
        assert!(!LibraryVerificationLane::from_units_value(Some("core;alloc")).is_active());
        assert!(!LibraryVerificationLane::from_units_value(Some("../core")).is_active());

        let lane = LibraryVerificationLane::from_units_value(Some("core"));
        assert!(lane.is_active());
        assert!(lane.authorizes_unit("core"));
        assert!(!lane.authorizes_unit("alloc"));
        assert!(!lane.authorizes_unit("std"));

        // Bootstrap normalization: trim + `-` → `_`.
        let lane = LibraryVerificationLane::from_units_value(Some(" core , panic-abort "));
        assert!(lane.authorizes_unit("core"));
        assert!(lane.authorizes_unit("panic_abort"));

        // One malformed entry does not poison a well-formed sibling.
        let lane = LibraryVerificationLane::from_units_value(Some("core,b?d"));
        assert!(lane.authorizes_unit("core"));
        assert!(!lane.authorizes_unit("b?d"));
    }

    /// FALSIFIES: "the carve-out could reach a user crate or a
    /// dependency-scoped `core` def". The conjunct is pure, so the
    /// non-local case — a user crate compiling against `core`, where
    /// `core` defs are NON-local — is directly testable: it must never
    /// narrow, with the lane fully active and the crate name exactly
    /// `core`.
    #[test]
    fn lane_narrowing_requires_local_core_under_authorized_lane() {
        let core_lane = LibraryVerificationLane::from_units_value(Some("core"));
        let std_lane = LibraryVerificationLane::from_units_value(Some("std"));
        let off = LibraryVerificationLane::off();

        // The one authorized shape.
        assert!(lane_narrows_defs_of_crate(&core_lane, true, "core"));

        // A `core` def seen from a USER crate compile is non-local.
        assert!(!lane_narrows_defs_of_crate(&core_lane, false, "core"));
        // Lane off: nothing narrows.
        assert!(!lane_narrows_defs_of_crate(&off, true, "core"));
        // Lane on for a different unit: `core` defs stay untouched.
        assert!(!lane_narrows_defs_of_crate(&std_lane, true, "core"));
        // Step 4 is `core`-only; other std-family units are later rungs.
        assert!(!lane_narrows_defs_of_crate(&std_lane, true, "std"));
        assert!(!lane_narrows_defs_of_crate(&core_lane, true, "alloc"));
        // A user crate is never narrowed even if it names itself oddly.
        assert!(!lane_narrows_defs_of_crate(&core_lane, true, "my_crate"));
    }

    // -----------------------------------------------------------------
    // Compiler-driving tests: classify real defs of a crate named
    // `core` (no_core fixture; the primitive impls use
    // `#[rustc_allow_incoherent_impl]`, the same mechanism
    // `library/core` itself relies on for incoherent impls).
    // -----------------------------------------------------------------

    extern crate rustc_driver;
    extern crate rustc_interface;

    use std::collections::BTreeMap;
    use std::io;
    use std::path::{Path, PathBuf};
    use std::sync::{Arc, OnceLock};

    use rustc_driver::Compilation;
    use rustc_interface::interface::{Compiler, Config};

    const CORE_NUM_LANE_FIXTURE_PATH: &str = "trust_policy_core_num_lane_fixture.rs";

    const CORE_NUM_LANE_FIXTURE_SOURCE: &str = r#"
#![feature(auto_traits, lang_items, no_core, rustc_attrs)]
#![allow(internal_features)]
#![no_core]

#[lang = "sized"]
pub trait Sized: MetaSized {}

#[lang = "meta_sized"]
pub trait MetaSized: PointeeSized {}

#[lang = "pointee_sized"]
pub trait PointeeSized {}

#[lang = "copy"]
pub trait Copy: Clone {}

#[lang = "clone"]
pub trait Clone {}

#[lang = "freeze"]
pub unsafe auto trait Freeze {}

pub mod num {
    // Targeted inherent integer methods: one prefix-family entry and
    // one exact-name entry, plus one measured helper.
    impl u32 {
        #[rustc_allow_incoherent_impl]
        pub fn checked_add(self, rhs: u32) -> u32 { rhs }
        #[rustc_allow_incoherent_impl]
        pub fn count_ones(self) -> u32 { self }
        #[rustc_allow_incoherent_impl]
        pub fn unchecked_shl(self, rhs: u32) -> u32 { rhs }
        // Right module, right impl shape, name NOT on the surface.
        #[rustc_allow_incoherent_impl]
        pub fn midpoint(self, rhs: u32) -> u32 { rhs }
    }

    // A targeted-prefix NAME on a non-integer self type.
    pub struct Widget;
    impl Widget {
        pub fn checked_mul(self) -> Widget { self }
    }

    // A free fn directly in `num` matches no carve-out shape.
    pub fn free_in_num() {}

    pub mod imp {
        pub mod int_log10 {
            pub fn u32_impl(v: u32) -> u32 { v }
        }
        pub mod int_sqrt {
            pub fn u32_stages(v: u32) -> u32 { v }
        }
        // Sibling module NOT in the measured closure.
        pub mod overflow_panic {
            pub fn add() {}
        }
    }

    pub mod nonzero {
        pub struct NonZero(pub u32);
        impl NonZero {
            // Measured helpers (uint checked_ilog2/checked_ilog10 path).
            pub fn new(v: u32) -> NonZero { NonZero(v) }
            pub fn ilog10(self) -> u32 { self.0 }
            // NOT in the measured helper set.
            pub fn widening_mul(self) -> u32 { self.0 }
        }
    }

    pub mod traits {
        pub trait TruncateTarget: crate::Sized {
            fn internal_checked_truncate(self) -> u8;
            fn other_method(self) -> u8;
        }
        impl TruncateTarget for u8 {
            fn internal_checked_truncate(self) -> u8 { self }
            fn other_method(self) -> u8 { self }
        }
    }
}

pub mod fmt {
    // Non-targeted module: must stay on the crate bucket under the lane.
    pub fn write_something() {}
    impl u8 {
        // Targeted NAME in the wrong module.
        #[rustc_allow_incoherent_impl]
        pub fn checked_add(self, rhs: u8) -> u8 { rhs }
    }
}
"#;

    struct InMemoryCoreNumLaneFileLoader;

    impl rustc_span::source_map::FileLoader for InMemoryCoreNumLaneFileLoader {
        fn file_exists(&self, path: &Path) -> bool {
            path == Path::new(CORE_NUM_LANE_FIXTURE_PATH)
        }

        fn read_file(&self, path: &Path) -> io::Result<String> {
            if self.file_exists(path) {
                Ok(CORE_NUM_LANE_FIXTURE_SOURCE.to_string())
            } else {
                Err(io::Error::other("unexpected core-num lane fixture path"))
            }
        }

        fn read_binary_file(&self, _path: &Path) -> io::Result<Arc<[u8]>> {
            Err(io::Error::other("binary reads are not supported in policy tests"))
        }

        fn current_directory(&self) -> io::Result<PathBuf> {
            std::env::current_dir()
        }
    }

    /// The three classifications of one def: under the core-authorized
    /// lane, under the OFF lane, and under a lane that authorizes a
    /// DIFFERENT unit (`std`).
    #[derive(Clone, Copy, Debug, PartialEq)]
    struct LaneBuckets {
        core_lane: PolicyBucket,
        off: PolicyBucket,
        std_only_lane: PolicyBucket,
    }

    #[derive(Default)]
    struct CoreNumLaneCallbacks {
        buckets: BTreeMap<String, LaneBuckets>,
    }

    impl rustc_driver::Callbacks for CoreNumLaneCallbacks {
        fn config(&mut self, config: &mut Config) {
            config.file_loader = Some(Box::new(InMemoryCoreNumLaneFileLoader));
        }

        fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
            tcx.sess.dcx().abort_if_errors();

            let core_lane = LibraryVerificationLane::from_units_value(Some("core"));
            let off = LibraryVerificationLane::off();
            let std_only_lane = LibraryVerificationLane::from_units_value(Some("std"));

            for local_def_id in tcx.hir_body_owners() {
                let def_id = local_def_id.to_def_id();
                if !matches!(tcx.def_kind(def_id), DefKind::Fn | DefKind::AssocFn) {
                    continue;
                }
                let key = tcx.def_path(def_id).to_string_no_crate_verbose();
                self.buckets.insert(
                    key,
                    LaneBuckets {
                        core_lane: classify_def(tcx, def_id, &core_lane),
                        off: classify_def(tcx, def_id, &off),
                        std_only_lane: classify_def(tcx, def_id, &std_only_lane),
                    },
                );
            }

            Compilation::Stop
        }
    }

    fn core_num_lane_buckets() -> &'static BTreeMap<String, LaneBuckets> {
        static RESULTS: OnceLock<BTreeMap<String, LaneBuckets>> = OnceLock::new();
        RESULTS.get_or_init(|| {
            let mut callbacks = CoreNumLaneCallbacks::default();
            let args = vec![
                "rustc".to_string(),
                CORE_NUM_LANE_FIXTURE_PATH.to_string(),
                "--crate-name".to_string(),
                "core".to_string(),
                "--crate-type=lib".to_string(),
                "--edition=2021".to_string(),
                "-Zno-codegen".to_string(),
                // Stop in `after_analysis`; the built-in dummy backend is
                // the rustc-supported analysis-only route (see the
                // convert.rs fixtures for why a dylib probe is unsafe
                // here).
                "-Zcodegen-backend=dummy".to_string(),
                // These tests exercise CLASSIFICATION, not the
                // batteries-on verification pass.
                "-Ztrust-verify=off".to_string(),
                "-Ainternal_features".to_string(),
            ];
            let result =
                rustc_driver::catch_fatal_errors(|| -> rustc_interface::interface::Result<()> {
                    rustc_driver::run_compiler(&args, &mut callbacks);
                    Ok(())
                });
            assert!(result.is_ok(), "failed to compile the core-num lane fixture crate");
            assert!(
                !callbacks.buckets.is_empty(),
                "core-num lane fixture produced no classified defs"
            );
            callbacks.buckets
        })
    }

    /// Exactly one def whose key starts with `prefix` and ends with
    /// `suffix`; a miss or an ambiguity is a fixture bug and must fail
    /// loudly.
    fn bucket_for(prefix: &str, suffix: &str) -> LaneBuckets {
        let map = core_num_lane_buckets();
        let matches: Vec<_> = map
            .iter()
            .filter(|(key, _)| key.starts_with(prefix) && key.ends_with(suffix))
            .collect();
        assert!(
            matches.len() == 1,
            "expected exactly one def matching {prefix}…{suffix}, got {matches:?}"
        );
        *matches[0].1
    }

    /// FALSIFIES: "a targeted `core::num` def under the lane is still
    /// classified `UpstreamRustModified`" — i.e. the exercise would
    /// produce assumption records rather than proofs, the exact
    /// failure mode the plan's step 4 calls out.
    #[test]
    fn step4_lane_narrows_targeted_core_num_defs() {
        for (prefix, suffix) in [
            ("::num::{impl", "::checked_add"),  // prefix family
            ("::num::{impl", "::count_ones"),   // exact-name family
            ("::num::{impl", "::unchecked_shl"), // measured helper
        ] {
            let buckets = bucket_for(prefix, suffix);
            assert_eq!(
                buckets.core_lane,
                PolicyBucket::TrustOwnedDefault,
                "{prefix}…{suffix} must narrow to TrustOwnedDefault under the core lane"
            );
        }
    }

    /// FALSIFIES: "the carve-out changes anything when the lane is off
    /// or aimed at a different unit". Same defs, no lane (or a
    /// `std`-only lane): the bucket must be exactly `classify_crate`'s
    /// answer for `core`.
    #[test]
    fn step4_lane_off_leaves_core_num_unchanged() {
        for (prefix, suffix) in [
            ("::num::{impl", "::checked_add"),
            ("::num::{impl", "::count_ones"),
            ("::num::{impl", "::unchecked_shl"),
        ] {
            let buckets = bucket_for(prefix, suffix);
            assert_eq!(
                buckets.off,
                PolicyBucket::UpstreamRustModified,
                "{prefix}…{suffix} must stay UpstreamRustModified with the lane OFF"
            );
            assert_eq!(
                buckets.std_only_lane,
                PolicyBucket::UpstreamRustModified,
                "{prefix}…{suffix} must stay UpstreamRustModified under a std-only lane"
            );
        }
    }

    /// FALSIFIES: "the carve-out leaks past the measured surface".
    /// Non-targeted defs — a `core::fmt` fn, a targeted NAME in the
    /// wrong module, a targeted-prefix name on a non-integer type, a
    /// non-helper `num` free fn, the unmeasured `imp::overflow_panic`
    /// sibling, a non-helper `NonZero` method, and a non-helper
    /// `num::traits` impl method — must ALL stay
    /// `UpstreamRustModified` with the lane fully active.
    #[test]
    fn step4_lane_leaves_non_targeted_defs_unchanged() {
        for (prefix, suffix) in [
            ("::fmt::", "::write_something"),      // core::fmt fn
            ("::fmt::{impl", "::checked_add"),     // targeted name, wrong module
            ("::num::{impl", "::midpoint"),        // right impl, non-targeted name
            ("::num::{impl", "::checked_mul"),     // targeted prefix, Widget self ty
            ("::num::", "::free_in_num"),          // free fn directly in num
            ("::num::imp::overflow_panic", "::add"), // unmeasured imp sibling
            ("::num::nonzero::{impl", "::widening_mul"), // non-helper NonZero method
            ("::num::traits::{impl", "::other_method"), // non-helper trait method
        ] {
            let buckets = bucket_for(prefix, suffix);
            assert_eq!(
                buckets.core_lane,
                PolicyBucket::UpstreamRustModified,
                "{prefix}…{suffix} must NOT be narrowed by the core lane"
            );
            assert_eq!(buckets.off, PolicyBucket::UpstreamRustModified);
        }
    }

    /// FALSIFIES: "the measured helper closure is not actually covered"
    /// — an uncovered helper would keep minting assumption records
    /// underneath a 'proved' targeted method.
    #[test]
    fn step4_lane_covers_measured_helper_closure() {
        for (prefix, suffix) in [
            ("::num::imp::int_log10", "::u32_impl"),
            ("::num::imp::int_sqrt", "::u32_stages"),
            ("::num::nonzero::{impl", "::new"),
            ("::num::nonzero::{impl", "::ilog10"),
            ("::num::traits::{impl", "::internal_checked_truncate"),
        ] {
            let buckets = bucket_for(prefix, suffix);
            assert_eq!(
                buckets.core_lane,
                PolicyBucket::TrustOwnedDefault,
                "{prefix}…{suffix} is a measured helper and must narrow under the core lane"
            );
            assert_eq!(
                buckets.off,
                PolicyBucket::UpstreamRustModified,
                "{prefix}…{suffix} must stay UpstreamRustModified with the lane OFF"
            );
        }
    }
}
