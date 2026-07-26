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
//! No trait-solver calls — pure metadata. Cost is O(1) per crate.
//!
//! Author: Andrew Yates | Copyright 2026 Andrew Yates | License: Apache-2.0

use rustc_middle::ty::TyCtxt;
use rustc_span::def_id::CrateNum;

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
}
