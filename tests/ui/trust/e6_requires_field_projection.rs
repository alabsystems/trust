//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-pass
// This file runs at the default per-obligation budget (20 s). It ran at 2 s,
// with every per-function verdict measured identical at 0.5 s, 2 s and 20 s
// (2026-09-23, 96f2019566), to save the time an engine burns on an obligation
// it cannot decide. That no longer holds at ay main 01b58012 (Trust train T8,
// 2026-10-07). The in-process refutation of `num_patches`' `grid * grid`
// splits its query into four disjoint components, each with a quarter of the
// budget, and ay now takes 0.58 s on the QF_NIA one
// (`0 <= g <= 2^64-1 and (g*g < 0 or g*g > 2^64-1)`) where ay 630e4d62 took
// 0.07 s (the ay CLI on the same program). At 2 s (0.5 s a component) the
// refutation misses and the row reads runtime-checked; at 5 s it held alone
// but missed under the ui suite's load. At 20 s every verdict is the one
// pinned below. The ay slowdown itself is not fixed here; the
// `Trust verification:` NOTE pins fail if a budget ever changes a verdict.
//! E6 — a `requires` CLAUSE MAY PROJECT A FIELD OF A PARAMETER.
//!
//! Until this landed, the native clause grammar accepted only plain scalar
//! parameters in a `requires`. `requires self.patch_size != 0` and
//! `requires c.patch_size != 0` were HARD ERRORS —
//! "source-contract variable `self`/`c` is not in scope" — while the
//! byte-identical `ensures` spelling proved (`e9_field_projection_discharge.rs`).
//! The asymmetry was structural, not semantic: a native function `requires` is
//! admitted by `lower_native_clause`, which types the AUTHORED text against
//! `function_source_sorts` (bare parameter bindings only) and carries no
//! `ProjectionEnvironment`; native `ensures` is excluded from that lane and
//! already reached the projection-aware snippet lane.
//!
//! That mattered because real invariants are about STRUCT FIELDS. The case
//! below is verbatim from `nn-core`'s `VitConfig`: `num_patches` divides by
//! `self.patch_size`, and `validate()` already checks `patch_size != 0` —
//! seventeen lines away, in a different function, so nothing at the division
//! site could use it.
//!
//! WHAT THE CLAUSE MEANS. The authored chain is resolved verbatim through
//! `ProjectionEnvironment`, built by walking the REAL field layout of the
//! parameter's type, to the canonical place text `(*self).5` — POSITIONAL,
//! because `place_to_var_name` renders `Field(i)` as `.i` and never by name.
//! That text parses to the var `self*.5`, byte-identical to the name
//! `trust_vcgen::place_to_var_name` mints for the MIR place `(*_1).5`. So the
//! clause denotes the FIELD AT THAT PLACE, never a fresh symbol.
//!
//! WHEN IT IS EVALUATED. At ENTRY, in the caller's pre-state, on both sides:
//! the callee conjoins it as an entry-named fact (`conjoin_preconditions_versioned`
//! version-renames the VC body, so a precondition about a place the body
//! reassigns is name-disjoint and inert), and each call site asserts it with
//! the callee's formals substituted by the caller's actuals
//! (`substitute_summary_params` rebinds `<formal>*.<i>` by splitting the base
//! and reattaching the field suffix).
//!
//! Companions: `e6_requires_field_projection_caller_refused.rs` is the
//! non-guarding caller, which must FAIL; `e6_requires_field_projection_refused.rs`
//! pins every projection with no exact scalar place as a hard error.

#[derive(Clone, Debug)]
#[non_exhaustive]
pub struct VitConfig {
    pub num_channels: usize,
    pub hidden_size: usize,
    pub num_layers: usize,
    pub num_heads: usize,
    pub intermediate_size: usize,
    pub patch_size: usize,
    pub image_size: usize,
    pub layer_norm_eps: f64,
    pub use_cls_token: bool,
}

pub enum TensorError {
    ValueOutOfRange { description: &'static str },
}

impl VitConfig {
    /// THE CASE, verbatim. The division by `self.patch_size` is DISCHARGED by
    /// the clause. Measured both ways on the same body:
    ///
    /// ```text
    ///   without the clause:  [divzero] FAILED; counterexample: self*.5 = 0
    ///   with the clause:     divzero proved
    /// ```
    ///
    /// The counterexample naming `self*.5` is the evidence that the projection
    /// is BOUND rather than free: a free variable would be spuriously SAT under
    /// a name the body never mentions.
    ///
    /// The `grid * grid` OVERFLOW obligation still fails, and that is correct —
    /// it is a different, real obligation about `image_size`, which this clause
    /// says nothing about. This file runs `-Ztrust-policy=advisory` so that
    /// genuine residue does not mask the result being pinned.
    #[must_use]
    pub fn num_patches(&self) -> usize
        requires self.patch_size != 0
    {
        //~^^^ NOTE Trust verification: 1 proved, 1 failed, 0 unknown
        let grid = self.image_size / self.patch_size;
        grid * grid
    }

    /// The real in-file caller. On the unmodified source this is refused with
    /// `[precond] FAILED; counterexample: self*.5 = 0` — the burden reached it
    /// BY NAME. Restating the same projected fact discharges it, which is the
    /// ordinary contract-propagation move and the thing the whole feature is
    /// for: the fact travels with the call graph instead of being re-derived at
    /// every division.
    #[must_use]
    pub fn seq_len(&self) -> usize
        requires self.patch_size != 0
    {
        //~^^^ NOTE Trust verification: 1 proved, 1 failed, 0 unknown
        let n = self.num_patches();
        if self.use_cls_token { n + 1 } else { n }
    }

    /// The check that was always there, seventeen lines away.
    pub fn validate(&self) -> Result<(), TensorError> {
        if self.patch_size == 0 {
            return Err(TensorError::ValueOutOfRange {
                description: "VitConfig: patch_size must be > 0",
            });
        }
        Ok(())
    }
}

/// The same fact stated on a free function over a SHARED REFERENCE — the other
/// spelling measured as a hard error before this landed.
pub fn grid_of(c: &VitConfig) -> usize
    requires c.patch_size != 0
{
    //~^^^ NOTE Trust verification: 1 proved, 0 failed, 0 unknown
    c.image_size / c.patch_size
}

/// And over a BY-VALUE aggregate parameter, whose canonical place carries no
/// deref segment (`c.5`, not `c*.5`).
pub fn grid_of_owned(c: VitConfig) -> usize
    requires c.patch_size != 0
{
    //~^^^ NOTE Trust verification: 1 proved, 0 failed, 0 unknown
    c.image_size / c.patch_size
}

/// GUARDING CALLER. The burden transferred BY NAME: the callee's `self*.5` is
/// rebound at this call site to the actual's own field (`substitute_summary_params`
/// splits base + suffix and reattaches `*.5` to the actual), and the dominating
/// guard discharges it. No `[precond]` row fails here.
///
/// The companion file removes the guard and the same row is REFUTED with
/// `[precond] FAILED; counterexample: c*.0 = 0`. Both directions are needed:
/// an unbound projection would be spuriously SAT and fail here too.
pub fn guarded(c: &VitConfig) -> usize {
    //~^ NOTE Trust verification: 1 proved, 0 failed, 0 unknown
    if c.patch_size != 0 { c.num_patches() } else { 0 }
}

/// The same guard against the FREE-FUNCTION callee — the two call shapes take
/// different σ paths (a method call reborrows the already-`&` receiver, a free
/// call passes the argument through a `Use(Copy)` temp), and both discharge.
pub fn guarded_free(c: &VitConfig) -> usize {
    //~^ NOTE Trust verification: 1 proved, 0 failed, 0 unknown
    if c.patch_size != 0 { grid_of(c) } else { 0 }
}

fn main() {}
