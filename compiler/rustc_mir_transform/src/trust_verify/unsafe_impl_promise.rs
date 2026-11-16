//! Trust (2026-09-29): AN `unsafe impl` OF A FOREIGN TRAIT IS A PROMISE NO LANE
//! CHECKS, AND THE CODE THAT RELIES ON IT IS CODE THIS BUILD DOES NOT VERIFY.
//!
//! docs/KNOWN_HAZARDS.md, "CLOSED 2026-09-29 — a local `unsafe impl` of a
//! foreign unsafe trait (a user `Allocator`) was believed by the std code that
//! calls it", is the hazard this closes.
//!
//! ## The hole
//!
//! An `unsafe trait` states a contract its IMPLEMENTER must uphold and its
//! CALLERS may rely on for memory safety: `core::alloc::Allocator` ("the
//! returned block is valid for the layout"), `GlobalAlloc`, the nightly
//! `TrustedLen` ("`size_hint` is exact"), `str::pattern::Searcher` ("every
//! reported index is a char boundary"), ... The implementing body is ordinary
//! code, and Trust verifies it as such — its panics and its own `unsafe`
//! operations. Nothing verifies the CONTRACT: that `allocate` really returns
//! memory, or that `size_hint` is really exact. And the code that relies on the
//! contract is the trait owner's — std, for a sysroot trait — whose memory
//! operations Trust credits under the sysroot premise ("std's safe API is
//! sound"). That premise is conditional on every `unsafe impl` std calls into
//! being correct.
//!
//! Measured on main (`0.10.0+g4715fe060`, source of `7eddcd160b`): a local
//! `unsafe impl Allocator for Bad` whose `allocate` returns
//! `NonNull::slice_from_raw_parts(NonNull::dangling(), l.size())` — safe code,
//! no row of its own — handed to `HashMap::with_hasher_in(RandomState::new(),
//! Bad)` behind `ManuallyDrop` built rc=0: the std-side `insert` was bundled and
//! credited, hashbrown wrote its control bytes through the dangling pointer, and
//! the program died of SIGSEGV (exit 139). Without the `ManuallyDrop` the same
//! program was refused only by an unrelated drop-glue row.
//!
//! ## The rule
//!
//! In a verifying compilation, every LOCAL positive impl of a NON-LOCAL `unsafe
//! trait` that is not an auto trait is an unverified safety promise, and the
//! crate is refused on it: an error under every fail-closed policy (the default,
//! `certify`, `memory-safe` — the violation is undefined behaviour, not a
//! panic), a warning under the explicit advisory survey. It is decided per
//! impl, from the impl's own header and the trait's identity, never from a name.
//!
//! * A LOCAL `unsafe trait` is out of scope: its contract is relied on only by
//!   this crate's own code, whose `unsafe` operations carry their own rows.
//! * AUTO traits (`Send`, `Sync`) are out of scope and stay an open premise:
//!   their contract is thread-safety, which no Trust lane models (v6/D2 keeps
//!   the concurrency kinds unrouted), and refusing every `unsafe impl Send` would
//!   refuse ordinary concurrent Rust wholesale. Recorded as remaining work in the
//!   KNOWN_HAZARDS entry.
//! * A dependency's own `unsafe impl` is the dependency-soundness premise every
//!   verify-off crate already rests on (docs/TCB.md): out of scope here.
//! * An impl a BUILTIN derive generated (`tcx.is_builtin_derived`: the impl is
//!   `#[automatically_derived]` AND its span's outermost expansion is a
//!   `#[rustc_builtin_macro]` derive) is the compiler's promise, not the
//!   program's: `#[derive(Clone, Copy)]` emits `unsafe impl TrivialClone` only
//!   when the `Clone` it emits beside it is the bitwise copy `*self`
//!   (`rustc_builtin_macros::deriving::clone`, `is_simple`), which is exactly
//!   the trait's contract. The compiler that writes the impl is already in the
//!   trusted base. A proc-macro derive, a `macro_rules!` expansion, or a
//!   hand-written impl carrying `#[automatically_derived]` is not a builtin
//!   derive and stays refused. Measured 2026-09-30 on the first version of this
//!   rule (`0.10.0+g2a7366482`): without this exemption every `#[derive(Clone,
//!   Copy)]` of a non-generic type was refused (ten ui fixtures that derive
//!   `Clone, Copy` went red).
//!
//! What it costs: a CORRECT local allocator (a bump allocator over a static
//! buffer) is refused too, because no lane can tell it from `Bad`. Every such
//! SYSROOT impl is nightly-only (`allocator_api`, `trusted_len`, `pattern`, ...)
//! except `GlobalAlloc`, and a user `#[global_allocator]` was already refused on
//! its `dealloc` contract. A dependency's unsafe trait is in scope on stable
//! (`unsafe impl bytemuck::Pod`, or the impl a proc-macro derive writes: a proc
//! macro is not a builtin derive). The honest recovery is a lane that verifies the contract
//! at the impl — the discharge `GlobalAlloc`'s contract row already plans — not
//! a narrower rule.

use super::*;

/// The repair note every refusal carries.
const OPTIONS: &str = "the impl's method bodies are still verified as ordinary code; what is \
     refused is the contract itself. Options: use the std-provided implementation (the default \
     `Global` allocator, a std iterator adapter), or `-Z trust-policy=advisory` to record this as \
     a warning";

/// One refused promise: the impl, and the trait whose contract it makes.
struct UnverifiedUnsafeImpl {
    impl_def_id: LocalDefId,
    trait_def_id: DefId,
}

/// Every local positive impl of a non-local, non-auto `unsafe trait` that no
/// builtin derive generated, in the order `all_local_trait_impls` yields them (a
/// stable, source-derived order), so the diagnostics are deterministic.
fn unverified_unsafe_impls(tcx: TyCtxt<'_>) -> Vec<UnverifiedUnsafeImpl> {
    let mut found = Vec::new();
    for (&trait_def_id, impls) in tcx.all_local_trait_impls(()) {
        if trait_def_id.is_local() || tcx.trait_is_auto(trait_def_id) {
            continue;
        }
        if !matches!(tcx.trait_def(trait_def_id).safety, rustc_hir::Safety::Unsafe) {
            continue;
        }
        for &impl_def_id in impls {
            let header = tcx.impl_trait_header(impl_def_id.to_def_id());
            if header.polarity != ty::ImplPolarity::Positive
                || !matches!(header.safety, rustc_hir::Safety::Unsafe)
            {
                continue;
            }
            // The compiler's own promise (see the module doc): a builtin derive
            // writes an `unsafe impl` only where its contract holds by
            // construction. `is_builtin_derived` asks the expansion, not a name.
            if tcx.is_builtin_derived(impl_def_id.to_def_id()) {
                continue;
            }
            found.push(UnverifiedUnsafeImpl { impl_def_id, trait_def_id });
        }
    }
    found
}

/// Refuse (or, under the explicit advisory survey, report) every unverified
/// `unsafe impl` promise of this crate. See the module doc. Crate-level: an
/// impl with no method (a marker `unsafe trait` like `TrustedLen`) has no body
/// a per-function gate could hang the refusal on.
pub(super) fn refuse_unverified_unsafe_impl_promises(tcx: TyCtxt<'_>, policy: &TrustVerifyPolicy) {
    for promise in unverified_unsafe_impls(tcx) {
        let trait_path = tcx.def_path_str(promise.trait_def_id);
        let span = tcx.def_span(promise.impl_def_id);
        let sysroot = trust_mir_extract::def_is_in_real_sysroot_crate(tcx, promise.trait_def_id);
        let relier = if sysroot {
            "std/core/alloc code, whose memory operations Trust credits under the sysroot \
             premise that every `unsafe impl` it calls into is correct"
        } else {
            "the dependency that owns the trait, whose code this build does not verify"
        };
        let message = format!(
            "Trust verification cannot accept `unsafe impl {trait_path}`: the impl promises the \
             trait's safety contract, and no Trust lane verifies that promise"
        );
        let reliance = format!(
            "the promise is relied on by {relier}; if it is false (an `Allocator` that returns \
             memory it does not own, a `TrustedLen` whose `size_hint` is wrong) that code has \
             undefined behaviour with no obligation of this crate covering it"
        );
        // `struct_span_err` and `struct_span_warn` yield different `Diag` payload
        // types, so the two levels are emitted separately (the same shape as the
        // default-policy gate in `abort_on_full_verification_failure`).
        if policy.fail_closed() {
            tcx.dcx().struct_span_err(span, message).with_note(reliance).with_note(OPTIONS).emit();
        } else {
            tcx.dcx()
                .struct_span_warn(span, message)
                .with_note(reliance)
                .with_note(OPTIONS)
                .with_note(
                    "reported, not failed, only because this is the explicit advisory survey; \
                     every fail-closed policy refuses it",
                )
                .emit();
        }
    }
}
