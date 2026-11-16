//! Trust (2026-10-02): A VERIFYING BUILD FOR A TARGET WHOSE POINTERS ARE NARROWER
//! THAN 64 BITS IS REFUSED UNDER EVERY FAIL-CLOSED POLICY.
//!
//! docs/KNOWN_HAZARDS.md, "CLOSED 2026-10-02 — on a target narrower than 64 bits,
//! the default policy's 64-bit allocation premises accepted programs that panic",
//! is the hazard this closes.
//!
//! ## The hole
//!
//! Several things the default policy accepts without a proof rest on a 64-bit
//! address space, and none of them asks the target's width:
//!
//! * the push-growth class (docs/TCB.md, "`insert` inherits `push`'s growth
//!   class"): RawVec's "capacity overflow" is tolerated for a SIZED element
//!   because the live buffer would have to exceed `isize::MAX / 2` bytes — 2^62
//!   on a 64-bit target, 2^30 on a 32-bit one;
//! * the vanilla-sysroot class ([`callee_is_vanilla_sysroot`]): a std callee at
//!   foundational argument types keeps its own panics as "std's defined
//!   behaviour", and among them are the growth and layout panics of every std
//!   function that allocates more than its live input (`collect` into a wider
//!   element, `to_uppercase`, `concat`), whose OUTPUT type that class never reads;
//! * vcgen's allocation lane: the bounded-source `collect`/`extend` grants
//!   (`trust_types::live_source_bound`, with `isize::MAX` taken as `i64::MAX`), the
//!   trusted-constant skip and the capacity line beside the element ceiling
//!   (`UNBOUNDED_ALLOC_ELEM_CEILING`, 2^28) were judged against a 64-bit
//!   `isize::MAX` on every target. This third bullet is the one main has since
//!   repaired (ALLOC-WIDTH-1, 2026-10-08, docs/DECISION_QUEUE.md): every capacity
//!   line is now `isize::MAX` at the compilation target's pointer width, and off
//!   64 bits every additional-count row fails and no bounded-source skip is taken.
//!   The first two bullets are not width-aware, so this refusal stays (see "The
//!   rule").
//!
//! The one premise that did ask — docs/TCB.md's `MAX_LIVE_ALLOC_BYTES` axiom for
//! the `Vec<u8>` grow summaries — is gated on a 64-bit width witness because, as
//! it says, on a 32-bit extraction "`isize::MAX / 2` = 2^30 − 1 bytes is
//! physically realizable and the axiom is false". Measured 2026-10-02 on
//! `wasm32-unknown-unknown` (std 1.97.1 run verify-off under node; no Trust
//! toolchain here carries a 32-bit std): `push`/`insert`/`push_back`/`push`/
//! `push_str` on a full 1 GiB `Vec<u8>`, `Vec<u32>`, `VecDeque<u8>`,
//! `BinaryHeap<u8>` and `String`; a `collect` of a 256 MiB `&[u8]` into a
//! `Vec<u64>` or, through `u64::from`, a `Box<[u64]>`; `to_uppercase` of a
//! 512 MiB string of `U+0390`; `Vec::<u128>::with_capacity(200_000_000)` (a
//! trusted constant below the element ceiling) and a `with_capacity(n)` of `u128`
//! guarded by `n < 2^28` — each panicked "capacity overflow"; a `HashSet`/
//! `HashMap` `extend` from a 512 MiB `&[u8]` panicked "Hash table capacity
//! overflow", and an `Rc<[u64]>` `collect` panicked on a `LayoutError`.
//!
//! ## The rule
//!
//! A verifying compilation whose target's `pointer_width` is below 64 is refused
//! once, crate-level: an error under every fail-closed policy (the default,
//! `certify`, `memory-safe`), a warning under the explicit advisory survey. It is
//! not narrowed to crates that link `alloc`: the 64-bit premises have been
//! audited for the allocation lanes above, not for core-only code, and a gate
//! that excused what nobody audited would be the same hole. Decided from the
//! session's target, never a name; refusal-only, and constant-false on a 64-bit
//! target. The honest recovery is width-aware premises — each one above read
//! against the target's own `isize::MAX` and address space, as the
//! `MAX_LIVE_ALLOC_BYTES` gate already is — after which this refusal can lift;
//! docs/KNOWN_HAZARDS.md records that design work. Main's ALLOC-WIDTH-1 is that
//! recovery for vcgen's counted allocation rows; the push-growth class and the
//! vanilla-sysroot class still ask no width, and a std `v.push(1)` on a
//! `Vec<u8>` has no counted row for ALLOC-WIDTH-1 to judge.

use super::*;

/// Refuse (or, under the explicit advisory survey, report) a verifying build for a
/// target narrower than 64 bits. See the module doc.
pub(super) fn refuse_narrow_target(tcx: TyCtxt<'_>, policy: &TrustVerifyPolicy) {
    let width = tcx.sess.target.pointer_width;
    if width >= 64 {
        return;
    }
    let message = format!(
        "Trust verification cannot accept a build for `{}`: its pointers are {width} bits \
         wide, and the default policy's allocation and growth premises hold only on a 64-bit \
         address space",
        tcx.sess.target.llvm_target
    );
    let reach = "on this target `isize::MAX` is 2^31 - 1 bytes, which a process can reach: a \
         `push` on a full 1 GiB `Vec<u8>`, a `collect` of a 256 MiB `&[u8]` into a \
         `Vec<u64>`, or `Vec::<u128>::with_capacity(200_000_000)` panics \"capacity \
         overflow\" here, and the push-growth class, the vanilla std-callee class and the \
         allocation ceilings would accept each of them";
    let options = "Options: verify the program for a 64-bit target (the verdict then covers \
         that target only), or `-Z trust-policy=advisory` to record this as a warning";
    if policy.fail_closed() {
        tcx.dcx().struct_err(message).with_note(reach).with_note(options).emit();
    } else {
        tcx.dcx()
            .struct_warn(message)
            .with_note(reach)
            .with_note(options)
            .with_note(
                "reported, not failed, only because this is the explicit advisory survey; \
                 every fail-closed policy refuses it",
            )
            .emit();
    }
}
