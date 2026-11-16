//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=certify --crate-type lib
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! DISC-CSE-PRE-BARRIER-WRITE-1, the precision control: a discriminant tie the fix must
//! KEEP. Two `discriminant(*&x)` reads with no barrier between them are still tied
//! when nothing in the body writes or reseats the referent:
//!
//! * `stable`       — an unwritten local, borrowed twice;
//! * `stable_param` — the pointee of a `&Option<u8>` parameter (frozen for the call);
//! * `Val::eq`      — `#[derive(PartialEq)]` on a data-carrying enum, which re-reads
//!   `discriminant(*self)` / `discriminant(*other)` through the `(self, other)` tuple.
//!
//! In `stable` and `stable_param` the `else` arm is dead, and its `v + 255` overflow row
//! proves only if the second read is tied to the first; `Val::eq`'s shared
//! `otherwise -> unreachable` is dead only if the per-arm re-reads are tied to the
//! outer reads. (Measured 2026-10-12 at the trust-vcgen level on the compiler's own
//! extraction of these bodies: with the discriminant-CSE admissions disabled, the
//! `stable` and `stable_param` overflow rows and `Val::eq`'s `[unreach]` row are
//! refuted; with them, all three prove.) THE STRICT BUILD IS THE ASSERTION: a refuted
//! row fails this file, which is what an over-tightened guard 2 would do. The liars are
//! `discriminant_cse_statement_write_no_false_proof.rs` and its run twin.
//!
//! BEFORE (measured 2026-10-12 on the wave-25 probe stage 1, `scratchpad/stage1-w25probe`,
//! with exactly these flags plus `--emit=metadata`): exit 0; `stable` and
//! `stable_param` each report "2 proved ... of which 2 kernel-certified", `Val::eq`
//! "1 proved". AFTER (predicted; FIX PREPARED 2026-10-12, not built on a stage 1): the
//! same. trust-vcgen's `real_mir_stable_referents_keep_their_pre_barrier_tie` measures
//! the ties on the compiler's own extraction of these three bodies, with the fix.

pub fn stable(v: u8) -> u8 {
    let cur = Some(v);
    if let None = &cur {
        return 0;
    }
    if let Some(_) = &cur { 0 } else { v + 255 }
}

pub fn stable_param(cur: &Option<u8>, v: u8) -> u8 {
    if let None = cur {
        return 0;
    }
    if let Some(_) = cur { 0 } else { v + 255 }
}

#[derive(PartialEq)]
pub enum Val {
    A(u8),
    B(u16),
}
