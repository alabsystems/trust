//@ revisions: ok unguarded reseat
//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@[ok] build-pass
//@[unguarded] check-fail
//@[reseat] check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! **A guarded `&mut [T]` index must stay proved when the body READS BACK what it
//! just wrote.**
//!
//! `guarded_mut_slice_index.rs` (trust-vcgen) pins the guarded STORE:
//! `if i < dst.len() { dst[i] = 0; }`. It misses this by exactly one statement.
//! Reading the element back false-REFUTED, because the store's opaque deref-havoc
//! minted a phantom `s{b}_pre` token for the derived `s__slice_len`, leaving the
//! read's length name-disjoint from the guard's — so `i < s__slice_len` was pruned
//! from the bounds VC of the second access. Measured before the fix:
//! `1 proved, 1 failed`, with the model binding the true `s__slice_len = 1`
//! beside a phantom `s__slice_len#s2_pre = 0`.
//!
//! The cause was a gate/search disagreement, not a missing fact.
//! `version_token_at`'s gate tested `dest_write_rebinds` — which carries the
//! derived-`__slice_len` channel — across a union that includes the opaque
//! deref-store HAVOC names, re-admitting for the havoc channel exactly what
//! `extend_with_derived_slice_len` deliberately withholds from it. The
//! per-statement search does not, honouring the ANCESTOR-ONLY ruling that an
//! element store "preserves the length metadata and must NOT count as a write of
//! `dst__slice_len`".
//!
//! The `unguarded` revision is the RAIL: an index with no dominating guard must
//! still be refused. A change that makes the `ok` half pass by weakening the
//! bounds obligation rather than by repairing the length tie fails here.

#[cfg(ok)]
pub fn write_then_read(s: &mut [u8], i: usize) -> u8 {
    if i < s.len() {
        s[i] = 7;
        s[i]
    } else {
        0
    }
}

/// Control: the same body with no store proves, and always did.
#[cfg(ok)]
pub fn read_only(s: &[u8], i: usize) -> u8 {
    if i < s.len() { s[i] } else { 0 }
}

/// Control: reading BEFORE the store proves — the phantom is minted at the store,
/// so a read ahead of it never sees one.
#[cfg(ok)]
pub fn read_then_write(s: &mut [u8], i: usize) -> u8 {
    if i < s.len() {
        let v = s[i];
        s[i] = 7;
        v
    } else {
        0
    }
}

/// Control: a local array takes no opaque deref store, so this shape always proved.
/// It isolates the deref store — not the write-then-read pattern — as the cause.
#[cfg(ok)]
pub fn local_array(i: usize) -> u8 {
    let mut a = [0u8; 4];
    if i < 4 {
        a[i] = 7;
        a[i]
    } else {
        0
    }
}

/// Control: re-reading the length after the store re-establishes the tie past the
/// phantom, which is why this proved even before the fix.
#[cfg(ok)]
pub fn reread_len(s: &mut [u8], i: usize) -> u8 {
    if i < s.len() {
        s[i] = 7;
        if i < s.len() { s[i] } else { 0 }
    } else {
        0
    }
}

/// Two distinct indices under their own guards must both keep their ties.
#[cfg(ok)]
pub fn two_indices(s: &mut [u8], i: usize, j: usize) -> u8 {
    if i < s.len() && j < s.len() {
        s[i] = 7;
        s[j] = 9;
        s[i] ^ s[j]
    } else {
        0
    }
}

#[cfg(unguarded)]
pub fn unguarded_write_then_read(s: &mut [u8], i: usize) -> u8 {
    s[i] = 7;
    s[i]
}

/// The adversary's differential, and the sharpest statement of the defect: `b` is
/// NEVER stored into. A store through `a` severed `b`'s length tie, because the
/// gate fired on `b`'s membership in the havoc list rather than on any write to it.
/// The same body with `b: &[u32]` always proved.
#[cfg(ok)]
pub fn cross_slice(a: &mut [u32], b: &mut [u32], i: usize) -> u32 {
    if i < a.len() && i < b.len() {
        a[i] = 1;
        b[i]
    } else {
        0
    }
}

/// Control: `&mut`-ness alone is not the trigger — two guarded reads through a
/// `&mut [T]` with NO store always proved.
#[cfg(ok)]
pub fn mut_reads_no_store(s: &mut [u32], i: usize) -> u32 {
    if i < s.len() { s[i] ^ s[i] } else { 0 }
}

fn main() {}

/// RAIL, and the one that matters most: RESEATING the slice through a mutable
/// pointer genuinely changes its length, so the tie MUST be severed and this must
/// stay refused. It is refused today on REAL tokens (`s__slice_len#s1_0`), not on
/// the phantom, because `mutably_borrowed_havoc_names` pushes `s__slice_len` BY
/// NAME — gate and search agree on it under the narrow relation, so the refusal
/// survives. This fixture exists so that a future provenance-split rewrite, which
/// would NOT preserve it automatically, fails here instead of minting a stale
/// length tie.
#[cfg(reseat)]
pub fn reseat_changes_length(a: &[u32], b: &[u32], i: usize) -> u32 {
    let mut s: &[u32] = a;
    let p = &mut s;
    if i < p.len() {
        *p = b;
        (*p)[i]
    } else {
        0
    }
}
