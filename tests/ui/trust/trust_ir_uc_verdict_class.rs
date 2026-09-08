//@ check-pass
//@ compile-flags: -Ztrust-ir-lower -Ztrust-verify=off
// Absent-callee Stage 3: the fenced UNINTERPRETED-CALLEE verdict class.
// `caller` reaches a bodyless scalar-signature declaration; under the fence
// (all-scalar args, one scalar return, one arity, no pointer-shaped entry
// param) the seam mints `agreed-uninterpreted-callee` — its own verdict
// marker, `equal: false` by invariant, NEVER the plain Agreed the artifact's
// other rows mean. `caller_ptr` is the standing refuter: a pointer-returning
// declaration stays outside `const_of` (a fabricated integer address would
// "agree" only by construction of the fabrication), so its row keeps the
// seam-deferred skip. The claim's exact text and blind spots: docs/TCB.md.

unsafe extern "Rust" {
    fn opaque(x: i32) -> i32;
}

pub fn caller(a: i32) -> i32 {
    if a > 0 { unsafe { opaque(a) } } else { 7 }
}

// wave-UCF: a FAT-pointer return joins the fence at the single two-zero
// (null/empty) constant trust-ir fecd740 admits; the leg count discloses the
// single-value modeling. The caller must share no OTHER absentee asymmetry —
// a companion bodyless std helper on one side only refuses as uc-unpaired
// (measured: `s.len()` did exactly that), which is the pairing conjunct
// working, not a gap.
unsafe extern "Rust" {
    fn name_of(x: u32) -> &'static str;
}

pub fn caller_fat(a: u32) -> u32 {
    let _s = unsafe { name_of(a) };
    a ^ 1
}

unsafe extern "Rust" {
    fn gives_ptr() -> *const i32;
}

pub fn caller_ptr() -> *const i32 {
    unsafe { gives_ptr() }
}

fn main() {}
