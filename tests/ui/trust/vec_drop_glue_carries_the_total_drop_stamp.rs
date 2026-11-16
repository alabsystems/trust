//@ revisions: ok bomb_elem bomb_through_member
//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@[ok] build-pass
//@[bomb_elem] check-fail
//@[bomb_through_member] check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! **A bare `Vec<T>` must carry the same drop-totality certificate every other
//! std owning container already carries.**
//!
//! Measured before the fix, each a one-line body `let x: T = ..; let _ = x;`:
//!
//!   Vec<u32>                    rc=1      Option<Vec<u32>>       rc=0
//!   Vec::with_capacity(4)       rc=1      Some(Vec::new())       rc=0
//!   fn f(v: Vec<u32>)           rc=1      struct W(Vec<u32>)     rc=0
//!   [Vec<u32>; 2]               rc=1      String / Box / HashMap rc=0
//!
//! `Option<Vec<T>>`'s glue CALLS `Vec<T>`'s glue, so proving the wrapper while
//! refusing the wrapped was incoherent. The cause: `ty_convert.rs` replaces
//! `Vec<T, A>` wholesale with `Ty::Seq { elem }` AHEAD of the site that stamps
//! `AdtAuth::TotalDrop` onto an ADT, and `Ty::Seq` had no slot for the stamp --
//! so the bridge's drop classifier, which reads exactly that stamp to admit
//! `Option<Vec<u32>>` field-free, had nothing to read and fell to its
//! fail-closed `_` arm. This is the seventh reading of the `vec![]` residue and
//! the first with a mechanism at the type rather than at a row label.
//!
//! The fix stamps `Ty::Seq` at extraction with the SAME predicate
//! (`tcx_drop_is_total`) on the FULL concrete type -- element AND allocator --
//! and the bridge reads it exactly as it reads the ADT's. What it deliberately
//! does NOT do, and why the rails below exist:
//!
//!   * it never recurses into `elem` in the bridge: `elem` omits the allocator,
//!     and `Vec<u32, NoisyAlloc>` with a panicking allocator `Drop` is refused
//!     today only because `tcx_drop_is_total` recurses the real type args;
//!   * it never touches `is_trivially_no_drop_ty`: a `Vec` OWNS an allocation,
//!     so its glue is real -- the stamp certifies the glue audited panic-free
//!     (dealloc only), never that there is no glue. `docs/DECISION_QUEUE.md`
//!     records the one-line "fix" that would have done that as a FALSE PROOF.
//!
//! `bomb_elem` is W3's hole 1 (`Vec<Bomb>` is not safe because `Vec<u32>` is);
//! `bomb_through_member` is hole 2 (the drop lives in a bundled member, not the
//! root). Both must keep refusing; the ordinary rail `Bomb`'s `Drop` is the ONLY
//! refusal source in those crates, so a wrongly-`Some` stamp would compile them.

#[cfg(ok)]
pub fn bare_new() {
    let v: Vec<u32> = Vec::new();
    let _ = v;
}

#[cfg(ok)]
pub fn with_capacity() {
    let v: Vec<u32> = Vec::with_capacity(4);
    let _ = v;
}

#[cfg(ok)]
pub fn as_parameter(v: Vec<u32>) {
    let _ = v;
}

#[cfg(ok)]
pub fn array_of_vecs() {
    let a: [Vec<u32>; 2] = [Vec::new(), Vec::new()];
    let _ = a;
}

/// `i02` of the idiomatic sample, the shape this residue was named for.
#[cfg(ok)]
pub fn literal() -> usize {
    let ports = vec![80u16, 443, 8080];
    ports.len()
}

/// The drop in a bundled MEMBER, not the root (hole 2, positive direction).
#[cfg(ok)]
fn helper() {
    let v: Vec<u32> = Vec::with_capacity(2);
    let _ = v;
}
#[cfg(ok)]
pub fn through_member() {
    helper();
}

#[cfg(any(bomb_elem, bomb_through_member))]
pub struct Bomb(pub u32);
#[cfg(any(bomb_elem, bomb_through_member))]
impl Drop for Bomb {
    fn drop(&mut self) {
        panic!("boom")
    }
}

// RAIL, hole 1: a panicking user `Drop` reached THROUGH the container.
#[cfg(bomb_elem)]
pub fn vec_of_bombs() {
    let v: Vec<Bomb> = Vec::new();
    let _ = v;
}

// RAIL, hole 2: the same, but the drop lives in a bundled member.
#[cfg(bomb_through_member)]
fn helper() {
    let v: Vec<Bomb> = Vec::new();
    let _ = v;
}
#[cfg(bomb_through_member)]
pub fn through_member() {
    helper();
}

fn main() {}
