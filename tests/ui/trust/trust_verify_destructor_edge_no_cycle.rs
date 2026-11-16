//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory --crate-type lib
//@ edition: 2021
//@ dont-check-compiler-stderr
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE
//@ check-pass
//! E0391 through a DESTRUCTOR EDGE. The `optimized_mir` cycle oracle
//! (`optimized_mir_query_would_cycle`) sees call edges and HOF closure arguments;
//! it never sees a `Drop` terminator. But the structural-drop lane forces
//! `trust_proof_results(<T as Drop>::drop)` for every Drop-bearing ADT a dropped
//! local's type REACHES (`RefMut<'_, Arena>` reaches `Arena` through its generic
//! args, not through ownership), and two verifier requests were issued with no
//! guard at all:
//!
//!     trust_verify.rs:36053  R144 paired-closure admission   `let cbody = tcx.optimized_mir(*cdid);`
//!     trust_verify.rs:30897  drop-glue discharge -> trait_panic_free.rs:216 `tcx.trust_proof_results(instance)`
//!
//! Measured query stack (callee-first walk, so the closure is optimized first):
//!
//!     optimizing MIR for `intern::{closure#0}`                                (root, :13963)
//!       -> trust proof results for `<Arena as Drop>::drop`                   (:30953 -> :30963 -> :30897 -> trait_panic_free.rs:216)
//!       -> optimizing MIR for `<Arena as Drop>::drop`
//!       -> optimizing MIR for `intern`                                       (:18649, GUARDED, and truthfully admitted)
//!       -> optimizing MIR for `intern::{closure#0}` AGAIN                    (:36053, UNGUARDED — the closure IS in progress)
//!
//! The guarded DefId lane had already seen the closure in `intern`'s bundle and
//! declined it (`[BUNDLE_DROP] reason=no-mir-for-trust-verification`); the mono
//! lane's R144 pairing for `LocalKey::try_with::<_, {closure#0}, u32>` then asked
//! for the same body unguarded. A cycle is an ABORT, not a verdict: advisory policy
//! cannot soften it, which is why this file needs the fix to pass at all.
//!
//! WHAT THE FIX IS NOT. It does not widen the oracle's call graph with drop edges
//! and it does not credit anything. Both sites consult the EXISTING oracle and
//! DECLINE: the R144 pair fails closed (the member's call sites take the
//! absent-callee may-panic arm) and the destructor node stays CUT (`false` = not
//! proved). These bodies still do not verify; advisory turns that into warnings,
//! and what this file asserts is that a VERDICT IS REACHED — if it ever reports
//! E0391 again, a guard has regressed.
//!
//! THE FLAGS ARE LOAD-BEARING. `-Ztrust-policy=advisory` is required for the
//! check-pass: under strict, the negative controls below already exit 1 on
//! ordinary unproved obligations (measured: 7 errors on `drop_without_call`),
//! which would hide the one thing this file pins. `-Ztrust-verify=off
//! -Ztrust-ir-lower=on` passes both faces today: this is a verifier defect, not
//! a lowering one, and it is not #189.

use std::cell::RefCell;

// ── face 1: the ny-cert shape (closure -> destructor -> caller -> closure) ────
// `ny_cert::rational::intern` / `Arena::drop` (cfg(test)) / `intern::{closure#0}`.

struct Arena {
    values: Vec<u32>,
}

impl Drop for Arena {
    fn drop(&mut self) {
        let _ = intern(0);
    }
}

thread_local! {
    static ARENA: RefCell<Arena> = RefCell::new(Arena { values: Vec::new() });
}

/// `try_with` is a FOREIGN generic instantiated with a LOCAL closure — the R144
/// pairing shape. The closure body drops a `RefMut<'_, Arena>`, which is the
/// destructor edge to `<Arena as Drop>::drop`.
fn intern(v: u32) -> u32 {
    let result = ARENA.try_with(|a| {
        let Ok(mut a) = a.try_borrow_mut() else {
            return 0;
        };
        a.values.push(v);
        v
    });
    match result {
        Ok(id) => id,
        Err(_) => 0,
    }
}

pub fn use_it() -> u32 {
    intern(7)
}

// ── face 2: the one-node shape (a destructor forcing its own verdict) ────────
// Closed by site :30897 alone; pins guard (B) independently of guard (A).

struct SelfDtor {
    values: Vec<u32>,
}

impl Drop for SelfDtor {
    fn drop(&mut self) {
        // A local whose type reaches `SelfDtor` is dropped INSIDE `SelfDtor::drop`:
        // the drop-glue lane forces this very body's verdict while it is optimizing.
        let cell = RefCell::new(SelfDtor { values: Vec::new() });
        let mut g = cell.borrow_mut();
        g.values.clear();
    }
}

pub fn use_self_dtor() -> usize {
    let a = SelfDtor { values: vec![1] };
    a.values.len()
}

// ── negative controls: the guards must stay narrow ───────────────────────────
// Each compiled alone under the same flags today: exit 0, no E0391.

/// A `Drop` that does NOT call back into `intern`: no destructor edge closes anything.
pub mod drop_without_call {
    use std::cell::RefCell;
    pub struct Arena { pub values: Vec<u32> }
    impl Drop for Arena { fn drop(&mut self) { self.values.clear(); } }
    thread_local! { static ARENA: RefCell<Arena> = RefCell::new(Arena { values: Vec::new() }); }
    pub fn intern(v: u32) -> u32 {
        let result = ARENA.try_with(|a| {
            let Ok(mut a) = a.try_borrow_mut() else { return 0; };
            a.values.push(v);
            v
        });
        match result { Ok(id) => id, Err(_) => 0 }
    }
}

/// No `Drop` impl at all: the structural-drop lane records the ADT and asks nothing.
pub mod no_drop_impl {
    use std::cell::RefCell;
    pub struct Arena { pub values: Vec<u32> }
    thread_local! { static ARENA: RefCell<Arena> = RefCell::new(Arena { values: Vec::new() }); }
    pub fn intern(v: u32) -> u32 {
        let result = ARENA.try_with(|a| {
            let Ok(mut a) = a.try_borrow_mut() else { return 0; };
            a.values.push(v);
            v
        });
        match result { Ok(id) => id, Err(_) => 0 }
    }
}

/// The call-back with NO closure: `drop -> intern` is a plain call edge, and the
/// re-entry `intern -> RefMut<Arena> drop -> glue -> drop` is refused at the sites
/// that were already guarded.
pub mod no_closure {
    use std::cell::RefCell;
    pub struct Arena { pub values: Vec<u32> }
    impl Drop for Arena {
        fn drop(&mut self) { let _ = intern(&RefCell::new(Arena { values: Vec::new() }), 0); }
    }
    pub fn intern(a: &RefCell<Arena>, v: u32) -> u32 {
        let Ok(mut a) = a.try_borrow_mut() else { return 0; };
        a.values.push(v);
        v
    }
}

/// The closure handed to a LOCAL generic instead of a foreign one: the HOF/DefId
/// lane (guarded) sees it, the R144 mono lane never does.
pub mod local_hof {
    use std::cell::RefCell;
    pub struct Arena { pub values: Vec<u32> }
    impl Drop for Arena {
        fn drop(&mut self) { let _ = intern(&RefCell::new(Arena { values: Vec::new() }), 0); }
    }
    fn apply<F: FnOnce() -> u32>(f: F) -> u32 { f() }
    pub fn intern(a: &RefCell<Arena>, v: u32) -> u32 {
        apply(|| {
            let Ok(mut a) = a.try_borrow_mut() else { return 0; };
            a.values.push(v);
            v
        })
    }
}

// Until the fix lands, replace `//@ check-pass` with:
//   //@ known-bug: unimplemented
//   //@ failure-status: 1
// (exactly the seq_lowering_vec_field_gap.rs convention), and keep the file so the
// flip to check-pass is the measured win.
