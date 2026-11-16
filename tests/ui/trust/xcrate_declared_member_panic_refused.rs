//@ needs-trust-verify
//@ aux-build:xcrate_member_panic_dep.rs
//@ edition: 2021
//@ revisions: h g unreach todo asserts never certify quiet
//@ revisions: undeclared local unwrap expect
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@[h] compile-flags: -Ztrust-bundle-foreign-crate=xcpanic_dep
//@[g] compile-flags: -Ztrust-bundle-foreign-crate=xcpanic_dep
//@[unreach] compile-flags: -Ztrust-bundle-foreign-crate=xcpanic_dep
//@[todo] compile-flags: -Ztrust-bundle-foreign-crate=xcpanic_dep
//@[asserts] compile-flags: -Ztrust-bundle-foreign-crate=xcpanic_dep
//@[never] compile-flags: -Ztrust-bundle-foreign-crate=xcpanic_dep
//@[certify] compile-flags: -Ztrust-bundle-foreign-crate=xcpanic_dep -Ztrust-policy=certify
//@[quiet] compile-flags: -Ztrust-bundle-foreign-crate=xcpanic_dep
//@[unwrap] compile-flags: -Ztrust-bundle-foreign-crate=xcpanic_dep
//@[expect] compile-flags: -Ztrust-bundle-foreign-crate=xcpanic_dep
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@[h] check-fail
//@[g] check-fail
//@[unreach] check-fail
//@[todo] check-fail
//@[asserts] check-fail
//@[never] check-fail
//@[certify] check-fail
//@[undeclared] check-fail
//@[local] check-fail
//@[unwrap] check-fail
//@[expect] check-fail
//@[quiet] check-pass
//! **A declared dependency's diverging site must not reach a verifying caller
//! as a tolerated `runtime-checked` row.**
//!
//! EVERY `check-fail` REVISION MUST STAY REFUSED. One going green is a possible
//! FALSE ACCEPT until shown otherwise: fix the compiler, never this file.
//!
//! # The false accept (measured on stage-1 `trustc` at `a8c853de6f`)
//!
//! The dependency is built `-Ztrust-verify=off -Zalways-encode-mir`. A
//! verifying binary calling `xcpanic_dep::h(black_box(7))` WITH
//! `-Ztrust-bundle-foreign-crate` built rc=0 under the default policy,
//! reporting one `[assert] runtime-checked` row. The binary then exited 101.
//! `g` (one frame deeper) behaved the same way. `targo trust build` injects
//! this flag for every workspace-internal library dependency, so the shape is
//! any workspace whose sibling crate panics.
//!
//! On the same compiler these were refused: the scope undeclared (`undeclared`),
//! a local copy (`local`), and `-Ztrust-policy=certify` (`certify`).
//!
//! # Why it happened
//!
//! The declared arm of the B-lane bundles `h` as a MEMBER. The bridge lowers the
//! member's `panic_fmt` call as `Assert(false)` with a PRIVATE obligation, and
//! the public inventory reset clears it (TCB, "A bundled member's `Assert`
//! mints NO obligation"). The only public row still carrying the panic is the
//! caller's whole-function aggregate `vc:<fn>:assertion:panic-freedom:0`. It is
//! rebuilt as `VcKind::Assertion`, which has a runtime fallback, so its Unknown
//! result became `RuntimeChecked` and policy B tolerated it. For a root's own
//! panic sites that is harmless: each site has its own row, and a reachable
//! one is refuted (`local`). The member's site had no row of its own, so the
//! claimed runtime check was the panic itself.
//!
//! The member `Assert` gate (`ensure_bundled_member_asserts_exactly_charged`)
//! did not catch it because it counts `Terminator::Assert` only, and an
//! explicit panic is a diverging CALL.
//!
//! # The fix this pins
//!
//! `foreign_member_has_uncharged_diverging_site` (trust_verify.rs) makes the
//! B-lane decline a non-local, non-sysroot member whose reachable MIR contains a
//! `TerminatorKind::Call { target: None }`. The call site then takes the
//! fail-closed absent-callee arm, the same as `undeclared`. The key is the
//! never-returning call, not a callee name, which is why `never` (a user
//! `-> !` helper) is here beside the panic macros.
//!
//! # The revisions
//!
//! * `h`, `g` — the two measured witnesses.
//! * `unreach`, `todo`, `asserts`, `never` — the same diverging-call shape
//!   from `unreachable!()`, `todo!()`, `assert!` and a `-> !` helper. Not
//!   separately measured before the fix.
//! * `certify` — `h` under the strict verb. Refused before and after.
//! * `undeclared`, `local` — the parity controls. The refusal the fix restores
//!   is the one these already had.
//! * `quiet` — POSITIVE CONTROL, check-pass. `h` with the panic replaced by a
//!   return, called in the shape of `cross_crate_bundle_scope_declared.rs`
//!   (`bump_capped`). A member with no diverging site stays bundled. If this
//!   revision fails, the fix over-refuses.
//!
//! Not pinned here: a member's own `Assert` (overflow, bounds, div/rem). The fix
//! does not read `Assert` terminators, so their charged-or-refused lane is
//! unchanged. `u_xh_idx` (array index in the dependency) was refused before
//! the fix by that lane.
extern crate xcpanic_dep;

#[cfg(h)]
pub fn f(x: u32) -> u32 { //[h]~ ERROR Trust strict verification failed
    xcpanic_dep::h(x)
}

// `g` itself stays bundled, and its call to the declined `h` becomes a member
// absent-callee row. Expected: the strict header, whether that row reaches the
// verdict through the aggregate or after the poison loop evicts `g`. The pin
// matches only the tail it shares with the lowering-failure header ("Trust full
// verification failed"), so a refusal by either route passes.
#[cfg(g)]
pub fn f(x: u32) -> u32 { //[g]~ ERROR verification failed
    xcpanic_dep::g(x)
}

#[cfg(unreach)]
pub fn f(x: u32) -> u32 { //[unreach]~ ERROR Trust strict verification failed
    xcpanic_dep::unreach(x)
}

#[cfg(todo)]
pub fn f(x: u32) -> u32 { //[todo]~ ERROR Trust strict verification failed
    xcpanic_dep::todo_at(x)
}

#[cfg(asserts)]
pub fn f(x: u32) -> u32 { //[asserts]~ ERROR Trust strict verification failed
    xcpanic_dep::asserts(x)
}

#[cfg(never)]
pub fn f(x: u32) -> u32 { //[never]~ ERROR Trust strict verification failed
    xcpanic_dep::never(x)
}

#[cfg(certify)]
pub fn f(x: u32) -> u32 { //[certify]~ ERROR Trust strict verification failed
    xcpanic_dep::h(x)
}

// The panic is inside std's `unwrap`/`expect`, which the member calls: a call
// outside the declared scope is charged nowhere in member context (vcgen's
// family recognizers see only the root's body), so the member is declined and
// the call is refused exactly as when undeclared.
#[cfg(unwrap)]
pub fn f(x: Option<u32>) -> u32 { //[unwrap]~ ERROR Trust strict verification failed
    xcpanic_dep::unwrap_at(x)
}

#[cfg(expect)]
pub fn f(v: &[u32], i: usize) -> u32 { //[expect]~ ERROR Trust strict verification failed
    xcpanic_dep::expect_at(v, i)
}

#[cfg(undeclared)]
pub fn f(x: u32) -> u32 { //[undeclared]~ ERROR Trust strict verification failed
    xcpanic_dep::h(x)
}

/// The parity reference: the same body, local. It is verified as its own root
/// and its reachable panic is refuted there.
#[cfg(local)]
fn h_local(x: u32) -> u32 { //[local]~ ERROR Trust strict verification failed
    if x == 7 {
        panic!("boom")
    }
    x
}

#[cfg(local)]
pub fn f(x: u32) -> u32 {
    h_local(x)
}

/// Deliberately not a bare passthrough (see `cross_crate_bundle_scope_declared.rs`):
/// the capped increment gives the caller obligations it must discharge itself,
/// so the pass is a pass WITH proofs.
#[cfg(quiet)]
pub fn f(a: u8) -> u8 {
    let _ = xcpanic_dep::quiet(3);
    if a > 200 {
        return 201;
    }
    a + 1
}
