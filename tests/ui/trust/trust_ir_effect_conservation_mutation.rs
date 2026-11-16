//@ needs-trust-verify
//@ compile-flags: -Ztrust-ir-lower=strict -Ztrust-verify=on -Ztrust-policy=advisory --crate-type=lib
//@ compile-flags: -Ztrust-ir-lower-mutate-rhs-effects
//@ dont-check-compiler-stderr
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE
//! THE MUTATION TEST of the effect-conservation gate: disable one lane's effect lowering and the
//! gate must name the effect it lost.
//!
//! `-Ztrust-ir-lower-mutate-rhs-effects` (TEST-ONLY, can only make a build fail) turns
//! `LowerCx::lower_for_effects` back into the pre-ec8b51bb3b lane: a field store's right-hand
//! side that the opaque `()` / Option-discriminant lanes do not model is SKIPPED instead of
//! lowered for its effects, so `self.rows = rows_after_close(fd)` is spliced as the bare
//! `load; extractfield (); insertfield; store` round trip with the call gone — exactly the
//! erasure the 2026-10-01 review measured. The producer pushes no tag for it (that was the bug),
//! so only an independent check can refuse it.
//!
//! Without the flag (`trust_ir_effect_conservation_value_abstractions.rs`) the same body is
//! refused only as an abstraction; with it, the gate's MIR census also finds the `rows_after_close`
//! call missing and says so: `EffectNotConserved(call, `rows_after_close` ..)`.

unsafe extern "C" {
    fn close(fd: i32) -> i32;
}

#[inline(never)]
fn rows_after_close(fd: i32) -> Vec<u32> {
    unsafe { close(fd) };
    Vec::new()
}

pub struct Spawn {
    pub argv: Vec<u32>,
    pub n: u32,
}

impl Spawn {
    pub fn set_argv(&mut self, fd: i32) {
        //~^ ERROR EffectNotConserved(call, `rows_after_close`
        self.argv = rows_after_close(fd);
    }

    /// The loop that sat in a field store's right-hand side (`reset_and_close` in the review):
    /// every `close` call is gone under the mutation, and each one is named.
    pub fn reset_and_close(&mut self, lo: i32, hi: i32) {
        //~^ ERROR EffectNotConserved(call, `close`
        self.argv = {
            let mut fd = lo;
            while fd < hi {
                unsafe { close(fd) };
                fd += 1;
            }
            Vec::new()
        };
    }
}
