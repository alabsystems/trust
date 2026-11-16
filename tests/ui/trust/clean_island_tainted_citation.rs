//@ needs-trust-verify
//@ compile-flags: -Z trust-verify=off
//@ check-fail
//@ dont-require-annotations: NOTE
//! A rejected island can leave successfully registered siblings in the
//! crate-local environment, and no later citation may receive positive
//! evidence from that partial state. Since 2026-09-13 the rejection is
//! reported at the resolve-time mint seam (`trust_clean_mint::decide`),
//! which makes it a FRONT-END error: the verify pass — and with it the E9
//! citation sweep — never runs on this crate, so the citation below is not
//! evaluated at all, which is the strongest form of "no positive evidence".
//! The session-taint rule the sweep applies when it DOES run (the deferred
//! `trust_import_` suffix, macro-introduced islands) is pinned by
//! `trust-certify`'s `is_tainted` unit tests. (The annotation sits OUTSIDE
//! the island: its body is Clean text verbatim to the closing `}`.)

clean {
    theorem registered_before_failure : 0 = 0 := rfl
    theorem hole : True := sorry
}
//~^^^ ERROR the publish audit refused this batch

fn f() -> u32
    ensures 0 == 0 by registered_before_failure
{
    0
}

fn main() {
    let _ = f();
}
