//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory --crate-type lib
//@ edition: 2024
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-pass
//! CORRECT code that the typed-CHC attestation must never refute. Each function below
//! was reported `failed` with `verified_counterexample = true` on trust main
//! `b6831d5dff` (the aterm corpus ledger, 2026-09-30), because the exactness check
//! (`typed_chc_payload_determines_every_name`) passed with a FREE name in the payload:
//!
//! * S-R1: `trust_spec_expr_variables` never walked bit-vector, `Ite` or quantifier
//!   nodes, so a name that occurred only there was not "mentioned" (`mm_ok`, `guard`,
//!   `alias_let`, `alias_match_guard`);
//! * S-R2: a bare-boolean pin let the negated goal ground the clause's own free name
//!   (`q3_agg_bool`: the payload is exactly `¬t*.0#s0_1`).
//!
//! None of these may read `failed`; each is Unknown (a coverage gap, not a
//! counterexample) until the lanes behind it model the missing definition, except
//! `alias_match_guard`, which proves since VS-1 (see its note). `no_alias` is the
//! control that proves.

pub fn mm_ok(hot: usize) -> usize
//~^ NOTE Trust verification: 0 proved, 0 failed, 2 unknown
    ensures result >= 1
{
    let h = hot.max(1);
    h.min(5)
}

pub struct D {
    pub e: bool,
    pub lra: u64,
}

pub fn guard(d: &D, abs_row: u64) -> u8
//~^ NOTE Trust verification: 2 proved, 0 failed, 2 unknown
    ensures result == 0 ==> (!d.e || abs_row >= d.lra)
{
    if d.e && abs_row < d.lra {
        return 1;
    }
    0
}

pub struct S {
    pub b: usize,
    pub e: bool,
}

pub fn alias_let(s: &mut S, x: usize)
//~^ NOTE Trust verification: 1 proved, 0 failed, 2 unknown
    ensures x > 0 ==> s'.e
{
    if x > 0 {
        let y = x;
        s.b = y;
        s.e = true;
    } else {
        s.e = false;
    }
}

// RE-PIN 2026-10-04 (VS-1): 1 proved / 2 unknown -> 3 proved, the same verdict as the
// `no_alias` control. The clause is TRUE. The match-guard binding `y` has two debug rows
// on two locals (`debug y => _2; debug y => _3;`, `_2` being the parameter `x`); since
// VS-1 such a spelling names no local, the parameter local keeps the name `x`, and the
// clause's `x` binds it instead of nothing. `alias_let`'s single `y` row still renames that local, so
// it stays Unknown.
pub fn alias_match_guard(s: &mut S, x: usize)
//~^ NOTE Trust verification: 3 proved, 0 failed, 0 unknown
    ensures x > 0 ==> s'.e
{
    match x {
        y if y > 0 => {
            s.b = y;
            s.e = true;
        }
        _ => {
            s.e = false;
        }
    }
}

pub fn no_alias(s: &mut S, x: usize)
//~^ NOTE Trust verification: 3 proved, 0 failed, 0 unknown
    ensures x > 0 ==> s'.e
{
    if x > 0 {
        s.b = x;
        s.e = true;
    } else {
        s.e = false;
    }
}

pub struct T {
    pub f: bool,
    pub n: u32,
}

pub fn q3_agg_bool(t: &mut T)
//~^ NOTE Trust verification: 0 proved, 0 failed, 2 unknown
    ensures t'.f
{
    *t = T { f: true, n: 1 };
}
