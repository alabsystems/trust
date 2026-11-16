//@ revisions: report check
//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory --crate-type lib
//@[report] compile-flags: -Ztrust-spawn-census-shadow=report
//@[check] compile-flags: -Ztrust-spawn-census-shadow=check
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ forbid-output:violates its invariant
//! Spawn census, plan step P4 review (probes c04, c05, c07): the trust-ir lane reads a module as
//! the program only when the producer's effect-conservation check finds it is. The producer lowers
//! an `Option<fn()>` payload or field as its discriminant `bool` (the Option-discriminant lane,
//! `abstracted(opaque-lane)`), so the CREATE of `launch` is in no module, and the lane read each
//! body below as QUIET with no gap where the MIR lane says ESCAPES. Each is now declined as
//! `abstracted`: UNKNOWN, with nothing read from it.
//@ regex-error-pattern:(?m)^trust-spawn-census-shadow: body `launch` mir=SPAWNS trust-ir=SPAWNS equal gaps=closure-value-omitted,drop$
//@ regex-error-pattern:(?m)^trust-spawn-census-shadow: body `ret_opt` mir=ESCAPES trust-ir=UNKNOWN trust-ir-unknown gaps=abstracted$
//@ regex-error-pattern:(?m)^trust-spawn-census-shadow: body `out_opt` mir=ESCAPES trust-ir=UNKNOWN trust-ir-unknown gaps=abstracted$
//@ regex-error-pattern:(?m)^trust-spawn-census-shadow: body `ret_opt_closure` mir=ESCAPES trust-ir=UNKNOWN trust-ir-unknown gaps=abstracted$
//@ regex-error-pattern:(?m)^trust-spawn-census-shadow: body `ret_opt_closure::\{closure#0\}` mir=SPAWNS trust-ir=SPAWNS equal gaps=closure-value-omitted,drop$
//@ regex-error-pattern:(?m)^trust-spawn-census-shadow: body `mk_h` mir=ESCAPES trust-ir=UNKNOWN trust-ir-unknown gaps=abstracted$
//@ regex-error-pattern:(?m)^trust-spawn-census-shadow: body `set_h` mir=ESCAPES trust-ir=UNKNOWN trust-ir-unknown gaps=abstracted$
//@ regex-error-pattern:(?m)^trust-spawn-census-shadow: crate `trust_ir_shadow_lane_not_the_program` bodies=8 equal=3 trust-ir-unknown=5 differs=0 fail-open=0 mir-quiet-claim=0 mir-not-walked=0 mir-fell-back=0 decided=1 residue=0$

#![allow(dead_code)]

pub fn launch() {
    let _handle = std::thread::spawn(|| {});
}

pub fn ret_opt() -> Option<fn()> {
    Some(launch)
}

pub fn out_opt(o: &mut Option<fn()>) {
    *o = Some(launch);
}

pub fn ret_opt_closure() -> Option<fn()> {
    Some(|| launch())
}

pub struct H {
    pub cb: Option<fn()>,
    pub n: u8,
}

pub fn mk_h() -> H {
    H { cb: Some(launch), n: 0 }
}

pub fn set_h(h: &mut H) {
    h.cb = Some(launch);
}
