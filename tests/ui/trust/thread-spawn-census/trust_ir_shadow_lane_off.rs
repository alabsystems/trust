//@ revisions: flag_off verify_off
//@ needs-trust-verify
//@ compile-flags: --crate-type lib
//@[flag_off] compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory
//@[verify_off] compile-flags: -Ztrust-verify=off -Ztrust-spawn-census-shadow=check
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@[flag_off] forbid-output:trust-spawn-census-shadow:
//@[verify_off] regex-error-pattern:(?m)^trust-spawn-census-shadow: not run: verification is disabled, so the MIR lane it is compared with did not run$
//@[verify_off] forbid-output:trust-spawn-census-shadow: body
//! Spawn census, plan step P4: the trust-ir shadow lane is OFF unless asked for (`flag_off`: a
//! verified compilation of a spawning crate prints no report line), and asked for without
//! verification it says it did not run, because the MIR lane it is compared with did not.

#![allow(dead_code)]

pub fn launch() {
    let _handle = std::thread::spawn(|| {});
}
