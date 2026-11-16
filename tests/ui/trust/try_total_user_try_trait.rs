//@ revisions: default certify
//@ needs-trust-verify
//@ edition: 2021
//@ aux-build: try_total_user_try_trait_dep.rs
//@ compile-flags: -Ztrust-verify=on -Coverflow-checks=on --crate-type lib
//@[certify] compile-flags: -Ztrust-policy=certify
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! A method whose path ENDS like a `?`-desugar method is not one (TRY-TOTAL-ANCHOR-1).
//!
//! `trust_mir_extract::convert::trust_try_total_marker` decides that a call is a
//! total `?`-desugar call. Its two consumers are the extractor's
//! `::<__trust_try_total>` stamp and the compiler's `compiler_total_out` set in
//! `collect_expected_absent_callees`, which the bridge spends as a no-panic call.
//! It identified the method by TEXT: the rendered path had to end with
//! `Try::branch` or `FromResidual::from_residual`. The dependency's own traits
//! render as `try_total_user_try_trait_dep::Try::branch` and
//! `try_total_user_try_trait_dep::FromResidual::from_residual`, their receiver and
//! target are std's `Option<u32>`, and both bodies panic.
//!
//! BEFORE (stage 1 of main + wave 7, `scratchpad/stage1-w14`, each revision's own
//! flags plus `--cfg <revision> --emit=metadata`, measured 2026-10-05): `a` and `b`
//! have no diagnostic in either revision (their rows read
//! `native-verification-gap`, which neither policy refuses), so neither annotation on
//! them fires. The controls `a_ctl` and `b_ctl`, the same bodies under trait names no
//! suffix test matches, are refused. The program panics (`..._run.rs`).
//!
//! AFTER (predicted): the marker requires the method to BE core's `branch` or
//! `from_residual` lang item, defined in a real sysroot crate, so `a` and `b` take
//! their controls' path: the call keeps the `[trust-absent-callee-assumption] ...
//! may panic` row. The annotations on `a` and `b` are what the BEFORE compiler prints
//! for `a_ctl` and `b_ctl`, line for line.
//!
//! Controls that must keep proving: std's `?` on `Option` and on `Result`, and a
//! CONVERTING `?` whose `From` impl is structurally total. Their callees ARE the lang
//! items, so the fix leaves them alone (measured BEFORE: each reads
//! `unreach proved`, no diagnostic, in both revisions).

extern crate try_total_user_try_trait_dep as dep;

pub struct Wide(pub u8);

impl From<u8> for Wide {
    fn from(v: u8) -> Wide {
        Wide(v)
    }
}

pub fn a(x: Option<u32>) -> u32 {
    //[default,certify]~^ ERROR Trust strict verification failed for `try_total_user_try_trait::a`: 1 obligation(s) were not fully verified
    //[certify]~^^ ERROR Trust Level 0 safety verification incomplete for `try_total_user_try_trait::a`: 1 obligation(s) were not proved
    dep::Try::branch(x)
}

pub fn b(r: u8) -> Option<u32> {
    //[default,certify]~^ ERROR Trust strict verification failed for `try_total_user_try_trait::b`: 1 obligation(s) were not fully verified
    //[certify]~^^ ERROR Trust Level 0 safety verification incomplete for `try_total_user_try_trait::b`: 1 obligation(s) were not proved
    <Option<u32> as dep::FromResidual<u8>>::from_residual(r)
}

pub fn a_ctl(x: Option<u32>) -> u32 {
    //[default,certify]~^ ERROR Trust strict verification failed for `try_total_user_try_trait::a_ctl`: 1 obligation(s) were not fully verified
    //[certify]~^^ ERROR Trust Level 0 safety verification incomplete for `try_total_user_try_trait::a_ctl`: 1 obligation(s) were not proved
    dep::Tri::branch(x)
}

pub fn b_ctl(r: u8) -> Option<u32> {
    //[default,certify]~^ ERROR Trust strict verification failed for `try_total_user_try_trait::b_ctl`: 1 obligation(s) were not fully verified
    //[certify]~^^ ERROR Trust Level 0 safety verification incomplete for `try_total_user_try_trait::b_ctl`: 1 obligation(s) were not proved
    <Option<u32> as dep::FromResid<u8>>::from_residual(r)
}

pub fn std_option(x: Option<u32>) -> Option<u32> {
    let v = x?;
    Some(v)
}

pub fn std_result(x: Result<u32, u8>) -> Result<u32, u8> {
    let v = x?;
    Ok(v)
}

pub fn std_converting(x: Result<u32, u8>) -> Result<u32, Wide> {
    let v = x?;
    Ok(v)
}
