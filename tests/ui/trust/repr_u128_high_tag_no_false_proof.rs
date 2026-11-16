//@ revisions: default certify control
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@[certify] compile-flags: -Ztrust-policy=certify
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! REPR-U128-HIGH-TAG-1: a `#[repr(u128)]` tag above `i128::MAX` has no `i128`
//! spelling, and `VariantDef::discriminant` is an `i128`. The extractor stored it as
//! the lossy `val as i128` (`u128::MAX` as `-1`, `1 << 127` as `i128::MIN`), and the
//! discriminant-domain fact then said `d ∈ {0, -1, 5}` about a `u128` read whose
//! `SwitchInt` label is the TRUE `u128::MAX`. The arm for that variant was UNSAT and
//! every row in it was PROVED. The lie is not limited to `match`: `local_aggregate`
//! and `local_payload` build the enum themselves, `returned` gets it from a call, and
//! `cast_index` reads the tag through `as` with no match at all.
//!
//! BEFORE, measured 2026-10-11 on `scratchpad/stage1-w22probe` (wave 22's BEFORE
//! compiler; it predates this fix) with each revision's flags plus `--cfg <revision>
//! -Zui-testing -Zdeduplicate-diagnostics=no -A unused --emit=metadata`: `default` and
//! `certify` exit 0, every function in `liars` reporting its arm's row `proved` and no
//! error, so every annotation in `liars` is missing. The run twin
//! `repr_u128_high_tag_no_false_proof_run.rs` panics in exactly those arms. `control`
//! exits 1 with both rows FAILED.
//!
//! FIX: such an enum is `Unsupported` at extraction (`ty_convert::lower_enum_adt`), so
//! no consumer sees a false tag, and trust-vcgen declines a negative tag read into an
//! unsigned destination. Each arm's row is then a real refutation. The CONTROLS —
//! `repr(u128)` at `i128::MAX` and `repr(i128)` at `i128::MIN`, both of which have an
//! `i128` spelling — were refuted before and must stay refuted.
//!
//! AFTER, measured 2026-10-11 under compiletest on the stage 1 of `integ/wave22`
//! `618d7bd287`: in `default` and `certify` every liar's arm row is FAILED at the true
//! tag, alongside `Trust Level 0 safety verification incomplete` and `Trust full
//! verification failed` (the enum is an `Unsupported` leaf, so native typed-TrustIr
//! lowering does not complete). No liar reports `Trust strict verification failed`, so
//! the liars' ERROR annotation names the Level 0 error; the controls still report it.
//! The annotations are revision-scoped because `liars` is compiled out under
//! `control` and `controls` under the other two.
//!
//! Do not "fix" this file by weakening an annotation: every row annotated FAILED is a
//! panic the run twin reaches.

#[cfg(not(control))]
pub mod liars {
    #[repr(u128)]
    pub enum E {
        A = 0,
        B = u128::MAX,
        C = 5,
    }

    #[repr(u128)]
    pub enum Hi {
        A = 0,
        B = 1u128 << 127,
        C = 3,
    }

    #[repr(u128)]
    pub enum K {
        A = 0,
        B = u128::MAX,
        C = 3,
    }

    #[repr(u128)]
    pub enum P {
        A(u8) = 0,
        B(u8) = u128::MAX,
        C = 3,
    }

    pub fn index_arm(e: E, a: &[u8; 1], i: usize) -> u8 {
        //[default,certify]~^ ERROR Trust Level 0 safety verification incomplete
        //[default,certify]~| NOTE [bounds] FAILED
        match e {
            E::B => a[i],
            _ => 0,
        }
    }

    pub fn add_arm(e: E, x: u8) -> u8 {
        //[default,certify]~^ ERROR Trust Level 0 safety verification incomplete
        //[default,certify]~| NOTE [overflow:add] FAILED
        if let E::B = e { x + 1 } else { 0 }
    }

    pub fn payload_arm(e: &P) -> u8 {
        //[default,certify]~^ ERROR Trust Level 0 safety verification incomplete
        //[default,certify]~| NOTE [overflow:add] FAILED
        match e {
            P::B(x) => *x + 1,
            _ => 0,
        }
    }

    pub fn top_bit_arm(e: Hi, a: &[u8; 1], i: usize) -> u8 {
        //[default,certify]~^ ERROR Trust Level 0 safety verification incomplete
        //[default,certify]~| NOTE [bounds] FAILED
        match e {
            Hi::B => a[i],
            _ => 0,
        }
    }

    #[inline(never)]
    pub fn mk(b: bool) -> E {
        if b { E::B } else { E::A }
    }

    pub fn returned(b: bool, a: &[u8; 1], i: usize) -> u8 {
        //[default,certify]~^ ERROR Trust Level 0 safety verification incomplete
        //[default,certify]~| NOTE [bounds] FAILED
        match mk(b) {
            E::B => a[i],
            _ => 0,
        }
    }

    pub fn local_aggregate(b: bool, x: u8) -> u8 {
        //[default,certify]~^ ERROR Trust Level 0 safety verification incomplete
        //[default,certify]~| NOTE [overflow:add] FAILED
        let e = if b { E::B } else { E::A };
        match e {
            E::B => x + 1,
            _ => 0,
        }
    }

    pub fn local_payload(b: bool, x: u8) -> u8 {
        //[default,certify]~^ ERROR Trust Level 0 safety verification incomplete
        //[default,certify]~| NOTE [overflow:add] FAILED
        let e = if b { P::B(x) } else { P::A(x) };
        match e {
            P::B(y) => y + 1,
            _ => 0,
        }
    }

    pub fn cast_index(e: K, a: &[u8; 4]) -> u8 {
        //[default,certify]~^ ERROR Trust Level 0 safety verification incomplete
        //[default,certify]~| NOTE [bounds] FAILED
        let d = e as u128;
        if d > 3 { a[(d - u128::MAX + 4) as usize] } else { 0 }
    }
}

// CONTROLS: refuted before the fix, and after it.
#[cfg(control)]
pub mod controls {
    #[repr(u128)]
    pub enum Fits {
        A = 0,
        B = i128::MAX as u128,
        C = 5,
    }

    #[repr(i128)]
    pub enum Neg {
        A = 0,
        B = i128::MIN,
        C = 5,
    }

    pub fn at_i128_max(e: Fits, x: u8) -> u8 {
        //[control]~^ ERROR Trust strict verification failed
        //[control]~| NOTE [overflow:add] FAILED
        if let Fits::B = e { x + 1 } else { 0 }
    }

    pub fn at_i128_min(e: Neg, x: u8) -> u8 {
        //[control]~^ ERROR Trust strict verification failed
        //[control]~| NOTE [overflow:add] FAILED
        if let Neg::B = e { x + 1 } else { 0 }
    }
}
