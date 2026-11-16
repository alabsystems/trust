//@ revisions: advisory strict certify
//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Ztrust-verify-output=both --crate-type=lib
//@[advisory] compile-flags: -Ztrust-policy=advisory
//@[strict] compile-flags: -Ztrust-policy=strict
//@[certify] compile-flags: -Ztrust-policy=certify
//@ dont-check-compiler-stderr
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE
//@[advisory] check-pass
//@[strict] check-fail
//@[certify] check-fail
//! OD-1 T-D (2026-10-12): a generic body that FORMATS something. preview4 (stage 1
//! `35a39d5c74`) kept nn-glm5 `Glm5MLP::load`/`Glm5Model::load` and nn-qwen3
//! `Qwen3Model::load`/`Qwen3MoeModel::load` as class (c) `failed` rows on their
//! `<impl AsRef<VarBuilder>>::as_ref` site, while their siblings without a `format!` were
//! admitted: D33's census counted the `format_args!` desugaring's own call to the
//! `unsafe fn core::fmt::Arguments::new` as "a call to an unsafe-signature function" and
//! refused the whole body. That call is now not counted, only where the MIR callee is the
//! authenticated sysroot `FmtArgumentsNew` impl's `new` AND its call span lies in a
//! `CompilerGenerated` unsafe block of the body's own HIR.
//!
//! Admitted: `load_fmt` (the nn shape: `format!` on an error path) and `load_fmt_twice`.
//! The controls are `format_args_body_controls_not_admitted.rs` (a separate file:
//! compiletest keeps only the first 512 KiB of stderr).
//! Discharge: `use_bad` names `load_fmt::<Bad>`, whose `as_ref` panics: a `failed`
//! discharge row (an error on strict and certify); `use_good` a `proved` one.

pub struct Vb(pub u32);

pub fn load_fmt<T: AsRef<Vb>>(vb: &T, n: u32) -> Result<u32, String> {
    //[advisory]~^ WARN Trust verification advisory for `format_args_body_admitted::load_fmt`: 1 instance hypothesis row(s)
    //[strict]~^^ WARN Trust verification advisory for `format_args_body_admitted::load_fmt`: 1 instance hypothesis row(s)
    //[certify]~^^^ ERROR Trust Level 0 safety verification incomplete for `format_args_body_admitted::load_fmt`
    //[certify]~^^^^ ERROR Trust certify verification failed for `format_args_body_admitted::load_fmt`: 1 instance hypothesis row(s)
    //[certify]~^^^^^ ERROR Trust strict verification failed for `format_args_body_admitted::load_fmt`
    let vb = vb.as_ref();
    if n == 0 {
        return Err(format!("bad n={n}"));
    }
    Ok(vb.0)
}

pub fn load_fmt_twice(vb: &impl AsRef<Vb>, n: u32) -> Result<u32, String> {
    //[advisory]~^ WARN Trust verification advisory for `format_args_body_admitted::load_fmt_twice`: 1 instance hypothesis row(s)
    //[strict]~^^ WARN Trust verification advisory for `format_args_body_admitted::load_fmt_twice`: 1 instance hypothesis row(s)
    //[certify]~^^^ ERROR Trust Level 0 safety verification incomplete for `format_args_body_admitted::load_fmt_twice`
    //[certify]~^^^^ ERROR Trust certify verification failed for `format_args_body_admitted::load_fmt_twice`: 1 instance hypothesis row(s)
    //[certify]~^^^^^ ERROR Trust strict verification failed for `format_args_body_admitted::load_fmt_twice`
    let vb = vb.as_ref();
    if n == 0 {
        return Err(format!("bad n={n}, vb={}", vb.0));
    }
    Ok(vb.0)
}

pub struct Bad;
impl AsRef<Vb> for Bad {
    fn as_ref(&self) -> &Vb {
        //[strict]~^ ERROR Trust Level 0 safety verification incomplete for `<format_args_body_admitted::Bad as core::convert::AsRef<format_args_body_admitted::Vb>>::as_ref`
        //[strict]~^^ ERROR Trust strict verification failed for `<format_args_body_admitted::Bad as core::convert::AsRef<format_args_body_admitted::Vb>>::as_ref`
        //[certify]~^^^ ERROR Trust Level 0 safety verification incomplete for `<format_args_body_admitted::Bad as core::convert::AsRef<format_args_body_admitted::Vb>>::as_ref`
        //[certify]~^^^^ ERROR Trust strict verification failed for `<format_args_body_admitted::Bad as core::convert::AsRef<format_args_body_admitted::Vb>>::as_ref`
        panic!("bad")
    }
}

pub struct Good(pub Vb);
impl AsRef<Vb> for Good {
    fn as_ref(&self) -> &Vb {
        &self.0
    }
}

pub fn use_bad() -> Result<u32, String> {
    //[advisory]~^ WARN Trust instance discharge not established for `format_args_body_admitted::use_bad`
    //[strict]~^^ ERROR Trust instance discharge not established for `format_args_body_admitted::use_bad`
    //[strict]~^^^ ERROR Trust strict verification failed for `format_args_body_admitted::use_bad`
    //[certify]~^^^^ ERROR Trust Level 0 safety verification incomplete for `format_args_body_admitted::use_bad`
    //[certify]~^^^^^ ERROR Trust instance discharge not established for `format_args_body_admitted::use_bad`
    //[certify]~^^^^^^ ERROR Trust strict verification failed for `format_args_body_admitted::use_bad`
    load_fmt(&Bad, 1)
}

pub fn use_good() -> Result<u32, String> {
    //[strict]~^ ERROR Trust strict verification failed for `format_args_body_admitted::use_good`
    //[certify]~^^ ERROR Trust Level 0 safety verification incomplete for `format_args_body_admitted::use_good`
    //[certify]~^^^ ERROR Trust strict verification failed for `format_args_body_admitted::use_good`
    load_fmt(&Good(Vb(3)), 1)
}
