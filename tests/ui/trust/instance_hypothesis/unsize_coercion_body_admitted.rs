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
//! OD-1 item 18 (shape 3): a body that performs an UNSIZING coercion. preview2's
//! nn-glm5/nn-qwen3 rows (`<impl AsRef<VarBuilder>>::as_ref`, 10 rows) are bodies like
//! `load` below: the `impl Trait` dispatch itself is admissible, but the body also
//! writes `vb.get(&[n], "w")`, an `&[usize; 1] -> &[usize]` coercion, and D33's census
//! (the body's unsafe-operation fence) counts EVERY cast to a non-scalar target as an
//! unsafe operation, because the extracted `Rvalue::Cast` carries no cast kind. So the
//! whole body admitted no site. The same census arm refused every serde-derive
//! `visit_seq`/`visit_u64` body (`&"…" as &dyn Expected`).
//!
//! An unsizing coercion is safe code: it writes nothing and attaches a length or a
//! vtable to the source pointer. The census now skips reference-target casts, but
//! ONLY when the MIR the body was extracted from shows that every cast with a
//! reference target is a `PointerCoercion::Unsize`
//! (`reference_casts_are_unsize`); any other reference-target cast (an inlined
//! `transmute`) keeps the full census.
//!
//! Admitted: `load` (slice unsize, `impl Trait` argument), `fmt_like` (trait-object
//! unsize the body builds and keeps to itself; its own `d.show()` on that self-built
//! trait object keeps the disclosed `runtime_checked` label, OD-1 item 14(c), which
//! strict and certify refuse). The control (a reference-target cast
//! that is not an unsizing coercion) is `unsize_coercion_transmute_body_not_admitted.rs`.

pub struct VarBuilder;

impl VarBuilder {
    pub fn get(&self, dims: &[usize]) -> usize {
        dims.len()
    }
}

pub fn load(vb: &impl AsRef<VarBuilder>, n: usize) -> usize {
    //[advisory]~^ WARN Trust verification advisory for `unsize_coercion_body_admitted::load`: 1 instance hypothesis row(s)
    //[strict]~^^ WARN Trust verification advisory for `unsize_coercion_body_admitted::load`: 1 instance hypothesis row(s)
    //[certify]~^^^ ERROR Trust certify verification failed for `unsize_coercion_body_admitted::load`: 1 instance hypothesis row(s)
    let vb = vb.as_ref();
    vb.get(&[n])
}

pub trait Show {
    fn show(&self) -> usize;
}

impl Show for u32 {
    fn show(&self) -> usize {
        4
    }
}

pub trait Sink {
    fn put(&self, n: usize);
}

pub fn fmt_like<S: Sink>(s: &S, v: u32) {
    //[advisory]~^ WARN Trust verification advisory for `unsize_coercion_body_admitted::fmt_like`: 1 instance hypothesis row(s)
    //[strict]~^^ WARN Trust verification advisory for `unsize_coercion_body_admitted::fmt_like`: 1 instance hypothesis row(s)
    //[strict]~^^^ ERROR Trust strict verification failed for `unsize_coercion_body_admitted::fmt_like`: 1 obligation(s) were not fully verified
    //[certify]~^^^^ ERROR Trust Level 0 safety verification incomplete for `unsize_coercion_body_admitted::fmt_like`: 1 obligation(s) were not proved
    //[certify]~^^^^^ ERROR Trust certify verification failed for `unsize_coercion_body_admitted::fmt_like`: 1 instance hypothesis row(s)
    //[certify]~^^^^^^ ERROR Trust strict verification failed for `unsize_coercion_body_admitted::fmt_like`: 1 obligation(s) were not fully verified
    let d: &dyn Show = &v;
    s.put(d.show())
}
