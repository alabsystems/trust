//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory --crate-type lib -Ztrust-tinv
//@ rustc-env:TRUST_TINV_NOTES=1
//@ build-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: HELP
//@ forbid-output: internal compiler error
//! The escape census and a TRAIT associated constant read through a type parameter
//! (`fn g<T: K>() -> T { T::C }`, instantiated with `T = P`). The census followed the
//! instantiation to the trait item `K::C`, which has no body, and ICEd in `with_body`
//! ("can't type-check body of `K::C`"). It now resolves the constant to the impl's body
//! (`Instance::try_resolve`) and denies what an unresolvable one touches.
//!
//! The constant must also stay a refusal for `P` (decision TINV-32 never clears a constant
//! whose type keeps a parameter): `P` is withheld.
//!
//! MEASURED 2026-10-10 (stage 1 of `tinv/alab-blockers`), as annotated.
#![forbid(unsafe_code)]

struct P<'a> {
    //~^ NOTE TINV: no type invariant of `tinv_assoc_const_generic::P` is certified
    //~| NOTE withheld at synthesis: ConstantConstruction { function: "tinv_assoc_const_generic::g"
    b: &'a [u8],
    i: usize,
}

impl<'a> P<'a> {
    fn literal(&mut self, w: &'static [u8]) -> bool {
        if self.b.len() >= self.i + w.len() && &self.b[self.i..self.i + w.len()] == w {
            self.i += w.len();
            true
        } else {
            false
        }
    }
}

pub fn parse(b: &[u8]) -> bool {
    let mut p = P { b, i: 0 };
    p.literal(b"null")
}

trait K {
    const C: Self;
}

impl K for P<'static> {
    const C: Self = P { b: b"", i: 0 };
}

fn g<T: K>() -> T {
    T::C
}

pub fn via_generic() -> bool {
    let mut p: P<'static> = g();
    p.literal(b"x")
}
