//@ revisions: fmt erased exported param param_s wrapped
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory --crate-type lib -Ztrust-tinv
//@ rustc-env:TRUST_TINV_NOTES=1
//@ build-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: HELP
//@ forbid-output: withheld by the escape census
//@ forbid-output: withheld at synthesis
//@ [fmt] forbid-output: unknown reach
//@ [param] forbid-output: unknown reach
//! TINV mint, decision TINV-33 (ALab step (c)): a `dyn` or a type parameter reaches a
//! crate-private `S` only if the crate lets it. Before, every derived `Debug::fmt` (its
//! `&mut Formatter` holds `&mut dyn Write`) and every polymorphic body's `I`-typed call
//! argument was "a call argument of unknown reach" for EVERY candidate.
//!
//! `fmt`: `P` certifies beside a derived-`Debug` `Json` that is formatted: no body unsizes a
//! type reaching `P` into a `dyn`, `P` is never handed to the sysroot, and it is private.
//! `erased`: one body unsizes `&P` into `&dyn Debug`: the `dyn` may be a `P`, so the
//! derived `Debug::fmt` arguments keep the refusal.
//! `exported`: `P` is `pub` (fields private) and returned by a `pub fn`: downstream code
//! can erase it into a `dyn` unseen, so the refusal stays.
//! `param`: `P` certifies beside a local generic `count<I: Iterator>` instantiated only
//! with `Copied<slice::Iter<u8>>`.
//! `param_s`: the local generic `with<T>` is instantiated with `T = P`: its `&T` argument
//! may be a `P`, so the refusal stays.
//! `wrapped`: `P` stays private, but a `pub struct Wrap` holds one in a private field:
//! downstream code can hold a `Wrap` and erase it into a `dyn`, so TINV-33 grants no
//! evidence (premise (1) as amended) and the refusal stays.
//!
//! MEASURED 2026-10-10 (stage 1 of `tinv/alab-blockers`, fixes (a)+(b)+(c)), as annotated.
#![forbid(unsafe_code)]

#[cfg_attr(erased, derive(Debug))]
#[cfg(not(exported))]
struct P<'a> {
    //[fmt]~^ NOTE TINV: type invariant of `tinv_dyn_param_evidence::P` certified: 1 conjunct(s)
    //[param]~^^ NOTE TINV: type invariant of `tinv_dyn_param_evidence::P` certified: 1 conjunct(s)
    //[erased]~^^^ NOTE TINV: no type invariant of `tinv_dyn_param_evidence::P` is certified
    //[erased]~^^^^ NOTE a call argument of unknown reach
    //[param_s]~^^^^^ NOTE TINV: no type invariant of `tinv_dyn_param_evidence::P` is certified
    //[param_s]~^^^^^^ NOTE a call argument of unknown reach
    //[wrapped]~^^^^^^^ NOTE TINV: no type invariant of `tinv_dyn_param_evidence::P` is certified
    //[wrapped]~^^^^^^^^ NOTE a call argument of unknown reach
    b: &'a [u8],
    i: usize,
}

#[cfg(exported)]
pub struct P<'a> {
    //[exported]~^ NOTE TINV: no type invariant of `tinv_dyn_param_evidence::P` is certified
    //[exported]~^^ NOTE a call argument of unknown reach
    b: &'a [u8],
    i: usize,
}

impl<'a> P<'a> {
    fn peek(&self) -> Option<u8> {
        self.b.get(self.i).copied()
    }

    fn bump(&mut self) -> Option<u8> {
        let c = self.peek()?;
        self.i += 1;
        Some(c)
    }

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
    p.bump();
    p.literal(b"null")
}

#[derive(Debug)]
pub enum Json {
    Null,
    Num(f64),
    Arr(Vec<Json>),
}

pub fn show(j: &Json) -> String {
    format!("{j:?}")
}

#[cfg(erased)]
pub fn erased(b: &[u8]) -> usize {
    let p = P { b, i: 0 };
    let d: &dyn core::fmt::Debug = &p;
    format!("{d:?}").len()
}

#[cfg(exported)]
pub fn make(b: &[u8]) -> P<'_> {
    P { b, i: 0 }
}

#[cfg(param)]
fn count<I: Iterator<Item = u8>>(it: I) -> usize {
    it.count()
}

#[cfg(param)]
pub fn bytes(b: &[u8]) -> usize {
    count(b.iter().copied())
}

#[cfg(param_s)]
fn with<T>(t: &T, f: fn(&T) -> usize) -> usize {
    f(t)
}

#[cfg(param_s)]
fn pos(p: &P<'_>) -> usize {
    p.i
}

#[cfg(param_s)]
pub fn at(b: &[u8]) -> usize {
    let p = P { b, i: 0 };
    with(&p, pos)
}

#[cfg(wrapped)]
pub struct Wrap(P<'static>);

#[cfg(wrapped)]
pub fn wrap() -> Wrap {
    Wrap(P { b: b"", i: 0 })
}
