//@ revisions: rec dynfield
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory --crate-type lib -Ztrust-tinv
//@ rustc-env:TRUST_TINV_NOTES=1
//@ build-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: HELP
//@ forbid-output: withheld at G
//@ forbid-output: withheld by the escape census
//@ forbid-output: withheld at synthesis
//@ [rec] forbid-output: unknown reach
//! TINV mint, `place_write::type_reaches` on a RECURSIVE datatype (the ALab blocker (a):
//! a3d_wire's `enum Json { Arr(Vec<Json>), Obj(Vec<(String, Json)>) }` beside its json
//! `Parser`). The derived `Clone`/`PartialEq` of `Json` pass `&Vec<Json>` and
//! `&Vec<(String, Json)>` to calls; the extracted argument type mentions the bare `Json`
//! marker, whose definition mentions it again. Before the least-fixpoint walk the reach
//! burnt its fuel and answered `Unknown` for EVERY candidate, so `P` (which `Json` cannot
//! contain) was withheld at the mint with "a call argument of unknown reach".
//!
//! `rec`: the walk answers `No`, and `P` certifies `i <= len(b)` exactly as
//! `tinv_p1_json_parser` does without `Json`.
//! `dynfield`: one variant also holds a `&'static dyn Debug`, and another body erases a `P`
//! into a `dyn` (so TINV-33 gives no `dyn` evidence): the trait object may hide a `P`, the
//! fixpoint must not turn that `Unknown` into `No`, and the derived `Clone`'s call argument
//! still withholds `P`.
//!
//! MEASURED 2026-10-10 (stage 1 of `tinv/alab-blockers`, fixes (a)+(b)): `rec` certifies
//! (1 conjunct, 8 kernel-certified rows, 2 arm lemmas); `dynfield` is withheld at the mint
//! with `Write("a call argument of unknown reach at bb2[7]")` in `<Json as Clone>::clone`.
//! RE-MEASURED with (c) (TINV-33) and the `erase` body: unchanged.
#![forbid(unsafe_code)]

#[cfg_attr(rec, derive(Clone, PartialEq))]
#[cfg_attr(dynfield, derive(Clone))]
pub enum Json {
    Null,
    Num(f64),
    Str(String),
    Arr(Vec<Json>),
    Obj(Vec<(String, Json)>),
    #[cfg(dynfield)]
    Dbg(&'static dyn core::fmt::Debug),
}

struct P<'a> {
    //[rec]~^ NOTE TINV: type invariant of `tinv_recursive_reach::P` certified: 1 conjunct(s)
    //[dynfield]~^^ NOTE TINV: no type invariant of `tinv_recursive_reach::P` is certified
    //[dynfield]~^^^ NOTE type invariant withheld: Write("a call argument of unknown reach at
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

#[cfg(rec)]
pub fn same(a: &Json, b: &Json) -> bool {
    a.clone() == *b
}

#[cfg(dynfield)]
pub fn copy(a: &Json) -> Json {
    a.clone()
}

// Some body erases a `P` into a `dyn` (`&P` unsized to `&dyn Any`), so under TINV-33 a
// `dyn` of this crate MAY hide a `P`, and the `&'static dyn Debug` field keeps the derived
// `Clone`'s argument of unknown reach. (A closure `|| p.i` would not do: edition-2021
// precise capture takes `&p.i`, a `&usize`, so nothing reaching `P` is erased.)
#[cfg(dynfield)]
pub fn erase() -> bool {
    let p: P<'static> = P { b: b"x", i: 0 };
    let d: &dyn core::any::Any = &p;
    d.is::<u8>()
}
