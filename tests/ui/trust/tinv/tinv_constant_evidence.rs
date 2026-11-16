//@ revisions: pos constant_s dyn_s
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
//@ [pos] forbid-output: function: "tinv_constant_evidence::best"
//! TINV step 8b amended (decision TINV-32; ALab blocker (b)): a constant whose rustc type
//! cannot hold `S` no longer withholds `S`. Before, ONE opaque constant passed to a call
//! anywhere in the crate (astream_term `rasterize`'s `unwrap_or(Cell::BLANK)`, a3d_solve's
//! `for f in RUNGS`) withheld every candidate type at synthesis.
//!
//! `pos`: `P` (the P1 parser shape) certifies beside `for f in RUNGS` (`[f64; 6]`) and
//! `unwrap_or(Cell::BLANK)` in unrelated bodies: the census proves no constant of those
//! bodies can hold a `P`. `Cell` itself (also a candidate: private fields) IS withheld by
//! `cell_or_blank`'s `Cell::BLANK`, which does hold a `Cell`: the refusal is per type.
//! `constant_s`: `const P0: P` passed by value and by reference to calls: those bodies'
//! constants reach `P`, so `P` is still withheld (`ConstantConstruction`), while the
//! unrelated candidate `Q` of the same crate still certifies (the refusal is per type).
//! `dyn_s`: `const D: &dyn Any = &P { .. }` handed to a call: a constant that holds a
//! `dyn` is no evidence, so `P` is still withheld.
//!
//! MEASURED 2026-10-10 (stage 1 of `tinv/alab-blockers`, fixes (a)+(b)), as annotated.
#![forbid(unsafe_code)]

struct P<'a> {
    //[pos]~^ NOTE TINV: type invariant of `tinv_constant_evidence::P` certified: 1 conjunct(s)
    //[constant_s]~^^ NOTE TINV: no type invariant of `tinv_constant_evidence::P` is certified
    //[constant_s]~^^^ NOTE withheld at synthesis: ConstantConstruction
    //[dyn_s]~^^^^ NOTE TINV: no type invariant of `tinv_constant_evidence::P` is certified
    //[dyn_s]~^^^^^ NOTE withheld at synthesis: ConstantConstruction
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

#[derive(Clone, Copy, PartialEq)]
pub enum Color {
    Default,
    Idx(u8),
}

#[derive(Clone, Copy, PartialEq)]
pub struct Cell {
    //~^ NOTE TINV: no type invariant of `tinv_constant_evidence::Cell` is certified
    //~| NOTE withheld at synthesis: ConstantConstruction { function: "tinv_constant_evidence::cell_or_blank"
    ch: char,
    fg: Color,
    bg: Color,
    attrs: u8,
}

impl Cell {
    pub const BLANK: Cell = Cell { ch: ' ', fg: Color::Default, bg: Color::Default, attrs: 0 };
}

const RUNGS: [f64; 6] = [1e-3, 1e-4, 1e-5, 1e-6, 1e-7, 1e-8];

pub fn best(x: f64) -> f64 {
    let mut out = 0.0;
    for f in RUNGS {
        out += f * x;
    }
    out
}

pub fn cell_or_blank(c: Option<Cell>) -> Cell {
    c.unwrap_or(Cell::BLANK)
}

#[cfg(constant_s)]
const P0: P<'static> = P { b: b"", i: 0 };

#[cfg(constant_s)]
fn take(p: P<'static>) -> usize {
    p.i
}

#[cfg(constant_s)]
fn take_ref(p: &P<'static>) -> usize {
    p.i
}

#[cfg(constant_s)]
pub fn use_const() -> usize {
    take(P0) + take_ref(&P0)
}

#[cfg(constant_s)]
struct Q {
    //[constant_s]~^ NOTE TINV: type invariant of `tinv_constant_evidence::Q` certified
    n: usize,
    m: usize,
}

#[cfg(constant_s)]
pub fn q(n: usize) -> usize {
    let q = Q { n, m: n + 1 };
    q.m - q.n
}

#[cfg(dyn_s)]
const D: &dyn core::any::Any = &P { b: b"", i: 0 };

#[cfg(dyn_s)]
fn look(d: &dyn core::any::Any) -> bool {
    d.is::<u8>()
}

#[cfg(dyn_s)]
pub fn via_dyn() -> bool {
    look(D)
}
