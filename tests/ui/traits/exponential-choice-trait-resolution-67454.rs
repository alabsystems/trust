// Trust: regression test for compile-time bug rust-lang#67454
//
// Parser combinator patterns with many alternatives (choice/or branches)
// cause exponential trait resolution time. The pattern is: an enum-like
// type with N variants, each requiring trait resolution, combined with
// error-reporting traits that add a multiplier at each level.
//
// The original report was from the `combine` crate where `choice!` with
// many branches caused compile times to explode. The root cause is that
// trait resolution for `impl Trait` return types with many branches
// requires evaluating all possible trait impls at each use site.
//
// This test uses 12 variants with a layered trait bound structure.
// Without deduplication in the solver, obligation count grows as O(N^2)
// or worse.
//
// Upstream: https://github.com/rust-lang/rust/issues/67454
// Tracked in Trust: #865
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//@ check-pass

trait Process {
    type Output;
    fn run(&self) -> Self::Output;
}

trait WithContext: Process {
    fn context(self, msg: &'static str) -> Contextual<Self>
    where
        Self: Sized,
    {
        Contextual { inner: self, _msg: msg }
    }
}

impl<T: Process> WithContext for T {}

struct Contextual<P> {
    inner: P,
    _msg: &'static str,
}

impl<P: Process> Process for Contextual<P> {
    type Output = P::Output;
    fn run(&self) -> Self::Output { self.inner.run() }
}

// Many concrete processors — each is a distinct type the trait solver
// must resolve independently.
struct P1; struct P2; struct P3; struct P4;
struct P5; struct P6; struct P7; struct P8;
struct P9; struct P10; struct P11; struct P12;

impl Process for P1 { type Output = u8; fn run(&self) -> u8 { 1 } }
impl Process for P2 { type Output = u8; fn run(&self) -> u8 { 2 } }
impl Process for P3 { type Output = u8; fn run(&self) -> u8 { 3 } }
impl Process for P4 { type Output = u8; fn run(&self) -> u8 { 4 } }
impl Process for P5 { type Output = u8; fn run(&self) -> u8 { 5 } }
impl Process for P6 { type Output = u8; fn run(&self) -> u8 { 6 } }
impl Process for P7 { type Output = u8; fn run(&self) -> u8 { 7 } }
impl Process for P8 { type Output = u8; fn run(&self) -> u8 { 8 } }
impl Process for P9 { type Output = u8; fn run(&self) -> u8 { 9 } }
impl Process for P10 { type Output = u8; fn run(&self) -> u8 { 10 } }
impl Process for P11 { type Output = u8; fn run(&self) -> u8 { 11 } }
impl Process for P12 { type Output = u8; fn run(&self) -> u8 { 12 } }

// Simulates `choice!` — returning an opaque type that the compiler must
// resolve through all branches. The `.context()` call adds an extra
// layer of trait resolution at each branch.
fn make_processor(n: u8) -> Box<dyn Process<Output = u8>> {
    match n {
        1 => Box::new(P1.context("p1")),
        2 => Box::new(P2.context("p2")),
        3 => Box::new(P3.context("p3")),
        4 => Box::new(P4.context("p4")),
        5 => Box::new(P5.context("p5")),
        6 => Box::new(P6.context("p6")),
        7 => Box::new(P7.context("p7")),
        8 => Box::new(P8.context("p8")),
        9 => Box::new(P9.context("p9")),
        10 => Box::new(P10.context("p10")),
        11 => Box::new(P11.context("p11")),
        12 => Box::new(P12.context("p12")),
        _ => Box::new(P1.context("default")),
    }
}

pub fn main() {
    // Force the compiler to resolve Process trait for all 12 Contextual<PN>
    // types and verify they satisfy the dyn Process<Output = u8> bound.
    let p = make_processor(7);
    assert_eq!(p.run(), 7);
}
