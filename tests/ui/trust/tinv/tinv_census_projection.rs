//@ revisions: control forge corrupt peek_dyn peek_generic peek_corrupt wconst a_local a_foreign b_transitive c_hold_peek c_hold_inner d_conjure e_public d_for_each d_any d_map_count d_each_items d_each_forge alias_poke w_first w_sink
//@ needs-trust-verify
//@ aux-build:tinv_tp_forge.rs
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory --crate-type lib -Ztrust-tinv
//@ rustc-env:TRUST_TINV_NOTES=1
//@ build-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: HELP
//! The escape census and PROJECTIONS (adversarial review of `tinv/alab-blockers`): every
//! type the census reads is now instantiated and normalized, and a storage component
//! that stays a concrete alias fails closed. Each revision below is a program shape that
//! slipped past the census before, with `P` (the P1 parser, `i <= len(b)`) as the
//! candidate. `control` certifies `P`; every other revision must withhold it.
//!
//! `forge`: a third-party `forge::<Map<Range<u8>, fn(u8) -> P>>() -> I::Item` returns a
//! `P` made by `mem::zeroed` (TINV D1 must see the normalized `P` output).
//! `corrupt`: the third-party `corrupt::<Map<..>>(&mut p)` writes bytes into a `P`
//! (rule 4 / D1 must see the normalized `&mut P` input).
//! `peek_dyn`: a `Peekable<Map<..>>` stores `Option<Option<P>>` in its private `peeked`
//! field; erasing it to `&mut dyn Debug` must count `P` as erased into a `dyn`, so the
//! TINV-33 `dyn` evidence is withheld (the derived `Debug::fmt` argument keeps its refusal).
//! `peek_generic`: a local generic `g::<Peekable<..>>` receives it (and formats it through
//! a `dyn`); the TINV-33 evidence is withheld.
//! In both, building the `Peekable` hands it to sysroot code (`map`, `peekable`, `peek`),
//! which now also counts `P` as handed out: the refusal does not isolate the unsize or the
//! instantiation, it pins that the walk sees the `P` inside the `Peekable` at all.
//! `peek_corrupt`: the third-party `corrupt_any(&mut peekable)` may overwrite the `P` it
//! holds (rule 4 must see the foreign storage).
//! `wconst`: `const C: W<X>` where `W`'s field is `<X as Tr>::Out = P`: TINV-32 must not
//! clear that constant (its census walk normalizes the field to `P`).
//!
//!
//! The re-review of `2249ae63f8` found that reading a projection over a parameter like the
//! parameter (and relying on every concrete instantiation being scanned) is unsound; the
//! census now FAILS CLOSED on any projection in a type's storage (TINV-33 amended). Shapes:
//! `a_local`: `scrub<T: Tr>(w: &mut W<T>)` with `W<T> { f: T::Out }` hands `w` to a
//! third-party `corrupt_any` (instantiated with `T = X`, `X::Out = P`).
//! `a_foreign`: the same with `scrub<I: Iterator>(&mut Peekable<I>)`.
//! `b_transitive`: `outer::<Map<..>>` calls `inner::<I>`, whose `I::Item` local goes to the
//! third-party `corrupt::<I>`.
//! `c_hold_peek` / `c_hold_inner`: a third-party `Hold<I>(Peekable<I>)` /
//! `HoldInner<I>(Inner<I>)`, `Inner<I>(Option<I::Item>)`, handed to `corrupt_any`.
//! `d_conjure`: a third-party `impl Iterator for Conjure<I> { type Item = I::Item }` forges
//! a `P` that comes back through sysroot `take`/`collect`.
//! `e_public`: a PUBLIC generic `Wrap<T: Tr> { f: T::Out }`: downstream code can name
//! `Wrap<X>` (which holds a `P`) and erase it into a `dyn`, so TINV-33 grants no evidence.
//!
//!
//! Final review (residual D and the third-party raw pointer): `d_for_each`, `d_any`,
//! `d_map_count`: the forged `P` from `Conjure::next` reaches a local closure through a
//! sysroot `for_each` / `any` / `map(..).count()` whose signature reaches no `P` (the
//! third-party type in the arguments must make the census follow the sysroot bounds);
//! `d_each_items`: a third-party `each<I, F: FnMut(I::Item)>` calls back with the item
//! (the where-clause names it); `d_each_forge`: a third-party `each_forge::<P, _>` calls
//! back with a zeroed `P` (`F: FnOnce(T)`); `alias_poke`: a third-party `Alias<T>(*mut T)`
//! writes through its raw pointer from `&self` (its field keeps its raw-pointer reading).
//!
//!
//! CENSUS-THIRD-PARTY-1 (2026-10-11): every revision that CALLS third-party code is now
//! withheld first by the coarse rule (no certificate in a crate that calls, implements or
//! stores third-party code), pinned below with the first third-party use it names; the
//! precise analysis (rule 4, TINV D1, `follow_bounds`) still runs and only adds denials.
//! `peek_dyn`, `peek_generic`, `wconst` and `e_public` use no third-party code and keep
//! their own reasons. Round 4's shapes: `w_first` (a local `first<I: Iterator<Item = P>>`
//! over `tp::Conjure`: the `Item` binding normalizes the alias away) and `w_sink` (a local
//! `impl tp::Sink for L { type In = P }` whose provided `pump` forges `Self::In`).
//!
//! MEASURED 2026-10-11 (stage 1 of `tinv/alab-blockers` with CENSUS-THIRD-PARTY-1), as
//! annotated.
#![forbid(unsafe_code)]

// Only the revisions that use third-party code link it: under CENSUS-THIRD-PARTY-1 a crate
// whose graph links a third-party crate gets no certificate at all.
#[cfg(not(any(control, peek_dyn, peek_generic, wconst, e_public)))]
extern crate tinv_tp_forge as tp;

#[cfg_attr(any(peek_dyn, peek_generic, peek_corrupt), derive(Debug))]
struct P<'a> {
    //[control]~^ NOTE TINV: type invariant of `tinv_census_projection::P` certified: 1 conjunct(s)
    //[forge]~^^ NOTE TINV: no type invariant of `tinv_census_projection::P` is certified
    //[forge]~| NOTE withheld by the escape census: the crate uses third-party code (the crate graph links `tinv_tp_forge`; first use found: `forged` calls the third-party `tp::forge`)
    //[corrupt]~^^^^ NOTE TINV: no type invariant of `tinv_census_projection::P` is certified
    //[corrupt]~| NOTE withheld by the escape census: the crate uses third-party code (the crate graph links `tinv_tp_forge`; first use found: `corrupted` calls the third-party `tp::corrupt`)
    //[peek_dyn]~^^^^^^ NOTE TINV: no type invariant of `tinv_census_projection::P` is certified
    //[peek_dyn]~| NOTE a call argument of unknown reach at bb2[15] in `<tinv_census_projection::Json as core::fmt::Debug>::fmt`
    //[peek_generic]~^^^^^^^^ NOTE TINV: no type invariant of `tinv_census_projection::P` is certified
    //[peek_generic]~| NOTE a call argument of unknown reach at bb2[15] in `<tinv_census_projection::Json as core::fmt::Debug>::fmt`
    //[peek_corrupt]~^^^^^^^^^^ NOTE TINV: no type invariant of `tinv_census_projection::P` is certified
    //[peek_corrupt]~| NOTE withheld by the escape census: the crate uses third-party code (the crate graph links `tinv_tp_forge`; first use found: `corrupted_peek` calls the third-party `tp::corrupt_any`)
    //[wconst]~^^^^^^^^^^^^ NOTE TINV: no type invariant of `tinv_census_projection::P` is certified
    //[wconst]~| NOTE withheld at synthesis: ConstantConstruction { function: "tinv_census_projection::go"
    //[a_local]~^^^^^^^^^^^^^^ NOTE TINV: no type invariant of `tinv_census_projection::P` is certified
    //[a_local]~| NOTE withheld by the escape census: the crate uses third-party code (the crate graph links `tinv_tp_forge`; first use found: `scrub` calls the third-party `tp::corrupt_any`)
    //[a_foreign]~^^^^^^^^^^^^^^^^ NOTE TINV: no type invariant of `tinv_census_projection::P` is certified
    //[a_foreign]~| NOTE withheld by the escape census: the crate uses third-party code (the crate graph links `tinv_tp_forge`; first use found: `scrub_peek` calls the third-party `tp::corrupt_any`)
    //[b_transitive]~^^^^^^^^^^^^^^^^^^ NOTE TINV: no type invariant of `tinv_census_projection::P` is certified
    //[b_transitive]~| NOTE withheld by the escape census: the crate uses third-party code (the crate graph links `tinv_tp_forge`; first use found: `inner` calls the third-party `tp::corrupt`)
    //[c_hold_peek]~^^^^^^^^^^^^^^^^^^^^ NOTE TINV: no type invariant of `tinv_census_projection::P` is certified
    //[c_hold_peek]~| NOTE withheld by the escape census: the crate uses third-party code (the crate graph links `tinv_tp_forge`; first use found: `c_hold_peek` calls the third-party `tp::corrupt_any`)
    //[c_hold_inner]~^^^^^^^^^^^^^^^^^^^^^^ NOTE TINV: no type invariant of `tinv_census_projection::P` is certified
    //[c_hold_inner]~| NOTE withheld by the escape census: the crate uses third-party code (the crate graph links `tinv_tp_forge`; first use found: `c_hold_inner` calls the third-party `tp::corrupt_any`)
    //[d_conjure]~^^^^^^^^^^^^^^^^^^^^^^^^ NOTE TINV: no type invariant of `tinv_census_projection::P` is certified
    //[d_conjure]~| NOTE withheld by the escape census: the crate uses third-party code (the crate graph links `tinv_tp_forge`; first use found: `d_conjure` calls the third-party `tp::Conjure::<I>::new`)
    //[e_public]~^^^^^^^^^^^^^^^^^^^^^^^^^^ NOTE TINV: no type invariant of `tinv_census_projection::P` is certified
    //[e_public]~| NOTE a call argument of unknown reach at bb2[15] in `<tinv_census_projection::Json as core::fmt::Debug>::fmt`
    //[d_for_each]~^^^^^^^^^^^^^^^^^^^^^^^^^^^^ NOTE TINV: no type invariant of `tinv_census_projection::P` is certified
    //[d_for_each]~| NOTE withheld by the escape census: the crate uses third-party code (the crate graph links `tinv_tp_forge`; first use found: `d_for_each` calls the third-party `tp::Conjure::<I>::new`)
    //[d_any]~^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ NOTE TINV: no type invariant of `tinv_census_projection::P` is certified
    //[d_any]~| NOTE withheld by the escape census: the crate uses third-party code (the crate graph links `tinv_tp_forge`; first use found: `d_any` calls the third-party `tp::Conjure::<I>::new`)
    //[d_map_count]~^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ NOTE TINV: no type invariant of `tinv_census_projection::P` is certified
    //[d_map_count]~| NOTE withheld by the escape census: the crate uses third-party code (the crate graph links `tinv_tp_forge`; first use found: `d_map_count` calls the third-party `tp::Conjure::<I>::new`)
    //[d_each_items]~^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ NOTE TINV: no type invariant of `tinv_census_projection::P` is certified
    //[d_each_items]~| NOTE withheld by the escape census: the crate uses third-party code (the crate graph links `tinv_tp_forge`; first use found: `d_each_items` calls the third-party `tp::each`)
    //[d_each_forge]~^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ NOTE TINV: no type invariant of `tinv_census_projection::P` is certified
    //[d_each_forge]~| NOTE withheld by the escape census: the crate uses third-party code (the crate graph links `tinv_tp_forge`; first use found: `d_each_forge` calls the third-party `tp::each_forge`)
    //[alias_poke]~^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ NOTE TINV: no type invariant of `tinv_census_projection::P` is certified
    //[alias_poke]~| NOTE withheld by the escape census: the crate uses third-party code (the crate graph links `tinv_tp_forge`; first use found: `alias_poke` calls the third-party `tp::Alias::<T>::from_box`)
    //[w_first]~^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ NOTE TINV: no type invariant of `tinv_census_projection::P` is certified
    //[w_first]~| NOTE withheld by the escape census: the crate uses third-party code (the crate graph links `tinv_tp_forge`; first use found: `w_first` calls the third-party `tp::Conjure::<I>::new`)
    //[w_sink]~^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ NOTE TINV: no type invariant of `tinv_census_projection::P` is certified
    //[w_sink]~| NOTE withheld by the escape census: the crate uses third-party code
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

#[cfg(not(control))]
fn mk(_: u8) -> P<'static> {
    P { b: b"", i: 0 }
}

#[cfg(not(control))]
type Items = core::iter::Map<core::ops::Range<u8>, fn(u8) -> P<'static>>;

#[cfg(forge)]
pub fn forged() -> bool {
    let mut p: P<'static> = tp::forge::<Items>();
    p.literal(b"x")
}

#[cfg(corrupt)]
pub fn corrupted() -> bool {
    let mut p = mk(0);
    tp::corrupt::<Items>(&mut p);
    p.literal(b"x")
}

#[cfg(any(peek_dyn, peek_generic, peek_corrupt, a_foreign, c_hold_peek))]
fn peekable() -> core::iter::Peekable<Items> {
    let mut it = (0u8..3).map(mk as fn(u8) -> P<'static>).peekable();
    it.peek();
    it
}

#[cfg(peek_dyn)]
pub fn erased() -> String {
    let mut it = peekable();
    let d: &mut dyn core::fmt::Debug = &mut it;
    format!("{d:?}")
}

#[cfg(peek_generic)]
fn g<T: core::fmt::Debug>(t: &mut T) -> String {
    format!("{t:?}")
}

#[cfg(peek_generic)]
pub fn generic() -> String {
    let mut it = peekable();
    g(&mut it)
}

#[cfg(peek_corrupt)]
pub fn corrupted_peek() -> bool {
    let mut it = peekable();
    tp::corrupt_any(&mut it);
    it.next().is_some_and(|mut p| p.literal(b"x"))
}

#[cfg(any(wconst, a_local, e_public))]
trait Tr {
    type Out;
}

#[cfg(any(wconst, a_local, e_public))]
struct X;

#[cfg(any(wconst, a_local, e_public))]
impl Tr for X {
    type Out = P<'static>;
}

#[cfg(any(wconst, a_local))]
struct W<T: Tr> {
    f: T::Out,
}

#[cfg(wconst)]
const C: W<X> = W { f: P { b: b"", i: 5 } };

#[cfg(wconst)]
fn take_w(w: W<X>) -> Option<u8> {
    w.f.peek()
}

#[cfg(wconst)]
pub fn go() -> Option<u8> {
    take_w(C)
}

#[cfg(a_local)]
fn scrub<T: Tr>(w: &mut W<T>) {
    tp::corrupt_any(w)
}

#[cfg(a_local)]
pub fn a_local() -> bool {
    let mut w = W::<X> { f: P { b: b"", i: 0 } };
    scrub(&mut w);
    w.f.literal(b"x")
}

#[cfg(a_foreign)]
fn scrub_peek<I: Iterator>(pk: &mut core::iter::Peekable<I>) {
    tp::corrupt_any(pk)
}

#[cfg(a_foreign)]
pub fn a_foreign() -> bool {
    let mut it = peekable();
    scrub_peek(&mut it);
    it.next().is_some_and(|mut p| p.literal(b"x"))
}

#[cfg(b_transitive)]
fn outer<I: Iterator<Item = P<'static>>>(it: I) -> bool {
    inner(it)
}

#[cfg(b_transitive)]
fn inner<I: Iterator>(mut it: I) -> bool
where
    I::Item: UseIt,
{
    while let Some(mut x) = it.next() {
        tp::corrupt::<I>(&mut x);
        x.use_it();
    }
    false
}

#[cfg(b_transitive)]
trait UseIt {
    fn use_it(&mut self) -> bool;
}

#[cfg(b_transitive)]
impl UseIt for P<'static> {
    fn use_it(&mut self) -> bool {
        self.literal(b"x")
    }
}

#[cfg(b_transitive)]
pub fn b_transitive() -> bool {
    outer((0u8..3).map(mk as fn(u8) -> P<'static>))
}

#[cfg(c_hold_peek)]
pub fn c_hold_peek() -> bool {
    let mut h = tp::Hold(peekable());
    tp::corrupt_any(&mut h);
    h.0.next().is_some_and(|mut p| p.literal(b"x"))
}

#[cfg(c_hold_inner)]
pub fn c_hold_inner() -> bool {
    let mut h: tp::HoldInner<Items> = tp::HoldInner(tp::Inner(Some(mk(0))));
    tp::corrupt_any(&mut h);
    (h.0).0.is_some_and(|mut p| p.literal(b"x"))
}

#[cfg(d_conjure)]
pub fn d_conjure() -> bool {
    let v: Vec<P<'static>> = tp::Conjure::<Items>::new().take(1).collect();
    v.into_iter().next().is_some_and(|mut p| p.literal(b"x"))
}

#[cfg(e_public)]
pub struct Wrap<T: Tr> {
    f: T::Out,
}

#[cfg(e_public)]
pub fn wrap() -> Wrap<X> {
    Wrap { f: P { b: b"", i: 0 } }
}

#[cfg(d_for_each)]
pub fn d_for_each() {
    tp::Conjure::<Items>::new().take(1).for_each(|mut p: P<'static>| assert!(p.literal(b"x")));
}

#[cfg(d_any)]
pub fn d_any() -> bool {
    tp::Conjure::<Items>::new().take(1).any(|mut p: P<'static>| p.literal(b"x"))
}

#[cfg(d_map_count)]
pub fn d_map_count() -> usize {
    tp::Conjure::<Items>::new().take(1).map(|mut p: P<'static>| p.literal(b"x")).count()
}

#[cfg(d_each_items)]
pub fn d_each_items() {
    tp::each((0u8..3).map(mk as fn(u8) -> P<'static>), |mut p: P<'static>| {
        p.literal(b"x");
    });
}

#[cfg(d_each_forge)]
pub fn d_each_forge() {
    tp::each_forge::<P<'static>, _>(|mut p| {
        p.literal(b"x");
    });
}

#[cfg(alias_poke)]
pub fn alias_poke() -> Option<u8> {
    let a = tp::Alias::from_box(Box::new(mk(0)));
    a.poke();
    a.get().peek()
}

#[cfg(w_first)]
fn first<I: Iterator<Item = P<'static>>>(mut it: I) -> P<'static> {
    it.next().unwrap()
}

#[cfg(w_first)]
pub fn w_first() -> bool {
    let mut p = first(tp::Conjure::<Items>::new());
    p.literal(b"x")
}

#[cfg(w_sink)]
struct L;

#[cfg(w_sink)]
impl tp::Sink for L {
    type In = P<'static>;
    fn take(&mut self, mut x: P<'static>) {
        x.literal(b"x");
    }
}

#[cfg(w_sink)]
pub fn w_sink() {
    tp::Sink::pump(&mut L);
}
