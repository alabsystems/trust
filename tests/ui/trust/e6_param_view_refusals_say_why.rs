//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ dont-require-annotations: ERROR
//! ref-self I1, amended at I2 — what the borrow-erased E6 PARAMETER VIEW still
//! REFUSES, and whether the refusal says why (v7/D3: the rule, why this program
//! broke it, and the options).
//!
//! **Every clause here is CITED, deliberately.** The D-REF notes are appended
//! by `trust_e6_self_admission_shortfall`, which only the post-walk citation
//! sweep calls, and the sweep skips an uncited contract. An earlier draft of
//! this fixture used uncited clauses and could not have printed a single note
//! it annotates.
//!
//! **What must not be blessed away is the set of functions that stay red.**
//! Every one of them is a shape that would be UNSOUND to admit under owner
//! ruling R1, or a scope cut that has its own undecided ruling; a bless that
//! turns one green is a soundness regression, not diagnostic churn. The e6
//! fragment probes `f70`–`f85`, plus `f89`–`f92` added with increment I2, pin
//! the same set by VERDICT (`clause-outside-fragment`), which is the
//! machine-checkable half. This file pins the half a machine cannot: that an
//! author is told what to do instead.
//!
//! **Increment I2 (2026-09-19) moved two functions OUT of this file**, not by
//! blessing them but by deleting the rule that refused them: `Cursor::row_of`
//! and `Ratio::num_of` now discharge and live in
//! `e6_param_view_skips_unsupported_fields.rs`, and probes `f80`/`f86` flipped
//! with them. **That deletion is why three of the refusals below are now held
//! by `Ty::is_freeze` and the K2 structural walk ALONE** — read `n_of`,
//! `raw_of` and `tag_of` with that in mind.
//!
//! One per refusal, in the order `trust_frozen_shared_param_scan` decides them:
//!
//!   * `x_mut`     — C1: a `&mut` pointee may differ at exit. R1 is about a
//!                   SHARED borrow and says nothing here.
//!   * `first`     — C2, the UNSIZED arm. `[u64]` IS `Freeze`; it is merely
//!                   unsized. The three C2 conditions carry three different
//!                   notes because one message for all three stated something
//!                   FALSE about two of them.
//!   * `cell_peek` — C2, the `Freeze` arm. In increment I1 this was the ONLY
//!                   shape where `Freeze` was the sole net; since I2 it is one
//!                   of four (`n_of`, `raw_of`, `tag_of`).
//!                   `UnsafeCell<u32>`'s single declared field is a `u32`, it is
//!                   a struct, sized and fully instantiated — so every later
//!                   condition (K2 aside) would admit it, and the carrier rule
//!                   would give it a row. What refuses it is `is_freeze`, which
//!                   is decided first. Its positive twin `Boxed { value: u32 }`
//!                   in `e6_param_view_ref_self_is_not_certified.rs` has the
//!                   same declared field shape and IS admitted; the pair is the
//!                   differential that RUNS, since no in-tree switch can stub
//!                   the trait solver's answer. The stub-both control WAS RUN
//!                   at I2 (2026-09-19, both directions on a stage-1 build):
//!                   with `is_freeze` and K2 stubbed, `f84`, `f71` and `f91`
//!                   all go `discharged` and `f85` does not move; restoring
//!                   both returns all three to red. Its runnable half is
//!                   `trust_types::e6_param_view::tests::
//!                   m_freeze_is_the_only_net_left_for_a_cell_sibling`.
//!   * `n_of`      — a `Cell<u32>` SIBLING field. **Since increment I2 this is
//!                   the one shape where `Freeze` is the ONLY net, and it is
//!                   the increment's whole cost.** Under I1 it was refused
//!                   twice: by C2 (`Ty::is_freeze`, MEASURED to name
//!                   `hits.value`) and again by the all-or-nothing vocabulary
//!                   rule D-REF-8, since `Cell<u32>` is a `ty::Adt` outside the
//!                   scalar vocabulary. I2 skips unsupported fields, so the
//!                   second net is gone BY CONSTRUCTION — a `Cell` sibling is
//!                   skipped exactly like a `Vec` one — and C2 with K2 behind
//!                   it is all that stands between this program and a defining
//!                   equation over bytes another alias may legally mutate
//!                   during the call. Neither is kernel-checked; `docs/TCB.md`
//!                   says so. A bless that turns this green is not diagnostic
//!                   churn, it is the soundness regression the row names.
//!   * `raw_of`    — the same, with `UnsafeCell<u32>` itself as the sibling
//!                   rather than a `Cell` wrapper over one. `f84`'s shape is
//!                   the WHOLE pointee being an `UnsafeCell`; this is the
//!                   sibling form, which is what a real struct looks like, and
//!                   it is a separate case because K2 reaches the cell at a
//!                   different depth.
//!   * `tag_of`    — C2's GENERIC arm, which I2 also leaves as the sole net for
//!                   its shape. `tag: u32` is a perfectly good scalar field, so
//!                   with the vocabulary rule gone the only reason
//!                   `&Tagged<T>` is refused is that `Freeze` for an
//!                   uninstantiated `T` is not decidable here. Its positive
//!                   control is probe `f88`: `&Wrapper<u32>` in a non-generic
//!                   function IS admitted, so "a generic" is not the refusal,
//!                   an undecided one is.
//!   * `pos_as`    — a body that READS a skipped field. `pos: usize` is outside
//!                   the view vocabulary on purpose, so the view has no value
//!                   for it and the `[Deref, Field(k)]` rule refuses `k = 0`
//!                   outright. Builder-side, so the E9 error carries no D-REF
//!                   headline — what it does carry is I2's own note naming the
//!                   skipped field, which is the only place the author is told
//!                   `pos` is not available.
//!   * `max_named_pos` — a CLAUSE that names a skipped field. The compiler
//!                   emits one clause binder per LISTED row and `self.pos` is
//!                   not one of them, so the elaborator has no TYPE for it and
//!                   the clause leaves the exact statement fragment. MEASURED
//!                   WORDING: "missing supported type for clause variable
//!                   `self.pos`" (`trust-spec-elab/src/lib.rs:1889`), not an
//!                   "unbound variable" headline — the annotation below pins
//!                   what is emitted, not what was predicted. Never a silently
//!                   defaulted zero, which is the failure that would matter.
//!   * `zero_of`   — the ZERO-ROW branch: EVERY declared field of `Blob` is
//!                   outside the carrier vocabulary, so the parameter
//!                   contributes no binder and the note lists all of them.
//!                   `pos_as`'s note is the OTHER branch of the same rewrite
//!                   (some rows survived); before this function only one of the
//!                   two was exercised.
//!   * `x_pat`     — the parameter pattern binds no single name to prefix the
//!                   clause rows with.
//!   * `outer`     — V2: the borrow is passed to a sibling instead of read.
//!                   Refused by the view BUILDER, not by the signature scan, so
//!                   it carries no D-REF note — `TRUST_E6_DEBUG=1` prints the
//!                   builder's reason.
//!   * `x_ptr`     — V3: the return is a reference, so there is no scalar
//!                   `result` row and no `*result` row is invented for one.
//!                   Also builder-side, also no D-REF note.
//!
//! Each refusal surfaces as the existing E9 citation error with the D-REF note
//! appended. The annotations below pin the NOTE text, which is the part that
//! tells the author what to do.

#![allow(unused_variables)]

clean {
    def id32 (x : UInt32) : UInt32 := x
    def id64 (x : UInt64) : UInt64 := x
    theorem id32_one : forall (a : UInt32), id32 a = id32 a := fun a => rfl
    theorem id32_two : forall (a b : UInt32), id32 a = id32 a := fun a b => rfl
    theorem id64_one : forall (a : UInt64), id64 a = id64 a := fun a => rfl
}

use std::cell::{Cell, UnsafeCell};

pub struct Point {
    pub x: u32,
    pub y: u32,
}

pub struct Counter {
    pub n: u32,
    pub hits: Cell<u32>,
}

pub struct Slot {
    pub n: u32,
    pub raw: UnsafeCell<u32>,
}

pub struct Tagged<T> {
    pub tag: u32,
    pub payload: T,
}

// The owner's real parser state, cut down to the two fields the twins need.
// TRIMMED ON PURPOSE to exactly one skipped field: the I2 note joins every
// skipped field with `, `, so an annotation greping a single field name only
// matches when the struct has one. `pos: usize` is SKIPPED (the view
// vocabulary is `bool`, `u8`..`u128`, `i8`..`i128`; the `usize`/`isize` PAIR is
// deliberately absent because `clean_island::ty_to_domain` has no arm for
// `PtrSizedInt { signed: true }` — measured — so admitting `isize` would split
// the two flattenings' arities), and `max` gets a row. Under I1 neither did,
// because the pointee was refused whole.
pub struct Parser {
    pub pos: usize,
    pub max: u32,
}

// EVERY declared field outside the vocabulary — the ZERO-ROW branch of the
// note I2 rewrote, and the half that would otherwise go untested. `Blob` is not
// refused for interior mutability (it is `Freeze`), nor for shape (it is a
// sized struct): the scan walks its fields, skips both, finds `rows.is_empty()`
// and refuses the parameter with the list of what it skipped. The message is a
// different branch from `pos_as`'s, which is emitted when SOME row survived.
pub struct Blob {
    pub pos: usize,
    pub buf: Vec<u8>,
}

// C1 — a mutable borrow.
impl Point {
    pub fn x_mut(&mut self) -> u32
        ensures result == id32(self.x) by id32_one
        //~^ NOTE rule: a borrowed parameter is E6-admitted only as a read-only shared borrow
    {
        self.x
    }
}

// C2, UNSIZED — and NOT an interior-mutability refusal, which is what the
// single merged message used to claim about this exact program.
pub fn first(xs: &[u64]) -> u64
    ensures result == id64(0) by id64_one
    //~^ ERROR rule: a shared borrow is admitted only for a SIZED pointee
{
    xs.len() as u64
}

// C2, FREEZE — the whole pointee. In I1 this was the ONLY shape `Freeze` held
// alone; since I2 it is one of four (`n_of`, `raw_of`, `tag_of` join it).
pub fn cell_peek(c: &UnsafeCell<u32>) -> u32
    ensures result == id32(0) by id32_one
    //~^ ERROR rule: entry == exit holds for a shared borrow only when the pointee is `Freeze`
{
    0
}

// C2, FREEZE — through a sibling field, and SINCE I2 THE SOLE NET FOR IT.
// The vocabulary rule that used to refuse `Counter` a second time is gone: a
// `Cell<u32>` sibling is now skipped exactly like a `Vec<u8>` one, and only
// `Ty::is_freeze` (with K2 behind it) keeps this red. The measured note names
// the field path, which `is_freeze` alone cannot — it answers a bool.
impl Counter {
    pub fn n_of(&self) -> u32
        ensures result == id32(self.n) by id32_one
        //~^ NOTE rule: entry == exit holds for a shared borrow only when the pointee is `Freeze`
    {
        self.n
    }
}

// C2, FREEZE — an `UnsafeCell` SIBLING, which is `f84`'s cell one indirection
// further out. `Slot`'s declared fields are `u32` and `UnsafeCell<u32>`; the
// first is in the vocabulary, the second is skipped since I2, and what refuses
// the pointee is that `Slot` is not `Freeze`. Kept separate from `n_of` because
// K2 reaches the cell at a different depth (`raw` itself, not `hits.value`).
impl Slot {
    pub fn raw_of(&self) -> u32
        ensures result == id32(self.n) by id32_one
        //~^ NOTE rule: entry == exit holds for a shared borrow only when the pointee is `Freeze`
    {
        self.n
    }
}

// C2, GENERIC — and since I2 the sole net for THIS shape too. `tag: u32` is a
// scalar field in the vocabulary, so with the all-or-nothing rule gone the only
// reason `&Tagged<T>` has no row is that `Freeze` for an uninstantiated `T` is
// undecidable here. Probe `f88` is the positive control: `&Wrapper<u32>` in a
// non-generic function IS admitted.
impl<T> Tagged<T> {
    pub fn tag_of(&self) -> u32
        ensures result == id32(self.tag) by id32_one
        //~^ NOTE rule: a shared borrow is admitted only for a pointee whose interior mutability
    {
        self.tag
    }
}

// A BODY THAT READS A SKIPPED FIELD. `pos: usize` is outside the view
// vocabulary, so the view has no parameter for it and `read_place` admits only
// `[Deref, Field(k)]` for a LISTED `k` — the whole view refuses, and `max`'s
// row buys nothing here. This is the shape the skip rule has to get right: the
// alternative to refusing would be minting an equation over a value the body
// does not compute from.
//
// Builder-side, so there is no D-REF headline. What the author does get is I2's
// own note, which is the only place `pos` is named at all.
impl Parser {
    pub fn pos_as(&self) -> u32
        ensures result == id32(self.max) by id32_one
        //~^ ERROR field(s) `pos: usize` are outside it and were SKIPPED
    {
        self.pos as u32
    }

    // A CLAUSE THAT NAMES A SKIPPED FIELD. `self.pos` is not a binder — the
    // compiler emits one row per LISTED field — so the elaborator's binder-type
    // table has no entry for it and the clause falls outside the exact
    // statement fragment. MEASURED WORDING, and it is not the one predicted:
    // the refusal is `crates/trust-spec-elab/src/lib.rs:1889`'s "missing
    // supported type for clause variable `self.pos`", not an "unbound variable"
    // headline. Same fail-closed outcome, named at the type table rather than
    // at scope resolution — the same message the design note records for the
    // tuple-struct case. The failure that would matter is the silent one: a
    // skipped field defaulting to zero, or binding to a same-named item, would
    // certify a false contract. It does neither.
    pub fn max_named_pos(&self) -> u32
        ensures result == id32(self.pos) by id32_one
        //~^ ERROR missing supported type for clause variable `self.pos`
    {
        self.max
    }
}

// The ZERO-ROW refusal. No field of `Blob` is in the carrier vocabulary, so the
// parameter contributes no clause binder at all and the note names every field
// it skipped — which is the only way the author learns that `Blob` as such is
// the problem, rather than this particular clause.
//
// MEASURED LEVEL, and it is NOT the same as `pos_as`'s even though both
// diagnostics come from the same `note!` list: this one arrives as a NOTE and
// the partial-admission one as an ERROR. The level is a property of the emit
// site the shortfall is reported through, not of the note, so both annotations
// here are measured rather than predicted — an annotation with the wrong level
// fails the file, and `dont-require-annotations` does not rescue it.
impl Blob {
    pub fn zero_of(&self) -> u32
        ensures result == id32(self.pos) by id32_one
        //~^ NOTE declares no field in it (every declared field is outside it
    {
        0
    }
}

// The pattern binds no single name.
pub fn x_pat(&Point { x, .. }: &Point) -> u32
    ensures result == id32(x) by id32_one
    //~^ NOTE rule: a borrowed parameter needs ONE name for its clause rows
{
    x
}

// V2 — the borrow is forwarded to a sibling rather than read. Builder-side.
impl Point {
    fn inner(&self) -> u32 {
        self.x
    }

    pub fn outer(&self) -> u32
        ensures result == id32(self.x) by id32_one
    {
        self.inner()
    }
}

// V3 — the return is a reference. Builder-side.
impl Point {
    pub fn x_ptr(&self) -> &u32
        ensures *result == id32(self.x) by id32_one
    {
        &self.x
    }
}

pub struct Named {
    pub a: u32,
    pub b: u32,
}

impl Named {
    // The view import of THIS function exists and discharges its own clause.
    pub fn a_of(&self) -> u32
        ensures result == id32(self.a) by id32_two
    {
        self.a
    }
}

// `Admission::self_result_only`, at the COMPILER level rather than in a unit
// test. `Named::a_of`'s view import is in the session facet table (the session
// mint puts it there for the citation sweep), its kernel constant is in the
// session environment, and this clause names it as a call — so the ONLY thing
// refusing it is the mark. Without the mark it would elaborate at the FLATTENED
// arity `a_of(self.a, self.b)`, a signature no Rust caller can write, and rustc
// does not type-check clause text.
pub fn borrows_a_view(p: u32, q: u32) -> u32
    ensures result == Named::a_of(p, q) by id32_one
    //~^ ERROR borrow-erased PARAMETER VIEW
{
    p
}

fn main() {}
