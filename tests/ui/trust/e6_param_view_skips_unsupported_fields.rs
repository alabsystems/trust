//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! ref-self I2 — a frozen shared pointee no longer has to be ALL scalar.
//!
//! **What changed and why it is the payoff.** I1 admitted `&self` through the
//! borrow-erased E6 parameter view, but only when EVERY declared field of the
//! pointee was in the scalar carrier vocabulary (`bool`, `u8`..`u128`,
//! `i8`..`i128`). That is not the shape of a real `Self`:
//! `struct Parser { pos: usize, max: u32, buf: Vec<u8>, name: String }` has one
//! `u32` and three fields outside the vocabulary, and under I1 the `u32` was
//! unreachable because of its siblings. I2 (disposition R4, implementer-proposed) SKIPS the
//! unsupported fields and admits a view over the scalar ones.
//!
//! **Why skipping on one side is sound**, which is the question I1's
//! all-or-nothing rule D-REF-8 was the answer to. D-REF-8 assumed two
//! independent flattenings that had to agree field by field. There is one:
//!
//!   * `trust_frozen_shared_param_scan` is the ONLY filter. The clause-side row
//!     table reads its rows; the view does not filter at all.
//!   * `trust_types::e6_param_view` VERIFIES every listed row against the
//!     extracted IR — declared index, field name and carrier — and refuses the
//!     WHOLE view on any disagreement. A drift costs the capability; it can
//!     never mint at a wrong field. A field the table did NOT list is never
//!     inspected, so however the extractor lowered it (opaquely, compacted,
//!     by name) is irrelevant.
//!   * the mint's own all-or-nothing flattening (`clean_island::param_flat_rows`)
//!     never sees a borrow here: it runs on the VIEW's body, whose parameters
//!     are already by-value scalars.
//!   * field names are unique within a struct and rows keep DECLARED order, so
//!     a same-length reorder cannot pass the per-row name check. THAT CHECK IS
//!     THE ONLY NET here, and the count matters: `Admission::param_names`'
//!     exact-list comparison in `elaborate_ensures` compares two lists that
//!     both descend from the same signature table (the clause side through
//!     `trust_fn_param_type_names`, the minted side through the view's
//!     `param_names`, built from the table's rows rather than from the
//!     extracted field names), so on this lane it is tautological. It is real
//!     defence on the BY-VALUE lane, where `param_flat_rows` re-derives the
//!     list from the extracted IR.
//!
//! **What this makes load-bearing, stated here because it is a real cost.**
//! `Cell<u32>` and `AtomicU32` are ADTs outside the scalar vocabulary, so until
//! now the carrier rule refused a pointee carrying one as a SIBLING — a second
//! net behind `Ty::is_freeze` (C2) and the compiler's structural `UnsafeCell`
//! walk (K2). From I2 on that net is gone by construction: a `Cell` sibling is
//! skipped like a `Vec` one, and **C2 and K2 are the only thing refusing it.**
//! Neither is kernel-checked. `docs/TCB.md`'s `EnsuresCitationViewDischarge`
//! row says so; the close negatives are in
//! `e6_param_view_refusals_say_why.rs` (`n_of`, `raw_of`, `tag_of`), the
//! `Freeze` differential is probe `f84` against `f85`, and the mutation control
//! WAS RUN (2026-09-19, both directions on a stage-1 build): with `is_freeze`
//! and K2 both stubbed out, `f71`, `f84` and `f91` all go `discharged` while
//! `f85` is unchanged, and restoring both guards returns all three to red.
//!
//! **The grade is unchanged and is not softened by any of this.** Every row
//! below is `Trusted`/`Constructive`, never `Certified`; it carries the marker
//! `frozen-shared-erased` on its spec-clean goal row, is absent from
//! `of which N kernel-certified`, ships no kernel proof evidence, and is
//! WITHHELD by the authenticated `targo trust` lane.
//! `e6_param_view_ref_self_is_not_certified.rs` is where that discipline is
//! pinned; this file is about which SHAPES reach it.
//!
//! **Why `check-pass` is not vacuous.** `-Ztrust-verify=on` is strict and a
//! clause calling a Clean island definition is outside every solver lane's
//! vocabulary, so the only thing that can close these rows is the kernel
//! discharge. Under I1 every function in this file failed to compile under this
//! flag.

clean {
    def id32 (x : UInt32) : UInt32 := x
    -- ORDER-SENSITIVE on purpose: `pickfst a b` and `pickfst b a` are different
    -- values, so a clause citing it is a statement about WHICH binder is which.
    def pickfst (a b : UInt32) : UInt32 := a
    theorem id32_one : forall (a : UInt32), id32 a = id32 a := fun a => rfl
    theorem id32_two : forall (a b : UInt32), id32 b = id32 b := fun a b => rfl
}

// THE FLAGSHIP, and the shape the whole increment exists for: an owner's real
// parser state. `pos: usize` is outside the view vocabulary deliberately, and
// it is the PAIR `usize`/`isize` that is excluded rather than `usize` alone:
// MEASURED, `clean_island::ty_to_domain` maps `PtrSizedInt { signed: false }`
// to `Domain::Machine(U64)` and has no arm for `signed: true`, so admitting
// `isize` would put the two flattenings at different arities — `e6_view_scalar`
// therefore takes both or neither, and the live `usize` lane owns extending it.
// `buf` and `name` are not scalars at all, and `max` is the one field
// a contract can name. Under I1 this struct admitted NOTHING.
pub struct Parser {
    pub pos: usize,
    pub max: u32,
    pub buf: Vec<u8>,
    pub name: String,
}

impl Parser {
    pub fn max_of(&self) -> u32
        ensures result == id32(self.max)
    {
        self.max
    }
}

// The design's worked example B. Two listed fields and one skipped, so this is
// where a wrong index would show: the view's parameters are `self.row` and
// `self.limit` in DECLARED order, and the body's `Field(0)` read must become
// view parameter 0. A table that mapped it to `self.limit` would mint
// `fun p0 p1 => p1` — well-typed, false, and invisible to the kernel. The
// field-name re-check against the extracted IR is what refuses that; the
// trust-types unit test
// `a_skipped_middle_field_keeps_the_declared_index_of_its_siblings` is its
// direct measurement.
pub struct Cursor {
    pub row: u32,
    pub limit: u32,
    pub cells: Vec<u8>,
}

impl Cursor {
    pub fn row_of(&self) -> u32
        ensures result == id32(self.row)
    {
        self.row
    }

    // The SECOND listed field, cited. Probe `f80` held this shape red for
    // D-REF-8; the citation lane is the one that grades, so it is exercised
    // here rather than only the uncited defeq lane.
    // `id32_two` is shaped for the VIEW's arity: `Cursor` contributes exactly
    // two binders (`cells` is skipped), so the goal is
    // `forall (self.row) (self.limit), <import limit_of> self.row self.limit
    // = id32 self.limit` — the same shape `e6_param_view_ref_self_is_not_certified.rs`
    // proves for the all-scalar `Point`. That the SKIPPED field contributes no
    // binder is therefore load-bearing for this citation: a three-binder goal
    // would not be inhabited by this theorem.
    pub fn limit_of(&self) -> u32
        ensures result == id32(self.limit) by id32_two
        //~^ NOTE kernel-discharges this postcondition statement
    {
        self.limit
    }

    // THE WIDENING I2 DOES THAT IS NOT A CAPABILITY, recorded because it is a
    // grade change and grades are not allowed to move silently.
    // `trust_e6_view_marker` is keyed on the signature TABLE, not on whether an
    // import minted — every binder a frozen shared parameter contributes names
    // a pointee value at entry, so the R1 assumption is in the goal whether or
    // not `result` is. I2 gives a table entry to structs that had none, so a
    // `&self` method over a MIXED struct whose cited clause mentions no field
    // of `self` moves from `Certified` to `Trusted`. That is the fail-safe
    // direction and it is deliberate; this function is the in-tree witness.
    // Its all-scalar twin is `Point::gap` in
    // `e6_param_view_ref_self_is_not_certified.rs`, which also pins the other
    // half: the added rows must NOT reach the goal's binder closure, because
    // `discharge_used_bindings` narrows it to the clause's own free variables.
    pub fn gap(&self, n: u32) -> u32
        ensures id32(n) == id32(n) by id32_one
        //~^ NOTE kernel-discharges this postcondition statement
    {
        n
    }
}

// The CLEANEST D-REF-8 shape, probe `f86`: every earlier condition admits
// `Ratio` — `f64` is `Freeze`, sized, non-generic and classified by K2 — and
// only the carrier rule stood between it and a row.
pub struct Ratio {
    pub num: u32,
    pub scale: f64,
}

impl Ratio {
    pub fn num_of(&self) -> u32
        ensures result == id32(self.num)
    {
        self.num
    }
}

// A SKIPPED FIELD IN THE MIDDLE. `head` and `tail` keep their DECLARED indices
// 0 and 2 across the skip, so the body's `Field(2)` read has to become view
// parameter 1 — an off-by-one in the index mapping would mint an equation about
// `head` for a function that returns `tail`, and the kernel would accept it
// because it is well-typed. A leading or trailing skip cannot exhibit this.
pub struct Gap {
    pub head: u32,
    pub body: f64,
    pub tail: u32,
}

impl Gap {
    pub fn head_of(&self) -> u32
        ensures result == id32(self.head)
    {
        self.head
    }

    pub fn tail_of(&self) -> u32
        ensures result == id32(self.tail)
    {
        self.tail
    }

    // THE ORDER-SENSITIVE ROW, and the reason `pickfst` is in the island. Every
    // other clause in this file names ONE binder, so it pins which field a read
    // became but not the ORDER the import is applied in. This one applies the
    // island definition to BOTH binders, in the order the table recorded them,
    // and `pickfst a b` is not `pickfst b a`.
    //
    // The goal is `forall (self.head) (self.tail),
    // <import head_ordered> self.head self.tail = pickfst self.head self.tail`,
    // and the import is `fun p0 p1 => p0` because the body reads DECLARED field
    // 0 across a skipped middle field. Swap which view parameter that read
    // becomes and the import is `fun p0 p1 => p1`: the two sides are then
    // `self.tail` and `self.head`, well-typed and NOT defeq, so the row goes red
    // rather than certifying a false equation. That is the direction this pin
    // exists to hold. Its mechanism-level twins are
    // `m_the_field_index_is_load_bearing_for_the_minted_equation` and
    // `m_a_swapped_row_list_across_a_skipped_field_is_refused` in
    // `trust_types::e6_param_view`. Those two ARE the net; `elaborate_ensures`'
    // list comparison is not a second one here, because both of its lists come
    // from the same signature table (see the module header).
    pub fn head_ordered(&self) -> u32
        ensures result == pickfst(self.head, self.tail)
    {
        self.head
    }
}

// THE FREE FUNCTION form, so the increment is not silently `self`-only: a named
// `&T` parameter prefixes its rows with its own name.
pub fn width_of(c: &Cursor) -> u32
    ensures result == id32(c.limit)
{
    c.limit
}

// THE CONTROL. No borrow: this discharges exactly as it did before I1, at
// `Certified`, with a `null` view on its spec-clean row.
//
// NOTE WHAT IT IS NOT. It is an ALL-SCALAR by-value struct, because the
// by-value lane's mint (`clean_island::param_flat_rows`) really IS
// all-or-nothing and I2 did not touch it: `fn num_by_value(r: Ratio)` would
// still be refused, and probe `f40` pins that it stays refused. I2 reverses the
// rule for FROZEN SHARED POINTEES only, where the mint runs on the view's own
// all-scalar body and that flattening never applies.
pub struct Point {
    pub x: u32,
    pub y: u32,
}

pub fn x_by_value(p: Point) -> u32
    ensures result == id32(p.x)
{
    p.x
}

fn main() {}
