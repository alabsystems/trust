//@ revisions: advisory strict certify
//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Ztrust-verify-output=human --crate-type=lib
//@[advisory] compile-flags: -Ztrust-policy=advisory
//@[strict] compile-flags: -Ztrust-policy=strict
//@[certify] compile-flags: -Ztrust-policy=certify
//@ dont-check-compiler-stderr
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE
//@[advisory] check-pass
//@[strict] check-fail
//@[certify] check-fail
//! OD-1 item 18 (shape 5): an argument of a RECURSIVE type. trust-vc-merge-contract's
//! `SortMeta` (`Seq { elem: Box<SortMeta> }`, ..) reaches itself through a `Box`, and
//! serde-derive hands `&self.sort` / `&self.args` (`Vec<TypedExpr>`, each holding a
//! `SortMeta`) to `serialize_field`, and a `PhantomData<VarDecl>` visitor to
//! `deserialize_struct`. The argument-shape walk answered every cycle `Opaque`, so each
//! such site was refused ("a `&` whose pointee holds a raw pointer or an opaque part").
//! A cycle reached with no reference or `UnsafeCell` between the two occurrences is
//! walked by `reach` in the same access context as its ancestor, whose walk already
//! collects every flag the subtree can raise; the back edge is now `Plain`. A cycle
//! across a reference or a cell is still `Opaque`.
//!
//! Admitted: `by_ref_sort`, `by_value_sort`, `by_ref_tree`. Discharge: `use_boom`
//! (`failed`), `use_fine` (`proved`, counted skipped).
//! Controls still refused: `mut_sort` (`&mut Sort`: a `Box` behind the `&mut`, which the
//! one-level havoc cannot cover), `cell_tree` (`&CellTree`: interior mutability reached
//! through shared access next to an owning pointer), `by_value_cell_list` (a by-value
//! `CellList` whose cycle runs across a `&`: the back edge stays `Opaque`; reading it
//! `Plain` would admit a callee that writes the caller's `Cell`).
//!
//! RE-PINNED 2026-10-15 (the merge of 2026-10-14): under `strict` the discharged
//! caller now carries its call's panic-freedom aggregate as one `runtime_checked` row,
//! which `strict` reports rather than fails (it keeps its runtime check), so that
//! caller is no longer a `strict` error; `certify` still refuses it, and every
//! discharge failure and refused control below is unchanged (measured on the merged
//! stage 1).
use std::cell::Cell;

pub enum Sort {
    Int,
    Seq(Box<Sort>),
    Map(Box<Sort>, Box<Sort>),
}

pub struct Tree {
    pub v: u32,
    pub kids: Vec<Tree>,
}

pub trait Ser {
    fn field<V: ?Sized>(&self, value: &V);
    fn take(&self, s: Sort);
}

pub fn by_ref_sort<S: Ser>(s: &S, sort: &Sort) {
    //[advisory]~^ WARN Trust verification advisory for `recursive_type_argument_admitted::by_ref_sort`: 1 instance hypothesis row(s)
    //[strict]~^^ WARN Trust verification advisory for `recursive_type_argument_admitted::by_ref_sort`: 1 instance hypothesis row(s)
    //[certify]~^^^ ERROR Trust certify verification failed for `recursive_type_argument_admitted::by_ref_sort`: 1 instance hypothesis row(s)
    s.field(sort)
}

pub fn by_value_sort<S: Ser>(s: &S, sort: Sort) {
    //[advisory]~^ WARN Trust verification advisory for `recursive_type_argument_admitted::by_value_sort`: 1 instance hypothesis row(s)
    //[strict]~^^ WARN Trust verification advisory for `recursive_type_argument_admitted::by_value_sort`: 1 instance hypothesis row(s)
    //[certify]~^^^ ERROR Trust certify verification failed for `recursive_type_argument_admitted::by_value_sort`: 1 instance hypothesis row(s)
    s.take(sort)
}

pub fn by_ref_tree<S: Ser>(s: &S, t: &Tree) {
    //[advisory]~^ WARN Trust verification advisory for `recursive_type_argument_admitted::by_ref_tree`: 1 instance hypothesis row(s)
    //[strict]~^^ WARN Trust verification advisory for `recursive_type_argument_admitted::by_ref_tree`: 1 instance hypothesis row(s)
    //[certify]~^^^ ERROR Trust certify verification failed for `recursive_type_argument_admitted::by_ref_tree`: 1 instance hypothesis row(s)
    s.field(t)
}

pub struct Fine;
pub struct Boom;

impl Ser for Fine {
    fn field<V: ?Sized>(&self, _value: &V) {}
    fn take(&self, _s: Sort) {}
    //[strict]~^ ERROR Trust strict verification failed for `<recursive_type_argument_admitted::Fine as recursive_type_argument_admitted::Ser>::take`: 1 obligation(s) were not fully verified
    //[certify]~^^ ERROR Trust Level 0 safety verification incomplete for `<recursive_type_argument_admitted::Fine as recursive_type_argument_admitted::Ser>::take`: 1 obligation(s) were not proved
    //[certify]~^^^ ERROR Trust strict verification failed for `<recursive_type_argument_admitted::Fine as recursive_type_argument_admitted::Ser>::take`: 1 obligation(s) were not fully verified
}

impl Ser for Boom {
    fn field<V: ?Sized>(&self, _value: &V) {
        //[strict]~^ ERROR Trust Level 0 safety verification incomplete for `<recursive_type_argument_admitted::Boom as recursive_type_argument_admitted::Ser>::field`: 2 obligation(s) were not proved
        //[strict]~^^ ERROR Trust strict verification failed for `<recursive_type_argument_admitted::Boom as recursive_type_argument_admitted::Ser>::field`: 2 obligation(s) were not fully verified
        //[certify]~^^^ ERROR Trust Level 0 safety verification incomplete for `<recursive_type_argument_admitted::Boom as recursive_type_argument_admitted::Ser>::field`: 2 obligation(s) were not proved
        //[certify]~^^^^ ERROR Trust strict verification failed for `<recursive_type_argument_admitted::Boom as recursive_type_argument_admitted::Ser>::field`: 2 obligation(s) were not fully verified
        panic!("boom")
    }
    fn take(&self, _s: Sort) {}
    //[strict]~^ ERROR Trust strict verification failed for `<recursive_type_argument_admitted::Boom as recursive_type_argument_admitted::Ser>::take`: 1 obligation(s) were not fully verified
    //[certify]~^^ ERROR Trust Level 0 safety verification incomplete for `<recursive_type_argument_admitted::Boom as recursive_type_argument_admitted::Ser>::take`: 1 obligation(s) were not proved
    //[certify]~^^^ ERROR Trust strict verification failed for `<recursive_type_argument_admitted::Boom as recursive_type_argument_admitted::Ser>::take`: 1 obligation(s) were not fully verified
}

pub fn use_fine(t: &Tree) {
    //~^ NOTE Trust verification: 1 proved, 0 failed, 0 unknown, 0 timed out, 0 runtime-checked, 1 assumed (instance discharge) out of 2 obligation(s)
    // Re-pinned 2026-11-07: the call's panic-freedom aggregate was `runtime_checked`
    // only because `&Fine` (the promoted borrow of a fieldless struct) had no
    // transport fact; it now carries a source reference VALUE fact
    // (`docs/DECISION_QUEUE.md`, 2026-11-07) and is proved, so `certify` accepts
    // `use_fine` exactly as it accepts `discharge_row_per_instance::use_good`
    // (measured A/B: `deep_owned_argument_admitted.rs`).
    by_ref_tree(&Fine, t)
}

pub fn use_boom(t: &Tree) {
    //[advisory]~^ WARN Trust instance discharge not established for `recursive_type_argument_admitted::use_boom`: 1 instance(s)
    //[strict]~^^ ERROR Trust instance discharge not established for `recursive_type_argument_admitted::use_boom`: 1 instance(s)
    //[strict]~^^^ ERROR Trust strict verification failed for `recursive_type_argument_admitted::use_boom`: 1 obligation(s) were not fully verified
    //[certify]~^^^^ ERROR Trust Level 0 safety verification incomplete for `recursive_type_argument_admitted::use_boom`: 1 obligation(s) were not proved
    //[certify]~^^^^^ ERROR Trust instance discharge not established for `recursive_type_argument_admitted::use_boom`: 1 instance(s)
    //[certify]~^^^^^^ ERROR Trust strict verification failed for `recursive_type_argument_admitted::use_boom`: 1 obligation(s) were not fully verified
    by_ref_tree(&Boom, t)
}

// Controls: still refused.

pub trait Edit {
    fn edit(&self, s: &mut Sort);
    fn peek(&self, t: &CellTree);
}

pub fn mut_sort<E: Edit>(e: &E, s: &mut Sort) {
    //[strict]~^ ERROR Trust Level 0 safety verification incomplete for `recursive_type_argument_admitted::mut_sort`: 1 obligation(s) were not proved
    //[strict]~^^ ERROR Trust strict verification failed for `recursive_type_argument_admitted::mut_sort`: 1 obligation(s) were not fully verified
    //[certify]~^^^ ERROR Trust Level 0 safety verification incomplete for `recursive_type_argument_admitted::mut_sort`: 1 obligation(s) were not proved
    //[certify]~^^^^ ERROR Trust strict verification failed for `recursive_type_argument_admitted::mut_sort`: 1 obligation(s) were not fully verified
    e.edit(s)
}

pub struct CellTree {
    pub v: Cell<u32>,
    pub kids: Vec<CellTree>,
}

pub fn cell_tree<E: Edit>(e: &E, t: &CellTree) {
    //[strict]~^ ERROR Trust Level 0 safety verification incomplete for `recursive_type_argument_admitted::cell_tree`: 1 obligation(s) were not proved
    //[strict]~^^ ERROR Trust strict verification failed for `recursive_type_argument_admitted::cell_tree`: 1 obligation(s) were not fully verified
    //[certify]~^^^ ERROR Trust Level 0 safety verification incomplete for `recursive_type_argument_admitted::cell_tree`: 1 obligation(s) were not proved
    //[certify]~^^^^ ERROR Trust strict verification failed for `recursive_type_argument_admitted::cell_tree`: 1 obligation(s) were not fully verified
    e.peek(t)
}

// Control (review fix): a cycle ACROSS a reference must stay `Opaque`. `CellList` holds a
// `Cell` and reaches itself through `&`, so a by-value `CellList` lends the callee a shared
// reference to interior mutability the caller still observes (`n.next.unwrap().c` is the
// caller's cell). Were the back edge read as `Plain` regardless of the barrier, the root
// `Cell` is reached in owned (non-shared) context, no flag refuses the argument, and the
// site would be admitted although the callee can write caller-visible state.
pub struct CellList<'a> {
    pub c: Cell<u32>,
    pub next: Option<&'a CellList<'a>>,
}

pub trait Sink {
    fn take_list(&self, n: CellList<'_>);
}

pub fn by_value_cell_list<S: Sink>(s: &S, n: CellList<'_>) {
    //[strict]~^ ERROR Trust Level 0 safety verification incomplete for `recursive_type_argument_admitted::by_value_cell_list`: 1 obligation(s) were not proved
    //[strict]~^^ ERROR Trust strict verification failed for `recursive_type_argument_admitted::by_value_cell_list`: 1 obligation(s) were not fully verified
    //[certify]~^^^ ERROR Trust Level 0 safety verification incomplete for `recursive_type_argument_admitted::by_value_cell_list`: 1 obligation(s) were not proved
    //[certify]~^^^^ ERROR Trust strict verification failed for `recursive_type_argument_admitted::by_value_cell_list`: 1 obligation(s) were not fully verified
    s.take_list(n)
}
