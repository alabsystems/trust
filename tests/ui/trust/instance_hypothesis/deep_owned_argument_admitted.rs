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
//! OD-1 item 18 follow-up (T3, 2026-10-10): an argument of DEEPLY NESTED OWNED type.
//! Preview3 (stage 1 `ed578e1a5`) kept ~13 serde rows `failed` as "the generic
//! receiver is a type parameter or projection and is not admitted" (`<__D>::
//! deserialize_struct`, `<<__S>::SerializeStruct>::serialize_field`,
//! `VariantAccess::struct_variant`). Every one of those receivers passes
//! `mentions_only_own_params`; the site was refused on its ARGUMENT, whose shape walk
//! reached `SHAPE_DEPTH_CAP` = 16 inside owned nesting (each `Vec`/`String` layer is
//! `Vec -> RawVec -> PhantomData<T> -> T`): tla-cert's `&Vec<CertificateStep>`, the
//! by-value `__Visitor { marker: PhantomData<Certificate> }`. The cap is now 64; the
//! node budget (4096) still bounds the walk's cost, and anything deeper or larger is
//! still `Opaque` (refused).
//!
//! Admitted (each was refused on the pre-fix compiler): `by_ref_deep` (a `&` to ~27
//! levels of `Vec`/`String` records), `by_value_visitor` (serde's by-value
//! `PhantomData` visitor), `projection_receiver` (the `<<S as Serializer>::
//! SerializeStruct as SerializeStruct>::serialize_field` shape). Discharge: `use_boom`
//! (`failed`), `use_fine` (counted skipped).
//! Controls still refused — the walk now SEES these leaves instead of stopping short:
//! `deep_raw` (a raw pointer at the same depth), `deep_cell` (a `Cell` behind the `&`,
//! next to owning pointers), `deep_map` (a `BTreeMap`, a `NonNull` inside: raw pointers
//! stay refused as ruled), `too_deep` (beyond the new cap of 64).
//!
//! RE-PINNED 2026-11-07: `use_fine` is now proved on every lane and `certify` no
//! longer refuses it (see its comment). Measured on one stage 1: the same file with
//! `Fine(pub u8)` and `&Fine(0)`, a non-zero-sized borrow that gets no value fact,
//! still reports both `certify` errors.
//!
//! RE-PINNED 2026-10-15 (the merge of 2026-10-14): under `strict` the discharged
//! caller now carries its call's panic-freedom aggregate as one `runtime_checked` row,
//! which `strict` reports rather than fails (it keeps its runtime check), so that
//! caller is no longer a `strict` error; `certify` still refuses it, and every
//! discharge failure and refused control below is unchanged (measured on the merged
//! stage 1).
use std::cell::Cell;
use std::collections::BTreeMap;
use std::marker::PhantomData;

pub struct Leaf {
    pub name: String,
    pub tags: Vec<String>,
}
pub struct L1 {
    pub leaves: Vec<Leaf>,
}
pub struct L2 {
    pub l1s: Vec<L1>,
}
pub struct L3 {
    pub l2s: Vec<L2>,
}
pub struct L4 {
    pub l3s: Vec<L3>,
}

pub trait Ser {
    fn field<V: ?Sized>(&self, value: &V);
}

pub fn by_ref_deep<S: Ser>(s: &S, d: &L4) {
    //[advisory]~^ WARN Trust verification advisory for `deep_owned_argument_admitted::by_ref_deep`: 1 instance hypothesis row(s)
    //[strict]~^^ WARN Trust verification advisory for `deep_owned_argument_admitted::by_ref_deep`: 1 instance hypothesis row(s)
    //[certify]~^^^ ERROR Trust certify verification failed for `deep_owned_argument_admitted::by_ref_deep`: 1 instance hypothesis row(s)
    s.field(d)
}

pub struct Visitor<T> {
    pub marker: PhantomData<T>,
}

pub trait De {
    fn deserialize_struct<V>(self, name: &'static str, visitor: V) -> u32;
}

pub fn by_value_visitor<D: De>(d: D) -> u32 {
    //[advisory]~^ WARN Trust verification advisory for `deep_owned_argument_admitted::by_value_visitor`: 1 instance hypothesis row(s)
    //[strict]~^^ WARN Trust verification advisory for `deep_owned_argument_admitted::by_value_visitor`: 1 instance hypothesis row(s)
    //[certify]~^^^ ERROR Trust certify verification failed for `deep_owned_argument_admitted::by_value_visitor`: 1 instance hypothesis row(s)
    d.deserialize_struct("L4", Visitor::<L4> { marker: PhantomData })
}

pub trait SerializeStruct {
    fn serialize_field<V: ?Sized>(&mut self, key: &'static str, value: &V);
}

pub trait Serializer {
    type SerializeStruct: SerializeStruct;
    fn start(&self) -> Self::SerializeStruct;
}

pub fn projection_receiver<S: Serializer>(st: &mut S::SerializeStruct, d: &L4) {
    //[advisory]~^ WARN Trust verification advisory for `deep_owned_argument_admitted::projection_receiver`: 1 instance hypothesis row(s)
    //[strict]~^^ WARN Trust verification advisory for `deep_owned_argument_admitted::projection_receiver`: 1 instance hypothesis row(s)
    //[certify]~^^^ ERROR Trust certify verification failed for `deep_owned_argument_admitted::projection_receiver`: 1 instance hypothesis row(s)
    st.serialize_field("l3s", d)
}

pub struct Fine;
pub struct Boom;

impl Ser for Fine {
    fn field<V: ?Sized>(&self, _value: &V) {}
}

impl Ser for Boom {
    fn field<V: ?Sized>(&self, _value: &V) {
        //[strict]~^ ERROR Trust Level 0 safety verification incomplete for `<deep_owned_argument_admitted::Boom as deep_owned_argument_admitted::Ser>::field`: 2 obligation(s) were not proved
        //[strict]~^^ ERROR Trust strict verification failed for `<deep_owned_argument_admitted::Boom as deep_owned_argument_admitted::Ser>::field`: 2 obligation(s) were not fully verified
        //[certify]~^^^ ERROR Trust Level 0 safety verification incomplete for `<deep_owned_argument_admitted::Boom as deep_owned_argument_admitted::Ser>::field`: 2 obligation(s) were not proved
        //[certify]~^^^^ ERROR Trust strict verification failed for `<deep_owned_argument_admitted::Boom as deep_owned_argument_admitted::Ser>::field`: 2 obligation(s) were not fully verified
        panic!("boom")
    }
}

pub fn use_fine(d: &L4) {
    //~^ NOTE Trust verification: 1 proved, 0 failed, 0 unknown, 0 timed out, 0 runtime-checked, 1 assumed (instance discharge) out of 2 obligation(s)
    // Re-pinned 2026-11-07: the call's panic-freedom aggregate was `runtime_checked`
    // only because `&Fine` (the promoted borrow of a fieldless struct) had no
    // transport fact; it now carries a source reference VALUE fact
    // (`docs/DECISION_QUEUE.md`, 2026-11-07) and is proved, so `certify` accepts
    // `use_fine` exactly as it accepts `discharge_row_per_instance::use_good`.
    by_ref_deep(&Fine, d)
}

pub fn use_boom(d: &L4) {
    //[advisory]~^ WARN Trust instance discharge not established for `deep_owned_argument_admitted::use_boom`: 1 instance(s)
    //[strict]~^^ ERROR Trust instance discharge not established for `deep_owned_argument_admitted::use_boom`: 1 instance(s)
    //[strict]~^^^ ERROR Trust strict verification failed for `deep_owned_argument_admitted::use_boom`: 1 obligation(s) were not fully verified
    //[certify]~^^^^ ERROR Trust Level 0 safety verification incomplete for `deep_owned_argument_admitted::use_boom`: 1 obligation(s) were not proved
    //[certify]~^^^^^ ERROR Trust instance discharge not established for `deep_owned_argument_admitted::use_boom`: 1 instance(s)
    //[certify]~^^^^^^ ERROR Trust strict verification failed for `deep_owned_argument_admitted::use_boom`: 1 obligation(s) were not fully verified
    by_ref_deep(&Boom, d)
}

// Controls: still refused. Each sits at the depth the old cap cut off, so before the
// fix it was refused as "opaque"; now the walk reaches the leaf and refuses it for
// what it is.

pub struct RawLeaf {
    pub name: String,
    pub p: *const u8,
}
pub struct R1 {
    pub leaves: Vec<RawLeaf>,
}
pub struct R2 {
    pub r1s: Vec<R1>,
}
pub struct R3 {
    pub r2s: Vec<R2>,
}
pub struct R4 {
    pub r3s: Vec<R3>,
}

pub fn deep_raw<S: Ser>(s: &S, d: &R4) {
    //[strict]~^ ERROR Trust Level 0 safety verification incomplete for `deep_owned_argument_admitted::deep_raw`: 1 obligation(s) were not proved
    //[strict]~^^ ERROR Trust strict verification failed for `deep_owned_argument_admitted::deep_raw`: 1 obligation(s) were not fully verified
    //[certify]~^^^ ERROR Trust Level 0 safety verification incomplete for `deep_owned_argument_admitted::deep_raw`: 1 obligation(s) were not proved
    //[certify]~^^^^ ERROR Trust strict verification failed for `deep_owned_argument_admitted::deep_raw`: 1 obligation(s) were not fully verified
    s.field(d)
}

pub struct CellLeaf {
    pub name: String,
    pub hits: Cell<u32>,
}
pub struct C1 {
    pub leaves: Vec<CellLeaf>,
}
pub struct C2 {
    pub c1s: Vec<C1>,
}
pub struct C3 {
    pub c2s: Vec<C2>,
}
pub struct C4 {
    pub c3s: Vec<C3>,
}

pub fn deep_cell<S: Ser>(s: &S, d: &C4) {
    //[strict]~^ ERROR Trust Level 0 safety verification incomplete for `deep_owned_argument_admitted::deep_cell`: 1 obligation(s) were not proved
    //[strict]~^^ ERROR Trust strict verification failed for `deep_owned_argument_admitted::deep_cell`: 1 obligation(s) were not fully verified
    //[certify]~^^^ ERROR Trust Level 0 safety verification incomplete for `deep_owned_argument_admitted::deep_cell`: 1 obligation(s) were not proved
    //[certify]~^^^^ ERROR Trust strict verification failed for `deep_owned_argument_admitted::deep_cell`: 1 obligation(s) were not fully verified
    s.field(d)
}

pub struct MapLeaf {
    pub env: BTreeMap<String, String>,
}

pub fn deep_map<S: Ser>(s: &S, d: &Vec<Vec<MapLeaf>>) {
    //[strict]~^ ERROR Trust Level 0 safety verification incomplete for `deep_owned_argument_admitted::deep_map`: 1 obligation(s) were not proved
    //[strict]~^^ ERROR Trust strict verification failed for `deep_owned_argument_admitted::deep_map`: 1 obligation(s) were not fully verified
    //[certify]~^^^ ERROR Trust Level 0 safety verification incomplete for `deep_owned_argument_admitted::deep_map`: 1 obligation(s) were not proved
    //[certify]~^^^^ ERROR Trust strict verification failed for `deep_owned_argument_admitted::deep_map`: 1 obligation(s) were not fully verified
    s.field(d)
}

// 17 owned layers of `W` (each `W -> Vec -> RawVec -> PhantomData<T>`): 68 levels
// before the `u8`, beyond the cap of 64, so the walk answers `Opaque` (refused).
pub struct W<T>(pub Vec<T>);
pub type Deep17 = W<W<W<W<W<W<W<W<W<W<W<W<W<W<W<W<W<u8>>>>>>>>>>>>>>>>>;

pub fn too_deep<S: Ser>(s: &S, d: &Deep17) {
    //[strict]~^ ERROR Trust Level 0 safety verification incomplete for `deep_owned_argument_admitted::too_deep`: 1 obligation(s) were not proved
    //[strict]~^^ ERROR Trust strict verification failed for `deep_owned_argument_admitted::too_deep`: 1 obligation(s) were not fully verified
    //[certify]~^^^ ERROR Trust Level 0 safety verification incomplete for `deep_owned_argument_admitted::too_deep`: 1 obligation(s) were not proved
    //[certify]~^^^^ ERROR Trust strict verification failed for `deep_owned_argument_admitted::too_deep`: 1 obligation(s) were not fully verified
    s.field(d)
}
