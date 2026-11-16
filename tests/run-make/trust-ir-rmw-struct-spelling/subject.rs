//! Actual THIR inputs: write/read ordering and preserved opaque-lane refusals.
#![allow(dead_code)]

pub struct PointerInner {
    pub ok: bool,
    pub p: *const u8,
}

pub struct PointerOuter {
    pub a: PointerInner,
    pub b: usize,
}

pub struct Envelope {
    pub outer: PointerOuter,
}

pub fn make() -> PointerOuter {
    PointerOuter { a: PointerInner { ok: true, p: core::ptr::null() }, b: 0 }
}

// This is the closed standalone reduction's triggering statement order.
pub fn pointer_write_then_read(o: &mut PointerInner) -> bool {
    o.ok = false;
    make().a.ok
}

pub fn pointer_read_then_write(o: &mut PointerInner) -> bool {
    let answer = make().a.ok;
    o.ok = false;
    answer
}

pub fn pointer_write_then_read_local(o: &mut PointerInner) -> bool {
    o.ok = false;
    let answer = make();
    answer.a.ok
}

// The first RMW retains its effect refusal, but its registration probe prefers
// the real pointer lane. A later literal must not treat that lane as a () floor.
pub fn pointer_write_then_literal(o: &mut PointerInner) -> bool {
    o.ok = false;
    let rebuilt = PointerInner { ok: true, p: core::ptr::null() };
    rebuilt.ok
}

pub fn consume_inner(value: PointerInner) -> bool {
    value.ok
}

pub fn pointer_write_then_pass(o: &mut PointerInner) -> bool {
    o.ok = false;
    consume_inner(make().a)
}

pub fn nested_write_then_read(o: &mut Envelope) -> bool {
    o.outer.a.ok = false;
    make().a.ok
}

pub struct CounterInner {
    pub n: u32,
    pub p: *const u8,
}

pub struct CounterOuter {
    pub a: CounterInner,
}

pub fn make_counter() -> CounterOuter {
    CounterOuter { a: CounterInner { n: 7, p: core::ptr::null() } }
}

// Compound assignment reaches written_field=Some, rather than the plain-store chain.
pub fn pointer_compound_then_read(o: &mut CounterInner) -> u32 {
    o.n ^= 1;
    make_counter().a.n
}

pub struct PureInner {
    pub ok: bool,
    pub n: usize,
}

pub struct PureOuter {
    pub a: PureInner,
}

pub fn make_pure() -> PureOuter {
    PureOuter { a: PureInner { ok: true, n: 3 } }
}

pub fn pure_write_then_read(o: &mut PureInner) -> bool {
    o.ok = false;
    make_pure().a.ok
}

pub struct WithVec {
    pub ok: bool,
    pub values: Vec<u8>,
}

pub fn vector_sibling_write(o: &mut WithVec) {
    o.ok = false;
}

pub struct WithOption {
    pub ok: bool,
    pub pair: Option<(u32, u32)>,
}

pub fn option_sibling_write(o: &mut WithOption) {
    o.ok = false;
}

pub struct AdmittedOption {
    pub n: u32,
    pub label: Option<String>,
}

// The RMW candidate is bool with Option flags on and () with them off;
// ordinary registration keeps the admitted enum in both modes.
pub fn admitted_option_write_then_literal(o: &mut AdmittedOption) -> u32 {
    o.n ^= 1;
    let rebuilt = AdmittedOption { n: 7, label: None };
    rebuilt.n
}

pub struct WithZeroArray {
    pub n: u32,
    pub z: [String; 0],
}

// A faithful zero-length array is not an actual () floor and must not receive
// the floor's PhantomData stand-in or its literal refusal.
pub fn zero_array_write_then_literal(o: &mut WithZeroArray) -> u32 {
    o.n ^= 1;
    let rebuilt = WithZeroArray { n: 7, z: [] };
    rebuilt.n
}

pub struct WithWide<'a> {
    pub ok: bool,
    pub values: &'a mut [u8],
}

pub fn mutable_wide_sibling_write(o: &mut WithWide<'_>) {
    o.ok = false;
}

pub union Bits {
    pub word: u32,
    pub bytes: [u8; 4],
}

pub struct WithUnion {
    pub ok: bool,
    pub bits: Bits,
}

pub fn union_sibling_write(o: &mut WithUnion) {
    o.ok = false;
}

// A genuinely non-scalar WRITTEN field: do not turn its union placeholder into
// an ordinary container/opaque store when the registration probe runs.
pub fn union_field_write(o: &mut WithUnion) {
    o.bits = Bits { word: 7 };
}
