//@ check-pass
//@ compile-flags: -Z trust-ir-lower -Z trust-verify=off

// Trust (vtable slice 13 — linked-call literal width conformance + seam/linked
// promoted-global admission). Every body below must keep COMPILING — a lowering decline
// is a coverage decision, never an error — and each pins one measured lane of the slice.

// (2d) THE WIDTH CONFORMANCE (mod-pub-access::main / issue-87988::main, measured):
// trust-types' signed literal carrier is WIDTH-LESS and the bridge's contextless
// emission defaulted it to I64 (and spelled a usize argument U64), while a LINKED
// callee's params lower faithfully (i32/usize) — the interpreter's exact-type call
// check then refused the bundle mid-interpretation ("expected i32, got i64" /
// "expected usize, got u64") and the trust-ir validator rejected it as
// CallArgTypeMismatch. A fitting Int/Uint literal call argument now conforms to the
// callee's declared param type (the same exact-fit retype assign destinations already
// had); a non-fitting literal keeps the contextless spelling byte-identically.
pub fn takes_i32(_n: i32) {}
pub fn takes_usize(_n: usize) {}

pub fn caller() {
    takes_i32(1);
    takes_usize(0);
}

// (3-ii) THE LINKED-CALL ADMISSION (macro-named-default::main, measured Agreed): a
// paired promoted-global address handed to a linked callee that never uses it. The
// call-free admission bound is retired; the seeded-parameter audit proves the callee
// use-free (Return positions refuse, call results are never tracked), so the pair
// mints the verdict the bound used to withhold.
pub struct Receiver;

impl Receiver {
    pub fn method(&self) {}
}

pub fn linked_admission() {
    Receiver.method();
}

// (3-i) THE DEAD-ADDRESS ARM (sugar-ambiguity::main, measured Agreed): promoted
// addresses whose Borrow/Copy closures are provably use-free materialize no
// observation and need no pairing — including the oracle-only respell extra the
// `ref`-pattern binding mints. The one LIVE loaded global still carries the full
// slice-7 pairing conjuncts.
pub struct Marker;

pub fn dead_addresses() {
    let _x: &Marker = &Marker;
    let &_y: &i32 = &0;
    let ref _z: i32 = 0;
}

fn main() {}
