//@ check-pass
//@ compile-flags: -Ztrust-ir-lower -Ztrust-verify=off
// wave-full-0901 residue (the first full re-baseline after the INVALID
// ledger closed): three roots the 2000-sample could not see, each pinned
// here.
//
// 1. D4 COMPLETION — `param_opaque` alone did not close the contract
//    elision channel: the differential samples a SYMBOLIC body whose
//    placeholder is provably never read, and a contract carrier is
//    exactly that (`typed_lane(x) requires x > 0 { x }` re-diverged at
//    i32::MIN — THIR ran the identity, the oracle trapped on the woven
//    requires assert). A contract-attributed body now also forces
//    `contains_call` (NotRun — the EMO/ER never-interpret spelling).
//
// 2. wave-LC — a struct LAYOUT claim must cohere with the DECLARED field
//    list: a degraded `()` field beside rustc's faithful size (NonNull<dyn
//    Fn> { () } size=16, reachable once the wave-RK2 region fold
//    un-blocked `for<'a>`-binder args from the layout query) is
//    absent-filled instead; and a NICHE enum descriptor whose payload
//    chain reaches a size-less row is STRIPPED (the root-2 decline
//    posture) — the validator's bounding rule could never resolve it.
//
// 3. wave-FPS — a fat raw pointer FIELD (`*const [T]`) is registered at
//    map_ty's tuple spelling while value lanes produce `fatptr`; the
//    struct literal fails closed (`Adt(fat raw ptr field)`) until the
//    spellings unify (maybe-bounds-where-cpass).

// (1) — must lower, must be symbolic AND NotRun; never sampled.
#[trust::requires(x > 0)]
fn contract_carrier(x: i32) -> i32 {
    x
}

// (2) — the 113793 shape: Option<Box<dyn Fn>> mints a niche over a
// declared chain whose NonNull<dyn> row degrades; the descriptor must
// strip and the module stay valid (probe-verified 0 validation errors).
struct T;
impl Iterator for T {
    type Item = Box<dyn Fn(&dyn ToString)>;
    fn next(&mut self) -> Option<Self::Item> {
        None
    }
}

// (3) — the maybe-bounds shape: fat-raw-ptr field literal declines.
struct S<Q>(*const Q)
where
    Q: ?Sized;

fn build(v: &[u8]) -> S<[u8]> {
    S(v)
}

fn main() {
    let _ = contract_carrier(1);
    let _ = T.next();
    let _ = build(&[1, 2]);
}
