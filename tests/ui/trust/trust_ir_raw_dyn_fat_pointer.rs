//@ check-pass
//@ compile-flags: -Z trust-ir-lower -Z trust-verify=off

// Trust (wave-RD): a raw `*const dyn Trait` / `*mut dyn Trait` is a (data, vtable) pair and now
// lowers to the format's first-class `Ty::FatPtr(FatPtrKind::TraitObject { trait_id })` — the same
// spelling B2-3 gave `&dyn Trait`, on BOTH the THIR producer (`map_ty`'s `ty::RawPtr` arm) and the
// MIR-side oracle (`trust-ir-bridge`'s stateless mapper).
//
// WHY BOTH SIDES IN ONE CHANGE. The oracle sent every `Ty::RawPtr { .. }` to a THIN `Ptr` and said
// so in its own comment ("...as do `&mut dyn` and raw `*dyn` (producer fail-closed)"). Moving the
// producer alone would not have added coverage — it would have MANUFACTURED the fat-vs-thin
// signature divergence that wave-19's DST-coherence gate exists to catch. `trait_id` comes from
// the one shared mint, `trust_ir::stable_trait_object_id`, so the two sides compare by value.
//
// Measured before the change: the `Ty(raw-ptr fat/array pointee)` bucket was 100% `*const dyn`
// (25 of 25 occurrences across the 19 non-symbolic sole-blocker bodies).
//
// Mutability is deliberately NOT part of the gate — unlike the `&dyn` arm, which is shared-only
// because `&mut dyn` still rides the thin `&mut` path on both sides. A raw pointer's fatness does
// not depend on mutability, and the oracle's `Ty::RawPtr` already ignores it.

trait Speak {
    fn speak(&self) -> u32;
}

struct Dog;
impl Speak for Dog {
    fn speak(&self) -> u32 {
        1
    }
}

// Both raw spellings reach the same arm and must get the same fat type.
fn hold_const(p: *const dyn Speak) -> *const dyn Speak {
    p
}

fn hold_mut(p: *mut dyn Speak) -> *mut dyn Speak {
    p
}

// The raw pointer as a struct field — the shape that made `Adt`/`Field` lanes fail closed.
struct Holder {
    tag: u64,
    p: *const dyn Speak,
}

fn hold_in_struct(h: Holder) -> u64 {
    h.tag
}

// A PRINCIPAL-LESS trait object still fails closed on both sides: `dyn Send` has no def path to
// hash, and the oracle keeps its thin `"dyn"` sentinel there, so the pair must stay uncompared
// rather than share a sentinel id. This must keep compiling — it is a coverage decline, not an
// error — which is the whole point of exercising it here.
fn hold_principalless(p: *const dyn Send) -> *const dyn Send {
    p
}

// The `&dyn` sibling, unchanged by this wave, kept alongside so a regression that collapsed the
// two spellings back together would show up here rather than only in the scorecard.
fn hold_ref(r: &dyn Speak) -> u32 {
    r.speak()
}

fn main() {
    let d = Dog;
    let rp: *const dyn Speak = &d;
    let _ = hold_const(rp);

    let mut d2 = Dog;
    let mp: *mut dyn Speak = &mut d2;
    let _ = hold_mut(mp);

    assert_eq!(hold_in_struct(Holder { tag: 7, p: rp }), 7);
    assert_eq!(hold_ref(&d), 1);

    let s = 5u32;
    let sp: *const dyn Send = &s;
    let _ = hold_principalless(sp);
}
