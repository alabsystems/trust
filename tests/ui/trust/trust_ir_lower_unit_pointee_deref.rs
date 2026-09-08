//@ check-pass
//@ compile-flags: -Ztrust-ir-lower -Ztrust-verify=off
// wave-UD: `*r` on `&()` is GROUND TRUTH, not a memory read — unit has one
// inhabitant, so the deref mints the zero-size PhantomData constant directly
// and emits no Load (there are no bytes to read).
//
// The clause is RESTRICTED to non-Borrow operands: the `*&()` identity chain
// (`&() as &'static dyn Debug` arrives as Borrow{Deref{Borrow{unit}}}) is
// place machinery whose address rustc PROMOTES — minting a value there fed the
// snapshot lane a frame address where the oracle holds the promoted static,
// and the differential caught it as a real divergence on this clause's first
// sweep (issue-55825's no_dyn_trait_ret). That chain keeps its refusal.

pub fn read_unit(r: &()) {
    *r
}

pub fn use_unit(r: &()) -> u32 {
    let _v = *r;
    7
}

fn main() {}
