//@ check-pass
//@ compile-flags: -Ztrust-ir-lower -Ztrust-verify=off
// wave-RK2 (INVALID root 7, full-population frontier): the RMW-opaque
// struct builder DELIBERATELY spells a non-pure-value sibling field as a
// placeholder (`()` / the `Ty::Bool` Option lane) — sound within one body,
// where every mention of the struct shares that spelling. But a BY-VALUE
// call arg typed at the degraded row crossing into a LOCAL callee meets
// the callee's own FAITHFUL signature at crate assembly:
// fn-arg-incomplete-pattern-drop-order registered `Context<'_>` as BOTH
// {i32, ptr} (the callee's map_ty spelling) and {i32, ()} (the Drop
// body's RMW spelling), and the call edge mixed them —
// CallArgTypeMismatch, an INVALID module. The producer now ledgers
// degraded registrations (`rmw_degraded_structs`, recorded only when the
// registered row actually carries the degraded field list — a dedup-hit
// on a faithful row is NOT ledgered) and `lower_call_args` fails a
// by-value degraded arg to a LOCAL callee closed. Extern callees keep the
// lane: their declaration is authored by the same builder under the same
// spelling, so those edges stay consistent.
use std::cell::RefCell;

#[derive(Copy, Clone)]
pub struct Ctx<'a> {
    pub tag: i32,
    pub log: &'a RefCell<Vec<i32>>,
}

impl<'a> Ctx<'a> {
    fn consume(self, index: i32) {
        self.log.borrow_mut().push(index + self.tag);
    }
}

pub struct Holder<'a>(pub i32, pub Ctx<'a>);

// The measured shape: `self.1` reaches this body through the RMW builder
// (the `&mut self` receiver), so `Ctx` registers degraded here; passing it
// BY VALUE to the LOCAL `consume` must DECLINE
// (`Call(rmw-degraded arg spelling)`) — probe-verified: this file's module
// carries 0 validation errors while this body reports the tag.
impl<'a> Drop for Holder<'a> {
    fn drop(&mut self) {
        self.1.consume(self.0);
    }
}

// Negative control: a body whose view of `Ctx` is the FAITHFUL map_ty
// spelling (no RMW receiver in sight) passes the same by-value arg to the
// same local callee and stays lowered — the ledger keys the ROW, not the
// type name.
pub fn faithful_forward(c: Ctx<'_>) {
    c.consume(7);
}

fn main() {
    let log = RefCell::new(Vec::new());
    faithful_forward(Ctx { tag: 1, log: &log });
    let _h = Holder(2, Ctx { tag: 3, log: &log });
}
