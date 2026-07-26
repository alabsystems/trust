#![crate_type = "lib"]
#![feature(register_tool)]
#![register_tool(trust)]
// SOUNDNESS REGRESSION (strict-mode false proof, found by the adversarial false-proof
// hunt). The owned `tx` is moved into a LOCAL array `[tx]` that is dropped at scope end —
// the transaction is silently abandoned (its destructor / rollback runs), never committed.
// Trust must REJECT must-consume (the move-into-a-locally-dropped aggregate is NOT a
// handoff). Pairs with leak_into_dropped_tuple.
pub struct Txn {
    id: u32,
}
// A real resource (e.g. an open transaction): its destructor is the rollback that must NOT
// run silently. Its Drop glue is what the linearity check keys on.
impl Drop for Txn {
    fn drop(&mut self) {}
}
#[trust::must_consume]
pub fn process(tx: Txn) {
    let _buf = [tx];
}
