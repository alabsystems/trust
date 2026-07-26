#![crate_type = "lib"]
#![feature(register_tool)]
#![register_tool(trust)]
// MUTANT of proved/contract_panic_formatted_message.rs: the annotation payload
// "is 8" occurs in the FORMATTED runtime message ("… capacity is 8" — it
// straddles the literal piece and the placeholder's runtime value) but NOT in
// the template's literal-piece concatenation ("ArrayVec overflow: capacity
// is " — the runtime value is never in the template). The T7 harvest decodes
// literal pieces ONLY, so this annotation must NOT message-match: the
// unused-annotation check mints its guaranteed-FAILED `contract-panic-unused`
// row and the gate must REFUSE this (exit 1). If it ever proves, the template
// decoder leaked runtime-value bytes (or matched across the placeholder as
// formatted text) — the fail-closed side of the T7 contract is broken.
#[trust::contract_panic(message_contains = "is 8")]
pub fn slot_index_fmt(i: usize) -> usize {
    let cap = 8usize;
    let k = if i < 8 { i } else { 7 };
    if k >= 8 {
        panic!("ArrayVec overflow: capacity is {}", cap);
    }
    k
}
