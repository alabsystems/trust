#![crate_type = "lib"]
// `contract_panic` is a TOOL attribute — same registration convention as
// proved/contract_panic_annotated.rs.
#![feature(register_tool)]
#![register_tool(trust)]
// T7 (contract-panic matcher through panic_fmt — FORMATTED message): on this
// toolchain `panic!("... {}", x)` lowers to
//   _t = const b"\x1fArrayVec overflow: capacity is \xc0\x00";   // fmt TEMPLATE
//   _a = fmt::Arguments::new::<N, 1>(move _t, ...);
//   panic_fmt(move _a)
// with the literal pieces carried ONLY in the length-prefixed TEMPLATE
// byte-string (library/core/src/fmt/mod.rs "Internal representation" 2).
// BUG (aterm-alloc evidence): extraction lowered the `&[u8; N]` template to
// the content-free OpaqueConst, and the matcher chased only
// `Arguments::from_str`/`new_const` — so `message_contains` could NEVER match
// a formatted panic, forcing const-message rewrites in user code. FIX: the
// template bytes are now carried (`ConstValue::Str`, trust-mir-extract
// convert.rs Slice/Array arm) and `panic_call_const_str_messages` decodes the
// literal-piece CONCATENATION through the `Arguments::new` chase
// (`fmt_template_literal_pieces`, fail-closed on any malformed byte), keeping
// the unused-annotation semantics on the same harvest.
// MUST PROVE (exit 0): `k` is provably < 8 on every path (the clamp-then-guard
// shape of proved/contract_panic_annotated.rs), so the annotated panic is
// unreachable, AND the annotation counts as USED because the payload occurs in
// the template's literal piece — no always-FAILED `contract-panic-unused` row.
// FLIP: mutant/contract_panic_formatted_message.rs moves the payload to text
// that exists only in the RUNTIME value of the formatted message — the
// template harvest must NOT match it, so the unused-annotation check mints its
// guaranteed-FAILED row (exit 1).

/// Clamp-then-guard with a FORMATTED capacity message: the runtime value
/// (`cap`) is a placeholder in the template; the payload below matches the
/// literal piece "ArrayVec overflow: capacity is ".
#[trust::contract_panic(message_contains = "capacity is")]
pub fn slot_index_fmt(i: usize) -> usize {
    // Literal-8 guards: byte-identical control shape to the proven-green
    // proved/contract_panic_annotated.rs, so the ONLY new capability under
    // test is the formatted-message harvest.
    let cap = 8usize;
    let k = if i < 8 { i } else { 7 };
    if k >= 8 {
        panic!("ArrayVec overflow: capacity is {}", cap);
    }
    k
}
