//@ dont-check-compiler-stderr
//@ check-pass
//@ compile-flags: -Ztrust-ir-lower=strict -Ztrust-verify=on -Ztrust-policy=advisory
//@ needs-trust-verify
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE
//! Trust (wave-PF): a ledgered borrow pointer may be stored into a THIN-ref
//! struct/tuple FIELD (`Holder { r: &x, .. }`, `(&a, &b)`) and the aggregate
//! handed on to a call — the measured shape (`AlignedDrop { drop_count:
//! &drop_count, .. }`, `Droppable(&mut xv, 1)`). The three escape routes
//! (return, memory, call) are each already closed — see
//! `borrow_ptr_field_admissible`. Under `strict`.
//!
//! UPDATED 2026-09-16. Two sentences this doc used to carry are retired:
//! "reading the pointer lane back through the `Field` arm is still refused"
//! (wave-PR admits it, unledgered) and the implicit "only a NAMED local's
//! snapshot is admitted" — an RVALUE temporary rustc provably cannot promote
//! (`&f(x)`, a non-`#[rustc_promotable]` `FnDef` call, or an aggregate holding
//! one) is admitted too, on the same borrowck argument; see
//! `trust_ir_lower_rvalue_snapshot_field.rs` and the predicate
//! `rvalue_temp_is_unpromotable`. This file's shapes are all named locals and
//! are a CONTROL for that landing: byte-identical.

struct Holder<'a> {
    r: &'a u32,
    tag: u8,
}

fn take_holder(h: Holder<'_>) -> u8 {
    h.tag
}

fn take_pair(p: (&u32, &mut u8)) -> u8 {
    let _ = p;
    7
}

fn through_struct(x: u32) -> u8 {
    let h = Holder { r: &x, tag: 42 };
    take_holder(h)
}

fn through_tuple(a: u32) -> u8 {
    let mut b = 1u8;
    let t = (&a, &mut b);
    take_pair(t)
}

fn main() {
    if through_struct(41) != 42 {
        std::process::exit(1);
    }
    if through_tuple(40) != 7 {
        std::process::exit(2);
    }
}
