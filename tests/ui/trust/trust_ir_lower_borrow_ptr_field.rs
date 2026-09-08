//@ dont-check-compiler-stderr
//@ check-pass
//@ compile-flags: -Ztrust-ir-lower=strict -Ztrust-verify=off
//! Trust (wave-PF): a ledgered borrow pointer may be stored into a THIN-ref
//! struct/tuple FIELD (`Holder { r: &x, .. }`, `(&a, &b)`) and the aggregate
//! handed on to a call — the measured shape (`AlignedDrop { drop_count:
//! &drop_count, .. }`, `Droppable(&mut xv, 1)`). The three escape routes
//! (return, memory, call) are each already closed — see
//! `borrow_ptr_field_admissible`. Reading the pointer lane back through the
//! `Field` arm is a separate, still-refused question. Under `strict`.

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
