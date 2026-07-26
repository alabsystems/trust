// Record-witness probe fixtures — fresh MIR dump for SemStructReturn (increment 1).
// Anchor: mk_pair (BinderData::new-class). Marker: mk_three (PhantomData<u32>).
// Forgery: mk_bad (reassigned param). Order probe: mk_swap (distinct swapped operands).
use std::marker::PhantomData;

pub struct Pair {
    pub a: i64,
    pub b: i64,
}

pub struct Three {
    pub a: i64,
    pub m: PhantomData<u32>,
    pub b: i64,
}

#[inline(never)]
pub fn mk_pair(a: i64, b: i64) -> Pair {
    Pair { a, b }
}

#[inline(never)]
pub fn mk_three(a: i64, b: i64) -> Three {
    Three { a, m: PhantomData, b }
}

// Reassigned-param forgery fixture: `a` is genuinely rewritten from a non-const
// (self+b) so trustc cannot const-fold it away — the Aggregate operand for field
// `a` is `Copy(_1)` where `_1` (param 0) was reassigned. The record recognizer MUST
// decline: an entry-time `Var(0)` denotation would certify the WRONG (pre-reassign)
// value.
#[inline(never)]
pub fn mk_bad(mut a: i64, b: i64) -> Pair {
    a = a & b;
    Pair { a, b }
}

// Distinct-operand two-same-sorted-field fixture: fields sourced in swapped param order.
#[inline(never)]
pub fn mk_swap(x: i64, y: i64) -> Pair {
    Pair { a: y, b: x }
}

fn main() {
    let n = std::env::args().count() as i64;
    let p = mk_pair(n, n + 1);
    let t = mk_three(n, n + 2);
    let bad = mk_bad(n, n + 3);
    let sw = mk_swap(n, n + 4);
    std::process::exit(((p.a ^ p.b ^ t.a ^ t.b ^ bad.a ^ bad.b ^ sw.a ^ sw.b) & 1) as i32);
}
