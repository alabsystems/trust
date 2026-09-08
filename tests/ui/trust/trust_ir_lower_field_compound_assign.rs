//@ check-pass
//@ compile-flags: --crate-type=lib -Ztrust-ir-lower -Ztrust-verify=off
//@ forbid-output: final Trust-IR module validation failed
// wave-AOF: `a.b op= v` — compound assignment to a scalar FIELD of an
// unpromoted, SSA-bound struct or tuple local.
//
// This wave is a pure ASYMMETRY repair, which is why it needs no new memory
// model. Measured at wave-full-0902 on `tests/ui/consts/const_let_eq.rs`:
// `foo.0 = 1` lowered (wave-AW struct / wave-TF tuple version the local by
// `InsertField` + `set_local`), and `a.b` as an rvalue already read through
// `ExtractField` — but `foo.0 += 1` on the very same local fell through to
// `AssignOp(non-local place)`, whose comment read "a projected place we do
// not version yet". Both halves of the versioning were already there; only
// their composition was missing.
//
// The place tags were the largest item on the frontier board
// (reports/frontier-after-the-scalar-seam-2026-09-02.md), and the sole-tag
// counts understated them badly: 1,110 bodies TOUCH a place tag against the
// ~69 the sole column showed.
//
// FENCES (each keeps the pre-wave tag): unpromoted, SSA-bound, registered
// struct/tuple lane; no borrow-ptr aggregate; scalar leaf equal to the place
// type the binop was set up for; and a registered union lane is refused
// outright. `emit_arith_binop` is shared with `ExprKind::Binary`, so `x.0 +=
// e` traps on exactly the inputs `x.0 = x.0 + e` does.

pub struct Foo<T>(pub T);
pub struct Bar<T> {
    pub x: T,
}

// The measured shape, both spellings: a tuple-struct field and a named field.
pub fn structs() -> u32 {
    let mut foo: Foo<u32> = Foo(0);
    let mut bar: Bar<u32> = Bar { x: 0 };
    foo.0 += 1;
    bar.x += 1;
    foo.0 + bar.x
}

// A bare TUPLE local — the wave-TF counterpart.
pub fn tuples() -> i64 {
    let mut t: (i64, i64) = (3, 4);
    t.0 += 10;
    t.1 *= 2;
    t.0 + t.1
}

// Every arithmetic op routes through the shared checked emitter, including
// the ones that trap on inputs other than overflow.
pub fn ops(d: u32) -> u32 {
    let mut f = Foo(64u32);
    f.0 += d;
    f.0 -= 1;
    f.0 *= 2;
    f.0 /= d + 1;
    f.0 %= 7;
    f.0
}

// Bitwise and shift compound forms share the same lane.
pub fn bits() -> u32 {
    let mut f = Foo(0b1010u32);
    f.0 |= 0b0101;
    f.0 &= 0b1110;
    f.0 ^= 0b0011;
    f.0 <<= 2;
    f.0 >>= 1;
    f.0
}

// FLOAT leaves do not trap, and the emitter already splits that path.
pub fn floats() -> f64 {
    let mut f = Foo(1.5f64);
    f.0 += 0.25;
    f.0 *= 2.0;
    f.0
}

// ORDER: the rhs is evaluated BEFORE the place is read, so a rebind inside
// the rhs is observed by the read. `t.0` is 1 when the rhs completes, so the
// result is 1 + 5 = 6, not 0 + 5.
pub fn rhs_first() -> i64 {
    let mut t = (0i64, 0i64);
    t.0 += {
        t.0 = 1;
        5
    };
    t.0
}

// A signed leaf — `signed` is derived from the place type, so the checked
// binop picks the signed overflow/division asserts.
pub fn signed(v: i32) -> i32 {
    let mut b = Bar { x: -5i32 };
    b.x += v;
    b.x
}

fn main() {}
