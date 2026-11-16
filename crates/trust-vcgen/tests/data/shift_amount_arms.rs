// Real-MIR arms for SHIFT-BINDER-RESIDUE-1: the two shift-member residues that
// SELF-GUARDED-CONST-OPERAND-1 left, place and const-generic alike. Compiled with
// overflow checks ON.
//
// (1) THE WIDTH. Two shifts of different widths share a widthless constant shifted
// value and one amount, so each matches the other by operands:
//
//     bb0: _2 = Lt(const N, const 64_u32); assert(_2, Overflow(Shl)) -> bb1
//     bb1: _1 = Shl(const 1, const N); _4 = Lt(const N, const 8_u32); assert(_4) -> bb2
//     bb2: _3 = Shl(const 1, const N); ...
//
// (2) THE SIGNED AMOUNT. rustc checks a signed amount through a same-width
// unsigned cast temporary:
//
//     bb0: _2 = Cast(const N, u32); _3 = Lt(move _2, const 32_u32); assert(_3) -> bb1
//     bb1: _0 = Shl(copy _1, const N)
//
// Every unguarded function here panics for some argument or instantiation
// (`rev_c::<64>()` at its FIRST shift, `shl_ci::<{ -1 }>(1)`), so none of its rows
// may read `proved`. Every `_guarded` twin is safe, so none of its rows may be
// refuted.

#[inline(never)]
pub fn rev_c<const N: u32>() -> (i64, i8) {
    (1i64 << N, 1i8 << N)
}

#[inline(never)]
pub fn rev_p(s: u32) -> (i64, i8) {
    (1i64 << s, 1i8 << s)
}

// The narrow shift first: the minimum was already right for the first assert.
#[inline(never)]
pub fn fwd_p(s: u32) -> (i8, i64) {
    (1i8 << s, 1i64 << s)
}

#[inline(never)]
pub fn shl_ci<const N: i32>(x: u32) -> u32 {
    x << N
}

#[inline(never)]
pub fn shl_s(x: u32, s: i32) -> u32 {
    x << s
}

#[inline(never)]
pub fn shr_ci8<const N: i8>(x: u64) -> u64 {
    x >> N
}

#[inline(never)]
pub fn shl_s64(x: u128, s: i64) -> u128 {
    x << s
}

// An i128 amount: the cast target is u128, where `2^(W-1)` no longer fits an i128.
#[inline(never)]
pub fn shl_s128(x: u64, s: i128) -> u64 {
    x << s
}

// Safe: the i64 shift under `N < 64`, the i8 one under `N < 8`. A row built at the
// by-operands minimum (8) for the i64 shift would be refuted here.
#[inline(never)]
pub fn rev_c_guarded<const N: u32>() -> (i64, i8) {
    if N < 64 { (1i64 << N, if N < 8 { 1i8 << N } else { 0 }) } else { (0, 0) }
}

#[inline(never)]
pub fn shl_s_guarded(x: u32, s: i32) -> u32 {
    if s >= 0 && s < 32 { x << s } else { x }
}
