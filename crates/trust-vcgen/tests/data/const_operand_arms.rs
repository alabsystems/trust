// Real-MIR arms for SELF-GUARDED-CONST-OPERAND-1: the self-guarded statement-lane
// row over a CONSTANT operand that has a value identity (a const-generic parameter,
// or a keyed opaque scalar such as `T::U`). Compiled with overflow checks ON.
//
// rustc does not fold these: `-N`, `x / N`, `x % N`, `x << N` keep their checked
// asserts, with the symbolic constant on both sides of the chain, e.g.
//
//     bb0: _1 = Eq(const N, const i32::MIN); assert(!_1, OverflowNeg) -> bb1
//     bb1: _0 = Neg(const N)
//
// Every one of these functions panics for some instantiation, so none of their
// rows may read `proved`.

pub trait Tr {
    const U: u32;
}

// THE HEADLINE: `neg_c::<{ i32::MIN }>()` panics.
#[inline(never)]
pub fn neg_c<const N: i32>() -> i32 {
    -N
}

// Width sweep. i128 is in scope: a symbolic constant has no BV rendering, so both
// lanes take the Int constructors there too.
#[inline(never)]
pub fn neg_c8<const N: i8>() -> i8 {
    -N
}

#[inline(never)]
pub fn neg_c64<const N: i64>() -> i64 {
    -N
}

#[inline(never)]
pub fn neg_c128<const N: i128>() -> i128 {
    -N
}

#[inline(never)]
pub fn div_c<const N: u32>(x: u32) -> u32 {
    x / N
}

#[inline(never)]
pub fn rem_c<const N: u32>(x: u32) -> u32 {
    x % N
}

// SIGNED: the zero assert, then the intervening `Overflow(Div)` assert.
#[inline(never)]
pub fn sdiv_c<const N: i32>(x: i32) -> i32 {
    x / N
}

#[inline(never)]
pub fn srem_c<const N: i32>(x: i32) -> i32 {
    x % N
}

// The const generic as the DIVIDEND: `N / -1` overflows at `N == i32::MIN`.
#[inline(never)]
pub fn sdiv_c_dividend<const N: i32>() -> i32 {
    N / -1
}

#[inline(never)]
pub fn shl_c<const N: u32>(x: u32) -> u32 {
    x << N
}

#[inline(never)]
pub fn shr_c<const N: u32>(x: u64) -> u64 {
    x >> N
}

// A KEYED opaque scalar (`OpaqueOrigin::Const`): `T::U` is one value per key.
#[inline(never)]
pub fn div_a<T: Tr>(x: u32) -> u32 {
    x / T::U
}
