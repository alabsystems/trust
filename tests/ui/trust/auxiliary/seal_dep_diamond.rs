//@ edition: 2021
//@ compile-flags: --crate-type=rlib -O -Ztrust-verify=off -A warnings
//@ no-prefer-dynamic
//! A dependency of `clean_island_seal_trust_masks.rs`: a chain of 20
//! diamonds (`a_i` and `b_i` each call `a_{i+1}` and `b_{i+1}`), which the
//! compiler makes as 40 instances and which has 2^20 paths. Safe, and sound.

#[inline(never)] pub fn a1<T: Copy>(t: T) -> usize { a2(t) + b2(t) }
#[inline(never)] pub fn b1<T: Copy>(t: T) -> usize { a2(t) + b2(t) + 1 }
#[inline(never)] pub fn a2<T: Copy>(t: T) -> usize { a3(t) + b3(t) }
#[inline(never)] pub fn b2<T: Copy>(t: T) -> usize { a3(t) + b3(t) + 1 }
#[inline(never)] pub fn a3<T: Copy>(t: T) -> usize { a4(t) + b4(t) }
#[inline(never)] pub fn b3<T: Copy>(t: T) -> usize { a4(t) + b4(t) + 1 }
#[inline(never)] pub fn a4<T: Copy>(t: T) -> usize { a5(t) + b5(t) }
#[inline(never)] pub fn b4<T: Copy>(t: T) -> usize { a5(t) + b5(t) + 1 }
#[inline(never)] pub fn a5<T: Copy>(t: T) -> usize { a6(t) + b6(t) }
#[inline(never)] pub fn b5<T: Copy>(t: T) -> usize { a6(t) + b6(t) + 1 }
#[inline(never)] pub fn a6<T: Copy>(t: T) -> usize { a7(t) + b7(t) }
#[inline(never)] pub fn b6<T: Copy>(t: T) -> usize { a7(t) + b7(t) + 1 }
#[inline(never)] pub fn a7<T: Copy>(t: T) -> usize { a8(t) + b8(t) }
#[inline(never)] pub fn b7<T: Copy>(t: T) -> usize { a8(t) + b8(t) + 1 }
#[inline(never)] pub fn a8<T: Copy>(t: T) -> usize { a9(t) + b9(t) }
#[inline(never)] pub fn b8<T: Copy>(t: T) -> usize { a9(t) + b9(t) + 1 }
#[inline(never)] pub fn a9<T: Copy>(t: T) -> usize { a10(t) + b10(t) }
#[inline(never)] pub fn b9<T: Copy>(t: T) -> usize { a10(t) + b10(t) + 1 }
#[inline(never)] pub fn a10<T: Copy>(t: T) -> usize { a11(t) + b11(t) }
#[inline(never)] pub fn b10<T: Copy>(t: T) -> usize { a11(t) + b11(t) + 1 }
#[inline(never)] pub fn a11<T: Copy>(t: T) -> usize { a12(t) + b12(t) }
#[inline(never)] pub fn b11<T: Copy>(t: T) -> usize { a12(t) + b12(t) + 1 }
#[inline(never)] pub fn a12<T: Copy>(t: T) -> usize { a13(t) + b13(t) }
#[inline(never)] pub fn b12<T: Copy>(t: T) -> usize { a13(t) + b13(t) + 1 }
#[inline(never)] pub fn a13<T: Copy>(t: T) -> usize { a14(t) + b14(t) }
#[inline(never)] pub fn b13<T: Copy>(t: T) -> usize { a14(t) + b14(t) + 1 }
#[inline(never)] pub fn a14<T: Copy>(t: T) -> usize { a15(t) + b15(t) }
#[inline(never)] pub fn b14<T: Copy>(t: T) -> usize { a15(t) + b15(t) + 1 }
#[inline(never)] pub fn a15<T: Copy>(t: T) -> usize { a16(t) + b16(t) }
#[inline(never)] pub fn b15<T: Copy>(t: T) -> usize { a16(t) + b16(t) + 1 }
#[inline(never)] pub fn a16<T: Copy>(t: T) -> usize { a17(t) + b17(t) }
#[inline(never)] pub fn b16<T: Copy>(t: T) -> usize { a17(t) + b17(t) + 1 }
#[inline(never)] pub fn a17<T: Copy>(t: T) -> usize { a18(t) + b18(t) }
#[inline(never)] pub fn b17<T: Copy>(t: T) -> usize { a18(t) + b18(t) + 1 }
#[inline(never)] pub fn a18<T: Copy>(t: T) -> usize { a19(t) + b19(t) }
#[inline(never)] pub fn b18<T: Copy>(t: T) -> usize { a19(t) + b19(t) + 1 }
#[inline(never)] pub fn a19<T: Copy>(t: T) -> usize { a20(t) + b20(t) }
#[inline(never)] pub fn b19<T: Copy>(t: T) -> usize { a20(t) + b20(t) + 1 }
#[inline(never)] pub fn a20<T: Copy>(t: T) -> usize { std::mem::size_of_val(&t) }
#[inline(never)] pub fn b20<T: Copy>(t: T) -> usize { std::mem::size_of_val(&t) + 1 }
