#![feature(contracts)]
#![allow(internal_features)]
#![allow(incomplete_features)]
#![allow(unused)]

// NESTED loop: t is untouched by BOTH the inner and outer loops, so t == 0 (>= 0)
// survives both. ensures ret >= 0.
#[core::contracts::ensures(move |ret: &u32| *ret >= 0)]
pub fn nested(n: u32) -> u32 {
    let t: u32 = 0;
    let mut i: u32 = 0;
    while i < n {
        let mut j: u32 = 0;
        while j < n {
            j = j + 1;
        }
        i = i + 1;
    }
    t
}
