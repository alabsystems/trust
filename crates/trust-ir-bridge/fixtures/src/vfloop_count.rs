#![crate_type = "lib"]
#![feature(contracts)]
#![allow(incomplete_features)]
#[core::contracts::ensures(move |r: &u32| *r >= 0)]
pub fn count(n: u32) -> u32 {
    let mut c = 0u32;
    let mut i = 0u32;
    while i < n {
        c = c.wrapping_add(1);
        i = i.wrapping_add(1);
    }
    c
}
