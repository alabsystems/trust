#![crate_type = "lib"]
#![feature(contracts)]
#![allow(incomplete_features)]
#[core::contracts::requires(x > 0)]
pub fn pre(x: i32) -> i32 { x + 100 }

#[core::contracts::requires(x > 0)]
#[core::contracts::ensures(move |r: &i32| *r > 0)]
pub fn both(x: i32) -> i32 { x + 1 }
