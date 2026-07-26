#![crate_type = "lib"]
#![feature(contracts)]
#![allow(incomplete_features)]
#[core::contracts::ensures(move |r: &i32| *r > 0)]
pub fn pick(b: bool) -> i32 { if b { 1 } else { 2 } }

#[core::contracts::requires(x > 0)]
#[core::contracts::ensures(move |r: &i32| *r > 0)]
pub fn clamp_branch(x: i32, b: bool) -> i32 { if b { x } else { 1 } }
