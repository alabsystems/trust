//@ edition: 2021
//@ compile-flags: --crate-type=rlib -O -Ztrust-verify=off -A warnings
//@ no-prefer-dynamic
//! A dependency of `r6_rob_f7_erase_fixpoint_walk_per_link_via_env_mask.rs`
//! (review 6 of the review-14 build): traits, and fns that box a value as a
//! `dyn` of one of them. Safe and sound.
#![forbid(unsafe_code)]
pub trait Src { type Item; }
pub trait T0 {}
pub trait T1 {}
pub trait T2 {}
pub trait T3 {}
pub fn box_1<X: T1 + 'static>(x: X) -> Box<dyn T1> { Box::new(x) }
pub fn box_2<X: T2 + 'static>(x: X) -> Box<dyn T2> { Box::new(x) }
pub fn box_3<X: T3 + 'static>(x: X) -> Box<dyn T3> { Box::new(x) }
