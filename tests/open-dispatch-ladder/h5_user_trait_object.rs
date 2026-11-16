//@ trust-ladder: refuses
//! `fmt` removed entirely. A two-line user trait reproduces the class, which is
//! why "derive(Debug)" and "open dispatch" are ONE item and not two.
pub trait T { fn m(&self) -> u32; }
pub fn f(x: &dyn T) -> u32 { x.m() }
