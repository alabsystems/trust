//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-pass
#![crate_type = "lib"]
//! A call that RESOLVES to a summarized body keeps its summary. The twin of
//! `summary_needs_a_resolved_call_refused.rs`. (A concrete call through a blanket
//! impl, `Bar.m(x)` with `Bar: Marker`, is not summarized at all, on this build and
//! on the 2026-09-17 pack alike: its rendering is not the blanket body's def path.)
//!
//! A concrete call to a trait impl's method names the TRAIT item, so its summary is
//! registered for exactly the identity such a call carries: the trait item at the
//! impl's own trait-reference arguments (`SummaryBodyIdentity::Instance`, round 7 of
//! the review; `summary_needs_the_summarized_body_refused.rs` is that twin). Those
//! arguments are normalized first, as the call's are: a header that names a const
//! item, a const expression or a projection keeps its summary (round 8).

#[inline(never)]
fn clamp_index(x: usize) -> usize {
    x.min(3)
}

#[inline(never)]
fn at_least_one(g: u32) -> u32 {
    g.max(1)
}

pub fn plain_helper(x: usize, a: &[u8; 4]) -> u8 {
    a[clamp_index(x)]
}

pub fn lower_bound_helper(h: u32, g: u32) -> u32 {
    h % at_least_one(g)
}

pub trait Clamp {
    fn clamp_to(&self, x: usize) -> usize;
    fn den(&self, g: u32) -> u32;
}

pub struct Four;

impl Clamp for Four {
    #[inline(never)]
    fn clamp_to(&self, x: usize) -> usize {
        x.min(3)
    }
    #[inline(never)]
    fn den(&self, g: u32) -> u32 {
        g.max(1)
    }
}

pub fn trait_impl_helper(x: usize, a: &[u8; 4]) -> u8 {
    a[Four.clamp_to(x)]
}

pub fn trait_impl_lower_bound(h: u32, g: u32) -> u32 {
    h % Four.den(g)
}

pub const N: usize = 4;

impl Clamp for [u8; N] {
    #[inline(never)]
    fn clamp_to(&self, x: usize) -> usize {
        x.min(3)
    }
    #[inline(never)]
    fn den(&self, g: u32) -> u32 {
        g.max(1)
    }
}

pub fn header_names_a_const_item(h: u32, g: u32, a: [u8; 4]) -> u32 {
    h % a.den(g)
}

impl Clamp for [u16; 2 + 2] {
    #[inline(never)]
    fn clamp_to(&self, x: usize) -> usize {
        x.min(3)
    }
    #[inline(never)]
    fn den(&self, g: u32) -> u32 {
        g.max(1)
    }
}

pub fn header_names_a_const_expression(h: u32, g: u32, a: [u16; 4]) -> u32 {
    h % a.den(g)
}

pub trait Id {
    type Out;
}

impl Id for u8 {
    type Out = u8;
}

pub struct W<T>(pub T);

impl Clamp for W<<u8 as Id>::Out> {
    #[inline(never)]
    fn clamp_to(&self, x: usize) -> usize {
        x.min(3)
    }
    #[inline(never)]
    fn den(&self, g: u32) -> u32 {
        g.max(1)
    }
}

pub fn header_names_a_projection(x: usize, a: &[u8; 4]) -> u8 {
    a[W(0u8).clamp_to(x)]
}
