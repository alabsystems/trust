#![feature(contracts)]
#![allow(internal_features, incomplete_features, unused, dead_code)]

// ay-proof-common/src/literal.rs, verbatim bodies.
#[derive(Clone, Copy, PartialEq, Eq)] pub struct Variable(u32);
#[derive(Clone, Copy, PartialEq, Eq)] #[repr(transparent)] pub struct Literal(u32);

/// `Literal::positive` — the real body (`<< 1`, no overflow assert), with the
/// CALL-FREE statement of what its rustdoc promises. The clause spells the
/// shift as `* 2`: in the declared-width reading those are the same u32
/// function, so this is not the body copied back as its own specification.
#[core::contracts::ensures(move |ret: &Literal| ret.0 == var.0 * 2)]
pub fn positive(var: Variable) -> Literal { Literal(var.0 << 1) }

/// The DISCRIMINATOR: true of every literal `positive` can return, and not a
/// logical tautology. `2v` and `2v+1` differ by one in every `u32`.
#[core::contracts::ensures(move |ret: &Literal| ret.0 != var.0 * 2 + 1)]
pub fn positive_discriminator(var: Variable) -> Literal { Literal(var.0 << 1) }

/// `Literal::negative` — the odd encoding. The same discriminator, flipped.
#[core::contracts::ensures(move |ret: &Literal| ret.0 != var.0 * 2)]
pub fn negative_discriminator(var: Variable) -> Literal { Literal((var.0 << 1) | 1) }

/// MUTANT of `positive`: claims the NEGATIVE encoding. Must be refuted.
#[core::contracts::ensures(move |ret: &Literal| ret.0 == var.0 * 2 + 1)]
pub fn positive_mutant(var: Variable) -> Literal { Literal(var.0 << 1) }
