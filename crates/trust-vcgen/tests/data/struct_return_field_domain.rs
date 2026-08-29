#![feature(contracts)]
#![allow(internal_features, incomplete_features, unused, dead_code)]

// ay-proof-common's real shapes: two single-u32 tuple structs.
#[derive(Clone, Copy)] pub struct Variable(pub u32);
#[derive(Clone, Copy)] #[repr(transparent)] pub struct Literal(pub u32);

/// `Literal::positive` written as a FIRST-CLASS, CALL-FREE postcondition:
/// the encoding relation itself, not `result.variable() == var`.
#[core::contracts::ensures(move |ret: &Literal| ret.0 == var.0 * 2)]
pub fn positive(var: Variable) -> Literal { Literal(var.0 * 2) }

/// MUTANT: the negative encoding. Must NOT prove.
#[core::contracts::ensures(move |ret: &Literal| ret.0 == var.0 * 2 + 1)]
pub fn positive_mutant(var: Variable) -> Literal { Literal(var.0 * 2) }

/// VACUITY: a logical tautology over the return field.
#[core::contracts::ensures(move |ret: &Literal| ret.0 == ret.0)]
pub fn vac_reflexive(var: Variable) -> Literal { Literal(var.0 * 2) }

/// VACUITY: a predicate true of EVERY u32 but not a logical tautology.
#[core::contracts::ensures(move |ret: &Literal| ret.0 + 0 == ret.0)]
pub fn vac_typewide(var: Variable) -> Literal { Literal(var.0 * 2) }

/// Heterogeneous field widths — the width-mixup vector.
pub struct Packed(pub u8, pub u32);
#[core::contracts::ensures(move |ret: &Packed| ret.1 == x + 1)]
pub fn packed_second(b: u8, x: u32) -> Packed { Packed(b, x + 1) }

/// UNION field: fields alias at offset 0. Must stay refused.
pub union U { a: u32, b: u32 }
#[core::contracts::ensures(move |ret: &u32| *ret == x + 1)]
pub fn union_read(u: U, x: u32) -> u32 { x + 1 }
