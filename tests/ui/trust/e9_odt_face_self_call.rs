//@ needs-trust-verify
//@ revisions: on off
//@[on] compile-flags: -Ztrust-verify=on
//@[off] compile-flags: -Ztrust-verify=off
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//! E9-ODT-FACE-SELF-CALL-1, POSITIVE. A cited `ensures` over a by-value
//! struct's flattened field rows (`b.degree`, `c.coeff`) is graded by the
//! post-walk citation sweep against TG11's NOMINAL ODT import, whose parameter
//! is the struct itself. The self-call that stands for `result` is rebuilt
//! through the face constructor, `trust_import_f (TrustOdt.k….mk b.degree
//! b.coeff)`, each field slot checked by its registered field name.
//!
//! `e9_field_projection_discharge` is the one-struct case. This fixture adds
//! the two shapes the rebuild must keep in order: two struct parameters (four
//! rows, the projected one third), and a scalar parameter before a struct
//! (three rows), plus a struct with a signed and a `bool` field. `off` is the
//! TG3 lane, where the ODT import is the only one: before this fix every note
//! below was a hard "has arity K but is applied to N argument(s)" error there
//! (K = 2, 2, 1 for `second_degree`, `mixed` and `offset`).
//!
//! The close negatives are `e9_odt_face_self_call_mutant` (a body that returns
//! the other field) and `e9_odt_face_self_call_refused` (swapped and
//! wrongly-counted rows).

clean {
    theorem b_degree_refl : forall (a0 : UInt64) (a1 : UInt64) (b0 : UInt64) (b1 : UInt64),
        b0 = b0 := fun a0 a1 b0 b1 => rfl
    theorem coeff_refl : forall (n : UInt64) (d : UInt64) (k : UInt64), k = k :=
        fun n d k => rfl
    theorem off_refl : forall (o : BitVec 64) (l : Bool), o = o := fun o l => rfl
}

pub struct Cst {
    pub degree: u64,
    pub coeff: u64,
}

pub struct Off {
    pub off: i64,
    pub live: bool,
}

#[allow(unused_variables)]
pub fn second_degree(a: Cst, b: Cst) -> u64
    ensures result == b.degree by b_degree_refl
    //~^ NOTE citation `b_degree_refl` kernel-discharges this postcondition statement
{
    b.degree
}

#[allow(unused_variables)]
pub fn mixed(n: u64, c: Cst) -> u64
    ensures result == c.coeff by coeff_refl
    //~^ NOTE citation `coeff_refl` kernel-discharges this postcondition statement
{
    c.coeff
}

pub fn offset(s: Off) -> i64
    ensures result == s.off by off_refl
    //~^ NOTE citation `off_refl` kernel-discharges this postcondition statement
{
    s.off
}

fn main() {}
