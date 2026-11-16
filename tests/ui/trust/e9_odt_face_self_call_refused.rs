//@ needs-trust-verify
//@ revisions: on off
//@[on] compile-flags: -Ztrust-verify=on
//@[off] compile-flags: -Ztrust-verify=off
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: ERROR
//! E9-ODT-FACE-SELF-CALL-1, REFUSED ROWS. The contracted function's own call,
//! spelled with its exact self key (`<crate>::<fn>`), is rebuilt over TG11's
//! nominal ODT import through the face constructor only when its rows are the
//! struct's fields in declaration order, one row per field. Each function here
//! breaks that once and each must stay a hard citation error.
//!
//! * `swapped` — the rows are the struct's two fields the other way round.
//!   The bridge refuses a reordered author-written self-call conservatively:
//!   its positional reading would be sound (it is what the in-walk lane's
//!   flattened import gives it), but the post-walk lanes give it no meaning
//!   rather than an order-only one. The hazard an order-only rebuild WOULD
//!   carry is the synthesized substitute for `result`, which cannot be swapped
//!   from source (the clause side and the face both walk the declaration); the
//!   unit tests pin that.
//! * `too_few` — one row for a two-field struct.
//! * `too_many` — three rows for a two-field struct.
//!
//! The primary ERROR of each is the ∀-`result` fallback's refusal, which never
//! installs the self key and so still applies the arity or carrier gate. The
//! rebuild's own refusal, by name or by count, is carried by the child NOTE
//! that reads the clause as a postcondition; before the fix that note restated
//! the arity refusal, so each NOTE pin is red without the fix.
//!
//! `dont-require-annotations: ERROR` tolerates only the secondary
//! strict-verification errors of the `on` revision; each primary refusal and
//! its note are pinned explicitly in both revisions.

clean {
    theorem fst_refl : forall (d : UInt64) (k : UInt64), d = d := fun d k => rfl
    theorem snd_refl : forall (d : UInt64) (k : UInt64), k = k := fun d k => rfl
}

pub struct Cst {
    pub degree: u64,
    pub coeff: u64,
}

pub fn swapped(c: Cst) -> u64
    ensures e9_odt_face_self_call_refused::swapped(c.coeff, c.degree) == c.coeff by snd_refl
    //~^ ERROR citation `snd_refl` cannot be validated because this clause is outside the exact statement fragment
    //~| NOTE `c.coeff` does not fill field slot 0 of parameter 0, whose registered field is `degree`
{
    c.degree
}

pub fn too_few(c: Cst) -> u64
    ensures e9_odt_face_self_call_refused::too_few(c.degree) == c.degree by fst_refl
    //~^ ERROR citation `fst_refl` cannot be validated because this clause is outside the exact statement fragment
    //~| NOTE parameter 0 needs 2 field row(s) and 1 remain
{
    c.degree
}

pub fn too_many(c: Cst) -> u64
    ensures e9_odt_face_self_call_refused::too_many(c.degree, c.coeff, c.degree) == c.degree
        by fst_refl
    //~^ ERROR citation `fst_refl` cannot be validated because this clause is outside the exact statement fragment
    //~| NOTE 1 row(s) are left over
{
    c.degree
}

fn main() {}
