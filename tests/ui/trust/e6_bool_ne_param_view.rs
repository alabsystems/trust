//@ needs-trust-verify
//@ revisions: unopt opt
//@ compile-flags: -Ztrust-verify=on
//@[opt] compile-flags: -O
//@ check-fail
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: HELP
//@ dont-require-annotations: ERROR
//@ normalize-stderr: "elapsed_ms=\d+" -> "elapsed_ms=$$TIME"
//! E6 expansion I1′ through the borrow-erased PARAMETER VIEW: `!=` over `bool`
//! FIELDS read through `&self` / `&T`.
//!
//! The view (`trust_types::e6_param_view`) rewrites `self.p != self.q` into a
//! body over by-value `bool` parameters `self.p`, `self.q`, and the UNCHANGED
//! `admit_function_into` runs on it — so since I1′ the E6-ONLY reader
//! `read_e6_body` reads view bodies too. rustc copies each field read into a
//! TEMPORARY and compares the temporaries (`_2 = copy ((*_1).0: bool);
//! _3 = copy ((*_1).1: bool); _0 = Ne(move _2, move _3)`, MEASURED at the
//! default level and at `-O` alike), so after the view's rewrite the reader
//! resolves single-assignment temporaries: the one live path that exercises
//! that resolution, since the by-value bodies the default and `-O` lanes
//! produce are already one statement. `docs/TCB.md`
//! (`EnsuresCitationViewDischarge`) discloses the reach; this fixture pins it.
//!
//! * POSITIVE: the right model discharges by definitional equality, and the
//!   row is graded through the VIEW (`view: frozen-shared-erased`), below
//!   `Certified` (owner ruling R1) — never counted as kernel-certified.
//! * NEGATIVE: the `==` model against a `!=` body, and models that name the
//!   wrong field or the wrong borrow, are refused by the KERNEL as not
//!   definitionally equal. A wrong reading of which temporary holds which field
//!   would make one of these discharge.

clean {
    def m_eq (a b : Bool) : Bool := a == b
    def m_ne (a b : Bool) : Bool := a != b
}

pub struct Flags {
    pub p: bool,
    pub q: bool,
}

impl Flags {
    pub fn differ(&self) -> bool
        ensures result == m_ne(self.p, self.q)
        //~^ NOTE island definition `m_ne` kernel-discharges this postcondition by definitional equality
    {
        self.p != self.q
    }

    pub fn differs_from(&self, o: bool) -> bool
        ensures result == m_ne(self.p, o)
        //~^ NOTE island definition `m_ne` kernel-discharges this postcondition by definitional equality
    {
        self.p != o
    }

    pub fn differ_against_eq(&self) -> bool
        ensures result == m_eq(self.p, self.q)
        //~^ ERROR the two sides are not definitionally equal
    {
        self.p != self.q
    }

    pub fn differ_wrong_field(&self) -> bool
        ensures result == m_ne(self.p, self.p)
        //~^ ERROR the two sides are not definitionally equal
    {
        self.p != self.q
    }

    pub fn differs_from_wrong_field(&self, o: bool) -> bool
        ensures result == m_ne(self.q, o)
        //~^ ERROR the two sides are not definitionally equal
    {
        self.p != o
    }
}

pub fn free_differ(f: &Flags) -> bool
    ensures result == m_ne(f.p, f.q)
    //~^ NOTE island definition `m_ne` kernel-discharges this postcondition by definitional equality
{
    f.p != f.q
}

pub fn two_borrows_swapped(f: &Flags, g: &Flags) -> bool
    ensures result == m_ne(g.p, f.q)
    //~^ ERROR the two sides are not definitionally equal
{
    f.p != g.q
}

fn main() {}
