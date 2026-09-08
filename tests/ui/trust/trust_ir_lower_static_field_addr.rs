//@ check-pass
//@ compile-flags: -Ztrust-ir-lower -Ztrust-verify=off
// wave-SF: a shared borrow of a STATIC'S FIELD lowers as an interior GEP off the
// static's GlobalAddr — not as a snapshot into a stack slot, whose address the
// tail guard rightly refuses to return. Covers both the direct spelling `&A.f`
// and the `*&place ≡ place` reborrow wrapper `&*(&A.f)` that the `&'static`
// coercion path produces (issue-17718 shape).

pub struct P {
    pub a: usize,
    pub b: usize,
}

pub static A: P = P { a: 3, b: 7 };

// direct: Field{Deref{StaticRef}}
pub fn direct() -> &'static usize {
    &A.b
}

// wrapper: Borrow{Deref{Borrow{Field{Deref{StaticRef}}}}} via the &'static coercion
pub static B: &'static usize = &A.a;

pub fn through_wrapper() -> usize {
    *B + *direct()
}

fn main() {}
