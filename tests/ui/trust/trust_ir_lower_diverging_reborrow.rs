//@ dont-check-compiler-stderr
//@ check-pass
//@ compile-flags: -Ztrust-ir-lower -Ztrust-verify=off -Aprivate_bounds -Aprivate_interfaces
//@ edition: 2021
//! Trust (wave-DVB): `&*<diverging expr>` -- a reference-returning stub whose body is
//! `todo!()`/`unimplemented!()`, with rustc's reborrow adjustment wrapped around it.
//!
//! `lower_expr`'s `None` is OVERLOADED: it means either "I failed and recorded my own leaf tag"
//! or "I DIVERGED -- I emitted my terminator, sealed the block, and there is legitimately no
//! value". The second is the producer's own shipped `sealed => None` invariant, and the shared
//! `Borrow` arm was tagging both. The panic call lowers COMPLETELY and CORRECTLY and seals the
//! cursor, so the `Borrow(inner unlowered)` tag it then pushed was a pure echo of a divergence
//! that had already been handled.
//!
//! DECISIVE EVIDENCE, and the reason this is a misclassification rather than a widening: the
//! identical body WITHOUT the adjustment already ships clean. `fn plain(w: &W) -> &u32
//! { todo!() }` lowers `clean=true`, and its THIR is the same `NeverToAny { Call }` chain with
//! no `Borrow`/`Deref` wrapper. The producer already lowers this class end to end; this arm was
//! its sole refuser.
//!
//! ZERO IR DELTA: both branches of the arm `return None`. The module produced for these bodies
//! is byte-identical before and after -- the only observable difference is whether a diagnostic
//! string is appended -- so became-dirty is 0 by construction.
//!
//! Not under `=strict`: the negative pins below MUST keep their tags, which strict turns into
//! compile errors.

#![allow(dead_code)]

trait Error {
    type Span;
}
trait AsBufferView {
    type Device;
}

// THE LANE, shape 1 (the `implied-bounds-entailment-wf-vars` corpus body): an unnormalizable
// associated-type projection reached through a SECOND generic param is what makes rustc insert
// the reborrow adjustment. `todo!()`.
trait Foo {
    type Error: Error;
    fn foo(&self) -> &<Self::Error as Error>::Span;
}

impl<D: Error, VBuf0> Foo for VBuf0
where
    VBuf0: AsBufferView<Device = D>,
{
    type Error = D;
    fn foo(&self) -> &<Self::Error as Error>::Span {
        todo!()
    }
}

// THE LANE, shape 2 (the `deref-to-dyn-fn-mut-callable` corpus body): an UNSIZED associated
// target. `unimplemented!()`.
trait V4 {
    type T: ?Sized;
    fn g(&self) -> &Self::T;
}

struct F;

impl V4 for F {
    type T = dyn FnMut() + 'static;
    fn g(&self) -> &Self::T {
        unimplemented!()
    }
}

// The SHIPPED-CLEAN control: the same divergence with no adjustment. It lowered clean before
// this wave and must still.
struct W;

pub fn plain(_w: &W) -> &'static u32 {
    todo!()
}

// The NEGATIVE controls, which pin that the two gates are not vacuous. rustc does NOT insert
// the adjustment for the direct-self projection or the free-fn form, so these never reach the
// arm at all -- they are here so that a future change which starts routing them through it is
// visible as a diff rather than as a silent widening.
impl<D: Error> Foo2 for D {
    type E = D;
    fn f(&self) -> &<Self::E as Error>::Span {
        todo!()
    }
}

trait Foo2 {
    type E: Error;
    fn f(&self) -> &<Self::E as Error>::Span;
}

pub fn free_fn<D: Error>(_d: &D) -> &<D as Error>::Span {
    todo!()
}

fn main() {}
