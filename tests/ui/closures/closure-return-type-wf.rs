// Regression test for rust-lang#151637: Closure return value WF not checked.
//
// Previously, the compiler did not check well-formedness of closure return types.
// This meant a closure could return a value whose type violates trait bounds
// without the compiler catching it. The fix adds a WF obligation for the closure
// return type in check_fn (compiler/rustc_hir_typeck/src/check.rs).
// Trust: soundness fix

trait Bound {}

struct NeedsBound<T: Bound>(T);

// The closure's return type NeedsBound<u32> should be checked for WF,
// which requires u32: Bound. This must be rejected.
fn constrain_return<T, F: FnOnce() -> NeedsBound<T>>(_: T, _: F) {}
//~^ ERROR the trait bound `T: Bound` is not satisfied

fn main() {
    constrain_return(1u32, || NeedsBound(1u32));
    //~^ ERROR the trait bound `u32: Bound` is not satisfied
    //~| ERROR the trait bound `u32: Bound` is not satisfied
}
