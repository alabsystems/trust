//@ dont-check-compiler-stderr
//@ compile-flags: -Ztrust-ir-lower=strict -Ztrust-verify=on -Ztrust-policy=advisory
//@ needs-trust-verify
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE
//! Trust (wave-FI): a FUNCTION ITEM passed as a call argument — the
//! `ExprKind::ZstLiteral` of `ty::FnDef` type that `thread_local!`'s
//! `get_or_init(init, __rust_std_internal_init_fn)` feeds a generic `F` —
//! lowers as the ZST `(Unit, PhantomData)` stand-in the wave-ZC closure lane
//! ships, under the same `zst_closure_arg` splice/seam refusal. Three shapes,
//! all under `strict` so a regression is a compile error, not a sidecar row:
//! a monomorphic parent (layout query available), a GENERIC parent (the query
//! refuses the parent-param-carrying `FnDef`; the structural fallback covers
//! exactly that case), and a tuple-struct CONSTRUCTOR used as the callable.
//! A reified fn POINTER (`take_ptr(init_fn)`) is a `PointerCoercion` wrapper
//! and is deliberately NOT this lane — it stays a real value.
//!
//! SOURCE ABI (EXACT-THIR-ABI-1, 51558bd9ff): the callees `apply` and `build` call their `F`
//! through the generic `FnOnce::call_once` havoc callee, declared `extern "rust-call"`, which
//! has no IR convention until a real tuple adapter exists, so the producer refuses both at the
//! callee (expected below). The CALLERS `main` and `generic_parent` carry all three ZST
//! stand-in shapes this file is about and stay unannotated, so a producer tag on either is
//! still its own strict error: this file keeps its mutation check. Strict's per-body errors
//! end the compile at the analysis error gate, before D28 runs, so `generic_parent`'s D28
//! refusal (`Abstracted(drop, ..)` of its by-value `T`) is no longer reached here; it is
//! still measured without strict.

fn init_fn() -> u32 {
    41
}

fn apply<F: FnOnce() -> u32>(f: F) -> u32 {
    //~^ ERROR the direct trust-ir producer could not fully lower this body (2 unsupported shape(s)): Callee(foreign-ABI repr(Rust) struct by value) at std::ops::FnOnce::call_once; Callee(unsupported source ABI) at callee
    f() + 1
}

fn generic_parent<T>(_t: T) -> u32 {
    apply(init_fn)
}

struct Wrap(u32);

fn build<F: FnOnce(u32) -> Wrap>(f: F) -> u32 {
    //~^ ERROR the direct trust-ir producer could not fully lower this body (2 unsupported shape(s)): Callee(foreign-ABI repr(Rust) struct by value) at std::ops::FnOnce::call_once; Callee(unsupported source ABI) at callee
    f(42).0
}

fn main() {
    if apply(init_fn) != 42 {
        std::process::exit(1);
    }
    if generic_parent(0u8) != 42 {
        std::process::exit(2);
    }
    if build(Wrap) != 42 {
        std::process::exit(3);
    }
}
