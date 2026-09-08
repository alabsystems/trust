//@ dont-check-compiler-stderr
//@ check-pass
//@ compile-flags: -Ztrust-ir-lower=strict -Ztrust-verify=off
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

fn init_fn() -> u32 {
    41
}

fn apply<F: FnOnce() -> u32>(f: F) -> u32 {
    f() + 1
}

fn generic_parent<T>(_t: T) -> u32 {
    apply(init_fn)
}

struct Wrap(u32);

fn build<F: FnOnce(u32) -> Wrap>(f: F) -> u32 {
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
