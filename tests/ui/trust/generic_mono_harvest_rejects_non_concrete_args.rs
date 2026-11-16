//@ needs-trust-verify
//@ build-pass
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory
//@ dont-check-compiler-stderr
//@ dont-require-annotations: WARN

//! **Regression: the R1 per-monomorphization harvest must reject a "mono"
//! whose args still carry a const-generic PARAM — never normalize it.**
//!
//! MEASURED 2026-09-09 on `first-party/ty`'s vendored `clap_builder` (seal
//! trust-d3866677, advisory census): `thread 'rustc' panicked at
//! compiler/rustc_middle/src/ty/sty.rs:365` (`find_const_ty_from_env`) while
//! normalizing `<[(ContextKind, ContextValue); N] as IntoIterator>::IntoIter`.
//! `Error::extend_context_unchecked<const N>(self, context: [(K, V); N])`
//! forwards its array to `extend_unchecked(impl IntoIterator)`; the harvest
//! observed THAT generic callee with `I = [(K, V); N]` — `N` being the
//! CALLER's param — took it for a monomorphization, and
//! `try_instantiate_mir_and_normalize_erasing_regions` under the callee's
//! own typing env asked the trait solver for the type of a const it never
//! declared. An ICE, in a dependency crate, under every policy. The harvest
//! now declines (fail-closed: no flip) when a mono's args are not concrete.

struct Ctx(Vec<(u8, u8)>);

impl Ctx {
    fn extend_unchecked(&mut self, iter: impl IntoIterator<Item = (u8, u8)>) {
        for (k, v) in iter {
            self.0.push((k, v));
        }
        let n = self.0.len();
        if n > 0 {
            let _ = self.0[n - 1];
        }
    }
}

struct Error {
    ctx: Ctx,
}

impl Error {
    #[inline(never)]
    fn extend_context_unchecked<const N: usize>(mut self, context: [(u8, u8); N]) -> Self {
        self.ctx.extend_unchecked(context);
        self
    }
}

fn main() {
    let e = Error { ctx: Ctx(Vec::new()) };
    let e = e.extend_context_unchecked([(1, 2)]);
    let e = e.extend_context_unchecked([(3, 4), (5, 6)]);
    assert_eq!(e.ctx.0.len(), 3);
}
