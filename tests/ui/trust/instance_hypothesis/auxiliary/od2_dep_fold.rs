//@ compile-flags: --crate-type=rlib -Ztrust-verify=off -Zalways-encode-mir
//@ edition: 2021
//@ no-prefer-dynamic
//! OD-1 phase 2 review fix (2026-10-05): a default method that dispatches on
//! `Self` (the `ExprFold::fold_box` shape). `run::<Q>`'s site resolves to the
//! default body `<Q as Fold>::wrap`, which is itself a dependency generic with a
//! site of its own.

pub trait Fold {
    fn wrap(&self, x: u32) -> u32 {
        self.leaf(x)
    }
    fn leaf(&self, x: u32) -> u32;
}

pub fn run<Q: Fold>(q: &Q) -> u32 {
    q.wrap(1)
}
