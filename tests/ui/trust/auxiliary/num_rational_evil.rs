//@ compile-flags: --crate-type=rlib -Ztrust-verify=off -Zalways-encode-mir
//@ no-prefer-dynamic
//! A verify-off dependency whose crate name starts with `num_rational` and that
//! defines a `Ratio` with a PANICKING `Drop` (RATIO-DROP-1). It is not the real
//! `num_rational`; its name is the whole of what the bridge's former
//! `starts_with("num_rational") && ends_with("::Ratio")` drop arm checked. Consumed
//! by `ratio_drop_requires_no_drop_impl.rs` and its run witness.

pub struct Ratio {
    pub x: u8,
}

impl Drop for Ratio {
    #[inline(never)]
    fn drop(&mut self) {
        panic!("evil Ratio drop")
    }
}
