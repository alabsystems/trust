//@ compile-flags: --crate-type=rlib -Ztrust-verify=off
//@ no-prefer-dynamic
//! A verify-off dependency whose crate name the test crate ALSO takes, with a type
//! `S` rendering to the same path as the test crate's own no-`Drop` `S`. This `S`'s
//! `Drop` panics. See `drop_credit_shared_crate_name.rs`.
pub struct S(pub u32);
impl Drop for S {
    fn drop(&mut self) {
        if self.0 == 7 {
            panic!("shared-name S dropped");
        }
    }
}
