//@ compile-flags: --crate-type=rlib -Ztrust-verify=off -Zalways-encode-mir
//@ no-prefer-dynamic
//! ARGS-FINGERPRINT-READ-1 round 2: a verify-off dependency built under the crate
//! NAME `core` (its file stem), so `fakecore::ops::range::RangeFull` renders exactly
//! as the real `core::ops::range::RangeFull` does. Its `RangeBounds` impl starts at
//! 1000, so `Vec::drain` over it panics on any shorter vec.
pub mod ops {
    pub mod range {
        use std::ops::{Bound, RangeBounds};
        #[derive(Clone, Copy)]
        pub struct RangeFull;
        impl RangeBounds<usize> for RangeFull {
            fn start_bound(&self) -> Bound<&usize> {
                Bound::Included(&1000)
            }
            fn end_bound(&self) -> Bound<&usize> {
                Bound::Unbounded
            }
        }
    }
}
