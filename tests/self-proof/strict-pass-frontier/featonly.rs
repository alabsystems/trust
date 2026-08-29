#![no_std]
#![expect(incomplete_features)]
#![feature(contracts)]
//! ONE-VARIABLE CONTROL that ens.rs/req.rs lack: the feature gate and the
//! import, but NO contract clause. If this already fails, the attribution of
//! the ens/req failures to "the clause" is wrong.
#[allow(unused_imports)]
use core::contracts::{ensures, requires};

pub fn udiv_guarded(n: u32, d: u32) -> u32 {
    if d == 0 { return 0; }
    n / d
}
