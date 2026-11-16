//! A DEPENDENCY built the way dependencies are built: `-Ztrust-verify=off`.
//! That is not an exotic setting — it is the default for deps, and the SYSROOT
//! itself is built with it (`TRUST_BOOTSTRAP_NO_VERIFY_FLAG`,
//! src/bootstrap/src/core/builder/cargo.rs). So `boom` is never verified
//! anywhere, and its address escapes as a plain `fn()`.
#![crate_name = "dep"]
pub fn boom() { panic!("dependency panicked through a fn pointer"); }
pub static F: fn() = boom;
