// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0
//
//! `trust_certify::reducer_universal_composition` exists only under `cfg(test)`.
//!
//! Its fixture loader reads the committed real-MIR fixtures from the source tree
//! at run time through `env!("CARGO_MANIFEST_DIR")`. A library build that
//! included it would compile this checkout's absolute path into the stage-1
//! compiler that links trust-certify, and a stage 1 cloned into another worktree
//! (EW-9, `src/bootstrap/src/utils/trust_stage1_seed.rs`) would then have to
//! rebuild the crate and everything that depends on it. The module is a
//! non-authoritative validation artifact with no caller outside its own tests,
//! so it is compiled only into this crate's unit-test binary.
//!
//! An integration test links the library as the compiler does: without
//! `cfg(test)`. This file checks that build's public surface by name
//! resolution. `reducer_universal_composition` below is glob-imported from both
//! `stand_in` and `trust_certify`. While the library does not export the
//! module, only the stand-in provides the name, and this file compiles and
//! passes. If the library exports it again (a `pub mod` without the gate, or a
//! re-export), the two glob imports name different modules and the use below is
//! ambiguous (E0659): this test target then fails to build.

use stand_in::*;
#[allow(unused_imports)]
use trust_certify::*;

mod stand_in {
    /// Stands in for the gated module; only this one may answer to the name.
    pub mod reducer_universal_composition {
        pub fn path() -> &'static str {
            module_path!()
        }
    }
}

#[test]
fn the_library_exports_no_reducer_universal_composition_outside_cfg_test() {
    // Resolving at all proves the library does not export the name (see the
    // module docs); the value names the module that answered.
    let answered = reducer_universal_composition::path();
    assert!(answered.ends_with("::stand_in::reducer_universal_composition"), "{answered}");
}
