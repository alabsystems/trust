//@ needs-trust-verify
//@ revisions: off on
//@[off] compile-flags: -Ztrust-verify=off
//@[on] compile-flags: -Ztrust-verify=on
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! An import-only island cannot silently accept an ineligible reference base.
//! Mathlib's stand-in installs structural IsClosed; no proof or grade may waive
//! the base check. The rejection is mandatory in both ordinary build modes.

// The refusal is anchored on the `import` that installs the stand-in. The
// annotation sits outside the island, whose text belongs to the Clean parser.
clean {
    import Mathlib
}
//~^^ ERROR reference base refused

fn main() {}
