// trust_vcgen/binary_analysis/mod.rs: Binary analysis pipeline
//
// Refactors binary pattern detection/type recovery into a module directory and
// adds binary lifting, CFG reconstruction, P-code translation, and CFGFast
// function recovery utilities.
//
// Part of #148: Binary analysis pipeline
// Part of #101: Binary Lifting
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

mod lowering;
pub(crate) mod relift;

pub(crate) mod cfg_reconstruct;
pub(crate) mod lifter;
// type_recovery.rs deleted — all items dead code (no callers).
// patterns.rs deleted — all items dead code (only used by deleted security_vcs.rs).

#[allow(unused_imports)]
pub(crate) use cfg_reconstruct::*;
#[allow(unused_imports)]
pub(crate) use lifter::*;
#[allow(unused_imports)]
pub(crate) use relift::*;
