// trust_vcgen/binary_analysis/mod.rs: Binary analysis pipeline
//
// Binary lifting into trust-types MIR (`lifter`), CFG reconstruction from a
// linear instruction stream (`cfg_reconstruct`), the lowering helpers they
// share (`lowering`), and the compiled-binary relift verification API
// (`relift`). Consumers name the submodule they use; nothing is re-exported
// from here.
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
