// String interning for Formula variable names.
//
// The Symbol/Interner definitions now live in `trust-ir-contract` (the leaf
// crate shared across the Trust <-> backend boundary). This module re-exports
// them verbatim so every `trust_types::Symbol` / `trust_types::interner::*`
// path is unchanged.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

pub use trust_ir_contract::interner::{Interner, Symbol};
