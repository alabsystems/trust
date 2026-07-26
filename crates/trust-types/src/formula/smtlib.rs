// trust-types/formula/smtlib: SMT-LIB2 text serialization for Formula
//
// `Formula::to_smtlib` and `escape_smtlib_symbol` now live in
// `trust-ir-contract` alongside the `Formula` definition. This module
// re-exports `escape_smtlib_symbol` so `trust_types::escape_smtlib_symbol`
// (and the `formula::*` glob) is unchanged; `Formula::to_smtlib` rides along
// with the re-exported `Formula` type.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

pub use trust_ir_contract::escape_smtlib_symbol;
