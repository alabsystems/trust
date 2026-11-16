// Copyright 2026 Andrew Yates | Apache-2.0
//! The separately owned program extension has its own fixed identity and proof roots.

pub(super) const MODEL_IR: &str = "5525be7f66db71509025ff62e89df4ef3277c829";
pub(super) const SCHEMA: &str = "trust.canonical-semr-scalar-program-cohort.v1";
pub(super) const ROOT_MODULE: &str = "MiniRustU64ProgramFromBytes";
pub(super) const ROOTS: [&str; 8] = [
    "MiniRustU64ProgramFromBytes.Construction",
    "MiniRustU64ProgramFromBytes.Correspondence",
    "MiniRustU64ProgramFromBytes.Available",
    "MiniRustU64ProgramFromBytes.construction",
    "MiniRustU64ProgramFromBytes.correspondence",
    "MiniRustU64ProgramFromBytes.available",
    "MiniRustU64ProgramFromBytes.literal_valid",
    "SemRU64ScalarProfile.decode_profile",
];
