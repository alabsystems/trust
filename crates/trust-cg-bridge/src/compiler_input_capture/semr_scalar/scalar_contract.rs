// Copyright 2026 Andrew Yates | Apache-2.0
//! One fixed scalar artifact contract shared by capture and production replay.
//! These names select mathematics, never a compiler grade or model chosen by a packet.

pub(super) const SCHEMA: &str = "trust.canonical-semr-scalar-cohort.v2";
pub(super) const ROOT_MODULES: [&str; 2] = ["U64AdditionConsumer", "U64ScalarProfile"];
pub(super) const ROOTS: [&str; 15] = [
    "SemRU64AdditionConsumer.Decodes",
    "SemRU64AdditionConsumer.Returns",
    "SemRU64AdditionConsumer.NoBad",
    "SemRU64AdditionConsumer.original_decoded",
    "SemRU64AdditionConsumer.original_returns",
    "SemRU64AdditionConsumer.original_no_bad",
    "SemRU64ScalarProfile.Decodes",
    "SemRU64ScalarProfile.Returns",
    "SemRU64ScalarProfile.NoBad",
    "SemRU64ScalarProfile.accepts",
    "SemRU64ScalarProfile.classify_exact",
    "SemRU64ScalarProfile.decoded_module",
    "SemRU64ScalarProfile.decode_profile",
    "SemRU64ScalarProfile.returns",
    "SemRU64ScalarProfile.no_bad",
];
