//@ compile-flags: --crate-type=rlib -Ztrust-verify=off -Cmetadata=stamped-genuine-core-aux
//@ no-prefer-dynamic
//! A SECOND crate named `core` (its file name makes its crate name `core`), built
//! verify-off the way Targo compiles every dependency unit. It is not an impostor
//! of anything the consumer calls: the consumer never names it. Its presence alone
//! makes the crate name `core` ambiguous, so the extractor stamps the GENUINE core's
//! paths (`__trust_crate@<stable crate id>::core::…`, rule 1 of
//! `trust_types::sysroot_identity_stamp_required`), which is what
//! `stamped_genuine_core_rows_kept.rs` needs.
pub fn hello() -> u32 {
    7
}
