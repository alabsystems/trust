//@ compile-flags: --crate-type=rlib -Ztrust-verify=off -Zalways-encode-mir -C metadata=aux
//@ no-prefer-dynamic
//! ARGS-FINGERPRINT-READ-1: a verify-off dependency whose crate NAME is its
//! consumer's (`args_fingerprint_full_range`), so the consumer's crate graph holds a
//! duplicate crate name, as Cargo's bin+lib layout or two semver versions of one
//! crate do. That is all it is for: in such a graph the extractor appended the
//! argument fingerprint `::<__trust_args@HEX>` to every generic callee
//! (DROP-NAME-COLLIDE-1); since ARGS-FINGERPRINT-READ-1 round 2 only to a call
//! whose arguments name a crate whose name does not identify it.
//! `-C metadata=aux` gives it its own `StableCrateId`.
pub fn id(x: u32) -> u32 {
    x
}
