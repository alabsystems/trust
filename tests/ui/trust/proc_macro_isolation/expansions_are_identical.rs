//@ only-apple
//@ edition: 2021
//@ run-pass
//! Trust (D21): the expected expansions of the serde-shaped and thiserror-shaped
//! derives are the same bytes for in-process and isolated expansion. The two
//! `*_expands_identically.rs` tests each compare a revision with its own file;
//! this is what makes the pair a comparison with each other. Blessing one
//! revision's file away from the other fails here.

fn main() {
    for (shape, in_process, isolated) in [
        (
            "serde-shaped",
            include_str!("serde_shaped_derive_expands_identically.in_process.stdout"),
            include_str!("serde_shaped_derive_expands_identically.isolated.stdout"),
        ),
        (
            "thiserror-shaped",
            include_str!("thiserror_shaped_derive_expands_identically.in_process.stdout"),
            include_str!("thiserror_shaped_derive_expands_identically.isolated.stdout"),
        ),
    ] {
        assert!(in_process.contains("impl"), "{shape}: the expansion holds no impl");
        assert_eq!(in_process, isolated, "{shape}: isolated expansion differs from in-process");
    }
}
