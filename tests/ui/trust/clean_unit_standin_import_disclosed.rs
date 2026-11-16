//@ needs-trust-verify
//@ check-pass
//@ compile-flags: -Z trust-verify=off
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//! **GREEN THAT LIES — the `clean mod` UNIT half of
//! `clean_island_standin_import_disclosed.rs`.**
//!
//! This is the shape the hazard actually arrives in: an existing `.lean` file
//! that begins `import Lean`, named from Rust with `clean mod …;`. The unit
//! shares the island's parse, batch and reporting (I8: a unit and an inline
//! island must produce identical graph entries), so it must disclose the
//! stand-in exactly as the island does. The note lands inside the `.lean`
//! file, which carries no compiletest annotations of its own, so the
//! expectation below is the file-less form (a tilde-question annotation).
//! (Spelling that form in prose would make compiletest parse a second,
//! unsatisfiable expectation out of this comment — measured 2026-09-17.)

clean mod clean_unit_standin_import_helper;

fn main() {
    let _ = crate::unit_six();
}

//~? NOTE `import Lean` was served by Clean's built-in prelude stand-in, NOT by the library of that name
