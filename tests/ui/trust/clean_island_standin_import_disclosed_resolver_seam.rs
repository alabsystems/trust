//@ needs-trust-verify
//@ check-fail
//@ compile-flags: -Z trust-verify=off
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//! **GREEN THAT LIES — the RESOLVER seam discloses a stand-in `import` in the
//! verify pass's exact words.**
//!
//! Two seams report an accepted island. When the crate's batch is accepted it
//! is the verify pass (`clean_island_standin_import_disclosed.rs`). When ANY
//! island is rejected, the rejection is a front-end error and the resolver
//! reports the whole batch itself — including progress for each island that
//! elaborated independently (measured at HEAD 9b4c6b3ab: the first island
//! below still prints `Clean island kernel-checked … (six)`), and the build
//! never reaches the verify pass. A disclosure wired only into the verify pass
//! would therefore vanish exactly when a sibling island is broken. Both seams
//! render `trust_certify::clean_island::CleanIslandStandinImport`, so the
//! wording cannot drift between them.
//!
//! The rejected island discloses nothing: it reports no green to qualify.

clean {
    import Lean
    def six : UInt64 := 6
}
//~^^^ NOTE Clean island kernel-checked: 1 declaration(s) registered (six)
//~| NOTE `import Lean` was served by Clean's built-in prelude stand-in, NOT by the library of that name

clean {
    def bad : UInt64 := no_such_name
}
//~^^ ERROR Unknown identifier: no_such_name

fn main() {}
