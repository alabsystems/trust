//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=off
//@ check-fail
//! TG3 (reported by aterm's PF1 worker, 2026-11-05): an island is deferred until
//! program admissions exist only when it NAMES a `trust_import_*` constant, read
//! by Clean's own lexer. A comment or a string that mentions the namespace
//! names nothing. Before TG3 the decision was a byte search, so the comment
//! below deferred this island (and every island after it) out of the
//! resolver's check, and its declarations could not be called from Rust.
//!
//! The pin is WHICH check refused the false theorem: the resolve-time batch
//! check ("did not elaborate", "rejected during resolver checking"), which is
//! where an undeferred island is checked. A deferred island is refused later,
//! with "Clean island declaration rejected" and the kernel-import note. This
//! file checks its whole `.stderr`.

clean {
    -- This comment mentions trust_import_off_island_comment_not_deferred__f,
    -- and a string can too:
    def note : String := "trust_import_"
    theorem bad : (1 : Nat) = 2 := rfl
}
//~^^ ERROR `bad` did not elaborate

fn main() {}
