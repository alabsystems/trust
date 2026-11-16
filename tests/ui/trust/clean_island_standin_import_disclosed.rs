//@ needs-trust-verify
//@ check-pass
//@ compile-flags: -Z trust-verify=off
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//! A reference-compatible stand-in import is disclosed at the import itself.
//!
//! This checks declarations relative to Clean's Lean stand-in, not the real
//! library. TG8 requires the reference entry as well; a structurally ineligible
//! stand-in is refused by `tg8_reference_base_standin_refused.rs`.
//!
//! The standalone `.lean` check lane refuses stand-ins outright. An accepted
//! Rust island retains its substitution note. The resolver-seam and clean-unit
//! twins cover the other reporting owners.

clean {
    import Lean
    def six : UInt64 := 6
}
//~^^^ NOTE Clean island kernel-checked: 1 declaration(s) registered (six)
//~| NOTE `import Lean` was served by Clean's built-in prelude stand-in, NOT by the library of that name
//~| NOTE vendor the declarations you need as Clean source in this crate

// CONTROL: an island that imports nothing discloses nothing — the note is
// about an `import`, not about islands. (`dont-require-annotations` cannot pin
// an absence; `trust-certify`'s
// `test_check_all_discloses_a_prelude_stand_in_import_on_the_accepted_island`
// does, per island.)
clean {
    def seven : UInt64 := 7
}
//~^^ NOTE Clean island kernel-checked: 1 declaration(s) registered (seven)

fn main() {
    let _ = six() + seven();
}
