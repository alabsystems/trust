//@ revisions: default strict
//@[default] check-pass
//@ compile-flags: -Ztrust-verify=on --crate-type=lib
//@[strict] compile-flags: -Ztrust-ir-lower=strict -Ztrust-policy=advisory
//@ needs-trust-verify
//@ dont-check-compiler-stderr
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE
//! Trust (wave-EMO contract, crystal U14): a field read THROUGH AN OPAQUE CARRIER LOCAL is
//! refused at the `Field` arm, keyed on the LOCAL, not on the value it currently holds.
//!
//! The opaque-enum match lane binds a payload binding (`Ok(h)` below) to the scrutinee's
//! fact-free carrier at `Ty::Unit` and promises that every value-needing use of it fails
//! closed at its own site. Main's `lower_field_aggregate` (2350e94697b) keeps that promise
//! for the carrier VALUE (`opaque_carrier_value_spellings`), which is enough while the local
//! still holds the value it was bound to (`alias_then_read`). It is not enough once the local
//! is REBOUND to a value no ledger row names:
//!
//!   * `havoc_then_read` -- the `for` summary havocs the mutated local to a fresh
//!     `undef ()` (its declared type is the carrier placeholder), and `h.tag` then read that
//!     value with `ExtractField`;
//!   * `join_then_read` -- the `if` merge rebinds the local to a join parameter typed `()`.
//!
//! On main 8e8e84edfa3 both lowered clean, spliced, and final module validation rejected the
//! crate: `FieldAccessInvalid { op: "extract_field", reason: "aggregate operand must be a
//! struct/record/tuple/enum/closure, got ()" }` (and, for the join, `BranchArgTypeMismatch
//! { expected: "()", actual: "struct.0" }`). Under the default verify-on policy that is a
//! hard error on valid Rust. With the refusal both bodies are refused with
//! `Field(opaque carrier base)`, stay out of the module, and the crate compiles.
//!
//! The `default` revision pins that the crate compiles. The `strict` revision pins WHICH
//! refusal each body gets (review follow-up, 2026-09-29): "compiles" alone would also pass if
//! a later change let the two rebound reads lower and some other arm happened to keep the
//! module valid. Under strict each refused body is a compile error that names its shape, so
//! `Field(opaque carrier base)` on the two rebound reads is U14's arm. The alias control
//! was refused by main's value-ledger arm (`Field(opaque aggregate carrier)`) until
//! 2026-10-02; it is now refused at its `let` (`Let(opaque carrier at a real type)`).
//!
//! `Header`'s tuple field is what sends `Result<Header, u64>` to the opaque lane:
//! `register_enum` admits a struct payload only when the struct's own fields are
//! layout-resolvable, and a tuple field is not.

pub struct Header {
    pub tag: u8,
    pub pair: (u8, u32),
}

pub fn havoc_then_read(r: Result<Header, u64>, n: u32) -> u8 {
//[strict]~^ ERROR Field(opaque carrier base)
    match r {
        Ok(mut h) => {
            for _ in 0..n {
                h = Header { tag: 1, pair: (2, 3) };
            }
            h.tag
        }
        Err(_) => 255,
    }
}

pub fn join_then_read(r: Result<Header, u64>, c: bool) -> u8 {
//[strict]~^ ERROR Field(opaque carrier base)
    match r {
        Ok(mut h) => {
            if c {
                h = Header { tag: 1, pair: (2, 3) };
            }
            h.tag
        }
        Err(_) => 255,
    }
}

// CONTROL: the carrier value itself (through an alias) was already refused on main, by
// `lower_field_aggregate`'s value-ledger check. It must stay refused and keep the crate valid.
// Since 2026-10-02 the alias binding is refused first, at the `let` (see
// `alias_rebind_then_read` below), so strict names that tag.
pub fn alias_then_read(r: Result<Header, u64>) -> u8 {
//[strict]~^ ERROR Let(opaque carrier at a real type)
    match r {
        Ok(h) => {
            let g = h;
            g.tag
        }
        Err(_) => 255,
    }
}

// KNOWN_HAZARDS "an opaque-carrier binding ALIASED into a new local and then rebound aborts
// valid Rust" (closed 2026-10-02): `g` is declared at the REAL type `Header`, so U14's
// carrier-local arm never sees it, and the `if` join typed `g` as `struct` with a `()`
// carrier on one edge. Final module validation rejected the crate with
// `BranchArgTypeMismatch { expected: "struct.0", actual: "()" }`. The binding is now refused
// where it is made.
pub fn alias_rebind_then_read(r: Result<Header, u64>, c: bool) -> u8 {
//[strict]~^ ERROR Let(opaque carrier at a real type)
    match r {
        Ok(h) => {
            let mut g = h;
            if c {
                g = Header { tag: 1, pair: (2, 3) };
            }
            g.tag
        }
        Err(_) => 255,
    }
}
