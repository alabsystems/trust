//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=certify --crate-type lib
//@ edition: 2021
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-fail
//! THE PLANTED REFUTATION FOR THE `ToString::to_string` TOTALITY STAMP.
//!
//! This file is a program that PANICS AT RUNTIME. Measured, on a compiler built
//! from this tree:
//!
//! ```text
//! thread 'main' panicked at library/alloc/src/string.rs:2943:14:
//! a Display implementation returned an error unexpectedly: Error
//! ```
//!
//! Line 2943 is the `.expect(...)` at the end of the BLANKET `SpecToString`
//! default — the one body the `to_string` stamp exists to stay away from. So the
//! obligation below is a real refutation, not a coverage gap, and a green build
//! here is a manufactured proof.
//!
//! # HOW A REFUTATION REACHED GREEN
//!
//! `trust_mir_extract::convert::to_string_self_ty_is_foundational` admits `Self`
//! = `String` by asking `tcx.is_diagnostic_item(sym::String, adt.did())`. Read
//! the deciding code (`rustc_middle::ty::context`):
//!
//! ```text
//! pub fn is_diagnostic_item(self, name: Symbol, did: DefId) -> bool {
//!     self.diagnostic_items(did.krate).name_to_id.get(&name) == Some(&did)
//! }
//! ```
//!
//! The table consulted is **`did`'s OWN crate's**, and `diagnostic_items` for a
//! local crate is collected by walking that crate's own items
//! (`rustc_passes::diagnostic_items`). `#[rustc_diagnostic_item = "String"]` is
//! therefore not an identity at all: it is a NAME any crate can mint for a type
//! of its own, and minting it here costs one `#![feature(rustc_attrs)]` and a
//! lint warning.
//!
//! The name was not even std's. Nothing in `library/` carries
//! `#[rustc_diagnostic_item = "String"]` — `alloc::string::String` is declared
//! `#[lang = "String"]` — so the arm never matched the real `String` at all. The
//! ONLY `Self` it could ever admit was an impostor like this one.
//!
//! So the pre-fix stamp read `Impostor`, saw the `String` diagnostic item on it,
//! concluded "`SpecToString for String` — a byte copy, total", and stamped the
//! call. `total_no_panic_call_summary` then returned `true` for the stamped
//! path, the call stopped being an absent may-panic callee, `refuter`'s single
//! obligation disappeared, and the crate verified clean — while the compiled
//! program aborts on the very `.expect` the model asserted was unreachable.
//!
//! A `Display::fmt` that returns `Err` is ordinary safe stable Rust. Nothing
//! about this program is exotic except the one attribute that supplies the
//! false identity.
//!
//! # THE FIX THIS FIXTURE GUARDS
//!
//! The `String` arm now keys on the LANG item (`tcx.lang_items().string()`)
//! AND on the ADT's crate being the compiler's own `alloc` by ARTIFACT RESIDENCY
//! (`is_real_alloc_crate`, i.e. `is_real_sysroot_crate` — the R2 discipline),
//! with no generic arguments. The lang item alone is not an identity: it is an
//! attribute too, and rustc's E0152 `found duplicate lang item` fires only when
//! the real owner is loaded, so a `#![no_std]` graph without `alloc` leaves it
//! uncontested (BOUNDARY HOLE 3, pinned by
//! `to_string_stamp_no_std_diagnostic_item_impostor_refuted.rs`). Residency is
//! not something a source attribute can claim. `Impostor` is neither the lang
//! item nor resident, so the stamp declines and the honest obligation comes
//! back.
//!
//! IF THIS FILE EVER COMPILES CLEAN, the stamp is admitting a `Self` on a name
//! rather than on an identity, and every `to_string` totality claim in the
//! toolchain is worthless.
#![feature(rustc_attrs)]
#![allow(internal_features)]

use std::fmt;

/// A LOCAL type that claims std's `String` diagnostic-item name.
#[rustc_diagnostic_item = "String"]
pub struct Impostor;

/// The refutation. `fmt::Write for String` never errors, so std documents this
/// `Display` as "incorrect" — but it COMPILES, it is safe, and `to_string` on it
/// panics. That is what makes this a counterexample rather than a lint.
impl fmt::Display for Impostor {
    fn fmt(&self, _f: &mut fmt::Formatter<'_>) -> fmt::Result {
        Err(fmt::Error)
    }
}

pub fn refuter() -> String {
    //~^ ERROR Trust Level 0 safety verification incomplete for `to_string_stamp_impersonated_string_refuted::refuter`
    //~| ERROR Trust strict verification failed for `to_string_stamp_impersonated_string_refuted::refuter`
    Impostor.to_string()
}
