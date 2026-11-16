//@ needs-trust-verify
//@ compile-flags: -Z trust-verify=off
//! **G2 negative — `name.lean` AND `name.clean` both on disk is an ambiguity,
//! refused with options (ruling v7/D3), never resolved by a preference order
//! that would let a stale twin shadow the edited file.**

clean mod clean_unit_both_spellings_helper;
//~^ ERROR the out-of-line Clean unit `clean_unit_both_spellings_helper` is spelled twice on disk

fn main() {}
