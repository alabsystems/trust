//@ needs-trust-verify
//@ compile-flags: -Z trust-verify=off
//! **I8 negative — missing `.clean` file.**
//! There is deliberately NO `clean_unit_missing_helper.clean` beside this
//! test. The refusal must name the ONE candidate path it looked for (a unit
//! has a single candidate — no `mod.clean` secondary, so no ambiguity class)
//! and carry the options (ruling v7/D3): create the file; `#[path]`; or
//! inline the declarations as `clean { … }`.

clean mod clean_unit_missing_helper;
//~^ ERROR file not found for out-of-line Clean unit `clean_unit_missing_helper`

fn main() {}
