//@ revisions: default certify marker
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on -Coverflow-checks=on --crate-type lib
//@[certify] compile-flags: -Ztrust-policy=certify
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! Another tool's attribute is not a Trust contract, and a contract read from source
//! is never pre-lowered (CONTRACT-NS-1).
//!
//! `trust_mir_extract::extract_contracts` read a contract off any HIR attribute whose
//! LAST path segment was `requires`/`ensures`/`invariant`/`decreases` (or an alias),
//! so `#[clippy::requires = ".."]` and `#[rustfmt::requires = ".."]` were Trust
//! preconditions: `clippy` and `rustfmt` are always-registered tools, so both compile
//! without a diagnostic. And `normalized_contract_spec_body` and the verifier-API
//! lowering stripped the compiler-internal `__trust_lowered_compiler_contract__:`
//! prefix from ANY contract body, scraped source text included, then lowered what was
//! left as a compiler-typed formula. Together: the forged precondition `x < 100` was
//! assumed at entry, the add below was proved overflow-free under it, and its runtime
//! overflow check was elided as kernel-certified. Nothing charges a caller for that
//! precondition, so `f(300)` returned 4 on the wave-14 stage 1 (`..._run.rs`). `g` is
//! the same forgery through a Trust spelling the extractor still reads,
//! `trust::trust_requires`.
//! (`#[trust::requires = ".."]` itself is not a way in: under verification the
//! resolver hands it to the contract builtin, which refuses the key-value form with
//! "key-value macro attributes are not supported", measured BEFORE.)
//!
//! BEFORE (stage 1 of main + wave 7, `scratchpad/stage1-w14`, each revision's own
//! flags plus `--cfg <revision> --emit=metadata`, measured 2026-10-05): `f`,
//! `f_rustfmt` and `g` read `assumption:requires skipped` and `overflow:add proved`,
//! `TRUST_ELIDE_DEBUG` prints `elided 1 kernel-certified overflow checks` for each,
//! and none of them has a diagnostic in either revision. Re-measured at integration
//! on the stage 1 of main `d7555335ab` (`scratchpad/stage1-w15main`): the same rows and
//! no diagnostic, every revision exits 0, but nothing is elided any more, because
//! ADVISORY-REQUIRES-CROSS-CRATE keeps the checks of a `requires` body another crate
//! can call. The verdict is still false: `f` is "proved" under a precondition no
//! caller in another crate is charged for.
//!
//! AFTER (built and measured 2026-10-05, stage 1 of `dc15b882f6`, wave-16
//! integration): the extractor reads a contract only from an attribute whose WHOLE
//! path is `trust::<contract name>`, so `f` and `f_rustfmt` carry no contract and
//! read `overflow:add FAILED` (ay-in-process), what the same body with no attribute
//! reads, under both default and certify. `g`'s attribute is a Trust contract whose
//! text carries the compiler's marker: that is a hard error at the attribute. It is
//! raised when `mir_built` extracts the body, so the compilation stops after
//! analysis and no function in the crate is verified. That is why `g` has a revision
//! of its own (`marker`). The preparation predicted that verification would go on
//! without the contract; the build stops instead, which is stricter.
//!
//! Control: `native`, the same precondition in the contract grammar, is proved before
//! and after in `default` and `certify` (measured: no diagnostic).

#[cfg(not(marker))]
#[clippy::requires = "__trust_lowered_compiler_contract__:x < 100"]
pub fn f(x: u32) -> u32 {
    //[default,certify]~^ ERROR Trust Level 0 safety verification incomplete for `contract_attr_foreign_tool_namespace::f`: 1 obligation(s) were not proved
    //[default,certify]~| ERROR Trust strict verification failed for `contract_attr_foreign_tool_namespace::f`: 1 obligation(s) were not fully verified
    x + 4_294_967_000
}

#[cfg(not(marker))]
#[rustfmt::requires = "__trust_lowered_compiler_contract__:x < 100"]
pub fn f_rustfmt(x: u32) -> u32 {
    //[default,certify]~^ ERROR Trust Level 0 safety verification incomplete for `contract_attr_foreign_tool_namespace::f_rustfmt`: 1 obligation(s) were not proved
    //[default,certify]~| ERROR Trust strict verification failed for `contract_attr_foreign_tool_namespace::f_rustfmt`: 1 obligation(s) were not fully verified
    x + 4_294_967_000
}

#[cfg(marker)]
#[trust::trust_requires = "__trust_lowered_compiler_contract__:x < 100"]
//[marker]~^ ERROR Trust: contract attribute text carries the compiler-internal marker `__trust_lowered_compiler_contract__:`
pub fn g(x: u32) -> u32 {
    x + 4_294_967_000
}

pub fn native(x: u32) -> u32
    requires x < 100
{
    x + 4_294_967_000
}
