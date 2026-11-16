//! Trust (2026-09-17): the finalization ROUTING probe behind
//! `-Ztrust-ir-lower-mutate-finalization`.
//!
//! WHY THIS EXISTS. `tests/ui/trust/advisory_invalid_module_is_a_warning.rs`
//! and its strict control pin ONE property: a crate-level Trust-IR module the
//! validator rejects is a WARNING under `-Ztrust-policy=advisory` (the crate
//! keeps compiling, every obligation is still reported) and a hard error under
//! every fail-closed policy. For two days that pair rode a live producer gap to
//! obtain an invalid module — a const-generic array parameter, then
//! `fmt::Arguments` by value, then a fn-pointer parameter — and each time the
//! producer campaign closed the gap within a day, both halves went red, and the
//! pair was re-pointed. Four re-points is a test measuring the calendar, which
//! its own doc names as the failure to avoid. The pair now asks for the invalid
//! module DIRECTLY: this probe hands the finalizer the one encoding trust-ir
//! v41 refuses by construction — a `CallingConv::Rust` declaration spelled
//! `params: [] + is_vararg: true` (`validate_rust_abi_is_not_variadic`) —
//! validated by the REAL validator, so the strings the finalizer routes are the
//! validator's own, not a hand-written imitation.
//!
//! WHAT IT IS NOT. It never touches the crate's real module (that is
//! `crate_module::finalize_and_dump`, a frozen oracle file, and stays frozen);
//! it manufactures a SEPARATE one-declaration module and appends that module's
//! refusals to the finalizer's error list. It is `TRUST_AUTHORITY:
//! EvidenceControl`, TEST-ONLY, and can only make a build FAIL that would have
//! passed — never the reverse — exactly the discipline of
//! `-Ztrust-clean-origin-mutate-emitter`.

use trust_ir::{BlockId, FuncId, FuncTy, Function, Linkage, Module};

/// The name the probe declaration carries, so a refusal that names it can never
/// be mistaken for a finding about the user's crate.
pub const PROBE_DECLARATION_NAME: &str = "__trust_finalization_probe::unsignable";

/// Build the one-declaration module trust-ir v41 refuses and run the real
/// validator over it. Returns the finalizer-shaped refusal lines (the same
/// `final Trust-IR module validation failed [Variant]: ...` spelling
/// `finalize_and_dump` produces), each suffixed with the probe's provenance.
///
/// Fail-closed: if the validator ever STOPS refusing this module — which would
/// mean the unknown-signature encoding became acceptable again — the probe
/// returns a refusal saying so, because a routing test that silently passes
/// with nothing to route is the vacuity this file exists to keep out.
pub fn manufactured_validator_refusals() -> Vec<String> {
    let mut module = Module::new("trust_finalization_probe");
    // Trust (trust-ir D1b): a door that refuses leaves no probe module, which is itself a
    // refusal line, never a panic and never an empty (vacuous) result.
    let probe_not_built = |refusal: String| {
        vec![format!(
            "final Trust-IR module validation failed [ProbeNotBuilt]: the finalization probe \
             (-Ztrust-ir-lower-mutate-finalization) could not build its module: {refusal}"
        )]
    };
    let sig = match module.add_func_type(FuncTy {
        params: Vec::new(),
        returns: Vec::new(),
        is_vararg: true,
        abi: None,
    }) {
        Ok(sig) => sig,
        Err(refusal) => return probe_not_built(refusal.to_string()),
    };
    let mut function = Function::new(FuncId::new(0), PROBE_DECLARATION_NAME, sig, BlockId::new(0))
        .with_producer(trust_ir::Producer::TRust);
    function.linkage = Linkage::External;
    function.calling_conv = trust_ir::CallingConv::Rust;
    if let Err(refusal) = module.try_add_function(function) {
        return probe_not_built(refusal.to_string());
    }

    let errors = trust_ir_build::validate_module(&module);
    if errors.is_empty() {
        return vec![
            "final Trust-IR module validation failed [ProbeNotRefused]: the finalization probe \
             (-Ztrust-ir-lower-mutate-finalization) built a `CallingConv::Rust` declaration \
             with `params: [] + is_vararg: true` and the validator ACCEPTED it — the \
             unknown-signature encoding v41 refuses is being accepted again; this is a \
             validator regression, not a routing result"
                .to_string(),
        ];
    }
    errors
        .iter()
        .map(|error| {
            let rendered = format!("{error:?}");
            let variant =
                rendered.split(|c: char| !c.is_ascii_alphanumeric()).next().unwrap_or("Unknown");
            format!(
                "final Trust-IR module validation failed [{variant}]: {rendered} (manufactured by \
                 -Ztrust-ir-lower-mutate-finalization on a separate one-declaration probe module \
                 `{PROBE_DECLARATION_NAME}`; the crate's own module is untouched)"
            )
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn the_probe_module_is_refused_by_the_real_validator_as_rust_abi_vararg() {
        let refusals = manufactured_validator_refusals();
        assert!(!refusals.is_empty());
        assert!(
            refusals.iter().any(|r| r.contains("[RustAbiVararg]")),
            "the probe must trip exactly the v41 vararg refusal: {refusals:?}"
        );
        assert!(
            refusals.iter().all(|r| r.contains(PROBE_DECLARATION_NAME)),
            "every refusal must name the probe, never the user's crate: {refusals:?}"
        );
        assert!(refusals.iter().all(|r| !r.contains("ProbeNotRefused")));
    }
}
