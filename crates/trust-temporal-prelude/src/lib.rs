// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Trust's canonical temporal vocabulary as Clean source text.
//!
//! ONE COPY. The text is `include_str!`ed from `trust-spec-temporal/clean/Trust`,
//! the files that crate's certification lanes elaborate, so the island lane and
//! the certification lane cannot disagree about what `Trust.Temporal.Always` or
//! `Trust.Temporal.FiniteModel.ScalarModel.safetyClaim` means. Nothing here is
//! trusted: every declaration is elaborated and kernel-checked by whoever
//! serves it (`trust_certify::clean_island::CleanIslandSession`).

/// `Trust.Temporal`: behaviours, `Always`/`Eventually`/`LeadsTo`, `StateMachine`,
/// fairness, `Satisfies`, `ForwardRefinement` and its transport theorems.
pub const TEMPORAL: &str = include_str!("../../trust-spec-temporal/clean/Trust/Temporal.lean");

/// `Trust.FiniteModel` (namespace `Trust.Temporal.FiniteModel`): the finite
/// model data — scalar and Boolean-function state, guarded actions, invariants
/// — and its `StateMachine` semantics, `SafetyClaim` and the strengthening
/// induction. Elaborates on top of [`TEMPORAL`].
pub const FINITE_MODEL: &str =
    include_str!("../../trust-spec-temporal/clean/Trust/FiniteModel.lean");

/// `Trust.FiniteModelCheck` (namespace `Trust.Temporal.FiniteModel`): an
/// executable finite-model checker the kernel evaluates by reduction —
/// `checkScalarRows`, the untrusted bounded search `reachRows`, the verdict
/// `safetyVerdict` — and its kernel-checked soundness theorem
/// `scalarSafetyOfCheck`, so `proveSafe M 64 rfl` (or `checkSafety M 64 rfl`)
/// proves `ScalarModel.safetyClaim M` while the island compiles, and a
/// rejection names its cause (`invariantFails <row> <i>`, `budgetExhausted`,
/// `unsupported`). Elaborates on top of [`FINITE_MODEL`].
pub const FINITE_MODEL_CHECK: &str =
    include_str!("../../trust-spec-temporal/clean/Trust/FiniteModelCheck.lean");

/// `Trust.Protocol`: short names and operators for writing a finite model
/// and its claims in an island (`machine`, `var`, `act`, `"x" ≔ v "x" ⊞ n 1`,
/// `inv`, `progress`). Ordinary definitions that unfold to the constructors of
/// [`FINITE_MODEL`] and [`FINITE_MODEL_CHECK`], with no authority of their own.
/// Served on top of [`BINDING`], so `Binding` and `binds` are in scope too.
pub const PROTOCOL: &str = include_str!("../../trust-spec-temporal/clean/Trust/Protocol.lean");

/// `Trust.Binding`: `Binding` and `binds`, the data that ties a model to the
/// Rust code beside it, which the compiler reads and checks against the code.
/// It depends on nothing, so an island that declares only a binding serves no
/// model library.
pub const BINDING: &str = include_str!("../../trust-spec-temporal/clean/Trust/Binding.lean");

/// The modules served, in dependency order: `(module, depends on, source)`.
pub const MODULES: &[(&str, &[&str], &str)] = &[
    ("Trust.Temporal", &[], TEMPORAL),
    ("Trust.FiniteModel", &["Trust.Temporal"], FINITE_MODEL),
    ("Trust.FiniteModelCheck", &["Trust.FiniteModel"], FINITE_MODEL_CHECK),
    ("Trust.Binding", &[], BINDING),
    ("Trust.Protocol", &["Trust.FiniteModelCheck", "Trust.Binding"], PROTOCOL),
];

/// The notation commands of every served module (`prefix`, `infix`,
/// `infixl`, `infixr`, `notation` lines), one per line: what a parser needs in
/// scope to parse an island written with that notation. Parsing only; the
/// modules themselves are served, elaborated and checked as before.
#[must_use]
pub fn notation() -> String {
    let mut out = String::new();
    for (_, _, source) in MODULES {
        for line in source.lines() {
            let command = line.split_whitespace().next().unwrap_or_default();
            let command = command.split(':').next().unwrap_or_default();
            if matches!(command, "prefix" | "postfix" | "infix" | "infixl" | "infixr" | "notation")
            {
                out.push_str(line);
                out.push('\n');
            }
        }
    }
    out
}

#[cfg(test)]
mod tests {
    #[test]
    fn the_served_text_is_the_certified_text() {
        assert!(super::TEMPORAL.contains("namespace Temporal"));
        assert!(super::TEMPORAL.contains("def Always"));
        assert!(super::FINITE_MODEL.contains("namespace FiniteModel"));
        assert!(super::FINITE_MODEL.contains("safetyClaim"));
        assert!(super::FINITE_MODEL_CHECK.contains("theorem scalarSafetyOfCheck"));
        assert!(super::FINITE_MODEL_CHECK.contains("theorem checkSafety"));
        assert!(super::PROTOCOL.contains("def machine"));
        assert!(super::BINDING.contains("structure Binding"));
        assert!(!super::PROTOCOL.contains("structure Binding"));
        let notation = super::notation();
        assert!(notation.contains("\"□\"") && notation.contains("\" ⊞ \""), "{notation}");
        for (module, deps, source) in super::MODULES {
            assert!(!source.is_empty(), "{module}");
            for dep in *deps {
                assert!(
                    super::MODULES.iter().position(|(m, _, _)| m == dep)
                        < super::MODULES.iter().position(|(m, _, _)| m == module),
                    "{module} is served after {dep}"
                );
            }
        }
    }
}
