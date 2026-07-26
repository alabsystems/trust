//@ battery-lane: C-combo
//@ battery-expect: frontier
//@ battery-flags: -Ztrust-verify=on --crate-type=lib
//! LANE C — **FRONTIER DOCUMENT**: an island definition called from a
//! `requires`, not an `ensures`.
//!
//! `c2_uncited_defeq.rs` shows the two languages meeting on the POSTCONDITION
//! side: `ensures result == ident_isl(x)` discharges because the kernel checks
//! a constructed `Eq.refl` against the E6-admitted Rust body. The obvious next
//! question is whether the same island definition may be called on the
//! PRECONDITION side. This file asks it, in a program someone would actually
//! write, and records the answer.
//!
//! ## The answer, from source: NO. The surface does not support it.
//!
//! **No fixture does this.** Of the 172 fixtures in `tests/ui/trust/`, exactly
//! two put anything island-shaped on a `requires`, and neither CALLS an island
//! definition:
//!
//! - `tests/ui/trust/typed_citation_domain.rs:24` — `requires x == x by
//!   u64_refl`. A `by` CITATION on a requires is supported (check-pass, with a
//!   "Clean-kernel statement match" note).
//! - `tests/ui/trust/typed_citation_result_scope.rs:14-16` — `requires result
//!   == result by u64_refl`, rejected for `result` scope, not for a call.
//!
//! The rest of the corpus's `requires` payloads are scalar arithmetic, one
//! quantifier (`native_clause_grammar.rs:37`), and exactly two call-shaped
//! forms — neither of which is a user-defined function of either language:
//!
//! - `contract_synthetic_namespace_collision.rs:22` — `priv_dropped()`, a
//!   member of the closed predicate vocabulary cited below, in a fixture that
//!   is itself a rejection test.
//! - `native_loop_collection_semantics.rs:17` — `xs.len() > 0`, admitted by a
//!   separate closed EXACT-PROJECTION lane that lowers `.len()` to the
//!   synthetic `xs_len` leaf, and only for an Array-typed base
//!   (`trust_contract_query.rs:451-469`, `:496-536`). That lane is a fixed
//!   list of projections, not an extension point.
//!
//! **Why, structurally.** The failure is not name resolution and never could
//! be: clause payloads are `verifier vocabulary — never name-resolved or
//! type-checked by rustc` (`compiler/rustc_ast/src/ast/trust_contract.rs:18-22`).
//! `ident_isl` will not produce "cannot find function". The rejection comes
//! from a different, earlier gate:
//!
//! 1. `compiler/rustc_mir_transform/src/trust_contract_query.rs:308-340` — a
//!    native clause is validated at an ALWAYS-ON boundary, and a failure is a
//!    hard `span_err`: ``invalid `requires` clause: {reason}``. Critically, the
//!    match arm at lines 311-314 admits only `Requires` and `Decreases` on a
//!    function (plus `LoopInvariant` on a loop). **`Ensures` is deliberately
//!    NOT in that set** — which is precisely why `c2_uncited_defeq.rs`
//!    compiles. The two sides of a signature are not governed by the same
//!    admission rule.
//! 2. `trust_contract_query.rs:595-611` routes the requires payload through
//!    `trust_types::validate_source_spec_expr_with_exact_projections`, which
//!    "resolves every source name".
//! 3. `crates/trust-types/src/spec_render.rs:469-475` — inside that validator a
//!    call `f(..)` is legal ONLY if `pred_arg_sorts(f)` is `Some`; otherwise
//!    `SpecRenderError::UnsupportedCall`, rendered as ``unsupported
//!    source-contract call `{name}` `` (`spec_render.rs:52-53`).
//! 4. `crates/trust-types/src/formula/pred_vocab.rs:23-36` and `:60-65` — that
//!    vocabulary is CLOSED: nine safety-capability predicates plus `is_whnf`.
//!    An island definition is not in it. Neither is any Rust program function,
//!    so `requires` is narrower than `ensures` in both languages at once.
//! 5. And the uncited defeq lane is ensures-only by construction:
//!    `compiler/rustc_mir_transform/src/trust_verify.rs:15502-15511` collects
//!    `TrustContractKind::Ensures` clauses and returns early otherwise. Even if
//!    a requires payload were admitted, no lane would discharge it.
//!
//! ## What the directive means here
//!
//! `battery-expect: reject` is the honest setting — the toolchain does reject
//! this file — but the runner will score it `reject-correct` because the
//! diagnostic carries "requires"/"clause". **Read that verdict as "the clause
//! ADMISSION GATE spoke", not "the kernel refused a proof."** Nothing here is
//! evidence about proof strength. Unlike `c3_NEG_divergent_defeq.rs`, this
//! file is not a soundness control: the program below is TRUE
//! (`ident_isl(x) == x` holds for every `x`), and it is refused for lack of
//! surface, not for lack of proof.
//!
//! This is therefore a FRONTIER MARKER. When the two-language surface grows
//! requires-side island calls — the natural counterpart to the R4 §1 composed
//! lane — this file must flip to `pass`, and this directive must be changed
//! deliberately, with the reason recorded. Until then its rejection is the
//! measurement.
//!
//! Expected diagnostic:
//! ``error: invalid `requires` clause: unsupported source-contract call `ident_isl` ``

clean {
    def ident_isl (x : UInt64) : UInt64 := x
}

/// CONTROL — the same island definition, the same call, on the ENSURES side.
/// This is `c2`'s mode and it compiles: the ensures lane has no always-on
/// source-vocabulary gate, and the kernel closes the clause by defeq.
/// Its presence in this file is what makes the rejection below attributable to
/// the clause ROLE rather than to the island, the definition, or the call.
pub fn pass_through(x: u64) -> u64
    ensures result == ident_isl(x)
{
    x
}

/// THE FRONTIER — the identical call, moved to a `requires`.
///
/// The precondition is true and the island definition is the same one the
/// function above uses successfully. It is rejected because a native `requires`
/// payload must lie inside the closed source-contract predicate vocabulary,
/// which contains no island definitions (and no Rust functions either).
pub fn guarded(x: u64) -> u64
    requires ident_isl(x) == x
{
    x
}
