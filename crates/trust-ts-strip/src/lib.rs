// trust-ts-strip: the TrustTS front-end — TS→JS type eraser (see Cargo.toml).
//
// Author: Andrew Yates
// Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0

/// The outcome of eliding TypeScript type syntax from a source string.
///
/// `Js` carries JavaScript that is behaviourally identical to running the
/// original under Node's native type-stripper (the oracle). `Refused` is the
/// fail-closed outcome: the source is outside the pure-erasure subset, or the
/// eraser cannot elide it soundly. A refusal is always sound; a wrong strip
/// (JS whose runtime behaviour differs from the TypeScript) is never emitted.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum StripOutcome {
    /// Erasable TypeScript, elided to JavaScript (width-preserving blanks).
    Js(String),
    /// Fail-closed: not erasable, or not soundly strippable. Carries a reason.
    Refused(String),
}

/// Elide TypeScript type syntax from `ts_source`, returning JavaScript or a
/// fail-closed refusal. Total: never panics (a would-be panic is a refusal).
#[must_use]
pub fn strip(ts_source: &str) -> StripOutcome {
    let src = ts_source.to_string();
    match std::panic::catch_unwind(move || erase::erase(&src)) {
        Ok(outcome) => outcome,
        Err(_) => {
            StripOutcome::Refused("internal eraser panic (refused, not stripped)".to_string())
        }
    }
}

/// Transform `ts_source` to JavaScript, ERASING types AND lowering the two most
/// common non-erasable constructs — `enum` and `namespace`/`module` — to the
/// runtime JavaScript the TypeScript-emit engines (Node
/// `--experimental-transform-types` and Bun) produce, or a fail-closed refusal.
///
/// This is a strict superset of [`strip`]: on pure-erasure input it is
/// byte-equivalent to `strip` (the same eraser runs as the final pass), and it
/// additionally lowers enums and namespaces. The lowering matches the engines'
/// OBSERVABLE runtime behaviour (object shape, forward/reverse mappings,
/// exported-vs-local members), not their byte output. Anything it cannot lower
/// to behaviourally-identical JavaScript is a `Refused` — never a guess. Total:
/// a would-be panic is a refusal.
#[must_use]
pub fn transform(ts_source: &str) -> StripOutcome {
    let src = ts_source.to_string();
    match std::panic::catch_unwind(move || transform::transform(&src)) {
        Ok(outcome) => outcome,
        Err(_) => {
            StripOutcome::Refused("internal transform panic (refused, not lowered)".to_string())
        }
    }
}

mod erase;
mod lexer;
mod transform;
