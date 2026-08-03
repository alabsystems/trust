// trust_vcgen/separation_logic/frame.rs: Frame rule for modular separation logic reasoning
//
// Implements the separation logic frame rule and framed unsafe block encoding.
//
// Reference: O'Hearn, Reynolds, Yang (2001) "Local Reasoning about Programs
// that Alter Data Structures"
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::{Formula, SourceSpan, VcKind, VerificationCondition};

use super::encoding::{collect_addresses, encode_unsafe_block};
use super::formula::SepFormula;

// ────────────────────────────────────────────────────────────────────────────
// Frame rule
// ────────────────────────────────────────────────────────────────────────────

/// Apply the separation logic frame rule.
///
/// Given a Hoare triple `{P} C {Q}` and a frame `R` that is disjoint from
/// the footprint of `C`, the frame rule says `{P * R} C {Q * R}`.
///
/// This function takes the pre/post conditions (P, Q) and the frame R,
/// and returns the framed pre/post conditions (P * R, Q * R).
///
/// The frame rule is the key to modular reasoning in separation logic:
/// it lets us verify an unsafe block against only its footprint (the heap
/// cells it actually touches), while preserving arbitrary additional heap
/// state in the frame.
///
/// Reference: O'Hearn, Reynolds, Yang (2001) "Local Reasoning about Programs
/// that Alter Data Structures"
#[must_use]
pub fn apply_frame_rule(
    pre: &SepFormula,
    post: &SepFormula,
    frame: &SepFormula,
) -> (SepFormula, SepFormula) {
    let framed_pre = SepFormula::star(pre.clone(), frame.clone());
    let framed_post = SepFormula::star(post.clone(), frame.clone());
    (framed_pre, framed_post)
}

/// Generate VCs with frame rule application for an unsafe block.
///
/// Given:
/// - `pre`: the local precondition (what the unsafe block needs)
/// - `post`: the local postcondition (what the unsafe block establishes)
/// - `frame`: the heap state outside the unsafe block's footprint
///
/// Produces VCs asserting:
/// 1. The framed precondition `P * R` is satisfiable
/// 2. The framed postcondition `Q * R` follows from the framed precondition
/// 3. The frame `R` is preserved (not modified by the operation)
#[must_use]
pub fn encode_framed_unsafe_block(
    func_name: &str,
    pre: &SepFormula,
    post: &SepFormula,
    frame: &SepFormula,
    span: &SourceSpan,
    heap_var: &str,
) -> Vec<VerificationCondition> {
    let (framed_pre, framed_post) = apply_frame_rule(pre, post, frame);

    let mut vcs = encode_unsafe_block(func_name, &framed_pre, &framed_post, span, heap_var);

    // VC 3: Frame preservation -- the frame addresses must not overlap
    // with the operation's footprint.
    let footprint_addrs: Vec<Formula> = {
        let mut a = collect_addresses(pre);
        a.extend(collect_addresses(post));
        a
    };
    let frame_addrs = collect_addresses(frame);

    if !footprint_addrs.is_empty() && !frame_addrs.is_empty() {
        let mut constraints = Vec::new();
        for f_addr in &footprint_addrs {
            for r_addr in &frame_addrs {
                constraints.push(Formula::Not(Box::new(Formula::Eq(
                    Box::new(f_addr.clone()),
                    Box::new(r_addr.clone()),
                ))));
            }
        }
        let disjointness = if constraints.len() == 1 {
            constraints
                .into_iter()
                .next()
                .unwrap_or_else(|| unreachable!("empty iter despite len == 1"))
        } else {
            Formula::And(constraints)
        };

        vcs.push(VerificationCondition {
            kind: VcKind::Assertion {
                message: format!(
                    "[unsafe:sep:frame] frame preservation for unsafe block in {func_name}"
                ),
            },
            function: func_name.into(),
            location: span.clone(),
            formula: Formula::Not(Box::new(disjointness)),
            contract_metadata: None,
            obligation: None,
        });
    }

    vcs
}
