// A slice-bounds obligation whose proof is a three-edge order chain must keep its
// kernel certificate when the compiler hands the certifier MORE true context.
//
// THE ROW (TRUST-KI-1014-1). aterm-codec `crates/aterm-codec/src/tty.rs:141`,
// `joint[..held]` in `SafeStream::push`:
//
// ```rust
// let mut joint = [0u8; 6];
// let held = self.held.min(self.carry.len());   // carry: [u8; 3]
// let take = piece.len().min(joint.len() - held);
// joint[..held].copy_from_slice(&self.carry[..held]);
// ```
//
// The compiler's ay lane proves the `[slice]` bound (`held > 6` is UNSAT under
// `held ≤ _10 = 3`). The store seal `321aaeda7` also minted its `CleanCic`
// certificate; from `6606d3bd` on (`trust-b58a105d` included) `certify_vc`
// returned `None`, the row reached targo with no attachable evidence, and the
// publication boundary withheld it: UNKNOWN, "compiler transport claimed a
// favorable outcome without attachable native or clean-kernel proof evidence;
// downgraded before publication". The boundary was right to withhold an
// uncertified claim; the certificate was what had gone missing.
//
// THE POOL below is that row's certify input on `trust-b58a105d`, captured
// verbatim with `RUSTC_LOG=trust_certify::violation=debug` from the
// ATERM-KI-1014-1 reproducer (aterm `docs/KNOWN_ISSUES.md`) under raw `trustc`.
// 66 atoms, 27 variables after normalization. MEASURED at the parent commit of
// this test: the chain lane's lifted edge set has 69 edges (its exhaustive DFS
// stops at 48); ay answers UNSAT but clean-auto reconstructs no closed term from
// its proof, even at an unlimited trust budget; every other lane declines.
// `src/large_order_chain.rs` is the route that now certifies it.
//
// FALSIFICATION CONTROL: `the_joint_slice_row_certifies` fails with the
// `large_order_chain` call removed from `certify_lanes` (measured), and
// `a_reachable_violation_in_the_same_pool_is_never_certified` is the same pool
// with the violated bound lowered to `held > 2`, which `held = 3` satisfies.
//
// Author: Andrew Yates. Copyright 2026 Andrew Yates. License: Apache-2.0 OR MIT.

use trust_types::{Formula, Sort, SourceSpan, VcKind, VerificationCondition};

fn v(name: &str) -> Formula {
    Formula::Var(name.to_string(), Sort::Int)
}
fn b(name: &str) -> Formula {
    Formula::Var(name.to_string(), Sort::Bool)
}
fn n(value: i128) -> Formula {
    Formula::Int(value)
}
fn and(conjuncts: Vec<Formula>) -> Formula {
    Formula::And(conjuncts)
}
fn or(disjuncts: Vec<Formula>) -> Formula {
    Formula::Or(disjuncts)
}
fn not(a: Formula) -> Formula {
    Formula::Not(Box::new(a))
}
fn eq(a: Formula, b: Formula) -> Formula {
    Formula::Eq(Box::new(a), Box::new(b))
}
fn le(a: Formula, b: Formula) -> Formula {
    Formula::Le(Box::new(a), Box::new(b))
}
fn lt(a: Formula, b: Formula) -> Formula {
    Formula::Lt(Box::new(a), Box::new(b))
}
fn ge(a: Formula, b: Formula) -> Formula {
    Formula::Ge(Box::new(a), Box::new(b))
}
fn gt(a: Formula, b: Formula) -> Formula {
    Formula::Gt(Box::new(a), Box::new(b))
}
fn add(a: Formula, b: Formula) -> Formula {
    Formula::Add(Box::new(a), Box::new(b))
}
fn sub(a: Formula, b: Formula) -> Formula {
    Formula::Sub(Box::new(a), Box::new(b))
}

/// The captured pool, verbatim but for the violated bound (`6` in the capture:
/// the final `gt(held, ..)`), which the tests vary.
fn joint_slice_pool(violated_bound: i128) -> Formula {
    and(vec![
        and(vec![ge(v("_6"), n(0)), le(v("_6"), n(18446744073709551615))]),
        and(vec![
            eq(v("_4#s0_0"), v("_2")),
            eq(v("_4__slice_len#s0_0"), v("_2__slice_len")),
            eq(v("_6"), v("self*.1#e")),
            eq(b("_5"), gt(v("_6"), n(0))),
            eq(v("_9"), v("self*.1#e")),
            eq(v("_12__slice_len#s1_2"), n(3)),
            eq(v("_12*#s1_2"), v("self*.0#e")),
            eq(v("_11__slice_len#s1_3"), n(3)),
            eq(v("_10"), v("_11__slice_len#s1_3")),
            le(v("held"), v("_9")),
            le(v("held"), v("_10")),
            and(vec![
                le(n(0), sub(v("_17"), v("held"))),
                le(sub(v("_17"), v("held")), n(18446744073709551615)),
            ]),
            eq(v("_20.0#s2_5"), sub(v("_17"), v("held"))),
            and(vec![le(n(0), v("_17")), le(v("_17"), n(18446744073709551615))]),
            and(vec![le(n(0), v("held")), le(v("held"), n(18446744073709551615))]),
            eq(v("_15"), v("_4#s0_0_s1_t")),
            eq(v("_15__slice_len#s2_0"), v("_4__slice_len#s0_0")),
            eq(v("_14"), v("_15__slice_len#s2_0")),
            eq(v("_19__slice_len#s2_2"), n(6)),
            eq(v("_19*#s2_2"), v("_7#s1_t")),
            eq(v("_18__slice_len#s2_3"), n(6)),
            eq(v("_17"), v("_18__slice_len#s2_3")),
            eq(v("_16"), v("_20.0#s2_5")),
            le(v("take"), v("_14")),
            le(v("take"), v("_16")),
            eq(v("self*.1#e"), v("self*.1")),
            eq(v("self*.0#e"), v("self*.0")),
            and(vec![
                gt(v("_6"), n(0)),
                not(b("_20.1#s2_5")),
                or(vec![lt(v("_17"), v("held")), eq(v("_16"), sub(v("_17"), v("held")))]),
                or(vec![lt(v("_42"), v("held")), eq(v("_51"), sub(v("_42"), v("held")))]),
                or(vec![
                    gt(add(v("held"), v("take")), n(18446744073709551615)),
                    eq(v("_32"), add(v("held"), v("take"))),
                ]),
                or(vec![
                    gt(add(v("held"), v("take")), n(18446744073709551615)),
                    eq(v("_40"), add(v("held"), v("take"))),
                ]),
                and(vec![
                    eq(v("_4__slice_len#s0_0"), v("_2__slice_len")),
                    eq(b("_5"), gt(v("_6"), n(0))),
                    eq(v("_12__slice_len#s1_2"), n(3)),
                    eq(v("_11__slice_len#s1_3"), n(3)),
                    eq(v("_10"), v("_11__slice_len#s1_3")),
                    eq(v("_15__slice_len#s2_0"), v("_4__slice_len#s0_0")),
                    eq(v("_14"), v("_15__slice_len#s2_0")),
                    eq(v("_19__slice_len#s2_2"), n(6)),
                    eq(v("_18__slice_len#s2_3"), n(6)),
                    eq(v("_17"), v("_18__slice_len#s2_3")),
                    and(vec![
                        le(n(0), sub(v("_17"), v("held"))),
                        le(sub(v("_17"), v("held")), n(18446744073709551615)),
                    ]),
                    eq(v("_20.0#s2_5"), sub(v("_17"), v("held"))),
                    and(vec![le(n(0), v("_17")), le(v("_17"), n(18446744073709551615))]),
                    and(vec![le(n(0), v("held")), le(v("held"), n(18446744073709551615))]),
                    eq(v("_16"), v("_20.0#s2_5")),
                    gt(v("held"), n(violated_bound)),
                ]),
            ]),
        ]),
    ])
}

fn row(violated_bound: i128) -> VerificationCondition {
    VerificationCondition {
        kind: VcKind::SliceBoundsCheck,
        function: "repro_tty141::SafeStream::push".into(),
        location: SourceSpan {
            file: "src/lib.rs".to_string(),
            line_start: 30,
            col_start: 17,
            line_end: 30,
            col_end: 25,
        },
        formula: joint_slice_pool(violated_bound),
        contract_metadata: None,
        obligation: None,
    }
}

/// The captured row (`held > 6`, joint is 6 bytes) certifies, and the consumer's
/// re-check replays the certificate against the same obligation.
#[test]
fn the_joint_slice_row_certifies() {
    let vc = row(6);
    let evidence = trust_certify::certify_vc(&vc);
    assert!(
        matches!(evidence, Some(trust_ir::ProofEvidence::CleanCic { .. })),
        "the 7 ≤ held ≤ _10 ≤ 3 chain must earn a kernel certificate"
    );
    let evidence = evidence.expect("certified above");
    assert!(trust_certify::replay_vc_evidence(&vc, &evidence), "consumer replay must accept it");
    // Bound to THIS obligation: the same bytes do not replay on another one.
    assert!(!trust_certify::replay_vc_evidence(&row(7), &evidence));
}

/// The same pool with a violation a real execution reaches (`held > 2`: the
/// program allows `held = 3`). Nothing may certify it.
#[test]
fn a_reachable_violation_in_the_same_pool_is_never_certified() {
    assert!(trust_certify::certify_vc(&row(2)).is_none());
}

/// A tighter true bound still certifies (`held > 3` contradicts `held ≤ 3`): the
/// pool's real bound decides, not the literal `6`. MEASURED: this variant also
/// certifies with the large-order-chain lane removed (ay's proof reconstructs on
/// it), which is the shape-sensitivity the lane exists to stop depending on.
#[test]
fn the_tight_bound_certifies() {
    assert!(matches!(
        trust_certify::certify_vc(&row(3)),
        Some(trust_ir::ProofEvidence::CleanCic { .. })
    ));
}
