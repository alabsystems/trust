//! `AyBlastAgrees`, made MACHINE-CHECKED.
//!
//! # What this closes
//!
//! `proofs/codegen-equivalence/g16_multiplier_equivalence.lean` reduces the
//! ay-blast correspondence to two obligations. Obligation 2 (`mul_ay = mul_m`)
//! is DISCHARGED there as a kernel-checked, axiom-free theorem
//! (`mul_ay_matches_model`). Obligation 1 — `AyBlastAgrees`, that ay's encoder
//! actually emits `mul_ay` — cannot be discharged in clean at all: the encoder
//! is Rust, so no closed term of that type can be written.
//!
//! What CAN be done is what this file does: evaluate the gates ay ACTUALLY
//! emits and compare them, exhaustively, against a Rust transcription of
//! `mul_ay`. That converts the obligation from "a human reads the loop and
//! agrees" into "the machine checked ay's own output computes this function on
//! every input at these widths".
//!
//! It is NOT a proof, and this file does not claim to be one. Coverage is in two
//! tiers, and the difference between them is load-bearing:
//!
//!   * EXHAUSTIVE at widths 1..=8 — every input pair, 87_380 of them. The upper
//!     end is `MAX_RECHECKABLE_MUL_WIDTH`, so this covers every width at which
//!     the correspondence can currently be cashed in for a kernel grade.
//!   * SAMPLED at widths 16, 32 and 64 — structured extremes (identities, max,
//!     every single-bit power of two, alternating carry-chain patterns) plus a
//!     deterministic pseudo-random stream. Width 32 is what the live gate
//!     actually lowers, so without this tier the correspondence had NO direct
//!     evidence at the width it is eventually meant to serve.
//!
//! The tiers catch different things, which is why both are kept: a defect at bit
//! 17 is invisible to the exhaustive tier (it never reaches that bit) and is
//! caught only by the sampled one. Neither tier is a proof for all widths.
//!
//! # Why the check is meaningful rather than circular
//!
//! `mul_ay_rust` below is transcribed from the CLEAN definition (`mul_ay` /
//! `accRows` in the proof file), not from ay's Rust. So the differential closes
//! a loop between two independently-written artifacts: ay's bit-blaster on one
//! side, and the model the kernel proved things about on the other. If they
//! agreed only because both were copied from the same source, the test would be
//! worthless — `blast_is_not_trivial` guards the other direction by pinning that
//! the emitted circuit is a real multiplier and not, say, an adder.
//!
//! # A discrepancy this found, worth recording
//!
//! g16's header says its model was built from "the EXACT gate shapes ay's
//! `BvExpr::Mul` emits". That is true of the AND/XOR3 gates but NOT literally of
//! the carry: ay documents `FullAdderCarry` as
//! `(in0 ∧ in1) ∨ (in2 ∧ (in0 ⊕ in1))`, while the model's `fcarry_m` is
//! `(a∧b) ∨ (a∧c) ∨ (b∧c)`. Both are the majority function, so the
//! correspondence still holds — `AyBlastAgrees` is stated about VALUES on
//! `List Bool`, not about clause syntax — but the prose is stronger than the
//! truth, and a reader auditing "exact shapes" by eye would have to notice that
//! and re-derive the equivalence. Checking values rather than syntax is exactly
//! why this differential is the right instrument.

#![cfg(feature = "ay-proofs")]

use ay_proof::bv_blast_export::{BitLemmaKind, ClauseProvenance, Lit, VarRole};
use ay_proof::bv_blast_solver::{BvExpr, export_bv_blast_proof_expr};

/// Widths checked EXHAUSTIVELY. Width `n` costs `4^n` input pairs, so 1..=8 is
/// 87_380 pairs and runs in ~2s.
///
/// The upper end is chosen, not arbitrary: `MAX_RECHECKABLE_MUL_WIDTH = 8` is
/// the widest multiply the live gate will re-check at all, so this range covers
/// EVERY width at which the correspondence can currently be cashed in.
const WIDTHS: &[u32] = &[1, 2, 3, 4, 5, 6, 7, 8];

/// Widths checked by SAMPLING, where `4^n` is impossible. 32 is the live gate
/// width; 64 is the widest operand trust-cg lowers.
const SAMPLED_WIDTHS: &[u32] = &[16, 32, 64];

/// Pairs drawn per sampled width, on top of the structured edge cases.
const SAMPLES: usize = 192;

/// `shl1`: prepend `false`, drop the top bit — the model's shift.
fn shl1(xs: &[bool]) -> Vec<bool> {
    let mut out = vec![false];
    if !xs.is_empty() {
        out.extend_from_slice(&xs[..xs.len() - 1]);
    }
    out
}

/// `selRow_m bit a`: the partial-product row `a & bit`.
fn sel_row(bit: bool, a: &[bool]) -> Vec<bool> {
    a.iter().map(|&x| x && bit).collect()
}

/// `wadd_m`: ripple-carry add, truncated to `|x|` bits, carry-in false.
fn wadd(x: &[bool], y: &[bool]) -> Vec<bool> {
    let mut carry = false;
    let mut out = Vec::with_capacity(x.len());
    for (i, &xi) in x.iter().enumerate() {
        let yi = y.get(i).copied().unwrap_or(false);
        out.push(xi ^ yi ^ carry);
        carry = (xi && yi) || (xi && carry) || (yi && carry);
    }
    out
}

/// `shlk k`: `shl1` applied `k` times.
fn shlk(k: u32, xs: &[bool]) -> Vec<bool> {
    let mut cur = xs.to_vec();
    for _ in 0..k {
        cur = shl1(&cur);
    }
    cur
}

/// TRANSCRIBED FROM THE CLEAN MODEL, not from ay's Rust.
///
/// ```text
/// accRows a []          k acc = acc
/// accRows a (bj::rest)  k acc = accRows a rest (k+1) (wadd acc (shlk k (selRow bj a)))
/// mul_ay  a []                = zerosLike a
/// mul_ay  a (b0::bs)          = accRows a bs 1 (selRow b0 a)
/// ```
fn mul_ay_rust(a: &[bool], b: &[bool]) -> Vec<bool> {
    if b.is_empty() {
        return vec![false; a.len()];
    }
    let mut acc = sel_row(b[0], a);
    for (j, &bj) in b.iter().enumerate().skip(1) {
        acc = wadd(&acc, &shlk(j as u32, &sel_row(bj, a)));
    }
    acc
}

/// Evaluate ay's emitted gate list on a concrete input assignment and read the
/// result bits back out.
///
/// Returns `None` if a gate references a variable that has no value yet, which
/// would mean the emitted lemmas are not in dependency order — a real finding
/// about ay's output rather than something to paper over, so it is surfaced
/// rather than defaulted.
fn eval_blast(
    vars: &[VarRole],
    lemmas: &[(BitLemmaKind, u32, Vec<u32>)],
    outs: &[u32],
    a: &[bool],
    b: &[bool],
) -> Option<Vec<bool>> {
    let mut val: Vec<Option<bool>> = vec![None; vars.len()];
    for (id, role) in vars.iter().enumerate() {
        if let VarRole::InputLeaf { leaf, bit } = *role {
            // Leaf 0 is the first operand to appear (`A`), leaf 1 the second.
            let src = if leaf == 0 { a } else { b };
            val[id] = Some(src[bit as usize]);
        }
    }
    for (kind, out, ins) in lemmas {
        let g = |k: usize| -> Option<bool> { val[ins[k] as usize] };
        let v = match kind {
            BitLemmaKind::ConstFalse => false,
            BitLemmaKind::ConstTrue => true,
            BitLemmaKind::Not => !g(0)?,
            BitLemmaKind::And2 => g(0)? && g(1)?,
            BitLemmaKind::Or2 => g(0)? || g(1)?,
            BitLemmaKind::Xor2 => g(0)? ^ g(1)?,
            BitLemmaKind::Xor3 => g(0)? ^ g(1)? ^ g(2)?,
            BitLemmaKind::FullAdderCarry => {
                let (x, y, c) = (g(0)?, g(1)?, g(2)?);
                (x && y) || (c && (x ^ y))
            }
            // `lhs_bit <=> rhs_bit`; both sides fuse to one var here, so this is
            // always true. It is evaluated anyway rather than skipped, so an
            // unexpected shape would show up instead of being ignored.
            BitLemmaKind::XnorEq => !(g(0)? ^ g(1)?),
            // Any gate kind this differential does not model must FAIL the run,
            // never silently evaluate to a default: an unmodelled kind means the
            // check no longer covers what ay emits.
            _ => return None,
        };
        val[*out as usize] = Some(v);
    }
    outs.iter().map(|&id| val[id as usize]).collect()
}

/// The full variable assignment produced by evaluating every gate — used to
/// check ay's emitted clauses, not just its result bits.
fn eval_full(
    vars: &[VarRole],
    lemmas: &[(BitLemmaKind, u32, Vec<u32>)],
    a: &[bool],
    b: &[bool],
) -> Option<Vec<Option<bool>>> {
    let mut val: Vec<Option<bool>> = vec![None; vars.len()];
    for (id, role) in vars.iter().enumerate() {
        if let VarRole::InputLeaf { leaf, bit } = *role {
            let src = if leaf == 0 { a } else { b };
            val[id] = Some(src[bit as usize]);
        }
    }
    for (kind, out, ins) in lemmas {
        let g = |k: usize| -> Option<bool> { val[ins[k] as usize] };
        let v = match kind {
            BitLemmaKind::ConstFalse => false,
            BitLemmaKind::ConstTrue => true,
            BitLemmaKind::Not => !g(0)?,
            BitLemmaKind::And2 => g(0)? && g(1)?,
            BitLemmaKind::Or2 => g(0)? || g(1)?,
            BitLemmaKind::Xor2 => g(0)? ^ g(1)?,
            BitLemmaKind::Xor3 => g(0)? ^ g(1)? ^ g(2)?,
            BitLemmaKind::FullAdderCarry => {
                let (x, y, c) = (g(0)?, g(1)?, g(2)?);
                (x && y) || (c && (x ^ y))
            }
            BitLemmaKind::XnorEq => !(g(0)? ^ g(1)?),
            _ => return None,
        };
        val[*out as usize] = Some(v);
    }
    Some(val)
}

/// Blast `Mul(A, B)` and recover (roles, gates, result-bit vars).
///
/// The expression path emits no `VarRole::Out`: the equality's two sides are the
/// same expression, so they FUSE, and the per-bit comparison shows up as one
/// `XnorEq` gate per result bit whose two inputs are that shared bit. Reading
/// the result vars off those gates (in emission order, LSB first) is therefore
/// reading ay's own account of which variable is output bit `i`, not a guess.
#[allow(clippy::type_complexity)]
fn blast_mul(
    width: u32,
) -> (Vec<VarRole>, Vec<(BitLemmaKind, u32, Vec<u32>)>, Vec<u32>, Vec<Vec<Lit>>) {
    let e = BvExpr::mul(BvExpr::leaf("A", width), BvExpr::leaf("B", width));
    let proof = export_bv_blast_proof_expr(&e, &e)
        .unwrap_or_else(|err| panic!("ay must blast a width-{width} Mul: {err:?}"));
    let outs: Vec<u32> = proof
        .bit_lemmas
        .iter()
        .filter(|l| matches!(l.kind, BitLemmaKind::XnorEq))
        .map(|l| l.ins[0])
        .collect();
    assert_eq!(
        outs.len(),
        width as usize,
        "width {width}: expected one XnorEq per result bit; ay emitted {}",
        outs.len()
    );
    let lemmas = proof.bit_lemmas.iter().map(|l| (l.kind, l.out, l.ins.clone())).collect();
    // Only the GATE-DEFINITION clauses. The single `Disequality` clause encodes
    // `not(lhs == rhs)`, which is deliberately UNSAT here and must not be
    // required to hold under a satisfying gate assignment.
    let gate_clauses: Vec<Vec<Lit>> = proof
        .clauses
        .iter()
        .filter(|c| matches!(c.provenance, ClauseProvenance::BitLemmaCnf { .. }))
        .map(|c| c.lits.clone())
        .collect();
    assert!(!gate_clauses.is_empty(), "width {width}: expected gate-definition clauses");
    (proof.vars.roles, lemmas, outs, gate_clauses)
}

fn bits(v: u128, width: u32) -> Vec<bool> {
    (0..width).map(|i| (v >> i) & 1 == 1).collect()
}

/// Deterministic 128-bit sample stream. A fixed seed keeps the test
/// reproducible — a failure can be re-run and lands on the same inputs.
struct Lcg(u128);
impl Lcg {
    fn next(&mut self) -> u128 {
        // 128-bit LCG (Knuth-style multiplier), wrapping.
        self.0 = self.0.wrapping_mul(0x2360_ED05_1FC6_5DA4_4385_DF64_9FCC_F645).wrapping_add(1);
        self.0
    }
}

/// Structured operands worth trying at every sampled width: the identities, the
/// extremes, the single-bit powers of two, and the alternating patterns that
/// exercise carry chains hardest.
fn edge_values(width: u32) -> Vec<u128> {
    let mask: u128 = if width >= 128 { u128::MAX } else { (1u128 << width) - 1 };
    let mut v = vec![0, 1, 2, 3, mask, mask - 1, mask >> 1];
    v.push(0x5555_5555_5555_5555_5555_5555_5555_5555 & mask);
    v.push(0xAAAA_AAAA_AAAA_AAAA_AAAA_AAAA_AAAA_AAAA & mask);
    for k in 0..width {
        v.push(1u128 << k);
    }
    v.sort_unstable();
    v.dedup();
    v
}

#[test]
fn ay_blast_agrees_with_mul_ay_exhaustively() {
    for &width in WIDTHS {
        let (vars, lemmas, outs, gate_clauses) = blast_mul(width);
        let n = 1u32 << width;
        for av in 0..n {
            for bv in 0..n {
                let (a, b) = (bits(u128::from(av), width), bits(u128::from(bv), width));
                let got = eval_blast(&vars, &lemmas, &outs, &a, &b).unwrap_or_else(|| {
                    panic!(
                        "width {width}: ay's emitted blast could not be evaluated at \
                         a={av}, b={bv} — either a gate kind is not modelled by this \
                         differential, or the bit lemmas are not in dependency order. \
                         Both are findings about ay's output, not about this test."
                    )
                });
                // The evaluator applies ay's DOCUMENTED gate semantics. Check
                // those against ay's ACTUAL emitted CNF: every gate-definition
                // clause must be satisfied by the assignment we computed. Without
                // this, a wrong `BitLemmaKind` reading in the evaluator would be
                // validated against ay's prose rather than its output.
                let full = eval_full(&vars, &lemmas, &a, &b).expect("assignment");
                for lits in &gate_clauses {
                    assert!(
                        lits.iter().any(|l| full[l.var as usize] == Some(!l.neg)),
                        "width {width}, a={av}, b={bv}: a gate-definition clause is \
                         UNSATISFIED by the assignment this differential computed — the \
                         evaluator's gate semantics disagree with ay's emitted CNF"
                    );
                }
                let want = mul_ay_rust(&a, &b);
                assert_eq!(
                    got, want,
                    "width {width}, a={av}, b={bv}: ay's emitted circuit disagrees with \
                     the clean model `mul_ay`. This is the AyBlastAgrees obligation \
                     failing — either ay's BvExpr::Mul lowering changed, or the model \
                     in g16_multiplier_equivalence.lean no longer mirrors it."
                );
            }
        }
    }
}

/// The differential must be able to FAIL. If `mul_ay_rust` were degenerate — or
/// if the blast were not really a multiplier — the test above would pass
/// vacuously. Pin both directions on a concrete product.
#[test]
fn blast_is_not_trivial() {
    let width = 4u32;
    let (vars, lemmas, outs, _) = blast_mul(width);
    // 3 * 5 = 15 in 4-bit two's complement.
    let got = eval_blast(&vars, &lemmas, &outs, &bits(3, width), &bits(5, width))
        .expect("the width-4 blast must evaluate");
    assert_eq!(got, bits(15, width), "ay's blast must compute 3*5 = 15");
    // ... and it must NOT be an adder: 3 + 5 = 8 differs from 15.
    assert_ne!(got, bits(8, width), "the emitted circuit must be a multiplier, not an adder");
    // The model agrees on the same witness, independently.
    assert_eq!(mul_ay_rust(&bits(3, width), &bits(5, width)), bits(15, width));
    // And wrapping is exercised: 7 * 7 = 49 = 1 (mod 16).
    let wrap = eval_blast(&vars, &lemmas, &outs, &bits(7, width), &bits(7, width))
        .expect("the width-4 blast must evaluate");
    assert_eq!(wrap, bits(1, width), "two's-complement wrap must match");
    assert_eq!(mul_ay_rust(&bits(7, width), &bits(7, width)), bits(1, width));
}

/// Where `4^n` is impossible, sample — including at the LIVE GATE WIDTH (32).
///
/// This is deliberately weaker evidence than the exhaustive test above, and is
/// labelled as such: it shows agreement on the structured extremes (identities,
/// max, every single-bit power of two, the alternating carry-chain patterns) and
/// on a deterministic pseudo-random stream, not on every input. A fixed seed
/// keeps failures reproducible.
///
/// It matters because width 32 is what the live gate actually lowers, while the
/// exhaustive range stops at 8. Without this, the correspondence had no direct
/// evidence at the width it is eventually meant to be cashed in at.
#[test]
fn ay_blast_agrees_at_sampled_wide_widths() {
    for &width in SAMPLED_WIDTHS {
        let (vars, lemmas, outs, gate_clauses) = blast_mul(width);
        let edges = edge_values(width);
        let mask: u128 = if width >= 128 { u128::MAX } else { (1u128 << width) - 1 };

        let mut pairs: Vec<(u128, u128)> = Vec::new();
        for &x in &edges {
            for &y in &edges {
                pairs.push((x, y));
            }
        }
        let mut rng = Lcg(0x9E37_79B9_7F4A_7C15_F39C_C060_5CED_C835);
        for _ in 0..SAMPLES {
            pairs.push((rng.next() & mask, rng.next() & mask));
        }

        for (av, bv) in pairs {
            let (a, b) = (bits(av, width), bits(bv, width));
            let full = eval_full(&vars, &lemmas, &a, &b).expect("the sampled blast must evaluate");
            for lits in &gate_clauses {
                assert!(
                    lits.iter().any(|l| full[l.var as usize] == Some(!l.neg)),
                    "width {width}, a={av:#x}, b={bv:#x}: a gate-definition clause is \
                     UNSATISFIED — the evaluator's gate semantics disagree with ay's CNF"
                );
            }
            let got =
                eval_blast(&vars, &lemmas, &outs, &a, &b).expect("the sampled blast must evaluate");
            assert_eq!(
                got,
                mul_ay_rust(&a, &b),
                "width {width}, a={av:#x}, b={bv:#x}: ay's emitted circuit disagrees with \
                 the clean model `mul_ay`"
            );
        }
    }
}

/// The sampled test must be able to fail, and its inputs must be non-degenerate.
/// Pin that the edge set actually spans the width and that a wrong model is
/// caught at the live gate width.
#[test]
fn sampled_inputs_are_non_degenerate() {
    for &width in SAMPLED_WIDTHS {
        let edges = edge_values(width);
        assert!(
            edges.len() >= width as usize,
            "width {width}: the edge set must include every single-bit power of two"
        );
        assert!(edges.contains(&0), "width {width}: zero must be exercised");
        assert!(
            edges.contains(&((1u128 << width) - 1)),
            "width {width}: the all-ones operand must be exercised"
        );
    }
    // At the live gate width, a deliberately wrong model must be rejected — so a
    // pass above is a real agreement, not an artefact of the harness.
    let width = 32u32;
    let (vars, lemmas, outs, _) = blast_mul(width);
    let (a, b) = (bits(0x0001_0001, width), bits(0x0000_0101, width));
    let got = eval_blast(&vars, &lemmas, &outs, &a, &b).expect("blast must evaluate");
    assert_eq!(got, mul_ay_rust(&a, &b), "the model must agree at width 32");
    // A shifted-by-one variant of the same product must NOT match.
    assert_ne!(got, mul_ay_rust(&a, &shl1(&b)), "the check must distinguish a wrong model");
}
