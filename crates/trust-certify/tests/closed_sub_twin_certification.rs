// Kernel certification of the `unix_hardened` twin of a CONSTANT subtraction
// (`BLOCK_LEN - 8`, `const BLOCK_LEN: usize = 64`) whose surrounding context grew
// past the disjunctive lane's 48-edge chain cap.
//
// THE ROW. aterm-digest `crates/aterm-digest/src/sha256.rs:155:17`, in
// `Sha256::finalize`:
//
// ```rust
// self.buf[self.buf_len] = 0x80;                       // :141
// self.buf_len += 1;                                   // :142
// ...
// self.buf[self.buf_len..BLOCK_LEN - 8].fill(0);       // :154
// self.buf[BLOCK_LEN - 8..].copy_from_slice(&bit_len.to_be_bytes()); // :155
// ```
//
// Its `[hardened_panic_boundary] mir_assert::Overflow(Sub)` twin was PROVED
// (clean-kernel-certified) on the store seal `321aaeda75` and on `6606d3bdf2`, and
// is UNKNOWN from `62f89f111a` on (`1b185739cf`, `2615acefeb`, `0a1bc12a09`,
// `f22fc270d1`, the channel `b58a105dde`). MEASURED 2026-10-14 with each seal's
// own `trustc` under `TRUST_ASSERT_DEBUG=1`: `promote_kernel_certifiable` asks
// `certify_vc` for this row and gets `true` on the first two seals, `false` on
// every later one, on aterm-digest's own `sha256.rs` and on the five-line
// reproducer in row 1 of the fixture. The compiler then tries the native full
// verifier, whose status for `finalize` is Unsupported ("constructor member has no
// complete exact root invocation path": `compress`'s `for i in 16..64`), and the
// row is withheld. That native refusal is not the cause: the reproducer has no
// callee at all, its native status is Unknown instead, and it loses the row too.
//
// THE CAUSE. `aebf15b1ed` (B2, 2026-09-29) gave the twin the full type-range
// battery (`hardened_twin_type_ranges`). The facts are true, and the violation core
// `Or([64 - 8 < 0, 64 - 8 > u64::MAX])` is still refuted by the two closed facts
// `0 <= 64 - 8 <= u64::MAX` beside it. But `certify_disjunctive_contradiction`
// builds its chain edges from the WHOLE context: 35/36 augmented edges on the
// `6606d3bdf2` spelling of the reproducer, 54/55 on `62f89f111a`'s and
// `b58a105dde`'s, past `refute_via_chain_edges`' cap of 48. Its relevance-pruned
// retry keys on the disjunction's VARIABLES; a closed disjunction has none, so the
// pruned context is the full one and the retry is skipped.
//
// THE FIX is a new last lane, `certify_closed_disjunction_in_closed_context`: a
// variable-free disjunction refuted against the variable-free conjuncts of the
// same violation, through the disjunctive lane's own builder (ay's UNSAT
// cross-check and the clean-kernel re-check unchanged). Dropping conjuncts only
// weakens the refuted system; the controls below hold that it still refutes
// nothing that can actually overflow.
//
// The fixture is `format!("{:?}", formula)` of the real twin formulas the
// compiler generated (`TRUST_DUMP_V2_VC=1`, channel `trustc` `b58a105dde`, and
// `6606d3bdf2` for row 2); `fixture_parses_back_to_the_captured_bytes` holds the
// reader to them byte for byte.
//
//   row 0  aterm-digest `sha256.rs:155:17`, `Sha256::finalize`, b58a105dde
//   row 1  the five-line reproducer (`x2_mark_inc`, lines 141-142 + 154-155), b58a105dde
//   row 2  the same reproducer as `6606d3bdf2` generated it (35/36 edges)
//   row 3  the reproducer with the last subtraction made `8 - BLOCK_LEN`: it
//          underflows on every execution (ay refutes it, counterexample printed)
//
// Author: Andrew Yates. Copyright 2026 Andrew Yates. License: Apache-2.0 OR MIT.

use trust_types::{Formula, HardenedVcCategory, Sort, SourceSpan, VcKind, VerificationCondition};

const CAPTURE: &str = include_str!("fixtures/closed-sub-twin-violations.txt");

fn captured_lines() -> Vec<&'static str> {
    CAPTURE.lines().map(str::trim).filter(|l| !l.is_empty()).collect()
}

/// Recursive-descent reader for the `Formula` derive-`Debug` rendering (the
/// reader of `path_membership_disjunction.rs`, plus `Sub` and `Implies`). Only the
/// constructors the capture contains are accepted; anything else panics.
struct Reader<'a> {
    s: &'a [u8],
    i: usize,
}

impl<'a> Reader<'a> {
    fn new(s: &'a str) -> Self {
        Reader { s: s.as_bytes(), i: 0 }
    }
    fn ws(&mut self) {
        while self.i < self.s.len() && (self.s[self.i] as char).is_whitespace() {
            self.i += 1;
        }
    }
    fn peek(&mut self) -> u8 {
        self.ws();
        assert!(self.i < self.s.len(), "unexpected end of input");
        self.s[self.i]
    }
    fn eat(&mut self, c: u8) {
        let got = self.peek();
        assert_eq!(got as char, c as char, "expected {} at byte {}", c as char, self.i);
        self.i += 1;
    }
    fn ident(&mut self) -> String {
        self.ws();
        let start = self.i;
        while self.i < self.s.len()
            && (self.s[self.i].is_ascii_alphanumeric() || self.s[self.i] == b'_')
        {
            self.i += 1;
        }
        assert!(self.i > start, "expected an identifier at byte {}", self.i);
        String::from_utf8(self.s[start..self.i].to_vec()).expect("ascii identifier")
    }
    fn string(&mut self) -> String {
        self.eat(b'"');
        let start = self.i;
        while self.s[self.i] != b'"' {
            assert_ne!(self.s[self.i], b'\\', "escaped string in the capture; extend the reader");
            self.i += 1;
        }
        let out = String::from_utf8(self.s[start..self.i].to_vec()).expect("utf8 var name");
        self.i += 1;
        out
    }
    fn int(&mut self) -> i128 {
        self.ws();
        let start = self.i;
        if self.peek() == b'-' {
            self.i += 1;
        }
        while self.i < self.s.len() && self.s[self.i].is_ascii_digit() {
            self.i += 1;
        }
        std::str::from_utf8(&self.s[start..self.i]).expect("ascii").parse().expect("i128 literal")
    }
    fn list(&mut self) -> Vec<Formula> {
        self.eat(b'[');
        let mut out = Vec::new();
        if self.peek() == b']' {
            self.i += 1;
            return out;
        }
        loop {
            out.push(self.formula());
            if self.peek() == b',' {
                self.i += 1;
            } else {
                break;
            }
        }
        self.eat(b']');
        out
    }
    fn sort(&mut self) -> Sort {
        match self.ident().as_str() {
            "Int" => Sort::Int,
            "Bool" => Sort::Bool,
            other => panic!("unhandled sort {other}"),
        }
    }
    fn formula(&mut self) -> Formula {
        let ctor = self.ident();
        self.eat(b'(');
        let out = match ctor.as_str() {
            "And" => Formula::And(self.list()),
            "Or" => Formula::Or(self.list()),
            "Not" => Formula::Not(Box::new(self.formula())),
            "Eq" | "Le" | "Lt" | "Ge" | "Gt" | "Sub" | "Implies" => {
                let a = Box::new(self.formula());
                self.eat(b',');
                let b = Box::new(self.formula());
                match ctor.as_str() {
                    "Eq" => Formula::Eq(a, b),
                    "Le" => Formula::Le(a, b),
                    "Ge" => Formula::Ge(a, b),
                    "Gt" => Formula::Gt(a, b),
                    "Sub" => Formula::Sub(a, b),
                    "Implies" => Formula::Implies(a, b),
                    _ => Formula::Lt(a, b),
                }
            }
            "Var" => {
                let name = self.string();
                self.eat(b',');
                Formula::Var(name, self.sort())
            }
            "Int" => Formula::Int(self.int()),
            "Bool" => match self.ident().as_str() {
                "true" => Formula::Bool(true),
                "false" => Formula::Bool(false),
                other => panic!("unhandled Bool payload {other}"),
            },
            other => panic!("unhandled Formula constructor {other}"),
        };
        self.eat(b')');
        out
    }
}

fn parse(line: &str) -> Formula {
    let mut r = Reader::new(line);
    let f = r.formula();
    r.ws();
    assert_eq!(r.i, r.s.len(), "trailing input after the formula");
    f
}

fn row(i: usize) -> Formula {
    parse(captured_lines()[i])
}

/// The VC the compiler hands `certify_vc` for the twin (kind, callee and detail as
/// `trust-vcgen`'s `append_assert_panic_vcs` spells them).
fn twin_vc(formula: Formula) -> VerificationCondition {
    VerificationCondition {
        kind: VcKind::HardenedBoundary {
            category: HardenedVcCategory::PanicBoundary,
            callee: "mir_assert::Overflow(Sub)".to_string(),
            detail: "MIR arithmetic assert can panic; hardened code needs proven arithmetic \
                     preconditions"
                .to_string(),
        },
        function: "repro::Sha256::finalize".into(),
        location: SourceSpan {
            file: "src/sha256.rs".into(),
            line_start: 155,
            col_start: 17,
            line_end: 155,
            col_end: 30,
        },
        formula,
        contract_metadata: None,
        obligation: None,
    }
}

/// Certify, then replay the certificate against the same obligation identity, as
/// a consumer would. `None` when nothing was certified.
fn certified_and_replayed(formula: Formula) -> Option<bool> {
    let vc = twin_vc(formula);
    match trust_certify::certify_vc(&vc)? {
        trust_ir::ProofEvidence::CleanCic { term, context, lineage, .. } => {
            Some(trust_certify::recheck_vc(&vc, &term, &context, &lineage))
        }
        _ => Some(false),
    }
}

fn sub(a: i128, b: i128) -> Formula {
    Formula::Sub(Box::new(Formula::Int(a)), Box::new(Formula::Int(b)))
}

/// Replace every node equal to `from` with `to`.
fn replace(f: &Formula, from: &Formula, to: &Formula) -> Formula {
    if f == from {
        return to.clone();
    }
    let r = |x: &Formula| Box::new(replace(x, from, to));
    match f {
        Formula::And(cs) => Formula::And(cs.iter().map(|c| replace(c, from, to)).collect()),
        Formula::Or(cs) => Formula::Or(cs.iter().map(|c| replace(c, from, to)).collect()),
        Formula::Not(a) => Formula::Not(r(a)),
        Formula::Eq(a, b) => Formula::Eq(r(a), r(b)),
        Formula::Lt(a, b) => Formula::Lt(r(a), r(b)),
        Formula::Le(a, b) => Formula::Le(r(a), r(b)),
        Formula::Gt(a, b) => Formula::Gt(r(a), r(b)),
        Formula::Ge(a, b) => Formula::Ge(r(a), r(b)),
        Formula::Sub(a, b) => Formula::Sub(r(a), r(b)),
        Formula::Implies(a, b) => Formula::Implies(r(a), r(b)),
        other => other.clone(),
    }
}

/// The twin's violation core for `a - b` at `usize`: `a - b < 0 ∨ a - b > u64::MAX`.
fn core(a: i128, b: i128) -> Formula {
    Formula::Or(vec![
        Formula::Lt(Box::new(sub(a, b)), Box::new(Formula::Int(0))),
        Formula::Gt(Box::new(sub(a, b)), Box::new(Formula::Int(i128::from(u64::MAX)))),
    ])
}

// ---------------------------------------------------------------------------
// Fidelity of the capture.
// ---------------------------------------------------------------------------

#[test]
fn fixture_parses_back_to_the_captured_bytes() {
    let lines = captured_lines();
    assert_eq!(lines.len(), 4, "the capture holds four twin formulas");
    for (i, line) in lines.iter().enumerate() {
        assert_eq!(&format!("{:?}", parse(line)), line, "row {i} did not round-trip");
    }
    // Rows 0-2 carry the closed core of `64 - 8`; row 3 the core of `8 - 64`.
    for i in 0..3 {
        assert!(captured_lines()[i].contains(&format!("{:?}", core(64, 8))), "row {i}");
    }
    assert!(captured_lines()[3].contains(&format!("{:?}", core(8, 64))), "row 3");
}

// ---------------------------------------------------------------------------
// The rows this restores.
// ---------------------------------------------------------------------------

/// aterm-digest `sha256.rs:155:17`, as the channel `b58a105dde` generates it.
/// RED before the closed-context lane (measured: `certify_vc` = None on this
/// formula with the lane's call removed), GREEN with it; the certificate replays.
#[test]
fn aterm_digest_sha256_155_twin_certifies_and_replays() {
    assert_eq!(certified_and_replayed(row(0)), Some(true));
}

/// The five-line reproducer's twin (54/55 augmented edges in the disjunctive
/// lane, over its cap of 48).
#[test]
fn reproducer_twin_certifies_and_replays() {
    assert_eq!(certified_and_replayed(row(1)), Some(true));
}

/// Control: the `6606d3bdf2` spelling of the same twin (35/36 edges) certified
/// before this lane existed, through the disjunctive lane, and still does.
#[test]
fn the_6606d3bd_spelling_still_certifies() {
    assert_eq!(certified_and_replayed(row(2)), Some(true));
}

// ---------------------------------------------------------------------------
// Controls: what can overflow is never certified.
// ---------------------------------------------------------------------------

/// A constant subtraction that underflows on every execution (`8 - BLOCK_LEN`),
/// generated by the compiler: ay refutes its twin with a counterexample, and no
/// lane may certify it.
#[test]
fn a_compiler_generated_underflowing_twin_declines() {
    assert_eq!(certified_and_replayed(row(3)), None);
}

/// The captured rows with ONLY the violation core swapped for a core that really
/// underflows (`8 - 64 < 0` is true). The closed context still says
/// `0 <= 64 - 8 <= u64::MAX`, which does not touch the new core, so the system is
/// satisfiable and must decline. This is the mutation that a lane keyed on "some
/// closed conjunct is false" or on the wrong `Or` would get wrong.
#[test]
fn a_swapped_underflowing_core_declines() {
    for i in 0..3 {
        let mutated = replace(&row(i), &core(64, 8), &core(8, 64));
        assert_ne!(mutated, row(i), "row {i}: the core was found and replaced");
        assert_eq!(certified_and_replayed(mutated), None, "row {i}");
    }
}

/// A closed disjunct that is TRUE without overflow (`64 - 8 < 57`): satisfiable,
/// declines. Holds that the lane refutes disjuncts by chains to the context, not
/// by their being closed.
#[test]
fn a_true_closed_disjunct_declines() {
    let true_core = Formula::Or(vec![
        Formula::Lt(Box::new(sub(64, 8)), Box::new(Formula::Int(57))),
        Formula::Gt(Box::new(sub(64, 8)), Box::new(Formula::Int(i128::from(u64::MAX)))),
    ]);
    for i in 0..2 {
        let mutated = replace(&row(i), &core(64, 8), &true_core);
        assert_ne!(mutated, row(i), "row {i}: the core was found and replaced");
        assert_eq!(certified_and_replayed(mutated), None, "row {i}");
    }
}

/// Every constant pair a, b in 0..=72 at the core, with the context left as
/// captured: certified exactly when `a - b` lies in `0..=u64::MAX`, i.e. `a >= b`,
/// AND the closed context can see it — which, for a core other than `64 - 8`,
/// it cannot (the context's closed facts are about `64 - 8`), so only `(64, 8)`
/// certifies. The oracle is the arithmetic; nothing else may certify.
#[test]
fn exhaustive_constant_pairs_follow_the_arithmetic() {
    let base = row(1);
    for a in (0..=72).step_by(8) {
        for b in (0..=72).step_by(8) {
            let mutated = replace(&base, &core(64, 8), &core(a, b));
            let got = certified_and_replayed(mutated);
            if a < b {
                assert_eq!(got, None, "{a} - {b} underflows: must decline");
            } else if (a, b) == (64, 8) {
                assert_eq!(got, Some(true), "the captured core certifies");
            } else {
                // a >= b: the core is false, but its refutation needs `0 <= a - b`,
                // which no conjunct states; declining is the fail-closed answer,
                // and a certificate would also be correct. Only a WRONG
                // certificate (one that does not replay) is a failure.
                assert_ne!(got, Some(false), "{a} - {b}: a certificate must replay");
            }
        }
    }
}
