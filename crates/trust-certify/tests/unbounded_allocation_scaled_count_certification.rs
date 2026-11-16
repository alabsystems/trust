// Trust (2026-09-23, D3/W1a): the interval-decided `unbounded_allocation` row
// of `(0..n.min(8) as u32).collect()` (ordinary-Rust sweep s20) earns `Certified`
// ONLY once vcgen folds the literal-zero range start out of its count atoms.
//
// Each formula below is VERBATIM the violation formula stage-1 `trustc`
// (`de437e35d`, 2026-09-23) handed the interval backend — and, through
// `certify_all`, `trust_certify::certify_vc` — captured with
//
// ```text
// TRUST_INTERVAL_DEBUG=1 trustc --edition 2021 -Ztrust-verify=on --crate-type lib \
//   -Ztrust-verify-timeout-ms=1 <file>.rs
// ```
//
// At that commit the count is spelled `Sub(end, Int(0))`, and the kernel's
// scaled-chain recognizer (`chain_node` / `int_var_name`) wants a BARE variable
// under the byte atom's `Mul(stride, _)`, so the row is not certifiable and, with
// `ay` starved (`-Ztrust-verify-timeout-ms=1`), reports
// `[unbounded_allocation] UNKNOWN (interval): Proved label lacked exact
// kernel/native proof authority`. `trust-vcgen`'s `fold_sub_literal_zero`
// (`generate/alloc_vcs.rs`) rewrites `end - 0` to `end` in the OBLIGATION, which
// is exact over the integers; the folded spelling below is the literal textual
// image of that rewrite on the captured formula.
//
// What this file pins:
//   * the captured s20 / sibling formulas do NOT certify unfolded (the recorded
//     limitation — if the kernel learns `Mul(k, x - 0)` this flips, harmlessly);
//   * they DO certify folded (the W1a claim, and the `starved_s20` ui revision's
//     premise);
//   * a genuinely reachable allocation certifies nothing, folded or not
//     (byte boundary `n.min(1 << 29)`, unbounded `0..n`);
//   * the NON-ZERO literal start stays uncertified as vcgen must leave it — and a
//     WRONG fold that dropped the literal WOULD certify it. That last case is the
//     false proof the literal-zero-only rule exists to prevent; it is asserted so
//     the rail's necessity is measured, not argued.
//
// Each claim is asserted twice: on the capture, and on the spelling vcgen emits
// since its 256 MiB byte budget was deleted (`without_byte_budget`, which drops
// the capture's one `Ge(Mul(stride, count), 2^28)` atom).
//
// Author: Andrew Yates. Copyright 2026 Andrew Yates. License: Apache-2.0 OR MIT.

use trust_types::{Formula, Sort, SourceSpan, VcKind, VerificationCondition};

/// s20: `pub fn build(n: usize) -> Vec<u32> { (0..n.min(8) as u32).collect() }`
const S20: &str = r###"And([And([Ge(Var("n", Int), Int(0)), Le(Var("n", Int), Int(18446744073709551615))]), And([Le(Var("_4", Int), Int(8)), Le(Var("_3", Int), Int(8)), Le(Var("_4", Int), Int(8)), And([Le(Var("_4", Int), Var("n", Int)), Le(Var("_4", Int), Int(8)), And([And([Ge(Var("n", Int), Int(0)), Le(Var("n", Int), Int(18446744073709551615))]), And([And([Le(Int(0), Var("_3", Int)), Le(Var("_3", Int), Int(4294967295))]), And([Le(Int(0), Var("_3", Int)), Le(Var("_3", Int), Int(4294967295))]), And([And([Le(Int(0), Var("n", Int)), Le(Var("n", Int), Int(18446744073709551615))]), And([And([Le(Int(0), Var("_3", Int)), Le(Var("_3", Int), Int(4294967295))]), Eq(Var("_2.1#s1_1", Int), Var("_3", Int)), Eq(Var("_2@0.1#s1_pre", Int), Var("_3", Int)), Or([Ge(Sub(Var("_3", Int), Int(0)), Int(268435456)), Ge(Mul(Int(8), Sub(Var("_3", Int), Int(0))), Int(268435456)), Ge(Mul(Int(8), Sub(Var("_3", Int), Int(0))), Int(9223372036854775807))])])])])])])])])"###;

/// folded sibling: `pub fn a(n: usize) -> Vec<u32> { (0..(n as u32).min(8)).collect() }`
const SIB_A: &str = r###"And([And([Ge(Var("n", Int), Int(0)), Le(Var("n", Int), Int(18446744073709551615))]), And([Le(Var("_3", Int), Int(8)), Le(Var("_3", Int), Int(8)), And([And([Le(Int(0), Var("_4", Int)), Le(Var("_4", Int), Int(4294967295))]), Le(Var("_3", Int), Var("_4", Int)), Le(Var("_3", Int), Int(8)), And([And([Ge(Var("n", Int), Int(0)), Le(Var("n", Int), Int(18446744073709551615))]), And([And([Le(Int(0), Var("_3", Int)), Le(Var("_3", Int), Int(4294967295))]), And([Le(Int(0), Var("_3", Int)), Le(Var("_3", Int), Int(4294967295))]), And([And([Le(Int(0), Var("n", Int)), Le(Var("n", Int), Int(18446744073709551615))]), And([Eq(Var("_2.1#s1_0", Int), Var("_3", Int)), Eq(Var("_2@0.1#s1_pre", Int), Var("_3", Int)), Or([Ge(Sub(Var("_3", Int), Int(0)), Int(268435456)), Ge(Mul(Int(8), Sub(Var("_3", Int), Int(0))), Int(268435456)), Ge(Mul(Int(8), Sub(Var("_3", Int), Int(0))), Int(9223372036854775807))])])])])])])])])"###;

/// byte boundary: `pub fn build(n: usize) -> Vec<u32> { (0..n.min(1 << 29) as u32).collect() }`
const BYTE_BOUNDARY: &str = r###"And([And([Ge(Var("_5", Int), Int(0)), Le(Var("_5", Int), Int(18446744073709551615)), Ge(Var("n", Int), Int(0)), Le(Var("n", Int), Int(18446744073709551615))]), And([Le(Var("_6", Int), Int(29)), And([Eq(Var("_6", Int), Int(29)), Eq(Var("_7", Bool), Lt(Var("_6", Int), Int(64))), Eq(Var("_5", Int), Int(536870912)), Le(Var("_4", Int), Var("n", Int)), Le(Var("_4", Int), Var("_5", Int)), And([Var("_7", Bool), And([Ge(Var("n", Int), Int(0)), Le(Var("n", Int), Int(18446744073709551615))]), And([And([Le(Int(0), Var("_3", Int)), Le(Var("_3", Int), Int(4294967295))]), And([Le(Int(0), Var("_3", Int)), Le(Var("_3", Int), Int(4294967295))]), And([And([Le(Int(0), Var("n", Int)), Le(Var("n", Int), Int(18446744073709551615))]), And([And([Le(Int(0), Var("_3", Int)), Le(Var("_3", Int), Int(4294967295))]), Eq(Var("_2.1#s2_1", Int), Var("_3", Int)), Eq(Var("_2@0.1#s2_pre", Int), Var("_3", Int)), Or([Ge(Sub(Var("_3", Int), Int(0)), Int(268435456)), Ge(Mul(Int(8), Sub(Var("_3", Int), Int(0))), Int(268435456)), Ge(Mul(Int(8), Sub(Var("_3", Int), Int(0))), Int(9223372036854775807))])])])])])])])])"###;

/// unbounded: `pub fn build(n: usize) -> Vec<u32> { (0..n as u32).collect() }`
const UNBOUNDED: &str = r###"And([And([Ge(Var("n", Int), Int(0)), Le(Var("n", Int), Int(18446744073709551615))]), And([And([Ge(Var("n", Int), Int(0)), Le(Var("n", Int), Int(18446744073709551615))]), And([And([Le(Int(0), Var("_3", Int)), Le(Var("_3", Int), Int(4294967295))]), And([Le(Int(0), Var("_3", Int)), Le(Var("_3", Int), Int(4294967295))]), And([And([Le(Int(0), Var("n", Int)), Le(Var("n", Int), Int(18446744073709551615))]), And([And([Le(Int(0), Var("_3", Int)), Le(Var("_3", Int), Int(4294967295))]), Eq(Var("_2.1#s0_1", Int), Var("_3", Int)), Eq(Var("_2@0.1#s0_pre", Int), Var("_3", Int)), Or([Ge(Sub(Var("_3", Int), Int(0)), Int(268435456)), Ge(Mul(Int(8), Sub(Var("_3", Int), Int(0))), Int(268435456)), Ge(Mul(Int(8), Sub(Var("_3", Int), Int(0))), Int(9223372036854775807))])])])])])])"###;

/// non-zero literal start: `pub fn build(n: usize) -> Vec<i64> { (-268435456i64..(n.min(8) as i64)).collect::<Vec<i64>>() }`
const NONZERO_LITERAL_START: &str = r###"And([And([Ge(Var("n", Int), Int(0)), Le(Var("n", Int), Int(18446744073709551615))]), And([Le(Var("_4", Int), Int(8)), Le(Var("_3", Int), Int(8)), Le(Var("_4", Int), Int(8)), And([Le(Var("_4", Int), Var("n", Int)), Le(Var("_4", Int), Int(8)), And([And([Ge(Var("n", Int), Int(0)), Le(Var("n", Int), Int(18446744073709551615))]), And([And([Le(Int(-9223372036854775808), Var("_3", Int)), Le(Var("_3", Int), Int(9223372036854775807))]), And([Le(Int(-9223372036854775808), Var("_3", Int)), Le(Var("_3", Int), Int(9223372036854775807))]), And([And([Le(Int(0), Var("n", Int)), Le(Var("n", Int), Int(18446744073709551615))]), And([And([Le(Int(-9223372036854775808), Var("_3", Int)), Le(Var("_3", Int), Int(9223372036854775807))]), Eq(Var("_2.1#s1_1", Int), Var("_3", Int)), Eq(Var("_2@0.1#s1_pre", Int), Var("_3", Int)), Or([Ge(Sub(Var("_3", Int), Int(-268435456)), Int(268435456)), Ge(Mul(Int(16), Sub(Var("_3", Int), Int(-268435456))), Int(268435456)), Ge(Mul(Int(16), Sub(Var("_3", Int), Int(-268435456))), Int(9223372036854775807))])])])])])])])])"###;

/// positive literal start: `pub fn build(n: usize) -> Vec<u32> { (5u32..n.min(8) as u32).collect() }`
const POSITIVE_LITERAL_START: &str = r###"And([And([Ge(Var("n", Int), Int(0)), Le(Var("n", Int), Int(18446744073709551615))]), And([Le(Var("_4", Int), Int(8)), Le(Var("_3", Int), Int(8)), Le(Var("_4", Int), Int(8)), And([Le(Var("_4", Int), Var("n", Int)), Le(Var("_4", Int), Int(8)), And([And([Ge(Var("n", Int), Int(0)), Le(Var("n", Int), Int(18446744073709551615))]), And([And([Le(Int(0), Var("_3", Int)), Le(Var("_3", Int), Int(4294967295))]), And([Le(Int(0), Var("_3", Int)), Le(Var("_3", Int), Int(4294967295))]), And([And([Le(Int(0), Var("n", Int)), Le(Var("n", Int), Int(18446744073709551615))]), And([And([Le(Int(0), Var("_3", Int)), Le(Var("_3", Int), Int(4294967295))]), Eq(Var("_2.1#s1_1", Int), Var("_3", Int)), Eq(Var("_2@0.1#s1_pre", Int), Var("_3", Int)), Or([Ge(Sub(Var("_3", Int), Int(5)), Int(268435456)), Ge(Mul(Int(8), Sub(Var("_3", Int), Int(5))), Int(268435456)), Ge(Mul(Int(8), Sub(Var("_3", Int), Int(5))), Int(9223372036854775807))])])])])])])])])"###;

/// Minimal reader for the `Debug` spelling of `Formula` used in the captures.
struct Reader<'a> {
    s: &'a [u8],
    i: usize,
}

impl Reader<'_> {
    fn skip_ws(&mut self) {
        while self.i < self.s.len() && self.s[self.i] == b' ' {
            self.i += 1;
        }
    }
    fn eat(&mut self, c: u8) {
        self.skip_ws();
        assert_eq!(self.s[self.i], c, "expected `{}` at byte {}", c as char, self.i);
        self.i += 1;
    }
    fn peek(&mut self) -> u8 {
        self.skip_ws();
        self.s[self.i]
    }
    fn ident(&mut self) -> String {
        self.skip_ws();
        let start = self.i;
        while self.s[self.i].is_ascii_alphanumeric() || self.s[self.i] == b'_' {
            self.i += 1;
        }
        String::from_utf8(self.s[start..self.i].to_vec()).unwrap()
    }
    fn int(&mut self) -> i128 {
        self.skip_ws();
        let start = self.i;
        if self.s[self.i] == b'-' {
            self.i += 1;
        }
        while self.s[self.i].is_ascii_digit() {
            self.i += 1;
        }
        std::str::from_utf8(&self.s[start..self.i]).unwrap().parse().unwrap()
    }
    fn string(&mut self) -> String {
        self.eat(b'"');
        let start = self.i;
        while self.s[self.i] != b'"' {
            self.i += 1;
        }
        let out = String::from_utf8(self.s[start..self.i].to_vec()).unwrap();
        self.i += 1;
        out
    }
    fn list(&mut self) -> Vec<Formula> {
        self.eat(b'[');
        let mut out = Vec::new();
        while self.peek() != b']' {
            out.push(self.formula());
            if self.peek() == b',' {
                self.eat(b',');
            }
        }
        self.eat(b']');
        out
    }
    fn formula(&mut self) -> Formula {
        let name = self.ident();
        self.eat(b'(');
        let out = match name.as_str() {
            "And" => Formula::And(self.list()),
            "Or" => Formula::Or(self.list()),
            "Not" => Formula::Not(Box::new(self.formula())),
            "Int" => Formula::Int(self.int()),
            "Var" => {
                let var = self.string();
                self.eat(b',');
                let sort = match self.ident().as_str() {
                    "Int" => Sort::Int,
                    "Bool" => Sort::Bool,
                    other => panic!("unexpected sort {other}"),
                };
                Formula::Var(var, sort)
            }
            op => {
                let a = Box::new(self.formula());
                self.eat(b',');
                let b = Box::new(self.formula());
                match op {
                    "Ge" => Formula::Ge(a, b),
                    "Le" => Formula::Le(a, b),
                    "Gt" => Formula::Gt(a, b),
                    "Lt" => Formula::Lt(a, b),
                    "Eq" => Formula::Eq(a, b),
                    "Sub" => Formula::Sub(a, b),
                    "Add" => Formula::Add(a, b),
                    "Mul" => Formula::Mul(a, b),
                    other => panic!("unexpected operator {other}"),
                }
            }
        };
        self.eat(b')');
        out
    }
}

fn parse(text: &str) -> Formula {
    let mut reader = Reader { s: text.as_bytes(), i: 0 };
    let formula = reader.formula();
    assert_eq!(reader.i, text.len(), "trailing input after the formula");
    formula
}

/// The literal image of `fold_sub_literal_zero` on a captured count `end - 0`.
fn fold_zero_start(text: &str, end: &str) -> String {
    let from = format!("Sub(Var(\"{end}\", Int), Int(0))");
    assert!(text.contains(&from), "the capture carries no `{from}`");
    let folded = text.replace(&from, &format!("Var(\"{end}\", Int)"));
    assert!(!folded.contains("Sub("), "the fold must leave no subtraction behind");
    folded
}

/// The 256 MiB availability byte budget, `2^28` bytes, as a captured atom's bound.
const DELETED_BYTE_BUDGET: &str = "Int(268435456)";

/// The spelling trust-vcgen emits today. The captures predate the deletion of
/// its 256 MiB byte budget (with trust-ir's `ALLOC_BYTE_BUDGET`,
/// 2026-09-29; DECISION_QUEUE ALLOC-BYTE-1), so each failure disjunction still
/// holds one `Ge(Mul(stride, count), 2^28)` byte atom. This removes exactly that
/// atom and keeps the element ceiling `Ge(count, 2^28)` and the capacity atom
/// `Ge(Mul(stride, count), isize::MAX)`, the two atoms vcgen still emits. Every
/// claim below is asserted on both spellings.
fn without_byte_budget(text: &str) -> String {
    let mut out = String::with_capacity(text.len());
    let mut removed = 0;
    let mut rest = text;
    while let Some(at) = rest.find("Ge(Mul(") {
        out.push_str(&rest[..at]);
        let atom = &rest[at..];
        // The atom ends at the parenthesis that closes its `Ge(`.
        let mut depth = 0usize;
        let mut end = None;
        for (i, b) in atom.bytes().enumerate() {
            match b {
                b'(' => depth += 1,
                b')' => {
                    depth -= 1;
                    if depth == 0 {
                        end = Some(i + 1);
                        break;
                    }
                }
                _ => {}
            }
        }
        let end = end.expect("a `Ge(` atom closes");
        let body = &atom[..end];
        if body.ends_with(&format!(", {DELETED_BYTE_BUDGET})")) {
            removed += 1;
            // The byte atom sits between the element ceiling and the capacity
            // atom, so a `, ` separator follows it.
            let after = &atom[end..];
            assert!(after.starts_with(", "), "the byte atom is not mid-disjunction: {body}");
            rest = &after[2..];
        } else {
            out.push_str(body);
            rest = &atom[end..];
        }
    }
    out.push_str(rest);
    assert_eq!(removed, 1, "each capture holds exactly one byte-budget atom");
    out
}

/// The capture as stage 1 handed it (with the deleted byte atom), then as
/// trust-vcgen spells it today (without).
fn both_spellings(text: &str) -> [(&'static str, String); 2] {
    [("captured", text.to_string()), ("current", without_byte_budget(text))]
}

fn certifies(count: &str, text: &str) -> bool {
    let vc = VerificationCondition {
        kind: VcKind::UnboundedAllocation {
            callee: "Iterator::collect".into(),
            count: count.into(),
            detail: "captured stage-1 violation formula".into(),
        },
        function: "s20::build".into(),
        location: SourceSpan {
            file: "s20.rs".into(),
            line_start: 1,
            col_start: 38,
            line_end: 1,
            col_end: 69,
        },
        formula: parse(text),
        contract_metadata: None,
        obligation: None,
    };
    trust_certify::certify_vc(&vc).is_some()
}

#[test]
fn instrument_controls_certify_unsat_and_decline_sat() {
    let captured_or = "Or([Ge(Sub(Var(\"_3\", Int), Int(0)), Int(268435456)), \
        Ge(Mul(Int(8), Sub(Var(\"_3\", Int), Int(0))), Int(268435456)), \
        Ge(Mul(Int(8), Sub(Var(\"_3\", Int), Int(0))), Int(9223372036854775807))])";
    assert!(S20.contains(captured_or), "the s20 capture's failure disjunction moved");
    let unsat = S20.replace(captured_or, "Or([Ge(Var(\"_3\", Int), Int(268435456))])");
    let sat = S20.replace(captured_or, "Or([Ge(Var(\"_3\", Int), Int(8))])");
    assert!(certifies("c", &unsat), "positive control: `_3 <= 8 /\\ _3 >= 2^28` is UNSAT");
    assert!(!certifies("c", &sat), "negative control: `_3 <= 8 /\\ _3 >= 8` is SAT");
}

#[test]
fn captured_zero_start_rows_do_not_certify_unfolded() {
    for (spelling, s20) in both_spellings(S20) {
        assert!(!certifies("(- _3 0)", &s20), "s20, {spelling}");
    }
    for (spelling, sib_a) in both_spellings(SIB_A) {
        assert!(!certifies("(- _3 0)", &sib_a), "sibling, {spelling}");
    }
}

#[test]
fn captured_zero_start_rows_certify_once_folded() {
    for (spelling, s20) in both_spellings(S20) {
        assert!(
            certifies("(- _3 0)", &fold_zero_start(&s20, "_3")),
            "s20 must certify folded, {spelling}"
        );
    }
    for (spelling, sib_a) in both_spellings(SIB_A) {
        assert!(
            certifies("(- _3 0)", &fold_zero_start(&sib_a, "_3")),
            "sibling must certify folded, {spelling}"
        );
    }
}

#[test]
fn reachable_allocations_certify_nothing_folded_or_not() {
    for (name, text) in [("byte_boundary", BYTE_BOUNDARY), ("unbounded", UNBOUNDED)] {
        for (spelling, text) in both_spellings(text) {
            assert!(!certifies("(- _3 0)", &text), "{name} unfolded, {spelling}");
            assert!(
                !certifies("(- _3 0)", &fold_zero_start(&text, "_3")),
                "{name} folded, {spelling}"
            );
        }
    }
}

#[test]
fn a_nonzero_literal_start_must_not_be_folded() {
    let literal = "Sub(Var(\"_3\", Int), Int(-268435456))";
    assert!(NONZERO_LITERAL_START.contains(literal), "the capture's count moved");
    for (spelling, text) in both_spellings(NONZERO_LITERAL_START) {
        assert!(
            !certifies("(- _3 (- 268435456))", &text),
            "as vcgen leaves it, the reachable allocation certifies nothing ({spelling})"
        );
        let wrong_fold = text.replace(literal, "Var(\"_3\", Int)");
        assert!(
            certifies("(- _3 (- 268435456))", &wrong_fold),
            "a fold that dropped the non-zero literal WOULD certify a reachable 2^28-element \
             allocation — the false proof the literal-zero-only rule prevents ({spelling})"
        );
    }
}

#[test]
fn a_positive_literal_start_is_not_certifiable_today() {
    // Not a soundness rail (folding `5` away would only over-count), but the
    // record that the general `end - start` count still reaches only
    // `SolverRevalidated`; `ChainNode::ScaledDiff` is the follow-up.
    for (spelling, text) in both_spellings(POSITIVE_LITERAL_START) {
        assert!(!certifies("(- _3 5)", &text), "{spelling}");
    }
}
