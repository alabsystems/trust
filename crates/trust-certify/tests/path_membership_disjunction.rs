// Kernel certification of the PER-PATH exhaustive-enum `otherwise -> unreachable`
// trap: a top-level `Or` OVER PATHS, each path carrying its own discriminant
// membership contradiction buried under sixty-to-a-hundred-and-fifty satisfiable
// facts about other locals.
//
// THE ROWS THIS CLOSES, measured rather than inferred. a3d's gate
// (`./scripts/verify.sh` over `crates/a3d-kernel`) reports, at Trust
// `2a458b9da9`:
//
// ```text
//   57 functions, 283 proved, 10 runtime-checked, 0 failed, 0 unknown
//   runtime-checked by kind: unreachable=10
//   Gate: FAIL [strict lane, exit 1]  (… / 293 total)
// ```
//
// The eleventh row was closed by `certify_membership_disjunction_resolution`
// (`fb96069407`), whose formula is the FLAT shape
// `And([And([¬E₀, ¬E₁]), Or([E₀, E₁]), Bool(true)])`. These ten are not that
// shape and the flat rung cannot see them.
//
// The whole run was re-taken with `AY_CERT_DUMP=1` on the HEAD-matching stage2
// `trustc`: 294 unique violations, of which exactly these TEN are the
// path-disjunctive unreachable family. They are pinned byte for byte in
// `tests/fixtures/a3d-unreach-path-disjunctions.txt` — ten lines, 3 KB to 242 KB
// each (3 to 29 paths). MEASURED against the crate: with this lane stubbed out, eleven
// of the 294 decline (these ten plus a bare `Bool(false)` that is not one of the
// gate's rows); with it in, only the `Bool(false)` does. Abbreviated, the family
// is:
//
// ```text
// And([ Bool(true),
//       Or([ And([ Not(Eq(_19, 0)), Not(Eq(_19, 1)),     <- the contradiction
//                  Or([Eq(_19, 0), Eq(_19, 1)]),         <- its own validity fact
//                  Or([Eq(_23, 0), Eq(_23, 1)]), …,      <- 45 OTHER locals' validity
//                  Eq(a[0;min=3]#s0_0, aex), … ]),          facts, all satisfiable
//            … 2 to 28 more path disjuncts, same internal shape … ]) ])
// ```
//
// The top level is a disjunction over PATHS — one per `?`-desugar site in the
// function — and the flat rung's pool is `[Bool(true), Or(paths)]`, in which no
// path appears negated. It declines structurally, exactly as designed. One row
// (`octree_node_count`) additionally carries the outer parameter-range context
// `Ge(depth, 0) ∧ Le(depth, u32::MAX)` around the same `Or`, which the lane
// ignores rather than consumes.
//
// THE FIX is one indirection deeper, the same step `eca5762d9e` (reified-`Bool`
// guard) was to `b76453697c` (`Ite` case split): close each PATH by the
// membership resolution it carries internally, then join the paths with
// `Or.rec`. The matching rule is not reimplemented — `membership_witnesses` is
// literally the function the flat lane calls, and the per-path term is
// `membership_resolution_false_at`, the flat lane's own `Or.rec` builder with the
// negation proofs supplied by a generator instead of an fvar slice.
//
// THE SOUNDNESS QUESTION THIS FILE EXISTS TO ANSWER. `Or` is false only when
// EVERY disjunct is false. A closer that accepted on "some path is
// contradictory" would certify a formula with a genuinely REACHABLE trap on the
// remaining path — real UB blessed by the verifier, the worst outcome available
// in this lane. `path_with_a_reachable_trap_declines` and
// `exhaustive_model_oracle_over_the_path_family` are the controls;
// `every_captured_a3d_row_certifies` is the payoff.

use std::time::Instant;

use trust_types::{Formula, Sort};

// ---------------------------------------------------------------------------
// The captured a3d violations.
//
// The fixture is `format!("{:?}", formula)` of the real `trust_types::Formula`
// the compiler handed `certify_vc`, so `parse` below is checked against the
// only oracle that matters: re-`Debug`ing the parse must reproduce the captured
// line byte for byte (`fixture_parses_back_to_the_captured_bytes`). A parser bug
// cannot quietly turn a hard formula into an easy one.
// ---------------------------------------------------------------------------

const A3D_DUMP: &str = include_str!("fixtures/a3d-unreach-path-disjunctions.txt");

fn captured_lines() -> Vec<&'static str> {
    A3D_DUMP
        .lines()
        .map(str::trim)
        .filter(|l| !l.is_empty())
        .map(|l| l.strip_prefix("CERTDUMP]").unwrap_or(l).trim())
        .collect()
}

/// Recursive-descent reader for the `Formula` derive-`Debug` rendering. Only the
/// nine constructors the capture actually contains are accepted; anything else
/// panics rather than being silently skipped.
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
            "Eq" | "Le" | "Lt" | "Ge" | "Gt" => {
                let a = Box::new(self.formula());
                self.eat(b',');
                let b = Box::new(self.formula());
                match ctor.as_str() {
                    "Eq" => Formula::Eq(a, b),
                    "Le" => Formula::Le(a, b),
                    "Ge" => Formula::Ge(a, b),
                    "Gt" => Formula::Gt(a, b),
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

fn certified(violation: &Formula) -> bool {
    matches!(
        trust_certify::certify_violation(violation),
        Some(trust_ir::ProofEvidence::CleanCic { .. })
    )
}

// ---------------------------------------------------------------------------
// Fidelity of the capture itself.
// ---------------------------------------------------------------------------

/// The reader is not trusted: re-`Debug`ing every parse must reproduce the
/// captured bytes exactly. This is what makes "these are a3d's real formulas" a
/// measurement instead of a claim.
#[test]
fn fixture_parses_back_to_the_captured_bytes() {
    let lines = captured_lines();
    assert_eq!(lines.len(), 10, "the capture holds a3d's ten remaining `[unreach]` rows");
    for (i, line) in lines.iter().enumerate() {
        let round = format!("{:?}", parse(line));
        assert_eq!(&round, line, "row {i}: the reader did not round-trip the captured formula");
    }
}

/// The SHAPE claim in this file's banner, checked against the capture rather
/// than asserted: every row flattens to a conjunct pool holding exactly one
/// `Or`, and every disjunct of that `Or` is an `And` — the nesting the flat
/// rung cannot reach.
fn flatten<'a>(f: &'a Formula, out: &mut Vec<&'a Formula>) {
    match f {
        Formula::And(children) => children.iter().for_each(|c| flatten(c, out)),
        other => out.push(other),
    }
}

#[test]
fn every_captured_row_is_an_or_over_and_paths() {
    let mut widths = Vec::new();
    for (i, line) in captured_lines().iter().enumerate() {
        let parsed = parse(line);
        let mut pool = Vec::new();
        flatten(&parsed, &mut pool);
        let ors: Vec<&&Formula> = pool.iter().filter(|c| matches!(c, Formula::Or(_))).collect();
        assert_eq!(ors.len(), 1, "row {i}: expected exactly one top-level Or conjunct");
        let Formula::Or(paths) = ors[0] else { unreachable!() };
        assert!(paths.len() >= 2, "row {i}: a single-path Or would not need this lane");
        for path in paths {
            assert!(matches!(path, Formula::And(_)), "row {i}: a path disjunct is not an And");
            // No path is itself a flat membership formula the previous rung
            // could already close: the contradiction is one level DOWN.
            let mut path_pool = Vec::new();
            flatten(path, &mut path_pool);
            assert!(
                path_pool.len() > 3,
                "row {i}: a path is small enough that the flat rung would already see it"
            );
        }
        widths.push(paths.len());
    }
    widths.sort_unstable();
    assert_eq!(widths.first(), Some(&3), "narrowest captured row");
    assert_eq!(widths.last(), Some(&29), "widest captured row");
}

// ---------------------------------------------------------------------------
// POSITIVE — the nine rows the a3d gate is stuck on.
// ---------------------------------------------------------------------------

/// FALSIFICATION CONTROL and payoff in one. Every captured a3d violation must
/// mint a `CleanCic`. At the parent commit — and the moment the
/// `certify_path_disjunction_membership` call site is removed from
/// `certify_with_identity_uncached` — all nine return `None` (measured). Nothing
/// else in the crate reaches this shape.
#[test]
fn every_captured_a3d_row_certifies() {
    for (i, line) in captured_lines().iter().enumerate() {
        let violation = parse(line);
        let started = Instant::now();
        let evidence = trust_certify::certify_violation(&violation);
        let elapsed = started.elapsed();
        let Some(trust_ir::ProofEvidence::CleanCic { term, context, lineage, .. }) = evidence
        else {
            panic!("row {i} ({} bytes) declined; the a3d gate stays red", line.len());
        };
        // The consumer independently REGENERATES the certificate from the
        // violation and compares bytes, so this also pins the lane's determinism
        // (indicator numbering, path order, and the two-level `Or.rec` shape).
        assert!(
            trust_certify::recheck_cleancic(&term, &context, &lineage, &violation),
            "row {i}: the consumer re-check rejected the producer's own certificate"
        );
        // The cost cap exists because these run to 242 KB. If a row ever needs
        // minutes the cap is in the wrong place, and a slow gate is a gate
        // people turn off.
        assert!(
            elapsed.as_secs() < 60,
            "row {i}: certification took {elapsed:?}; revisit PATH_MEMBERSHIP_MAX_*"
        );
    }
}

/// The COMPILER'S entry point, not the formula-only one. `certify_all` calls
/// `certify_vc` on the `Proved` row `promote_structurally_dead_unreachable`
/// produced, and the exact row authority is minted only from the resulting
/// `CleanCic`. Run on the WIDEST captured row (29 paths, 242 KB) so the identity
/// binding, the serialized payload and the VC-bound replay are all pinned at
/// a3d's real scale.
#[test]
fn the_widest_captured_row_certifies_through_the_vc_entry_point_and_replays() {
    let widest =
        captured_lines().into_iter().max_by_key(|l| l.len()).expect("the capture is non-empty");
    assert!(widest.len() > 200_000, "the widest captured row is 242 KB");
    let vc = trust_types::VerificationCondition {
        kind: trust_types::VcKind::Unreachable,
        function: "a3d_kernel::insphere_explicit".into(),
        location: trust_types::SourceSpan::default(),
        formula: parse(widest),
        contract_metadata: None,
        obligation: None,
    };
    let Some(trust_ir::ProofEvidence::CleanCic { term, context, lineage, .. }) =
        trust_certify::certify_vc(&vc)
    else {
        panic!("certify_vc declined a3d's widest captured `[unreach]` row");
    };
    assert!(
        trust_certify::recheck_vc_cleancic(&term, &context, &lineage, &vc),
        "the VC-bound certificate did not replay"
    );
}

// ---------------------------------------------------------------------------
// NEGATIVE CONTROLS — the ones that decide whether this lane is safe.
// ---------------------------------------------------------------------------

fn var(n: &str) -> Formula {
    Formula::Var(n.to_string(), Sort::Int)
}
fn eq(n: &str, tag: i128) -> Formula {
    Formula::Eq(Box::new(var(n)), Box::new(Formula::Int(tag)))
}
fn neq(n: &str, tag: i128) -> Formula {
    Formula::Not(Box::new(eq(n, tag)))
}
fn member(n: &str, tags: &[i128]) -> Formula {
    Formula::Or(tags.iter().map(|&t| eq(n, t)).collect())
}

/// One path of a3d's shape: the discriminant contradiction for `local`, plus
/// `noise` satisfiable validity facts about other locals, plus a state equality.
fn contradictory_path(local: &str, noise: usize) -> Formula {
    let mut parts = vec![neq(local, 0), neq(local, 1), member(local, &[0, 1])];
    for k in 0..noise {
        parts.push(member(&format!("{local}_n{k}"), &[0, 1]));
    }
    parts.push(Formula::Eq(Box::new(var(&format!("{local}_s"))), Box::new(var("aex"))));
    Formula::And(parts)
}

/// The SAME path with the membership fact widened to an uncovered tag: `local`
/// may be `2`, so the trap on this path is REACHABLE.
fn reachable_path(local: &str, noise: usize) -> Formula {
    let mut parts = vec![neq(local, 0), neq(local, 1), member(local, &[0, 1, 2])];
    for k in 0..noise {
        parts.push(member(&format!("{local}_n{k}"), &[0, 1]));
    }
    parts.push(Formula::Eq(Box::new(var(&format!("{local}_s"))), Box::new(var("aex"))));
    Formula::And(parts)
}

fn a3d_shaped(paths: Vec<Formula>) -> Formula {
    Formula::And(vec![Formula::Bool(true), Formula::Or(paths)])
}

/// The lane certifies the synthetic replica of a3d's shape, so the negative
/// controls below are DIFFERENCES from a certifying baseline rather than
/// formulas that were never in range.
#[test]
fn synthetic_replica_of_the_a3d_shape_certifies() {
    let paths = (0..6).map(|i| contradictory_path(&format!("_{i}"), 20)).collect();
    assert!(certified(&a3d_shaped(paths)), "the synthetic a3d replica did not certify");
}

/// ***THE TEST THIS LANE EXISTS TO PASS.*** Five paths are contradictory and ONE
/// is satisfiable — a genuinely reachable `unreachable_unchecked` on that path,
/// which is real UB. The whole formula is SAT and must NOT certify. A closer
/// that accepts on "some disjunct is contradictory" is a false proof of
/// unreachability; this is the single most important assertion in the file.
#[test]
fn path_with_a_reachable_trap_declines() {
    for reachable_at in [0usize, 3, 5] {
        let paths: Vec<Formula> = (0..6)
            .map(|i| {
                let name = format!("_{i}");
                if i == reachable_at {
                    reachable_path(&name, 20)
                } else {
                    contradictory_path(&name, 20)
                }
            })
            .collect();
        let violation = a3d_shaped(paths);
        // The witness: `_{reachable_at} = 2` satisfies that path's membership
        // fact and both of its exclusions, so the `Or` — and the whole
        // violation — is satisfiable.
        assert!(
            !certified(&violation),
            "a path Or with a REACHABLE trap at index {reachable_at} was certified dead \
             — a false proof of UB"
        );
    }
}

/// The degenerate version of the same failure: every path but one is dropped, so
/// the `Or` is a single satisfiable path. Pins that a one-path `Or` is not a
/// back door around the every-path gate.
#[test]
fn single_reachable_path_declines() {
    assert!(
        !certified(&a3d_shaped(vec![reachable_path("_0", 20)])),
        "a single reachable path was certified dead"
    );
}

/// A path whose exclusions and membership fact range over DIFFERENT variables.
/// Nothing connects them, the path is satisfiable, and the lane must not pair a
/// negation with a foreign disjunct.
#[test]
fn path_whose_membership_is_over_another_variable_declines() {
    let bad = Formula::And(vec![neq("_0", 0), neq("_0", 1), member("_9", &[0, 1])]);
    assert!(
        !certified(&a3d_shaped(vec![contradictory_path("_1", 5), bad])),
        "a path whose membership fact is about a different variable was closed"
    );
}

/// A NEAR-MISS tag inside one path: the guard excludes {0, 2} while the validity
/// fact ranges over {0, 1}, so `_0 = 1` satisfies that path. Pins that the
/// presence test stays exact structural equality one level down.
#[test]
fn near_miss_tag_inside_a_path_declines() {
    let bad = Formula::And(vec![neq("_0", 0), neq("_0", 2), member("_0", &[0, 1])]);
    assert!(
        !certified(&a3d_shaped(vec![contradictory_path("_1", 5), bad])),
        "a near-miss excluded tag inside a path was closed"
    );
}

/// The negations of path `i` present only on path `j`. Each path in isolation is
/// satisfiable; the lane must consult ONLY a path's own conjuncts and never
/// borrow a sibling's units.
#[test]
fn negations_borrowed_from_a_sibling_path_decline() {
    let holds_the_negations = Formula::And(vec![neq("_0", 0), neq("_0", 1), member("_9", &[0, 1])]);
    let holds_the_membership = Formula::And(vec![member("_0", &[0, 1]), neq("_9", 7)]);
    assert!(
        !certified(&a3d_shaped(vec![holds_the_negations, holds_the_membership])),
        "a path was closed with a SIBLING path's negations — paths are alternatives, \
         not conjuncts"
    );
}

// The "does the lane borrow the OUTER context's negations?" question cannot be
// asked here: `¬E₀ ∧ ¬E₁ ∧ Or([path asserting E₀, …])` is genuinely UNSAT, and
// MEASURED, an EARLIER rung certifies it with this lane disabled. Asserting a
// decline end to end would pin some other lane's behaviour, not this one. The
// claim is pinned where it can be isolated —
// `tests::path_lane_does_not_borrow_the_outer_context` in `src/lib.rs`, which
// calls `certify_path_disjunction_membership` directly.

/// EXHAUSTIVE-MODEL ORACLE over the two-path family. Each path gets a membership
/// set `M` and an excluded set `X` drawn from the tags `{0,1,2}` over its OWN
/// variable; the path is UNSAT exactly when `M \ X` is empty, and the whole `Or`
/// is UNSAT exactly when BOTH paths are. Every satisfiable instance must decline.
/// The oracle enumerates the integer domain rather than asserting the answer.
#[test]
fn exhaustive_model_oracle_over_the_path_family() {
    let domain: Vec<i128> = (-2..=5).collect();
    let subsets: Vec<Vec<i128>> = (0u8..8)
        .map(|mask| (0i128..3).filter(|t| mask & (1 << t) != 0).collect::<Vec<_>>())
        .collect();
    let path_sat =
        |m: &[i128], x: &[i128]| domain.iter().any(|v| m.contains(v) && !x.iter().any(|e| e == v));

    let mut sat_declined = 0usize;
    let mut unsat_certified = 0usize;
    for m0 in &subsets {
        if m0.is_empty() {
            continue; // an empty `Or` is not a shape vcgen emits.
        }
        for x0 in &subsets {
            for m1 in &subsets {
                if m1.is_empty() {
                    continue;
                }
                for x1 in &subsets {
                    let path = |v: &str, m: &[i128], x: &[i128]| {
                        let mut parts = vec![member(v, m)];
                        parts.extend(x.iter().map(|&t| neq(v, t)));
                        Formula::And(parts)
                    };
                    let violation = a3d_shaped(vec![path("_0", m0, x0), path("_1", m1, x1)]);
                    let sat = path_sat(m0, x0) || path_sat(m1, x1);
                    let cert = certified(&violation);
                    if sat {
                        assert!(
                            !cert,
                            "SATISFIABLE path disjunction certified \
                             (M0={m0:?} X0={x0:?} M1={m1:?} X1={x1:?}) — a false proof"
                        );
                        sat_declined += 1;
                    } else {
                        assert!(
                            cert,
                            "UNSAT path disjunction declined \
                             (M0={m0:?} X0={x0:?} M1={m1:?} X1={x1:?}) — fixture-keyed"
                        );
                        unsat_certified += 1;
                    }
                }
            }
        }
    }
    assert!(sat_declined >= 200, "oracle covered too few satisfiable instances: {sat_declined}");
    assert!(unsat_certified >= 20, "oracle covered too few UNSAT instances: {unsat_certified}");
}

// ---------------------------------------------------------------------------
// The caps, measured rather than assumed.
// ---------------------------------------------------------------------------

/// Wider than `PATH_MEMBERSHIP_MAX_PATHS` (64). Declining on a cap is
/// fail-closed: it costs a certificate, never soundness.
#[test]
fn a_disjunction_wider_than_the_cap_declines() {
    let paths = (0..65).map(|i| contradictory_path(&format!("_{i}"), 2)).collect();
    assert!(!certified(&a3d_shaped(paths)), "a 65-path disjunction must fail closed on the cap");
    let paths = (0..64).map(|i| contradictory_path(&format!("_{i}"), 2)).collect();
    assert!(certified(&a3d_shaped(paths)), "a 64-path disjunction is inside the cap");
}
