//! Trust (2026-10-07, INTRINSIC-RESIDUAL-1): A COUNTEREXAMPLE NAMES AN EXECUTION,
//! AND NO EXECUTION GIVES A TYPED INTEGER PARAMETER A VALUE OUTSIDE ITS TYPE.
//!
//! VC generation lowers every Rust integer to the unbounded `Sort::Int`. A
//! parameter's declared range reaches the solver as a FACT, and outside the
//! arithmetic batteries (`conjoin_arg_type_ranges`) every lane reads that fact from
//! one place: `func.preconditions`, where the extractor puts it for every named
//! integer parameter of width <= 64 (`trust_mir_extract::
//! integer_param_range_preconditions`, since 2026-07-05). The PRODUCER owns the
//! fact at those widths; the lane trusts it to be there. At 128 bits, which the
//! extractor's envelope leaves out, the GENERATOR states it
//! (`generate::missing_param_type_range_facts`, 2026-10-08: on main 4aa65b4618 true
//! clauses over `u128`/`i128` parameters were refuted with `x = -1` / `x = 2^127`;
//! `tests/range_fact_adversarial.rs` pins those rows).
//!
//! MEASURED on main c132f5a193: `fixtures/sat_add_ge.json` (`#[ensures(result >= x)]
//! fn sat_add_ge(x: u32, y: u32) -> u32 { x.saturating_add(y) }`) was `Failed` with
//! `_0 = 0, x = 1, y = -1` — a `u32` at -1 — and had been since the day it landed in
//! `intrinsic_semantics_realmir`'s residual test (identical at 1cd49676ba), whose
//! `!Proved` assertion cannot tell `Unknown` from `Failed`. The capture predated the
//! extractor's facts (`"preconditions": []`); `sat_sub_le.json` the same, with
//! `y = -1`. No other function in this crate's fixture corpus produced such a witness
//! (a 929-function census on c132f5a193 — 391 `escaped_seam_*` captures and 538
//! others — solved with the deterministic in-process ay router: these two rows were
//! the only ones). Both captures now carry exactly the facts today's extractor
//! attaches (docs/KNOWN_HAZARDS.md, 2026-10-07: "a fixture is the extractor's
//! output"); this file is what keeps the next stale capture from hiding the same way.
//!
//! These tests state the rule on the OUTPUT — no refuted row gives a typed integer
//! parameter (any SSA spelling of it, any width `1..=128`, any value spelling — a
//! `Term` decimal past `i128` included) a value outside its declared type — over the
//! population it can fail on: every fixture whose producer attached no range fact
//! for some parameter, or that has a 128-bit parameter (found by SCANNING, so a new
//! stale capture is guarded the day it lands), the two refreshed captures, and
//! extracted captures that really refute.
//! A LOCAL is not in the claim: an overflow row's witness legitimately shows the
//! unbounded mathematical result of the overflowing op, and the loop-free bounds lane
//! withholds local ranges on purpose (`generate::safety`, the `count_back_edges` rule).
use std::collections::HashMap;

use trust_types::{
    AssuranceLevel, CounterexampleValue, Formula, Sort, Ty, VcKind, VerifiableFunction,
    VerificationResult,
};

#[path = "support/pre_carrier_keys.rs"]
mod pre_carrier_keys;
#[path = "support/test_router.rs"]
mod test_router;

fn fixture_dir() -> String {
    format!("{}/tests/fixtures", env!("CARGO_MANIFEST_DIR"))
}

/// A fixture as `escaped_local_seam_realmir.rs` loads one: pre-carrier captures get
/// the `callee_key` today's extractor mints. `None` for a JSON file that is not a
/// `VerifiableFunction`.
fn load_path(path: &str) -> Option<VerifiableFunction> {
    let func = serde_json::from_str(&std::fs::read_to_string(path).ok()?).ok()?;
    Some(pre_carrier_keys::rekey_pre_carrier_dump(func))
}

fn load(name: &str) -> VerifiableFunction {
    load_path(&format!("{}/{name}", fixture_dir()))
        .unwrap_or_else(|| panic!("{name}: fixture must deserialize"))
}

/// `[MIN, MAX]` of a type in the extractor's envelope (`Ty::Int`, width `1..=64`).
fn int_range(ty: &Ty) -> Option<(i128, i128)> {
    let Ty::Int { width, signed } = ty else { return None };
    let (width, signed) = (*width, *signed);
    if !(1..=64).contains(&width) {
        return None;
    }
    Some(if signed {
        (-(1i128 << (width - 1)), (1i128 << (width - 1)) - 1)
    } else {
        (0, (1i128 << width) - 1)
    })
}

/// Formula name -> parameter local index, for every named integer parameter of ANY
/// width (`1..=128`), spelled as the generator spells it. The 128-bit ones are outside
/// the extractor's envelope; since INTRINSIC-RESIDUAL-1 the generator states their
/// range itself (`generate::missing_param_type_range_facts`), and the guard checks
/// them like every other width.
fn integer_params(func: &VerifiableFunction) -> HashMap<String, usize> {
    func.body
        .locals
        .iter()
        .filter(|d| d.index >= 1 && d.index <= func.body.arg_count && d.name.is_some())
        .filter(|d| matches!(d.ty, Ty::Int { width: 1..=128, .. }))
        .map(|d| (trust_vcgen::local_var_name(func, d), d.index))
        .collect()
}

/// The range fact the extractor attaches for the parameter spelled `name`.
fn extractor_range_fact(name: &str, (lo, hi): (i128, i128)) -> Formula {
    let var = || Formula::Var(name.to_string(), Sort::Int);
    Formula::And(vec![
        Formula::Ge(Box::new(var()), Box::new(Formula::Int(lo))),
        Formula::Le(Box::new(var()), Box::new(Formula::Int(hi))),
    ])
}

/// Whether `func` carries, as captured, the range fact of every integer parameter:
/// the extractor's for each one in its envelope. A 128-bit parameter has none in any
/// capture (the generator states it), so a function with one is never "carried" and
/// always joins the scanned population.
fn carries_every_param_range(func: &VerifiableFunction) -> bool {
    integer_params(func).iter().all(|(name, index)| {
        let decl = func.body.locals.iter().find(|d| d.index == *index).expect("param decl");
        int_range(&decl.ty)
            .is_some_and(|range| func.preconditions.contains(&extractor_range_fact(name, range)))
    })
}

/// An integer counterexample value, exactly, as `(negative, magnitude)` — whichever
/// spelling carries it: `Int`, `Uint`, or a `Term` holding the decimal the solver
/// printed for a value past `i128` (`170141183460469231731687303715884105728`, or
/// `-…` / `(- …)` below `i128::MIN`). A magnitude past `u128` is `None` (outside every
/// integer type). `None` overall for a value that is not an integer.
fn exact_int(value: &CounterexampleValue) -> Option<(bool, Option<u128>)> {
    match value {
        CounterexampleValue::Int(v) => Some((*v < 0, Some(v.unsigned_abs()))),
        CounterexampleValue::Uint(v) => Some((false, Some(*v))),
        CounterexampleValue::Term(text) => {
            let text = text.trim();
            let (negative, digits) = if let Some(inner) =
                text.strip_prefix("(-").and_then(|rest| rest.strip_suffix(')'))
            {
                (true, inner.trim())
            } else if let Some(digits) = text.strip_prefix('-') {
                (true, digits)
            } else {
                (false, text)
            };
            if digits.is_empty() || !digits.bytes().all(|b| b.is_ascii_digit()) {
                return None;
            }
            Some((negative, digits.parse::<u128>().ok()))
        }
        _ => None,
    }
}

/// Whether `(negative, magnitude)` is a value of the integer type `ty`, at every width
/// `1..=128`.
fn in_type(ty: &Ty, (negative, magnitude): (bool, Option<u128>)) -> bool {
    let Ty::Int { width: width @ 1..=128, signed } = *ty else { return true };
    let Some(magnitude) = magnitude else { return false };
    let negative = negative && magnitude != 0;
    if signed {
        let half = 1u128 << (width - 1);
        if negative { magnitude <= half } else { magnitude < half }
    } else {
        !negative && (width == 128 || magnitude < (1u128 << width))
    }
}

/// Every assignment of `row` that names an integer parameter (bare or `#`-versioned)
/// with a value outside its declared type.
fn out_of_type(func: &VerifiableFunction, row: &[(String, CounterexampleValue)]) -> Vec<String> {
    let params = integer_params(func);
    let mut bad = Vec::new();
    for (name, value) in row {
        let base = name.split('#').next().unwrap_or(name);
        let Some(&index) = params.get(base) else { continue };
        let decl = func.body.locals.iter().find(|d| d.index == index).expect("param decl");
        // Every integer spelling is judged, a `Term` decimal past `i128` included (it was
        // read as "not an integer" before, so `x = 2^127` for an `i128` passed). A value
        // that is not an integer is some other encoding, not this guard's claim.
        let in_range = exact_int(value).is_none_or(|v| in_type(&decl.ty, v));
        if !in_range {
            bad.push(format!("{name} = {value:?} (declared {:?})", decl.ty));
        }
    }
    bad
}

/// Every VC of `func` with the deterministic in-process ay verdict, on a big stack
/// (VC generation of some fixtures overflows libtest's default).
fn verdicts(func: &VerifiableFunction) -> Vec<(VcKind, VerificationResult)> {
    let func = func.clone();
    std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(move || {
            let vcs = trust_vcgen::generate_vcs(&func);
            let router = test_router::deterministic_test_router();
            router.verify_all(&vcs).into_iter().map(|(vc, r)| (vc.kind, r)).collect()
        })
        .expect("spawn solver thread")
        .join()
        .expect("solver thread must not panic")
}

/// (refuted rows, out-of-type assignments in them) for `func`, labelled.
fn refutations(label: &str, func: &VerifiableFunction) -> (usize, Vec<String>) {
    let (mut refuted, mut bad) = (0, Vec::new());
    for (kind, verdict) in verdicts(func) {
        if let VerificationResult::Failed { counterexample: Some(cex), .. } = &verdict {
            refuted += 1;
            for b in out_of_type(func, &cex.assignments) {
                bad.push(format!("{label}: {kind:?}: {b}"));
            }
        }
    }
    (refuted, bad)
}

const METHOD_SPELLING: [&str; 2] = ["sat_add_ge.json", "sat_sub_le.json"];

/// THE MEASURED ROWS. Both captures carry exactly the extractor's facts, the clause
/// (true of every `u32` pair) proves at strict-checked strength, and no row of either
/// function is refuted with an out-of-type parameter value.
#[test]
fn method_spelling_saturating_clauses_prove_and_are_never_refuted_out_of_type() {
    for name in METHOD_SPELLING {
        let func = load(name);
        // Exactly the extractor's facts — no more (an extra fact would be a hypothesis
        // nobody's producer states), no fewer.
        let expected: Vec<Formula> = func
            .body
            .locals
            .iter()
            .filter(|d| d.index >= 1 && d.index <= func.body.arg_count && d.name.is_some())
            .filter_map(|d| {
                int_range(&d.ty).map(|range| {
                    extractor_range_fact(&trust_vcgen::local_var_name(&func, d), range)
                })
            })
            .collect();
        assert_eq!(func.preconditions, expected, "{name}: the extractor's facts, exactly");

        let rows = verdicts(&func);
        let post: Vec<_> =
            rows.iter().filter(|(kind, _)| matches!(kind, VcKind::Postcondition)).collect();
        assert!(!post.is_empty(), "{name}: the ensures clause must produce a Postcondition VC");
        for (_, verdict) in post {
            assert!(
                matches!(
                    verdict,
                    VerificationResult::Proved { strength, .. }
                        if matches!(strength.assurance, AssuranceLevel::SmtBacked | AssuranceLevel::Certified)
                ),
                "{name}: the clause is true of every u32 pair and must prove strict-checked; \
                 got {verdict:?}"
            );
        }
        let (_, bad) = refutations(name, &func);
        assert!(bad.is_empty(), "out-of-type counterexample values: {bad:#?}");
    }
}

/// THE PRODUCER CONTRACT IS LOAD-BEARING, pinned rather than assumed. The same two
/// captures as they were dumped — facts removed — are refuted with a parameter value
/// outside `u32`: the lane has no other source for the range. This is the hazard the
/// rows above close by carrying the facts, and the reason every guard in this file
/// scans for captures without them.
///
/// It FAILS the day the generator states parameter ranges itself. That is a design
/// change, not a fix to make here: measured on c132f5a193, a trust-vcgen version of
/// it (green in trust-vcgen; every `escaped_seam_*` row unchanged) broke 28
/// trust-ir-bridge lib tests (the flip's spine byte-equality: the trust-ir spine does
/// not add the facts), 5 trust-clean lib tests (certification-shape pins built on
/// bodies without the facts) and trust-router's `cross_crate_pipeline`, all green
/// without it — those crates assume the extractor owns the fact. When that move is
/// made, flip this test with it.
#[test]
fn without_the_producers_facts_the_lane_refutes_out_of_type() {
    for name in METHOD_SPELLING {
        let mut func = load(name);
        func.preconditions.clear();
        let (_, bad) = refutations(name, &func);
        assert!(
            !bad.is_empty(),
            "{name}: with no range facts the postcondition lane was measured to refute with \
             an out-of-type parameter; if it no longer does, the generator now states the \
             ranges itself — update this file's doc and this pin"
        );
    }
}

/// THE GUARD over the population the hazard lives in: every fixture whose producer
/// left some integer parameter without its range fact.
#[test]
fn counterexamples_of_unranged_fixtures_respect_parameter_types() {
    let mut names: Vec<_> = std::fs::read_dir(fixture_dir())
        .expect("fixture dir")
        .flatten()
        .map(|e| e.file_name().to_string_lossy().into_owned())
        .filter(|n| n.ends_with(".json"))
        .collect();
    names.sort();
    let (mut scanned, mut bad) = (0, Vec::new());
    for name in names {
        let Some(func) = load_path(&format!("{}/{name}", fixture_dir())) else { continue };
        if integer_params(&func).is_empty() || carries_every_param_range(&func) {
            continue;
        }
        scanned += 1;
        bad.extend(refutations(&name, &func).1);
    }
    // A floor, so a fixture-format change that silently empties the population reads
    // as a failure rather than a vacuous pass (14 such fixtures on 2026-10-07; 47 on
    // 2026-10-08, once the 32 with a 128-bit parameter joined).
    assert!(scanned >= 40, "only {scanned} unranged fixtures found; the scan lost its population");
    assert!(bad.is_empty(), "out-of-type counterexample values: {bad:#?}");
}

/// The same guard on extracted captures that really refute (two `_bug` rows) and
/// two controls whose loop-free bounds rows read the parameter's range only from
/// the entry hypothesis. With their preconditions REMOVED these four were measured
/// refuted with `k = -1` for a `usize` parameter; as captured, they carry the facts.
#[test]
fn counterexamples_of_extracted_captures_respect_parameter_types() {
    let (mut refuted, mut bad) = (0, Vec::new());
    for name in [
        "escaped_seam_r5b_index_local_enum_bug_o1_mir.json",
        "escaped_seam_r5b_index_local_len_bug_o1_mir.json",
        "escaped_seam_rev11d_store_reseat_read_ctl_o0_mir.json",
        "escaped_seam_rev11d_store_reseat_read_ctl_o1_mir.json",
    ] {
        let func = load(name);
        assert!(carries_every_param_range(&func), "{name}: an extracted capture carries the facts");
        let (n, b) = refutations(name, &func);
        refuted += n;
        bad.extend(b);
    }
    assert!(refuted > 0, "the corpus produced no counterexample to inspect");
    assert!(bad.is_empty(), "out-of-type counterexample values: {bad:#?}");
}

/// The guard's own reader, pinned: every spelling of an integer value is judged
/// against the declared type at every width, including the `Term` decimals the
/// solver prints past `i128` (read as "not an integer" before INTRINSIC-RESIDUAL-1,
/// which let `x = 2^127` for an `i128` pass), and a non-integer is not judged.
#[test]
fn out_of_type_reads_every_integer_spelling() {
    use CounterexampleValue::{Bool, Int, Term, Uint};
    let i128_ty = Ty::Int { width: 128, signed: true };
    let u128_ty = Ty::Int { width: 128, signed: false };
    let u32_ty = Ty::Int { width: 32, signed: false };
    let i8_ty = Ty::Int { width: 8, signed: true };
    let judged = |ty: &Ty, value: CounterexampleValue| {
        exact_int(&value)
            .map(|v| in_type(ty, v))
            .unwrap_or_else(|| panic!("{value:?} is an integer"))
    };
    assert!(!judged(&i128_ty, Term("170141183460469231731687303715884105728".into())));
    assert!(judged(&i128_ty, Int(i128::MIN)));
    assert!(!judged(&i128_ty, Term("-170141183460469231731687303715884105729".into())));
    assert!(!judged(&i128_ty, Term("(- 170141183460469231731687303715884105729)".into())));
    assert!(judged(&u128_ty, Term("340282366920938463463374607431768211455".into())));
    assert!(judged(&u128_ty, Uint(u128::MAX)));
    assert!(!judged(&u128_ty, Term("340282366920938463463374607431768211456".into())));
    assert!(!judged(&u128_ty, Int(-1)));
    assert!(!judged(&u128_ty, Term("(- 1)".into())));
    assert!(judged(&u128_ty, Int(0)));
    assert!(!judged(&u32_ty, Int(-1)));
    assert!(!judged(&u32_ty, Uint(1 << 32)));
    assert!(judged(&u32_ty, Uint(u128::from(u32::MAX))));
    assert!(!judged(&i8_ty, Int(128)));
    assert!(judged(&i8_ty, Int(-128)));
    assert!(!judged(&i8_ty, Int(-129)));
    assert!(exact_int(&Bool(true)).is_none());
    assert!(exact_int(&Term("(succ zero)".into())).is_none());
}
