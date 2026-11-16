//! Adversarial review of the integer-parameter type-range facts (2026-10-08,
//! INTRINSIC-RESIDUAL-1).
//!
//! Captures in `fixtures/range_adversarial/` are `-Ztrust-dump=mir-only` output of
//! the stage-2 trustc built from d36c551fac (2026-10-01; no stage 1 of main
//! existed on this machine). The extractor's `integer_param_range_preconditions`,
//! `char_range_preconditions` and `enum_discriminant_range_preconditions` are
//! unchanged since d36c551fac. Sources: `fixtures/range_adversarial/src/*.rs`. File
//! suffixes: `_o0` (debug), `_o1` (`-O`), `_nooverflowchecks`
//! (`-C overflow-checks=off`, so `+ - *` are plain wrapping MIR BinaryOps). The
//! sysroot spans of `bug_d6_*` were rewritten from the capturing checkout's absolute
//! path to `<repo>/library/core/src/...` (`scripts/check_fixture_span_paths.py`); the
//! `library/core/src/` tail that `is_trusted_std_file` reads is kept.
//!
//! Three questions:
//!   (1) Can a type-range fact make a REACHABLE panic, or a FALSE `ensures`,
//!       UNSAT (a false proof)? `false_proofs_none_over_the_reinterpretation_probes`
//!       is the pin, over casts, transmutes, unions, raw-pointer reinterpretation,
//!       wrapping results, `mut` parameters reassigned by each of these, enum
//!       discriminant casts, uninit and padding, and (`bug_w*`,
//!       `src/probes_128_false.rs`) false clauses over 128-bit parameters. The same
//!       probes on the 2026-10-01 compiler DID prove `bug_d2_high_disc_as_i8`
//!       (CAST-ENUMDISC-SIGNED-1, fixed on main on 2026-10-06), so the probe set can
//!       detect this class of false proof.
//!   (2) Is the `y = -1` class (a refutation that gives a typed integer PARAMETER a
//!       value outside its type) gone at every width? The extractor's envelope stops
//!       at width 64 and the postcondition lane reads a parameter's range only from
//!       `func.preconditions`, so on main 4aa65b4618 true clauses over `u128`/`i128`
//!       parameters were refuted with `x = -1` / `x = 2^127` (and the 2026-10-01
//!       compiler reported the `i128` rows `postcond FAILED ... verified_counterexample
//!       = true` against correct code). The generator now states the 128-bit
//!       parameter ranges itself (`generate::missing_param_type_range_facts`): the
//!       `wide_*` tests pin that those clauses PROVE, and the `bug_w*` tests that the
//!       facts are not too tight — the boundary values `u128::MAX` and `i128::MIN`
//!       still refute the false clauses that need them.
//!   (3) A postcondition row over a return value that an UNMODELED sysroot call
//!       defines (`i32::unsigned_abs`, `u128::saturating_add`) was refuted with a value
//!       the call never returns (`_0` free). The postcondition lane now fails that row
//!       closed to the visible `SpecUnverifiable` row — a false clause over such a call
//!       too, which is the cost; a MODELED call keeps its real refutation.
use trust_types::{
    AssuranceLevel, ContractBodyDeclineCause, CounterexampleValue, Ty, VcKind, VerifiableFunction,
    VerificationResult,
};

#[path = "support/pre_carrier_keys.rs"]
mod pre_carrier_keys;

fn dir() -> String {
    format!("{}/tests/fixtures/range_adversarial", env!("CARGO_MANIFEST_DIR"))
}

fn load(file: &str) -> VerifiableFunction {
    let text = std::fs::read_to_string(format!("{}/{file}", dir()))
        .unwrap_or_else(|e| panic!("{file}: {e}"));
    let func = serde_json::from_str(&text).unwrap_or_else(|e| panic!("{file}: {e}"));
    pre_carrier_keys::rekey_pre_carrier_dump(func)
}

/// Every row of `generate_vcs` plus the full-mode assertion-refutation lane
/// (`trust-assert-refute`), labelled, with its deterministic in-process ay verdict.
fn rows(func: &VerifiableFunction) -> Vec<(bool, VcKind, VerificationResult)> {
    let func = func.clone();
    std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(move || {
            let mut vcs = trust_vcgen::generate_vcs(&func);
            let main = vcs.len();
            vcs.extend(trust_vcgen::generate_full_assert_refutation_vcs(&func));
            let router = trust_router::Router::deterministic_in_process_ay(
                30_000,
                trust_types::determinism::EffortScale::BUILTIN,
            );
            router
                .verify_all(&vcs)
                .into_iter()
                .enumerate()
                .map(|(i, (vc, r))| (i >= main, vc.kind, r))
                .collect()
        })
        .expect("spawn")
        .join()
        .expect("vcgen/solver thread must not panic")
}

fn fixtures(prefix: &str) -> Vec<String> {
    let mut names: Vec<String> = std::fs::read_dir(dir())
        .expect("fixture dir")
        .flatten()
        .map(|e| e.file_name().to_string_lossy().into_owned())
        .filter(|n| n.starts_with(prefix) && n.ends_with(".json"))
        .collect();
    names.sort();
    names
}

/// (1) THE SOUNDNESS PIN. Every `bug_*` capture has a reachable panic or a false
/// `ensures` (the witness is in its source comment). Neither a Postcondition row
/// nor a loop-invariant row may prove, and if the assertion lane emitted
/// candidates, at least one must fail to prove (the lane splits a panic site per
/// discriminant tag, so an infeasible tag's candidate legitimately proves, and
/// `bug_i4` carries a second assert that really holds).
#[test]
fn false_proofs_none_over_the_reinterpretation_probes() {
    let names = fixtures("bug_");
    assert!(names.len() >= 100, "only {} probe captures", names.len());
    let mut bad = Vec::new();
    for name in &names {
        let func = load(name);
        let rows = rows(&func);
        for (_, kind, verdict) in &rows {
            let claim = matches!(
                kind,
                VcKind::Postcondition
                    | VcKind::LoopInvariantInitiation { .. }
                    | VcKind::LoopInvariantConsecution { .. }
            );
            // `bug_l1`'s initiation of `x >= s` (x == s at entry), `bug_l2`'s
            // consecution of `y >= 0` (y is never written) and both halves of
            // `bug_l3`'s `i <= n` are TRUE; only the other halves are false.
            let true_half = match kind {
                VcKind::LoopInvariantInitiation { invariant, .. } => {
                    invariant == "x >= s" || invariant == "i <= n"
                }
                VcKind::LoopInvariantConsecution { invariant, .. } => {
                    invariant == "y >= 0" || invariant == "i <= n"
                }
                _ => false,
            };
            if claim && !true_half && matches!(verdict, VerificationResult::Proved { .. }) {
                bad.push(format!("{name}: {kind:?} PROVED"));
            }
        }
        let lane: Vec<_> = rows.iter().filter(|(assert_lane, _, _)| *assert_lane).collect();
        if !lane.is_empty()
            && lane.iter().all(|(_, _, v)| matches!(v, VerificationResult::Proved { .. }))
        {
            bad.push(format!("{name}: every assertion-lane candidate PROVED ({})", lane.len()));
        }
    }
    assert!(bad.is_empty(), "FALSE PROOFS: {bad:#?}");
}

/// The value of a counterexample assignment as an exact integer, if it is one
/// (`Term` carries decimal strings past i128 — e.g. `i128::MAX + 1`).
fn as_big(value: &CounterexampleValue) -> Option<(bool, u128)> {
    match value {
        CounterexampleValue::Int(v) => Some((*v < 0, v.unsigned_abs())),
        CounterexampleValue::Uint(v) => Some((false, *v)),
        CounterexampleValue::Term(s) => {
            let (neg, digits) = s.strip_prefix('-').map_or((false, s.as_str()), |d| (true, d));
            digits.parse::<u128>().ok().map(|m| (neg, m))
        }
        _ => None,
    }
}

/// Whether `(neg, magnitude)` is a value of the integer type `ty` (any width).
fn in_type(ty: &Ty, (neg, mag): (bool, u128)) -> bool {
    let Ty::Int { width, signed } = ty else { return true };
    let width = *width;
    if *signed {
        let half = 1u128 << (width - 1);
        if neg { mag <= half } else { mag < half }
    } else {
        (!neg || mag == 0) && (width >= 128 || mag < (1u128 << width))
    }
}

/// Every refuted row of `func` that gives an integer PARAMETER (any SSA spelling) a
/// value outside its declared type, labelled.
fn out_of_type_refutations(name: &str, func: &VerifiableFunction) -> Vec<String> {
    let params: Vec<(String, Ty)> = func
        .body
        .locals
        .iter()
        .filter(|d| d.index >= 1 && d.index <= func.body.arg_count)
        .map(|d| (trust_vcgen::local_var_name(func, d), d.ty.clone()))
        .collect();
    let mut bad = Vec::new();
    for (_, kind, verdict) in rows(func) {
        let VerificationResult::Failed { counterexample: Some(cex), .. } = &verdict else {
            continue;
        };
        for (var, value) in &cex.assignments {
            let base = var.split('#').next().unwrap_or(var);
            let Some((_, ty)) = params.iter().find(|(p, _)| p == base) else { continue };
            if let Some(v) = as_big(value)
                && !in_type(ty, v)
            {
                bad.push(format!("{name}: {kind:?}: {var} = {value:?} (declared {ty:?})"));
            }
        }
    }
    bad
}

fn is_spec_unverifiable(kind: &VcKind) -> bool {
    matches!(kind, VcKind::UnsupportedMir { kind, .. } if kind == "SpecUnverifiable")
}

/// The `wide_ok_*` rows whose clause holds by the 128-bit PARAMETER's type alone.
const WIDE_PARAM_ROWS: [&str; 5] = [
    "wide_ok_f21_u128_identity_o0.json",
    "wide_ok_f22_i128_identity_hi_o0.json",
    "wide_ok_h6_i128_param_hi_o0.json",
    "wide_ok_h7_u128_param_lo_o0.json",
    "wide_ok_h7b_u128_cmp_zero_o0.json",
];

/// The `wide_ok_*` rows whose return value an UNMODELED call defines.
const UNMODELED_CALL_ROWS: [&str; 3] = [
    "wide_ok_f23_u32_unsigned_abs_o0.json",
    "wide_ok_h1_u128_sat_add_o0.json",
    "wide_ok_h2_u128_sat_sub_o0.json",
];

/// (2) THE `y = -1` CLASS AT 128 BITS. Every `wide_*` parameter clause is true
/// of every value of its type; a refutation of one may only name in-type
/// parameter values. On main 4aa65b4618 this was `u128` `x = -1`, `i128` `x = 2^127`.
#[test]
fn wide_integer_parameters_are_never_refuted_out_of_type() {
    let names = fixtures("wide_ok_");
    assert_eq!(names.len(), WIDE_PARAM_ROWS.len() + UNMODELED_CALL_ROWS.len(), "{names:?}");
    let bad: Vec<String> =
        names.iter().flat_map(|name| out_of_type_refutations(name, &load(name))).collect();
    assert!(bad.is_empty(), "out-of-type PARAMETER values in refutations: {bad:#?}");
}

/// (2') The same rows, stated as verdicts: each clause over a 128-bit parameter
/// holds by the parameter's type, so it PROVES at strict-checked strength (it was
/// `Failed` on main 4aa65b4618 — f21, f22, h6, h7, h7b).
#[test]
fn wide_true_clauses_prove() {
    let mut bad = Vec::new();
    for name in WIDE_PARAM_ROWS {
        let rows = rows(&load(name));
        let post: Vec<_> =
            rows.iter().filter(|(_, kind, _)| matches!(kind, VcKind::Postcondition)).collect();
        if post.is_empty() {
            bad.push(format!("{name}: no Postcondition row"));
        }
        for (_, kind, verdict) in rows.iter().filter(|(_, kind, _)| !is_spec_unverifiable(kind)) {
            let proved_strict = matches!(
                verdict,
                VerificationResult::Proved { strength, .. }
                    if matches!(strength.assurance, AssuranceLevel::SmtBacked | AssuranceLevel::Certified)
            );
            if !proved_strict {
                bad.push(format!("{name}: {kind:?} is not proved: {verdict:?}"));
            }
        }
    }
    assert!(bad.is_empty(), "TRUE clauses over 128-bit parameters: {bad:#?}");
}

/// (2'') THE FACTS ARE NOT TOO TIGHT. Each false clause below needs a parameter AT
/// its type's boundary (`u128::MAX`, `i128::MIN`) or just past a 64-bit one (`2^64`,
/// `i64::MIN - 1`): a truncated or off-by-one bound would make it prove. Each must be
/// `Failed` with in-type parameter values, in both builds.
#[test]
fn wide_false_clauses_still_refute_at_the_type_boundary() {
    let mut bad = Vec::new();
    for stem in [
        "bug_w1_u128_identity_ge1",
        "bug_w2_i128_identity_nonneg",
        "bug_w3_u128_below_max",
        "bug_w4_i128_above_min",
        "bug_w9_u128_assert_below_max",
        "bug_w10_i128_assert_not_min",
        "bug_w11_u128_within_u64",
        "bug_w14_i128_within_i64",
    ] {
        for build in ["o0", "o1"] {
            let name = format!("{stem}_{build}.json");
            let func = load(&name);
            let rows = rows(&func);
            let claims: Vec<_> = rows
                .iter()
                .filter(|(_, kind, _)| {
                    matches!(kind, VcKind::Postcondition | VcKind::Assertion { .. })
                })
                .collect();
            if claims.is_empty() {
                bad.push(format!("{name}: no Postcondition/Assertion row"));
            }
            for (_, kind, verdict) in claims {
                if !matches!(verdict, VerificationResult::Failed { .. }) {
                    bad.push(format!("{name}: {kind:?} not refuted: {verdict:?}"));
                }
            }
            bad.extend(out_of_type_refutations(&name, &func));
        }
    }
    assert!(bad.is_empty(), "{bad:#?}");
}

/// (3) A postcondition row whose return slot is defined only by an UNMODELED sysroot
/// call was refuted over a free `_0` — `_0 = 2147483649` for `i32::unsigned_abs`, a
/// value it never returns, from the formula `range(x) && !(_0 <= 2147483648)`. It is
/// now the visible `SpecUnverifiable` row: no Postcondition row, no refutation.
///
/// Since `1007a19e07` (DECISION_QUEUE 2026-11-06, "retain the authored question at a
/// typed body-lowering decline") that refusal, for a clause with an authored source
/// index, is the typed `VcKind::DeclinedContractBody` with cause
/// `UnconstrainedReturnCall` rather than the generic `UnsupportedMir` spelling — the
/// same refusal, now carrying the authored predicate. Every capture here has its one
/// authored `ensures`, so each must carry exactly that typed refusal, retaining
/// clause 0's own predicate, and it must decide nothing (neither `Proved` nor
/// `Failed`). VCGEN-PERF-67-69-VERDICTS-1: this pin kept asking for the generic
/// spelling only, so it read the ruled typed row as a missing refusal.
///
/// THE COST, pinned with it: a FALSE clause over such a call (`bug_w17`, `bug_w18`)
/// is not refuted either — no witness over a free `_0` is an execution. Modeling the
/// call (as the `<= 64`-bit saturating methods are) is what turns these into real
/// verdicts; when that lands, these rows move and this pin with them.
#[test]
fn unmodeled_call_return_is_not_refuted() {
    let mut bad = Vec::new();
    let cost: Vec<String> = ["bug_w17_i32_unsigned_abs_lt5", "bug_w18_u128_sat_add_gt"]
        .iter()
        .flat_map(|stem| [format!("{stem}_o0.json"), format!("{stem}_o1.json")])
        .collect();
    for name in UNMODELED_CALL_ROWS.iter().copied().chain(cost.iter().map(String::as_str)) {
        let func = load(name);
        let rows = rows(&func);
        let refusals: Vec<_> = rows
            .iter()
            .filter(|(_, kind, _)| {
                matches!(
                    kind.declined_contract_body(),
                    Some(d) if d.cause == ContractBodyDeclineCause::UnconstrainedReturnCall
                )
            })
            .collect();
        if refusals.is_empty() {
            bad.push(format!("{name}: no UnconstrainedReturnCall refusal row"));
        }
        for (_, kind, verdict) in &refusals {
            let decline = kind.declined_contract_body().expect("filtered above");
            if decline.source_contract_index != 0
                || func.postconditions.first() != Some(&decline.source_predicate)
            {
                bad.push(format!("{name}: refusal does not retain clause 0: {decline:?}"));
            }
            if matches!(
                verdict,
                VerificationResult::Proved { .. } | VerificationResult::Failed { .. }
            ) {
                bad.push(format!("{name}: a refusal row decided: {verdict:?}"));
            }
        }
        for (_, kind, verdict) in &rows {
            if matches!(kind, VcKind::Postcondition)
                || matches!(verdict, VerificationResult::Failed { .. })
            {
                bad.push(format!("{name}: {kind:?} {verdict:?}"));
            }
        }
    }
    assert!(bad.is_empty(), "refuted over a free return: {bad:#?}");
}

/// (3') A MODELED call keeps its row: the `u32`/`u64` saturating model pins `_0`, so
/// a FALSE clause over it is still refuted, with an in-type witness (`y = 0`).
#[test]
fn modeled_call_return_is_still_refuted() {
    let mut bad = Vec::new();
    for name in fixtures("bug_w15_").into_iter().chain(fixtures("bug_w16_")) {
        let func = load(&name);
        let rows = rows(&func);
        let post: Vec<_> =
            rows.iter().filter(|(_, kind, _)| matches!(kind, VcKind::Postcondition)).collect();
        if post.is_empty()
            || !post.iter().all(|(_, _, v)| matches!(v, VerificationResult::Failed { .. }))
        {
            bad.push(format!("{name}: {rows:?}"));
        }
        bad.extend(out_of_type_refutations(&name, &func));
    }
    assert!(bad.is_empty(), "{bad:#?}");
}
