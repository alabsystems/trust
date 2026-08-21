// dyn_carrier_corpus_coverage — the missing gate on the `targo trust prove` lane's
// TRAIT-OBJECT carrier coverage over the committed fixture corpus.
//
// Author: Andrew Yates. Copyright 2026 Andrew Yates. License: Apache-2.0 OR MIT.
//
// WHAT WAS INVISIBLE, AND FOR HOW LONG
// ------------------------------------
// `fd824f53df` re-keyed three trust-clean trait-object consumers off the
// generics-erased `trait_name` and onto the faithful `Ty::Dynamic::principal_key`,
// failing closed on `None`. That fail-closure is CORRECT: a dump that does not
// record which trait object it meant has unknown type identity. But every one of
// the committed fixture dumps predates the field, so from that commit onward
// 481 of 481 `Ty::Dynamic` nodes reachable through `VerifiableBody::locals` across
// 10 corpora mint NO carrier at all.
//
// A total collapse of the prove lane's trait-object coverage turned ZERO tests red.
// The corpus reaches `inhabit_verifiable_function` only when a human runs a census
// BINARY (`src/bin/corpus-census-2026-07-24.rs` and friends) — never through
// `cargo test`. A gate that cannot go red is worse than no gate, because it reads
// as evidence. This file is that gate.
//
// WHAT IT MEASURES — carrier coverage, NOT merge detection
// -------------------------------------------------------
// A gate keyed on "did the identity merge happen" would be VACUOUSLY green over
// this corpus: it holds 8 distinct `trait_name`s, every one single-bound and
// argument-free, and no single fixture file holds two distinct trait names. The
// merge `principal_key` exists to prevent is not expressible in these dumps. So the
// corpus half of this gate keys on CARRIER COVERAGE — how many trait objects the
// census path can still model — which is exactly what collapsed and exactly what a
// re-dump restores. The MERGE property is covered separately and unconditionally by
// `dyn_carrier_identity_is_keyed_on_the_principal_not_the_trait_name`, which
// synthesizes the two-key case the corpus cannot supply.
//
// WHY MIGRATION IS IMPOSSIBLE AND A RE-DUMP IS REQUIRED
// ----------------------------------------------------
// The erasure is total, and the corpus proves it: `w16-mono-harvest-2026-07-25`
// records `"trait_name": "core::ops::function::Fn"` for a local whose real type is
// `&(dyn Fn() -> i32 + Sync + RefUnwindSafe)` — arguments, the `Output` binding and
// BOTH auto traits collapsed into one string. Auto traits are not recoverable from
// a dump by any rule, so no offline migration can mint a faithful key. Only a
// re-dump with a post-`8b9626a7de` `trustc` can (task #199).
//
// TCB PLACEMENT — stated precisely, neither over- nor under-claimed
// ----------------------------------------------------------------
// This is the `targo trust prove` lane's trusted base, NOT the compiler's.
// `docs/TCB.md` scopes trust-clean out of the compile lane by name; its only
// non-test consumer is `targo-trust/src/main.rs`. `Trust.Dyn.*` carriers DO reach a
// real CIC kernel (`register_dyn_carriers` -> `add_inductive`/`add_decl` against a
// real `Environment::with_prelude()`), so the coverage loss is a real loss of
// kernel-checked modelling in the prove lane — not a compiler defect, and not
// merely tooling.
//
// Run:
//   cd crates && targo test -p trust-clean --test dyn_carrier_corpus_coverage -- --nocapture

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

use clean_kernel::{Environment, Name};
use trust_clean::{reachable_dyn_carriers, register_dyn_carriers};
use trust_types::VerifiableFunction;

// ===========================================================================
// THE WAIVER TABLE — an outage recorded as an OUTAGE, not as the expected state
// ===========================================================================
//
// A row means: "this corpus models ZERO trait objects, the cause is NAMED below,
// someone owns it, and it is not the current lane's fault." It does NOT mean the
// state is correct. The rules below are enforced mechanically so a row cannot rot,
// deliberately mirroring `scripts/hooks-pin/pin-waivers.txt`, which CLAUDE.md
// endorses for exactly this shape of known-bad state:
//
//   * past `expires`, the row STOPS APPLYING and the coverage floor bites again;
//   * once the corpus carries ANY faithful key, the row FAILS until it is DELETED
//     (the retirement condition is executable, not a comment);
//   * once the corpus mints ANY carrier, the row FAILS until it is DELETED;
//   * `demanded` / `files_with_dyn` are pinned EXACTLY, so a corpus cannot quietly
//     shrink (deleted dumps, a fixture that stopped deserializing) and pass by
//     having less to model;
//   * a corpus that demands carriers and has NO row FAILS — a new stale corpus
//     cannot be added silently;
//   * `WAIVED_DEMAND_CEILING` is a RATCHET: the waived total may only shrink.
//
// CAUSE (identical for all ten rows): every dump predates
// `Ty::Dynamic::principal_key` (`8b9626a7de` / `fdac8437be`, consumed by
// `fd824f53df`), so `dyn_principal_keys_in` yields `None` and
// `reachable_dyn_carriers` correctly declines to mint a carrier keyed on the erased
// `trait_name`.
//
// RETIREMENT CONDITION (task #199): re-dump the corpus with a post-`8b9626a7de`
// `trustc` so each `Ty::Dynamic` carries its faithful `principal_key`. Then DELETE
// the corresponding row — this gate will demand exactly that, because a row over a
// corpus that has become keyed is a hard failure. There is no migration path: see
// "WHY MIGRATION IS IMPOSSIBLE" above.
//
// BLOCKED HERE, ON PURPOSE: re-dumping needs a stage2 `trustc` build, which this
// lane cannot run (a soundness lane owns the build tree). The gate is what is not
// blocked, so the gate lands now and the outage is visible from `cargo test`
// onward instead of being discoverable only by running a census bin by hand.

struct StaleFixtureWaiver {
    corpus: &'static str,
    /// `Ty::Dynamic` nodes present in `body.locals` — pinned EXACTLY.
    demanded: usize,
    /// Of those, how many the PRODUCTION walk actually traverses to — measured
    /// through the real seam by the keyed probe, never by a model of the walk.
    /// This is exactly how much coverage a re-dump would restore. Pinned EXACTLY.
    ///
    /// A row with `reachable_if_keyed: 0` has a SECOND cause on top of staleness
    /// (see `CAUSE_B` below) and a re-dump alone will NOT retire it.
    reachable_if_keyed: usize,
    /// Fixture files contributing them — pinned EXACTLY.
    files_with_dyn: usize,
    /// `YYYY-MM-DD`. Past this, the row stops applying and coverage is demanded.
    expires: &'static str,
}

/// Measured 2026-08-19 at `fd824f53df`, by this test's own census.
///
/// Read the third column: only 164 of the 481 present nodes are REACHABLE by
/// `dyn_principal_keys_in` even with a perfect key. Three corpora are at zero.
const STALE_FIXTURE_WAIVERS: &[StaleFixtureWaiver] = &[
    w("census-2026-07-06", 98, 7, 27),
    w("census-m6-cleankernel-2026-07-08", 143, 132, 55),
    w("census-rung2-2026-07-07", 42, 13, 11),
    w("cmp-mono-select-2026-07-16", 1, 1, 1),
    w("expr-fold-corpus", 16, 0, 3),
    w("fold-crate-lambda-calculus-3.5.0", 130, 8, 11),
    w("mass-harvest2-2026-07-21", 16, 0, 5),
    w("optres-payload-extract-2026-07-17", 1, 1, 1),
    w("w16-mono-harvest-2026-07-25", 22, 2, 3),
    w("w2-iter-harvest-2026-07-20", 12, 0, 3),
];

/// CAUSE A — applies to every row. The dump predates `Ty::Dynamic::principal_key`.
/// RETIREMENT: re-dump with a post-`8b9626a7de` `trustc` (task #199).
const CAUSE_A: &str = "dump predates `principal_key` (8b9626a7de); consumed fail-closed by fd824f53df";

/// CAUSE B — a SECOND, independent gap, measured 2026-08-19 and not previously
/// recorded anywhere: `clean_ground::dyn_principal_keys_in` traverses only
/// `Ref`/`RawPtr`/`Slice`/`Array`/`Tuple`/`Adt` to depth 8, so a `Ty::Dynamic` under
/// a `FnPtr` signature, a `Closure`/`Coroutine` upvar, a `Datatype` definition, or
/// deeper than 8 is invisible to the census REGARDLESS of its key.
///
/// SCALE: 317 of the 481 present nodes (66%) are unreachable this way — so even a
/// perfect re-dump restores only 164. Three corpora are at ZERO reach
/// (`expr-fold-corpus` 16, `mass-harvest2-2026-07-21` 16,
/// `w2-iter-harvest-2026-07-20` 12 = 44 nodes): a re-dump moves them not at all.
///
/// RETIREMENT: widen `dyn_principal_keys_in` (a separate, deliberate change needing
/// its own soundness review — every new arm is a new carrier the kernel must accept).
/// The `reachable_if_keyed` pin below makes any such widening show up as a required
/// re-pin, so progress is measured rather than asserted.
const CAUSE_B: &str =
    "`dyn_principal_keys_in` never traverses to these nodes (no FnPtr/Closure/Datatype \
     arm, depth cap 8), so a re-dump alone cannot restore them";

/// All rows share one expiry: enough runway for a re-dump, not so much that the
/// outage becomes furniture.
const WAIVER_EXPIRY: &str = "2026-11-30";

const fn w(
    corpus: &'static str,
    demanded: usize,
    reachable_if_keyed: usize,
    files_with_dyn: usize,
) -> StaleFixtureWaiver {
    StaleFixtureWaiver { corpus, demanded, reachable_if_keyed, files_with_dyn, expires: WAIVER_EXPIRY }
}

/// RATCHET. The waived (unmodelled) demand may only ever SHRINK. Raising this number
/// means new trait-object coverage was lost, and that is a failure, not a re-pin.
const WAIVED_DEMAND_CEILING: usize = 481;

/// The one fixture the always-live controls below are pinned to: a real, committed,
/// stale dump holding exactly one `Ty::Dynamic` (`std::fmt::Write`, reached through
/// `&Formatter`'s buffer field).
const CONTROL_FIXTURE: &str =
    "cmp-mono-select-2026-07-16/dumps/trust-mir-326d3211b49ce78c-e84020fa4e3504b6.json";

// ===========================================================================
// Census over the real production seam
// ===========================================================================

/// Per-corpus census of trait-object carrier coverage.
#[derive(Debug, Default, Clone, PartialEq, Eq)]
struct CorpusCensus {
    /// `Ty::Dynamic` nodes reachable in `body.locals` — carriers DEMANDED.
    demanded: usize,
    /// Of those, how many carry a faithful `principal_key` (`Some`).
    keyed: usize,
    /// Distinct carriers the REAL production seam `reachable_dyn_carriers` mints.
    minted: usize,
    /// What the REAL seam would mint if every node carried a faithful key — the
    /// keyed probe. Measures how far `dyn_principal_keys_in` actually traverses,
    /// by asking production rather than by modelling it.
    reachable_if_keyed: usize,
    /// Fixture files that parsed as a `VerifiableFunction` AND demand >= 1 carrier.
    files_with_dyn: usize,
}

/// Count `Ty::Dynamic` nodes in a serialized locals list, and how many are keyed.
///
/// Deliberately a JSON walk, not a `Ty`-tree walk. A `Ty`-tree walk here would be a
/// SECOND model of "where a trait object can hide", and it would drift the moment
/// `Ty` grows a variant — the exact producer/consumer drift the one-renderer
/// `principal_key` design closes by construction. A JSON walk is a provable SUPERSET
/// of any `Ty`-tree walk, so the asymmetry is fail-closed: if production's
/// `dyn_principal_keys_in` ever NARROWS, `minted` falls while `demanded` holds and
/// this gate goes RED. It can never go green by production seeing less.
fn count_dynamic(v: &serde_json::Value, demanded: &mut usize, keyed: &mut usize) {
    match v {
        serde_json::Value::Object(map) => {
            if let Some(serde_json::Value::Object(dynamic)) = map.get("Dynamic") {
                *demanded += 1;
                if dynamic.get("principal_key").is_some_and(|k| !k.is_null()) {
                    *keyed += 1;
                }
            }
            for inner in map.values() {
                count_dynamic(inner, demanded, keyed);
            }
        }
        serde_json::Value::Array(items) => {
            for inner in items {
                count_dynamic(inner, demanded, keyed);
            }
        }
        _ => {}
    }
}

/// Stamp `key` as the `principal_key` of every `Ty::Dynamic` node in `v`.
///
/// This SIMULATES a re-dump; it is not a migration. The faithful key is not
/// recoverable from a stale dump (auto traits are erased with no trace), so this is
/// only ever used by the always-live controls to prove the consumer chain is
/// healthy — never to repair a fixture.
fn stamp_principal_key(v: &mut serde_json::Value, key: &str) {
    match v {
        serde_json::Value::Object(map) => {
            if let Some(serde_json::Value::Object(dynamic)) = map.get_mut("Dynamic") {
                dynamic.insert("principal_key".into(), serde_json::Value::String(key.into()));
            }
            for inner in map.values_mut() {
                stamp_principal_key(inner, key);
            }
        }
        serde_json::Value::Array(items) => {
            for inner in items {
                stamp_principal_key(inner, key);
            }
        }
        _ => {}
    }
}

/// Stamp a DISTINCT synthetic key on every `Ty::Dynamic` node in `v`.
///
/// The keyed probe. Distinct keys defeat `reachable_dyn_carriers`'s by-name dedup, so
/// the resulting carrier count is exactly the number of nodes the production walk
/// TRAVERSES TO. That makes "how far does the census actually reach" a measurement of
/// the real seam instead of a reimplementation of it — no second model, nothing to
/// drift. Widening `dyn_principal_keys_in` moves this number and forces a re-pin;
/// narrowing it moves the number the other way and fails the gate.
fn stamp_unique_principal_keys(v: &mut serde_json::Value, next: &mut usize) {
    match v {
        serde_json::Value::Object(map) => {
            if let Some(serde_json::Value::Object(dynamic)) = map.get_mut("Dynamic") {
                let key = format!("probe::K{next}");
                *next += 1;
                dynamic.insert("principal_key".into(), serde_json::Value::String(key));
            }
            for inner in map.values_mut() {
                stamp_unique_principal_keys(inner, next);
            }
        }
        serde_json::Value::Array(items) => {
            for inner in items {
                stamp_unique_principal_keys(inner, next);
            }
        }
        _ => {}
    }
}

fn fixtures_root() -> PathBuf {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("fixtures");
    assert!(root.is_dir(), "fixtures root missing at {}", root.display());
    root
}

/// Every `*.json` under `fixtures/`, sorted for determinism.
fn all_fixture_json(root: &Path) -> Vec<PathBuf> {
    fn walk(dir: &Path, out: &mut Vec<PathBuf>) {
        let Ok(entries) = std::fs::read_dir(dir) else { return };
        let mut paths: Vec<PathBuf> = entries.flatten().map(|e| e.path()).collect();
        paths.sort();
        for p in paths {
            if p.is_dir() {
                walk(&p, out);
            } else if p.extension().is_some_and(|e| e == "json") {
                out.push(p);
            }
        }
    }
    let mut out = Vec::new();
    walk(root, &mut out);
    out
}

/// The corpus a fixture belongs to: its immediate subdirectory under `fixtures/`.
fn corpus_of(root: &Path, file: &Path) -> String {
    file.strip_prefix(root)
        .ok()
        .and_then(|rel| rel.components().next())
        .map(|c| c.as_os_str().to_string_lossy().into_owned())
        .unwrap_or_else(|| "<root>".to_string())
}

/// Drive the REAL production census path over every committed fixture dump.
fn census_corpus() -> BTreeMap<String, CorpusCensus> {
    let root = fixtures_root();
    let mut by_corpus: BTreeMap<String, CorpusCensus> = BTreeMap::new();

    for path in all_fixture_json(&root) {
        let Ok(text) = std::fs::read_to_string(&path) else { continue };
        // Many fixture JSONs are scorecards/manifests, not dumps. A file that does
        // not deserialize as a `VerifiableFunction` is not a dump and is skipped —
        // but a dump that STOPS deserializing would silently shrink coverage, which
        // is why every waiver row pins `files_with_dyn` as well as `demanded`.
        let Ok(func) = serde_json::from_str::<VerifiableFunction>(&text) else { continue };

        let locals = serde_json::to_value(&func.body.locals).expect("locals reserialize");
        let (mut demanded, mut keyed) = (0usize, 0usize);
        count_dynamic(&locals, &mut demanded, &mut keyed);
        if demanded == 0 {
            continue;
        }

        // THE SEAM UNDER TEST — the same call `inhabit_verifiable_function` makes.
        let minted = reachable_dyn_carriers(&func).len();

        // THE KEYED PROBE — the same seam, asked what a re-dump would buy.
        //
        // Round-trips ONLY `body.locals`, and from the already-typed value rather than
        // from the file text. Both details are load-bearing: `serde_json::Value` cannot
        // hold a `u128` exactly (it degrades to `f64`), so re-parsing a whole dump
        // through `Value` corrupts bodies like `census-2026-07-06/itoa`'s
        // `udiv128::udivmod_1e19`. Locals are types only, and the census walks nothing
        // else — so this is both narrower and safe.
        let reachable_if_keyed = {
            let mut locals_json = locals.clone();
            let mut next = 0usize;
            stamp_unique_principal_keys(&mut locals_json, &mut next);
            let probed_locals: Vec<trust_types::LocalDecl> = serde_json::from_value(locals_json)
                .unwrap_or_else(|e| {
                    // A locals list that survives serialization but not a stamped
                    // round-trip is a defect in this probe's premise, not something to
                    // skip past silently.
                    panic!("stamped locals probe failed on {}: {e}", path.display())
                });
            let mut probed = func.clone();
            probed.body.locals = probed_locals;
            reachable_dyn_carriers(&probed).len()
        };

        let entry = by_corpus.entry(corpus_of(&root, &path)).or_default();
        entry.demanded += demanded;
        entry.keyed += keyed;
        entry.minted += minted;
        entry.reachable_if_keyed += reachable_if_keyed;
        entry.files_with_dyn += 1;
    }
    by_corpus
}

fn load_control_fixture() -> serde_json::Value {
    let path = fixtures_root().join(CONTROL_FIXTURE);
    assert!(
        path.is_file(),
        "control fixture missing at {} — this gate's always-live half is pinned to it; \
         if it moved, re-pin CONTROL_FIXTURE to another committed dump holding exactly \
         one Ty::Dynamic",
        path.display()
    );
    let text = std::fs::read_to_string(&path).expect("read control fixture");
    serde_json::from_str(&text).expect("control fixture is JSON")
}

// --- date arithmetic for the expiry rule (no chrono dependency) -------------

/// Days since the Unix epoch for a proleptic-Gregorian date (Howard Hinnant's
/// `days_from_civil`).
fn days_from_civil(y: i64, m: i64, d: i64) -> i64 {
    let y = if m <= 2 { y - 1 } else { y };
    let era = if y >= 0 { y } else { y - 399 } / 400;
    let yoe = y - era * 400;
    let mp = (m + 9) % 12;
    let doy = (153 * mp + 2) / 5 + d - 1;
    let doe = yoe * 365 + yoe / 4 - yoe / 100 + doy;
    era * 146_097 + doe - 719_468
}

fn parse_ymd(s: &str) -> i64 {
    let parts: Vec<&str> = s.split('-').collect();
    assert_eq!(parts.len(), 3, "expiry must be YYYY-MM-DD, got {s:?}");
    let n = |p: &str| p.parse::<i64>().unwrap_or_else(|_| panic!("bad date component in {s:?}"));
    days_from_civil(n(parts[0]), n(parts[1]), n(parts[2]))
}

fn today_days() -> i64 {
    let secs = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .expect("system clock is after 1970")
        .as_secs();
    (secs / 86_400) as i64
}

// ===========================================================================
// GATE 1 — corpus carrier coverage, with a self-retiring staleness waiver
// ===========================================================================

#[test]
fn trait_object_carrier_coverage_over_committed_corpus() {
    let census = census_corpus();
    let today = today_days();
    let expiry_of: BTreeMap<&str, &str> =
        STALE_FIXTURE_WAIVERS.iter().map(|w| (w.corpus, w.expires)).collect();

    println!("\n===== dyn carrier coverage over the committed prove-lane corpus =====");
    println!(
        "{:<40} {:>8} {:>6} {:>7} {:>10} {:>6}  {}",
        "corpus", "present", "keyed", "minted", "if-keyed", "files", "waiver"
    );
    let (mut td, mut tk, mut tm, mut tr) = (0usize, 0usize, 0usize, 0usize);
    for (name, c) in &census {
        println!(
            "{:<40} {:>8} {:>6} {:>7} {:>10} {:>6}  {}",
            name,
            c.demanded,
            c.keyed,
            c.minted,
            c.reachable_if_keyed,
            c.files_with_dyn,
            expiry_of.get(name.as_str()).map_or("-", |e| *e)
        );
        td += c.demanded;
        tk += c.keyed;
        tm += c.minted;
        tr += c.reachable_if_keyed;
    }
    println!("{:<40} {:>8} {:>6} {:>7} {:>10}", "TOTAL", td, tk, tm, tr);
    println!(
        "\nSTATE: {tm} of {td} `Ty::Dynamic` nodes in locals model a carrier; {} DECLINE.\n\
         CAUSE A (all rows): {CAUSE_A}.\n\
         \x20 -> a re-dump (task #199, needs a stage2 trustc) restores {tr} of them: the \
         `if-keyed` column is the REAL seam answering a keyed probe.\n\
         CAUSE B ({} nodes, {}% — INDEPENDENT of the key): {CAUSE_B}.\n\
         \x20 -> those are NOT fixed by a re-dump; widening the walk is a separate change.\n\
         RETIREMENT: delete a row once its corpus is re-dumped — this gate fails while a \
         row sits over a corpus that has become keyed or started minting.",
        td - tm,
        td - tr,
        (td - tr) * 100 / td.max(1),
    );
    println!("=====================================================================\n");

    let mut failures: Vec<String> = Vec::new();

    // --- every corpus that demands carriers must model some, or be waived ---
    for (name, c) in &census {
        let waiver = STALE_FIXTURE_WAIVERS.iter().find(|w| w.corpus == name.as_str());
        let Some(waiver) = waiver else {
            failures.push(format!(
                "UNWAIVED COVERAGE COLLAPSE in corpus `{name}`: {} of {} `Ty::Dynamic` nodes \
                 model no carrier and there is no waiver row. Either the corpus is newly \
                 stale (fix the dumps) or a consumer regressed (fix the consumer). Adding a \
                 row is a decision, not a workaround.",
                c.demanded - c.minted,
                c.demanded,
            ));
            continue;
        };

        // RETIREMENT, executable: a keyed corpus no longer has this row's cause.
        if c.keyed > 0 {
            failures.push(format!(
                "WAIVER RETIRED BY FIX in corpus `{name}`: {} of {} nodes now carry a faithful \
                 `principal_key`, so the row's stated cause (pre-8b9626a7de dumps) no longer \
                 holds. DELETE the row from STALE_FIXTURE_WAIVERS and lower \
                 WAIVED_DEMAND_CEILING by {}.",
                c.keyed, c.demanded, waiver.demanded,
            ));
        }
        // A waived corpus that models anything is likewise no longer waivable.
        if c.minted > 0 {
            failures.push(format!(
                "WAIVER SUPERSEDED in corpus `{name}`: it now mints {} carrier(s). DELETE the \
                 row and let the coverage floor hold it.",
                c.minted,
            ));
        }
        // EXPIRY: past the date the row stops applying and coverage is demanded.
        let expires = parse_ymd(waiver.expires);
        if today > expires {
            failures.push(format!(
                "WAIVER EXPIRED for corpus `{name}` (expired {}): it still models 0 of {} trait \
                 objects. The waiver has run out of runway — re-dump the corpus (task #199, \
                 needs a stage2 trustc) or, with an owner decision, extend WAIVER_EXPIRY and \
                 say why. Do not delete the row while the outage stands.",
                waiver.expires, c.demanded,
            ));
        } else {
            let left = expires - today;
            if left <= 30 {
                println!(
                    "WARN: waiver for `{name}` expires in {left} day(s) ({}). Re-dump or renew.",
                    waiver.expires
                );
            }
        }
        // DRIFT: a corpus must not quietly shrink and pass by having less to model.
        if c.demanded != waiver.demanded || c.files_with_dyn != waiver.files_with_dyn {
            failures.push(format!(
                "WAIVER SUBJECT DRIFTED in corpus `{name}`: pinned present={} files={}, \
                 measured present={} files={}. A dump was added, deleted, or stopped \
                 deserializing. Re-measure deliberately and re-pin — never widen to fit.",
                waiver.demanded, waiver.files_with_dyn, c.demanded, c.files_with_dyn,
            ));
        }
        // REACH: how far the production walk traverses, measured through the real seam.
        // This is the LIVE half of the corpus gate — it is a real, non-zero number today
        // (164 of 481) that moves the moment `dyn_principal_keys_in` changes in either
        // direction. Narrowing the walk shrinks it and fails here; widening it is welcome
        // progress that must be re-pinned deliberately.
        if c.reachable_if_keyed != waiver.reachable_if_keyed {
            let verb = if c.reachable_if_keyed < waiver.reachable_if_keyed {
                "NARROWED — the census now reaches FEWER trait objects; this is a coverage \
                 regression in `dyn_principal_keys_in`, fix it rather than re-pin"
            } else {
                "WIDENED — the census now reaches MORE trait objects; welcome, re-pin the \
                 row and lower WAIVED_DEMAND_CEILING to match"
            };
            failures.push(format!(
                "WALK REACH CHANGED in corpus `{name}`: pinned if-keyed={}, measured {}. {verb}.",
                waiver.reachable_if_keyed, c.reachable_if_keyed,
            ));
        }
    }

    // --- an orphan row (its corpus vanished entirely) is also a failure -----
    for waiver in STALE_FIXTURE_WAIVERS {
        if !census.contains_key(waiver.corpus) {
            failures.push(format!(
                "ORPHAN WAIVER for corpus `{}`: it demands no trait-object carriers at all \
                 (deleted, renamed, or every dump stopped deserializing). DELETE the row, or \
                 restore the corpus.",
                waiver.corpus,
            ));
        }
    }

    // --- RATCHET: the unmodelled demand may only ever shrink ---------------
    let unmodelled = td - tm;
    if unmodelled > WAIVED_DEMAND_CEILING {
        failures.push(format!(
            "RATCHET BROKEN: {unmodelled} `Ty::Dynamic` nodes now model no carrier, above the \
             ceiling of {WAIVED_DEMAND_CEILING}. Trait-object coverage got WORSE. Raising this \
             number is not a re-pin — find what stopped modelling.",
        ));
    }

    assert!(
        failures.is_empty(),
        "dyn carrier corpus gate RED ({} problem(s)):\n  - {}",
        failures.len(),
        failures.join("\n  - "),
    );
}

// ===========================================================================
// GATE 2 — the always-live half: the seam works when the key is present
// ===========================================================================
//
// While the corpus half is waived, THIS is what guards the code. It is never
// waived, uses a real committed dump, and covers the merge hazard the corpus
// cannot express (8 trait names, all single-bound and argument-free, never two in
// one file) by stamping the two-key case a re-dump would produce.

#[test]
fn dyn_carrier_identity_is_keyed_on_the_principal_not_the_trait_name() {
    // Both stampings leave `trait_name` UNTOUCHED and identical. Under the pre-
    // `fd824f53df` keying these two produced ONE carrier name for two different
    // types; under the faithful key they must produce two.
    let bare = "core::fmt::Write";
    let with_auto = "core::fmt::Write+core::marker::Send";

    let mint = |key: &str| {
        let mut json = load_control_fixture();
        stamp_principal_key(&mut json, key);
        let func: VerifiableFunction =
            serde_json::from_value(json).expect("stamped control fixture still deserializes");
        let carriers = reachable_dyn_carriers(&func);
        assert_eq!(
            carriers.len(),
            1,
            "the control fixture holds exactly one Ty::Dynamic, so a keyed re-dump must mint \
             exactly one carrier — got {} for key {key:?}",
            carriers.len(),
        );
        carriers.into_iter().next().expect("one carrier")
    };

    let a = mint(bare);
    let b = mint(with_auto);

    assert_ne!(
        a.name, b.name,
        "MERGE HAZARD LIVE: two trait objects differing only in an auto trait minted ONE \
         carrier name ({}). Identity must derive from `principal_key`, never `trait_name` \
         (identical in both).",
        a.name,
    );
    assert_ne!(a.vtable_name, b.vtable_name, "the vtable records must not merge either");

    // …and both register as SEPARATE existentials in a real CIC kernel environment.
    // This is the end of the chain `inhabit_verifiable_function` drives.
    let mut env = Environment::with_prelude();
    let registry = register_dyn_carriers(&mut env, &[a.clone(), b.clone()]);
    assert_eq!(
        registry.len(),
        2,
        "both carriers must register; the merge would have admitted the second against the \
         first's vtable",
    );
    for carrier in [&a, &b] {
        assert!(registry.get(&carrier.name).is_some(), "{} registers", carrier.name);
        assert!(
            env.inductive_info(&Name::from_string(&carrier.vtable_name)).is_some(),
            "{} exists independently in the env",
            carrier.vtable_name,
        );
        for n in [carrier.vtable_name.as_str(), carrier.name.as_str()] {
            assert!(
                env.axiom_deps(&Name::from_string(n)).expect("declared").is_empty(),
                "{n} must rest on exactly the 3 foundational axioms (no 4th axiom)",
            );
        }
    }
}

// ===========================================================================
// GATE 3 — the negative control: no key means NO carrier, never a guessed one
// ===========================================================================

#[test]
fn dyn_carrier_seam_fails_closed_on_an_unkeyed_dump() {
    let json = load_control_fixture();
    let (mut demanded, mut keyed) = (0usize, 0usize);
    count_dynamic(&json["body"]["locals"], &mut demanded, &mut keyed);
    assert_eq!(demanded, 1, "control fixture must hold exactly one Ty::Dynamic");
    assert_eq!(keyed, 0, "control fixture must be a STALE (unkeyed) dump — that is its job");

    let func: VerifiableFunction =
        serde_json::from_value(json).expect("control fixture deserializes");
    assert!(
        reachable_dyn_carriers(&func).is_empty(),
        "FAIL-OPEN: an unkeyed `Ty::Dynamic` minted a carrier. A carrier keyed on the erased \
         `trait_name` is exactly the merge `principal_key` exists to prevent — declining is \
         the only sound answer.",
    );
}
