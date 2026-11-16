//! The refusal catalog (design §2.7): every `Refusal` variant has a stable
//! code and a one-line meaning, and EVERY code has a fixture that produces
//! it. Adding a variant without a fixture fails here.
//!
//! The fixtures are the real stage1 dumps in `tests/ir/` wherever a real
//! body exhibits the refusal (a shape only an older producer emitted, such
//! as S1's erased `for`, from its held dump in `tests/ir/771983b92/`);
//! `synthetic.trust_ir` (hand-written, labeled so) covers the four shapes
//! no real dump has. The verdict-level codes
//! (`PC-REPLAY`, `PC-ENGINE-DISAGREE`) are conditions on the host's
//! evidence; they are produced by [`site_verdict`] from that evidence.

mod common;

use std::collections::{BTreeMap, BTreeSet};

use common::*;
use trust_platform_census::refusal::{CATALOG, one_of_each};
use trust_platform_census::verdict::{
    Completeness, NonVacuity, Outcome, SiteEvidence, SiteVerdict, site_verdict,
};
use trust_platform_census::{CensusOptions, CensusOutput, HirSite, SiteGate, SiteKind, coverage};
use trust_platform_derive::derive::DeriveOptions;

#[test]
fn every_code_is_stable_unique_and_explained() {
    let codes: Vec<&str> = CATALOG.iter().map(|r| r.code).collect();
    let set: BTreeSet<&str> = codes.iter().copied().collect();
    assert_eq!(set.len(), codes.len(), "duplicate codes");
    let variants: BTreeSet<&str> = one_of_each().iter().map(|r| r.code()).collect();
    assert_eq!(variants, set, "every variant has a catalog row and every row a variant");
    for r in CATALOG {
        assert!(r.code.starts_with("PC-"), "{}", r.code);
        assert!(!r.meaning.is_empty() && !r.source.is_empty(), "{}", r.code);
    }
    for r in one_of_each() {
        assert!(r.to_string().starts_with(r.code()), "{r}");
        assert_eq!(r.row().code, r.code());
    }
}

fn note(seen: &mut BTreeMap<&'static str, String>, code: &'static str, what: String) {
    seen.entry(code).or_insert(what);
}

fn all(seen: &mut BTreeMap<&'static str, String>, tag: &str, out: &CensusOutput) {
    for r in &out.refusals {
        note(seen, r.refusal.code(), format!("{tag}: {}", r.refusal));
    }
}

fn ok_evidence(root: usize, ps: usize) -> SiteEvidence {
    SiteEvidence {
        root,
        program_site: ps,
        env: 0,
        outcome: Outcome::NoCounterexample { completeness: Completeness::Exhaustive },
        non_vacuity: NonVacuity::Witnessed,
        derive_violation: false,
    }
}

#[test]
#[allow(clippy::too_many_lines)]
fn every_code_has_a_fixture_that_produces_it() {
    let mut seen: BTreeMap<&'static str, String> = BTreeMap::new();
    let o = CensusOptions::default();

    // The real census_shapes dump.
    let m = module("census_shapes");
    let side = sidecar("census_shapes");
    let out = census(&m, "census_shapes");
    all(&mut seen, "census_shapes", &out);
    // ... with the refused helper's identity unknown (PC-RESOLVE).
    let unresolved: String =
        side.lines().filter(|l| !l.starts_with("refused")).collect::<Vec<_>>().join("\n");
    all(&mut seen, "census_shapes without the refused row", &census_with(&m, &unresolved, &o));
    // ... with an inlining budget of 1 (PC-SIZE).
    let small = CensusOptions { max_inline_depth: 1, ..CensusOptions::default() };
    all(&mut seen, "census_shapes, inline depth 1", &census_with(&m, &side, &small));
    // ... with typeck's drop facts for a translated root (PC-DROP-ELIDED).
    let drops = format!("{side}\ndrops spawn_full_inline std::fs::File\n");
    all(&mut seen, "census_shapes, typeck drop facts", &census_with(&m, &drops, &o));
    // I-SITES-COVERED with no HIR twin for any census site (PC-CENSUS-SKEW).
    for r in coverage::sites_covered(&m, &out, &[]) {
        note(
            &mut seen,
            r.refusal.code(),
            format!("census_shapes sites vs an empty HIR census: {}", r.refusal),
        );
    }

    // The measurement's constructs dump.
    let mc = module("constructs");
    let outc = census(&mc, "constructs");
    all(&mut seen, "constructs", &outc);
    // ... without the closure bindings (PC-PRE-EXEC-UNRESOLVED).
    let no_closures: String = sidecar("constructs")
        .lines()
        .filter(|l| !l.starts_with("closure"))
        .collect::<Vec<_>>()
        .join("\n");
    all(&mut seen, "constructs without closure rows", &census_with(&mc, &no_closures, &o));
    // The HIR sees c9's fcntl. The 771983b92 producer erased it
    // (PC-SITE-NOT-IN-IR, from the held dump below); today's lowers the
    // loop, so the site has its trust-ir twin and nothing is refused.
    let c9 = HirSite { body: "c9_range_loop".into(), line: 45, col: 32, callee: "fcntl".into() };
    let c9_refusals = coverage::sites_covered(&mc, &outc, &[c9]);
    assert!(
        c9_refusals.iter().all(|r| r.refusal.code() != "PC-SITE-NOT-IN-IR"),
        "today's producer lowers c9's loop: {c9_refusals:#?}"
    );
    for r in c9_refusals {
        note(&mut seen, r.refusal.code(), format!("constructs c9_range_loop: {}", r.refusal));
    }

    // The held 771983b92 census_shapes dump: its producer erased
    // `dup_stdout_for`'s `for` (S1) — PC-PRODUCER-ERASED, and the HIR's
    // `dup` has no census twin (PC-SITE-NOT-IN-IR).
    let held = "771983b92/census_shapes";
    let mh = module(held);
    all(&mut seen, held, &census(&mh, held));

    // The real aterm-uds dump: refused bodies (PC-BODY-NOT-LOWERED), the
    // Linux arm (PC-CFG-SKEW).
    let mu = module("aterm_uds");
    let outu = census(&mu, "aterm_uds");
    let darwin = vec![HirSite {
        body: "spawnfd::darwin_strip::mark_listed".into(),
        line: 1101,
        col: 20,
        callee: "fcntl".into(),
    }];
    for r in coverage::sites_covered(&mu, &outu, &darwin) {
        note(&mut seen, r.refusal.code(), format!("aterm-uds: {}", r.refusal));
    }
    let mut linux = darwin.clone();
    linux.push(HirSite {
        body: "spawnfd::platform::spawn".into(),
        line: 820,
        col: 27,
        callee: "fork".into(),
    });
    for r in coverage::cfg_skew(&darwin, &linux) {
        note(&mut seen, r.refusal.code(), format!("aterm-uds linux arm: {}", r.refusal));
    }

    // The synthetic fixture.
    let ms = module("synthetic");
    let outs = census(&ms, "synthetic");
    all(&mut seen, "synthetic", &outs);
    for s in &outs.sites {
        if let SiteGate::Unanalysed(rs) = outs.gate(s.id) {
            for r in rs {
                note(
                    &mut seen,
                    r.code(),
                    format!("synthetic site {} in {}: {r}", s.symbol, s.body),
                );
            }
        }
    }

    // Verdict-level codes, from real derivations.
    let site_of = |out: &CensusOutput, body: &str| {
        out.sites.iter().find(|s| s.body == body && s.kind == SiteKind::Fork).map(|s| s.id).unwrap()
    };
    for body in ["spawn_never_execs", "spawn_pid_dependent"] {
        let (i, rp) = root(&out, &m, body);
        let s = rp.policy_sites[0].site;
        let (e, _) = evidence(&out, i, rp.policy_sites[0].program_site);
        if let SiteVerdict::Unanalysed(rs) = site_verdict(&out, s, &[e]) {
            for r in rs {
                note(&mut seen, r.code(), format!("{body}: {r}"));
            }
        }
    }
    let (i, rp) = root(&out, &m, "spawn_full_inline");
    let (e, _) =
        evidence_with(&out, i, rp.policy_sites[0].program_site, 0, &DeriveOptions { budget: 3 });
    if let Outcome::DeriveFailed { refusal } = &e.outcome {
        note(&mut seen, refusal.code(), format!("spawn_full_inline, budget 3: {refusal}"));
    }
    // The host's evidence conditions (C-1): a failed replay, and an
    // exploration that disagrees with ty.
    let s = site_of(&out, "spawn_full_inline");
    let ps = rp.policy_sites[0].program_site;
    let bad_replay = SiteEvidence {
        outcome: Outcome::ReplayFailed { detail: "a step did not re-execute".into() },
        ..ok_evidence(i, ps)
    };
    let disagree = SiteEvidence { derive_violation: true, ..ok_evidence(i, ps) };
    for ev in [bad_replay, disagree] {
        if let SiteVerdict::Unanalysed(rs) = site_verdict(&out, s, &[ev]) {
            for r in rs {
                note(&mut seen, r.code(), format!("spawn_full_inline, host evidence: {r}"));
            }
        }
    }

    for (code, what) in &seen {
        println!("{code:24} {what}");
    }
    let missing: Vec<&str> =
        CATALOG.iter().map(|r| r.code).filter(|c| !seen.contains_key(c)).collect();
    assert!(missing.is_empty(), "codes no fixture produces: {missing:?}");
}
