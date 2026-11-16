//! Regression tests for the adversarial review of census/c0 (cec67a957f):
//! thirteen findings, seven of them false passes. Every input is a REAL
//! stage1 dump of the review's sources (`tests/ir/adv*.rs` beside their
//! dumps), each naming its trustc in its `; trustc` header, except `adv7m`
//! and `adv2t`, hand edits of real dumps labeled in their headers. The
//! review ran on trustc 771983b92; its dumps whose producer erased `for`
//! loops (S1) or emitted no drops are held in `tests/ir/771983b92/` for the
//! findings that need that shape (F1, F2). Every leaking root forks and strips every
//! descriptor >= 3 in the child before the leak, so only the leak itself can
//! make a site refuted.
//!
//! Each site is judged through the host's path ([`common::verdict_of`]):
//! the census, the single-site program derived in every library
//! environment, NativeTyEngine on the leak and non-vacuity formulas, the
//! replay, the join.

mod common;

use std::collections::{BTreeMap, BTreeSet};

use common::*;
use trust_ir::{FuncId, Module, SourceSpan};
use trust_platform_census::stub::SidecarContext;
use trust_platform_census::verdict::{Outcome, SiteVerdict};
use trust_platform_census::{
    Callee, CensusContext, CensusOptions, CensusOutput, HirEffect, HirSite, SiteKind, run,
    symcensus,
};

/// The census site of `kind` in `body`.
fn site(out: &CensusOutput, body: &str, kind: SiteKind) -> usize {
    out.sites
        .iter()
        .find(|s| s.body == body && s.kind == kind)
        .unwrap_or_else(|| panic!("no {kind:?} site in `{body}`"))
        .id
}

fn codes(v: &SiteVerdict) -> Vec<&'static str> {
    match v {
        SiteVerdict::Unanalysed(rs) => rs.iter().map(|r| r.code()).collect(),
        _ => Vec::new(),
    }
}

/// The verdict of `body`'s fork site, printed.
fn fork_verdict(out: &CensusOutput, body: &str) -> SiteVerdict {
    let v = verdict_of(out, site(out, body, SiteKind::Fork));
    match &v {
        SiteVerdict::Refuted { trace, .. } => println!("{body}: REFUTED\n  {}", trace.join("\n  ")),
        SiteVerdict::NotRefuted { premises, .. } => println!(
            "{body}: not refuted under {:?}",
            premises.iter().map(|p| p.code).collect::<Vec<_>>()
        ),
        SiteVerdict::Unanalysed(rs) => {
            println!("{body}: unanalysed");
            for r in rs {
                println!("  {r}");
            }
        }
    }
    v
}

fn assert_unanalysed(v: &SiteVerdict, code: &str) {
    assert!(codes(v).contains(&code), "want {code}: {v:#?}");
}

/// A clean refutation: replayed, no over-approximating choice (the
/// verdict's own condition), with the leak named.
fn assert_refuted(v: &SiteVerdict, what: &str) {
    match v {
        SiteVerdict::Refuted { trace, .. } => {
            assert!(trace.iter().any(|l| l.contains("execv")), "{trace:#?}");
        }
        other => panic!("{what} must be refuted: {other:#?}"),
    }
}

// ---- false passes ----------------------------------------------------------

/// F1: the producer's erased `for` (S1) one call deeper — the loop's body
/// calls a local helper (`leak_one` dups stdout; `mark` strips). The loop
/// function lowered to a bare `ret` (the 771983b92 dumps, held in
/// `tests/ir/771983b92/`). I-EFFECTS-COVERED counted only foreign and
/// std-table calls, so the erased LOCAL call was invisible: the leak read
/// not refuted and the correct strip was refuted. Now every call not
/// audited effect-free is counted: PC-PRODUCER-ERASED, both ways.
///
/// Today's producer lowers both loops: the leak is refuted through the
/// helper, and the correct strip is still never an error.
#[test]
fn f1_an_erased_call_to_a_local_helper_is_producer_erased() {
    let m = module("771983b92/adv");
    let out = census(&m, "771983b92/adv");
    let rs = out.root_refusals(func(&m, "adv_erased_helper"));
    assert!(
        rs.iter().any(|r| r.code() == "PC-PRODUCER-ERASED" && r.to_string().contains("leak_one")),
        "{rs:#?}"
    );
    assert_unanalysed(&fork_verdict(&out, "adv_erased_helper"), "PC-PRODUCER-ERASED");

    let m2 = module("771983b92/adv2");
    let out2 = census(&m2, "771983b92/adv2");
    let v = fork_verdict(&out2, "adv_strip_via_for");
    assert!(!matches!(v, SiteVerdict::Refuted { .. }), "correct code is never an error: {v:#?}");
    assert_unanalysed(&v, "PC-PRODUCER-ERASED");

    // Today's dumps: the loops are lowered.
    let m = module("adv");
    let out = census(&m, "adv");
    match fork_verdict(&out, "adv_erased_helper") {
        SiteVerdict::Refuted { trace, .. } => {
            assert!(trace.iter().any(|l| l.contains("dup(1)")), "{trace:#?}");
            assert!(trace.iter().any(|l| l.contains("execv")), "{trace:#?}");
        }
        other => panic!("the leak through the lowered loop must be refuted: {other:#?}"),
    }
    let m2 = module("adv2");
    let out2 = census(&m2, "adv2");
    let v = fork_verdict(&out2, "adv_strip_via_for");
    assert!(!matches!(v, SiteVerdict::Refuted { .. }), "correct code is never an error: {v:#?}");
}

/// F2: Drop of types other than the std carriers. A guard whose Drop dups
/// stdout read not refuted (dropped implicitly, or with `drop(g)`); a user
/// owner whose Drop closes was refuted (correct code). Now the drop gate
/// covers every type whose glue may have an effect, from typeck's facts
/// (required) and from the module's own Drop impls; `mem::drop` of a
/// non-trivial type is PC-DROP-UNMODELED. (Those drops were implicit in the
/// 771983b92 dumps, held in `tests/ir/771983b92/`.)
#[test]
fn f2_a_user_drop_impl_is_a_drop_refusal_never_a_verdict() {
    let held = "771983b92/adv2";
    let m = module(held);
    let out = census(&m, held);
    assert_unanalysed(&fork_verdict(&out, "adv_drop_dup"), "PC-DROP-ELIDED");
    assert_unanalysed(&fork_verdict(&out, "adv_drop_dup_explicit"), "PC-DROP-UNMODELED");
    let v = fork_verdict(&out, "adv_owner_closed");
    assert!(!matches!(v, SiteVerdict::Refuted { .. }), "correct code is never an error: {v:#?}");
    assert_unanalysed(&v, "PC-DROP-ELIDED");

    // Without typeck's facts the census's own scan still sees the guard:
    // its Drop impl is in the module.
    let no_facts: String = sidecar(held)
        .lines()
        .filter(|l| !l.starts_with("drops adv_drop_dup DupOnDrop"))
        .chain(std::iter::once("drops adv_drop_dup"))
        .collect::<Vec<_>>()
        .join("\n");
    let out = census_with(&m, &no_facts, &CensusOptions::default());
    let rs = out.root_refusals(func(&m, "adv_drop_dup"));
    assert!(
        rs.iter().any(|r| r.code() == "PC-DROP-ELIDED" && r.to_string().contains("DupOnDrop")),
        "{rs:#?}"
    );
    // And a body with no typeck facts at all cannot pass the gate.
    let none: String = sidecar(held)
        .lines()
        .filter(|l| !l.starts_with("drops adv_drop_dup "))
        .collect::<Vec<_>>()
        .join("\n");
    let out = census_with(&m, &none, &CensusOptions::default());
    assert!(
        out.root_refusals(func(&m, "adv_drop_dup"))
            .iter()
            .any(|r| r.code() == "PC-DROP-ELIDED" && r.to_string().contains("no typeck drop facts"))
    );

    // adv.rs: a guard whose Drop clears FD_CLOEXEC on fd 5.
    let m = module("771983b92/adv");
    let out = census(&m, "771983b92/adv");
    assert_unanalysed(&fork_verdict(&out, "adv_drop_guard"), "PC-DROP-ELIDED");
    // The control: an std OwnedFd dropped implicitly.
    let m = module("771983b92/adv8");
    let out = census(&m, "771983b92/adv8");
    assert_unanalysed(&fork_verdict(&out, "adv_owned_implicit"), "PC-DROP-ELIDED");

    // Today's producer emits each implicit drop (Step-2 4b/4c): the census
    // meets the drop itself and refuses glue it does not model, before the
    // drop gate runs — still a refusal, never a verdict.
    for (name, bodies) in [
        ("adv2", &["adv_drop_dup", "adv_drop_dup_explicit", "adv_owner_closed"][..]),
        ("adv", &["adv_drop_guard"][..]),
        ("adv8", &["adv_owned_implicit"][..]),
    ] {
        let m = module(name);
        let out = census(&m, name);
        for body in bodies {
            let v = fork_verdict(&out, body);
            assert!(!matches!(v, SiteVerdict::Refuted { .. }), "{name} {body}: {v:#?}");
            assert_unanalysed(&v, "PC-DROP-UNMODELED");
        }
    }
}

/// F3: a closure handed to core. `srcs.iter().for_each(|x| dup(*x + k))`
/// after the strip: `for_each` is DEFINED in core (design §2.2 classifies it
/// CoreAlloc), a CoreAlloc call was treated as effect-free, and the
/// closure's `dup` never ran — not refuted. Now a core/alloc call off the
/// audited lists is PC-UNKNOWN-STD, and no list entry takes a closure.
#[test]
fn f3_a_closure_handed_to_core_is_never_skipped() {
    let m = module("adv3");
    let out = census(&m, "adv3");
    let rs = out.root_refusals(func(&m, "adv_for_each_dup"));
    assert!(
        rs.iter().any(|r| r.code() == "PC-UNKNOWN-STD" && r.to_string().contains("for_each")),
        "{rs:#?}"
    );
    assert_unanalysed(&fork_verdict(&out, "adv_for_each_dup"), "PC-UNKNOWN-STD");
}

/// F4: un-stripping counted as "declared". `fcntl(fd, F_SETFD, 0)` for
/// every fd >= 3, or for fd 5 alone, then exec: the derivation recorded
/// every successfully un-flagged number as a declared lane, including the
/// RL-INIT foreign descriptor the program never created — not refuted.
/// Now un-flagging (or placing) a FOREIGN description declares nothing:
/// the foreign descriptor leaks, refuted with a replayed trace.
#[test]
fn f4_unflagging_a_foreign_descriptor_is_a_leak_not_a_lane() {
    let m = module("adv");
    let out = census(&m, "adv");
    let v = fork_verdict(&out, "adv_unstrip_direct");
    assert_refuted(&v, "adv_unstrip_direct");

    let m2 = module("adv2");
    let out2 = census(&m2, "adv2");
    assert_refuted(&fork_verdict(&out2, "adv_unstrip_all"), "adv_unstrip_all");

    // A lane the program places from its OWN descriptor still declares it:
    // closing everything, then `dup2(1, 3)` (stdout's description on 3).
    let m3 = module("adv3");
    let out3 = census(&m3, "adv3");
    let v = fork_verdict(&out3, "adv_close_then_place");
    assert!(matches!(v, SiteVerdict::NotRefuted { .. }), "{v:#?}");
}

/// F5: the state budget did not bound a forked child. A descriptor loop
/// the ForRange recognizer correctly declines (step 2, `<=`, a `u32`
/// index) ran in ONE macro step outside the budget: 6.3 s / 149 MB at
/// 20 000 iterations, unbounded at 2^31. Now a child's macro step is
/// bounded in events (`MAX_CHILD_EVENTS`): PC-BUDGET, fast. (`break` on the
/// first failing `fcntl` is refuted outright: the strip stops at the first
/// hole, fd 3, and the foreign descriptor at 4 leaks — a real bug.)
#[test]
fn f5_a_child_loop_the_recognizer_declines_is_a_bounded_budget_refusal() {
    let t0 = std::time::Instant::now();
    let m = module("adv3");
    let out = census(&m, "adv3");
    assert_refuted(&fork_verdict(&out, "adv_strip_until_hole"), "adv_strip_until_hole");
    for (dump, body) in [
        ("adv4", "adv_step2_bounded"),
        ("adv", "adv_u32_strip"),
        ("adv3", "adv_strip_le"),
        ("adv3", "adv_strip_step2"),
    ] {
        let m = module(dump);
        let out = census(&m, dump);
        let v = fork_verdict(&out, body);
        assert!(
            matches!(&v, SiteVerdict::Unanalysed(rs) if rs.iter().any(|r| r.code() == "PC-BUDGET" && r.to_string().contains("macro step"))),
            "{body}: {v:#?}"
        );
    }
    println!("five unbounded child loops refused in {:?}", t0.elapsed());
}

/// F6: only success outcomes for allocating calls. In the child, `kqueue()`
/// or `socket()` fails (ENFILE, ENOMEM, ENOBUFS, a sandbox's EACCES) and
/// the failure path execs WITHOUT the strip — not refuted. Now every census
/// event explores one representative admissible failure: refuted.
#[test]
fn f6_an_allocating_call_can_fail_and_its_error_path_is_checked() {
    let m = module("adv5");
    let out = census(&m, "adv5");
    for body in ["adv_errpath_kqueue", "adv_errpath_socket"] {
        let v = fork_verdict(&out, body);
        assert_refuted(&v, body);
        if let SiteVerdict::Refuted { trace, .. } = &v {
            assert!(trace.iter().any(|l| l.contains("= -1")), "{body}: the failure: {trace:#?}");
        }
    }
}

/// F7: one machine's descriptor limit. A strip capped at 92 160 — this
/// Mac's `kern.maxfilesperproc`, a sysctl (`kern.maxfiles` is 184 320) —
/// read not refuted under `Limits::measured_darwin()`. The census's
/// library environment is host-independent: a foreign descriptor may sit
/// anywhere below the `int` bound, above the soft limit too.
#[test]
fn f7_a_strip_capped_at_this_hosts_limit_is_refuted() {
    let m = module("adv6");
    let out = census(&m, "adv6");
    let v = fork_verdict(&out, "adv_strip_to_this_hosts_limit");
    assert_refuted(&v, "adv_strip_to_this_hosts_limit");
    if let SiteVerdict::Refuted { trace, .. } = &v {
        assert!(trace.iter().any(|l| l.contains("for fd in 3..92160")), "{trace:#?}");
    }
    // The full strip is still not refuted in every environment.
    let ms = module("census_shapes");
    let outs = census(&ms, "census_shapes");
    assert!(matches!(fork_verdict(&outs, "spawn_full_inline"), SiteVerdict::NotRefuted { .. }));
}

// ---- refusals that were never surfaced ---------------------------------------

/// A context whose HIR site census is overridden (a host whose site census
/// disagrees with the trust-ir census).
struct SkewedSites<'m> {
    inner: SidecarContext<'m>,
    sites: Option<Vec<HirSite>>,
    product: Option<Vec<HirSite>>,
}

impl CensusContext for SkewedSites<'_> {
    fn callee(&self, f: FuncId) -> Callee {
        self.inner.callee(f)
    }
    fn closure_body_of(&self, d: FuncId, s: Option<SourceSpan>) -> Result<FuncId, String> {
        self.inner.closure_body_of(d, s)
    }
    fn render_span(&self, s: SourceSpan) -> String {
        self.inner.render_span(s)
    }
    fn hir_effects(&self, f: FuncId) -> Option<Vec<HirEffect>> {
        self.inner.hir_effects(f)
    }
    fn drops(&self, f: FuncId) -> Option<Vec<String>> {
        self.inner.drops(f)
    }
    fn hir_sites(&self) -> Option<Vec<HirSite>> {
        self.sites.clone()
    }
    fn product_sites(&self) -> Option<Vec<HirSite>> {
        self.product.clone()
    }
    fn spawn_capable_crates(&self) -> Option<BTreeSet<String>> {
        self.inner.spawn_capable_crates()
    }
}

/// F8: I-SITES-COVERED and C-7 returned their refusals on the side: a
/// census site with no HIR twin read not refuted. Now [`run`] merges them,
/// site-linked: the site is unanalysed; a HIR-only or shipped-only site is
/// an unanalysed site by its identity; no HIR site census at all is
/// unanalysed too.
#[test]
fn f8_a_site_census_refusal_reaches_the_verdict() {
    let m = module("adv3");
    let side = sidecar("adv3");
    let honest = census(&m, "adv3");
    let body = "adv_close_then_place";
    assert!(matches!(fork_verdict(&honest, body), SiteVerdict::NotRefuted { .. }));
    let cx = SidecarContext::parse(&m, &side).expect("sidecar");
    let all = cx.hir_sites().expect("a HIR site census");
    // The host's HIR census misses the fork (and sees one more call).
    let mut skewed: Vec<HirSite> =
        all.iter().filter(|h| !(h.body == body && h.callee == "fork")).cloned().collect();
    skewed.push(HirSite { body: body.into(), line: 55, col: 8, callee: "close".into() });
    let product = {
        let mut p = skewed.clone();
        p.push(HirSite { body: "linux_arm".into(), line: 1, col: 1, callee: "fork".into() });
        p
    };
    let o = CensusOptions::default();
    let sk = SkewedSites { inner: cx, sites: Some(skewed), product: Some(product) };
    let out = run(&m, &sk, &o);
    assert_unanalysed(&fork_verdict(&out, body), "PC-CENSUS-SKEW");
    let hir_only: Vec<(&str, &str)> =
        out.unanalysed_hir_sites().iter().map(|(h, r)| (h.callee.as_str(), r.code())).collect();
    assert!(hir_only.contains(&("close", "PC-SITE-NOT-IN-IR")), "{hir_only:?}");
    assert!(hir_only.contains(&("fork", "PC-CFG-SKEW")), "{hir_only:?}");

    // No HIR site census: no site reads not refuted.
    let cx = SidecarContext::parse(&m, &side).expect("sidecar");
    let none = SkewedSites { inner: cx, sites: None, product: None };
    let out = run(&m, &none, &o);
    assert_unanalysed(&fork_verdict(&out, body), "PC-CENSUS-SKEW");
    assert!(out.crate_refusals().iter().any(|r| r.code() == "PC-CFG-SKEW"));
}

// ---- latent false passes -------------------------------------------------------

/// F9: a load's signedness. An `i32` cell holding -1 read back as `u32`
/// (4 294 967 295 > 100: the child execs without the strip). The census kept
/// -1 for the u32 load and took the wrong branch — not refuted. Now a load
/// (or store) of another integer type of the same width reinterprets.
#[test]
fn f9_a_load_reinterprets_signedness() {
    let m = module("adv7m");
    let out = census(&m, "adv7m");
    assert_refuted(&fork_verdict(&out, "adv_transmute_guard"), "adv_transmute_guard");
}

/// F10: `thread::spawn` bypassed its refusal: X3a's STD-THREAD-SPAWN row was
/// looked up before the PC-THREAD-UNRESOLVED branch, and on Darwin a
/// `JoinHandle` holds only pointers, so the row was accepted with its
/// closure never run. Now thread spawns are refused before the table.
#[test]
fn f10_thread_spawn_is_refused_before_the_symbol_table() {
    let m = module("adv2t");
    let out = census(&m, "adv2t");
    let rs = out.root_refusals(func(&m, "adv_drop_dup"));
    assert!(rs.iter().any(|r| r.code() == "PC-THREAD-UNRESOLVED"), "{rs:#?}");
    let t = site(&out, "adv_drop_dup", SiteKind::ThreadSpawn);
    assert_unanalysed(&verdict_of(&out, t), "PC-THREAD-UNRESOLVED");
}

// ---- policy sites ----------------------------------------------------------------

/// F11: a raw exec of the root process was not a policy site (`SiteKind::
/// Exec` was outside fd-inherit while `CommandExt::exec` was inside): a
/// `dup(1)` then `execv` of the process itself had no root and no refusal.
/// Now every exec is under fd-inherit: in the root process it is
/// PC-UNMODELED; in a forked child it reads its fork's verdict.
#[test]
fn f11_every_exec_is_a_policy_site() {
    let m = module("adv");
    let out = census(&m, "adv");
    let e = site(&out, "adv_reexec", SiteKind::Exec);
    assert!(out.sites[e].policy);
    assert_unanalysed(&verdict_of(&out, e), "PC-UNMODELED");

    // An exec in a child answers with its fork: the full strip's exec is
    // not refuted, the 65 536-capped one's (fork_strip_exec, joined over
    // its roots) is refuted.
    let ms = module("census_shapes");
    let outs = census(&ms, "census_shapes");
    let full = site(&outs, "spawn_full_inline", SiteKind::Exec);
    assert!(matches!(verdict_of(&outs, full), SiteVerdict::NotRefuted { .. }));
    let shared = site(&outs, "fork_strip_exec", SiteKind::Exec);
    assert!(matches!(verdict_of(&outs, shared), SiteVerdict::Refuted { .. }));
}

/// F12: upstream spawners left no trace (Critique C-3's backstop was not
/// built). `nm -u` of the upstream crate's rlib shows `_fork`, `_execv`,
/// `_dup`: the symbol census reports the crate unless it is under the
/// policy or audited; the crates it marks spawn-capable make every call
/// into them a site (PC-UPSTREAM until C8), and the host's HIR site in the
/// body the producer refused is an unanalysed site by identity.
#[test]
fn f12_upstream_spawners_are_found_by_the_symbol_census() {
    let read = |f: &str| std::fs::read_to_string(path(&format!("nm/{f}"))).expect("nm output");
    let mut crates = BTreeMap::new();
    crates.insert(
        ("upstream_spawn".to_string(), "0.0.0".to_string()),
        symcensus::parse_nm(&read("libupstream_spawn.nm")),
    );
    crates
        .insert(("libc".to_string(), "0.2".to_string()), symcensus::parse_nm(&read("liblibc.nm")));
    let bad = symcensus::check(&crates, &BTreeSet::new(), &[]);
    let names: BTreeSet<&str> = bad.iter().map(|u| u.reference.names.as_str()).collect();
    assert!(bad.iter().all(|u| u.krate == "upstream_spawn"), "{bad:?}");
    assert_eq!(names, ["dup", "execv", "fork"].into_iter().collect(), "{bad:?}");
    for u in &bad {
        println!("{u}");
    }
    assert_eq!(symcensus::spawn_capable(&crates), ["upstream_spawn".to_string()].into());

    let m = module("adv3");
    let out = census(&m, "adv3");
    assert!(
        out.unanalysed_hir_sites()
            .iter()
            .any(|(h, r)| h.callee == "upstream_spawn::spawn_leaky"
                && r.code() == "PC-BODY-NOT-LOWERED"),
        "{:#?}",
        out.unanalysed_hir_sites()
    );

    // A lowered call into a spawn-capable upstream crate is a site.
    let ms = module("census_shapes");
    let side = sidecar("census_shapes").replace("\nspawners\n", "\nspawners libc\n");
    let out = census_with(&ms, &side, &CensusOptions::default());
    let s = site(&out, "spawn_upstream", SiteKind::UpstreamSpawn);
    assert_unanalysed(&verdict_of(&out, s), "PC-UPSTREAM");
    // ... and every upstream call is one when the symbol census did not run.
    let side = sidecar("census_shapes").replace("\nspawners\n", "\n");
    let out = census_with(&ms, &side, &CensusOptions::default());
    assert!(out.sites.iter().any(|s| s.kind == SiteKind::UpstreamSpawn));
    // With it and libc clean, no upstream site.
    let out = census(&ms, "census_shapes");
    assert!(out.sites.iter().all(|s| s.kind != SiteKind::UpstreamSpawn));
}

/// F13: `match fork() { 0 => …, pid => pid }` refused correct code: the
/// Switch path did not apply the parent's pid != 0 fact, so the child's arm
/// was translated in the parent ("exec of the root process"). Now the
/// census translates it; this child dups stdout after the strip: refuted.
#[test]
fn f13_match_on_the_fork_result_is_translated() {
    let m = module("adv2");
    let out = census(&m, "adv2");
    let rs = out.root_refusals(func(&m, "adv_match_pid"));
    assert!(!rs.iter().any(|r| r.to_string().contains("exec of the root process")), "{rs:#?}");
    assert_refuted(&fork_verdict(&out, "adv_match_pid"), "adv_match_pid");
}

/// The review's model-row note: `fcntl(fd, F_SETFD)` with no third argument
/// was modeled as argument 0 ("clear close-on-exec, declare a lane"); C
/// leaves it undefined. Now it is PC-NONCONST-ARG. (A labeled hand edit of
/// the real adv6 dump: the strip's `fcntl` call loses its third operand.)
#[test]
fn fcntl_without_its_argument_is_refused_not_zero() {
    let text = std::fs::read_to_string(path("adv6.trust_ir")).expect("dump");
    let edited = text.replace("call @func.2(%2, %13, %14)", "call @func.2(%2, %13)");
    assert_ne!(edited, text, "the hand edit applies");
    let m: Module = trust_ir::parser::parse_module(&edited).expect("parses");
    let out = census(&m, "adv6");
    let rs = out.root_refusals(func(&m, "adv_strip_to_this_hosts_limit"));
    assert!(
        rs.iter().any(|r| r.code() == "PC-NONCONST-ARG" && r.to_string().contains("undefined")),
        "{rs:#?}"
    );
}

/// What held up in the review stays so: a strip that skips fd 7 is refuted;
/// an exec on a dead branch of a full strip is refuted (the live branch
/// execs first).
#[test]
fn the_reviews_controls_hold() {
    let m = module("adv3");
    let out = census(&m, "adv3");
    assert_refuted(&fork_verdict(&out, "adv_strip_skip7"), "adv_strip_skip7");
    assert_refuted(
        &fork_verdict(&out, "adv_exec_without_strip_if_nonzero"),
        "adv_exec_without_strip_if_nonzero",
    );
    let _ = Outcome::ReplayFailed { detail: String::new() };
}
