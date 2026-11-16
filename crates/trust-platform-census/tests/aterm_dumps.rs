//! What the census covers on the REAL aterm dumps (the measurement's stage1
//! trustc 771983b92 dumps of aterm-uds and aterm-pty at aterm 4ba80b2b6),
//! printed as a report: sites seen (by kind), policy sites, roots, and every
//! policy site's gate by `PC-*` code. The dumps carry no host facts (no HIR
//! effect lists, typeck drop facts or HIR site census: that host is PR 9),
//! so nothing may read "not refuted": the test asserts the census fails
//! closed on real code with every refusal named.

mod common;

use std::collections::BTreeMap;

use common::*;
use trust_platform_census::{SiteGate, SiteKind};

fn report(name: &str) -> BTreeMap<&'static str, usize> {
    let m = module(name);
    let out = census(&m, name);
    let s = &out.stats;
    println!(
        "== {name}: {} functions, {} bodies; {} sites, {} policy; {} root candidates, {} \
         translated, {} refused",
        s.functions,
        s.bodies,
        s.sites,
        s.policy_sites,
        s.root_candidates,
        s.roots_translated,
        s.roots_refused
    );
    let mut kinds: BTreeMap<SiteKind, usize> = BTreeMap::new();
    for site in &out.sites {
        *kinds.entry(site.kind).or_default() += 1;
    }
    println!("   sites by kind: {kinds:?}");
    let mut by_code: BTreeMap<&'static str, usize> = BTreeMap::new();
    let (mut analysed, mut unanalysed) = (0, 0);
    for site in out.sites.iter().filter(|s| s.policy) {
        match out.gate(site.id) {
            SiteGate::Check(_) => {
                analysed += 1;
                println!("   CHECK      {:?} `{}` in `{}`", site.kind, site.symbol, site.body);
            }
            SiteGate::Unanalysed(rs) => {
                unanalysed += 1;
                let mut codes: Vec<&str> = rs.iter().map(|r| r.code()).collect();
                codes.sort_unstable();
                codes.dedup();
                for c in &codes {
                    *by_code.entry(c).or_default() += 1;
                }
                println!(
                    "   UNANALYSED {:?} `{}` in `{}` ({}): {}",
                    site.kind,
                    site.symbol,
                    site.body,
                    site.span_text,
                    codes.join(" ")
                );
            }
        }
    }
    println!("   policy sites: {analysed} with a check to run, {unanalysed} unanalysed");
    println!("   unanalysed policy sites by code: {by_code:?}");
    println!("   all refusals by code: {:?}", s.refusals_by_code);
    println!(
        "   crate-level: {:?}",
        out.crate_refusals().iter().map(|r| r.code()).collect::<Vec<_>>()
    );
    for (h, r) in out.unanalysed_hir_sites() {
        *by_code.entry(r.code()).or_default() += 1;
        println!(
            "   UNANALYSED (HIR only) `{}` in `{}` at {}:{}: {}",
            h.callee,
            h.body,
            h.line,
            h.col,
            r.code()
        );
    }
    for site in out.sites.iter().filter(|s| s.policy) {
        assert!(
            matches!(out.gate(site.id), SiteGate::Unanalysed(ref rs) if !rs.is_empty()),
            "{name}: a policy site without host facts must be a named refusal: {site:?}"
        );
    }
    by_code
}

#[test]
fn the_real_aterm_dumps_fail_closed_with_named_refusals() {
    let uds = report("aterm_uds");
    let pty = report("aterm_pty");
    // The product spawn sites are in bodies the producer refused: each is
    // unanalysed by its HIR identity.
    assert_eq!(uds.get("PC-BODY-NOT-LOWERED"), Some(&4), "{uds:?}");
    assert_eq!(pty.get("PC-BODY-NOT-LOWERED"), Some(&2), "{pty:?}");
    // Every unanalysed policy site carries at least one named code; the
    // host-fact gates are among them (no HIR lists, no drop facts).
    for (name, codes) in [("aterm_uds", &uds), ("aterm_pty", &pty)] {
        for c in codes.keys() {
            assert!(c.starts_with("PC-"), "{name}: {c}");
        }
    }
}
