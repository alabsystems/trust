use super::CensusDischarges;

fn credited(sites: &[(&str, Option<bool>)]) -> Vec<String> {
    let mut ledger = CensusDischarges::default();
    for (key, verdict) in sites {
        ledger.note(key, *verdict);
    }
    // Sorted below, so the set's iteration order never reaches the result.
    #[allow(rustc::potential_query_instability)]
    let mut keys: Vec<String> = ledger.into_credited().into_iter().collect();
    keys.sort();
    keys
}

/// A key is granted only when EVERY recorded site of it was censused total.
#[test]
fn census_ledger_grants_a_key_only_when_every_site_is_total() {
    assert_eq!(credited(&[("k", Some(true)), ("k", Some(true))]), vec!["k".to_string()]);
    assert_eq!(credited(&[("k", Some(true)), ("k", Some(false))]), Vec::<String>::new());
    assert_eq!(credited(&[("k", Some(false)), ("k", Some(true))]), Vec::<String>::new());
    assert_eq!(
        credited(&[("a", Some(true)), ("b", Some(false))]),
        vec!["a".to_string()],
        "a declined key withholds only itself"
    );
}

/// Trust (2026-09-27): a WITNESS site (a B-lane member's, never walked) can
/// withhold a key a walked site earned, but grants nothing on its own.
#[test]
fn census_ledger_witness_site_withholds_but_never_grants() {
    let witnessed = |walked: &[(&str, Option<bool>)], witness: &[(&str, Option<bool>)]| {
        let mut ledger = CensusDischarges::default();
        for (key, verdict) in walked {
            ledger.note(key, *verdict);
        }
        for (key, verdict) in witness {
            ledger.note_witness(key, *verdict);
        }
        #[allow(rustc::potential_query_instability)]
        let mut keys: Vec<String> = ledger.into_credited().into_iter().collect();
        keys.sort();
        keys
    };
    assert_eq!(witnessed(&[], &[("k", Some(true))]), Vec::<String>::new());
    assert_eq!(witnessed(&[("k", Some(true))], &[("k", Some(true))]), vec!["k".to_string()]);
    assert_eq!(witnessed(&[("k", Some(true))], &[("k", Some(false))]), Vec::<String>::new());
    assert_eq!(witnessed(&[("k", Some(true))], &[("k", None)]), Vec::<String>::new());
}

/// Trust (2026-09-27): a site the census does NOT speak for (`None` — a
/// callee outside `core`/`alloc`/`std`) withholds its key too. The bridge
/// spends a granted key by name on every row of the lowered module, so a
/// grant may never cover a site nobody judged; before this, `None` recorded
/// nothing and a total site of the same spelling carried the grant.
#[test]
fn census_ledger_site_it_did_not_judge_withholds_the_key() {
    assert_eq!(credited(&[("k", Some(true)), ("k", None)]), Vec::<String>::new());
    assert_eq!(credited(&[("k", None), ("k", Some(true))]), Vec::<String>::new());
    assert_eq!(credited(&[("k", None)]), Vec::<String>::new());
}
