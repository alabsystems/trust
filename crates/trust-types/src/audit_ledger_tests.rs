// Tests for crate::audit_ledger: attribution to the innermost scope (L4-SCOPE-2), a scope
// that drains once, the disabled no-op, column escaping, and the build-independent texts
// the audit digests and keys (L4-AUDIT-7, L4-AUDIT-8).
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use super::*;

const SITE: &str = "crates/trust-verifier-api/src/lib.rs:MAX_VERIFIER_RUN_RECORDS";

fn cap() -> AuditEntry {
    AuditEntry::Cap { site: SITE }
}

#[test]
fn an_entry_under_one_active_scope_is_that_scopes() {
    let ledger = Ledger::new();
    let scope = ledger.enter("demo::f");
    ledger.record(cap());
    assert_eq!(scope.finish(), vec![cap()]);
    assert!(ledger.take_crate_level().is_empty());
}

#[test]
fn an_entry_recorded_on_another_thread_belongs_to_the_one_active_scope() {
    let ledger = Ledger::new();
    let scope = ledger.enter("demo::f");
    std::thread::scope(|threads| {
        threads.spawn(|| ledger.record(cap()));
    });
    assert_eq!(scope.finish(), vec![cap()]);
}

#[test]
fn a_nested_scope_gets_what_is_recorded_while_it_is_open() {
    // A body's pass nested in another's on the one front-end thread: the inner scope gets
    // its own entries and those of the threads it waits on; the outer one gets the rest.
    let ledger = Ledger::new();
    let outer = ledger.enter("demo::f");
    ledger.record(AuditEntry::CertifyStop { index: Some(1), cause: StopCause::Effort });
    let inner = ledger.enter("demo::g");
    ledger.record(cap());
    std::thread::scope(|threads| {
        threads.spawn(|| ledger.record(cap()));
    });
    assert_eq!(inner.finish(), vec![cap(), cap()]);
    ledger.record(AuditEntry::CertifyStop { index: Some(2), cause: StopCause::WallBackstop });
    assert_eq!(
        outer.finish(),
        vec![
            AuditEntry::CertifyStop { index: Some(1), cause: StopCause::Effort },
            AuditEntry::CertifyStop { index: Some(2), cause: StopCause::WallBackstop },
        ]
    );
    assert!(ledger.take_crate_level().is_empty());
}

#[test]
fn scopes_of_two_threads_own_only_their_threads_entries() {
    let ledger = Ledger::new();
    let first = ledger.enter("demo::f");
    std::thread::scope(|threads| {
        threads.spawn(|| {
            let second = ledger.enter("demo::g");
            ledger.record(AuditEntry::CertifyStop { index: None, cause: StopCause::Effort });
            // A thread with no scope of its own cannot tell which of two threads' scopes
            // it works for: crate-level.
            std::thread::scope(|helpers| {
                helpers.spawn(|| ledger.record(cap()));
            });
            assert_eq!(
                second.finish(),
                vec![AuditEntry::CertifyStop { index: None, cause: StopCause::Effort }]
            );
        });
    });
    ledger.record(AuditEntry::CertifyStop { index: Some(3), cause: StopCause::Effort });
    assert_eq!(
        first.finish(),
        vec![AuditEntry::CertifyStop { index: Some(3), cause: StopCause::Effort }]
    );
    assert_eq!(ledger.take_crate_level(), vec![cap()]);
    assert!(ledger.take_crate_level().is_empty(), "taking clears the crate level");
}

#[test]
fn no_active_scope_is_crate_level() {
    let ledger = Ledger::new();
    ledger.record(cap());
    assert_eq!(ledger.take_crate_level(), vec![cap()]);
}

#[test]
fn a_scope_drains_once() {
    let ledger = Ledger::new();
    let scope = ledger.enter("demo::f");
    ledger.record(cap());
    assert_eq!(scope.finish(), vec![cap()]);
    // The finished scope is gone: a later entry is crate-level, and the drained one does
    // not come back.
    ledger.record(AuditEntry::Stop { lane: "solver".into(), cause: StopCause::Effort, item: None });
    assert_eq!(
        ledger.take_crate_level(),
        vec![AuditEntry::Stop { lane: "solver".into(), cause: StopCause::Effort, item: None }]
    );
}

#[test]
fn a_scope_dropped_without_finish_hands_its_entries_to_the_crate() {
    let ledger = Ledger::new();
    {
        let _scope = ledger.enter("demo::f");
        ledger.record(cap());
    }
    assert_eq!(ledger.take_crate_level(), vec![cap()]);
}

#[test]
fn the_process_ledger_is_a_no_op_when_disabled() {
    // The test process runs without TRUST_ELIDE_AUDIT (the harness never sets it); with
    // the variable unset nothing is recorded or opened.
    if enabled() {
        return;
    }
    assert!(Scope::enter("demo::f").is_none());
    cap_hit(SITE);
    stop("solver", StopCause::WallBackstop, None);
    certify_stop(Some(0), StopCause::Unclassified);
    assert!(cap_hit_if(true, SITE));
    assert!(!cap_hit_if(false, SITE));
    assert!(take_crate_level().is_empty());
    assert!(LEDGER.take_crate_level().is_empty());
    append_rows("never.tsv", &["x\n".to_string()]);
}

#[test]
fn entries_render_their_rows() {
    assert_eq!(cap().kind(), "CAP");
    assert_eq!(cap().columns(), vec![SITE.to_string()]);
    let stop = AuditEntry::Stop {
        lane: "ay".into(),
        cause: StopCause::WallBackstop,
        item: Some(StopItem::StrictCheckCancelled),
    };
    assert_eq!(stop.kind(), "STOP");
    assert_eq!(
        stop.columns(),
        vec!["ay[strict-check-cancelled]".to_string(), "wall-backstop".to_string()]
    );
    let certify = AuditEntry::CertifyStop { index: None, cause: StopCause::Unclassified };
    assert_eq!(certify.kind(), "CERTIFY-STOP");
    assert_eq!(certify.columns(), vec!["-".to_string(), "unclassified".to_string()]);
}

#[test]
fn columns_never_carry_the_separator() {
    assert_eq!(escape_column("a\tb\nc\rd"), "a b c d");
    let line = row_line(
        "CAP",
        &["in\tput", "out", "krate", "f\nn"],
        &["si\tte".to_string(), "plain".to_string()],
    );
    assert_eq!(line, "CAP\tin put\tout\tkrate\tf n\tsi te\tplain\n");
    assert_eq!(line.matches('\t').count(), 6);
}

/// [`build_independent`] of one text.
fn alone(text: &str) -> String {
    build_independent(&[text]).pop().unwrap_or_default()
}

#[test]
fn crate_stamps_are_renamed_by_first_appearance() {
    let one = r#"{"callee":"__trust_crate@e22d88b308847231::core::ops::Add","other":"__trust_crate@0000000000000011::std::vec::Vec","again":"__trust_crate@e22d88b308847231::x"}"#;
    let rebuilt = r#"{"callee":"__trust_crate@aaaaaaaaaaaaaaaa::core::ops::Add","other":"__trust_crate@bbbbbbbbbbbbbbbb::std::vec::Vec","again":"__trust_crate@aaaaaaaaaaaaaaaa::x"}"#;
    let renamed = alone(one);
    assert_eq!(
        renamed,
        r#"{"callee":"__trust_crate@#0::core::ops::Add","other":"__trust_crate@#1::std::vec::Vec","again":"__trust_crate@#0::x"}"#
    );
    assert_eq!(alone(rebuilt), renamed, "another build's ids, one pattern");
    // One crate where there were two is a different text.
    let merged = r#"{"callee":"__trust_crate@aaaaaaaaaaaaaaaa::core::ops::Add","other":"__trust_crate@aaaaaaaaaaaaaaaa::std::vec::Vec","again":"__trust_crate@aaaaaaaaaaaaaaaa::x"}"#;
    assert_ne!(alone(merged), renamed);
    // No stamp, or a stamp with no id, is unchanged.
    assert_eq!(alone("plain"), "plain");
    assert_eq!(alone("__trust_crate@::x"), "__trust_crate@::x");
}

#[test]
fn args_fingerprints_are_renamed_by_first_appearance() {
    let fingerprint = |lo, hi| crate::args_fingerprint::render_trailing_args_fingerprint(lo, hi);
    let row =
        |a: &str, b: &str| format!(r#"{{"m":"`Vec::<u32>::drain{a}` and `g{b}` and `h{a}`"}}"#);
    let one = row(&fingerprint(1, 2), &fingerprint(3, 4));
    let rebuilt = row(&fingerprint(5, 6), &fingerprint(7, 8));
    assert_eq!(
        alone(&one),
        r#"{"m":"`Vec::<u32>::drain::<__trust_args@#0>` and `g::<__trust_args@#1>` and `h::<__trust_args@#0>`"}"#
    );
    assert_eq!(alone(&rebuilt), alone(&one));
    let merged = row(&fingerprint(5, 6), &fingerprint(5, 6));
    assert_ne!(alone(&merged), alone(&one));
}

#[test]
fn def_path_debug_disambiguators_are_renamed_by_first_appearance() {
    let row = |core: &str, alloc: &str| {
        format!(
            "{{\"m\":\"DefId(2:4495 ~ core[{core}]::ops::FnOnce::Output) DefId(2:9 ~ core[{core}]::marker::Send) DefId(3:1 ~ alloc[{alloc}]::boxed::Box)\"}}"
        )
    };
    let renamed = alone(&row("82a8", "1f0c"));
    assert_eq!(renamed, row("#0", "#1"));
    assert_eq!(alone(&row("0b3e", "ffff")), renamed, "another build's crate ids");
    assert_ne!(alone(&row("0b3e", "0b3e")), renamed, "one crate where there were two");
    // The crate name stays; a `~ ` that opens no `name[hhhh]` is left alone.
    for plain in ["a ~ b", "x ~ core[82a]", "x ~ core[82a8", "~ [82a8]", "~ 9core[82a8]", "~ "] {
        assert_eq!(alone(plain), plain);
    }
}

/// CALL-REACH-1's message for `std::panic::set_hook`'s dropped hook, as one build printed it,
/// with its list's auto traits in `order` and `core`'s disambiguator `core`.
fn set_hook_row(core: &str, order: [&str; 2]) -> String {
    let auto = |name: &str| {
        let index = if name == "Sync" { 4225 } else { 32157 };
        format!(
            "Binder {{ value: AutoTrait(DefId(2:{index} ~ {core}::marker::{name})), bound_vars: [] }}"
        )
    };
    format!(
        "{{\"m\":\"call to absent callee `std::panicking::set_hook` (CALL-REACH-1: its instance drops a `dyn \
         [Binder {{ value: Trait(std::ops::Fn<(&std::panic::PanicHookInfo<'_>,)>), bound_vars: [Region(BrAnon), \
         Region(BrAnon)] }}, Binder {{ value: Projection(ExistentialProjection {{ def_id: DefId(2:4495 ~ \
         {core}::ops::function::FnOnce::Output), args: [(&'^0 std::panic::PanicHookInfo<'^1>,)], term: \
         Term::Ty(()), .. }}), bound_vars: [Region(BrAnon), Region(BrAnon)] }}, {}, {}] + '{{erased}}`, whose \
         destructor is chosen by its vtable) may panic\"}}",
        auto(order[0]),
        auto(order[1]),
    )
}

#[test]
fn a_dyn_types_auto_traits_and_projections_are_put_in_path_order() {
    // Measured 2026-10-15: the stage 1s of two commits listed `Sync` and `Send` the other way
    // round for one source, because rustc orders them by `DefPathHash`.
    let one = alone(&set_hook_row("core[16eb]", ["Sync", "Send"]));
    assert_eq!(alone(&set_hook_row("core[0a1b]", ["Send", "Sync"])), one, "another build");
    assert_eq!(one, set_hook_row("core[#0]", ["Send", "Sync"]), "path order, principal first");
    // A different set of auto traits is a different text.
    let send_only = set_hook_row("core[16eb]", ["Send", "Send"]);
    assert_ne!(alone(&send_only), one);
    // Two projections sort by path too; the principal keeps its place before them.
    let projections = |first: &str, second: &str| {
        format!(
            "dyn [Binder {{ value: Trait(Coroutine), bound_vars: [] }}, Binder {{ value: \
             Projection(ExistentialProjection {{ def_id: DefId(2:{first}) }}), bound_vars: [] }}, \
             Binder {{ value: Projection(ExistentialProjection {{ def_id: DefId(2:{second}) }}), \
             bound_vars: [] }}] + 'x"
        )
    };
    let yield_ = "11 ~ core[16eb]::ops::Coroutine::Yield";
    let return_ = "12 ~ core[16eb]::ops::Coroutine::Return";
    assert_eq!(alone(&projections(yield_, return_)), alone(&projections(return_, yield_)));
    // A list inside an entry is ordered as well.
    let nested = |order: [&str; 2]| {
        format!(
            "dyn [Binder {{ value: Trait(Fn<(Box<{}>,)>), bound_vars: [] }}]",
            set_hook_row("core[16eb]", order)
        )
    };
    assert_eq!(alone(&nested(["Sync", "Send"])), alone(&nested(["Send", "Sync"])));
    // Anything that is not such a list is left as it is.
    for plain in [
        "dyn [",
        "dyn []",
        "dyn [a, b]",
        "dyn [Binder { value: Region(x), bound_vars: [] }, Binder { value: Trait(T), bound_vars: [] }]",
        "dyn [Binder { value: AutoTrait(DefId(2:9 ~ core::marker::Sync)) ) ]",
        "x dyn [b] y dyn [a]",
    ] {
        assert_eq!(alone(plain), plain);
    }
}

#[test]
fn ids_are_renamed_across_the_whole_function() {
    let stamp = |id: &str, path: &str| format!("__trust_crate@{id}::{path}");
    // Two rows naming one crate, and a third naming another.
    let function =
        |a: &str, b: &str| vec![stamp(a, "core::f"), stamp(a, "core::g"), stamp(b, "core::h")];
    let texts =
        |rows: &[String]| build_independent(&rows.iter().map(String::as_str).collect::<Vec<_>>());
    let one = texts(&function("aaaaaaaaaaaaaaaa", "bbbbbbbbbbbbbbbb"));
    assert_eq!(one, vec![stamp("#0", "core::f"), stamp("#0", "core::g"), stamp("#1", "core::h")]);
    assert_eq!(texts(&function("cccccccccccccccc", "dddddddddddddddd")), one, "another build");
    // Text by text the rows are the same; across the function, one crate became two.
    let split = texts(&[
        stamp("aaaaaaaaaaaaaaaa", "core::f"),
        stamp("bbbbbbbbbbbbbbbb", "core::g"),
        stamp("bbbbbbbbbbbbbbbb", "core::h"),
    ]);
    assert_ne!(split, one);
    // The order rows are visited in is their renamed spelling, not the build's ids: the ids
    // sort differently under another build, and the texts do not move.
    let x = |id: &str| format!("x {}", stamp(id, "a"));
    let y = |id: &str| format!("y {}", stamp(id, "b"));
    let low = texts(&[y("1111111111111111"), x("2222222222222222")]);
    let high = texts(&[y("ffffffffffffffff"), x("eeeeeeeeeeeeeeee")]);
    assert_eq!(low, high);
    assert_eq!(low, vec![y("#1"), x("#0")]);
}

#[test]
fn sc8_row_disclosures_become_their_count_of_causes() {
    let row = |causes: &[&str]| {
        let causes: Vec<String> = causes.iter().map(|cause| (*cause).to_string()).collect();
        format!(
            "{{\"detail\":\"not enumerated (via f){}\",\"x\":1}}",
            crate::sc8_row_disclosure(&causes)
        )
    };
    let (env, fun, arr) = (
        "open principal `dyn Env` @ f",
        "open principal `dyn Fn(u32)` @ g",
        "open principal `dyn Fn([u8; 4])` @ h",
    );
    let one = row(&[env, fun, arr]);
    assert_eq!(alone(&one), r#"{"detail":"not enumerated (via f) [SC-8 causes=3]","x":1}"#);
    // Another build names the causes in another order: the same text.
    assert_eq!(alone(&row(&[fun, arr, env])), alone(&one));
    assert_eq!(alone(&row(&[arr, env, fun])), alone(&one));
    // A cause with the separator in it counts once, whichever build names it.
    assert_eq!(alone(&row(&[arr, env])), alone(&row(&[env, arr])));
    assert_eq!(
        alone(&row(&[arr, env])),
        r#"{"detail":"not enumerated (via f) [SC-8 causes=2]","x":1}"#
    );
    assert_eq!(alone(&row(&[env])), r#"{"detail":"not enumerated (via f) [SC-8 causes=1]","x":1}"#);
    // A different count, or a difference outside the disclosure, is a different text.
    assert_ne!(alone(&row(&[env, fun])), alone(&one));
    assert_ne!(alone(&one.replace("(via f)", "(via g)")), alone(&one));
    // An opener with no close is left as it is.
    let unclosed = format!("a{}b", crate::SC8_ROW_DISCLOSURE_OPEN);
    assert_eq!(alone(&unclosed), unclosed);
}
