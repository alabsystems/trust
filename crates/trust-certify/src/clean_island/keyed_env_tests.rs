// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! TG6: a keyed session imports a fact it already has and elaborates
//! nothing; every input of an elaboration misses when it changes; a corrupt
//! or wrong fact is quarantined and the island checked again.

use std::path::PathBuf;
use std::sync::Arc;

use clean_kernel::{Declaration, Expr};

use super::*;
use crate::clean_fact::FactContext;
use crate::clean_island::CleanIslandSession;

fn home(tag: &str) -> PathBuf {
    crate::clean_fact::test_scratch(&format!("keyed-env-{tag}"))
}

fn context(home: &std::path::Path, identity: &str, audit_every_hit: bool) -> Arc<FactContext> {
    Arc::new(FactContext::for_tests(home, identity, audit_every_hit))
}

fn session(facts: &Arc<FactContext>) -> CleanIslandSession {
    let mut session = CleanIslandSession::new();
    session.enable_facts(Arc::clone(facts));
    session
}

/// Two islands; the first leaves `TgSix` OPEN, which only the elaborator's
/// file context remembers.
const BATCH: [&str; 2] = [
    "namespace TgSix\ndef one : Nat := 1\nend TgSix\nopen TgSix\n",
    "theorem TgSix.one_eq : TgSix.one = 1 := rfl\n",
];

fn admit_imports(session: &mut CleanIslandSession, f: u64, g: u64) {
    session.keyed.admit(|env| {
        for (name, value) in [("trust_import_tgsix_f", f), ("trust_import_tgsix_g", g)] {
            env.add_decl(Declaration::Definition {
                name: Name::from_string(name),
                level_params: vec![],
                type_: Expr::const_(Name::from_string("Nat"), vec![]),
                value: Expr::nat_lit(value),
                is_reducible: false,
            })
            .expect("the admission checks");
        }
    });
}

const USES_F: &str = "theorem tgsix_uses_f : trust_import_tgsix_f = 5 := rfl\n";

#[test]
fn a_second_session_imports_the_batch_and_elaborates_nothing() {
    let home = home("hit");
    let facts = context(&home, "one", false);
    let mut first = session(&facts);
    let produced = first.check_all(&BATCH);
    assert!(!produced.is_rejected(), "{:?}", produced.outcomes);
    assert_eq!((first.keyed.elaborations, facts.written()), (1, 1));

    let mut second = session(&facts);
    let imported = second.check_all(&BATCH);
    assert_eq!(second.keyed.elaborations, 0, "a hit elaborates nothing");
    assert!(!second.is_tainted());
    assert_eq!(
        imported.outcomes.iter().map(|o| o.registered.clone()).collect::<Vec<_>>(),
        produced.outcomes.iter().map(|o| o.registered.clone()).collect::<Vec<_>>()
    );
    assert_eq!(second.env().local_fact_difference(first.env()), None);
    assert_eq!(
        second.env().declaration_verification(&Name::from_string("TgSix.one_eq")),
        Some(clean_kernel::env::DeclarationVerification::FullKernelCheck),
        "the producer's stamp is replayed"
    );
    let _ = std::fs::remove_dir_all(home);
}

/// A `def` whose value is a `∀` records the value's binder names, which a
/// named argument reads (`h (a := 3)` with `h : TgSixAll`). The delta carries
/// them: the batch stores a fact, a second session imports it, and a later
/// elaboration that reads the names agrees with the rebuild. Measured on
/// `astream-broker`, whose batches all failed to store before the delta
/// carried the table.
#[test]
fn a_definition_whose_value_is_a_forall_is_a_fact() {
    const DEF: [&str; 1] = [
        "def TgSixAll : Prop := ∀ (a : Nat), a = a\ntheorem tgSixAll_holds : TgSixAll := fun a => rfl\n",
    ];
    const USE: [&str; 1] = ["theorem tgSixUse : (3 : Nat) = 3 := tgSixAll_holds (a := 3)\n"];
    let home = home("value-binders");
    let facts = context(&home, "one", false);
    let mut first = session(&facts);
    assert!(!first.check_all(&DEF).is_rejected());
    assert_eq!(facts.written(), 1, "the batch is storable");
    let binders = |session: &CleanIslandSession| {
        session
            .env()
            .get_value_forall_binder_names(&Name::from_string("TgSixAll"))
            .map(|shape| shape.names.iter().map(ToString::to_string).collect::<Vec<_>>())
    };
    assert_eq!(binders(&first), Some(vec!["a".to_string()]));

    let mut second = session(&facts);
    assert!(!second.check_all(&DEF).is_rejected());
    assert_eq!(second.keyed.elaborations, 0, "a hit elaborates nothing");
    assert_eq!(binders(&second), binders(&first), "the hit replays the binder names");
    let used = second.check_all(&USE);
    assert!(!used.is_rejected(), "{:?}", used.outcomes);
    assert!(!second.is_tainted(), "the rebuild agrees with the hit");
    let _ = std::fs::remove_dir_all(home);
}

/// NEGATIVE CONTROL: a changed island misses and is elaborated.
#[test]
fn a_changed_island_misses() {
    let home = home("changed");
    let facts = context(&home, "one", false);
    session(&facts).check_all(&BATCH);
    let mut second = session(&facts);
    let changed = [BATCH[0], "theorem TgSix.one_eq : TgSix.one = 1 := by rfl\n"];
    assert!(!second.check_all(&changed).is_rejected());
    assert_eq!(second.keyed.elaborations, 1);
    let _ = std::fs::remove_dir_all(home);
}

/// NEGATIVE CONTROL: another compiler identity misses.
#[test]
fn another_compiler_identity_misses() {
    let home = home("identity");
    session(&context(&home, "one", false)).check_all(&BATCH);
    let mut second = session(&context(&home, "two", false));
    second.check_all(&BATCH);
    assert_eq!(second.keyed.elaborations, 1);
    let _ = std::fs::remove_dir_all(home);
}

/// NEGATIVE CONTROL: other session settings miss.
#[test]
fn other_session_settings_miss() {
    let home = home("params");
    let facts = context(&home, "one", false);
    session(&facts).check_all(&BATCH);
    let mut second = session(&facts);
    second.enable_model_checks();
    second.check_all(&BATCH);
    assert_eq!(second.keyed.elaborations, 1);
    let _ = std::fs::remove_dir_all(home);
}

#[test]
fn a_flipped_byte_is_quarantined_and_the_batch_checked_again() {
    let home = home("flip");
    let facts = context(&home, "one", false);
    session(&facts).check_all(&BATCH);
    let objects = facts.store().root().join("objects");
    for shard in std::fs::read_dir(&objects).expect("objects").flatten() {
        for object in std::fs::read_dir(shard.path()).expect("shard").flatten() {
            let mut bytes = std::fs::read(object.path()).expect("object");
            let middle = bytes.len() / 2;
            bytes[middle] ^= 0x40;
            std::fs::write(object.path(), bytes).expect("flip");
        }
    }
    let mut second = session(&facts);
    assert!(!second.check_all(&BATCH).is_rejected());
    assert_eq!(second.keyed.elaborations, 1, "the corrupt fact is not used");
    assert!(std::fs::read_dir(facts.store().root().join("quarantine")).expect("q").count() > 0);
    // The re-check stored a sound fact again.
    let mut third = session(&facts);
    third.check_all(&BATCH);
    assert_eq!(third.keyed.elaborations, 0);
    let _ = std::fs::remove_dir_all(home);
}

/// An edit to a body no island reaches is a hit; a changed body the island
/// uses is a miss, and a theorem it falsifies is an error.
#[test]
fn an_unrelated_body_hits_and_a_changed_imported_body_misses() {
    let home = home("imports");
    let facts = context(&home, "one", false);
    let mut first = session(&facts);
    first.check_all(&BATCH);
    admit_imports(&mut first, 5, 7);
    assert!(!first.check(USES_F).is_rejected());
    assert_eq!(facts.written(), 2);

    let mut unrelated = session(&facts);
    unrelated.check_all(&BATCH);
    admit_imports(&mut unrelated, 5, 8);
    assert!(!unrelated.check(USES_F).is_rejected());
    assert_eq!(unrelated.keyed.elaborations, 0, "`g` is not reached by the island");

    let mut changed = session(&facts);
    changed.check_all(&BATCH);
    admit_imports(&mut changed, 6, 7);
    let outcome = changed.check(USES_F);
    assert_eq!(changed.keyed.elaborations, 1, "`f` changed");
    assert!(outcome.is_rejected(), "`trust_import_tgsix_f = 5` is false now");
    assert!(changed.is_tainted());
    // A rejection is never stored (a clock-budgeted tactic can refuse under
    // load what it accepts otherwise), but it stays in the log and the chain:
    // the accepted island after it is stored with the rejection in its log.
    assert_eq!(facts.written(), 2, "the rejection stored nothing");
    const AFTER: &str = "theorem tgsix_after : 2 = 2 := rfl\n";
    assert!(!changed.check(AFTER).is_rejected());
    assert_eq!(facts.written(), 3, "the island after the rejection is stored");

    // The same false theorem again is elaborated again, and is the same
    // error, with the session tainted the same way.
    let mut again = session(&facts);
    again.check_all(&BATCH);
    admit_imports(&mut again, 6, 7);
    let repeated = again.check(USES_F);
    assert_eq!(
        (again.keyed.rebuilds, again.keyed.elaborations),
        (1, 1),
        "the rejection is elaborated again, after a rebuild past the batch's hit"
    );
    let messages = |outcome: &super::super::CleanIslandOutcome| -> Vec<String> {
        outcome.errors.iter().map(|error| error.message.clone()).collect()
    };
    assert_eq!(messages(&repeated), messages(&outcome));
    assert!(again.is_tainted());
    // The chain after the re-elaborated rejection is the one it had before,
    // so the island after it hits; the next miss rebuilds through the
    // rejected log entry without a failure of its own.
    assert!(!again.check(AFTER).is_rejected());
    assert_eq!(again.keyed.elaborations, 1, "the island after the rejection is a hit");
    let next = again.check("theorem tgsix_last : 3 = 3 := rfl\n");
    assert_eq!((again.keyed.rebuilds, again.keyed.elaborations), (2, 2));
    assert!(
        next.errors.iter().all(|error| !error.message.contains("local kernel facts")),
        "{:?}",
        next.errors
    );
    assert_eq!(facts.written(), 4, "nor did the rejection's repetition store anything");
    // `targo trust store verify --facts` replays each fact's log, the rejected
    // entry included, and reproduces every fact.
    let report = verify_store(facts.store());
    assert_eq!((report.reproduced, report.quarantined.len()), (4, 0), "{report:?}");
    let _ = std::fs::remove_dir_all(home);
}

/// Origin is authority, not merely a cache discriminator: replacing a checked
/// import's origin by an unrechecked olean origin makes the reference base
/// ineligible. The old fact cannot pass, and fresh checking must refuse.
#[test]
fn an_unrechecked_origin_ends_facts_and_is_refused() {
    let home = home("origin");
    let facts = context(&home, "one", false);
    let mut first = session(&facts);
    first.check_all(&BATCH);
    admit_imports(&mut first, 5, 7);
    assert!(!first.check(USES_F).is_rejected());

    // NEGATIVE CONTROL: the same admissions hit.
    let mut same = session(&facts);
    same.check_all(&BATCH);
    admit_imports(&mut same, 5, 7);
    assert!(!same.check(USES_F).is_rejected());
    assert_eq!(same.keyed.elaborations, 0);

    let mut other = session(&facts);
    other.check_all(&BATCH);
    admit_imports(&mut other, 5, 7);
    other.keyed.admit(|env| {
        assert!(env.set_constant_origin(
            Name::from_string("trust_import_tgsix_f"),
            clean_kernel::env::ConstantOrigin::olean_import(None),
        ));
    });
    let outcome = other.check(USES_F);
    assert_eq!(other.keyed.elaborations, 1, "the import's origin changed");
    assert!(outcome.is_rejected(), "an unrechecked imported base is not reference authority");
    assert!(
        outcome.errors.iter().any(|error| error.message.contains("reference")
            || error.message.contains("certification audit")),
        "{outcome:?}"
    );
    assert!(other.keyed.active().is_none(), "an ineligible reference base cannot reuse facts");
    let _ = std::fs::remove_dir_all(home);
}

/// TG11's shape: a Rust enum arrives as an inductive type with a tag table,
/// and a scalar import reads one tag. All of it is admitted before any island
/// runs, as TG11 admits `trust_type_*` aliases and `<C2>.toTag`. Editing a tag
/// leaves the constructor names, the match branches and the scalar import's
/// own bytes as they were.
fn admit_states(session: &mut CleanIslandSession, ready: u64, unrelated: u64) {
    let source = format!(
        "inductive TgElevenState where\n  | Ready\n  | Done\n\n\
         def TgElevenState.toTag (s : TgElevenState) : Nat :=\n  match s with\n  \
         | TgElevenState.Ready => {ready}\n  | TgElevenState.Done => 7\n"
    );
    let nat = || Expr::const_(Name::from_string("Nat"), vec![]);
    let ready_tag = Expr::app(
        Expr::const_(Name::from_string("TgElevenState.toTag"), vec![]),
        Expr::const_(Name::from_string("TgElevenState.Ready"), vec![]),
    );
    session.keyed.admit(|env| {
        let mut file_ctx = clean_elab::FileContext::new();
        let batch =
            crate::clean_island_batch::check_islands_batched(env, &mut file_ctx, &[&source]);
        assert!(!batch.is_rejected(), "the admitted datatype checks: {:?}", batch.outcomes);
        // The scalar imports are E6 admissions, which an island may not declare.
        for (name, value) in [
            ("trust_import_tgeleven_ready_tag", ready_tag),
            ("trust_import_tgeleven_unrelated", Expr::nat_lit(unrelated)),
        ] {
            env.add_decl(Declaration::Definition {
                name: Name::from_string(name),
                level_params: vec![],
                type_: nat(),
                value,
                is_reducible: false,
            })
            .expect("the admission checks");
        }
    });
}

/// TG11's tag-only mutant (`Ready` 42 -> 43) as a fact control. The theorem
/// reaches the tag table only through the scalar import's body and
/// `toTag`'s match. Editing the tag misses, and the theorem it falsifies is an
/// error. NEGATIVE CONTROL: an admitted body the theorem does not reach changes
/// and the fact still hits.
#[test]
fn a_tag_only_change_misses_and_falsifies_the_theorem() {
    const READY_IS_42: &str =
        "theorem tgeleven_ready : trust_import_tgeleven_ready_tag = 42 := rfl\n";
    let home = home("tag-table");
    let facts = context(&home, "one", false);
    let mut first = session(&facts);
    admit_states(&mut first, 42, 1);
    assert!(!first.check(READY_IS_42).is_rejected());
    assert_eq!(facts.written(), 1);

    let mut unrelated = session(&facts);
    admit_states(&mut unrelated, 42, 2);
    assert!(!unrelated.check(READY_IS_42).is_rejected());
    assert_eq!(unrelated.keyed.elaborations, 0, "the unrelated body is not reached");

    let mut mutant = session(&facts);
    admit_states(&mut mutant, 43, 1);
    let outcome = mutant.check(READY_IS_42);
    assert_eq!(mutant.keyed.elaborations, 1, "the tag table changed under `toTag`");
    assert!(outcome.is_rejected(), "`Ready`'s tag is 43 now");
    let _ = std::fs::remove_dir_all(home);
}

/// The reverse direction: a rejection is never stored, so the same
/// environment elaborates it again, and fixing the tag table it failed on
/// (named directly, not through a `trust_import_` name) elaborates the island
/// and accepts it. Only the acceptance is stored, and it is hit after.
#[test]
fn a_rejection_is_not_stored_and_the_fixed_table_is_accepted() {
    const READY_IS_43: &str =
        "theorem tgeleven_ready_fixed : TgElevenState.toTag TgElevenState.Ready = 43 := rfl\n";
    let home = home("rejection-fixed");
    let facts = context(&home, "one", false);
    let mut first = session(&facts);
    admit_states(&mut first, 42, 1);
    assert!(first.check(READY_IS_43).is_rejected());
    assert_eq!(facts.written(), 0, "a rejection is not stored");

    let mut same = session(&facts);
    admit_states(&mut same, 42, 1);
    assert!(same.check(READY_IS_43).is_rejected());
    assert_eq!(same.keyed.elaborations, 1, "the same environment elaborates the rejection again");
    assert_eq!(facts.written(), 0, "nor is its repetition");

    let mut fixed = session(&facts);
    admit_states(&mut fixed, 43, 1);
    let outcome = fixed.check(READY_IS_43);
    assert_eq!(fixed.keyed.elaborations, 1, "nothing was stored to hit");
    assert!(!outcome.is_rejected(), "{:?}", outcome.errors);
    assert_eq!(facts.written(), 1, "the acceptance is stored");

    let mut again = session(&facts);
    admit_states(&mut again, 43, 1);
    assert!(!again.check(READY_IS_43).is_rejected());
    assert_eq!(again.keyed.elaborations, 0, "the acceptance is hit");
    let _ = std::fs::remove_dir_all(home);
}

/// A rejection for a name that does not exist yet is accepted once the name
/// is admitted: nothing of the rejection survives to hide its arrival.
#[test]
fn a_rejection_misses_when_its_missing_name_arrives() {
    const LATE: &str = "theorem tgeleven_late_is_one : trust_type_tgeleven_late = 1 := rfl\n";
    let home = home("rejection-late");
    let facts = context(&home, "one", false);
    let mut first = session(&facts);
    assert!(first.check(LATE).is_rejected(), "no `trust_type_tgeleven_late` yet");

    let mut later = session(&facts);
    later.keyed.admit(|env| {
        env.add_decl(Declaration::Definition {
            name: Name::from_string("trust_type_tgeleven_late"),
            level_params: vec![],
            type_: Expr::const_(Name::from_string("Nat"), vec![]),
            value: Expr::nat_lit(1),
            is_reducible: false,
        })
        .expect("the admission checks");
    });
    let outcome = later.check(LATE);
    assert_eq!(later.keyed.elaborations, 1, "a name arrived in the environment");
    assert!(!outcome.is_rejected(), "{:?}", outcome.errors);
    let _ = std::fs::remove_dir_all(home);
}

/// After a hit the file context is behind; the next miss rebuilds it, so an
/// island that needs the batch's `open TgSix` still elaborates.
#[test]
fn a_miss_after_a_hit_rebuilds_the_elaborator() {
    let home = home("rebuild");
    let facts = context(&home, "one", false);
    session(&facts).check_all(&BATCH);
    let mut second = session(&facts);
    second.check_all(&BATCH);
    assert!(second.keyed.is_stale());
    let outcome = second.check("theorem tgsix_opened : one = 1 := rfl\n");
    assert!(!outcome.is_rejected(), "{:?}", outcome.errors);
    assert_eq!((second.keyed.rebuilds, second.keyed.elaborations), (1, 1));
    assert!(!second.keyed.is_stale());
    // NEGATIVE CONTROL: without the batch's `open`, the same island fails.
    let mut bare = CleanIslandSession::new();
    assert!(bare.check("theorem tgsix_opened : one = 1 := rfl\n").is_rejected());
    let _ = std::fs::remove_dir_all(home);
}

#[test]
fn an_audited_hit_is_elaborated_and_matches() {
    let home = home("audit");
    let facts = context(&home, "one", true);
    session(&facts).check_all(&BATCH);
    let mut second = session(&facts);
    assert!(!second.check_all(&BATCH).is_rejected());
    assert_eq!(second.keyed.elaborations, 1);
    assert_eq!(std::fs::read_dir(facts.store().root().join("quarantine")).expect("q").count(), 0);
    let _ = std::fs::remove_dir_all(home);
}

/// A fact that hashes (written by a same-user process, P-CORESIDENT) but says
/// something its elaboration did not is caught by the audit and by
/// `store verify`, and quarantined.
#[test]
fn a_forged_fact_is_caught_by_the_audit_and_by_store_verify() {
    let home = home("forged");
    let facts = context(&home, "one", false);
    session(&facts).check_all(&BATCH);
    let key = facts.store().keys()[0];
    let StoreRead::Present { bytes, .. } = facts.store().get(&key) else { panic!("stored") };
    let mut fact = StoredFact::decode(&bytes).expect("decodes");
    let mut outcomes: (
        Vec<super::super::CleanIslandOutcome>,
        Vec<crate::clean_island_batch::CleanIslandCycle>,
    ) = crate::clean_fact::decode(&fact.outcome).expect("the stored outcome decodes");
    outcomes.0[0].registered.push("TgSix.forged".to_string());
    fact.outcome = encode(&outcomes).expect("encode");
    facts.store().put(&key, &encode(&fact).expect("encode")).expect("put");

    let report = verify_store(facts.store());
    assert_eq!((report.reproduced, report.quarantined.len()), (0, 1), "{report:?}");
    assert!(facts.store().keys().is_empty());

    // Stored again by a real check, it verifies.
    session(&facts).check_all(&BATCH);
    let report = verify_store(facts.store());
    assert_eq!((report.reproduced, report.quarantined.len()), (1, 0), "{report:?}");

    // The audit catches the same forgery in a build.
    let StoreRead::Present { bytes, .. } = facts.store().get(&key) else { panic!("stored") };
    let mut fact = StoredFact::decode(&bytes).expect("decodes");
    fact.outcome = encode(&outcomes).expect("encode");
    facts.store().put(&key, &encode(&fact).expect("encode")).expect("put");
    let auditing = context(&home, "one", true);
    let mut audited = session(&auditing);
    let batch = audited.check_all(&BATCH);
    assert!(!batch.outcomes[0].registered.contains(&"TgSix.forged".to_string()));
    assert_eq!(auditing.store().keys().len(), 1, "re-stored after the quarantine");
    let _ = std::fs::remove_dir_all(home);
}

/// An unkeyed change (here, a direct environment write) ends the session's
/// use of facts: nothing is read or written after it.
#[test]
fn an_unkeyed_change_ends_the_use_of_facts() {
    let home = home("unkeyed");
    let facts = context(&home, "one", false);
    session(&facts).check_all(&BATCH);
    let mut poisoned = session(&facts);
    poisoned.keyed.env_mut_for_tests();
    poisoned.check_all(&BATCH);
    assert_eq!(poisoned.keyed.elaborations, 1, "no fact is read");
    assert_eq!(facts.written(), 1, "and none is written");
    let _ = std::fs::remove_dir_all(home);
}

#[test]
fn spelled_admitted_names_are_whole_identifiers() {
    let names = spelled_admitted_names(
        "x trust_import_a + my_trust_import_b (trust_import_c.d) -- trust_import_z\n\
         trust_type_Pair.fields.lo TrustOdt.k1_2.toTag NotTrustOdt.k trust_checked_toInt64 \
         \"trust_type_in_a_string\"",
    );
    assert_eq!(
        names.into_iter().collect::<Vec<_>>(),
        [
            "TrustOdt.k1_2.toTag",
            "trust_checked_toInt64",
            "trust_import_a",
            "trust_import_c",
            "trust_import_c.d",
            "trust_type_Pair.fields.lo",
        ]
    );
}

#[test]
fn a_judgment_checked_without_registering_is_seen() {
    assert!(checks_without_registering("example : 1 = 1 := rfl"));
    assert!(checks_without_registering("#guard 1 == 1"));
    assert!(checks_without_registering("def a : Nat := 1\n#eval a"));
    assert!(!checks_without_registering("theorem t : 1 = 1 := rfl -- example #guard"));
    assert!(!checks_without_registering("def s : String := \"#eval example\""));
}

/// TG6 review: an `example` is checked and thrown away, so no registered
/// declaration records what it read. This one reads the admitted tag table
/// without spelling an admitted name; changing the tag misses and rejects,
/// where a walk of registered constants alone would replay the acceptance.
/// The cost, pinned: an unrelated admission change misses it too. NEGATIVE
/// CONTROL: the same judgment as a `theorem` keys on what it reaches, and
/// hits on the unrelated change.
#[test]
fn an_example_depends_on_the_whole_environment() {
    const EXAMPLE: &str = "example : TgElevenState.toTag TgElevenState.Ready = 42 := rfl\n";
    const THEOREM: &str =
        "theorem tgsix_ready_tag : TgElevenState.toTag TgElevenState.Ready = 42 := rfl\n";
    let home = home("example");
    let facts = context(&home, "one", false);
    for island in [EXAMPLE, THEOREM] {
        let mut first = session(&facts);
        admit_states(&mut first, 42, 1);
        let outcome = first.check(island);
        assert!(!outcome.is_rejected(), "{island}: {:?}", outcome.errors);
    }
    assert_eq!(facts.written(), 2);

    let mut mutant = session(&facts);
    admit_states(&mut mutant, 43, 1);
    assert!(mutant.check(EXAMPLE).is_rejected(), "`Ready`'s tag is 43 now");
    assert_eq!(mutant.keyed.elaborations, 1);

    let mut unrelated = session(&facts);
    admit_states(&mut unrelated, 42, 2);
    assert!(!unrelated.check(EXAMPLE).is_rejected());
    assert_eq!(unrelated.keyed.elaborations, 1, "an example misses on any change");

    let mut theorem = session(&facts);
    admit_states(&mut theorem, 42, 2);
    assert!(!theorem.check(THEOREM).is_rejected());
    assert_eq!(theorem.keyed.elaborations, 0, "a theorem keys on what it reaches");
    let _ = std::fs::remove_dir_all(home);
}

/// Admit a two-field structure the way TG11 admits a Rust struct face
/// (`crate::odt`): an inductive whose constructor takes two `Nat`s, and a
/// field table naming them. Only the table says which field is which.
fn admit_pair(session: &mut CleanIslandSession, fields: [&str; 2]) {
    use clean_kernel::inductive::{Constructor, InductiveDecl, InductiveType};
    let nat = || Expr::const_(Name::from_string("Nat"), vec![]);
    let pair = Name::from_string("TgSixPair");
    session.keyed.admit(|env| {
        env.add_inductive(InductiveDecl {
            level_params: vec![],
            num_params: 0,
            types: vec![InductiveType {
                name: pair.clone(),
                type_: Expr::type_(),
                constructors: vec![Constructor {
                    name: Name::from_string("TgSixPair.mk"),
                    type_: Expr::arrow(
                        nat(),
                        Expr::arrow(nat(), Expr::const_(pair.clone(), vec![])),
                    ),
                }],
            }],
        })
        .expect("the admitted structure checks");
        env.register_structure_fields(pair.clone(), fields.map(Name::from_string).to_vec())
            .expect("the field table registers");
    });
}

/// TG6 review: swapping two same-typed fields of an admitted struct changes
/// only its field table, which no kernel record carries. The theorem reads
/// `.width` through that table; the swap misses and the theorem, now false,
/// is rejected. NEGATIVE CONTROL: the same table hits.
#[test]
fn a_swapped_field_table_misses_and_falsifies_the_theorem() {
    const READS_WIDTH: &str = "theorem tgsix_width : (TgSixPair.mk 3 4).width = 3 := rfl\n";
    let home = home("field-table");
    let facts = context(&home, "one", false);
    let mut first = session(&facts);
    admit_pair(&mut first, ["width", "height"]);
    let outcome = first.check(READS_WIDTH);
    assert!(!outcome.is_rejected(), "{:?}", outcome.errors);

    let mut same = session(&facts);
    admit_pair(&mut same, ["width", "height"]);
    assert!(!same.check(READS_WIDTH).is_rejected());
    assert_eq!(same.keyed.elaborations, 0);

    let mut swapped = session(&facts);
    admit_pair(&mut swapped, ["height", "width"]);
    assert!(swapped.check(READS_WIDTH).is_rejected(), "`width` is the second field now");
    assert_eq!(swapped.keyed.elaborations, 1);
    let _ = std::fs::remove_dir_all(home);
}

/// TG6 review: a rebuild that finds a hit this session returned disagreeing
/// with real elaboration fails the operation that triggered it and taints
/// the session; it does not only quarantine. The hit here returns a forged
/// outcome (the audit is off). NEGATIVE CONTROL: the honest fact rebuilds and
/// the next island is accepted.
#[test]
fn a_rebuild_that_disproves_a_hit_fails_the_operation() {
    let home = home("disproved");
    let facts = context(&home, "one", false);
    session(&facts).check_all(&BATCH);
    let key = facts.store().keys()[0];

    let mut honest = session(&facts);
    honest.check_all(&BATCH);
    let outcome = honest.check("theorem tgsix_opened : one = 1 := rfl\n");
    assert!(!outcome.is_rejected(), "{:?}", outcome.errors);
    assert!(!honest.is_tainted());

    let StoreRead::Present { bytes, .. } = facts.store().get(&key) else { panic!("stored") };
    let mut fact = StoredFact::decode(&bytes).expect("decodes");
    let mut outcomes: (
        Vec<super::super::CleanIslandOutcome>,
        Vec<crate::clean_island_batch::CleanIslandCycle>,
    ) = crate::clean_fact::decode(&fact.outcome).expect("the stored outcome decodes");
    outcomes.0[0].registered.push("TgSix.forged".to_string());
    fact.outcome = encode(&outcomes).expect("encode");
    facts.store().put(&key, &encode(&fact).expect("encode")).expect("put");

    let mut forged = session(&facts);
    let batch = forged.check_all(&BATCH);
    assert!(batch.outcomes[0].registered.contains(&"TgSix.forged".to_string()), "the hit");
    let outcome = forged.check("theorem tgsix_opened_again : one = 1 := rfl\n");
    assert!(outcome.is_rejected(), "the rebuild disproved the hit");
    assert!(
        outcome.errors.iter().any(|e| e.message.contains("disagrees with real elaboration")),
        "{:?}",
        outcome.errors
    );
    assert!(forged.is_tainted());
    assert!(!matches!(facts.store().get(&key), StoreRead::Present { .. }), "quarantined");
    let _ = std::fs::remove_dir_all(home);
}

/// An admission window that changes session state rather than per-name
/// records ends the session's use of facts: no dependency would see it.
#[test]
fn an_admission_that_changes_session_state_ends_the_use_of_facts() {
    let home = home("session-admission");
    let facts = context(&home, "one", false);
    let mut first = session(&facts);
    first.keyed.admit(|env| env.set_option("tgSix.option".to_string(), Some("1".to_string())));
    first.check(USES_NOTHING);
    assert_eq!(facts.written(), 0, "no fact after an unkeyable window");
    // NEGATIVE CONTROL: a per-name admission keeps facts on.
    let mut second = session(&facts);
    admit_imports(&mut second, 5, 6);
    second.check(USES_NOTHING);
    assert_eq!(facts.written(), 1);
    let _ = std::fs::remove_dir_all(home);
}

const USES_NOTHING: &str = "theorem tgsix_plain : 2 = 2 := rfl\n";

/// Before facts are enabled, an admission is an unkeyed change: enabling
/// facts afterwards refuses, since the environment is no longer the prelude.
#[test]
fn an_admission_before_facts_are_enabled_keeps_them_off() {
    let home = home("early-admission");
    let facts = context(&home, "one", false);
    let mut early = CleanIslandSession::new();
    admit_imports(&mut early, 5, 6);
    early.enable_facts(Arc::clone(&facts));
    early.check(USES_F);
    assert_eq!(facts.written(), 0);
    let _ = std::fs::remove_dir_all(home);
}

/// TG4's producer (`CheckedIslandEnvironment::check`) prepares the batch and
/// reports it once in a binding-only preview fork; the HIR owner later
/// reports the original. That is three facts: the declarations (`Prepare`)
/// and two `Report`s, keyed after the same `Prepare` under their own
/// settings. A second compile imports all three and elaborates nothing.
#[test]
fn the_tg4_producer_and_its_hir_report_are_facts() {
    use crate::clean_island_environment::CheckedIslandEnvironment;
    let home = home("tg4");
    let facts = context(&home, "one", false);
    let sources: Vec<String> = BATCH.iter().map(|source| (*source).to_string()).collect();
    let compile = || {
        let (mut checked, preview, batch) =
            CheckedIslandEnvironment::check(&sources, &[], true, Some(Arc::clone(&facts)))
                .expect("no callees to refuse");
        assert!(!batch.is_rejected(), "{:?}", batch.outcomes);
        let prepared = checked.take_for_reporting(&sources, &[]).expect("an accepted batch");
        let (session, report) = prepared.finish();
        assert!(!report.is_rejected(), "{:?}", report.outcomes);
        (preview.keyed.elaborations, session.keyed.elaborations)
    };
    let (preview, hir) = compile();
    assert!(preview > 0 && hir > 0);
    assert_eq!(facts.written(), 3, "prepare, the preview's report, the HIR report");
    assert_eq!(compile(), (0, 0), "the second compile elaborates nothing");
    assert_eq!(facts.written(), 3);
    let _ = std::fs::remove_dir_all(home);
}

/// A hit carries the reference acceptance, rather than rechecking an unchanged
/// proof. An unrelated admission with no full-check provenance invalidates
/// base eligibility even though it is outside that proof's dependency closure.
#[test]
fn reference_acceptance_is_reused_but_an_ineligible_base_cannot_hit() {
    let home = home("reference-fence");
    let facts = context(&home, "reference", false);
    const SOURCE: &str = "theorem tg8_fact : (1 : Nat) = 1 := rfl\n";
    let mut first = session(&facts);
    let before = crate::reference_mint::island_rechecks();
    let checked = first.check(SOURCE);
    assert!(!checked.is_rejected(), "{checked:?}");
    assert!(crate::reference_mint::island_rechecks() > before);
    let mut second = session(&facts);
    let before = crate::reference_mint::island_rechecks();
    assert!(!second.check(SOURCE).is_rejected());
    assert_eq!(second.keyed.elaborations, 0);
    assert_eq!(
        crate::reference_mint::island_rechecks(),
        before,
        "an ordinary fact hit performs zero reference proof checks"
    );
    let mut mutant = session(&facts);
    mutant.keyed.admit(|env| {
        env.add_decl_structural(Declaration::Definition {
            name: Name::from_string("tg8_unchecked_fact_base"),
            level_params: vec![],
            type_: Expr::const_str("Nat"),
            value: Expr::nat_lit(0),
            is_reducible: false,
        })
        .expect("test-only structural record");
    });
    let refused = mutant.check(SOURCE);
    assert!(refused.is_rejected(), "a cached green cannot survive an ineligible reference base");
    assert_eq!(mutant.keyed.elaborations, 1);
    assert!(refused.errors.iter().any(|error| error.message.contains("reference")), "{refused:?}");
    let _ = std::fs::remove_dir_all(home);
}

/// Exercise the single-island, whole-batch and actual prepare/report paths.
/// The latter is the ordinary compiler path; none may retain a permission
/// that disappeared or became invalid, and unchanged permissions must hit.
fn bounded_permission_changes(source: &str, permission: &str, tag: &str) {
    for route in 0..3 {
        for invalid in [None, Some("")] {
            let home = home(&format!("tg9-{tag}-{route}-{}", invalid.is_some()));
            let facts = context(&home, "one", false);
            let new_session = |unrelated_body| {
                let mut session = session(&facts);
                session.enable_model_checks();
                admit_imports(&mut session, 5, unrelated_body);
                session
            };
            let admit = |session: &mut CleanIslandSession, reason: Option<&str>| {
                if let Some(reason) = reason {
                    session.keyed.admit(|env| {
                        env.add_decl(Declaration::Definition {
                            name: Name::from_string(permission),
                            level_params: vec![],
                            type_: Expr::const_str("String"),
                            value: Expr::str_lit(reason),
                            is_reducible: false,
                        })
                        .expect("typed bounded metadata");
                    });
                }
            };
            let run = |mut session: CleanIslandSession| {
                if route == 2 {
                    let (session, batch) = session.prepare_all(&[source]).finish();
                    let errors: Vec<_> = batch
                        .outcomes
                        .iter()
                        .flat_map(|o| &o.errors)
                        .map(|e| e.message.clone())
                        .collect();
                    (session, batch.is_rejected(), errors)
                } else {
                    let (refused, errors) = if route == 0 {
                        let outcome = session.check(source);
                        (
                            outcome.is_rejected(),
                            outcome.errors.into_iter().map(|e| e.message).collect::<Vec<_>>(),
                        )
                    } else {
                        let batch = session.check_all(&[source]);
                        (
                            batch.is_rejected(),
                            batch
                                .outcomes
                                .into_iter()
                                .flat_map(|o| o.errors)
                                .map(|e| e.message)
                                .collect::<Vec<_>>(),
                        )
                    };
                    (session, refused, errors)
                }
            };
            let mut first = new_session(1);
            admit(&mut first, Some("Diagnostic scope; exhaustive certification remains open"));
            let (_, refused, _) = run(first);
            assert!(!refused, "valid permission, {tag}, route {route}");
            assert_eq!(facts.written(), if route == 2 { 2 } else { 1 });

            let mut same = new_session(1);
            admit(&mut same, Some("Diagnostic scope; exhaustive certification remains open"));
            let (same, refused, _) = run(same);
            assert!(!refused);
            assert_eq!(same.keyed.elaborations, 0, "unchanged permission reuses its facts");

            let mut unrelated = new_session(2);
            admit(&mut unrelated, Some("Diagnostic scope; exhaustive certification remains open"));
            let (unrelated, refused, _) = run(unrelated);
            assert!(!refused);
            assert_eq!(
                unrelated.keyed.elaborations, 0,
                "unrelated bodies must not invalidate facts"
            );

            let mut fresh = CleanIslandSession::new();
            fresh.enable_model_checks();
            admit_imports(&mut fresh, 5, 1);
            admit(&mut fresh, invalid);
            assert!(run(fresh).1, "fresh missing/invalid permission control refuses");
            let mut changed = new_session(1);
            admit(&mut changed, invalid);
            let (changed, refused, errors) = run(changed);
            assert!(refused, "a stored bounded acceptance must not outlive its permission");
            let expected = if invalid.is_some() {
                "invalid bounded declaration"
            } else {
                "explicitly declare"
            };
            assert!(
                errors.iter().any(|e| e.contains(expected)),
                "{tag} route {route}: expected actual metadata refusal, got {errors:?}"
            );
            assert!(
                changed.keyed.elaborations > 0,
                "changed metadata must miss: {tag} route {route}, {errors:?}"
            );
            let _ = std::fs::remove_dir_all(home);
        }
    }
}

#[test]
fn bounded_model_fact_misses_when_external_permission_disappears() {
    let source = format!(
        "import Trust.FiniteModel\n{}\ndef Example.Lockstep.stateBudget : Nat := 2\n",
        include_str!("../../../trust-spec-temporal/examples/clean_scalar_lockstep.lean")
    );
    bounded_permission_changes(&source, "Example.Lockstep.bounded", "bounded-model");
}

#[test]
fn bounded_progress_fact_misses_when_external_permission_changes() {
    let source = format!(
        "import Trust.Protocol\n{}\nopen Trust.Protocol\n\
         def HarnessPolicy.CatchesUp : Trust.Temporal.FiniteModel.ScalarProgress :=\n  \
         progress HarnessPolicy.OneWriter\n    \
         (v \"committed\" ≐ n 0 ⋎ v \"in_force\" ≐ v \"disk\")\n    \
         [\"Poll\", \"Deliver\", \"Forget\"] []\n\
         def HarnessPolicy.CatchesUp.stateBudget : Nat := 0\n",
        include_str!("../../../trust-spec-temporal/examples/harness_policy_one_writer.lean")
    );
    bounded_permission_changes(&source, "HarnessPolicy.CatchesUp.bounded", "bounded-progress");
}
