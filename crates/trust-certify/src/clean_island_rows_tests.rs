// Island rows over the REAL Clean kernel, in process: each island text is
// checked by `CleanIslandSession` exactly as the compiler's seams check it
// (`check_all` for the pre-walk batch, `check_import_islands` for the deferred
// suffix), and the rows are read from those outcomes. No row is proved on any
// condition the module docs do not state.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::clean_island_rows::{CleanIslandPhase, CleanIslandRowVerdict as V};
use trust_types::lean_declaration_identity::{lean_command_texts, lean_declarations};

use super::*;
use crate::clean_island::{CleanIslandDiagnostic, CleanIslandSession};
use crate::clean_island_batch::CleanIslandBatch;

const LOCKSTEP: &str =
    include_str!("../../trust-spec-temporal/examples/clean_scalar_lockstep.lean");

const FIRST: &str = "namespace Demo\n\
                     theorem one_pos : 0 < 1 := by decide\n\
                     def double (n : Nat) : Nat := n + n\n\
                     end Demo\n";
const SECOND: &str = "open Demo\n\
                      theorem double_two : Demo.double 2 = 4 := rfl\n\
                      example : (1 : Nat) = 1 := rfl\n\
                      example : (1 : Nat) = 1 := rfl\n";

/// The facts of a verified crate whose session checked models and read
/// bindings, untainted, with a whole inventory: what the MIR seam states.
fn verified() -> CrateIslandFacts {
    CrateIslandFacts {
        verified: true,
        models_and_bindings_read: true,
        ..CrateIslandFacts::default()
    }
}

/// The rows of a pre-walk batch over `sources`.
fn rows_of(sources: &[&str], batch: &CleanIslandBatch, facts: &CrateIslandFacts) -> IslandRows {
    let accepted = !batch.is_rejected();
    let inputs: Vec<IslandRowInput<'_>> = sources
        .iter()
        .zip(&batch.outcomes)
        .map(|(text, outcome)| IslandRowInput {
            text,
            outcome,
            accepted,
            bindings_checked: &[],
            seals_checked: &[],
        })
        .collect();
    clean_island_rows("demo", &inputs, facts)
}

fn checked(sources: &[&str]) -> (CleanIslandSession, CleanIslandBatch) {
    let mut session = CleanIslandSession::new();
    let batch = session.check_all(sources);
    (session, batch)
}

/// `(key, verdict)` of each row.
fn verdicts(rows: &IslandRows) -> Vec<(String, V)> {
    rows.rows.iter().map(|row| (row.key.clone(), row.verdict)).collect()
}

fn verdict_of(rows: &IslandRows, name: &str) -> V {
    let found: Vec<_> =
        rows.rows.iter().filter(|row| row.key.starts_with(&format!("demo::{name}#"))).collect();
    assert_eq!(found.len(), 1, "{name}: {rows:#?}");
    found[0].verdict
}

fn none_proved(rows: &IslandRows) -> bool {
    !rows.rows.is_empty() && rows.rows.iter().all(|row| row.verdict != V::Proved)
}

#[test]
fn an_accepted_pair_of_islands_proves_every_declaration_under_the_lean_lanes_keys() {
    let sources = [FIRST, SECOND];
    let (session, batch) = checked(&sources);
    assert!(!batch.is_rejected(), "{batch:?}");
    assert!(!session.is_tainted());
    let rows = rows_of(&sources, &batch, &verified());
    assert!(rows.complete(), "{:?}", rows.problems);
    let kinds: Vec<&str> = rows.rows.iter().map(|row| row.kind.as_str()).collect();
    assert_eq!(kinds, ["lean:theorem", "lean:def", "lean:theorem", "lean:example", "lean:example"]);
    assert!(rows.rows.iter().all(|row| row.verdict == V::Proved), "{rows:#?}");
    // The keys are the `.lean` lane's: the same commands, named by the same
    // call over the crate's islands in order, with the crate in front.
    let mut commands = Vec::new();
    for (text, outcome) in sources.iter().zip(&batch.outcomes) {
        let listed = outcome.declarations.as_deref().unwrap();
        let spans: Vec<_> = listed.iter().map(|d| (d.start, d.end)).collect();
        for (declaration, slice) in listed.iter().zip(lean_command_texts(text, &spans)) {
            commands.push((declaration.name.as_deref(), slice.unwrap()));
        }
    }
    let lean: Vec<String> = lean_declarations(commands)
        .into_iter()
        .flatten()
        .map(|declaration| format!("demo::{}", declaration.key()))
        .collect();
    let keys: Vec<String> = rows.rows.iter().map(|row| row.key.clone()).collect();
    assert_eq!(keys, lean);
    assert!(keys[0].starts_with("demo::Demo.one_pos#"), "{keys:?}");
    assert!(keys[1].starts_with("demo::Demo.double#"), "{keys:?}");
    // Two identical `example`s share a def path, told apart by their ids, and
    // so carry no one source digest.
    assert_ne!(keys[3], keys[4]);
    assert!(rows.rows[3].source.is_none() && rows.rows[4].source.is_none());
    assert!(rows.rows[0].source.as_deref().is_some_and(|s| s.len() == 64));
    // The transport is in key order and validates.
    let message =
        rows.transport("demo", "demo", "s", true, CleanIslandPhase::Verified, 2, |i, at| {
            (
                "src/lib.rs".to_string(),
                u32::try_from(i + 1).unwrap(),
                u32::try_from(at + 1).unwrap(),
            )
        });
    assert_eq!(message.validate(), Ok(()));
    assert_eq!(message.rows.len(), 5);
    assert!(message.rows.windows(2).all(|pair| pair[0].key < pair[1].key));
}

#[test]
fn a_comment_a_blank_line_or_a_reformat_moves_no_key() {
    let keys = |sources: &[&str]| -> Vec<String> {
        let (_, batch) = checked(sources);
        assert!(!batch.is_rejected(), "{batch:?}");
        rows_of(sources, &batch, &verified()).rows.into_iter().map(|row| row.key).collect()
    };
    let before = keys(&[FIRST, SECOND]);
    let commented = FIRST
        .replace("theorem one_pos", "-- one is positive\n\n/- a block comment -/\ntheorem one_pos");
    let reformatted = SECOND.replace("Demo.double 2 = 4", "Demo.double   2\n    =   4");
    // A Rust line above the island is outside its text altogether; an empty
    // island before it shifts nothing either.
    assert_eq!(keys(&[&commented, &reformatted]), before);
    assert_eq!(keys(&["", &commented, &reformatted]), before);
    // A statement edit moves that key, and only that one.
    let edited = keys(&[&FIRST.replace("0 < 1", "0 < 2"), SECOND]);
    assert_ne!(edited[0], before[0]);
    assert_eq!(edited[1..], before[1..]);
}

#[test]
fn a_sorry_fails_its_own_row_and_proves_nothing_else() {
    let broken = FIRST.replace("by decide", "by sorry");
    let sources = [broken.as_str(), SECOND];
    let (session, batch) = checked(&sources);
    assert!(batch.is_rejected());
    assert!(session.is_tainted());
    // Read as untainted first: the batch's rejection alone proves nothing.
    let rows = rows_of(&sources, &batch, &verified());
    assert!(rows.complete());
    assert!(none_proved(&rows), "{rows:#?}");
    let facts = CrateIslandFacts { tainted: session.is_tainted(), ..verified() };
    let rows = rows_of(&sources, &batch, &facts);
    assert_eq!(verdict_of(&rows, "Demo.one_pos"), V::ProofRefused, "{rows:#?}");
    assert!(none_proved(&rows), "{rows:#?}");
    // Its siblings were never accepted: nothing refuted them, so they are not
    // dispatched, never failed.
    assert_eq!(verdict_of(&rows, "Demo.double"), V::NotDispatched);
    assert_eq!(verdict_of(&rows, "double_two"), V::NotDispatched);
    // A tainted session is named, so the rows are not complete.
    assert!(!rows.complete());
}

#[test]
fn an_error_in_a_sibling_island_or_outside_every_declaration_proves_nothing() {
    for bad in [
        "theorem wrong : (1 : Nat) = 2 := rfl\n",
        "#check no_such_constant\n",
        "#reduce no_such_constant\n",
    ] {
        let sources = [FIRST, SECOND, bad];
        let (_, batch) = checked(&sources);
        assert!(batch.is_rejected(), "{bad}");
        // Even read as untainted and complete, a rejected batch proves nothing.
        let rows = rows_of(&sources, &batch, &verified());
        assert!(none_proved(&rows), "{bad}: {rows:#?}");
        assert_eq!(verdict_of(&rows, "Demo.one_pos"), V::NotDispatched, "{bad}");
    }
}

#[test]
fn a_stand_in_import_is_unsupported_everywhere() {
    let sources = ["import Lean\ntheorem lean_side : (1 : Nat) = 1 := rfl\n", FIRST];
    let (_, batch) = checked(&sources);
    assert!(!batch.is_rejected(), "{batch:?}");
    assert!(!batch.outcomes[0].standin_imports.is_empty(), "{batch:?}");
    let rows = rows_of(&sources, &batch, &verified());
    assert!(rows.rows.iter().all(|row| row.verdict == V::Unsupported), "{rows:#?}");
}

#[test]
fn an_incomplete_inventory_or_an_unverified_crate_proves_nothing() {
    let sources = [FIRST, SECOND];
    let (_, batch) = checked(&sources);
    assert!(!batch.is_rejected());
    let incomplete = CrateIslandFacts {
        inventory_problems: vec!["island 3's text could not be recovered".to_string()],
        ..verified()
    };
    let rows = rows_of(&sources, &batch, &incomplete);
    assert!(!rows.complete());
    assert!(rows.rows.iter().all(|row| row.verdict == V::NotDispatched), "{rows:#?}");
    let unverified = rows_of(&sources, &batch, &CrateIslandFacts::default());
    assert!(unverified.complete());
    assert!(unverified.rows.iter().all(|row| row.verdict == V::NotDispatched), "{unverified:#?}");
    let tainted = CrateIslandFacts { tainted: true, ..verified() };
    let rows = rows_of(&sources, &batch, &tainted);
    assert!(!rows.complete());
    assert!(none_proved(&rows));
    // The transport of an unverified crate's rows validates on the
    // front-end-error path; an incomplete one never carries a proved row.
    let message = unverified.transport(
        "demo",
        "demo",
        "s",
        true,
        CleanIslandPhase::FrontEndError,
        2,
        |_, _| ("src/lib.rs".to_string(), 1, 1),
    );
    assert_eq!(message.validate(), Ok(()));
}

#[test]
fn an_island_that_does_not_parse_makes_the_rows_incomplete() {
    let sources = [FIRST, "theorem := := (\n"];
    let (_, batch) = checked(&sources);
    assert!(batch.is_rejected());
    assert!(batch.outcomes[1].declarations.is_none(), "{batch:?}");
    let rows = rows_of(&sources, &batch, &verified());
    assert!(!rows.complete());
    assert!(
        rows.problems.iter().any(|problem| problem.contains("island 2 was not enumerated")),
        "{:?}",
        rows.problems
    );
    assert!(none_proved(&rows), "{rows:#?}");
}

#[test]
fn an_unsafe_model_fails_its_declaration() {
    let safe = format!("import Trust.FiniteModel\n{LOCKSTEP}");
    let unsafe_ = safe.replace("\"Buggy\" 0", "\"Buggy\" 1");
    assert_ne!(safe, unsafe_);
    let mut session = CleanIslandSession::new();
    session.enable_model_checks();
    let batch = session.check_all(&[&safe]);
    assert!(!batch.is_rejected(), "{batch:?}");
    let rows = rows_of(&[&safe], &batch, &verified());
    assert!(rows.complete(), "{:?}", rows.problems);
    assert_eq!(verdict_of(&rows, "Example.Lockstep"), V::Proved, "{rows:#?}");

    let mut session = CleanIslandSession::new();
    session.enable_model_checks();
    let batch = session.check_all(&[&unsafe_]);
    assert!(batch.is_rejected());
    let rows = rows_of(&[&unsafe_], &batch, &verified());
    assert_eq!(verdict_of(&rows, "Example.Lockstep"), V::ProofRefused, "{rows:#?}");
    assert_eq!(verdict_of(&rows, "Example.X"), V::NotDispatched);
    assert!(none_proved(&rows));

    // A model whose check decided nothing, and that declares no `bounded`
    // reason, is refused: an unbounded incomplete model is an error at the
    // model, so it fails and its siblings are not dispatched.
    let mut session = CleanIslandSession::new();
    session.enable_model_checks();
    session.set_model_state_budget(1);
    let batch = session.check_all(&[&safe]);
    assert!(batch.is_rejected(), "{batch:?}");
    assert!(
        batch.outcomes[0]
            .model_checks
            .iter()
            .all(|check| matches!(check.verdict, CleanIslandModelVerdict::Undecided { .. })),
        "{batch:?}"
    );
    let rows = rows_of(&[&safe], &batch, &verified());
    assert_eq!(verdict_of(&rows, "Example.Lockstep"), V::ProofRefused, "{rows:#?}");
    assert_eq!(verdict_of(&rows, "Example.X"), V::NotDispatched, "{rows:#?}");
}

#[test]
fn a_binding_the_compiler_did_not_check_is_not_proved() {
    let source = "import Trust.Protocol\nnamespace HarnessPolicy\nopen Trust.Protocol\n\
                  def arm : String := \"HarnessPolicyObserved\"\n\
                  def policy : Trust.Protocol.Binding :=\n  \
                  binds \"config.harness\" [arm, \"Wake::Reset\"] [\"App::carry\"]\n\
                  end HarnessPolicy\n";
    let mut session = CleanIslandSession::new();
    session.enable_model_checks();
    let batch = session.check_all(&[source]);
    assert!(!batch.is_rejected(), "{batch:?}");
    assert_eq!(batch.outcomes[0].bindings.len(), 1);
    let rows_given = |checked: &[bool]| {
        let input = IslandRowInput {
            text: source,
            outcome: &batch.outcomes[0],
            accepted: true,
            bindings_checked: checked,
            seals_checked: &[],
        };
        clean_island_rows("demo", &[input], &verified())
    };
    let unchecked = rows_given(&[]);
    assert_eq!(verdict_of(&unchecked, "HarnessPolicy.policy"), V::NotDispatched, "{unchecked:#?}");
    // The binding is the declaration's own: its sibling is unaffected.
    assert_eq!(verdict_of(&unchecked, "HarnessPolicy.arm"), V::Proved);
    let failed_check = rows_given(&[false]);
    assert_eq!(verdict_of(&failed_check, "HarnessPolicy.policy"), V::NotDispatched);
    let held = rows_given(&[true]);
    assert_eq!(verdict_of(&held, "HarnessPolicy.policy"), V::Proved);
}

#[test]
fn an_error_added_after_cleans_flag_still_fails_its_declaration() {
    // Errors added to the outcome after Clean set each declaration's
    // `refused` flag (a failing model check, placed at its model's
    // declaration) are missed by the flag; the rows read the final errors.
    // Plant one at a declaration's keyword in an otherwise accepted batch. A
    // refused served import lies before every region instead
    // (`an_error_before_every_region_refuses_every_declaration_of_its_island`).
    let sources = [FIRST, SECOND];
    let (_, mut batch) = checked(&sources);
    let double = batch.outcomes[0].declarations.as_ref().unwrap()[1].clone();
    assert_eq!(double.name.as_deref(), Some("Demo.double"));
    assert!(!double.refused);
    batch.outcomes[0].errors.push(CleanIslandDiagnostic {
        start: double.start,
        end: double.end,
        message: "the model reaches a state its invariant does not hold in".to_string(),
    });
    let rows = rows_of(&sources, &batch, &verified());
    assert_eq!(verdict_of(&rows, "Demo.double"), V::ProofRefused, "{rows:#?}");
    assert!(none_proved(&rows), "{rows:#?}");
    // A whole-batch refusal placed at the first byte is no declaration's own.
    let (_, mut batch) = checked(&sources);
    batch.outcomes[0].errors.push(CleanIslandDiagnostic {
        start: 0,
        end: 0,
        message: format!(
            "{} the batch was not committed",
            crate::clean_island_batch::UNRECOVERABLE_BATCH_PREFIX
        ),
    });
    let rows = rows_of(&sources, &batch, &verified());
    assert_eq!(verdict_of(&rows, "Demo.one_pos"), V::NotDispatched, "{rows:#?}");
    assert!(none_proved(&rows));
}

/// The rows of a pre-walk batch followed by a deferred suffix, as the
/// compiler orders them.
fn rows_with_suffix(
    prewalk: &[&str],
    batch: &CleanIslandBatch,
    suffix: &[&str],
    import: &crate::clean_island::CleanImportBatch,
    facts: &CrateIslandFacts,
) -> IslandRows {
    let mut inputs: Vec<IslandRowInput<'_>> = prewalk
        .iter()
        .zip(&batch.outcomes)
        .map(|(text, outcome)| IslandRowInput {
            text,
            outcome,
            accepted: !batch.is_rejected(),
            bindings_checked: &[],
            seals_checked: &[],
        })
        .collect();
    inputs.extend(suffix.iter().zip(&import.outcomes).enumerate().map(|(i, (text, outcome))| {
        IslandRowInput {
            text,
            outcome,
            accepted: import.committed && !import.refused_islands.contains(&i),
            bindings_checked: &[],
            seals_checked: &[],
        }
    }));
    clean_island_rows("demo", &inputs, facts)
}

#[test]
fn deferred_survivors_are_proved_only_when_their_batch_committed() {
    let prewalk = [FIRST];
    let suffix =
        ["theorem middle : (2 : Nat) = 2 := rfl\n", "theorem last : (3 : Nat) = 3 := rfl\n"];
    let mut session = CleanIslandSession::new();
    let batch = session.check_all(&prewalk);
    assert!(!batch.is_rejected());
    let import = session.check_import_islands(&suffix);
    assert!(import.committed, "{import:?}");
    assert!(!session.is_tainted());
    let rows = rows_with_suffix(&prewalk, &batch, &suffix, &import, &verified());
    assert!(rows.complete(), "{:?}", rows.problems);
    assert!(rows.rows.iter().all(|row| row.verdict == V::Proved), "{rows:#?}");
    assert_eq!(rows.rows.len(), 4);

    // The same outcomes, uncommitted: no error on a survivor is not acceptance.
    let mut uncommitted = import.clone();
    uncommitted.committed = false;
    let rows = rows_with_suffix(&prewalk, &batch, &suffix, &uncommitted, &verified());
    assert_eq!(verdict_of(&rows, "middle"), V::NotDispatched, "{rows:#?}");
    assert_eq!(verdict_of(&rows, "last"), V::NotDispatched);
    assert_eq!(verdict_of(&rows, "Demo.one_pos"), V::Proved);
}

#[test]
fn a_deferred_unit_refused_before_elaboration_makes_the_rows_incomplete() {
    let prewalk = [FIRST];
    let missing = "theorem bad : trust_import_missing = trust_import_missing := rfl\n";
    // Alone, every unit refused: nothing committed.
    let mut session = CleanIslandSession::new();
    let batch = session.check_all(&prewalk);
    let import = session.check_import_islands(&[missing]);
    assert!(!import.committed, "{import:?}");
    assert!(import.outcomes[0].declarations.is_none());
    let rows = rows_with_suffix(&prewalk, &batch, &[missing], &import, &verified());
    assert!(rows.problems.iter().any(|problem| problem.contains("island 2 was not enumerated")));
    assert!(none_proved(&rows), "{rows:#?}");

    // Beside a survivor: the survivor's batch committed, but the refused unit
    // was never enumerated, so the rows are incomplete and none is proved.
    let suffix = [missing, "theorem last : (3 : Nat) = 3 := rfl\n"];
    let mut session = CleanIslandSession::new();
    let batch = session.check_all(&prewalk);
    let import = session.check_import_islands(&suffix);
    assert!(import.committed, "{import:?}");
    assert_eq!(import.refused_islands, [0]);
    let rows = rows_with_suffix(&prewalk, &batch, &suffix, &import, &verified());
    assert!(!rows.complete());
    assert!(none_proved(&rows), "{rows:#?}");
}

#[test]
fn a_taint_after_an_accepted_prewalk_batch_proves_nothing() {
    let prewalk = [FIRST, SECOND];
    let mut session = CleanIslandSession::new();
    let batch = session.check_all(&prewalk);
    assert!(!batch.is_rejected());
    assert!(!session.is_tainted());
    // A deferred unit that declares into the reserved import namespace is a
    // policy refusal that keeps the session tainted.
    let suffix = ["def trust_import_lookalike__spec (a : UInt64) : UInt64 := a\n"];
    let import = session.check_import_islands(&suffix);
    assert!(session.is_tainted(), "{import:?}");
    let facts = CrateIslandFacts { tainted: session.is_tainted(), ..verified() };
    let rows = rows_with_suffix(&prewalk, &batch, &suffix, &import, &facts);
    assert!(!rows.complete());
    assert!(rows.problems.iter().any(|problem| problem.contains("tainted")));
    assert!(none_proved(&rows), "{rows:#?}");
    assert_eq!(verdict_of(&rows, "Demo.one_pos"), V::NotDispatched);
}

#[test]
fn every_row_is_one_of_the_four_island_verdicts_on_the_wire() {
    let sources = [FIRST.replace("by decide", "by sorry"), SECOND.to_string()];
    let sources: Vec<&str> = sources.iter().map(String::as_str).collect();
    let (_, batch) = checked(&sources);
    let rows = rows_of(&sources, &batch, &verified());
    let message =
        rows.transport("demo", "demo", "s", true, CleanIslandPhase::Verified, 2, |_, at| {
            ("src/lib.rs".to_string(), 1, u32::try_from(at + 1).unwrap())
        });
    assert_eq!(message.validate(), Ok(()));
    let refused =
        message.rows.iter().find(|row| row.key.starts_with("demo::Demo.one_pos#")).unwrap();
    assert_eq!(
        (refused.status.as_str(), refused.stop.as_str(), refused.basis.as_deref()),
        ("failed", "solver-incomplete", Some("unproved_fail_closed"))
    );
    assert_eq!(verdicts(&rows).len(), message.rows.len());
}

#[test]
fn a_named_or_refused_command_with_no_row_makes_the_rows_incomplete() {
    // `coinductive` is a declaration Clean names that the shared slicer has
    // no keyword for: no row, so the rows are not the whole set. Refused, its
    // refusal would otherwise be lost; accepted, its sibling would be proved
    // in rows that say they are complete.
    let refused = ["theorem keep_a : 0 < 1 := by decide\ncoinductive Nix : Nat → Prop\n"];
    let (_, batch) = checked(&refused);
    let listed = batch.outcomes[0].declarations.as_deref().unwrap();
    assert!(listed.iter().any(|d| d.name.as_deref() == Some("Nix") && d.refused), "{listed:?}");
    let rows = rows_of(&refused, &batch, &verified());
    assert!(!rows.complete(), "{rows:#?}");
    assert!(
        rows.problems
            .iter()
            .any(|p| p.contains("declaration `Nix` has no row, and something refused it")),
        "{:?}",
        rows.problems
    );
    assert!(none_proved(&rows), "{rows:#?}");

    let accepted = ["coinductive Always : Nat → Prop\n| step : Always (n + 1) → Always n\n\
                     theorem keep_b : 0 < 1 := by decide\n"];
    let (_, batch) = checked(&accepted);
    let listed = batch.outcomes[0].declarations.as_deref().unwrap();
    assert!(listed.iter().any(|d| d.name.as_deref() == Some("Always")), "{listed:?}");
    let rows = rows_of(&accepted, &batch, &verified());
    assert!(!rows.complete(), "{rows:#?}");
    assert!(
        rows.problems.iter().any(|p| p.contains("declaration `Always` has no row")),
        "{:?}",
        rows.problems
    );
    assert_eq!(verdict_of(&rows, "keep_b"), V::NotDispatched, "{rows:#?}");
}

#[test]
fn an_error_before_every_region_refuses_every_declaration_of_its_island() {
    // Where Clean places a refused served import: its `import` line, before
    // the first listed command. It is the island's, not the batch's.
    let sources = [FIRST, SECOND];
    let (_, mut batch) = checked(&sources);
    assert!(!batch.is_rejected(), "{batch:?}");
    batch.outcomes[0].errors.push(CleanIslandDiagnostic {
        start: 0,
        end: 9,
        message: "`import Trust.Binding` names Trust's temporal vocabulary, but its canonical \
                  source did not check in this session"
            .to_string(),
    });
    let rows = rows_of(&sources, &batch, &verified());
    assert_eq!(verdict_of(&rows, "Demo.one_pos"), V::ProofRefused, "{rows:#?}");
    assert_eq!(verdict_of(&rows, "Demo.double"), V::ProofRefused, "{rows:#?}");
    // The other island's declarations are not refused by it.
    assert_eq!(verdict_of(&rows, "double_two"), V::NotDispatched, "{rows:#?}");
    assert!(none_proved(&rows), "{rows:#?}");
}

#[test]
fn a_session_that_did_not_check_models_and_read_bindings_proves_none_of_them() {
    let safe = format!("import Trust.FiniteModel\n{LOCKSTEP}");
    let mut session = CleanIslandSession::new();
    session.enable_model_checks();
    assert!(!session.models_and_bindings_read());
    let batch = session.check_all(&[&safe]);
    assert!(!batch.is_rejected(), "{batch:?}");
    // The facts a compiler that did not say so states: verified only.
    let rows = rows_of(
        &[&safe],
        &batch,
        &CrateIslandFacts { verified: true, ..CrateIslandFacts::default() },
    );
    assert!(rows.rows.iter().all(|row| row.verdict == V::NotDispatched), "{rows:#?}");

    // Why model checks alone are not enough: an island that imports only
    // `Trust.Binding` has its binding read only by a session that reads
    // bindings.
    let binding = "import Trust.Binding\nopen Trust.Protocol\n\
                   def policy : Trust.Protocol.Binding :=\n  \
                   binds \"config.harness\" [\"HarnessPolicyObserved\"] []\n";
    let mut models_only = CleanIslandSession::new();
    models_only.enable_model_checks();
    let batch = models_only.check_all(&[binding]);
    assert!(!batch.is_rejected(), "{batch:?}");
    assert!(batch.outcomes[0].bindings.is_empty(), "{batch:?}");
    let mut both = CleanIslandSession::new();
    both.enable_model_checks();
    both.enable_binding_reads();
    assert!(both.models_and_bindings_read());
    let batch = both.check_all(&[binding]);
    assert!(!batch.is_rejected(), "{batch:?}");
    assert_eq!(batch.outcomes[0].bindings.len(), 1, "{batch:?}");
    let rows = rows_of(&[binding], &batch, &verified());
    assert_eq!(verdict_of(&rows, "policy"), V::NotDispatched, "{rows:#?}");
}

#[test]
fn a_refused_served_import_refuses_every_declaration_of_its_island() {
    // A crate that already declared `Trust.Protocol.binds` cannot be served
    // `Trust.Binding`: Clean refuses the import at its `import` command, a
    // command with no row, after it set each declaration's flag.
    let mut session = CleanIslandSession::new();
    let first =
        ["namespace Trust\nnamespace Protocol\ndef binds : Nat := 0\nend Protocol\nend Trust\n"];
    assert!(!session.check_all(&first).is_rejected());
    let island = "import Trust.Binding\nnamespace Demo\ntheorem one_pos : 0 < 1 := by decide\n\
                  theorem two_pos : 0 < 2 := by decide\nend Demo\n";
    let sources = [island, "theorem other_one : (1 : Nat) = 1 := rfl\n"];
    let batch = session.check_all(&sources);
    assert!(batch.is_rejected(), "{batch:?}");
    let errors = &batch.outcomes[0].errors;
    assert!(
        errors.iter().any(
            |error| error.start == 0 && error.message.contains("did not check in this session")
        ),
        "{errors:?}"
    );
    let listed = batch.outcomes[0].declarations.as_deref().unwrap();
    assert!(!listed.iter().any(|d| d.name.as_deref() == Some("Demo.one_pos") && d.refused));
    let rows = rows_of(&sources, &batch, &verified());
    assert_eq!(verdict_of(&rows, "Demo.one_pos"), V::ProofRefused, "{rows:#?}");
    assert_eq!(verdict_of(&rows, "Demo.two_pos"), V::ProofRefused, "{rows:#?}");
    // The other island is not refused by it; nothing is proved.
    assert_eq!(verdict_of(&rows, "other_one"), V::NotDispatched, "{rows:#?}");
    assert!(none_proved(&rows), "{rows:#?}");
}
