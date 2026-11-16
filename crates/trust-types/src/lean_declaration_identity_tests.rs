// Unit tests for the stable Lean declaration key: the token reading, the
// statement anchor, and which edits move a key. The commands and their
// canonical names are given as Clean's parse reports them.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use super::*;

/// `(Clean's canonical name, the command's source text)`, in authored order.
fn commands(succ: &str, double: &str) -> Vec<(Option<String>, String)> {
    vec![
        (None, "open Nat".to_string()),
        (Some("Demo.succ_pos".to_string()), succ.to_string()),
        (Some("Demo.double".to_string()), double.to_string()),
        (Some("Demo.instInhabitedNat".to_string()), "instance : Inhabited Nat := ⟨0⟩".to_string()),
        (None, "example : 1 = 1 := rfl".to_string()),
        (None, "example : 1 = 1 := by rfl".to_string()),
        (Some("Demo.Color".to_string()), "inductive Color\n| red\n| green".to_string()),
        (None, "#check Nat".to_string()),
        (Some("top".to_string()), "theorem _root_.top (a : Nat) : a = a := rfl".to_string()),
        (Some("c".to_string()), "set_option pp.all true in\ntheorem c : 3 = 3 := rfl".to_string()),
    ]
}

const SUCC: &str =
    "/-- The successor is positive. -/\ntheorem succ_pos (n : Nat) : 0 < n + 1 := by\n  omega";
const DOUBLE: &str = "@[simp] def double (n : Nat) : Nat := n + n";

fn named(list: &[(Option<String>, String)]) -> Vec<Option<LeanDeclaration>> {
    lean_declarations(list.iter().map(|(name, text)| (name.as_deref(), text.as_str())))
}

fn keys(list: &[(Option<String>, String)]) -> Vec<Option<String>> {
    named(list).iter().map(|d| d.as_ref().map(LeanDeclaration::key)).collect()
}

#[test]
fn the_token_reading_drops_whitespace_and_comments_only() {
    assert_eq!(lean_token_text("(a:Nat)"), lean_token_text("( a : Nat )"));
    assert_eq!(lean_token_text("x := a+b -- tail"), "x := a + b");
    assert_eq!(lean_token_text("/- a /- nested -/ block -/ y"), "y");
    assert_eq!(lean_token_text("Nat.succ n.1"), "Nat.succ n . 1");
    assert_eq!(lean_token_text("\"a -- b\" c"), "\"a -- b\" c");
    assert_eq!(lean_token_text("a → b"), lean_token_text("a→b"));
}

#[test]
fn each_declaration_is_named_by_clean_and_each_lexical_command_by_nothing() {
    let found = named(&commands(SUCC, DOUBLE));
    let names: Vec<Option<(&str, &str)>> =
        found.iter().map(|d| d.as_ref().map(|d| (d.keyword.as_str(), d.name.as_str()))).collect();
    assert_eq!(
        names,
        [
            None,
            Some(("theorem", "Demo.succ_pos")),
            Some(("def", "Demo.double")),
            Some(("instance", "Demo.instInhabitedNat")),
            Some(("example", "example")),
            Some(("example", "example")),
            Some(("inductive", "Demo.Color")),
            None,
            Some(("theorem", "top")),
            Some(("theorem", "c")),
        ]
    );
    for key in keys(&commands(SUCC, DOUBLE)).into_iter().flatten() {
        let (_, id) = crate::obligation_identity::split_obligation_key(&key).expect("a key");
        assert!(crate::obligation_identity::is_local_id(id), "{key}");
    }
    // The two examples share a statement and are told apart by rank.
    let (a, b) = (found[4].as_ref().unwrap(), found[5].as_ref().unwrap());
    assert_eq!(a.anchor, b.anchor);
    assert_ne!(a.local_id, b.local_id);
    // `set_option … in` is seen through to the declaration it scopes.
    assert_eq!(found[9].as_ref().unwrap().anchor, "theorem : 3 = 3");
    // A keyword inside brackets declares nothing.
    assert_eq!(lean_declarations([(None, "attribute [instance] foo")]), [None]);
}

#[test]
fn a_reformat_moves_no_key_and_no_source_digest() {
    let reformatted = commands(
        "/-- Edited doc. -/\n-- and a comment\ntheorem succ_pos (n:Nat):0<n+1:=by\n    omega -- done",
        DOUBLE,
    );
    let (before, after) = (named(&commands(SUCC, DOUBLE)), named(&reformatted));
    assert_eq!(keys(&commands(SUCC, DOUBLE)), keys(&reformatted));
    let digests = |list: &[Option<LeanDeclaration>]| -> Vec<Option<String>> {
        list.iter().map(|d| d.as_ref().map(|d| d.source_digest.clone())).collect()
    };
    assert_eq!(digests(&before), digests(&after));
}

#[test]
fn a_proof_edit_keeps_the_key_and_moves_the_source_digest() {
    let edited = commands(&SUCC.replace("omega", "simp"), DOUBLE);
    let (before, after) = (named(&commands(SUCC, DOUBLE)), named(&edited));
    assert_eq!(keys(&commands(SUCC, DOUBLE)), keys(&edited));
    assert_ne!(before[1].as_ref().unwrap().source_digest, after[1].as_ref().unwrap().source_digest);
    assert_eq!(before[2], after[2]);
}

#[test]
fn a_statement_edit_moves_only_that_key() {
    let (before, after) = (
        keys(&commands(SUCC, DOUBLE)),
        keys(&commands(&SUCC.replace("0 < n + 1", "0 < n + 2"), DOUBLE)),
    );
    assert_ne!(before[1], after[1]);
    assert_eq!(before[..1], after[..1]);
    assert_eq!(before[2..], after[2..]);
}

#[test]
fn a_rename_keeps_the_local_id() {
    let mut renamed = commands(&SUCC.replace("succ_pos", "succ_positive"), DOUBLE);
    renamed[1].0 = Some("Demo.succ_positive".to_string());
    let (before, after) = (named(&commands(SUCC, DOUBLE)), named(&renamed));
    let (before, after) = (before[1].as_ref().unwrap(), after[1].as_ref().unwrap());
    assert_eq!(after.name, "Demo.succ_positive");
    assert_eq!(before.local_id, after.local_id);
    assert_eq!(before.source_digest, after.source_digest);
}

#[test]
fn a_command_runs_to_the_line_the_next_listed_command_starts_on() {
    let text = "theorem a : 1 = 1 := rfl\n@[simp] def b : Nat := 2\n-- tail\n";
    let b = text.find("def").unwrap();
    let texts = lean_command_texts(text, &[(0, 7), (b, b + 3), (text.len() + 1, text.len() + 2)]);
    // `a` runs to the start of `b`'s line, so `b`'s attribute is `b`'s.
    assert_eq!(texts[0], Some("theorem a : 1 = 1 := rfl\n"));
    // A span outside the text is a command no record can read, and so is the
    // one before it, whose end that span would fix: never a guess.
    assert_eq!(texts[1], None);
    assert_eq!(texts[2], None);
    assert_eq!(lean_command_texts(text, &[(b, b + 3)]), [Some("def b : Nat := 2\n-- tail\n")]);
    // Two commands on one line: the first ends where the second starts.
    let one_line = "open Nat theorem c : 2 = 2 := rfl";
    let c = one_line.find("theorem").unwrap();
    assert_eq!(lean_command_texts(one_line, &[(0, 4), (c, c + 7)])[0], Some("open Nat "));
}
