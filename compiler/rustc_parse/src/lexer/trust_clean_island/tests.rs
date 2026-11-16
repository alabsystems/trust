use super::{IslandScanError, scan_clean_island_body};

fn close_of(body: &str) -> usize {
    let off = scan_clean_island_body(body).unwrap();
    assert!(body[off..].starts_with('}'), "{body:?} @ {off}");
    off
}

#[test]
fn plain_and_nested_braces() {
    assert_eq!(close_of("}"), 0);
    assert_eq!(close_of(" def x : Nat := 1 }"), 18);
    let s = " def o : P := { x := 0, y := { z := 1 } } }";
    assert_eq!(close_of(s), s.len() - 1);
    let s = " theorem t {α : Type} (a : α) : a = a := rfl }";
    assert_eq!(close_of(s), s.len() - 1);
}

#[test]
fn unicode_is_just_bytes() {
    let s = " theorem t (n : Nat) : n ≤ n := Nat.le_refl n\n ∀ → λ ⟨⟩ ∧ ¬ ≠ ↔ × }";
    assert_eq!(close_of(s), s.len() - 1);
}

#[test]
fn comments_are_opaque() {
    let s = " -- a } with \" and it's\n def x := 1 }";
    assert_eq!(close_of(s), s.len() - 1);
    let s = " /- outer /- nested } -/ \" outer -/ }";
    assert_eq!(close_of(s), s.len() - 1);
    let s = " /-- doc } -/ def x := 1 }";
    assert_eq!(close_of(s), s.len() - 1);
}

#[test]
fn strings_chars_raw_and_guillemets_are_opaque() {
    let s = r#" def s : String := "a\"}b{" }"#;
    assert_eq!(close_of(s), s.len() - 1);
    let s = r##" def s : String := r#"a"b}"# }"##;
    assert_eq!(close_of(s), s.len() - 1);
    let s = r#" def s : String := r"x}y" }"#;
    assert_eq!(close_of(s), s.len() - 1);
    let s = " def c : Char := '{' \n def d : Char := '}' }";
    assert_eq!(close_of(s), s.len() - 1);
    let s = r" def e : Char := '\n' def f : Char := '\'' }";
    assert_eq!(close_of(s), s.len() - 1);
    let s = " def «odd } name» : Nat := 1 }";
    assert_eq!(close_of(s), s.len() - 1);
}

#[test]
fn identifier_primes_are_not_char_literals() {
    // `h'` then ` : ` then `}` — a naive char-literal rule would read
    // `' :` as a literal start and lose the closing brace.
    let s = " theorem t (h' : 0 = 0) : 0 = 0 := h' }";
    assert_eq!(close_of(s), s.len() - 1);
    let s = " def x'' := x' }";
    assert_eq!(close_of(s), s.len() - 1);
    // A prime after a non-ASCII identifier char is still a prime.
    let s = " def α' := α }";
    assert_eq!(close_of(s), s.len() - 1);
    // `r'` is an identifier, not a raw string.
    let s = " def r' := r }";
    assert_eq!(close_of(s), s.len() - 1);
}

#[test]
fn unclosed_reasons() {
    assert_eq!(
        scan_clean_island_body(" def x := { a := 1 "),
        Err(IslandScanError::Unclosed { depth: 2, innermost: Some(10) })
    );
    assert_eq!(
        scan_clean_island_body(" def x := 1 "),
        Err(IslandScanError::Unclosed { depth: 1, innermost: None })
    );
    assert_eq!(
        scan_clean_island_body(" def s := \"abc }"),
        Err(IslandScanError::UnterminatedString { at: 10 })
    );
    assert_eq!(
        scan_clean_island_body(" /- open } "),
        Err(IslandScanError::UnterminatedBlockComment { at: 1 })
    );
    assert_eq!(
        scan_clean_island_body(" def «x } "),
        Err(IslandScanError::UnterminatedGuillemets { at: 5 })
    );
    assert_eq!(
        scan_clean_island_body(" def s := r#\"abc }"),
        Err(IslandScanError::UnterminatedRawString { at: 10 })
    );
}
