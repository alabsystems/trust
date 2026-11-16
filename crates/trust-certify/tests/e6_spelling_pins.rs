//! Re-measured SPELLING pins for the E6 admission expansion — increment P
//! (`docs/design-notes/2026-09-28-e6-admission-expansion.md` §4, §6).
//!
//! The design note's "defeq" rows were measured on an installed pack whose
//! Clean pin differs from this tree's, so every row an increment relies on is
//! re-measured HERE, on the Clean this tree builds, as a kernel check of the
//! island author's natural spelling against the term the E6 producer mints.
//! Each theorem is checked in its own session, so a refusal names its row.
//!
//! Only the rows the landed increments rest on are pinned; each later
//! increment adds its own rows beside its producer.

use trust_certify::clean_island::CleanIslandSession;

fn checks(theorem: &str) -> bool {
    let mut session = CleanIslandSession::new();
    !session.check(theorem).is_rejected()
}

/// The kernel's refusal of `theorem`, which must be a TYPE refusal of the
/// `rfl` proof — never a parse or name error, which would make a negative
/// pin pass for the wrong reason.
fn refused_as_not_defeq(theorem: &str) -> bool {
    let mut session = CleanIslandSession::new();
    let outcome = session.check(theorem);
    let text = outcome.errors.iter().map(|e| e.message.clone()).collect::<Vec<_>>().join(" | ");
    eprintln!("{theorem}\n  -> {text}");
    outcome.is_rejected()
        && !text.contains("parse")
        && !text.contains("unexpected")
        && !text.contains("unknown")
}

/// Row 11 (I1′): an island's `a == b` over `Bool` is definitionally the
/// `decide (a = b)` the bool-equality producer mints, at OPEN operands.
#[test]
fn bool_eq_is_the_decide_image() {
    assert!(checks("theorem r11 (a b : Bool) : (a == b) = decide (a = b) := rfl"));
}

/// Row 10 (I1′): an island's `a != b` over `Bool` is the negated decision.
#[test]
fn bool_ne_is_the_negated_decide_image() {
    assert!(checks("theorem r10 (a b : Bool) : (a != b) = !(decide (a = b)) := rfl"));
}

/// The negative control for both rows: the equality image is NOT the image of
/// an ordering. `a < b` over `Bool` is `!a && b` — not `decide (a = b)` — and
/// the kernel says so at a ground instance (review H1's witness, `false < true`).
#[test]
fn the_equality_image_is_not_an_ordering() {
    assert!(checks("theorem h1_value : (decide (false = true)) = false := rfl"));
    assert!(refused_as_not_defeq("theorem h1_wrong : (decide (false = true)) = true := rfl"));
}

/// Row 11's note, q24: Clean parses `a || b || c` RIGHT-nested, which is also
/// the nesting of MIR's short-circuit tree. Lean declares `||` `infixl`
/// (INFERRED); if Clean's parser moves to that rule, the left-nested spelling
/// becomes the parse and every n-ary `||` discharge (increment I3′) breaks —
/// this pin says so first.
#[test]
fn or_parses_right_nested() {
    assert!(checks("theorem q24r (a b c : Bool) : (a || b || c) = (a || (b || c)) := rfl"));
    assert!(refused_as_not_defeq(
        "theorem q24l (a b c : Bool) : (a || b || c) = ((a || b) || c) := rfl"
    ));
}

/// Row 11 (I3′): an island's `&&`, `||` and `!` are definitionally the
/// `Bool.and`, `Bool.or` and `Bool.not` the tree producer mints, and `xor`
/// is `Bool.xor`. Clean has no infix `^^` (it does not parse), so an island
/// spells `^` as the call.
#[test]
fn bool_connectives_are_the_tree_images() {
    assert!(checks("theorem i3_and (a b : Bool) : (a && b) = Bool.and a b := rfl"));
    assert!(checks("theorem i3_or (a b : Bool) : (a || b) = Bool.or a b := rfl"));
    assert!(checks("theorem i3_not (a : Bool) : (!a) = Bool.not a := rfl"));
    assert!(checks("theorem i3_xor (a b : Bool) : (xor a b) = Bool.xor a b := rfl"));
}

/// The `&&` twin of q24: Clean parses `a && b && c` RIGHT-nested, and the
/// tree reader re-nests a left-nested `s & i & n` to meet it.
#[test]
fn and_parses_right_nested() {
    assert!(checks("theorem q24and (a b c : Bool) : (a && b && c) = (a && (b && c)) := rfl"));
    assert!(refused_as_not_defeq(
        "theorem q24andl (a b c : Bool) : (a && b && c) = ((a && b) && c) := rfl"
    ));
}

/// Row 10 over an unsigned carrier (I3′'s integer `!=` leaf): an island's
/// `x != y` over `UInt8` is `Bool.not (decide (x = y))`, and `x == 3` is
/// `decide (x = 3)` — the frozen comparison mint's equality decision.
#[test]
fn unsigned_equality_leaves_are_the_decide_images() {
    assert!(checks("theorem i3_ne_u8 (x y : UInt8) : (x != y) = Bool.not (decide (x = y)) := rfl"));
    assert!(checks("theorem i3_eq_u8 (x : UInt8) : (x == 3) = decide (x = 3) := rfl"));
}

/// Rows 7 and 12 (I4′): an island's `if c then x else y` over a `Bool` `c`
/// is `ite (c = true) x y` — the image of a value decision on a `bool` — at
/// open arms and at literal arms (i04); `cond c x y` is NOT (i03, review H8),
/// which is why the producer never mints `cond`.
#[test]
fn bool_conditions_are_the_ite_image_never_cond() {
    assert!(checks(
        "theorem r12 (c : Bool) (a b : UInt8) : (if c then a else b) = ite (c = true) a b := rfl"
    ));
    assert!(checks(
        "theorem i04 (c : Bool) : (if c then (1 : UInt8) else 0) = \
         ite (c = true) (UInt8.ofNat 1) (UInt8.ofNat 0) := rfl"
    ));
    assert!(refused_as_not_defeq(
        "theorem i03 (a b c : Bool) : (if a then b else c) = cond a b c := rfl"
    ));
}

/// Row 12 and H7 (I4′): `>` in a select is its operands swapped with the
/// arms kept — an island's `if a > b then a else b` is `if b < a then a else
/// b` (i06).
#[test]
fn a_greater_than_select_is_the_swapped_less_than() {
    assert!(checks(
        "theorem i06 (a b : UInt8) : (if a > b then a else b) = (if b < a then a else b) := rfl"
    ));
}

/// I4′'s `match` image is the design note's `if x = v then … else …` chain.
/// Clean's own `match` on a `UInt8` literal elaborates through `x == v`
/// (`BEq`), a different proposition, so it is NOT that chain — an island
/// author writes the chain. If Clean's `match` elaboration changes, this
/// negative says so first.
#[test]
fn a_clean_match_is_not_the_if_chain() {
    assert!(refused_as_not_defeq(
        "theorem p13 (x : UInt8) : (match x with | 0 => (10 : UInt8) | 1 => 20 | _ => 0) = \
         (if x = 0 then 10 else if x = 1 then 20 else 0) := rfl"
    ));
}
