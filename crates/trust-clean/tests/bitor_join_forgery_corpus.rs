// #49 — BITOR-JOIN forgery corpus.
//
// WHY THIS EXISTS, and why it is not optional. The trust-ir branch lane's
// certificate IS kernel-checked: `check_refinement_decl` type-checks the proof
// term against the statement, adds it as a `Declaration::Theorem`, and requires
// empty axiom residue. So a recognizer that builds a WRONG PROOF is rejected
// loudly, and the census already fails the build on `KERNEL_REJECTED != 0`.
//
// But the kernel proves `evalCfg(cfg) = denotation` — a statement about the CFG
// the recognizer BUILT. It never relates that CFG back to the MIR body. A
// recognizer that MISLIFTS a body therefore produces a statement that is
// kernel-VALID and means the wrong thing, and every other check in the prove
// loop accepts it. That is the one failure mode a shape-recognizer widening can
// introduce, and nothing else in the tree catches it.
//
// A forgery corpus does. Mirrors `bitintrin_forgery_corpus.rs`'s methodology:
// the genuine body certifies (kernel witness, modulo 3) while every adversarial
// mutation DECLINES. A recognizer loose enough to accept a forgery is loose
// enough to have mislifted the real body, so these mutations are the test.
//
// THE SHAPE UNDER TEST. `is_ascii_hexdigit` is
// `is_ascii_digit() | matches!(*self, b'A'..=b'F' | b'a'..=b'f')`, and that `|`
// survives to MIR as a literal `_0 := BitOr(Move(_a), Move(_b))` in the Return
// block, where the pre-existing recognizer admits only a single `_0 := Use(_t)`
// pass-through.
//
// THE ACTUAL SHAPE, measured 2026-08-13 — do not design against a guess.
// `_0 := BitOr(_2, _9)`, and the operands are NOT symmetric:
//   * `_9` is a convergence temp — two `Goto` arms, bb9/bb10.
//   * `_2` is `_2 := BitOr(Move(_3), Move(_6))`, computed in bb8 — itself a
//     CONNECTIVE of two further convergence temps, in a block that ends in a
//     `SwitchInt` (it also carries the next range's decision, `_10`).
// So `is_ascii_hexdigit` is a NESTED disjunction `(_3 | _6) | _9` — three range
// checks — not a flat join of two branch-computed regions. Three implementation
// passes each foundered on a flatter model than the body actually has.
//
// The soundness argument for the lift is unchanged and does not depend on that:
// for booleans `a | b` IS `if a then true else b`. Each mutation below breaks
// one premise of exactly that rewriting.
//
// Uses ONLY the public API (`diagnose_fully_faithful_gate`), so it exercises the
// same gate `prove_one_function` evaluates.
//
// STATUS — LIVE. The or-chain lane landed with this battery, and the
// `#[ignore]`s came off in that same commit. The positive control passing while
// every mutation still declines is what makes the widening faithful rather than
// merely permissive: before the lane, all seven mutation tests passed VACUOUSLY,
// because the recognizer declined every one of these bodies outright.
//
// Author: Andrew Yates <alabsystems@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0 OR MIT

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

use trust_clean::mirsem::CalleeFact;
use trust_clean::prove::diagnose_fully_faithful_gate;
use trust_types::VerifiableFunction;

fn corpus_dir() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("fixtures/stdlib-leaf-ascii-2026-07-16/dumps")
}

/// Load the one dump in the ascii corpus whose function name matches and whose
/// Return block carries a `BitOr` join. Panics (not skips) if absent: a missing
/// fixture must fail loudly rather than silently vacate every assertion below.
fn load_bitor_join(name: &str) -> VerifiableFunction {
    let mut found = None;
    for entry in std::fs::read_dir(corpus_dir()).expect("ascii corpus present").flatten() {
        let path = entry.path();
        if path.extension().and_then(|e| e.to_str()) != Some("json") {
            continue;
        }
        let Ok(text) = std::fs::read_to_string(&path) else { continue };
        let Ok(func) = serde_json::from_str::<VerifiableFunction>(&text) else { continue };
        if func.name == name && return_block_bitor_operands(&func).is_some() {
            found = Some(func);
            break;
        }
    }
    found.unwrap_or_else(|| panic!("no `{name}` dump with a BitOr-join Return block in the corpus"))
}

/// The two operand locals of a Return-block `_0 := BitOr(Move(a), Move(b))`.
fn return_block_bitor_operands(func: &VerifiableFunction) -> Option<(usize, usize)> {
    use trust_types::{BinOp, Operand, Rvalue, Statement, Terminator};
    let ret = func.body.blocks.iter().find(|b| matches!(b.terminator, Terminator::Return))?;
    for statement in &ret.stmts {
        if let Statement::Assign { place, rvalue, .. } = statement
            && place.local == 0
            && let Rvalue::BinaryOp(BinOp::BitOr, a, b) = rvalue
            && let (Operand::Copy(pa) | Operand::Move(pa)) = a
            && let (Operand::Copy(pb) | Operand::Move(pb)) = b
        {
            return Some((pa.local, pb.local));
        }
    }
    None
}

fn certifies(func: &VerifiableFunction) -> bool {
    let callees: BTreeMap<String, CalleeFact> = BTreeMap::new();
    diagnose_fully_faithful_gate(func, &callees).via_ir
}

/// The SHAPE pillar alone. Trust (#53): the bool-join family carries unsigned
/// `Mul` overflow VCs, and `trustir_safety` has no unsigned-multiply family — so
/// those bodies are SHAPE-witnessed and SAFETY-declined. The recognizer tests
/// below assert what the recognizer is responsible for; the safety gap is tracked
/// separately and must NOT be papered over by asserting `via_ir` here.
fn shape_witnessed(func: &VerifiableFunction) -> bool {
    let callees: BTreeMap<String, CalleeFact> = BTreeMap::new();
    diagnose_fully_faithful_gate(func, &callees).via_ir_shape
}

/// Rewrite the Return block's join rvalue in place, returning the mutated body.
fn with_return_join<F>(func: &VerifiableFunction, mutate: F) -> VerifiableFunction
where
    F: FnOnce(&mut trust_types::Rvalue),
{
    use trust_types::{Statement, Terminator};
    let mut out = func.clone();
    let ret = out
        .body
        .blocks
        .iter_mut()
        .find(|b| matches!(b.terminator, Terminator::Return))
        .expect("return block");
    for statement in &mut ret.stmts {
        if let Statement::Assign { place, rvalue, .. } = statement
            && place.local == 0
        {
            mutate(rvalue);
            return out;
        }
    }
    panic!("no `_0 := ..` in the return block");
}

/// THE POSITIVE CONTROL. Without this the whole file is vacuous: every mutation
/// would "decline" simply because the lane declines the shape outright, which is
/// exactly the state before #49 and exactly what this corpus must distinguish.
#[test]
fn genuine_bitor_join_body_certifies_via_trustir() {
    let func = load_bitor_join("is_ascii_hexdigit");
    assert!(
        certifies(&func),
        "the genuine BitOr-join body must certify via trust-ir; if this fails every \
         DECLINE assertion below is vacuous"
    );
}

/// BitAnd is not BitOr. `a & b` is `if a then b else false`, NOT
/// `if a then true else b` — substituting the right tree for the left's
/// `Leaf(false)` computes the wrong function. A recognizer that accepts this
/// has stopped reading the operator.
#[test]
fn bitand_join_declines() {
    use trust_types::{BinOp, Rvalue};
    let func = load_bitor_join("is_ascii_hexdigit");
    let forged = with_return_join(&func, |rv| {
        if let Rvalue::BinaryOp(op, _, _) = rv {
            *op = BinOp::BitAnd;
        }
    });
    assert!(!certifies(&forged), "a BitAnd join must DECLINE — it is a different function");
}

/// Swapping the operands swaps which region's `false` exits flow into the other.
/// `a | b` and `b | a` agree as values, but the LIFT is asymmetric: the tree is
/// built from the left operand's region. Accepting a swap means the recognizer
/// is not tracking which region it substituted into.
#[test]
fn swapped_join_operands_decline() {
    use trust_types::Rvalue;
    let func = load_bitor_join("is_ascii_hexdigit");
    let forged = with_return_join(&func, |rv| {
        if let Rvalue::BinaryOp(_, a, b) = rv {
            std::mem::swap(a, b);
        }
    });
    assert!(
        !certifies(&forged),
        "a swapped-operand join must DECLINE: the lift is asymmetric in the operands"
    );
}

/// An operand that is a PARAMETER is not branch-computed, so it has no region
/// and no `Leaf(false)` to substitute into. Fail-closed.
#[test]
fn parameter_join_operand_declines() {
    use trust_types::{Operand, Place, Rvalue};
    let func = load_bitor_join("is_ascii_hexdigit");
    assert!(func.body.arg_count >= 1, "fixture has at least one parameter");
    let forged = with_return_join(&func, |rv| {
        if let Rvalue::BinaryOp(_, a, _) = rv {
            *a = Operand::Copy(Place { local: 1, projections: Vec::new() });
        }
    });
    assert!(
        !certifies(&forged),
        "a parameter operand is not branch-computed and must DECLINE"
    );
}

/// `_0` as its own operand is a self-reference, not a convergence temp.
#[test]
fn self_referential_join_operand_declines() {
    use trust_types::{Operand, Place, Rvalue};
    let func = load_bitor_join("is_ascii_hexdigit");
    let forged = with_return_join(&func, |rv| {
        if let Rvalue::BinaryOp(_, a, _) = rv {
            *a = Operand::Copy(Place { local: 0, projections: Vec::new() });
        }
    });
    assert!(!certifies(&forged), "`_0` as a join operand must DECLINE");
}

/// Both operands the SAME local is not a two-region join; admitting it would let
/// one region be substituted into itself.
#[test]
fn duplicated_join_operand_declines() {
    use trust_types::Rvalue;
    let func = load_bitor_join("is_ascii_hexdigit");
    let forged = with_return_join(&func, |rv| {
        if let Rvalue::BinaryOp(_, a, b) = rv {
            *b = a.clone();
        }
    });
    assert!(!certifies(&forged), "a join of one local with itself must DECLINE");
}

/// A non-`BitOr` binary join (arithmetic) has no boolean rewriting at all.
#[test]
fn arithmetic_join_declines() {
    use trust_types::{BinOp, Rvalue};
    let func = load_bitor_join("is_ascii_hexdigit");
    for op in [BinOp::Add, BinOp::BitXor] {
        let forged = with_return_join(&func, |rv| {
            if let Rvalue::BinaryOp(o, _, _) = rv {
                *o = op;
            }
        });
        assert!(!certifies(&forged), "a {op:?} join must DECLINE");
    }
}

/// A `Use` join is the PRE-EXISTING single-convergence shape and must keep
/// behaving as it did — this pins that the widening did not swallow the old
/// path. `is_ascii_alphabetic` (two ranges, one join) certified before #49 and
/// must still certify.
#[test]
fn preexisting_single_join_shape_still_certifies() {
    let mut checked = false;
    for entry in std::fs::read_dir(corpus_dir()).expect("ascii corpus present").flatten() {
        let path = entry.path();
        if path.extension().and_then(|e| e.to_str()) != Some("json") {
            continue;
        }
        let Ok(text) = std::fs::read_to_string(&path) else { continue };
        let Ok(func) = serde_json::from_str::<VerifiableFunction>(&text) else { continue };
        if func.name == "is_ascii_alphabetic" && return_block_bitor_operands(&func).is_none() {
            assert!(
                certifies(&func),
                "the pre-existing single-join shape must still certify — the BitOr \
                 widening must not disturb it"
            );
            checked = true;
        }
    }
    assert!(checked, "no single-join `is_ascii_alphabetic` dump found to check against");
}

// ---------------------------------------------------------------------------
// Trust (#53, 2026-08-14): the SHORT-CIRCUIT ARM widening.
// ---------------------------------------------------------------------------
//
// `is_ascii_punctuation` is the same left-nested OR spine as `is_ascii_hexdigit`,
// but each of its four regions is itself a short-circuit `&&`, so the taken arm
// carries the range's SECOND half rather than a literal:
//
//   bb1  _4 := false                       // literal — the pre-existing path
//   bb2  _6 := Le(c, 47); _4 := Ne(_6, false)   // NOT a literal — the new path
//
// `Ne(b, false)` on a `Ty::Bool` operand is the identity on the 0/1 carrier, so
// the arm's value IS the inner condition. The gate that makes this safe is the
// Bool check: an INTEGER `x != 0` is a genuine comparison and collapsing it would
// be a mis-lift that closes by `rfl` and reads as certified.

fn load_named(dir: &str, name: &str) -> Option<VerifiableFunction> {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join(dir);
    for entry in std::fs::read_dir(&root).ok()?.flatten() {
        let path = entry.path();
        if path.extension().and_then(|e| e.to_str()) != Some("json") {
            continue;
        }
        let Ok(text) = std::fs::read_to_string(&path) else { continue };
        let Ok(func) = serde_json::from_str::<VerifiableFunction>(&text) else { continue };
        if func.name == name {
            return Some(func);
        }
    }
    None
}

/// POSITIVE CONTROL. Without it every decline below is vacuous.
#[test]
fn short_circuit_or_chain_certifies_via_trustir() {
    let func = load_named("fixtures/mass-harvest-2026-07-17/char-ascii/dumps", "is_ascii_punctuation")
        .expect("`is_ascii_punctuation` fixture must be present");
    assert!(
        certifies(&func),
        "the four-range short-circuit OR chain must certify via trust-ir; if this \
         fails every DECLINE below is vacuous"
    );
}

/// THE GATE THAT MATTERS. Retyping the inner temp from `bool` to an integer turns
/// `Ne(_6, false)` into a GENUINE comparison against zero. Collapsing that to
/// "the temp is true" would compute a different function while still closing the
/// refinement, so it must DECLINE.
#[test]
fn integer_inner_temp_declines() {
    use trust_types::Ty;
    let mut forged =
        load_named("fixtures/mass-harvest-2026-07-17/char-ascii/dumps", "is_ascii_punctuation")
            .expect("fixture present");
    let mut retyped = 0;
    for local in &mut forged.body.locals {
        // The inner conjunct temps are the Bool locals that are NOT the
        // convergence values on the spine; retyping every Bool but _0 is a
        // superset and is enough to make the arm's `Ne` an integer comparison.
        if local.index != 0 && local.ty == Ty::Bool {
            local.ty = Ty::Int { width: 8, signed: false };
            retyped += 1;
        }
    }
    assert!(retyped > 0, "the fixture must carry Bool temps to retype");
    assert!(
        !certifies(&forged),
        "an INTEGER `x != 0` is a real comparison, not a bool normalization — it \
         must DECLINE rather than be collapsed"
    );
}

/// A non-zero right operand is a genuine comparison too, not a normalization.
#[test]
fn nonzero_right_operand_declines() {
    use trust_types::{BinOp, ConstValue, Operand, Rvalue, Statement};
    let mut forged =
        load_named("fixtures/mass-harvest-2026-07-17/char-ascii/dumps", "is_ascii_punctuation")
            .expect("fixture present");
    let mut mutated = 0;
    for block in &mut forged.body.blocks {
        for statement in &mut block.stmts {
            if let Statement::Assign { rvalue, .. } = statement
                && let Rvalue::BinaryOp(BinOp::Ne, _, b) = rvalue
            {
                *b = Operand::Constant(ConstValue::Bool(true));
                mutated += 1;
            }
        }
    }
    assert!(mutated > 0, "the fixture must carry the `Ne(_, false)` arms");
    assert!(!certifies(&forged), "`Ne(b, true)` is negation, not identity — must DECLINE");
}

// ---------------------------------------------------------------------------
// Trust (#53, 2026-08-15): the BOOL-JOIN CHAIN — two folds compared.
// ---------------------------------------------------------------------------
//
// `eq_ignore_ascii_case` folds a short-circuit `&&` into an intermediate value
// TWICE (once per operand) and compares the results:
//
//   bb1  <FOLD 1 -> _3>;  _10 := (*_2); _13 := Le(65,_10)   SwitchInt -> bb5/bb6
//   bb4  <FOLD 2 -> _4>;  _0 := Eq(_3, _4)                  Return
//
// The lift is a 2x2 tree whose four leaves are `Eq(BitOr(a,m1), BitOr(b,m2))`
// for `m in {0,32}` — each leaf a THREE-statement IR block, since `IrRvalue::Cmp`
// takes operands and both sides here are computed.

/// POSITIVE CONTROL. Without it the declines below are vacuous.
#[test]
fn bool_join_chain_certifies_via_trustir() {
    let func =
        load_named("fixtures/mass-harvest-2026-07-17/char-ascii/dumps", "eq_ignore_ascii_case")
            .expect("`eq_ignore_ascii_case` fixture must be present");
    assert!(
        shape_witnessed(&func),
        "the two-fold compare chain must be SHAPE-witnessed via trust-ir (its safety \
         pillar declines on the unmodelled unsigned-Mul overflow family, tracked \
         separately)"
    );
}

/// The chain's final statement must COMPARE the two folds. Rewriting it to read
/// the same fold twice is a different function, so it must decline.
#[test]
fn chain_comparing_one_fold_with_itself_declines() {
    use trust_types::{Operand, Rvalue, Statement};
    let mut forged =
        load_named("fixtures/mass-harvest-2026-07-17/char-ascii/dumps", "eq_ignore_ascii_case")
            .expect("fixture present");
    let mut mutated = false;
    for block in &mut forged.body.blocks {
        for statement in &mut block.stmts {
            if let Statement::Assign { place, rvalue, .. } = statement
                && place.local == 0
                && let Rvalue::BinaryOp(_, a, b) = rvalue
            {
                *a = b.clone(); // compare fold 2 against itself
                mutated = true;
            }
        }
    }
    assert!(mutated, "the fixture must carry the final `_0 := Eq(_3, _4)`");
    assert!(
        !shape_witnessed(&forged),
        "comparing one fold with itself is a different function — must DECLINE"
    );
}

/// A fold whose mask multiplier differs between the two operands is still a valid
/// SHAPE, so this pins that the recognizer reads the REAL multiplier rather than
/// assuming 32 for both: with a changed multiplier the body must still certify
/// (it is a genuine, if unusual, function), never silently reuse the other's.
#[test]
fn chain_reads_each_folds_own_multiplier() {
    use trust_types::{BinOp, ConstValue, Operand, Rvalue, Statement};
    let mut forged =
        load_named("fixtures/mass-harvest-2026-07-17/char-ascii/dumps", "eq_ignore_ascii_case")
            .expect("fixture present");
    let mut seen = 0;
    for block in &mut forged.body.blocks {
        for statement in &mut block.stmts {
            if let Statement::Assign { rvalue, .. } = statement
                && let Rvalue::BinaryOp(BinOp::Mul, _, b) = rvalue
            {
                seen += 1;
                if seen == 2 {
                    *b = Operand::Constant(ConstValue::Uint(64, 8));
                }
            }
        }
    }
    assert_eq!(seen, 2, "the fixture must carry exactly two fold multipliers");
    assert!(
        shape_witnessed(&forged),
        "a differing per-fold multiplier is a valid shape — the recognizer must read \
         each fold's OWN multiplier, not assume both are equal"
    );
}
