// structural-fold-corpus SOURCE — rung A of the structural-recursion
// certification lane (docs/design/2026-07-10-structural-fold-lane.md §5 Rung A):
// the mini-ADT pilot. A 3-constructor `Arc`-recursive tree enum plus:
//
//   GOOD Int-valued structural folds (strict-subterm recursion only):
//     * `xor_all`    — combines BOTH IHs with `^` (BitXor raises no overflow VC,
//                      so the fold reaches FULLY_FAITHFUL end-to-end).
//     * `first_leaf` — payload/IH selection, no arithmetic at all; the `Two` arm
//                      deliberately IGNORES its second subtree (an unused
//                      recursive field still gets an IH slot in the model).
//     * `tag_xor`    — the SAME `xor_all` shape over `TaggedTree`, whose
//                      explicit `#[repr(i64)]` discriminants (10/20/30) make the
//                      SwitchInt tag != declaration index — the load-bearing pin
//                      for the design's "do NOT assume tag == decl index" rule.
//     * `size`/`sum` — the design doc's literal members, using `+`. Their MIR
//                      shape is recognized and the kernel witness mints, but the
//                      `i64` ArithmeticOverflow safety VC over an unbounded
//                      recursive result is genuinely NOT dischargeable, so they
//                      honestly stop short of FULLY_FAITHFUL (measured residue,
//                      not a recognizer gap — see the corpus PROVENANCE).
//
//   ADVERSARIAL members (must DECLINE, by name — design §6):
//     * `bad_self`    — a switch arm recurses on the SCRUTINEE itself
//                       (`f(x) = f(x)` inside the `One` arm).
//     * `bad_rebuilt` — recurses on a RECONSTRUCTED node (the `beta_normalize`
//                       shape): `bad_rebuilt(&Tree::One(a.clone()))`.
//     * `bad_nonsub`  — recurses on a SIBLING-CALL result: `bad_nonsub(pick(a))`
//                       where `pick` is a foreign (non-self, non-Arc-deref)
//                       callee.
//
// RUNG B additions (docs/design/2026-07-10-structural-fold-lane.md §5 Rung B,
// §4):
//
//   BOOL-fold lane members (result sort Bool, short-circuit &&/|| as per-arm
//   cond-trees, Int-payload comparisons as Bool leaves):
//     * `has_leaf_zero` — `Leaf(v)=>v==0; One(a)=>f(a); Two(a,b)=>f(a)||f(b)`.
//     * `all_leaves_pos` — `Leaf(v)=>v>0; One(a)=>f(a); Two(a,b)=>f(a)&&f(b)`.
//
//   ACCUMULATOR lane members (design §4: motive `Acc → Acc`, one uninterpreted
//   total insert op, the model pins the exact post-order insert sequence):
//     * `collect_leaves` — the good member: `&mut HashSet<i64>` threaded
//       UNCHANGED to every recursive call, mutated ONLY via `insert` with the
//       returned bool DISCARDED.
//     * `bad_acc_escape` — adversarial: the accumulator is passed to a foreign
//       (non-insert, non-self) callee (`sink`) — design §4 rule (iii).
//     * `bad_acc_read`  — adversarial: `insert`'s bool return is CONSUMED
//       (control flow becomes accumulator-dependent) — design §4 rule (ii).
//     * `bad_acc_alias` — adversarial: the `One` arm recurses with a FRESH
//       local accumulator instead of the threaded parameter — design §4
//       rule (i) (the model would pin inserts into `out` that the code
//       discards).
//
// NO closures anywhere (this corpus exercises DIRECT self-recursion; the
// stack_safe-closure-routed recursion idiom is exercised by the REAL
// clean-kernel `level-fold-corpus` fixtures instead).
//
// Author: Andrew Yates | Copyright 2026 Andrew Yates | License: Apache-2.0 OR MIT
#![allow(unused)]

use std::collections::HashSet;
use std::sync::Arc;

pub enum Tree {
    Leaf(i64),
    One(Arc<Tree>),
    Two(Arc<Tree>, Arc<Tree>),
}

/// Explicit-discriminant sibling: SwitchInt tags are 10/20/30 while the
/// declaration indices (and the `Downcast` projections) are 0/1/2.
#[repr(i64)]
pub enum TaggedTree {
    Leaf(i64) = 10,
    One(Arc<TaggedTree>) = 20,
    Two(Arc<TaggedTree>, Arc<TaggedTree>) = 30,
}

// ---------------------------------------------------------------------------
// GOOD folds
// ---------------------------------------------------------------------------

pub fn xor_all(t: &Tree) -> i64 {
    match t {
        Tree::Leaf(v) => *v,
        Tree::One(a) => xor_all(a),
        Tree::Two(a, b) => xor_all(a) ^ xor_all(b),
    }
}

pub fn first_leaf(t: &Tree) -> i64 {
    match t {
        Tree::Leaf(v) => *v,
        Tree::One(a) => first_leaf(a),
        Tree::Two(a, _b) => first_leaf(a),
    }
}

pub fn tag_xor(t: &TaggedTree) -> i64 {
    match t {
        TaggedTree::Leaf(v) => *v,
        TaggedTree::One(a) => tag_xor(a),
        TaggedTree::Two(a, b) => tag_xor(a) ^ tag_xor(b),
    }
}

pub fn size(t: &Tree) -> i64 {
    match t {
        Tree::Leaf(_) => 1,
        Tree::One(a) => 1 + size(a),
        Tree::Two(a, b) => 1 + size(a) + size(b),
    }
}

pub fn sum(t: &Tree) -> i64 {
    match t {
        Tree::Leaf(v) => *v,
        Tree::One(a) => sum(a),
        Tree::Two(a, b) => sum(a) + sum(b),
    }
}

// ---------------------------------------------------------------------------
// RUNG B: BOOL folds
// ---------------------------------------------------------------------------

pub fn has_leaf_zero(t: &Tree) -> bool {
    match t {
        Tree::Leaf(v) => *v == 0,
        Tree::One(a) => has_leaf_zero(a),
        Tree::Two(a, b) => has_leaf_zero(a) || has_leaf_zero(b),
    }
}

pub fn all_leaves_pos(t: &Tree) -> bool {
    match t {
        Tree::Leaf(v) => *v > 0,
        Tree::One(a) => all_leaves_pos(a),
        Tree::Two(a, b) => all_leaves_pos(a) && all_leaves_pos(b),
    }
}

// ---------------------------------------------------------------------------
// RUNG B: ACCUMULATOR folds
// ---------------------------------------------------------------------------

pub fn collect_leaves(t: &Tree, out: &mut HashSet<i64>) {
    match t {
        Tree::Leaf(v) => {
            out.insert(*v);
        }
        Tree::One(a) => collect_leaves(a, out),
        Tree::Two(a, b) => {
            collect_leaves(a, out);
            collect_leaves(b, out);
        }
    }
}

/// Foreign sink the escape adversary hands the accumulator to.
pub fn sink(_s: &HashSet<i64>) {}

pub fn bad_acc_escape(t: &Tree, out: &mut HashSet<i64>) {
    match t {
        Tree::Leaf(v) => {
            out.insert(*v);
            sink(out); // the accumulator ESCAPES to a foreign callee
        }
        Tree::One(a) => bad_acc_escape(a, out),
        Tree::Two(a, b) => {
            bad_acc_escape(a, out);
            bad_acc_escape(b, out);
        }
    }
}

pub fn bad_acc_read(t: &Tree, out: &mut HashSet<i64>) {
    match t {
        Tree::Leaf(v) => {
            // insert's bool return CONSUMED — control flow becomes
            // accumulator-dependent.
            if out.insert(*v) {
                out.insert(0);
            }
        }
        Tree::One(a) => bad_acc_read(a, out),
        Tree::Two(a, b) => {
            bad_acc_read(a, out);
            bad_acc_read(b, out);
        }
    }
}

pub fn bad_acc_alias(t: &Tree, out: &mut HashSet<i64>) {
    match t {
        Tree::Leaf(v) => {
            out.insert(*v);
        }
        Tree::One(a) => {
            // recursion with a FRESH accumulator — the threaded parameter's
            // inserts are silently discarded (rule (i) kill).
            let mut other: HashSet<i64> = HashSet::new();
            bad_acc_alias(a, &mut other);
        }
        Tree::Two(a, b) => {
            bad_acc_alias(a, out);
            bad_acc_alias(b, out);
        }
    }
}

// ---------------------------------------------------------------------------
// ADVERSARIAL members
// ---------------------------------------------------------------------------

/// The foreign sibling callee `bad_nonsub` routes its recursive argument
/// through. NOT itself recursive.
pub fn pick(t: &Tree) -> &Tree {
    t
}

pub fn bad_self(t: &Tree) -> i64 {
    match t {
        Tree::Leaf(v) => *v,
        Tree::One(_a) => bad_self(t), // recursion on the scrutinee — NO IH slot
        Tree::Two(a, b) => bad_self(a) ^ bad_self(b),
    }
}

pub fn bad_rebuilt(t: &Tree) -> i64 {
    match t {
        Tree::Leaf(v) => *v,
        // recursion on a RECONSTRUCTED node — provenance is a fresh local
        // aggregate, not a field projection of the matched variant payload.
        Tree::One(a) => bad_rebuilt(&Tree::One(a.clone())),
        Tree::Two(a, b) => bad_rebuilt(a) ^ bad_rebuilt(b),
    }
}

pub fn bad_nonsub(t: &Tree) -> i64 {
    match t {
        Tree::Leaf(v) => *v,
        // recursion on a SIBLING-CALL result — `pick(a)`'s return value has
        // call-result provenance, not subterm provenance.
        Tree::One(a) => bad_nonsub(pick(a)),
        Tree::Two(a, b) => bad_nonsub(a) ^ bad_nonsub(b),
    }
}
