//@ check-pass
//@ compile-flags: -Ztrust-ir-lower -Ztrust-verify=off
#![allow(dead_code)]
//
// Trust (#205R) regression: an enum rustc gives NO discriminant must be DESCRIBED as untagged,
// not left undescribed.
//
// THE DEFECT. `enum UnOp { Not(Vec<()>) }` is, in memory, exactly its 24-byte payload — rustc
// stores no tag at all. Before trust-ir v37 the descriptor grammar could only say `Direct` or
// `Niche`, so `producer_enum_layout_descriptor` DECLINED on `Variants::Single`, and a
// descriptor-less enum falls back to trust-ir's canonical tagged-union layout, which budgets a
// tag. The consumer of that fallback was `Option<UnOp>`, whose own (correct, rustc-derived)
// descriptor says the payload fits in 24 bytes, while the canonical recomputation of its `UnOp`
// field says 8 + 24 = 32. Every layout involved was correct and the module still failed to
// validate:
//
//     ConstTypeMismatch { location: "enum.1 (Option) layout",
//       expected: "variant 1 field 0 entirely within size 24",
//       actual:   "offset 0, field size 32" }
//
// WHY THE FIX IS A NEW ENCODING AND NOT A CANONICAL-LAYOUT CHANGE. trust-ir's canonical layout is
// deliberately NOT a rustc model — rustc also REORDERS fields, so `enum G { X(u8,u64,u8) }` is
// size 16 with field 0 at offset 8, which no tag-free canonical rule reproduces. Making canonical
// untagged would buy no parity and would trade a loud, checkable error for a silent, wider
// disagreement. Every other rustc layout fact rides the descriptor; so does this one.
//
// THE PREDICATE IS `Variants::Single`, NOT "one variant". rustc drops the tag only when
// `present_second.is_none() && !repr.inhibit_enum_layout_opt()`, and `inhibit` is
// `repr.c() || repr.int.is_some()`. Cases (b) and (c) below are the ones a variant-count test
// would get wrong.

// (a) THE DEFECT ITSELF. One inhabited variant, `repr(Rust)`, non-trivial payload: rustc stores no
//     tag, so the producer must emit the untagged descriptor. `Option<UnOp>` is what made the
//     absence observable, so it is what the test actually exercises.
enum UnOp {
    Not(Vec<()>),
}

fn wrap(v: Vec<()>) -> Option<UnOp> {
    Some(UnOp::Not(v))
}

fn unwrap_len(o: Option<UnOp>) -> usize {
    match o {
        Some(UnOp::Not(v)) => v.len(),
        None => 0,
    }
}

// (b) `#[repr(C)]` INHIBITS the optimization: rustc keeps a real discriminant (size 8, field at 4),
//     so this must keep using `Direct`. A variant-count predicate would mislabel it untagged and
//     mint a descriptor claiming the payload starts at 0.
#[repr(C)]
enum ReprC {
    Only(u8),
}

fn repr_c(v: u8) -> ReprC {
    ReprC::Only(v)
}

// (c) `#[repr(u8)]` inhibits it too (size 2, field at 1) — same trap, different clause of
//     `inhibit_enum_layout_opt`.
#[repr(u8)]
enum ReprU8 {
    Only(u8),
}

fn repr_u8(v: u8) -> ReprU8 {
    ReprU8::Only(v)
}

// (d) THE OTHER `Variants::Single` SOURCE, and the one that must keep DECLINING. A multi-variant
//     enum whose other variants are uninhabited is also `Variants::Single`, but the trust-ir def
//     still lists every declared variant and nothing in a tag-free image could pick between them —
//     so the validator, the `shape` queries and the interpreter all reject a multi-variant
//     untagged descriptor. Emitting one here would mint a module they refuse.
enum Void {}

enum OneInhabited {
    Dead(Void),
    Live(u8),
}

fn one_inhabited(v: u8) -> OneInhabited {
    OneInhabited::Live(v)
}

// (e) A fieldless single-variant enum is a ZST — the untagged image is zero bytes. Pinned because
//     a zero-length payload is the degenerate end of the same lane.
enum Unit {
    Only,
}

fn unit() -> Unit {
    Unit::Only
}

// (f) The multi-variant tagged cases are untouched: this is the lane the change must NOT reach.
enum Multi {
    A(u8),
    B(u16),
}

fn multi(c: bool) -> Multi {
    if c { Multi::A(1) } else { Multi::B(2) }
}

fn main() {}
