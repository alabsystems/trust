//@ dont-check-compiler-stderr
//@ check-pass
//@ compile-flags: -Ztrust-ir-lower=strict -Ztrust-verify=off
//! Trust (wave-MRB): the SYNTACTIC SHARED-BORROW PEEL. A scrutinee the programmer
//! WROTE as `&e` — at any depth — against arms that each carry the matching
//! `PatKind::Deref` layers is notation for the by-value match: the dispatch reads
//! exactly the place `e` denotes, borrowck freezes that place for the whole match,
//! and every layer between is a temporary. `lower_match` peels BOTH sides (the
//! `Borrow` nodes off the expression, the `Deref` layers off each arm) and hands the
//! result to the lane that already owns the peeled type — its own integer `Switch`,
//! or `lower_tuple_match` for a tuple / struct / fixed array.
//!
//! No pointer is materialized and nothing is loaded through one, so this lane reads
//! and writes NO pointer ledger (`borrow_ptrs` / `ref_param_ptrs` / `mut_borrow_ptrs`
//! / `interior_ptrs` / `local_snapshot_ptrs` are untouched) and mints no
//! frame-derived address. Under `strict`, so a refusal is a compile error and the
//! derived-MIR differential must also agree with the built MIR.
//!
//! The three MEASURED corpus shapes (ct-control-0830) are `struct_scrut`
//! (tests/ui/lint/unaligned_references_fake_borrow.rs), `nested_ref_int`
//! (tests/ui/rfcs/rfc-2005-default-binding-mode/range.rs) and `array_rest`
//! (tests/ui/rfcs/rfc-2005-default-binding-mode/slice-ok.rs).
//!
//! DELIBERATELY ABSENT, each still fail-closed with its own precise tag and each
//! probed: a `&mut` scrutinee; a ref-typed VARIABLE with no `Borrow` node to peel
//! (`fn f(a: &A) { match a { .. } }`); a FLOAT terminal; a BOOL terminal; an ENUM
//! terminal (`&&E` — `lower_enum_match` takes its arms unpeeled, and the depth-1
//! `&E` case is wave-MR's); a union / raw-pointer / slice / `str` / generic terminal;
//! and any arm the peel would leave holding a by-REF binding, an or-pattern, a
//! nested variant subpattern or a `box` pattern — those refuse DOWNSTREAM, on their
//! own pattern, which is where that obligation belongs.

#[repr(packed)]
struct Packed(i32);

// Depth 1, STRUCT terminal, with a guarded catch-all — the measured corpus shape.
fn struct_scrut(x: Packed) -> i32 {
    match &x {
        Packed(4) => 1,
        _ if true => 2,
        _ => 3,
    }
}

// Depth 2, STRUCT terminal: the walk is a loop, not a single peel.
fn struct_scrut_deep(x: Packed) -> i32 {
    match &&x {
        Packed(4) => 1,
        _ => 0,
    }
}

// Depth 4, INTEGER terminal, RANGE arms — the measured corpus shape. Peeling all
// four layers leaves `match i { .. }`, which the integer `Switch` already lowers.
fn nested_ref_int() -> i32 {
    let i = 5;
    match &&&&i {
        1..=3 => 1,
        4..=8 => 2,
        _ => 3,
    }
}

// Depth 1, TUPLE terminal, refutable + terminal catch-all.
fn tuple_scrut(t: (i32, i32)) -> i32 {
    match &t {
        (1, _) => 1,
        _ => 0,
    }
}

// Depth 1, TUPLE terminal over a LITERAL tuple expression: the wave-27 syntactic
// destructure fast path is by-value-only (`peel == 0`), so this must reach the
// ordinary classifier rather than inherit a plan written against unpeeled arms.
fn tuple_lit_scrut() -> i32 {
    match &(1i32, 2i32) {
        (1, _) => 1,
        _ => 0,
    }
}

// Depth 1, fixed-ARRAY terminal, `..` rest binding nothing — the measured corpus
// shape (wave-SR's rest classifier over the peeled `ty::Array`).
fn array_rest() {
    match &[0, 1, 2] {
        [..] => {}
    };
}

// Depth 1, fixed-ARRAY terminal, EXPLICIT `&`-pattern spelling. The explicit form
// makes the element binding BY VALUE (`BindingMode(No, Not)`), which is what the
// peeled classifier accepts. The match-ergonomics spelling `[a, _, _] => *a` binds
// `a` BY REF and therefore still refuses downstream on `TupleMatch`'s by-ref
// binding wall — deliberately, and it is NOT in this pin.
fn array_pos() -> i32 {
    match &[7i32, 8, 9] {
        &[a, _, _] => a,
    }
}

// Depth 1, TUPLE terminal, EXPLICIT `&`-pattern with a by-value binding.
fn tuple_bind() -> i32 {
    match &(1i32, 2i32) {
        &(a, _) => a,
    }
}

fn main() {
    if struct_scrut(Packed(4)) != 1 {
        std::process::exit(1);
    }
    if struct_scrut_deep(Packed(4)) != 1 {
        std::process::exit(2);
    }
    if nested_ref_int() != 2 {
        std::process::exit(3);
    }
    if tuple_scrut((1, 2)) != 1 {
        std::process::exit(4);
    }
    if tuple_lit_scrut() != 1 {
        std::process::exit(5);
    }
    array_rest();
    if array_pos() != 7 {
        std::process::exit(6);
    }
    if tuple_bind() != 1 {
        std::process::exit(7);
    }
}
