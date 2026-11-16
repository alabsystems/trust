//! INTERIOR-MUT-CHANNEL-1 on real, UNEDITED rustc MIR: a union read through its plain
//! field beside a cell field. `interior_mut_channel_realmir.rs` pins the channel on
//! hand-edited dumps, because `Cell::get` stays a call; a union needs no edit, because
//! rustc reads `u.n` as a place (`copy (_2.1: u32)`). Every program in
//! `tests/data/interior_mut_channel_union.rs` guards `u.n < 100`, then lets the cell be
//! set to `u32::MAX`, then computes `u.n + 1`. The cell is set by a call handed `&u`, or a
//! borrow below it such as `&u.c`, or by a zero-argument call that reaches a parked
//! reference, or by the body itself (`u.c.set(..)`).
//!
//! Each `must_refute_*` program panics natively (`attempt to add with overflow`) at
//! `-O0`, and at `-O3` with `-C overflow-checks=on`. Its `+ 1` row and the row's
//! hardened twin must be FAILED. Each `control_*` program returns normally, and its row
//! must be PROVED, so a verifier that refused every union read would fail this file.
//!
//! # Fixtures
//!
//! `tests/fixtures/interior_mut_channel_union_{O0,O3}_*_mir.json` are the compiler's own
//! extraction, unedited, captured with the channel `trustc` b58a105dd:
//!
//! ```text
//! trustc --edition 2021 --crate-type lib -C opt-level=0 -Ztrust-verify=on \
//!        -Ztrust-verify-profile=unix_hardened -Ztrust-verify-level=2 \
//!        -Ztrust-policy=advisory -Ztrust-verify-output=json \
//!        -Ztrust-dump=mir:<dir> interior_mut_channel_union.rs
//! ```
//!
//! The `O3` set adds `-C opt-level=3 -C overflow-checks=on`. Each set then goes through
//! `python3 tests/data/interior_mut_channel_edit.py --union <O0|O3> <dir> tests/fixtures`,
//! which only makes the data file's span paths crate-relative.
//!
//! # Measured 2026-10-16
//!
//! b58a105dd's own `trustc`, which predates G2 (`41436c3aae`), PROVES every add row and
//! twin here, the 23 panicking programs included, at both levels. On main `d512993d21` 9
//! of them refute, and all 16 controls prove; since INTERIOR-MUT-CHANNEL-2 closed, all 23
//! refute. With `generate/path_defs.rs`'s `unsafe_cell_places` naming nothing, the add row
//! and twin of the first nine refuting programs turn PROVED again at both levels (36
//! rows), so those nine `must_refute_*` tests fail first; no control row changes. The
//! same mutant turns the two `must_refute_*` rows of `interior_mut_channel_realmir.rs` red.
//!
//! CLOSED 2026-10-16 (INTERIOR-MUT-CHANNEL-2, `docs/KNOWN_HAZARDS.md`): main `d512993d21`
//! PROVED the add row and twin of the other 14 panicking programs, at both levels. Each
//! takes, somewhere in the body, a shared borrow of an owned place STRICTLY BELOW a union
//! that holds cell bytes: the cell field (`&u.c` as `&Cell` or as `&ManuallyDrop<Cell>`,
//! `&h.u.c`, `&a[0].c`, `&t.1.c`, an atomic, `UnsafeCell` or `MaybeUninit<Cell>` field), or
//! a field that holds a cell without being one (`&o.inner` of a nested union, `&u.s` of a
//! struct wrapping the cell). The borrow is handed to the call between guard and add,
//! taken BEFORE the guard and handed over after it, stored in a struct, or parked for a
//! zero-argument call; or the body sets the cell itself, with no user callee. The slot
//! half named the cell place below the union (`u.0.0.0`) but not its union cover `u`, so
//! the sibling field `u.1` that the add reads looked like disjoint storage. The same
//! borrow behind `&` refuted, because the pointee half names `*u` whole. Those 14
//! `must_refute_*` tests were `#[ignore]`d with the verdict they must meet until the slot
//! half named the union cover of every shared borrow below a union, asking the byte
//! question of the borrowed type (`generate::shared_borrow_cell_places`, the review of
//! G2-OPTSTRING-1); they run now. The 7 `control_*` programs that follow them are their
//! correct twins, and still prove.
#[path = "support/realmir_rows.rs"]
mod realmir_rows;

use realmir_rows::{PRIMARY_ADD, TWIN_ADD, Verdict, expect, rows};

/// The `+ 1` row and its hardened twin at `line` of `name`, in the `-O0` and the `-O3`
/// dump: exactly one of each per dump, and every one has verdict `want`.
fn add_at(name: &str, line: u32, want: Verdict, why: &str) {
    for opt in ["O0", "O3"] {
        let rows = rows("interior_mut_channel_union_", &format!("{opt}_{name}"), &[]);
        expect(&rows, line, PRIMARY_ADD, 1, want, &format!("{opt} {name}: {why}"));
        expect(&rows, line, TWIN_ADD, 1, want, &format!("{opt} {name}: {why}"));
    }
}

// ─── must refute: a call that may set the cell runs between the guard and the add ───

/// `u: U32` by value, then `poke(&u)` (the review's `q04`). The slot half names `u`
/// whole, because a union's fields share its bytes.
#[test]
fn must_refute_owned_union() {
    add_at("must_refute_owned_union", 36, Verdict::Failed, "`poke(&u)` may set `u.n`");
}

/// `u: &U32`, then `poke(u)` (the review's `q05`). The pointee half names `*u`.
#[test]
fn must_refute_union_ref() {
    add_at("must_refute_union_ref", 46, Verdict::Failed, "`poke(u)` may set `(*u).n`");
}

/// The call is handed the cell field of an owned union: `&u.c` goes through
/// `ManuallyDrop::deref` into `poke_cell`. The borrowed place is `u.0`; the add reads
/// `u.1`, the same bytes. PROVED on main `d512993d21` (INTERIOR-MUT-CHANNEL-2).
#[test]
fn must_refute_owned_union_cell_field_borrow() {
    add_at(
        "must_refute_owned_union_cell_field_borrow",
        57,
        Verdict::Failed,
        "`poke_cell(&*u.c)` writes the bytes `u.n` reads",
    );
}

/// The same borrow of the cell field, of a union behind `&`.
#[test]
fn must_refute_union_ref_cell_field_borrow() {
    add_at(
        "must_refute_union_ref_cell_field_borrow",
        67,
        Verdict::Failed,
        "`poke_cell(&*(*u).c)` writes the bytes `(*u).n` reads",
    );
}

/// A union field of an owned struct, with `poke(&h.u)`.
#[test]
fn must_refute_owned_struct_union_field() {
    add_at(
        "must_refute_owned_struct_union_field",
        87,
        Verdict::Failed,
        "`poke(&h.u)` may set `h.u.n`",
    );
}

/// A union field of a struct behind `&`, with `poke_h(h)`.
#[test]
fn must_refute_struct_union_field_ref() {
    add_at(
        "must_refute_struct_union_field_ref",
        97,
        Verdict::Failed,
        "`poke_h(h)` may set `(*h).u.n`",
    );
}

/// The cell field of a union field of an owned struct, `&h.u.c`. PROVED on main
/// `d512993d21` (INTERIOR-MUT-CHANNEL-2).
#[test]
fn must_refute_owned_struct_union_cell_field_borrow() {
    add_at(
        "must_refute_owned_struct_union_cell_field_borrow",
        108,
        Verdict::Failed,
        "`poke_cell(&*h.u.c)` writes the bytes `h.u.n` reads",
    );
}

/// The cell field is a bare `ManuallyDrop<UnsafeCell<u32>>`.
#[test]
fn must_refute_owned_unsafecell_union() {
    add_at(
        "must_refute_owned_unsafecell_union",
        129,
        Verdict::Failed,
        "`poke_uu(&u)` writes through `get()`",
    );
}

/// The cell field is a `ManuallyDrop<AtomicU32>`.
#[test]
fn must_refute_owned_atomic_union() {
    add_at(
        "must_refute_owned_atomic_union",
        150,
        Verdict::Failed,
        "`poke_ua(&u)` stores to the atomic",
    );
}

/// The cell sits inside a `MaybeUninit` (itself a union) inside the `ManuallyDrop`.
#[test]
fn must_refute_owned_maybe_uninit_cell_union() {
    add_at(
        "must_refute_owned_maybe_uninit_cell_union",
        171,
        Verdict::Failed,
        "`poke_um(&u)` sets the cell inside the `MaybeUninit`",
    );
}

/// `u: &U32`, and `poke_parked()` takes no argument: a `&'static U32` parked in a
/// `thread_local!` lets it set the cell.
#[test]
fn must_refute_union_ref_zero_arg_call() {
    add_at(
        "must_refute_union_ref_zero_arg_call",
        197,
        Verdict::Failed,
        "`poke_parked()` may set `(*u).n`",
    );
}

// ─── correct twins: the same unions where the add cannot overflow ────────────────

/// Nothing runs between the guard and the add.
#[test]
fn control_owned_union_no_call() {
    add_at(
        "control_owned_union_no_call",
        208,
        Verdict::Proved,
        "no code runs between guard and add",
    );
}

/// `poke(&u)` runs BEFORE the guard, so the guard reads the bytes the add reads.
#[test]
fn control_owned_union_guard_after_call() {
    add_at(
        "control_owned_union_guard_after_call",
        215,
        Verdict::Proved,
        "the guard follows the call",
    );
}

/// The same behind `&`.
#[test]
fn control_union_ref_guard_after_call() {
    add_at(
        "control_union_ref_guard_after_call",
        221,
        Verdict::Proved,
        "the guard follows the call",
    );
}

/// `poke_cell(&u.c)` runs before the guard: the twin a fix of INTERIOR-MUT-CHANNEL-2 must
/// keep proving.
#[test]
fn control_owned_union_cell_field_borrow_guard_after_call() {
    add_at(
        "control_owned_union_cell_field_borrow_guard_after_call",
        228,
        Verdict::Proved,
        "the guard follows the call",
    );
}

/// The call may set the cell, but `u.n / 2 + 1` cannot overflow.
#[test]
fn control_owned_union_add_cannot_overflow() {
    add_at(
        "control_owned_union_add_cannot_overflow",
        236,
        Verdict::Proved,
        "`u32::MAX / 2 + 1` fits",
    );
}

/// The call is handed ANOTHER union; `u`'s address is never taken.
#[test]
fn control_other_union_call() {
    add_at("control_other_union_call", 248, Verdict::Proved, "`poke(&v)` cannot reach `u`");
}

/// A union with no cell (`P32 { a: u32, n: u32 }`): its bytes are frozen behind `&p`.
#[test]
fn control_owned_frozen_union_call() {
    add_at("control_owned_frozen_union_call", 269, Verdict::Proved, "`look(&p)` cannot write `p`");
}

/// The same behind `&`.
#[test]
fn control_frozen_union_ref_call() {
    add_at("control_frozen_union_ref_call", 279, Verdict::Proved, "`look(p)` cannot write `*p`");
}

/// `poke(&h.u)` is handed the struct's union field; the add reads the frozen sibling
/// `h.k`, which the slot half does not name.
#[test]
fn control_owned_struct_frozen_sibling() {
    add_at(
        "control_owned_struct_frozen_sibling",
        290,
        Verdict::Proved,
        "`h.k` is outside the borrowed `h.u`",
    );
}

// ─── INTERIOR-MUT-CHANNEL-2 (closed): more shared borrows strictly below the union ───
//
// Main `d512993d21` PROVED the add row and twin of every program in this section at -O0
// and -O3, and each one panics natively: false proofs, pinned `#[ignore]`d with the
// verdict they must meet until the union cover closed them. The review of this file's first version, which pinned only the two programs
// above, found them; the diagnostic mutant in the header turns every one of them FAILED.

/// `poke_md(&u.c)` takes `&ManuallyDrop<Cell<u32>>`: no `ManuallyDrop::deref` call.
#[test]
fn must_refute_owned_union_md_field_borrow() {
    add_at(
        "must_refute_owned_union_md_field_borrow",
        315,
        Verdict::Failed,
        "`poke_md(&u.c)` sets the bytes `u.n` reads",
    );
}

/// The body sets the cell itself (`u.c.set(u32::MAX)`); no user function is called.
#[test]
fn must_refute_owned_union_cell_set_in_body() {
    add_at(
        "must_refute_owned_union_cell_set_in_body",
        326,
        Verdict::Failed,
        "`u.c.set(u32::MAX)` sets the bytes `u.n` reads",
    );
}

/// An array of unions: `poke_cell(&a[0].c)`, then `a[0].n + 1`.
#[test]
fn must_refute_union_array_cell_field_borrow() {
    add_at(
        "must_refute_union_array_cell_field_borrow",
        337,
        Verdict::Failed,
        "`poke_cell(&a[0].c)` sets the bytes `a[0].n` reads",
    );
}

/// A union in a tuple: `poke_cell(&t.1.c)`, then `t.1.n + 1`.
#[test]
fn must_refute_union_tuple_cell_field_borrow() {
    add_at(
        "must_refute_union_tuple_cell_field_borrow",
        348,
        Verdict::Failed,
        "`poke_cell(&t.1.c)` sets the bytes `t.1.n` reads",
    );
}

/// A union nested in a union: `poke(&o.inner)` is handed a field that holds a cell
/// without being one, then `o.m + 1`.
#[test]
fn must_refute_nested_union_inner_borrow() {
    add_at(
        "must_refute_nested_union_inner_borrow",
        366,
        Verdict::Failed,
        "`poke(&o.inner)` sets the bytes `o.m` reads",
    );
}

/// `let c = &u.c` BEFORE the guard; `poke_cell(c)` after it.
#[test]
fn must_refute_owned_union_cell_borrow_before_guard() {
    add_at(
        "must_refute_owned_union_cell_borrow_before_guard",
        378,
        Verdict::Failed,
        "`poke_cell(c)`, `c = &u.c`, sets the bytes `u.n` reads",
    );
}

/// The `AtomicU32` field itself borrowed: `poke_atomic(&u.c)`.
#[test]
fn must_refute_owned_atomic_union_field_borrow() {
    add_at(
        "must_refute_owned_atomic_union_field_borrow",
        394,
        Verdict::Failed,
        "`poke_atomic(&u.c)` stores to the bytes `u.n` reads",
    );
}

/// The `UnsafeCell<u32>` field itself borrowed: `poke_uc(&u.c)`.
#[test]
fn must_refute_owned_unsafecell_union_field_borrow() {
    add_at(
        "must_refute_owned_unsafecell_union_field_borrow",
        410,
        Verdict::Failed,
        "`poke_uc(&u.c)` writes the bytes `u.n` reads",
    );
}

/// The `MaybeUninit<Cell<u32>>` field itself borrowed: `poke_mu(&u.c)`.
#[test]
fn must_refute_owned_maybe_uninit_union_field_borrow() {
    add_at(
        "must_refute_owned_maybe_uninit_union_field_borrow",
        426,
        Verdict::Failed,
        "`poke_mu(&u.c)` sets the bytes `u.n` reads",
    );
}

/// The union field is a struct wrapping the cell: `poke_sc(&u.s)`.
#[test]
fn must_refute_owned_union_struct_wrapped_cell_borrow() {
    add_at(
        "must_refute_owned_union_struct_wrapped_cell_borrow",
        451,
        Verdict::Failed,
        "`poke_sc(&u.s)` sets the bytes `u.n` reads",
    );
}

/// `park_cell(&u.c)` BEFORE the guard; the ZERO-ARGUMENT `poke_parked_cell()` after it
/// sets the cell through the parked pointer.
#[test]
fn must_refute_owned_union_parked_cell_zero_arg_call() {
    add_at(
        "must_refute_owned_union_parked_cell_zero_arg_call",
        481,
        Verdict::Failed,
        "`poke_parked_cell()` sets the bytes `u.n` reads",
    );
}

/// `&u.c` stored in a struct; `poke_cell_ref(&r)` is handed the struct.
#[test]
fn must_refute_owned_union_cell_ref_in_struct() {
    add_at(
        "must_refute_owned_union_cell_ref_in_struct",
        501,
        Verdict::Failed,
        "`poke_cell_ref(&r)`, `r.c = &u.c`, sets the bytes `u.n` reads",
    );
}

// ─── correct twins of those shapes: a fix of INTERIOR-MUT-CHANNEL-2 must keep them ───

/// The body sets the cell BEFORE the guard.
#[test]
fn control_owned_union_cell_set_in_body_guard_after() {
    add_at(
        "control_owned_union_cell_set_in_body_guard_after",
        513,
        Verdict::Proved,
        "the guard follows the write",
    );
}

/// The parked cell is poked BEFORE the guard.
#[test]
fn control_owned_union_parked_cell_poked_before_guard() {
    add_at(
        "control_owned_union_parked_cell_poked_before_guard",
        521,
        Verdict::Proved,
        "the guard follows the call",
    );
}

/// The nested union, `poke(&o.inner)` BEFORE the guard.
#[test]
fn control_nested_union_guard_after_call() {
    add_at(
        "control_nested_union_guard_after_call",
        528,
        Verdict::Proved,
        "the guard follows the call",
    );
}

/// `poke_cell(&u.c)` may set the cell, but `u.n / 2 + 1` cannot overflow.
#[test]
fn control_owned_union_cell_field_borrow_cannot_overflow() {
    add_at(
        "control_owned_union_cell_field_borrow_cannot_overflow",
        536,
        Verdict::Proved,
        "`u32::MAX / 2 + 1` fits",
    );
}

/// Two unions: `poke_cell(&v.c)`, then `u.n + 1`.
#[test]
fn control_other_union_cell_field_borrow() {
    add_at(
        "control_other_union_cell_field_borrow",
        548,
        Verdict::Proved,
        "`poke_cell(&v.c)` cannot reach `u`",
    );
}

/// A tuple: `poke_cell(&t.1.c)`, then the frozen sibling `t.0 + 1`, outside the union
/// cover `t.1`.
#[test]
fn control_union_tuple_frozen_sibling() {
    add_at(
        "control_union_tuple_frozen_sibling",
        559,
        Verdict::Proved,
        "`t.0` is outside the union `t.1`",
    );
}

/// A struct: `poke_cell(&h.u.c)`, then the frozen sibling `h.k + 1`, outside the union
/// cover `h.u`.
#[test]
fn control_owned_struct_cell_field_borrow_frozen_sibling() {
    add_at(
        "control_owned_struct_cell_field_borrow_frozen_sibling",
        570,
        Verdict::Proved,
        "`h.k` is outside the union `h.u`",
    );
}
