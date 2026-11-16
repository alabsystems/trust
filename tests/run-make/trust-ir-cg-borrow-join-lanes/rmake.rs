//! Borrowed-scalar references across BLOCK JOINS in the trust-ir-cg backend: the
//! value-divergent join that degraded a `&`/`&mut` of a scalarized local into a
//! self-target PLACEHOLDER, and the placeholder's value being mistaken for an
//! ADDRESS.
//!
//! A reference to a scalarized local has no runtime address; its borrow RECORD
//! (`borrowed_scalars[r] = { target, .. }`) is its only denotation. When a join's
//! predecessors disagreed about the record's VALUE, the join replaced it with a
//! placeholder `{ target: Local(r), branch_varying: true }` and bound the referent's
//! value phi as `scalar_values[r]`. Two defects followed:
//!
//! 1. A SAME-referent borrow (every predecessor names the same local; only that
//!    local's value differs, e.g. after a write through `r` in one arm) was treated
//!    as branch-varying, so every later store / `&mut` call through it was refused
//!    (`[TCG-PTRSEL-STORE]`, `[TCG-MUTREF-ARG-PHI]`) although its target is
//!    statically known. The join now keeps such a record; the referent itself is
//!    threaded as the one post-join name.
//! 2. `scalar_values[r]` satisfied the "`r` holds a pointer" predicate
//!    (`scalar_values.contains_key(r) || is_entry_arg(r)`) that EVERY Deref-led
//!    memory lane gates on, so the referent's VALUE became a Load / GEP base — a
//!    SIGSEGV, or silently reading whatever the value pointed at. Measured on both
//!    frozen builds (2026-09-15) for a field read, a field borrow, a discriminant
//!    read, and a whole-deref store followed by a field read. Root fix: a
//!    placeholder's value lives in its own table (`placeholder_borrow_values`) and
//!    NEVER in `scalar_values`, so no lane can mistake it for an address; readers of
//!    what the reference denotes go through `value_for_borrow_target`.
//!
//! Every case below RUNS (or must be REFUSED by name) at -O0 AND -O3, because the
//! two levels produce the join on different locals (-O0 copies `_r = copy _tmp` in
//! each arm; -O3 borrows directly in each arm). Each program is its own crate so one
//! refusal cannot mask another case. The refusal cases are the genuinely
//! branch-varying shapes: there is no single referent to name, so the only correct
//! outcome short of real memory is a named refusal — never exit 139.

//@ needs-trust-ir-cg-backend
//@ only-apple
//@ only-aarch64

use run_make_support::{rfs, run, rustc};

/// (crate name, source, expected stdout) — must compile and print exactly this.
const VALUE_CASES: &[(&str, &str, &str)] = &[
    // whole-deref store `(*_2) = Bits(5)` in one arm, `(*_2).0` read after the join. SIGSEGV
    // (exit 139) at -O3 on BOTH frozen builds before the root fix, with no deref-field code
    // involved: the placeholder's `scalar_values` entry (the referent's value, 5) was loaded
    // through as a pointer.
    (
        "probe_a",
        r##"// PROBE A: the memory-lane hazard WITHOUT any deref-field access before the join.
// Pre-join the closure body does a WHOLE-deref store `(*_2) = const Bits(5)` (the
// supported bare-[Deref] arm); the FIRST `((*_2).0)` read is AFTER the join.
#[derive(Copy, Clone, Default)] pub struct Bits(u128);
#[inline(never)] fn probe(e: bool) -> bool { std::hint::black_box(e) }
#[inline(never)]
pub fn hazard() -> u128 {
    let mut value = Bits::default();
    let mut ef = |e: bool| -> u128 { if e { value = Bits(5); } value.0 };
    ef(probe(true))
}
fn main() { let got = hazard(); assert_eq!(got, 5); println!("ok {got}"); }
"##,
        "ok 5",
    ),
    // same-referent `&mut` across a join, then a bare `*r = v` store. Refused
    // `[TCG-PTRSEL-STORE]` at -O3 before the join rule although the referent is statically
    // known.
    (
        "probe_b",
        r##"// PROBE B: a SAME-referent borrow across a join, then a bare-deref STORE through it.
// Expect today's join to degrade `_2` to a self-target branch-varying placeholder and
// the second store `(*_2) = const 5` to be refused by name ([TCG-PTRSEL-STORE]).
#[inline(never)] fn probe(e: bool) -> bool { std::hint::black_box(e) }
#[inline(never)]
pub fn store_after_join() -> u128 {
    let mut value: u128 = 0;
    let mut ef = |e: bool| { if e { value = 5; } };
    ef(probe(true));
    ef(probe(true));
    value
}
fn main() { let got = store_after_join(); assert_eq!(got, 5); println!("ok {got}"); }
"##,
        "ok 5",
    ),
    // store on one arm only, read through the reference after the join (already correct; must
    // stay so).
    (
        "f1_read_after_join",
        r##"// F1: same-referent borrow, store on one arm only, READ through the reference after the join.
#[inline(never)] fn probe(e: bool) -> bool { std::hint::black_box(e) }
#[inline(never)]
pub fn read_after_join() -> u128 {
    let mut value: u128 = 1;
    let mut ef = |e: bool| -> u128 { if e { value = 5; } value };
    ef(probe(true))
}
fn main() { let got = read_after_join(); assert_eq!(got, 5); println!("ok {got}"); }
"##,
        "ok 5",
    ),
    // the referent is an ENTRY ARG (no `scalar_values` entry on the untouched path).
    // `[TCG-PTRSEL-STORE]` at -O3 before.
    (
        "f3_entry_arg",
        r##"// F3: the referent is an ENTRY ARG (no scalar_values entry on the untouched path).
#[inline(never)] fn probe(e: bool) -> bool { std::hint::black_box(e) }
#[inline(never)]
pub fn entry_arg(mut value: u128) -> u128 {
    let mut ef = |e: bool| { if e { value += 5; } };
    ef(probe(true));
    ef(probe(true));
    value
}
fn main() { let got = entry_arg(std::hint::black_box(1)); assert_eq!(got, 11); println!("ok {got}"); }
"##,
        "ok 11",
    ),
    // two closures capturing the SAME referent (two reference locals naming one local).
    // `[TCG-PTRSEL-STORE]` at -O3 before.
    (
        "f4_two_closures",
        r##"// F4: two closures capturing the SAME referent by &mut, used alternately (two reference locals -> Local(t)).
#[inline(never)] fn probe(e: bool) -> bool { std::hint::black_box(e) }
#[inline(never)]
pub fn two_closures() -> u128 {
    let mut value: u128 = 1;
    {
        let mut a = |e: bool| { if e { value += 10; } };
        a(probe(true));
        a(probe(false));
    }
    {
        let mut b = |e: bool| { if e { value *= 3; } };
        b(probe(true));
        b(probe(true));
    }
    value
}
fn main() { let got = two_closures(); assert_eq!(got, 99); println!("ok {got}"); }
"##,
        "ok 99",
    ),
    // single-scalar newtype: deref-FIELD write in one arm, deref-field read after the join,
    // by-value return. SIGSEGV at -O3 on the resolver-only build.
    (
        "f5_newtype_join_write_then_read",
        r##"// F5: single-scalar newtype referent; deref-FIELD write in one arm, read after join, then by-value return.
#[derive(Copy, Clone, Default, PartialEq, Debug)] pub struct Bits(u128);
impl Bits { #[inline] fn set(&mut self, b: u32) { let v = self.0; self.0 = v | (1u128 << b); } }
#[inline(never)] fn probe(e: bool) -> bool { std::hint::black_box(e) }
#[inline(never)] fn raw(b: Bits) -> u128 { b.0 }
#[inline(never)]
pub fn f() -> (u128, Bits) {
    let mut value = Bits::default();
    let mut ef = |b: u32, e: bool| -> u128 { if e { value.set(b); } value.0 };
    let a = ef(0, probe(true));
    let c = ef(64, probe(true));
    (a + c, value)
}
fn main() { let (s, v) = f(); let v0 = raw(v); assert_eq!(s, 1 + (1 + (1u128 << 64))); assert_eq!(v0, 1 | (1u128 << 64)); println!("ok"); }
"##,
        "ok",
    ),
    // referent reassigned DIRECTLY after the join while the first closure is dead, then
    // re-borrowed. `[TCG-PTRSEL-STORE]` at -O3 before.
    (
        "f6_direct_reassign_after_join",
        r##"// F6: referent reassigned DIRECTLY (not through the reference) after the join while the closure is dead,
// then a NEW closure borrows it again.
#[inline(never)] fn probe(e: bool) -> bool { std::hint::black_box(e) }
#[inline(never)] fn seven() -> u128 { std::hint::black_box(7) }
#[inline(never)]
pub fn f() -> u128 {
    let mut value: u128 = 1;
    { let mut a = |e: bool| { if e { value = 5; } }; a(probe(true)); }
    value = seven();
    { let mut b = |e: bool| { if e { value += 1; } }; b(probe(true)); b(probe(false)); }
    value
}
fn main() { let got = f(); assert_eq!(got, 8); println!("ok {got}"); }
"##,
        "ok 8",
    ),
    // `&mut acc` taken before a diamond that calls `put(r, ..)` on both arms, then a post-join
    // `put(r, 100)`. `[TCG-MUTREF-ARG-PHI]` at -O0 AND -O3 before.
    (
        "f7_put_diamond",
        r##"// F7: the differential-fuzz shape: `&mut acc` taken BEFORE a diamond that calls `put` on both arms,
// then a post-join `put` through the same reference ([TCG-MUTREF-ARG-PHI] today).
#[inline(never)] fn probe(e: bool) -> bool { std::hint::black_box(e) }
#[inline(never)] fn put(dst: &mut u64, v: u64) { *dst += v; }
#[inline(never)]
pub fn f() -> u64 {
    let mut acc: u64 = 1;
    let r = &mut acc;
    if probe(true) { put(r, 10); } else { put(r, 20); }
    put(r, 100);
    acc
}
fn main() { let got = f(); assert_eq!(got, 111); println!("ok {got}"); }
"##,
        "ok 111",
    ),
    // shared borrow across a diamond, direct write after it, re-borrow (already correct; must
    // stay so).
    (
        "f8_shared_read_after_direct_write",
        r##"// F8: SHARED borrow bound before a diamond in which the referent is NOT written; after the join
// the reference is dead and the referent is written directly, then re-borrowed.
#[inline(never)] fn probe(e: bool) -> bool { std::hint::black_box(e) }
#[inline(never)] fn sink(v: &u64) -> u64 { std::hint::black_box(*v) }
#[inline(never)]
pub fn f() -> u64 {
    let mut t: u64 = 1;
    let r = &t;
    let a = if probe(true) { sink(r) + 1 } else { sink(r) + 2 };
    t = a + 5;
    let r2 = &t;
    let b = if probe(false) { sink(r2) } else { sink(r2) * 2 };
    b
}
fn main() { let got = f(); assert_eq!(got, 14); println!("ok {got}"); }
"##,
        "ok 14",
    ),
    // the write through the captured `&mut` sits in a loop body with a forward join (already
    // correct; must stay so).
    (
        "loop_store",
        r##"// A `&mut` closure capture written ONLY through the reference, inside a loop whose
// body also contains a forward join. Is the referent recognized as loop-carried?
#[inline(never)] fn probe(e: bool) -> bool { std::hint::black_box(e) }
#[inline(never)] fn count() -> u32 { std::hint::black_box(4) }
#[inline(never)]
pub fn loop_store() -> u128 {
    let mut value: u128 = 0;
    let mut ef = |e: bool| { if e { value += 1; } };
    let n = count();
    let mut i = 0;
    while i < n { ef(probe(true)); i += 1; }
    value
}
fn main() { let got = loop_store(); assert_eq!(got, 4); println!("ok {got}"); }
"##,
        "ok 4",
    ),
    // the same loop with an unconditional write (already correct; must stay so).
    (
        "loop_store_nojoin",
        r##"// Same as loop_store but with NO forward join inside the loop body: the write
// through the captured `&mut` is unconditional.
#[inline(never)] fn count() -> u32 { std::hint::black_box(4) }
#[inline(never)] fn bump() -> u128 { std::hint::black_box(1) }
#[inline(never)]
pub fn loop_store() -> u128 {
    let mut value: u128 = 0;
    let mut ef = || { value += bump(); };
    let n = count();
    let mut i = 0;
    while i < n { ef(); i += 1; }
    value
}
fn main() { let got = loop_store(); assert_eq!(got, 4); println!("ok {got}"); }
"##,
        "ok 4",
    ),
    // a GENUINELY branch-varying shared borrow read WHOLE (`*r`) after the join: the
    // `BorrowTarget` read of the placeholder's value, which now lives outside `scalar_values`.
    // Correct before; must stay correct.
    (
        "bv_whole_read",
        r##"// PIN: a branch-varying SHARED borrow read WHOLE (`*r`) after the join — the
// `Resolution::BorrowTarget` read of the self-target placeholder's value.
#[inline(never)] fn probe(e: bool) -> bool { std::hint::black_box(e) }
#[inline(never)]
pub fn bv_whole_read(c: bool) -> u64 {
    let a = std::hint::black_box(5u64);
    let b = std::hint::black_box(9u64);
    let r: &u64 = if probe(c) { &a } else { &b };
    *r + 1
}
fn main() { let x = bv_whole_read(true); let y = bv_whole_read(false); assert_eq!(x, 6); assert_eq!(y, 10); println!("ok {x} {y}"); }
"##,
        "ok 6 10",
    ),
    // a branch-varying shared borrow passed to a non-inlined callee: the call-arg snapshot
    // reads the placeholder's value. Correct before; must stay correct.
    (
        "bv_call_arg",
        r##"// PIN: a branch-varying SHARED borrow passed to a non-inlined callee after the
// join — the call-arg materialization reads the placeholder's value.
#[inline(never)] fn probe(e: bool) -> bool { std::hint::black_box(e) }
#[inline(never)] fn sink(v: &u64) -> u64 { std::hint::black_box(*v) }
#[inline(never)]
pub fn bv_call_arg(c: bool) -> u64 {
    let a = std::hint::black_box(5u64);
    let b = std::hint::black_box(9u64);
    let r: &u64 = if probe(c) { &a } else { &b };
    sink(r) * 2
}
fn main() { let x = bv_call_arg(true); let y = bv_call_arg(false); assert_eq!(x, 10); assert_eq!(y, 18); println!("ok {x} {y}"); }
"##,
        "ok 10 18",
    ),
    // a COPY of a branch-varying borrow taken after the join (`let r2 = r;`), read whole: the
    // copied record's target names the placeholder. Correct before; must stay correct.
    (
        "bv_copy_read",
        r##"// PIN: a COPY of a branch-varying borrow taken AFTER the join (`let r2 = r;`),
// then read whole — the copied record's target is the placeholder local itself.
#[inline(never)] fn probe(e: bool) -> bool { std::hint::black_box(e) }
#[inline(never)]
pub fn bv_copy_read(c: bool) -> u64 {
    let a = std::hint::black_box(5u64);
    let b = std::hint::black_box(9u64);
    let r: &u64 = if probe(c) { &a } else { &b };
    let r2 = r;
    let k = std::hint::black_box(3u64);
    *r2 + k
}
fn main() { let x = bv_copy_read(true); let y = bv_copy_read(false); assert_eq!(x, 8); assert_eq!(y, 12); println!("ok {x} {y}"); }
"##,
        "ok 8 12",
    ),
];

/// (crate name, source, required stderr substrings) — must be REFUSED by name.
const REFUSAL_CASES: &[(&str, &str, &[&str])] = &[
    // a GENUINELY branch-varying shared `(*r).0` READ (`_0 = copy ((*r).0: u128)`, `r`
    // selecting `&a` / `&b`). SIGSEGV (exit 139) at -O0 AND -O3 on both frozen builds: the
    // scalar-collapsed-newtype memory arm loaded through the placeholder's value. No single
    // referent exists, so the resolver refuses it by name.
    (
        "bv_field_read",
        r##"// A GENUINELY branch-varying SHARED `(*r).0` read: `r` selects DIFFERENT
// scalarized referents on the two arms, so the post-join borrow is the
// self-target placeholder, and the field read goes through it.
#[derive(Copy, Clone)] pub struct Bits(u128);
#[inline(never)] fn probe(e: bool) -> bool { std::hint::black_box(e) }
#[inline(never)]
pub fn bv_field_read(c: bool) -> u128 {
    let a = Bits(std::hint::black_box(5u128));
    let b = Bits(std::hint::black_box(9u128));
    let r: &Bits = if probe(c) { &a } else { &b };
    r.0
}
fn main() { let x = bv_field_read(true); let y = bv_field_read(false); assert_eq!(x, 5); assert_eq!(y, 9); println!("ok {x} {y}"); }
"##,
        &["bv_field_read", "[TCG-PTRSEL-FIELD]"],
    ),
    // `let p = &r.0; *p` on a branch-varying shared borrow (`_p = &((*r).0)`). SIGSEGV (exit
    // 139) at -O0 AND -O3 on both frozen builds: `lower_scalar_ref`'s scalar-leaf
    // field-address arm used the placeholder's value as the base pointer. With no
    // `scalar_values` entry that arm (and `memory_aggregate_ref_pointee`) declines, and the
    // generic scalar-bindable check refuses.
    (
        "bv_field_ref",
        r##"// LANE #2, in-function deref: `p = &(*r).0` after the branch-varying SHARED
// join, then `*p` read in the same body (no call-arg adapter gate in the way).
#[derive(Copy, Clone)] pub struct Bits(u128);
#[inline(never)] fn probe(e: bool) -> bool { std::hint::black_box(e) }
#[inline(never)]
pub fn hazard(c: bool) -> u128 {
    let a = Bits(std::hint::black_box(5u128));
    let b = Bits(std::hint::black_box(9u128));
    let r: &Bits = if probe(c) { &a } else { &b };
    let p: &u128 = &r.0;
    *p
}
fn main() { let got = hazard(true); assert_eq!(got, 5); println!("ok {got}"); }
"##,
        &["hazard", "Rvalue::Ref source projection is not scalar-bindable"],
    ),
    // `match r.0 { .. }` on a fieldless enum through a branch-varying shared borrow
    // (`discriminant(((*r).0: K))`). SIGSEGV (exit 139) at -O0 AND -O3 on both frozen builds:
    // the tag was loaded through the placeholder's value (x0 == the tag). The reference-deref
    // discriminant lane now sees no bound pointer and refuses.
    (
        "bv_field_discriminant",
        r##"// LANE #4 probe: `discriminant(((*r).0))` — a fieldless-enum tag read through a
// deref+field chain on a placeholder-joined borrowed scalar. The `rest`
// non-empty path in the reference-deref discriminant lowering loads the tag
// through `scalar_values[r]` (the referent's VALUE phi).
#[derive(Copy, Clone, PartialEq, Eq, Debug)] pub enum K { A, B, C }
#[derive(Copy, Clone)] pub struct W(K);
#[inline(never)] fn probe(e: bool) -> bool { std::hint::black_box(e) }
#[inline(never)]
pub fn hazard(c: bool) -> u32 {
    let a = W(std::hint::black_box(K::B));
    let b = W(std::hint::black_box(K::C));
    let r: &W = if probe(c) { &a } else { &b };
    match r.0 { K::A => 10, K::B => 20, K::C => 30 }
}
fn main() { let got = hazard(true); assert_eq!(got, 20); println!("ok {got}"); }
"##,
        &["hazard", "Rvalue::Discriminant deref before reference pointer binding"],
    ),
];

fn compile(name: &str, opt: &str) -> run_make_support::Rustc {
    let src = format!("{name}.rs");
    let mut cmd = rustc();
    cmd.input(src)
        .crate_type("bin")
        .crate_name(name)
        .output(format!("{name}_o{opt}"))
        .opt_level(opt)
        // Unwinding is a separate axis: with `-Cpanic=unwind` the -O0 `main`'s
        // `assert_eq!` cleanup path refuses as `[TCG-REGALLOC-063]` (measured on both
        // frozen builds, 2026-09-15), which would mask every case below.
        .panic("abort")
        .arg("-Zcodegen-backend=trust-ir-cg")
        // Codegen axis only: the certificate lane is a separate axis (like
        // `-Ztrust-verify=off` above). AArch64 pair opcodes have no checker-accepted
        // certificate yet, so leaving proofs on would refuse every compile here with
        // [TCG-PROOF-465] regardless of what this test measures.
        .arg("-Ztrust-ir-cg-args=no-proof-certs=1")
        // The verifier is a separate axis; this test is about codegen alone.
        .arg("-Ztrust-verify=off")
        .arg("-Cdebuginfo=0");
    cmd
}

fn main() {
    for (name, src, _) in VALUE_CASES {
        rfs::write(format!("{name}.rs"), src);
    }
    for (name, src, _) in REFUSAL_CASES {
        rfs::write(format!("{name}.rs"), src);
    }
    for opt in ["0", "3"] {
        for (name, _, expected) in VALUE_CASES {
            compile(name, opt).run();
            run(&format!("{name}_o{opt}")).assert_stdout_contains(expected);
        }
        for (name, _, must) in REFUSAL_CASES {
            let out = compile(name, opt).run_fail();
            out.assert_stderr_contains("[TCG-MIR-UNSUPPORTED]");
            for needle in must.iter() {
                out.assert_stderr_contains(needle);
            }
        }
    }
}
