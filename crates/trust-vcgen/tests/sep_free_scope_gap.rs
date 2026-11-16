// The REVIEWER'S SCOPE PROBE for the global-deallocator free channel
// (`sep_double_free.rs` is the channel's own suite).
//
// That channel charges `[unsafe:sep:free]` and the heap's use-after-free rows
// with `Formula::Bool(true)` — a definite violation, a claim about EVERY
// execution — and licenses it by dominance: a free is visible only in the blocks
// its freeing block dominates. The engine walks blocks in INDEX order, not along
// a path, so the licence also needs the visibility to END where the dominated
// region ends. These fixtures are CORRECT code built to find out whether it
// does: `p` is freed on one `SwitchInt` arm, and read (or written, then read) on
// the other arm, which frees it only afterwards. rustc numbers the free's
// successor block — dominated by the free — BEFORE the other arm, so a free that
// stayed visible once applied is charged against a read no execution performs
// after a free.
//
// MEASURED 2026-09-24 on the first port of the channel to this tree, whose
// `enter_block` applied the free with the sticky `SymbolicHeap::free` (the
// design of the commit this lands): `free_one_arm_use_other` minted one
// definite use-after-free (the read) and `write_other_arm` two (the write and
// the read) — `Formula::Bool(true)` refutations of correct code. `enter_block`
// now REPLACES the path-conditioned freed set per block
// (`SymbolicHeap::set_path_freed`), and both census to zero.
//
// Two more fixtures pin the neighbouring claim that a freed LOCAL which is
// rebound before the read is not charged:
//  * `free_then_rebind_by_call` — `p = fresh()` after `dealloc(p, l)`; rustc
//    routes the call result through a temporary and an `Assign`, which drops
//    the stale allocation binding.
//  * `free_realloc_after_checked_write` — the re-`alloc` sits in the block the
//    null-check pass APPENDS (highest-numbered), and the read of the new
//    allocation in the lower-numbered continuation, so the index-ordered walk
//    reaches the read FIRST. The continuation's `p = move _t` still drops the
//    stale binding, so the read falls to the untracked, fail-closed deref rows
//    rather than a definite use-after-free.
//
// Fixtures are REAL extracted MIR (`-Ztrust-dump=mir-only:<dir>
// -Ztrust-policy=advisory`, stage1 trustc fc5538510 2026-09-24, which mints the
// compiler-resolved `callee_key` the engine decides on) of
// `fixtures/sep_free_scope_gap_fx.rs`. The first two reproduce, block for block,
// the MIR of the reviewer's original probes (salvaged without their source).
use trust_types::*;
use trust_vcgen::generate_vcs;

const ONE_ARM_READ: &str = include_str!("fixtures/gap_free_one_arm_use_other_mir.json");
const ONE_ARM_WRITE: &str = include_str!("fixtures/gap_write_other_arm_mir.json");
const REBIND_BY_CALL: &str = include_str!("fixtures/gap_free_then_rebind_by_call_mir.json");
const REALLOC_APPENDED: &str =
    include_str!("fixtures/gap_free_realloc_after_checked_write_mir.json");

fn sep_rows(json: &str) -> Vec<String> {
    let func: VerifiableFunction =
        serde_json::from_str(json).expect("fixture MIR must deserialize");
    generate_vcs(&func)
        .iter()
        .filter_map(|vc| match &vc.kind {
            VcKind::Assertion { message } if message.contains("[unsafe:sep:") => {
                Some(message.clone())
            }
            _ => None,
        })
        .collect()
}

fn census(name: &str, json: &str) -> Vec<String> {
    let rows = sep_rows(json);
    println!("GAPCENSUS {name}: {} sep rows", rows.len());
    for r in &rows {
        println!("GAPCENSUS {name}   | {r}");
    }
    let charged: Vec<String> = rows
        .into_iter()
        .filter(|r| r.contains("use-after-free") || r.contains("[unsafe:sep:free]"))
        .collect();
    println!("GAPCENSUS {name}: use-after-free / double-free rows = {}", charged.len());
    charged
}

#[test]
fn a_free_on_one_arm_is_not_charged_against_a_read_on_the_other() {
    let charged = census("free_one_arm_use_other", ONE_ARM_READ);
    assert!(
        charged.is_empty(),
        "`if c {{ dealloc(p, l); g() }} else {{ h(); *p; dealloc(p, l) }}` reads `p` \
         only on the arm that has not freed it: {charged:#?}"
    );
}

#[test]
fn a_free_on_one_arm_is_not_charged_against_a_write_on_the_other() {
    let charged = census("write_other_arm", ONE_ARM_WRITE);
    assert!(
        charged.is_empty(),
        "`if c {{ dealloc(p, l); g() }} else {{ h(); *p = 7; *p; dealloc(p, l) }}` \
         writes and reads `p` only on the arm that has not freed it: {charged:#?}"
    );
}

#[test]
fn a_freed_local_rebound_by_a_call_is_not_a_use_after_free() {
    let charged = census("free_then_rebind_by_call", REBIND_BY_CALL);
    assert!(
        charged.is_empty(),
        "`dealloc(p, l); p = fresh(); *p` reads through the NEW pointer: {charged:#?}"
    );
}

#[test]
fn a_reallocation_the_walk_reaches_late_is_not_a_use_after_free() {
    let charged = census("free_realloc_after_checked_write", REALLOC_APPENDED);
    assert!(
        charged.is_empty(),
        "`dealloc(p, l); *q = 1; p = alloc(l); *p` reads the NEW allocation: {charged:#?}"
    );
}
