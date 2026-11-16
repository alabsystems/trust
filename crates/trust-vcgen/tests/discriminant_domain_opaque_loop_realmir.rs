//! Real-MIR cover for the IMPOSSIBLE-DISCRIMINANT false REFUTATION: an exhaustive
//! `match` on a `Result` whose `otherwise -> Unreachable` arm was refuted with a tag
//! the type has no inhabitant for.
//!
//! THE DEFECT, measured on orca-daemon (orca `bc52b0880`, seal `321aaeda7`,
//! `targo trust check --allow-l0-gaps --keep-going -p orca-daemon`):
//!
//!     [unreach] FAILED (ay-in-process) @ termination_signals.rs:40:18-46:5
//!     counterexample: _4 = 0, _5 = 0, _5#s2_0 = -1, __trust_mir__discr__2 = 0, ..
//!
//! `_5 = Discriminant(_2)` reads a `Result<Signal, Errno>` (tags `{0, 1}`), and the
//! `SwitchInt` reads it back as `_5#s2_0`, the token of that very write. The enum
//! tag-range fact (`value_facts::build_discriminant_variant_range_facts`) bound the
//! destination only under its BARE name and only when it was single-assignment. One
//! `Terminator::Opaque` anywhere in the body (there: `std::process::exit` at the
//! seal; on main: any indirect `fn() -> !` call, which still takes the Opaque bail)
//! is an unlocatable write to EVERY local, so no local was single-assignment, the
//! bound went missing, and `_5#s2_0 = -1` satisfied `_5 ∉ {0, 1}`.
//!
//! Re-measured on main's stage 1 (72d80d86b) with the fixture source below: the
//! same row, `_5#s2_0 = -1`. The seal's `exit` shape was mitigated at extraction by
//! a53999401d (a `-> !` direct call became a `Call`); the vcgen gap was not, and this
//! fixture reaches it through the indirect call that keeps the bail.
//!
//! Fixtures (`-Ztrust-dump=mir-only:<dir>`, stage 1 72d80d86b, `--edition 2021
//! --crate-type lib -Ztrust-verify=on -Ztrust-policy=advisory`):
//!
//!   discr_domain_opaque_loop_mir.json
//!     pub trait Waiter { fn wait(&self) -> Result<Signal, Errno>; }
//!     pub fn wait_loop(w: &dyn Waiter, on_signal: fn() -> !) {
//!         loop { match w.wait() {
//!             Ok(_) => on_signal(),
//!             Err(Errno::EINTR) => continue,
//!             Err(_) => return,
//!         } }
//!     }
//!   discr_domain_opaque_loop_transmute_mir.json — the same loop, but the `Result`
//!     comes from `transmute::<u64, Result<Signal, Errno>>(w.raw())`.
//!
//! (`Errno` is `#[repr(i32)] { Unknown = 0, EPERM = 1, EINTR = 4, EAGAIN = 35 }`,
//! `Signal` is `#[repr(i32)] { SIGHUP = 1, SIGTERM = 15 }`.)
//!
//! What the controls pin:
//!  * a destination REASSIGNED after the read (`_5 = Discriminant(_3); _5 = 7`) keeps
//!    its refutation at `7` — the fact names the read's own write, not the place.
//!    MUTATION: pin the fact at the block END (`version_token_at(.., stmts.len(), ..)`)
//!    instead of just after the read, and this test fails (the fact then speaks
//!    about `7`'s token and false-PROVES the reachable arm).
//!  * a `Result` manufactured by `transmute` keeps rustc's own `InvalidEnumConstruction`
//!    check — the row that charges an invalid value AT ITS CREATION — unproved. The
//!    tag fact is the type's validity invariant for a value READ through a valid
//!    place; it does not and must not discharge the check that a constructed value IS
//!    valid. (The compiler additionally charges the transmute with its
//!    `[unsafe:validity-transmute]` creation row; that row is minted outside vcgen.)
use std::collections::HashSet;

use trust_types::{BlockId, CounterexampleValue, VcKind, VerifiableFunction, VerificationResult};

#[path = "support/test_router.rs"]
mod test_router;

const SOLVER_STACK_BYTES: usize = 256 * 1024 * 1024;

fn load(name: &str) -> VerifiableFunction {
    let path = format!("{}/tests/fixtures/{name}_mir.json", env!("CARGO_MANIFEST_DIR"));
    let text = std::fs::read_to_string(&path)
        .unwrap_or_else(|e| panic!("fixture `{name}` must be readable: {e}"));
    serde_json::from_str(&text).unwrap_or_else(|e| panic!("fixture `{name}` must deserialize: {e}"))
}

/// Every row of `func` through the PRODUCTION generation entry the compiler calls
/// (`generate_vcs_with_discharge_and_summaries_configured_with_context_and_box_deref_ops`),
/// decided by the same in-process ay backend, with the hardened profile `hardened`.
fn rows(func: VerifiableFunction, hardened: bool) -> Vec<(VcKind, VerificationResult)> {
    std::thread::Builder::new()
        .stack_size(SOLVER_STACK_BYTES)
        .spawn(move || {
            let context = trust_vcgen::VcgenContext::for_function(func.def_path.clone());
            let db = trust_vcgen::SummaryDatabase::new();
            let ops: HashSet<(BlockId, usize)> = HashSet::new();
            let (solver_vcs, preclassified) =
                trust_vcgen::generate_vcs_with_discharge_and_summaries_configured_with_context_and_box_deref_ops(
                    &func, &db, hardened, &context, &ops,
                );
            let router = test_router::deterministic_test_router();
            let decided: Vec<_> = solver_vcs
                .into_iter()
                .map(|vc| {
                    let result = router.verify_one(&vc);
                    (vc.kind, result)
                })
                .collect();
            preclassified.into_iter().map(|(vc, result)| (vc.kind, result)).chain(decided).collect()
        })
        .expect("spawn")
        .join()
        .expect("generation thread")
}

fn unreachable_rows(func: &VerifiableFunction, hardened: bool) -> Vec<VerificationResult> {
    rows(func.clone(), hardened)
        .into_iter()
        .filter(|(kind, _)| matches!(kind, VcKind::Unreachable))
        .map(|(_, result)| result)
        .collect()
}

/// Whether `result` is a refutation whose witness assigns some version of `local`
/// (`_5`, `_5#s2_1`, ...) the integer `value`.
fn refuted_with(result: &VerificationResult, local: &str, value: i128) -> bool {
    let VerificationResult::Failed { counterexample: Some(ce), .. } = result else {
        return false;
    };
    ce.assignments.iter().any(|(n, v)| {
        n.split('#').next() == Some(local)
            && matches!(v, CounterexampleValue::Int(x) if *x == value)
    })
}

/// The fixture's shape is what makes it a regression test for THIS gap: the
/// discriminant destination `_5` is NOT single-assignment (the Opaque terminator
/// disqualifies every local), so the bare-name arm of the tag fact cannot fire.
#[test]
fn fixture_shape_disqualifies_every_local_from_single_assignment() {
    let func = load("discr_domain_opaque_loop");
    assert!(
        func.body
            .blocks
            .iter()
            .any(|b| matches!(b.terminator, trust_types::Terminator::Opaque { .. })),
        "the fixture must carry the Opaque terminator that poisons single-assignment"
    );
    assert!(
        !trust_vcgen::local_defs::is_single_static_assignment(&func, 5),
        "`_5` must not be single-assignment, or this fixture exercises the bare-name arm"
    );
}

/// THE REPRO. Before the fix: `Failed`, witness `_5#s2_0 = -1`.
#[test]
fn exhaustive_result_match_in_an_opaque_loop_proves_its_unreachable_arm() {
    let func = load("discr_domain_opaque_loop");
    for hardened in [false, true] {
        let unreach = unreachable_rows(&func, hardened);
        assert_eq!(unreach.len(), 1, "one Unreachable row (hardened={hardened}): {unreach:?}");
        assert!(
            matches!(unreach[0], VerificationResult::Proved { .. }),
            "the `otherwise` arm of an exhaustive `Result` match is dead; a refutation here \
             assigns a tag no `Result` has (hardened={hardened}): {:?}",
            unreach[0]
        );
    }
}

/// CONTROL: the fact is about the VALUE the read wrote, not about the place. Write
/// `_5 = 7` right after the read (before the `SwitchInt` reads `_5`): the switch now
/// sees `7`, the `otherwise` arm is reachable, and the row must stay refuted AT 7.
#[test]
fn a_destination_overwritten_after_the_read_stays_refuted() {
    let mut func = load("discr_domain_opaque_loop");
    let bb2 = func.body.blocks.iter_mut().find(|b| b.id == BlockId(2)).expect("bb2");
    assert!(
        matches!(
            &bb2.stmts[..],
            [trust_types::Statement::Assign { place, rvalue: trust_types::Rvalue::Discriminant(_), .. }]
                if place.local == 5 && place.projections.is_empty()
        ),
        "bb2 must be exactly `_5 = Discriminant(_3)`: {:?}",
        bb2.stmts
    );
    let overwrite: trust_types::Statement = serde_json::from_value(serde_json::json!({
        "Assign": {
            "place": { "local": 5, "projections": [] },
            "rvalue": { "Use": { "Constant": { "Int": 7 } } },
            "span": { "file": "m_dyn.rs", "line_start": 13, "col_start": 14,
                      "line_end": 13, "col_end": 22 }
        }
    }))
    .expect("overwrite statement must deserialize");
    bb2.stmts.push(overwrite);
    for hardened in [false, true] {
        let unreach = unreachable_rows(&func, hardened);
        assert_eq!(unreach.len(), 1, "one Unreachable row (hardened={hardened}): {unreach:?}");
        assert!(
            refuted_with(&unreach[0], "_5", 7),
            "a switch on an overwritten `_5 = 7` REACHES `otherwise`; it must stay refuted \
             at 7 (hardened={hardened}): {:?}",
            unreach[0]
        );
    }
}

/// CONTROL: a `Result` built by `transmute` keeps the check that charges its
/// CREATION. rustc lowers the transmute with an `InvalidEnumConstruction` assert; the
/// tag fact (an assumption about a value read through a valid place) must not
/// discharge it. The `Unreachable` row of the match behind it is decided under the
/// same tag fact as the single-assignment lane: the invalid-value path is charged where the
/// value is made, not where it is read. (In this body the `Unreachable` row is
/// `Unknown` after the fix: the in-process solver gives up on the transmute's
/// unsupported cast chain. It is pinned only as NOT REFUTED.)
///
/// READ THIS TEST FOR WHAT IT IS: it FAILS without the pin (the `Unreachable` row is
/// refuted with an impossible tag), so it shows that the tag premise IS applied to a
/// transmuted value and that the cost sits on the creation row. It is not evidence
/// that an invalid value is kept out of the premise (TCB.md, "The enum tag-range
/// premise at a `Discriminant` read").
#[test]
fn a_transmuted_result_keeps_its_invalid_enum_construction_row() {
    let func = load("discr_domain_opaque_loop_transmute");
    for hardened in [false, true] {
        let rows = rows(func.clone(), hardened);
        let construction: Vec<_> = rows
            .iter()
            .filter(|(kind, _)| format!("{kind:?}").contains("InvalidEnumConstruction"))
            .collect();
        assert!(
            !construction.is_empty(),
            "the transmute's InvalidEnumConstruction row must be generated (hardened={hardened}): \
             {:?}",
            rows.iter().map(|(k, _)| format!("{k:?}")).collect::<Vec<_>>()
        );
        for (kind, result) in &construction {
            assert!(
                !matches!(result, VerificationResult::Proved { .. }),
                "the creation check of a transmuted enum must never be discharged by the read's \
                 tag fact (hardened={hardened}): {kind:?} -> {result:?}"
            );
        }
        let unreach: Vec<_> =
            rows.iter().filter(|(kind, _)| matches!(kind, VcKind::Unreachable)).collect();
        assert_eq!(unreach.len(), 1, "one Unreachable row (hardened={hardened}): {unreach:?}");
        // Before the fix this row was REFUTED with `_6#s7_1 = -1` (the same impossible
        // tag). Now the tag fact closes the domain; what remains is the in-process
        // solver's (`Unknown` at 93c27b4ab7), so only the false refutation is pinned.
        assert!(
            !matches!(unreach[0].1, VerificationResult::Failed { .. }),
            "the `otherwise` arm of the match behind the transmute must not be refuted with \
             an impossible tag (hardened={hardened}): {:?}",
            unreach[0].1
        );
        if std::env::var_os("DISCR_DOMAIN_TRACE").is_some() {
            for (kind, result) in &construction {
                eprintln!("[discr-domain] hardened={hardened} {kind:?} -> {result:?}");
            }
            eprintln!("[discr-domain] hardened={hardened} unreachable -> {:?}", unreach[0].1);
        }
    }
}

// ── An UNVERSIONED write between the read and the switch (review of 0a16a57648) ──
//
// The pin names the read's own statement-version token, `_5#s2_0`. The oracle mints
// no new token for an unlocatable write (inline asm, an `Unsupported` statement), so
// a switch placed AFTER one still reads `_5#s2_0` while `_5` may hold anything. Each
// variant below makes the `otherwise` arm genuinely reachable; the row must stay
// refuted. At 0a16a57648 (pin with no position check) all three were PROVED.
// MUTATION: drop the `stmt_dest_fact_is_version_pinnable_at` gate from
// `value_facts::discriminant_dest_establish_name` and all three fail.

fn span_json() -> serde_json::Value {
    serde_json::json!({"file": "m_dyn.rs", "line_start": 13, "col_start": 14,
                       "line_end": 13, "col_end": 22})
}

fn fixture_json() -> serde_json::Value {
    let path =
        format!("{}/tests/fixtures/discr_domain_opaque_loop_mir.json", env!("CARGO_MANIFEST_DIR"));
    serde_json::from_str(&std::fs::read_to_string(path).expect("fixture")).expect("json")
}

fn assert_unreachable_stays_refuted(func: VerifiableFunction, what: &str) {
    for hardened in [false, true] {
        let unreach = unreachable_rows(&func, hardened);
        assert_eq!(unreach.len(), 1, "{what}: one Unreachable row (hardened={hardened})");
        assert!(
            matches!(unreach[0], VerificationResult::Failed { .. }),
            "{what}: an unversioned write between the read and the switch may leave any \
             value in `_5`, so `otherwise` is reachable and must stay refuted \
             (hardened={hardened}): {:?}",
            unreach[0]
        );
    }
}

/// bb2 `_5 = Discriminant(_3)` -> `Opaque{InlineAsm}` -> bb7 `switchInt(_5)`: the
/// shape of `asm!(.., out(reg) _5)` between the read and the switch.
#[test]
fn inline_asm_between_the_read_and_the_switch_keeps_the_refutation() {
    let mut v = fixture_json();
    let blocks = v["body"]["blocks"].as_array_mut().expect("blocks");
    let switch = blocks[2]["terminator"].clone();
    blocks[2]["terminator"] = serde_json::json!(
        {"Opaque": {"kind": "InlineAsm", "targets": [7], "span": span_json()}});
    blocks.push(serde_json::json!({"id": 7, "stmts": [], "terminator": switch}));
    assert_unreachable_stays_refuted(serde_json::from_value(v).expect("func"), "asm");
}

/// bb2 `_5 = Discriminant(_3); Unsupported; switchInt(_5)`.
#[test]
fn an_unsupported_statement_after_the_read_keeps_the_refutation() {
    let mut v = fixture_json();
    v["body"]["blocks"][2]["stmts"].as_array_mut().expect("stmts").push(serde_json::json!(
        {"Unsupported": {"kind": "X", "detail": "unmodelled write", "operands": [],
                         "span": span_json()}}));
    assert_unreachable_stays_refuted(serde_json::from_value(v).expect("func"), "unsupported");
}

/// The same `Unsupported` statement with NO `Opaque` terminator in the body (bb6
/// returns): the statement alone is what makes `_5` non-single-assignment.
#[test]
fn an_unsupported_statement_alone_keeps_the_refutation() {
    let mut v = fixture_json();
    v["body"]["blocks"][6]["terminator"] = serde_json::json!("Return");
    v["body"]["blocks"][2]["stmts"].as_array_mut().expect("stmts").push(serde_json::json!(
        {"Unsupported": {"kind": "X", "detail": "unmodelled write", "operands": [],
                         "span": span_json()}}));
    assert_unreachable_stays_refuted(serde_json::from_value(v).expect("func"), "unsupported-only");
}

/// The position gate itself: the fixture's diverging `Opaque` (no successor) does not
/// disqualify the read at bb2[0]; the same `Opaque` given a successor does (its write
/// could be observed after the read — the gate does not track whether `_5` is read
/// there, so it declines); an unlocatable statement BEFORE the read in a block the
/// read cannot reach back to does not; a `&mut _5` anywhere does.
#[test]
fn the_pin_gate_is_positional() {
    use trust_vcgen::local_defs::stmt_dest_fact_is_version_pinnable_at as gate;
    let func = load("discr_domain_opaque_loop");
    assert!(gate(&func, 5, 2, 0), "a successor-free Opaque cannot be observed in the body");

    let mut v = fixture_json();
    v["body"]["blocks"][6]["terminator"] = serde_json::json!(
        {"Opaque": {"kind": "Call(indirect)", "targets": [5], "span": span_json()}});
    let f: VerifiableFunction = serde_json::from_value(v).expect("func");
    assert!(!gate(&f, 5, 2, 0), "an Opaque with a successor after the read must decline");

    // bb0 runs once, before the loop; nothing leads back to it.
    let mut v = fixture_json();
    v["body"]["blocks"][0]["stmts"].as_array_mut().expect("stmts").push(serde_json::json!(
        {"Unsupported": {"kind": "X", "detail": "before", "operands": [], "span": span_json()}}));
    let f: VerifiableFunction = serde_json::from_value(v).expect("func");
    assert!(gate(&f, 5, 2, 0), "an unlocatable write that cannot run after the read is harmless");

    // ... but inside the loop (bb1 is re-entered from bb4) it runs after the read.
    let mut v = fixture_json();
    v["body"]["blocks"][1]["stmts"].as_array_mut().expect("stmts").push(serde_json::json!(
        {"Unsupported": {"kind": "X", "detail": "loop", "operands": [], "span": span_json()}}));
    let f: VerifiableFunction = serde_json::from_value(v).expect("func");
    assert!(!gate(&f, 5, 2, 0), "an unlocatable write on the loop back path runs after the read");

    let mut v = fixture_json();
    v["body"]["locals"].as_array_mut().expect("locals").push(serde_json::json!(
        {"index": 7, "ty": {"Ref": {"mutable": true, "inner": {"Int": {"width": 64, "signed": true}}}},
         "name": null}));
    v["body"]["blocks"][5]["stmts"].as_array_mut().expect("stmts").push(serde_json::json!(
        {"Assign": {"place": {"local": 7, "projections": []},
                    "rvalue": {"Ref": {"mutable": true, "place": {"local": 5, "projections": []}}},
                    "span": span_json()}}));
    let f: VerifiableFunction = serde_json::from_value(v).expect("func");
    assert!(!gate(&f, 5, 2, 0), "a `&mut _5` anywhere refuses the pin");
}

// ── The `as usize` consumer (review finding 3, measured) ─────────────────────
//
//   discr_domain_opaque_cast_index_mir.json (main stage 1 72d80d86b, same flags):
//     #[derive(Clone, Copy)] pub enum E { A, B }
//     pub trait G { fn get(&self) -> E; }
//     pub fn idx(g: &dyn G, arr: &[u8; 2], die: fn() -> !) -> u8 {
//         let e = g.get();
//         if arr[0] == 7 { die() }
//         arr[e as usize]
//     }
//
// Main stage 1 reports `[bounds] FAILED` with `_11#s4_0 = 2` (a tag `E` does not
// have); the same function without the `die()` call proves. The diverging indirect
// call is the only reason `_11` (the Discriminant dest) and `_10` (the cast dest) are
// not single-assignment. The pinned tag fact on `_11#s4_0` reaches the bounds check
// through the modeled cast; the cast-destination fact itself is still SSA-gated.

/// Before the pin: `IndexOutOfBounds` refuted at `_11#s4_0 = 2`.
#[test]
fn an_enum_cast_index_behind_a_diverging_indirect_call_proves_its_bounds() {
    let func = load("discr_domain_opaque_cast_index");
    for hardened in [false, true] {
        let bounds: Vec<_> = rows(func.clone(), hardened)
            .into_iter()
            .filter(|(kind, _)| matches!(kind, VcKind::IndexOutOfBounds))
            .collect();
        assert!(!bounds.is_empty(), "the fixture must carry bounds rows (hardened={hardened})");
        for (kind, result) in &bounds {
            assert!(
                matches!(result, VerificationResult::Proved { .. }),
                "`arr[e as usize]` on `[u8; 2]` with `E` tags {{0, 1}} is in bounds \
                 (hardened={hardened}): {kind:?} -> {result:?}"
            );
        }
    }
}
