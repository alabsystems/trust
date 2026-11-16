// Trust (2026-10-11, VC-NARROW-CAST-FALSE-REFUTE-1): a strictly narrowing int->int
// cast was a FREE value of the target type in the block definitions — only
// `narrowing_cast_result_range`'s `0 <= dest <= 255` was emitted, nothing tied `dest`
// to the source — so a lossless cast under a guard (`arr[x as u8 as usize]` under
// `x < 0x80`, `TABLE[c as u8 as usize]` under `c.is_ascii()`) was refuted at
// `dest = 128`. Measured on the stage 1 of `1213387e6d` (`scratchpad/stage1-w24probe`,
// `tests/ui/trust/narrowing_cast_in_range_identity.rs`): every `holds` function is
// refused with `[bounds] FAILED (trust-full-verifier); counterexample:
// verified_counterexample = true`, or `[overflow:add]` / `[shift:left] FAILED
// (ay-in-process)` "UNGROUNDED". `guards.rs` now also emits
// `narrowing_cast_in_range_identity`: `(to_min <= src <= to_max) => dest == src` (for an
// unsigned source, `src <= to_max => dest == src`).
//
// The fixtures are REAL extracted MIR (`-Ztrust-dump=mir-only:<dir>
// -Ztrust-policy=advisory --edition 2021 --crate-type lib`, the stage 1 of
// `1213387e6d`) of `fixtures/narrowing_cast_identity/{narrow_holds,narrow_liars}.rs`,
// one function per file, spans rewritten to `<dump-root>/`. The extractor is not
// touched by this fix. Every `holds` test FAILS BEFORE (its row is refuted on the
// free cast value); the liars pin that the identity proves nothing false: each
// liar panics for some input, and `st1`..`st3` rewrite the cast's source before the
// guard reads it, so an identity bound to a LATER value would prove them. Oracle
// (stock rustc 1.97.1, `scratchpad/scout24/D/oracle/oracle.rs`): no `holds`
// function panics over its input domain (exhaustively for `char`, `u16`, and
// `0..0x20000` plus extremes for the wider types); every liar panics at its witness
// (`l1(0x80)`, `l2(0x7f)`, `l3(0x80)`, `st1(200)`, `st2(&[200, 5])`, `st3(200, 1)`,
// `add_l(0x81)`, `shl_l(0x20)`).
use trust_types::*;
use trust_vcgen::generate_vcs;

#[path = "support/test_router.rs"]
mod test_router;

fn load(name: &str) -> VerifiableFunction {
    let path = format!(
        "{}/tests/fixtures/narrowing_cast_identity/{name}.json",
        env!("CARGO_MANIFEST_DIR")
    );
    let json = std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("{path}: {e}"));
    serde_json::from_str(&json).expect("fixture MIR must deserialize")
}

fn router() -> trust_router::Router {
    test_router::deterministic_test_router()
}

/// Every narrowing int->int cast in the body, as `(source ty, target ty)` — the
/// fixture premise (the bug needs one).
fn narrowing_casts(func: &VerifiableFunction) -> Vec<(Ty, Ty)> {
    let mut out = Vec::new();
    for block in &func.body.blocks {
        for stmt in &block.stmts {
            if let Statement::Assign { rvalue: Rvalue::Cast(op, to_ty), .. } = stmt
                && let Operand::Copy(p) | Operand::Move(p) = op
                && let Some(Ty::Int { width: sw, .. }) =
                    func.body.locals.get(p.local).map(|d| &d.ty)
                && p.projections.is_empty()
                && let Ty::Int { width: dw, .. } = to_ty
                && dw < sw
            {
                out.push((func.body.locals[p.local].ty.clone(), to_ty.clone()));
            }
        }
    }
    out
}

/// The safety rows the compiler reported for these functions: the array bounds
/// check, the `+` overflow and the `<<` overflow.
fn is_safety_row(kind: &VcKind) -> bool {
    matches!(
        kind,
        VcKind::IndexOutOfBounds
            | VcKind::SliceBoundsCheck
            | VcKind::ArithmeticOverflow { .. }
            | VcKind::ShiftOverflow { .. }
    )
}

fn verdicts(func: &VerifiableFunction) -> Vec<(VcKind, VerificationResult)> {
    let vcs: Vec<VerificationCondition> =
        generate_vcs(func).into_iter().filter(|vc| is_safety_row(&vc.kind)).collect();
    router().verify_all(&vcs).into_iter().map(|(vc, r)| (vc.kind.clone(), r)).collect()
}

/// `add_edge` is `(x as u8) + 0x7f` under `x <= 0x80`: `0x80 + 0x7f == 0xff` fits, so
/// the identity's bound is exact at the 8-bit edge (its twin `add_l`, `x <= 0x81`,
/// overflows and is a liar).
const HOLDS: [&str; 12] =
    ["a6", "b1", "n1", "n2", "n4", "n6", "i16n", "i8n", "us8", "add_u8", "shl_u8", "add_edge"];

const LIARS: [&str; 8] = ["l1", "l2", "l3", "st1", "st2", "st3", "add_l", "shl_l"];

/// FAILS BEFORE: with the cast result free in `[0, 2^w - 1]`, each of these rows is
/// refuted at a value the guard excludes from the source.
#[test]
fn a_lossless_narrowing_cast_under_its_guard_proves() {
    let mut unproved = Vec::new();
    for name in HOLDS {
        let func = load(name);
        assert!(!narrowing_casts(&func).is_empty(), "{name}: fixture premise (a narrowing cast)");
        let v = verdicts(&func);
        assert!(!v.is_empty(), "{name}: fixture premise (a safety row)");
        for (kind, r) in v {
            if !matches!(r, VerificationResult::Proved { .. }) {
                unproved.push(format!("{name}: {kind:?} -> {r:?}"));
            }
        }
    }
    assert!(
        unproved.is_empty(),
        "the guard keeps each cast source in its target type, so every row must PROVE; \
         unproved:\n{}",
        unproved.join("\n")
    );
}

/// Each liar panics for some input; the identity must never prove one.
#[test]
fn a_narrowing_cast_liar_stays_unproved() {
    for name in LIARS {
        let func = load(name);
        assert!(!narrowing_casts(&func).is_empty(), "{name}: fixture premise (a narrowing cast)");
        let v = verdicts(&func);
        assert!(
            v.iter().any(|(_, r)| !matches!(r, VerificationResult::Proved { .. })),
            "{name} panics for some input; a safety row must stay unproved, got {v:?}"
        );
    }
}

/// The row each liar's panic is: the index for the `l*`/`st*` liars, the `u8` add for
/// `add_l`, the shift for `shl_l`. (A liar's OTHER rows may be genuinely safe: `st3`'s
/// `i += 1` under `i < n` cannot overflow, and is proved and kernel-certified.)
fn is_panicking_row(name: &str, kind: &VcKind) -> bool {
    match name {
        "add_l" => matches!(kind, VcKind::ArithmeticOverflow { op: BinOp::Add, .. }),
        "shl_l" => matches!(kind, VcKind::ShiftOverflow { .. }),
        _ => matches!(kind, VcKind::IndexOutOfBounds),
    }
}

/// Every liar's panicking row stays REFUTED, not merely unknown, and is never
/// kernel-certified (the `certify` lane): the boundary liars (`l1`..`l3`, `add_l`,
/// `shl_l`) and the staleness liars (`st1`..`st3`).
#[test]
fn every_liar_stays_refuted() {
    for name in LIARS {
        let func = load(name);
        let rows: Vec<VerificationCondition> =
            generate_vcs(&func).into_iter().filter(|vc| is_panicking_row(name, &vc.kind)).collect();
        assert!(!rows.is_empty(), "{name}: fixture premise (its panicking row)");
        for (vc, r) in router().verify_all(&rows) {
            assert!(
                matches!(r, VerificationResult::Failed { .. }),
                "{name}: the panic is reachable; `{:?}` must stay REFUTED, got {r:?}",
                vc.kind
            );
            assert!(
                trust_certify::certify_vc(&vc).is_none(),
                "{name}: the panicking `{:?}` row was kernel-certified",
                vc.kind
            );
        }
    }
}

/// The unsigned-source holds are kernel-certified (`trust_certify::certify_vc`, the
/// lane `-Ztrust-policy=certify` reads): their identity's antecedent is the single
/// `src <= to_max` atom `discharge_entailed_implications` takes by modus ponens. FAILS
/// BEFORE (refuted, so nothing to certify) and with the two-atom antecedent on an
/// unsigned source (measured: no row certified). The signed-source holds `i16n` and
/// `i8n` need both bounds and are proved by SMT only (KNOWN_HAZARDS
/// VC-NARROW-CAST-FALSE-REFUTE-1, a residual).
#[test]
fn an_unsigned_source_hold_is_kernel_certified() {
    let mut uncertified = Vec::new();
    for name in HOLDS.iter().filter(|n| !matches!(**n, "i16n" | "i8n")) {
        for vc in generate_vcs(&load(name)).iter().filter(|vc| is_safety_row(&vc.kind)) {
            if trust_certify::certify_vc(vc).is_none() {
                uncertified.push(format!("{name}: {:?}", vc.kind));
            }
        }
    }
    assert!(uncertified.is_empty(), "not kernel-certified:\n{}", uncertified.join("\n"));
}

/// UNION-SIBLING-WRITE-1 (wave-24 review of this fix, 2026-10-12): a union's fields
/// overlap, so a write to `u.1` rewrites `u.0`. The place-name algebra took them for
/// disjoint storage, and the identity above (`x <= 255 => u.0 == x`) survived the write
/// of `u.1`: on the stage 1 of `51eac007f3`, advisory, `u_dst_add`'s `overflow:add` row
/// was kernel-certified and its check ELIDED (the binary printed 71 where rustc panics),
/// and `u_dst_idx` / `u_src_idx` read PROVED. The widening twins `uw_dst_add` /
/// `uw_src_add` (a widening cast's `dest == src`) were elided the same way before this
/// fix too. Fixtures: `narrow_union_liars.rs`, dumped like the others by the stage 1
/// of `51eac007f3` (`scratchpad/stage1-w24`). Each liar panics at the witness its
/// source names (stock rustc 1.97.1).
/// Which row of a liar is its panic.
type PanickingRow = fn(&VcKind) -> bool;

const UNION_LIARS: [(&str, PanickingRow); 5] = [
    ("u_dst_add", |k| matches!(k, VcKind::ArithmeticOverflow { op: BinOp::Add, .. })),
    ("u_dst_idx", |k| matches!(k, VcKind::IndexOutOfBounds)),
    ("u_src_idx", |k| matches!(k, VcKind::IndexOutOfBounds)),
    ("uw_dst_add", |k| matches!(k, VcKind::ArithmeticOverflow { op: BinOp::Add, .. })),
    ("uw_src_add", |k| matches!(k, VcKind::ArithmeticOverflow { op: BinOp::Add, .. })),
];

/// The panicking row of every union liar is neither PROVED nor kernel-certified, on
/// the formula path (`generate_vcs` and the in-process ay router) and on the entry the
/// compiler drives (`generate_vcs_with_discharge`: a row the interval pre-pass
/// discharges never reaches the solver). FAILS BEFORE: `u_dst_add`, `u_dst_idx`,
/// `u_src_idx`, `uw_dst_add` and `uw_src_add` proved.
#[test]
fn a_union_sibling_write_liar_is_never_proved() {
    let mut bad = Vec::new();
    for (name, panicking) in UNION_LIARS {
        let func = load(name);
        let rows: Vec<VerificationCondition> =
            generate_vcs(&func).into_iter().filter(|vc| panicking(&vc.kind)).collect();
        assert!(!rows.is_empty(), "{name}: fixture premise (its panicking row)");
        for (vc, r) in router().verify_all(&rows) {
            if matches!(r, VerificationResult::Proved { .. }) {
                bad.push(format!("{name}: {:?} PROVED", vc.kind));
            }
            if trust_certify::certify_vc(&vc).is_some() {
                bad.push(format!("{name}: {:?} kernel-certified", vc.kind));
            }
        }
        let (to_solve, discharged) = trust_vcgen::generate_vcs_with_discharge(&func);
        for (vc, r) in discharged.iter().filter(|(vc, _)| panicking(&vc.kind)) {
            bad.push(format!("{name}: {:?} discharged by the interval pre-pass: {r:?}", vc.kind));
        }
        let solve: Vec<VerificationCondition> =
            to_solve.into_iter().filter(|vc| panicking(&vc.kind)).collect();
        for (vc, r) in router().verify_all(&solve) {
            if matches!(r, VerificationResult::Proved { .. }) {
                bad.push(format!("{name}: {:?} PROVED on the discharge entry", vc.kind));
            }
        }
    }
    assert!(bad.is_empty(), "union sibling-write liars proved:\n{}", bad.join("\n"));
}

/// The control: with no sibling write, `u.a = x as u8` under `x < 0x80` still proves
/// `u.a + 0x7f` (the union cover rebinds the siblings of a write, never the value the
/// write itself defines).
#[test]
fn a_union_field_write_without_a_sibling_write_still_proves() {
    let func = load("u_dst_add_ctl");
    let v = verdicts(&func);
    assert!(!v.is_empty(), "fixture premise (a safety row)");
    for (kind, r) in v {
        assert!(matches!(r, VerificationResult::Proved { .. }), "{kind:?} -> {r:?}");
    }
}
