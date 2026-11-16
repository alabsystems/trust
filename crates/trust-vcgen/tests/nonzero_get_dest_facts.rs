// Trust: `NonZero<T>::get` call-destination non-zero fact — the REAL-ARTIFACT
// regression rows.
//
// Every `MIR_*` constant below is the compiler's OWN extracted verification
// input, captured verbatim with
//
//   trustc --edition 2021 --crate-type lib -Ztrust-dump=mir:<dir> <file>.rs
//
// against
//
//   pub fn nz_div(a: u32, d: NonZeroU32) -> u32 { a / d.get() }
//   pub fn nz_div_minus1(a: u32, d: NonZeroU32) -> u32 { a / (d.get() - 1) }
//   pub fn nz_field_ovf(d: NonZeroU32) -> u32 { d.get() + 1 }
//   pub fn nzi_sub1(d: NonZeroI32) -> i32 { d.get() - 1 }
//   pub fn nz_or_else(a: u32, d: NonZeroU32, e: u32, c: bool) -> u32 {
//       let x = if c { d.get() } else { e };
//       a / x
//   }
//
// so these are not hand-built approximations of the MIR — they are the MIR.
// The one exception is `MIR_NZ_REASSIGNED`, which is SYNTHESIZED and says so at
// its own definition, and `MIR_NZ_OR_ELSE_DEST`, which is `nz_or_else`'s capture
// with one localized edit that its own definition spells out.
// They are embedded INLINE rather than dropped in `tests/fixtures/` on purpose:
// a corpus-derived obligation count is ratcheted elsewhere and this lane must
// not perturb it.
//
// WHAT IS BEING PINNED. `ty_convert` lowers `NonZero<T>`'s wrapped field
// `pattern_type!(T is 1..)` to the bare carrier `T`, and `get` reaches the body
// as an opaque `Terminator::Call`, so the divisor local is a free integer and
// `a / d.get()` was refuted at `d.get() == 0` — a value the type cannot hold.
// `build_nonzero_get_dest_facts` restores `dest != 0`.
//
// The three negative rows are what keep the fact from becoming a false-proof
// engine, and each is killed by a different mutant of the builder (recorded in
// each test's own doc): a same-named USER function must not be assumed
// non-zero, a longer method tail must not match, and the fact must be `!= 0`
// rather than `>= 1` because `NonZero<T>` is generic over the SIGNED integers
// too.

use trust_types::{VcKind, VerifiableFunction, VerificationResult};

#[path = "support/test_router.rs"]
mod test_router;

const MIR_NZ_DIV: &str = r#"{"name":"nz_div","def_path":"probes::nz_div","span":{"file":"probes.rs","line_start":17,"col_start":0,"line_end":17,"col_end":59},"body":{"locals":[{"index":0,"ty":{"Int":{"width":32,"signed":false}},"name":null},{"index":1,"ty":{"Int":{"width":32,"signed":false}},"name":"a"},{"index":2,"ty":{"Adt":{"name":"core::num::nonzero::NonZero","fields":[["0",{"Adt":{"name":"core::num::niche_types::NonZeroU32Inner","fields":[["0",{"Int":{"width":32,"signed":false}}]],"variants":[],"disc_index_safe":false,"faithful_enum_repr":null,"layout":null,"enum_layout":null,"adt_kind":"Struct"}}]],"variants":[],"disc_index_safe":false,"faithful_enum_repr":null,"layout":null,"enum_layout":null,"adt_kind":"Struct"}},"name":"d"},{"index":3,"ty":{"Int":{"width":32,"signed":false}},"name":null},{"index":4,"ty":"Bool","name":null}],"blocks":[{"id":0,"stmts":[],"terminator":{"Call":{"func":"core::num::nonzero::NonZero::<u32>::get","args":[{"Copy":{"local":2,"projections":[]}}],"dest":{"local":3,"projections":[]},"target":1,"span":{"file":"probes.rs","line_start":17,"col_start":52,"line_end":17,"col_end":52},"atomic":null,"is_foreign":false,"is_unsafe_sig":false,"unwind":"Continue"}}},{"id":1,"stmts":[{"Assign":{"place":{"local":4,"projections":[]},"rvalue":{"BinaryOp":["Eq",{"Copy":{"local":3,"projections":[]}},{"Constant":{"Uint":[0,32]}}]},"span":{"file":"probes.rs","line_start":17,"col_start":46,"line_end":17,"col_end":46}}}],"terminator":{"Assert":{"cond":{"Move":{"local":4,"projections":[]}},"expected":false,"msg":"DivisionByZero","target":2,"span":{"file":"probes.rs","line_start":17,"col_start":46,"line_end":17,"col_end":46},"unwind":"Continue"}}},{"id":2,"stmts":[{"Assign":{"place":{"local":0,"projections":[]},"rvalue":{"BinaryOp":["Div",{"Copy":{"local":1,"projections":[]}},{"Copy":{"local":3,"projections":[]}}]},"span":{"file":"probes.rs","line_start":17,"col_start":46,"line_end":17,"col_end":46}}}],"terminator":"Return"}],"arg_count":2,"return_ty":{"Int":{"width":32,"signed":false}}},"contracts":[],"preconditions":[{"And":[{"Ge":[{"Var":["a","Int"]},{"Int":0}]},{"Le":[{"Var":["a","Int"]},{"Int":4294967295}]}]}],"postconditions":[],"spec":{"requires":[],"ensures":[],"invariants":[]}}"#;

const MIR_NZ_DIV_MINUS1: &str = r#"{"name":"nz_div_minus1","def_path":"probes::nz_div_minus1","span":{"file":"probes.rs","line_start":26,"col_start":0,"line_end":26,"col_end":72},"body":{"locals":[{"index":0,"ty":{"Int":{"width":32,"signed":false}},"name":null},{"index":1,"ty":{"Int":{"width":32,"signed":false}},"name":"a"},{"index":2,"ty":{"Adt":{"name":"core::num::nonzero::NonZero","fields":[["0",{"Adt":{"name":"core::num::niche_types::NonZeroU32Inner","fields":[["0",{"Int":{"width":32,"signed":false}}]],"variants":[],"disc_index_safe":false,"faithful_enum_repr":null,"layout":null,"enum_layout":null,"adt_kind":"Struct"}}]],"variants":[],"disc_index_safe":false,"faithful_enum_repr":null,"layout":null,"enum_layout":null,"adt_kind":"Struct"}},"name":"d"},{"index":3,"ty":{"Int":{"width":32,"signed":false}},"name":null},{"index":4,"ty":{"Tuple":[{"Int":{"width":32,"signed":false}},"Bool"]},"name":null},{"index":5,"ty":"Bool","name":null}],"blocks":[{"id":0,"stmts":[],"terminator":{"Call":{"func":"core::num::nonzero::NonZero::<u32>::get","args":[{"Copy":{"local":2,"projections":[]}}],"dest":{"local":3,"projections":[]},"target":1,"span":{"file":"probes.rs","line_start":26,"col_start":60,"line_end":26,"col_end":60},"atomic":null,"is_foreign":false,"is_unsafe_sig":false,"unwind":"Continue"}}},{"id":1,"stmts":[{"Assign":{"place":{"local":4,"projections":[]},"rvalue":{"CheckedBinaryOp":["Sub",{"Copy":{"local":3,"projections":[]}},{"Constant":{"Uint":[1,32]}}]},"span":{"file":"probes.rs","line_start":26,"col_start":57,"line_end":26,"col_end":57}}}],"terminator":{"Assert":{"cond":{"Move":{"local":4,"projections":[{"Field":1}]}},"expected":false,"msg":{"Overflow":"Sub"},"target":2,"span":{"file":"probes.rs","line_start":26,"col_start":57,"line_end":26,"col_end":57},"unwind":"Continue"}}},{"id":2,"stmts":[{"Assign":{"place":{"local":5,"projections":[]},"rvalue":{"BinaryOp":["Eq",{"Copy":{"local":4,"projections":[{"Field":0}]}},{"Constant":{"Uint":[0,32]}}]},"span":{"file":"probes.rs","line_start":26,"col_start":53,"line_end":26,"col_end":53}}}],"terminator":{"Assert":{"cond":{"Move":{"local":5,"projections":[]}},"expected":false,"msg":"DivisionByZero","target":3,"span":{"file":"probes.rs","line_start":26,"col_start":53,"line_end":26,"col_end":53},"unwind":"Continue"}}},{"id":3,"stmts":[{"Assign":{"place":{"local":0,"projections":[]},"rvalue":{"BinaryOp":["Div",{"Copy":{"local":1,"projections":[]}},{"Copy":{"local":4,"projections":[{"Field":0}]}}]},"span":{"file":"probes.rs","line_start":26,"col_start":53,"line_end":26,"col_end":53}}}],"terminator":"Return"}],"arg_count":2,"return_ty":{"Int":{"width":32,"signed":false}}},"contracts":[],"preconditions":[{"And":[{"Ge":[{"Var":["a","Int"]},{"Int":0}]},{"Le":[{"Var":["a","Int"]},{"Int":4294967295}]}]}],"postconditions":[],"spec":{"requires":[],"ensures":[],"invariants":[]}}"#;

const MIR_NZ_FIELD_OVF: &str = r#"{"name":"nz_field_ovf","def_path":"probes::nz_field_ovf","span":{"file":"probes.rs","line_start":27,"col_start":0,"line_end":27,"col_end":57},"body":{"locals":[{"index":0,"ty":{"Int":{"width":32,"signed":false}},"name":null},{"index":1,"ty":{"Adt":{"name":"core::num::nonzero::NonZero","fields":[["0",{"Adt":{"name":"core::num::niche_types::NonZeroU32Inner","fields":[["0",{"Int":{"width":32,"signed":false}}]],"variants":[],"disc_index_safe":false,"faithful_enum_repr":null,"layout":null,"enum_layout":null,"adt_kind":"Struct"}}]],"variants":[],"disc_index_safe":false,"faithful_enum_repr":null,"layout":null,"enum_layout":null,"adt_kind":"Struct"}},"name":"d"},{"index":2,"ty":{"Int":{"width":32,"signed":false}},"name":null},{"index":3,"ty":{"Tuple":[{"Int":{"width":32,"signed":false}},"Bool"]},"name":null}],"blocks":[{"id":0,"stmts":[],"terminator":{"Call":{"func":"core::num::nonzero::NonZero::<u32>::get","args":[{"Copy":{"local":1,"projections":[]}}],"dest":{"local":2,"projections":[]},"target":1,"span":{"file":"probes.rs","line_start":27,"col_start":46,"line_end":27,"col_end":46},"atomic":null,"is_foreign":false,"is_unsafe_sig":false,"unwind":"Continue"}}},{"id":1,"stmts":[{"Assign":{"place":{"local":3,"projections":[]},"rvalue":{"CheckedBinaryOp":["Add",{"Copy":{"local":2,"projections":[]}},{"Constant":{"Uint":[1,32]}}]},"span":{"file":"probes.rs","line_start":27,"col_start":44,"line_end":27,"col_end":44}}}],"terminator":{"Assert":{"cond":{"Move":{"local":3,"projections":[{"Field":1}]}},"expected":false,"msg":{"Overflow":"Add"},"target":2,"span":{"file":"probes.rs","line_start":27,"col_start":44,"line_end":27,"col_end":44},"unwind":"Continue"}}},{"id":2,"stmts":[{"Assign":{"place":{"local":0,"projections":[]},"rvalue":{"Use":{"Copy":{"local":3,"projections":[{"Field":0}]}}},"span":{"file":"probes.rs","line_start":27,"col_start":57,"line_end":27,"col_end":57}}}],"terminator":"Return"}],"arg_count":1,"return_ty":{"Int":{"width":32,"signed":false}}},"contracts":[],"preconditions":[],"postconditions":[],"spec":{"requires":[],"ensures":[],"invariants":[]}}"#;

const MIR_NZI_SUB1: &str = r#"{"name":"nzi_sub1","def_path":"probes2::nzi_sub1","span":{"file":"probes2.rs","line_start":4,"col_start":0,"line_end":4,"col_end":53},"body":{"locals":[{"index":0,"ty":{"Int":{"width":32,"signed":true}},"name":null},{"index":1,"ty":{"Adt":{"name":"core::num::nonzero::NonZero","fields":[["0",{"Adt":{"name":"core::num::niche_types::NonZeroI32Inner","fields":[["0",{"Int":{"width":32,"signed":true}}]],"variants":[],"disc_index_safe":false,"faithful_enum_repr":null,"layout":null,"enum_layout":null,"adt_kind":"Struct"}}]],"variants":[],"disc_index_safe":false,"faithful_enum_repr":null,"layout":null,"enum_layout":null,"adt_kind":"Struct"}},"name":"d"},{"index":2,"ty":{"Int":{"width":32,"signed":true}},"name":null},{"index":3,"ty":{"Tuple":[{"Int":{"width":32,"signed":true}},"Bool"]},"name":null}],"blocks":[{"id":0,"stmts":[],"terminator":{"Call":{"func":"core::num::nonzero::NonZero::<i32>::get","args":[{"Copy":{"local":1,"projections":[]}}],"dest":{"local":2,"projections":[]},"target":1,"span":{"file":"probes2.rs","line_start":4,"col_start":42,"line_end":4,"col_end":42},"atomic":null,"is_foreign":false,"is_unsafe_sig":false,"unwind":"Continue"}}},{"id":1,"stmts":[{"Assign":{"place":{"local":3,"projections":[]},"rvalue":{"CheckedBinaryOp":["Sub",{"Copy":{"local":2,"projections":[]}},{"Constant":{"Int":1}}]},"span":{"file":"probes2.rs","line_start":4,"col_start":40,"line_end":4,"col_end":40}}}],"terminator":{"Assert":{"cond":{"Move":{"local":3,"projections":[{"Field":1}]}},"expected":false,"msg":{"Overflow":"Sub"},"target":2,"span":{"file":"probes2.rs","line_start":4,"col_start":40,"line_end":4,"col_end":40},"unwind":"Continue"}}},{"id":2,"stmts":[{"Assign":{"place":{"local":0,"projections":[]},"rvalue":{"Use":{"Copy":{"local":3,"projections":[{"Field":0}]}}},"span":{"file":"probes2.rs","line_start":4,"col_start":53,"line_end":4,"col_end":53}}}],"terminator":"Return"}],"arg_count":1,"return_ty":{"Int":{"width":32,"signed":true}}},"contracts":[],"preconditions":[],"postconditions":[],"spec":{"requires":[],"ensures":[],"invariants":[]}}"#;

/// One verdict per VC, from the REAL in-process ay backend, on a big stack (VC
/// generation and the solver search both overflow libtest's default stack).
fn verdicts(mir: &str) -> Vec<(VcKind, VerificationResult, bool)> {
    let func: VerifiableFunction =
        serde_json::from_str(mir).expect("the captured MIR fixture must deserialize");
    std::thread::Builder::new()
        .stack_size(32 * 1024 * 1024)
        .spawn(move || {
            let vcs = trust_vcgen::generate_vcs(&func);
            let router = test_router::deterministic_test_router();
            router
                .verify_all(&vcs)
                .into_iter()
                .map(|(vc, r)| {
                    let certified = trust_certify::certify_vc(&vc).is_some();
                    (vc.kind, r, certified)
                })
                .collect::<Vec<_>>()
        })
        .expect("spawn solver thread")
        .join()
        .expect("solver thread must not panic")
}

fn rows_of(mir: &str, want: fn(&VcKind) -> bool) -> Vec<(VerificationResult, bool)> {
    let rows: Vec<_> = verdicts(mir)
        .into_iter()
        .filter(|(kind, _, _)| want(kind))
        .map(|(_, r, c)| (r, c))
        .collect();
    assert!(!rows.is_empty(), "the obligation this row is about must be generated at all");
    rows
}

fn is_proved(r: &VerificationResult) -> bool {
    matches!(r, VerificationResult::Proved { .. })
}

fn is_divzero(k: &VcKind) -> bool {
    matches!(k, VcKind::DivisionByZero | VcKind::RemainderByZero)
}

/// The row that carries the divisor's zero-check when the divisor is the return of a
/// call the `get` recognizer does NOT bless.
///
/// Such a divisor is a free variable, and a row of that shape is now emitted as
/// `UnsupportedMir { kind: "UnmodeledCalleeReturn" }` and DECLINED rather than kept as
/// `DivisionByZero` and refuted on a model no execution can produce. The obligation is
/// still emitted and still accounted for; its KIND moved. Both kinds are matched here so
/// the assertion keeps its DENOMINATOR: a change that emits NOTHING for this statement
/// trips `rows_of`'s non-empty check instead of passing vacuously.
fn divisor_rows(mir: &str) -> Vec<(VerificationResult, bool)> {
    rows_of(mir, |k| {
        is_divzero(k)
            || matches!(k, VcKind::UnsupportedMir { kind, .. } if kind == "UnmodeledCalleeReturn")
    })
}

fn is_sub_overflow(k: &VcKind) -> bool {
    matches!(k, VcKind::ArithmeticOverflow { op: trust_types::BinOp::Sub, .. })
}

fn is_add_overflow(k: &VcKind) -> bool {
    matches!(k, VcKind::ArithmeticOverflow { op: trust_types::BinOp::Add, .. })
}

/// Rewrite the callee path of every `Call` in the captured MIR. Used by the
/// negative rows to vary the ONE input the recognizer keys on while holding the
/// rest of the body byte-identical.
fn with_callee(mir: &str, from: &str, to: &str) -> String {
    assert!(mir.contains(from), "the captured MIR must contain the callee being rewritten");
    mir.replace(from, to)
}

const NZ_GET_U32: &str = "core::num::nonzero::NonZero::<u32>::get";

// ── the rows that must be PROVED ────────────────────────────────────────────

/// `a / d.get()` on `d: NonZeroU32` divides by a value the type cannot hold as
/// zero, so no execution of it can fault.
///
/// Killed by the NO-OP mutant (`build_nonzero_get_dest_facts` returning an
/// empty vector), which returns this row to `Failed { _3 = 0 }`, and by the
/// INVERTED mutant (`dest == 0`), which refutes it for the opposite reason.
#[test]
fn nonzero_get_divisor_is_proved_and_kernel_certified() {
    for (verdict, certified) in rows_of(MIR_NZ_DIV, is_divzero) {
        assert!(
            is_proved(&verdict) && certified,
            "a / d.get() on NonZeroU32 cannot divide by zero; got {verdict:?} certified={certified}"
        );
    }
}

/// `d.get() - 1` cannot underflow: `!= 0` plus the destination's own unsigned
/// type range gives `>= 1`, and `1 - 1 == 0` is the worst case. Killed by the
/// NO-OP and INVERTED mutants.
#[test]
fn nonzero_get_minus_one_cannot_underflow() {
    for (verdict, certified) in rows_of(MIR_NZ_DIV_MINUS1, is_sub_overflow) {
        assert!(
            is_proved(&verdict) && certified,
            "d.get() - 1 on NonZeroU32 cannot underflow; got {verdict:?} certified={certified}"
        );
    }
}

// ── the rows that must STILL be refuted ─────────────────────────────────────

/// `a / (d.get() - 1)` CAN divide by zero — `d.get() == 1` is a legal
/// `NonZeroU32` and makes the divisor `0`. Killed by the INVERTED mutant, which
/// makes the divisor provably zero and so proves the obligation vacuously.
#[test]
fn nonzero_get_minus_one_divisor_still_refutes() {
    for (verdict, _) in rows_of(MIR_NZ_DIV_MINUS1, is_divzero) {
        assert!(!is_proved(&verdict), "a / (d.get() - 1) divides by zero at d == 1");
    }
}

/// `d.get() + 1` CAN overflow — `u32::MAX` is a legal `NonZeroU32`. Killed by
/// the INVERTED mutant.
#[test]
fn overflow_on_the_unwrapped_value_still_refutes() {
    for (verdict, _) in rows_of(MIR_NZ_FIELD_OVF, is_add_overflow) {
        assert!(!is_proved(&verdict), "d.get() + 1 overflows at d == u32::MAX");
    }
}

/// THE SIGNED ROW, and the reason the fact is `!= 0` and not `>= 1`:
/// `NonZero<T>` is generic over the signed integers, so `NonZeroI32::get()` can
/// be `i32::MIN` and `d.get() - 1` genuinely underflows.
///
/// Killed by the OVER-EAGER mutant that emits `dest >= 1` instead of
/// `dest != 0`: that mutant proves this row, which is a FALSE PROOF — the
/// program faults at `i32::MIN`.
#[test]
fn signed_nonzero_get_is_not_bounded_below_by_one() {
    for (verdict, _) in rows_of(MIR_NZI_SUB1, is_sub_overflow) {
        assert!(!is_proved(&verdict), "NonZeroI32::get() - 1 underflows at i32::MIN");
    }
}

/// A user function that happens to be spelled `NonZero::get` carries no
/// validity invariant the verifier may assume. Same body, same arity, same
/// destination — only the crate root differs.
///
/// Killed by the OVER-EAGER mutant that drops the `is_nonzero_get_call` gate
/// and mints the fact for every one-argument call: that mutant PROVES this row,
/// which would assume an arbitrary user function never returns zero.
#[test]
fn a_user_crate_get_is_not_assumed_non_zero() {
    let mir = with_callee(MIR_NZ_DIV, NZ_GET_U32, "mycrate::num::nonzero::NonZero::<u32>::get");
    for (verdict, _) in divisor_rows(&mir) {
        assert!(!is_proved(&verdict), "a user-crate `get` must leave the divisor free");
    }
}

/// The method tail is matched EXACTLY, so a longer sibling does not inherit the
/// fact. Killed by the same drop-the-recognizer OVER-EAGER mutant.
#[test]
fn a_longer_method_tail_is_not_assumed_non_zero() {
    let mir =
        with_callee(MIR_NZ_DIV, NZ_GET_U32, "core::num::nonzero::NonZero::<u32>::get_unchecked");
    for (verdict, _) in divisor_rows(&mir) {
        assert!(!is_proved(&verdict), "only the exact `get` tail carries the fact");
    }
}

// ── the reassigned-DESTINATION rows (the single-assignment gate) ─────────────
//
// `is_single_static_assignment(dest)` in `build_nonzero_get_dest_facts` is what
// keeps the fact from binding a value the `get` call never produced. The two
// fixtures below are the two ways a destination local acquires a second
// definition — a straight-line reassignment and a branch merge — and each is a
// program that GENUINELY FAULTS, so a PROVED verdict on it is a false proof, not
// merely a vacuous one.
//
// Both are killed by mutant M4: replace the gate with
// `if false && !is_single_static_assignment(func, dest.local)`. Under M4 BOTH
// divzero rows of BOTH fixtures come back `Proved` + kernel-certified. The
// mechanism is spelled out on `build_nonzero_get_dest_facts`: the global fact is
// conjoined into `vc.formula` BEFORE the whole-formula version rename, so it is
// renamed in lockstep and binds the block's TERMINAL version of the dest —
// contradicting the divisor-is-zero path condition and emptying the path.
//
// `nonzero_get_single_assignment_dest_is_still_proved` is the paired control: the
// SAME fixture with the reassignment statement deleted and nothing else changed.
// It must be PROVED, which is what makes the two refutation rows above
// non-vacuous — they refute because of the gate, not because the fixture failed
// to reach the recognizer at all.

/// SYNTHESIZED (the only fixture in this file that is not a capture): the MIR of
///
///   let mut x = d.get();
///   x = e;
///   a / x
///
/// with the `get` destination and `x` as the SAME local `_4`. Real rustc gives
/// `x` its own local and copy-propagates, so the capture of that source has a
/// single-assignment (and dead) call dest; this fixture is that source's MIR with
/// the copy step collapsed. `a / x` is `a / e`, which faults at `e == 0`.
const MIR_NZ_REASSIGNED: &str = r#"{"name":"nz_reassigned","def_path":"probes::nz_reassigned","span":{"file":"probes.rs","line_start":1,"col_start":0,"line_end":1,"col_end":1},"body":{"locals":[{"index":0,"ty":{"Int":{"width":32,"signed":false}},"name":null},{"index":1,"ty":{"Int":{"width":32,"signed":false}},"name":"a"},{"index":2,"ty":{"Adt":{"name":"core::num::nonzero::NonZero","fields":[["0",{"Adt":{"name":"core::num::niche_types::NonZeroU32Inner","fields":[["0",{"Int":{"width":32,"signed":false}}]],"variants":[],"disc_index_safe":false,"faithful_enum_repr":null,"layout":null,"enum_layout":null,"adt_kind":"Struct"}}]],"variants":[],"disc_index_safe":false,"faithful_enum_repr":null,"layout":null,"enum_layout":null,"adt_kind":"Struct"}},"name":"d"},{"index":3,"ty":{"Int":{"width":32,"signed":false}},"name":"e"},{"index":4,"ty":{"Int":{"width":32,"signed":false}},"name":null},{"index":5,"ty":"Bool","name":null}],"blocks":[{"id":0,"stmts":[],"terminator":{"Call":{"func":"core::num::nonzero::NonZero::<u32>::get","args":[{"Copy":{"local":2,"projections":[]}}],"dest":{"local":4,"projections":[]},"target":1,"span":{"file":"probes.rs","line_start":2,"col_start":1,"line_end":2,"col_end":1},"atomic":null,"is_foreign":false,"is_unsafe_sig":false,"unwind":"Continue"}}},{"id":1,"stmts":[{"Assign":{"place":{"local":4,"projections":[]},"rvalue":{"Use":{"Copy":{"local":3,"projections":[]}}},"span":{"file":"probes.rs","line_start":3,"col_start":1,"line_end":3,"col_end":1}}}],"terminator":{"Goto":2}},{"id":2,"stmts":[{"Assign":{"place":{"local":5,"projections":[]},"rvalue":{"BinaryOp":["Eq",{"Copy":{"local":4,"projections":[]}},{"Constant":{"Uint":[0,32]}}]},"span":{"file":"probes.rs","line_start":4,"col_start":1,"line_end":4,"col_end":1}}}],"terminator":{"Assert":{"cond":{"Move":{"local":5,"projections":[]}},"expected":false,"msg":"DivisionByZero","target":3,"span":{"file":"probes.rs","line_start":4,"col_start":1,"line_end":4,"col_end":1},"unwind":"Continue"}}},{"id":3,"stmts":[{"Assign":{"place":{"local":0,"projections":[]},"rvalue":{"BinaryOp":["Div",{"Copy":{"local":1,"projections":[]}},{"Copy":{"local":4,"projections":[]}}]},"span":{"file":"probes.rs","line_start":4,"col_start":1,"line_end":4,"col_end":1}}}],"terminator":"Return"}],"arg_count":3,"return_ty":{"Int":{"width":32,"signed":false}}},"contracts":[],"preconditions":[{"And":[{"Ge":[{"Var":["a","Int"]},{"Int":0}]},{"Le":[{"Var":["a","Int"]},{"Int":4294967295}]}]},{"And":[{"Ge":[{"Var":["e","Int"]},{"Int":0}]},{"Le":[{"Var":["e","Int"]},{"Int":4294967295}]}]}],"postconditions":[],"spec":{"requires":[],"ensures":[],"invariants":[]}}"#;

/// The reassignment statement of [`MIR_NZ_REASSIGNED`], verbatim, so a test can
/// strip it and get the single-assignment control.
const NZ_REASSIGN_STMT: &str = r#"{"Assign":{"place":{"local":4,"projections":[]},"rvalue":{"Use":{"Copy":{"local":3,"projections":[]}}},"span":{"file":"probes.rs","line_start":3,"col_start":1,"line_end":3,"col_end":1}}}"#;

/// `nz_or_else`'s CAPTURED MIR with one edit: the `get` call writes DIRECTLY into
/// the merged local `_5` (instead of a temp `_6`) and the now-redundant
/// `_5 = _6` copy in block 4 is dropped. Same program — `x` is `e` on the
/// `c == false` arm, so `a / x` faults at `c == false, e == 0` — with the call
/// destination now carrying a second definition (block 2's `_5 = e`).
const MIR_NZ_OR_ELSE_DEST: &str = r#"{"name":"nz_or_else_dest","def_path":"probe_arm::nz_or_else_dest","span":{"file":"probe_arm.rs","line_start":4,"col_start":0,"line_end":7,"col_end":1},"body":{"locals":[{"index":0,"ty":{"Int":{"width":32,"signed":false}},"name":null},{"index":1,"ty":{"Int":{"width":32,"signed":false}},"name":"a"},{"index":2,"ty":{"Adt":{"name":"core::num::nonzero::NonZero","fields":[["0",{"Adt":{"name":"core::num::niche_types::NonZeroU32Inner","fields":[["0",{"Int":{"width":32,"signed":false}}]],"variants":[],"disc_index_safe":false,"faithful_enum_repr":null,"layout":null,"enum_layout":null,"adt_kind":"Struct"}}]],"variants":[],"disc_index_safe":false,"faithful_enum_repr":null,"layout":null,"enum_layout":null,"adt_kind":"Struct"}},"name":"d"},{"index":3,"ty":{"Int":{"width":32,"signed":false}},"name":"e"},{"index":4,"ty":"Bool","name":"c"},{"index":5,"ty":{"Int":{"width":32,"signed":false}},"name":null},{"index":6,"ty":{"Int":{"width":32,"signed":false}},"name":null},{"index":7,"ty":"Bool","name":null}],"blocks":[{"id":0,"stmts":[],"terminator":{"SwitchInt":{"discr":{"Copy":{"local":4,"projections":[]}},"targets":[[0,2]],"otherwise":1,"exhaustive_enum_unreachable":false,"span":{"file":"probe_arm.rs","line_start":5,"col_start":12,"line_end":5,"col_end":12}}}},{"id":1,"stmts":[],"terminator":{"Call":{"func":"core::num::nonzero::NonZero::<u32>::get","args":[{"Copy":{"local":2,"projections":[]}}],"dest":{"local":5,"projections":[]},"target":4,"span":{"file":"probe_arm.rs","line_start":5,"col_start":21,"line_end":5,"col_end":21},"atomic":null,"is_foreign":false,"is_unsafe_sig":false,"unwind":"Continue"}}},{"id":2,"stmts":[{"Assign":{"place":{"local":5,"projections":[]},"rvalue":{"Use":{"Copy":{"local":3,"projections":[]}}},"span":{"file":"probe_arm.rs","line_start":5,"col_start":12,"line_end":5,"col_end":12}}}],"terminator":{"Goto":3}},{"id":3,"stmts":[{"Assign":{"place":{"local":7,"projections":[]},"rvalue":{"BinaryOp":["Eq",{"Copy":{"local":5,"projections":[]}},{"Constant":{"Uint":[0,32]}}]},"span":{"file":"probe_arm.rs","line_start":6,"col_start":4,"line_end":6,"col_end":4}}}],"terminator":{"Assert":{"cond":{"Move":{"local":7,"projections":[]}},"expected":false,"msg":"DivisionByZero","target":5,"span":{"file":"probe_arm.rs","line_start":6,"col_start":4,"line_end":6,"col_end":4},"unwind":"Continue"}}},{"id":4,"stmts":[],"terminator":{"Goto":3}},{"id":5,"stmts":[{"Assign":{"place":{"local":0,"projections":[]},"rvalue":{"BinaryOp":["Div",{"Copy":{"local":1,"projections":[]}},{"Copy":{"local":5,"projections":[]}}]},"span":{"file":"probe_arm.rs","line_start":6,"col_start":4,"line_end":6,"col_end":4}}}],"terminator":"Return"}],"arg_count":4,"return_ty":{"Int":{"width":32,"signed":false}}},"contracts":[],"preconditions":[{"And":[{"Ge":[{"Var":["a","Int"]},{"Int":0}]},{"Le":[{"Var":["a","Int"]},{"Int":4294967295}]}]},{"And":[{"Ge":[{"Var":["e","Int"]},{"Int":0}]},{"Le":[{"Var":["e","Int"]},{"Int":4294967295}]}]}],"postconditions":[],"spec":{"requires":[],"ensures":[],"invariants":[]}}"#;

/// A reassigned destination must NOT inherit the non-zero fact. `x = e` overwrites
/// the unwrapped value, and `a / x` divides by zero at `e == 0`.
///
/// At least one divzero row must refute; the second row of this fixture is the
/// `Div` itself, which the passing `DivisionByZero` assert legitimately dominates.
/// RED under M4 — both rows go Proved + certified.
#[test]
fn nonzero_get_reassigned_dest_still_refutes() {
    let rows = rows_of(MIR_NZ_REASSIGNED, is_divzero);
    assert!(
        rows.iter().any(|(verdict, _)| !is_proved(verdict)),
        "`x = d.get(); x = e; a / x` divides by zero at e == 0; got {rows:?}"
    );
}

/// The branch-merge twin: the destination's second definition is on the OTHER arm
/// rather than after it. RED under M4.
#[test]
fn nonzero_get_branch_merged_dest_still_refutes() {
    let rows = rows_of(MIR_NZ_OR_ELSE_DEST, is_divzero);
    assert!(
        rows.iter().any(|(verdict, _)| !is_proved(verdict)),
        "`if c {{ d.get() }} else {{ e }}` divides by zero at c == false, e == 0; got {rows:?}"
    );
}

/// The control for the two rows above: [`MIR_NZ_REASSIGNED`] with the ONE
/// reassignment statement deleted and nothing else touched, i.e.
/// `let x = d.get(); a / x`. Its destination is single-assignment, so the fact IS
/// emitted and every divzero row proves.
///
/// Killed by the NO-OP mutant (an empty fact vector). If this row ever stops
/// proving, the two refutation rows above have stopped testing the gate.
#[test]
fn nonzero_get_single_assignment_dest_is_still_proved() {
    let mir = MIR_NZ_REASSIGNED.replace(NZ_REASSIGN_STMT, "");
    assert!(mir.contains(r#""stmts":[],"terminator":{"Goto":2}"#), "the strip must land");
    for (verdict, certified) in rows_of(&mir, is_divzero) {
        assert!(
            is_proved(&verdict) && certified,
            "`let x = d.get(); a / x` cannot divide by zero; got {verdict:?} certified={certified}"
        );
    }
}
