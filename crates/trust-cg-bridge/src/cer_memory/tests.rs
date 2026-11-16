use ay::{Logic, Solver};
use trust_disasm::decode_aarch64;
use trust_machine_sem::{Aarch64Semantics, ConcreteState, Effect, MachineState, Semantics};

use super::*;

fn var(name: &str) -> Formula {
    Formula::Var(name.into(), Sort::BitVec(64))
}
fn val(n: u64, bits: u32) -> Formula {
    Formula::BitVec { value: i128::from(n), width: bits }
}
fn access(kind: AccessKind, address: Formula, bytes: u32) -> PathAccess {
    PathAccess::new(kind, Formula::Bool(true), address, bytes).unwrap()
}
fn assert_valid(formula: &Formula, valid: bool) {
    // Diagnostic AY checks, NOT kernel certificates or output grades. Use the
    // actual production Formula translator, including its failure behavior.
    let mut solver = Solver::try_new(Logic::QfAbv).unwrap();
    let term = crate::verify_output::formula_to_term(&mut solver, formula).unwrap();
    let neg = solver.try_not(term).unwrap();
    solver.try_assert_term(neg).unwrap();
    let answer = solver.check_sat();
    assert!(if valid { answer.is_unsat() } else { answer.is_sat() }, "{answer:?}");
}
fn obligations_valid(terms: &[PendingMemoryObligation], valid: bool) {
    assert_valid(&and(terms.iter().map(|t| t.formula.clone()).collect()), valid);
}
fn at(address: &Formula, memory: &Formula) -> Formula {
    Formula::Select(b(memory.clone()), b(address.clone()))
}
fn frame() -> PrivateFrame {
    PrivateFrame::new(bv(0x8000), 32).unwrap()
}
fn query() -> Formula {
    var("fresh_exit_byte")
}
fn obligation(source: &Formula, machine: &Formula) -> PendingMemoryObligation {
    outside_memory_equal(&Formula::Bool(true), source, machine, &query(), &frame()).unwrap()
}

/// Replay actual AArch64 bytes through the production decoder/effects and both
/// symbolic/concrete executors. Dropping STRB changes no return bits.
fn replay(words: &[u32]) -> (MachineState, ConcreteState, Vec<PathAccess>) {
    let mut symbolic = MachineState::symbolic();
    symbolic.memory = shared_entry_memory("dropped-store");
    symbolic.gpr[0] = bv(0x1000);
    symbolic.gpr[1] = bv(1);
    let mut concrete = ConcreteState::new();
    concrete.gpr[0] = 0x1000;
    concrete.gpr[1] = 1;
    concrete.sp = 0x8000;
    concrete.store_memory_le(0x1000, 1, 0).unwrap();
    let mut accesses = Vec::new();
    for (i, word) in words.iter().enumerate() {
        let decoded = decode_aarch64(&word.to_le_bytes(), (i * 4) as u64).unwrap();
        let effects = Aarch64Semantics.effects(&symbolic, &decoded).unwrap();
        for effect in &effects {
            match effect {
                Effect::MemWrite { address, width_bytes, .. } => {
                    accesses.push(access(AccessKind::Write, address.clone(), *width_bytes))
                }
                Effect::MemRead { address, width_bytes } => {
                    accesses.push(access(AccessKind::Read, address.clone(), *width_bytes))
                }
                _ => {}
            }
        }
        symbolic.apply_effects(&effects).unwrap();
        for effect in &effects {
            if let Effect::Return { target } = effect {
                // ConcreteState deliberately leaves control flow to a driver.
                // Handle only the final decoded RET, evaluating its real target;
                // every memory effect above is still replayed without filtering.
                assert_eq!(*word, 0xd65f_03c0);
                assert_eq!(i + 1, words.len());
                concrete.pc = concrete.eval_bv(target, 64).unwrap() as u64;
            } else {
                concrete.apply_effect(effect).unwrap();
            }
        }
    }
    (symbolic, concrete, accesses)
}

#[test]
fn dropped_store_in_actual_bytes_preserves_return_but_fails_exit_memory() {
    // strb w1,[x0]; mov w0,#0; ret. Mutant deletes only STRB.
    let (good, concrete_good, machine_accesses) = replay(&[0x3900_0001, 0x5280_0000, 0xd65f_03c0]);
    let (bad, concrete_bad, _) = replay(&[0x5280_0000, 0xd65f_03c0]);
    let initial = shared_entry_memory("dropped-store");
    let source = store_le(initial.clone(), &bv(0x1000), &val(1, 8), 1).unwrap();
    let source_access = [access(AccessKind::Write, bv(0x1000), 1)];
    assert_valid(&eq(good.read_gpr(0, 32), bad.read_gpr(0, 32)), true);
    assert_eq!(concrete_good.gpr[0], concrete_bad.gpr[0]);
    assert_eq!(concrete_good.load_memory_le(0x1000, 1).unwrap(), 1);
    assert_eq!(concrete_bad.load_memory_le(0x1000, 1).unwrap(), 0);
    obligations_valid(&frame_separation(&source_access, &frame()), true);
    obligations_valid(&coverage(&source_access, &machine_accesses), true);
    assert_valid(&obligation(&source, &good.memory).formula, true);
    // Constructive legal disjoint witness: one initialized incoming byte,
    // outside the frame, initially zero. O6 distinguishes this from return-only.
    let witness = and(vec![eq(query(), bv(0x1000)), eq(at(&bv(0x1000), &initial), val(0, 8))]);
    assert_valid(&implies(witness, obligation(&source, &bad.memory).formula), false);
    assert_eq!(
        obligation(&source, &bad.memory).counterexample_use,
        CounterexampleUse::RequiresLegalDisjointWitness
    );
}

#[test]
fn wrong_store_offset_width_and_value_do_not_pass_exit_memory() {
    let mem = shared_entry_memory("mutants");
    let p = bv(0x1000);
    let source = store_le(mem.clone(), &p, &val(0x1234, 16), 2).unwrap();
    let mutants = [
        store_le(mem.clone(), &bv(0x1001), &val(0x1234, 16), 2).unwrap(),
        store_le(mem.clone(), &p, &val(0x34, 8), 1).unwrap(),
        store_le(mem.clone(), &p, &val(0x1235, 16), 2).unwrap(),
    ];
    for machine in mutants {
        assert_valid(&obligation(&source, &machine).formula, false);
    }
}

#[test]
fn reordered_and_merged_accesses_use_byte_coverage_not_pairing() {
    let p = bv(0x1000);
    let mem = shared_entry_memory("reordered");
    let source = store_le(
        store_le(mem.clone(), &p, &val(0x34, 8), 1).unwrap(),
        &byte_at(&p, 1),
        &val(0x12, 8),
        1,
    )
    .unwrap();
    let reordered = store_le(
        store_le(mem.clone(), &byte_at(&p, 1), &val(0x12, 8), 1).unwrap(),
        &p,
        &val(0x34, 8),
        1,
    )
    .unwrap();
    let merged = store_le(mem, &p, &val(0x1234, 16), 2).unwrap();
    let source_accesses =
        [access(AccessKind::Write, p.clone(), 1), access(AccessKind::Write, byte_at(&p, 1), 1)];
    let machine_accesses =
        [access(AccessKind::Write, p.clone(), 2), access(AccessKind::Read, p, 2)];
    obligations_valid(&coverage(&source_accesses, &machine_accesses), true);
    assert_valid(&obligation(&source, &reordered).formula, true);
    assert_valid(&obligation(&source, &merged).formula, true);
    assert_valid(&eq(load_le(&source, &bv(0x1000), 2).unwrap(), val(0x1234, 16)), true);
}

#[test]
fn extra_load_and_read_only_source_cannot_cover_machine_store() {
    let p = bv(0x1000);
    let extra = coverage(&[], &[access(AccessKind::Read, p.clone(), 1)]);
    obligations_valid(&extra, false);
    assert!(extra.iter().all(|t| t.counterexample_use == CounterexampleUse::Inconclusive));
    obligations_valid(
        &coverage(&[access(AccessKind::Read, p.clone(), 1)], &[access(AccessKind::Write, p, 1)]),
        false,
    );
}

#[test]
fn source_access_on_wrong_path_cannot_supply_coverage() {
    let taken = Formula::Var("taken".into(), Sort::Bool);
    let source = PathAccess::new(AccessKind::Write, taken.clone(), bv(0x1000), 1).unwrap();
    let opposite =
        PathAccess::new(AccessKind::Write, Formula::Not(b(taken)), bv(0x1000), 1).unwrap();
    obligations_valid(&coverage(&[source], &[opposite]), false);
    let dead = PathAccess::new(AccessKind::Write, Formula::Bool(false), bv(0x1000), 1).unwrap();
    obligations_valid(&coverage(&[], &[dead]), true);
}

#[test]
fn frame_separation_is_explicit_and_covers_every_byte() {
    // First byte is outside, second byte enters the private frame.
    let crossing = access(AccessKind::Write, bv(0x7fdf), 2);
    obligations_valid(&frame_separation(&[crossing], &frame()), false);
    obligations_valid(
        &frame_separation(&[access(AccessKind::Write, bv(0x1000), 8)], &frame()),
        true,
    );
    let wrapping = PrivateFrame::new(bv(16), 32).unwrap();
    assert_valid(&wrapping.well_formed(), false);
    let initial = shared_entry_memory("frame");
    let inside = store_le(initial.clone(), &bv(0x7ff0), &val(1, 8), 1).unwrap();
    // O6 alone deliberately ignores own frame: M1′ must not be omitted.
    assert_valid(&obligation(&inside, &initial).formula, true);
    obligations_valid(
        &frame_separation(&[access(AccessKind::Write, bv(0x7ff0), 1)], &frame()),
        false,
    );
}

#[test]
fn shared_call_memory_detects_cached_pre_call_value() {
    let before = shared_entry_memory("calls");
    let after = shared_post_call_memory("calls", 7);
    assert_ne!(before, after);
    assert_eq!(after, shared_post_call_memory("calls", 7));
    assert_ne!(after, shared_post_call_memory("calls", 8));
    let p = bv(0x1000);
    let cached = load_le(&before, &p, 1).unwrap();
    let reloaded = load_le(&after, &p, 1).unwrap();
    // Callee writes one byte. Fresh post-call memory is shared, not equated
    // to pre-call memory. Reusing the old value is demonstrably wrong.
    let witness = and(vec![eq(at(&p, &before), val(0, 8)), eq(at(&p, &after), val(1, 8))]);
    assert_valid(&implies(witness, eq(cached, reloaded)), false);
    assert_valid(
        &outside_memory_equal(&Formula::Bool(true), &before, &after, &query(), &frame())
            .unwrap()
            .formula,
        false,
    );
}

#[test]
fn alias_only_counterexample_requires_a_legal_disjoint_witness() {
    let mem = shared_entry_memory("alias");
    let p = var("p");
    let q = var("q");
    let source =
        store_le(store_le(mem.clone(), &p, &val(1, 8), 1).unwrap(), &q, &val(2, 8), 1).unwrap();
    let machine = store_le(store_le(mem, &q, &val(2, 8), 1).unwrap(), &p, &val(1, 8), 1).unwrap();
    let obligation = obligation(&source, &machine);
    assert_valid(&obligation.formula, false);
    assert_valid(&implies(Formula::Not(b(eq(p, q))), obligation.formula), true);
    assert_eq!(obligation.counterexample_use, CounterexampleUse::RequiresLegalDisjointWitness);
}

#[test]
fn invalid_sorts_widths_and_silent_truncation_are_rejected() {
    let mem = shared_entry_memory("invalid");
    for bytes in [0, 9, u32::MAX] {
        assert!(load_le(&mem, &bv(0x1000), bytes).is_err());
        assert!(PathAccess::new(AccessKind::Read, Formula::Bool(true), bv(0x1000), bytes).is_err());
    }
    assert!(store_le(mem.clone(), &bv(0x1000), &val(1, 64), 1).is_err());
    assert!(load_le(&mem, &val(0x1000, 32), 1).is_err());
    assert!(load_le(&bv(0), &bv(0x1000), 1).is_err());
    assert!(PathAccess::new(AccessKind::Read, bv(1), bv(0x1000), 1).is_err());
    assert!(outside_memory_equal(&Formula::Bool(true), &mem, &mem, &val(0, 32), &frame()).is_err());
    assert!(outside_memory_equal(&Formula::Bool(true), &mem, &mem, &bv(0x1000), &frame()).is_err());
    let contaminated = store_le(mem.clone(), &query(), &val(1, 8), 1).unwrap();
    assert!(
        outside_memory_equal(&Formula::Bool(true), &contaminated, &mem, &query(), &frame())
            .is_err()
    );
}
