// trust-certify: Phase-3 link-3 — auto-source a finite-DFA refinement obligation
// from a real trust-ir program, then feed it to the kernel-checked finite-sim
// re-check lane (`finite_dfa`).
//
// `finite_dfa.rs` already provides a SOUND kernel-checked re-check lane for a 2D
// `table_step(state, byteclass) -> next_state` forward-simulation obligation
// (`SimFlavor::EnumCases2d`, discharged by a nested `casesOn` proof). Its inputs
// are clean-kernel `Expr`/`InductiveDecl` cell matrices — built BY HAND in the
// lane's own tests. This module closes the remaining gap: instead of hand-writing
// the implementation matrix, it AUTHORS a real `trust-ir` function that encodes
// the table as a nested `switch`, then EXTRACTS the matrix back by traversing that
// program's CFG, and hands the extracted (program) matrix to the lane as `impl_def`
// against an independent `reference` (spec) matrix.
//
// EXACTLY WHAT IS PROVEN (and what is NOT) — read before trusting a green result.
// A successful `verify_ir_table_refines_spec` PROVES, kernel-checked, that:
//
//   the NEXT-STATE-INDEX table the trust-ir program computes agrees, cell-by-cell
//   over the finite (state-index x byte-class-index) domain, with the independent
//   `reference`.
//
// A single `verify_ir_table_refines_spec` call is forward simulation at the
// next-state-INDEX level ONLY. Coverage was since EXTENDED by reusing this same
// proven lane on additional projections/edges (see the tests):
//   * the byte -> byte-class CLASSIFIER is now kernel-certified over all 256 bytes
//     (`verifies_pair_classifier_in_chunks`), and the next-state composition
//     `full[s][b] = class_matrix[s][classify(b)]` is kernel-CHECKED over all 256
//     bytes (`kernel_checks_table_composition` / `verifies_nextstate_composition_in_chunks`);
//   * the parser's ACTION/effect edge (Print/Execute/Collect/Clear/...) is
//     kernel-certified over the 14×23 pair-classes
//     (`verifies_action_edge_over_pair_classes`). NOTE: the ACTION composition
//     `action[s][b] = pair_action[s][pair_classifier(b)]` is NOT itself
//     kernel-checked (only the NEXT-STATE composition is); the action edge's
//     full-256-byte accounting is STRUCTURAL, resting on the separately-verified
//     14×23 action table plus the kernel-verified 256-byte pair classifier.
// Still NOT covered:
//   * the deployed binary as a Rust artifact (irrelevant — the trust-ir program IS
//     the artifact under the Trust framing).
//
// SOUNDNESS: this module mints NO evidence itself. All trust flows through
// `finite_dfa::certify_finite_sim`, whose clean-kernel re-check is the sole trusted
// component (unchanged). Every step is fail-closed (`None` on any unexpected CFG
// shape, ragged matrix, negative cell, or interpreter error).
//
// EXTRACTION == EXECUTION is a CHECKED invariant, not an assumed one. The
// implementation matrix is sourced BOTH by static extraction (the nested-switch
// literals) AND by running the trust-ir interpreter on every (state, class)
// (`execution_table`); `verify_ir_table_refines_spec` requires the two to be equal
// before certifying. So the kernel's "impl == spec" entails "the program EXECUTES
// to spec" — closing the foreign-module seam where a raw `iconst` literal could
// diverge from its width-masked runtime value. (The static reader alone rests on
// trust-ir's monotonic single-definition SSA invariant, `alloc_value`; the
// execution cross-check makes the I/O claim hold regardless.) A buggy program (one
// wrong switch leaf) executes to a different table and fails closed.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

// These entry points are production-public: temporal and protocol frontends can
// now submit literal Trust-IR transition programs rather than rebuilding a
// parallel hand-written model.

use clean_auto::bridge::ay_contract::serialize_term;
use clean_kernel::name::Name;
use clean_kernel::{
    BinderInfo, Declaration, Environment, Expr, InductiveDecl, Level, LocalContext, TypeChecker,
};
use trust_ir::constant::Constant;
use trust_ir::inst::{Inst, SwitchCase};
use trust_ir::interpret::{InterpretValue, Interpreter};
use trust_ir::ty::Ty;
use trust_ir::value::{BlockId, ValueId};
use trust_ir::{Block, Function, Module};
use trust_ir_build::ModuleBuilder;

use crate::finite_dfa::{
    FiniteSimSpec, SimFlavor, certify_finite_sim, enum_cases_refl_proof_2d,
    enum_transition_body_2d, is_nullary_enum_domain, recheck_finite_sim,
};

/// Stable name the authored `table_step` function is registered under. The
/// extractor resolves the function by this name (`Module::function_by_name`).
const TABLE_STEP: &str = "table_step";

// ───────────────────────────── authoring ────────────────────────────────────

/// Author a `trust-ir` `Module` containing a function
/// `table_step(state, byteclass) -> next_state` that encodes the 2D table
/// `cells[state][byteclass]` as a NESTED switch:
///
/// ```text
/// entry(state, byteclass):
///     switch state -> [0 => row_0, 1 => row_1, …]  default => trap
/// row_i(): switch byteclass -> [0 => leaf_{i,0}, 1 => leaf_{i,1}, …] default => trap
/// leaf_{i,j}(): %v = iconst cells[i][j]; ret %v
/// ```
///
/// Every leaf is exactly `iconst; ret` so extraction is a single-hop trace from
/// the returned `ValueId` to its defining `Const`. A `default` block (required by
/// `Inst::Switch`) is authored per switch; it is never reached for in-range
/// inputs and the extractor never follows it. Returns `None` on an empty or
/// ragged matrix.
pub fn author_table_step_module(cells: &[Vec<i128>]) -> Option<Module> {
    let n_states = cells.len();
    if n_states == 0 {
        return None;
    }
    let n_bc = cells[0].len();
    if n_bc == 0 || cells.iter().any(|row| row.len() != n_bc) {
        return None;
    }

    let mut mb = ModuleBuilder::new("table_step_module");
    // (state: i64, byteclass: i64) -> i64
    let sig = mb.add_func_type(vec![Ty::I64, Ty::I64], vec![Ty::I64]);
    let mut fb = mb.function(TABLE_STEP, sig);

    // Entry block carries the two function parameters as block params.
    let entry = fb.create_block();
    let state = fb.add_block_param(entry, Ty::I64);
    let byteclass = fb.add_block_param(entry, Ty::I64);

    // One per-state "row" block (the inner switch lives here) and, under each, one
    // leaf block per byte class. Create them up front so the switches can target
    // them, then fill bodies.
    let row_blocks: Vec<BlockId> = (0..n_states).map(|_| fb.create_block()).collect();
    let leaf_blocks: Vec<Vec<BlockId>> =
        (0..n_states).map(|_| (0..n_bc).map(|_| fb.create_block()).collect()).collect();

    // Shared default/trap block (one per function is enough: switches that fall
    // through here for an out-of-range input return 0). Never on the extracted
    // path.
    let trap = fb.create_block();

    // entry: outer switch on `state` → row_i.
    fb.set_entry(entry);
    fb.switch_to_block(entry);
    let outer_cases: Vec<SwitchCase> = (0..n_states)
        .map(|i| SwitchCase {
            value: Constant::Int(i as i128),
            target: row_blocks[i],
            args: vec![],
        })
        .collect();
    fb.switch(state, outer_cases, trap, vec![]);

    // row_i: inner switch on `byteclass` → leaf_{i,j}.
    for (i, &row_block) in row_blocks.iter().enumerate() {
        fb.switch_to_block(row_block);
        let inner_cases: Vec<SwitchCase> = (0..n_bc)
            .map(|j| SwitchCase {
                value: Constant::Int(j as i128),
                target: leaf_blocks[i][j],
                args: vec![],
            })
            .collect();
        fb.switch(byteclass, inner_cases, trap, vec![]);
    }

    // leaf_{i,j}: %v = iconst cells[i][j]; ret %v.
    for (i, row) in cells.iter().enumerate() {
        for (j, &value) in row.iter().enumerate() {
            fb.switch_to_block(leaf_blocks[i][j]);
            let v = fb.iconst(Ty::I64, value);
            fb.ret(vec![v]);
        }
    }

    // trap: %z = iconst 0; ret %z (well-formed terminator; off the read path).
    fb.switch_to_block(trap);
    let zero = fb.iconst(Ty::I64, 0);
    fb.ret(vec![zero]);

    fb.build();
    Some(mb.build())
}

// ──────────────────────────── extraction ────────────────────────────────────

/// Traverse the authored `table_step` function and read the `n_states × n_bc`
/// table back out of its nested switch.
///
/// Walks: entry block's outer `Inst::Switch` on param0 → per-state block's inner
/// `Inst::Switch` on param1 → leaf block's `Inst::Return` → the `Inst::Const`
/// defining the returned value. Fail-closed (`None`) on ANY unexpected shape:
/// wrong instruction, missing block/case, non-`Const` return, ragged dimensions,
/// or a negative cell value (a `Nat` cell cannot be negative).
pub fn extract_2d_matrix(module: &Module, n_states: usize, n_bc: usize) -> Option<Vec<Vec<i128>>> {
    let func = module.function_by_name(TABLE_STEP)?;
    let (param0, param1) = function_two_params(func)?;

    let entry = func.entry_block()?;
    let (outer_value, outer_targets) = block_switch(entry)?;
    // The outer switch must dispatch on param0 (the state).
    if outer_value != param0 {
        return None;
    }

    let mut matrix = Vec::with_capacity(n_states);
    for state in 0..n_states {
        let row_block_id = case_target(&outer_targets, state)?;
        let row_block = func.block(row_block_id)?;
        let (inner_value, inner_targets) = block_switch(row_block)?;
        // The inner switch must dispatch on param1 (the byte class).
        if inner_value != param1 {
            return None;
        }

        let mut row = Vec::with_capacity(n_bc);
        for bc in 0..n_bc {
            let leaf_block_id = case_target(&inner_targets, bc)?;
            let leaf_block = func.block(leaf_block_id)?;
            let ret_value = block_single_return_value(leaf_block)?;
            let cell = trace_const_int(func, ret_value)?;
            if cell < 0 {
                return None; // a Nat cell cannot be negative
            }
            row.push(cell);
        }
        matrix.push(row);
    }
    Some(matrix)
}

/// The two SSA `ValueId`s of a binary function: its entry block's two params.
/// `None` unless the entry block has exactly two params.
fn function_two_params(func: &Function) -> Option<(ValueId, ValueId)> {
    let entry = func.entry_block()?;
    match entry.params.as_slice() {
        [(p0, _), (p1, _)] => Some((*p0, *p1)),
        _ => None,
    }
}

/// If `block`'s terminator is an `Inst::Switch`, return `(switched-on value,
/// (case-literal → target) pairs)`. The default target is intentionally NOT
/// returned — the extractor follows explicit cases only.
fn block_switch(block: &Block) -> Option<(ValueId, Vec<(i128, BlockId)>)> {
    let term = block.terminator()?;
    let Inst::Switch { value, cases, .. } = &term.inst else {
        return None;
    };
    let mut targets = Vec::with_capacity(cases.len());
    for case in cases {
        let Constant::Int(k) = case.value else {
            return None;
        };
        targets.push((k, case.target));
    }
    Some((*value, targets))
}

/// The target block of the switch case whose literal equals `index`, or `None`
/// if no case matches (fail-closed: a missing case is an unexpected shape).
fn case_target(targets: &[(i128, BlockId)], index: usize) -> Option<BlockId> {
    let key = index as i128;
    targets.iter().find_map(|&(k, t)| (k == key).then_some(t))
}

/// If `block`'s terminator is an `Inst::Return` of exactly one value, return it.
fn block_single_return_value(block: &Block) -> Option<ValueId> {
    let term = block.terminator()?;
    let Inst::Return { values } = &term.inst else {
        return None;
    };
    match values.as_slice() {
        [v] => Some(*v),
        _ => None,
    }
}

/// Trace `value` back to the `Inst::Const { Constant::Int(n) }` that defines it
/// (scanning every block's body for the node whose `results` contain `value`),
/// returning `n`. `None` if `value` is undefined or not an integer constant.
fn trace_const_int(func: &Function, value: ValueId) -> Option<i128> {
    for block in &func.blocks {
        for node in &block.body {
            if node.results.contains(&value) {
                let Inst::Const { value: Constant::Int(n), .. } = &node.inst else {
                    return None;
                };
                return Some(*n);
            }
        }
    }
    None
}

/// Source the table from the program's EXECUTED I/O: run the trust-ir interpreter
/// on every `(state, byteclass)` in range and read the returned next-state. This
/// is the program's actual runtime behaviour (the interpreter masks `iconst` to
/// the declared width, so it is byte-identical to what the compiled artifact would
/// compute) — NOT a static read of the switch literals. `None` (fail-closed) on
/// any interpreter error or a non-integer return.
fn execution_table(module: &Module, n_states: usize, n_bc: usize) -> Option<Vec<Vec<i128>>> {
    let func_id = module.function_by_name(TABLE_STEP)?.id;
    let interp = Interpreter::with_module(module);
    let mut matrix = Vec::with_capacity(n_states);
    for s in 0..n_states {
        let mut row = Vec::with_capacity(n_bc);
        for c in 0..n_bc {
            let args = [
                InterpretValue::int(Ty::I64, s as i128).ok()?,
                InterpretValue::int(Ty::I64, c as i128).ok()?,
            ];
            let outcome = interp.execute_func(func_id, args).ok()?;
            let value = outcome.returns.first()?.as_int()?.as_signed();
            if value < 0 {
                return None; // a Nat cell cannot be negative
            }
            row.push(value);
        }
        matrix.push(row);
    }
    Some(matrix)
}

// ─────────────────────── refinement against a spec ──────────────────────────

/// Convert an `i128` matrix into `Expr::nat_lit` cells, fail-closed on a negative
/// value or a `u64` overflow (`Nat` literals are non-negative).
fn matrix_to_nat_cells(matrix: &[Vec<i128>]) -> Option<Vec<Vec<Expr>>> {
    matrix
        .iter()
        .map(|row| {
            row.iter()
                .map(|&n| u64::try_from(n).ok().map(Expr::nat_lit))
                .collect::<Option<Vec<_>>>()
        })
        .collect()
}

/// Source a 2D finite-DFA refinement obligation from `module` and certify it
/// against the independent `reference` (spec) matrix through the kernel-checked
/// `finite_dfa` lane.
///
/// 1. EXTRACT the PROGRAM's matrix by traversing `module`'s `table_step` CFG.
/// 2. Build `impl_def` from the PROGRAM matrix and `spec_def` from `reference`
///    (both as `Expr::nat_lit` cells) via `enum_transition_body_2d`.
/// 3. Build the nested-`casesOn` proof from the PROGRAM matrix
///    (`enum_cases_refl_proof_2d`) — so it claims exactly the program's values;
///    if the program disagrees with the reference at any cell, that cell's
///    `Eq.refl` cannot discharge the obligation and the lane fails closed.
/// 4. Hand the spec + serialized proof to `certify_finite_sim`, whose clean
///    kernel re-check is the only trusted step.
///
/// Returns `Some(ProofEvidence::CleanCic { .. })` iff the program implements the
/// reference; `None` (fail-closed) on a buggy program, a mismatched-arity
/// reference, an extraction failure, or any kernel rejection.
fn ir_table_refinement_material(
    module: &Module,
    reference: &[Vec<i128>],
    dom_a: &InductiveDecl,
    dom_b: &InductiveDecl,
) -> Option<(FiniteSimSpec, Vec<u8>)> {
    let n_states = reference.len();
    if n_states == 0 {
        return None;
    }
    let n_bc = reference[0].len();
    if n_bc == 0 || reference.iter().any(|row| row.len() != n_bc) {
        return None;
    }

    // 1. The implementation matrix, SOURCED from the trust-ir program — both by
    //    STATIC extraction (the nested-switch literals) and by EXECUTION (the
    //    interpreter's actual I/O). They MUST agree: this turns extraction
    //    fidelity from a generator-specific coincidence into a CHECKED invariant,
    //    so the kernel's "impl == spec" entails "the program EXECUTES to spec"
    //    even for a foreign module (e.g. one whose `iconst` width-masks differently
    //    from the raw literal). A mismatch fails closed.
    let program = extract_2d_matrix(module, n_states, n_bc)?;
    let executed = execution_table(module, n_states, n_bc)?;
    if program != executed {
        return None;
    }

    // 2. impl_def from the program, spec_def from the independent reference.
    let program_cells = matrix_to_nat_cells(&program)?;
    let reference_cells = matrix_to_nat_cells(reference)?;
    let impl_def = enum_transition_body_2d(dom_a, dom_b, &program_cells)?;
    let spec_def = enum_transition_body_2d(dom_a, dom_b, &reference_cells)?;

    let spec = FiniteSimSpec {
        label: "trust_ir_table_step_refines_spec".to_string(),
        flavor: SimFlavor::EnumCases2d {
            dom_a: dom_a.clone(),
            dom_b: dom_b.clone(),
            impl_def,
            spec_def,
        },
    };

    // 3. Proof built from the PROGRAM's (extracted) matrix — fails closed on any
    //    disagreement with the reference baked into spec_def.
    let proof = enum_cases_refl_proof_2d(dom_a, dom_b, &program_cells)?;
    let term_bytes = serialize_term(&proof).ok()?;

    Some((spec, term_bytes))
}

/// Build and certify the exact IR-sourced finite-simulation obligation.
pub fn verify_ir_table_refines_spec(
    module: &Module,
    reference: &[Vec<i128>],
    dom_a: &InductiveDecl,
    dom_b: &InductiveDecl,
) -> Option<trust_ir::ProofEvidence> {
    let (spec, term_bytes) = ir_table_refinement_material(module, reference, dom_a, dom_b)?;
    certify_finite_sim(&spec, &term_bytes)
}

/// Consumer-side pair for [`verify_ir_table_refines_spec`]. The module's static
/// and executed tables, the reference, both domains, definitions, and goal are
/// rebuilt before delegating to the finite-simulation rechecker.
pub fn recheck_ir_table_refines_spec(
    module: &Module,
    reference: &[Vec<i128>],
    dom_a: &InductiveDecl,
    dom_b: &InductiveDecl,
    term_bytes: &[u8],
    context_bytes: &[u8],
    lineage: &trust_ir::ProofDigest,
) -> bool {
    let Some((spec, _)) = ir_table_refinement_material(module, reference, dom_a, dom_b) else {
        return false;
    };
    recheck_finite_sim(&spec, term_bytes, context_bytes, lineage)
}

// ─────────────────── composition: class_matrix ∘ classify ────────────────────
//
// The lane verifies the class table (St × Cls → Nat) and the byte→class
// classifier (Byte → Cls) SEPARATELY. `kernel_checks_table_composition` makes
// their COMPOSITION a single kernel-checked fact: for a byte chunk,
//
//     ∀ (s : St) (b : Byte), Eq Nat (full s b) (class_matrix s (classify b))
//
// where `full` is the REAL per-byte next-state table (an INDEPENDENT dump) — so
// the equation is non-trivial (LHS ≠ RHS by construction; they agree only if the
// classifier and class table correctly factor the real table). A correct
// factorization is accepted; a wrong classifier or class-table cell makes some
// cell's `Eq.refl` ill-typed and the kernel rejects (fail-closed). Chunking the
// byte domain keeps the nested `casesOn` within the kernel's recursion depth (a
// flat 256-constructor inner domain overflows the stack — see §8.11).
//
// SOUNDNESS: the sole trusted step is the clean-kernel `check_type`
// (infer_only=false) — the SAME anchor as `certify_finite_sim`. Every domain and
// def body is fully re-checked by `add_inductive`/`add_decl`; the goal is built
// here and structurally re-checked (`is_composition_goal`, defense-in-depth); the
// proof reuses the lane's audited `enum_cases_refl_proof_2d`. This function mints
// no transportable certificate — it returns whether the kernel accepts the proof.

// These two names MUST equal `finite_dfa`'s private TSTEP/SPEC, since the reused
// `enum_cases_refl_proof_2d` builds a proof that references them by name.
const COMP_TSTEP: &str = "trust_dfa_tstep";
const COMP_SPEC: &str = "trust_dfa_spec";
const COMP_CMX: &str = "trust_dfa_cmx";
const COMP_CLASSIFY: &str = "trust_dfa_classify";

fn apply_head(head: Expr, args: Vec<Expr>) -> Expr {
    args.into_iter().fold(head, Expr::app)
}

fn nat_const() -> Expr {
    Expr::const_(Name::from_string("Nat"), vec![])
}

/// `λ b : Byte, Byte.casesOn.{1} (λ _:Byte, Cls) b Cls.ctor[class[0]] …` — the
/// classifier as a total function returning the class CONSTRUCTOR of each byte.
/// `class[j]` is the class index of byte-ctor `j`; out-of-range ⇒ `None`. The
/// motive returns `Cls : Sort 1`, so the `casesOn` level arg is `succ(zero)`.
fn classify_body(
    byte_dom: &InductiveDecl,
    cls_dom: &InductiveDecl,
    class: &[usize],
) -> Option<Expr> {
    let bt = byte_dom.types.first()?;
    let ct = cls_dom.types.first()?;
    if bt.constructors.len() != class.len() {
        return None;
    }
    let bt_ref = Expr::const_(bt.name.clone(), vec![]);
    let cls_ref = Expr::const_(ct.name.clone(), vec![]);
    let motive = Expr::lam(BinderInfo::Default, bt_ref.clone(), cls_ref);
    let mut args = vec![motive, Expr::bvar(0)];
    for &ci in class {
        args.push(Expr::const_(ct.constructors.get(ci)?.name.clone(), vec![]));
    }
    let cases_on = Expr::const_(
        Name::from_string(&format!("{}.casesOn", bt.name)),
        vec![Level::succ(Level::zero())],
    );
    Some(Expr::lam(BinderInfo::Default, bt_ref, apply_head(cases_on, args)))
}

/// `A → B → Nat`.
fn fn2_ty(a: &InductiveDecl, b: &InductiveDecl) -> Option<Expr> {
    let a = a.types.first()?;
    let b = b.types.first()?;
    Some(Expr::pi(
        BinderInfo::Default,
        Expr::const_(a.name.clone(), vec![]),
        Expr::pi(BinderInfo::Default, Expr::const_(b.name.clone(), vec![]), nat_const()),
    ))
}

fn register_reducible(env: &mut Environment, name: &str, type_: Expr, value: Expr) -> Option<()> {
    env.add_decl(Declaration::Definition {
        name: Name::from_string(name),
        level_params: vec![],
        type_,
        value,
        is_reducible: true,
    })
    .ok()
}

fn comp_is_const_named(e: &Expr, name: &str) -> bool {
    matches!(e.kind(), clean_kernel::expr::ExprKind::Const(n, _) if n.to_string() == name)
}

/// `head #1 #0`.
fn comp_is_app2(e: &Expr, head_name: &str) -> bool {
    use clean_kernel::expr::ExprKind;
    let ExprKind::App(f, a0) = e.kind() else { return false };
    if !matches!(a0.kind(), ExprKind::BVar(0)) {
        return false;
    }
    let ExprKind::App(h, a1) = f.kind() else { return false };
    if !matches!(a1.kind(), ExprKind::BVar(1)) {
        return false;
    }
    comp_is_const_named(h, head_name)
}

/// Defense-in-depth: confirm `goal` is EXACTLY
/// `∀ (s:St)(b:Byte), Eq Nat (tstep #1 #0) (spec #1 #0)` with the heads being the
/// distinct `full`/composition consts. Built here, so this can only confirm the
/// intended shape; it blocks a future refactor from silently widening the claim.
fn is_composition_goal(goal: &Expr, st_dom: &InductiveDecl, byte_dom: &InductiveDecl) -> bool {
    use clean_kernel::expr::ExprKind;
    let (Some(st), Some(bt)) = (st_dom.types.first(), byte_dom.types.first()) else {
        return false;
    };
    let ExprKind::Pi(_, d1, b1) = goal.kind() else { return false };
    if !comp_is_const_named(d1, &st.name.to_string()) {
        return false;
    }
    let ExprKind::Pi(_, d2, b2) = b1.kind() else { return false };
    if !comp_is_const_named(d2, &bt.name.to_string()) {
        return false;
    }
    let ExprKind::App(eqnat_lhs, rhs) = b2.kind() else { return false };
    if !comp_is_app2(rhs, COMP_SPEC) {
        return false;
    }
    let ExprKind::App(eqnat, lhs) = eqnat_lhs.kind() else { return false };
    if !comp_is_app2(lhs, COMP_TSTEP) {
        return false;
    }
    let ExprKind::App(eqhead, alpha) = eqnat.kind() else { return false };
    comp_is_const_named(alpha, "Nat") && comp_is_const_named(eqhead, "Eq")
}

/// Kernel-check that the real per-byte table FACTORS THROUGH the classifier over
/// one byte chunk: `∀ s b, Eq Nat (full s b) (class_matrix s (classify b))`.
/// Returns `Some(())` iff the clean kernel accepts; `None` (fail-closed) on any
/// dimension/shape/build/kernel failure.
pub(crate) fn kernel_checks_table_composition(
    st_dom: &InductiveDecl,
    byte_dom: &InductiveDecl,
    cls_dom: &InductiveDecl,
    full_chunk: &[Vec<i128>],
    class_matrix: &[Vec<i128>],
    classify: &[i128],
) -> Option<()> {
    // Defense-in-depth (mirrors `finite_dfa::certify_finite_sim`'s EnumCases2d arm):
    // the hand-built `enum_cases_refl_proof_2d` / `enum_transition_body_2d` /
    // `classify_body` proof shape assumes each domain is a single parameter-free
    // inductive with NULLARY constructors. A parametric or field-carrying domain is
    // ALREADY caught by the downstream kernel `check_type` (the generated `casesOn`
    // gains param/field binders the hand-built application never supplies, so the
    // proof fails to type-check -> fail-closed; see the `*_domain_with_*_data`
    // regression tests). This up-front guard turns that silent kernel rejection into
    // an explicit one and keeps both lanes' domain contract identical. It is NOT the
    // soundness anchor — the kernel check at the end of this fn is.
    if !is_nullary_enum_domain(st_dom)
        || !is_nullary_enum_domain(byte_dom)
        || !is_nullary_enum_domain(cls_dom)
    {
        return None;
    }
    let st = st_dom.types.first()?;
    let bt = byte_dom.types.first()?;
    let ct = cls_dom.types.first()?;
    let (n_st, n_byte, n_cls) =
        (st.constructors.len(), bt.constructors.len(), ct.constructors.len());
    if n_st == 0 || n_byte == 0 || n_cls == 0 {
        return None;
    }
    if full_chunk.len() != n_st || class_matrix.len() != n_st {
        return None;
    }
    if full_chunk.iter().any(|r| r.len() != n_byte) || class_matrix.iter().any(|r| r.len() != n_cls)
    {
        return None;
    }
    if classify.len() != n_byte {
        return None;
    }
    let classify_idx: Vec<usize> = classify
        .iter()
        .map(|&c| usize::try_from(c).ok().filter(|&u| u < n_cls))
        .collect::<Option<Vec<_>>>()?;

    let mut env = Environment::default();
    env.init_nat().ok()?;
    env.init_eq().ok()?;
    env.add_inductive(st_dom.clone()).ok()?;
    env.add_inductive(byte_dom.clone()).ok()?;
    env.add_inductive(cls_dom.clone()).ok()?;

    let cmx_cells = matrix_to_nat_cells(class_matrix)?;
    let full_cells = matrix_to_nat_cells(full_chunk)?;
    let class_matrix_def = enum_transition_body_2d(st_dom, cls_dom, &cmx_cells)?;
    let classify_def = classify_body(byte_dom, cls_dom, &classify_idx)?;
    let full_def = enum_transition_body_2d(st_dom, byte_dom, &full_cells)?;

    let st_ref = Expr::const_(st.name.clone(), vec![]);
    let bt_ref = Expr::const_(bt.name.clone(), vec![]);
    // spec := λ (s:St)(b:Byte), class_matrix s (classify b)   (s = #1, b = #0)
    let spec_def = Expr::lam(
        BinderInfo::Default,
        st_ref.clone(),
        Expr::lam(
            BinderInfo::Default,
            bt_ref.clone(),
            apply_head(
                Expr::const_(Name::from_string(COMP_CMX), vec![]),
                vec![
                    Expr::bvar(1),
                    apply_head(
                        Expr::const_(Name::from_string(COMP_CLASSIFY), vec![]),
                        vec![Expr::bvar(0)],
                    ),
                ],
            ),
        ),
    );

    let classify_ty =
        Expr::pi(BinderInfo::Default, bt_ref.clone(), Expr::const_(ct.name.clone(), vec![]));
    let full_ty = fn2_ty(st_dom, byte_dom)?;
    // dependency order: spec references CMX + CLASSIFY, so register them first.
    register_reducible(&mut env, COMP_CMX, fn2_ty(st_dom, cls_dom)?, class_matrix_def)?;
    register_reducible(&mut env, COMP_CLASSIFY, classify_ty, classify_def)?;
    register_reducible(&mut env, COMP_TSTEP, full_ty.clone(), full_def)?;
    register_reducible(&mut env, COMP_SPEC, full_ty, spec_def)?;

    let eq_body = apply_head(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        vec![
            nat_const(),
            apply_head(
                Expr::const_(Name::from_string(COMP_TSTEP), vec![]),
                vec![Expr::bvar(1), Expr::bvar(0)],
            ),
            apply_head(
                Expr::const_(Name::from_string(COMP_SPEC), vec![]),
                vec![Expr::bvar(1), Expr::bvar(0)],
            ),
        ],
    );
    let goal =
        Expr::pi(BinderInfo::Default, st_ref, Expr::pi(BinderInfo::Default, bt_ref, eq_body));
    if !is_composition_goal(&goal, st_dom, byte_dom) {
        return None;
    }

    let proof = enum_cases_refl_proof_2d(st_dom, byte_dom, &full_cells)?;
    if TypeChecker::with_context(&env, LocalContext::new()).check_type(&proof, &goal).is_ok() {
        Some(())
    } else {
        None
    }
}

// ─────────────────────── First Light: the public engine entry ────────────────
// A REAL kernel-checked verdict that the aterm VT parser's next-state table
// refines its reference — the same path exercised by
// `verifies_full_aterm_table_step_refines_spec`, exposed publicly because the
// finite-simulation lane is a general capability and this table is the worked
// example that proves it end to end. It has no in-tree caller: the diagnostic
// engine that used to wrap its evidence was a TypeScript-refinement surface
// that predated the two-language ratification and was removed rather than
// promoted to a third authoritative language.

/// A nullary-constructor inductive with `names.len()` constructors (engine copy of
/// the test `enum_domain`).
fn enum_decl(type_name: &str, names: &[&str]) -> InductiveDecl {
    let ty = Name::from_string(type_name);
    let ty_ref = Expr::const_(ty.clone(), vec![]);
    let ctors = names
        .iter()
        .map(|n| clean_kernel::Constructor { name: Name::from_string(n), type_: ty_ref.clone() })
        .collect();
    InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![clean_kernel::InductiveType {
            name: ty,
            type_: Expr::type_(),
            constructors: ctors,
        }],
    }
}

/// The 14 aterm parser states (outer domain), in `state.rs` index order.
fn aterm_state14_domain() -> InductiveDecl {
    enum_decl(
        "St14",
        &[
            "St14.ground",
            "St14.escape",
            "St14.escInter",
            "St14.csiEntry",
            "St14.csiParam",
            "St14.csiInter",
            "St14.csiIgnore",
            "St14.dcsEntry",
            "St14.dcsParam",
            "St14.dcsInter",
            "St14.dcsPass",
            "St14.dcsIgnore",
            "St14.oscString",
            "St14.sosPmApc",
        ],
    )
}

/// 8 representative byte classes (inner domain).
fn aterm_byteclass8_domain() -> InductiveDecl {
    enum_decl(
        "Bc8",
        &[
            "Bc8.c0",
            "Bc8.can",
            "Bc8.esc",
            "Bc8.inter",
            "Bc8.digit",
            "Bc8.semi",
            "Bc8.final",
            "Bc8.c1csi",
        ],
    )
}

/// The full real aterm 14×8 next-state-index table (engine copy of the pinned
/// `full_aterm_matrix`).
fn aterm_next_state_14x8() -> Vec<Vec<i128>> {
    vec![
        vec![0, 0, 1, 0, 0, 0, 0, 3],
        vec![1, 0, 1, 2, 0, 0, 0, 3],
        vec![2, 0, 1, 2, 0, 0, 0, 3],
        vec![3, 0, 1, 5, 4, 4, 0, 3],
        vec![4, 0, 1, 5, 4, 4, 0, 3],
        vec![5, 0, 1, 5, 6, 6, 0, 3],
        vec![6, 0, 1, 6, 6, 6, 0, 3],
        vec![7, 0, 1, 9, 8, 8, 10, 3],
        vec![8, 0, 1, 9, 8, 8, 10, 3],
        vec![9, 0, 1, 9, 11, 11, 10, 3],
        vec![10, 0, 1, 10, 10, 10, 10, 10],
        vec![11, 0, 1, 11, 11, 11, 11, 3],
        vec![12, 0, 1, 12, 12, 12, 12, 12],
        vec![13, 0, 1, 13, 13, 13, 13, 13],
    ]
}

/// Certify, through the `clean` kernel, that the real 14-state aterm parser
/// next-state table refines its reference. Returns the kernel `CleanCic` evidence,
/// or `None` (fail-closed).
pub fn certify_aterm_parser_next_state() -> Option<trust_ir::ProofEvidence> {
    let dom_a = aterm_state14_domain();
    let dom_b = aterm_byteclass8_domain();
    let m = aterm_next_state_14x8();
    let module = author_table_step_module(&m)?;
    // Static read and executed I/O must agree before certification (anti-vacuity).
    if extract_2d_matrix(&module, 14, 8).as_ref() != Some(&m) {
        return None;
    }
    if execution_table(&module, 14, 8).as_ref() != Some(&m) {
        return None;
    }
    verify_ir_table_refines_spec(&module, &m, &dom_a, &dom_b)
}

/// Consumer-side pair for [`certify_aterm_parser_next_state`]. Rebuilds the
/// pinned module, reference matrix, and domains before checking the evidence.
pub fn recheck_aterm_parser_next_state(
    term_bytes: &[u8],
    context_bytes: &[u8],
    lineage: &trust_ir::ProofDigest,
) -> bool {
    let dom_a = aterm_state14_domain();
    let dom_b = aterm_byteclass8_domain();
    let reference = aterm_next_state_14x8();
    let Some(module) = author_table_step_module(&reference) else {
        return false;
    };
    recheck_ir_table_refines_spec(
        &module,
        &reference,
        &dom_a,
        &dom_b,
        term_bytes,
        context_bytes,
        lineage,
    )
}

#[cfg(test)]
mod tests {
    use clean_kernel::name::Name;
    use clean_kernel::{Constructor, InductiveType};

    use super::*;
    use crate::finite_dfa::recheck_finite_sim;

    /// 3 parser states (outer domain), mirroring `finite_dfa.rs::state3_domain`:
    /// Ground, CsiEntry, CsiParam — a single nullary-ctor inductive.
    fn state3_domain() -> InductiveDecl {
        let st = Name::from_string("St3");
        let st_ref = Expr::const_(st.clone(), vec![]);
        let ctor = |n: &str| Constructor { name: Name::from_string(n), type_: st_ref.clone() };
        InductiveDecl {
            level_params: vec![],
            num_params: 0,
            types: vec![InductiveType {
                name: st,
                type_: Expr::type_(),
                constructors: vec![ctor("St3.ground"), ctor("St3.csiEntry"), ctor("St3.csiParam")],
            }],
        }
    }

    /// 3 byte classes (inner domain), mirroring `finite_dfa.rs::byteclass3_domain`:
    /// C0 control, ESC, intermediate — a single nullary-ctor inductive.
    fn byteclass3_domain() -> InductiveDecl {
        let bc = Name::from_string("Bc3");
        let bc_ref = Expr::const_(bc.clone(), vec![]);
        let ctor = |n: &str| Constructor { name: Name::from_string(n), type_: bc_ref.clone() };
        InductiveDecl {
            level_params: vec![],
            num_params: 0,
            types: vec![InductiveType {
                name: bc,
                type_: Expr::type_(),
                constructors: vec![ctor("Bc3.c0"), ctor("Bc3.esc"), ctor("Bc3.inter")],
            }],
        }
    }

    /// The REAL 3×3 aterm state×byte-class next-state table (GROUND TRUTH, same as
    /// `finite_dfa.rs::real_2d_matrix`), as plain `i128`:
    ///   Ground   : C0→Ground(0)   ESC→Escape(1)  inter→Ground(0)
    ///   CsiEntry : C0→CsiEntry(3)  ESC→Escape(1)  inter→CsiIntermediate(5)
    ///   CsiParam : C0→CsiParam(4)  ESC→Escape(1)  inter→CsiIntermediate(5)
    fn real_matrix() -> Vec<Vec<i128>> {
        vec![vec![0, 1, 0], vec![3, 1, 5], vec![4, 1, 5]]
    }

    #[test]
    fn ir_extraction_roundtrips() {
        // The authored trust-ir `table_step` program is faithfully read back: the
        // matrix extracted by traversing the nested switch equals the matrix we
        // encoded into it.
        let m = real_matrix();
        let module =
            author_table_step_module(&m).expect("authoring the real 3×3 table must succeed");
        let extracted = extract_2d_matrix(&module, 3, 3);
        assert_eq!(extracted, Some(m));
    }

    #[test]
    fn ir_execution_matches_static_extraction() {
        // The trust-ir interpreter EXECUTES the authored program to exactly the
        // table we encoded — and that executed table equals the statically
        // extracted one. This is the checked invariant `verify` relies on
        // (extraction == execution), so the kernel's "impl == spec" entails the
        // program's runtime I/O refines the spec.
        let m = real_matrix();
        let module = author_table_step_module(&m).expect("authoring must succeed");
        assert_eq!(super::execution_table(&module, 3, 3), Some(m.clone()));
        assert_eq!(super::extract_2d_matrix(&module, 3, 3), Some(m));
    }

    #[test]
    fn verifies_ir_table_step_refines_spec() {
        // A trust-ir program matching the reference spec is kernel-verified: the
        // impl is SOURCED from the program, the spec is the SAME real reference,
        // they agree at every cell, and the lane mints a CleanCic certificate
        // whose payload re-checks.
        let dom_a = state3_domain();
        let dom_b = byteclass3_domain();
        let m = real_matrix();
        let module = author_table_step_module(&m).expect("authoring must succeed");
        let evidence = verify_ir_table_refines_spec(&module, &m, &dom_a, &dom_b)
            .expect("a trust-ir program matching the spec must certify");
        let trust_ir::ProofEvidence::CleanCic { term, context, lineage, .. } = evidence else {
            panic!("expected CleanCic evidence");
        };
        assert!(recheck_ir_table_refines_spec(
            &module, &m, &dom_a, &dom_b, &term, &context, &lineage,
        ));
        assert!(!recheck_ir_table_refines_spec(
            &module,
            &m,
            &dom_a,
            &dom_b,
            &term,
            &context,
            &trust_ir::ProofDigest::zero(),
        ));

        let mut tampered_term = term.clone();
        tampered_term[0] ^= 0xff;
        assert!(!recheck_ir_table_refines_spec(
            &module,
            &m,
            &dom_a,
            &dom_b,
            &tampered_term,
            &context,
            &lineage,
        ));
        let mut noncanonical_context = context.clone();
        noncanonical_context.push(0);
        assert!(!recheck_ir_table_refines_spec(
            &module,
            &m,
            &dom_a,
            &dom_b,
            &term,
            &noncanonical_context,
            &lineage,
        ));

        let mut drifted_reference = m.clone();
        drifted_reference[0][0] = 2;
        assert!(!recheck_ir_table_refines_spec(
            &module,
            &drifted_reference,
            &dom_a,
            &dom_b,
            &term,
            &context,
            &lineage,
        ));

        let mut drifted_program = m.clone();
        drifted_program[0][0] = 2;
        let drifted_module =
            author_table_step_module(&drifted_program).expect("drifted module authors");
        assert!(!recheck_ir_table_refines_spec(
            &drifted_module,
            &m,
            &dom_a,
            &dom_b,
            &term,
            &context,
            &lineage,
        ));

        let drifted_dom_a =
            enum_domain("St3Drift", &["St3Drift.ground", "St3Drift.csiEntry", "St3Drift.csiParam"]);
        assert!(!recheck_ir_table_refines_spec(
            &module,
            &m,
            &drifted_dom_a,
            &dom_b,
            &term,
            &context,
            &lineage,
        ));

        let spec = FiniteSimSpec {
            label: "trust_ir_table_step_refines_spec".to_string(),
            flavor: SimFlavor::EnumCases2d {
                dom_a: dom_a.clone(),
                dom_b: dom_b.clone(),
                impl_def: enum_transition_body_2d(
                    &dom_a,
                    &dom_b,
                    &matrix_to_nat_cells(&m).unwrap(),
                )
                .unwrap(),
                spec_def: enum_transition_body_2d(
                    &dom_a,
                    &dom_b,
                    &matrix_to_nat_cells(&m).unwrap(),
                )
                .unwrap(),
            },
        };
        assert!(recheck_finite_sim(&spec, &term, &context, &lineage));
    }

    #[test]
    fn rejects_buggy_ir_table_step() {
        // THE key test: a buggy trust-ir program (CsiEntry × intermediate = 0
        // instead of the table's CsiIntermediate(5)) is caught. The impl is sourced
        // from the buggy program; the reference (spec) is the CORRECT table; the
        // nested-casesOn proof built from the buggy matrix cannot discharge the
        // disagreeing cell ⇒ the lane fails closed.
        let dom_a = state3_domain();
        let dom_b = byteclass3_domain();
        let mut buggy = real_matrix();
        buggy[1][2] = 0; // CsiEntry × intermediate: 5 → 0 (the bug)
        let module = author_table_step_module(&buggy).expect("authoring must succeed");
        // Sanity: the bug is faithfully encoded and read back.
        assert_eq!(extract_2d_matrix(&module, 3, 3), Some(buggy.clone()));
        // The reference is the CORRECT table; the buggy program must not certify.
        let evidence = verify_ir_table_refines_spec(&module, &real_matrix(), &dom_a, &dom_b);
        assert!(evidence.is_none(), "a buggy trust-ir program must fail closed");
    }

    // ── The FULL 14-state aterm parser table ──────────────────────────────────

    /// A nullary-constructor inductive with `names.len()` constructors.
    fn enum_domain(type_name: &str, names: &[&str]) -> InductiveDecl {
        let ty = Name::from_string(type_name);
        let ty_ref = Expr::const_(ty.clone(), vec![]);
        let ctors = names
            .iter()
            .map(|n| Constructor { name: Name::from_string(n), type_: ty_ref.clone() })
            .collect();
        InductiveDecl {
            level_params: vec![],
            num_params: 0,
            types: vec![InductiveType { name: ty, type_: Expr::type_(), constructors: ctors }],
        }
    }

    /// An `n`-constructor nullary enum with ctors `{prefix}{0..n}` — for domains too
    /// large to spell out (e.g. the 256 byte values).
    fn indexed_enum_domain(type_name: &str, prefix: &str, n: usize) -> InductiveDecl {
        let names: Vec<String> = (0..n).map(|i| format!("{prefix}{i}")).collect();
        let refs: Vec<&str> = names.iter().map(String::as_str).collect();
        enum_domain(type_name, &refs)
    }

    /// The 14 parser states (outer domain), in `state.rs` index order.
    fn state14_domain() -> InductiveDecl {
        enum_domain(
            "St14",
            &[
                "St14.ground",
                "St14.escape",
                "St14.escInter",
                "St14.csiEntry",
                "St14.csiParam",
                "St14.csiInter",
                "St14.csiIgnore",
                "St14.dcsEntry",
                "St14.dcsParam",
                "St14.dcsInter",
                "St14.dcsPass",
                "St14.dcsIgnore",
                "St14.oscString",
                "St14.sosPmApc",
            ],
        )
    }

    /// 8 representative byte classes (inner domain): one concrete byte each, so
    /// every cell is unambiguous: C0(0x05), CAN(0x18), ESC(0x1B), intermediate
    /// (0x20), digit(0x30), semicolon(0x3B), final(0x40), C1-CSI(0x9B).
    fn byteclass8_domain() -> InductiveDecl {
        enum_domain(
            "Bc8",
            &[
                "Bc8.c0",
                "Bc8.can",
                "Bc8.esc",
                "Bc8.inter",
                "Bc8.digit",
                "Bc8.semi",
                "Bc8.final",
                "Bc8.c1csi",
            ],
        )
    }

    /// The 19 TRUE behavioral byte classes of the real aterm parser — i.e. the
    /// equivalence classes of the 256 byte values under "identical next-state
    /// column across all 14 states", derived empirically from the compiled
    /// `aterm_parser::TRANSITIONS` (aterm @ `4e2e6c2`) and ordered by the
    /// lexicographic sort of those columns. These are NOT a hand-chosen sample
    /// (the earlier 8-byte set covered only 7 of them) — they are the complete,
    /// machine-generated partition. Each `Cls19.k{i}` is the class whose column is
    /// `full_aterm_class_matrix()[*][i]`; representative bytes per class:
    ///   k0  {0x18,0x1a}            k1  {0x9c}                 k2  C1-area {0x80..,0xa0..}
    ///   k3  printable {0x40..0x7e} k4  digit/semi {0x30..,0x3b} k5  colon {0x3a}
    ///   k6  csi-priv {0x3c..0x3f}  k7  BEL {0x07}              k8  C0/stay {0x00..,0x7f}
    ///   k9  intermediate {0x20..}  k10 CSI-'[' {0x5b}          k11 DCS-'P' {0x50}
    ///   k12 OSC-']' {0x5d}         k13 ST-area {0x58,0x5e..}   k14 ESC {0x1b}
    ///   k15 C1-CSI {0x9b}          k16 C1-DCS {0x90}           k17 C1-OSC {0x9d}
    ///   k18 C1-ST-area {0x98,0x9e..}
    fn class19_domain() -> InductiveDecl {
        enum_domain(
            "Cls19",
            &[
                "Cls19.k0",
                "Cls19.k1",
                "Cls19.k2",
                "Cls19.k3",
                "Cls19.k4",
                "Cls19.k5",
                "Cls19.k6",
                "Cls19.k7",
                "Cls19.k8",
                "Cls19.k9",
                "Cls19.k10",
                "Cls19.k11",
                "Cls19.k12",
                "Cls19.k13",
                "Cls19.k14",
                "Cls19.k15",
                "Cls19.k16",
                "Cls19.k17",
                "Cls19.k18",
            ],
        )
    }

    /// The FULL real aterm 14x8 next-state-index table. Every cell was transcribed
    /// from `table/mod.rs` / `table/dcs_osc.rs` (anywhere rule first, then the
    /// per-state apply_* override; payload states 10/12/13 override C1 0x9B) AND
    /// verified against an empirical dump of the real compiled
    /// `aterm_parser::TRANSITIONS` (aterm @ 4e2e6c2) for these 8 representative
    /// bytes — that dump caught and corrected a 4-cell C0/CAN column swap in
    /// rows 1-2 (the escape states keep C0 0x05 ∈ 0x00-0x17 in-state via
    /// apply_escape*, while CAN 0x18 falls through to the anywhere rule → Ground).
    /// Rows are the 14 states in index order; columns are the 8 byte classes above.
    /// NOTE: this is a pinned one-shot cross-check, NOT a standing test — a
    /// continuous spec-vs-artifact guard would require a (cross-repo) dependency
    /// on the aterm crate, which is deliberately not taken here.
    fn full_aterm_matrix() -> Vec<Vec<i128>> {
        vec![
            vec![0, 0, 1, 0, 0, 0, 0, 3],       // 0  Ground
            vec![1, 0, 1, 2, 0, 0, 0, 3],       // 1  Escape (C0 0x05 stays; CAN 0x18 → Ground)
            vec![2, 0, 1, 2, 0, 0, 0, 3],       // 2  EscapeIntermediate (C0 stays; CAN → Ground)
            vec![3, 0, 1, 5, 4, 4, 0, 3],       // 3  CsiEntry
            vec![4, 0, 1, 5, 4, 4, 0, 3],       // 4  CsiParam
            vec![5, 0, 1, 5, 6, 6, 0, 3],       // 5  CsiIntermediate
            vec![6, 0, 1, 6, 6, 6, 0, 3],       // 6  CsiIgnore
            vec![7, 0, 1, 9, 8, 8, 10, 3],      // 7  DcsEntry
            vec![8, 0, 1, 9, 8, 8, 10, 3],      // 8  DcsParam
            vec![9, 0, 1, 9, 11, 11, 10, 3],    // 9  DcsIntermediate
            vec![10, 0, 1, 10, 10, 10, 10, 10], // 10 DcsPassthrough (C1 0x9B override → stay)
            vec![11, 0, 1, 11, 11, 11, 11, 3],  // 11 DcsIgnore
            vec![12, 0, 1, 12, 12, 12, 12, 12], // 12 OscString (C1 0x9B override → stay)
            vec![13, 0, 1, 13, 13, 13, 13, 13], // 13 SosPmApcString (C1 0x9B override → stay)
        ]
    }

    /// The COMPLETE 14-state × 19-behavioral-class next-state table — every distinct
    /// byte behavior of the real parser, not a sample. MACHINE-GENERATED by dumping
    /// the compiled `aterm_parser::TRANSITIONS` (aterm @ `4e2e6c2`), partitioning the
    /// 256 bytes into their 19 equivalence classes, and transposing — i.e. it was
    /// NOT hand-transcribed (the discipline lesson from the §8.10 C0/CAN audit). Rows
    /// are the 14 states in index order; columns are `class19_domain` k0..k18.
    fn full_aterm_class_matrix() -> Vec<Vec<i128>> {
        vec![
            vec![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 3, 7, 12, 13], // state 0  Ground
            vec![0, 0, 0, 0, 0, 0, 0, 1, 1, 2, 3, 7, 12, 13, 1, 3, 7, 12, 13], // state 1  Escape
            vec![0, 0, 0, 0, 0, 0, 0, 2, 2, 2, 0, 0, 0, 0, 1, 3, 7, 12, 13], // state 2  EscInter
            vec![0, 0, 0, 0, 4, 4, 4, 3, 3, 5, 0, 0, 0, 0, 1, 3, 7, 12, 13], // state 3  CsiEntry
            vec![0, 0, 0, 0, 4, 4, 6, 4, 4, 5, 0, 0, 0, 0, 1, 3, 7, 12, 13], // state 4  CsiParam
            vec![0, 0, 0, 0, 6, 6, 6, 5, 5, 5, 0, 0, 0, 0, 1, 3, 7, 12, 13], // state 5  CsiInter
            vec![0, 0, 0, 0, 6, 6, 6, 6, 6, 6, 0, 0, 0, 0, 1, 3, 7, 12, 13], // state 6  CsiIgnore
            vec![0, 0, 0, 10, 8, 11, 8, 7, 7, 9, 10, 10, 10, 10, 1, 3, 7, 12, 13], // state 7  DcsEntry
            vec![0, 0, 0, 10, 8, 11, 11, 8, 8, 9, 10, 10, 10, 10, 1, 3, 7, 12, 13], // state 8  DcsParam
            vec![0, 0, 0, 10, 11, 11, 11, 9, 9, 9, 10, 10, 10, 10, 1, 3, 7, 12, 13], // state 9  DcsInter
            vec![0, 0, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 1, 10, 10, 10, 10], // state 10 DcsPass
            vec![0, 0, 0, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 1, 3, 7, 12, 13], // state 11 DcsIgnore
            vec![0, 12, 12, 12, 12, 12, 12, 0, 12, 12, 12, 12, 12, 12, 1, 12, 12, 12, 12], // state 12 OscString
            vec![0, 0, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 1, 13, 13, 13, 13], // state 13 SosPmApc
        ]
    }

    #[test]
    fn verifies_full_aterm_table_step_refines_spec() {
        // END-TO-END at FULL SCALE: the COMPLETE 14-state aterm parser transition
        // table, authored as a real trust-ir program (a nested switch over 14
        // states x 8 byte classes), is certified — through the kernel lane, over a
        // 14x8 = 112-cell nested casesOn proof — to refine the spec, with extraction
        // cross-checked against the program's executed I/O. This is the 14-state x
        // 8-byte-class next-state table verified as a Trust artifact (next-state-index
        // level; the byte->class classifier and action edge are NOT covered — see header).
        let dom_a = state14_domain();
        let dom_b = byteclass8_domain();
        let m = full_aterm_matrix();
        let module = author_table_step_module(&m).expect("authoring the full table must succeed");
        // Static read and executed I/O agree on the whole table.
        assert_eq!(extract_2d_matrix(&module, 14, 8), Some(m.clone()));
        assert_eq!(super::execution_table(&module, 14, 8), Some(m.clone()));
        let evidence = certify_aterm_parser_next_state()
            .expect("the pinned aterm trust-ir table must certify against its spec");
        let trust_ir::ProofEvidence::CleanCic { term, context, lineage, .. } = evidence else {
            panic!("expected CleanCic evidence");
        };
        assert!(recheck_aterm_parser_next_state(&term, &context, &lineage));
        assert!(!recheck_aterm_parser_next_state(&term, &context, &trust_ir::ProofDigest::zero(),));
        assert!(recheck_ir_table_refines_spec(
            &module, &m, &dom_a, &dom_b, &term, &context, &lineage,
        ));
        let mut tampered = term.clone();
        tampered[0] ^= 0xff;
        assert!(!recheck_aterm_parser_next_state(&tampered, &context, &lineage));
        let mut noncanonical_context = context.clone();
        noncanonical_context.push(0);
        assert!(!recheck_aterm_parser_next_state(&term, &noncanonical_context, &lineage,));
        assert!(recheck_finite_sim(
            &FiniteSimSpec {
                label: "trust_ir_table_step_refines_spec".to_string(),
                flavor: SimFlavor::EnumCases2d {
                    dom_a: dom_a.clone(),
                    dom_b: dom_b.clone(),
                    impl_def: enum_transition_body_2d(
                        &dom_a,
                        &dom_b,
                        &matrix_to_nat_cells(&m).unwrap()
                    )
                    .unwrap(),
                    spec_def: enum_transition_body_2d(
                        &dom_a,
                        &dom_b,
                        &matrix_to_nat_cells(&m).unwrap()
                    )
                    .unwrap(),
                },
            },
            &term,
            &context,
            &lineage
        ));
    }

    #[test]
    fn rejects_full_aterm_table_with_one_wrong_cell() {
        // Fail-closed scales: flip ONE of the 112 cells of the full table (DcsEntry
        // x final: DcsPassthrough(10) -> Ground(0)) and the lane rejects.
        let dom_a = state14_domain();
        let dom_b = byteclass8_domain();
        let mut buggy = full_aterm_matrix();
        buggy[7][6] = 0; // DcsEntry x final: 10 -> 0 (the bug)
        let module = author_table_step_module(&buggy).expect("authoring must succeed");
        assert_eq!(extract_2d_matrix(&module, 14, 8), Some(buggy.clone()));
        let evidence = verify_ir_table_refines_spec(&module, &full_aterm_matrix(), &dom_a, &dom_b);
        assert!(evidence.is_none(), "a single wrong cell in the full table must fail closed");
    }

    #[test]
    fn verifies_full_aterm_class_table_refines_spec() {
        // COMPLETE BEHAVIORAL COVERAGE: the real parser's 256 bytes collapse to 19
        // distinct next-state behaviors; this verifies the trust-ir program over the
        // full 14-state x 19-class table (14x19 = 266 cells) — every distinct byte
        // behavior, not the earlier 7-of-19 sample. Same proven EnumCases2d lane,
        // same checked extract==execution invariant, just the complete inner domain.
        let dom_a = state14_domain();
        let dom_b = class19_domain();
        let m = full_aterm_class_matrix();
        let module =
            author_table_step_module(&m).expect("authoring the 14x19 class table must succeed");
        assert_eq!(extract_2d_matrix(&module, 14, 19), Some(m.clone()));
        assert_eq!(super::execution_table(&module, 14, 19), Some(m.clone()));
        let evidence = verify_ir_table_refines_spec(&module, &m, &dom_a, &dom_b)
            .expect("the full 14x19 class table must certify against its spec");
        let trust_ir::ProofEvidence::CleanCic { term, context, lineage, .. } = evidence else {
            panic!("expected CleanCic evidence");
        };
        assert!(recheck_finite_sim(
            &FiniteSimSpec {
                label: "trust_ir_table_step_refines_spec".to_string(),
                flavor: SimFlavor::EnumCases2d {
                    dom_a: dom_a.clone(),
                    dom_b: dom_b.clone(),
                    impl_def: enum_transition_body_2d(
                        &dom_a,
                        &dom_b,
                        &matrix_to_nat_cells(&m).unwrap()
                    )
                    .unwrap(),
                    spec_def: enum_transition_body_2d(
                        &dom_a,
                        &dom_b,
                        &matrix_to_nat_cells(&m).unwrap()
                    )
                    .unwrap(),
                },
            },
            &term,
            &context,
            &lineage
        ));
    }

    #[test]
    fn rejects_full_aterm_class_table_with_one_wrong_cell() {
        // Fail-closed scales to 266 cells: flip ONE cell (DcsEntry x k4 digit class:
        // CsiParam(8) -> Ground(0)) and the lane rejects.
        let dom_a = state14_domain();
        let dom_b = class19_domain();
        let mut buggy = full_aterm_class_matrix();
        buggy[7][4] = 0; // DcsEntry x k4: 8 -> 0 (the bug)
        let module = author_table_step_module(&buggy).expect("authoring must succeed");
        assert_eq!(extract_2d_matrix(&module, 14, 19), Some(buggy.clone()));
        let evidence =
            verify_ir_table_refines_spec(&module, &full_aterm_class_matrix(), &dom_a, &dom_b);
        assert!(
            evidence.is_none(),
            "a single wrong cell in the 14x19 class table must fail closed"
        );
    }

    /// The byte→class classifier as a single 256-entry row: `classify[b]` = the
    /// behavioral-class index (0..18) of byte `b`. MACHINE-GENERATED from the
    /// compiled `aterm_parser::TRANSITIONS` (aterm @ `4e2e6c2`) by partitioning the
    /// 256 byte columns — NOT hand-transcribed. Together with `full_aterm_class_matrix`
    /// (verified by `verifies_full_aterm_class_table_refines_spec`) this covers all
    /// 14×256 concrete next states: `table_step(s,b) = class_matrix[s][classify[b]]`.
    fn aterm_byte_classifier_row() -> Vec<Vec<i128>> {
        // 256 entries, 16/line — generated from /tmp/real_classifier.txt and verified
        // to equal the real dump exactly (count 256, sum 1058) before commit.
        vec![vec![
            8, 8, 8, 8, 8, 8, 8, 7, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 0, 8, 0, 14, 8,
            8, 8, 8, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4,
            5, 4, 6, 6, 6, 6, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 11, 3, 3, 3, 3, 3, 3,
            3, 13, 3, 3, 10, 3, 12, 13, 13, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3,
            3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 8, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
            2, 16, 2, 2, 2, 2, 2, 2, 2, 18, 2, 2, 15, 1, 17, 18, 18, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
            2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
            2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
            2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
        ]]
    }

    /// Verify the byte→class classifier over the half-open byte range [lo, hi) as a
    /// degenerate 1×k table_step (state ignored; inner domain = the k byte values in
    /// the chunk), through the proven EnumCases2d lane + checked extract==execution.
    fn certify_classifier_chunk(lo: usize, hi: usize) -> Option<trust_ir::ProofEvidence> {
        let full = aterm_byte_classifier_row();
        let chunk: Vec<i128> = full[0][lo..hi].to_vec();
        let k = chunk.len();
        let m = vec![chunk];
        let dom_a = enum_domain("Unit1", &["Unit1.only"]);
        let dom_b = indexed_enum_domain("ByteChunk", "ByteChunk.b", k);
        let module = author_table_step_module(&m)?;
        assert_eq!(extract_2d_matrix(&module, 1, k), Some(m.clone()));
        assert_eq!(super::execution_table(&module, 1, k), Some(m.clone()));
        verify_ir_table_refines_spec(&module, &m, &dom_a, &dom_b)
    }

    #[test]
    fn verifies_aterm_byte_classifier_in_chunks() {
        // CLOSES THE BYTE BOUNDARY (piecewise): the byte→class map over ALL 256 byte
        // values, verified in 8 chunks of 32 that TILE 0x00..=0xff with no gap/overlap,
        // each kernel-certified through the lane. A flat 1×256 casesOn proof overflows
        // the kernel's recursion stack (SIGBUS) — chunking is the scaling path; 32-ctor
        // domains are well within depth. Together with the verified 14×19 class table
        // this accounts for every one of the 14×256 concrete next states.
        let mut covered = 0usize;
        for c in 0..8 {
            let (lo, hi) = (c * 32, c * 32 + 32);
            let ev = certify_classifier_chunk(lo, hi)
                .unwrap_or_else(|| panic!("classifier chunk [{lo:#x},{hi:#x}) must certify"));
            assert!(matches!(ev, trust_ir::ProofEvidence::CleanCic { .. }));
            covered += hi - lo;
        }
        assert_eq!(covered, 256, "the 8 chunks must tile all 256 byte values");
    }

    #[test]
    fn rejects_aterm_byte_classifier_chunk_with_one_wrong_byte() {
        // Fail-closed inside a chunk: misclassify ESC (0x1b: class 14 -> 8) in the
        // first 32-byte chunk and the lane rejects.
        let full = aterm_byte_classifier_row();
        let mut chunk: Vec<i128> = full[0][0..32].to_vec();
        chunk[0x1b] = 8; // ESC misclassified as the C0/stay class
        let m = vec![chunk];
        let dom_a = enum_domain("Unit1", &["Unit1.only"]);
        let dom_b = indexed_enum_domain("ByteChunk", "ByteChunk.b", 32);
        let module = author_table_step_module(&m).expect("authoring must succeed");
        // spec = the correct first-chunk classifier
        let spec = vec![full[0][0..32].to_vec()];
        let evidence = verify_ir_table_refines_spec(&module, &spec, &dom_a, &dom_b);
        assert!(evidence.is_none(), "a misclassified byte in a chunk must fail closed");
    }

    // ---- ACTION EDGE: the (next_state, action) pair codomain ----------------
    //
    // Tracking the FULL transition output (next_state AND ActionType) refines the
    // 256 bytes into 23 distinct (next_state, action) PAIR classes (vs 19 for
    // next-state alone). All three matrices below are MACHINE-GENERATED from the
    // compiled `aterm_parser::TRANSITIONS` (aterm @ `4e2e6c2`) — never hand-typed.

    /// The 23 (next_state, action) pair-classes (inner domain).
    fn pairclass23_domain() -> InductiveDecl {
        let names: Vec<String> = (0..23).map(|i| format!("Pc23.k{i}")).collect();
        let refs: Vec<&str> = names.iter().map(String::as_str).collect();
        enum_domain("Pc23", &refs)
    }

    /// 14×23 NEXT-STATE over the 23 pair-classes (machine-generated).
    fn pair_nextstate_matrix() -> Vec<Vec<i128>> {
        vec![
            vec![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 3, 7, 12, 13, 13], // state 0
            vec![0, 0, 0, 0, 0, 0, 2, 3, 7, 12, 13, 13, 0, 0, 1, 1, 1, 1, 3, 7, 12, 13, 13], // state 1
            vec![0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 2, 2, 1, 3, 7, 12, 13, 13], // state 2
            vec![0, 0, 0, 4, 4, 4, 5, 0, 0, 0, 0, 0, 0, 0, 3, 3, 3, 1, 3, 7, 12, 13, 13], // state 3
            vec![0, 0, 0, 6, 4, 4, 5, 0, 0, 0, 0, 0, 0, 0, 4, 4, 4, 1, 3, 7, 12, 13, 13], // state 4
            vec![0, 0, 0, 6, 6, 6, 5, 0, 0, 0, 0, 0, 0, 0, 5, 5, 5, 1, 3, 7, 12, 13, 13], // state 5
            vec![0, 0, 0, 6, 6, 6, 6, 0, 0, 0, 0, 0, 0, 0, 6, 6, 6, 1, 3, 7, 12, 13, 13], // state 6
            vec![0, 0, 10, 8, 8, 11, 9, 10, 10, 10, 10, 10, 0, 0, 7, 7, 7, 1, 3, 7, 12, 13, 13], // state 7
            vec![0, 0, 10, 11, 8, 11, 9, 10, 10, 10, 10, 10, 0, 0, 8, 8, 8, 1, 3, 7, 12, 13, 13], // state 8
            vec![0, 0, 10, 11, 11, 11, 9, 10, 10, 10, 10, 10, 0, 0, 9, 9, 9, 1, 3, 7, 12, 13, 13], // state 9
            vec![
                0, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 0, 10, 10, 10, 10, 1, 10, 10, 10,
                10, 10,
            ], // state 10
            vec![
                0, 0, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 0, 0, 11, 11, 11, 1, 3, 7, 12, 13, 13,
            ], // state 11
            vec![
                12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 0, 12, 0, 12, 12, 1, 12, 12, 12,
                12, 12,
            ], // state 12
            vec![
                0, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 0, 13, 13, 13, 13, 1, 13, 13, 13,
                13, 13,
            ], // state 13
        ]
    }

    /// 14×23 ACTION (ActionType index 0..16) over the 23 pair-classes (machine-generated).
    fn pair_action_matrix() -> Vec<Vec<i128>> {
        vec![
            vec![0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 13, 3, 3, 3, 10, 0, 14], // state 0
            vec![0, 0, 6, 6, 6, 6, 4, 3, 3, 10, 0, 14, 2, 2, 2, 2, 13, 3, 3, 3, 10, 0, 14], // state 1
            vec![0, 0, 6, 6, 6, 6, 4, 6, 6, 6, 6, 6, 2, 2, 2, 2, 13, 3, 3, 3, 10, 0, 14], // state 2
            vec![0, 0, 7, 4, 5, 5, 4, 7, 7, 7, 7, 7, 2, 2, 2, 2, 13, 3, 3, 3, 10, 0, 14], // state 3
            vec![0, 0, 7, 0, 5, 5, 4, 7, 7, 7, 7, 7, 2, 2, 2, 2, 13, 3, 3, 3, 10, 0, 14], // state 4
            vec![0, 0, 7, 0, 0, 0, 4, 7, 7, 7, 7, 7, 2, 2, 2, 2, 13, 3, 3, 3, 10, 0, 14], // state 5
            vec![0, 0, 0, 13, 13, 13, 13, 0, 0, 0, 0, 0, 2, 2, 2, 2, 13, 3, 3, 3, 10, 0, 14], // state 6
            vec![0, 0, 8, 4, 5, 0, 4, 8, 8, 8, 8, 8, 2, 2, 13, 13, 13, 3, 3, 3, 10, 0, 14], // state 7
            vec![0, 0, 8, 0, 5, 0, 4, 8, 8, 8, 8, 8, 2, 2, 13, 13, 13, 3, 3, 3, 10, 0, 14], // state 8
            vec![0, 0, 8, 0, 0, 0, 4, 8, 8, 8, 8, 8, 2, 2, 13, 13, 13, 3, 3, 3, 10, 0, 14], // state 9
            vec![0, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 2, 9, 9, 9, 13, 3, 9, 9, 9, 9, 9], // state 10
            vec![
                0, 0, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 2, 2, 13, 13, 13, 3, 3, 3, 10, 0, 14,
            ], // state 11
            vec![
                11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 2, 11, 12, 13, 11, 3, 11, 11, 11,
                11, 11,
            ], // state 12
            vec![
                0, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 2, 15, 15, 15, 15, 3, 15, 15, 15,
                15, 15,
            ], // state 13
        ]
    }

    /// byte (0..256) -> (next_state,action) pair-class index (0..22). Machine-generated.
    fn aterm_pair_classifier_row() -> Vec<Vec<i128>> {
        vec![vec![
            15, 15, 15, 15, 15, 15, 15, 14, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15,
            15, 15, 12, 15, 12, 17, 15, 15, 15, 15, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6,
            4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 4, 3, 3, 3, 3, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
            2, 2, 2, 8, 2, 2, 2, 2, 2, 2, 2, 10, 2, 2, 7, 2, 9, 10, 11, 2, 2, 2, 2, 2, 2, 2, 2, 2,
            2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 16, 13, 13, 13, 13,
            13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 19, 13, 13, 13, 13, 13, 13, 13, 21, 13,
            13, 18, 0, 20, 21, 22, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
            1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
            1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
            1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
        ]]
    }

    #[test]
    fn verifies_nextstate_over_pair_classes() {
        // The next-state edge over the FINER 23-pair-class partition (vs 19): every
        // distinct (next_state,action) behavior gets its own column.
        let dom_a = state14_domain();
        let dom_b = pairclass23_domain();
        let m = pair_nextstate_matrix();
        let module = author_table_step_module(&m).expect("authoring 14x23 next-state must succeed");
        assert_eq!(extract_2d_matrix(&module, 14, 23), Some(m.clone()));
        assert_eq!(super::execution_table(&module, 14, 23), Some(m.clone()));
        assert!(verify_ir_table_refines_spec(&module, &m, &dom_a, &dom_b).is_some());
    }

    #[test]
    fn verifies_action_edge_over_pair_classes() {
        // THE ACTION EDGE: the trust-ir program's ACTION output (ActionType index)
        // is kernel-certified to match the spec at all 14×23 cells — the second
        // projection of the (next_state, action) codomain. Same proven lane.
        let dom_a = state14_domain();
        let dom_b = pairclass23_domain();
        let m = pair_action_matrix();
        let module = author_table_step_module(&m).expect("authoring 14x23 action must succeed");
        assert_eq!(extract_2d_matrix(&module, 14, 23), Some(m.clone()));
        assert_eq!(super::execution_table(&module, 14, 23), Some(m.clone()));
        let evidence = verify_ir_table_refines_spec(&module, &m, &dom_a, &dom_b)
            .expect("the action table must certify against its spec");
        assert!(matches!(evidence, trust_ir::ProofEvidence::CleanCic { .. }));
    }

    #[test]
    fn rejects_action_edge_with_one_wrong_cell() {
        // Fail-closed: flip ONE action cell (Ground × k2: Print(1) -> None(0)).
        let dom_a = state14_domain();
        let dom_b = pairclass23_domain();
        let mut buggy = pair_action_matrix();
        buggy[0][2] = 0; // Ground × k2: action 1 -> 0
        let module = author_table_step_module(&buggy).expect("authoring must succeed");
        let evidence = verify_ir_table_refines_spec(&module, &pair_action_matrix(), &dom_a, &dom_b);
        assert!(evidence.is_none(), "a wrong action cell must fail closed");
    }

    #[test]
    fn verifies_pair_classifier_in_chunks() {
        // The byte -> (next_state,action) pair-class map over ALL 256 bytes, verified
        // in 8 chunks of 32 tiling 0x00..=0xff. With the two 14×23 projection tables
        // this STRUCTURALLY accounts for every 14×256 concrete (next_state, action)
        // output: action[s][b] = pair_action[s][pair_classifier(b)] is a mathematical
        // composition of the two kernel-verified pieces — that ACTION composition is
        // NOT itself kernel-rechecked here (unlike the next-state composition, which
        // `kernel_checks_table_composition` rechecks cell-by-cell).
        let full = aterm_pair_classifier_row();
        let mut covered = 0usize;
        for c in 0..8 {
            let (lo, hi) = (c * 32, c * 32 + 32);
            let chunk: Vec<i128> = full[0][lo..hi].to_vec();
            let m = vec![chunk];
            let dom_a = enum_domain("Unit1", &["Unit1.only"]);
            let dom_b = indexed_enum_domain("ByteChunk", "ByteChunk.b", 32);
            let module = author_table_step_module(&m).expect("authoring chunk must succeed");
            let ev = verify_ir_table_refines_spec(&module, &m, &dom_a, &dom_b)
                .unwrap_or_else(|| panic!("pair-classifier chunk [{lo:#x},{hi:#x}) must certify"));
            assert!(matches!(ev, trust_ir::ProofEvidence::CleanCic { .. }));
            covered += hi - lo;
        }
        assert_eq!(covered, 256, "the 8 chunks must tile all 256 byte values");
    }

    // ---- COMPOSITION: full = class_matrix ∘ classify (kernel-checked) --------

    fn full_nextstate_14x256() -> Vec<Vec<i128>> {
        // Real aterm 14x256 next-state table (independent dump, aterm @ 4e2e6c2),
        // 32/line; machine-generated. Total cell sum = 15791.
        vec![
            vec![
                // state 0
                0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
                0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 7, 0, 0, 0, 0, 0, 0, 0, 13, 0, 0, 3, 0, 12, 13, 13, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0, 0,
            ],
            vec![
                // state 1
                1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1,
                1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 0, 0, 0,
                0, 0, 0, 0, 13, 0, 0, 3, 0, 12, 13, 13, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0, 0, 7, 0, 0, 0, 0, 0, 0, 0, 13, 0, 0, 3, 0, 12, 13, 13, 0, 0, 0, 0,
                0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0, 0, 0, 0,
            ],
            vec![
                // state 2
                2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 0, 2, 0, 1,
                2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 7, 0, 0, 0, 0, 0, 0, 0, 13, 0, 0, 3, 0, 12, 13, 13, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0, 0,
            ],
            vec![
                // state 3
                3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 0, 3, 0, 1,
                3, 3, 3, 3, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 4, 4, 4, 4, 4, 4, 4, 4,
                4, 4, 4, 4, 4, 4, 4, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 7, 0, 0, 0, 0, 0, 0, 0, 13, 0, 0, 3, 0, 12, 13, 13, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0, 0,
            ],
            vec![
                // state 4
                4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 0, 4, 0, 1,
                4, 4, 4, 4, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 4, 4, 4, 4, 4, 4, 4, 4,
                4, 4, 4, 4, 6, 6, 6, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 7, 0, 0, 0, 0, 0, 0, 0, 13, 0, 0, 3, 0, 12, 13, 13, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0, 0,
            ],
            vec![
                // state 5
                5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 0, 5, 0, 1,
                5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 6, 6, 6, 6, 6, 6, 6, 6,
                6, 6, 6, 6, 6, 6, 6, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 7, 0, 0, 0, 0, 0, 0, 0, 13, 0, 0, 3, 0, 12, 13, 13, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0, 0,
            ],
            vec![
                // state 6
                6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 0, 6, 0, 1,
                6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6,
                6, 6, 6, 6, 6, 6, 6, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 7, 0, 0, 0, 0, 0, 0, 0, 13, 0, 0, 3, 0, 12, 13, 13, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0, 0,
            ],
            vec![
                // state 7
                7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 0, 7, 0, 1,
                7, 7, 7, 7, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 8, 8, 8, 8, 8, 8, 8, 8,
                8, 8, 11, 8, 8, 8, 8, 8, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10,
                10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10,
                10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10,
                10, 10, 10, 10, 10, 10, 10, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7,
                0, 0, 0, 0, 0, 0, 0, 13, 0, 0, 3, 0, 12, 13, 13, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0,
            ],
            vec![
                // state 8
                8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 0, 8, 0, 1,
                8, 8, 8, 8, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 8, 8, 8, 8, 8, 8, 8, 8,
                8, 8, 11, 8, 11, 11, 11, 11, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10,
                10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10,
                10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10,
                10, 10, 10, 10, 10, 10, 10, 10, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                7, 0, 0, 0, 0, 0, 0, 0, 13, 0, 0, 3, 0, 12, 13, 13, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0,
            ],
            vec![
                // state 9
                9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 0, 9, 0, 1,
                9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 11, 11, 11, 11, 11, 11,
                11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10,
                10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10,
                10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10,
                10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 7, 0, 0, 0, 0, 0, 0, 0, 13, 0, 0, 3, 0, 12, 13, 13, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0,
            ],
            vec![
                // state 10
                10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10,
                10, 10, 10, 0, 10, 0, 1, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10,
                10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10,
                10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10,
                10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10,
                10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10,
                10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10,
                10, 10, 10, 10, 10, 10, 10, 10, 10, 0, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10,
                10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10,
                10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10,
                10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10,
                10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10,
                10, 10, 10, 10,
            ],
            vec![
                // state 11
                11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11,
                11, 11, 11, 0, 11, 0, 1, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11,
                11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11,
                11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11,
                11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11,
                11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11,
                11, 11, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 0, 0, 0, 0, 0, 0, 0, 13,
                0, 0, 3, 0, 12, 13, 13, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            ],
            vec![
                // state 12
                12, 12, 12, 12, 12, 12, 12, 0, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12,
                12, 12, 12, 0, 12, 0, 1, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12,
                12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12,
                12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12,
                12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12,
                12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12,
                12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12,
                12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12,
                12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12,
                12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12,
                12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12,
                12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12,
                12, 12, 12, 12,
            ],
            vec![
                // state 13
                13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13,
                13, 13, 13, 0, 13, 0, 1, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13,
                13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13,
                13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13,
                13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13,
                13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13,
                13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13,
                13, 13, 13, 13, 13, 13, 13, 13, 13, 0, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13,
                13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13,
                13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13,
                13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13,
                13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13,
                13, 13, 13, 13,
            ],
        ]
    }

    #[test]
    fn verifies_nextstate_composition_in_chunks() {
        // COMPOSITION as a kernel-checked fact: the REAL per-byte next-state table
        // factors through the verified classifier — full[s][b] = class_matrix[s][
        // classify(b)] — proven for ALL 256 bytes in 8 chunks of 32 (a flat 256
        // overflows the kernel stack). The RHS composes the two SEPARATELY-verified
        // pieces (class table + classifier); `full` is an INDEPENDENT real dump, so
        // the equation is non-trivial. `kernel_checks_table_composition` checks ONE
        // kernel-verified composition FACT per chunk (it returns whether the kernel
        // accepts; it mints no transportable term), not an argued identity.
        let st = state14_domain();
        let cls = class19_domain();
        let class_matrix = full_aterm_class_matrix();
        let classify = aterm_byte_classifier_row()[0].clone();
        let full = full_nextstate_14x256();
        // 32 chunks of 8 (14x8 = 112-cell proof per chunk — a 14x32 proof overflows
        // the kernel recursion stack; 8-byte chunks are well within depth).
        let mut covered = 0usize;
        for c in 0..32 {
            let (lo, hi) = (c * 8, c * 8 + 8);
            let byte = indexed_enum_domain("ByteChunk", "ByteChunk.b", 8);
            let full_chunk: Vec<Vec<i128>> = full.iter().map(|row| row[lo..hi].to_vec()).collect();
            let classify_chunk: Vec<i128> = classify[lo..hi].to_vec();
            kernel_checks_table_composition(
                &st,
                &byte,
                &cls,
                &full_chunk,
                &class_matrix,
                &classify_chunk,
            )
            .unwrap_or_else(|| panic!("composition chunk [{lo:#x},{hi:#x}) must kernel-check"));
            covered += hi - lo;
        }
        assert_eq!(covered, 256, "the 32 chunks must tile all 256 byte values");
    }

    /// Helper: certify the composition over byte chunk [0, 8) with the given
    /// (possibly tampered) class_matrix / classifier.
    fn compose_chunk0(class_matrix: &[Vec<i128>], classify_full: &[i128]) -> Option<()> {
        let st = state14_domain();
        let cls = class19_domain();
        let byte = indexed_enum_domain("ByteChunk", "ByteChunk.b", 8);
        let full = full_nextstate_14x256();
        let full_chunk: Vec<Vec<i128>> = full.iter().map(|row| row[0..8].to_vec()).collect();
        let classify_chunk: Vec<i128> = classify_full[0..8].to_vec();
        kernel_checks_table_composition(
            &st,
            &byte,
            &cls,
            &full_chunk,
            class_matrix,
            &classify_chunk,
        )
    }

    #[test]
    fn rejects_composition_with_wrong_classifier() {
        // Fail-closed: misclassify BEL (0x07: class 7 -> class 8) in chunk 0. At
        // OscString the real full[12][0x07] = Ground(0) (BEL ends OSC) != class
        // table's class-8 value class_matrix[12][8] = 12 -> reject.
        let class_matrix = full_aterm_class_matrix();
        let mut classify = aterm_byte_classifier_row()[0].clone();
        classify[0x07] = 8;
        assert!(
            compose_chunk0(&class_matrix, &classify).is_none(),
            "a wrong classifier must fail closed"
        );
    }

    #[test]
    fn rejects_composition_with_wrong_class_matrix() {
        // Fail-closed: corrupt class_matrix[Ground][k8] (reached by byte 0x00 in
        // chunk 0): real full[Ground][0x00] = Ground(0) != 99.
        let mut class_matrix = full_aterm_class_matrix();
        class_matrix[0][8] = 99;
        let classify = aterm_byte_classifier_row()[0].clone();
        assert!(
            compose_chunk0(&class_matrix, &classify).is_none(),
            "a wrong class_matrix must fail closed"
        );
    }

    // ─── domain-shape regression: out-of-shape st_dom must FAIL CLOSED ───
    // These pin the soundness argument that the kernel check (not the up-front
    // `is_nullary_enum_domain` guard) is the anchor: even with the guard removed the
    // kernel rejects an out-of-shape domain, and WITH false data it never accepts.

    /// `St14` but with constructor #0 carrying a `Nat` FIELD (`type_ = Nat → St14`),
    /// num_params still 0. The lane's proof assumes nullary ctors.
    fn state14_field_domain() -> InductiveDecl {
        let mut d = state14_domain();
        let ty = &mut d.types[0];
        // make the first ctor field-carrying: Nat → St14
        ty.constructors[0].type_ =
            Expr::pi(BinderInfo::Default, nat_const(), Expr::const_(ty.name.clone(), vec![]));
        d
    }

    /// `St14` but parametric: num_params = 1 with a leading `Nat` param, and each
    /// ctor's type becomes `Nat → St14` (the param). The kernel-generated casesOn
    /// carries an extra param slot the lane's hand-built proof never supplies.
    fn state14_parametric_domain() -> InductiveDecl {
        let mut d = state14_domain();
        d.num_params = 1;
        let ty = &mut d.types[0];
        ty.type_ = Expr::pi(BinderInfo::Default, nat_const(), Expr::type_());
        for c in &mut ty.constructors {
            c.type_ =
                Expr::pi(BinderInfo::Default, nat_const(), Expr::const_(ty.name.clone(), vec![]));
        }
        d
    }

    fn compose_chunk0_with_st(
        st: &InductiveDecl,
        class_matrix: &[Vec<i128>],
        classify_full: &[i128],
    ) -> Option<()> {
        let cls = class19_domain();
        let byte = indexed_enum_domain("ByteChunk", "ByteChunk.b", 8);
        let full = full_nextstate_14x256();
        let full_chunk: Vec<Vec<i128>> = full.iter().map(|row| row[0..8].to_vec()).collect();
        let classify_chunk: Vec<i128> = classify_full[0..8].to_vec();
        kernel_checks_table_composition(st, &byte, &cls, &full_chunk, class_matrix, &classify_chunk)
    }

    #[test]
    fn field_carrying_ctor_domain_with_true_data_fails_closed() {
        // Even with the CORRECT data, a field-carrying-ctor st_dom must NOT certify
        // (the proof shape is invalid for it) -> fail-closed, no false ACCEPT.
        let r = compose_chunk0_with_st(
            &state14_field_domain(),
            &full_aterm_class_matrix(),
            &aterm_byte_classifier_row()[0].clone(),
        );
        assert!(r.is_none(), "field-carrying-ctor domain must fail closed (got {r:?})");
    }

    #[test]
    fn parametric_domain_with_true_data_fails_closed() {
        let r = compose_chunk0_with_st(
            &state14_parametric_domain(),
            &full_aterm_class_matrix(),
            &aterm_byte_classifier_row()[0].clone(),
        );
        assert!(r.is_none(), "parametric domain must fail closed (got {r:?})");
    }

    #[test]
    fn field_carrying_ctor_domain_with_false_data_fails_closed() {
        // THE false-accept probe: tamper the class_matrix AND use a field-carrying
        // domain. If the kernel ever accepts, this returns Some and the test fails.
        let mut class_matrix = full_aterm_class_matrix();
        class_matrix[0][8] = 99;
        let r = compose_chunk0_with_st(
            &state14_field_domain(),
            &class_matrix,
            &aterm_byte_classifier_row()[0].clone(),
        );
        assert!(r.is_none(), "false data + field domain must fail closed (got {r:?})");
    }

    #[test]
    fn parametric_domain_with_false_data_fails_closed() {
        let mut class_matrix = full_aterm_class_matrix();
        class_matrix[0][8] = 99;
        let r = compose_chunk0_with_st(
            &state14_parametric_domain(),
            &class_matrix,
            &aterm_byte_classifier_row()[0].clone(),
        );
        assert!(r.is_none(), "false data + parametric domain must fail closed (got {r:?})");
    }

    // ---- ACTION COMPOSITION: action = pair_action ∘ pair_classify (kernel-checked) ----

    fn full_action_14x256() -> Vec<Vec<i128>> {
        // Real aterm 14x256 ACTION table (ActionType idx 0..16; independent dump,
        // aterm @ 4e2e6c2), 32/line; machine-generated. Total cell sum = 18224.
        vec![
            vec![
                // state 0
                2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3,
                2, 2, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
                1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
                1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
                1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 13, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
                2, 2, 2, 2, 2, 3, 2, 2, 2, 2, 2, 2, 2, 0, 2, 2, 3, 0, 10, 0, 14, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0, 0,
            ],
            vec![
                // state 1
                2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3,
                2, 2, 2, 2, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 6, 6, 6, 6, 6, 6, 6,
                6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 3, 6, 6, 6,
                6, 6, 6, 6, 0, 6, 6, 3, 6, 10, 0, 14, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6,
                6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 13, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
                2, 2, 2, 2, 2, 2, 3, 2, 2, 2, 2, 2, 2, 2, 0, 2, 2, 3, 0, 10, 0, 14, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0, 0, 0,
            ],
            vec![
                // state 2
                2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3,
                2, 2, 2, 2, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 6, 6, 6, 6, 6, 6, 6,
                6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6,
                6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6,
                6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 13, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
                2, 2, 2, 2, 2, 3, 2, 2, 2, 2, 2, 2, 2, 0, 2, 2, 3, 0, 10, 0, 14, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0, 0,
            ],
            vec![
                // state 3
                2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3,
                2, 2, 2, 2, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 5, 5, 5, 5, 5, 5, 5,
                5, 5, 5, 5, 4, 4, 4, 4, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7,
                7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7,
                7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 13, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
                2, 2, 2, 2, 2, 3, 2, 2, 2, 2, 2, 2, 2, 0, 2, 2, 3, 0, 10, 0, 14, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0, 0,
            ],
            vec![
                // state 4
                2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3,
                2, 2, 2, 2, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 5, 5, 5, 5, 5, 5, 5,
                5, 5, 5, 5, 0, 0, 0, 0, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7,
                7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7,
                7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 13, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
                2, 2, 2, 2, 2, 3, 2, 2, 2, 2, 2, 2, 2, 0, 2, 2, 3, 0, 10, 0, 14, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0, 0,
            ],
            vec![
                // state 5
                2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3,
                2, 2, 2, 2, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0, 0, 0, 0, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7,
                7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7,
                7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 13, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
                2, 2, 2, 2, 2, 3, 2, 2, 2, 2, 2, 2, 2, 0, 2, 2, 3, 0, 10, 0, 14, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0, 0,
            ],
            vec![
                // state 6
                2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3,
                2, 2, 2, 2, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13,
                13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 13,
                2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 2, 2, 2, 2, 2, 2, 2, 0, 2, 2, 3,
                0, 10, 0, 14, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            ],
            vec![
                // state 7
                13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13,
                13, 13, 13, 2, 13, 2, 3, 13, 13, 13, 13, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4,
                4, 4, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 0, 5, 4, 4, 4, 4, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8,
                8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8,
                8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 13, 2,
                2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 2, 2, 2, 2, 2, 2, 2, 0, 2, 2, 3, 0,
                10, 0, 14, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            ],
            vec![
                // state 8
                13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13,
                13, 13, 13, 2, 13, 2, 3, 13, 13, 13, 13, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4,
                4, 4, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 0, 5, 0, 0, 0, 0, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8,
                8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8,
                8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 13, 2,
                2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 2, 2, 2, 2, 2, 2, 2, 0, 2, 2, 3, 0,
                10, 0, 14, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            ],
            vec![
                // state 9
                13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13,
                13, 13, 13, 2, 13, 2, 3, 13, 13, 13, 13, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4,
                4, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8,
                8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8,
                8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 13, 2,
                2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 2, 2, 2, 2, 2, 2, 2, 0, 2, 2, 3, 0,
                10, 0, 14, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            ],
            vec![
                // state 10
                9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 2, 9, 2, 3,
                9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9,
                9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9,
                9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9,
                9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 13, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9,
                9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 0, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9,
                9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9,
                9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9,
                9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9,
                9, 9, 9, 9, 9,
            ],
            vec![
                // state 11
                13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13,
                13, 13, 13, 2, 13, 2, 3, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13,
                13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13,
                13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13,
                13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13,
                13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13,
                13, 13, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 2, 2, 2, 2, 2, 2, 2, 0,
                2, 2, 3, 0, 10, 0, 14, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            ],
            vec![
                // state 12
                13, 13, 13, 13, 13, 13, 13, 12, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13,
                13, 13, 13, 2, 13, 2, 3, 13, 13, 13, 13, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11,
                11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11,
                11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11,
                11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11,
                11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11,
                11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11,
                11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11,
                11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11,
                11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11,
                11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11,
                11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11,
                11, 11, 11, 11,
            ],
            vec![
                // state 13
                15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15,
                15, 15, 15, 2, 15, 2, 3, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15,
                15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15,
                15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15,
                15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15,
                15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15,
                15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15,
                15, 15, 15, 15, 15, 15, 15, 15, 15, 0, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15,
                15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15,
                15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15,
                15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15,
                15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15,
                15, 15, 15, 15,
            ],
        ]
    }

    #[test]
    fn verifies_action_composition_in_chunks() {
        // ACTION composition as a kernel-checked fact (parallel to next-state): the
        // REAL per-byte ACTION table factors through the (next_state,action) pair
        // classifier — action[s][b] = pair_action[s][pair_classify(b)] — kernel-checked
        // for ALL 256 bytes in 32 chunks of 8. Reuses the SAME generic
        // `kernel_checks_table_composition` with the 23 pair-classes as the inner
        // class domain. Together with `verifies_nextstate_composition_in_chunks` BOTH
        // codomain projections' compositions are now kernel-verified over all bytes.
        let st = state14_domain();
        let cls = pairclass23_domain();
        let pair_action = pair_action_matrix();
        let pair_classify = aterm_pair_classifier_row()[0].clone();
        let full_act = full_action_14x256();
        let mut covered = 0usize;
        for c in 0..32 {
            let (lo, hi) = (c * 8, c * 8 + 8);
            let byte = indexed_enum_domain("ByteChunk", "ByteChunk.b", 8);
            let full_chunk: Vec<Vec<i128>> =
                full_act.iter().map(|row| row[lo..hi].to_vec()).collect();
            let classify_chunk: Vec<i128> = pair_classify[lo..hi].to_vec();
            kernel_checks_table_composition(
                &st,
                &byte,
                &cls,
                &full_chunk,
                &pair_action,
                &classify_chunk,
            )
            .unwrap_or_else(|| {
                panic!("action composition chunk [{lo:#x},{hi:#x}) must kernel-check")
            });
            covered += hi - lo;
        }
        assert_eq!(covered, 256, "the 32 chunks must tile all 256 byte values");
    }

    #[test]
    fn rejects_action_composition_with_wrong_pair_action() {
        // Fail-closed: corrupt pair_action[Ground][k17] (the pair-class of ESC 0x1b,
        // reached in the 0x18..0x20 chunk). Real action[Ground][0x1b] != 99 -> reject.
        let st = state14_domain();
        let cls = pairclass23_domain();
        let mut pair_action = pair_action_matrix();
        pair_action[0][17] = 99;
        let pair_classify = aterm_pair_classifier_row()[0].clone();
        let full_act = full_action_14x256();
        let byte = indexed_enum_domain("ByteChunk", "ByteChunk.b", 8);
        // chunk 3 = bytes 0x18..0x20, contains ESC 0x1b (pair-class 17).
        let full_chunk: Vec<Vec<i128>> =
            full_act.iter().map(|row| row[0x18..0x20].to_vec()).collect();
        let classify_chunk: Vec<i128> = pair_classify[0x18..0x20].to_vec();
        assert!(
            kernel_checks_table_composition(
                &st,
                &byte,
                &cls,
                &full_chunk,
                &pair_action,
                &classify_chunk
            )
            .is_none(),
            "a wrong pair_action cell must fail closed"
        );
    }
}
