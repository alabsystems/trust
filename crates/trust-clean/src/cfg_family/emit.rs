// Trust: M4 v0 — the Lean emitter (design §3, templates T0/T1/T2/T3/T4/T8;
// T5-C0 composition; T5-C1/T7 deliberately NOT implemented in v0 — see
// `spec.rs`'s module doc and `envelope.rs`'s `UnmeasuredComposition`).
//
// ANTI-INJECTION: every function here renders Lean by matching on the typed
// enums from `spec.rs`/`plan.rs` and formatting their numeral/ident
// payloads — never by splicing an arbitrary caller string into a `r#"…"#`
// fragment (design §2, requirement 4).
//
// The emitter produces STATEMENTS ONLY; nothing here is trusted (design §2's
// "Trust story"). Every statement text this module returns is independently
// elaborated + kernel-rechecked by `gate.rs` exactly like a hand-written
// bridge arm — a bug here surfaces as a pinned `rfl`/`rw` failure or an
// accepted-forgery hard error, never as a silent green.

use super::plan::{FamilyPlan, Known, RetVal, Visit, VisitOutcome, VisitShape};
use super::spec::{BlockSpec, InstSpec, TermSpec, TyLit};

/// One visit's generated Lean: 1 declaration (ground) or 2 (chain+connect).
pub struct EmittedVisit {
    pub label: String,
    /// Theorem name(s) `gate.rs` must `require_empty_axiom_deps` on, in load
    /// order.
    pub names: Vec<&'static str>,
    pub names_owned: Vec<String>,
    pub src: String,
}

pub struct EmittedFamily {
    pub fixtures_src: String,
    pub visits: Vec<EmittedVisit>,
    pub composed_name: String,
    pub composed_src: String,
    /// Exactly 2 probes (T8; Spot mode uses `[..1]`).
    pub probes: Vec<(String, String)>,
}

fn block_name(prefix: &str, i: usize) -> String {
    format!("{prefix}_block{i}")
}
fn cfg_name(prefix: &str) -> String {
    format!("{prefix}_cfg")
}
fn state_name(prefix: &str, k: usize) -> String {
    format!("{prefix}_state{k}")
}

/// Groups adjacent symbolic idents by their Lean SCALAR carrier (`Int` vs
/// `Bool` — `TrustIr.Value.int`'s payload is always `Int` regardless of
/// declared bit width, so every non-`Bool` `TyLit` shares one binder group)
/// and renders `(v_l v_r : Int)`-style binder clauses.
fn render_symbolic_binders(idents: &[(&'static str, TyLit)]) -> String {
    if idents.is_empty() {
        return String::new();
    }
    let mut groups: Vec<(Vec<&'static str>, &'static str)> = Vec::new();
    for (ident, ty) in idents {
        let carrier = if matches!(ty, TyLit::Bool) { "Bool" } else { "Int" };
        if let Some(last) = groups.last_mut() {
            if last.1 == carrier {
                last.0.push(ident);
                continue;
            }
        }
        groups.push((vec![ident], carrier));
    }
    groups
        .into_iter()
        .map(|(names, carrier)| format!("({} : {carrier})", names.join(" ")))
        .collect::<Vec<_>>()
        .join(" ")
}

/// The application `v_l v_r` (bare idents, no binder syntax) — used to apply
/// a parameterized state def.
fn symbolic_apply(idents: &[(&'static str, TyLit)]) -> String {
    idents.iter().map(|(id, _)| *id).collect::<Vec<_>>().join(" ")
}

fn render_block_def(prefix: &str, i: usize, block: &BlockSpec) -> String {
    let name = block_name(prefix, i);
    let params = block
        .params
        .iter()
        .map(|(vid, ty)| format!("(TrustIr.ValueId.mk {vid}, {})", ty.lean()))
        .collect::<Vec<_>>()
        .join(", ");
    let (body, dests) = match block.insts.first() {
        Some(InstSpec::BinOp { op, ty, lhs, rhs }) => {
            let dest = block.dests[0];
            (
                format!(
                    "[TrustIr.Inst.BinOp {} {} (TrustIr.ValueId.mk {lhs}) (TrustIr.ValueId.mk {rhs})]",
                    op.lean(),
                    ty.lean()
                ),
                format!("[[TrustIr.ValueId.mk {dest}]]"),
            )
        }
        None => ("[]".to_string(), "[]".to_string()),
    };
    let term = match block.term {
        TermSpec::Return(ids) => {
            let ids_s = ids
                .iter()
                .map(|id| format!("TrustIr.ValueId.mk {id}"))
                .collect::<Vec<_>>()
                .join(", ");
            format!("TrustIr.Inst.Return [{ids_s}]")
        }
        TermSpec::Br { target, args } => {
            let args_s = args
                .iter()
                .map(|id| format!("TrustIr.ValueId.mk {id}"))
                .collect::<Vec<_>>()
                .join(", ");
            format!("TrustIr.Inst.Br (TrustIr.BlockId.mk {target}) [{args_s}]")
        }
    };
    format!(
        "def {name} : TrustIr.BasicBlock :=\n  {{ params := [{params}]\n  , body := {body}\n  , bodyResultDests := {dests}\n  , terminator := {term}\n  , terminatorResultDests := [] }}\n"
    )
}

fn render_cfg_def(prefix: &str, plan: &FamilyPlan) -> String {
    let name = cfg_name(prefix);
    let mut arms = String::new();
    for i in 0..plan.spec.blocks.len() {
        arms.push_str(&format!("  | {i} => some {}\n", block_name(prefix, i)));
    }
    format!("def {name} : TrustIr.CFG := fun bb =>\n  match bb.index with\n{arms}  | _ => none\n")
}

/// T0 (state-def half, design §3): for every NON-terminal (`Br`) visit, a
/// named post-state def that the NEXT visit's `pre_state_expr` references
/// by name (W4 — never re-inlining history: `{p}State{k} := { {p}State{k-1}
/// with … }`). A single-visit (always-terminal) family emits none — v0's
/// original two families (`gen_block_add`/`gen_block_add_sym`) are
/// byte-for-byte unaffected by this function's addition. When symbolic
/// idents flow into the state, the def is parameterized (`{p}State{k}
/// (v_l v_r : Int) : …`), matching `pre_state_expr`'s existing "apply the
/// def" rendering for k > 1 (that half was already implemented — only the
/// def itself was missing, which is why no registered family ever
/// exercised a k > 1 visit before this increment).
fn render_state_defs(plan: &FamilyPlan) -> String {
    let prefix = plan.spec.name;
    let mut s = String::new();
    for visit in &plan.visits {
        if !matches!(visit.outcome, VisitOutcome::Br { .. }) {
            continue;
        }
        let block = &plan.spec.blocks[visit.pc];
        let name = state_name(prefix, visit.k);
        let params = if plan.symbolic_idents.is_empty() {
            String::new()
        } else {
            format!(" {}", render_symbolic_binders(&plan.symbolic_idents))
        };
        // A pending (unfolded) instruction's result has no top-level-valid
        // name inside a standalone `def` (a `match … | .ok result => …`
        // binder is only in scope inside ITS OWN theorem) — use the
        // cited-lemma value expression instead (`Int.add v_l v_r`), the
        // same substitution T4's connect theorem already uses. Not
        // exercised by any v0 registered family (all-ground), but correct
        // for the SymbolicCoreNonTerminal shape `plan.rs` already types.
        let subst = visit.inst.and_then(|inst| {
            inst.folded.is_none().then(|| {
                format!(
                    "{} {} {}",
                    inst.op.value_fn(),
                    inst.lhs.as_scalar_lean(),
                    inst.rhs.as_scalar_lean()
                )
            })
        });
        let literal = render_state_literal(prefix, plan, visit, block, subst.as_deref());
        s.push_str(&format!("def {name}{params} : TrustIr.MachineState :=\n  {literal}\n"));
    }
    s
}

/// T0. Emitted once per family, before any per-visit theorem.
pub fn render_fixtures(plan: &FamilyPlan) -> String {
    let prefix = plan.spec.name;
    let mut s = String::new();
    for (i, b) in plan.spec.blocks.iter().enumerate() {
        s.push_str(&render_block_def(prefix, i, b));
    }
    s.push_str(&render_cfg_def(prefix, plan));
    s.push_str(&render_state_defs(plan));
    s
}

fn render_args_list(visit: &Visit, block: &BlockSpec) -> String {
    visit
        .args
        .iter()
        .zip(block.params.iter())
        .map(|(k, (_, ty))| k.as_value_lean(*ty))
        .collect::<Vec<_>>()
        .join(", ")
}

/// The LHS's pre-state expression: `TrustIr.MachineState.empty` at k = 1,
/// else the previous visit's named (and, if symbolic, applied) state.
fn pre_state_expr(prefix: &str, plan: &FamilyPlan, visit: &Visit) -> String {
    if visit.pre_state_is_empty {
        "TrustIr.MachineState.empty".to_string()
    } else {
        let name = state_name(prefix, visit.k - 1);
        if plan.symbolic_idents.is_empty() {
            name
        } else {
            format!("({name} {})", symbolic_apply(&plan.symbolic_idents))
        }
    }
}

/// Render one return/branch-arg value, substituting `subst` (a bare scalar
/// Lean expression, e.g. `"result"` or `"Int.add v_l v_r"`) for
/// `RetVal::InstResult`.
fn render_ret_val(rv: RetVal, width: u32, subst: &str) -> String {
    match rv {
        RetVal::Known(k, ty) => k.as_value_lean(ty),
        // `subst` is a multi-token expression (`result` or `Int.add v_l
        // v_r`) — wrap it. Lean's greedy application parser does not treat
        // a list's `,`/`]` as a boundary for an EARLIER argument's own
        // sub-terms, so leaving this bare parses as a 4-argument
        // application of `Value.int` even inside `[…]`.
        RetVal::InstResult => format!("TrustIr.Value.int {width} ({subst})"),
    }
}

/// The state literal (W4: `.set` per param, then fresh-then-dest DOUBLE
/// `.set` per instruction — always both, even when the ids coincide) for one
/// visit's post-state, substituting `subst` for the instruction's own
/// result value. `subst = None` is only valid when the visit has no pending
/// instruction (ground fold or no instruction at all).
fn render_state_literal(
    prefix: &str,
    plan: &FamilyPlan,
    visit: &Visit,
    block: &BlockSpec,
    subst: Option<&str>,
) -> String {
    let base = pre_state_expr(prefix, plan, visit);
    let mut chain = if visit.pre_state_is_empty {
        "TrustIr.ValueMap.empty".to_string()
    } else {
        format!("{base}.locals")
    };
    // NOTE: every value spliced in as a `.set` ARGUMENT below is wrapped in
    // its OWN parens. Lean application is whitespace juxtaposition, so
    // `.set (mk 0) TrustIr.Value.int 8 3` parses as a FOUR-argument
    // application (`.set (mk 0) TrustIr.Value.int 8 3`), not
    // `.set (mk 0) (TrustIr.Value.int 8 3)` — the exact bug the v0.1 draft
    // of this emitter shipped (`StructureFieldTypeMismatch` /
    // `Discriminant(6) vs Discriminant(3)`: the elaborator tried to unify
    // the bare un-applied `TrustIr.Value.int` constructor against `Value`).
    for ((vid, ty), a) in block.params.iter().zip(visit.args.iter()) {
        chain = format!("({chain}.set (TrustIr.ValueId.mk {vid}) ({}))", a.as_value_lean(*ty));
    }
    if let Some(inst) = visit.inst {
        let value_expr = match (inst.folded, subst) {
            (Some(k), _) => k.as_value_lean(TyLit::from_width(inst.width)),
            (None, Some(s)) => format!("TrustIr.Value.int {} ({s})", inst.width),
            (None, None) => panic!("symbolic-core visit rendered without a result substitution"),
        };
        chain = format!("({chain}.set (TrustIr.ValueId.mk {}) ({value_expr}))", inst.fresh_id);
        chain = format!("({chain}.set (TrustIr.ValueId.mk {}) ({value_expr}))", inst.dest);
    }
    format!(
        "{{ {base} with\n      locals :=\n        {chain},\n      nextValueId := {} }}",
        visit.next_value_id
    )
}

fn lhs_app(prefix: &str, visit: &Visit, block: &BlockSpec, fuel: &str) -> String {
    format!(
        "TrustIr.stepNWithContext TrustIr.EvalContext.empty {fuel} 0 {} (TrustIr.BlockId.mk {}) [{}]",
        cfg_name(prefix),
        visit.pc,
        render_args_list(visit, block)
    )
}

fn theorem_name(prefix: &str, k: usize) -> String {
    format!("{prefix}_visit{k}")
}

/// T1/T2 — a plain `rfl` visit (ground operands only; no `bridge_<op>`
/// citation needed). Terminal (`Return`) or non-terminal (`Br`).
fn render_ground_visit(plan: &FamilyPlan, visit: &Visit) -> EmittedVisit {
    let prefix = plan.spec.name;
    let block = &plan.spec.blocks[visit.pc];
    let name = theorem_name(prefix, visit.k);
    let pre = pre_state_expr(prefix, plan, visit);
    let lhs = lhs_app(prefix, visit, block, "(Nat.succ f)");
    let width = visit.inst.map_or(0, |i| i.width);
    let rhs = match &visit.outcome {
        VisitOutcome::Return(ret) => {
            let vals =
                ret.iter().map(|r| render_ret_val(*r, width, "")).collect::<Vec<_>>().join(", ");
            let state = render_state_literal(prefix, plan, visit, block, None);
            format!("Except.ok ([{vals}], {state})")
        }
        VisitOutcome::Br { target_pc, args } => {
            let vals =
                args.iter().map(|r| render_ret_val(*r, width, "")).collect::<Vec<_>>().join(", ");
            let next_lhs = format!(
                "TrustIr.stepNWithContext TrustIr.EvalContext.empty f 0 {} (TrustIr.BlockId.mk {})",
                cfg_name(prefix),
                target_pc
            );
            let state = render_state_literal(prefix, plan, visit, block, None);
            format!("TrustIr.Sem.run\n      ({next_lhs} [{vals}])\n      {state}")
        }
    };
    let src = format!(
        "theorem {name} (f : Nat) :\n    TrustIr.Sem.run\n      ({lhs})\n      {pre}\n    =\n    {rhs} := rfl\n"
    );
    EmittedVisit {
        label: format!("visit{}", visit.k),
        names: Vec::new(),
        names_owned: vec![name],
        src,
    }
}

/// T3/T4 — the symbolic-core split (chain, `rfl`, `match semIntBinOp … with`
/// staying stuck on the symbolic operands; connect, kernel-checked `rw`
/// citing the chain and `bridge_<op>`). Terminal or non-terminal.
fn render_symbolic_core_visit(plan: &FamilyPlan, visit: &Visit) -> EmittedVisit {
    let prefix = plan.spec.name;
    let block = &plan.spec.blocks[visit.pc];
    let inst = visit.inst.expect("SymbolicCore visit must carry a pending instruction");
    let chain_name = format!("{prefix}_visit{}_chain", visit.k);
    let connect_name = theorem_name(prefix, visit.k);
    let binders = render_symbolic_binders(&plan.symbolic_idents);
    let pre = pre_state_expr(prefix, plan, visit);
    let lhs = lhs_app(prefix, visit, block, "(Nat.succ f)");

    let value_fn_expr = format!(
        "{} {} {}",
        inst.op.value_fn(),
        inst.lhs.as_scalar_lean(),
        inst.rhs.as_scalar_lean()
    );

    let render_rhs = |subst: &str| -> String {
        match &visit.outcome {
            VisitOutcome::Return(ret) => {
                let vals = ret
                    .iter()
                    .map(|r| render_ret_val(*r, inst.width, subst))
                    .collect::<Vec<_>>()
                    .join(", ");
                let state = render_state_literal(prefix, plan, visit, block, Some(subst));
                format!("Except.ok ([{vals}], {state})")
            }
            VisitOutcome::Br { target_pc, args } => {
                let vals = args
                    .iter()
                    .map(|r| render_ret_val(*r, inst.width, subst))
                    .collect::<Vec<_>>()
                    .join(", ");
                let next_lhs = format!(
                    "TrustIr.stepNWithContext TrustIr.EvalContext.empty f 0 {} (TrustIr.BlockId.mk {})",
                    cfg_name(prefix),
                    target_pc
                );
                let state = render_state_literal(prefix, plan, visit, block, Some(subst));
                format!("TrustIr.Sem.run\n        ({next_lhs} [{vals}])\n        {state}")
            }
        }
    };

    // T3 — chain: `match semIntBinOp op w l r with | .ok result => … | .error e => Except.error e`.
    let chain_rhs_ok = render_rhs("result");
    let chain_src = format!(
        "theorem {chain_name} {binders} (f : Nat) :\n    TrustIr.Sem.run\n      ({lhs})\n      {pre}\n    =\n    match TrustIr.semIntBinOp {} {} {} {} with\n    | .ok result =>\n        {chain_rhs_ok}\n    | .error e => Except.error e := rfl\n",
        inst.op.lean(),
        inst.width,
        inst.lhs.as_scalar_lean(),
        inst.rhs.as_scalar_lean(),
    );

    // T4 — connect: rewrite the chain and then its symbolic value core with
    // `bridge_<op>`. Clean's `rw` emits an explicit `Eq.subst` witness and
    // kernel-checks it, while avoiding the general term elaborator's premature
    // rigid-head comparison of the iota-redex against the outer result pair.
    let connect_rhs = render_rhs(&value_fn_expr);
    let h0 = format!("0 ≤ {value_fn_expr}");
    let h1 = format!("{value_fn_expr} < (2 : Int) ^ {}", inst.width);
    let bridge_call = format!(
        "{} {} {} {} h0 h1",
        inst.op.bridge_lemma(),
        inst.width,
        inst.lhs.as_scalar_lean(),
        inst.rhs.as_scalar_lean()
    );
    let connect_src = format!(
        "theorem {connect_name} {binders} (h0 : {h0}) (h1 : {h1}) (f : Nat) :\n    TrustIr.Sem.run\n      ({lhs})\n      {pre}\n    =\n    {connect_rhs} :=\n  by\n    rw [{chain_name} {} f, {bridge_call}]\n",
        symbolic_apply(&plan.symbolic_idents),
    );

    EmittedVisit {
        label: format!("visit{}", visit.k),
        names: Vec::new(),
        names_owned: vec![chain_name, connect_name],
        src: format!("{chain_src}\n{connect_src}"),
    }
}

fn render_visit(plan: &FamilyPlan, visit: &Visit) -> EmittedVisit {
    match visit.shape {
        VisitShape::GroundRflTerminal | VisitShape::GroundRflNonTerminal => {
            render_ground_visit(plan, visit)
        }
        VisitShape::SymbolicCoreTerminal | VisitShape::SymbolicCoreNonTerminal => {
            render_symbolic_core_visit(plan, visit)
        }
    }
}

/// T5-C0 — the composed conjunction. For N > 1 visits this is a genuine
/// `And.intro`-folded conjunction of every visit's own theorem, restated
/// verbatim (design §3, T5 "C0"): each conjunct stays binder-stuck at its
/// own visit (E1), so the composed declaration adds zero reduction work
/// over what every per-visit theorem already proved. For v0's original
/// single-visit families this degenerates to the bare restatement (no `∧`
/// for a lone conjunct) — matching `STEPBLOCK_COMPOSED_SRC`'s own
/// "singleton conjunction" precedent, and producing byte-identical Lean to
/// the pre-M4.1 single-visit code path (the added parens around the proof
/// lambda are a no-op to Lean's elaborator).
fn render_composed(plan: &FamilyPlan, emitted: &[EmittedVisit]) -> (String, String) {
    let prefix = plan.spec.name;
    let name = format!("{prefix}_agreement_all");
    let binders = render_symbolic_binders(&plan.symbolic_idents);
    let apply = symbolic_apply(&plan.symbolic_idents);

    let mut types: Vec<String> = Vec::with_capacity(plan.visits.len());
    let mut proofs: Vec<String> = Vec::with_capacity(plan.visits.len());

    for (visit, ev) in plan.visits.iter().zip(emitted.iter()) {
        let block = &plan.spec.blocks[visit.pc];
        let lhs = lhs_app(prefix, visit, block, "(Nat.succ f)");
        let pre = pre_state_expr(prefix, plan, visit);
        let last_name = ev.names_owned.last().expect("visit emits at least one theorem").clone();

        let (hyp_binders, hyp_args, rhs) = match visit.shape {
            VisitShape::SymbolicCoreTerminal | VisitShape::SymbolicCoreNonTerminal => {
                let inst = visit.inst.expect("symbolic-core visit has an instruction");
                let value_fn_expr = format!(
                    "{} {} {}",
                    inst.op.value_fn(),
                    inst.lhs.as_scalar_lean(),
                    inst.rhs.as_scalar_lean()
                );
                let h0 = format!("0 ≤ {value_fn_expr}");
                let h1 = format!("{value_fn_expr} < (2 : Int) ^ {}", inst.width);
                let rhs = match &visit.outcome {
                    VisitOutcome::Return(ret) => {
                        let vals = ret
                            .iter()
                            .map(|r| render_ret_val(*r, inst.width, &value_fn_expr))
                            .collect::<Vec<_>>()
                            .join(", ");
                        let state =
                            render_state_literal(prefix, plan, visit, block, Some(&value_fn_expr));
                        format!("Except.ok ([{vals}], {state})")
                    }
                    VisitOutcome::Br { target_pc, args } => {
                        let vals = args
                            .iter()
                            .map(|r| render_ret_val(*r, inst.width, &value_fn_expr))
                            .collect::<Vec<_>>()
                            .join(", ");
                        let next_lhs = format!(
                            "TrustIr.stepNWithContext TrustIr.EvalContext.empty f 0 {} (TrustIr.BlockId.mk {})",
                            cfg_name(prefix),
                            target_pc
                        );
                        let state =
                            render_state_literal(prefix, plan, visit, block, Some(&value_fn_expr));
                        format!("TrustIr.Sem.run\n        ({next_lhs} [{vals}])\n        {state}")
                    }
                };
                (format!("(h0 : {h0}) (h1 : {h1}) "), " h0 h1".to_string(), rhs)
            }
            VisitShape::GroundRflTerminal | VisitShape::GroundRflNonTerminal => {
                let width = visit.inst.map_or(0, |i| i.width);
                let rhs = match &visit.outcome {
                    VisitOutcome::Return(ret) => {
                        let vals = ret
                            .iter()
                            .map(|r| render_ret_val(*r, width, ""))
                            .collect::<Vec<_>>()
                            .join(", ");
                        let state = render_state_literal(prefix, plan, visit, block, None);
                        format!("Except.ok ([{vals}], {state})")
                    }
                    VisitOutcome::Br { target_pc, args } => {
                        let vals = args
                            .iter()
                            .map(|r| render_ret_val(*r, width, ""))
                            .collect::<Vec<_>>()
                            .join(", ");
                        let next_lhs = format!(
                            "TrustIr.stepNWithContext TrustIr.EvalContext.empty f 0 {} (TrustIr.BlockId.mk {})",
                            cfg_name(prefix),
                            target_pc
                        );
                        let state = render_state_literal(prefix, plan, visit, block, None);
                        format!("TrustIr.Sem.run\n      ({next_lhs} [{vals}])\n      {state}")
                    }
                };
                (String::new(), String::new(), rhs)
            }
        };

        types.push(format!(
            "∀ {binders} {hyp_binders}(f : Nat),\n      TrustIr.Sem.run\n        ({lhs})\n        {pre}\n      =\n      {rhs}"
        ));
        proofs.push(format!(
            "(fun {apply} {}f => {last_name} {apply}{hyp_args} f)",
            if hyp_binders.is_empty() { "" } else { "h0 h1 " }
        ));
    }

    // PRECEDENCE (learned from the first Full-mode kernel run of a 2-visit
    // family, which was kernel-REJECTED here — fail-closed working exactly
    // as designed): Lean's `∀` binder extends as far right as possible, so
    // an unparenthesized `∀ f, A = B ∧ ∀ f, C = D` parses as
    // `∀ f, (A = B ∧ ∀ f, C = D)` — NOT the intended conjunction of two
    // closed statements. Each conjunct must be parenthesized, exactly as
    // the hand-written `STEPBRANCH_COMPOSED_SRC`/`STEPLOOP` composed
    // theorems do: `(∀ (a b : Int), …) ∧ (∀ (a b : Int), …)`. The lone-
    // conjunct case stays bare for byte-compatibility with the v0 families'
    // already-kernel-validated composed shape.
    let ty = if types.len() == 1 {
        types[0].clone()
    } else {
        types.iter().map(|t| format!("({t})")).collect::<Vec<_>>().join("\n  ∧ ")
    };
    let proof = fold_and_intro(&proofs);
    let src = format!("theorem {name} :\n    {ty} :=\n  {proof}\n");
    (name, src)
}

/// Right-nest `And.intro` over N ≥ 1 per-visit proof terms — N = 1 is just
/// the bare term (no conjunction to fold), matching v0's original
/// single-visit composed theorem exactly.
fn fold_and_intro(proofs: &[String]) -> String {
    match proofs.split_first() {
        None => unreachable!("plan_family always plans at least one visit"),
        Some((first, [])) => first.clone(),
        Some((first, rest)) => format!("And.intro {first} ({})", fold_and_intro(rest)),
    }
}

/// T8 rule 1/3 — the terminal-value-mutation probe(s), always derived from
/// the LAST (necessarily `Terminal`, `Return`-ending — `plan_family` only
/// ever breaks its trace loop on `TermSpec::Return`) visit, so a
/// multi-visit family's earlier `Br` visits never reach this function's
/// `unreachable!` arm.
fn render_terminal_probes(plan: &FamilyPlan) -> Vec<(String, String)> {
    let prefix = plan.spec.name;
    let visit = plan.visits.last().expect("plan_family always plans at least one visit");
    let block = &plan.spec.blocks[visit.pc];
    let binders = render_symbolic_binders(&plan.symbolic_idents);
    let pre = pre_state_expr(prefix, plan, visit);
    let lhs = lhs_app(prefix, visit, block, "(Nat.succ f)");

    match visit.shape {
        VisitShape::GroundRflTerminal => {
            // Precondition of THIS render path (not a general truth): v0's
            // only registered `GroundRflTerminal` family has one
            // instruction. A zero-instruction ground passthrough family
            // would need its own probe derivation (fallback #3's "operand
            // order swap" doesn't apply either) — not attempted in v0.
            visit.inst.expect("ground terminal probe needs an instruction");
            let VisitOutcome::Return(ret) = &visit.outcome else {
                unreachable!("v0 only probes terminal visits")
            };
            let true_val = ret[0];
            let RetVal::Known(Known::Ground(true_lit), _) = true_val else {
                unreachable!("ground visit's return value is always a folded ground literal")
            };
            let true_state = render_state_literal(prefix, plan, visit, block, None);
            // Probe 1: wrong final value (bump the numeral by one — still a
            // genuinely different, decidably-false claim for ground ints).
            let wrong_value = match true_lit {
                super::spec::ValueLit::Int { width, value } => {
                    format!("TrustIr.Value.int {width} {}", value + 1)
                }
                super::spec::ValueLit::Bool(b) => format!("TrustIr.Value.bool {}", !b),
            };
            let p1 = format!(
                "theorem {prefix}_visit{}_WRONG_VALUE (f : Nat) :\n    TrustIr.Sem.run\n      ({lhs})\n      {pre}\n    = Except.ok ([{wrong_value}], {true_state}) := rfl\n",
                visit.k
            );
            // Probe 2: wrong width on the SAME numeral (fallback #3 — no
            // branch to mutate a successor-pc on, no symbolic operand-order
            // to swap).
            let wrong_width = match true_lit {
                super::spec::ValueLit::Int { width, value } => {
                    format!("TrustIr.Value.int {} {value}", width + 8)
                }
                super::spec::ValueLit::Bool(b) => format!("TrustIr.Value.bool {b}"),
            };
            let p2 = format!(
                "theorem {prefix}_visit{}_WRONG_WIDTH (f : Nat) :\n    TrustIr.Sem.run\n      ({lhs})\n      {pre}\n    = Except.ok ([{wrong_width}], {true_state}) := rfl\n",
                visit.k
            );
            vec![
                ("wrong-final-value (result numeral off by one)".to_string(), p1),
                ("wrong-width (claims a different bit width for the same numeral)".to_string(), p2),
            ]
        }
        VisitShape::SymbolicCoreTerminal => {
            let inst = visit.inst.expect("symbolic-core probe needs an instruction");
            let sub = inst.op.subtract_variant();
            let true_state = render_state_literal(
                prefix,
                plan,
                visit,
                block,
                Some(&format!(
                    "{} {} {}",
                    inst.op.value_fn(),
                    inst.lhs.as_scalar_lean(),
                    inst.rhs.as_scalar_lean()
                )),
            );
            // Probe 1: wrong final value — claim the OTHER op's value
            // (Add's forgery claims Sub's value, matching
            // `bridge_stepblock_add_return_WRONG_VALUE`'s exact rationale:
            // a genuinely different, non-commutative claim for symbolic
            // operands).
            let wrong_value_expr =
                format!("{} {} {}", sub, inst.lhs.as_scalar_lean(), inst.rhs.as_scalar_lean());
            let p1 = format!(
                "theorem {prefix}_visit{}_WRONG_VALUE {binders} (f : Nat) :\n    TrustIr.Sem.run\n      ({lhs})\n      {pre}\n    =\n    (match TrustIr.semIntBinOp {} {} {} {} with\n      | .ok _ =>\n          Except.ok ([TrustIr.Value.int {} ({wrong_value_expr})], {true_state})\n      | .error e => Except.error e) := rfl\n",
                visit.k,
                inst.op.lean(),
                inst.width,
                inst.lhs.as_scalar_lean(),
                inst.rhs.as_scalar_lean(),
                inst.width,
            );
            // Probe 2: wrong-operand-threaded-to-terminator — claims the
            // block returns the RAW lhs operand instead of the
            // instruction's own result (mirrors
            // `bridge_stepblock_add_return_WRONG_OPERAND` exactly).
            let p2 = format!(
                "theorem {prefix}_visit{}_WRONG_OPERAND {binders} (f : Nat) :\n    TrustIr.Sem.run\n      ({lhs})\n      {pre}\n    = Except.ok ([TrustIr.Value.int {} {}], {true_state}) := rfl\n",
                visit.k,
                inst.width,
                inst.lhs.as_scalar_lean(),
            );
            vec![
                (format!("wrong-final-value ({} instead of {})", sub, inst.op.value_fn()), p1),
                (
                    "wrong-operand-threaded-to-terminator (raw lhs, not the BinOp's own result)"
                        .to_string(),
                    p2,
                ),
            ]
        }
        VisitShape::GroundRflNonTerminal | VisitShape::SymbolicCoreNonTerminal => {
            unreachable!("plan.visits.last() is always Terminal (Return) by construction")
        }
    }
}

/// T8 rule 2, generalized from CondBr's "swap then/else target" (design §3,
/// T8) to any unconditional `Br`: mutate a non-terminal visit's successor
/// block id to a DIFFERENT valid block index — "the true statement with one
/// token mutated" (W5's own worked example, `BlockId.mk 2 ≠ BlockId.mk 1`).
/// Picks the FIRST ground non-terminal visit; `None` for a single-visit
/// (always-terminal) family, so v0's original two families get exactly the
/// same 2 probes as before (this function contributes nothing for them).
/// Deliberately restricted to `GroundRflNonTerminal` — a
/// `SymbolicCoreNonTerminal` visit's own args/state rendering needs the
/// unresolved-pending-value plumbing `plan.rs` itself flags as unexercised
/// (`Known::Sym("result")`, `plan.rs`'s `TermSpec::Br` arm doc comment); no
/// family registered in this increment hits that path.
fn render_successor_pc_probe(plan: &FamilyPlan) -> Option<(String, String)> {
    let prefix = plan.spec.name;
    let visit = plan.visits.iter().find(|v| matches!(v.shape, VisitShape::GroundRflNonTerminal))?;
    let VisitOutcome::Br { target_pc, args } = &visit.outcome else {
        unreachable!("GroundRflNonTerminal visits always end in Br")
    };
    let block_count = plan.spec.blocks.len();
    let wrong_target = (target_pc + 1) % block_count;
    debug_assert_ne!(wrong_target, *target_pc, "a Br visit's family always has >= 2 blocks");

    let block = &plan.spec.blocks[visit.pc];
    let pre = pre_state_expr(prefix, plan, visit);
    let lhs = lhs_app(prefix, visit, block, "(Nat.succ f)");
    let width = visit.inst.map_or(0, |i| i.width);
    let vals = args.iter().map(|r| render_ret_val(*r, width, "")).collect::<Vec<_>>().join(", ");
    let state = render_state_literal(prefix, plan, visit, block, None);
    let next_lhs = format!(
        "TrustIr.stepNWithContext TrustIr.EvalContext.empty f 0 {} (TrustIr.BlockId.mk {wrong_target})",
        cfg_name(prefix)
    );
    let src = format!(
        "theorem {prefix}_visit{}_WRONG_SUCCESSOR (f : Nat) :\n    TrustIr.Sem.run\n      ({lhs})\n      {pre}\n    =\n    TrustIr.Sem.run\n      ({next_lhs} [{vals}])\n      {state} := rfl\n",
        visit.k
    );
    Some((
        format!(
            "wrong-successor-block (visit {} claimed to Br to block {wrong_target}, not the true block {target_pc})",
            visit.k
        ),
        src,
    ))
}

/// T8 — the family's full forgery-probe set: the terminal-value mutation(s)
/// (rule 1/3, always available) plus, for a genuine multi-visit family, the
/// successor-pc mutation (rule 2). v0's original single-visit families get
/// exactly 2 probes (unchanged); a 2+-visit `Br`-chain family gets 3.
fn render_probes(plan: &FamilyPlan) -> Vec<(String, String)> {
    let mut probes = render_terminal_probes(plan);
    if let Some(pc_probe) = render_successor_pc_probe(plan) {
        probes.push(pc_probe);
    }
    probes
}

/// Compile a planned [`FamilyPlan`] into Lean source text (T0-T4, T5-C0,
/// T8). `plan_family` (`plan.rs`) must have already succeeded — this
/// function assumes the envelope already accepted the plan.
pub fn emit_family(plan: &FamilyPlan) -> EmittedFamily {
    let fixtures_src = render_fixtures(plan);
    let visits: Vec<EmittedVisit> = plan.visits.iter().map(|v| render_visit(plan, v)).collect();
    let (composed_name, composed_src) = render_composed(plan, &visits);
    let probes = render_probes(plan);
    EmittedFamily { fixtures_src, visits, composed_name, composed_src, probes }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::cfg_family::plan::plan_family;
    use crate::cfg_family::{GEN_BLOCK_ADD, GEN_BLOCK_ADD_SYM, GEN_BLOCK_CHAIN2, GEN_BLOCK_CHAIN3};

    /// Not a correctness test (the real kernel-check lives in
    /// `tests/lean_clean_bridge.rs`, which needs the vendored oleans) — a
    /// FAST, toolchain-free dump of what the emitter produces, useful for
    /// diffing against the hand-written `STEPBLOCK_*` sources. Run with
    /// `cargo test -p trust-clean --lib cfg_family::emit -- --nocapture`.
    #[test]
    fn dump_gen_block_add_sym_lean() {
        let plan = plan_family(&GEN_BLOCK_ADD_SYM).expect("plan");
        let e = emit_family(&plan);
        assert!(
            e.visits[0].src.contains(
                "by\n    rw [gen_block_add_sym_visit1_chain v_l v_r f, \
                 bridge_add 8 v_l v_r h0 h1]"
            ),
            "symbolic connect must use the kernel-checked rw path: {}",
            e.visits[0].src
        );
        assert!(
            !e.visits[0].src.contains("congrArg"),
            "the fragile term-elaborated congrArg connect must not regress"
        );
        println!("=== FIXTURES ===\n{}", e.fixtures_src);
        for v in &e.visits {
            println!("=== VISIT {} ===\n{}", v.label, v.src);
        }
        println!("=== COMPOSED {} ===\n{}", e.composed_name, e.composed_src);
        for (label, src) in &e.probes {
            println!("=== PROBE {label} ===\n{src}");
        }
    }

    #[test]
    fn dump_gen_block_add_lean() {
        let plan = plan_family(&GEN_BLOCK_ADD).expect("plan");
        let e = emit_family(&plan);
        println!("=== FIXTURES ===\n{}", e.fixtures_src);
        for v in &e.visits {
            println!("=== VISIT {} ===\n{}", v.label, v.src);
        }
        println!("=== COMPOSED {} ===\n{}", e.composed_name, e.composed_src);
        for (label, src) in &e.probes {
            println!("=== PROBE {label} ===\n{src}");
        }
    }

    /// M4.1: dump `gen_block_chain2` — the FIRST multi-visit (`Br`-chain)
    /// generated family, run through the full plan+emit pipeline (still no
    /// Lean toolchain needed; the real kernel-check lives in
    /// `tests/lean_clean_bridge.rs`). Verifies structurally: 2 visits, a
    /// `gen_block_chain2_state1` def, a genuine `∧`-conjunction composed
    /// theorem, and 3 probes (2 terminal + 1 successor-pc).
    #[test]
    fn dump_gen_block_chain2_lean() {
        let plan = plan_family(&GEN_BLOCK_CHAIN2).expect("plan");
        assert_eq!(plan.visits.len(), 2, "gen_block_chain2 is a 2-visit Br chain");
        let e = emit_family(&plan);
        println!("=== FIXTURES ===\n{}", e.fixtures_src);
        assert!(
            e.fixtures_src.contains("def gen_block_chain2_state1"),
            "the k=1 post-state must be emitted as a named def for visit2 to reference"
        );
        for v in &e.visits {
            println!("=== VISIT {} ===\n{}", v.label, v.src);
        }
        println!("=== COMPOSED {} ===\n{}", e.composed_name, e.composed_src);
        assert!(
            e.composed_src.contains(" ∧ "),
            "a genuine 2-visit family must compose a real conjunction, not a bare restatement"
        );
        assert!(e.composed_src.contains("And.intro"));
        for (label, src) in &e.probes {
            println!("=== PROBE {label} ===\n{src}");
        }
        assert_eq!(e.probes.len(), 3, "2 terminal-value probes + 1 successor-pc probe");
        assert!(e.probes.iter().any(|(_, s)| s.contains("WRONG_SUCCESSOR")));
    }

    /// M4.1: dump `gen_block_chain3` — the 3-visit `Br` chain (mission's "a
    /// 3-visit chain if (1) is cheap"). Verifies structurally: 3 visits, TWO
    /// named state defs (`state1` referencing `MachineState.empty`,
    /// `state2` referencing `state1`), a 3-way `∧` composed theorem.
    #[test]
    fn dump_gen_block_chain3_lean() {
        let plan = plan_family(&GEN_BLOCK_CHAIN3).expect("plan");
        assert_eq!(plan.visits.len(), 3, "gen_block_chain3 is a 3-visit Br chain");
        let e = emit_family(&plan);
        println!("=== FIXTURES ===\n{}", e.fixtures_src);
        assert!(e.fixtures_src.contains("def gen_block_chain3_state1"));
        assert!(e.fixtures_src.contains("def gen_block_chain3_state2"));
        for v in &e.visits {
            println!("=== VISIT {} ===\n{}", v.label, v.src);
        }
        println!("=== COMPOSED {} ===\n{}", e.composed_name, e.composed_src);
        assert_eq!(
            e.composed_src.matches(" ∧ ").count(),
            2,
            "3 conjuncts need exactly 2 top-level ∧ separators"
        );
        for (label, src) in &e.probes {
            println!("=== PROBE {label} ===\n{src}");
        }
        assert_eq!(e.probes.len(), 3, "2 terminal-value probes + 1 successor-pc probe");
    }
}
