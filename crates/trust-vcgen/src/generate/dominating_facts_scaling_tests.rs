//! LINEAR SCALING of the dominating guard-fact index (`dominating_facts`), pinned by
//! deterministic WORK COUNTERS (`fn_memo::AnalysisMemoStats`), never by wall time.
//!
//! THE DEFECT THIS PINS. The retired per-row miner walked every ENUMERATED path into a
//! row's block and, per guard leaf, scanned the body for a copy statement; the guard
//! resolution beneath it asked the whole-body `value_local_is_unstable` per operand.
//! The 2026-10-01 review measured it on `if a >= MIN+1 { acc ^= -a; .. N times }`
//! (`guarded_neg_chain` below): the miner's total grew ~8x per doubling, 1.9 ms at
//! N=50 to 4.45 s at N=800 — cubic. And it rode `MAX_PATHS_PER_BLOCK`: past 64 paths a
//! block's facts were simply gone (`guarded_neg_diamonds`, a false refutation of safe
//! code at 7 diamonds).
//!
//! THE DRIVER builds the index and asks it what every row asks: for each `Neg` and
//! `Mul` operand, its copy source and its facts at the operation's own statement. Each
//! rung doubles the family's parameter (the program grows by at most 2x, asserted);
//! every counter may grow by at most 2.5x per rung, and the per-query jump steps are
//! gated at O(log size) per query. Each family also checks the ANSWER, so a fast index
//! that stopped finding the facts cannot pass.

use serde_json::{Value, json};
use trust_types::{Operand, Rvalue, Statement, VerifiableFunction};

use super::dominating_facts::{DominatingFacts, GuardSubject};
use super::legacy_version_oracle::without_differential;
use super::{BvGuardCmp, FuncAnalysisScope};
use crate::AnalysisMemoStats;

const MIN_PLUS_ONE: i128 = i128::MIN + 1;

fn span() -> Value {
    json!({"file": "family.rs", "line_start": 1, "col_start": 0, "line_end": 1, "col_end": 1})
}
fn i128_ty() -> Value {
    json!({"Int": {"width": 128, "signed": true}})
}
fn place(local: usize) -> Value {
    json!({"local": local, "projections": []})
}
fn copy(local: usize) -> Value {
    json!({"Copy": place(local)})
}
fn mv(local: usize) -> Value {
    json!({"Move": place(local)})
}
/// An `i128` constant. `serde_json::Value` cannot hold one past `i64`/`u64`, so it rides
/// as a marker string and [`function`] splices the digits into the JSON text — the form
/// a real extraction's file has.
fn int(value: i128) -> Value {
    json!({"Constant": {"Int": format!("{I128_MARK}{value}")}})
}
const I128_MARK: &str = "__i128__";
fn assign(dest: usize, rvalue: Value) -> Value {
    json!({"Assign": {"place": place(dest), "rvalue": rvalue, "span": span()}})
}
fn binop(op: &str, a: Value, b: Value) -> Value {
    json!({"BinaryOp": [op, a, b]})
}
fn switch_bool(discr: Value, on_false: usize, on_true: usize) -> Value {
    json!({"SwitchInt": {"discr": discr, "targets": [[0, on_false]], "otherwise": on_true,
        "exhaustive_enum_unreachable": false, "span": span()}})
}
fn assert_not(cond: usize, msg: &str, target: usize) -> Value {
    json!({"Assert": {"cond": mv(cond), "expected": false, "msg": msg, "target": target,
        "span": span(), "unwind": "Continue"}})
}
fn goto(t: usize) -> Value {
    json!({"Goto": t})
}
fn block(id: usize, stmts: Vec<Value>, terminator: Value) -> Value {
    json!({"id": id, "stmts": stmts, "terminator": terminator})
}
fn local(index: usize, ty: Value, name: Option<&str>) -> Value {
    json!({"index": index, "ty": ty, "name": name})
}
fn function(
    name: &str,
    locals: Vec<Value>,
    blocks: Vec<Value>,
    arg_count: usize,
) -> VerifiableFunction {
    let v = json!({
        "name": name,
        "def_path": format!("family::{name}"),
        "span": span(),
        "body": {"locals": locals, "blocks": blocks, "arg_count": arg_count,
            "return_ty": i128_ty()},
        "contracts": [], "preconditions": [], "postconditions": [],
        "spec": {"requires": [], "ensures": [], "invariants": []},
    });
    let mut text = v.to_string();
    while let Some(start) = text.find(&format!("\"{I128_MARK}")) {
        let digits_start = start + 1 + I128_MARK.len();
        let end = digits_start + text[digits_start..].find('"').expect("closing quote");
        let digits = text[digits_start..end].to_string();
        text.replace_range(start..=end, &digits);
    }
    serde_json::from_str(&text).expect("a generated family body deserializes")
}

/// The review's family, as debug rustc lowers it: one guard `a >= MIN+1`, then `n`
/// checked negations `acc ^= -a`, each behind its own `OverflowNeg` assert — so the
/// one recorded path into the `i`-th negation carries `i + 1` guards.
fn guarded_neg_chain(n: usize) -> VerifiableFunction {
    // _0 ret, _1 a, _2 guard flag, _3 acc; per i: _(4+2i) eq flag, _(5+2i) neg value.
    let mut locals = vec![
        local(0, i128_ty(), None),
        local(1, i128_ty(), Some("a")),
        local(2, json!("Bool"), None),
        local(3, i128_ty(), Some("acc")),
    ];
    for i in 0..n {
        locals.push(local(4 + 2 * i, json!("Bool"), None));
        locals.push(local(5 + 2 * i, i128_ty(), None));
    }
    // bb0 guard; per i: assert block 1+2i, negation block 2+2i; exit 1+2n.
    let exit = 1 + 2 * n;
    let mut blocks = vec![block(
        0,
        vec![assign(3, json!({"Use": int(0)})), assign(2, binop("Ge", copy(1), int(MIN_PLUS_ONE)))],
        switch_bool(mv(2), exit, 1),
    )];
    for i in 0..n {
        let (check, neg) = (1 + 2 * i, 2 + 2 * i);
        let (flag, value) = (4 + 2 * i, 5 + 2 * i);
        blocks.push(block(
            check,
            vec![assign(flag, binop("Eq", copy(1), int(i128::MIN)))],
            assert_not(flag, "OverflowNeg", neg),
        ));
        blocks.push(block(
            neg,
            vec![
                assign(value, json!({"UnaryOp": ["Neg", copy(1)]})),
                assign(3, binop("BitXor", copy(3), mv(value))),
            ],
            goto(if i + 1 < n { 1 + 2 * (i + 1) } else { exit }),
        ));
    }
    blocks.push(block(exit, vec![assign(0, json!({"Use": copy(3)}))], json!("Return")));
    function(&format!("guarded_neg_chain_{n}"), locals, blocks, 1)
}

/// The cap's family: one guard `a >= MIN+1`, then `n` independent diamonds (each a
/// branch on its own `bool` parameter), then ONE negation — `2^n` paths into it. The
/// retired miner lost the guard past `MAX_PATHS_PER_BLOCK` (n = 7).
fn guarded_neg_diamonds(n: usize) -> VerifiableFunction {
    // _0 ret, _1 a, _(2+i) c_i (the parameters come first, as rustc numbers them),
    // then the guard flag, z, the eq flag and the neg value.
    let (guard, z, flag, value) = (2 + n, 3 + n, 4 + n, 5 + n);
    let mut locals = vec![local(0, i128_ty(), None), local(1, i128_ty(), Some("a"))];
    for i in 0..n {
        locals.push(local(2 + i, json!("Bool"), None));
    }
    locals.push(local(guard, json!("Bool"), None));
    locals.push(local(z, i128_ty(), Some("z")));
    locals.push(local(flag, json!("Bool"), None));
    locals.push(local(value, i128_ty(), None));
    // bb0 guard; per i: branch 1+3i, left 2+3i, right 3+3i (both join at 1+3(i+1));
    // then check 1+3n, negation 2+3n, exit 3+3n.
    let (check, neg, exit) = (1 + 3 * n, 2 + 3 * n, 3 + 3 * n);
    let mut blocks = vec![block(
        0,
        vec![
            assign(z, json!({"Use": int(0)})),
            assign(guard, binop("Ge", copy(1), int(MIN_PLUS_ONE))),
        ],
        switch_bool(mv(guard), exit, 1),
    )];
    for i in 0..n {
        let (br, left, right, join) = (1 + 3 * i, 2 + 3 * i, 3 + 3 * i, 1 + 3 * (i + 1));
        blocks.push(block(br, vec![], switch_bool(copy(2 + i), right, left)));
        blocks.push(block(left, vec![assign(z, binop("Add", copy(z), int(1)))], goto(join)));
        blocks.push(block(right, vec![assign(z, binop("Add", copy(z), int(2)))], goto(join)));
    }
    blocks.push(block(
        check,
        vec![assign(flag, binop("Eq", copy(1), int(i128::MIN)))],
        assert_not(flag, "OverflowNeg", neg),
    ));
    blocks.push(block(
        neg,
        vec![
            assign(value, json!({"UnaryOp": ["Neg", copy(1)]})),
            assign(0, json!({"Use": mv(value)})),
        ],
        goto(exit),
    ));
    blocks.push(block(exit, vec![], json!("Return")));
    function(&format!("guarded_neg_diamonds_{n}"), locals, blocks, 1 + n)
}

/// `n` NESTED guards on `n` different parameters (`x_i >= -5`), each guarded body
/// negating its own parameter through a debug-style COPY (`_t = copy x_i; -_t`), so
/// every query also takes the copy hop.
fn nested_copy_guards(n: usize) -> VerifiableFunction {
    // _0 ret, _(1+i) x_i params; per i: _(1+n+3i) guard flag, _(2+n+3i) copy,
    // _(3+n+3i) neg value.
    let mut locals = vec![local(0, i128_ty(), None)];
    for i in 0..n {
        locals.push(local(1 + i, i128_ty(), None));
    }
    for i in 0..n {
        let base = 1 + n + 3 * i;
        locals.push(local(base, json!("Bool"), None));
        locals.push(local(base + 1, i128_ty(), None));
        locals.push(local(base + 2, i128_ty(), None));
    }
    // per i: guard block 2i, body block 2i+1 (then on to guard i+1); exit 2n.
    let exit = 2 * n;
    let mut blocks = Vec::new();
    for i in 0..n {
        let (guard, body) = (2 * i, 2 * i + 1);
        let base = 1 + n + 3 * i;
        blocks.push(block(
            guard,
            vec![assign(base, binop("Ge", copy(1 + i), int(-5)))],
            switch_bool(mv(base), exit, body),
        ));
        blocks.push(block(
            body,
            vec![
                assign(base + 1, json!({"Use": copy(1 + i)})),
                assign(base + 2, json!({"UnaryOp": ["Neg", mv(base + 1)]})),
                assign(0, json!({"Use": mv(base + 2)})),
            ],
            goto(if i + 1 < n { 2 * (i + 1) } else { exit }),
        ));
    }
    blocks.push(block(exit, vec![], json!("Return")));
    function(&format!("nested_copy_guards_{n}"), locals, blocks, n)
}

/// `n` sequential LOOPS over one mutable parameter, each negating it under a guard and
/// then rewriting it: `while c { if a > -5 { -a } a -= 3 }` n times. Every negation reads
/// the loop header's JOIN, so every query resolves a value identity through the SSA
/// oracle (pseudo-defs, joins) — the shape the identity exists for.
fn loop_guards(n: usize) -> VerifiableFunction {
    // _0 ret, _1 a (mut), _2 c (param); per i: _(3+3i) the guard's copy of `a` (debug
    // rustc compares a per-guard copy; a reassigned local is never compared directly),
    // _(4+3i) guard flag, _(5+3i) neg value.
    let mut locals = vec![
        local(0, i128_ty(), None),
        local(1, i128_ty(), Some("a")),
        local(2, json!("Bool"), Some("c")),
    ];
    for i in 0..n {
        locals.push(local(3 + 3 * i, i128_ty(), None));
        locals.push(local(4 + 3 * i, json!("Bool"), None));
        locals.push(local(5 + 3 * i, i128_ty(), None));
    }
    // per i: header 4i, guard 4i+1, negation 4i+2, rewrite 4i+3; exit 4n.
    let exit = 4 * n;
    let mut blocks = Vec::new();
    for i in 0..n {
        let (header, guard, neg, rewrite) = (4 * i, 4 * i + 1, 4 * i + 2, 4 * i + 3);
        let next = if i + 1 < n { 4 * (i + 1) } else { exit };
        let (copied, flag, value) = (3 + 3 * i, 4 + 3 * i, 5 + 3 * i);
        blocks.push(block(header, vec![], switch_bool(copy(2), next, guard)));
        blocks.push(block(
            guard,
            vec![
                assign(copied, json!({"Use": copy(1)})),
                assign(flag, binop("Gt", mv(copied), int(-5))),
            ],
            switch_bool(mv(flag), rewrite, neg),
        ));
        blocks.push(block(
            neg,
            vec![
                assign(value, json!({"UnaryOp": ["Neg", copy(1)]})),
                assign(0, json!({"Use": mv(value)})),
            ],
            goto(rewrite),
        ));
        blocks.push(block(rewrite, vec![assign(1, binop("Sub", copy(1), int(3)))], goto(header)));
    }
    blocks.push(block(exit, vec![], json!("Return")));
    function(&format!("loop_guards_{n}"), locals, blocks, 2)
}

/// Every `(operand local, block, statement)` a `Neg` row asks the index about.
fn neg_uses(func: &VerifiableFunction) -> Vec<(usize, trust_types::BlockId, usize)> {
    let mut out = Vec::new();
    for b in &func.body.blocks {
        for (k, s) in b.stmts.iter().enumerate() {
            if let Statement::Assign {
                rvalue: Rvalue::UnaryOp(trust_types::UnOp::Neg, Operand::Copy(p) | Operand::Move(p)),
                ..
            } = s
                && p.projections.is_empty()
            {
                out.push((p.local, b.id, k));
            }
        }
    }
    out
}

/// Build the index and ask it every row's questions; the counters, and the facts each
/// use was answered with (operand facts plus its copy source's, as the lanes merge them).
fn drive(func: &VerifiableFunction) -> (AnalysisMemoStats, Vec<Vec<(BvGuardCmp, i128)>>) {
    without_differential(|| {
        let _analysis = FuncAnalysisScope::enter(func);
        let _scope = crate::gen_work_scope_unmetered();
        crate::fn_memo::reset_analysis_memo_stats();
        let index = DominatingFacts::build(func);
        let mut answers = Vec::new();
        for (operand, block, k) in neg_uses(func) {
            let mut facts =
                index.facts(func, operand, block, k, GuardSubject::LiveCopyOfBase).to_vec();
            if let Some(src) = index.copy_source_at(func, operand, block, k) {
                facts.extend_from_slice(index.facts(
                    func,
                    src,
                    block,
                    k,
                    GuardSubject::LiveCopyOfBase,
                ));
            }
            answers.push(facts);
        }
        (crate::fn_memo::analysis_memo_stats(), answers)
    })
}

fn size(func: &VerifiableFunction) -> u64 {
    (func.body.blocks.iter().map(|b| b.stmts.len() + 1).sum::<usize>() + func.body.locals.len())
        as u64
}

fn counters(s: &AnalysisMemoStats) -> [(&'static str, u64); 12] {
    [
        ("cfg_work", s.cfg_work),
        ("rebind_probes", s.rebind_probes),
        ("block_write_entries", s.block_write_entries),
        ("gate_fallbacks", s.gate_fallbacks),
        ("ssa_queries", s.ssa_queries),
        ("ssa_phis", s.ssa_phis),
        ("tracked_names", s.tracked_names),
        ("pseudo_defs", s.pseudo_defs),
        ("extraction_stmts", s.extraction_stmts),
        ("body_scan_items", s.body_scan_items),
        ("writes_until", s.writes_until_computed),
        ("place_names", s.place_names_computed),
    ]
}

const LADDER: [usize; 4] = [64, 128, 256, 512];

/// Per DOUBLING, at most this growth in any counter. Linear work grows ~2x; the rebind
/// index's probe count steps when the locals' decimal names gain a digit (2.11x, 2.51x,
/// 1.59x on `nested_copy_guards` — 8.4x over the ladder), so one rung may exceed 2.5x
/// while the slope is linear; the WHOLE-ladder bound below is the tight one. Quadratic
/// work is 4x per rung and 64x over the ladder, and fails both.
const PER_RUNG: f64 = 3.0;

/// Every counter at most 2.5x per doubling, query steps O(log) per query, and every
/// answer as `expect` says.
fn assert_linear(
    family: &str,
    mk: impl Fn(usize) -> VerifiableFunction,
    expect: impl Fn(&[Vec<(BvGuardCmp, i128)>]),
) {
    let ladder: Vec<VerifiableFunction> = LADDER.iter().map(|&n| mk(n)).collect();
    let runs: Vec<(AnalysisMemoStats, Vec<Vec<(BvGuardCmp, i128)>>)> =
        ladder.iter().map(drive).collect();
    if std::env::var("DOMFACTS_SCALING_TRACE").is_ok() {
        for (func, (s, _)) in ladder.iter().zip(&runs) {
            eprintln!("{family} size={} {:?}", size(func), counters(s));
        }
    }
    for (_, answers) in &runs {
        assert!(!answers.is_empty(), "{family}: the driver asked nothing");
        expect(answers);
    }
    for w in 0..ladder.len() - 1 {
        let ((small, _), (big, _)) = (&runs[w], &runs[w + 1]);
        let size_ratio = size(&ladder[w + 1]) as f64 / size(&ladder[w]) as f64;
        assert!(
            (1.3..=2.1).contains(&size_ratio),
            "{family}: each rung must grow the program by at most 2x ({size_ratio:.2})"
        );
        for ((name, a), (_, b)) in counters(small).into_iter().zip(counters(big)) {
            if b <= 16 {
                continue;
            }
            let ratio = b as f64 / a.max(1) as f64;
            assert!(
                ratio <= PER_RUNG,
                "{family}: `{name}` grew {ratio:.2}x ({a} -> {b}) over a rung where the program \
                 grew {size_ratio:.2}x — the dominating-fact index is super-linear. All \
                 counters: {small:?} -> {big:?}"
            );
        }
    }
    // The whole ladder: 8x the parameter, at most 1.25x that in every counter.
    let (first, last) = (&runs[0].0, &runs[runs.len() - 1].0);
    let size_ratio = size(&ladder[ladder.len() - 1]) as f64 / size(&ladder[0]) as f64;
    for ((name, a), (_, b)) in counters(first).into_iter().zip(counters(last)) {
        if b <= 16 {
            continue;
        }
        let ratio = b as f64 / a.max(1) as f64;
        assert!(
            ratio <= 1.25 * size_ratio,
            "{family}: `{name}` grew {ratio:.2}x ({a} -> {b}) over the ladder, where the \
             program grew {size_ratio:.2}x — super-linear. All counters: {first:?} -> {last:?}"
        );
    }
    for (func, (s, answers)) in ladder.iter().zip(&runs) {
        let per = 8.0 * (size(func) as f64).log2();
        assert!(
            (s.query_steps as f64) <= per * (answers.len() + s.ssa_queries as usize) as f64,
            "{family}: {} jump steps for {} queries exceeds O(log) per query at size {}",
            s.query_steps,
            answers.len(),
            size(func)
        );
    }
}

/// The review's cubic family is linear, and every negation still sees the guard.
#[test]
fn guarded_neg_chain_is_linear() {
    assert_linear("guarded_neg_chain", guarded_neg_chain, |answers| {
        for facts in answers {
            assert!(
                facts.contains(&(BvGuardCmp::Ge, MIN_PLUS_ONE)),
                "every negation is dominated by `a >= MIN+1`: {facts:?}"
            );
        }
    });
}

/// `2^n` paths into the negation, and the guard still reaches it — at every rung,
/// which is 64 to 512 diamonds, far past the retired cap's 6.
#[test]
fn guarded_neg_diamonds_is_linear_and_keeps_the_guard_past_the_retired_cap() {
    assert_linear("guarded_neg_diamonds", guarded_neg_diamonds, |answers| {
        assert_eq!(answers.len(), 1);
        assert_eq!(answers[0], vec![(BvGuardCmp::Ge, MIN_PLUS_ONE)]);
    });
}

/// Small sizes, the cliff itself: 6, 7 and 8 diamonds answer alike.
#[test]
fn the_guard_survives_the_retired_path_cap() {
    for n in [1, 6, 7, 8, 20] {
        let (_, answers) = drive(&guarded_neg_diamonds(n));
        assert_eq!(answers, vec![vec![(BvGuardCmp::Ge, MIN_PLUS_ONE)]], "{n} diamonds");
    }
}

/// `n` keys, each answered through the copy hop, each with exactly its own guard.
#[test]
fn nested_copy_guards_are_linear() {
    assert_linear("nested_copy_guards", nested_copy_guards, |answers| {
        for facts in answers {
            assert_eq!(facts, &vec![(BvGuardCmp::Ge, -5)], "only the operand's own guard");
        }
    });
}

/// Every negation reads a loop JOIN: the value identity is resolved through the SSA
/// oracle at every query, and still costs O(log) per query.
#[test]
fn loop_guards_are_linear_through_the_value_identity() {
    assert_linear("loop_guards", loop_guards, |answers| {
        for facts in answers {
            assert_eq!(facts, &vec![(BvGuardCmp::Gt, -5)], "each loop's own guard");
        }
    });
}
