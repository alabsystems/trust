//! Trust (wave-ASM): the direct producer's OWN OUTPUT for an empty `noreturn`
//! `asm!` must be a reachability CHARGE on exactly the inputs that reach the
//! asm, and on no others.
//!
//! WHY THIS TEST EXISTS. `tests/ui/trust/trust_ir_lower_noreturn_empty_asm.rs`
//! requires the "Trust Level 0 safety verification incomplete" warning, but that
//! warning is the MIR lane's: it reads the built body's own `InlineAsm`
//! terminator, never the direct module the wave-ASM arm writes, and it fires the
//! same way for an asm no input reaches. So that file cannot see the arm's
//! output. A variant that ERASED the asm (no seal, the `x == 0` path falling
//! through to `ret x`) or turned it into an ASSUMPTION (`assume false`, the path
//! silently pruned) would leave every UI test green. This test reads the arm's
//! output where it lands, the `-Ztrust-dump=ir` module.
//!
//! WHAT IT CHECKS, on the dumped module (the direct lane's crate module, after
//! the splice; the coverage rows must say every body lowered and spliced with no
//! unsupported shape):
//!   * every charge site is an `unreachable` TERMINATOR. That instruction is the
//!     charge: `trust-ir-bridge`'s `vcgen_proto` gives it a `PanicFreedom` row
//!     ("path must be infeasible"), and the structural reachability CHC in
//!     `trust_verify` derives `error` from its block;
//!   * a small path-interval evaluator over the body (below) computes, for each
//!     charge site, the exact set of `u32` inputs whose path reaches it, and for
//!     each `ret` the inputs that return:
//!       - `diverge`: one charge, reached unconditionally;
//!       - `guarded` (the LIVE control): one charge, reached on exactly {0};
//!         every other input returns. An erased asm has no charge and returns
//!         on 0; an assumed one has no charge and prunes 0 from every outcome;
//!       - `dead` (the DEAD control): the arm still emits its one charge, but
//!         the evaluator finds its reaching set EMPTY (`x < 1 && x > 5`), and
//!         every input returns. The dead charge is discharged by path
//!         infeasibility alone; the live one has the witness `x == 0`.
//!
//! WHAT IT DOES NOT CHECK. No verifier runs over this module today: the coverage
//! header's `native_verification_requests` is false and `proof_authority` is
//! false (both pinned below), so neither charge is proved or refuted by any
//! shipped lane. The evaluator is this test's own reading of the body, not a
//! verifier verdict, and it fails closed on any instruction it does not model.
//!
//! Measured non-vacuous on 2026-09-30 by rebuilding stage1 with the arm's seal
//! replaced (1) by nothing (erasure) and (2) by `assume false`; see the landing
//! commit's message.

//@ needs-asm-support

use std::collections::BTreeMap;

use run_make_support::{rfs, rustc, serde_json, trust_ir};

const MAX: u64 = u32::MAX as u64;

/// A set of `u32` inputs as sorted, disjoint, inclusive intervals.
type Set = Vec<(u64, u64)>;

fn full() -> Set {
    vec![(0, MAX)]
}

fn intersect(a: &Set, b: &Set) -> Set {
    let mut out = Vec::new();
    for &(alo, ahi) in a {
        for &(blo, bhi) in b {
            let (lo, hi) = (alo.max(blo), ahi.min(bhi));
            if lo <= hi {
                out.push((lo, hi));
            }
        }
    }
    normalize(out)
}

fn complement(a: &Set) -> Set {
    let mut out = Vec::new();
    let mut next = 0u64;
    for &(lo, hi) in a {
        if lo > next {
            out.push((next, lo - 1));
        }
        next = hi + 1;
    }
    if next <= MAX {
        out.push((next, MAX));
    }
    out
}

fn union(a: &Set, b: &Set) -> Set {
    let mut all = a.clone();
    all.extend_from_slice(b);
    normalize(all)
}

fn normalize(mut v: Set) -> Set {
    v.sort();
    let mut out: Set = Vec::new();
    for (lo, hi) in v {
        match out.last_mut() {
            Some(last) if lo <= last.1.saturating_add(1) => last.1 = last.1.max(hi),
            _ => out.push((lo, hi)),
        }
    }
    out
}

/// The inputs `x` with `x <op> c`.
fn predicate(op: &str, c: u64) -> Set {
    let below = |c: u64| if c == 0 { vec![] } else { vec![(0, c - 1)] };
    let above = |c: u64| if c == MAX { vec![] } else { vec![(c + 1, MAX)] };
    match op {
        "eq" => vec![(c, c)],
        "ne" => complement(&vec![(c, c)]),
        "ult" => below(c),
        "ule" => vec![(0, c)],
        "ugt" => above(c),
        "uge" => vec![(c, MAX)],
        other => panic!("the evaluator does not model `icmp {other}`"),
    }
}

fn mirrored(op: &str) -> &'static str {
    match op {
        "eq" => "eq",
        "ne" => "ne",
        "ult" => "ugt",
        "ule" => "uge",
        "ugt" => "ult",
        "uge" => "ule",
        other => panic!("the evaluator does not model `icmp {other}`"),
    }
}

#[derive(Clone, Debug)]
enum Val {
    /// The function's `u32` parameter.
    Param,
    Int(u64),
    /// A boolean: true exactly on this input set.
    Bool(Set),
}

#[derive(Debug)]
struct Block {
    params: Vec<String>,
    insts: Vec<String>,
}

fn function<'a>(text: &'a str, name: &str) -> &'a str {
    let needle = format!("fn @{name}(");
    assert_eq!(text.matches(&needle).count(), 1, "missing/duplicate {name}: {text}");
    text.split_once(&needle).unwrap().1.split_once("\n}\n").unwrap().0
}

fn blocks(body: &str) -> BTreeMap<String, Block> {
    let mut out = BTreeMap::new();
    let mut current: Option<String> = None;
    for raw in body.lines().skip(1) {
        let line = raw.split("  ;").next().unwrap().trim();
        if line.is_empty() || line.starts_with(';') {
            continue;
        }
        if let Some(header) = line.strip_suffix(':') {
            let (name, params) = match header.split_once('(') {
                Some((name, rest)) => (
                    name,
                    rest.trim_end_matches(')')
                        .split(", ")
                        .map(|p| p.split(':').next().unwrap().trim().to_string())
                        .collect(),
                ),
                None => (header, Vec::new()),
            };
            out.insert(name.to_string(), Block { params, insts: Vec::new() });
            current = Some(name.to_string());
            continue;
        }
        let name = current.as_ref().unwrap_or_else(|| panic!("instruction before a block: {line}"));
        out.get_mut(name).unwrap().insts.push(line.to_string());
    }
    out
}

/// `bbN` or `bbN(%a, %b)` -> (block, args).
fn target(spelling: &str) -> (String, Vec<String>) {
    match spelling.trim().split_once('(') {
        Some((name, args)) => (
            name.to_string(),
            args.trim_end_matches(')').split(", ").map(str::to_string).collect(),
        ),
        None => (spelling.trim().to_string(), Vec::new()),
    }
}

/// What the evaluator saw: for each charge block, the inputs reaching it, and
/// the inputs that return.
#[derive(Debug, Default)]
struct Outcome {
    charges: BTreeMap<String, Set>,
    returns: Set,
}

fn evaluate(name: &str, body: &str) -> Outcome {
    let blocks = blocks(body);
    let mut outcome = Outcome::default();
    for (id, block) in &blocks {
        let terminator = block.insts.last().unwrap_or_else(|| panic!("{name}: empty {id}"));
        for inst in &block.insts[..block.insts.len() - 1] {
            assert_ne!(inst, "unreachable", "{name}: `unreachable` must terminate {id}");
        }
        if terminator == "unreachable" {
            outcome.charges.insert(id.clone(), Vec::new());
        }
    }
    let entry = blocks.get("bb0").unwrap_or_else(|| panic!("{name}: no bb0"));
    let mut env: BTreeMap<String, Val> = BTreeMap::new();
    for param in &entry.params {
        env.insert(param.clone(), Val::Param);
    }
    walk(name, &blocks, "bb0", env, full(), 0, &mut outcome);
    outcome
}

fn walk(
    name: &str,
    blocks: &BTreeMap<String, Block>,
    id: &str,
    mut env: BTreeMap<String, Val>,
    mut domain: Set,
    depth: usize,
    outcome: &mut Outcome,
) {
    assert!(depth < 64, "{name}: path longer than 64 blocks (a loop?)");
    if domain.is_empty() {
        return;
    }
    let block = &blocks[id];
    let get = |env: &BTreeMap<String, Val>, v: &str| {
        env.get(v).cloned().unwrap_or_else(|| panic!("{name}: {v} used before definition"))
    };
    for inst in &block.insts {
        if let Some((dest, rhs)) = inst.split_once(" = ") {
            let words: Vec<&str> = rhs.split_whitespace().collect();
            let val = match words.as_slice() {
                ["const", "u32", n] => Val::Int(n.parse().unwrap()),
                ["const", "bool", "true"] => Val::Bool(full()),
                ["const", "bool", "false"] => Val::Bool(Vec::new()),
                ["icmp", op, "u32", a, b] => {
                    let a = get(&env, a.trim_end_matches(','));
                    let b = get(&env, b);
                    match (a, b) {
                        (Val::Param, Val::Int(c)) => Val::Bool(predicate(op, c)),
                        (Val::Int(c), Val::Param) => Val::Bool(predicate(mirrored(op), c)),
                        other => panic!("{name}: the evaluator does not model {inst} ({other:?})"),
                    }
                }
                _ => panic!("{name}: the evaluator does not model `{inst}`"),
            };
            env.insert(dest.to_string(), val);
            continue;
        }
        let words: Vec<&str> = inst.splitn(2, ' ').collect();
        match words.as_slice() {
            ["unreachable"] => {
                let reached = outcome.charges.get_mut(id).unwrap();
                *reached = union(reached, &domain);
                return;
            }
            ["ret", _] | ["ret"] => {
                outcome.returns = union(&outcome.returns, &domain);
                return;
            }
            // An assumption PRUNES the inputs that falsify it and falls through.
            // Modelled, not refused, so that a producer which assumed the asm
            // away fails below on its missing charge and its pruned inputs.
            ["assume", cond] => {
                let Val::Bool(set) = get(&env, cond) else { panic!("{name}: non-bool {inst}") };
                domain = intersect(&domain, &set);
                if domain.is_empty() {
                    return;
                }
            }
            ["br", rest] => {
                let (to, args) = target(rest);
                bind(&mut env, &blocks[&to], &args, &get);
                return walk(name, blocks, &to, env, domain, depth + 1, outcome);
            }
            ["condbr", rest] => {
                let (cond, targets) = rest.split_once(", ").unwrap();
                let Val::Bool(set) = get(&env, cond) else { panic!("{name}: non-bool {inst}") };
                let (then_t, else_t) = split_targets(targets);
                let then_part = intersect(&domain, &set);
                let else_part = intersect(&domain, &complement(&set));
                for (spelling, part) in [(then_t, then_part), (else_t, else_part)] {
                    let (to, args) = target(&spelling);
                    let mut env = env.clone();
                    bind(&mut env, &blocks[&to], &args, &get);
                    walk(name, blocks, &to, env, part, depth + 1, outcome);
                }
                return;
            }
            _ => panic!("{name}: the evaluator does not model `{inst}`"),
        }
    }
    panic!("{name}: {id} has no terminator");
}

fn split_targets(targets: &str) -> (String, String) {
    // `bbT, bbF` or `bbT(%a), bbF(%b, %c)`: split at the top-level comma.
    let mut level = 0;
    for (i, ch) in targets.char_indices() {
        match ch {
            '(' => level += 1,
            ')' => level -= 1,
            ',' if level == 0 => {
                return (targets[..i].to_string(), targets[i + 1..].trim().to_string());
            }
            _ => {}
        }
    }
    panic!("condbr without two targets: {targets}")
}

fn bind(
    env: &mut BTreeMap<String, Val>,
    block: &Block,
    args: &[String],
    get: &dyn Fn(&BTreeMap<String, Val>, &str) -> Val,
) {
    assert_eq!(block.params.len(), args.len(), "block argument arity: {block:?} <- {args:?}");
    let values: Vec<Val> = args.iter().map(|a| get(env, a)).collect();
    for (param, value) in block.params.iter().zip(values) {
        env.insert(param.clone(), value);
    }
}

fn main() {
    // Stock-rustc replay has no Trust-IR artifact interface. This is a Trust
    // producer test, not an exclusion from the Rust language compatibility suite.
    if std::env::var_os("__COMPILETEST_TRUST_VANILLA_REAL_RUSTC").is_some() {
        return;
    }
    let directory = "asmpin-ir";
    rustc()
        .input("asm.rs")
        .edition("2024")
        .crate_type("lib")
        .crate_name("asmpin")
        .emit("mir")
        .args([
            "-Copt-level=0",
            "-Zthreads=1",
            "-Ztrust-verify=off",
            "-Ztrust-ir-lower=on",
            "-Ztrust-ir-flip=no",
            &format!("-Ztrust-dump=ir:{directory}"),
        ])
        .output("asmpin.mir")
        .run();

    let coverage: serde_json::Value =
        serde_json::from_slice(&rfs::read(format!("{directory}/asmpin.coverage.json"))).unwrap();
    assert_eq!(coverage["proof_authority"].as_bool(), Some(false));
    assert_eq!(coverage["native_verification_requests"].as_bool(), Some(false));
    let rows = coverage["bodies"].as_array().unwrap();
    assert_eq!(rows.len(), 3, "{coverage:#}");
    for name in ["diverge", "guarded", "dead"] {
        let matching: Vec<_> = rows.iter().filter(|row| row["def_path"] == name).collect();
        assert_eq!(matching.len(), 1, "missing/duplicate row {name}");
        let row = matching[0];
        assert_eq!(row["lowered"].as_bool(), Some(true), "{name} must lower: {row:#}");
        assert_eq!(row["spliced"].as_bool(), Some(true), "{name} must be in the module: {row:#}");
        assert!(row["unsupported"].as_array().unwrap().is_empty(), "{name}: {row:#}");
    }

    // Headers by def path (WS5.2 names them by link symbol; `trust_ir::by_display_path`).
    let text =
        trust_ir::by_display_path(&rfs::read_to_string(format!("{directory}/asmpin.trust-ir.txt")));
    let one_charge = |name: &str, outcome: &Outcome| -> Set {
        assert_eq!(
            outcome.charges.len(),
            1,
            "{name}: the asm must lower to exactly ONE `unreachable` charge: {outcome:?}\n{text}"
        );
        outcome.charges.values().next().unwrap().clone()
    };

    let diverge = evaluate("diverge", function(&text, "diverge"));
    assert_eq!(one_charge("diverge", &diverge), full(), "diverge: charge reached always");
    assert!(diverge.returns.is_empty(), "diverge must not return: {diverge:?}");

    // LIVE: the charge is reached on x == 0 and only there.
    let guarded = evaluate("guarded", function(&text, "guarded"));
    assert_eq!(
        one_charge("guarded", &guarded),
        vec![(0, 0)],
        "guarded: the reachable asm edge (x == 0) must reach the charge"
    );
    assert_eq!(guarded.returns, vec![(1, MAX)], "guarded: x == 0 must not return: {guarded:?}");

    // DEAD: the arm emits the same charge, and no input reaches it.
    let dead = evaluate("dead", function(&text, "dead"));
    assert_eq!(
        one_charge("dead", &dead),
        Vec::<(u64, u64)>::new(),
        "dead: `x < 1 && x > 5` admits no u32, so no path may reach the charge"
    );
    assert_eq!(dead.returns, full(), "dead: every input returns: {dead:?}");

    // Each charge must sit ON the asm statement. Without this, `diverge` would
    // pass with the arm erased: its `-> !` fall-through seal also ends the body
    // in an `unreachable`, located at the closing brace instead.
    let source = rfs::read_to_string("asm.rs");
    let asm_lines: Vec<usize> = source
        .lines()
        .enumerate()
        .filter(|(_, line)| line.contains("asm!(\"\""))
        .map(|(i, _)| i + 1)
        .collect();
    assert_eq!(asm_lines.len(), 3, "asm.rs holds one asm per body");
    for (name, line) in ["diverge", "guarded", "dead"].into_iter().zip(asm_lines) {
        let sites: Vec<&str> = function(&text, name)
            .lines()
            .filter(|l| l.split("  ;").next().unwrap().trim() == "unreachable")
            .collect();
        assert_eq!(sites.len(), 1, "{name}: one charge site: {sites:?}");
        let loc = sites[0].split("#loc: ").nth(1).unwrap_or_else(|| panic!("{name}: no #loc"));
        let at: Vec<&str> = loc.split_whitespace().collect();
        assert_eq!(
            at[1],
            line.to_string(),
            "{name}: the charge must be the asm's own (line {line}): {loc}"
        );
    }
}
