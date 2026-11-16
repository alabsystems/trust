//! F7 regression (docs/KNOWN_HAZARDS.md; reports/2026-09-29-crystal-callee-sidecar-retired.md
//! F7): a body the trust-ir -> MIR flip installs must never READ a forwarded pointer parameter
//! after passing it to a call by `move`.
//!
//! The wave-8a call-argument arm in `crates/trust-thir-lower/src/to_mir.rs` passed a forwarded
//! `&T`/`&mut T` parameter as `move _p` unconditionally, and the same body read `_p` again: a
//! second forward, a load through it, or the same call on the next loop iteration. MIR forbids a
//! read after `Operand::Move`. The objects came out right only because a reference is a scalar,
//! so no run-time check can see it; the defect is in the installed MIR, which is what this reads.
//!
//! The compile meets the flip's session gates (`session_gates_allow_flip`: TrustIR lowering on,
//! the flip on, no debuginfo, no coverage), at `-Copt-level=0`, where the flip does not require
//! the exact marker channel. Each target must carry the flip's own `compiled from trust-ir`
//! event, so the MIR checked is the DERIVED body, not rustc's. The check is a maybe-moved
//! dataflow over each target's emitted MIR, the body codegen consumes. Measured on a stage-1
//! compiler without the fix (bd8681c2628): all nine targets flip, and the seven that read the
//! parameter again (every target but the two controls) fail the check.

use std::collections::{BTreeMap, BTreeSet};

use run_make_support::{cmd, rfs, rustc_path};

/// `(function, number of reference parameters)`: every target's leading parameters are
/// references, and each is forwarded into a call at least once.
const TARGETS: &[(&str, usize)] = &[
    ("shared_twice", 1),
    ("shared_pair", 1),
    ("shared_then_load", 1),
    ("mut_value_twice", 1),
    ("mut_value_then_bump", 1),
    ("mut_loop", 1),
    ("mut_branch_then", 1),
    ("mut_branch", 1),
    ("mut_value_once", 1),
];

const CALLEES: &[&str] = &["bump(", "inc(", "get(", "get2("];

fn main() {
    if std::env::var_os("__COMPILETEST_TRUST_VANILLA_REAL_RUSTC").is_some() {
        return;
    }
    checker_has_teeth();

    // The same file with the flip OFF: rustc's own MIR for every target passes the checker, so
    // a failure below is the derived body's, never the checker misreading valid MIR.
    let (_, built) = compile("no", "built.mir");
    let built_failures: Vec<String> = TARGETS
        .iter()
        .flat_map(|&(name, params)| {
            reads_after_move(&fn_body(&built, name), params)
                .into_iter()
                .map(move |e| format!("{name}: {e}"))
        })
        .collect();
    assert!(
        built_failures.is_empty(),
        "the checker flags rustc's own MIR:\n{}\n\n{built}",
        built_failures.join("\n"),
    );

    let (log, mir) = compile("yes", "derived.mir");
    let mut failures = Vec::new();
    for &(name, params) in TARGETS {
        // The flip's own event names the body by `DefId(.. ~ forwarded[..]::name)`.
        let needle = format!("::{name})");
        let flipped = log
            .lines()
            .any(|line| line.contains("compiled from trust-ir") && line.contains(&needle));
        assert!(
            flipped,
            "`{name}` was not installed from trust-ir, so this checks nothing:\n{log}",
        );
        assert!(
            !log.lines().any(|line| line.contains("FALLBACK") && line.contains(&needle)),
            "`{name}` fell back to built MIR:\n{log}",
        );
        let body = fn_body(&mir, name);
        // Not vacuous: the body calls a fixture callee, and every parameter is used inside a
        // basic block (not only in the signature or a `debug` line).
        assert!(
            CALLEES.iter().any(|c| body.contains(c)),
            "`{name}` calls no fixture callee:\n{body}",
        );
        let in_blocks: Vec<&str> =
            body.lines().filter(|l| l.starts_with("        ") && !l.contains("debug ")).collect();
        for p in 1..=params {
            let arg = format!("_{p}");
            assert!(
                in_blocks.iter().any(|l| mentions(l, &arg)),
                "`{name}` never uses {arg} in a block:\n{body}",
            );
        }
        let found = reads_after_move(&body, params);
        failures.extend(found.into_iter().map(|e| format!("{name}: {e}")));
    }
    assert!(
        failures.is_empty(),
        "a flipped body reads a parameter after moving it:\n{}\n\n{mir}",
        failures.join("\n"),
    );
}

/// Compiles `forwarded.rs` under the flip's session gates with `-Ztrust-ir-flip={flip}`,
/// returning the flip's event log and the emitted MIR.
fn compile(flip: &str, out: &str) -> (String, String) {
    let run = cmd(rustc_path())
        .env("RUSTC_LOG", "rustc_mir_transform::trust_ir_flip=info")
        .args([
            "forwarded.rs",
            "--edition=2021",
            "--crate-type=lib",
            "--crate-name=forwarded",
            "--emit=mir",
            "-Copt-level=0",
            "-Cdebuginfo=0",
            "-Zthreads=1",
            "-Ztrust-verify=off",
            "-Ztrust-ir-lower=on",
            &format!("-Ztrust-ir-flip={flip}"),
            "-o",
            out,
        ])
        .run();
    (run.stderr_utf8(), rfs::read_to_string(out))
}

/// The checker must find the defect it exists for, in each shape: straight-line reuse, two moves
/// in one call, and a forward inside a loop. A checker that finds nothing proves nothing.
fn checker_has_teeth() {
    let straight = "\
fn t(_1: &u64) -> u64 {
    let mut _0: u64;

    bb0: {
        _2 = get(move _1) -> [return: bb1, unwind continue];
    }

    bb1: {
        _3 = get(move _1) -> [return: bb2, unwind continue];
    }

    bb2: {
        return;
    }
}
";
    assert_eq!(reads_after_move(&fn_body(straight, "t"), 1).len(), 1);
    let last_use = straight.replace("_2 = get(move _1)", "_2 = get(copy _1)");
    assert!(reads_after_move(&fn_body(&last_use, "t"), 1).is_empty());
    let pair = straight.replace("_2 = get(move _1)", "_2 = get2(move _1, move _1)");
    assert_eq!(reads_after_move(&fn_body(&pair, "t"), 1).len(), 2);
    let looped = "\
fn t(_1: &mut u64, _2: u32) -> () {
    let mut _0: ();

    bb0: {
        goto -> bb1;
    }

    bb1: {
        switchInt(copy _2) -> [0: bb3, otherwise: bb2];
    }

    bb2: {
        _3 = bump(move _1) -> [return: bb1, unwind continue];
    }

    bb3: {
        return;
    }
}
";
    assert_eq!(reads_after_move(&fn_body(looped, "t"), 1).len(), 1);
    let fixed =
        looped.replace("_3 = bump(move _1)", "_4 = &mut (*_1);\n        _3 = bump(move _4)");
    assert!(reads_after_move(&fn_body(&fixed, "t"), 1).is_empty());
}

/// The text of `fn name(..) { .. }` in a `--emit=mir` file, up to its closing brace.
fn fn_body(mir: &str, name: &str) -> String {
    let header = format!("fn {name}(");
    let start = mir
        .lines()
        .position(|l| l.starts_with(&header))
        .unwrap_or_else(|| panic!("no MIR for `{name}`:\n{mir}"));
    let lines: Vec<&str> = mir.lines().skip(start).collect();
    let end = lines.iter().position(|l| *l == "}").expect("unterminated fn");
    lines[..=end].join("\n")
}

/// Does `line` mention the local `arg` (`_1`, not `_10`)?
fn mentions(line: &str, arg: &str) -> bool {
    occurrences(line, arg).next().is_some()
}

/// Byte offsets of each whole-token occurrence of the local `arg` in `line`.
fn occurrences<'a>(line: &'a str, arg: &'a str) -> impl Iterator<Item = usize> + 'a {
    line.match_indices(arg).map(|(i, _)| i).filter(move |&i| {
        let before = line[..i].chars().next_back();
        let after = line[i + arg.len()..].chars().next();
        !before.is_some_and(|c| c.is_alphanumeric() || c == '_')
            && !after.is_some_and(|c| c.is_ascii_digit())
    })
}

/// Every place where a parameter local `_1..=_params` is used while some path has already
/// moved it (`move _k` of the whole local), found by a forward maybe-moved dataflow over the
/// body's basic blocks. A statement that moves `_k` and mentions it again (another operand of
/// the same call, say) counts too.
fn reads_after_move(body: &str, params: usize) -> Vec<String> {
    let mut blocks: BTreeMap<usize, (Vec<String>, Vec<usize>)> = BTreeMap::new();
    let mut current: Option<usize> = None;
    for line in body.lines() {
        let t = line.trim();
        if let Some(rest) = t.strip_prefix("bb") {
            if t.ends_with('{') {
                let n: String = rest.chars().take_while(|c| c.is_ascii_digit()).collect();
                let id = n.parse().expect("block number");
                blocks.insert(id, (Vec::new(), Vec::new()));
                current = Some(id);
                continue;
            }
        }
        if t == "}" {
            current = None;
            continue;
        }
        let Some(id) = current else { continue };
        let entry = blocks.get_mut(&id).unwrap();
        if let Some((_, targets)) = t.split_once(" -> ") {
            for part in targets.split("bb").skip(1) {
                let n: String = part.chars().take_while(|c| c.is_ascii_digit()).collect();
                if let Ok(s) = n.parse() {
                    entry.1.push(s);
                }
            }
        }
        entry.0.push(t.to_string());
    }
    assert!(blocks.contains_key(&0), "no entry block:\n{body}");

    let args: Vec<String> = (1..=params).map(|p| format!("_{p}")).collect();
    let mut moved_in: BTreeMap<usize, BTreeSet<usize>> = BTreeMap::new();
    moved_in.insert(0, BTreeSet::new());
    let mut work = vec![0usize];
    let mut visited = BTreeSet::new();
    let mut errors = BTreeSet::new();
    while let Some(b) = work.pop() {
        visited.insert(b);
        let mut moved = moved_in[&b].clone();
        let (stmts, succs) =
            blocks.get(&b).unwrap_or_else(|| panic!("edge to an undeclared bb{b}:\n{body}"));
        for s in stmts {
            for (k, arg) in args.iter().enumerate() {
                let uses = occurrences(s, arg).count();
                let moves = occurrences(s, arg).filter(|&i| s[..i].ends_with("move ")).count();
                if uses > 0 && moved.contains(&k) {
                    errors.insert(format!("bb{b}: `{s}` reads {arg} after a move of it"));
                }
                if moves > 0 && uses > 1 {
                    errors.insert(format!("bb{b}: `{s}` moves {arg} and reads it again"));
                }
                if moves > 0 {
                    moved.insert(k);
                }
            }
        }
        for &s in succs {
            let into = moved_in.entry(s).or_default();
            let before = into.len();
            into.extend(moved.iter().copied());
            if (into.len() != before || !visited.contains(&s)) && !work.contains(&s) {
                work.push(s);
            }
        }
    }
    errors.into_iter().collect()
}
