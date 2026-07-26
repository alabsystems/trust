#!/usr/bin/env python3
# Standing spec-vs-artifact guard for the aterm-parser refinement obligation.
#
# The trust-certify finite-DFA lane re-checks that a trust-ir program refines a
# SPEC (concrete next-state / action / classifier tables, committed as Rust
# literals in `src/finite_dfa_from_ir.rs`). Those literals were transcribed from
# the real compiled `aterm_parser::TRANSITIONS`. This script is the CONTINUOUS
# guard the §8.10 audit named as missing: it re-dumps the live aterm table and
# diffs every committed literal against it, so silent spec-vs-artifact drift
# (a future aterm table change, or a bad edit to a literal) is caught.
#
# It is a STRUCTURAL drift check, not a kernel re-proof — the kernel proofs live
# in the lane. It needs the aterm source tree (ATERM_DIR, default ~/aterm); it
# adds no build-time dependency on aterm (option 2 of the §8.11 trade-off matrix).
#
# This is the lower two of the three evidence rungs that, together, span the chain
# from a trust-ir program to the documented standard:
#   Rung 1 (kernel PROOF, in the lane): trust-ir program  ==  spec.
#   Rung 2 (this script, STRUCTURAL):   spec  ==  aterm's live TRANSITIONS table.
#   Rung 3 (--oracle, EVIDENCE):        aterm's table  behaves per the standard,
#           witnessed by aterm's own vt100.net-DEC-ANSI conformance suite passing.
# Rung 3 is evidence on the tested inputs (aterm's own tests), NOT a proof — that
# the table is faithful to ECMA-48/VT500 in full is the irreducible spec=intent
# residue (§8.10/§8.12): only an external oracle can speak to it, and Rung 3 wires
# in the best available one rather than leaving it as prose.
#
# Usage:  python3 check_aterm_spec_drift.py [--aterm DIR] [--oracle]
# Exit 0 = all requested rungs pass; exit 1 = drift or (with --oracle) a conformance failure.
#
# Author: Andrew Yates | Apache-2.0

import argparse
import os
import re
import subprocess
import sys
import tempfile
from pathlib import Path

REP8_BYTES = [0x05, 0x18, 0x1B, 0x20, 0x30, 0x3B, 0x40, 0x9B]  # C0,CAN,ESC,inter,digit,semi,final,C1CSI
N_ACT = 17  # ActionType variant count (None=0..ApcEnd=16); pair encode = ns*17+act

DUMP_TEST = r'''
use aterm_parser::TRANSITIONS;
use std::fmt::Write as _;
use std::fs;
#[test]
fn _spec_drift_dump() {
    let (mut ns, mut act) = (String::new(), String::new());
    for s in 0..14usize {
        let nr: Vec<String> = (0..256).map(|b| (TRANSITIONS[s][b].next_state as u8).to_string()).collect();
        let ar: Vec<String> = (0..256).map(|b| (TRANSITIONS[s][b].action as u8).to_string()).collect();
        let _ = writeln!(ns, "{}", nr.join(" "));
        let _ = writeln!(act, "{}", ar.join(" "));
    }
    fs::write(std::env::var("SPEC_DRIFT_NS").unwrap(), ns).unwrap();
    fs::write(std::env::var("SPEC_DRIFT_ACT").unwrap(), act).unwrap();
}
'''


def dump_live_table(aterm_dir: Path):
    """Dump the live 14x256 next-state + action tables from the compiled artifact."""
    test_path = aterm_dir / "crates" / "aterm-parser" / "tests" / "_spec_drift_dump.rs"
    ns_path = Path(tempfile.gettempdir()) / "spec_drift_ns.txt"
    act_path = Path(tempfile.gettempdir()) / "spec_drift_act.txt"
    test_path.write_text(DUMP_TEST)
    try:
        env = dict(os.environ, SPEC_DRIFT_NS=str(ns_path), SPEC_DRIFT_ACT=str(act_path))
        subprocess.run(
            ["cargo", "test", "-p", "aterm-parser", "--test", "_spec_drift_dump", "--", "--nocapture"],
            cwd=aterm_dir, env=env, check=True, capture_output=True,
        )
    finally:
        test_path.unlink(missing_ok=True)
    ns = [list(map(int, l.split())) for l in ns_path.read_text().strip().splitlines()]
    act = [list(map(int, l.split())) for l in act_path.read_text().strip().splitlines()]
    ns_path.unlink(missing_ok=True)
    act_path.unlink(missing_ok=True)
    assert len(ns) == 14 and all(len(r) == 256 for r in ns), "bad ns dump"
    assert len(act) == 14 and all(len(r) == 256 for r in act), "bad act dump"
    return ns, act


# aterm's own vt100.net-DEC-ANSI-derived conformance modules: feeding real byte
# sequences and asserting the spec-correct state/action. This is the EXTERNAL
# ORACLE rung — it is EVIDENCE (on the tested inputs), not a proof, and they are
# aterm's own tests, but they tie the table to the documented standard
# (vt100.net/emu/dec_ansi_parser, cited in table/mod.rs + state.rs).
ORACLE_MODULES = [
    "tests::basic", "tests::csi", "tests::c1", "tests::subparams",
    "tests::utf8_errors", "tests::table_validity", "tests::invariants", "tests::refinement",
]


def run_oracle(aterm_dir: Path):
    """Run aterm's conformance suite. Returns (ok, summary_line)."""
    proc = subprocess.run(
        ["cargo", "test", "-p", "aterm-parser", "--lib", "--"] + ORACLE_MODULES,
        cwd=aterm_dir, capture_output=True, text=True,
    )
    out = proc.stdout + proc.stderr
    m = re.search(r"test result:\s*(ok|FAILED)\.\s*(\d+)\s+passed;\s*(\d+)\s+failed", out)
    if proc.returncode == 0 and m and m.group(1) == "ok" and m.group(3) == "0":
        return True, f"{m.group(2)} passed; 0 failed"
    return False, (m.group(0) if m else f"cargo exited {proc.returncode}")


def partition(columns):
    """columns: list of 256 tuples; return (sorted distinct cols, byte->class idx)."""
    distinct = sorted(set(columns))
    idx = {c: i for i, c in enumerate(distinct)}
    return distinct, [idx[c] for c in columns]


def expected(ns, act):
    """Recompute every committed literal from the live dump."""
    out = {}
    out["full_nextstate_14x256"] = ns
    out["full_action_14x256"] = act
    out["full_aterm_matrix"] = [[ns[s][b] for b in REP8_BYTES] for s in range(14)]
    # 19-class next-state partition
    cols = [tuple(ns[s][b] for s in range(14)) for b in range(256)]
    distinct, classify = partition(cols)
    out["full_aterm_class_matrix"] = [[distinct[k][s] for k in range(len(distinct))] for s in range(14)]
    out["aterm_byte_classifier_row"] = [classify]
    # 23-class (next_state,action) pair partition (encoded ns*17+act)
    pcols = [tuple(ns[s][b] * N_ACT + act[s][b] for s in range(14)) for b in range(256)]
    pdist, pclassify = partition(pcols)
    out["pair_nextstate_matrix"] = [[pdist[k][s] // N_ACT for k in range(len(pdist))] for s in range(14)]
    out["pair_action_matrix"] = [[pdist[k][s] % N_ACT for k in range(len(pdist))] for s in range(14)]
    out["aterm_pair_classifier_row"] = [pclassify]
    return out


def extract_literal(src: str, fn_name: str):
    """Parse `fn fn_name() -> Vec<Vec<i128>> { vec![ ... ] }` into a list of lists."""
    m = re.search(r"fn %s\(\)\s*->\s*Vec<Vec<i128>>\s*\{" % re.escape(fn_name), src)
    if not m:
        return None
    # find the matching outer vec![ ... ] by brace/bracket counting from the body
    i = src.index("vec![", m.end())
    depth, j = 0, i
    while j < len(src):
        if src[j] == "[":
            depth += 1
        elif src[j] == "]":
            depth -= 1
            if depth == 0:
                break
        j += 1
    body = src[i:j + 1]
    body = re.sub(r"//[^\n]*", "", body)  # strip line comments (may sit inside a row)
    # split into inner vec![...] rows
    rows = re.findall(r"vec!\[([^\]]*)\]", body)
    return [[int(x) for x in re.findall(r"-?\d+", r)] for r in rows]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--aterm", default=os.path.expanduser("~/aterm"))
    ap.add_argument("--oracle", action="store_true",
                    help="also run aterm's vt100.net-derived conformance suite as the "
                         "standard-conformance evidence rung")
    args = ap.parse_args()
    aterm_dir = Path(args.aterm)
    src_path = Path(__file__).resolve().parent.parent / "src" / "finite_dfa_from_ir.rs"
    if not (aterm_dir / "crates" / "aterm-parser").is_dir():
        print(f"SKIP: aterm source not found at {aterm_dir} (set --aterm)", file=sys.stderr)
        return 0
    src = src_path.read_text()

    ns, act = dump_live_table(aterm_dir)
    exp = expected(ns, act)

    ok = True
    for fn_name, expected_mat in exp.items():
        committed = extract_literal(src, fn_name)
        if committed is None:
            print(f"DRIFT: committed literal `{fn_name}` not found in {src_path.name}")
            ok = False
            continue
        if committed != expected_mat:
            ok = False
            print(f"DRIFT in `{fn_name}`:")
            for r, (c_row, e_row) in enumerate(zip(committed, expected_mat)):
                if c_row != e_row:
                    diffs = [(j, c, e) for j, (c, e) in enumerate(zip(c_row, e_row)) if c != e]
                    print(f"  row {r}: {diffs[:8]}{' …' if len(diffs) > 8 else ''}")
            if len(committed) != len(expected_mat):
                print(f"  row count: committed {len(committed)} vs live {len(expected_mat)}")
        else:
            print(f"OK: `{fn_name}` matches the live aterm artifact ({len(expected_mat)} rows)")

    # The trust-cg-bridge codegen test inlines COPIES of two proven literals
    # (class19_matrix, byte_classifier) to author the table_step VerifiableFunction.
    # Guard them against the same live artifact so they can't silently drift.
    cg_path = (Path(__file__).resolve().parent.parent.parent
               / "trust-cg-bridge" / "tests" / "aterm_table_step_codegen.rs")
    if cg_path.is_file():
        cg = cg_path.read_text()
        cg_class = extract_literal(cg, "class19_matrix")
        if cg_class != exp["full_aterm_class_matrix"]:
            print("DRIFT: trust-cg-bridge class19_matrix != proven class matrix")
            ok = False
        else:
            print("OK: trust-cg-bridge `class19_matrix` matches the proven class matrix")
        cg_clf = [int(x) for x in re.findall(r"-?\d+", re.sub(
            r"//[^\n]*", "", cg[cg.index("fn byte_classifier()"):][:4000]))]
        # drop the leading "256"/"64" width tokens if any; the body is exactly 256 entries
        cg_clf = cg_clf[:256] if len(cg_clf) >= 256 else cg_clf
        if cg_clf != exp["aterm_byte_classifier_row"][0]:
            print("DRIFT: trust-cg-bridge byte_classifier != proven classifier")
            ok = False
        else:
            print("OK: trust-cg-bridge `byte_classifier` matches the proven classifier")

    if ok:
        print("\nRung 2 PASS: every committed spec literal matches the live aterm_parser::TRANSITIONS.")
    else:
        print("\nRung 2 FAIL: spec drifted from the live artifact (see above).", file=sys.stderr)

    if args.oracle:
        oracle_ok, summary = run_oracle(aterm_dir)
        if oracle_ok:
            print(f"Rung 3 PASS: aterm's vt100.net conformance suite green ({summary}) — "
                  "evidence (on tested inputs) that the table behaves per the documented standard.")
        else:
            print(f"Rung 3 FAIL: aterm conformance suite not green ({summary}).", file=sys.stderr)
            ok = False

    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
