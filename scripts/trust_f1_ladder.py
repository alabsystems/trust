#!/usr/bin/env python3
"""trust_f1_ladder.py — how much ordinary Rust the THIR -> trust-ir -> trust-cg lane compiles.

docs/PLAN.md section 2 names the production compile (R-1) and the one backend
consumer (R-5, trust-cg's `Compiler::compile`). This instrument answers one
question about that lane with an EXISTING trustc: of a fixed ladder of ordinary
Rust programs, how many compile on it, link, and print what the LLVM build of
the same source prints.

The corpus is `tests/trust-f1-ladder/`: `programs/` (20 rungs from integer
arithmetic to a small tokenizer) and `micro/` (28 single-construct rungs that
locate the frontier). Each rung is an rlib exporting
`extern "C" fn rung(u64) -> u64`; `driver.rs` links it into an LLVM-built
executable. That shape is forced: the builtin trust-cg backend emits rlibs at
`-Cpanic=abort` only, so no program can be a trust-cg executable yet. The
script passes both and records that it did.

Columns (each compared with an LLVM build of the same rung, built with
verification off and the mode's overflow-check setting):
  f1-strict          -Zcodegen-backend=trust-cg -Ztrust-cg-frontend=trust-ir
                     -Ztrust-cg-f1-backend=compiler, output gate at its
                     default (strict: only [PROVED] functions ship).
                     `--consumer lir` selects the consumer R-5 retires
                     instead, for the parity check of PKG-C2b0 only.
  f1-allow-unknown   the same with -Ztrust-cg-output-gate=allow-unknown, which
                     still refuses a Refuted function but ships bytes the gate
                     did not prove. Not the product.
  llvm-verified      the LLVM backend with verification on (default mode only):
                     what a default build accepts today. It separates a rung
                     the verifier rejects on every backend from a rung this
                     lane alone refuses.

Modes:
  --mode default     the lane selected by its -Z flags with everything else
                     as a default build has it: verification on, overflow
                     checks on. The compiler pins the gate to strict here, so
                     f1-strict and llvm-verified are run.
  --mode fixture     -Ztrust-verify=off -Ztrust-ir-lower=on -Coverflow-checks=off:
                     the configuration the tests/run-make/trust-cg-f1-*
                     fixtures use. It removes every runtime check, so a count
                     here is an upper bound on codegen coverage, not a result
                     about the product.
  --mode fixture-checked
                     the fixture configuration with -Coverflow-checks=on, so
                     the overflow checks are emitted and must panic as LLVM's
                     do.

Per rung the result is one of
  OK        compiled, linked, and matched LLVM on every input
  REFUSED   the compiler exited nonzero; the bracketed refusal classes it
            printed are tallied
  MISMATCH  compiled and linked, and an output or exit code differs from LLVM
  TIMEOUT   the compile ran past --timeout seconds
  LINK      compiled, but the driver did not link against it
  ORACLE    the LLVM build of the rung itself failed (a harness or corpus
            defect; no lane is judged)

Exit status: 1 if any rung is MISMATCH or ORACLE (emitted code is wrong, or
the instrument is broken), 2 on a usage error or when the trustc cannot load
the trust-cg backend, else 0. REFUSED is a
measurement, not a failure of this script. With `--expect LANE=N` the script
also exits 1 unless that lane's OK count is exactly N, so a fixture can pin
the number in either direction; `--expect SET:LANE=N` pins one set's count.

Honesty rules:
  * The compiler identity (`-vV`) is printed and recorded. A count from an
    installed toolchain is a fact about that toolchain, not about main.
  * OK means "agreed with LLVM on the listed inputs", never "proved".
  * Nothing here builds a compiler. All outputs go under --out-dir.

Usage:
  python3 scripts/trust_f1_ladder.py --trustc ~/.rustup/toolchains/trust/bin/trustc \
      --out-dir "$(mktemp -d)" --mode fixture

Author: Andrew Yates | Copyright 2026 Andrew Yates | License: Apache-2.0 OR MIT
"""

from __future__ import annotations

import argparse
import json
import re
import shutil
import subprocess
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[1]
DEFAULT_CORPUS = REPO_ROOT / "tests" / "trust-f1-ladder"
SETS = ("programs", "micro")

# Inputs each built rung is run on. The LLVM build's (exit code, stdout) on the
# same input is the expected value. They stay small on purpose: several rungs
# loop `x` times, and an input the LLVM build cannot finish in the run limit
# compares a timeout with a timeout, which says nothing.
INPUTS = ("0", "1", "2", "3", "7", "8", "10", "16", "255", "999", "4097", "65535")

BASE_FLAGS = ("--crate-type", "rlib", "--crate-name", "rung", "--edition", "2021", "-Cpanic=abort", "-Ccodegen-units=1")
F1_FLAGS = ("-Zcodegen-backend=trust-cg", "-Ztrust-cg-frontend=trust-ir")
# The backend consumer of the lane. `compiler` (trust-cg's `Compiler::compile`)
# is the subject; `lir` is the consumer R-5 retires, measured only so that a
# parity check can show the compiler consumer loses no rung it had.
CONSUMERS = ("compiler", "lir")
MODE_FLAGS = {
    "default": ("-Coverflow-checks=on",),
    "fixture": ("-Ztrust-verify=off", "-Ztrust-ir-lower=on", "-Coverflow-checks=off"),
    "fixture-checked": ("-Ztrust-verify=off", "-Ztrust-ir-lower=on", "-Coverflow-checks=on"),
}
# The LLVM oracle supplies expected output only, so it is always built with
# verification off: a rung the verifier rejects must still have an oracle, or
# the subject lane's own refusal could not be recorded. It keeps the mode's
# overflow-check setting, which changes what the program prints.
ORACLE_FLAGS = {
    "default": ("-Ztrust-verify=off", "-Coverflow-checks=on"),
    "fixture": ("-Ztrust-verify=off", "-Coverflow-checks=off"),
    "fixture-checked": ("-Ztrust-verify=off", "-Coverflow-checks=on"),
}
# The driver executable is always an LLVM build with verification off: it is
# harness, not subject.
DRIVER_FLAGS = ("--edition", "2021", "-Cpanic=abort", "-Ztrust-verify=off", "-Copt-level=0")
LANES = {
    "f1-strict": F1_FLAGS,
    "f1-allow-unknown": F1_FLAGS + ("-Ztrust-cg-output-gate=allow-unknown",),
    "llvm-verified": (),
}
# Under verification the compiler pins the output gate to strict
# (compiler/rustc_session/src/options.rs, `trust_cg_output_gate`), so the
# allow-unknown column would silently repeat f1-strict.
MODE_LANES = {
    "default": ("f1-strict", "llvm-verified"),
    "fixture": ("f1-strict", "f1-allow-unknown"),
    "fixture-checked": ("f1-strict", "f1-allow-unknown"),
}

CLASS_ROW = re.compile(r"^\s*(\d+)\s+\(\s*[\d.]+%\)\s+(\[[^\]]+\])", re.M)
CLASS_TAG = re.compile(r"\[[a-z][a-z0-9:-]*\]")


def run(cmd: list[str], timeout: float) -> tuple[int | None, str, str]:
    """Run `cmd`; a `None` return code means it timed out."""
    try:
        done = subprocess.run(cmd, capture_output=True, timeout=timeout, check=False)
    except subprocess.TimeoutExpired as exc:
        return None, "", (exc.stderr or b"").decode(errors="replace")
    return done.returncode, done.stdout.decode(errors="replace"), done.stderr.decode(errors="replace")


def refusal_classes(stderr: str) -> dict[str, int]:
    """The refusal classes a failed compile printed.

    F1 prints a census (`  3 ( 75.0%) [upstream-body] ...`); when it does, its
    counts are used. A refusal outside the census (a session fatal such as an
    unsupported crate type) has no bracketed class and is tallied under the
    first `error` line instead (names and numbers blanked, so a verifier
    rejection of twenty different functions is one class), so it is never
    dropped.
    """
    rows = CLASS_ROW.findall(stderr)
    if rows:
        out: dict[str, int] = {}
        for count, tag in rows:
            out[tag] = out.get(tag, 0) + int(count)
        return out
    tags = CLASS_TAG.findall("\n".join(line for line in stderr.splitlines() if line.startswith("error")))
    if tags:
        return {tag: 1 for tag in dict.fromkeys(tags)}
    for line in stderr.splitlines():
        if line.startswith("error"):
            # Names and counts vary per rung; the class is the message shape.
            shape = re.sub(r"\d+", "N", re.sub(r"`[^`]*`", "`_`", line))
            return {"(unclassified) " + shape[:120]: 1}
    return {"(unclassified) no error line": 1}


def build_and_run(trustc: str, rung: Path, driver: Path, out: Path, flags: tuple[str, ...], opt: str, timeout: float) -> dict:
    """Compile `rung` with `flags`, link the driver against it, run every input."""
    shutil.rmtree(out, ignore_errors=True)
    out.mkdir(parents=True)
    rc, _, err = run([trustc, str(rung), *BASE_FLAGS, f"-Copt-level={opt}", *flags, "--out-dir", str(out)], timeout)
    (out / "compile.stderr").write_text(err)
    rlib = out / "librung.rlib"
    if rc is None:
        return {"status": "TIMEOUT"}
    if rc != 0 or not rlib.exists():
        return {"status": "REFUSED", "classes": refusal_classes(err)}
    exe = out / "driver"
    rc, _, err = run([trustc, str(driver), *DRIVER_FLAGS, "--extern", f"rung={rlib}", "-o", str(exe)], timeout)
    if rc != 0 or not exe.exists():
        (out / "link.stderr").write_text(err)
        return {"status": "LINK"}
    runs = {}
    for value in INPUTS:
        rc, stdout, _ = run([str(exe), value], 20)
        runs[value] = [rc, stdout.strip()]
    return {"status": "BUILT", "runs": runs}


def measure(trustc: str, corpus: Path, sets: tuple[str, ...], mode: str, opt: str, out_dir: Path, timeout: float, consumer: str = "compiler") -> list[dict]:
    driver = corpus / "driver.rs"
    consumer_flag = (f"-Ztrust-cg-f1-backend={consumer}",)
    results = []
    for set_name in sets:
        for rung in sorted((corpus / set_name).glob("*.rs")):
            base = out_dir / set_name / rung.stem
            oracle = build_and_run(trustc, rung, driver, base / "llvm", ORACLE_FLAGS[mode], opt, timeout)
            row = {"set": set_name, "rung": rung.stem, "lanes": {}}
            for lane in MODE_LANES[mode]:
                if oracle["status"] == "BUILT" and any(rc is None for rc, _ in oracle["runs"].values()):
                    oracle = {"status": "RUN-TIMEOUT"}  # no expected value: judge nothing
                if oracle["status"] != "BUILT":
                    row["lanes"][lane] = {"status": "ORACLE", "oracle": oracle["status"]}
                    continue
                flags = MODE_FLAGS[mode] + LANES[lane] + (consumer_flag if LANES[lane] else ())
                got = build_and_run(trustc, rung, driver, base / lane, flags, opt, timeout)
                if got["status"] == "BUILT":
                    diff = {k: [oracle["runs"][k], got["runs"][k]] for k in INPUTS if oracle["runs"][k] != got["runs"][k]}
                    got = {"status": "MISMATCH", "diff": diff} if diff else {"status": "OK"}
                row["lanes"][lane] = got
            results.append(row)
    return results


def summarize(results: list[dict], lanes: tuple[str, ...]) -> dict:
    summary: dict = {}
    for lane in lanes:
        per_set: dict = {}
        classes: dict[str, int] = {}
        for row in results:
            got = row["lanes"][lane]
            bucket = per_set.setdefault(row["set"], {"total": 0})
            bucket["total"] += 1
            bucket[got["status"]] = bucket.get(got["status"], 0) + 1
            for tag, count in got.get("classes", {}).items():
                classes[tag] = classes.get(tag, 0) + count
        summary[lane] = {"sets": per_set, "refusal_classes": dict(sorted(classes.items(), key=lambda kv: (-kv[1], kv[0])))}
    return summary


def render(identity: str, mode: str, opt: str, results: list[dict], summary: dict, lanes: tuple[str, ...], consumer: str = "compiler") -> str:
    lines = [
        f"trustc: {identity}",
        f"mode: {mode}  consumer: {consumer}  opt-level: {opt}  (rlib, -Cpanic=abort; driver and oracle are LLVM builds)",
        "",
    ]
    table = [["rung", *lanes]]
    for row in results:
        cells = [row["rung"]]
        for lane in lanes:
            got = row["lanes"][lane]
            cell = got["status"]
            if got.get("classes"):
                cell += " " + next(iter(got["classes"]))[:60]
            cells.append(cell)
        table.append(cells)
    widths = [max(len(r[i]) for r in table) for i in range(len(table[0]))]
    lines.extend("  ".join(cell.ljust(w) for cell, w in zip(r, widths)).rstrip() for r in table)
    lines.append("")
    for lane in lanes:
        for set_name, bucket in summary[lane]["sets"].items():
            rest = ", ".join(f"{k} {v}" for k, v in sorted(bucket.items()) if k not in ("total", "OK"))
            lines.append(f"{lane} {set_name}: {bucket.get('OK', 0)}/{bucket['total']} OK" + (f" ({rest})" if rest else ""))
        if summary[lane]["refusal_classes"]:
            lines.append(f"{lane} refusal rows by class:")
            lines.extend(f"  {count:4d}  {tag}" for tag, count in summary[lane]["refusal_classes"].items())
    return "\n".join(lines)


def ok_count(summary: dict, lane: str, set_name: str | None = None) -> int:
    return sum(bucket.get("OK", 0) for name, bucket in summary[lane]["sets"].items() if set_name in (None, name))


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("--trustc", required=True, help="an existing trustc with the builtin trust-cg backend")
    parser.add_argument("--out-dir", required=True, type=Path, help="scratch directory for every output")
    parser.add_argument("--corpus", type=Path, default=DEFAULT_CORPUS)
    parser.add_argument("--set", dest="sets", choices=SETS + ("all",), default="all")
    parser.add_argument("--mode", choices=sorted(MODE_FLAGS), default="default")
    parser.add_argument("--consumer", choices=CONSUMERS, default="compiler", help="the F1 backend consumer (-Ztrust-cg-f1-backend); `lir` is for the parity check only")
    parser.add_argument("--opt", choices=("0", "1", "2", "3"), default="0")
    parser.add_argument("--timeout", type=float, default=120.0, help="seconds per compile")
    parser.add_argument("--expect", action="append", default=[], metavar="[SET:]LANE=N", help="exit 1 unless LANE's OK count (in SET, or over every set run) is exactly N")
    args = parser.parse_args(argv)

    lanes = MODE_LANES[args.mode]
    sets = SETS if args.sets == "all" else (args.sets,)
    expect = {}
    for item in args.expect:
        key, sep, count = item.partition("=")
        set_name, colon, lane = key.rpartition(":")
        if not sep or lane not in lanes or not count.isdigit() or (colon and set_name not in sets):
            print(
                f"trust_f1_ladder: --expect {item!r}: want [SET:]LANE=N with LANE in {list(lanes)} for --mode {args.mode} and SET in {list(sets)}",
                file=sys.stderr,
            )
            return 2
        expect[(set_name or None, lane)] = int(count)
    for set_name in sets:
        if not any((args.corpus / set_name).glob("*.rs")):
            print(f"trust_f1_ladder: no rungs in {args.corpus / set_name}", file=sys.stderr)
            return 2

    rc, stdout, stderr = run([args.trustc, "-vV"], 60)
    if rc != 0:
        print(f"trust_f1_ladder: `{args.trustc} -vV` failed: {stderr.strip()[:200]}", file=sys.stderr)
        return 2
    identity = stdout.splitlines()[0] if stdout else "unknown"
    # A trustc without the builtin backend would refuse every rung, and an
    # all-REFUSED ladder exits 0. Refuse to measure instead (compiletest's
    # `needs-trust-cg-backend` uses the same probe).
    rc, _, stderr = run([args.trustc, "-Zunstable-options", "--print=supported-crate-types", "-Zcodegen-backend=trust-cg"], 60)
    if rc != 0:
        print(f"trust_f1_ladder: {args.trustc} cannot load the trust-cg backend: {stderr.strip()[:200]}", file=sys.stderr)
        return 2

    results = measure(args.trustc, args.corpus, sets, args.mode, args.opt, args.out_dir, args.timeout, args.consumer)
    summary = summarize(results, lanes)
    print(render(identity, args.mode, args.opt, results, summary, lanes, args.consumer))
    (args.out_dir / "results.json").write_text(
        json.dumps(
            {"trustc": stdout, "mode": args.mode, "consumer": args.consumer, "opt": args.opt, "inputs": INPUTS, "summary": summary, "results": results},
            indent=1,
        )
    )

    failed = False
    for row in results:
        for lane, got in row["lanes"].items():
            if got["status"] in ("MISMATCH", "ORACLE"):
                print(f"trust_f1_ladder: {row['set']}/{row['rung']} {lane}: {got['status']} {got.get('diff') or got.get('oracle')}", file=sys.stderr)
                failed = True
    for (set_name, lane), want in expect.items():
        got_count = ok_count(summary, lane, set_name)
        if got_count != want:
            print(f"trust_f1_ladder: {set_name + ':' if set_name else ''}{lane}: {got_count} OK, expected {want}", file=sys.stderr)
            failed = True
    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main())
