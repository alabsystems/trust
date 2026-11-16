#!/usr/bin/env python3
"""The ever-init footprint ladder (T3 SEAL-1): verification memory against program size.

Author: Andrew Yates. Copyright 2026 Andrew Yates. License: Apache-2.0 OR MIT.

MEASUREMENT, NOT A GATE. The T3 design
(docs/design/2026-10-08-t3-memory-proportional-reconstruction.md §13) judges its
landings on how a verifying compile's peak memory grows with the size of one
function. The input is the macro of tests/ui/borrowck/ever-init-many-locals.rs,
whose N let-bound boxes make the per-function VC output Θ(rows × cone) today.
This script generates `ever_init_N.rs` for each rung N (default 1, 200, 400,
800, 1600), compiles each ALONE under `taskpolicy -m <MiB>` and
`/usr/bin/time -l` with

    $STAGE1/bin/rustc -Ztrust-verify=on -Ztrust-policy=strict
        -Ztrust-verify-output=json -C opt-level=0 --crate-type lib ever_init_N.rs

and records, per rung: peak memory footprint F(N), maximum resident set size,
wall time, rc, the obligation outcome tallies, the stop-cause tallies (each
row's `[stop:<cause>]` token and the coverage row's `noted_stops`), every
counter the coverage row carries beyond its fixed fields, and the counters of
its memory summary (`memory_counters`). T3 L4 C09w makes that summary required
(`memory`, schema `trust-memory-summary/v1`): a rung whose coverage row lacks it
could not be measured, and the run says so. `-Ztrust-verify-output=json` only
selects how rows are printed (the option is TRACKED_NO_CRATE_HASH); it is there
because the stop tallies are read from the TRUST_JSON transport.

Rungs of 800 and more pass `-Ztrust-verify-function-budget-ms=0` while the
compiler has that option (plan SF22: the wall clock would otherwise end the
large rungs, and a clock stop is not a measurement); the record says which
flags each rung ran with.

`--targo-rung N` (repeatable) also runs `targo trust check` on a generated
`ever_init_N` crate and records the process tree's max RSS, and
`targo_retained_transport_bytes` once targo-trust reports it (T3 C11e adds it;
until then the record says `absent`).

KEYED BY STABLE ID (T3 C01b). Each rung also records its VERDICT VECTOR: one
`(obligation key, status, stop)` row per published obligation, the key being
T9's stable `<function>#<local id>` (the function envelope's `stable_ids`,
`trust_types::obligation_identity`), the stop being
`trust_types::determinism::StopCause::of_outcome` of the row's outcome and
reason (ported below, rule for rule), sorted as `VerdictVector::new` sorts and
digested as `VerdictVector::digest` digests (domain `trust-verdict-vector/v2`).
A function whose envelope carries no ids, or a number other than its row count,
is listed in `unkeyed_functions` and contributes no row: its verdicts cannot be
compared, exactly as targo-trust's `UnitDeterminism::of_rows` reads it. Each
rung's vector is also written to `<out-dir>/ever_init_N.vector.tsv`.

`--baseline-out FILE` writes the path-free part of the record (compiler
identity, and per rung its flags, rc, memory, wall, load, tallies and verdict
vector): the form a baseline is committed in. `--compare FILE` reads a baseline
(or a full v2 record) and prints, per rung present in both, whether the two
verdict vectors are identical and which stable keys were added, removed or
changed; the record carries the same as `vector_diff`. It is a report, not a
verdict: the exit status does not depend on it.

"Each run alone on an idle m3" is the operator's half: the script runs the rungs
one after another and records the 1-minute load average before each, so a run
taken on a busy machine says so.

Usage:
    scripts/measure_ever_init_ladder.py --stage1 build/host/stage1 \\
        [--rungs 1,200,400,800,1600] [--out-dir DIR] [--json FILE] \\
        [--memory-limit-mib 49152] [--targo-rung N ...] \\
        [--baseline-out FILE] [--compare BASELINE]

Exit 0 when every requested rung ran (whatever its rc: a refused or failed
compile is a measurement), 2 on a usage error, 3 when a rung could not be run
at all (no compiler, the fixture's macro not found) or the `--compare` file is
not a v2 record or baseline.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import time
from pathlib import Path
from typing import Any

REPO_ROOT = Path(__file__).resolve().parent.parent
FIXTURE = REPO_ROOT / "tests/ui/borrowck/ever-init-many-locals.rs"
DEFAULT_RUNGS = (1, 200, 400, 800, 1600)
# SF22: the rungs at or above this pass the clock-off flag while it exists.
CLOCK_OFF_FROM = 800
CLOCK_OFF_FLAG = "-Ztrust-verify-function-budget-ms=0"
DEFAULT_MEMORY_LIMIT_MIB = 48 * 1024
STOP_TOKEN = re.compile(r"\[stop:([a-z-]+)")
TRANSPORT = "TRUST_JSON:"
# The coverage row's fixed fields; anything else it carries is a counter.
COVERAGE_FIXED = {
    "type",
    "crate_name",
    "package_name",
    "primary_package",
    "verification_session",
    "eligible",
    "processed",
    "function_identities",
    "noted_stops",
    "degraded_anchors",
    "memory",
}
# T3 L4 C09w: the coverage row's required memory summary (L4-SUMMARY-1). A rung whose
# coverage row lacks it, or carries another schema, could not be measured.
MEMORY_SCHEMA = "trust-memory-summary/v1"


SCHEMA = "trust.ever-init-ladder.v2"
BASELINE_SCHEMA = "trust.ever-init-ladder-baseline.v1"

# trust_types::determinism, ported rule for rule (C01b): the stop causes and the
# class each belongs to (`StopCause::reproducibility`): 0 deterministic, 1 not
# reproducible, 2 could not run.
STOP_RANK = {
    "admission-refused": 2,
    "effort": 0,
    "frames": 0,
    "not-dispatched": 0,
    "rss-backstop": 1,
    "solved": 0,
    "solver-fault": 1,
    "solver-incomplete": 0,
    "steps": 0,
    "term-memory": 0,
    "unclassified": 1,
    "unsupported": 0,
    "wall-backstop": 1,
}
# `Outcome::as_str` spellings.
OUTCOMES = {
    "proved", "failed", "unknown", "timeout", "runtime_checked",
    "skipped", "unsupported", "canceled", "rejected",
}
VERDICT_VECTOR_DOMAIN = b"trust-verdict-vector/v2\0"
KEY_SEPARATOR = "#"


def combine_stop(inner: str, outer: str) -> str:
    """`StopCause::combine`: the less reproducible cause wins; within a class
    the outer one, except that `unclassified` never replaces a stated cause."""
    if STOP_RANK[inner] > STOP_RANK[outer]:
        return inner
    if STOP_RANK[outer] > STOP_RANK[inner]:
        return outer
    return inner if outer == "unclassified" else outer


def stop_from_reason(reason: str) -> str | None:
    """`StopCause::from_reason`: every `[stop:<cause>]` token, folded in order
    with `combine_stop`; a token naming no known cause is ignored."""
    found: str | None = None
    rest = reason
    while True:
        at = rest.find("[stop:")
        if at < 0:
            break
        after = rest[at + len("[stop:") :]
        close = after.find("]")
        if close < 0:
            break
        cause = after[:close]
        if cause in STOP_RANK:
            found = cause if found is None else combine_stop(found, cause)
        rest = after[close:]
    return found


def stop_of_outcome(outcome: str, reason: str | None) -> str:
    """`StopCause::of_outcome`: the stop cause of one transported row."""
    stated = stop_from_reason(reason) if reason else None
    if outcome in ("timeout", "canceled") and stated is not None:
        return combine_stop(stated, "wall-backstop")
    if stated is not None:
        return stated
    if outcome in ("proved", "failed", "rejected"):
        return "solved"
    if outcome in ("timeout", "canceled"):
        return "wall-backstop"
    if outcome == "skipped":
        return "not-dispatched"
    if outcome == "unsupported":
        return "unsupported"
    return "unclassified"


def volatile_key_reason(key: str) -> str | None:
    """`VerdictEntry::new`'s refusal of a key that carries volatile identity."""
    if not key.strip():
        return "it is empty"
    if "rustc-crate:" in key:
        return "it names a crate hash"
    if (
        "path+file://" in key
        or "registry+" in key
        or "git+" in key
        or key.startswith("/")
        or ":/" in key
    ):
        return "it names a package ID or an absolute path"
    return None


def verdict_vector_digest(entries: list[list[str]]) -> str:
    """`VerdictVector::digest` over rows already in canonical order: the domain,
    the row count, then each field length-prefixed (u64 little-endian)."""
    h = hashlib.sha256()
    h.update(VERDICT_VECTOR_DOMAIN)
    h.update(len(entries).to_bytes(8, "little"))
    for entry in entries:
        for field in entry:
            raw = field.encode("utf-8")
            h.update(len(raw).to_bytes(8, "little"))
            h.update(raw)
    return h.hexdigest()


class CouldNotRun(Exception):
    """A rung that could not be run at all (exit 3)."""


def make_locals_macro(fixture: Path) -> str:
    """The fixture's `macro_rules! make_locals { ... }` item, verbatim.

    Taken from the file each time, by brace matching, so the ladder's input
    stays the fixture's shape if the fixture changes.
    """
    text = fixture.read_text(encoding="utf-8")
    start = text.find("macro_rules! make_locals")
    if start < 0:
        raise CouldNotRun(f"{fixture}: no `macro_rules! make_locals` item")
    line_start = text.rfind("\n", 0, start) + 1
    open_at = text.find("{", start)
    depth = 0
    for i in range(open_at, len(text)):
        if text[i] == "{":
            depth += 1
        elif text[i] == "}":
            depth -= 1
            if depth == 0:
                return text[line_start : i + 1]
    raise CouldNotRun(f"{fixture}: `make_locals` is not brace-balanced")


def ever_init_source(n: int, macro: str) -> str:
    """`ever_init_N.rs`: the fixture's function with N locals, as a library."""
    width = max(3, len(str(n)))
    names = [f"a{i:0{width}d}" for i in range(1, n + 1)]
    rows = [", ".join(names[i : i + 10]) for i in range(0, len(names), 10)]
    args = ",\n        ".join(rows)
    return (
        f"// Generated by scripts/measure_ever_init_ladder.py: the `make_locals` macro of\n"
        f"// tests/ui/borrowck/ever-init-many-locals.rs with N = {n} locals.\n"
        f"pub fn many_locals() -> u64 {{\n"
        f"    let mut sum = 0u64;\n"
        f"{macro}\n"
        f"    make_locals!(\n"
        f"        {args}\n"
        f"    );\n"
        f"    sum\n"
        f"}}\n"
    )


def parse_time_l(path: Path) -> dict[str, Any]:
    """The fields of BSD `/usr/bin/time -l` the ladder records."""
    out: dict[str, Any] = {}
    if not path.exists():
        return out
    for line in path.read_text(encoding="utf-8", errors="replace").splitlines():
        line = line.strip()
        m = re.match(r"([\d.]+) real\s+([\d.]+) user\s+([\d.]+) sys", line)
        if m:
            out["wall_s"] = float(m.group(1))
            out["user_s"] = float(m.group(2))
            out["sys_s"] = float(m.group(3))
            continue
        m = re.match(r"(\d+)\s+(maximum resident set size|peak memory footprint)$", line)
        if m:
            key = "max_rss_bytes" if m.group(2).startswith("maximum") else "peak_footprint_bytes"
            out[key] = int(m.group(1))
    return out


def tally_transport(stderr: str) -> dict[str, Any]:
    """Outcome and stop-cause tallies, and the coverage row's counters."""
    outcomes: dict[str, int] = {}
    row_stops: dict[str, int] = {}
    noted_stops: dict[str, int] = {}
    crate_summary: dict[str, Any] | None = None
    counters: dict[str, Any] = {}
    memory: dict[str, Any] | None = None
    functions = 0
    malformed = 0
    entries: list[list[str]] = []
    unkeyed: set[str] = set()
    volatile: list[str] = []
    unrecognized_outcomes = 0
    for line in stderr.splitlines():
        at = line.find(TRANSPORT)
        if at < 0:
            continue
        try:
            row = json.loads(line[at + len(TRANSPORT) :])
        except json.JSONDecodeError:
            malformed += 1
            continue
        kind = row.get("type")
        if kind == "function_result":
            functions += 1
            function = str(row.get("function", ""))
            results = row.get("results", []) or []
            ids = row.get("stable_ids", []) or []
            keyed = len(ids) == len(results)
            if not keyed:
                unkeyed.add(function)
            for index, result in enumerate(results):
                outcome = str(result.get("outcome", "?"))
                outcomes[outcome] = outcomes.get(outcome, 0) + 1
                reason = result.get("reason")
                for cause in STOP_TOKEN.findall(str(reason or "")):
                    row_stops[cause] = row_stops.get(cause, 0) + 1
                if not keyed:
                    continue
                if outcome not in OUTCOMES:
                    unrecognized_outcomes += 1
                key = f"{function}{KEY_SEPARATOR}{ids[index]}"
                why = volatile_key_reason(key)
                if why is not None:
                    volatile.append(f"{key}: {why}")
                    continue
                entries.append([key, outcome, stop_of_outcome(outcome, reason)])
        elif kind == "coverage_summary":
            for stop in row.get("noted_stops", []) or []:
                cause = str(stop.get("cause", "?"))
                noted_stops[cause] = noted_stops.get(cause, 0) + int(stop.get("count", 1))
            counters = {k: v for k, v in row.items() if k not in COVERAGE_FIXED}
            summary = row.get("memory")
            if (
                not isinstance(summary, dict)
                or summary.get("schema") != MEMORY_SCHEMA
                or not isinstance(summary.get("counters"), dict)
            ):
                raise CouldNotRun(
                    f"a coverage row carries no {MEMORY_SCHEMA} memory summary (C09w): "
                    "the compiler predates it"
                )
            memory = dict(sorted(summary["counters"].items()))
        elif kind == "crate_summary":
            crate_summary = {k: v for k, v in row.items() if k != "type"}
    entries.sort(key=lambda e: (e[0].encode("utf-8"), e[1].encode("utf-8"), e[2].encode("utf-8")))
    return {
        "function_rows": functions,
        "verdict_vector": entries,
        "verdict_vector_sha256": verdict_vector_digest(entries),
        "unkeyed_functions": sorted(unkeyed),
        "volatile_keys": volatile,
        "unrecognized_outcomes": unrecognized_outcomes,
        "outcomes": dict(sorted(outcomes.items())),
        "row_stops": dict(sorted(row_stops.items())),
        "noted_stops": dict(sorted(noted_stops.items())),
        "coverage_counters": counters,
        "memory_counters": memory,
        "crate_summary": crate_summary,
        "malformed_transport_rows": malformed,
    }


def compiler_identity(rustc: Path) -> dict[str, str]:
    out = subprocess.run([str(rustc), "-vV"], capture_output=True, text=True, check=False)
    ident: dict[str, str] = {}
    for line in out.stdout.splitlines():
        key, sep, value = line.partition(": ")
        if sep and key in ("commit-hash", "commit-date", "release", "trust"):
            ident[key] = value
    return ident


def has_clock_off(rustc: Path) -> bool:
    out = subprocess.run([str(rustc), "-Z", "help"], capture_output=True, text=True, check=False)
    return "trust-verify-function-budget-ms" in out.stdout


def load_1m() -> float | None:
    try:
        return round(os.getloadavg()[0], 2)
    except OSError:
        return None


def timed(cmd: list[str], memory_limit_mib: int, time_file: Path, **kw: Any):
    """Run `cmd` under taskpolicy and /usr/bin/time -l (macOS); plain elsewhere."""
    wrapped = list(cmd)
    if Path("/usr/bin/time").exists():
        wrapped = ["/usr/bin/time", "-l", "-o", str(time_file), *wrapped]
    if shutil.which("taskpolicy"):
        wrapped = ["taskpolicy", "-m", str(memory_limit_mib), *wrapped]
    started = time.monotonic()
    proc = subprocess.run(wrapped, capture_output=True, text=True, check=False, **kw)
    return proc, time.monotonic() - started, wrapped


def run_rung(n: int, rustc: Path, out_dir: Path, macro: str, clock_off: bool, limit: int):
    src = out_dir / f"ever_init_{n}.rs"
    src.write_text(ever_init_source(n, macro), encoding="utf-8")
    flags = [
        "-Ztrust-verify=on",
        "-Ztrust-policy=strict",
        "-Ztrust-verify-output=json",
        "-C",
        "opt-level=0",
        "--crate-type",
        "lib",
    ]
    if n >= CLOCK_OFF_FROM and clock_off:
        flags.append(CLOCK_OFF_FLAG)
    cmd = [str(rustc), *flags, str(src), "-o", str(out_dir / f"libever_init_{n}.rlib")]
    time_file = out_dir / f"ever_init_{n}.time"
    load = load_1m()
    proc, elapsed, wrapped = timed(cmd, limit, time_file)
    (out_dir / f"ever_init_{n}.stderr").write_text(proc.stderr, encoding="utf-8")
    record: dict[str, Any] = {
        "rung": n,
        "kind": "trustc",
        "rc": proc.returncode,
        "load_1m_before": load,
        "flags": flags,
        "command": wrapped,
        "wall_s_monotonic": round(elapsed, 3),
    }
    record.update(parse_time_l(time_file))
    record.update(tally_transport(proc.stderr))
    (out_dir / f"ever_init_{n}.vector.tsv").write_text(
        "".join("\t".join(entry) + "\n" for entry in record["verdict_vector"]),
        encoding="utf-8",
    )
    if n >= CLOCK_OFF_FROM and not clock_off:
        record["note"] = f"{CLOCK_OFF_FLAG} not offered by this compiler; ran with its clock"
    return record


def run_targo_rung(n: int, stage1: Path, out_dir: Path, macro: str, limit: int):
    crate = out_dir / f"targo_ever_init_{n}"
    (crate / "src").mkdir(parents=True, exist_ok=True)
    (crate / "Cargo.toml").write_text(
        f'[package]\nname = "ever_init_{n}"\nversion = "0.0.0"\nedition = "2024"\n\n'
        "[lib]\npath = \"src/lib.rs\"\n\n[workspace]\n",
        encoding="utf-8",
    )
    (crate / "src/lib.rs").write_text(ever_init_source(n, macro), encoding="utf-8")
    targo = stage1 / "bin" / "targo"
    cmd = [str(targo), "trust", "check", "--manifest-path", str(crate / "Cargo.toml")]
    env = dict(os.environ)
    env["CARGO_TARGET_DIR"] = str(out_dir / f"targo_target_{n}")
    env["PATH"] = f"{stage1 / 'bin'}{os.pathsep}{env.get('PATH', '')}"
    time_file = out_dir / f"targo_ever_init_{n}.time"
    load = load_1m()
    proc, elapsed, wrapped = timed(cmd, limit, time_file, env=env)
    (out_dir / f"targo_ever_init_{n}.out").write_text(proc.stdout + proc.stderr, encoding="utf-8")
    retained = re.search(r"targo_retained_transport_bytes\D+(\d+)", proc.stdout + proc.stderr)
    record: dict[str, Any] = {
        "rung": n,
        "kind": "targo",
        "rc": proc.returncode,
        "load_1m_before": load,
        "command": wrapped,
        "wall_s_monotonic": round(elapsed, 3),
        "targo_retained_transport_bytes": int(retained.group(1)) if retained else "absent",
        "rss_scope": "the targo process tree (rusage of its waited children), not targo-trust alone",
    }
    record.update(parse_time_l(time_file))
    return record


def ratios(rows: list[dict[str, Any]]) -> list[dict[str, Any]]:
    """(F(2N) - B) / (F(N) - B) with B = F(1), for each doubling present (§13)."""
    by_n = {r["rung"]: r.get("peak_footprint_bytes") for r in rows if r["kind"] == "trustc"}
    base = by_n.get(1)
    out = []
    for n, f in sorted(by_n.items()):
        f2 = by_n.get(2 * n)
        if n == 1 or f is None or f2 is None or base is None or f == base:
            continue
        out.append({"from": n, "to": 2 * n, "excess_ratio": round((f2 - base) / (f - base), 3)})
    return out


BASELINE_RUNG_FIELDS = (
    "rung", "kind", "rc", "flags", "load_1m_before", "wall_s", "user_s", "sys_s",
    "peak_footprint_bytes", "max_rss_bytes", "function_rows", "outcomes", "row_stops",
    "noted_stops", "coverage_counters", "memory_counters", "crate_summary",
    "malformed_transport_rows",
    "unkeyed_functions", "volatile_keys", "unrecognized_outcomes",
    "verdict_vector_sha256", "verdict_vector", "note",
)


def baseline_of(report: dict[str, Any]) -> dict[str, Any]:
    """The path-free part of a report: what a committed baseline carries."""
    compiler = {k: v for k, v in report["compiler"].items() if k != "path"}
    return {
        "schema": BASELINE_SCHEMA,
        "compiler": compiler,
        "clock_off_flag_offered": report["clock_off_flag_offered"],
        "rungs": [
            {k: r[k] for k in BASELINE_RUNG_FIELDS if k in r}
            for r in report["rungs"]
            if r["kind"] == "trustc"
        ],
        "footprint_excess_ratios": report["footprint_excess_ratios"],
    }


def load_vectors(path: Path) -> dict[int, list[list[str]]]:
    """Rung -> verdict vector, from a v2 report or a baseline."""
    try:
        doc = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as e:
        raise CouldNotRun(f"--compare {path}: {e}") from e
    if doc.get("schema") not in (SCHEMA, BASELINE_SCHEMA):
        raise CouldNotRun(
            f"--compare {path}: schema {doc.get('schema')!r} carries no stable-id vector "
            f"(want {SCHEMA} or {BASELINE_SCHEMA})"
        )
    return {
        int(r["rung"]): [list(e) for e in r["verdict_vector"]]
        for r in doc.get("rungs", [])
        if r.get("kind", "trustc") == "trustc" and "verdict_vector" in r
    }


def vector_diff(base: list[list[str]], cand: list[list[str]]) -> dict[str, Any]:
    """A stable-id differential of two vectors: keys added, removed, changed."""
    def by_key(entries: list[list[str]]) -> dict[str, list[tuple[str, str]]]:
        out: dict[str, list[tuple[str, str]]] = {}
        for key, status, stop in entries:
            out.setdefault(key, []).append((status, stop))
        return out

    b, c = by_key(base), by_key(cand)
    changed = [
        {"key": k, "baseline": b[k], "candidate": c[k]}
        for k in sorted(b.keys() & c.keys())
        if sorted(b[k]) != sorted(c[k])
    ]
    return {
        "identical": base == cand,
        "baseline_sha256": verdict_vector_digest(base),
        "candidate_sha256": verdict_vector_digest(cand),
        "added": sorted(c.keys() - b.keys()),
        "removed": sorted(b.keys() - c.keys()),
        "changed": changed,
    }


def main(argv: list[str]) -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--stage1", default=os.environ.get("STAGE1"),
                    help="the stage1 sysroot (or its bin/); default $STAGE1")
    ap.add_argument("--rungs", default=",".join(map(str, DEFAULT_RUNGS)),
                    help="comma-separated N (default 1,200,400,800,1600)")
    ap.add_argument("--targo-rung", type=int, action="append", default=[],
                    help="also run `targo trust check` on a generated ever_init_N crate")
    ap.add_argument("--out-dir", help="where the inputs, stderr and time records go")
    ap.add_argument("--json", help="write the records here as well as to stdout")
    ap.add_argument("--memory-limit-mib", type=int, default=DEFAULT_MEMORY_LIMIT_MIB,
                    help="taskpolicy -m ceiling for each run (a safety net, not a budget)")
    ap.add_argument("--baseline-out",
                    help="also write the path-free baseline form of the record here")
    ap.add_argument("--compare",
                    help="a baseline (or v2 record) to diff each rung's verdict vector against")
    args = ap.parse_args(argv)

    if not args.stage1:
        ap.error("--stage1 (or $STAGE1) is required")
    stage1 = Path(args.stage1).resolve()
    if stage1.name == "bin":
        stage1 = stage1.parent
    rustc = stage1 / "bin" / "rustc"
    try:
        rungs = [int(x) for x in args.rungs.split(",") if x.strip()]
    except ValueError:
        ap.error(f"--rungs: not a list of integers: {args.rungs}")
    if not rungs or any(n < 1 for n in rungs):
        ap.error("--rungs: every N must be at least 1")

    out_dir = Path(args.out_dir) if args.out_dir else Path.cwd() / "ever-init-ladder"
    out_dir.mkdir(parents=True, exist_ok=True)
    try:
        baseline_vectors = load_vectors(Path(args.compare)) if args.compare else None
        if not rustc.is_file():
            raise CouldNotRun(f"no compiler at {rustc}")
        macro = make_locals_macro(FIXTURE)
        clock_off = has_clock_off(rustc)
        records = [run_rung(n, rustc, out_dir, macro, clock_off, args.memory_limit_mib)
                   for n in rungs]
        records += [run_targo_rung(n, stage1, out_dir, macro, args.memory_limit_mib)
                    for n in args.targo_rung]
    except CouldNotRun as e:
        print(f"COULD NOT RUN: {e}", file=sys.stderr)
        return 3

    if baseline_vectors is not None:
        for r in records:
            if r["kind"] == "trustc" and r["rung"] in baseline_vectors:
                r["vector_diff"] = vector_diff(baseline_vectors[r["rung"]], r["verdict_vector"])
    report = {
        "schema": SCHEMA,
        "compiler": {"path": str(rustc), **compiler_identity(rustc)},
        "clock_off_flag_offered": clock_off,
        "out_dir": str(out_dir),
        "rungs": records,
        "footprint_excess_ratios": ratios(records),
    }
    if args.compare:
        report["compared_against"] = args.compare
    text = json.dumps(report, indent=2, sort_keys=False)
    print(text)
    if args.json:
        Path(args.json).write_text(text + "\n", encoding="utf-8")
    if args.baseline_out:
        Path(args.baseline_out).write_text(
            json.dumps(baseline_of(report), indent=2, sort_keys=False) + "\n", encoding="utf-8"
        )
    for r in records:
        print(
            f"LADDER {r['kind']} N={r['rung']} rc={r['rc']} "
            f"footprint={r.get('peak_footprint_bytes', '?')} max_rss={r.get('max_rss_bytes', '?')} "
            f"wall_s={r.get('wall_s', r['wall_s_monotonic'])} load_1m={r['load_1m_before']} "
            f"outcomes={r.get('outcomes', {})} stops={r.get('row_stops', {})} "
            f"noted={r.get('noted_stops', {})} memory={r.get('memory_counters')} "
            f"vector={r.get('verdict_vector_sha256', '-')[:16]} rows={len(r.get('verdict_vector', []))} "
            f"unkeyed={len(r.get('unkeyed_functions', []))}",
            file=sys.stderr,
        )
        diff = r.get("vector_diff")
        if diff is not None:
            print(
                f"VECTOR N={r['rung']} "
                f"{'identical' if diff['identical'] else 'differs'} "
                f"+{len(diff['added'])} -{len(diff['removed'])} ~{len(diff['changed'])}",
                file=sys.stderr,
            )
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
