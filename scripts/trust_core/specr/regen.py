#!/usr/bin/env python3
"""regen — the specr → Clean translator v2's byte-identical regeneration and its drift check.

RM1 of docs/plans/2026-10-15-proven-core.md: "regeneration is byte-identical". This driver
turns the pinned inputs into the committed outputs with the committed translator, and the
check fails on any byte that differs.

Inputs (pinned/, each recorded by sha256 in generated/MANIFEST.json):
  pinned/ast.json.gz       the syn front end's JSON AST of MiniRust's specr sources at the
                           pin (EXTERNAL_PINS.toml [sources.minirust]), for the files
                           slice.json names; gzip with no name and mtime 0
  pinned/records.jsonl.gz  the minitest programs and the outcomes the tests assert (K8's
                           export, minitest-export/ of the K8 report)
  slice.json               the slice and its monomorphization
Translator: specr2clean/*.py, conformance/*.py, this driver (regen.py), and the hand-authored
Lean the outputs are checked with: SpecrPrelude.lean (the runtime), PreludeVectors.lean (its
vectors) and SliceVectors.lean (the slice's int2ptr prediction, which no minitest reaches).
Outputs (generated/):
  MiniRustSlice.lean, census.json, schema.json         the translator's
  selection.json, conformance.lean.gz, conformance_index.json   the conformance theorems'

Usage:
  regen.py [check]  [--root DIR] [--from-source [--frontend BIN] [--minirust DIR]] [--clean BIN]
  regen.py write    [--root DIR] [--from-source [--frontend BIN] [--minirust DIR]]

check (the default) regenerates every output into a scratch directory and compares it with
the committed bytes, compares every pinned input and translator file with its manifest
digest, and fails on any file in generated/ that is not an output or the manifest. It also
compares SpecrPrelude.lean and generated/MiniRustSlice.lean with the copies Clean's TrustSem
fixture imports (--fixture; by default the pinned first-party/clean's
crates/clean-olean/tests/fixtures/lean/v4.30.0-rc2/trust_sem/), where Clean proves core_wf,
run_sound, run_ub and run_adequate over this SOut and checks the slice through the reference
entry: a copy that differs is DRIFT; a pinned Clean that has no copies yet is reported as
PENDING (the pin predates the fixture) and does not fail. It prints one line per file and
exits 0 when all are identical, 1 on any drift.
--from-source also re-runs the front end (the K8 probe's syn front end, unchanged in v2:
reports/2026-09-17-phase0-k8-specr/translator/frontend, built with
`targo --unverified build --release`) on the MiniRust checkout (the trust-core source
cache by default, common.sources_root()/minirust, which must hold the pin) and compares the
AST with the pinned one. write regenerates the committed outputs and the manifest (and,
with --from-source, the pinned AST) in place.

--clean BIN (check only) also kernel-checks SpecrPrelude.lean, PreludeVectors.lean, the slice,
SliceVectors.lean and the conformance theorems with `BIN check --json` and requires 0 failed
declarations, 0 `sorry` axioms and 0 `sorry` terms minted, 0 kernel-check failures, no
assumption, and every conformance theorem accepted. BIN must report
`trust_summary.sorry_terms_minted`: a clean built from Clean 01189665c (2026-09-28) or later.
The atpkg store's clean 0.9.0 does not report it, and the check then fails closed and says so.
--clean-timeout SECONDS (default 1800) bounds the run: a `clean check` still running then is
killed and the check fails, so a regression that makes evaluation diverge is a red, not a hang.

--root names another copy of this directory (the tests mutate copies).

Author: Andrew Yates <andrewyates.name@gmail.com>
Copyright 2026 Andrew Yates | License: Apache-2.0 OR MIT
"""

from __future__ import annotations

import argparse
import gzip
import hashlib
import io
import json
import os
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent

TRANSLATOR_GLOBS = ("specr2clean/*.py", "conformance/*.py", "regen.py", "SpecrPrelude.lean",
                    "PreludeVectors.lean", "SliceVectors.lean", "slice.json")
OUTPUTS = (
    "generated/MiniRustSlice.lean",
    "generated/census.json",
    "generated/schema.json",
    "generated/selection.json",
    "generated/conformance.lean.gz",
    "generated/conformance_index.json",
)
PINNED = ("pinned/ast.json.gz", "pinned/records.jsonl.gz")
# The files Clean's TrustSem fixture imports, byte for byte (its name for each, our path).
FIXTURE_COPIES = (("SpecrPrelude.lean", "SpecrPrelude.lean"),
                  ("MiniRustSlice.lean", "generated/MiniRustSlice.lean"))
FIXTURE_REL = "first-party/clean/crates/clean-olean/tests/fixtures/lean/v4.30.0-rc2/trust_sem"
CLEAN_TIMEOUT = 1800
# The conformance run's limits (K8's: reports/2026-09-17-phase0-k8-specr/run_probe.sh).
STEPS, FUEL = 200000, 2000


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def gz_bytes(data: bytes) -> bytes:
    """Deterministic gzip: no file name, mtime 0, level 9."""
    buf = io.BytesIO()
    with gzip.GzipFile(filename="", mode="wb", fileobj=buf, compresslevel=9, mtime=0) as f:
        f.write(data)
    return buf.getvalue()


def translator_files(root: Path) -> list[str]:
    out: list[str] = []
    for pat in TRANSLATOR_GLOBS:
        out.extend(sorted(str(p.relative_to(root)) for p in root.glob(pat)))
    return out


def run(cmd: list[str], cwd: Path) -> None:
    proc = subprocess.run(cmd, cwd=cwd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
    if proc.returncode != 0:
        sys.stderr.write(proc.stdout + proc.stderr)
        raise SystemExit(f"regen: `{' '.join(cmd)}` exited {proc.returncode}")


def frontend_ast(root: Path, frontend: Path, minirust: Path) -> bytes:
    slice_cfg = json.loads((root / "slice.json").read_text())
    rev = subprocess.run(["git", "-C", str(minirust), "rev-parse", "HEAD"], stdout=subprocess.PIPE,
                         text=True, check=False).stdout.strip()
    if rev != slice_cfg["minirust_revision"]:
        raise SystemExit(f"regen: {minirust} is at {rev or '?'}, not the pin {slice_cfg['minirust_revision']}")
    proc = subprocess.run([str(frontend), str(minirust / "spec"), *slice_cfg["files"]],
                          stdout=subprocess.PIPE, stderr=subprocess.PIPE, check=False)
    if proc.returncode != 0:
        sys.stderr.write(proc.stderr.decode(errors="replace"))
        raise SystemExit(f"regen: the front end exited {proc.returncode}")
    return proc.stdout


def regenerate(root: Path, ast: bytes, records: bytes, out: Path) -> dict[str, bytes]:
    """Run the translator and the conformance generator of `root` into `out`."""
    py = sys.executable
    # -B: a regeneration writes no bytecode into the tree
    (out / "ast.json").write_bytes(ast)
    (out / "records.jsonl").write_bytes(records)
    run([py, "-B", "specr2clean.py", str(out / "ast.json"), str(root / "slice.json"),
         str(out / "MiniRustSlice.lean"), str(out / "census.json"), str(out / "schema.json")],
        cwd=root / "specr2clean")
    conf = root / "conformance"
    run([py, "-B", "select_slice.py", str(out / "records.jsonl"), str(out / "schema.json"),
         str(out / "selection.json")], cwd=conf)
    bound = json.loads((root / "slice.json").read_text())["pick_candidate_bound"]
    run([py, "-B", "records2clean.py", str(out / "records.jsonl"), str(out / "schema.json"),
         str(out / "selection.json"), str(out / "conformance.lean"), str(out / "conformance_index.json"),
         "--steps", str(STEPS), "--fuel", str(FUEL), "--bound", str(bound)], cwd=conf)
    produced = {
        "generated/MiniRustSlice.lean": (out / "MiniRustSlice.lean").read_bytes(),
        "generated/census.json": (out / "census.json").read_bytes(),
        "generated/schema.json": (out / "schema.json").read_bytes(),
        "generated/selection.json": (out / "selection.json").read_bytes(),
        "generated/conformance.lean.gz": gz_bytes((out / "conformance.lean").read_bytes()),
        "generated/conformance_index.json": (out / "conformance_index.json").read_bytes(),
    }
    return produced


def manifest_for(root: Path, ast: bytes, records: bytes, produced: dict[str, bytes]) -> dict:
    slice_cfg = json.loads((root / "slice.json").read_text())
    return {
        "comment": "regen.py's record: every pinned input, translator file and output by sha256. "
                   "`regen.py check` regenerates the outputs and fails on any byte that differs.",
        "minirust_revision": slice_cfg["minirust_revision"],
        "frontend": "reports/2026-09-17-phase0-k8-specr/translator/frontend (unchanged from K8: syn 2.0.106, syn-serde 0.3.2; Cargo.lock)",
        "conformance_limits": {"steps": STEPS, "fuel": FUEL, "bound": slice_cfg["pick_candidate_bound"]},
        "pinned": {
            "pinned/ast.json.gz": {"gunzipped_sha256": sha256(ast)},
            "pinned/records.jsonl.gz": {"gunzipped_sha256": sha256(records)},
        },
        "translator": {f: sha256((root / f).read_bytes()) for f in translator_files(root)},
        "outputs": {f: sha256(produced[f]) for f in OUTPUTS},
    }


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("mode", nargs="?", default="check", choices=("check", "write"))
    ap.add_argument("--root", type=Path, default=HERE)
    ap.add_argument("--from-source", action="store_true")
    ap.add_argument("--frontend", type=Path)
    ap.add_argument("--minirust", type=Path)
    ap.add_argument("--clean", type=Path)
    ap.add_argument("--clean-timeout", type=float, default=CLEAN_TIMEOUT)
    ap.add_argument("--fixture", type=Path, default=HERE.parents[2] / FIXTURE_REL)
    a = ap.parse_args(argv)
    root = a.root.resolve()

    records = gzip.decompress((root / "pinned/records.jsonl.gz").read_bytes())
    pinned_ast_path = root / "pinned/ast.json.gz"
    pinned_ast = gzip.decompress(pinned_ast_path.read_bytes()) if pinned_ast_path.exists() else None
    ast = pinned_ast
    lines: list[str] = []
    drift = False

    if a.from_source:
        if a.frontend is None:
            raise SystemExit("regen: --from-source needs --frontend <built specr-frontend binary>")
        minirust = a.minirust
        if minirust is None:
            sys.path.insert(0, str(root.parent))
            import common  # noqa: PLC0415  (trust_core/common.py)
            minirust = common.sources_root() / "minirust"
        ast = frontend_ast(root, a.frontend, minirust)
        if a.mode == "check":
            same = pinned_ast is not None and ast == pinned_ast
            drift |= not same
            lines.append(f"{'identical' if same else 'DRIFT    '}  pinned/ast.json.gz  (front end on {minirust})")
    if ast is None:
        raise SystemExit("regen: no pinned/ast.json.gz; run `regen.py write --from-source` first")

    with tempfile.TemporaryDirectory(prefix="specr-regen-") as tmp:
        produced = regenerate(root, ast, records, Path(tmp))
    manifest = manifest_for(root, ast, records, produced)

    if a.mode == "write":
        if a.from_source:
            pinned_ast_path.write_bytes(gz_bytes(ast))
        for f, data in produced.items():
            (root / f).write_bytes(data)
        (root / "generated/MANIFEST.json").write_text(json.dumps(manifest, indent=1, sort_keys=True) + "\n")
        print(f"regen: wrote {len(produced)} outputs and generated/MANIFEST.json")
        return 0

    recorded_path = root / "generated/MANIFEST.json"
    recorded = json.loads(recorded_path.read_text()) if recorded_path.exists() else {}
    for f in OUTPUTS:
        path = root / f
        same = path.exists() and path.read_bytes() == produced[f]
        drift |= not same
        lines.append(f"{'identical' if same else 'DRIFT    '}  {f}")
    for section in ("pinned", "translator", "outputs"):
        want = recorded.get(section)
        same = want == manifest[section]
        drift |= not same
        lines.append(f"{'identical' if same else 'DRIFT    '}  generated/MANIFEST.json [{section}]")
    expected = set(OUTPUTS) | {"generated/MANIFEST.json"}
    for p in sorted((root / "generated").rglob("*")):
        rel = str(p.relative_to(root))
        if p.is_file() and rel not in expected:
            drift = True
            lines.append(f"DRIFT      {rel}  (not an output of this translator)")
    copies = fixture_lines(root, a.fixture.resolve())
    drift |= any(line.startswith("DRIFT") for line in copies)
    lines.extend(copies)
    print("\n".join(lines))
    print("regen: byte-identical" if not drift else "regen: DRIFT (run `regen.py write` and review the diff)")
    bad_check = False
    if a.clean is not None:
        bad_check = not clean_check(root, a.clean, a.clean_timeout)
    return 1 if drift or bad_check else 0


def fixture_lines(root: Path, fixture: Path) -> list[str]:
    """One line per file Clean's TrustSem fixture copies: identical, DRIFT, or (no copy at
    all yet) PENDING."""
    present = [name for name, _ in FIXTURE_COPIES if (fixture / name).is_file()]
    if not present:
        return [f"PENDING    clean fixture {name}  (no copy in {fixture})" for name, _ in FIXTURE_COPIES]
    out = []
    for name, ours in FIXTURE_COPIES:
        theirs = fixture / name
        same = theirs.is_file() and theirs.read_bytes() == (root / ours).read_bytes()
        out.append(f"{'identical' if same else 'DRIFT    '}  clean fixture {name}  (= {ours})")
    return out


def clean_check(root: Path, clean: Path, timeout: float = CLEAN_TIMEOUT) -> bool:
    """`clean check --json` of the prelude, the committed slice and conformance theorems."""
    index = json.loads((root / "generated/conformance_index.json").read_text())
    with tempfile.TemporaryDirectory(prefix="specr-check-") as tmp:
        probe = Path(tmp) / "probe.lean"
        probe.write_bytes((root / "SpecrPrelude.lean").read_bytes()
                          + (root / "PreludeVectors.lean").read_bytes()
                          + (root / "generated/MiniRustSlice.lean").read_bytes()
                          + (root / "SliceVectors.lean").read_bytes()
                          + gzip.decompress((root / "generated/conformance.lean.gz").read_bytes()))
        try:
            proc = subprocess.run([str(clean), "check", "--json", str(probe)], stdout=subprocess.PIPE,
                                  stderr=subprocess.PIPE, text=True, check=False, timeout=timeout)
        except subprocess.TimeoutExpired:
            print(f"clean check: still running after {timeout:g} s, killed -> FAILED")
            return False
    try:
        rep = json.loads(proc.stdout)
    except json.JSONDecodeError:
        sys.stderr.write(proc.stderr[-4000:])
        print("clean check: no JSON report")
        return False
    failed = {e.split(":")[0].strip() for e in rep.get("errors", [])}
    theorems = [t["theorem"] for t in index["theorems"]]
    ts = rep.get("trust_summary") or {}
    missing = [k for k in ("sorry_axioms", "sorry_terms_minted", "kernel_check_failures") if k not in ts]
    if missing:
        print(f"clean check: {clean} reports no trust_summary.{', '.join(missing)}; it is older than "
              "this check needs (Clean 01189665c, 2026-09-28, or later) -> FAILED")
        return False
    ok = (rep.get("failed_count") == 0 and not failed and ts.get("sorry_axioms") == 0
          and ts.get("sorry_terms_minted") == 0 and ts.get("kernel_check_failures") == 0
          and not rep.get("assumptions") and not rep.get("diverged"))
    tests = {t["test"] for t in index["theorems"]}
    print(f"clean check: {rep.get('success_count')}/{rep.get('decl_count')} declarations accepted, "
          f"{len([t for t in theorems if t not in failed])}/{len(theorems)} conformance theorems "
          f"({len(tests)} minitests), sorry {ts.get('sorry_axioms')}/{ts.get('sorry_terms_minted')}, "
          f"kernel failures {ts.get('kernel_check_failures')}, assumptions {len(rep.get('assumptions') or [])}"
          f" -> {'ok' if ok else 'FAILED'}")
    return ok


if __name__ == "__main__":
    sys.exit(main())
