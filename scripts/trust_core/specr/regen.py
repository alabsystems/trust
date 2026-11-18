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
                    [--repo DIR] [--sibling-git NAME=DIR ...] [--require-siblings]
  regen.py write    [--root DIR] [--from-source [--frontend BIN] [--minirust DIR]]
  regen.py copies   [--root DIR] [--clean DIR] [--trust-ir DIR]

check (the default) regenerates every output into a scratch directory and compares it with
the committed bytes, compares every pinned input and translator file with its manifest
digest, and fails on any file in generated/ that is not an output or the manifest.

It also compares the byte copies the sibling repositories hold (SIBLING_COPIES) AT THE
REVISIONS THIS REPOSITORY PINS: the gitlinks `first-party/clean` and `first-party/trust-ir` in
the HEAD commit of the Trust repository holding --root (--repo names another). Clean's TrustSem
fixture (crates/clean-olean/tests/fixtures/lean/v4.30.0-rc2/trust_sem/) holds SpecrPrelude.lean
and generated/MiniRustSlice.lean, where Clean proves core_wf, run_sound, run_ub and run_adequate
over this SOut and checks the slice through the reference entry; Clean's semr fixture and
trust-ir's lean/semr/ each hold MiniRust.lean, the wrapper `noncomputable section` + prelude +
slice + `end`. Each blob is read with `git cat-file blob <gitlink>:<path>` from the object store
--sibling-git NAME=DIR names, or else from first-party/NAME when that is checked out. A copy
that differs, or a pinned revision without the file, is DRIFT; a revision the object store does
not hold (or no store, or no Trust repository) is NOT RUN, never identical. It prints one line
per file and exits 0 when all are identical, 1 on any drift or failure, and 2 when a sibling
comparison is NOT RUN under --require-siblings (without it, NOT RUN is printed and exits 0).

copies writes those byte copies into the sibling working trees named by --clean DIR (a Clean
checkout) and --trust-ir DIR (a trust-ir checkout), from this directory's committed files; it
refuses when a source file's digest differs from generated/MANIFEST.json (run `write` first).
The sibling commits that hold them are then pinned by moving the gitlinks.
--from-source also re-runs the front end (the K8 probe's syn front end, unchanged in v2:
reports/2026-09-17-phase0-k8-specr/translator/frontend, built with
`targo --unverified build --release`) on the MiniRust checkout (the trust-core source
cache by default, common.sources_root()/minirust, which must hold the pin) and compares the
AST with the pinned one. write regenerates the committed outputs and the manifest (and,
with --from-source, the pinned AST) in place.

--clean BIN (check only) also kernel-checks SpecrPrelude.lean, PreludeVectors.lean, the slice,
SliceVectors.lean and the conformance theorems with `BIN check --json` and requires 0 failed
declarations, 0 `sorry` axioms and 0 `sorry` terms minted, 0 kernel-check failures, no
assumption, and every conformance theorem accepted: present in the report's
`timing.per_declaration` and absent from its errors (a theorem the report never mentions is not
accepted). BIN must report
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
# The byte copies the sibling repositories hold: (sibling, its path, what it holds). `wrapper` is
# WRAPPER_HEAD + prelude + slice + WRAPPER_TAIL, the module Clean's rm1_trust_sem and semr_reference
# compile and trust-ir's lean/semr/ builds on.
CLEAN_FIXTURES = "crates/clean-olean/tests/fixtures/lean/v4.30.0-rc2"
SIBLING_COPIES = (
    ("clean", f"{CLEAN_FIXTURES}/trust_sem/SpecrPrelude.lean", "SpecrPrelude.lean"),
    ("clean", f"{CLEAN_FIXTURES}/trust_sem/MiniRustSlice.lean", "generated/MiniRustSlice.lean"),
    ("clean", f"{CLEAN_FIXTURES}/semr/MiniRust.lean", "wrapper"),
    ("trust-ir", "lean/semr/MiniRust.lean", "wrapper"),
)
SIBLINGS = ("clean", "trust-ir")
WRAPPER_HEAD, WRAPPER_TAIL = b"noncomputable section\n", b"\nend\n"
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
    ap.add_argument("mode", nargs="?", default="check", choices=("check", "write", "copies"))
    ap.add_argument("--root", type=Path, default=HERE)
    ap.add_argument("--from-source", action="store_true")
    ap.add_argument("--frontend", type=Path)
    ap.add_argument("--minirust", type=Path)
    ap.add_argument("--clean", type=Path,
                    help="check: the clean binary for --clean's kernel check; copies: a Clean checkout")
    ap.add_argument("--trust-ir", type=Path, help="copies: a trust-ir checkout")
    ap.add_argument("--clean-timeout", type=float, default=CLEAN_TIMEOUT)
    ap.add_argument("--repo", type=Path,
                    help="the Trust repository whose HEAD gitlinks pin the siblings (default: the one holding --root)")
    ap.add_argument("--sibling-git", action="append", default=[], metavar="NAME=DIR",
                    help="read sibling NAME's blobs from the object store of DIR (default: first-party/NAME)")
    ap.add_argument("--require-siblings", action="store_true",
                    help="a sibling comparison that is NOT RUN exits 2")
    a = ap.parse_args(argv)
    root = a.root.resolve()
    stores: dict[str, Path] = {}
    for spec in a.sibling_git:
        name, sep, d = spec.partition("=")
        if not sep or name not in SIBLINGS or not d:
            raise SystemExit(f"regen: --sibling-git takes NAME=DIR with NAME one of {', '.join(SIBLINGS)}, not {spec!r}")
        if name in stores:
            raise SystemExit(f"regen: --sibling-git {name} given twice")
        stores[name] = Path(d).resolve()
    if a.mode == "copies":
        return write_copies(root, {"clean": a.clean, "trust-ir": a.trust_ir})

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
    copies = sibling_lines(root, a.repo.resolve() if a.repo else trust_repo_of(root), stores)
    drift |= any(line.startswith("DRIFT") for line in copies)
    not_run = any(line.startswith("NOT RUN") for line in copies)
    lines.extend(copies)
    print("\n".join(lines))
    print("regen: byte-identical" if not drift else "regen: DRIFT (run `regen.py write` and review the diff)")
    bad_check = False
    if a.clean is not None:
        bad_check = not clean_check(root, a.clean, a.clean_timeout)
    if drift or bad_check:
        return 1
    if not_run and a.require_siblings:
        print("regen: a sibling comparison was NOT RUN under --require-siblings")
        return 2
    return 0


def git(cwd: Path, *args: str) -> subprocess.CompletedProcess:
    env = {k: v for k, v in os.environ.items() if not k.startswith("GIT_")}
    return subprocess.run(["git", "-C", str(cwd), *args], stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                          check=False, env=env)


def trust_repo_of(root: Path) -> Path | None:
    """The work tree of the git repository holding `root`, or None."""
    proc = git(root, "rev-parse", "--show-toplevel")
    return Path(proc.stdout.decode().strip()).resolve() if proc.returncode == 0 else None


def is_own_work_tree(d: Path) -> bool:
    """`d` is the top of its own git work tree (an initialised submodule), not an empty
    directory inside the parent repository, whose objects are not the sibling's."""
    if not d.is_dir():
        return False
    top = trust_repo_of(d)
    return top is not None and top == d.resolve()


def wrapper_bytes(root: Path) -> bytes:
    return (WRAPPER_HEAD + (root / "SpecrPrelude.lean").read_bytes()
            + (root / "generated/MiniRustSlice.lean").read_bytes() + WRAPPER_TAIL)


def copy_source(root: Path, what: str) -> tuple[bytes, str]:
    """The bytes a sibling copy must equal, and how the line names them."""
    if what == "wrapper":
        return wrapper_bytes(root), "noncomputable section + SpecrPrelude.lean + generated/MiniRustSlice.lean + end"
    return (root / what).read_bytes(), what


def sibling_lines(root: Path, repo: Path | None, stores: dict[str, Path]) -> list[str]:
    """One line per sibling copy, compared at the sibling revision HEAD's gitlink pins:
    identical, DRIFT (different bytes, or no such file at that revision), or NOT RUN (that
    revision cannot be read here)."""
    out = []
    for name in SIBLINGS:
        rows = [(path, what) for sib, path, what in SIBLING_COPIES if sib == name]
        rev, why = None, None
        if repo is None:
            why = f"{root} is not in a git repository, so no gitlink pins {name}"
        else:
            tree = git(repo, "ls-tree", "HEAD", f"first-party/{name}")
            fields = tree.stdout.decode().split()
            if tree.returncode != 0:
                why = f"{repo} has no HEAD commit to read the gitlink first-party/{name} from"
            elif len(fields) < 3 or fields[0] != "160000" or fields[1] != "commit":
                for path, what in rows:
                    out.append(f"DRIFT      {name}@(none) {path}  (HEAD of {repo} has no gitlink first-party/{name})")
                continue
            else:
                rev = fields[2]
        store = None
        if rev is not None:
            if name in stores:
                store = stores[name]
                if git(store, "rev-parse", "--git-dir").returncode != 0:
                    raise SystemExit(f"regen: --sibling-git {name}={store}: not a git repository")
            elif is_own_work_tree(repo / "first-party" / name):
                store = repo / "first-party" / name
            else:
                why = f"first-party/{name} is not checked out; pass --sibling-git {name}=DIR"
        if store is not None and git(store, "cat-file", "-e", f"{rev}^{{commit}}").returncode != 0:
            why = f"{store} does not hold commit {rev}"
            store = None
        for path, what in rows:
            ours, label = copy_source(root, what)
            if store is None:
                at = f"{name}@{rev[:10]}" if rev else f"{name}@?"
                out.append(f"NOT RUN    {at} {path}  ({why})")
                continue
            blob = git(store, "cat-file", "blob", f"{rev}:{path}")
            if blob.returncode != 0:
                out.append(f"DRIFT      {name}@{rev[:10]} {path}  (no such file at {rev})")
                continue
            same = blob.stdout == ours
            out.append(f"{'identical' if same else 'DRIFT    '}  {name}@{rev[:10]} {path}  (= {label})")
    return out


def write_copies(root: Path, dests: dict[str, Path | None]) -> int:
    """Write every SIBLING_COPIES file into the named sibling working trees."""
    if not any(dests.values()):
        raise SystemExit("regen: copies needs --clean DIR and/or --trust-ir DIR")
    recorded = json.loads((root / "generated/MANIFEST.json").read_text())
    for f, section in (("SpecrPrelude.lean", "translator"), ("generated/MiniRustSlice.lean", "outputs")):
        want = recorded.get(section, {}).get(f)
        if want != sha256((root / f).read_bytes()):
            raise SystemExit(f"regen: {f} differs from generated/MANIFEST.json [{section}]; run `regen.py write` "
                             "and review the diff before copying")
    for name, path, what in SIBLING_COPIES:
        d = dests.get(name)
        if d is None:
            continue
        dst = d.resolve() / path
        if not dst.parent.is_dir():
            raise SystemExit(f"regen: {dst.parent} does not exist: is {d} a {name} checkout?")
        data, label = copy_source(root, what)
        same = dst.is_file() and dst.read_bytes() == data
        if not same:
            dst.write_bytes(data)
        print(f"{'unchanged' if same else 'wrote    '}  {name} {path}  (= {label})")
    return 0


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
    # A theorem is accepted only when the report names it and records no error for it: a theorem
    # the report never mentions (elaboration dropped it, the probe lost it) is not accepted.
    present = {d.get("name") for d in ((rep.get("timing") or {}).get("per_declaration") or [])
               if isinstance(d, dict)}
    accepted = [t for t in theorems if t in present and t not in failed]
    missing = [t for t in theorems if t not in present]
    ok = (rep.get("failed_count") == 0 and not failed and ts.get("sorry_axioms") == 0
          and ts.get("sorry_terms_minted") == 0 and ts.get("kernel_check_failures") == 0
          and not rep.get("assumptions") and not rep.get("diverged") and len(accepted) == len(theorems))
    tests = {t["test"] for t in index["theorems"]}
    print(f"clean check: {rep.get('success_count')}/{rep.get('decl_count')} declarations accepted, "
          f"{len(accepted)}/{len(theorems)} conformance theorems "
          f"({len(tests)} minitests{f'; {len(missing)} absent from the report' if missing else ''}), "
          f"sorry {ts.get('sorry_axioms')}/{ts.get('sorry_terms_minted')}, "
          f"kernel failures {ts.get('kernel_check_failures')}, assumptions {len(rep.get('assumptions') or [])}"
          f" -> {'ok' if ok else 'FAILED'}")
    return ok


if __name__ == "__main__":
    sys.exit(main())
