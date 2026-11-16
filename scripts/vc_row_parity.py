#!/usr/bin/env python3
"""VC row parity: does a change move any row trust-vcgen emits for the in-tree fixtures?

Author: Andrew Yates. Copyright 2026 Andrew Yates. License: Apache-2.0 OR MIT.

The T3 landings L4 and L5 change how the per-function VC context is built and
stored, and claim the ROWS do not move (design
docs/design/2026-10-08-t3-memory-proportional-reconstruction.md §12). This
script is that claim's instrument (T3 C01; plan S16, which replaced an
`#[ignore]` test nobody ran). It builds trust-vcgen's row-parity probe
(crates/trust-vcgen/examples/vc_row_parity_probe.rs) in a PARENT tree and in a
CANDIDATE tree, runs both over the same fixture roots (by default the
candidate's crates/trust-vcgen/tests, every `*.json` under it), and diffs the
two outputs. Each output line is

    <fixture> <row index> <sha256 of the row's canonical JSON>

in the exact-VC payload's encoding (see the probe's header), or
`<fixture> - unparsed|panicked|rows=0`. Equal outputs mean every fixture
produced the same rows, in the same order, byte for byte.

Trees:
  --parent REV / --candidate REV   a commit, checked out into a temporary
                                   detached worktree (removed afterwards
                                   unless --keep). Its first-party/* sources
                                   are linked from this checkout when the
                                   pins agree, or extracted from this
                                   checkout's submodule repository when it
                                   has the pinned commit; otherwise the run
                                   refuses and names the submodule.
  --parent-tree DIR / --candidate-tree DIR
                                   an existing checkout, used in place (its
                                   first-party/* must already be populated).
The candidate defaults to this checkout's working tree. A temporary worktree
whose commit predates the probe gets this checkout's probe copied in. The
probe's source must be byte-identical in the two trees (a probe change is not
a vcgen change); --allow-probe-drift accepts a difference and says so.

  --diff A B                       compare two saved outputs only.

Builds use `targo --unverified run --locked` against each tree's own
Cargo.toml and lock, with one shared CARGO_TARGET_DIR (--target-dir).

Exit 0 when the outputs are identical, 1 when they differ, 2 on a usage error,
3 when a side could not be built or run (COULD NOT RUN).
"""

from __future__ import annotations

import argparse
import difflib
import os
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
PROBE_REL = Path("crates/trust-vcgen/examples/vc_row_parity_probe.rs")
FIXTURES_REL = Path("crates/trust-vcgen/tests")
SHOWN_DIFF_LINES = 80


class CouldNotRun(Exception):
    """A side could not be prepared, built or run (exit 3)."""


def git(*args: str, cwd: Path = REPO_ROOT, check: bool = True) -> str:
    proc = subprocess.run(["git", *args], cwd=cwd, capture_output=True, text=True, check=False)
    if check and proc.returncode != 0:
        raise CouldNotRun(f"git {' '.join(args)}: {proc.stderr.strip()}")
    return proc.stdout


def gitlinks(rev: str) -> dict[str, str]:
    """`first-party/<name>` -> pinned commit, at `rev`."""
    out = git("ls-tree", rev, "first-party/")
    links = {}
    for line in out.splitlines():
        meta, _, path = line.partition("\t")
        mode, kind, sha = meta.split()
        if kind == "commit":
            links[path] = sha
    return links


def populate_first_party(tree: Path, rev: str) -> list[str]:
    """Give a temporary worktree the first-party sources its pins name."""
    here = gitlinks("HEAD")
    notes = []
    for path, sha in sorted(gitlinks(rev).items()):
        dest = tree / path
        src = REPO_ROOT / path
        if here.get(path) == sha and src.is_dir() and any(src.iterdir()):
            if dest.exists() and not any(dest.iterdir()):
                dest.rmdir()
            dest.symlink_to(src, target_is_directory=True)
            notes.append(f"{path}: linked (pin {sha[:12]} = this checkout's)")
            continue
        if (src / ".git").exists() and subprocess.run(
            ["git", "-C", str(src), "cat-file", "-e", f"{sha}^{{commit}}"],
            capture_output=True, check=False,
        ).returncode == 0:
            dest.mkdir(parents=True, exist_ok=True)
            archive = subprocess.Popen(["git", "-C", str(src), "archive", sha],
                                       stdout=subprocess.PIPE)
            untar = subprocess.run(["tar", "-x", "-C", str(dest)], stdin=archive.stdout,
                                   check=False)
            if archive.wait() != 0 or untar.returncode != 0:
                raise CouldNotRun(f"{path}: extracting {sha} failed")
            notes.append(f"{path}: extracted {sha[:12]} from this checkout's submodule")
            continue
        raise CouldNotRun(
            f"{path} is pinned at {sha} at {rev}, which this checkout neither has checked "
            f"out nor holds; populate a checkout at {rev} and pass it as a --*-tree"
        )
    return notes


class Side:
    def __init__(self, label: str, tree: Path, temp: bool, notes: list[str]):
        self.label, self.tree, self.temp, self.notes = label, tree, temp, notes


def prepare(label: str, rev: str | None, tree: str | None, scratch: Path) -> Side:
    if tree is not None:
        path = Path(tree).resolve()
        if not (path / "crates/trust-types/Cargo.toml").is_file():
            raise CouldNotRun(f"{label}: {path} is not a trust checkout (no crates/trust-types/Cargo.toml)")
        if not (path / PROBE_REL).is_file():
            raise CouldNotRun(f"{label}: {path} has no {PROBE_REL}; pass its commit as a rev")
        return Side(label, path, False, [f"tree {path}, in place"])
    assert rev is not None
    sha = git("rev-parse", "--verify", f"{rev}^{{commit}}").strip()
    path = scratch / f"{label}-{sha[:12]}"
    git("worktree", "add", "--detach", str(path), sha)
    notes = [f"{rev} = {sha}, temporary worktree {path}"]
    try:
        notes += populate_first_party(path, sha)
        if not (path / PROBE_REL).is_file():
            shutil.copyfile(REPO_ROOT / PROBE_REL, path / PROBE_REL)
            notes.append(f"{PROBE_REL} absent at {sha[:12]}: this checkout's copied in")
    except Exception:
        remove_worktree(path)
        raise
    return Side(label, path, True, notes)


def remove_worktree(path: Path) -> None:
    subprocess.run(["git", "worktree", "remove", "--force", str(path)], cwd=REPO_ROOT,
                   capture_output=True, check=False)


def run_probe(side: Side, targo: str, target_dir: Path, roots: list[Path], out: Path) -> None:
    cmd = [
        targo, "--unverified", "run", "--quiet", "--locked",
        "--manifest-path", str(side.tree / "Cargo.toml"),
        "-p", "trust-vcgen", "--example", "vc_row_parity_probe", "--",
        *map(str, roots),
    ]
    env = dict(os.environ, CARGO_TARGET_DIR=str(target_dir))
    with out.open("w", encoding="utf-8") as sink:
        proc = subprocess.run(cmd, stdout=sink, stderr=subprocess.PIPE, text=True, env=env,
                              check=False)
    tail = "\n".join(proc.stderr.strip().splitlines()[-15:])
    if proc.returncode != 0:
        raise CouldNotRun(f"{side.label}: probe exited {proc.returncode}:\n{tail}")
    side.notes.append(tail.splitlines()[-1] if tail else "probe printed no summary")


def compare(a: Path, b: Path, label_a: str, label_b: str) -> int:
    left = a.read_text(encoding="utf-8").splitlines()
    right = b.read_text(encoding="utf-8").splitlines()
    print(f"{label_a}: {len(left)} line(s) ({a})")
    print(f"{label_b}: {len(right)} line(s) ({b})")
    if left == right:
        print("ROW PARITY: identical")
        return 0
    diff = list(difflib.unified_diff(left, right, label_a, label_b, lineterm="", n=0))
    changed = sum(1 for d in diff if d[:1] in "+-" and d[:3] not in ("+++", "---"))
    print(f"ROW PARITY: DIFFERS ({changed} line(s) changed)")
    for line in diff[:SHOWN_DIFF_LINES]:
        print(line)
    if len(diff) > SHOWN_DIFF_LINES:
        print(f"... {len(diff) - SHOWN_DIFF_LINES} more diff line(s); compare the files")
    return 1


def main(argv: list[str]) -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--parent", help="the parent commit (a temporary worktree)")
    ap.add_argument("--parent-tree", help="the parent as an existing checkout")
    ap.add_argument("--candidate", help="the candidate commit (a temporary worktree)")
    ap.add_argument("--candidate-tree", help="the candidate checkout (default: this one)")
    ap.add_argument("--fixtures", action="append", default=[],
                    help="a fixture root (repeatable; default the candidate's "
                         "crates/trust-vcgen/tests)")
    ap.add_argument("--targo", default=os.environ.get("TARGO", "targo"))
    ap.add_argument("--target-dir", help="shared CARGO_TARGET_DIR (default <out-dir>/target)")
    ap.add_argument("--out-dir", help="where the outputs and temporary worktrees go")
    ap.add_argument("--allow-probe-drift", action="store_true")
    ap.add_argument("--keep", action="store_true", help="keep the temporary worktrees")
    ap.add_argument("--diff", nargs=2, metavar=("A", "B"), help="compare two saved outputs")
    args = ap.parse_args(argv)

    if args.diff:
        a, b = map(Path, args.diff)
        for p in (a, b):
            if not p.is_file():
                ap.error(f"--diff: no such file: {p}")
        return compare(a, b, str(a), str(b))
    if (args.parent is None) == (args.parent_tree is None):
        ap.error("name the parent once: --parent REV or --parent-tree DIR")
    if args.candidate is not None and args.candidate_tree is not None:
        ap.error("name the candidate once: --candidate REV or --candidate-tree DIR")
    if args.candidate is None and args.candidate_tree is None:
        args.candidate_tree = str(REPO_ROOT)

    out_dir = Path(args.out_dir or tempfile.mkdtemp(prefix="vc-row-parity-")).resolve()
    out_dir.mkdir(parents=True, exist_ok=True)
    target_dir = Path(args.target_dir).resolve() if args.target_dir else out_dir / "target"
    sides: list[Side] = []
    try:
        parent = prepare("parent", args.parent, args.parent_tree, out_dir)
        sides.append(parent)
        candidate = prepare("candidate", args.candidate, args.candidate_tree, out_dir)
        sides.append(candidate)
        probes = [(s.tree / PROBE_REL).read_bytes() for s in sides]
        if probes[0] != probes[1]:
            if not args.allow_probe_drift:
                raise CouldNotRun(
                    f"{PROBE_REL} differs between the trees; a probe change is not a vcgen "
                    "change (--allow-probe-drift to compare anyway)"
                )
            print(f"NOTE: {PROBE_REL} differs between the trees (--allow-probe-drift)")
        roots = [Path(r).resolve() for r in args.fixtures] or [candidate.tree / FIXTURES_REL]
        outputs = []
        for side in sides:
            out = out_dir / f"{side.label}.rows"
            run_probe(side, args.targo, target_dir, roots, out)
            outputs.append(out)
        for side in sides:
            for note in side.notes:
                print(f"{side.label}: {note}")
        print(f"fixture roots: {', '.join(map(str, roots))}")
        return compare(outputs[0], outputs[1], "parent", "candidate")
    except CouldNotRun as e:
        print(f"COULD NOT RUN: {e}", file=sys.stderr)
        return 3
    finally:
        if not args.keep:
            for side in sides:
                if side.temp:
                    remove_worktree(side.tree)


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
