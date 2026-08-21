#!/usr/bin/env python3
"""Retrofit `scripts/lib/measure_stamp.sh` into lane measurement runners.

Author: Andrew Yates | Copyright 2026 Andrew Yates | License: Apache-2.0 OR MIT

WHY
---
Measured 2026-08-20 by `check_measurement_provenance.sh --audit-runners`: 86
lane measurement runners under `scratchpad/`, 31 of which record a blob or
worktree dirt before reporting and 55 of which do not. The RCA that found this
(reports/revert-silence-rca-2026-08-20.md) named adoption as the whole problem:
the fix is two lines, one peer had already invented it, and it still was not in
the other 55 runners.

So the retrofit is mechanical, and this is the machine.

WHAT IT INSERTS
---------------
One line, immediately before the first measurement command, at that line's own
indentation — which puts it INSIDE a `{ ... } > "$log" 2>&1` block when the
runner has one, and in stdout position when it does not. Both land the stamp in
the artifact the runner publishes.

    bash /abs/path/to/scripts/lib/measure_stamp.sh <paths under test>

The paths are derived from the runner's own `cargo ... -p <pkg>` selectors,
mapped to that package's source directory, which `measure_stamp.sh` stamps as a
git tree. A runner whose measured paths cannot be derived is REPORTED, NEVER
GUESSED — a stamp naming the wrong file is worse than no stamp, because it reads
as evidence.

SAFETY, and why each rule is here
---------------------------------
* ATOMIC REPLACE. The new text is written to a temp file and `os.replace`d, so a
  runner that is mid-execution keeps its file descriptor on the old inode. Bash
  and zsh read a script incrementally by byte offset; editing one in place while
  it runs can make the shell resume at a shifted offset and execute a fragment.
  This is not theoretical — two lane runners were executing when this was
  written.
* RUNNING RUNNERS ARE SKIPPED ANYWAY. Belt and braces: `ps` is consulted and any
  runner that appears in a live command line is left alone and reported.
* IDEMPOTENT. A runner that already mentions `measure_stamp` is skipped.
* DRY RUN BY DEFAULT. `--apply` is required to write anything.
* It never touches a file outside the scan root, and it never touches a file
  tracked by git.

Usage:
    scripts/lib/retrofit_measure_stamp.py [--root scratchpad] [--apply]
"""

from __future__ import annotations

import argparse
import os
import re
import subprocess
import sys
import tempfile
from pathlib import Path

# Resolved from the SCAN ROOT, not from this file: the runners being retrofitted
# live in the shared checkout, and the inserted line must name that checkout's
# helper. A lane worktree is deleted when its lane ends; a path into one would
# turn every retrofitted runner into a broken one the day after.
REPO_ROOT = Path("/")
HELPER = Path("/")

# A runner MEASURES when it runs one of these.
# Kept IDENTICAL to `check_measurement_provenance.sh --audit-runners`, so the
# adoption counter and this retrofit are talking about the same population.
MEASURES = re.compile(
    r"cargo[^\n]*(test|build|rustc)|x\.py|test result|--lib|\.o\s|objdump|nm -|MUTATION|scorecard",
)
# It already names its tree when it does any of these.
STAMPED = re.compile(r"measure_stamp|hash-object|status --porcelain")
# The line the stamp goes in front of.
# The line the stamp goes in front of. `$CARGO` / `"$CARGO"` counts: most lane
# runners invoke the stage0 cargo through a variable, and matching only the
# literal word `cargo` silently classified 14 real build runners as "runs no
# cargo line" on the first pass.
MEASURE_CMD = re.compile(
    r"(?:cargo|\$\{?CARGO\}?)[^\n]*\b(?:test|build|rustc)\b|\bx\.py\b"
)
# `-p <pkg>` / `--package <pkg>` selectors.
PKG = re.compile(r"(?:-p|--package)[= ]+([A-Za-z0-9_-]+)")
MANIFEST = re.compile(r"--manifest-path[= ]+\"?\$?[A-Za-z0-9_{}/$.-]*?([a-z-]+)/Cargo\.toml")


def package_dirs(text: str) -> list[str]:
    """Repo-relative source dirs naming the tree this runner measures.

    Two derivations, in order of specificity. Neither ever guesses: a package
    directory is emitted only when it EXISTS on disk, because a stamp naming
    the wrong file is worse than no stamp — it reads as evidence.
    """
    out: list[str] = []

    # 1. `-p <pkg>` — the runner named its subject. `first-party/*` is included
    #    because several lanes measure the vendored clean/ay crates, which is
    #    where the first pass of this retrofit lost most of its candidates.
    for pkg in dict.fromkeys(PKG.findall(text)):
        cands = [
            f"crates/{pkg}/src",
            f"compiler/{pkg}/src",
            f"src/tools/{pkg}/src",
        ]
        cands += [
            f"first-party/{fp.name}/crates/{pkg}/src"
            for fp in sorted((REPO_ROOT / "first-party").glob("*"))
            if fp.is_dir()
        ]
        cands += [
            f"first-party/{fp.name}/{pkg}/src"
            for fp in sorted((REPO_ROOT / "first-party").glob("*"))
            if fp.is_dir()
        ]
        if pkg.startswith("targo"):
            cands.append("targo-trust/src")
        for cand in cands:
            if (REPO_ROOT / cand).is_dir():
                out.append(cand)
                break
    if out:
        return out

    # 2. No package selector: a WHOLE-COMPILER build or dump. Its subject is the
    #    compiler source itself, and `measure_stamp` reduces a directory to one
    #    tree hash, so naming the whole thing costs one line and one object id.
    #    This is the honest answer for a driver build: the binary is a function
    #    of exactly these trees.
    for m in dict.fromkeys(MANIFEST.findall(text)):
        if m == "rustc" or m == "compiler":
            for d in ("compiler", "crates"):
                if (REPO_ROOT / d).is_dir() and d not in out:
                    out.append(d)
        elif (REPO_ROOT / "crates").is_dir() and "crates" not in out:
            out.append("crates")
    return out


def running_scripts() -> set[str]:
    try:
        ps = subprocess.run(
            ["ps", "-Ao", "command"], capture_output=True, text=True, timeout=20
        ).stdout
    except Exception:
        # If we cannot tell, assume everything is running. Failing closed here
        # costs a skipped retrofit; failing open costs a corrupted live run.
        return {"*"}
    return {tok for tok in re.findall(r"\S+\.sh", ps)}


def tracked(path: Path) -> bool:
    r = subprocess.run(
        ["git", "-C", str(REPO_ROOT), "ls-files", "--error-unmatch", str(path)],
        capture_output=True,
        text=True,
    )
    return r.returncode == 0


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--root", default="scratchpad")
    ap.add_argument("--apply", action="store_true")
    args = ap.parse_args()

    global REPO_ROOT, HELPER
    root = Path(args.root)
    root = (root if root.is_absolute() else Path.cwd() / root).resolve()
    if not root.is_dir():
        print(f"retrofit: no such directory: {root}", file=sys.stderr)
        return 2
    top = subprocess.run(
        ["git", "-C", str(root), "rev-parse", "--show-toplevel"],
        capture_output=True, text=True,
    )
    if top.returncode != 0:
        print(f"retrofit: {root} is not inside a git worktree", file=sys.stderr)
        return 2
    REPO_ROOT = Path(top.stdout.strip())
    HELPER = REPO_ROOT / "scripts" / "lib" / "measure_stamp.sh"
    print(f"retrofit: scan root {root}")
    print(f"retrofit: helper     {HELPER}")

    wt = subprocess.run(
        ["git", "-C", str(REPO_ROOT), "worktree", "list", "--porcelain"],
        capture_output=True, text=True,
    ).stdout
    wt_roots = [
        Path(l[len("worktree "):]) for l in wt.splitlines() if l.startswith("worktree ")
    ]
    live = running_scripts()

    converted, skipped_running, skipped_nopaths, already, failed = [], [], [], [], []
    skipped_tracked, skipped_nocmd = [], []

    candidates = sorted(
        p for depth in (1, 2) for p in root.glob("/".join(["*"] * depth) + ".sh")
    )
    for p in candidates:
        if any(p.is_relative_to(w) and w != REPO_ROOT for w in wt_roots):
            continue
        try:
            text = p.read_text(encoding="utf-8", errors="replace")
        except OSError:
            continue
        if not MEASURES.search(text):
            continue
        if STAMPED.search(text):
            already.append(p)
            continue
        if tracked(p):
            skipped_tracked.append(p)
            continue
        if "*" in live or any(str(p) in l or p.name == Path(l).name for l in live):
            skipped_running.append(p)
            continue

        lines = text.splitlines(keepends=True)
        idx = next(
            (i for i, l in enumerate(lines)
             if MEASURE_CMD.search(l) and not l.lstrip().startswith("#")),
            None,
        )
        if idx is None:
            skipped_nocmd.append(p)
            continue

        dirs = package_dirs(text)
        if not dirs:
            skipped_nopaths.append(p)
            continue

        indent = re.match(r"[ \t]*", lines[idx]).group(0)
        # RESOLVE THE HELPER AT RUN TIME, from the worktree the runner is
        # measuring, with the shared checkout as a fallback. A single hardcoded
        # absolute path is wrong and was measured to be wrong: the shared
        # checkout sits at a detached sha that need not contain the helper, and
        # 43 runners would each have printed "No such file or directory" into
        # the log they publish. When neither path resolves, the runner emits an
        # explicit UNSTAMPABLE block — which `--log` REJECTS — because a missing
        # stamp must never be mistaken for a clean one.
        stamp = (
            f"{indent}# provenance: name the tree this measurement is of "
            f"(reports/reporting-integrity-2026-08-20.md)\n"
            f'{indent}_ms="$(git rev-parse --show-toplevel 2>/dev/null)/scripts/lib/measure_stamp.sh"\n'
            f'{indent}[ -f "$_ms" ] || _ms="{HELPER}"\n'
            f'{indent}if [ -f "$_ms" ]; then bash "$_ms" {" ".join(dirs)}; '
            f'else echo "=== MEASURE-STAMP v1 UNSTAMPABLE"; '
            f'echo "--- reason   measure_stamp.sh not found; this log names no tree"; '
            f'echo "=== END MEASURE-STAMP v1"; fi\n'
        )
        new = "".join(lines[:idx]) + stamp + "".join(lines[idx:])

        if not args.apply:
            converted.append((p, dirs, idx + 1))
            continue
        try:
            st = p.stat()
            fd, tmp = tempfile.mkstemp(dir=str(p.parent), prefix=".retrofit.")
            with os.fdopen(fd, "w", encoding="utf-8") as fh:
                fh.write(new)
            os.chmod(tmp, st.st_mode)
            os.replace(tmp, p)  # ATOMIC: a live shell keeps the old inode.
            converted.append((p, dirs, idx + 1))
        except OSError as exc:
            failed.append((p, str(exc)))

    mode = "APPLIED" if args.apply else "DRY RUN (pass --apply to write)"
    print(f"=== retrofit measure_stamp — {mode} ===")
    print(f"  already stamped        : {len(already)}")
    print(f"  converted              : {len(converted)}")
    print(f"  skipped, RUNNING now   : {len(skipped_running)}")
    print(f"  skipped, paths unknown : {len(skipped_nopaths)}")
    print(f"  skipped, no cargo cmd  : {len(skipped_nocmd)}")
    print(f"  skipped, git-tracked   : {len(skipped_tracked)}")
    print(f"  failed                 : {len(failed)}")
    total = (len(already) + len(converted) + len(skipped_running)
             + len(skipped_nopaths) + len(skipped_nocmd) + len(skipped_tracked)
             + len(failed))
    print(f"  ---------------------- : {total} runners, every one accounted for")
    def rel(q: Path) -> str:
        try:
            return str(q.relative_to(REPO_ROOT))
        except ValueError:
            return str(q)

    for p, dirs, line in converted:
        print(f"    + {rel(p)}  @line {line}  stamps: {' '.join(dirs)}")
    for p in skipped_running:
        print(f"    ~ {rel(p)}  EXECUTING NOW — not touched")
    for p in skipped_nopaths:
        print(f"    ? {rel(p)}  no derivable subject (no -p selector, no recognised manifest)")
    for p in skipped_nocmd:
        print(f"    ? {rel(p)}  matches the measurement vocabulary but runs no cargo/x.py line")
    for p in skipped_tracked:
        print(f"    ~ {rel(p)}  git-tracked; not a lane scratch runner")
    for p, err in failed:
        print(f"    x {rel(p)}  {err}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
