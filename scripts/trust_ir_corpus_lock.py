#!/usr/bin/env python3
# trust_ir_corpus_lock.py --- pin the measured corpus by CONTENT, not by re-deriving it.
#
# Author: Andrew Yates. Copyright 2026 Andrew Yates. License: Apache-2.0 OR MIT.
#
# THE DEFECT THIS RETIRES
# -----------------------
# The producer scorecard chose its 2000-file corpus by `random.sample(eligible,
# 2000)` under a fixed seed. `random.sample` is a function of the population
# LENGTH, so the corpus was only stable while `len(eligible)` was. It was not:
#
#   * `scripts/trust_ir_producer_ui_pins.txt` exists solely to hold that length
#     fixed by hand, and its own header records the count creeping 8 -> 9 -> 13
#     -> 14 -> 15 -> 16, "lived in nobody's head";
#   * measured, ONE added file moved 179 of 2000, and a slice-16 sweep was
#     discarded outright after 233 shifted;
#   * that manifest governs `tests/ui/trust/` only, while the population is all
#     of `tests/ui` --- so on 2026-08-27 four files landing in
#     `tests/ui/contracts/` moved the sample with nothing firing. The gate built
#     to stop sample drift could not see most of the tree it sampled from;
#   * and two files LEFT the population by gaining a `//~` annotation, silently.
#
# The seed pinned the DERIVATION. What matters is the RESULT. This pins the
# result: a lockfile naming every measured path with the sha256 of its contents.
# A sweep reads the lockfile and measures exactly those files, so nothing landing
# anywhere in the tree can move the corpus, and no manifest has to be maintained
# to prevent it.
#
# WHAT THIS RECOVERS, which is the reason it was worth building
# -------------------------------------------------------------
# Comparability was believed lost: the reference population 6983 is unreachable
# today (it is 6985 = 6983 + 4 new eligible under tests/ui/contracts/ - 2 that
# gained `//~`), and no edit to the pin manifest can restore it. But every
# recorded sweep stored its own file list in `corpora.ui_sample.files[]`. So the
# corpus can be locked to the exact 2000 files a recorded sweep measured, and a
# new sweep then measures THE SAME FILES --- the delta against that sweep's
# numbers is meaningful again. Re-sampling was the only thing that had lost it.
#
# `//~` CHURN STOPS MATTERING, and this is a real consequence rather than a
# side effect. The content filters (no `//~`, no aux-build, no ignore-) are a
# SELECTION heuristic for picking files that compile standalone. They are not a
# measurement requirement: the sweep compiles with `--emit=metadata`, and `//~`
# is a compiletest directive that plain rustc ignores. Under a lockfile, a file
# that gains an annotation keeps being measured instead of silently vanishing
# from the denominator. `--check` reports how many locked files today's filters
# would no longer select, precisely so that number is visible rather than
# load-bearing.
#
#   trust_ir_corpus_lock.py --generate --from-artifact <sweep-dir> [--out PATH]
#   trust_ir_corpus_lock.py --check [--lock PATH] [--strict]
#
# --check exits nonzero when a locked file is MISSING (the corpus cannot be
# measured as specified). Content CHANGED is reported and counted but does not
# fail without --strict: test files legitimately evolve, and a sweep over an
# edited file is still a sweep over the locked corpus --- it is the identity of
# the corpus that is pinned here, not the tree's history.

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import subprocess
import sys

LOCK_DEFAULT = os.path.join("scripts", "trust_ir_corpus.lock")

# Kept in step with UI_CONTENT_FILTERS in trust_ir_producer_scorecard.py. Used
# ONLY to report how many locked files today's selection heuristic would skip;
# it never removes a file from the corpus.
SELECTION_FILTERS = [
    ("error-annotation", re.compile(r"//~")),
    ("aux-build", re.compile(r"aux-build|aux-crate|// *compile-flags:.*--extern")),
    ("ignore-directive", re.compile(r"^\s*//@?\s*ignore-", re.M)),
]


def repo_root() -> str:
    return subprocess.run(
        ["git", "rev-parse", "--show-toplevel"],
        cwd=os.path.dirname(os.path.abspath(__file__)),
        capture_output=True, text=True, check=True,
    ).stdout.strip()


def sha256_file(path: str) -> str:
    h = hashlib.sha256()
    with open(path, "rb") as fh:
        for chunk in iter(lambda: fh.read(1 << 16), b""):
            h.update(chunk)
    return h.hexdigest()


def selection_skips(path: str) -> list[str]:
    try:
        text = open(path, "r", encoding="utf-8", errors="replace").read()
    except OSError:
        return []
    return [name for name, rx in SELECTION_FILTERS if rx.search(text)]


def generate(repo: str, artifact: str, out: str) -> int:
    data_path = os.path.join(artifact, "data.json")
    if not os.path.isfile(data_path):
        print(f"no data.json under {artifact}", file=sys.stderr)
        return 2
    with open(data_path) as fh:
        data = json.load(fh)

    corpora = data.get("corpora", {})
    if "ui_sample" not in corpora:
        print(f"{artifact} has no ui_sample corpus", file=sys.stderr)
        return 2
    entries = corpora["ui_sample"]["files"]
    meta = corpora["ui_sample"].get("sample_meta", {})
    prov = data.get("provenance", {})

    rows, missing = [], []
    for e in entries:
        rel = e["file"]
        abs_path = os.path.join(repo, rel)
        if not os.path.isfile(abs_path):
            missing.append(rel)
            continue
        rows.append((rel, sha256_file(abs_path)))
    rows.sort()

    header = f"""# trust-ir producer corpus lock --- the measured corpus, pinned by content.
#
# GENERATED by scripts/trust_ir_corpus_lock.py. Do not hand-edit to make a
# check pass; regenerate, or record the decision that changed the corpus.
#
# Source artifact : {os.path.relpath(artifact, repo)}
#   repo_head     : {prov.get('repo_head')}
#   swept         : {prov.get('date_utc')}
#   seed / sample : {meta.get('seed')} / {meta.get('sampled')} of {meta.get('eligible')} eligible
#
# This file replaces `random.sample(eligible, N)` as the definition of the
# corpus. The sample was stable only while the eligible population length was,
# and it was not --- see the header of scripts/trust_ir_corpus_lock.py for the
# measured drift. Locking the RESULT rather than the derivation means nothing
# landing anywhere in tests/ui can move the corpus again.
#
# A sweep run with --corpus-lock measures exactly these paths, so its numbers
# are directly comparable to the source artifact's. Verify before trusting:
#     python3 scripts/trust_ir_corpus_lock.py --check
#
# Format: <sha256>  <repo-relative path>
# Files : {len(rows)}
"""
    if missing:
        header += f"#\n# WARNING: {len(missing)} path(s) in the source artifact no longer exist and\n" \
                  f"# were dropped from the lock. The corpus is therefore SMALLER than the\n" \
                  f"# artifact's, and totals are not directly comparable without saying so:\n"
        for m in missing[:20]:
            header += f"#   {m}\n"
        if len(missing) > 20:
            header += f"#   ... and {len(missing) - 20} more\n"

    with open(out, "w") as fh:
        fh.write(header)
        for rel, digest in rows:
            fh.write(f"{digest}  {rel}\n")

    print(f"wrote {out}: {len(rows)} file(s)"
          + (f", {len(missing)} missing and dropped" if missing else ""))
    return 0


def load_lock(path: str) -> list[tuple[str, str]]:
    rows = []
    with open(path) as fh:
        for line in fh:
            line = line.rstrip("\n")
            if not line or line.startswith("#"):
                continue
            parts = line.split(None, 1)
            if len(parts) != 2:
                raise ValueError(f"malformed lock row: {line!r}")
            rows.append((parts[1].strip(), parts[0].strip()))
    return rows


def check(repo: str, lock: str, strict: bool) -> int:
    if not os.path.isfile(lock):
        print(f"CORPUS LOCK: absent ({lock})")
        print("  generate one with --generate --from-artifact <sweep-dir>")
        return 1
    rows = load_lock(lock)
    if not rows:
        print("CORPUS LOCK: EMPTY --- a lock that names no file pins nothing.")
        return 1

    missing, changed, unselectable = [], [], []
    for rel, digest in rows:
        abs_path = os.path.join(repo, rel)
        if not os.path.isfile(abs_path):
            missing.append(rel)
            continue
        if sha256_file(abs_path) != digest:
            changed.append(rel)
        skips = selection_skips(abs_path)
        if skips:
            unselectable.append((rel, ",".join(skips)))

    print(f"corpus lock : {os.path.relpath(lock, repo)}")
    print(f"locked files: {len(rows)}")
    print(f"missing     : {len(missing)}")
    print(f"content drift: {len(changed)}")
    print(f"would not be re-selected by today's filters: {len(unselectable)}")
    if unselectable:
        print("  (these keep being measured BECAUSE the corpus is locked --- the")
        print("   filters are a selection heuristic, not a measurement requirement)")
        for rel, why in unselectable[:10]:
            print(f"    {rel}  [{why}]")
        if len(unselectable) > 10:
            print(f"    ... and {len(unselectable) - 10} more")
    for rel in missing[:20]:
        print(f"  MISSING  {rel}")
    if len(missing) > 20:
        print(f"  ... and {len(missing) - 20} more")
    if strict:
        for rel in changed[:20]:
            print(f"  CHANGED  {rel}")
        if len(changed) > 20:
            print(f"  ... and {len(changed) - 20} more")

    if missing:
        print("\nCORPUS LOCK: FAIL --- locked file(s) absent; the corpus cannot be "
              "measured as specified.")
        return 1
    if strict and changed:
        print("\nCORPUS LOCK: FAIL (--strict) --- locked file(s) changed content.")
        return 1
    print("\nCORPUS LOCK: OK")
    return 0


def main() -> int:
    ap = argparse.ArgumentParser(description="pin the producer corpus by content")
    ap.add_argument("--generate", action="store_true")
    ap.add_argument("--from-artifact", metavar="DIR",
                    help="a recorded sweep directory containing data.json")
    ap.add_argument("--check", action="store_true")
    ap.add_argument("--lock", default=None, help=f"lock path (default {LOCK_DEFAULT})")
    ap.add_argument("--strict", action="store_true",
                    help="--check also fails on content drift")
    ap.add_argument("--root", default=None,
                    help="repository to resolve locked paths against (default: the "
                         "repository containing this script, so a hook is unaffected "
                         "by the cwd it fires in)")
    args = ap.parse_args()

    repo = os.path.abspath(args.root) if args.root else repo_root()
    lock = args.lock or os.path.join(repo, LOCK_DEFAULT)

    if args.generate:
        if not args.from_artifact:
            print("--generate requires --from-artifact", file=sys.stderr)
            return 2
        return generate(repo, args.from_artifact, lock)
    if args.check:
        return check(repo, lock, args.strict)
    ap.print_help()
    return 2


if __name__ == "__main__":
    sys.exit(main())
