#!/usr/bin/env python3
"""Advance active TRUST-TWO-LANGUAGE-100 claim bases onto the integration head.

WHY THIS EXISTS
---------------

``base_revision``/``integration_head`` on an active claim record the tree the
reservation was taken against.  The ledger protocol has always treated moving
them as a first-class operation -- the goal document lists "integration-base
updates" alongside renewal, release and abandonment, and
``check_two_language_claim_ledger.py``'s transition rules are written to permit
exactly a FORWARD move of those two fields and nothing else.  Every other field
an active claim carries is either immutable or may only grow.

It was nevertheless performed BY HAND.  ``55d293ee4b`` and ``cf2d5cc36b`` each
retyped the same sha into every active claim, and the operator justified the
move in prose: *"synchronization head X leaves the complete W3 exact-file tree
byte-identical to parent Y; the integrated producer delta is ... outside this
claim."*  A hand operation that must be repeated whenever anything lands is one
nobody runs, and the ledger drifted until the gate refused every push.

This is that operation, mechanised, with the operator's justification computed
instead of asserted.

WHAT IT REFUSES TO DO
---------------------

* It never touches a claim that is not ``active``.  Released and abandoned
  records are history.
* It never moves a base BACKWARDS or sideways.  A base that is not already an
  ancestor of the integration head is a diverged/rewound/foreign claim; that
  needs its owner, not a script, and is reported and skipped.
* It never silently launders an OVERTAKEN reservation.  When the integration
  head's tree is not byte-identical to the base's over the claim's
  ``exact_files``, some other machine has changed the residue under an
  in-flight increment.  That claim is skipped unless ``--accept-overtaken`` is
  given, and when it is given the paths and the commits that took them are
  written into the ledger commit message, so the acceptance is published rather
  than implied.
* It never edits any field but ``base_revision``, ``integration_head`` and --
  where the claim carries one -- the ``validation_at_integration`` record that
  must agree with them.  A claim whose bytes do not survive a JSON round trip
  is skipped rather than reformatted.
* It never force-pushes.  The ledger child and every affected mirror go out in
  ONE fast-forward push, and the candidate is validated by the real checker
  with ``--expected-parent`` before it is published.

Usage::

    python3 scripts/refresh_two_language_claim_bases.py            # dry run
    python3 scripts/refresh_two_language_claim_bases.py --publish
    python3 scripts/refresh_two_language_claim_bases.py --publish --accept-overtaken

Exit codes: 0 refreshed (or nothing to do), 1 refused, 2 environment failure.

Author: Andrew Yates | Copyright 2026 Andrew Yates | License: Apache-2.0 OR MIT
"""

from __future__ import annotations

import argparse
import collections
import json
import os
import subprocess
import sys
import tempfile
from datetime import datetime, timezone
from pathlib import Path
from typing import Dict, List, Optional, Sequence, Tuple

REPO_ROOT = Path(__file__).resolve().parents[1]
CHECKER = REPO_ROOT / "scripts" / "check_two_language_claim_ledger.py"

DEFAULT_LEDGER_REF = "refs/remotes/origin/goals/TRUST-TWO-LANGUAGE-100"
DEFAULT_INTEGRATION_REF = "refs/remotes/origin/main"
DEFAULT_REMOTE = "origin"
LEDGER_PUSH_REF = "refs/heads/goals/TRUST-TWO-LANGUAGE-100"
MIRROR_PUSH_PREFIX = "refs/heads/claims"
CLAIM_TREE_DIR = "coordination/claims"
FETCH_REFSPECS = (
    f"+{LEDGER_PUSH_REF}:{DEFAULT_LEDGER_REF}",
    f"+{MIRROR_PUSH_PREFIX}/TRUST-TWO-LANGUAGE-100/*"
    ":refs/remotes/origin/claims/TRUST-TWO-LANGUAGE-100/*",
)


class Refusal(RuntimeError):
    pass


def git(*args: str, check: bool = True, env: Optional[Dict[str, str]] = None) -> str:
    environment = os.environ.copy()
    environment["GIT_OPTIONAL_LOCKS"] = "0"
    environment["LC_ALL"] = "C"
    if env:
        environment.update(env)
    completed = subprocess.run(
        ["git", "-C", str(REPO_ROOT), *args],
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
        text=True,
        env=environment,
    )
    if check and completed.returncode != 0:
        raise Refusal(
            f"git {' '.join(args)} exited {completed.returncode}: "
            f"{completed.stderr.strip() or '<no stderr>'}"
        )
    return completed.stdout


def rev_parse(revision: str) -> str:
    out = git("rev-parse", "--verify", "--quiet", "--end-of-options", f"{revision}^{{commit}}",
              check=False).strip()
    if len(out) != 40:
        raise Refusal(f"{revision!r} does not resolve to a commit in this clone")
    return out


def merge_base(left: str, right: str) -> str:
    out = git("merge-base", "--end-of-options", left, right, check=False).strip()
    if len(out) != 40:
        raise Refusal(f"{left[:12]} and {right[:12]} share no history")
    return out


def is_ancestor(older: str, newer: str) -> bool:
    completed = subprocess.run(
        ["git", "-C", str(REPO_ROOT), "merge-base", "--is-ancestor", older, newer],
        stdout=subprocess.DEVNULL,
        stderr=subprocess.PIPE,
        check=False,
    )
    if completed.returncode not in (0, 1):
        raise Refusal(f"cannot compare {older[:12]}..{newer[:12]}: {completed.stderr!r}")
    return completed.returncode == 0


def reserved_paths_moved(base: str, head: str, paths: Sequence[str]) -> List[str]:
    """Reserved paths whose bytes differ between the two trees.

    ``--ignore-submodules=none`` is mandatory here for the same reason it is in
    the checker: this clone's config sets ``diff.ignoreSubmodules = all``, which
    would hide a ``first-party/*`` gitlink move inside a reservation.
    """
    if not paths:
        return []
    out = git(
        "diff", "--name-only", "-z", "--ignore-submodules=none", "--end-of-options",
        base, head, "--", *paths,
    )
    return sorted({item for item in out.split("\0") if item})


def commits_touching(base: str, head: str, paths: Sequence[str]) -> List[str]:
    if not paths:
        return []
    out = git("log", "--format=%h %s", "--end-of-options", f"{base}..{head}", "--", *paths,
              check=False)
    return [line.strip() for line in out.splitlines() if line.strip()]


def claim_blobs(ledger_commit: str) -> Dict[str, bytes]:
    listing = git("ls-tree", "-r", "--name-only", "-z", ledger_commit, "--", CLAIM_TREE_DIR)
    blobs: Dict[str, bytes] = {}
    for path in (item for item in listing.split("\0") if item):
        raw = subprocess.run(
            ["git", "-C", str(REPO_ROOT), "cat-file", "blob", f"{ledger_commit}:{path}"],
            stdout=subprocess.PIPE,
            check=True,
        ).stdout
        blobs[path] = raw
    return blobs


def render(document: object) -> bytes:
    return (json.dumps(document, indent=2, ensure_ascii=False) + "\n").encode("utf-8")


def refresh_document(
    document: "collections.OrderedDict[str, object]",
    head: str,
    moved: Sequence[str],
    witnesses: Sequence[str],
    now: datetime,
) -> None:
    """Move the two revision fields, and keep any validation record honest."""
    old_base = str(document["base_revision"])
    document["base_revision"] = head
    document["integration_head"] = head
    record = document.get("validation_at_integration")
    if not isinstance(record, dict):
        return
    record["integration_head"] = head
    record["observed_at"] = now.astimezone(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")
    results = record.get("results")
    limitations = record.get("limitations")
    if not isinstance(results, list) or not isinstance(limitations, list):
        raise Refusal(
            f"{document['claim_id']}: validation_at_integration is malformed; refusing to edit it"
        )
    if moved:
        results.insert(
            0,
            f"coordination synchronization head {head} does NOT leave this claim's exact-file "
            f"tree byte-identical to parent {old_base}: {', '.join(moved)} moved "
            f"[{'; '.join(witnesses)}]",
        )
        limitations.insert(
            0,
            f"the {head} synchronization accepted an OVERTAKEN reservation: the listed reserved "
            "paths changed under the in-flight increment and neither this claim's validation "
            "battery nor a remeasurement was rerun",
        )
    else:
        results.insert(
            0,
            f"coordination synchronization head {head} leaves this claim's complete exact-file "
            f"tree byte-identical to parent {old_base}; the integrated delta is outside this claim",
        )
        limitations.insert(
            0,
            f"the {head} synchronization received a direct exact-file tree diff audit, not a "
            "rerun of this claim's validation battery",
        )


def build_ledger_child(
    ledger_commit: str, updates: Dict[str, bytes], message: str
) -> str:
    """Commit the replacement blobs onto the ledger tip through a scratch index.

    A scratch ``GIT_INDEX_FILE`` keeps the worktree and the real index out of
    it entirely -- which also sidesteps this clone's ``submodule.*.ignore = all``
    staging trap, since nothing is ever staged from the worktree.
    """
    with tempfile.TemporaryDirectory() as scratch:
        index = os.path.join(scratch, "index")
        env = {"GIT_INDEX_FILE": index}
        git("read-tree", ledger_commit, env=env)
        for path, raw in updates.items():
            blob = subprocess.run(
                ["git", "-C", str(REPO_ROOT), "hash-object", "-w", "--stdin"],
                input=raw,
                stdout=subprocess.PIPE,
                check=True,
            ).stdout.decode().strip()
            git("update-index", "--cacheinfo", f"100644,{blob},{path}", env=env)
        tree = git("write-tree", env=env).strip()
    return git("commit-tree", tree, "-p", ledger_commit, "-m", message).strip()


def validate_candidate(candidate: str, integration: str, parent: str) -> None:
    completed = subprocess.run(
        [
            sys.executable,
            str(CHECKER),
            "--ledger-ref",
            candidate,
            "--integration-ref",
            integration,
            "--expected-parent",
            parent,
        ],
        cwd=str(REPO_ROOT),
        check=False,
        text=True,
        capture_output=True,
    )
    sys.stdout.write(completed.stdout)
    sys.stderr.write(completed.stderr)
    if completed.returncode != 0:
        raise Refusal(
            f"the candidate ledger child {candidate[:12]} does not validate "
            f"(checker exit {completed.returncode}); nothing was published"
        )


def main(argv: Optional[Sequence[str]] = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--ledger-ref", default=DEFAULT_LEDGER_REF)
    parser.add_argument("--integration-ref", default=DEFAULT_INTEGRATION_REF)
    parser.add_argument("--remote", default=DEFAULT_REMOTE)
    parser.add_argument("--fetch", action="store_true",
                        help="fetch the ledger and mirror refs before reading them")
    parser.add_argument("--publish", action="store_true",
                        help="push the ledger child and its mirrors (one fast-forward push)")
    parser.add_argument(
        "--accept-overtaken",
        action="store_true",
        help="also refresh claims whose reserved tree changed, recording the paths and "
             "commits that took them in the ledger commit message",
    )
    args = parser.parse_args(argv)

    try:
        if args.fetch:
            git("fetch", args.remote, *FETCH_REFSPECS)
        ledger_commit = rev_parse(args.ledger_ref)
        integration = rev_parse(args.integration_ref)
        # A claim's integration_head must be contained in the ledger commit, so
        # the newest revision this ledger can legally stamp is the merge base --
        # NOT the integration tip. Advancing past it is a MERGE of the
        # integration branch into the goals branch, which is a content decision
        # with real conflicts (measured 2026-09-01: it conflicts today). This
        # tool does bookkeeping, so it says so rather than attempting it.
        head = merge_base(ledger_commit, integration)
        now = datetime.now(timezone.utc)
        if head != integration:
            ahead = git("rev-list", "--count", "--end-of-options",
                        f"{head}..{integration}").strip()
            print(
                f"OBSERVED HEAD {head[:12]} = merge-base(ledger, {args.integration_ref}); "
                f"the integration ref is {ahead} commit(s) beyond what this ledger "
                "references. Going further needs the goals branch to MERGE the "
                "integration branch first; this tool will not do that for you."
            )

        updates: Dict[str, bytes] = {}
        refreshed: List[Tuple[str, str, List[str], List[str]]] = []
        skipped: List[str] = []

        for path, raw in sorted(claim_blobs(ledger_commit).items()):
            document = json.loads(raw.decode("utf-8"),
                                  object_pairs_hook=collections.OrderedDict)
            claim_id = str(document.get("claim_id"))
            if document.get("status") != "active":
                continue
            base = str(document.get("base_revision"))
            if base == head and str(document.get("integration_head")) == head:
                continue
            if render(document) != raw:
                skipped.append(f"{claim_id}: bytes do not survive a JSON round trip")
                continue
            if not is_ancestor(base, head):
                skipped.append(
                    f"{claim_id}: base {base[:12]} is not an ancestor of {head[:12]} "
                    "(diverged/rewound) -- its owner must re-take it"
                )
                continue
            exact_files = [item for item in document.get("exact_files", [])
                           if isinstance(item, str) and item]
            moved = reserved_paths_moved(base, head, exact_files)
            witnesses = commits_touching(base, head, moved) if moved else []
            if moved and not args.accept_overtaken:
                skipped.append(
                    f"{claim_id}: OVERTAKEN at {', '.join(moved)} "
                    f"[{'; '.join(witnesses) or 'merge resolution'}] -- rerun with "
                    "--accept-overtaken to publish that acceptance, or remeasure first"
                )
                continue
            refresh_document(document, head, moved, witnesses, now)
            updates[path] = render(document)
            refreshed.append((claim_id, base, moved, witnesses))

        for line in skipped:
            print(f"SKIP {line}")
        if not updates:
            print(f"NOTHING TO REFRESH: every active claim already names {head[:12]}"
                  if not skipped else "NOTHING REFRESHED: every candidate was skipped above")
            return 1 if skipped else 0

        clean = [row for row in refreshed if not row[2]]
        overtaken = [row for row in refreshed if row[2]]
        lines = [
            "coordination(two-language): advance active claim bases onto "
            f"{head[:12]}",
            "",
            f"Mechanical integration-base update produced by {Path(__file__).name}.",
            f"Integration head: {head}",
            f"Ledger parent:    {ledger_commit}",
            "",
        ]
        if clean:
            lines.append("Reserved tree byte-identical across the move (no remeasurement owed):")
            lines.extend(f"  {claim_id}  {base[:12]} -> {head[:12]}"
                         for claim_id, base, _moved, _w in clean)
            lines.append("")
        if overtaken:
            lines.append("OVERTAKEN reservations, accepted explicitly with --accept-overtaken.")
            lines.append("Another machine changed these reserved paths under an in-flight")
            lines.append("increment; the base is advanced to record that, and no validation")
            lines.append("battery was rerun:")
            for claim_id, base, moved, witnesses in overtaken:
                lines.append(f"  {claim_id}  {base[:12]} -> {head[:12]}")
                for item in moved:
                    lines.append(f"    path: {item}")
                for item in witnesses:
                    lines.append(f"    took: {item}")
            lines.append("")
        message = "\n".join(lines)

        candidate = build_ledger_child(ledger_commit, updates, message)
        print(f"CANDIDATE {candidate}")
        validate_candidate(candidate, head, ledger_commit)

        refspecs = [f"{candidate}:{LEDGER_PUSH_REF}"]
        refspecs += [f"{candidate}:{MIRROR_PUSH_PREFIX}/{claim_id}"
                     for claim_id, _base, _moved, _w in refreshed]
        if not args.publish:
            print("DRY RUN — the candidate validates. Publish it with:")
            print(f"  git push {args.remote} \\\n    " + " \\\n    ".join(refspecs))
            return 0
        print(f"PUSH {args.remote} ({len(refspecs)} refs, fast-forward only)")
        git("push", args.remote, *refspecs)
        print("PUBLISHED")
        return 0
    except Refusal as exc:
        print(f"CLAIM BASE REFRESH REFUSED: {exc}", file=sys.stderr)
        return 1
    except (OSError, ValueError) as exc:
        print(f"CLAIM BASE REFRESH ERROR: {exc}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    sys.exit(main())
