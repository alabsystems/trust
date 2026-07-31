#!/usr/bin/env python3
# Trust: audit every first-party submodule pin recorded in superproject history.
#
# A superproject gitlink names an exact sibling commit. Nothing in git enforces
# that the sibling commit was pushed before the gitlink referencing it was
# pushed, so a pin can name a commit that exists only on the machine that made
# it. When that happens, any clone whose fetch traverses the offending
# superproject commit fails --- git falls back to a direct-SHA fetch and the
# server answers "not our ref". See docs/first-party-pin-ledger.md.
#
# Classification, weakest evidence to strongest:
#
#   MISSING   absent from the sibling's local object store. If the remote also
#             refuses it, the pin is unrecoverable and that superproject commit
#             can never be reproduced.
#   ORPHAN    present, but not reachable from any remote-tracking branch. The
#             forge still serves such objects by SHA, so the pin resolves
#             today, but it survives only until a server-side gc.
#   OK        reachable from a remote-tracking branch.
#
# Remote-tracking refs are only as fresh as the last fetch; pass --fetch to
# refresh them first, and --probe to ask each remote whether it can actually
# serve the MISSING/ORPHAN pins.

from __future__ import annotations

import argparse
import re
import subprocess
import sys
import tempfile
import time
from pathlib import Path

ZERO = "0" * 40


def git(repo: Path, args: list[str], *, git_dir: Path | None = None) -> str:
    cmd = ["git"]
    if git_dir is not None:
        cmd += ["--git-dir", str(git_dir)]
    else:
        cmd += ["-C", str(repo)]
    done = subprocess.run(
        cmd + args, capture_output=True, text=True, check=False
    )
    if done.returncode != 0:
        return ""
    return done.stdout


def submodule_paths(repo: Path) -> list[str]:
    """Gitlink paths declared by the indexed .gitmodules, in listed order."""
    out = git(repo, ["config", "-f", ".gitmodules", "--get-regexp", r"^submodule\..*\.path$"])
    return [line.split(" ", 1)[1] for line in out.splitlines() if " " in line]


def pins_for(repo: Path, path: str) -> set[str]:
    """Every gitlink value this path has ever held in HEAD's history.

    ``--raw -m`` reports the diff against each parent, so pins introduced on a
    merged side branch are counted too, not just first-parent ones.
    """
    out = git(repo, ["log", "--format=%H", "--raw", "--no-abbrev", "-m", "HEAD", "--", path])
    pins: set[str] = set()
    for line in out.splitlines():
        if not line.startswith(":"):
            continue
        fields = line[1:].split()
        # <oldmode> <newmode> <oldsha> <newsha> <status>\t<path>
        if len(fields) < 4 or "160000" not in (fields[0], fields[1]):
            continue
        for sha in (fields[2], fields[3]):
            if len(sha) == 40 and sha != ZERO:
                pins.add(sha)
    return pins


def remote_reachable_set(git_dir: Path) -> set[str]:
    """Commits reachable from the sibling's remote-tracking refs (one walk).

    ``refs/pins/*`` counts: an anchored pin is held by a real ref on the remote
    and is therefore gc-safe, even though no branch contains it.
    """
    out = git(Path("."), ["rev-list", "--remotes", "--glob=refs/pins"], git_dir=git_dir)
    return set(out.split())


PINS_REFSPEC = "+refs/pins/*:refs/pins/*"


def remote_url(repo: Path, path: str) -> str:
    name = path.split("/")[-1]
    for key in (f"submodule.{path}.url", f"submodule.{name}.url"):
        url = git(repo, ["config", "-f", ".gitmodules", "--get", key]).strip()
        if url:
            return url
    return ""


SERVED, REFUSED, UNKNOWN = "served", "refused", "unknown"


def classify_probe_results(
    local_presence: dict[str, bool], verdicts: dict[str, str]
) -> tuple[list[str], list[str], list[str]]:
    """Classify candidates without discarding locally recoverable objects.

    A remote refusal proves loss only when the commit is absent locally too.
    If the object is present in the sibling object store, it remains an ORPHAN
    that ``--anchor`` can rescue even when a direct-SHA fetch is refused.
    """
    missing, orphan, indeterminate = [], [], []
    for sha, present in local_presence.items():
        verdict = verdicts[sha]
        if present or verdict == SERVED:
            orphan.append(sha)
        elif verdict == REFUSED:
            missing.append(sha)
        else:
            indeterminate.append(sha)
    return missing, orphan, indeterminate


def probe(url: str, sha: str, timeout: int = 180, attempts: int = 3) -> str:
    """Ask the remote whether it can serve `sha` at all.

    Returns SERVED, REFUSED, or UNKNOWN. The distinction matters: only an
    explicit "not our ref" proves the object is gone. Any other failure --- a
    throttled connection, a transport hiccup --- must NOT be reported as a lost
    pin, so it degrades to UNKNOWN and is retried with backoff first.

    ``--filter=tree:0`` keeps this to the commit object rather than a full
    depth-1 snapshot, so probing stays cheap on large siblings; servers that
    reject the filter get a second, unfiltered attempt.
    """
    for attempt in range(attempts):
        with tempfile.TemporaryDirectory() as tmp:
            subprocess.run(["git", "init", "-q", tmp], check=False, capture_output=True)
            for extra in (["--filter=tree:0"], []):
                try:
                    done = subprocess.run(
                        ["git", "-C", tmp, "fetch", "-q", "--depth", "1", *extra,
                         "--no-tags", url, sha],
                        capture_output=True, text=True, timeout=timeout, check=False,
                    )
                except subprocess.TimeoutExpired:
                    continue
                if done.returncode == 0:
                    return SERVED
                if "not our ref" in done.stderr:
                    return REFUSED
        time.sleep(2 * (attempt + 1))
    return UNKNOWN


def _ssh_url(url: str) -> str:
    """github.com/<owner>/<repo>.git over SSH, for the workflow-scope fallback."""
    m = re.match(r"https://github\.com/([^/]+)/(.+?)(?:\.git)?/?$", url)
    return f"git@github.com:{m.group(1)}/{m.group(2)}.git" if m else ""


def _last_line(text: str) -> str:
    lines = [line for line in text.strip().splitlines() if line.strip()]
    return lines[-1] if lines else "(no output)"


def anchor(git_dir: Path, url: str, sha: str) -> str:
    """Give an unreferenced-but-servable pin a permanent ref in the sibling.

    An ORPHAN pin resolves only because forges serve unreferenced objects; a
    server-side gc may stop. Pushing refs/pins/<sha> makes the commit reachable,
    so the pin is guaranteed for as long as the sibling repo exists. The ref is
    additive and touches no branch.
    """
    present = subprocess.run(
        ["git", "--git-dir", str(git_dir), "cat-file", "-e", f"{sha}^{{commit}}"],
        capture_output=True,
    ).returncode == 0
    if not present:
        got = subprocess.run(
            ["git", "--git-dir", str(git_dir), "fetch", "-q", "--no-tags", url, sha],
            capture_output=True, text=True, check=False,
        )
        if got.returncode != 0:
            return f"cannot anchor (fetch failed): {_last_line(got.stderr)}"
    for target in (url, _ssh_url(url)):
        if not target:
            continue
        done = subprocess.run(
            ["git", "--git-dir", str(git_dir), "push", "-q", target,
             f"{sha}:refs/pins/{sha}"],
            capture_output=True, text=True, check=False,
        )
        if done.returncode == 0:
            return "anchored" if target == url else "anchored (ssh)"
        # GitHub refuses OAuth-token pushes that carry .github/workflows
        # changes unless the token holds the `workflow` scope. SSH keys are
        # not scope-limited, so retry there rather than reporting a failure
        # that has nothing to do with the pin.
        if "workflow" not in done.stderr:
            return f"push failed: {_last_line(done.stderr)}"
    return f"push failed: {_last_line(done.stderr)}"


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--fetch", action="store_true", help="refresh remote-tracking refs first")
    parser.add_argument("--probe", action="store_true", help="ask remotes to serve MISSING/ORPHAN pins")
    parser.add_argument("--anchor", action="store_true",
                        help="push refs/pins/<sha> for ORPHAN pins so a gc cannot reap them")
    parser.add_argument("--repo", default=".", help="superproject path")
    args = parser.parse_args()

    repo = Path(args.repo).resolve()
    paths = submodule_paths(repo)
    if not paths:
        print("no submodules declared in .gitmodules", file=sys.stderr)
        return 2

    unrecoverable: list[tuple[str, str]] = []
    fragile: list[tuple[str, str]] = []

    for path in paths:
        git_dir = repo / ".git" / "modules" / path
        if not git_dir.is_dir():
            print(f"{path:<22} gitdir absent — not materialized, skipped")
            continue
        if args.fetch:
            git(Path("."), ["fetch", "--quiet", "--prune", "origin"], git_dir=git_dir)
            # Anchors live outside the default refspec; fetch them explicitly
            # so previously anchored pins are recognized as safe.
            git(Path("."), ["fetch", "--quiet", "origin", PINS_REFSPEC], git_dir=git_dir)

        pins = pins_for(repo, path)
        reachable = remote_reachable_set(git_dir)
        url = remote_url(repo, path)

        missing, orphan = [], []
        for sha in sorted(pins):
            if sha in reachable:
                continue
            # cat-file -e is silent on success, so check the status, not stdout.
            present = subprocess.run(
                ["git", "--git-dir", str(git_dir), "cat-file", "-e", f"{sha}^{{commit}}"],
                capture_output=True,
            ).returncode == 0
            if not present:
                missing.append(sha)
            else:
                orphan.append(sha)

        note, indeterminate = "", []
        if args.probe:
            # One decision per candidate: the remote either serves the object
            # (fragile but resolvable) or explicitly refuses it. A refusal is
            # lost only when no local copy can be anchored. A probe that could
            # not reach a verdict is reported, never assumed lost.
            candidates = missing + orphan
            local_presence = {
                sha: sha in orphan
                for sha in candidates
            }
            verdicts = {}
            for sha in candidates:
                verdicts[sha] = probe(url, sha)
                time.sleep(0.5)  # keep well under the forge's abuse threshold
            missing, orphan, indeterminate = classify_probe_results(
                local_presence, verdicts
            )
            note = "  (probed)"

        ok = len(pins) - len(missing) - len(orphan) - len(indeterminate)
        print(f"{path:<22} {len(pins):>4} pins   OK={ok:<4} "
              f"ORPHAN={len(orphan):<3} MISSING={len(missing):<3} "
              f"UNKNOWN={len(indeterminate)}{note}")
        for sha in missing:
            print(f"    MISSING {sha}")
            unrecoverable.append((path, sha))
        for sha in orphan:
            suffix = f"  → {anchor(git_dir, url, sha)}" if args.anchor else ""
            print(f"    ORPHAN  {sha}{suffix}")
            fragile.append((path, sha))
        for sha in indeterminate:
            print(f"    UNKNOWN {sha}  (probe inconclusive — re-run)")

    print()
    if unrecoverable:
        print(f"UNRECOVERABLE pins: {len(unrecoverable)} "
              f"(superproject commits naming them cannot be reproduced)")
    if fragile:
        print(f"FRAGILE pins: {len(fragile)} — served by SHA but on no branch; "
              f"anchor them with a ref in the sibling repo")
    if not unrecoverable and not fragile:
        print("every first-party pin is reachable from a remote branch")
    return 1 if unrecoverable else 0


if __name__ == "__main__":
    raise SystemExit(main())
