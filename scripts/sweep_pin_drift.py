#!/usr/bin/env python3
# Trust: report submodule pin drift ACROSS THE FLEET, when it is created.
#
# Author: Andrew Yates. Copyright 2026 Andrew Yates. License: Apache-2.0 OR MIT.
#
# WHY THIS EXISTS
# ---------------
# Every pin gate in this repo is a PUSH gate. `fast.dependency-constellation`
# refuses a revision whose terminal pins lag their own dependency graph, and
# `fast.submodule-remote-reachability` refuses a gitlink naming a commit no
# remote can serve --- but only for the lane that happens to push next. So
# drift lands, sits, and is then discovered by whoever pushes afterwards, which
# is never the lane that created it. Measured 2026-08-30, four distinct pin
# failures in one day, every one caught by an unrelated lane and one of them
# blocking the compiler repo for hours:
#
#   * a superproject gitlink whose sibling commit was NEVER PUSHED
#     (first-party/ay b851ff380a existed on no remote)
#   * an audit that reported all-clear from STALE remote-tracking refs
#   * trust's `clean` terminal at 96d4ce6b (08-29) while trust-cg's lock ---
#     selected by trust's OWN trust-cg pin --- referenced 51eac32b (08-30)
#   * the identical shape again for `ty` (terminal 991c0595 vs 384ee914)
#
# This is the same set of checks with the subject changed from "the revision I
# am pushing" to "every superproject on this machine, at what it has PUBLISHED".
# It is meant to be run on a timer, so drift is named within one sweep interval
# of being created rather than at the next unrelated push.
#
# IT NEVER JUDGES FROM REMOTE-TRACKING REFS, and that is not a stylistic
# choice. `git branch -r --contains` and `rev-list --remotes` read
# refs/remotes/*, which survive a branch the forge has since deleted or
# rewound; an audit built on them reports a confident all-clear about pins that
# are on no remote at all. That is exactly how the second failure above went
# unnoticed. Durability here is decided against the canonical remote's own
# `git ls-remote` inventory, sampled during the sweep, via
# `audit_first_party_pins.remote_authoritative_reachability` --- the one
# implementation, so this tool cannot drift away from the audit's semantics.
#
# WHAT IT REPORTS, per first-party gitlink
# ----------------------------------------
#   UNPUBLISHED   the pinned commit is on no branch and no refs/pins/* ref on
#                 the canonical remote. A clone cannot reproduce it, and a
#                 server-side gc can end it. This is failure (a), and it is the
#                 finding that makes a superproject commit unreproducible
#                 forever --- 22 such pins already exist (see
#                 docs/first-party-pin-ledger.md); the point of this sweep is
#                 that there is never a 23rd.
#   ANCHORED      on no branch, but held by a durable refs/pins/* ref. Safe.
#   BEHIND n      published, and n commits behind the sibling's remote main.
#                 This is the lag that becomes failures (c)/(d) as soon as
#                 another pinned sibling starts referencing the newer revision.
#   AHEAD n       the pin holds commits remote main does not.
#   DIVERGED      neither is an ancestor of the other.
#
# BEHIND is REPORTED, not refused. A superproject pins deliberately and a lag
# is normal for as long as the consumer has not been updated; the sweep's job
# is to make the number visible while it is small. Only UNPUBLISHED and
# operational failures are hard.
#
# Third-party gitlinks (trust-cg's SAT solvers, tlaplus-examples' upstream
# spec mirrors) are checked for reachability and NOT for lag: pinning an
# upstream project at an old revision is the intended state, so reporting it as
# drift would be noise that trains readers to ignore the report.
#
# MEASURED COST (2026-08-31, this machine, warm clones, four superprojects and
# 17 gitlinks): 30.7 s wall for the reachability sweep --- one `git ls-remote`
# per distinct remote (1.0-1.5 s each, network-bound) and no object transfer at
# all, because a clone that has fetched recently already holds every sampled
# tip. `--constellation` adds one `check_dependency_cycle_anchor.py` run per
# constellation-bearing repo, measured 36.2 s for Trust. Nothing compiles and
# no build-tree lock is taken, so it is safe to run beside a build.
#
#     scripts/sweep_pin_drift.py                  # the sweep, reachability + lag
#     scripts/sweep_pin_drift.py --constellation  # ...and the terminal-lag gate
#     scripts/sweep_pin_drift.py --json           # machine-readable rows
#     scripts/sweep_pin_drift.py --repo ~/trust   # one superproject
#
# Exit 0 clean, 1 findings, 2 the sweep could not do its job.

from __future__ import annotations

import argparse
import json
import subprocess
import sys
import time
from pathlib import Path
from typing import NamedTuple

sys.path.insert(0, str(Path(__file__).resolve().parent))
import audit_first_party_pins as audit  # noqa: E402  (path-relative by design)


# A gitlink is FIRST-PARTY when its canonical remote is one of the fleet's own
# owners. Only those carry the "a pin move and its consumer updates belong in
# the same commit" obligation; an upstream mirror is pinned old on purpose.
FIRST_PARTY_OWNERS = ("alabsystems", "alabsystems")


class Finding(NamedTuple):
    """Two independent verdicts, never collapsed into one word.

    ``status`` answers "can anyone else reproduce this pin" and ``lag`` answers
    "is this pin current". They are orthogonal and the interesting cases are
    exactly the mixed ones: Trust's live `first-party/ay` pin is ANCHORED (a
    refs/pins/* ref is the ONLY thing holding it — it is on no branch of `ay`)
    and simultaneously DIVERGED from that sibling's published main. Reporting
    one word would have hidden whichever half the reader was not looking for.
    """

    repo: str
    path: str
    sha: str
    status: str
    lag: str
    detail: str

    @property
    def hard(self) -> bool:
        return self.status in ("UNPUBLISHED", "ERROR")

    @property
    def drifted(self) -> bool:
        return self.lag in ("BEHIND", "AHEAD", "DIVERGED")


def run(repo: Path, args: list[str], *, git_dir: Path | None = None) -> tuple[int, str, str]:
    cmd = ["git"]
    cmd += ["--git-dir", str(git_dir)] if git_dir is not None else ["-C", str(repo)]
    done = subprocess.run(cmd + args, capture_output=True, text=True, check=False)
    return done.returncode, done.stdout, done.stderr


def out(repo: Path, args: list[str], *, git_dir: Path | None = None) -> str:
    code, stdout, _ = run(repo, args, git_dir=git_dir)
    return stdout.strip() if code == 0 else ""


def resolve_url(raw: str, superproject: Path) -> str:
    """Resolve `.gitmodules` URLs, including the relative form git allows.

    orca-alab declares `rust/aterm` as `../aterm.git`, which git resolves
    against the SUPERPROJECT's own remote rather than against a path on disk.
    Treating that as a filesystem path silently audits nothing.
    """
    if not raw.startswith(("./", "../")):
        return raw
    base = out(superproject, ["config", "--get", "remote.origin.url"])
    if not base:
        return ""
    base = base.rstrip("/")
    if base.endswith(".git"):
        base = base[: -len(".git")]
    for part in raw.split("/"):
        if part == ".":
            continue
        if part == "..":
            base = base.rsplit("/", 1)[0] if "/" in base else base
        else:
            base = f"{base}/{part}"
    return base


def is_first_party(url: str) -> bool:
    lowered = url.lower()
    return any(f"/{owner}/" in lowered or f":{owner}/" in lowered
               for owner in FIRST_PARTY_OWNERS)


def superprojects(roots: list[Path]) -> list[Path]:
    found: list[Path] = []
    for root in roots:
        if (root / ".gitmodules").is_file():
            found.append(root)
            continue
        if not root.is_dir():
            continue
        for child in sorted(root.iterdir()):
            if (child / ".gitmodules").is_file() and (child / ".git").exists():
                found.append(child)
    return found


def default_head(refs: dict[str, str]) -> tuple[str, str]:
    """(ref, sha) of the branch a clone would check out, or ("", "").

    Hardcoding `refs/heads/main` reported `tlaplus-examples` --- whose default
    branch is `master` --- as having no main at all, which is a defect in the
    sweep dressed up as a finding about the repo.
    """
    for name in ("refs/heads/main", "refs/heads/master"):
        if name in refs:
            return name, refs[name]
    heads = {ref: sha for ref, sha in refs.items() if ref.startswith("refs/heads/")}
    if len(heads) == 1:
        return next(iter(heads.items()))
    return "", ""


def published_revision(repo: Path) -> tuple[str, str, str]:
    """The revision the world can see, read from the remote and not remembered.

    Returns (rev, label, error). A sweep that judged this clone's HEAD would
    report drift nobody else can observe and miss drift that is already public
    --- and a sweep that judged refs/remotes/origin/main without checking it
    against the remote would repeat the staleness defect this whole file exists
    to close. So the remote is asked, and the answer is what gets judged.
    """
    url = out(repo, ["config", "--get", "remote.origin.url"])
    if not url:
        return "", "", "no remote.origin.url"
    code, stdout, stderr = run(repo, ["ls-remote", "--refs", url, "refs/heads/*"])
    if code != 0:
        last = (stderr or stdout).strip().splitlines()
        return "", "", f"ls-remote failed: {last[-1] if last else '(no output)'}"
    refs = {}
    for line in stdout.splitlines():
        fields = line.split()
        if len(fields) == 2:
            refs[fields[1]] = fields[0]
    name, tip = default_head(refs)
    if not tip:
        return "", "", f"canonical remote exposes no default branch ({len(refs)} heads)"
    if run(repo, ["cat-file", "-e", f"{tip}^{{commit}}"])[0] != 0:
        code, _, _ = run(repo, ["fetch", "--quiet", "--no-tags", url, tip])
        if code != 0 or run(repo, ["cat-file", "-e", f"{tip}^{{commit}}"])[0] != 0:
            return "", "", (
                f"published {name} {tip[:12]} is not in this object store and "
                "could not be fetched"
            )
    return tip, f"{name.removeprefix('refs/heads/')} {tip[:12]}", ""


def gitlinks(repo: Path, rev: str) -> list[tuple[str, str]]:
    """(path, sha) for every gitlink recorded AT `rev`, not in the worktree."""
    code, stdout, _ = run(repo, ["ls-tree", "-r", rev])
    if code != 0:
        return []
    rows = []
    for line in stdout.splitlines():
        meta, _, path = line.partition("\t")
        fields = meta.split()
        if len(fields) == 3 and fields[0] == "160000":
            rows.append((path, fields[2]))
    return rows


def declared_urls(repo: Path, rev: str) -> dict[str, str]:
    """path -> canonical URL, read from `.gitmodules` AS COMMITTED at `rev`.

    Read through `git config --blob` rather than from the worktree file: the
    sweep judges a published revision, and a worktree `.gitmodules` is a third
    revision that nobody else can see. The submodule NAME is not the path
    (`first-party/ay`'s name is `first-party/ay` here, but git does not require
    it), so paths and urls are joined through the name.
    """
    def config(pattern: str) -> dict[str, str]:
        done = subprocess.run(
            ["git", "-C", str(repo), "config", "--blob", f"{rev}:.gitmodules",
             "--get-regexp", pattern],
            capture_output=True, text=True, check=False,
        )
        rows: dict[str, str] = {}
        if done.returncode != 0:
            return rows
        for line in done.stdout.splitlines():
            key, _, value = line.partition(" ")
            if key.startswith("submodule.") and value:
                rows[key.split(".", 1)[1].rsplit(".", 1)[0]] = value.strip()
        return rows

    paths, urls = config(r"^submodule\..*\.path$"), config(r"^submodule\..*\.url$")
    return {path: urls.get(name, "") for name, path in paths.items()}


def lag(git_dir: Path, pin: str, tip: str) -> tuple[str, str]:
    if pin == tip:
        return "CURRENT", "at the sibling's published main"
    ancestor = run(Path("."), ["merge-base", "--is-ancestor", pin, tip], git_dir=git_dir)[0]
    if ancestor == 0:
        count = out(Path("."), ["rev-list", "--count", f"{pin}..{tip}"], git_dir=git_dir)
        return "BEHIND", f"{count or '?'} commits behind the sibling's published main"
    descendant = run(Path("."), ["merge-base", "--is-ancestor", tip, pin], git_dir=git_dir)[0]
    if descendant == 0:
        count = out(Path("."), ["rev-list", "--count", f"{tip}..{pin}"], git_dir=git_dir)
        return "AHEAD", f"{count or '?'} commits the sibling's published main does not hold"
    return "DIVERGED", "neither the pin nor published main is an ancestor of the other"


def sweep_repo(repo: Path, *, want_lag: bool) -> tuple[list[Finding], str]:
    rev, label, error = published_revision(repo)
    if error:
        return [Finding(repo.name, "-", "-", "ERROR", "-", error)], ""

    findings: list[Finding] = []
    urls = declared_urls(repo, rev)
    for path, pin in gitlinks(repo, rev):
        url = resolve_url(urls.get(path, ""), repo)
        if not url:
            findings.append(Finding(
                repo.name, path, pin, "ERROR", "-",
                "no canonical URL in .gitmodules at the published revision"))
            continue
        if not is_first_party(url):
            findings.append(Finding(
                repo.name, path, pin, "THIRD-PARTY", "-",
                f"upstream mirror ({url}); lag is intentional, not swept"))
            continue
        git_dir = audit.submodule_git_dir(repo, path)
        if git_dir is None or not git_dir.is_dir():
            findings.append(Finding(
                repo.name, path, pin, "NOT-MATERIALIZED", "-",
                "submodule gitdir absent; cannot judge without an object store"))
            continue
        # One implementation of "what the canonical remote actually holds",
        # shared with the pin audit, so the two cannot disagree.
        view, error = audit.remote_authoritative_reachability(git_dir, url)
        if view is None:
            findings.append(Finding(repo.name, path, pin, "ERROR", "-", error))
            continue
        if pin in view.heads:
            status, detail = "PUBLISHED", "reachable from a branch on the canonical remote"
        elif pin in view.pins:
            status, detail = "ANCHORED", "on NO branch; only a durable refs/pins/* ref holds it"
        else:
            findings.append(Finding(
                repo.name, path, pin, "UNPUBLISHED", "-",
                f"on no branch and no pin ref of {url} — this superproject commit "
                "cannot be reproduced by anyone else. Push the sibling, or anchor "
                "it: scripts/audit_first_party_pins.py --anchor"))
            continue
        lag_status, lag_detail = "-", ""
        _, tip = default_head(view.sampled)
        if want_lag and tip:
            lag_status, lag_detail = lag(git_dir, pin, tip)
        findings.append(Finding(
            repo.name, path, pin, status, lag_status,
            lag_detail or detail))
    return findings, label


ORDER = {
    "ERROR": 0, "UNPUBLISHED": 1, "NOT-MATERIALIZED": 2, "ANCHORED": 3,
    "PUBLISHED": 4, "THIRD-PARTY": 5,
}
LAG_ORDER = {"DIVERGED": 0, "AHEAD": 1, "BEHIND": 2, "CURRENT": 3, "-": 4}


def constellation(repo: Path) -> tuple[int, str]:
    """The terminal-lag gate, run OFF the push path against what is published."""
    checker = repo / "scripts" / "check_dependency_cycle_anchor.py"
    if not checker.is_file():
        return -1, ""
    rev, _, error = published_revision(repo)
    if error:
        return 2, f"cannot select the published revision: {error}"
    done = subprocess.run(
        [sys.executable, str(checker), "--rev", rev, "--derive-when-receipt-absent"],
        capture_output=True, text=True, check=False, cwd=str(repo),
    )
    return done.returncode, (done.stdout + done.stderr).strip()


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--repo", action="append", default=[], type=Path,
        help="sweep this checkout only (repeatable); default is every "
        "submodule-bearing repo beside the Trust checkout",
    )
    parser.add_argument(
        "--fleet-root", type=Path, default=None,
        help="directory holding the fleet's checkouts (default: the Trust "
        "checkout's parent)",
    )
    parser.add_argument(
        "--constellation", action="store_true",
        help="also run scripts/check_dependency_cycle_anchor.py against each "
        "repo's PUBLISHED revision (+36 s for Trust; catches a terminal pin "
        "that lags its own dependency graph)",
    )
    parser.add_argument("--json", action="store_true", help="machine-readable rows")
    parser.add_argument(
        "--no-lag", action="store_true",
        help="reachability only; skip the behind/ahead comparison",
    )
    args = parser.parse_args()

    here = Path(__file__).resolve().parents[1]
    roots = [p.resolve() for p in args.repo] or [
        (args.fleet_root or here.parent).resolve()
    ]
    repos = superprojects(roots)
    if not repos:
        print("sweep: no submodule-bearing repository found", file=sys.stderr)
        return 2

    started = time.monotonic()
    findings: list[Finding] = []
    labels: dict[str, str] = {}
    for repo in repos:
        rows, label = sweep_repo(repo, want_lag=not args.no_lag)
        labels[repo.name] = label
        findings.extend(rows)

    constellation_rc = 0
    constellation_notes: list[tuple[str, int, str]] = []
    if args.constellation:
        for repo in repos:
            code, note = constellation(repo)
            if code < 0:
                continue
            constellation_notes.append((repo.name, code, note))
            if code != 0:
                constellation_rc = 1

    elapsed = time.monotonic() - started

    if args.json:
        print(json.dumps({
            "seconds": round(elapsed, 1),
            "repositories": {name: labels.get(name, "") for name in labels},
            "gitlinks": [f._asdict() for f in findings],
            "constellation": [
                {"repo": name, "exit": code, "report": note}
                for name, code, note in constellation_notes
            ],
        }, indent=2))
    else:
        current = None
        ordered = sorted(findings, key=lambda f: (
            f.repo, ORDER.get(f.status, 9), LAG_ORDER.get(f.lag, 9), f.path))
        for finding in ordered:
            if finding.repo != current:
                current = finding.repo
                print(f"\n{current}   [published {labels.get(current, '?')}]")
                print(f"  {'REACHABILITY':<16} {'LAG':<10} {'GITLINK':<28} PIN")
            print(f"  {finding.status:<16} {finding.lag:<10} {finding.path:<28} "
                  f"{finding.sha[:12]}  {finding.detail}")
        for name, code, note in constellation_notes:
            print(f"\n{name}   constellation: {'OK' if code == 0 else f'RED (exit {code})'}")
            for line in note.splitlines():
                print(f"    {line}")

        hard = [f for f in findings if f.hard]
        drift = [f for f in findings if f.drifted]
        print()
        print(f"swept {len(repos)} superproject(s), {len(findings)} gitlink(s) "
              f"in {elapsed:.1f}s — judged against each canonical remote's own ref "
              f"inventory, never against remote-tracking refs")
        if hard:
            print(f"HARD: {len(hard)} — "
                  + ", ".join(f"{f.repo}:{f.path} {f.status}" for f in hard))
        if drift:
            print(f"DRIFT (reported, not refused): {len(drift)} — "
                  + ", ".join(f"{f.repo}:{f.path} {f.lag}" for f in drift))
        if not hard and not drift:
            print("no pin drift and no unpublished gitlink")

    return 1 if any(f.hard for f in findings) or constellation_rc else 0


if __name__ == "__main__":
    raise SystemExit(main())
