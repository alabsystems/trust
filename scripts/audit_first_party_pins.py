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
#
# Before deleting non-main remote heads, use --prepare-head-prune.  That mode
# deliberately stops counting topic/archive heads as durable: every historical
# pin must be reachable from remote main, an exact refs/pins/* anchor, or (only
# with --retain-tags) a remote tag.  --anchor then publishes and verifies an
# exact refs/pins/<sha> ref for every pin that would otherwise become orphaned.
# The mode never deletes branches.

from __future__ import annotations

import argparse
import re
import subprocess
import sys
import tempfile
import time
from pathlib import Path
from typing import NamedTuple

ZERO = "0" * 40
HEX40 = re.compile(r"^[0-9a-f]{40}$")


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


def git_result(
    repo: Path,
    args: list[str],
    *,
    git_dir: Path | None = None,
    input_text: str | None = None,
) -> subprocess.CompletedProcess[str]:
    """Run Git without erasing the reason a fail-closed operation failed."""
    cmd = ["git"]
    if git_dir is not None:
        cmd += ["--git-dir", str(git_dir)]
    else:
        cmd += ["-C", str(repo)]
    return subprocess.run(
        cmd + args,
        input=input_text,
        capture_output=True,
        text=True,
        check=False,
    )


def submodule_paths(repo: Path) -> list[str]:
    """Gitlink paths declared by the indexed .gitmodules, in listed order."""
    out = git(repo, ["config", "-f", ".gitmodules", "--get-regexp", r"^submodule\..*\.path$"])
    return [line.split(" ", 1)[1] for line in out.splitlines() if " " in line]


def submodule_git_dir(repo: Path, path: str) -> Path | None:
    """Return Git's per-worktree object store for an initialized submodule.

    A linked worktree has a ``.git`` *file*, not a ``.git`` directory.  Asking
    Git to resolve ``modules/<path>`` therefore matters: spelling the location
    as ``repo/.git/modules/<path>`` silently classifies every initialized
    submodule in a linked worktree as absent.
    """
    resolved = git(
        repo,
        ["rev-parse", "--path-format=absolute", "--git-path", f"modules/{path}"],
    ).strip()
    return Path(resolved) if resolved else None


def _pins_from_log(out: str) -> set[str]:
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


def pins_for_checked(repo: Path, path: str) -> tuple[set[str] | None, str]:
    """Every historical gitlink value, retaining Git failures for authority."""
    done = git_result(
        repo,
        ["log", "--format=%H", "--raw", "--no-abbrev", "-m", "HEAD", "--", path],
    )
    if done.returncode != 0:
        return None, f"history walk failed: {_last_line(done.stderr)}"
    return _pins_from_log(done.stdout), ""


def pins_for(repo: Path, path: str) -> set[str]:
    """Compatibility wrapper for callers that do not need failure detail."""
    pins, _ = pins_for_checked(repo, path)
    return pins or set()


def remote_reachable_set(git_dir: Path) -> set[str]:
    """Commits reachable from the sibling's remote-tracking refs (one walk).

    ``refs/pins/*`` counts: an anchored pin is held by a real ref on the remote
    and is therefore gc-safe, even though no branch contains it.
    """
    out = git(Path("."), ["rev-list", "--remotes", "--glob=refs/pins"], git_dir=git_dir)
    return set(out.split())


def remote_reachable_set_checked(
    git_dir: Path,
) -> tuple[set[str] | None, str]:
    done = git_result(
        Path("."),
        ["rev-list", "--remotes", "--glob=refs/pins"],
        git_dir=git_dir,
    )
    if done.returncode != 0:
        return None, _git_failure("remote reachability walk failed", done)
    return set(done.stdout.split()), ""


class DurableReachability(NamedTuple):
    main: set[str]
    pins: set[str]
    tags: set[str]


def _git_failure(label: str, done: subprocess.CompletedProcess[str]) -> str:
    return f"{label}: {_last_line(done.stderr or done.stdout)}"


def _remote_refs(
    git_dir: Path, target: str, patterns: list[str]
) -> tuple[dict[str, str] | None, str]:
    done = git_result(
        Path("."),
        ["ls-remote", "--refs", target, *patterns],
        git_dir=git_dir,
    )
    if done.returncode != 0:
        return None, _git_failure("remote ref inventory failed", done)
    refs: dict[str, str] = {}
    for line in done.stdout.splitlines():
        fields = line.split()
        if len(fields) != 2 or not HEX40.fullmatch(fields[0]):
            return None, f"remote ref inventory returned malformed row: {line!r}"
        sha, ref = fields
        if ref in refs and refs[ref] != sha:
            return None, f"remote ref inventory returned duplicate ref: {ref}"
        refs[ref] = sha
    return refs, ""


def _reachable_from_tips(
    git_dir: Path, tips: set[str]
) -> tuple[set[str] | None, str]:
    if not tips:
        return set(), ""
    done = git_result(
        Path("."),
        ["rev-list", "--stdin"],
        git_dir=git_dir,
        input_text="".join(f"{sha}\n" for sha in sorted(tips)),
    )
    if done.returncode != 0:
        return None, _git_failure("durable reachability walk failed", done)
    return set(done.stdout.split()), ""


def refresh_remote_refs(git_dir: Path) -> str:
    """Refresh the ordinary audit's refs, failing instead of trusting staleness."""
    done = git_result(
        Path("."), ["fetch", "--quiet", "--prune", "origin"], git_dir=git_dir
    )
    if done.returncode != 0:
        return _git_failure("origin fetch failed", done)
    refs, error = _remote_refs(git_dir, "origin", ["refs/pins/*"])
    if refs is None:
        return error
    if refs:
        done = git_result(
            Path("."),
            ["fetch", "--quiet", "origin", PINS_REFSPEC],
            git_dir=git_dir,
        )
        if done.returncode != 0:
            return _git_failure("pin-ref fetch failed", done)
    return ""


def prepare_head_prune_reachability(
    git_dir: Path, url: str, *, retain_tags: bool
) -> tuple[DurableReachability | None, str]:
    """Fetch side heads, but count only refs that survive a head prune.

    The durable remote namespace is sampled both before and after fetching its
    objects.  A concurrent main/pin/tag rewrite therefore causes a retryable
    hard failure instead of mixing two remote states into a false proof.
    """
    if not url:
        return None, "canonical submodule URL is missing"

    heads = git_result(
        Path("."),
        [
            "fetch",
            "--quiet",
            "--prune",
            url,
            "+refs/heads/*:refs/remotes/origin/*",
        ],
        git_dir=git_dir,
    )
    if heads.returncode != 0:
        return None, _git_failure("remote-head fetch failed", heads)

    patterns = ["refs/heads/main", "refs/pins/*"]
    if retain_tags:
        patterns.append("refs/tags/*")
    before, error = _remote_refs(git_dir, url, patterns)
    if before is None:
        return None, error
    if "refs/heads/main" not in before:
        return None, "remote ref inventory has no refs/heads/main"

    pin_refs = {ref: sha for ref, sha in before.items() if ref.startswith("refs/pins/")}
    tag_refs = {ref: sha for ref, sha in before.items() if ref.startswith("refs/tags/")}
    if pin_refs:
        done = git_result(
            Path("."),
            ["fetch", "--quiet", url, PINS_REFSPEC],
            git_dir=git_dir,
        )
        if done.returncode != 0:
            return None, _git_failure("pin-ref fetch failed", done)
    if tag_refs:
        done = git_result(
            Path("."),
            ["fetch", "--quiet", url, "+refs/tags/*:refs/tags/*"],
            git_dir=git_dir,
        )
        if done.returncode != 0:
            return None, _git_failure("tag fetch failed", done)

    after, error = _remote_refs(git_dir, url, patterns)
    if after is None:
        return None, error
    if before != after:
        return None, "durable remote refs changed during audit; retry from a stable remote"

    main, error = _reachable_from_tips(git_dir, {after["refs/heads/main"]})
    if main is None:
        return None, error
    pin_tips = {sha for ref, sha in after.items() if ref.startswith("refs/pins/")}
    pins, error = _reachable_from_tips(git_dir, pin_tips)
    if pins is None:
        return None, error
    tag_tips = {sha for ref, sha in after.items() if ref.startswith("refs/tags/")}
    tags, error = _reachable_from_tips(git_dir, tag_tips)
    if tags is None:
        return None, error
    return DurableReachability(main, pins, tags), ""


SAFE_MAIN, SAFE_PIN, SAFE_TAG, NEEDS_ANCHOR = (
    "SAFE_MAIN",
    "SAFE_PIN",
    "SAFE_TAG",
    "NEEDS_ANCHOR",
)


def head_prune_status(sha: str, reachable: DurableReachability) -> str:
    if sha in reachable.main:
        return SAFE_MAIN
    if sha in reachable.pins:
        return SAFE_PIN
    if sha in reachable.tags:
        return SAFE_TAG
    return NEEDS_ANCHOR


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


def remote_pin_is_exact(git_dir: Path, url: str, sha: str) -> tuple[bool, str]:
    """Prove the canonical remote exposes exactly refs/pins/<sha> -> <sha>."""
    ref = f"refs/pins/{sha}"
    refs, error = _remote_refs(git_dir, url, [ref])
    if refs is None:
        return False, f"post-push verification failed: {error}"
    if refs != {ref: sha}:
        actual = refs.get(ref, "absent")
        return False, f"post-push verification mismatch: {ref} -> {actual}"
    return True, ""


def anchor(git_dir: Path, url: str, sha: str) -> tuple[bool, str]:
    """Give an unreferenced-but-servable pin a permanent ref in the sibling.

    An ORPHAN pin resolves only because forges serve unreferenced objects; a
    server-side gc may stop. Pushing refs/pins/<sha> makes the commit reachable,
    so the pin is guaranteed for as long as the sibling repo exists. The ref is
    additive and touches no branch.
    """
    if not url:
        return False, "cannot anchor (canonical submodule URL is missing)"
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
            return False, f"cannot anchor (fetch failed): {_last_line(got.stderr)}"
    pushed_via = ""
    for target in (url, _ssh_url(url)):
        if not target:
            continue
        done = subprocess.run(
            ["git", "--git-dir", str(git_dir), "push", "-q", target,
             f"{sha}:refs/pins/{sha}"],
            capture_output=True, text=True, check=False,
        )
        if done.returncode == 0:
            pushed_via = "anchored" if target == url else "anchored (ssh)"
            break
        # GitHub refuses OAuth-token pushes that carry .github/workflows
        # changes unless the token holds the `workflow` scope. SSH keys are
        # not scope-limited, so retry there rather than reporting a failure
        # that has nothing to do with the pin.
        if "workflow" not in done.stderr:
            return False, f"push failed: {_last_line(done.stderr)}"
    if not pushed_via:
        return False, f"push failed: {_last_line(done.stderr)}"

    verified, detail = remote_pin_is_exact(git_dir, url, sha)
    if not verified:
        return False, detail

    # Keep the local proof namespace synchronized too.  The exact remote
    # ls-remote check above is the authority; this fetch makes the subsequent
    # closure recomputation use the same object/ref locally.
    ref = f"refs/pins/{sha}"
    fetched = git_result(
        Path("."),
        ["fetch", "--quiet", "--no-tags", url, f"+{ref}:{ref}"],
        git_dir=git_dir,
    )
    if fetched.returncode != 0:
        return False, _git_failure("post-push pin-ref fetch failed", fetched)
    local = git_result(Path("."), ["rev-parse", "--verify", ref], git_dir=git_dir)
    if local.returncode != 0 or local.stdout.strip() != sha:
        return False, f"post-push local pin-ref mismatch: {ref}"
    closure, error = _reachable_from_tips(git_dir, {sha})
    if closure is None or sha not in closure:
        return False, error or "post-push durable closure omitted anchored commit"
    return True, pushed_via


def _commit_present(git_dir: Path, sha: str) -> bool:
    return git_result(
        Path("."), ["cat-file", "-e", f"{sha}^{{commit}}"], git_dir=git_dir
    ).returncode == 0


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--fetch", action="store_true", help="refresh remote-tracking refs first")
    parser.add_argument(
        "--probe",
        action="store_true",
        help="ask remotes to serve MISSING/ORPHAN pins",
    )
    parser.add_argument("--anchor", action="store_true",
                        help="push refs/pins/<sha> for ORPHAN pins so a gc cannot reap them")
    parser.add_argument(
        "--prepare-head-prune",
        action="store_true",
        help="fail unless every historical pin survives deletion of every remote head "
        "except main; implies checked fetch and probes for absent candidates",
    )
    parser.add_argument(
        "--retain-tags",
        action="store_true",
        help="with --prepare-head-prune, count remote tags as durable retained refs",
    )
    parser.add_argument("--repo", default=".", help="superproject path")
    args = parser.parse_args()

    if args.retain_tags and not args.prepare_head_prune:
        parser.error("--retain-tags requires --prepare-head-prune")

    repo = Path(args.repo).resolve()
    paths = submodule_paths(repo)
    if not paths:
        print("no submodules declared in .gitmodules", file=sys.stderr)
        return 2

    unrecoverable: list[tuple[str, str]] = []
    fragile: list[tuple[str, str]] = []
    indeterminate_all: list[tuple[str, str]] = []
    operational_failures: list[tuple[str, str]] = []
    anchor_failures: list[tuple[str, str, str]] = []
    anchored_count = 0

    for path in paths:
        git_dir = submodule_git_dir(repo, path)
        if git_dir is None or not git_dir.is_dir():
            detail = "gitdir absent — not materialized"
            if args.prepare_head_prune:
                print(f"{path:<22} ERROR {detail}")
                operational_failures.append((path, detail))
            else:
                print(f"{path:<22} {detail}, skipped")
            continue
        url = remote_url(repo, path)
        pins, error = pins_for_checked(repo, path)
        if pins is None:
            print(f"{path:<22} ERROR {error}")
            operational_failures.append((path, error))
            continue

        if args.prepare_head_prune:
            durable, error = prepare_head_prune_reachability(
                git_dir, url, retain_tags=args.retain_tags
            )
            if durable is None:
                print(f"{path:<22} ERROR {error}")
                operational_failures.append((path, error))
                continue

            needs_anchor: list[str] = []
            initially_served: list[str] = []
            initially_missing: list[str] = []
            initially_indeterminate: list[str] = []
            for sha in sorted(pins):
                status = head_prune_status(sha, durable)
                if status != NEEDS_ANCHOR:
                    continue
                if _commit_present(git_dir, sha):
                    needs_anchor.append(sha)
                else:
                    verdict = probe(url, sha)
                    time.sleep(0.5)
                    if verdict == SERVED:
                        needs_anchor.append(sha)
                        initially_served.append(sha)
                    elif verdict == REFUSED:
                        initially_missing.append(sha)
                    else:
                        initially_indeterminate.append(sha)

            anchor_notes: dict[str, str] = {}
            for sha in needs_anchor:
                if not args.anchor:
                    continue
                anchored, detail = anchor(git_dir, url, sha)
                anchor_notes[sha] = detail
                if anchored:
                    anchored_count += 1
                else:
                    anchor_failures.append((path, sha, detail))

            # Re-sample the complete durable namespace after every potential
            # push and reclassify every historical pin.  Per-pin verification
            # is necessary but insufficient: main or a pre-existing pin ref
            # may have been rewritten while the anchor loop was running.
            final_durable, error = prepare_head_prune_reachability(
                git_dir, url, retain_tags=args.retain_tags
            )
            if final_durable is None:
                print(f"{path:<22} ERROR final durable revalidation: {error}")
                operational_failures.append(
                    (path, f"final durable revalidation: {error}")
                )
                continue

            counts = {SAFE_MAIN: 0, SAFE_PIN: 0, SAFE_TAG: 0}
            final_unsafe: list[str] = []
            final_status: dict[str, str] = {}
            for sha in sorted(pins):
                status = head_prune_status(sha, final_durable)
                final_status[sha] = status
                if status == NEEDS_ANCHOR:
                    final_unsafe.append(sha)
                else:
                    counts[status] += 1

            missing = [sha for sha in final_unsafe if sha in initially_missing]
            indeterminate = [
                sha for sha in final_unsafe if sha in initially_indeterminate
            ]
            remaining = [
                sha
                for sha in final_unsafe
                if sha not in initially_missing and sha not in initially_indeterminate
            ]
            # A pin newly made unsafe by a concurrent durable-ref rewrite may
            # also have disappeared from the local object store.  Do not call
            # it anchorable from stale evidence.
            final_race_unknown = [
                sha
                for sha in remaining
                if sha not in initially_served and not _commit_present(git_dir, sha)
            ]
            if final_race_unknown:
                remaining = [sha for sha in remaining if sha not in final_race_unknown]
                indeterminate.extend(final_race_unknown)

            print(
                f"{path:<22} {len(pins):>4} pins   "
                f"SAFE_MAIN={counts[SAFE_MAIN]:<4} "
                f"SAFE_PIN={counts[SAFE_PIN]:<4} "
                f"SAFE_TAG={counts[SAFE_TAG]:<4} "
                f"NEEDS_ANCHOR={len(remaining):<3} "
                f"MISSING={len(missing):<3} UNKNOWN={len(indeterminate)}  (pre-prune)"
            )
            for sha in remaining:
                suffix = f"  → {anchor_notes[sha]}" if sha in anchor_notes else ""
                print(f"    NEEDS_ANCHOR {sha}{suffix}")
                fragile.append((path, sha))
            for sha, detail in anchor_notes.items():
                if sha not in final_unsafe:
                    print(
                        f"    {final_status[sha]:<12} {sha}  → {detail}; "
                        "exact remote ref verified"
                    )
            for sha in missing:
                print(f"    MISSING      {sha}")
                unrecoverable.append((path, sha))
            for sha in indeterminate:
                print(f"    UNKNOWN      {sha}  (probe inconclusive — re-run)")
                indeterminate_all.append((path, sha))
            continue

        if args.fetch:
            error = refresh_remote_refs(git_dir)
            if error:
                print(f"{path:<22} ERROR {error}")
                operational_failures.append((path, error))
                continue

        reachable, error = remote_reachable_set_checked(git_dir)
        if reachable is None:
            print(f"{path:<22} ERROR {error}")
            operational_failures.append((path, error))
            continue

        missing, orphan = [], []
        for sha in sorted(pins):
            if sha in reachable:
                continue
            # cat-file -e is silent on success, so check the status, not stdout.
            present = _commit_present(git_dir, sha)
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
            suffix = ""
            anchored = False
            if args.anchor:
                anchored, detail = anchor(git_dir, url, sha)
                suffix = f"  → {detail}"
                if anchored:
                    anchored_count += 1
                else:
                    anchor_failures.append((path, sha, detail))
            print(f"    ORPHAN  {sha}{suffix}")
            if not anchored:
                fragile.append((path, sha))
        for sha in indeterminate:
            print(f"    UNKNOWN {sha}  (probe inconclusive — re-run)")
            indeterminate_all.append((path, sha))

    print()
    if operational_failures:
        print(f"AUDIT OPERATION FAILURES: {len(operational_failures)}")
    if anchor_failures:
        print(f"ANCHOR FAILURES: {len(anchor_failures)}")
    if unrecoverable:
        print(f"UNRECOVERABLE pins: {len(unrecoverable)} "
              f"(superproject commits naming them cannot be reproduced)")
    if indeterminate_all:
        print(f"INDETERMINATE probes: {len(indeterminate_all)} — no safety claim is possible")
    if fragile:
        if args.prepare_head_prune:
            print(f"NEEDS ANCHOR before head prune: {len(fragile)}")
        else:
            print(f"FRAGILE pins: {len(fragile)} — served by SHA but on no branch; "
                  f"anchor them with a ref in the sibling repo")
    if anchored_count:
        print(f"ANCHORED and exact-remote-verified: {anchored_count}")

    hard_failure = bool(
        operational_failures
        or anchor_failures
        or unrecoverable
        or indeterminate_all
        or (args.prepare_head_prune and fragile)
    )
    if args.prepare_head_prune and not hard_failure:
        retained = "remote main + refs/pins/*"
        if args.retain_tags:
            retained += " + remote tags"
        print(f"HEAD-PRUNE READY: every historical pin is reachable from {retained}")
        print("no branches were deleted; delete non-main heads separately with exact SHA leases")
    elif not hard_failure and not fragile:
        print("every first-party pin is reachable from a remote branch")
    return 1 if hard_failure else 0


if __name__ == "__main__":
    raise SystemExit(main())
