#!/usr/bin/env python3
"""Fail-closed check for parent-pinned submodule commit reachability.

This release gate verifies that each commit recorded by the parent checkout's
submodule gitlinks is contained in at least one branch or durable
``refs/pins/<sha>`` archival ref that the submodule's remote PUBLISHES, read
with ``git ls-remote`` during this run. If a parent points at a local-only
submodule commit, a fresh recursive clone may fail to reproduce that pin; this
script reports that condition and exits 1. It never pushes and never writes a
ref; exit 2 is COULD NOT RUN (a remote could not be read), never a pass.

THE REMOTE IS READ, NOT THIS STORE'S MEMORY OF IT (2026-10-15)
--------------------------------------------------------------
Until 2026-10-15 the predicate was ``for-each-ref --contains <sha>
refs/remotes refs/pins`` in the local store. Those refs are only as fresh as
the store's last fetch, so a pin newer than a stale ``origin/main`` read as
unpublished: four pushes to Trust main from ~/trust-b1 went RED on
2026-10-14/15 while the remote served every pin, and the remedy each time was
a fetch that WRITES refs in module stores several worktrees share. It was also
wrong the other way: a stale remote-tracking ref for a branch the forge had
deleted, or a refs/pins/<sha> created locally and never pushed, made a pin
"durable" that no fresh clone could fetch.

Now the remote's own inventory (heads and refs/pins, one ``ls-remote`` per
remote per run) is the authority, and ancestry is walked from THOSE tips. When
that needs objects this store lacks (the pinned commit, or a remote tip it may
sit under), they are fetched BY SHA with no destination --- no ref and no
FETCH_HEAD is written. A remote that cannot be read is COULD NOT RUN
(``remote-unreadable``), never a pass and never a finding. The shared
mechanism is ``scripts/lib/remote_tips.py``; the decision is
docs/DECISION_QUEUE.md "HOOKS-PIN-REMOTE-TIPS-1".

``refs/pins/*`` is the repository's branch-free retention namespace. The
historical-pin audit fetches that namespace explicitly and anchors orphaned
commits there, so a server-side garbage collection cannot destroy a published
superproject pin. Suggesting that an old detached commit be pushed to ``main``
would overwrite the release branch and is never an acceptable repair.

WHICH PINS THIS JUDGES, AND WHY THE OLD ANSWER WAS BIASED SAFE
--------------------------------------------------------------
Until 2026-08-30 the subject was always ``git submodule status --cached
--recursive`` --- this clone's INDEX. That is the wrong subject for a push, and
wrong in a direction that manufactures a green: the predicate is "the pinned
commit is contained in some fetched remote ref", and an OLDER pin is
systematically MORE likely to satisfy it, because time has given it branches.
A clone that is behind therefore audits a systematically SAFER pin set than the
one it is about to publish. Measured on this checkout that day: HEAD was 41
commits behind ``origin/main`` and 8 of 9 first-party gitlinks differed between
the two, so the lane audited 12 pins --- the wrong 12 --- and printed PASS.
The stale ``ay`` pin was on three refs including ``main``; the published one
was on a single deletable topic branch.

So the subject is now parameterised by revision, and ``--push-context`` points
it at what is actually being published. See ``select_subjects``.

A PUSH PUBLISHES EVERY COMMIT IT INTRODUCES, NOT ONLY ITS TIP
-------------------------------------------------------------
Until 2026-09-27 ``--push-context`` judged only the tip tree of each pushed
ref. A push publishes every commit in ``<remote sha>..<local sha>``, so a
range whose middle commit pins a local-only submodule commit and whose last
commit moves the pin back passed, while the published history kept a
superproject commit no one else can reproduce --- and a consumer's plain
``git pull`` (on-demand submodule recursion) then aborts fetching it. That is
the mechanism behind the unrecoverable pins in docs/first-party-pin-ledger.md.
The subject is now each pushed TIP TREE (every pin, as before) PLUS every
gitlink that any commit the push introduces (one not already on the old
remote tip or a fetched remote-tracking ref) adds or changes, merges included.
A pin only an introduced commit names, at a path with no worktree (renamed or
removed later in the same push), is judged in the object store that holds
it. See ``introduced_commits`` and ``changed_gitlinks``.

NESTED PINS COME FROM THE PINNED TREE, NOT THE SUBMODULE WORKTREE
-----------------------------------------------------------------
``submodule status --recursive`` can only descend into a submodule that is
materialized, so an uninitialized module takes its whole nested subtree out of
the work set. This reads every gitlink out of the PINNED tree instead --- for
children, out of the submodule's own object store via ``--git-dir``, which
survives a ``submodule deinit`` --- so the work set is a property of the
revision under audit and not of what happens to be checked out.

Git keys that store by submodule NAME (``modules/<name>``), not by path, and a
module registered over an existing clone keeps an embedded ``.git`` directory
with no ``modules/`` entry at all. So the store is looked up by name from the
judged tree's ``.gitmodules``, then from the worktree's real git dir, then by
path, with the common Git directory's module stores as fallbacks for linked
worktrees. The first candidate that HOLDS the pinned commit is read (a commit id
names its tree, so any store holding it gives the same answer). When no store
can be found, or none can list the pinned tree, the pin is REFUSED
(``nested-store-unresolved`` / ``nested-pins-unreadable``) rather than
silently leaving its nested subtree out of the work set.

ONE ANCESTRY READ PER REF HELD A PUSH FOR 1H41M (2026-11-13)
-----------------------------------------------------------
Each (pin, remote ref) question was its own ``agh repo commit-ancestry``
process, asked serially over the remote's whole inventory until one ref
contained the pin, with no total bound: a one-commit docs push waited 1h41m.
Now (``rt.RemoteTips.judge_many``) the pins of a store are asked against main
in one read and against the other refs in reads of up to 128 questions (Agh's
cap); the store itself answers what it proves; answers are remembered by
commit ids under ``<git common dir>/trust-land/commit-ancestry/<FORMAT>``
(immutable; ``rt.AncestryMemory.FORMAT`` names the answer sources' version and
Agh's native reply contract, so a fix to a source or a new contract retires the
old answers, see docs/DECISION_QUEUE.md REACH-MEMO-1; check_ir_cohort.py reads
the same answers). The remote's refs, and whether it serves a commit, are still
read every run: they can change. Every remote read shares one bound
(``--time-bound``), and a transient failure is retried inside it; past it a
pin is COULD NOT RUN (exit 2) with the command to rerun, never a pass.

A ZERO-SIZE WORK SET IS A FAILURE
---------------------------------
``AuditResult.ok`` was ``not self.failed``, so auditing nothing printed the
full PASS banner at exit 0. A zero delta means *never ran* before it means
*returned true*; an empty work set is now a refusal that names the subject.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import shlex
import subprocess
import sys
import tempfile
from dataclasses import dataclass, replace
from pathlib import Path
from typing import Iterable, Mapping, Optional, Sequence


REPO_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(Path(__file__).resolve().parent / "lib"))

import remote_tips as rt  # noqa: E402  (scripts/lib/remote_tips.py)

DEFAULT_REMOTE = "origin"
# A status in this set means the pin was NOT JUDGED: the remote, or an object
# it named, could not be read. It blocks like a failure, and exits 2, not 1.
COULD_NOT_RUN_STATUSES = frozenset({"remote-unreadable"})
GITLINK_MODE = "160000"
NULL_SHA = "0" * 40
SHA_RE = re.compile(r"^[0-9a-fA-F]{40}$")

# A manifest command string is fixed and receives no stdin, so scripts/hooks/pre-push
# exports the ref lines git handed it and the SAME row text runs in both runners.
# This mirrors fast.revert-rationale / fast.measurement-provenance /
# fast.pin-regression / fast.dependency-constellation.
PUSH_REFS_ENV = "TRUST_PUSHED_REFS"
# The whole row's remote reads share this bound (scripts/lib/remote_tips.py
# RemoteTips.time_bound). Past it a pin is COULD NOT RUN (exit 2): until
# 2026-11-13 there was none, and the row once waited 1h41m on serial ancestry
# reads and once 37 minutes on a GitHub rate limit.
DEFAULT_TIME_BOUND_S = 900.0


@dataclass(frozen=True)
class SubmodulePin:
    path: str
    sha: str
    state: str
    # Why this pin's own nested gitlinks could not be enumerated ("" when they
    # were). A pin whose subtree is unknown is never judged complete.
    nested_status: str = ""
    nested_detail: str = ""
    # The object store that holds ``sha`` (None when none was found).
    store: Optional[Path] = None


@dataclass(frozen=True)
class PinCheck:
    path: str
    sha: str
    status: str
    remote_refs: tuple[str, ...] = ()
    remote: str = DEFAULT_REMOTE
    remote_url: str = ""
    publish_ref: str = ""
    suggested_command: str = ""
    detail: str = ""
    named_by: tuple[str, ...] = ()

    @property
    def ok(self) -> bool:
        return self.status == "reachable"

    @property
    def could_not_run(self) -> bool:
        return self.status in COULD_NOT_RUN_STATUSES

    def as_dict(self) -> dict[str, object]:
        return {
            "path": self.path,
            "sha": self.sha,
            "status": self.status,
            "remote_refs": list(self.remote_refs),
            "remote": self.remote,
            "remote_url": self.remote_url,
            "publish_ref": self.publish_ref,
            "suggested_command": self.suggested_command,
            "detail": self.detail,
            "named_by": list(self.named_by),
        }


@dataclass(frozen=True)
class AuditResult:
    repo_root: Path
    pins: tuple[PinCheck, ...]
    source: str

    @property
    def failed(self) -> tuple[PinCheck, ...]:
        return tuple(check for check in self.pins if not check.ok)

    @property
    def empty(self) -> bool:
        """No pin was judged at all.

        Fail closed. ``ok`` used to be ``not self.failed``, which is vacuously
        true over an empty work set, so a subject that yielded nothing printed
        the full PASS banner at exit 0. Every way the work set can silently
        shrink --- a deinit'd module, a revision whose tree has no gitlink, a
        misread subject --- reaches this predicate.
        """
        return not self.pins

    @property
    def ok(self) -> bool:
        return not self.failed and not self.empty

    @property
    def unjudged(self) -> bool:
        """Not ok ONLY because a remote could not be read: COULD NOT RUN.

        One definite finding beside an unreadable remote is still a finding,
        so this is false then and the exit is 1.
        """
        failed = self.failed
        return bool(failed) and all(check.could_not_run for check in failed)

    @property
    def exit_code(self) -> int:
        if self.ok:
            return 0
        return 2 if self.unjudged else 1

    def as_dict(self) -> dict[str, object]:
        failed = self.failed
        return {
            "repo_root": str(self.repo_root),
            "source": self.source,
            "summary": {
                "checked": len(self.pins),
                "reachable": len(self.pins) - len(failed),
                "failed": len(failed),
                "could_not_run": sum(1 for check in failed if check.could_not_run),
                "empty_work_set": self.empty,
            },
            "pins": [pin.as_dict() for pin in self.pins],
        }


class GitError(RuntimeError):
    pass


def run_git(
    repo: Path,
    args: Sequence[str],
    *,
    check: bool = True,
    extra_config: Sequence[str] = (),
    input_text: Optional[str] = None,
) -> subprocess.CompletedProcess[str]:
    command = ["git", *extra_config, *args]
    completed = subprocess.run(
        command,
        cwd=repo,
        text=True,
        input=input_text,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    if check and completed.returncode != 0:
        rendered = " ".join(shlex.quote(part) for part in command)
        raise GitError(
            f"{rendered} failed in {repo}: {completed.stderr.strip() or completed.stdout.strip()}"
        )
    return completed


def run_git_dir(
    git_dir: Path, args: Sequence[str], *, check: bool = True
) -> subprocess.CompletedProcess[str]:
    """Run Git against a bare object store.

    Children are read through ``--git-dir`` rather than ``-C <worktree>`` so a
    ``submodule deinit`` --- which removes the worktree and leaves
    ``modules/<name>`` intact --- cannot silently remove that module's nested
    pins from the work set.
    """
    command = ["git", "--git-dir", str(git_dir), *args]
    completed = subprocess.run(
        command, text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE
    )
    if check and completed.returncode != 0:
        rendered = " ".join(shlex.quote(part) for part in command)
        raise GitError(
            f"{rendered} failed: {completed.stderr.strip() or completed.stdout.strip()}"
        )
    return completed


def _parse_gitlinks(output: str, *, sha_field: int, origin: str) -> list[tuple[str, str]]:
    """(path, sha) for every mode-160000 row of a NUL-separated Git listing.

    ``ls-tree -z`` rows are ``<mode> <type> <object>\\t<path>`` and ``ls-files
    -s -z`` rows are ``<mode> <object> <stage>\\t<path>``; ``sha_field`` picks
    the object column. ``-z`` matters beyond tidiness: without it Git QUOTES
    any path holding a space or a non-ASCII byte, and a quoted path silently
    names a submodule that does not exist.
    """
    entries: list[tuple[str, str]] = []
    for record in output.split("\0"):
        if not record.strip():
            continue
        head, sep, path = record.partition("\t")
        if not sep:
            raise GitError(f"could not parse gitlink row from {origin}: {record!r}")
        fields = head.split()
        if len(fields) <= sha_field:
            raise GitError(f"could not parse gitlink row from {origin}: {record!r}")
        if fields[0] != GITLINK_MODE:
            continue
        sha = fields[sha_field]
        if not SHA_RE.match(sha):
            raise GitError(f"could not parse gitlink sha from {origin}: {record!r}")
        entries.append((path, sha.lower()))
    return entries


def index_gitlinks(repo_root: Path) -> list[tuple[str, str]]:
    """Gitlinks staged in this checkout's index.

    ``git ls-files -s`` is deliberate: this clone sets ``diff.ignoreSubmodules
    = all`` and ``submodule.<name>.ignore = all``, under which ``git status``
    and ``git diff --cached`` omit submodule rows entirely. ``ls-files -s`` is
    the readout that ignores that configuration.
    """
    listed = run_git(repo_root, ["ls-files", "-s", "-z"])
    return _parse_gitlinks(listed.stdout, sha_field=1, origin="the index")


def tree_gitlinks(repo_root: Path, revision: str) -> list[tuple[str, str]]:
    listed = run_git(repo_root, ["ls-tree", "-r", "-z", "--full-tree", revision])
    return _parse_gitlinks(listed.stdout, sha_field=2, origin=f"tree {revision}")


def gitmodules_names(
    completed: subprocess.CompletedProcess[str],
) -> dict[str, list[str]]:
    """path -> submodule NAME(s), from ``git config -z --blob <.gitmodules>``.

    A non-zero exit (no ``.gitmodules`` in that tree, or no ``path`` key) is an
    empty mapping, and that is safe here rather than fail-open: a name only
    proposes a CANDIDATE store. Whether a store is used is decided by whether
    it holds the pinned commit, and a pin with no usable store is refused by
    ``list_nested``.
    """
    names: dict[str, list[str]] = {}
    if completed.returncode != 0:
        return names
    prefix, suffix = "submodule.", ".path"
    for record in completed.stdout.split("\0"):
        key, sep, value = record.partition("\n")
        if not sep or not key.startswith(prefix) or not key.endswith(suffix):
            continue
        name = key[len(prefix) : -len(suffix)]
        if name:
            names.setdefault(value, []).append(name)
    return names


def gitmodules_query(blob: str) -> list[str]:
    return ["config", "-z", "--blob", blob, "--get-regexp", r"^submodule\..*\.path$"]


def top_level_names(repo_root: Path, subject: "Subject") -> dict[str, list[str]]:
    blob = ":.gitmodules" if subject.kind == "index" else f"{subject.rev}:.gitmodules"
    return gitmodules_names(run_git(repo_root, gitmodules_query(blob), check=False))


def nested_names(store: Path, sha: str) -> dict[str, list[str]]:
    query = gitmodules_query(f"{sha}:.gitmodules")
    return gitmodules_names(run_git_dir(store, query, check=False))


def git_path(repo_root: Path, relative: str) -> Optional[Path]:
    """Resolve ``$GIT_DIR/<relative>`` the way Git does.

    A linked worktree has a ``.git`` FILE, so asking Git to resolve
    ``modules/<name>`` matters --- spelling it ``repo/.git/modules/<name>``
    classifies every submodule in a linked worktree as absent.
    """
    resolved = run_git(
        repo_root,
        ["rev-parse", "--path-format=absolute", "--git-path", relative],
        check=False,
    )
    if resolved.returncode != 0:
        return None
    text = resolved.stdout.strip()
    return Path(text) if text else None


def git_common_dir(repo: Path, *, is_store: bool = False) -> Optional[Path]:
    """Ask Git for the common directory of a worktree or selected object store.

    A linked worktree's ``--git-path modules/...`` is private to that worktree,
    while an existing submodule clone may live in the common directory.
    """
    runner = run_git_dir if is_store else run_git
    resolved = runner(
        repo, ["rev-parse", "--path-format=absolute", "--git-common-dir"], check=False
    )
    text = resolved.stdout.strip()
    return Path(text) if resolved.returncode == 0 and text else None


def worktree_git_dir(repo_root: Path, path: str) -> Optional[Path]:
    """The real git dir of a materialized submodule worktree, absorbed or not.

    Only when ``<path>`` is itself a worktree TOPLEVEL: an empty directory
    inside the superproject would otherwise answer with the superproject's
    own git dir.
    """
    worktree = repo_root / path
    if not worktree.is_dir() or not git_dir_exists(worktree):
        return None
    resolved = run_git(worktree, ["rev-parse", "--absolute-git-dir"], check=False)
    text = resolved.stdout.strip()
    if resolved.returncode != 0 or not text:
        return None
    return Path(text)


@dataclass(frozen=True)
class NestedListing:
    """The gitlinks a pinned commit's own tree carries, or why they are unknown."""

    store: Optional[Path]
    gitlinks: tuple[tuple[str, str], ...]
    status: str = ""  # "" | "nested-store-unresolved" | "nested-pins-unreadable"
    detail: str = ""


def _existing_stores(candidates: Sequence[Optional[Path]]) -> list[Path]:
    stores: list[Path] = []
    for candidate in candidates:
        if candidate is not None and candidate.is_dir() and candidate not in stores:
            stores.append(candidate)
    return stores


def _fetch_store(
    stores: Sequence[Path], tips: "rt.RemoteTips"
) -> Optional[Path]:
    """The first candidate store that is a repository with a remote to ask."""
    for store in stores:
        remote = tips.remote(store)
        if remote.git_dir is not None and not remote.error:
            return store
    return None


def _list_from(store: Path, sha: str) -> Optional[NestedListing]:
    """``sha``'s gitlinks from ``store``, or None when the store lacks it."""
    present = run_git_dir(store, ["cat-file", "-e", f"{sha}^{{commit}}"], check=False)
    if present.returncode != 0:
        return None
    listed = run_git_dir(store, ["ls-tree", "-r", "-z", "--full-tree", sha], check=False)
    if listed.returncode != 0:
        return NestedListing(
            store=store,
            gitlinks=(),
            status="nested-pins-unreadable",
            detail=(
                f"git ls-tree {sha} failed in {store}: "
                f"{listed.stderr.strip() or listed.stdout.strip()}"
            ),
        )
    return NestedListing(
        store=store,
        gitlinks=tuple(_parse_gitlinks(listed.stdout, sha_field=2, origin=f"tree {sha}")),
    )


def list_nested(
    path: str,
    sha: str,
    candidates: Sequence[Optional[Path]],
    cache: dict[tuple[str, str, tuple[str, ...]], NestedListing],
    tips: Optional["rt.RemoteTips"] = None,
) -> NestedListing:
    """Read ``sha``'s gitlinks from the first candidate store that holds it.

    Every way this can come up empty is a REFUSAL, never ``[]``: this used to
    treat an unlocatable store and a failing ``ls-tree`` as "no nested pins",
    with a comment claiming check_pin would refuse the pin instead. check_pin
    probes the WORKTREE, which is a different repository whenever the store
    was located by the wrong key, so a whole nested subtree left the work set
    under a PASS.

    When no store holds the commit and ``tips`` is given, the commit is
    fetched by sha into the first store that has a remote (no ref written)
    and read from there. A store that merely has not fetched is not a
    finding; a remote that will not serve the commit still is, and a remote
    that cannot be read is ``remote-unreadable`` (COULD NOT RUN).
    """
    stores = _existing_stores(candidates)
    key = (path, sha, tuple(str(store) for store in stores))
    if key in cache:
        return cache[key]
    listing: Optional[NestedListing] = None
    if not stores:
        tried = ", ".join(str(c) for c in candidates if c is not None) or "none"
        listing = NestedListing(
            store=None,
            gitlinks=(),
            status="nested-store-unresolved",
            detail=(
                f"no object store was found for {path} (tried: {tried}), so the "
                "gitlinks its pinned commit carries were not enumerated"
            ),
        )
    for store in stores:
        if listing is not None:
            break
        listing = _list_from(store, sha)
    fetch_note = ""
    if listing is None and tips is not None:
        target = _fetch_store(stores, tips)
        if target is not None:
            failed = tips.ensure(target, [sha])
            if not failed:
                listing = _list_from(target, sha)
            else:
                kind, why = failed[sha]
                if kind == "error":
                    listing = NestedListing(
                        store=None,
                        gitlinks=(),
                        status="remote-unreadable",
                        detail=(
                            f"no local store holds {sha} and it could not be fetched, so "
                            f"the gitlinks it pins were not enumerated: {why}"
                        ),
                    )
                else:
                    fetch_note = f"; and its remote does not serve it either ({why})"
    if listing is None:
        listing = NestedListing(
            store=None,
            gitlinks=(),
            status="nested-pins-unreadable",
            detail=(
                f"none of the object stores found for {path} "
                f"({', '.join(str(store) for store in stores)}) holds {sha}, so "
                f"the gitlinks it pins were not enumerated{fetch_note}"
            ),
        )
    cache[key] = listing
    return listing


def collect_pins(
    repo_root: Path,
    subject: "Subject",
    cache: Optional[dict[tuple[str, str, tuple[str, ...]], NestedListing]] = None,
    tips: Optional["rt.RemoteTips"] = None,
) -> tuple[SubmodulePin, ...]:
    """Every gitlink the subject names, recursively, read from PINNED trees.

    Each pin's children are read from the store that holds the pinned commit,
    located by NAME first --- ``modules/<name>`` from the judged tree's
    ``.gitmodules``, Git's real on-disk key --- then by the worktree's own git
    dir, then by path. Common-directory name/path fallbacks cover existing
    stores shared with another linked worktree. A pin whose subtree cannot be
    enumerated carries
    ``nested_status`` so ``audit`` refuses it. A cycle cannot spin: a path is
    expanded at most once per subject.

    With ``tips``, the top-level pinned commits a store lacks are fetched
    first, one fetch per store and all stores at once, together with each
    remote's main tip (the containment check's first question).
    """
    listings = {} if cache is None else cache
    if subject.kind == "index":
        top = index_gitlinks(repo_root)
    elif subject.kind == "introduced":
        top = list(subject.gitlinks)
    else:
        top = tree_gitlinks(repo_root, subject.rev)

    names = top_level_names(repo_root, subject) if top else {}
    common = git_common_dir(repo_root) if top else None
    pins: list[SubmodulePin] = []
    seen: set[str] = set()
    queue: list[tuple[str, str, list[Optional[Path]]]] = []
    for path, sha in top:
        candidates: list[Optional[Path]] = [
            git_path(repo_root, f"modules/{name}") for name in names.get(path, [])
        ]
        candidates.append(worktree_git_dir(repo_root, path))
        candidates.append(git_path(repo_root, f"modules/{path}"))
        if common is not None:
            candidates.extend(common / "modules" / name for name in names.get(path, []))
            candidates.append(common / "modules" / path)
        queue.append((path, sha, candidates))
    if tips is not None:
        by_store: dict[Path, list[str]] = {}
        for _, sha, candidates in queue:
            target = _fetch_store(_existing_stores(candidates), tips)
            if target is not None:
                by_store.setdefault(target, []).append(sha)
        rt.parallel_map(lambda item: tips.warm(item[0], item[1]), list(by_store.items()))
    while queue:
        path, sha, candidates = queue.pop(0)
        if path in seen:
            continue
        seen.add(path)
        listing = list_nested(path, sha, candidates, listings, tips)
        pins.append(
            SubmodulePin(
                path=path,
                sha=sha,
                state=" ",
                nested_status=listing.status,
                nested_detail=listing.detail,
                store=listing.store,
            )
        )
        store = listing.store
        if store is None or listing.status:
            continue
        child_names = nested_names(store, sha) if listing.gitlinks else {}
        common = git_common_dir(store, is_store=True) if listing.gitlinks else None
        for relpath, nested_sha in listing.gitlinks:
            child_path = f"{path}/{relpath}"
            child: list[Optional[Path]] = [
                store / "modules" / name for name in child_names.get(relpath, [])
            ]
            child.append(worktree_git_dir(repo_root, child_path))
            child.append(store / "modules" / relpath)
            if common is not None:
                child.extend(common / "modules" / name for name in child_names.get(relpath, []))
                child.append(common / "modules" / relpath)
            queue.append((child_path, nested_sha, child))
            if tips is not None:
                # Read the nested store's remote while the walk goes on.
                nested_store = _fetch_store(_existing_stores(child), tips)
                if nested_store is not None:
                    tips.prefetch([nested_store], wait=False)
    return tuple(pins)


def git_dir_exists(path: Path) -> bool:
    result = run_git(path, ["rev-parse", "--show-toplevel"], check=False)
    if result.returncode != 0:
        return False
    try:
        return Path(result.stdout.strip()).resolve() == path.resolve()
    except OSError:
        return False


def remote_names(path: Path) -> tuple[str, ...]:
    result = run_git(path, ["remote"], check=False)
    if result.returncode != 0:
        return ()
    return tuple(remote for remote in result.stdout.splitlines() if remote)


def preferred_remote(path: Path) -> str:
    names = remote_names(path)
    if DEFAULT_REMOTE in names:
        return DEFAULT_REMOTE
    return names[0] if names else DEFAULT_REMOTE


def remote_url(path: Path, remote: str) -> str:
    result = run_git(path, ["remote", "get-url", remote], check=False)
    if result.returncode != 0:
        return ""
    return result.stdout.strip()


def shell_join(parts: Iterable[str]) -> str:
    return " ".join(shlex.quote(part) for part in parts)


def pin_ref(sha: str) -> str:
    return f"refs/pins/{sha}"


def publish_command(path: str, remote: str, sha: str) -> str:
    return shell_join(["git", "-C", path, "push", remote, f"{sha}:{pin_ref(sha)}"])


def check_pin(
    repo_root: Path,
    pin: SubmodulePin,
    store: Optional[Path] = None,
    tips: Optional["rt.RemoteTips"] = None,
) -> PinCheck:
    """Judge one pin in the repository that owns it.

    That is the submodule WORKTREE at ``<repo_root>/<path>``. ``store`` is used
    only when that path does not exist at all: a pin named solely by a commit
    the push introduces, at a path the same push later renames or removes, has
    no worktree, so it is judged in the object store that holds it (located by
    name, see ``collect_pins``). ``audit`` never passes a store for a pin a
    pushed tip or the index names, so a missing tip worktree still refuses.

    The verdict is the REMOTE's (``rt.RemoteTips.judge``): contained in a
    branch or refs/pins anchor the remote publishes this run. No local ref is
    consulted, and none is written.
    """
    tips = rt.RemoteTips() if tips is None else tips
    submodule_path = repo_root / pin.path
    in_store = store is not None and not submodule_path.exists()
    repo = store if in_store and store is not None else submodule_path
    where = str(repo) if in_store else pin.path
    present = in_store or submodule_path.exists()
    remote = preferred_remote(repo) if present else DEFAULT_REMOTE
    url = remote_url(repo, remote) if present else ""
    publish_ref = pin_ref(pin.sha)
    command = publish_command(where, remote, pin.sha)

    if not present:
        return PinCheck(
            path=pin.path,
            sha=pin.sha,
            status="missing-submodule-worktree",
            remote=remote,
            remote_url=url,
            publish_ref=publish_ref,
            suggested_command=shell_join(
                [
                    "python3",
                    "scripts/recreate_bootstrap.py",
                    "--require-seed",
                    "--no-build",
                ]
            ),
            detail="submodule path is missing; initialize it before checking remote reachability",
        )

    if not in_store and not git_dir_exists(submodule_path):
        return PinCheck(
            path=pin.path,
            sha=pin.sha,
            status="uninitialized-submodule",
            remote=remote,
            remote_url=url,
            publish_ref=publish_ref,
            suggested_command=shell_join(
                [
                    "python3",
                    "scripts/recreate_bootstrap.py",
                    "--require-seed",
                    "--no-build",
                ]
            ),
            detail="submodule path is not a Git worktree",
        )

    verdict = tips.judge(repo, pin.sha, scope="durable")

    if verdict.state == rt.CONTAINED:
        return PinCheck(
            path=pin.path,
            sha=pin.sha,
            status="reachable",
            remote_refs=verdict.refs,
            remote=remote,
            remote_url=url,
        )

    if verdict.state == rt.ABSENT:
        # No local store holds it AND the remote refused it by sha: only the
        # clone that authored the commit can repair this, by publishing it.
        return PinCheck(
            path=pin.path,
            sha=pin.sha,
            status="missing-commit-object",
            remote=remote,
            remote_url=url,
            publish_ref=publish_ref,
            suggested_command=f"{command}   # from the clone that has the commit",
            detail=(
                "pinned commit object is not present in the initialized submodule, "
                f"and {remote} does not serve it either: {verdict.detail}"
            ),
        )

    if verdict.state == rt.NOT_CONTAINED:
        # The remote's whole inventory was read, so this is decided: the
        # anchor does not exist (an existing one is a reachable verdict
        # above), and publishing it is the repair.
        return PinCheck(
            path=pin.path,
            sha=pin.sha,
            status="not-reachable-from-remote",
            remote=remote,
            remote_url=url,
            publish_ref=publish_ref,
            suggested_command=command,
            detail=verdict.detail,
        )

    # UNJUDGED: COULD NOT RUN. Not a pass, and not a claim about the pin.
    return PinCheck(
        path=pin.path,
        sha=pin.sha,
        status="remote-unreadable",
        remote=remote,
        remote_url=url,
        publish_ref=publish_ref,
        suggested_command=(
            f"{shell_join(['git', '-C', where, 'ls-remote', remote, 'refs/heads/main'])}"
            "   # check the network and credentials, then push again"
        ),
        detail=verdict.detail,
    )


@dataclass(frozen=True)
class Subject:
    """One revision (or the index) whose gitlinks this run must judge.

    ``kind`` is ``index`` (the staged gitlinks), ``revision`` (every gitlink in
    that commit's tree), or ``introduced`` (only the gitlinks that commit adds
    or changes relative to a parent, carried in ``gitlinks``; ``rev`` is still
    the commit, whose ``.gitmodules`` names the stores).
    """

    kind: str  # "index" | "revision" | "introduced"
    rev: str  # "" for the index
    label: str
    gitlinks: tuple[tuple[str, str], ...] = ()


INDEX_SUBJECT = Subject(kind="index", rev="", label="index (git ls-files -s)")


@dataclass(frozen=True)
class PushedUpdate:
    """One non-deletion line git handed the pre-push hook."""

    local_ref: str
    local_sha: str
    remote_ref: str
    remote_sha: str  # NULL_SHA for a new ref, or when git gave none


def _is_null_sha(sha: str) -> bool:
    return not sha or set(sha) == {"0"}


def pushed_updates(env: Mapping[str, str]) -> Optional[list[PushedUpdate]]:
    """The ref updates a push in flight would publish.

    ``None`` means no push is in flight --- the variable is UNSET, so the
    caller widens to its historical reading. An empty LIST means a push that
    updates no ref that publishes a tree (empty-but-set, or all deletions),
    which also has nothing narrower to judge. Set-vs-unset is the test, not
    empty-vs-nonempty: an empty-but-set variable is a REAL push.

    The REMOTE sha is kept, not discarded: it bounds the commits the push
    introduces (``introduced_commits``), and every one of those is published.
    """
    raw = env.get(PUSH_REFS_ENV)
    if raw is None:
        return None
    updates: list[PushedUpdate] = []
    seen: set[tuple[str, str]] = set()
    for line in raw.splitlines():
        fields = line.split()
        if len(fields) < 2:
            continue
        local_ref, local_sha = fields[0], fields[1]
        # A deletion publishes no tree; its local sha is all zeroes.
        if _is_null_sha(local_sha):
            continue
        remote_ref = fields[2] if len(fields) > 2 else ""
        # A missing remote sha is read as a new ref, which only WIDENS the
        # introduced range (to everything no remote-tracking ref has).
        remote_sha = fields[3] if len(fields) > 3 else NULL_SHA
        if (local_sha, remote_sha) in seen:
            continue
        seen.add((local_sha, remote_sha))
        updates.append(PushedUpdate(local_ref, local_sha, remote_ref, remote_sha))
    return updates


def resolve_revision(repo_root: Path, revision: str, label: str) -> str:
    completed = run_git(
        repo_root,
        ["rev-parse", "--verify", "--quiet", f"{revision}^{{commit}}"],
        check=False,
    )
    resolved = completed.stdout.strip()
    if completed.returncode != 0 or not SHA_RE.match(resolved):
        raise GitError(
            f"{label} {revision!r} does not name a commit in this checkout. Options:\n"
            f"  * name a revision this clone has:  --rev origin/main\n"
            f"  * fetch it first:                  git fetch origin\n"
            f"  * drop --rev/--push-context to judge this clone's index"
        )
    return resolved.lower()


def introduced_commits(repo_root: Path, local_sha: str, remote_sha: str) -> list[str]:
    """Every commit this ref update publishes that was not already published.

    ``rev-list <local> --not <remote sha> --remotes``: the old remote tip
    bounds the range, and a commit already on a fetched remote-tracking ref
    was published by an earlier push (a ``Merge origin/main into topic`` push
    would otherwise re-judge a thousand commits of main). With a new ref, or a
    remote sha this clone does not have (a force push over unfetched work),
    only ``--remotes`` bounds it, which WIDENS the range rather than guessing.
    A rev-list failure raises: an empty list here must mean "introduces
    nothing", never "could not tell".
    """
    exclude = ["--remotes"]
    if not _is_null_sha(remote_sha):
        known = run_git(
            repo_root, ["cat-file", "-e", f"{remote_sha}^{{commit}}"], check=False
        )
        if known.returncode == 0:
            exclude.insert(0, remote_sha)
    listed = run_git(repo_root, ["rev-list", local_sha, "--not", *exclude])
    commits = [line.strip().lower() for line in listed.stdout.splitlines() if line.strip()]
    for commit in commits:
        if not SHA_RE.match(commit):
            raise GitError(f"could not parse rev-list output for {local_sha}: {commit!r}")
    return commits


def changed_gitlinks(
    repo_root: Path, commits: Sequence[str]
) -> dict[str, list[tuple[str, str]]]:
    """commit -> the gitlinks it adds or changes against any parent.

    One ``diff-tree --stdin`` for the whole range. ``-m`` diffs a merge
    against EACH parent, so a pin a merge resolution introduces is seen;
    ``--root`` diffs a root commit against the empty tree. A gitlink equal to
    one parent's is inherited from it, and that parent is either introduced
    too (and listed there) or already published. Submodule-ignore
    configuration is overridden twice over (``diff.ignoreSubmodules`` and
    ``--ignore-submodules=none``): this clone sets ``ignore = all``, under
    which a porcelain diff drops every gitlink row. ``-z`` so a non-ASCII
    path is not C-quoted into a path that does not exist.
    """
    found: dict[str, list[tuple[str, str]]] = {}
    if not commits:
        return found
    listed = run_git(
        repo_root,
        [
            "diff-tree",
            "--stdin",
            "-r",
            "-z",
            "-m",
            "--root",
            "--no-renames",
            "--ignore-submodules=none",
        ],
        extra_config=["-c", "diff.ignoreSubmodules=none"],
        input_text="".join(f"{commit}\n" for commit in commits),
    )
    tokens = listed.stdout.split("\0")
    current = ""
    index = 0
    while index < len(tokens):
        token = tokens[index]
        index += 1
        if not token.strip():
            continue
        if token.startswith(":"):
            if index >= len(tokens) or not current:
                raise GitError(f"could not parse diff-tree row: {token!r}")
            path = tokens[index]
            index += 1
            fields = token[1:].split()
            if len(fields) < 5:
                raise GitError(f"could not parse diff-tree row: {token!r}")
            dst_mode, dst_sha, status = fields[1], fields[3], fields[4]
            if dst_mode != GITLINK_MODE or status.startswith("D"):
                continue
            if not SHA_RE.match(dst_sha):
                raise GitError(f"could not parse diff-tree gitlink sha: {token!r}")
            entry = (path, dst_sha.lower())
            rows = found.setdefault(current, [])
            if entry not in rows:
                rows.append(entry)
            continue
        header = token.split()[0].lower()
        if not SHA_RE.match(header):
            raise GitError(f"could not parse diff-tree commit header: {token!r}")
        current = header
    return found


def select_subjects(
    repo_root: Path,
    *,
    rev: Optional[str] = None,
    push_context: bool = False,
    env: Optional[Mapping[str, str]] = None,
    emit: bool = True,
    stream: object = None,
) -> tuple[Subject, ...]:
    """Which revisions this invocation judges, announcing the choice.

    Every path here either NARROWS to something strictly more relevant than the
    index (what a push actually publishes) or WIDENS back to the index. It
    never narrows to nothing --- an empty subject list would pass vacuously,
    which is the failure mode this whole lane exists to refuse.

    A push is judged as each pushed TIP tree (every pin it names) plus every
    gitlink added or changed by a commit the push introduces: an intermediate
    commit is published exactly as much as the tip is.
    """
    environ = os.environ if env is None else env
    out = sys.stdout if stream is None else stream
    if rev is not None:
        return (
            Subject(
                kind="revision",
                rev=resolve_revision(repo_root, rev, "--rev"),
                label=f"--rev {rev}",
            ),
        )
    if push_context:
        pushed = pushed_updates(environ)
        if pushed is None:
            if emit:
                print(
                    f"SUBJECT: index/HEAD (no push in flight; {PUSH_REFS_ENV} unset)",
                    file=out,
                )
            return (INDEX_SUBJECT,)
        if not pushed:
            # Set but yielding nothing: a push whose refs are all deletions, or
            # one with no ref updates at all. It publishes no tree, so there is
            # nothing narrower to judge, and widening is the fail-closed choice.
            if emit:
                print(
                    "SUBJECT: index/HEAD (push in flight updates no ref that "
                    "publishes a tree)",
                    file=out,
                )
            return (INDEX_SUBJECT,)
        tips: list[Subject] = []
        tip_shas: set[str] = set()
        introduced_by: dict[str, list[str]] = {}
        introduced_order: list[str] = []
        for update in pushed:
            resolved = resolve_revision(
                repo_root, update.local_sha, f"pushed ref {update.local_ref}"
            )
            if resolved not in tip_shas:
                tip_shas.add(resolved)
                tips.append(
                    Subject(
                        kind="revision",
                        rev=resolved,
                        label=f"pushed {update.local_ref} [{update.local_sha[:12]}]",
                    )
                )
            for commit in introduced_commits(repo_root, resolved, update.remote_sha):
                if commit not in introduced_by:
                    introduced_by[commit] = []
                    introduced_order.append(commit)
                if update.local_ref not in introduced_by[commit]:
                    introduced_by[commit].append(update.local_ref)
        # A pushed tip's whole tree is already judged; its diff adds nothing.
        intermediate = [c for c in introduced_order if c not in tip_shas]
        changed = changed_gitlinks(repo_root, intermediate)
        introduced = [
            Subject(
                kind="introduced",
                rev=commit,
                label=f"{', '.join(introduced_by[commit])} introduces {commit[:12]}",
                gitlinks=tuple(changed[commit]),
            )
            for commit in intermediate
            if changed.get(commit)
        ]
        if emit:
            print(
                f"SUBJECT: push ({len(pushed)} ref update(s); "
                f"{len(introduced_order)} introduced commit(s), "
                f"{len(introduced)} intermediate one(s) changing a gitlink)",
                file=out,
            )
        return (*tips, *introduced)
    if emit:
        print("SUBJECT: index/HEAD (no push context requested)", file=out)
    return (INDEX_SUBJECT,)


def audit(
    repo_root: Path,
    subjects: Sequence[Subject] = (INDEX_SUBJECT,),
    tips: Optional["rt.RemoteTips"] = None,
) -> AuditResult:
    """Judge every distinct (path, sha) pin any subject names.

    A pin named by several pushed revisions is checked once and reports all of
    them, so a failure says which ref --- or which introduced commit --- would
    publish it. A pin whose own nested gitlinks could not be enumerated is
    refused even when its reachability passes: its subtree was never judged.

    One ``RemoteTips`` serves the whole run, so each remote is listed once;
    the pins are judged concurrently (each remote read is network latency).
    """
    tips = rt.RemoteTips() if tips is None else tips
    order: list[tuple[str, str]] = []
    named_by: dict[tuple[str, str], list[str]] = {}
    unenumerated: dict[tuple[str, str], tuple[str, str]] = {}
    # A pin named by a tip tree or the index is judged in its worktree only.
    # A pin named ONLY by an introduced commit may be at a path the same push
    # renamed away, so check_pin may judge it in the store that holds it.
    tip_named: set[tuple[str, str]] = set()
    stores: dict[tuple[str, str], Path] = {}
    cache: dict[tuple[str, str, tuple[str, ...]], NestedListing] = {}
    for subject in subjects:
        for pin in collect_pins(repo_root, subject, cache, tips):
            key = (pin.path, pin.sha)
            if key not in named_by:
                named_by[key] = []
                order.append(key)
            if subject.label not in named_by[key]:
                named_by[key].append(subject.label)
            if subject.kind != "introduced":
                tip_named.add(key)
            if pin.store is not None and key not in stores:
                stores[key] = pin.store
            if pin.nested_status and key not in unenumerated:
                unenumerated[key] = (pin.nested_status, pin.nested_detail)

    def judge(key: tuple[str, str]) -> PinCheck:
        path, sha = key
        return check_pin(
            repo_root,
            SubmodulePin(path=path, sha=sha, state=" "),
            store=None if key in tip_named else stores.get(key),
            tips=tips,
        )

    # Ask each store's remote about all of its pins together (one inventory,
    # and the ancestry questions batched across pins: ``judge_many``), so the
    # per-pin judging below reads this run's verdicts instead of the network.
    by_repo: dict[str, tuple[Path, list[str]]] = {}
    for key in order:
        store = None if key in tip_named else stores.get(key)
        worktree = repo_root / key[0]
        repo = store if store is not None and not worktree.exists() else worktree
        by_repo.setdefault(str(repo), (repo, []))[1].append(key[1])
    rt.parallel_map(lambda item: tips.judge_many(item[0], item[1], scope="durable"),
                    list(by_repo.values()))

    checks: list[PinCheck] = []
    for (path, sha), check in zip(order, rt.parallel_map(judge, order)):
        nested = unenumerated.get((path, sha))
        if nested is not None:
            status, detail = nested
            if check.ok:
                check = replace(check, status=status, detail=detail)
            else:
                check = replace(
                    check, detail=f"{check.detail}; nested pins not enumerated: {detail}"
                )
        checks.append(replace(check, named_by=tuple(named_by[(path, sha)])))
    tips = [subject.label for subject in subjects if subject.kind != "introduced"]
    introduced = len(subjects) - len(tips)
    source = "; ".join(tips)
    if introduced:
        source += f"; + {introduced} introduced commit(s) changing a gitlink"
    return AuditResult(
        repo_root=repo_root,
        pins=tuple(checks),
        source=source,
    )


def render_text(result: AuditResult, rerun: str = "") -> str:
    lines: list[str] = []
    lines.append(f"Submodule remote reachability check: {result.repo_root}")
    lines.append(f"source: {result.source}")
    lines.append(
        "summary: checked={checked} reachable={reachable} failed={failed}".format(
            checked=len(result.pins),
            reachable=len(result.pins) - len(result.failed),
            failed=len(result.failed),
        )
    )

    if result.empty:
        # Never reachable from a widening subject, so this names a revision
        # whose tree really has no gitlink, or a Git read that returned none.
        lines.append(
            "FAIL: audited ZERO submodule pins — an empty work set is not evidence "
            "of reachability"
        )
        lines.append("")
        lines.append(f"  subject: {result.source}")
        lines.append(
            "  detail: a zero delta means *never ran* before it means *returned "
            "true*, so this refuses rather than printing PASS over nothing"
        )
        lines.append("  Options:")
        lines.append(
            "    * confirm the subject really has gitlinks:  "
            "git ls-tree -r <rev> | awk '$1==\"160000\"'"
        )
        lines.append(
            "    * judge this checkout instead:              "
            "python3 scripts/check_submodule_remote_reachability.py"
        )
        lines.append(
            "    * if the revision predates first-party/, it is not a release "
            "subject; push a revision that carries the gitlinks"
        )
        return "\n".join(lines)

    if result.ok:
        lines.append(
            "PASS: every parent-pinned submodule commit is contained in a branch or "
            "refs/pins/* anchor its remote publishes (read with ls-remote this run)"
        )
        return "\n".join(lines)

    if result.unjudged:
        lines.append(
            "COULD NOT RUN: a remote could not be read, so the pin(s) below were not "
            "judged. This is not a pass, and it is not a finding about any pin."
        )
        if rerun:
            lines.append(f"Rerun with: {rerun}")
    else:
        lines.append(
            "FAIL: parent-pinned submodule commit(s) are not reproducible from the "
            "branches and refs/pins/* anchors their remotes publish"
        )
    for check in result.failed:
        lines.append("")
        lines.append(f"- {check.path} @ {check.sha}")
        lines.append(f"  status: {check.status}")
        if check.named_by:
            lines.append(f"  named by: {', '.join(check.named_by)}")
        if check.remote_url:
            lines.append(f"  remote: {check.remote} {check.remote_url}")
        else:
            lines.append(f"  remote: {check.remote}")
        if check.detail:
            lines.append(f"  detail: {check.detail}")
        if check.suggested_command:
            lines.append(f"  next command: {check.suggested_command}")

    lines.append("")
    lines.append(
        "This audit judged the remotes' own refs, not this clone's, and wrote no ref; "
        "a local fetch cannot change its verdict. It does not emit a recursive "
        "fetch/update command: materialize missing gitlinks through the canonical "
        "recreator."
    )
    return "\n".join(lines)


def render_json(result: AuditResult) -> str:
    return json.dumps(result.as_dict(), indent=2, sort_keys=True)


def self_git(repo: Path, args: Sequence[str], *, allow_file: bool = False) -> None:
    config = [
        "-c",
        "user.name=Trust Submodule Check",
        "-c",
        "user.email=trust-submodule-check@example.invalid",
    ]
    if allow_file:
        config.extend(["-c", "protocol.file.allow=always"])
    run_git(repo, args, extra_config=config)


def ref_state(repo: Path) -> str:
    """Every ref in ``repo``'s store, plus its FETCH_HEAD: what the audit
    must leave exactly as it found it."""
    refs = run_git(repo, ["for-each-ref", "--format=%(objectname) %(refname)"]).stdout
    fetch_head = git_path(repo, "FETCH_HEAD")
    if fetch_head is not None and fetch_head.exists():
        head = fetch_head.read_text(encoding="utf-8", errors="replace")
    else:
        head = "<no FETCH_HEAD>"
    return f"{refs}--- FETCH_HEAD ---\n{head}"


def write_file(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")


def commit_file(repo: Path, relative: str, text: str, message: str) -> None:
    write_file(repo / relative, text)
    self_git(repo, ["add", relative])
    self_git(repo, ["commit", "-m", message])


def record_case(
    cases: list[dict[str, object]], name: str, passed: bool, **details: object
) -> None:
    """Record a self-check case whose shape is not one-pin-one-status."""
    cases.append({"name": name, "passed": passed, **details})


def assert_self_check_case(
    *,
    cases: list[dict[str, object]],
    name: str,
    result: AuditResult,
    expected_status: str,
    expected_ok: bool,
    expected_publish_ref: str | None = None,
    expected_ref_prefix: str | None = None,
    expected_command_contains: str | None = None,
    expected_command_excludes: str | None = None,
) -> None:
    observed_statuses = [pin.status for pin in result.pins]
    only_pin = result.pins[0] if len(result.pins) == 1 else None
    publish_ref_matches = (
        expected_publish_ref is None
        or (only_pin is not None and only_pin.publish_ref == expected_publish_ref)
    )
    containing_ref_matches = (
        expected_ref_prefix is None
        or (
            only_pin is not None
            and any(ref.startswith(expected_ref_prefix) for ref in only_pin.remote_refs)
        )
    )
    # The ADVICE is part of the contract. A gate that reports the right status
    # and then names a command that cannot fix it still costs the reader the
    # whole diagnosis.
    command_matches = (
        expected_command_contains is None
        or (
            only_pin is not None
            and expected_command_contains in only_pin.suggested_command
        )
    )
    # An EXCLUSION is what makes the advice assertion non-vacuous. The
    # remote-unreadable branch offers both commands, so "contains fetch" is
    # satisfied by the very fallback the test is meant to distinguish from a
    # decided answer. Measured: with only the inclusion, reverting the fix left
    # the case GREEN.
    command_excludes = (
        expected_command_excludes is None
        or (
            only_pin is not None
            and expected_command_excludes not in only_pin.suggested_command
        )
    )
    passed = (
        len(result.pins) == 1
        and observed_statuses == [expected_status]
        and result.ok is expected_ok
        and publish_ref_matches
        and containing_ref_matches
        and command_matches
        and command_excludes
    )
    cases.append(
        {
            "name": name,
            "expected_status": expected_status,
            "expected_ok": expected_ok,
            "expected_publish_ref": expected_publish_ref,
            "expected_ref_prefix": expected_ref_prefix,
            "expected_command_contains": expected_command_contains,
            "expected_command_excludes": expected_command_excludes,
            "observed_command": only_pin.suggested_command if only_pin is not None else None,
            "observed_statuses": observed_statuses,
            "observed_ok": result.ok,
            "observed_publish_ref": only_pin.publish_ref if only_pin is not None else None,
            "observed_remote_refs": list(only_pin.remote_refs) if only_pin is not None else [],
            "passed": passed,
            "pins": [pin.as_dict() for pin in result.pins],
        }
    )


def render_self_check_report(cases: Sequence[dict[str, object]]) -> dict[str, object]:
    failed = [case for case in cases if not case["passed"]]
    return {
        "summary": {
            "checked": len(cases),
            "passed": len(cases) - len(failed),
            "failed": len(failed),
        },
        "cases": list(cases),
    }


def _scenario_subject_selection(cases: list[dict[str, object]]) -> None:
    """Mutation-prove that the PUSHED revision is what gets judged.

    This is the defect the lane shipped with: the subject came from the local
    index, and "contained in some fetched remote ref" is a predicate an OLDER
    pin satisfies more often, so a behind clone audited a systematically SAFER
    pin set and printed PASS over the wrong 12 pins.

    The mutation reproduces exactly that shape --- publish a local-only pin,
    then move HEAD back so the index names the safe one --- and asserts the two
    readings DISAGREE. If they ever agree again the fix has been undone.
    """
    with tempfile.TemporaryDirectory(prefix="trust-submodule-subject-") as tmp:
        root = Path(tmp)
        source = root / "sub-source"
        bare = root / "submodule.git"
        super_repo = root / "super"

        source.mkdir()
        self_git(source, ["init", "-b", "main"])
        commit_file(source, "README.md", "reachable\n", "initial submodule commit")
        self_git(root, ["clone", "--bare", str(source), str(bare)])

        super_repo.mkdir()
        self_git(super_repo, ["init", "-b", "main"])
        commit_file(super_repo, "README.md", "super\n", "root commit, no gitlink yet")
        no_gitlink_rev = run_git(super_repo, ["rev-parse", "HEAD"]).stdout.strip()
        self_git(super_repo, ["submodule", "add", str(bare), "deps/sub"], allow_file=True)
        self_git(super_repo, ["commit", "-m", "add reachable submodule"])
        safe_rev = run_git(super_repo, ["rev-parse", "HEAD"]).stdout.strip()

        submodule = super_repo / "deps" / "sub"
        commit_file(submodule, "LOCAL_ONLY.txt", "local-only\n", "local-only commit")
        local_only_sha = run_git(submodule, ["rev-parse", "HEAD"]).stdout.strip()
        self_git(super_repo, ["add", "deps/sub"])
        self_git(super_repo, ["commit", "-m", "publish local-only pin"])
        published_rev = run_git(super_repo, ["rev-parse", "HEAD"]).stdout.strip()

        # Make the clone BEHIND: HEAD/index name the safe pin, while the
        # revision a push would publish names the local-only one.
        self_git(super_repo, ["reset", "--hard", safe_rev])

        index_result = audit(super_repo, (INDEX_SUBJECT,))
        record_case(
            cases,
            "behind clone: index reading still PASSES (the old, biased subject)",
            index_result.ok and not index_result.failed,
            observed_statuses=[pin.status for pin in index_result.pins],
            observed_ok=index_result.ok,
            note="the stale pin is on a remote branch, so the old subject is green",
        )

        pushed_env = {
            PUSH_REFS_ENV: f"refs/heads/main {published_rev} refs/heads/main {safe_rev}"
        }
        subjects = select_subjects(
            super_repo, push_context=True, env=pushed_env, emit=False
        )
        push_result = audit(super_repo, subjects)
        refused = (
            not push_result.ok
            and len(push_result.failed) == 1
            and push_result.failed[0].status == "not-reachable-from-remote"
            and push_result.failed[0].sha == local_only_sha
        )
        record_case(
            cases,
            "behind clone: --push-context REFUSES the pushed local-only pin",
            refused,
            subjects=[subject.label for subject in subjects],
            observed_statuses=[pin.status for pin in push_result.pins],
            observed_shas=[pin.sha for pin in push_result.pins],
            expected_sha=local_only_sha,
            observed_ok=push_result.ok,
        )

        # Widening, never narrowing: unset and deletion-only must fall back to
        # the index rather than to an empty (vacuously passing) subject.
        unset = select_subjects(super_repo, push_context=True, env={}, emit=False)
        record_case(
            cases,
            f"{PUSH_REFS_ENV} unset widens to the index",
            unset == (INDEX_SUBJECT,),
            observed=[subject.label for subject in unset],
        )
        deletion_only = select_subjects(
            super_repo,
            push_context=True,
            env={PUSH_REFS_ENV: f"refs/heads/gone {NULL_SHA} refs/heads/gone {safe_rev}"},
            emit=False,
        )
        record_case(
            cases,
            "deletion-only push widens to the index (never narrows to nothing)",
            deletion_only == (INDEX_SUBJECT,),
            observed=[subject.label for subject in deletion_only],
        )
        empty_but_set = select_subjects(
            super_repo, push_context=True, env={PUSH_REFS_ENV: ""}, emit=False
        )
        record_case(
            cases,
            "empty-but-set push variable widens to the index",
            empty_but_set == (INDEX_SUBJECT,),
            observed=[subject.label for subject in empty_but_set],
        )

        # A subject that yields no pin must REFUSE, not pass vacuously.
        empty_result = audit(
            super_repo,
            (Subject(kind="revision", rev=no_gitlink_rev, label="pre-submodule root"),),
        )
        record_case(
            cases,
            "empty work set fails closed",
            empty_result.empty and not empty_result.ok and not empty_result.failed,
            checked=len(empty_result.pins),
            observed_ok=empty_result.ok,
            note="zero pins, zero failures, and still not ok",
        )


def _scenario_nested_pins(cases: list[dict[str, object]]) -> None:
    """Nested pins come from the PINNED tree, so deinit cannot shrink the set.

    ``submodule status --recursive`` can only descend into a materialized
    module, so an uninitialized child silently leaves the work set while the
    lane still reports PASS. Reading the child's gitlinks out of the parent's
    object store makes the work set a property of the revision instead.
    """
    with tempfile.TemporaryDirectory(prefix="trust-submodule-nested-") as tmp:
        root = Path(tmp)
        inner_source = root / "inner-source"
        inner_bare = root / "inner.git"
        outer_source = root / "outer-source"
        outer_bare = root / "outer.git"
        super_repo = root / "super"

        inner_source.mkdir()
        self_git(inner_source, ["init", "-b", "main"])
        commit_file(inner_source, "README.md", "inner\n", "inner commit")
        self_git(root, ["clone", "--bare", str(inner_source), str(inner_bare)])

        outer_source.mkdir()
        self_git(outer_source, ["init", "-b", "main"])
        commit_file(outer_source, "README.md", "outer\n", "outer commit")
        self_git(
            outer_source, ["submodule", "add", str(inner_bare), "nested"], allow_file=True
        )
        self_git(outer_source, ["commit", "-m", "outer pins inner"])
        self_git(root, ["clone", "--bare", str(outer_source), str(outer_bare)])

        super_repo.mkdir()
        self_git(super_repo, ["init", "-b", "main"])
        self_git(
            super_repo, ["submodule", "add", str(outer_bare), "deps/outer"], allow_file=True
        )
        self_git(super_repo, ["commit", "-m", "super pins outer"])

        # The nested module is never initialized in this checkout — the exact
        # state under which the recursive status reading loses it.
        legacy = run_git(
            super_repo, ["submodule", "status", "--cached", "--recursive"]
        ).stdout
        legacy_paths = sorted(
            line.strip().split()[1] for line in legacy.splitlines() if line.strip()
        )
        collected = collect_pins(super_repo, INDEX_SUBJECT)
        collected_paths = sorted(pin.path for pin in collected)

        record_case(
            cases,
            "nested pin is read from the pinned tree, not the submodule worktree",
            "deps/outer/nested" in collected_paths,
            legacy_reading=legacy_paths,
            tree_reading=collected_paths,
            note=(
                "the recursive status reading loses an uninitialized child; the "
                "pinned-tree reading keeps it"
            ),
        )
        result = audit(super_repo, (INDEX_SUBJECT,))
        record_case(
            cases,
            "the recovered nested pin is actually judged",
            any(pin.path == "deps/outer/nested" for pin in result.pins),
            checked=len(result.pins),
            paths=[pin.path for pin in result.pins],
        )


def _refuses(result: AuditResult, path: str, sha: str, label_part: str = "") -> bool:
    """``result`` is red and names exactly this (path, sha) among its failures."""
    return not result.ok and any(
        pin.path == path
        and pin.sha == sha
        and (not label_part or any(label_part in label for label in pin.named_by))
        for pin in result.failed
    )


def _scenario_introduced_commits(cases: list[dict[str, object]]) -> None:
    """A push publishes EVERY commit it introduces, not only its tip.

    The shape that used to pass: BASE -> B (pins a local-only submodule commit)
    -> C (moves the pin back to a published one). The tip tree of C is clean,
    but B is published by the same push and a consumer's on-demand submodule
    fetch of B aborts. The clone also sets ``ignore = all`` on the submodule and
    ``diff.ignoreSubmodules = all``, under which a porcelain diff shows no
    gitlink row at all, so the introduced-gitlink reading must override both.
    """
    with tempfile.TemporaryDirectory(prefix="trust-submodule-introduced-") as tmp:
        root = Path(tmp)
        source = root / "sub-source"
        bare = root / "submodule.git"
        super_bare = root / "super.git"
        super_repo = root / "super"

        source.mkdir()
        self_git(source, ["init", "-b", "main"])
        commit_file(source, "README.md", "reachable\n", "initial submodule commit")
        self_git(root, ["clone", "--bare", str(source), str(bare)])
        self_git(root, ["init", "--bare", "-b", "main", str(super_bare)])

        super_repo.mkdir()
        self_git(super_repo, ["init", "-b", "main"])
        commit_file(super_repo, "README.md", "super\n", "root")
        self_git(super_repo, ["submodule", "add", str(bare), "deps/sub"], allow_file=True)
        self_git(super_repo, ["config", "-f", ".gitmodules", "submodule.deps/sub.ignore", "all"])
        self_git(super_repo, ["config", "diff.ignoreSubmodules", "all"])
        # Under ignore=all, git 2.54 (Apple Git-157) SKIPS a plain `git add` of the
        # gitlink ("Skipping submodule due to ignore=all"), so the pin below would never
        # be staged and `commit` would find nothing to commit. `--force` stages it on
        # every git, which is what this scenario means to do.
        self_git(super_repo, ["add", ".gitmodules"])
        self_git(super_repo, ["commit", "-m", "BASE: pin a published commit"])
        base = run_git(super_repo, ["rev-parse", "HEAD"]).stdout.strip()
        self_git(super_repo, ["remote", "add", "origin", str(super_bare)])
        self_git(super_repo, ["push", "-q", "origin", "main"])
        self_git(super_repo, ["fetch", "-q", "origin"])

        submodule = super_repo / "deps" / "sub"
        safe = run_git(submodule, ["rev-parse", "HEAD"]).stdout.strip()
        commit_file(submodule, "LOCAL_ONLY.txt", "local-only\n", "local-only commit")
        local_only = run_git(submodule, ["rev-parse", "HEAD"]).stdout.strip()
        self_git(super_repo, ["add", "--force", "deps/sub"])
        self_git(super_repo, ["commit", "-m", "B: pin the local-only commit"])
        b_rev = run_git(super_repo, ["rev-parse", "HEAD"]).stdout.strip()
        self_git(submodule, ["checkout", "-q", safe])
        self_git(super_repo, ["add", "--force", "deps/sub"])
        self_git(super_repo, ["commit", "-m", "C: move the pin back"])
        c_rev = run_git(super_repo, ["rev-parse", "HEAD"]).stdout.strip()

        def push(line: str, tips: Optional[rt.RemoteTips] = None) -> AuditResult:
            subjects = select_subjects(
                super_repo, push_context=True, env={PUSH_REFS_ENV: line}, emit=False
            )
            return audit(super_repo, subjects, tips)

        ranged_tips = rt.RemoteTips()
        ranged = push(f"refs/heads/main {c_rev} refs/heads/main {base}", ranged_tips)
        record_case(
            cases,
            "push range: an INTERMEDIATE commit's local-only pin is refused and named",
            _refuses(ranged, "deps/sub", local_only, b_rev[:12]),
            observed_ok=ranged.ok,
            observed=[pin.as_dict() for pin in ranged.pins],
            expected_sha=local_only,
            expected_named_by=b_rev[:12],
        )
        record_case(
            cases,
            "one ls-remote per remote per run, however many subjects and pins ask it",
            len(ranged.pins) == 2 and ranged_tips.ls_remote_calls == 1,
            pins=len(ranged.pins),
            ls_remote_calls=ranged_tips.ls_remote_calls,
        )

        new_ref = push(f"refs/heads/topic {c_rev} refs/heads/topic {NULL_SHA}")
        record_case(
            cases,
            "new-ref push: introduced commits bounded by --remotes, intermediate pin refused",
            _refuses(new_ref, "deps/sub", local_only, b_rev[:12]),
            observed_ok=new_ref.ok,
            observed=[pin.as_dict() for pin in new_ref.pins],
        )

        unknown_remote = push(f"refs/heads/main {c_rev} refs/heads/main {'e' * 40}")
        record_case(
            cases,
            "remote sha this clone lacks: range widens to --remotes, never to nothing",
            _refuses(unknown_remote, "deps/sub", local_only, b_rev[:12]),
            observed_ok=unknown_remote.ok,
            observed=[pin.as_dict() for pin in unknown_remote.pins],
        )

        # Control: B is already on the remote side of this update, so the push
        # introduces only C, whose tree is clean. Over-judging is not the fix.
        published_b = push(f"refs/heads/main {c_rev} refs/heads/main {b_rev}")
        record_case(
            cases,
            "control: a push that does not introduce B passes",
            published_b.ok,
            observed_ok=published_b.ok,
            observed=[pin.as_dict() for pin in published_b.pins],
        )

        # A merge whose RESOLUTION sets the local-only pin (no parent has it),
        # followed by a commit that restores the published one. diff-tree skips
        # merges unless told otherwise, so this proves the -m reading.
        self_git(super_repo, ["checkout", "-q", "-b", "side"])
        commit_file(super_repo, "SIDE.md", "side\n", "side work")
        self_git(super_repo, ["checkout", "-q", "main"])
        commit_file(super_repo, "MAIN.md", "main\n", "main work")
        self_git(super_repo, ["merge", "--no-ff", "--no-commit", "side"])
        self_git(submodule, ["checkout", "-q", local_only])
        self_git(super_repo, ["add", "--force", "deps/sub"])
        self_git(super_repo, ["commit", "-m", "merge side, resolving the pin to local-only"])
        merge_rev = run_git(super_repo, ["rev-parse", "HEAD"]).stdout.strip()
        self_git(submodule, ["checkout", "-q", safe])
        self_git(super_repo, ["add", "--force", "deps/sub"])
        self_git(super_repo, ["commit", "-m", "D: restore"])
        d_rev = run_git(super_repo, ["rev-parse", "HEAD"]).stdout.strip()
        merged = push(f"refs/heads/main {d_rev} refs/heads/main {c_rev}")
        record_case(
            cases,
            "push range: a MERGE resolution's local-only pin is refused and named",
            _refuses(merged, "deps/sub", local_only, merge_rev[:12]),
            observed_ok=merged.ok,
            observed=[pin.as_dict() for pin in merged.pins],
        )

        # Control: history ALREADY on a remote is not re-judged. Main (with B
        # and the merge in it) is published; a topic push that merges it
        # introduces only the topic's own commits. Without --remotes in the
        # exclusion every such merge would re-refuse main's published past.
        self_git(super_repo, ["push", "-q", "origin", f"{d_rev}:refs/heads/main"])
        self_git(super_repo, ["push", "-q", "origin", f"{base}:refs/heads/topic"])
        self_git(super_repo, ["fetch", "-q", "origin"])
        self_git(super_repo, ["checkout", "-q", "-b", "topic", base])
        commit_file(super_repo, "TOPIC.md", "topic\n", "topic work")
        self_git(super_repo, ["merge", "-q", "--no-ff", "-m", "merge origin/main", "origin/main"])
        topic_rev = run_git(super_repo, ["rev-parse", "HEAD"]).stdout.strip()
        topic = push(f"refs/heads/topic {topic_rev} refs/heads/topic {base}")
        record_case(
            cases,
            "control: merging already-published history does not re-judge it",
            topic.ok,
            observed_ok=topic.ok,
            observed=[pin.as_dict() for pin in topic.pins],
        )

        # Control: bump then RENAME a submodule in one push, every pin
        # published. The bump commit names a path with no worktree at the tip,
        # so it is judged in the store that holds it instead of refused as a
        # missing worktree.
        self_git(super_repo, ["checkout", "-q", "main"])
        commit_file(submodule, "PUBLISHED.txt", "published\n", "published bump")
        self_git(submodule, ["push", "-q", "origin", "HEAD:refs/heads/bump"])
        self_git(submodule, ["fetch", "-q", "origin"])
        self_git(super_repo, ["add", "--force", "deps/sub"])
        self_git(super_repo, ["commit", "-m", "bump to a published commit"])
        self_git(super_repo, ["mv", "deps/sub", "deps/renamed"])
        self_git(super_repo, ["commit", "-m", "rename the submodule path"])
        renamed_rev = run_git(super_repo, ["rev-parse", "HEAD"]).stdout.strip()
        renamed = push(f"refs/heads/main {renamed_rev} refs/heads/main {d_rev}")
        record_case(
            cases,
            "control: bump then rename a submodule in one push passes",
            renamed.ok and any(pin.path == "deps/sub" for pin in renamed.pins),
            observed_ok=renamed.ok,
            observed=[pin.as_dict() for pin in renamed.pins],
        )


def _scenario_store_by_name(cases: list[dict[str, object]]) -> None:
    """Nested pins are enumerated from the store that holds the pinned commit.

    Git keys ``modules/`` by submodule NAME. Reading it by PATH lost the whole
    nested subtree after a ``git mv``, for any name != path, and for a module
    registered over an existing clone (embedded ``.git``, no ``modules/``
    entry) --- each time under a PASS. A store that cannot list the pinned tree
    used to read as "no nested pins" as well.
    """
    with tempfile.TemporaryDirectory(prefix="trust-submodule-byname-") as tmp:
        root = Path(tmp)
        inner_source = root / "inner-source"
        inner_bare = root / "inner.git"
        outer_source = root / "outer-source"
        outer_bare = root / "outer.git"

        inner_source.mkdir()
        self_git(inner_source, ["init", "-b", "main"])
        commit_file(inner_source, "README.md", "inner\n", "inner commit")
        self_git(root, ["clone", "--bare", str(inner_source), str(inner_bare)])
        outer_source.mkdir()
        self_git(outer_source, ["init", "-b", "main"])
        commit_file(outer_source, "README.md", "outer\n", "outer commit")
        self_git(
            outer_source, ["submodule", "add", str(inner_bare), "nested"], allow_file=True
        )
        self_git(outer_source, ["commit", "-m", "outer pins inner"])
        self_git(root, ["clone", "--bare", str(outer_source), str(outer_bare)])

        # Each fixture publishes its outer commit on its OWN branch: a main
        # that pins a local-only inner commit cannot be cloned recursively.
        def publish_outer_pinning_local_only_inner(outer: Path, branch: str) -> str:
            nested = outer / "nested"
            commit_file(nested, "LOCAL_ONLY.txt", str(outer) + "\n", "inner local-only")
            sha = run_git(nested, ["rev-parse", "HEAD"]).stdout.strip()
            self_git(outer, ["add", "nested"])
            self_git(outer, ["commit", "-m", "outer pins a local-only inner commit"])
            self_git(outer, ["push", "-q", "origin", f"HEAD:refs/heads/{branch}"])
            self_git(outer, ["fetch", "-q", "origin"])
            return sha

        # (1) RENAME: `git mv` keeps the name, so the store stays modules/deps/outer.
        renamed = root / "renamed"
        renamed.mkdir()
        self_git(renamed, ["init", "-b", "main"])
        self_git(renamed, ["submodule", "add", str(outer_bare), "deps/outer"], allow_file=True)
        self_git(renamed, ["commit", "-m", "pin outer"])
        self_git(renamed, ["submodule", "update", "-q", "--init", "--recursive"], allow_file=True)
        inner_local = publish_outer_pinning_local_only_inner(
            renamed / "deps" / "outer", "renamed"
        )
        self_git(renamed, ["add", "deps/outer"])
        self_git(renamed, ["commit", "-m", "bump outer"])
        self_git(renamed, ["mv", "deps/outer", "deps/moved"])
        self_git(renamed, ["commit", "-m", "rename the submodule path"])
        result = audit(renamed, select_subjects(renamed, rev="HEAD", emit=False))
        record_case(
            cases,
            "renamed submodule (store keyed by NAME): nested local-only pin refused",
            _refuses(result, "deps/moved/nested", inner_local),
            observed_ok=result.ok,
            observed=[pin.as_dict() for pin in result.pins],
        )

        # (2) NAME != PATH with a stale store at the path-derived location that
        # does not hold the pinned commit (``ls-tree`` fails there).
        stale = root / "stale"
        stale.mkdir()
        self_git(stale, ["init", "-b", "main"])
        self_git(
            stale,
            ["submodule", "add", "--name", "alpha", str(outer_bare), "deps/outer"],
            allow_file=True,
        )
        self_git(stale, ["commit", "-m", "pin outer under the name alpha"])
        leftover = git_path(stale, "modules/deps/outer")
        if leftover is not None:
            self_git(root, ["init", "-q", "--bare", str(leftover)])
        result = audit(stale, select_subjects(stale, rev="HEAD", emit=False))
        record_case(
            cases,
            "name != path over a stale path-keyed store: nested pin stays in the work set",
            any(pin.path == "deps/outer/nested" for pin in result.pins) and not result.ok,
            observed_ok=result.ok,
            observed=[pin.as_dict() for pin in result.pins],
        )

        # (3) EMBEDDED .git: registered over an existing clone, never absorbed.
        embedded = root / "embedded"
        embedded.mkdir()
        self_git(embedded, ["init", "-b", "main"])
        commit_file(embedded, "README.md", "super\n", "root")
        self_git(
            embedded,
            ["clone", "-q", "--recurse-submodules", str(outer_bare), "deps/outer"],
            allow_file=True,
        )
        embedded_local = publish_outer_pinning_local_only_inner(
            embedded / "deps" / "outer", "embedded"
        )
        self_git(embedded, ["submodule", "add", str(outer_bare), "deps/outer"], allow_file=True)
        self_git(embedded, ["commit", "-m", "register the existing clone"])
        result = audit(embedded, select_subjects(embedded, rev="HEAD", emit=False))
        record_case(
            cases,
            "embedded-.git submodule: nested local-only pin refused",
            (embedded / "deps" / "outer" / ".git").is_dir()
            and _refuses(result, "deps/outer/nested", embedded_local),
            observed_ok=result.ok,
            observed=[pin.as_dict() for pin in result.pins],
        )

        # (4) The store HOLDS the pinned commit but cannot list its tree (a
        # commit whose tree object is absent). Its reachability passes, so only
        # the enumeration can refuse it --- this used to read as "no nested pins".
        treeless = root / "treeless"
        treeless.mkdir()
        self_git(treeless, ["init", "-b", "main"])
        self_git(treeless, ["submodule", "add", str(inner_bare), "deps/sub"], allow_file=True)
        self_git(treeless, ["commit", "-m", "pin inner"])
        module = treeless / "deps" / "sub"
        body = (
            f"tree {'d' * 40}\n"
            "author T <t@example.invalid> 0 +0000\n"
            "committer T <t@example.invalid> 0 +0000\n\n"
            "commit whose tree is absent\n"
        )
        broken = run_git(
            module,
            ["hash-object", "-t", "commit", "-w", "--literally", "--stdin"],
            input_text=body,
        ).stdout.strip()
        # Reachability must PASS so only the enumeration can refuse, and the
        # remote is the authority for reachability: the REMOTE advertises it.
        run_git(
            root,
            ["--git-dir", str(inner_bare), "hash-object", "-t", "commit", "-w", "--literally", "--stdin"],
            input_text=body,
        )
        run_git(root, ["--git-dir", str(inner_bare), "update-ref", "refs/heads/broken", broken])
        self_git(treeless, ["update-index", "--cacheinfo", f"160000,{broken},deps/sub"])
        self_git(treeless, ["commit", "-m", "pin a commit whose tree cannot be read"])
        result = audit(treeless, select_subjects(treeless, rev="HEAD", emit=False))
        record_case(
            cases,
            "store holds the pin but cannot list its tree: nested-pins-unreadable",
            not result.ok
            and [pin.status for pin in result.pins if pin.path == "deps/sub"]
            == ["nested-pins-unreadable"],
            observed_ok=result.ok,
            observed=[pin.as_dict() for pin in result.pins],
        )


def _scenario_common_module_stores(cases: list[dict[str, object]]) -> None:
    """Linked worktrees can reuse existing stores without relaxing tip checks."""
    with tempfile.TemporaryDirectory(prefix="trust-submodule-common-") as tmp:
        root = Path(tmp)
        inner_source = root / "inner-source"
        inner_bare = root / "inner.git"
        outer_source = root / "outer-source"
        outer_bare = root / "outer.git"
        primary = root / "primary"
        linked_tip = root / "linked-tip"
        removal = root / "removal"
        linked_removed = root / "linked-removed"

        inner_source.mkdir()
        self_git(inner_source, ["init", "-b", "main"])
        commit_file(inner_source, "README.md", "inner\n", "inner commit")
        self_git(root, ["clone", "--bare", str(inner_source), str(inner_bare)])
        outer_source.mkdir()
        self_git(outer_source, ["init", "-b", "main"])
        commit_file(outer_source, "README.md", "outer\n", "outer commit")
        self_git(
            outer_source,
            ["submodule", "add", "--name", "inner-name", str(inner_bare), "nested/leaf"],
            allow_file=True,
        )
        self_git(outer_source, ["commit", "-m", "outer pins inner"])
        self_git(root, ["clone", "--bare", str(outer_source), str(outer_bare)])
        primary.mkdir()
        self_git(primary, ["init", "-b", "main"])
        self_git(
            primary,
            ["submodule", "add", "--name", "outer-name", str(outer_bare), "deps/outer"],
            allow_file=True,
        )
        self_git(primary, ["commit", "-m", "super pins outer"])
        self_git(primary, ["submodule", "update", "--init", "--recursive"], allow_file=True)
        pinned_rev = run_git(primary, ["rev-parse", "HEAD"]).stdout.strip()
        outer_pin = run_git(primary / "deps/outer", ["rev-parse", "HEAD"]).stdout.strip()
        outer_store = worktree_git_dir(primary, "deps/outer")
        inner_store = worktree_git_dir(primary, "deps/outer/nested/leaf")
        assert outer_store is not None and inner_store is not None

        # Even a materialized outer module can itself be a linked worktree:
        # its nested modules remain under the outer repository's common dir.
        self_git(primary, ["worktree", "add", "--detach", str(linked_tip), pinned_rev])
        self_git(
            primary / "deps/outer",
            ["worktree", "add", "--detach", str(linked_tip / "deps/outer"), outer_pin],
        )
        selected_outer = worktree_git_dir(linked_tip, "deps/outer")
        assert selected_outer is not None and selected_outer != outer_store
        linked_pins = collect_pins(linked_tip, INDEX_SUBJECT)
        record_case(
            cases,
            "linked submodule gitdir recovers nested common-name store",
            any(
                pin.path == "deps/outer/nested/leaf"
                and pin.store == inner_store
                and not pin.nested_status
                for pin in linked_pins
            ),
            observed=[pin.path for pin in linked_pins],
        )
        tip_result = audit(linked_tip)
        record_case(
            cases,
            "common nested store does not replace a tip-named child checkout",
            not tip_result.ok
            and any(
                pin.path == "deps/outer/nested/leaf"
                and pin.status in {"missing-submodule-worktree", "uninitialized-submodule"}
                for pin in tip_result.failed
            ),
            observed=[pin.as_dict() for pin in tip_result.pins],
        )

        # Remove the path at the current tip, while an introduced historical
        # commit still names it. No clone exists in this new linked worktree.
        self_git(primary, ["worktree", "add", "--detach", str(removal), pinned_rev])
        self_git(removal, ["rm", "-f", "deps/outer"])
        self_git(removal, ["commit", "-m", "remove outer from current tip"])
        removed_rev = run_git(removal, ["rev-parse", "HEAD"]).stdout.strip()
        self_git(primary, ["worktree", "add", "--detach", str(linked_removed), removed_rev])
        local_candidate = git_path(linked_removed, "modules/outer-name")
        assert local_candidate is not None and not local_candidate.exists()
        history = Subject(
            kind="introduced",
            rev=pinned_rev,
            label="historical add before removal",
            gitlinks=(("deps/outer", outer_pin),),
        )
        def store_state(store: Path) -> tuple[str, bytes]:
            refs = run_git_dir(store, ["for-each-ref", "--format=%(objectname) %(refname)"])
            fetch = store / "FETCH_HEAD"
            return refs.stdout, fetch.read_bytes() if fetch.exists() else b"<no FETCH_HEAD>"

        before = (store_state(outer_store), store_state(inner_store))
        historical = audit(linked_removed, (history,))
        record_case(
            cases,
            "historical removed pin in linked worktree uses common stores without cloning",
            historical.ok
            and {pin.path for pin in historical.pins}
            == {"deps/outer", "deps/outer/nested/leaf"}
            and before == (store_state(outer_store), store_state(inner_store))
            and not local_candidate.exists(),
            observed=[pin.as_dict() for pin in historical.pins],
        )
        missing_tip = audit(
            linked_removed,
            (Subject(kind="revision", rev=pinned_rev, label="tip still names outer"),),
        )
        record_case(
            cases,
            "common stores do not replace a missing tip-named outer checkout",
            not missing_tip.ok
            and len(missing_tip.pins) == 2
            and any(
                pin.path == "deps/outer" and pin.status == "missing-submodule-worktree"
                for pin in missing_tip.failed
            ),
            observed=[pin.as_dict() for pin in missing_tip.pins],
        )


def _scenario_bounded_and_remembered(cases: list[dict[str, object]]) -> None:
    """Remember only what cannot change, and bound the rest honestly.

    Until 2026-11-13 every (pin, remote ref) ancestry question was a fresh
    network read, one per ref, with no total bound: the row ran 1h41m on a
    docs-only push. Ancestry between two ids is now remembered
    (``rt.AncestryMemory``), the remote's refs are still read every run, and a
    spent time bound is COULD NOT RUN with a rerun command, never a pass.
    Batching against a GitHub remote is pinned in
    scripts/tests/remote_tips_agh_test.py.
    """
    with tempfile.TemporaryDirectory(prefix="trust-submodule-memory-") as tmp:
        root = Path(tmp)
        source = root / "sub-source"
        bare = root / "submodule.git"
        super_repo = root / "super"
        memory = root / "memory"

        source.mkdir()
        self_git(source, ["init", "-b", "main"])
        commit_file(source, "README.md", "main\n", "main commit")
        self_git(source, ["checkout", "-q", "-b", "side"])
        commit_file(source, "SIDE.md", "pinned\n", "pinned side commit")
        pinned = run_git(source, ["rev-parse", "HEAD"]).stdout.strip()
        commit_file(source, "SIDE.md", "later\n", "later side commit")
        self_git(source, ["checkout", "-q", "main"])
        self_git(root, ["clone", "--bare", str(source), str(bare)])

        super_repo.mkdir()
        self_git(super_repo, ["init", "-b", "main"])
        self_git(super_repo, ["submodule", "add", str(bare), "deps/sub"], allow_file=True)
        self_git(super_repo / "deps" / "sub", ["checkout", "-q", pinned])
        self_git(super_repo, ["add", "--force", "deps/sub"])
        self_git(super_repo, ["commit", "-m", "pin a commit only refs/heads/side contains"])

        first_tips = rt.RemoteTips(memory=memory)
        first = audit(super_repo, (INDEX_SUBJECT,), first_tips)
        second_tips = rt.RemoteTips(memory=memory)
        second = audit(super_repo, (INDEX_SUBJECT,), second_tips)
        record_case(
            cases,
            "a second run asks no ancestry it already knows, and still reads the refs",
            first.ok and second.ok and first_tips.remembered == 0
            and second_tips.remembered == 2 and second_tips.ls_remote_calls == 1,
            first_ok=first.ok,
            second_ok=second.ok,
            remembered=[first_tips.remembered, second_tips.remembered],
            ls_remote_calls=second_tips.ls_remote_calls,
        )

        bounded = audit(super_repo, (INDEX_SUBJECT,), rt.RemoteTips(memory=memory, time_bound=0))
        text = render_text(bounded, rerun="RERUN-COMMAND")
        record_case(
            cases,
            "a spent time bound is COULD NOT RUN with a rerun command, never PASS",
            bounded.exit_code == 2 and "Rerun with: RERUN-COMMAND" in text and "PASS" not in text,
            exit_code=bounded.exit_code,
            text=text,
        )

        self_git(bare, ["branch", "-D", "side"])
        gone = audit(super_repo, (INDEX_SUBJECT,), rt.RemoteTips(memory=memory))
        record_case(
            cases,
            "remembered ancestry never outlives the ref: a deleted anchor is a finding",
            _refuses(gone, "deps/sub", pinned) and gone.exit_code == 1,
            exit_code=gone.exit_code,
            observed=[pin.as_dict() for pin in gone.pins],
        )


def self_check(*, json_output: bool = False) -> int:
    cases: list[dict[str, object]] = []
    with tempfile.TemporaryDirectory(prefix="trust-submodule-reachability-") as tmp:
        root = Path(tmp)
        source = root / "sub-source"
        bare = root / "submodule.git"
        super_repo = root / "super"

        source.mkdir()
        self_git(source, ["init", "-b", "main"])
        commit_file(source, "README.md", "reachable\n", "initial submodule commit")
        self_git(root, ["clone", "--bare", str(source), str(bare)])

        super_repo.mkdir()
        self_git(super_repo, ["init", "-b", "main"])
        self_git(super_repo, ["submodule", "add", str(bare), "deps/sub"], allow_file=True)
        self_git(super_repo, ["commit", "-m", "add reachable submodule"])

        reachable = audit(super_repo)
        assert_self_check_case(
            cases=cases,
            name="reachable remote-tracking pin",
            result=reachable,
            expected_status="reachable",
            expected_ok=True,
        )

        submodule = super_repo / "deps" / "sub"
        commit_file(submodule, "LOCAL_ONLY.txt", "local-only\n", "local-only submodule commit")
        self_git(super_repo, ["add", "deps/sub"])
        self_git(super_repo, ["commit", "-m", "pin local-only submodule commit"])

        unreachable = audit(super_repo)
        assert_self_check_case(
            cases=cases,
            name="local-only parent pin",
            result=unreachable,
            expected_status="not-reachable-from-remote",
            expected_ok=False,
            expected_publish_ref=pin_ref(
                run_git(submodule, ["rev-parse", "HEAD"]).stdout.strip()
            ),
        )

        initial_sha = run_git(submodule, ["rev-parse", "HEAD~1"]).stdout.strip()
        pinned_sha = run_git(submodule, ["rev-parse", "HEAD"]).stdout.strip()
        self_git(submodule, ["push", "origin", f"{pinned_sha}:{pin_ref(pinned_sha)}"])

        # ANCHORED REMOTELY, NEVER FETCHED HERE — the state that cost real
        # pushes. Until 2026-10-15 this was RED with "fetch the anchor" advice,
        # because only a LOCAL refs/pins ref counted. The remote's own
        # inventory is the authority now, and judging it copies no ref here.
        before = ref_state(submodule)
        anchored_not_fetched = audit(super_repo)
        assert_self_check_case(
            cases=cases,
            name="anchored on the remote, never fetched here: reachable (the remote is the authority)",
            result=anchored_not_fetched,
            expected_status="reachable",
            expected_ok=True,
            expected_ref_prefix="refs/pins/",
        )
        record_case(
            cases,
            "judging the remote anchor wrote no ref and no FETCH_HEAD in the store",
            ref_state(submodule) == before,
            before=before,
            after=ref_state(submodule),
        )

        # The converse, which the local predicate PASSED: a refs/pins ref
        # created here and never pushed, and a remote-tracking ref for a
        # branch the forge no longer has. Neither is fetchable by anyone else.
        commit_file(submodule, "LOCAL_TWO.txt", "local-two\n", "second local-only commit")
        local_two = run_git(submodule, ["rev-parse", "HEAD"]).stdout.strip()
        self_git(submodule, ["update-ref", pin_ref(local_two), local_two])
        self_git(submodule, ["update-ref", "refs/remotes/origin/deleted-topic", local_two])
        self_git(super_repo, ["add", "deps/sub"])
        self_git(super_repo, ["commit", "-m", "pin a commit only LOCAL refs name"])
        local_refs_only = audit(super_repo)
        assert_self_check_case(
            cases=cases,
            name="a local refs/pins ref and a stale remote-tracking ref are not durable",
            result=local_refs_only,
            expected_status="not-reachable-from-remote",
            expected_ok=False,
        )

        # STALE origin/main: the remote's main moved past the pin's commit and
        # this store's refs/remotes/origin/main never followed. GREEN, and the
        # stale ref is left exactly as it was.
        self_git(submodule, ["checkout", "-q", "--detach", initial_sha])
        commit_file(submodule, "ON_MAIN.txt", "on main\n", "published on main")
        on_main = run_git(submodule, ["rev-parse", "HEAD"]).stdout.strip()
        self_git(submodule, ["push", "-q", "origin", "HEAD:refs/heads/main"])
        self_git(submodule, ["update-ref", "refs/remotes/origin/main", initial_sha])
        self_git(super_repo, ["add", "deps/sub"])
        self_git(super_repo, ["commit", "-m", "pin a commit the remote's main carries"])
        before = ref_state(submodule)
        stale_main = audit(super_repo)
        assert_self_check_case(
            cases=cases,
            name="stale local origin/main, the remote's main has the pin: reachable",
            result=stale_main,
            expected_status="reachable",
            expected_ok=True,
            expected_ref_prefix="refs/heads/main",
        )
        record_case(
            cases,
            "the stale-origin/main verdict moved no ref (origin/main is still stale)",
            ref_state(submodule) == before
            and run_git(submodule, ["rev-parse", "refs/remotes/origin/main"]).stdout.strip()
            == initial_sha,
            before=before,
            after=ref_state(submodule),
        )

        # The pinned commit is not in this store AT ALL (another clone pushed
        # it and nothing here fetched). It used to be missing-commit-object.
        other = root / "other-clone"
        self_git(root, ["clone", "-q", str(bare), str(other)])
        commit_file(other, "ELSEWHERE.txt", "elsewhere\n", "pushed by another clone")
        elsewhere = run_git(other, ["rev-parse", "HEAD"]).stdout.strip()
        self_git(other, ["push", "-q", "origin", "HEAD:refs/heads/main"])
        self_git(super_repo, ["update-index", "--cacheinfo", f"160000,{elsewhere},deps/sub"])
        self_git(super_repo, ["commit", "-m", "pin a commit this store has never seen"])
        before = ref_state(submodule)
        never_seen = audit(super_repo)
        assert_self_check_case(
            cases=cases,
            name="pin absent from this store, on the remote's main: fetched by sha, reachable",
            result=never_seen,
            expected_status="reachable",
            expected_ok=True,
        )
        record_case(
            cases,
            "fetching the absent pin by sha brought its objects and wrote no ref",
            ref_state(submodule) == before
            and run_git(submodule, ["cat-file", "-e", f"{elsewhere}^{{commit}}"], check=False).returncode
            == 0,
            before=before,
            after=ref_state(submodule),
        )

        # THE NETWORK IS DOWN: the remote cannot be read. COULD NOT RUN (exit
        # 2), never a pass and never a finding, for a present pin and for an
        # absent one alike.
        away = root / "submodule.git.unreachable"
        bare.rename(away)
        try:
            offline = audit(super_repo)
            assert_self_check_case(
                cases=cases,
                name="remote unreadable: remote-unreadable, not a pass",
                result=offline,
                expected_status="remote-unreadable",
                expected_ok=False,
            )
            record_case(
                cases,
                "remote unreadable: exit 2 and COULD NOT RUN, never PASS",
                offline.exit_code == 2
                and "COULD NOT RUN" in render_text(offline)
                and "PASS" not in render_text(offline),
                observed_exit=offline.exit_code,
                rendered=render_text(offline),
            )
            self_git(super_repo, ["update-index", "--cacheinfo", f"160000,{'2' * 40},deps/sub"])
            self_git(super_repo, ["commit", "-m", "pin an absent commit while offline"])
            offline_absent = audit(super_repo)
            assert_self_check_case(
                cases=cases,
                name="remote unreadable, pin absent: remote-unreadable, not missing-commit-object",
                result=offline_absent,
                expected_status="remote-unreadable",
                expected_ok=False,
            )
        finally:
            away.rename(bare)

        missing_object_sha = "1" * 40
        self_git(
            super_repo,
            ["update-index", "--cacheinfo", f"160000,{missing_object_sha},deps/sub"],
        )
        self_git(super_repo, ["commit", "-m", "pin missing submodule object"])
        missing_object = audit(super_repo)
        assert_self_check_case(
            cases=cases,
            name="missing pinned commit object",
            result=missing_object,
            expected_status="missing-commit-object",
            expected_ok=False,
        )

        self_git(super_repo, ["submodule", "deinit", "-f", "deps/sub"])
        (super_repo / "deps" / "sub").mkdir(parents=True, exist_ok=True)
        uninitialized = audit(super_repo)
        assert_self_check_case(
            cases=cases,
            name="uninitialized submodule worktree",
            result=uninitialized,
            expected_status="uninitialized-submodule",
            expected_ok=False,
        )

    _scenario_subject_selection(cases)
    _scenario_nested_pins(cases)
    _scenario_introduced_commits(cases)
    _scenario_store_by_name(cases)
    _scenario_common_module_stores(cases)
    _scenario_bounded_and_remembered(cases)

    report = render_self_check_report(cases)
    failed = report["summary"]["failed"]  # type: ignore[index]
    if json_output:
        print(json.dumps(report, indent=2, sort_keys=True))
    elif failed:
        print(json.dumps(report, indent=2, sort_keys=True), file=sys.stderr)
        for case in cases:
            if not case["passed"]:
                print(f"  [BAD] {case['name']}", file=sys.stderr)
        print("FAIL: submodule reachability self-check failed", file=sys.stderr)
    else:
        for case in cases:
            print(f"  [ok ] {case['name']}")
        print(f"PASS: self-check proved {len(cases)} submodule pin behaviours")
    return 0 if not failed else 1


def ancestry_memory_dir(repo_root: Path) -> Optional[Path]:
    """Where answers to "is A an ancestor of B?" are remembered across runs.

    ``<git common dir>/trust-land/commit-ancestry``, beside the landing
    gate's own cache, shared by every worktree of the clone. Keyed by the two
    commit ids under a format version (``rt.AncestryMemory.FORMAT``), it is
    never invalidated: the answer cannot change; a fix to an answer source, or
    a new native reply contract, changes the version instead. Remote
    inventories are never stored there. check_ir_cohort.py computes the same
    directory (``ancestry_memory_dir`` there) and shares these answers.
    """
    common = git_common_dir(repo_root)
    return None if common is None else common / "trust-land" / "commit-ancestry"


def run_tips(repo_root: Path, time_bound: Optional[float]) -> "rt.RemoteTips":
    return rt.RemoteTips(memory=ancestry_memory_dir(repo_root), time_bound=time_bound)


def rerun_command(repo_root: Path, args: argparse.Namespace) -> str:
    """The command that asks the same question again (exit 2's next step)."""
    parts = ["python3", "scripts/check_submodule_remote_reachability.py"]
    if args.repo_root.resolve() != REPO_ROOT:
        parts += ["--repo-root", str(repo_root)]
    if args.rev is not None:
        parts += ["--rev", args.rev]
    if args.push_context:
        parts.append("--push-context")
    if args.time_bound != DEFAULT_TIME_BOUND_S:
        parts += ["--time-bound", f"{args.time_bound:g}"]
    command = shell_join(parts)
    pushed = os.environ.get(PUSH_REFS_ENV)
    if args.push_context and pushed is not None:
        command = f"{PUSH_REFS_ENV}={shlex.quote(pushed)} {command}"
    return command


def parse_args(argv: Sequence[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        prog="targo trust repo submodule-reachability",
        description=(
            "Fail closed when parent-pinned submodule commits are not contained "
            "in a branch or durable refs/pins/* anchor the submodule's remote "
            "publishes (read with ls-remote; no ref is written). Exit 1 is a "
            "finding, exit 2 is COULD NOT RUN (a remote could not be read)."
        )
    )
    parser.add_argument(
        "--repo-root",
        type=Path,
        default=REPO_ROOT,
        help="Trust checkout root to audit (default: repository containing this script)",
    )
    parser.add_argument("--json", action="store_true", help="emit machine-readable JSON")
    parser.add_argument(
        "--rev",
        default=None,
        help="judge the gitlinks of an explicit revision instead of the index",
    )
    parser.add_argument(
        "--push-context",
        action="store_true",
        help=(
            f"judge what the push in flight would publish (each pushed tip tree "
            f"plus every gitlink its introduced commits change), read from "
            f"${PUSH_REFS_ENV} (exported by scripts/hooks/pre-push); with the "
            f"variable unset the subject widens to the index"
        ),
    )
    parser.add_argument(
        "--time-bound",
        type=float,
        default=DEFAULT_TIME_BOUND_S,
        metavar="SECONDS",
        help=(
            "bound every remote read of this run together; a pin still unjudged "
            "when it is spent is COULD NOT RUN (exit 2), never a pass "
            f"(default {DEFAULT_TIME_BOUND_S:.0f})"
        ),
    )
    parser.add_argument(
        "--self-check",
        action="store_true",
        help=(
            "run an isolated local Git self-check instead of auditing this checkout; "
            "combine with --json for machine-readable assertions"
        ),
    )
    return parser.parse_args(argv)


def main(argv: Optional[Sequence[str]] = None) -> int:
    args = parse_args(sys.argv[1:] if argv is None else argv)
    if args.self_check:
        return self_check(json_output=args.json)

    repo_root = args.repo_root.resolve()
    try:
        subjects = select_subjects(
            repo_root, rev=args.rev, push_context=args.push_context
        )
        result = audit(repo_root, subjects, run_tips(repo_root, args.time_bound))
    except GitError as error:
        payload = {
            "repo_root": str(repo_root),
            "summary": {"checked": 0, "reachable": 0, "failed": 1},
            "error": str(error),
        }
        if args.json:
            print(json.dumps(payload, indent=2, sort_keys=True))
        else:
            print(f"FAIL: could not audit submodule reachability: {error}", file=sys.stderr)
        return 1

    if args.json:
        print(render_json(result))
    else:
        output = render_text(result, rerun_command(repo_root, args))
        if result.ok:
            print(output)
        else:
            print(output, file=sys.stderr)
    return result.exit_code


if __name__ == "__main__":
    raise SystemExit(main())
