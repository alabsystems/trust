#!/usr/bin/env python3
"""Fail-closed check for parent-pinned submodule commit reachability.

This release gate verifies that each commit recorded by the parent checkout's
submodule gitlinks is contained in at least one fetched remote-tracking branch
or durable ``refs/pins/<sha>`` archival ref in the corresponding submodule. It
does not fetch or push. If a parent points at a local-only submodule commit, a
fresh recursive clone may fail to reproduce that pin; this script reports that
condition and exits non-zero.

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

NESTED PINS COME FROM THE PINNED TREE, NOT THE SUBMODULE WORKTREE
-----------------------------------------------------------------
``submodule status --recursive`` can only descend into a submodule that is
materialized, so an uninitialized module takes its whole nested subtree out of
the work set. This reads every gitlink out of the PINNED tree instead --- for
children, out of the submodule's own object store via ``--git-dir``, which
survives a ``submodule deinit`` --- so the work set is a property of the
revision under audit and not of what happens to be checked out.

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
DEFAULT_REMOTE = "origin"
GITLINK_MODE = "160000"
NULL_SHA = "0" * 40
SHA_RE = re.compile(r"^[0-9a-fA-F]{40}$")

# A manifest command string is fixed and receives no stdin, so scripts/hooks/pre-push
# exports the ref lines git handed it and the SAME row text runs in both runners.
# This mirrors fast.revert-rationale / fast.measurement-provenance /
# fast.pin-regression / fast.dependency-constellation.
PUSH_REFS_ENV = "TRUST_PUSHED_REFS"


@dataclass(frozen=True)
class SubmodulePin:
    path: str
    sha: str
    state: str


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

    def as_dict(self) -> dict[str, object]:
        failed = self.failed
        return {
            "repo_root": str(self.repo_root),
            "source": self.source,
            "summary": {
                "checked": len(self.pins),
                "reachable": len(self.pins) - len(failed),
                "failed": len(failed),
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
) -> subprocess.CompletedProcess[str]:
    command = ["git", *extra_config, *args]
    completed = subprocess.run(
        command,
        cwd=repo,
        text=True,
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
    ``modules/<path>`` intact --- cannot silently remove that module's nested
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


def tree_gitlinks_in_store(git_dir: Path, revision: str) -> list[tuple[str, str]]:
    listed = run_git_dir(
        git_dir, ["ls-tree", "-r", "-z", "--full-tree", revision], check=False
    )
    if listed.returncode != 0:
        # The pinned commit is not in this store, so its nested gitlinks cannot
        # be enumerated. That is never silently absorbed: the pin itself is in
        # the work set and check_pin refuses it as missing-commit-object.
        return []
    return _parse_gitlinks(listed.stdout, sha_field=2, origin=f"tree {revision}")


def top_level_git_dir(repo_root: Path, path: str) -> Optional[Path]:
    """Git's per-worktree object store for a first-level submodule.

    A linked worktree has a ``.git`` FILE, so asking Git to resolve
    ``modules/<path>`` matters --- spelling it ``repo/.git/modules/<path>``
    classifies every submodule in a linked worktree as absent.
    """
    resolved = run_git(
        repo_root,
        ["rev-parse", "--path-format=absolute", "--git-path", f"modules/{path}"],
        check=False,
    )
    if resolved.returncode != 0:
        return None
    text = resolved.stdout.strip()
    return Path(text) if text else None


def collect_pins(repo_root: Path, subject: "Subject") -> tuple[SubmodulePin, ...]:
    """Every gitlink the subject names, recursively, read from PINNED trees.

    The recursion carries each module's object store so children are read from
    ``<parent git dir>/modules/<relpath>`` --- git's real on-disk layout --- and
    a cycle cannot spin: a path is expanded at most once.
    """
    if subject.kind == "index":
        top = index_gitlinks(repo_root)
    else:
        top = tree_gitlinks(repo_root, subject.rev)

    pins: list[SubmodulePin] = []
    seen: set[str] = set()
    queue: list[tuple[str, str, Optional[Path]]] = [
        (path, sha, top_level_git_dir(repo_root, path)) for path, sha in top
    ]
    while queue:
        path, sha, git_dir = queue.pop(0)
        if path in seen:
            continue
        seen.add(path)
        pins.append(SubmodulePin(path=path, sha=sha, state=" "))
        if git_dir is None or not git_dir.is_dir():
            continue
        for relpath, nested_sha in tree_gitlinks_in_store(git_dir, sha):
            queue.append(
                (f"{path}/{relpath}", nested_sha, git_dir / "modules" / relpath)
            )
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


def durable_refs_containing(path: Path, sha: str) -> tuple[str, ...]:
    result = run_git(
        path,
        [
            "for-each-ref",
            "--contains",
            sha,
            "--format=%(refname:short)",
            "refs/remotes",
            "refs/pins",
        ],
        check=False,
    )
    if result.returncode != 0:
        raise GitError(result.stderr.strip() or result.stdout.strip())
    return tuple(ref for ref in result.stdout.splitlines() if ref)


def shell_join(parts: Iterable[str]) -> str:
    return " ".join(shlex.quote(part) for part in parts)


def pin_ref(sha: str) -> str:
    return f"refs/pins/{sha}"


def publish_command(path: str, remote: str, sha: str) -> str:
    return shell_join(["git", "-C", path, "push", remote, f"{sha}:{pin_ref(sha)}"])


def fetch_anchor_command(path: str, remote: str, sha: str) -> str:
    """Retrieve an anchor that already exists on the remote.

    NOT ``fetch --all``. That expands each remote's DEFAULT refspec, which is
    ``+refs/heads/*:refs/remotes/<remote>/*`` — branches. ``refs/pins/*`` is a
    branch-free namespace by construction, so the one fetch a reader is most
    likely to reach for is the one that provably cannot help.
    """
    return shell_join(
        ["git", "-C", path, "fetch", remote, f"+{pin_ref(sha)}:{pin_ref(sha)}"]
    )


def remote_has_pin_anchor(path: Path, remote: str, sha: str) -> Optional[bool]:
    """Does the remote already carry ``refs/pins/<sha>``?

    ``ls-remote`` is a READ: it neither fetches nor pushes, so this keeps the
    module's stated contract while letting a failure name the ONE command that
    fixes it. Returns None when the remote cannot be reached, so an offline run
    degrades to offering both options rather than asserting the wrong one.
    """
    result = run_git(path, ["ls-remote", remote, pin_ref(sha)], check=False)
    if result.returncode != 0:
        return None
    return bool(result.stdout.strip())


def check_pin(repo_root: Path, pin: SubmodulePin) -> PinCheck:
    submodule_path = repo_root / pin.path
    remote = preferred_remote(submodule_path) if submodule_path.exists() else DEFAULT_REMOTE
    url = remote_url(submodule_path, remote) if submodule_path.exists() else ""
    publish_ref = pin_ref(pin.sha)
    command = publish_command(pin.path, remote, pin.sha)

    if not submodule_path.exists():
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

    if not git_dir_exists(submodule_path):
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

    object_check = run_git(
        submodule_path,
        ["cat-file", "-e", f"{pin.sha}^{{commit}}"],
        check=False,
    )
    if object_check.returncode != 0:
        return PinCheck(
            path=pin.path,
            sha=pin.sha,
            status="missing-commit-object",
            remote=remote,
            remote_url=url,
            publish_ref=publish_ref,
            # NOT `fetch --all --tags --prune`: that expands the default
            # refspec (branches) plus tags, and a pin that lands here is
            # characteristically on neither — an anchored pin lives only under
            # `refs/pins/*`. Fetch the sha itself, which works whether the
            # commit is on a branch, on an anchor ref, or reachable only by
            # identity.
            suggested_command=shell_join(["git", "-C", pin.path, "fetch", remote, pin.sha]),
            detail="pinned commit object is not present in the initialized submodule",
        )

    try:
        refs = durable_refs_containing(submodule_path, pin.sha)
    except GitError as error:
        return PinCheck(
            path=pin.path,
            sha=pin.sha,
            status="remote-reachability-error",
            remote=remote,
            remote_url=url,
            publish_ref=publish_ref,
            suggested_command=command,
            detail=str(error),
        )

    if refs:
        return PinCheck(
            path=pin.path,
            sha=pin.sha,
            status="reachable",
            remote_refs=refs,
            remote=remote,
            remote_url=url,
        )

    # The commit IS in the local object store; it is simply not named by any
    # local durable ref. There are TWO different worlds behind that one symptom
    # and they need opposite commands:
    #
    #   * the anchor does not exist yet          -> PUBLISH it (push)
    #   * the anchor exists but was never fetched -> RETRIEVE it (fetch)
    #
    # This used to always advise the push. Measured 2026-08-31 on
    # `first-party/ay b851ff38`: the anchor had been on the remote the whole
    # time and only the local clone lacked it, because `refs/pins/*` is outside
    # the default fetch refspec and nothing fetches it. Being told to publish an
    # anchor that already exists reads as "someone pushed a gitlink for an
    # unpublished commit" — a false accusation about another author's push
    # discipline, produced by the tool that was supposed to settle the question.
    # One read-only `ls-remote` distinguishes them.
    anchored_remotely = remote_has_pin_anchor(submodule_path, remote, pin.sha)
    if anchored_remotely is True:
        fix = fetch_anchor_command(pin.path, remote, pin.sha)
        detail = (
            "pinned commit is present locally and ALREADY ANCHORED at "
            f"{publish_ref} on {remote}; this clone has not fetched that ref "
            "(refs/pins/* is outside the default fetch refspec)"
        )
    elif anchored_remotely is False:
        fix = command
        detail = (
            "pinned commit is present locally, is not contained in refs/remotes/* "
            f"or refs/pins/*, and {remote} does not carry {publish_ref} either"
        )
    else:
        fix = f"{fetch_anchor_command(pin.path, remote, pin.sha)}   # if it is already anchored; otherwise: {command}"
        detail = (
            "pinned commit is present locally but not contained in refs/remotes/* "
            f"or refs/pins/*; {remote} could not be read, so it is unknown whether "
            f"{publish_ref} already exists"
        )

    return PinCheck(
        path=pin.path,
        sha=pin.sha,
        status="not-reachable-from-fetched-remotes",
        remote=remote,
        remote_url=url,
        publish_ref=publish_ref,
        suggested_command=fix,
        detail=detail,
    )


@dataclass(frozen=True)
class Subject:
    """One revision (or the index) whose gitlinks this run must judge."""

    kind: str  # "index" | "revision"
    rev: str  # "" for the index
    label: str


INDEX_SUBJECT = Subject(kind="index", rev="", label="index (git ls-files -s)")


def pushed_revisions(env: Mapping[str, str]) -> Optional[list[tuple[str, str]]]:
    """The (local sha, local ref) pairs a push in flight would publish.

    ``None`` means no push is in flight --- the variable is UNSET, so the
    caller widens to its historical reading. An empty LIST means a push that
    updates no ref that publishes a tree (empty-but-set, or all deletions),
    which also has nothing narrower to judge. Set-vs-unset is the test, not
    empty-vs-nonempty: an empty-but-set variable is a REAL push.
    """
    raw = env.get(PUSH_REFS_ENV)
    if raw is None:
        return None
    revisions: list[tuple[str, str]] = []
    seen: set[str] = set()
    for line in raw.splitlines():
        fields = line.split()
        if len(fields) < 2:
            continue
        local_ref, local_sha = fields[0], fields[1]
        # A deletion publishes no tree; its local sha is all zeroes.
        if not local_sha or set(local_sha) == {"0"}:
            continue
        if local_sha in seen:
            continue
        seen.add(local_sha)
        revisions.append((local_sha, local_ref))
    return revisions


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
    index (an actual pushed revision) or WIDENS back to the index. It never
    narrows to nothing --- an empty subject list would pass vacuously, which is
    the failure mode this whole lane exists to refuse.
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
        pushed = pushed_revisions(environ)
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
        if emit:
            print(f"SUBJECT: push ({len(pushed)} ref update(s))", file=out)
        return tuple(
            Subject(
                kind="revision",
                rev=resolve_revision(repo_root, sha, f"pushed ref {ref}"),
                label=f"pushed {ref} [{sha[:12]}]",
            )
            for sha, ref in pushed
        )
    if emit:
        print("SUBJECT: index/HEAD (no push context requested)", file=out)
    return (INDEX_SUBJECT,)


def audit(
    repo_root: Path, subjects: Sequence[Subject] = (INDEX_SUBJECT,)
) -> AuditResult:
    """Judge every distinct (path, sha) pin any subject names.

    A pin named by several pushed revisions is checked once and reports all of
    them, so a failure says which ref would publish it.
    """
    order: list[tuple[str, str]] = []
    named_by: dict[tuple[str, str], list[str]] = {}
    for subject in subjects:
        for pin in collect_pins(repo_root, subject):
            key = (pin.path, pin.sha)
            if key not in named_by:
                named_by[key] = []
                order.append(key)
            if subject.label not in named_by[key]:
                named_by[key].append(subject.label)

    checks: list[PinCheck] = []
    for path, sha in order:
        check = check_pin(repo_root, SubmodulePin(path=path, sha=sha, state=" "))
        checks.append(replace(check, named_by=tuple(named_by[(path, sha)])))
    return AuditResult(
        repo_root=repo_root,
        pins=tuple(checks),
        source="; ".join(subject.label for subject in subjects),
    )


def render_text(result: AuditResult) -> str:
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
            "PASS: every parent-pinned submodule commit is reachable from fetched "
            "remote branches or durable pin refs"
        )
        return "\n".join(lines)

    lines.append(
        "FAIL: parent-pinned submodule commit(s) are not reproducible from fetched "
        "remote branches or durable pin refs"
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
        "This audit does not emit a recursive fetch/update command. Materialize missing "
        "gitlinks through the canonical recreator; inspect and fetch any stale existing "
        "repository explicitly so local work is not reset."
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
            and push_result.failed[0].status == "not-reachable-from-fetched-remotes"
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
            expected_status="not-reachable-from-fetched-remotes",
            expected_ok=False,
            expected_publish_ref=pin_ref(
                run_git(submodule, ["rev-parse", "HEAD"]).stdout.strip()
            ),
        )

        pinned_sha = run_git(submodule, ["rev-parse", "HEAD"]).stdout.strip()
        self_git(submodule, ["push", "origin", f"{pinned_sha}:{pin_ref(pinned_sha)}"])

        # ANCHORED REMOTELY, NOT FETCHED HERE — the state that cost a real push.
        # Still not reachable (correct: no local durable ref names it), but the
        # fix is to RETRIEVE the anchor, not to publish one that already exists.
        anchored_not_fetched = audit(super_repo)
        assert_self_check_case(
            cases=cases,
            name="anchored on the remote but not fetched into this clone",
            result=anchored_not_fetched,
            expected_status="not-reachable-from-fetched-remotes",
            expected_ok=False,
            expected_command_contains=f"+{pin_ref(pinned_sha)}:{pin_ref(pinned_sha)}",
            # decided, not hedged: no push, and not the both-options fallback
            expected_command_excludes="push",
        )

        self_git(submodule, ["fetch", "origin", f"+{pin_ref(pinned_sha)}:{pin_ref(pinned_sha)}"])
        pinned = audit(super_repo)
        assert_self_check_case(
            cases=cases,
            name="branch-free durable pin ref",
            result=pinned,
            expected_status="reachable",
            expected_ok=True,
            expected_ref_prefix="pins/",
        )

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


def parse_args(argv: Sequence[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        prog="targo trust repo submodule-reachability",
        description=(
            "Fail closed when parent-pinned submodule commits are not contained "
            "in fetched refs/remotes/* or durable refs/pins/*."
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
            f"judge the revision(s) the push in flight would publish, read from "
            f"${PUSH_REFS_ENV} (exported by scripts/hooks/pre-push); with the "
            f"variable unset the subject widens to the index"
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
        result = audit(repo_root, subjects)
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
        output = render_text(result)
        if result.ok:
            print(output)
        else:
            print(output, file=sys.stderr)
    return 0 if result.ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
