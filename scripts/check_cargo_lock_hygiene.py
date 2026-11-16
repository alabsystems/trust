#!/usr/bin/env python3
"""Fail-closed guard for the `cargo --locked` refusal in this workspace.

WHY THIS EXISTS
---------------
Lanes repeatedly hit::

    error: cannot update the lock file ... because --locked was passed

and worked around it with ``cargo --offline`` plus ``git checkout -- Cargo.lock``.
That workaround is a footgun: the intermediate step leaves a *regenerated*
Cargo.lock in the tree, and committing it silently rewrites the dependency graph
of the whole constellation. One lane came within a step of doing exactly that.

The refusal is almost never a defect in the committed state. Measured on
2026-08-13 at superproject 352aa0306d: a pristine checkout of trust `main` with
all nine ``first-party/*`` submodules at their **recorded gitlinks** passes
``cargo metadata --locked`` with exit 0. The refusal is produced by the *working
tree*, when a submodule pointer is moved off its recorded gitlink onto a branch
whose manifest demands a version the root ``[patch]`` tables cannot supply.

THE MECHANISM
-------------
A Cargo ``[patch]`` entry applies only when the version of the *patched* crate
satisfies the dependency's version requirement. The root ``[patch]`` tables
redirect every ``alabsystems/*`` git edge to the checked-out submodule path,
so the committed Cargo.lock contains **zero** ``git+`` sources -- that is the
invariant this script enforces.

If a submodule is moved to a commit that asks for, say, ``ay-core = { version =
"0.8.0", git = "...ay.git", rev = "d58d6280" }`` while ``first-party/ay`` is at
0.9.0, then ``^0.8.0`` is not satisfied by 0.9.0, the patch silently does *not*
apply, and cargo must resolve the real git source -- which needs the network and
new lock entries. ``--locked`` correctly refuses.

THE REMEDY IS TO RESTORE THE POINTER, NEVER TO REGENERATE THE LOCK.


WHEN THE COMMITTED LOCK IS STALE
--------------------------------
"Almost never" happened on 2026-11-06 (LOCK-STALE-1). afec3dff20 added
``errno`` to ``crates/trust-stage-receipt`` and updated only that crate's own
lock. The root lock and ``crates/trust-qualification/Cargo.lock`` list the
crate as a path package and lacked the new edge. So every ``--locked`` build of
those two workspaces refused, with all twelve submodules at their pins. The
push builds no workspace (its profile is the eight rows of
DEV-MAIN-FOCUSED-VALIDATION-20261102), and no land gate ran on that landing.

So this script also resolves the committed locks ``--locked --offline`` and
fails on a refusal. It judges every tracked ``Cargo.lock`` that sits beside a
tracked ``Cargo.toml`` and is one of these (``select_locks``):
- the root lock, or a lock under ``crates/`` or ``targo-trust/`` outside
  ``fixtures/``. This rule is by directory, so a renamed or unreadable package
  keeps its lock judged.
- any other lock that lists, with no ``source``, a package whose manifest is
  tracked there, fixtures aside. This rule is by content: the ``fabric``
  fixture, the jobserver lock under ``compiler/``, ``library/``,
  ``src/bootstrap`` and ``src/tools/targo``.
- any other lock that names a git source from the first-party organization
  (``first_party_git``): a consumer that takes Trust crates only from git.
  None does today.

``vendor/`` holds foreign crates whose locks no ``--locked`` run reads.
``reports/`` holds dated evidence, kept unchanged, so it is not judged either:
a lock there that the rules select goes stale as the pins move, and relocking
it would change the evidence. The one selected on 2026-11-10 (the
formatter-scheduler qualification frontend) names paths in a temporary tree
that no longer exists; the K8 translator frontend's lock is selected by no
rule.

It also fails when:
- a Trust manifest does not parse;
- a standalone Trust workspace has no tracked lock;
- a first-party worktree is not the committed input. Then the locks it reads
  are not the committed ones, and no relock repairs that;
- a judged lock other than ``KEEPS_GIT`` (the ``fabric`` fixture) names a
  ``git+`` source or cannot be read or parsed (``judged_git_sources``,
  LOCK-STALE-2). Such a lock still resolves ``--locked``, so only this rule
  sees it. Sources are read from every entry Cargo reads in the parsed lock
  (``lock_entries``: ``[[package]]``, the legacy ``[root]`` table,
  ``[[patch.unused]]``), because Cargo accepts a respelled row. A lock with
  any other top-level key fails as unparsable. Locks are read as TOML 1.0;
  Cargo's own reader takes TOML 1.1 and ignores unknown keys, but writes
  neither, so such a lock fails here rather than being judged loosely.

The remedy for a stale lock is to relock that one workspace offline and commit
only the entries it adds, with no git source, or for ``KEEPS_GIT`` only the
revisions its manifests declare (``stale_remedy``).

The offline call, its 60 s bound, the one network fill when the host lacks
registry data, and the refusal's spellings are all the land gate's
(``scripts/land_gate.py``: ``answer_offline``, ``locked_metadata_refusal``,
``first_party_drift``, ``git_query_env``), so the two never disagree. The
call runs without ``CARGO_RESOLVER_LOCKFILE_PATH`` and its ``TARGO_`` twin
or any ``[unstable]`` variable (``metadata_env``; ``avoid-dev-deps`` turns
the ``--locked`` comparison off). No call is made when a config file targo
may read sets ``resolver.lockfile-path``, an ``include`` or an ``[unstable]``
table, or outside the tree a ``[patch]`` or ``paths`` table, or cannot be
read or parsed, or when an untracked ``.cargo/config`` stands beside the
committed ``config.toml`` (``lock_redirect``, LOCK-STALE-3 and -4). The
first three could name another lock or skip the comparison; ``[patch]``
resolves the lock against other sources than a clean host has, and
``paths`` replaces packages in the graph the land gate reads (it lets no
stale lock pass). Then one FAIL line names the file.
A refusal from a PATH targo older than the tree's ``[[patch.unused]]`` sort
is put to the land gate's private-copy check (``unused_order_answer``,
LAND-GATE-UNUSED-PATCH-ORDER-1, docs/LANDING_GATE.md): it passes only when
that targo's rewrite differs from the lock in the order of complete unused
rows alone, never with drift and never for the root workspace. The PASS line
names each lock that passed that way, and dead copies beside every judged
workspace are swept before any lock is judged.
Importing it re-executes this script under Python >= 3.11, as the land gate's
own rows do. The land gate runs ``targo`` from PATH, so ``$TARGO`` is not
read.
"""

from __future__ import annotations

import argparse
import contextlib
import io
import os
import re
import subprocess
import sys
import tempfile
import types
import unicodedata
import urllib.parse
from pathlib import Path
from typing import Callable, Dict, FrozenSet, Iterable, List, Optional, Set, Tuple

REPO_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO_ROOT / "scripts"))
import land_gate as lg  # noqa: E402  (re-executes under Python >= 3.11)
import tomllib  # noqa: E402

# `name = { version = "X", git = "...<repo>.git", rev = "..." }` on one line.
GIT_DEP_RE = re.compile(
    r'^\s*(?P<name>[A-Za-z0-9_-]+)\s*=\s*\{[^}]*?'
    r'version\s*=\s*"(?P<version>[^"]+)"[^}]*?'
    r'git\s*=\s*"(?P<url>[^"]*alabsystems/[^"]+)"'
    r'(?:[^}]*?rev\s*=\s*"(?P<rev>[0-9a-f]+)")?',
    re.MULTILINE,
)
# A registry package's download, the one offline failure Cargo reaches only
# after it accepted the lock. Every other `failed to ...` (to get a dependency,
# load a manifest, parse the lock, select a version, download the index) can
# come before that judgement, and so is undecided.
DOWNLOAD_MISS_RE = re.compile(r"^error: failed to download `", re.MULTILINE)
# The directories whose manifests a superproject commit edits as Trust's own.
TRUST_TOPS = ("crates", "targo-trust")
# Foreign crates: no `--locked` run reads their locks (vendor/openssl-sys is a
# path dependency of src/tools/targo, resolved through targo's own lock).
FOREIGN_TOPS = ("vendor",)
# Dated evidence, kept unchanged: a lock there records the resolution of a
# past build and is never relocked, so it is not judged (LOCK-STALE-3: the
# formatter-scheduler report's qualification workspace names paths in a
# temporary tree that no longer exists).
EVIDENCE_TOPS = ("reports",)
# The one judged lock that keeps git+ rows on purpose: an unpatched external
# consumer of trust-spec-temporal (docs/testing-strategy.md), whose rows
# fast.cargo-manifest-alignment checks against the revisions the manifests
# declare. Every other judged lock patches each git edge to a path, as the
# root lock does.
KEEPS_GIT = frozenset({"targo-trust/tests/fixtures/fabric"})
# The first-party organization on GitHub. A lock the directory rule does not
# select (outside crates/ and targo-trust/, or a fixture) is judged when it
# names a git source there, even with no path package of Trust's.
FIRST_PARTY_HOSTS = frozenset({"github.com", "ssh.github.com"})  # ssh.github.com: SSH on 443
FIRST_PARTY_ORG = "alabsystems"
# The top-level keys of Cargo's lock format. Cargo still reads the legacy
# `[root]` table as a package; any other key means a lock this script cannot
# read with certainty, so it fails as unparsable.
LOCK_KEYS = frozenset({"version", "package", "root", "metadata", "patch"})

# (exit status, or None when there was no answer in time; stderr or why not)
Answer = Tuple[Optional[int], str]
Resolver = Callable[[str], Answer]
# (drifted first-party worktrees, why drift could not be read)
Drift = Callable[[], Tuple[List[str], List[str]]]


def git(args: List[str], cwd: Path = REPO_ROOT) -> str:
    out = subprocess.run(
        ["git", *args], cwd=str(cwd), capture_output=True, text=True, check=False
    )
    return out.stdout


def dirty_submodules() -> List[Tuple[str, str, str]]:
    """Return (path, recorded_sha, worktree_sha) for moved gitlinks.

    ``git submodule status`` prefixes a moved pointer with ``+``. The recorded
    gitlink is read from HEAD rather than from that line, because the line
    reports the worktree sha.
    """
    moved = []
    for line in git(["submodule", "status"]).splitlines():
        if not line.startswith("+"):
            continue
        parts = line[1:].split()
        if len(parts) < 2:
            continue
        worktree_sha, path = parts[0], parts[1]
        recorded = git(["rev-parse", f"HEAD:{path}"]).strip()
        moved.append((path, recorded, worktree_sha))
    return moved


def explain_submodule(path: str, recorded: str, worktree: str) -> List[str]:
    """Name the version requirements that changed when the pointer moved."""
    lines = []
    sub = REPO_ROOT / path

    def deps_at(ref: str):
        found = {}
        blob = git(["show", f"{ref}:Cargo.toml"], cwd=sub)
        for m in GIT_DEP_RE.finditer(blob):
            found[m.group("name")] = (m.group("version"), m.group("rev") or "")
        return found

    before, after = deps_at(recorded), deps_at(worktree)
    for name in sorted(set(before) | set(after)):
        b, a = before.get(name), after.get(name)
        if b != a:
            bs = f'{b[0]} @ {b[1][:10]}' if b else "(absent)"
            as_ = f'{a[0]} @ {a[1][:10]}' if a else "(absent)"
            lines.append(f"      {name}: recorded wants {bs} -> worktree wants {as_}")
    return lines




def tracked_files(root: Path) -> Optional[List[str]]:
    """Every tracked path, or None when git cannot say. It runs `git ls-files -z`
    with no pathspec, in land_gate's git_query_env, which removes git's
    repository-local and config variables. A pathspec bends to
    GIT_LITERAL_PATHSPECS, and a GIT_INDEX_FILE or GIT_DIR would answer for
    another index."""
    try:
        proc = subprocess.run(["git", "-C", str(root), "ls-files", "-z"], capture_output=True,
                              text=True, env=lg.git_query_env(), check=False, timeout=60)
    except (OSError, subprocess.TimeoutExpired):
        return None
    if proc.returncode != 0:
        return None
    return [path for path in proc.stdout.split("\0") if path]


def in_workspace(directory: str, name: str) -> str:
    return name if directory == "." else f"{directory}/{name}"


def trust_manifests(tracked: Iterable[str], read: Callable[[str], str]
                    ) -> Tuple[Dict[str, dict], List[str]]:
    """The parsed tracked manifests under crates/ and targo-trust/, fixtures
    aside, and one problem per manifest that does not parse. A fixture is a
    test's input. A lock that lists only its own fixture package is that test's
    to judge: fold-crate-lambda-calculus-3.5.0/SOURCE is deliberately not a
    workspace."""
    parsed: Dict[str, dict] = {}
    problems: List[str] = []
    for path in tracked:
        parts = Path(path).parts
        if (len(parts) < 2 or parts[0] not in TRUST_TOPS or parts[-1] != "Cargo.toml"
                or "fixtures" in parts):
            continue
        try:
            parsed[path] = tomllib.loads(read(path))
        except (OSError, UnicodeDecodeError, tomllib.TOMLDecodeError) as error:
            problems.append(f"{path} does not parse, so Cargo cannot read it: {error}")
    return parsed, problems


def lock_entries(lock_text: str) -> Optional[List[dict]]:
    """Every package entry Cargo reads from a lock: `[[package]]`, the legacy
    `[root]` table and `[[patch.unused]]`. None when the lock does not parse,
    has a key outside LOCK_KEYS or a `[patch]` key other than `unused`, or
    holds an entry that is not a table. Cargo reads a lock by its meaning, so
    every spelling it accepts has to be read the way it reads it."""
    try:
        document = tomllib.loads(lock_text)
    except tomllib.TOMLDecodeError:
        return None
    if not set(document) <= LOCK_KEYS:
        return None
    patch = document.get("patch", {})
    if not isinstance(patch, dict) or not set(patch) <= {"unused"}:
        return None
    root = document.get("root")
    groups = [document.get("package", []), [root] if root is not None else [],
              patch.get("unused", [])]
    entries: List[dict] = []
    for group in groups:
        if not isinstance(group, list):
            return None
        for entry in group:
            if not isinstance(entry, dict):
                return None
            entries.append(entry)
    return entries


def path_packages(lock_text: str) -> Optional[Set[str]]:
    """The names of a lock's packages with no `source` (its members and path
    dependencies), or None when the lock does not parse."""
    entries = lock_entries(lock_text)
    if entries is None:
        return None
    return {entry["name"] for entry in entries if isinstance(entry.get("name"), str)
            and "source" not in entry}


def git_packages(lock_text: str) -> Optional[List[Tuple[str, str, str]]]:
    """(name, version, source) of every entry whose source is git, or None
    when the lock does not parse (`lock_entries`). A respelled row
    (`source="git+..."`) is a git source to Cargo, and so it is here."""
    entries = lock_entries(lock_text)
    if entries is None:
        return None
    found = set()
    for entry in entries:
        source = entry.get("source", "")
        if not isinstance(source, str):
            return None
        if source.startswith("git+"):
            found.add((str(entry.get("name", "?")), str(entry.get("version", "?")), source))
    return sorted(found)


def first_party_git(source: str) -> bool:
    """Whether a git source is a repository of the first-party organization.
    Cargo writes the manifest's spelling into the lock, so the host and the
    first path segment are compared after removing what GitHub and Cargo's
    URL reading ignore: scheme, user and port, percent-encoding, compatibility
    forms (NFKC: full-width letters), letter case, a trailing `.` and `www.`,
    and empty segments. A URL that does not parse counts as first-party, so
    its lock is judged rather than skipped."""
    try:
        parsed = urllib.parse.urlsplit(git_url(source))
        host = parsed.hostname or ""
    except ValueError:
        return True
    host = unicodedata.normalize("NFKC", urllib.parse.unquote(host)).casefold().rstrip(".")
    if host.startswith("www."):
        host = host[len("www."):]
    path = unicodedata.normalize("NFKC", urllib.parse.unquote(parsed.path)).casefold()
    segments = [segment for segment in path.split("/") if segment]
    return host in FIRST_PARTY_HOSTS and bool(segments) and segments[0] == FIRST_PARTY_ORG


def git_url(source: str) -> str:
    """`git+<url>?rev=..#<sha>` -> `<url>`, the key of the `[patch."<url>"]`
    table that would redirect it."""
    return source[len("git+"):].split("?")[0].split("#")[0]


def select_locks(tracked: List[str], read: Callable[[str], str]) -> Tuple[List[str], List[str]]:
    """(the workspace directories whose committed lock to judge, the problems
    that fail the run before any lock is judged). The rules are in the module
    docstring. A lock that cannot be read or parsed is judged."""
    manifests, problems = trust_manifests(tracked, read)
    names = set()
    for document in manifests.values():
        package = document.get("package")
        name = package.get("name") if isinstance(package, dict) else None
        if isinstance(name, str):
            names.add(name)
    present = set(tracked)
    chosen = set()
    for path in tracked:
        lock = Path(path)
        if lock.name != "Cargo.lock" or lock.parts[0] in FOREIGN_TOPS + EVIDENCE_TOPS:
            continue
        directory = lock.parent.as_posix()
        if in_workspace(directory, "Cargo.toml") not in present:
            continue
        if directory == "." or (lock.parts[0] in TRUST_TOPS and "fixtures" not in lock.parts):
            chosen.add(directory)
            continue
        try:
            text = read(path)
        except (OSError, UnicodeDecodeError):
            chosen.add(directory)
            continue
        listed, gits = path_packages(text), git_packages(text)
        if listed is None or gits is None or listed & names:
            chosen.add(directory)
        elif any(first_party_git(source) for _, _, source in gits):
            chosen.add(directory)
    for manifest, document in sorted(manifests.items()):
        lock = in_workspace(Path(manifest).parent.as_posix(), "Cargo.lock")
        if "workspace" in document and lock not in present:
            problems.append(f"{manifest} is a standalone workspace with no tracked {lock}: "
                            "every --locked build of it refuses")
    return sorted(chosen), problems


def judged_git_sources(workspaces: List[str], read: Callable[[str], str]) -> List[str]:
    """One problem per judged lock, the root's (`git_source_check`) and
    KEEPS_GIT aside, that names a git+ source or cannot be read or parsed.
    Such a lock
    builds a sibling crate from a remote revision, not from the submodule the
    pins name. Measured 2026-11-06 (LOCK-STALE-2): the trust-cg pin b8c428ff
    gave trust-cg-verify a git edge to clean-olean, which
    crates/trust-spec-temporal did not patch, so a plain relock fetched it
    from git, and that lock then resolved --locked like any other."""
    problems: List[str] = []
    for directory in workspaces:
        if directory == "." or directory in KEEPS_GIT:
            continue
        lock = in_workspace(directory, "Cargo.lock")
        try:
            text = read(lock)
        except (OSError, UnicodeDecodeError) as error:
            problems.append(f"{lock} could not be read for git+ sources: {error}")
            continue
        found = git_packages(text)
        if found is None:
            problems.append(f"{lock} does not parse as a Cargo lock (read as TOML 1.0), so its "
                            "git+ sources cannot be read")
            continue
        if found:
            named = "; ".join(f"{name} {version} from {git_url(source)}"
                              for name, version, source in found)
            rows = "; ".join(sorted({f'[patch."{git_url(source)}"] {name} = {{ path = ... }}'
                                     for name, _, source in found}))
            problems.append(
                f"{lock} names git+ sources ({named}), so that workspace builds them from a "
                f"remote revision, not the submodule the pins name. Add the missing row to "
                f"{in_workspace(directory, 'Cargo.toml')} ({rows}) and relock. If the row is "
                "there, a moved submodule pointer stopped it applying: restore the pointer "
                "(this script's docstring). Do not commit a lock that names one")
    return problems


def classify(returncode: Optional[int], stderr: str, git_sourced: bool = False
             ) -> Tuple[str, str]:
    """Return `current`, `uncached`, `stale` or `undecided`, with the line that
    decided it.

    Cargo judges the lock while it resolves, before it downloads any registry
    package. So an offline download miss (`uncached`) means the lock was
    already accepted. Measured 2026-11-06 on crates/trust-spec-temporal: with
    the errno edge removed, it refuses the lock; with the edge restored, it
    fails later, on the download of `cc v1.4.2`. Git sources are fetched
    during resolution and fail with other words, which are undecided. A lock
    that keeps git sources on purpose (`git_sourced`, the fabric fixture) gets
    its own wording for that."""
    if returncode is None:
        return "undecided", stderr
    if returncode == 0:
        return "current", ""
    said = lg.cargo_error(stderr)
    if lg.locked_metadata_refusal(stderr):
        return "stale", said
    if DOWNLOAD_MISS_RE.search(stderr):
        return "uncached", said
    if lg.escaped_git_source(stderr):
        if git_sourced:
            return "undecided", (f"{said} (this lock keeps git sources on purpose, and their "
                                 "checkouts are not on this host)")
        return "undecided", f"{said} (a git source was reached offline: no [patch] captured it)"
    return "undecided", f"exit {returncode}: {said}"


def land_gate_ask(drift: Drift, fills_git: FrozenSet[str] = frozenset(),
                  by_order: Optional[Set[str]] = None
                  ) -> Callable[[str], Tuple[object, Optional[str]]]:
    """The land gate's bounded offline call on one manifest. When only a
    registry gap stops it, the land gate fills from the network once
    (`answer_offline`). A manifest in `fills_git` (KEEPS_GIT's, which keeps
    git sources on purpose) gets the same single fill when only its git
    checkouts are missing; any other git-sourced lock fails the git+ rule, so
    asking the network for it would be wasted. Under `--locked`, neither form
    can move a lock. A refusal the land gate's private lock copy answers
    (`unused_order_answer`) may fill once without `--locked`, on the copy,
    only when the copy's resolve is already the committed lock's. After one
    fill fails the network is not asked again. Each manifest the copy
    answers is added to `by_order`, so the PASS line can name it."""
    state: Dict[str, Optional[str]] = {"no_network": None}

    def ask(manifest: str):
        proc, hung, state["no_network"] = lg.answer_offline(manifest, state["no_network"],
                                                           drift=drift)
        if (proc is not None and proc.returncode != 0 and lg.escaped_git_source(proc.stderr)
                and manifest in fills_git and state["no_network"] is None
                and not drift()[0]):
            filled, why = lg.fill_registry(manifest)
            if why is None:
                proc, hung = lg.offline_metadata(manifest)
            else:
                state["no_network"] = why
                if filled is not None and lg.locked_metadata_refusal(filled.stderr):
                    proc, hung = filled, None
        if (proc is not None and proc.returncode != 0 and lg.locked_metadata_refusal(proc.stderr)
                and not any(drift())):
            # A PATH targo that predates the tree's unused-row sort refuses
            # every such lock (LAND-GATE-UNUSED-PATCH-ORDER-1); the land gate
            # judges its rewrite on a private copy, and so does this check.
            try:
                rel = Path(manifest).resolve().relative_to(lg.REPO_ROOT.resolve())
                committed = (Path(manifest).parent / "Cargo.lock").read_bytes()
            except (OSError, ValueError):
                rel = committed = None
            if rel is not None and committed is not None:
                copied, state["no_network"] = lg.unused_order_answer(
                    str(rel), committed, state["no_network"], may_fill=True)
                if copied is not None:
                    proc, hung = copied, None
                    if by_order is not None:
                        by_order.add(manifest)
        return proc, hung
    return ask


def resolver_for(root: Path, ask: Callable[[str], Tuple[object, Optional[str]]]) -> Resolver:
    """Resolve `<root>/<directory>/Cargo.toml` through `ask`. A targo that
    cannot start answers 127, which is undecided, never a pass."""
    def resolve(directory: str) -> Answer:
        try:
            proc, hung = ask(str(root / directory / "Cargo.toml"))
        except OSError as error:
            return 127, f"error: cannot run targo: {error}"
        if proc is None:
            return None, hung or "offline targo metadata did not finish"
        return proc.returncode, proc.stderr
    return resolve


def stale_remedy(directory: str, keeps_git: bool = False) -> str:
    """The relock, and when its diff may be committed. A lock that keeps git
    rows on purpose may move them only to the revisions its manifests declare;
    any other lock must stay free of them (`judged_git_sources`)."""
    relock = (f"targo metadata --offline --format-version 1 --manifest-path "
              f"{in_workspace(directory, 'Cargo.toml')} >/dev/null, then commit "
              f"{in_workspace(directory, 'Cargo.lock')} only if ")
    if keeps_git:
        return relock + ("every git+ package stays git, no registry version changes, and "
                         "scripts/check_cargo_manifest_alignment.py accepts its revisions")
    return relock + ("its diff adds entries, changes no version and names no git+ source "
                     "(a git+ row means a [patch] row is missing)")


def locked_check(workspaces: List[str], resolve: Resolver, drift: Drift,
                 git_sourced: FrozenSet[str] = frozenset(),
                 by_order: Callable[[str], bool] = lambda directory: False) -> int:
    """Fail unless the first-party worktrees are the committed inputs and
    every workspace's committed lock resolves `--locked`, or through the
    land gate's private lock copy (`by_order` says which), which the PASS
    line names."""
    if not workspaces:
        print("FAIL: no committed workspace lock found to resolve; nothing was judged",
              file=sys.stderr)
        return 1
    drifted, unknown = drift()
    if drifted or unknown:
        print("FAIL: the committed locks were not judged: the first-party worktrees Cargo "
              "would read are not the committed inputs", file=sys.stderr)
        for path in drifted:
            print(f"  {path}: off its gitlink, a staged gitlink, or tracked edits",
                  file=sys.stderr)
        for why in unknown:
            print(f"  could not be read: {why}", file=sys.stderr)
        print("  No relock or fetch repairs that. Restore them (scripts/submodule_sync.sh) "
              "and rerun before touching any lock.", file=sys.stderr)
        return 1
    stale, undecided, uncached, ordered = [], [], 0, []
    for directory in workspaces:
        returncode, stderr = resolve(directory)
        verdict, line = classify(returncode, stderr, directory in git_sourced)
        if verdict == "stale":
            stale.append((directory, line))
        elif verdict == "undecided":
            undecided.append((directory, line))
        elif verdict == "uncached":
            uncached += 1
        elif verdict == "current" and by_order(directory):
            ordered.append(directory)
    if not stale and not undecided:
        note = f"; {uncached} with registry sources not cached offline" if uncached else ""
        if ordered:
            print(f"PASS: all {len(workspaces)} judged committed locks resolve: "
                  f"{len(workspaces) - len(ordered)} --locked, and {len(ordered)} "
                  f"({', '.join(ordered)}) through the land gate's private lock copy, which the "
                  "PATH targo refuses under --locked and rewrites only in unused-row order "
                  f"(LAND-GATE-UNUSED-PATCH-ORDER-1){note}")
        else:
            print(f"PASS: all {len(workspaces)} judged committed locks resolve --locked{note}")
        return 0
    for directory, line in stale:
        print(f"FAIL: {in_workspace(directory, 'Cargo.lock')} is stale: {line}",
              file=sys.stderr)
    for directory, line in undecided:
        print(f"FAIL: {in_workspace(directory, 'Cargo.lock')} could not be judged "
              f"offline: {line}", file=sys.stderr)
    print("", file=sys.stderr)
    if stale:
        print("  Every first-party worktree is its committed input, so the committed lock is",
              file=sys.stderr)
        print("  stale: a manifest changed without every lock that lists its package. For "
              "each one:", file=sys.stderr)
        for directory, _ in stale:
            print(f"    {stale_remedy(directory, directory in git_sourced)}", file=sys.stderr)
            if directory in git_sourced:
                print("    (this lock keeps git+ rows on purpose: the diff must keep every one; "
                      "docs/testing-strategy.md)", file=sys.stderr)
    if undecided:
        print("  An undecided lock is not a pass. The network was asked once, where only what",
              file=sys.stderr)
        print("  this host lacks stopped it. Where it is reachable, run the online form",
              file=sys.stderr)
        print("  (under --locked it cannot move the lock), then rerun:", file=sys.stderr)
        for directory, _ in undecided:
            print(f"    targo metadata --locked --format-version 1 --manifest-path "
                  f"{in_workspace(directory, 'Cargo.toml')} >/dev/null", file=sys.stderr)
        print("  A timeout means another Cargo holds $CARGO_HOME/.package-cache.",
              file=sys.stderr)
    return 1


def git_source_check(lock: Path, explain: bool, moved: List[Tuple[str, str, str]]) -> int:
    if not lock.is_file():
        print(f"FAIL: {lock} does not exist", file=sys.stderr)
        return 2

    found = git_packages(lock.read_text(encoding="utf-8"))
    if found is None:
        print(f"FAIL: {lock} does not parse as a Cargo lock (read as TOML 1.0), so its git+ "
              "sources cannot be read", file=sys.stderr)
        return 1
    sources = [f"{name} {version}: {source}" for name, version, source in found]

    if not sources:
        print("PASS: Cargo.lock contains zero git+ sources "
              "(every first-party git edge is patched to a submodule path)")
        if moved and explain:
            print("\nnote: these submodule pointers are moved off their recorded "
                  "gitlinks, which can still make `cargo --locked` refuse:")
            for path, recorded, worktree in moved:
                print(f"  {path}: recorded {recorded[:12]} -> worktree {worktree[:12]}")
        return 0

    print("FAIL: Cargo.lock contains git+ sources; it has been regenerated.",
          file=sys.stderr)
    print("", file=sys.stderr)
    for s in sources:
        print(f"  {s}", file=sys.stderr)
    print("", file=sys.stderr)
    print("  The committed lock redirects every alabsystems/* git edge to a", file=sys.stderr)
    print("  submodule path via the root [patch] tables, so a git+ source means", file=sys.stderr)
    print("  a [patch] entry stopped applying and cargo re-resolved from git.", file=sys.stderr)
    print("  A [patch] applies only when the patched crate's version SATISFIES", file=sys.stderr)
    print("  the dependency's version requirement.", file=sys.stderr)

    if moved:
        print("", file=sys.stderr)
        print("  Moved submodule pointers (the usual cause):", file=sys.stderr)
        for path, recorded, worktree in moved:
            print(f"    {path}: recorded {recorded[:12]} -> worktree {worktree[:12]}",
                  file=sys.stderr)
            for line in explain_submodule(path, recorded, worktree):
                print(line, file=sys.stderr)

    print("", file=sys.stderr)
    print("  REMEDY: restore the submodule pointer, do NOT commit this lock:", file=sys.stderr)
    print("    git checkout -- Cargo.lock", file=sys.stderr)
    for path, recorded, _ in moved or []:
        print(f"    git -C {path} checkout --detach {recorded}", file=sys.stderr)
    print("", file=sys.stderr)
    print("  If the version bump is intended, the whole constellation must move", file=sys.stderr)
    print("  together (the patched submodule too) -- that is a pinning decision,", file=sys.stderr)
    print("  not a lockfile edit.", file=sys.stderr)
    return 1




def run_checks(lock: Path, explain: bool, moved: List[Tuple[str, str, str]],
               tracked: Optional[List[str]], read: Callable[[str], str],
               resolve: Resolver, drift: Drift, redirect: Optional[str] = None,
               by_order: Callable[[str], bool] = lambda directory: False,
               sweep: Callable[[List[str]], None] = lambda workspaces: None) -> int:
    """Both rules; either one failing fails the run. The git+ rule covers the
    root lock and every other judged lock but KEEPS_GIT. The root lock lists
    every crates/ member, so a selection without it read the tree wrongly.
    `redirect` is `lg.lock_redirect`'s answer for this host: when set, no
    metadata call can judge a lock here, so none is made and one FAIL line
    names the file. Before any lock is judged, `sweep` gets the judged
    workspaces (main removes the private lock copies a killed run left beside
    them); `by_order` is locked_check's."""
    sources_rc = git_source_check(lock, explain, moved)
    if tracked is None:
        print("FAIL: git ls-files did not answer; no lock was judged", file=sys.stderr)
        return sources_rc or 1
    workspaces, problems = select_locks(tracked, read)
    problems += judged_git_sources(workspaces, read)
    for problem in problems:
        print(f"FAIL: {problem}", file=sys.stderr)
    if "." not in workspaces:
        print(f"FAIL: the root lock was not selected ({len(workspaces)} selected); "
              "the tracked file list is not this tree's", file=sys.stderr)
        return sources_rc or 1

    if redirect:
        print(f"FAIL: no lock was judged --locked: {redirect}. Remove that setting, or judge on a "
              "host that does not read that file, then rerun", file=sys.stderr)
        locked_rc = 1
    else:
        sweep(workspaces)
        locked_rc = locked_check(workspaces, resolve, drift, KEEPS_GIT & set(workspaces), by_order)
    if problems or sources_rc:
        print(f"FAIL: the {len(problems) + (1 if sources_rc else 0)} problem(s) above fail "
              "this run, whatever the resolution found", file=sys.stderr)
    return sources_rc or locked_rc or (1 if problems else 0)


def tree_wiring(root: Path, drift: Drift
                ) -> Tuple[Resolver, Callable[[str], bool], Callable[[List[str]], None]]:
    """What main() hands run_checks for the tree at `root`: the resolver, the
    PASS line's by_order (sharing one set of copy-answered manifests with the
    resolver) and the sweep, over the parents of the judged workspaces but the
    root, where unused_order_answer makes its copies (beside each workspace,
    under the land gate's root)."""
    copied: Set[str] = set()
    resolve = resolver_for(root, land_gate_ask(
        drift, frozenset(str(root / d / "Cargo.toml") for d in KEEPS_GIT), copied))

    def by_order(directory: str) -> bool:
        return str(root / directory / "Cargo.toml") in copied

    def sweep(workspaces: List[str]) -> None:
        lg.sweep_dead_unused_order_copies(
            parents=sorted({(lg.REPO_ROOT / d).parent for d in workspaces if d != "."}))
    return resolve, by_order, sweep


def selftest() -> int:
    """Exercise the locked-resolution check without reading this tree's locks."""
    failures: List[str] = []

    def expect(condition: bool, what: str) -> None:
        if not condition:
            failures.append(what)

    def quiet(call: Callable[[], int]) -> Tuple[int, str]:
        out = io.StringIO()
        with contextlib.redirect_stdout(out), contextlib.redirect_stderr(out):
            code = call()
        return code, out.getvalue()

    no_drift: Drift = lambda: ([], [])
    real_lg = (lg.answer_offline, lg.fill_registry, lg.offline_metadata)
    refusal = ("error: cannot update the lock file /w/Cargo.lock because --locked "
               "was passed to prevent this\n")
    miss = "error: failed to download `cc v1.4.2`\n\nCaused by:\n  but --offline was specified\n"
    git_offline = ("error: failed to get `ty` as a dependency of package `fab v0.1.0`\n\n"
                   "Caused by:\n  can't checkout from 'https://github.com/alabsystems/ty.git': "
                   "you are in the offline mode (--offline)\n")
    for returncode, stderr, want in [
        (0, "", "current"),
        (101, "warning: x\n" + refusal, "stale"),
        (101, "error: the lock file /w/Cargo.lock needs to be updated but --locked "
              "was passed to prevent this\n", "stale"),
        (101, "error: cannot create the lock file /w/Cargo.lock because --locked was "
              "passed to prevent this\n", "stale"),
        (101, miss, "uncached"),
        (101, refusal + miss, "stale"),
        (101, "warning: failed to download `cc v1.4.2`, retrying\n"
              "error: failed to get `x` as a dependency of package `y v0.1.0`\n", "undecided"),
        (101, "error: failed to download from `https://index.crates.io/config.json`\n",
         "undecided"),
        (101, "error: failed to get `x` as a dependency of package `y v0.1.0`\n", "undecided"),
        (101, "error: failed to load manifest for workspace member `/w/a`\n", "undecided"),
        (101, "error: failed to parse lock file at: /w/Cargo.lock\n", "undecided"),
        (101, "error: failed to select a version for the requirement `z = \"^1\"`\n",
         "undecided"),
        (101, "error: current package believes it's in a workspace when it's not:\n",
         "undecided"),
        (101, git_offline, "undecided"),
        (101, "", "undecided"),
        (75, "atpkg: build cache ownership refused\n", "undecided"),
        (127, "error: cannot run targo: [Errno 2] No such file or directory: 'targo'",
         "undecided"),
        (None, "offline targo metadata did not finish: no answer in 60 s", "undecided"),
    ]:
        got = classify(returncode, stderr)[0]
        expect(got == want, f"classify({returncode}, {stderr!r}) = {got}, want {want}")
    expect("on purpose" in classify(101, git_offline, git_sourced=True)[1]
           and "no [patch]" in classify(101, git_offline)[1],
           "a git checkout missing offline is not worded by whether the lock keeps git sources")
    argv = lg.metadata_argv("w/Cargo.toml")
    expect("--locked" in argv and "--offline" in argv, f"metadata_argv = {argv}")

    def package(name: str, workspace: bool = False) -> str:
        return f'[package]\nname = "{name}"\nversion = "0.1.0"\n' + ("[workspace]\n" if workspace else "")

    def lock(*entries: Tuple[str, bool]) -> str:
        return "version = 4\n" + "".join(
            f'\n[[package]]\nname = "{name}"\nversion = "1.0.0"\n'
            + ('source = "registry+https://github.com/rust-lang/crates.io-index"\n'
               if registry else "")
            for name, registry in entries)

    files = {
        "Cargo.toml": "[workspace]\n", "Cargo.lock": lock(("a", False), ("libc", True)),
        "crates/a/Cargo.toml": package("a", True), "crates/a/Cargo.lock": lock(("a", False)),
        "crates/b/Cargo.toml": package("b"),
        "crates/renamed/Cargo.toml": package("new-name", True),
        "crates/renamed/Cargo.lock": lock(("old-name", False)),
        "crates/a/fixtures/f/Cargo.toml": package("f", True),
        "crates/a/fixtures/f/Cargo.lock": lock(("f", False)),
        "targo-trust/tests/fixtures/fab/Cargo.toml": package("fab"),
        "targo-trust/tests/fixtures/fab/Cargo.lock": lock(("fab", False), ("b", False)),
        "compiler/x/early/Cargo.toml": package("early"),
        "compiler/x/early/Cargo.lock": lock(("early", False), ("a", False)),
        "src/tools/t/Cargo.toml": package("t"),
        "src/tools/t/Cargo.lock": lock(("t", False), ("a", True)),
        "vendor/v/Cargo.toml": package("v"),
        "vendor/v/Cargo.lock": lock(("v", False), ("a", False)),
        "crates/no-manifest/Cargo.lock": lock(("a", False)),
        "crates/bad-lock/Cargo.toml": package("bad-lock"),
        "crates/bad-lock/Cargo.lock": "[[package\n",
        "targo-trust/Cargo.toml": package("targo-trust"),
        "examples/e/Cargo.toml": package("e"),
        "examples/e/Cargo.lock": lock(("e", False), ("targo-trust", False)),
        "examples/bad/Cargo.toml": package("bad"), "examples/bad/Cargo.lock": "[[package\n",
    }
    tracked = sorted(files)
    got, problems = select_locks(tracked, files.__getitem__)
    want = [".", "compiler/x/early", "crates/a", "crates/bad-lock", "crates/renamed",
            "examples/bad", "examples/e", "targo-trust/tests/fixtures/fab"]
    expect(got == want, f"select_locks = {got}, want {want}")
    expect(problems == [], f"select_locks problems = {problems}")
    broken = dict(files, **{"crates/b/Cargo.toml": "[package\n",
                            "crates/s/Cargo.toml": package("s", True)})
    got, problems = select_locks(sorted(broken), broken.__getitem__)
    expect(len(problems) == 2 and "crates/b/Cargo.toml does not parse" in problems[0]
           and "crates/s/Cargo.toml is a standalone workspace" in problems[1],
           f"an unparsable manifest and a lockless workspace gave {problems}")

    def fake(answers: dict) -> Resolver:
        return lambda directory: answers[directory]

    current, stale = (0, ""), (101, refusal)
    hung = (None, "offline targo metadata did not finish: no answer in 60 s")
    for workspaces, answers, want_code, what in [
        ([], {}, 1, "an empty workspace list"),
        (["a", "b"], {"a": current, "b": (101, miss)}, 0, "current and uncached locks"),
        (["a", "b"], {"a": current, "b": stale}, 1, "a stale lock"),
        (["a"], {"a": (101, "error: x\n")}, 1, "an undecided lock"),
        (["a"], {"a": hung}, 1, "a timeout"),
    ]:
        code, _ = quiet(lambda: locked_check(workspaces, fake(answers), no_drift))
        expect(code == want_code, f"locked_check on {what} = {code}, want {want_code}")
    code, said = quiet(lambda: locked_check(["a"], fake({"a": stale}), no_drift))
    expect("targo metadata --offline --format-version 1 --manifest-path a/Cargo.toml" in said
           and "names no git+ source" in said and "submodule_sync" not in said,
           f"the stale remedy reads {said!r}")
    code, said = quiet(lambda: locked_check(["fab"], fake({"fab": stale}), no_drift,
                                            frozenset({"fab"})))
    expect("keeps git+ rows on purpose" in said and "every git+ package stays git" in said
           and "names no git+ source" not in said, f"a git-sourced stale lock reads {said!r}")
    for drift, word in (((["first-party/ay"], []), "first-party/ay"),
                        (([], ["first-party/ (git status exit 128)"]), "exit 128")):
        asked: List[str] = []
        code, said = quiet(lambda: locked_check(
            ["a"], lambda d: asked.append(d) or current, lambda: drift))
        expect(code == 1 and word in said and "submodule_sync" in said
               and "adds entries" not in said and not asked,
               f"locked_check under drift {drift}: rc {code}, asked {asked}, said {said!r}")

    def raising(_manifest: str):
        raise OSError("[Errno 2] No such file or directory: 'targo'")
    answer = resolver_for(Path("/w"), raising)("a")
    expect(answer[0] == 127 and classify(*answer)[0] == "undecided",
           f"a targo that cannot start answered {answer}")

    with tempfile.TemporaryDirectory(prefix="lock-hygiene-selftest-") as tmp:
        # The fake tree without its two unparsable locks, which fail on their own.
        good = {path: text for path, text in files.items()
                if not path.startswith(("crates/bad-lock/", "examples/bad/"))}
        good_tracked = sorted(good)
        clean_lock = Path(tmp) / "Cargo.lock"
        clean_lock.write_text(lock(("a", False)))
        git_lock = Path(tmp) / "git.lock"
        git_lock.write_text(lock(("a", False)) + 'source = "git+https://github.com/'
                            'alabsystems/ay.git?rev=abc#abc"\n')
        respelled_lock = Path(tmp) / "respelled.lock"
        respelled_lock.write_text(lock(("a", False)) + 'source="git+https://github.com/'
                                  'alabsystems/ay.git?rev=abc#abc"\n')
        bad_root_lock = Path(tmp) / "bad.lock"
        bad_root_lock.write_text("[[package\n")
        for root_lock, answer, want_code, what in (
                (clean_lock, current, 0, "a clean root lock, every lock current"),
                (clean_lock, stale, 1, "every lock stale"),
                (git_lock, current, 1, "a git+ source in the root lock"),
                (respelled_lock, current, 1, "a respelled git+ source in the root lock"),
                (bad_root_lock, current, 1, "an unparsable root lock")):
            code, said = quiet(lambda: run_checks(root_lock, False, [], good_tracked,
                                                  good.__getitem__, lambda d: answer, no_drift))
            expect(code == want_code, f"run_checks with {what} = {code}, want {want_code}")
            if root_lock is not clean_lock:
                expect(said.rstrip().splitlines()[-1].startswith("FAIL: the 1 problem(s) above"),
                       f"run_checks with {what} did not end on the closing FAIL line: {said!r}")
        code, said = quiet(lambda: run_checks(clean_lock, False, [], tracked, files.__getitem__,
                                              lambda d: current, no_drift))
        expect(code == 1 and said.count("does not parse as a Cargo lock") == 2
               and "the 2 problem(s) above fail this run" in said,
               f"run_checks on two unparsable judged locks: rc {code}, said {said!r}")
        rootless = [path for path in good_tracked if path != "Cargo.lock"]
        code, _ = quiet(lambda: run_checks(clean_lock, False, [], rootless, good.__getitem__,
                                           lambda d: current, no_drift))
        expect(code == 1, "run_checks passed a selection without the root lock")
        code, _ = quiet(lambda: run_checks(clean_lock, False, [], sorted(broken),
                                           broken.__getitem__, lambda d: current, no_drift))
        expect(code == 1, "run_checks passed an unparsable Trust manifest")
        code, _ = quiet(lambda: run_checks(clean_lock, False, [], None, good.__getitem__,
                                           lambda d: current, no_drift))
        expect(code == 1, "run_checks passed when git ls-files did not answer")
        asked: List[str] = []
        code, said = quiet(lambda: run_checks(clean_lock, False, [], good_tracked, good.__getitem__,
                                              lambda d: (asked.append(d), current)[1], no_drift,
                                              "/h/.cargo/config.toml sets an include"))
        expect(code == 1 and not asked and said.count("FAIL:") == 1
               and "FAIL: no lock was judged --locked: /h/.cargo/config.toml sets an include" in said,
               f"run_checks under a host config redirect: rc {code}, asked {asked}, said {said!r}")

        # The git+ rule: only KEEPS_GIT may name a git source (LOCK-STALE-2).
        git_row = 'source = "git+https://github.com/alabsystems/ty.git?rev=abc#abc"\n'
        fabric = "targo-trust/tests/fixtures/fabric"
        keeps = dict(good, **{
            f"{fabric}/Cargo.toml": package("fabric"),
            f"{fabric}/Cargo.lock": lock(("fabric", False), ("b", False), ("ty", False)) + git_row})
        expect(fabric in select_locks(sorted(keeps), keeps.__getitem__)[0],
               "the fake fabric lock was not judged")
        code, said = quiet(lambda: run_checks(clean_lock, False, [], sorted(keeps),
                                              keeps.__getitem__, lambda d: current, no_drift))
        expect(code == 0, f"run_checks failed the lock that keeps git+ rows on purpose: {said!r}")
        code, said = quiet(lambda: run_checks(clean_lock, False, [], sorted(keeps),
                                              keeps.__getitem__,
                                              lambda d: stale if d == fabric else current,
                                              no_drift))
        expect(code == 1 and "keeps git+ rows on purpose" in said
               and "check_cargo_manifest_alignment.py accepts" in said,
               f"run_checks on a stale fabric lock: rc {code}, said {said!r}")
        code, said = quiet(lambda: run_checks(clean_lock, False, [], sorted(keeps),
                                              keeps.__getitem__,
                                              lambda d: stale if d == "crates/a" else current,
                                              no_drift))
        expect(code == 1 and "on purpose" not in said and "names no git+ source" in said,
               f"run_checks on a stale lock other than fabric: rc {code}, said {said!r}")
        unpatched = dict(keeps, **{
            "crates/a/Cargo.lock": lock(("a", False), ("ty", False)) + git_row})
        code, said = quiet(lambda: run_checks(git_lock, False, [], sorted(unpatched),
                                              unpatched.__getitem__, lambda d: current, no_drift))
        expect(code == 1 and said.rstrip().splitlines()[-1].startswith("FAIL: the 2 problem(s)"),
               f"run_checks with both git+ rules failing: rc {code}, said {said!r}")
        code, said = quiet(lambda: run_checks(clean_lock, False, [], sorted(unpatched),
                                              unpatched.__getitem__, lambda d: current, no_drift))
        expect(code == 1 and "crates/a/Cargo.lock names git+ sources "
               "(ty 1.0.0 from https://github.com/alabsystems/ty.git)" in said
               and '[patch."https://github.com/alabsystems/ty.git"] ty = ' in said,
               f"run_checks on a current lock with an unpatched git edge: rc {code}, said {said!r}")

        def unreadable(path: str) -> str:
            if path == "crates/a/Cargo.lock":
                raise OSError("[Errno 13] Permission denied")
            return keeps[path]
        code, said = quiet(lambda: run_checks(clean_lock, False, [], sorted(keeps), unreadable,
                                              lambda d: current, no_drift))
        expect(code == 1 and "crates/a/Cargo.lock could not be read" in said,
               f"run_checks on an unreadable judged lock: rc {code}, said {said!r}")

        # tracked_files ignores a pathspec mode and an index or git dir from
        # the environment.
        repo = Path(tmp) / "repo"
        (repo / "crates" / "n").mkdir(parents=True)
        for name in ("Cargo.lock", "crates/n/Cargo.lock"):
            (repo / name).write_text("")
        try:
            subprocess.run(["git", "init", "-q", str(repo)], check=True, capture_output=True)
            subprocess.run(["git", "-C", str(repo), "add", "-A"], check=True, capture_output=True)
            hostile = {"GIT_LITERAL_PATHSPECS": "1", "GIT_INDEX_FILE": str(Path(tmp) / "no-index"),
                       "GIT_DIR": str(Path(tmp) / "no-git")}
            saved = {key: os.environ.get(key) for key in hostile}
            os.environ.update(hostile)
            try:
                listed = tracked_files(repo)
            finally:
                for key, value in saved.items():
                    if value is None:
                        os.environ.pop(key, None)
                    else:
                        os.environ[key] = value
            expect(listed == ["Cargo.lock", "crates/n/Cargo.lock"],
                   f"tracked_files under a hostile environment = {listed}")
        except (OSError, subprocess.CalledProcessError) as error:
            failures.append(f"could not build the git fixture: {error}")

    expect(not Path(tmp).exists(), f"the selftest's temporary directory {tmp} outlived its block")
    expect(lg.metadata_env({"CARGO_RESOLVER_LOCKFILE_PATH": "/elsewhere/Cargo.lock",
                            "TARGO_RESOLVER_LOCKFILE_PATH": "/elsewhere/Cargo.lock",
                            "CARGO_UNSTABLE_AVOID_DEV_DEPS": "true",
                            "TARGO_UNSTABLE_AVOID_DEV_DEPS": "true", "KEPT": "1"})
           == {"KEPT": "1"} and lg.metadata_env({"KEPT": "1"}) == {"KEPT": "1"},
           "the lock-judging metadata call inherits a lockfile redirect or an [unstable] "
           "variable (either spelling)")
    # A config that sets resolver.lockfile-path or an include (LOCK-STALE-3),
    # or outside the tree a [patch] or paths table, makes the call no answer,
    # and targo does not run. A harmless file hides none of them.
    not_run: List[str] = []
    with tempfile.TemporaryDirectory(prefix="lock-hygiene-redirect-") as config_tmp:
        base = Path(config_tmp).resolve()
        work, home = base / "w", base / "home"
        work.mkdir()
        host = lg.lock_redirect(work, {}, home)
        if host:
            not_run.append(f"the config cases: a config above {base} trips the scan ({host})")
        harmless, sets = '[build]\njobs = 2\n', '[resolver]\nlockfile-path = "/x/Cargo.lock"\n'
        near = work / ".cargo" / "config.toml"
        for files, named, env in (
                ({near: harmless}, None, {}),
                ({near: 'paths = ["/x"]\n[patch.crates-io]\nx = { path = "/x" }\n'}, None, {}),
                ({near: sets}, near, {}),
                ({near: 'include = ["more.toml"]\n'}, near, {}),
                # LOCK-STALE-4: [unstable] anywhere, and any untracked `config`
                # beside the committed file, which targo reads in its place.
                ({near: '[unstable]\navoid-dev-deps = true\n'}, near, {}),
                ({home / ".cargo" / "config.toml": '[unstable]\nany-other = true\n'},
                 home / ".cargo" / "config.toml", {}),
                ({near: harmless, work / ".cargo" / "config": harmless}, work / ".cargo" / "config", {}),
                ({near: harmless, work / ".cargo" / "config": sets}, work / ".cargo" / "config", {}),
                ({near: harmless, base / ".cargo" / "config.toml": sets}, base / ".cargo" / "config.toml", {}),
                ({near: harmless, base / ".cargo" / "config": sets}, base / ".cargo" / "config", {}),
                ({near: harmless, home / ".cargo" / "config.toml": sets}, home / ".cargo" / "config.toml", {}),
                ({base / ".cargo" / "config.toml": '[patch.crates-io]\nx = { path = "/x" }\n'},
                 base / ".cargo" / "config.toml", {}),
                ({home / ".cargo" / "config.toml": 'paths = ["/x"]\n'}, home / ".cargo" / "config.toml", {}),
                # $CARGO_HOME is read as well as ~/.cargo.
                ({base / "ch" / "config.toml": sets}, base / "ch" / "config.toml",
                 {"CARGO_HOME": str(base / "ch")})):
            if host:
                break
            for where, text in files.items():
                where.parent.mkdir(parents=True, exist_ok=True)
                where.write_text(text)
            why = lg.lock_redirect(work, env, home)
            for where in files:
                where.unlink()
            expect(why is None if named is None else str(named) in (why or ""),
                   f"lock_redirect over {sorted(str(w.relative_to(base)) for w in files)} = {why!r}, "
                   f"want {named}")
        if not host:
            # A `.cargo` that is a file holds no config, and targo reads none there.
            (base / "f" / "g").mkdir(parents=True)
            (base / "f" / ".cargo").write_text("")
            why = lg.lock_redirect(base / "f" / "g", {}, home)
            expect(why is None, f"lock_redirect below a .cargo file = {why!r}")
    saved_redirect, saved_run = lg.lock_redirect, lg.subprocess.run

    def ran(*_args, **_kwargs):
        raise AssertionError("targo ran")
    try:
        lg.lock_redirect = lambda cwd, env=None, home=None: "/w/.cargo/config.toml sets it"
        lg.subprocess.run = ran
        offline, fill = lg.offline_metadata("Cargo.toml"), lg.fill_registry("Cargo.toml")
    except AssertionError as error:
        offline = fill = (error, None)
    finally:
        lg.lock_redirect, lg.subprocess.run = saved_redirect, saved_run
    expect(all(proc is None and "/w/.cargo/config.toml sets it" in (why or "")
               for proc, why in (offline, fill)),
           f"a config that names a lock still ran targo: {offline}, {fill}")

    # git_url and first_party_git, exactly.
    for source, want in (
            ("git+https://github.com/japaric/utest#e32073e2", "https://github.com/japaric/utest"),
            ("git+https://github.com/alabsystems/ty.git?rev=abc#abc",
             "https://github.com/alabsystems/ty.git")):
        expect(git_url(source) == want, f"git_url({source!r}) = {git_url(source)!r}, want {want!r}")
    for url, want in (
            ("https://github.com/alabsystems/ty.git", True),
            ("https://github.com/alabsystems/clean.git", True),
            ("ssh://git@github.com:22/alabsystems/ty.git", True),
            ("https://github.com//alabsystems/ty.git", True),
            ("https://www.github.com/alabsystems/ty.git", True),
            ("http://GitHub.com/alabsystems/ty", True),
            ("https://github.com/alabsystems-fork/ty.git", False),
            ("https://github.com/japaric/utest", False),
            ("https://gitlab.com/alabsystems/ty.git", False),
            ("https://github.com./alabsystems/ty.git", True),
            ("https://github.com/%61ndrewyatesai/ty.git", True),
            ("ssh://git@ssh.github.com:443/alabsystems/ty.git", True),
            ("https://\uff47ithub.com/alabsystems/ty.git", True),
            ("https://github%2Ecom/alabsystems/ty.git", True),
            ("https://[github.com]/alabsystems/ty.git", True),
            ("https://github.com.example.org/alabsystems/ty.git", False),
            ("https://notgithub.com/alabsystems/ty.git", False),
            ("https://github.com/", False)):
        got_party = first_party_git(f"git+{url}?rev=abc#abc")
        expect(got_party == want, f"first_party_git({url!r}) = {got_party}, want {want}")

    # judged_git_sources on its own: every judged lock but KEEPS_GIT, whatever
    # its directory, URL or spelling, wherever Cargo reads the entry from; one
    # problem per lock.
    other_git = 'source = "git+https://github.com/japaric/utest#e32073e2"\n'
    texts = {
        "compiler/x/early/Cargo.lock": lock(("early", False), ("utest", False)) + other_git,
        "crates/a/Cargo.lock": lock(("a", False), ("ty", False)) + git_row,
        "crates/b/Cargo.lock": "",
        "crates/c/Cargo.lock": lock(("c", False), ("ty", False)) + git_row.replace(" = ", "="),
        "crates/d/Cargo.lock": lock(("d", False)) + '\n[[patch.unused]]\nname = "ty"\n'
                               'version = "1.0.0"\n' + git_row,
        "crates/e/Cargo.lock": "[[package\n",
        "crates/f/Cargo.lock": lock(("f", False)) + '\n[root]\nname = "ty"\nversion = "1.0.0"\n'
                               + git_row,
        "crates/g/Cargo.lock": lock(("g", False)) + '\n[extra]\nname = "ty"\n',
        "crates/h/Cargo.lock": 'version = 4\npackage = "x"\n',
        "crates/i/Cargo.lock": lock(("i", False)) + '\n[[patch.extra]]\nname = "ty"\n'
                               'version = "1.0.0"\n' + git_row,
        "crates/j/Cargo.lock": 'version = 4\npackage = [1]\n',
        "crates/k/Cargo.lock": '[[package]]\nname = "k"\nversion = "0.1.0"\n\n[metadata]\n'
                               '"checksum x 1.0.0 (registry+https://x)" = "abc"\n',
        "examples/fabric/Cargo.lock": lock(("e", False), ("ty", False)) + git_row,
        "targo-trust/tests/fixtures/fab/Cargo.lock": lock(("fab", False), ("ty", False)) + git_row,
        f"{fabric}/Cargo.lock": lock(("fabric", False), ("ty", False)) + git_row,
    }

    def reading(path: str) -> str:
        if path == "crates/b/Cargo.lock":
            raise UnicodeDecodeError("utf-8", b"\xff", 0, 1, "invalid start byte")
        return texts[path]
    judged = sorted(path[:-len("/Cargo.lock")] for path in texts)
    found = judged_git_sources(judged, reading)
    want_problems = (
        ("compiler/x/early/Cargo.lock",
         '(utest 1.0.0 from https://github.com/japaric/utest)'),
        ("compiler/x/early/Cargo.lock", '[patch."https://github.com/japaric/utest"] utest = '),
        ("crates/a/Cargo.lock", "names git+"),
        ("crates/b/Cargo.lock", "could not be read"),
        ("crates/c/Cargo.lock", "names git+"),
        ("crates/d/Cargo.lock", "names git+"),
        ("crates/e/Cargo.lock", "does not parse"),
        ("crates/f/Cargo.lock", "(ty 1.0.0 from https://github.com/alabsystems/ty.git)"),
        ("crates/g/Cargo.lock", "does not parse"),
        ("crates/h/Cargo.lock", "does not parse"),
        ("crates/i/Cargo.lock", "does not parse"),
        ("crates/j/Cargo.lock", "does not parse"),
        ("examples/fabric/Cargo.lock", "names git+"),
        ("targo-trust/tests/fixtures/fab/Cargo.lock", "names git+"))
    for path, word in want_problems:
        mine = [problem for problem in found if problem.startswith(path + " ")]
        expect(len(mine) == 1 and word in mine[0],
               f"judged_git_sources on {path} gave {mine}, want one saying {word!r}")
    expect(not any(problem.startswith("crates/k/") for problem in found),
           f"a v1 lock with [metadata] was refused: {found}")
    want_count = len({path for path, _ in want_problems})
    expect(len(found) == want_count and not any(problem.startswith(fabric) for problem in found),
           f"judged_git_sources gave {len(found)} problems, want {want_count}: {found}")

    # Selection beyond the directory rule: a lock that takes a Trust crate only
    # from first-party git, however spelled, is judged, and so is a lock that
    # cannot be read or names a Trust path package in [root]; another git
    # source is not a reason to judge.
    consumers = dict(good, **{
        "tools/consumer/Cargo.toml": package("consumer"),
        "tools/consumer/Cargo.lock": lock(("consumer", False), ("ty", False)) + git_row,
        "tools/mixed/Cargo.toml": package("mixed"),
        "tools/mixed/Cargo.lock": lock(("mixed", False), ("clean", False))
        + 'source = "git+ssh://git@github.com:22/alabsystems/clean.git?rev=abc#abc"\n',
        "tools/legacy/Cargo.toml": package("legacy"),
        "tools/legacy/Cargo.lock": 'version = 1\n[root]\nname = "a"\nversion = "0.1.0"\n',
        "tools/late/Cargo.toml": package("late"),
        "tools/late/Cargo.lock": lock(("late", False), ("aaa", False)) + other_git
        + '\n[[package]]\nname = "zzz"\nversion = "1.0.0"\n' + git_row,
        "tools/other/Cargo.toml": package("other"),
        "tools/other/Cargo.lock": lock(("other", False), ("utest", False)) + other_git,
        "reports/r/frontend/Cargo.toml": package("frontend"),
        "reports/r/frontend/Cargo.lock": lock(("frontend", False), ("a", False)) + git_row})

    def consumer_read(path: str) -> str:
        if path == "examples/e/Cargo.lock":
            raise OSError("[Errno 13] Permission denied")
        return consumers[path]
    got = select_locks(sorted(consumers), consumer_read)[0]
    expect(all(d in got for d in ("tools/consumer", "tools/mixed", "tools/legacy", "tools/late",
                                  "examples/e"))
           and "tools/other" not in got and "reports/r/frontend" not in got,
           f"select_locks beyond the directory rule = {got}")

    # The git fill (land_gate_ask): only for a manifest in fills_git, only when
    # a git checkout is what is missing and no first-party worktree drifted,
    # at most once. A failed fill keeps the offline answer unless it refused
    # the lock; a successful one is followed by a fresh offline answer.
    no_git = types.SimpleNamespace(returncode=101, stderr=git_offline)
    refused = types.SimpleNamespace(returncode=101, stderr=refusal)
    online_miss = types.SimpleNamespace(returncode=101, stderr=miss)
    online_ok = types.SimpleNamespace(returncode=0, stderr="")
    after_fill = types.SimpleNamespace(returncode=0, stderr="the fresh offline answer")
    fab_m, other_m = "/w/fabric/Cargo.toml", "/w/a/Cargo.toml"

    def run_ask(asks, offline, fill, drift_now=no_drift):
        calls: List[str] = []
        saved_lg = (lg.answer_offline, lg.fill_registry, lg.offline_metadata)
        lg.answer_offline = lambda manifest, why, drift=None: (offline, None, why)
        lg.fill_registry = lambda manifest: (calls.append(manifest), fill)[1]
        lg.offline_metadata = lambda manifest: (after_fill, None)
        try:
            ask = land_gate_ask(drift_now, frozenset({fab_m}))
            answers = [ask(manifest) for manifest in asks]
        finally:
            lg.answer_offline, lg.fill_registry, lg.offline_metadata = saved_lg
        return calls, answers
    for asks, offline, fill, drift_now, want_calls, want_answers, what in (
            ([other_m], no_git, (online_ok, None), no_drift, [], [(no_git, None)],
             "a lock outside fills_git"),
            ([fab_m], refused, (online_ok, None), no_drift, [], [(refused, None)],
             "a failure that is not a missing git checkout"),
            ([fab_m], no_git, (online_ok, None), lambda: (["first-party/ay"], []), [],
             [(no_git, None)], "a drifted first-party worktree"),
            ([fab_m], no_git, (online_ok, None), no_drift, [fab_m], [(after_fill, None)],
             "a fill that succeeds"),
            ([fab_m, fab_m], no_git, (online_miss, "no network"), no_drift, [fab_m],
             [(no_git, None), (no_git, None)], "a fill that fails"),
            ([fab_m], no_git, (refused, "refused"), no_drift, [fab_m], [(refused, None)],
             "a fill that refuses the lock")):
        calls, answers = run_ask(asks, offline, fill, drift_now)
        expect(calls == want_calls and answers == want_answers,
               f"land_gate_ask on {what}: filled {calls}, answered {answers}")
    now_lg = (lg.answer_offline, lg.fill_registry, lg.offline_metadata)
    expect(all(now is real for now, real in zip(now_lg, real_lg)),
           "land_gate_ask's selftest did not restore the land gate")

    # The unused-row order (LAND-GATE-UNUSED-PATCH-ORDER-1): a lock refusal
    # with no drift, for a manifest under the land gate's root, is put to
    # unused_order_answer with that manifest's path relative to the root and
    # the worktree's lock bytes, and may fill. Its graph replaces the refusal
    # (None leaves the refusal), and its network verdict is kept for the next
    # manifest. Any other answer, a drift, or a manifest outside the root is
    # not put to it.
    real_order = (lg.answer_offline, lg.unused_order_answer, lg.REPO_ROOT)
    copied_ok = types.SimpleNamespace(returncode=0, stderr="the copy's graph")
    with tempfile.TemporaryDirectory(prefix="lock-hygiene-unused-order-") as tmp:
        fake_root = Path(tmp) / "root"
        (fake_root / "tools" / "t").mkdir(parents=True)
        (fake_root / "tools" / "t" / "Cargo.lock").write_bytes(b"the worktree lock")
        (fake_root / "tools" / "nolock").mkdir(parents=True)
        in_tree = str(fake_root / "tools" / "t" / "Cargo.toml")
        no_lock = str(fake_root / "tools" / "nolock" / "Cargo.toml")
        # Outside the root, with a lock beside it: only the root check stops it.
        (Path(tmp) / "outside" / "w").mkdir(parents=True)
        (Path(tmp) / "outside" / "w" / "Cargo.lock").write_bytes(b"an outside lock")
        outside = str(Path(tmp) / "outside" / "w" / "Cargo.toml")

        def run_order(manifests, offline, copied, drift_now=no_drift):
            seen: List[Tuple[str, bytes, Optional[str], bool]] = []
            marked: Set[str] = set()

            def order(ws, committed, why, may_fill=False):
                seen.append((ws, committed, why, may_fill))
                return copied, "no network for the copy"
            lg.answer_offline = lambda manifest, why, drift=None: (offline, None, why)
            lg.unused_order_answer = order
            lg.REPO_ROOT = fake_root
            try:
                ask = land_gate_ask(drift_now, by_order=marked)
                answers = [ask(manifest) for manifest in manifests]
            finally:
                lg.answer_offline, lg.unused_order_answer, lg.REPO_ROOT = real_order
            return seen, answers, marked
        asked_once = [("tools/t/Cargo.toml", b"the worktree lock", None, True)]
        for manifests, offline, copied, drift_now, want_seen, want_answers, want_marked, what in (
                ([in_tree], refused, copied_ok, no_drift, asked_once, [(copied_ok, None)], {in_tree},
                 "a refusal the copy answers"),
                ([in_tree], refused, None, no_drift, asked_once, [(refused, None)], set(),
                 "a refusal the copy does not answer"),
                ([in_tree, in_tree], refused, None, no_drift,
                 asked_once + [("tools/t/Cargo.toml", b"the worktree lock",
                                "no network for the copy", True)],
                 [(refused, None), (refused, None)], set(), "the copy's network verdict"),
                ([in_tree], no_git, copied_ok, no_drift, [], [(no_git, None)], set(),
                 "a failure that is not a refusal"),
                ([in_tree], refused, copied_ok, lambda: ([], ["first-party/ay: unreadable"]), [],
                 [(refused, None)], set(), "unreadable drift"),
                ([in_tree], refused, copied_ok, lambda: (["first-party/ay"], []), [],
                 [(refused, None)], set(), "a drifted first-party worktree"),
                ([no_lock], refused, copied_ok, no_drift, [], [(refused, None)], set(),
                 "a manifest with no lock beside it"),
                ([outside], refused, copied_ok, no_drift, [], [(refused, None)], set(),
                 "a manifest outside the land gate's root")):
            seen, answers, marked = run_order(manifests, offline, copied, drift_now)
            expect(seen == want_seen and answers == want_answers and marked == want_marked,
                   f"land_gate_ask's unused-order copy on {what}: asked {seen}, answered {answers}, "
                   f"marked {marked}")
    expect((lg.answer_offline, lg.unused_order_answer, lg.REPO_ROOT) == real_order,
           "the unused-order selftest did not restore the land gate")
    # A lock the copy answered is named in the PASS line, not counted as --locked.
    code, said = quiet(lambda: locked_check(["a", "b"], fake({"a": current, "b": current}), no_drift,
                                            by_order=lambda d: d == "b"))
    expect(code == 0 and "1 --locked, and 1 (b) through the land gate's private lock copy" in said,
           f"locked_check with a copy-answered lock: rc {code}, said {said!r}")
    code, said = quiet(lambda: locked_check(["a"], fake({"a": current}), no_drift))
    expect(code == 0 and "PASS: all 1 judged committed locks resolve --locked" in said,
           f"locked_check with no copy-answered lock: rc {code}, said {said!r}")
    # run_checks sweeps the judged workspaces' copies before judging, and not
    # when a redirect means nothing is judged.
    judged = sorted(select_locks(good_tracked, good.__getitem__)[0])
    with tempfile.TemporaryDirectory(prefix="lock-hygiene-sweep-") as tmp:
        sweep_lock = Path(tmp) / "Cargo.lock"
        sweep_lock.write_text(lock(("a", False)))
        for redirect, want, what in ((None, [judged], "a judged run"),
                                     ("/h/.cargo/config.toml sets an include", [], "a redirected run")):
            swept: List[List[str]] = []
            quiet(lambda: run_checks(sweep_lock, False, [], good_tracked, good.__getitem__,
                                     lambda d: current, no_drift, redirect,
                                     sweep=lambda workspaces: swept.append(sorted(workspaces))))
            expect(len(judged) > 1 and swept == want, f"run_checks swept {swept} on {what}, want {want}")
    # main()'s own wiring (tree_wiring), on a temporary root: the copy the
    # resolver's refusal reaches is named by the PASS line, and the sweep
    # removes a dead run's copy beside a nested workspace (crates/, which is
    # no METADATA_WORKSPACES parent) and keeps a live one.
    real_wiring = (lg.answer_offline, lg.unused_order_answer, lg.REPO_ROOT)
    with tempfile.TemporaryDirectory(prefix="lock-hygiene-wiring-") as tmp:
        wired_root = Path(tmp).resolve()
        (wired_root / "crates" / "w").mkdir(parents=True)
        (wired_root / "crates" / "w" / "Cargo.lock").write_bytes(b"the worktree lock")
        dead = subprocess.Popen([sys.executable, "-c", "pass"])
        dead.wait()
        copies = {pid: wired_root / "crates" / f"{lg.UNUSED_ORDER_COPY_PREFIX}{pid}.x.w"
                  for pid in (dead.pid, os.getppid())}
        for copy in copies.values():
            copy.mkdir()
            (copy / "Cargo.lock").write_bytes(b"a copy's lock")
        lg.answer_offline = lambda manifest, why, drift=None: (refused, None, why)
        lg.unused_order_answer = lambda ws, committed, why, may_fill=False: (copied_ok, why)
        lg.REPO_ROOT = wired_root
        try:
            resolve, by_order, sweep = tree_wiring(wired_root, no_drift)
            code, said = quiet(lambda: locked_check(["crates/w"], resolve, no_drift, by_order=by_order))
            sweep(["crates/w", "."])
            left = sorted(path.name for path in (wired_root / "crates").iterdir())
        finally:
            lg.answer_offline, lg.unused_order_answer, lg.REPO_ROOT = real_wiring
        expect(code == 0 and "1 (crates/w) through the land gate's private lock copy" in said,
               f"tree_wiring's PASS line for a copy-answered lock: rc {code}, said {said!r}")
        expect(left == sorted([copies[os.getppid()].name, "w"]),
               f"tree_wiring's sweep left {left}: the dead copy must go and the live one stay")
    expect((lg.answer_offline, lg.unused_order_answer, lg.REPO_ROOT) == real_wiring,
           "the wiring selftest did not restore the land gate")

    # Live, through targo: a path-only chain a -> b, then b gains a path
    # dependency on c that a's committed lock does not list (afec3dff20's shape).
    with tempfile.TemporaryDirectory(prefix="lock-hygiene-selftest-") as tmp:
        root = Path(tmp)
        for name, deps in (("a", 'b = { path = "../b" }\n'), ("b", ""), ("c", "")):
            (root / name / "src").mkdir(parents=True)
            (root / name / "src" / "lib.rs").write_text("")
            (root / name / "Cargo.toml").write_text(
                f'{package(name)}edition = "2021"\n\n[dependencies]\n{deps}\n[workspace]\n')
        a = root / "a"
        # The offline calls run in REPO_ROOT, and the one that makes the
        # fixture's lock in the fixture, so no stub could make them judge the
        # fixture's own lock where this host's configs trip the scan there.
        host = lg.lock_redirect(lg.REPO_ROOT) or lg.lock_redirect(a)
        made_ok, made_err = False, ""
        if host:
            not_run.append(f"the live case: {host}")
        else:
            try:
                made = subprocess.run(["targo", "metadata", "--offline", "--format-version", "1",
                                       "--manifest-path", str(a / "Cargo.toml")], cwd=str(a),
                                      stdout=subprocess.DEVNULL, stderr=subprocess.PIPE, text=True,
                                      check=False, env=lg.metadata_env())
                made_ok, made_err = made.returncode == 0, made.stderr
            except OSError as error:
                made_err = str(error)
        lock_file = a / "Cargo.lock"
        if host:
            pass
        elif not made_ok or not lock_file.is_file():
            failures.append(f"could not lock the fixture: {made_err.strip()[-300:]}")
        else:
            before = lock_file.read_bytes()
            resolve = resolver_for(root, land_gate_ask(no_drift))
            got = classify(*resolve("a"))[0]
            expect(got == "current", f"a fresh lock judged {got}")
            b_manifest = root / "b" / "Cargo.toml"
            b_manifest.write_text(b_manifest.read_text().replace(
                "[dependencies]\n", '[dependencies]\nc = { path = "../c" }\n'))
            verdict, line = classify(*resolve("a"))
            expect(verdict == "stale", f"a lock missing b -> c judged {verdict} ({line})")
            expect(lock_file.read_bytes() == before, "the --locked resolution wrote the lock")
            code, _ = quiet(lambda: locked_check(["a"], resolve, no_drift))
            expect(code == 1, "locked_check passed the stale fixture")

    for failure in failures:
        print(f"SELFTEST FAIL: {failure}", file=sys.stderr)
    if failures:
        return 1
    for case in not_run:
        print(f"SELFTEST NOT RUN: {case}")
    ran = ["classify", "select_locks", "locked_check", "run_checks", "the git+ rule", "the git fill",
           "the unused-order copy", "tree_wiring", "tracked_files", "metadata_env"]
    ran += [] if any(case.startswith("the config cases") for case in not_run) else ["lock_redirect"]
    ran += [] if any(case.startswith("the live case") for case in not_run) else [
        "a live stale path-dependency lock"]
    print(f"SELFTEST PASS: {', '.join(ran[:-1])} and {ran[-1]}")
    return 0


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--explain",
        action="store_true",
        help="also diagnose which moved submodule pointer caused a refusal",
    )
    parser.add_argument(
        "--selftest",
        action="store_true",
        help="exercise the locked-resolution check on temporary workspaces; "
             "read none of this tree's locks",
    )
    args = parser.parse_args()
    # PASS lines go to stdout and FAIL lines to stderr; keep their order when
    # both go to one file, so the closing FAIL line is the last one.
    if hasattr(sys.stdout, "reconfigure"):
        sys.stdout.reconfigure(line_buffering=True)
    if args.selftest:
        return selftest()

    drift = lg._once(lg.first_party_drift)
    resolve, by_order, sweep = tree_wiring(REPO_ROOT, drift)
    return run_checks(REPO_ROOT / "Cargo.lock", args.explain, dirty_submodules(),
                      tracked_files(REPO_ROOT),
                      lambda path: (REPO_ROOT / path).read_text(encoding="utf-8"),
                      resolve, drift, lg.lock_redirect(lg.REPO_ROOT), by_order, sweep)


if __name__ == "__main__":
    raise SystemExit(main())
