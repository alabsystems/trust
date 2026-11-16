#!/usr/bin/env python3
"""check_first_party_pin_lattice.py — one trust-ir and one clean-kernel per integration.

Trust vendors trust-ir, trust-cg and clean as `first-party/*` gitlinks and
builds all three into one compiler. Each of the three ALSO names the others by
exact git revision in its own manifests and lockfiles, because each is built
standalone too (clean's `--locked` packaging lane, trust-cg's own CI, trust-ir's
gates). Nothing made those revisions agree. Measured 2026-09-18 (F-118): the
superproject pinned trust-ir `cff732fe`, its clean gitlink named trust-ir
`6a7fe352` (101 commits behind), its trust-cg gitlink named `d41fa3f8`, and the
clean-kernel trust-ir's gates had tested (`61c10a67`) differed from the one
trustc compiles (`first-party/clean`) by 7 files, +741/-25. Every one of those
builds "passed", each against a different trust-ir or a different kernel.

Let R be the trust-ir gitlink, G the trust-cg gitlink, C the clean gitlink, and
K the `CLEAN_REVISION` constant trust-ir records at R
(`crates/trust-ir/tests/dependency_pin_coherence.rs`). The lattice is:

  L1  every trust-ir git declaration in EVERY `Cargo.toml` tracked at G names
      R, and every `Cargo.lock` tracked at G that resolves trust-ir records R.
  L2  every trust-ir declaration and lock row tracked at C names R, and every
      trust-cg declaration and lock row tracked at C names G.
  L3  K is an ancestor of C; `crates/clean-kernel` is byte-identical between K
      and C (DECIDE (a), the strict form: it is the only form under which
      trust-ir's gates tested the kernel trustc runs); and every workspace row
      `crates/clean-kernel/Cargo.toml` inherits (`<key>.workspace = true` in
      its package, lints and dependency tables) is identical in clean's root
      `Cargo.toml` at K and at C, because those rows are part of the kernel's
      build even though they are not in its tree; and every in-repository
      crate the kernel's PRODUCTION closure reaches by path (a `path = …`
      dependency, or an inherited row whose value is a path, such as the
      optional `clean-features`; transitively; never dev-dependencies) is
      byte-identical at K and C too, because an identical row names a crate
      whose bytes the row does not fix. Also, every clean git declaration and
      lock row tracked at R names K, so K is what trust-ir's gates actually
      built and not just a constant.
  L4  every submodule worktree sits at its gitlink — `scripts/check_pin_coherence.sh`
      (row `fast.pin-coherence`), not re-checked here.
  L5  no pin moves backward — `scripts/check_pin_regression.sh`, not re-checked here.

HOW IT READS. Only git objects: `git show <gitlink>:<path>` against each
submodule's object store, resolved the way Git resolves it
(`--git-path modules/<path>`, which is per-worktree in a linked worktree).
Clean objects absent there may come from the `TRUST_IR_CLEAN_REPO` object
cache. No working tree is ever read — in particular never `~/clean`, which was
three weeks stale when F-118 was measured — no checkout is made, and no
network is touched (`GIT_NO_LAZY_FETCH=1`, `--no-replace-objects`). An absent
object is a failure, never a skip.

WHAT IS JUDGED. Declarations are found by the repository a git URL names (the
last path component, `.git` stripped), never by package name and never from a
fixed file list: every file named exactly `Cargo.toml` or `Cargo.lock` in
`git ls-tree -r <gitlink>` is judged. A `[patch.<url>]` entry that redirects
the repository onto a path OR onto another git repository (a fork under any
name), and a path dependency that escapes the holder repo into a
`trust-ir*`/`trust-cg*` crate, are declarations that do not name R and fail. Each manifest is scanned twice — a line scanner that yields file:line,
and `tomllib` — and a disagreement between the two about which declarations a
file holds is itself a failure: a manifest this script cannot read
unambiguously is never passed.

EXEMPT. A lock or manifest outside every packaging lane (an archived report
snapshot, a scratch workspace) may be exempted only by exact path, in the
`EXEMPT` table below, with a reason. An unlisted file is checked, never
skipped.

WHICH COMMIT. `--rev` (default HEAD) names the superproject commit whose
gitlinks are judged. Under a push — TRUST_PUSHED_REFS set and non-empty; the
pre-push hook exports git's `<local_ref> <local_sha> <remote_ref> <remote_sha>`
lines — and with no explicit `--rev`, the subject is instead EVERY non-deletion
pushed sha, never HEAD: the row passes no `--rev`, and until 2026-09-28 a push
of a skewed non-HEAD ref from a clean main printed `PIN LATTICE OK` for HEAD
while the remote took the skew (docs/issues/2026-09-28-push-lanes-judge-the-
checkout-not-the-push.md, case P). The verdict depends on the (trust-ir,
trust-cg, clean) gitlinks AND committed root manifests/symlinks that could
activate sealed source evidence. Only identical root trees and pin triples
share a verdict; moving a root dependency requires its own judgment. A pushed sha that names no commit here, or
whose tree records no gitlink for one of the three, is a refusal, never a pass;
deletions judge nothing (a deletion-only push prints a column-0 `SKIPPED: `
line and exits 0, which the hook grades SKIPPED, not PASS); a malformed line
is exit 2. An explicit `--rev` keeps
its meaning under a push (the push is then not consulted) — an explicit empty
`--rev ""` is refused as it always was, never read as HEAD — and with the
variable unset or empty the output is today's, byte for byte.

Output: one line per violated leg,

    LATTICE-L<n> <file>:<line> declares <rev>, expected <rev>

followed by the command that fixes it, then `PIN LATTICE OK` (exit 0) or
`PIN LATTICE FAILED` (exit 1). Exit 2 is a usage or environment error.

The move procedure that makes the lattice green again is written down in
docs/first-party-pin-ledger.md, "Pin lattice". Roadmap increment WS8.2;
closes the pin half of F-118. Required since the train-T0 realignment landed
on 2026-09-28; the live manifest records `required=true`, `last_green=2026-09-30`.

Python 3.11+ is required (tomllib); under an older `python3` the script
re-executes itself with the newest python3.1x on PATH, and fails closed if
there is none.

Author: Andrew Yates
Copyright 2026 Andrew Yates | License: Apache-2.0 OR MIT
"""

from __future__ import annotations

import os
import sys

try:
    import tomllib
except ModuleNotFoundError:  # pragma: no cover - exercised by the CLI re-exec
    tomllib = None  # type: ignore[assignment]

if tomllib is None and __name__ == "__main__":  # pragma: no cover
    import shutil
    import subprocess as _subprocess

    if os.environ.get("TRUST_PIN_LATTICE_REEXEC") != "1":
        for _candidate in ("python3.14", "python3.13", "python3.12", "python3.11"):
            _path = shutil.which(_candidate)
            if _path and _subprocess.run(
                [_path, "-c", "import tomllib"], capture_output=True
            ).returncode == 0:
                _env = dict(os.environ, TRUST_PIN_LATTICE_REEXEC="1")
                os.execve(_path, [_path, os.path.abspath(__file__), *sys.argv[1:]], _env)
    print(
        "check_first_party_pin_lattice.py requires Python 3.11+ (tomllib); "
        "none found on PATH — failing closed",
        file=sys.stderr,
    )
    raise SystemExit(2)

import argparse
import atexit
import fnmatch
import hashlib
import json
import posixpath
import re
import subprocess
import unicodedata
from collections import Counter
from dataclasses import dataclass, field
from pathlib import Path

HEX40 = re.compile(r"^[0-9a-f]{40}$")

TRUST_IR = "trust-ir"
TRUST_CG = "trust-cg"
CLEAN = "clean"

GITLINKS = {
    TRUST_IR: "first-party/trust-ir",
    TRUST_CG: "first-party/trust-cg",
    CLEAN: "first-party/clean",
}

# Where trust-ir records the clean revision its own gates build (K).
CLEAN_REVISION_FILE = "crates/trust-ir/tests/dependency_pin_coherence.rs"
CLEAN_REVISION_RE = re.compile(r'const\s+CLEAN_REVISION\s*:\s*&str\s*=\s*"([0-9a-f]{40})"\s*;')
KERNEL_DIR = "crates/clean-kernel"

LEDGER = "docs/first-party-pin-ledger.md#pin-lattice"

@dataclass(frozen=True)
class Exemption:
    reason: str
    # When True the exemption holds only while no `Cargo.toml` sits beside the
    # lock: a snapshot that grows a manifest has become a workspace, and a
    # workspace is judged.
    not_a_workspace: bool = True


# (holder, path) -> Exemption. Exact paths only; there is deliberately no glob,
# so a new lock anywhere — including a new report snapshot — is judged until a
# row names it.
_REPORT_SNAPSHOT = Exemption(
    "archived measurement snapshot: a byte copy of the lock as it stood before "
    "a recorded experiment, kept as report evidence; not a Cargo workspace and "
    "built by no lane"
)
# An archived SOURCE snapshot is a byte copy of a holder's own workspace files
# (manifest and lock together) taken as report evidence: the packet's checker
# re-hashes the copy, so it must stay as it was, and no lane builds it. It holds
# a `Cargo.toml` by construction, so its exemption cannot depend on there being
# none; each of its files is still named by exact path.
_SOURCE_SNAPSHOT = Exemption(
    "archived source snapshot: a byte copy of the holder's manifest and lock at "
    "the commit an acceptance packet binds, re-hashed by that packet's check.py; "
    "built by no lane",
    not_a_workspace=False,
)
EXEMPT: dict[tuple[str, str], Exemption] = {}


@dataclass(frozen=True)
class SealedSourceSnapshot:
    holder: str
    root: str
    subject: str
    seal_sha256: str
    endpoints: tuple[str, ...]


SEALED_SOURCE_SNAPSHOTS = (
    SealedSourceSnapshot(
        TRUST_IR,
        "reports/2026-11-08-source-value-operational/evidence/afa-corrected-compact",
        "afa042711e835e068a223d83f1b7fa30ee42e5e4",
        "e2083a87711b4fc2a63d63ce1eefaa62946b3c8ba7df82ac05c45feef2cfdb10",
        ("source/Cargo.lock", "source/crates/trust-ir-build/Cargo.toml"),
    ),
)


class GitError(RuntimeError):
    pass


def _git_env() -> dict[str, str]:
    # These readers judge immutable objects and ancestry, not caller-selected
    # namespaces or Git configuration. A cached info/grafts file also changes
    # ancestry despite --no-replace-objects, so neutralize it explicitly.
    # Repository-local configuration/object stores remain the existing TCB.
    env = {key: value for key, value in os.environ.items()
           if not key.startswith("GIT_")}
    env["GIT_CONFIG_GLOBAL"] = os.devnull
    env["GIT_CONFIG_NOSYSTEM"] = "1"
    env["GIT_GRAFT_FILE"] = os.devnull
    # No network: a partial clone must not lazily fetch a missing blob, and no
    # credential prompt may block a gate.
    env["GIT_NO_LAZY_FETCH"] = "1"
    env["GIT_TERMINAL_PROMPT"] = "0"
    env["GIT_NO_REPLACE_OBJECTS"] = "1"
    return env


def run_git(args: list[str], *, cwd: Path | None = None, git_dir: Path | None = None,
            check: bool = True) -> subprocess.CompletedProcess[bytes]:
    cmd = ["git", "--no-replace-objects"]
    if git_dir is not None:
        cmd += ["--git-dir", str(git_dir)]
    elif cwd is not None:
        cmd += ["-C", str(cwd)]
    cmd += args
    done = subprocess.run(cmd, capture_output=True, env=_git_env())
    if check and done.returncode != 0:
        raise GitError(f"{' '.join(cmd)}: {done.stderr.decode(errors='replace').strip()}")
    return done


class _Batch:
    """One `git cat-file --batch` per object store: a process per blob made the
    gate cost seconds, which a push-profile row cannot afford."""

    def __init__(self, git_dir: Path) -> None:
        self.proc = subprocess.Popen(
            ["git", "--no-replace-objects", "--git-dir", str(git_dir), "cat-file", "--batch", "-Z"],
            stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.DEVNULL,
            env=_git_env())
        _OPEN_BATCHES.append(self)

    def read(self, spec: str) -> tuple[str, bytes] | None:
        assert self.proc.stdin is not None and self.proc.stdout is not None
        query = spec.encode()
        if b"\0" in query:
            raise GitError("NUL in git object query")
        self.proc.stdin.write(query + b"\0")
        self.proc.stdin.flush()
        # Git paths may contain newlines. Frame both directions with NUL so
        # neither a path nor a missing-object reply can inject another query.
        raw_header = bytearray()
        while True:
            byte = self.proc.stdout.read(1)
            if byte == b"\0":
                break
            if not byte:
                raise GitError(f"truncated git cat-file --batch -Z header while reading {spec}")
            raw_header.extend(byte)
        header = raw_header.decode(errors="replace")
        fields = header.split()
        if len(fields) != 3 or not fields[2].isdigit():
            if not header:
                raise GitError(f"git cat-file --batch exited while reading {spec}")
            return None  # "<spec> missing" / "ambiguous"
        size = int(fields[2])
        framed = self.proc.stdout.read(size + 1)
        if len(framed) != size + 1 or framed[-1:] != b"\0":
            raise GitError(f"truncated or malformed git cat-file response while reading {spec}")
        return fields[1], framed[:-1]

    def close(self) -> None:
        # Pipes remain ours after the child exits. Always close both and reap
        # it, including when an earlier close raises; preserve that failure.
        try:
            if self.proc.stdin is not None:
                self.proc.stdin.close()
        finally:
            try:
                if self.proc.stdout is not None:
                    self.proc.stdout.close()
            finally:
                self.proc.wait()


_OPEN_BATCHES: list[_Batch] = []


def _close_batches(opened: int = 0) -> None:
    # Retire the selected registry entries and attempt every owned cleanup;
    # one broken pipe must not strand later readers or hide other failures.
    batches = _OPEN_BATCHES[opened:]
    del _OPEN_BATCHES[opened:]
    errors: list[BaseException] = []
    for batch in batches:
        try:
            batch.close()
        except BaseException as error:
            errors.append(error)
    if errors:
        raise BaseExceptionGroup("failed to close Git object readers", errors)


atexit.register(_close_batches)


@dataclass
class Store:
    """One or more git object stores for a repository, read-only."""

    name: str
    git_dirs: list[Path]
    _batches: dict[Path, _Batch] = field(default_factory=dict)
    _found: dict[str, Path | None] = field(default_factory=dict)

    def _batch(self, git_dir: Path) -> _Batch:
        if git_dir not in self._batches:
            self._batches[git_dir] = _Batch(git_dir)
        return self._batches[git_dir]

    def _find(self, rev: str) -> Path | None:
        if rev not in self._found:
            self._found[rev] = None
            for git_dir in self.git_dirs:
                got = self._batch(git_dir).read(f"{rev}^{{commit}}")
                if got is not None and got[0] == "commit":
                    self._found[rev] = git_dir
                    break
        return self._found[rev]

    def has(self, rev: str) -> bool:
        return self._find(rev) is not None

    def _dir(self, rev: str) -> Path:
        found = self._find(rev)
        if found is None:
            raise GitError(f"{self.name}: {rev} absent from every store")
        return found

    def _blob(self, rev: str, path: str) -> bytes | None:
        got = self._batch(self._dir(rev)).read(f"{rev}:{path}")
        if got is None or got[0] != "blob":
            return None
        return got[1]

    def show(self, rev: str, path: str) -> bytes:
        body = self._blob(rev, path)
        if body is None:
            raise GitError(f"{self.name}: {rev}:{path} is not a blob")
        return body

    def exists(self, rev: str, path: str) -> bool:
        return self._blob(rev, path) is not None

    def ls_tree(self, rev: str) -> list[tuple[str, str, str]]:
        out = run_git(["ls-tree", "-r", "-z", "--full-tree", rev], git_dir=self._dir(rev)).stdout
        rows = []
        for entry in out.split(b"\0"):
            if not entry:
                continue
            meta, _, path = entry.partition(b"\t")
            mode, kind, _sha = meta.decode().split()
            rows.append((mode, kind, path.decode()))
        return rows

    def _dir_with(self, *revs: str) -> Path:
        """A single store holding every rev: ancestry and diffs are one store's question."""
        for git_dir in self.git_dirs:
            batch = self._batch(git_dir)
            if all((got := batch.read(f"{rev}^{{commit}}")) is not None and got[0] == "commit"
                   for rev in revs):
                return git_dir
        raise GitError(f"{self.name}: no single object store holds all of {', '.join(revs)}; "
                       "fetch them into one (git -C <submodule> fetch origin <sha>)")

    def is_ancestor(self, older: str, newer: str) -> bool:
        git_dir = self._dir_with(older, newer)
        done = run_git(["merge-base", "--is-ancestor", older, newer], git_dir=git_dir, check=False)
        if done.returncode not in (0, 1):
            raise GitError(done.stderr.decode(errors="replace").strip())
        return done.returncode == 0

    def tree_diff(self, a: str, b: str, path: str) -> list[tuple[str, int]]:
        """(file, first differing line in b, or 1) for every file under `path` that differs."""
        git_dir = self._dir_with(a, b)
        base = ["diff", "--no-ext-diff", "--no-textconv", "--no-renames", "--no-color"]
        names = run_git(base + ["--name-only", "-z", a, b, "--", path], git_dir=git_dir).stdout
        files = [n.decode() for n in names.split(b"\0") if n]
        result = []
        for name in files:
            patch = run_git(base + ["-U0", a, b, "--", name], git_dir=git_dir).stdout.decode(
                errors="replace")
            match = re.search(r"^@@ -\d+(?:,\d+)? \+(\d+)", patch, re.M)
            result.append((name, max(1, int(match.group(1))) if match else 1))
        return result


# ---------------------------------------------------------------------------
# Declarations
# ---------------------------------------------------------------------------

def repo_of_url(url: str) -> str:
    """The repository a git URL names: its last path component, `.git` stripped."""
    u = url.strip()
    if u.startswith("git+"):
        u = u[4:]
    u = u.split("#", 1)[0].split("?", 1)[0].rstrip("/")
    last = re.split(r"[/:]", u)[-1]
    if last.endswith(".git"):
        last = last[: -len(".git")]
    return last.lower()


@dataclass(frozen=True)
class Decl:
    line: int
    value: str  # a 40-hex rev, or a marker like "branch=main", "<no rev>", "path:../x"

    @property
    def token(self) -> str:
        return self.value


def _escaping_crate_path(manifest_dir: str, rel: str, repo: str) -> bool:
    joined = posixpath.normpath(posixpath.join(manifest_dir or ".", rel))
    if not (joined == ".." or joined.startswith("../")):
        return False
    return posixpath.basename(joined.rstrip("/")).lower().startswith(repo)


def _git_value(rev: str | None, branch: str | None, tag: str | None) -> str:
    if rev is not None:
        return rev
    if branch is not None:
        return f"branch={branch}"
    if tag is not None:
        return f"tag={tag}"
    return "<no rev>"


_STR = r"""(?:"((?:[^"\\]|\\.)*)"|'([^']*)')"""


def _strip_comment(line: str) -> str:
    quote: str | None = None
    escaped = False
    for index, char in enumerate(line):
        if escaped:
            escaped = False
            continue
        if quote == '"' and char == "\\":
            escaped = True
            continue
        if quote is None and char in "\"'":
            quote = char
        elif quote is not None and char == quote:
            quote = None
        elif quote is None and char == "#":
            return line[:index]
    return line


# A table header: `[a.b]`, `[[bin]]`, `[patch."https://…"]`, `[target.'cfg(x)'.dependencies]`.
_HEADER_RE = re.compile(r"""^\[\[?\s*([A-Za-z0-9_"'-](?:[^\[\]"']|"[^"]*"|'[^']*')*?)\s*\]\]?$""")


def _split_keys(header: str) -> list[str]:
    keys: list[str] = []
    buf = ""
    quote: str | None = None
    for char in header:
        if quote is not None:
            if char == quote:
                quote = None
            else:
                buf += char
        elif char in "\"'":
            quote = char
        elif char == ".":
            keys.append(buf.strip())
            buf = ""
        else:
            buf += char
    keys.append(buf.strip())
    return keys


def _first(pattern: str, text: str) -> str | None:
    match = re.search(pattern, text)
    if match is None:
        return None
    return match.group(1) if match.group(1) is not None else match.group(2)


def scan_manifest_lines(text: str, repo: str, manifest_dir: str) -> list[Decl]:
    """The declarations of `repo` in a manifest, with their lines."""
    decls: list[Decl] = []
    header: list[str] = []
    section: dict[str, tuple[str, int]] = {}

    def patches_repo(keys: list[str]) -> bool:
        return len(keys) >= 2 and keys[0] == "patch" and repo_of_url(keys[1]) == repo

    def close_section() -> None:
        if "git" in section:
            url, url_line = section["git"]
            if repo_of_url(url) == repo:
                rev = section.get("rev")
                line = (rev or section["git"])[1]
                decls.append(Decl(line, _git_value(
                    rev[0] if rev else None,
                    section["branch"][0] if "branch" in section else None,
                    section["tag"][0] if "tag" in section else None)))
            elif len(header) == 3 and patches_repo(header):
                # `[patch."…/trust-ir".trust-ir] git = "…/fork"`: every trust-ir
                # dependency now resolves to another repository. A declaration
                # that names no revision of R at all.
                decls.append(Decl(url_line, f"redirect:{url.strip()}"))
        elif "path" in section:
            path, line = section["path"]
            if (len(header) == 3 and patches_repo(header)) or _escaping_crate_path(
                    manifest_dir, path, repo):
                decls.append(Decl(line, f"path:{path}"))

    for number, raw in enumerate(text.splitlines(), start=1):
        line = _strip_comment(raw).strip()
        if not line:
            continue
        head = _HEADER_RE.match(line)
        if head:
            close_section()
            header = _split_keys(head.group(1))
            section = {}
            continue
        key_match = re.match(r"^(git|rev|branch|tag|path)\s*=\s*" + _STR + r"\s*$", line)
        if key_match is not None:
            value = key_match.group(2) if key_match.group(2) is not None else key_match.group(3)
            section[key_match.group(1)] = (value, number)
            continue
        if "{" not in line:
            continue
        gits = re.findall(r"\bgit\s*=\s*" + _STR, line)
        if len(gits) > 1:
            decls.append(Decl(number, "<ambiguous: several git keys on one line>"))
            continue
        if len(gits) == 1:
            url = gits[0][0] or gits[0][1]
            if repo_of_url(url) == repo:
                decls.append(Decl(number, _git_value(
                    _first(r"\brev\s*=\s*" + _STR, line),
                    _first(r"\bbranch\s*=\s*" + _STR, line),
                    _first(r"\btag\s*=\s*" + _STR, line))))
            elif len(header) == 2 and patches_repo(header):
                decls.append(Decl(number, f"redirect:{url.strip()}"))
            continue
        path = _first(r"\bpath\s*=\s*" + _STR, line)
        if path is not None and (
                (len(header) == 2 and patches_repo(header))
                or _escaping_crate_path(manifest_dir, path, repo)):
            decls.append(Decl(number, f"path:{path}"))
    close_section()
    return decls


def scan_manifest_toml(doc: dict, repo: str, manifest_dir: str) -> list[str]:
    """The same declarations, from the parsed document, without lines."""
    tokens: list[str] = []

    def walk(node: object, in_repo_patch: bool) -> None:
        if isinstance(node, dict):
            git = node.get("git")
            if isinstance(git, str):
                if repo_of_url(git) == repo:
                    def s(key: str) -> str | None:
                        value = node.get(key)
                        return value if isinstance(value, str) else None
                    tokens.append(_git_value(s("rev"), s("branch"), s("tag")))
            else:
                path = node.get("path")
                if isinstance(path, str) and (
                        in_repo_patch or _escaping_crate_path(manifest_dir, path, repo)):
                    tokens.append(f"path:{path}")
            for value in node.values():
                walk(value, False)
        elif isinstance(node, list):
            for value in node:
                walk(value, False)

    for key, value in doc.items():
        if key == "patch" and isinstance(value, dict):
            for url, entries in value.items():
                if repo_of_url(url) == repo and isinstance(entries, dict):
                    for entry in entries.values():
                        if isinstance(entry, dict) and "git" not in entry:
                            walk(entry, True)
                        elif (isinstance(entry, dict) and isinstance(entry.get("git"), str)
                              and repo_of_url(entry["git"]) != repo):
                            tokens.append(f"redirect:{entry['git'].strip()}")
                            for value in entry.values():
                                walk(value, False)
                        else:
                            walk(entry, False)
                else:
                    walk(entries, False)
        else:
            walk(value, False)
    return tokens


_SOURCE_RE = re.compile(r'^\s*source\s*=\s*"([^"]*)"\s*$')


def _lock_value(source: str) -> str:
    fragment = source.split("#", 1)[1] if "#" in source else ""
    return fragment if fragment else "<no resolved commit>"


def scan_lock_lines(text: str, repo: str) -> list[Decl]:
    decls = []
    for number, raw in enumerate(text.splitlines(), start=1):
        match = _SOURCE_RE.match(raw)
        if match and match.group(1).startswith("git+") and repo_of_url(match.group(1)) == repo:
            decls.append(Decl(number, _lock_value(match.group(1))))
    return decls


def scan_lock_toml(doc: dict, repo: str) -> list[str]:
    tokens = []
    for package in doc.get("package", []) or []:
        source = package.get("source") if isinstance(package, dict) else None
        if isinstance(source, str) and source.startswith("git+") and repo_of_url(source) == repo:
            tokens.append(_lock_value(source))
    return tokens


# ---------------------------------------------------------------------------
# Judgement
# ---------------------------------------------------------------------------

@dataclass
class Report:
    violations: list[str] = field(default_factory=list)
    notes: list[str] = field(default_factory=list)
    counts: Counter = field(default_factory=Counter)
    archive_scope: list[tuple[str, str, Store]] = field(default_factory=list)
    archive_root: Path | None = None
    archive_results: dict[tuple[str, str, str], str | None] = field(default_factory=dict)

    def fail(self, leg: str, where: str, message: str, fix: str) -> None:
        self.violations.append(f"LATTICE-{leg} {where} {message}\n    fix: {fix}")


@dataclass
class Holder:
    name: str
    rev: str
    store: Store

    @property
    def prefix(self) -> str:
        return GITLINKS[self.name]


def _archive_path_references(doc: object):
    if isinstance(doc, dict):
        for key in ("path", "workspace"):
            if isinstance(doc.get(key), str):
                yield doc[key]
        for value in doc.values():
            yield from _archive_path_references(value)
    elif isinstance(doc, list):
        for value in doc:
            yield from _archive_path_references(value)


def _activation_path_key(value: str) -> str:
    # macOS accepts canonically equivalent Unicode filename spellings. This is
    # a conservative overapproximation on case/normalization-sensitive hosts.
    return unicodedata.normalize("NFC", value).casefold()


def _archive_activated(snapshot: SealedSourceSnapshot, report: Report) -> str | None:
    """Check committed operational manifests in the root and all lattice holders."""
    if not report.archive_scope or report.archive_root is None:
        return "the complete root/holder activation scope is unavailable"
    archived = posixpath.join(GITLINKS[snapshot.holder], snapshot.root)
    source_root = archived + "/source"
    trees = [(prefix, rev, store, store.ls_tree(rev))
             for prefix, rev, store in report.archive_scope]
    # Resolve links from the judged Git objects, never the mutable checkout.
    # Component-wise traversal matters: link/.. follows the link before '..'.
    links: dict[str, str] = {}
    spellings: dict[str, str] = {}
    for prefix, rev, store, rows in trees:
        for mode, kind, path in rows:
            if mode != "120000" or kind != "blob":
                continue
            key = _activation_path_key(posixpath.join(prefix, path))
            if key in links:
                return "committed activation symlinks collide under case folding"
            links[key] = store.show(rev, path).decode("utf-8")
            spellings[key] = posixpath.join(prefix, path)
    # A case-distinct directory or gitlink can also share a folded link key.
    # On a case-sensitive checkout it must not be silently redirected through
    # the other spelling's link. Check directory prefixes as well as leaves.
    for prefix, _rev, _store, rows in trees:
        for _mode, _kind, path in rows:
            full = posixpath.join(prefix, path)
            components = full.split("/")
            for count in range(1, len(components) + 1):
                component = "/".join(components[:count])
                key = _activation_path_key(component)
                if key in spellings and component != spellings[key]:
                    return "a committed path collides with an activation symlink under case folding"
    root = posixpath.normpath(str(report.archive_root))

    def resolve(value: str) -> str:
        # Use absolute components so ordinary fixture dependencies outside the
        # root stay outside, while ../ paths that re-enter it are still judged.
        pending = (value if value.startswith("/") else root + "/" + value).split("/")
        parts: list[str] = []
        followed = 0
        while pending:
            part = pending.pop(0)
            if part in ("", "."):
                continue
            if part == "..":
                if parts:
                    parts.pop()
                continue
            absolute = "/" + "/".join(parts + [part])
            key_absolute, key_root = _activation_path_key(absolute), _activation_path_key(root)
            candidate = key_absolute[len(key_root) + 1:] if key_absolute.startswith(key_root + "/") else None
            if candidate in links:
                followed += 1
                if followed > 40:
                    raise ValueError("a committed activation symlink loops or exceeds 40 links")
                target = links[candidate]
                if target.startswith("/"):
                    parts = []
                pending = target.split("/") + pending
            else:
                parts.append(part)
        absolute = "/" + "/".join(parts)
        key_absolute, key_root = _activation_path_key(absolute), _activation_path_key(root)
        if key_absolute == key_root:
            return ""
        return key_absolute[len(key_root) + 1:] if key_absolute.startswith(key_root + "/") else key_absolute

    for prefix, rev, store, rows in trees:
        for _mode, kind, path in rows:
            if kind != "blob" or posixpath.basename(path) != "Cargo.toml":
                continue
            full = posixpath.join(prefix, path)
            if full.startswith(archived + "/"):
                continue  # The exact sealed historical package is data.
            try:
                doc = tomllib.loads(store.show(rev, path).decode("utf-8"))
            except (UnicodeDecodeError, tomllib.TOMLDecodeError):
                # An intentionally malformed Cargo fixture cannot activate a
                # dependency. Ordinary holder manifest refusals remain intact.
                continue
            directory = posixpath.dirname(full)

            def normalize(value: str) -> str:
                return resolve(value if value.startswith("/") else posixpath.join(directory, value))

            for value in _archive_path_references(doc):
                target = normalize(value)
                if target == source_root or target.startswith(source_root + "/"):
                    return f"operational manifest {full} activates archived source through path {value!r}"
            workspace = doc.get("workspace", {})
            if not isinstance(workspace, dict):
                continue
            members = workspace.get("members", [])
            excluded = workspace.get("exclude", [])
            if not isinstance(members, list) or not isinstance(excluded, list):
                return f"activation workspace {full} has nonliteral members/exclude"
            for member in members:
                if not isinstance(member, str):
                    return f"activation workspace {full} has a nonliteral member"
                if "**" in member:
                    return f"recursive workspace glob in {full} cannot prove archived source inactive"
                pattern = normalize(member)
                # Both the archived workspace and its exact crate endpoint are
                # candidate members; exclusions never cancel a direct path dep.
                candidates = [source_root] + [
                    posixpath.dirname(posixpath.join(archived, p))
                    for p in snapshot.endpoints if p.endswith("Cargo.toml")
                ]
                # A glob may select an alias before any literal path
                # component can be resolved. Include every committed alias of
                # each archived member (and composed aliases), bounded to the
                # same link-following limit as direct resolution.
                aliases = set(candidates)
                # Only aliases short enough to match this finite pattern
                # need expansion; root aliases otherwise grow without bound.
                maximum = len(pattern.split("/")) + 1
                for _ in range(min(40, maximum)):
                    added = set()
                    for link in links:
                        try:
                            destination = resolve(link)
                        except ValueError as failure:
                            if fnmatch.fnmatchcase(link, pattern) or pattern.startswith(link + "/"):
                                return str(failure)
                            continue
                        for candidate in aliases:
                            if not destination or candidate == destination or candidate.startswith(destination + "/"):
                                suffix = candidate[len(destination):].lstrip("/")
                                alias = posixpath.join(link, suffix)
                                if len(alias.split("/")) <= maximum:
                                    added.add(alias)
                    added -= aliases
                    if not added:
                        break
                    aliases.update(added)
                    if len(aliases) > 4096:
                        return "committed archived-member aliases exceed the bounded activation inventory"
                for candidate in aliases:
                    if fnmatch.fnmatchcase(candidate, pattern) and not any(
                        isinstance(item, str) and fnmatch.fnmatchcase(candidate, normalize(item))
                        for item in excluded
                    ):
                        return f"operational workspace {full} activates archived member {member!r}"
    return None


def _authenticate_source_snapshot(holder: Holder, snapshot: SealedSourceSnapshot,
                                  report: Report) -> str | None:
    key = (holder.name, holder.rev, snapshot.root)
    if key in report.archive_results:
        return report.archive_results[key]
    error = None
    try:
        seal_path = snapshot.root + "/artifact-manifest.json"
        raw = holder.store.show(holder.rev, seal_path)
        if hashlib.sha256(raw).hexdigest() != snapshot.seal_sha256:
            raise ValueError("the exact authenticated outer seal changed")
        seal = json.loads(raw)
        if seal.get("schema") != "compact-handoff-v2" or seal.get("subject") != snapshot.subject:
            raise ValueError("the seal does not bind the declared historical subject")
        if not holder.store.is_ancestor(snapshot.subject, holder.rev):
            raise ValueError("the historical subject is not a retained ancestor")
        files = seal.get("files")
        if not isinstance(files, list) or not 1 <= len(files) <= 4096:
            raise ValueError("the seal has no bounded file inventory")
        inventory = {}
        for row in files:
            path = row.get("path")
            if (not isinstance(path, str) or path.startswith("/") or "\\" in path
                    or any(p in ("", ".", "..") for p in path.split("/"))
                    or path in inventory):
                raise ValueError("the seal has a noncanonical or duplicate payload path")
            inventory[path] = row
        tracked = {
            p[len(snapshot.root) + 1:]: (mode, kind)
            for mode, kind, p in holder.store.ls_tree(holder.rev)
            if p.startswith(snapshot.root + "/")
        }
        if set(tracked) != set(inventory) | {"artifact-manifest.json"}:
            raise ValueError("sealed payloads and the committed packet file set differ")
        if tracked["artifact-manifest.json"] != ("100644", "blob"):
            raise ValueError("the outer seal is not its exact regular Git file")
        total = 0
        for path, row in inventory.items():
            mode, kind = tracked[path]
            expected_mode = "100755" if row.get("mode", 0) & 0o111 else "100644"
            if kind != "blob" or mode != expected_mode:
                raise ValueError(f"sealed payload {path} changed type or executable mode")
            content = holder.store.show(holder.rev, snapshot.root + "/" + path)
            if len(content) != row.get("bytes") or hashlib.sha256(content).hexdigest() != row.get("sha256"):
                raise ValueError(f"sealed payload {path} changed")
            total += len(content)
        if seal.get("payload_count") != len(inventory) or seal.get("payload_bytes") != total:
            raise ValueError("the seal's payload totals differ")
        handoff = json.loads(holder.store.show(holder.rev, snapshot.root + "/handoff.json"))
        if handoff.get("code") != snapshot.subject:
            raise ValueError("the sealed handoff names another source subject")
        for endpoint in snapshot.endpoints:
            if not endpoint.startswith("source/") or endpoint not in inventory:
                raise ValueError("a named historical endpoint is absent from the seal")
            if holder.store.show(holder.rev, snapshot.root + "/" + endpoint) != holder.store.show(
                    snapshot.subject, endpoint.removeprefix("source/")):
                raise ValueError(f"archived endpoint {endpoint} differs from its original Git source")
        error = _archive_activated(snapshot, report)
    except (GitError, ValueError, TypeError, KeyError) as failure:
        error = str(failure)
    report.archive_results[key] = error
    return error


def cargo_files(holder: Holder, report: Report, leg: str) -> list[tuple[str, str]]:
    """Every tracked `Cargo.toml` / `Cargo.lock` at the holder's gitlink: (path, kind)."""
    files = []
    for mode, kind, path in holder.store.ls_tree(holder.rev):
        base = posixpath.basename(path)
        if base not in ("Cargo.toml", "Cargo.lock"):
            continue
        if kind != "blob" or mode not in ("100644", "100755"):
            report.fail(leg, f"{holder.prefix}/{path}:1",
                        f"is a {kind} of mode {mode}, not a regular file; it cannot be judged",
                        "commit the manifest as a regular file")
            continue
        files.append((path, "lock" if base == "Cargo.lock" else "manifest"))
    tracked = {path for path, _ in files}
    for name, path in EXEMPT:
        if name == holder.name and path not in tracked:
            report.notes.append(f"STALE EXEMPT row {holder.prefix}/{path}: not tracked at "
                                f"{holder.rev}; delete the row")
    return files


def judge_file(holder: Holder, path: str, kind: str, repo: str, expected: str,
               leg: str, fix: str, report: Report) -> None:
    where = f"{holder.prefix}/{path}"
    raw = holder.store.show(holder.rev, path)
    snapshot = next((item for item in SEALED_SOURCE_SNAPSHOTS
                     if item.holder == holder.name
                     and path in (item.root + "/" + name for name in item.endpoints)), None)
    if snapshot is not None:
        error = _authenticate_source_snapshot(holder, snapshot, report)
        if error is not None:
            report.fail("ARCHIVE", f"{where}:1", f"historical source authentication refused: {error}",
                        "preserve the original sealed evidence; remove live archive consumption "
                        "or repair its independent source classification")
        else:
            report.counts[("ARCHIVE", kind)] += 1
            report.notes.append(f"SEALED HISTORICAL SOURCE {where}: exact original "
                                f"{snapshot.subject}, complete outer seal and inactive dependency role")
        return
    try:
        text = raw.decode("utf-8")
        doc = tomllib.loads(text)
    except (UnicodeDecodeError, tomllib.TOMLDecodeError) as error:
        report.fail(leg, f"{where}:1", f"cannot be parsed ({error}); it cannot be judged",
                    "fix the file so it parses as TOML")
        return
    if kind == "manifest":
        lines = scan_manifest_lines(text, repo, posixpath.dirname(path))
        parsed = scan_manifest_toml(doc, repo, posixpath.dirname(path))
    else:
        lines = scan_lock_lines(text, repo)
        parsed = scan_lock_toml(doc, repo)
    if Counter(d.token for d in lines) != Counter(parsed):
        report.fail(leg, f"{where}:1",
                    f"holds {repo} declarations the line scanner and tomllib disagree about "
                    f"(lines: {sorted(d.token for d in lines)}, tomllib: {sorted(parsed)}); "
                    "an ambiguous manifest is never passed",
                    f"spell every {repo} dependency as a one-line inline table or a "
                    "[dependencies.<name>] table")
        return
    if not lines:
        return
    exempt = EXEMPT.get((holder.name, path))
    stale = [d for d in lines if d.value != expected]
    if exempt is not None:
        sibling = posixpath.join(posixpath.dirname(path), "Cargo.toml")
        if exempt.not_a_workspace and holder.store.exists(holder.rev, sibling):
            report.notes.append(f"EXEMPTION VOID {where}: {holder.prefix}/{sibling} exists, so "
                                "it is a workspace and is judged")
        else:
            report.notes.append(f"EXEMPT {where} ({len(stale)} stale {repo} row(s)): "
                                f"{exempt.reason}")
            return
    report.counts[(leg, kind)] += len(lines)
    for decl in stale:
        report.fail(leg, f"{where}:{decl.line}", f"declares {decl.value}, expected {expected}", fix)


def read_gitlinks(root: Path, rev: str) -> dict[str, str]:
    links = {}
    for name, path in GITLINKS.items():
        out = run_git(["ls-tree", rev, "--", path], cwd=root).stdout.decode().strip()
        fields = out.split("\t", 1)[0].split() if out else []
        if len(fields) != 3 or fields[0] != "160000" or fields[1] != "commit" or not HEX40.match(
                fields[2]):
            raise GitError(f"{path}: no 160000 commit gitlink recorded at {rev}")
        links[name] = fields[2]
    return links


def resolve_store_dirs(root: Path, path: str) -> list[Path]:
    """Git's own answer for where a submodule's objects live; never a working tree's files."""
    candidates: list[Path] = []
    done = run_git(["rev-parse", "--path-format=absolute", "--git-path", f"modules/{path}"],
                   cwd=root, check=False)
    if done.returncode == 0 and done.stdout.strip():
        candidates.append(Path(done.stdout.decode().strip()))
    common = run_git(["rev-parse", "--path-format=absolute", "--git-common-dir"], cwd=root,
                     check=False)
    if common.returncode == 0 and common.stdout.strip():
        candidates.append(Path(common.stdout.decode().strip()) / "modules" / path)
    if (root / path / ".git").exists():
        pointed = run_git(["rev-parse", "--absolute-git-dir"], cwd=root / path, check=False)
        if pointed.returncode == 0 and pointed.stdout.strip():
            candidates.append(Path(pointed.stdout.decode().strip()))
    seen: list[Path] = []
    for candidate in candidates:
        if candidate.is_dir() and candidate not in seen:
            seen.append(candidate)
    return seen


def git_dir_of(path: Path) -> Path | None:
    done = run_git(["rev-parse", "--absolute-git-dir"], cwd=path, check=False)
    if done.returncode != 0 or not done.stdout.strip():
        return None
    return Path(done.stdout.decode().strip())


def check(root: Path, rev: str, overrides: dict[str, Path]) -> Report:
    report = Report()
    links = read_gitlinks(root, rev)
    stores: dict[str, Store] = {}
    for name, path in GITLINKS.items():
        if name in overrides:
            found = git_dir_of(overrides[name])
            dirs = [found] if found else []
        else:
            dirs = resolve_store_dirs(root, path)
        if name == CLEAN and os.environ.get("TRUST_IR_CLEAN_REPO"):
            cache = git_dir_of(Path(os.environ["TRUST_IR_CLEAN_REPO"]))
            if cache is not None and cache not in dirs:
                dirs.append(cache)
        stores[name] = Store(name, dirs)

    R, G, C = links[TRUST_IR], links[TRUST_CG], links[CLEAN]
    report.notes.append(f"R {GITLINKS[TRUST_IR]} = {R}")
    report.notes.append(f"G {GITLINKS[TRUST_CG]} = {G}")
    report.notes.append(f"C {GITLINKS[CLEAN]}    = {C}")

    missing = False
    for name, sha in ((TRUST_IR, R), (TRUST_CG, G), (CLEAN, C)):
        if not stores[name].has(sha):
            missing = True
            where = ", ".join(str(d) for d in stores[name].git_dirs) or "no object store found"
            report.fail("OBJECTS", GITLINKS[name], f"pin {sha} is absent from {where}",
                        f"git -C {GITLINKS[name]} fetch origin {sha}   "
                        "(then scripts/submodule_sync.sh --restore; never a blanket "
                        "`git submodule update`)")
    if missing:
        return report

    ir = Holder(TRUST_IR, R, stores[TRUST_IR])
    cg = Holder(TRUST_CG, G, stores[TRUST_CG])
    cl = Holder(CLEAN, C, stores[CLEAN])
    root_git = git_dir_of(root)
    if root_git is None:
        raise GitError("cannot establish the superproject archive activation scope")
    report.archive_root = root
    report.archive_scope = [("", rev, Store("trust", [root_git])),
                            (ir.prefix, R, ir.store), (cg.prefix, G, cg.store),
                            (cl.prefix, C, cl.store)]

    # K: the clean revision trust-ir's own gates build.
    K = None
    if ir.store.exists(R, CLEAN_REVISION_FILE):
        found = CLEAN_REVISION_RE.findall(ir.store.show(R, CLEAN_REVISION_FILE).decode(
            errors="replace"))
        if len(found) == 1:
            K = found[0]
    if K is None:
        report.fail("L3", f"{ir.prefix}/{CLEAN_REVISION_FILE}:1",
                    "declares no single 40-hex CLEAN_REVISION, expected one",
                    "in trust-ir: scripts/bump-dep-pin.sh clean <sha> (it owns that constant)")
    else:
        report.notes.append(f"K CLEAN_REVISION@R = {K}")

    # L1 — trust-cg holds trust-ir at R.
    l1_fix = (f"in trust-cg: pin trust-ir to {R} in EVERY declaration and re-resolve every "
              f"lock that resolves it, push trust-cg, then move {GITLINKS[TRUST_CG]} in the same "
              f"~/trust lattice commit ({LEDGER}, step 3)")
    for path, kind in cargo_files(cg, report, "L1"):
        judge_file(cg, path, kind, TRUST_IR, R, "L1", l1_fix, report)

    # L2 — clean holds trust-ir at R and trust-cg at G.
    l2_fix = (f"in clean: commit C1 = C0 + {{trust-ir -> {R}, trust-cg -> {G}, every lock}} "
              f"touching nothing under {KERNEL_DIR}, push clean, then move "
              f"{GITLINKS[CLEAN]} in the same ~/trust lattice commit ({LEDGER}, step 4)")
    for path, kind in cargo_files(cl, report, "L2"):
        judge_file(cl, path, kind, TRUST_IR, R, "L2", l2_fix, report)
        judge_file(cl, path, kind, TRUST_CG, G, "L2", l2_fix, report)

    # L3 — one clean-kernel.
    if K is not None:
        l3_fix = (f"in trust-ir: scripts/bump-dep-pin.sh clean <C0> (or `clean-ay <C0> <ay>`), "
                  f"where C0 is a clean commit whose {KERNEL_DIR} and inherited workspace rows "
                  f"equal C's, then redo the lattice move ({LEDGER}, steps 1-5)")
        for path, kind in cargo_files(ir, report, "L3"):
            judge_file(ir, path, kind, CLEAN, K, "L3",
                       f"in trust-ir: scripts/bump-dep-pin.sh clean {K} repairs every leg", report)
        if not cl.store.has(K):
            report.fail("L3", GITLINKS[CLEAN], f"K {K} is absent from the clean object store",
                        f"git -C {GITLINKS[CLEAN]} fetch origin {K}  (or point TRUST_IR_CLEAN_REPO "
                        "at an object cache holding it)")
        elif not cl.store.is_ancestor(K, C):
            report.fail("L3", GITLINKS[CLEAN], f"is {C}, which does not descend from K {K}",
                        l3_fix)
        else:
            if not cl.store.exists(C, f"{KERNEL_DIR}/Cargo.toml"):
                report.fail("L3", f"{GITLINKS[CLEAN]}/{KERNEL_DIR}/Cargo.toml:1",
                            "is absent at C, expected the kernel manifest", l3_fix)
            for name, line in cl.store.tree_diff(K, C, KERNEL_DIR):
                report.fail("L3", f"{GITLINKS[CLEAN]}/{name}:{line}",
                            f"differs between K {K} and C {C}, expected byte-identical", l3_fix)
            judge_inherited_rows(cl, K, C, l3_fix, report)
    return report


def _find_row_line(text: str, table: list[str], key: str) -> int:
    header: list[str] = []
    for number, raw in enumerate(text.splitlines(), start=1):
        line = _strip_comment(raw).strip()
        head = _HEADER_RE.match(line)
        if head:
            header = _split_keys(head.group(1))
            if header[: len(table) + 1] == table + [key]:
                return number
            continue
        if header == table:
            match = re.match(r"""^("[^"]*"|'[^']*'|[A-Za-z0-9_-]+)\s*[.=]""", line)
            if match and match.group(1).strip("\"'") == key:
                return number
    return 1


def judge_inherited_rows(cl: Holder, K: str, C: str, fix: str, report: Report) -> None:
    """Every workspace row the kernel manifest inherits is identical at K and C."""
    try:
        kernel = tomllib.loads(cl.store.show(C, f"{KERNEL_DIR}/Cargo.toml").decode())
        root_c_text = cl.store.show(C, "Cargo.toml").decode()
        root_c = tomllib.loads(root_c_text)
        root_k = tomllib.loads(cl.store.show(K, "Cargo.toml").decode())
    except (GitError, UnicodeDecodeError, tomllib.TOMLDecodeError) as error:
        report.fail("L3", f"{GITLINKS[CLEAN]}/Cargo.toml:1",
                    f"cannot be read at K and C ({error}); inherited rows cannot be judged", fix)
        return
    rows: list[tuple[list[str], str]] = []
    for key, value in (kernel.get("package") or {}).items():
        if isinstance(value, dict) and value.get("workspace") is True:
            rows.append((["workspace", "package"], key))
    lints = kernel.get("lints")
    if isinstance(lints, dict) and lints.get("workspace") is True:
        rows.append((["workspace"], "lints"))

    for table in _dep_tables(kernel, dev=True):
        for name, spec in table.items():
            if isinstance(spec, dict) and spec.get("workspace") is True:
                rows.append((["workspace", "dependencies"], name))
    seen = set()
    for table, key in rows:
        if (tuple(table), key) in seen:
            continue
        seen.add((tuple(table), key))

        def lookup(doc: dict) -> object:
            node: object = doc
            for part in table + [key]:
                node = node.get(part) if isinstance(node, dict) else None
            return node

        at_c, at_k = lookup(root_c), lookup(root_k)
        report.counts[("L3", "inherited")] += 1
        if at_c is None:
            report.fail("L3", f"{GITLINKS[CLEAN]}/Cargo.toml:1",
                        f"[{'.'.join(table)}].{key} is absent at C, expected the row "
                        f"{KERNEL_DIR} inherits", fix)
        elif at_c != at_k:
            line = _find_row_line(root_c_text, table, key)
            report.fail("L3", f"{GITLINKS[CLEAN]}/Cargo.toml:{line}",
                        f"[{'.'.join(table)}].{key} declares {at_c!r} at C, expected "
                        f"{at_k!r} as at K {K} (inherited by {KERNEL_DIR})", fix)
    judge_path_closure(cl, K, C, root_c, fix, report)


def _dep_tables(doc: dict, *, dev: bool) -> list[dict]:
    """A manifest's dependency tables: the production ones, plus dev when asked."""
    kinds = ("dependencies", "build-dependencies") + (("dev-dependencies",) if dev else ())
    tables = [doc.get(k) for k in kinds]
    for target in (doc.get("target") or {}).values():
        if isinstance(target, dict):
            tables += [target.get(k) for k in kinds]
    return [t for t in tables if isinstance(t, dict)]


def judge_path_closure(cl: Holder, K: str, C: str, root_c: dict, fix: str, report: Report) -> None:
    """Every in-workspace crate the kernel can be built WITH is byte-identical at K and C.

    `crates/clean-kernel/Cargo.toml` names workspace crates by path — directly
    (`path = "../x"`) or through a `[workspace.dependencies]` row whose value is
    a path (`clean-features = { path = "crates/clean-features" }`, inherited by
    the kernel's optional `cli` feature). Byte-identity of the kernel's own tree
    and equality of the inherited ROW say nothing about the crate the row names,
    so the kernel's build could still differ between K and C through it. Walk
    the production closure (dependencies, build-dependencies, per-target ones,
    optional included — a consumer's feature choice may enable it; never
    dev-dependencies, which no production build compiles) transitively, and
    require each crate directory identical. A path that leaves the clean
    repository is refused: it cannot be judged from clean's objects."""
    workspace_deps = (root_c.get("workspace") or {}).get("dependencies")
    workspace_deps = workspace_deps if isinstance(workspace_deps, dict) else {}
    pending = [KERNEL_DIR]
    visited: set[str] = set()
    while pending:
        crate_dir = pending.pop()
        if crate_dir in visited:
            continue
        visited.add(crate_dir)
        manifest_path = f"{crate_dir}/Cargo.toml"
        try:
            manifest = tomllib.loads(cl.store.show(C, manifest_path).decode())
        except (GitError, UnicodeDecodeError, tomllib.TOMLDecodeError) as error:
            report.fail("L3", f"{GITLINKS[CLEAN]}/{manifest_path}:1",
                        f"cannot be read at C ({error}); the kernel's path closure cannot be "
                        "judged", fix)
            continue
        if crate_dir != KERNEL_DIR:
            report.counts[("L3", "path-closure")] += 1
            for name, line in cl.store.tree_diff(K, C, crate_dir):
                report.fail("L3", f"{GITLINKS[CLEAN]}/{name}:{line}",
                            f"differs between K {K} and C {C}, expected byte-identical "
                            f"(a path dependency in {KERNEL_DIR}'s production closure)", fix)
        for table in _dep_tables(manifest, dev=False):
            for name, spec in table.items():
                if not isinstance(spec, dict):
                    continue
                rel: str | None = None
                if isinstance(spec.get("path"), str):
                    rel, base = spec["path"], crate_dir
                elif spec.get("workspace") is True:
                    row = workspace_deps.get(name)
                    if isinstance(row, dict) and isinstance(row.get("path"), str):
                        rel, base = row["path"], "."
                if rel is None:
                    continue
                target = posixpath.normpath(posixpath.join(base, rel))
                if target == ".." or target.startswith("../") or posixpath.isabs(target):
                    report.fail("L3", f"{GITLINKS[CLEAN]}/{manifest_path}:1",
                                f"dependency {name} names path {rel!r}, which leaves the clean "
                                "repository; the kernel's production closure cannot be judged "
                                "from clean's objects", fix)
                    continue
                pending.append(target)


def print_report(rev: str, report: Report, pushed: list[str] | None = None) -> bool:
    """One subject's block, without the final verdict line; True when it has no violation."""
    if pushed is None:
        print(f"first-party pin lattice @ {rev}")
    else:
        print(f"first-party pin lattice @ {rev} (pushed: {', '.join(pushed)})")
    for note in report.notes:
        print(f"  {note}")
    for (leg, kind), count in sorted(report.counts.items()):
        print(f"  judged {leg} {kind}: {count}")
    print("  L4 (worktrees at gitlinks) is fast.pin-coherence; L5 (no backward move) is "
          "scripts/check_pin_regression.sh")
    if report.violations:
        print()
        for violation in report.violations:
            print(violation)
        print()
        return False
    return True


HEX_SHA = re.compile(r"^(?:[0-9a-f]{40}|[0-9a-f]{64})$")
ZERO_SHA = re.compile(r"^0+$")


class PushedRefsError(ValueError):
    pass


def parse_pushed_refs(raw: str) -> list[tuple[str, str]]:
    """(local_ref, local_sha) per TRUST_PUSHED_REFS line; malformed input raises."""
    pushed = []
    for line in raw.splitlines():
        if not line.strip():
            continue
        fields = line.split()
        if len(fields) != 4 or not HEX_SHA.match(fields[1]) or not HEX_SHA.match(fields[3]):
            raise PushedRefsError(
                f"malformed TRUST_PUSHED_REFS line {line!r}; expected "
                "`<local_ref> <local_sha> <remote_ref> <remote_sha>`")
        pushed.append((fields[0], fields[1]))
    return pushed


def judge_pushed(root: Path, pushed: list[tuple[str, str]], overrides: dict[str, Path]) -> int:
    """Every pushed sha; reuse only an identical root tree and pin triple."""
    live = [(ref, sha) for ref, sha in pushed if not ZERO_SHA.match(sha)]
    deletions = len(pushed) - len(live)
    if not live:
        print(f"SUBJECT: the pushed commits (TRUST_PUSHED_REFS: {deletions} deletion(s), "
              "nothing else), not HEAD")
        # `SKIPPED: ` at column 0 is the pre-push hook's contract for a lane
        # that judged nothing (run_lane's `^[[:space:]]*SKIPPED: `); a
        # `PIN LATTICE SKIPPED:` line would be graded PASS.
        print("SKIPPED: deletion(s) only, no commit pushed — nothing to judge")
        return 0
    refusals: list[str] = []
    # Root tree is a semantic input: Cargo adoption can change without pins.
    # (root tree, R, G, C) -> (first commit carrying it, equivalent tip labels).
    triples: dict[tuple[str, str, str, str], tuple[str, list[str]]] = {}
    for ref, sha in live:
        label = f"{ref} {sha[:12]}"
        try:
            done = run_git(["rev-parse", "--verify", "--quiet", f"{sha}^{{commit}}"], cwd=root,
                           check=False)
            commit = done.stdout.decode().strip()
            if done.returncode != 0 or not HEX_SHA.match(commit):
                raise GitError(f"{sha} names no commit in {root}")
            links = read_gitlinks(root, commit)
        except GitError as error:
            refusals.append(f"PIN LATTICE FAILED @ {label}: the pushed object cannot be judged "
                            f"({error}); a push this gate cannot read is not a pass")
            continue
        root_tree = run_git(["rev-parse", f"{commit}^{{tree}}"], cwd=root).stdout.decode().strip()
        key = (root_tree, links[TRUST_IR], links[TRUST_CG], links[CLEAN])
        if key not in triples:
            triples[key] = (commit, [])
        if label not in triples[key][1]:
            triples[key][1].append(label)
    names = ", ".join(f"{ref} {sha[:12]}" for ref, sha in live)
    extra = f"; {deletions} deletion(s) not judged" if deletions else ""
    print(f"SUBJECT: the pushed commits (TRUST_PUSHED_REFS: {names}{extra}), not HEAD; "
          f"{len(triples)} distinct root-tree/pin subject(s)")
    violations = 0
    failed_triples = 0
    for commit, labels in triples.values():
        print()
        opened = len(_OPEN_BATCHES)
        try:
            report = check(root, commit, overrides)
        except GitError as error:
            print(f"first-party pin lattice @ {commit} (pushed: {', '.join(labels)})")
            print(f"  cannot be judged: {error}")
            print()
            violations += 1
            failed_triples += 1
            continue
        finally:
            # Each check opens its own `cat-file --batch` per store; reap them
            # per triple, or a push of many tips runs out of descriptors
            # (EMFILE after ~41 triples under `ulimit -n 256`).
            _close_batches(opened)
        if not print_report(commit, report, labels):
            violations += len(report.violations)
            failed_triples += 1
    if refusals:
        print()
        for refusal in refusals:
            print(refusal)
    if violations or refusals:
        print()
        print(f"PIN LATTICE FAILED: {violations} violation(s) in {failed_triples} of "
              f"{len(triples)} pushed root-tree/pin subject(s), {len(refusals)} unreadable pushed "
              f"sha(s). The move procedure is {LEDGER}.")
        return 1
    print()
    print("PIN LATTICE OK: one trust-ir and one clean-kernel across trust-ir, trust-cg and clean, "
          f"in every pushed commit ({len(live)} tip(s), {len(triples)} gitlink triple(s))")
    return 0


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n", 1)[0])
    parser.add_argument("--root", type=Path, default=None,
                        help="superproject checkout (default: this script's repository)")
    parser.add_argument("--rev", default=None,
                        help="superproject commit-ish to judge (default: HEAD, or under a push "
                             "every pushed sha in TRUST_PUSHED_REFS)")
    parser.add_argument("--store", action="append", default=[], metavar="NAME=PATH",
                        help="object store override for trust-ir, trust-cg or clean")
    args = parser.parse_args(argv)

    root = args.root or Path(__file__).resolve().parents[1]
    top = run_git(["rev-parse", "--show-toplevel"], cwd=root, check=False)
    if top.returncode != 0:
        print(f"pin lattice: {root} is not a git checkout", file=sys.stderr)
        return 2
    root = Path(top.stdout.decode().strip())
    overrides: dict[str, Path] = {}
    for item in args.store:
        name, sep, path = item.partition("=")
        if not sep or name not in GITLINKS:
            print(f"pin lattice: bad --store {item!r} (expected one of {sorted(GITLINKS)}=PATH)",
                  file=sys.stderr)
            return 2
        overrides[name] = Path(path)

    raw = os.environ.get("TRUST_PUSHED_REFS", "")
    if args.rev is None and raw.strip():
        try:
            pushed = parse_pushed_refs(raw)
        except PushedRefsError as error:
            print(f"pin lattice: {error}", file=sys.stderr)
            return 2
        return judge_pushed(root, pushed, overrides)
    if args.rev is not None and raw.strip():
        print(f"SUBJECT: --rev {args.rev} (explicit; TRUST_PUSHED_REFS is set and not consulted)")

    try:
        # `is None`, never `or`: an explicit empty --rev is `^{commit}`, which
        # refuses, as it always has — it must not quietly become HEAD.
        subject = "HEAD" if args.rev is None else args.rev
        commit = run_git(["rev-parse", "--verify", f"{subject}^{{commit}}"], cwd=root)
        rev = commit.stdout.decode().strip()
        report = check(root, rev, overrides)
    except GitError as error:
        print(f"PIN LATTICE FAILED: {error}")
        return 1

    if not print_report(rev, report):
        print(f"PIN LATTICE FAILED: {len(report.violations)} violation(s). "
              f"The move procedure is {LEDGER}.")
        return 1
    print("PIN LATTICE OK: one trust-ir and one clean-kernel across trust-ir, trust-cg and clean")
    return 0


if __name__ == "__main__":
    sys.exit(main())
