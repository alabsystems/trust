#!/usr/bin/env python3
"""Versioned Git-visible build-source observations; never compiler proof authority.

Version 1 records only top-level submodule status. Version 2 enumerates committed
gitlinks in every initialized repository, checks the immediate parent's pin,
and binds each repository's non-ignored Git status and diff. Ignored build
outputs and an atomic filesystem snapshot are outside this observation's scope.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import stat
import subprocess
import tempfile
import time


RECORD_VERSION = "2"
CENSUS_SCOPE = "recursive-worktrees/v1"
LEGACY_SCOPE = "top-level-only/v1"
EMPTY_SHA256 = hashlib.sha256(b"").hexdigest()
BASE_IDENTITY = ("head", "diff_sha256", "status_sha256", "submodule_sha256")
RECURSIVE_IDENTITY = (
    "submodule_census_scope", "recursive_submodule_sha256", "recursive_submodule_count",
    "tree_state", "dirty_tracked", "dirty_untracked",
)


class ProvenanceError(ValueError):
    """A source observation or record could not establish its declared scope."""


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def _git(root: Path, *arguments: str) -> bytes:
    environment = os.environ.copy()
    # A caller running from a Git hook must not redirect nested reads to the
    # outer index/object store. Configuration overrides are not source facts.
    for key in list(environment):
        if key.startswith("GIT_"):
            del environment[key]
    environment["GIT_OPTIONAL_LOCKS"] = "0"
    try:
        result = subprocess.run(
            ["git", *arguments], cwd=root, env=environment, capture_output=True,
            timeout=120, check=False,
        )
    except (OSError, subprocess.TimeoutExpired) as error:
        raise ProvenanceError(f"source census could not read Git at {root}: {error}") from error
    if result.returncode:
        raise ProvenanceError(f"source census Git command failed at {root}: {' '.join(arguments)}")
    return result.stdout


def _head(root: Path) -> str:
    head = _git(root, "rev-parse", "--verify", "HEAD").decode("ascii").strip()
    if re.fullmatch(r"[0-9a-f]{40}|[0-9a-f]{64}", head) is None:
        raise ProvenanceError(f"source census has an invalid HEAD at {root}")
    return head


def _status_counts(data: bytes) -> tuple[int, int]:
    tracked = untracked = 0
    entries = data.split(b"\0")
    if entries.pop() != b"":
        raise ProvenanceError("source census has unterminated porcelain status")
    position = 0
    while position < len(entries):
        entry = entries[position]
        if len(entry) < 4 or entry[2:3] != b" ":
            raise ProvenanceError("source census has malformed porcelain status")
        if entry[:2] == b"??":
            untracked += 1
        else:
            tracked += 1
        position += 1
        if b"R" in entry[:2] or b"C" in entry[:2]:
            if position == len(entries) or not entries[position]:
                raise ProvenanceError("source census has incomplete rename status")
            position += 1
    return tracked, untracked


def _gitlinks(root: Path, head: str) -> list[tuple[str, str]]:
    data = _git(root, "ls-tree", "-r", "-z", head)
    if data and not data.endswith(b"\0"):
        raise ProvenanceError("source census has unterminated Git tree")
    links = []
    for entry in data.split(b"\0"):
        if not entry:
            continue
        header, separator, raw_path = entry.partition(b"\t")
        fields = header.split(b" ")
        if not separator or len(fields) != 3:
            raise ProvenanceError("source census has malformed Git tree")
        if fields[0] != b"160000":
            continue
        path = raw_path.decode("utf-8")
        pin = fields[2].decode("ascii")
        relative = PurePosixPath(path)
        if (fields[1] != b"commit" or not path or relative.is_absolute()
                or relative.as_posix() != path or any(p in (".", "..", "") for p in path.split("/"))
                or re.fullmatch(r"[0-9a-f]{40}|[0-9a-f]{64}", pin) is None):
            raise ProvenanceError("source census has an invalid gitlink")
        links.append((path, pin))
    return sorted(links)


def fingerprint(fields: dict[str, str]) -> str:
    keys = BASE_IDENTITY
    domain = ""
    if fields["record_version"] == RECORD_VERSION:
        keys += RECURSIVE_IDENTITY
        domain = "trust-build-tree-provenance-v2\n"
    elif fields["record_version"] != "1":
        raise ProvenanceError("build stamp has an unsupported version")
    return digest((domain + "".join(fields[key] + "\n" for key in keys)).encode("utf-8"))


def source_facts(directory: Path) -> tuple[dict[str, str], str]:
    """Observe complete committed recursive pins or refuse; never repair them."""
    root = directory.resolve(strict=True)
    if not (root / ".git").exists():
        raise ProvenanceError("source census root is not an initialized repository")
    rows = []
    annotations = []
    pending = [(PurePosixPath("."), None)]
    visited = set()
    tracked = untracked = 0
    while pending:
        relative, pinned = pending.pop()
        owner = root / relative
        # A symlinked path must not silently turn a committed gitlink into an
        # observation of a different checkout. Linked worktrees' .git files are
        # allowed; the worktree directories themselves remain exactly located.
        cursor = root
        for component in relative.parts:
            cursor /= component
            if cursor.is_symlink():
                raise ProvenanceError(f"source census gitlink traverses a symlink: {relative}")
        if not owner.is_dir() or not (owner / ".git").exists():
            raise ProvenanceError(f"source census has an uninitialized repository: {relative}")
        resolved = owner.resolve(strict=True)
        if resolved in visited or not resolved.is_relative_to(root):
            raise ProvenanceError("source census has a repeated or escaping repository")
        visited.add(resolved)
        actual = _head(owner)
        if pinned is not None and actual != pinned:
            raise ProvenanceError(f"source census checkout differs from committed pin: {relative}")
        status_bytes = _git(owner, "status", "--porcelain=v1", "-z",
                            "--untracked-files=all", "--ignore-submodules=none")
        diff = _git(owner, "diff", actual, "--binary", "--ignore-submodules=none",
                    "--no-ext-diff", "--no-textconv")
        owner_tracked, owner_untracked = _status_counts(status_bytes)
        tracked += owner_tracked
        untracked += owner_untracked
        rows.append(dict(path=relative.as_posix(), pin=pinned, head=actual,
                         status_sha256=digest(status_bytes), diff_sha256=digest(diff),
                         dirty_tracked=owner_tracked, dirty_untracked=owner_untracked))
        annotations.append(dict(path=relative.as_posix(), status=status_bytes.decode("utf-8")))
        links = _gitlinks(owner, actual)
        if _head(owner) != actual:
            raise ProvenanceError(f"source census HEAD changed during observation: {relative}")
        pending.extend((relative / path, pin) for path, pin in reversed(links))

    rows.sort(key=lambda row: row["path"])
    main = next(row for row in rows if row["path"] == ".")
    nested = [row for row in rows if row["path"] != "."]
    # Retain the old top-level observation as a diagnostic field. It is not
    # silently redefined to mean recursive and failure is never hashed as empty.
    top_level = _git(root, "submodule", "status")
    # A parent read before its descendants must still name the same commit at
    # the end. This detects observed HEAD races; it is not an atomic snapshot.
    for row in rows:
        if _head(root / row["path"]) != row["head"]:
            raise ProvenanceError(f"source census HEAD changed during observation: {row['path']}")
    fields = dict(record_version=RECORD_VERSION, head=main["head"],
                  head_short=main["head"][:9], tree_state="dirty" if tracked or untracked else "clean",
                  dirty_tracked=str(tracked), dirty_untracked=str(untracked),
                  diff_sha256=main["diff_sha256"], status_sha256=main["status_sha256"],
                  submodule_sha256=digest(top_level), submodule_census_scope=CENSUS_SCOPE,
                  recursive_submodule_sha256=digest(json.dumps(
                      nested, sort_keys=True, separators=(",", ":")).encode("utf-8")),
                  recursive_submodule_count=str(len(nested)))
    fields["tree_fingerprint"] = fingerprint(fields)
    return fields, json.dumps(dict(scope=CENSUS_SCOPE, repositories=rows, status=annotations),
                              sort_keys=True, indent=2) + "\n"


def _atomic_text(path: Path, text: str) -> None:
    descriptor, name = tempfile.mkstemp(prefix=path.name + ".pending-", dir=path.parent)
    try:
        with os.fdopen(descriptor, "w", encoding="utf-8") as output:
            output.write(text)
            output.flush()
            os.fsync(output.fileno())
        os.replace(name, path)
    finally:
        if os.path.exists(name):
            os.unlink(name)


class BuildStamp:
    """One invocation owns a start record and atomically replaces it at finish."""

    def __init__(self, root: Path, directory: Path, argv: list[str]):
        self.root, self.path = root, directory / "trust-build-provenance"
        self.fields = None
        self.done = False
        # Invalidate any previous completed record BEFORE a fallible census.
        # If even invalidation fails, continuing could let stale evidence seal
        # new output. The caller must stop that build rather than swallow it.
        directory.mkdir(parents=True, exist_ok=True)
        _atomic_text(self.path, "record_version=2\nrecord_kind=build-stamp\nexit_status=incomplete\n")
        self.argv = argv

    def start(self) -> dict[str, str]:
        facts, annotations = source_facts(self.root)
        fields = dict(record_version=RECORD_VERSION, record_kind="build-stamp",
                      started_at=str(int(time.time())), repo=str(self.root),
                      argv=" ".join(self.argv[:12]).replace("\n", " "))
        fields.update(facts)
        _atomic_text(Path(str(self.path) + ".status"), annotations)
        _atomic_text(self.path, render(fields))
        self.fields = fields
        return fields

    def finish(self, status: str) -> None:
        if self.done or self.fields is None:
            return
        self.done = True
        fields = dict(self.fields)
        try:
            final, _ = source_facts(self.root)
            end = final["tree_fingerprint"]
        except (ProvenanceError, OSError, UnicodeError):
            end = "unreadable"
        fields.update(completed_at=str(int(time.time())), exit_status=status,
                      end_tree_fingerprint=end,
                      tree_changed_during_build=("unknown" if end == "unreadable" else
                          "no" if end == fields["tree_fingerprint"] else "YES"))
        _atomic_text(self.path, render(fields))


def render(fields: dict[str, str]) -> str:
    return "".join(f"{key}={value}\n" for key, value in fields.items())


def validate_record(text: str, artifact_head: str) -> dict[str, str]:
    fields = {}
    for line in text.splitlines():
        if not line or line.startswith("#"):
            continue
        key, separator, value = line.partition("=")
        if not separator or not key or key in fields:
            raise ProvenanceError("build stamp has malformed or duplicate fields")
        fields[key] = value
    required = set(("record_version record_kind head started_at completed_at exit_status "
                    "tree_state dirty_tracked dirty_untracked diff_sha256 status_sha256 "
                    "submodule_sha256 tree_fingerprint end_tree_fingerprint "
                    "tree_changed_during_build").split())
    if not required.issubset(fields):
        raise ProvenanceError("build stamp is incomplete (missing required start/completion fields)")
    if fields["record_version"] not in ("1", RECORD_VERSION) or fields["record_kind"] != "build-stamp":
        raise ProvenanceError("build stamp has an unsupported version or kind")
    if fields["record_version"] == RECORD_VERSION:
        if not set(RECURSIVE_IDENTITY).issubset(fields):
            raise ProvenanceError("build stamp is incomplete (missing recursive census fields)")
        if fields["submodule_census_scope"] != CENSUS_SCOPE:
            raise ProvenanceError("build stamp has an unsupported recursive census scope")
    elif any(key in fields for key in RECURSIVE_IDENTITY[:3]):
        raise ProvenanceError("legacy build stamp cannot declare recursive census scope")
    if re.fullmatch(r"[0-9a-f]{40}|[0-9a-f]{64}", fields["head"]) is None:
        raise ProvenanceError("build stamp has an invalid HEAD")
    if fields["head"] != artifact_head:
        raise ProvenanceError("build stamp HEAD does not match this artifact")
    if fields["exit_status"] != "ok":
        raise ProvenanceError("build stamp does not record successful completion")
    numbers = ("started_at", "completed_at", "dirty_tracked", "dirty_untracked")
    hashes = ("diff_sha256", "status_sha256", "submodule_sha256",
              "tree_fingerprint", "end_tree_fingerprint")
    if fields["record_version"] == RECORD_VERSION:
        numbers += ("recursive_submodule_count",)
        hashes += ("recursive_submodule_sha256",)
    if any(re.fullmatch(r"0|[1-9][0-9]{0,18}", fields[key]) is None for key in numbers):
        raise ProvenanceError("build stamp has an invalid timestamp or change count")
    if int(fields["completed_at"]) < int(fields["started_at"]):
        raise ProvenanceError("build stamp completion precedes its start")
    if any(re.fullmatch(r"[0-9a-f]{64}", fields[key]) is None for key in hashes):
        raise ProvenanceError("build stamp has an invalid fingerprint")
    if fingerprint(fields) != fields["tree_fingerprint"]:
        raise ProvenanceError("build stamp start fingerprint does not match its source facts")
    same = fields["tree_fingerprint"] == fields["end_tree_fingerprint"]
    if fields["tree_changed_during_build"] != ("no" if same else "YES"):
        raise ProvenanceError("build stamp change flag and endpoint fingerprints disagree")
    if fields["tree_state"] == "clean":
        if (fields["dirty_tracked"] != "0" or fields["dirty_untracked"] != "0"
                or fields["diff_sha256"] != EMPTY_SHA256 or fields["status_sha256"] != EMPTY_SHA256):
            raise ProvenanceError("build stamp clean state contradicts its source facts")
    elif fields["tree_state"] == "dirty":
        if fields["dirty_tracked"] == fields["dirty_untracked"] == "0":
            raise ProvenanceError("build stamp dirty state contradicts its source facts")
        if fields["record_version"] == "1" and fields["status_sha256"] == EMPTY_SHA256:
            raise ProvenanceError("build stamp dirty state contradicts its source facts")
    else:
        raise ProvenanceError("build stamp has an invalid tree state")
    return fields


def require_recursive_source(fields: dict[str, str], source: Path) -> None:
    if fields["record_version"] != RECORD_VERSION or fields.get("submodule_census_scope") != CENSUS_SCOPE:
        raise ProvenanceError("legacy build stamp has only top-level scope, not recursive source admission")
    observed, _ = source_facts(source)
    if observed["tree_fingerprint"] != fields["end_tree_fingerprint"]:
        raise ProvenanceError("build stamp does not match the current recursive source census")


def read_record(path: Path) -> str:
    if not stat.S_ISREG(path.lstat().st_mode):
        raise ProvenanceError("build stamp is not a regular file")
    flags = os.O_RDONLY | getattr(os, "O_NONBLOCK", 0) | getattr(os, "O_NOFOLLOW", 0)
    descriptor = os.open(path, flags)
    with os.fdopen(descriptor, "rb") as input_file:
        if not stat.S_ISREG(os.fstat(input_file.fileno()).st_mode):
            raise ProvenanceError("build stamp is not a regular file")
        raw = input_file.read(65537)
    if len(raw) > 65536:
        raise ProvenanceError("build stamp is oversized")
    return raw.decode("utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("record", type=Path)
    parser.add_argument("artifact_head")
    parser.add_argument("source", type=Path)
    args = parser.parse_args()
    try:
        fields = validate_record(read_record(args.record), args.artifact_head)
        scope = fields.get("submodule_census_scope", LEGACY_SCOPE)
        # Dirty/changed evidence must stay visibly dirty even if the source has
        # since moved. Demoting it to generic unknown would evade --allow-dirty.
        if fields["record_version"] == RECORD_VERSION and fields["tree_state"] == "clean" and fields["tree_changed_during_build"] == "no":
            require_recursive_source(fields, args.source)
        print("\t".join(fields[key] for key in ("tree_state", "tree_changed_during_build",
                        "dirty_tracked", "dirty_untracked", "diff_sha256")) + "\t" + scope)
        return 0
    except (ProvenanceError, OSError, UnicodeError) as error:
        print(str(error))
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
