#!/usr/bin/env python3
"""check_patch_binds.py — a `[patch]` that does not BIND is worse than no patch.

Trust's root manifest redirects several git URLs to vendored first-party paths
so each patched package binding resolves exactly once, from that path:

    [patch."https://github.com/alabsystems/clean.git"]
    clean-kernel = { path = "first-party/clean/crates/clean-kernel" }

Cargo applies such an entry only when the replacement's VERSION satisfies the
dependency's version requirement. When a submodule pin moves across a version
bump, the requirement stops being satisfied, the patch silently stops applying,
and cargo reaches for the original git rev instead — producing a SECOND copy of
the crate that the patch existed to prevent. Nothing warns; `--locked` fails
with a message about updating the lock file, which reads like lock staleness.

That is what happened on 2026-08-19: `8dddf6c755` moved `first-party/clean` to
`bc0941514` as "fmt-only", but that rev carries clean's `0.1.0 -> 0.2.0`
workspace bump. `Cargo.lock` still records `clean-kernel 1.5.0`.

This gate reads only manifests and the lock, so it is cheap: milliseconds on
the working tree, about a second in the push reading (measured 2026-09-27 on
trust: ~90 short git calls). For every `[patch.<url>] <name> = { path = P }`:

  * P/Cargo.toml's version (resolving `version.workspace = true` against the
    nearest enclosing `[workspace.package]`) must MATCH exactly one path-owned
    `[[package]]` entry of that name and version in Cargo.lock -- otherwise
    `--locked` cannot hold; and
  * Cargo.lock must not hold another entry of that name from the source named by
    the patch table -- AT ANY VERSION -- otherwise that patched source still
    resolved alongside its replacement.

Cargo's package identity includes the source. A registry or unrelated-git
package with the same name and version is therefore allowed beside the path
replacement. Only a sourced row whose canonical source is the source being
patched is the duplicate this gate is meant to catch. Network-Git spellings
outside the deliberately audited URL subset fail closed; they are never guessed
to be unrelated.

"AT ANY VERSION" is a 2026-08-28 correction, and it is the whole reason this
gate did not catch the break it was written for. The rule used to compare only
rows whose version EQUALED the path manifest's, and the docstring said in as
many words that "another version of the same name" was allowed beside the
replacement -- with `scripts/tests/check_patch_binds_test.sh` asserting exit 0
for exactly that shape. But a different version from the patched source is not
a coexisting neighbour: it is the patch having been DROPPED for some consumer,
which is the only way that row can exist. Measured against origin/main's own
Cargo.lock: this gate exited 0 while the lock held `ay-core` 0.17.0 (submodule
path) beside `ay-core` 0.18.0 from `git+https://github.com/alabsystems/ay.git
?rev=45eb977133` -- 37 duplicated ay crates in all -- and `./x.py build
--stage 2` could not compile rustc_mir_transform ("multiple different versions
of crate `ay_core`"). With the correction the same lockfile yields 18 SPLIT
rows and exit 1.

The correction is scoped to git patch tables. `[patch.crates-io]` is the
opposite case: semver-major neighbours from the registry (`rustc-hash` 1.1.0
beside 2.1.2) coexist by design, and applying the rule there fails on a healthy
tree -- measured, before the carve-out went in.

WHICH TREE IS JUDGED (2026-09-27). The subject is the locked graph `--locked`
will see, and in a push that is the PUSHED commit's tree, not the checkout.
With TRUST_PUSHED_REFS set (the pre-push hook exports git's
`<local_ref> <local_sha> <remote_ref> <remote_sha>` lines), every non-deletion
local sha is judged on its own: root Cargo.toml and Cargo.lock come from that
commit, and each patched crate's manifests from the object store of the
submodule at the commit that tree PINS -- never from whatever the submodule has
checked out. Until then the gate read the working tree whatever was pushed, so
a committed SPLIT lock with a healthy uncommitted one on disk passed, as did
`git push origin topic:main` of a topic that moved `first-party/<x>` across a
version bump without the lock (8dddf6c755's exact shape), while uncommitted
WIP blocked a healthy push and even a ref deletion. A pushed tree whose
manifest, lock, submodule worktree or pinned rev cannot be read is an error,
never a skip; deletions have no tree and are not judged (all-deletion pushes
print `SKIPPED: `). With the variable unset or empty the working tree is judged,
as before. Either way a `SUBJECT:` line says which reading was taken.

A patch path whose Cargo.toml is missing is MISSING (exit 1) -- a patch that
points at nothing -- with ONE exception in the working-tree reading: the path
lies inside a gitlink (at HEAD) whose submodule worktree has no `.git`, i.e. the
submodule is simply not checked out, which check_pin_coherence.sh owns. The
skip used to cover every missing manifest, so a typo'd path, a vendored path
outside any submodule, or a checked-out pin that moved the crate directory all
printed OK with the false reason "submodule not checked out".

Exit 0 iff every patch entry of every judged tree binds (a push of deletions
only judges nothing and exits 0 after `SKIPPED: `). Author: Andrew Yates |
Apache-2.0
"""
from __future__ import annotations

import os
import pathlib
import re
import subprocess
import sys
from typing import Callable, Dict, List, Optional, Tuple
from urllib.parse import urlsplit, urlunsplit

PATCH_HEADER = re.compile(r'^\[patch\.(?:crates-io|"([^"]+)")\]\s*$')
TABLE_HEADER = re.compile(r"^\[")
ENTRY = re.compile(r'^\s*([A-Za-z0-9_-]+)\s*=\s*\{(.*)\}\s*$')
PATH_FIELD = re.compile(r'path\s*=\s*"([^"]+)"')
VERSION_FIELD = re.compile(r'^\s*version\s*=\s*"([^"]+)"', re.M)
WORKSPACE_VERSION = re.compile(r'^\s*version\s*\.?\s*workspace\s*=\s*true', re.M)
DNS_LABEL = re.compile(r"[A-Za-z0-9](?:[A-Za-z0-9-]*[A-Za-z0-9])?")
DNS_FINAL_LABEL = re.compile(r"[A-Za-z](?:[A-Za-z0-9-]*[A-Za-z0-9])?")
URL_PATH_SEGMENT = re.compile(r"[A-Za-z0-9._~!$&'()*+,;=:@-]*")


ZERO_SHA = re.compile(r"^0+$")
HEX_SHA = re.compile(r"^(?:[0-9a-f]{40}|[0-9a-f]{64})$")
FILE_MODES = {"100644", "100755"}


class GateError(Exception):
    """A read the verdict depends on could not be made. Always fails closed."""


_GIT_ENV: Optional[Dict[str, str]] = None


def git_env() -> Dict[str, str]:
    """The environment minus git's repository-local variables.

    A stray GIT_DIR/GIT_WORK_TREE/GIT_INDEX_FILE (a hook or `rebase -x` caller)
    would make every `git -C <dir>` below read that repository instead, so a
    submodule read could silently land in the superproject. Git names its own
    list, so none is hard-coded here.
    """
    global _GIT_ENV
    if _GIT_ENV is None:
        proc = subprocess.run(
            ["git", "rev-parse", "--local-env-vars"], capture_output=True, text=True,
        )
        if proc.returncode != 0:
            raise GateError(f"`git rev-parse --local-env-vars` failed: {proc.stderr.strip()}")
        local = set(proc.stdout.split())
        _GIT_ENV = {k: v for k, v in os.environ.items() if k not in local}
    return _GIT_ENV


def run_git(cwd: pathlib.Path, args: List[str]) -> bytes:
    """stdout of `git -C cwd args`; any nonzero exit is a GateError, never ''."""
    proc = subprocess.run(["git", "-C", str(cwd), *args], capture_output=True, env=git_env())
    if proc.returncode != 0:
        err = proc.stderr.decode("utf-8", "replace").strip()
        raise GateError(f"`git -C {cwd} {' '.join(args)}` failed (exit {proc.returncode}): {err}")
    return proc.stdout


def is_toplevel(path: pathlib.Path) -> bool:
    """Whether `path` is itself the top of a git worktree (not merely inside one)."""
    if not path.is_dir():
        return False
    try:
        top = run_git(path, ["rev-parse", "--show-toplevel"]).decode("utf-8", "surrogateescape").strip()
    except GateError:
        return False
    return pathlib.Path(top).resolve() == path.resolve()


def repo_root() -> pathlib.Path:
    """The workspace to check: argv[1] if given, else this script's own repo."""
    if len(sys.argv) > 1:
        return pathlib.Path(sys.argv[1]).resolve()
    out = subprocess.run(
        ["git", "rev-parse", "--show-toplevel"],
        cwd=pathlib.Path(__file__).resolve().parent,
        capture_output=True, text=True, check=True, env=git_env(),
    )
    return pathlib.Path(out.stdout.strip())


def rel_parts(rel: str) -> Optional[List[str]]:
    """`rel` as normalized path components under the root, or None if it escapes it.

    Lexical, like Cargo's own path normalization: `.` and empty components drop,
    `..` pops. An absolute path or one that climbs above the root cannot be read
    from a committed tree and is reported, not guessed at.
    """
    if rel.startswith("/"):
        return None
    parts: List[str] = []
    for part in rel.split("/"):
        if part in {"", "."}:
            continue
        if part == "..":
            if not parts:
                return None
            parts.pop()
            continue
        parts.append(part)
    return parts


class WorkingTree:
    """Files as they sit on disk under `root` (the no-push-in-flight reading)."""

    def __init__(self, root: pathlib.Path) -> None:
        self.root = root

    def read(self, parts: List[str]) -> Optional[str]:
        path = self.root.joinpath(*parts)
        return path.read_text(encoding="utf-8") if path.is_file() else None


class CommittedTree:
    """Files of one committed tree, read from object stores and never from disk.

    A gitlink on the way to a path is followed into that submodule's own object
    store at the commit THIS tree pins -- not the commit the submodule has
    checked out, which is what the working-tree reading sees and what a pushed
    ref that is not HEAD does not publish. A submodule that is not initialized,
    or whose store lacks the pin, is a GateError: this reading has no skip.
    """

    def __init__(self, repo: pathlib.Path, tree: str) -> None:
        self.repo = repo
        self.tree = tree
        self._listings: Dict[Tuple[str, str], Dict[str, Tuple[str, str]]] = {}
        self._entered: Dict[Tuple[str, str], str] = {}
        self._blobs: Dict[Tuple[str, ...], Optional[str]] = {}

    def _entries(self, repo: pathlib.Path, tree: str) -> Dict[str, Tuple[str, str]]:
        key = (str(repo), tree)
        if key not in self._listings:
            entries: Dict[str, Tuple[str, str]] = {}
            for record in run_git(repo, ["ls-tree", "-z", tree]).split(b"\0"):
                if not record:
                    continue
                meta, _, name = record.partition(b"\t")
                fields = meta.decode("ascii").split(" ")
                if len(fields) != 3 or not name:
                    raise GateError(f"unparseable `git ls-tree` record in {repo}: {record!r}")
                entries[name.decode("utf-8", "surrogateescape")] = (fields[0], fields[2])
            self._listings[key] = entries
        return self._listings[key]

    def _enter(self, repo: pathlib.Path, prefix: List[str], pin: str) -> Tuple[pathlib.Path, str]:
        sub = repo.joinpath(*prefix)
        key = (str(sub), pin)
        if key in self._entered:
            return sub, self._entered[key]
        where = "/".join(prefix)
        if not (sub / ".git").exists() or not is_toplevel(sub):
            raise GateError(
                f"submodule {where} (pinned at {pin}) is not initialized under {repo}, so the\n"
                f"            pinned manifests cannot be read; run `git submodule update --init {where}`."
            )
        try:
            tree = run_git(sub, ["rev-parse", "--verify", "--quiet", f"{pin}^{{tree}}"])
        except GateError:
            raise GateError(
                f"submodule {where}: the pinned rev {pin} is not in its object store;\n"
                f"            fetch it (`git -C {where} fetch`) -- an unreadable pin is not a pass."
            ) from None
        self._entered[key] = tree.decode("ascii").strip()
        return sub, self._entered[key]

    def _walk(self, parts: List[str], follow: bool):
        """Yield (repo, index, mode, sha) for each entry along `parts`, entering gitlinks iff `follow`."""
        repo, tree, start = self.repo, self.tree, 0
        for index, name in enumerate(parts):
            entry = self._entries(repo, tree).get(name)
            if entry is None:
                return
            mode, sha = entry
            yield repo, index, mode, sha
            if index == len(parts) - 1:
                return
            if mode == "040000":
                tree = sha
            elif mode == "160000" and follow:
                repo, tree = self._enter(repo, parts[start:index + 1], sha)
                start = index + 1
            else:
                return

    def read(self, parts: List[str]) -> Optional[str]:
        key = tuple(parts)
        if key not in self._blobs:
            self._blobs[key] = self._read(parts)
        return self._blobs[key]

    def _read(self, parts: List[str]) -> Optional[str]:
        for repo, index, mode, sha in self._walk(parts, follow=True):
            where = "/".join(parts[: index + 1])
            if mode == "120000":
                raise GateError(f"{where} is a symlink in the committed tree; not resolved here")
            if index < len(parts) - 1:
                if mode not in {"040000", "160000"}:
                    return None
                continue
            if mode not in FILE_MODES:
                return None
            try:
                return run_git(repo, ["cat-file", "blob", sha]).decode("utf-8")
            except UnicodeDecodeError:
                raise GateError(f"{where} is not UTF-8") from None
        return None

    def gitlink_on(self, parts: List[str]) -> Optional[List[str]]:
        """The prefix of `parts` recorded as a gitlink in this tree, if any."""
        for _repo, index, mode, _sha in self._walk(parts, follow=False):
            if mode == "160000":
                return parts[: index + 1]
        return None


def patch_entries(manifest_text: str):
    """(url, crate_name, path) for every `name = { path = ... }` under [patch.*]."""
    url = None
    for line in manifest_text.splitlines():
        header = PATCH_HEADER.match(line)
        if header:
            url = header.group(1) or "crates-io"
            continue
        if url is not None and TABLE_HEADER.match(line):
            url = None
            continue
        if url is None:
            continue
        entry = ENTRY.match(line)
        if not entry:
            continue
        path = PATH_FIELD.search(entry.group(2))
        if path:
            yield url, entry.group(1), path.group(1)


def manifest_version(reader, parts: List[str]) -> tuple[str | None, str]:
    """Declared version of the crate at `parts` (read through `reader`), and where it came from."""
    rel = "/".join(parts) or "."
    text = reader.read(parts + ["Cargo.toml"])
    if text is None:
        return None, f"no manifest at {rel}/Cargo.toml"
    # The crate's own `[package] version = "..."` wins over anything later in
    # the file (a `[dependencies] foo = { version = ... }` must not be read as
    # the package version), so scan only the [package] table.
    package = re.split(r"^\[", text, flags=re.M)
    for chunk in package:
        if not chunk.startswith("package]"):
            continue
        own = VERSION_FIELD.search(chunk)
        if own:
            return own.group(1), f"{rel}/Cargo.toml"
        if WORKSPACE_VERSION.search(chunk):
            break
    # `version.workspace = true`: walk up to the nearest [workspace.package],
    # through the same reader (so a pushed tree's walk never touches the disk).
    for depth in range(len(parts), -1, -1):
        candidate = parts[:depth] + ["Cargo.toml"]
        body = reader.read(candidate)
        if body is None:
            continue
        for chunk in re.split(r"^\[", body, flags=re.M):
            if chunk.startswith("workspace.package]"):
                ws = VERSION_FIELD.search(chunk)
                if ws:
                    return ws.group(1), f"{'/'.join(candidate)} [workspace.package]"
    return None, f"{rel}: version.workspace = true but no [workspace.package] above it"


def lock_versions(lock_text: str) -> dict[str, list[tuple[str, str | None]]]:
    """name -> [(version, source-or-None)] for every [[package]] in Cargo.lock."""
    found: dict[str, list[tuple[str, str | None]]] = {}
    name = version = source = None
    for line in lock_text.splitlines() + ["[[package]]"]:
        if line.strip() == "[[package]]":
            if name and version:
                found.setdefault(name, []).append((version, source))
            name = version = source = None
            continue
        key, _, raw = line.partition(" = ")
        value = raw.strip().strip('"')
        if key == "name":
            name = value
        elif key == "version":
            version = value
        elif key == "source":
            source = value
    return found


def canonical_url_path(path: str) -> str:
    """Apply the base-URL dot-segment normalization used by Cargo's URL parser."""
    normalized: list[str] = []
    for segment in path.split("/"):
        folded = segment.lower()
        if folded in {".", "%2e"}:
            continue
        if folded in {"..", ".%2e", "%2e.", "%2e%2e"}:
            # Keep the first empty component as the absolute-path root, but an
            # additional empty component is an ordinary segment and `..`
            # removes it (for example `/owner//../widget`).
            if len(normalized) > 1:
                normalized.pop()
            continue
        normalized.append(segment)
    return "/".join(normalized)


def audited_dns_hostname(hostname: str) -> bool:
    """Whether `hostname` is in the non-IP ASCII DNS subset audited below."""
    labels = hostname.split(".")
    return (
        len(labels) >= 2
        and all(DNS_LABEL.fullmatch(label) for label in labels)
        and DNS_FINAL_LABEL.fullmatch(labels[-1]) is not None
    )


def canonical_git_source(source: str) -> str | None:
    """Canonical repository URL for a Cargo git source or `[patch]` URL.

    Lock sources add a `git+` transport marker plus query/commit material;
    Cargo also treats a terminal `.git` and slash as repository spelling, not
    package identity. Cargo additionally special-cases GitHub: every supported
    transport becomes HTTPS and the repository path is lower-cased. Preserve
    transport, authority, port, and path for other hosts; HTTPS and SSH
    repositories are not generally assumed interchangeable.

    This intentionally accepts only the repository's auditable network-Git
    subset: ASCII http/https/ssh/git URLs, an optional simple username, a
    non-IP DNS hostname whose final label starts with a letter, an optional
    numeric port, and RFC path characters whose only percent escapes are
    URL-parser dot segments. Callers treat `None` as a gate error, never as
    evidence that two sources differ. That is safer than partially emulating
    WHATWG URL parsing for file URLs, IDNA, IPv4/IPv6, passwords, backslashes,
    or URL-encoded arbitrary path bytes.
    """
    raw = source.removeprefix("git+")
    base = raw.split("#", 1)[0].split("?", 1)[0]
    if not base.isascii() or "\\" in base or any(ch.isspace() for ch in base):
        return None
    parsed = urlsplit(raw)
    if parsed.scheme not in {"http", "https", "ssh", "git"} or not parsed.netloc:
        return None
    hostname = parsed.hostname
    if hostname is None or not hostname.isascii() or not audited_dns_hostname(hostname):
        return None
    if parsed.password is not None:
        return None
    if parsed.username is not None and not re.fullmatch(r"[A-Za-z0-9._~-]+", parsed.username):
        return None
    try:
        port = parsed.port
    except ValueError:
        return None

    original_scheme = parsed.scheme.lower()
    scheme = original_scheme
    for segment in parsed.path.split("/"):
        if "%" in segment:
            if segment.lower() not in {"%2e", ".%2e", "%2e.", "%2e%2e"}:
                return None
        elif URL_PATH_SEGMENT.fullmatch(segment) is None:
            return None
    path = canonical_url_path(parsed.path)
    if path.endswith("/"):
        path = path[:-1]
    if hostname.lower() == "github.com":
        # Match Cargo's CanonicalUrl GitHub rule exactly: protocol differences
        # and repository-path case do not create distinct package sources.
        scheme = "https"
        path = path.lower()
    if path.endswith(".git"):
        path = path[:-4]

    # URL schemes and DNS names are case-insensitive. Preserve raw userinfo,
    # but rebuild the host component so mixed-case host spellings compare
    # equally without accidentally rewriting matching text in the userinfo.
    userinfo, separator, _ = parsed.netloc.rpartition("@")
    prefix = f"{userinfo}@" if separator else ""
    rendered_host = hostname.lower()
    if ":" in rendered_host:
        rendered_host = f"[{rendered_host}]"
    authority = f"{prefix}{rendered_host}"
    is_default_port = (
        (original_scheme == "http" and port == 80)
        or (original_scheme == "https" and port == 443)
        or (scheme == "http" and port == 80)
        or (scheme == "https" and port == 443)
    )
    if port is not None and not is_default_port:
        authority += f":{port}"
    return urlunsplit((scheme, authority, path, "", ""))


def source_patch_relation(patch_source: str, lock_source: str) -> bool | None:
    """True=same source, False=provably distinct, None=unsupported spelling."""
    if patch_source == "crates-io":
        if lock_source in {
            "registry+https://github.com/rust-lang/crates.io-index",
            "sparse+https://index.crates.io/",
        }:
            return True
        if lock_source.startswith(("registry+", "sparse+")):
            return False
        if lock_source.startswith("git+"):
            return False if canonical_git_source(lock_source) is not None else None
        return None
    if lock_source.startswith(("registry+", "sparse+")):
        return False
    if not lock_source.startswith("git+"):
        return None
    patch = canonical_git_source(patch_source)
    locked = canonical_git_source(lock_source)
    if patch is None or locked is None:
        return None
    return patch == locked


Verdict = Tuple[List[str], int, int, int]


def judge(
    manifest_text: str,
    lock_text: str,
    reader,
    subject: str,
    missing_manifest: Callable[[List[str]], Optional[str]],
) -> Verdict:
    """(problems, checked, skipped, coexisting) for one manifest + lock + file reader.

    `missing_manifest(parts)` names why a patch path with no Cargo.toml may be
    skipped, or returns None to report it MISSING.
    """
    locked = lock_versions(lock_text)
    problems: list[str] = []
    checked = 0
    skipped = 0
    coexisting = 0
    for url, name, rel in patch_entries(manifest_text):
        parts = rel_parts(rel)
        if parts is None:
            checked += 1
            problems.append(
                f"UNREADABLE  [patch.\"{url}\"] {name} -> {rel}\n"
                "            the path is absolute or climbs above the workspace root."
            )
            continue
        try:
            present = reader.read(parts + ["Cargo.toml"]) is not None
            skip_reason = None if present else missing_manifest(parts)
        except GateError as error:
            checked += 1
            problems.append(f"ERROR       [patch.\"{url}\"] {name} -> {rel}\n            {error}")
            continue
        if not present:
            # An un-checked-out submodule is a DIFFERENT condition, owned by
            # check_pin_coherence.sh. Failing here too would only teach lanes to
            # ignore this gate in every worktree that has not run `submodule
            # update`. That is the ONLY missing manifest `missing_manifest`
            # excuses: a path outside every gitlink, or inside a submodule that
            # IS checked out, points at nothing, and that is this gate's finding.
            if skip_reason is not None:
                skipped += 1
                continue
            checked += 1
            problems.append(
                f"MISSING     [patch.\"{url}\"] {name} -> {rel}\n"
                f"            no {rel}/Cargo.toml in {subject}: the patch points at nothing."
            )
            continue
        if url != "crates-io" and canonical_git_source(url) is None:
            checked += 1
            problems.append(
                f"UNSUPPORTED [patch.\"{url}\"] {name} -> {rel}\n"
                "            patch source is outside the gate's audited network-Git URL subset;\n"
                "            refusing to guess at Cargo source identity."
            )
            continue
        try:
            declared, origin = manifest_version(reader, parts)
        except GateError as error:
            checked += 1
            problems.append(f"ERROR       [patch.\"{url}\"] {name} -> {rel}\n            {error}")
            continue
        checked += 1
        if declared is None:
            problems.append(
                f"UNREADABLE  [patch.\"{url}\"] {name} -> {rel}\n"
                f"            {origin}"
            )
            continue
        entries = locked.get(name, [])
        if not entries:
            problems.append(
                f"UNLOCKED    [patch.\"{url}\"] {name} -> {rel}\n"
                f"            manifest says {declared} ({origin}) but Cargo.lock has no\n"
                f"            [[package]] named {name} at all."
            )
            continue
        exact = [(version, source) for version, source in entries if version == declared]
        path_exact = [(version, source) for version, source in exact if source is None]
        source_relations = [
            (version, source, source_patch_relation(url, source))
            for version, source in exact
            if source is not None
        ]
        patched_source_exact = [
            (version, source) for version, source, relation in source_relations if relation is True
        ]
        unsupported_source_exact = [
            (version, source) for version, source, relation in source_relations if relation is None
        ]
        if len(path_exact) != 1:
            shown = ", ".join(f"{v} ({s or 'path'})" for v, s in entries)
            problems.append(
                f"UNBOUND     [patch.\"{url}\"] {name} -> {rel}\n"
                f"            manifest says {declared} ({origin})\n"
                f"            Cargo.lock holds: {shown}\n"
                f"            expected exactly one path-owned {name} {declared}; without it\n"
                f"            the patch is not part of the locked graph."
            )
            continue
        if unsupported_source_exact:
            shown = ", ".join(f"{v} ({s})" for v, s in unsupported_source_exact)
            problems.append(
                f"UNSUPPORTED [patch.\"{url}\"] {name} -> {rel}\n"
                f"            Cargo.lock holds exact-version source spelling(s) outside the\n"
                f"            gate's audited URL subset: {shown}\n"
                "            refusing to classify them as unrelated."
            )
            continue
        if patched_source_exact:
            shown = ", ".join(
                f"{v} ({s or 'path'})" for v, s in path_exact + patched_source_exact
            )
            problems.append(
                f"DUPLICATED  [patch.\"{url}\"] {name} -> {rel}\n"
                f"            Cargo.lock holds path-owned {name} {declared} and the source\n"
                f"            this patch replaces: {shown}\n"
                f"            The patched source still resolving beside its replacement is\n"
                f"            exactly what this gate exists to prevent."
            )
            continue
        # THE SAME DUPLICATE, AT A DIFFERENT VERSION — the shape this gate used to
        # wave through. Everything above compares only rows whose version EQUALS
        # the path manifest's, so a row from the patched source at a DIFFERENT
        # version fell straight to `coexisting` and was reported as benign. That is
        # precisely what a version-bump-induced patch drop produces: the path crate
        # keeps its own correctly-locked row, and the consumer that wanted the newer
        # version gets a second copy from git. Measured 2026-08-28 against
        # origin/main's own Cargo.lock: this gate exited 0 while the lock held 37
        # duplicated ay crates (`ay-core` 0.17.0 path AND 0.18.0 from
        # `git+https://github.com/alabsystems/ay.git?rev=45eb977133`) and
        # `./x.py build --stage 2` could not compile rustc_mir_transform.
        #
        # Version is not part of the question being asked. The invariant is "this
        # source resolves exactly once, from the path" — a second row from the
        # patched source violates it whatever version it carries.
        #
        # GIT PATCH TABLES ONLY. For `[patch.crates-io]` a second version of the
        # same name from the registry is ordinary, correct Rust — semver-major
        # neighbours (`rustc-hash` 1.1.0 beside 2.1.2) coexist by design and the
        # patch was never meant to claim them. Measured: without this guard the
        # gate fails on a HEALTHY tree at `[patch."crates-io"] rustc-hash`, which
        # would have made it useless within a day. The one-instance invariant is a
        # property of the first-party git sources, where every consumer is meant to
        # bind to the single checked-out submodule.
        inexact = [
            (version, source, source_patch_relation(url, source))
            for version, source in entries
            if source is not None and version != declared and url != "crates-io"
        ]
        unsupported_source_inexact = [(v, s) for v, s, rel in inexact if rel is None]
        patched_source_inexact = [(v, s) for v, s, rel in inexact if rel is True]
        if unsupported_source_inexact:
            shown = ", ".join(f"{v} ({s})" for v, s in unsupported_source_inexact)
            problems.append(
                f"UNSUPPORTED [patch.\"{url}\"] {name} -> {rel}\n"
                f"            Cargo.lock holds other-version source spelling(s) outside the\n"
                f"            gate's audited URL subset: {shown}\n"
                "            refusing to classify them as unrelated."
            )
            continue
        if patched_source_inexact:
            shown = ", ".join(f"{v} ({s or 'path'})" for v, s in path_exact + patched_source_inexact)
            problems.append(
                f"SPLIT       [patch.\"{url}\"] {name} -> {rel}\n"
                f"            manifest says {declared} ({origin}), but Cargo.lock ALSO holds\n"
                f"            {name} from the source this patch replaces, at another version:\n"
                f"            {shown}\n"
                f"            The patch did not apply for that consumer: cargo applies a patch\n"
                f"            only when the replacement version satisfies the requirement, and\n"
                f"            silently uses the git source when it does not. Move the pin and\n"
                f"            the declared version in the SAME edit, or the graph carries two\n"
                f"            incompatible copies of {name} and downstream fails with E0308."
            )
            continue
        coexisting += len(entries) - len(path_exact)

    return problems, checked, skipped, coexisting


def report(verdicts: List[Tuple[str, Verdict]]) -> int:
    """Print the combined verdict; `label` prefixes each problem when non-empty."""
    problems = [
        f"[{label}] {problem}" if label else problem
        for label, verdict in verdicts
        for problem in verdict[0]
    ]
    checked = sum(verdict[1] for _, verdict in verdicts)
    skipped = sum(verdict[2] for _, verdict in verdicts)
    coexisting = sum(verdict[3] for _, verdict in verdicts)
    if problems:
        print("check_patch_binds: FAIL — a [patch] entry does not bind\n", file=sys.stderr)
        if skipped:
            print(f"({skipped} further entries skipped: submodule not checked out)\n", file=sys.stderr)
        for problem in problems:
            print(problem + "\n", file=sys.stderr)
        return 1
    notes = []
    if coexisting:
        notes.append(f"{coexisting} unrelated-source/other-version package row(s) coexist")
    if skipped:
        notes.append(f"{skipped} skipped: submodule not checked out")
    note = f" ({'; '.join(notes)})" if notes else ""
    print(f"check_patch_binds: OK — {checked} path-redirecting [patch] entries bind{note}")
    return 0


def fail(message: str) -> int:
    print(f"check_patch_binds: FAIL — {message}", file=sys.stderr)
    return 1


def judge_working_tree(root: pathlib.Path) -> int:
    """The standing reading: Cargo.toml, Cargo.lock and every manifest on disk."""
    print(f"SUBJECT: the working tree at {root} (no push in flight: TRUST_PUSHED_REFS unset or empty)", flush=True)
    manifest, lock = root / "Cargo.toml", root / "Cargo.lock"
    if not lock.is_file():
        return fail(f"no Cargo.lock at {lock}")
    if not manifest.is_file():
        return fail(f"no Cargo.toml at {manifest}")
    head: List[Optional[CommittedTree]] = []

    def missing_manifest(parts: List[str]) -> Optional[str]:
        # Skip only a path inside a gitlink recorded at HEAD whose submodule
        # worktree is absent. Outside a git checkout there is no gitlink to
        # appeal to, so a missing manifest is MISSING.
        if not head:
            tree = None
            if is_toplevel(root):
                try:
                    tree = run_git(root, ["rev-parse", "--verify", "--quiet", "HEAD^{tree}"])
                except GateError:
                    tree = None  # unborn HEAD: no gitlinks, so nothing is excused
            head.append(CommittedTree(root, tree.decode("ascii").strip()) if tree else None)
        if head[0] is None:
            return None
        prefix = head[0].gitlink_on(parts)
        if prefix is None or (root.joinpath(*prefix) / ".git").exists():
            return None
        return "submodule not checked out"

    verdict = judge(
        manifest.read_text(encoding="utf-8"),
        lock.read_text(encoding="utf-8"),
        WorkingTree(root),
        "the working tree",
        missing_manifest,
    )
    return report([("", verdict)])


def parse_pushed_refs(raw: str) -> List[Tuple[str, str]]:
    """(local_ref, local_sha) per TRUST_PUSHED_REFS line; malformed input is a GateError."""
    pushed = []
    for line in raw.splitlines():
        if not line.strip():
            continue
        fields = line.split()
        if len(fields) != 4 or not HEX_SHA.match(fields[1]) or not HEX_SHA.match(fields[3]):
            raise GateError(
                f"malformed TRUST_PUSHED_REFS line {line!r}; expected "
                "`<local_ref> <local_sha> <remote_ref> <remote_sha>`"
            )
        pushed.append((fields[0], fields[1]))
    return pushed


def judge_pushed(root: pathlib.Path, raw: str) -> int:
    """The push reading: each non-deletion pushed sha's own committed tree."""
    try:
        pushed = parse_pushed_refs(raw)
    except GateError as error:
        return fail(str(error))
    live = [(ref, sha) for ref, sha in pushed if not ZERO_SHA.match(sha)]
    deletions = len(pushed) - len(live)
    if not live:
        print(f"SUBJECT: the pushed trees (TRUST_PUSHED_REFS: {deletions} deletion(s), nothing else)", flush=True)
        print("SKIPPED: deletion(s) only, no tree pushed — nothing to judge")
        return 0
    if not is_toplevel(root):
        return fail(f"TRUST_PUSHED_REFS is set but {root} is not the top of a git worktree")
    # One verdict per distinct tree; refs sharing a tree share its label.
    labels: Dict[str, List[str]] = {}
    verdicts: List[Tuple[str, Verdict]] = []
    for ref, sha in live:
        try:
            tree = run_git(root, ["rev-parse", "--verify", "--quiet", f"{sha}^{{tree}}"])
        except GateError:
            verdicts.append((f"{ref} {sha[:12]}", ([
                f"UNRESOLVED  pushed object {sha} does not name a tree in {root};\n"
                "            a push this gate cannot read is not a pass."
            ], 0, 0, 0)))
            continue
        labels.setdefault(tree.decode("ascii").strip(), []).append(f"{ref} {sha[:12]}")
    names = ", ".join(label for group in labels.values() for label in group)
    extra = f"; {deletions} deletion(s) not judged" if deletions else ""
    print(f"SUBJECT: the pushed trees (TRUST_PUSHED_REFS: {names}{extra}), not the working tree", flush=True)

    def never_skip(_parts: List[str]) -> Optional[str]:
        return None

    for tree, group in labels.items():
        label = ", ".join(group)
        reader = CommittedTree(root, tree)
        try:
            manifest_text = reader.read(["Cargo.toml"])
            lock_text = reader.read(["Cargo.lock"])
        except GateError as error:
            verdicts.append((label, ([f"ERROR       {error}"], 0, 0, 0)))
            continue
        if manifest_text is None or lock_text is None:
            absent = "Cargo.toml" if manifest_text is None else "Cargo.lock"
            verdicts.append((label, ([f"MISSING     the pushed tree has no root {absent}"], 0, 0, 0)))
            continue
        verdicts.append((label, judge(manifest_text, lock_text, reader, "the pushed tree", never_skip)))
    return report(verdicts)


def main() -> int:
    try:
        root = repo_root()
        raw = os.environ.get("TRUST_PUSHED_REFS", "")
        if raw.strip():
            return judge_pushed(root, raw)
        return judge_working_tree(root)
    except GateError as error:
        return fail(str(error))


if __name__ == "__main__":
    sys.exit(main())
