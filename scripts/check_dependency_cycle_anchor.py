#!/bin/sh
""":"
for candidate in python3.14 python3.13 python3.12 python3.11 python3; do
    if command -v "$candidate" >/dev/null 2>&1 \
        && "$candidate" -c 'import sys; raise SystemExit(sys.version_info < (3, 11))' 2>/dev/null; then
        exec "$candidate" "$0" "$@"
    fi
done
echo "check_dependency_cycle_anchor.py requires Python 3.11+ (tomllib)" >&2
exit 2
":"""
__doc__ = """Validate the first-party dependency constellation.

The validator derives its authority from committed Cargo/Lake surfaces and
root gitlinks.  The receipt is an exact inventory to compare with that
independent observation; it is never used as the source of dependency edges.
V3 evidence is printed from a clean committed HEAD and remains untracked.
Generation rejects replacement/graft/shallow history, hidden index flags, dirty
tracked paths, and non-ignored untracked paths in Trust and every bound
submodule.  Ignored untracked paths are allowed because evidence authority is
read exclusively from committed objects.

Python 3.11 or newer is required because manifests are parsed with tomllib.
Normal validation and preterminal derivation are deterministic and offline.
``--verify-remote`` adds a config-isolated, non-mutating ``git ls-remote``
check that Trust and every terminal pin are exactly canonical remote main.

THE REVISION IS SELECTED, NOT ASSUMED.  Every read in one judgement — receipt,
``.gitmodules``, gitlinks, exclusion policy, manifests — is taken at the same
tree-ish, and which one is a choice:

    --rev REV        an explicit commit-ish
    --push-context   the revision(s) the push in flight would publish, read
                     from $TRUST_PUSHED_REFS (exported by scripts/hooks/pre-push)
    (neither)        HEAD; external generation additionally proves the index
                     and worktree equal that committed HEAD

``--derive-when-receipt-absent`` derives and validates from the judged revision
when no receipt is committed there, which is the same coherence check without
the inventory comparison.  It never weakens what counts as incoherent.

An immutable committed policy marker makes every later TrustWP gitlink move a
permanent terminal claim.  Judging that selected revision then requires the
remote witness and exact full terminal cut; neither a stale checkout, R2, a
tracked legacy receipt, nor malformed W1 authority can downgrade the harness.
"""

import argparse
import base64
import configparser
import fnmatch
import json
import os
import posixpath
import re
import subprocess
import sys
import tempfile
import unicodedata
from pathlib import Path, PurePosixPath
from typing import Any, BinaryIO, NoReturn, Sequence
from urllib.parse import parse_qs, unquote, urlsplit, urlunsplit

try:
    import tomllib
except ModuleNotFoundError as error:  # pragma: no cover - exercised by CLI only
    raise SystemExit(
        "check_dependency_cycle_anchor.py requires Python 3.11+ (tomllib)"
    ) from error


SCHEMA = "trust.constellation.first-party.v2"
EXTERNAL_SCHEMA = "trust.constellation.first-party.v3"
SELF_SENTINEL = "CONTAINING_COMMIT"
RECEIPT_PATH = "docs/audits/first-party-constellation-v2.json"
EXTERNAL_RECEIPT_PATH = "docs/audits/first-party-constellation-v3.json"
EXCLUSIONS_PATH = "docs/audits/first-party-constellation-exclusions-v1.json"
EXCLUSIONS_SCHEMA = "trust.constellation.exclusions.v1"
ROOT_URL = "https://github.com/alabsystems/trust.git"
WP_DEPENDS_PATH = "spikes/DEPENDS.lock"
WP_DEPENDS_REPOSITORIES = {"ay", "clean", "trust", "trust-cg", "trust-ir"}
WP_ROOT_DELTA_PATH = "first-party/trust-wp"
WP_W1_REQUIRED_DELTAS = {"Cargo.toml", "VISION.md", WP_DEPENDS_PATH}
WP_AY_SHORT_WIDTH = 8
TERMINAL_POLICY_MARKER_PATH = ".trust-terminal-policy-v1"
TERMINAL_POLICY_MARKER = (
    b"trust.constellation.terminal-policy.v1\n"
    b"policy=trust-wp-root-cycle\n"
)
TERMINAL_POLICY_V2_MARKER_PATH = ".trust-terminal-policy-v2"
TERMINAL_POLICY_V2_W0 = "e7c353690e1b58a4e830edc9facb0e4396164585"
TERMINAL_POLICY_V2_PRESERVATION_FLOOR = (
    "1de995e192aabec74646d4d53642df05fa59466f"
)
TERMINAL_POLICY_V2_PRE_MARKER = (
    b"trust.constellation.terminal-policy.v2\n"
    b"state=pre-v2\n"
    b"policy=trust-wp-root-cycle-forward\n"
    b"w0=e7c353690e1b58a4e830edc9facb0e4396164585\n"
    b"preservation-floor=1de995e192aabec74646d4d53642df05fa59466f\n"
)
TERMINAL_POLICY_HISTORY_LIMIT = 100_000
WP_ROOT_ANCHOR_KEYS = {
    "authority_repository",
    "authority_commit",
    "authority_path",
    "anchor_repository",
    "anchor_commit",
    "terminal_repository",
    "terminal_commit",
    "only_tree_delta",
    "anchor_gitlink",
    "terminal_gitlink",
}
WP_ROOT_ANCHOR_V2_EXTRA_KEYS = {
    "policy_version",
    "preservation_floor",
    "predecessor_commit",
    "root_bindings",
}
GENERATION_CUT_REASON = (
    "finite exact-SHA generation cut; dependency predates this consumer generation"
)
SHA_RE = re.compile(r"[0-9a-f]{40}\Z")

SUBMODULES = {
    "ay": ("first-party/ay", "https://github.com/alabsystems/ay.git"),
    "clean": ("first-party/clean", "https://github.com/alabsystems/clean.git"),
    "ny": ("first-party/ny", "https://github.com/alabsystems/ny.git"),
    "trust-cg": (
        "first-party/trust-cg",
        "https://github.com/alabsystems/trust-cg.git",
    ),
    "trust-ir": (
        "first-party/trust-ir",
        "https://github.com/alabsystems/trust-ir.git",
    ),
    "trust-mc": (
        "first-party/trust-mc",
        "https://github.com/alabsystems/trust-mc.git",
    ),
    "trust-vc": (
        "first-party/trust-vc",
        "https://github.com/alabsystems/trust-vc.git",
    ),
    "trust-wp": (
        "first-party/trust-wp",
        "https://github.com/alabsystems/trust-wp.git",
    ),
    "ty": ("first-party/ty", "https://github.com/alabsystems/ty.git"),
}
CONSUMERS = {"trust", *SUBMODULES}
SURFACE_KINDS = {
    "cargo-git",
    "cargo-path",
    "cargo-patch-git",
    "cargo-patch-path",
    "cargo-replace-git",
    "cargo-replace-path",
    "cargo-lock",
    "lake-require",
    "lake-lock",
    "lake-path",
    "lake-path-lock",
    "proof-identity",
}
SURFACE_KEYS = {
    "id",
    "repository",
    "scope",
    "kind",
    "path",
    "locator",
    "dependency",
    "package",
    "url",
    "rev",
    "dependency_path",
    "subdir",
    "optional",
}
NY_IDENTITY_PATHS = {
    "crates/ny-cert/SPEC.md",
    "crates/ny-cert/proofs/README.md",
    "crates/ny-cert/proofs/lean/PROVENANCE.md",
    "crates/ny-cert/src/cite_check.rs",
    "crates/ny-cert/proofs/cite-map.json",
    "crates/ny-cert/proofs/lean/lakefile.toml",
    "crates/ny-cert/proofs/lean/lake-manifest.json",
}


class AnchorError(RuntimeError):
    """A fail-closed dependency-constellation finding."""


class UnresolvableAtRevision(AnchorError):
    """A finding that the constellation could not be READ at the chosen revision.

    Every other finding in this file is a statement about a constellation that
    was read and found incoherent.  This one says the authority the gate needs
    is not present at the revision it was pointed at — a different problem, with
    a different remedy, and one whose commonest cause is a stale local ``HEAD``
    rather than anything wrong with what is being pushed.  CLAUDE.md standing
    ruling v7/D3: a refusal must carry the fix, with options.  So this carries
    its own option list instead of being flattened into a one-line
    ``CONSTELLATION-INVALID`` that names no next step.
    """

    def __init__(self, message: str, options: Sequence[str]) -> None:
        super().__init__(message)
        self.options = list(options)


def fail(message: str) -> NoReturn:
    raise AnchorError(message)


def authority_git_environment() -> dict[str, str]:
    """Disable alternate history/object acquisition for every authority read."""
    environment = os.environ.copy()
    # A partial clone normally turns ``cat-file`` into an implicit network
    # operation when a promised object is absent.  Authority must come only
    # from objects already present in the judged checkout: fetching while
    # reading would silently admit ambient remote/config/credential authority
    # through a path that is intended to be local and replacement-disabled.
    environment["GIT_NO_LAZY_FETCH"] = "1"
    environment["GIT_NO_REPLACE_OBJECTS"] = "1"
    for key in (
        "GIT_ALTERNATE_OBJECT_DIRECTORIES",
        "GIT_COMMON_DIR",
        "GIT_DIR",
        "GIT_INDEX_FILE",
        "GIT_NAMESPACE",
        "GIT_OBJECT_DIRECTORY",
        "GIT_REPLACE_REF_BASE",
        "GIT_WORK_TREE",
    ):
        environment.pop(key, None)
    return environment


def remote_git_environment(
    ceiling: Path, *, authorization_header: str | None = None
) -> dict[str, str]:
    """Return a config-isolated environment for canonical remote probes.

    In particular, ``url.*.insteadOf`` must not be able to redirect a named
    GitHub authority to an attacker-controlled repository.  A remote probe has
    no repository cwd and reads neither system nor user Git configuration.
    Config-selected credential helpers are deliberately absent from this
    transport process.  When needed, a separately acquired credential is
    reintroduced only as the constructed GitHub-scoped authorization header.
    """
    environment = authority_git_environment()
    transport_overrides = {
        "CURL_CA_BUNDLE",
        "GIT_ALLOW_PROTOCOL",
        "GIT_ASKPASS",
        "GIT_CONFIG",
        "GIT_CONFIG_COUNT",
        "GIT_CONFIG_PARAMETERS",
        "GIT_EXEC_PATH",
        "GIT_CURL_VERBOSE",
        "GIT_PROTOCOL_FROM_USER",
        "GIT_PROXY_COMMAND",
        "GIT_SSH",
        "GIT_SSH_COMMAND",
        "GIT_SSL_CAINFO",
        "GIT_SSL_CAPATH",
        "GIT_SSL_CIPHER_LIST",
        "GIT_SSL_NO_VERIFY",
        "GIT_SSL_VERSION",
        "SSH_ASKPASS",
        "SSL_CERT_DIR",
        "SSL_CERT_FILE",
    }
    for key in list(environment):
        if key in transport_overrides or key.startswith(
            ("GIT_CONFIG_KEY_", "GIT_CONFIG_VALUE_", "GIT_TRACE")
        ):
            environment.pop(key, None)
    environment["GIT_CONFIG_NOSYSTEM"] = "1"
    environment["GIT_CONFIG_SYSTEM"] = os.devnull
    environment["GIT_CONFIG_GLOBAL"] = os.devnull
    environment["GIT_CEILING_DIRECTORIES"] = str(ceiling.resolve())
    environment["GIT_TERMINAL_PROMPT"] = "0"
    if authorization_header is not None:
        # Reintroduce one constructed, host-scoped setting after deleting all
        # ambient config injection.  It supplies credentials but cannot select
        # or rewrite the transport URL.
        environment["GIT_CONFIG_COUNT"] = "1"
        environment["GIT_CONFIG_KEY_0"] = "http.https://github.com/.extraHeader"
        environment["GIT_CONFIG_VALUE_0"] = authorization_header
    return environment


def credential_git_environment(ceiling: Path) -> dict[str, str]:
    """Allow normal credential helpers without using their config for transport."""
    environment = authority_git_environment()
    for key in list(environment):
        if key in {
            "GIT_CONFIG",
            "GIT_CONFIG_COUNT",
            "GIT_CONFIG_GLOBAL",
            "GIT_CONFIG_NOSYSTEM",
            "GIT_CONFIG_PARAMETERS",
            "GIT_CONFIG_SYSTEM",
        } or key.startswith(("GIT_CONFIG_KEY_", "GIT_CONFIG_VALUE_")):
            environment.pop(key, None)
    environment["GIT_CEILING_DIRECTORIES"] = str(ceiling.resolve())
    environment["GIT_TERMINAL_PROMPT"] = "0"
    return environment


def run_git(repo: Path, args: Sequence[str], *, check: bool = True) -> bytes:
    command = ["git", "-C", str(repo), *args]
    completed = subprocess.run(
        command,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        env=authority_git_environment(),
        check=False,
    )
    if check and completed.returncode != 0:
        detail = (completed.stderr or completed.stdout).decode("utf-8", "replace").strip()
        fail(f"{' '.join(command)} failed: {detail or f'exit {completed.returncode}'}")
    return completed.stdout


def strict_object(pairs: list[tuple[str, object]]) -> dict[str, object]:
    result: dict[str, object] = {}
    for key, value in pairs:
        if key in result:
            fail(f"receipt contains duplicate JSON key {key!r}")
        result[key] = value
    return result


def parse_json(raw: bytes, label: str) -> object:
    try:
        text = raw.decode("utf-8", "strict")
    except UnicodeDecodeError as error:
        fail(f"{label} is not valid UTF-8: {error}")
    try:
        return json.loads(text, object_pairs_hook=strict_object)
    except AnchorError:
        raise
    except (json.JSONDecodeError, RecursionError) as error:
        fail(f"{label} is not valid strict JSON: {error}")


def parse_toml(raw: bytes, label: str) -> dict[str, Any]:
    try:
        text = raw.decode("utf-8", "strict")
    except UnicodeDecodeError as error:
        fail(f"{label} is not valid UTF-8: {error}")
    try:
        value = tomllib.loads(text)
    except tomllib.TOMLDecodeError as error:
        fail(f"{label} is not valid TOML: {error}")
    if not isinstance(value, dict):  # tomllib currently always returns a dict
        fail(f"{label} top level must be a table")
    return value


def decode_text(raw: bytes, label: str) -> str:
    try:
        return raw.decode("utf-8", "strict")
    except UnicodeDecodeError as error:
        fail(f"{label} is not valid UTF-8: {error}")


def repeatedly_unquote(value: str) -> tuple[str, bool]:
    """Percent-decode to a bounded fixed point; flag intentionally deep encodings."""
    decoded = value
    for _ in range(8):
        next_value = unquote(decoded)
        if next_value == decoded:
            return decoded, False
        decoded = next_value
    return decoded, "%" in decoded


def might_reference_first_party(raw: bytes) -> bool:
    """Conservatively identify malformed fixtures that could hide an edge."""
    decoded, excessive = repeatedly_unquote(raw.decode("latin-1").lower())
    if excessive or "alabsystems" in decoded or "first-party/" in decoded:
        return True
    return any(("../" + name) in decoded for name in SUBMODULES)


def require_exact_keys(value: dict[str, object], expected: set[str], label: str) -> None:
    actual = set(value)
    if actual != expected:
        fail(
            f"{label} keys differ: missing={sorted(expected - actual)}, "
            f"extra={sorted(actual - expected)}"
        )


def require_nonempty_string(value: object, label: str) -> str:
    if not isinstance(value, str) or not value.strip():
        fail(f"{label} must be a non-empty string")
    return value


def require_sha(value: object, label: str) -> str:
    if not isinstance(value, str) or SHA_RE.fullmatch(value) is None:
        fail(f"{label} must be one lowercase full 40-hex commit id")
    if value == "0" * 40:
        fail(f"{label} may not be the all-zero object id")
    return value


class RawObjectReader:
    """Read literal Git objects through one replacement-disabled batch process."""

    def __init__(self, repo: Path, label: str) -> None:
        self.repo = repo
        self.label = label
        object_format = decode_text(
            run_git(repo, ["rev-parse", "--show-object-format"]),
            f"{label} object format",
        ).strip()
        if object_format != "sha1":
            fail(
                f"{label} uses unsupported object format {object_format!r}; "
                "the terminal policy requires literal 40-hex SHA-1 objects"
            )
        self._stderr = tempfile.TemporaryFile()
        self._process: subprocess.Popen[bytes] = subprocess.Popen(
            ["git", "-C", str(repo), "cat-file", "--batch"],
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=self._stderr,
            env=authority_git_environment(),
        )
        if self._process.stdin is None or self._process.stdout is None:
            self._abort()
            fail(f"could not open literal object reader for {label}")
        self._stdin: BinaryIO = self._process.stdin
        self._stdout: BinaryIO = self._process.stdout
        self._cache: dict[str, tuple[str, bytes]] = {}

    def __enter__(self) -> "RawObjectReader":
        return self

    def __exit__(self, exc_type: object, _exc: object, _traceback: object) -> None:
        if exc_type is not None:
            self._abort()
            return
        try:
            self._stdin.close()
            returncode = self._process.wait(timeout=5)
        except (BrokenPipeError, subprocess.TimeoutExpired):
            self._abort()
            fail(f"literal object reader for {self.label} did not exit cleanly")
        self._stdout.close()
        detail = self._stderr_detail()
        self._stderr.close()
        if returncode != 0:
            fail(
                f"literal object reader for {self.label} failed with exit "
                f"{returncode}: {detail or 'no diagnostic'}"
            )

    def _stderr_detail(self) -> str:
        self._stderr.seek(0)
        return self._stderr.read().decode("utf-8", "replace").strip()

    def _abort(self) -> None:
        process = getattr(self, "_process", None)
        if process is not None and process.poll() is None:
            process.terminate()
            try:
                process.wait(timeout=2)
            except subprocess.TimeoutExpired:
                process.kill()
                process.wait()
        for stream_name in ("_stdin", "_stdout"):
            stream = getattr(self, stream_name, None)
            if stream is None and process is not None:
                stream = getattr(
                    process, "stdin" if stream_name == "_stdin" else "stdout", None
                )
            if stream is not None and not stream.closed:
                stream.close()
        stderr = getattr(self, "_stderr", None)
        if stderr is not None and not stderr.closed:
            stderr.close()

    def read(self, oid: str, expected_type: str, label: str) -> bytes:
        oid = require_sha(oid, f"{label} object id")
        cached = self._cache.get(oid)
        if cached is None:
            try:
                self._stdin.write(oid.encode("ascii") + b"\n")
                self._stdin.flush()
            except BrokenPipeError:
                detail = self._stderr_detail()
                fail(
                    f"literal object reader for {self.label} closed early: "
                    f"{detail or 'no diagnostic'}"
                )
            header = self._stdout.readline(256)
            if not header.endswith(b"\n"):
                fail(f"{label} returned a missing or overlong cat-file header")
            fields = header[:-1].split(b" ")
            if len(fields) == 2 and fields[1] == b"missing":
                fail(f"{label} object {oid} is missing")
            if len(fields) != 3:
                fail(f"{label} returned malformed cat-file header {header!r}")
            try:
                observed_oid = fields[0].decode("ascii", "strict")
                object_type = fields[1].decode("ascii", "strict")
                size_text = fields[2].decode("ascii", "strict")
            except UnicodeDecodeError as error:
                fail(f"{label} returned non-ASCII cat-file metadata: {error}")
            if observed_oid != oid:
                fail(
                    f"{label} literal object identity changed: requested={oid}, "
                    f"observed={observed_oid}"
                )
            if re.fullmatch(r"0|[1-9][0-9]*", size_text) is None:
                fail(f"{label} returned malformed object size {size_text!r}")
            size = int(size_text)
            raw = self._stdout.read(size)
            if len(raw) != size or self._stdout.read(1) != b"\n":
                fail(f"{label} returned a truncated literal object")
            cached = (object_type, raw)
            self._cache[oid] = cached
        object_type, raw = cached
        if object_type != expected_type:
            fail(
                f"{label} object {oid} must be type {expected_type}, "
                f"not {object_type}"
            )
        return raw


def parse_raw_commit(
    reader: RawObjectReader, commit: str, label: str
) -> tuple[str, list[str]]:
    """Return the literal tree and parent headers of one commit object."""
    commit = require_sha(commit, f"{label} commit")
    raw = reader.read(commit, "commit", label)
    header, separator, _message = raw.partition(b"\n\n")
    if separator != b"\n\n":
        fail(f"{label} commit {commit} has no raw header terminator")
    tree: str | None = None
    parents: list[str] = []
    for line in header.split(b"\n"):
        if line.startswith(b"tree"):
            if not line.startswith(b"tree ") or tree is not None:
                fail(f"{label} commit {commit} has malformed/duplicate tree headers")
            try:
                tree_text = line[5:].decode("ascii", "strict")
            except UnicodeDecodeError as error:
                fail(f"{label} commit {commit} tree header is not ASCII: {error}")
            tree = require_sha(tree_text, f"{label} tree")
        elif line.startswith(b"parent"):
            if not line.startswith(b"parent "):
                fail(f"{label} commit {commit} has malformed parent header {line!r}")
            try:
                parent_text = line[7:].decode("ascii", "strict")
            except UnicodeDecodeError as error:
                fail(f"{label} commit {commit} parent header is not ASCII: {error}")
            parent = require_sha(parent_text, f"{label} parent")
            if parent in parents:
                fail(f"{label} commit {commit} repeats raw parent {parent}")
            parents.append(parent)
    if tree is None:
        fail(f"{label} commit {commit} has no raw tree header")
    return tree, parents


def parse_raw_tree(
    raw: bytes, label: str
) -> dict[bytes, tuple[str, str]]:
    """Parse one literal SHA-1 tree without invoking config-sensitive diff logic."""
    entries: dict[bytes, tuple[str, str]] = {}
    offset = 0
    valid_modes = {b"40000", b"100644", b"100755", b"120000", b"160000"}
    while offset < len(raw):
        space = raw.find(b" ", offset)
        nul = raw.find(b"\0", space + 1) if space >= 0 else -1
        if space < 0 or nul < 0 or nul == space + 1:
            fail(f"{label} contains a malformed literal tree entry")
        mode = raw[offset:space]
        name = raw[space + 1 : nul]
        oid_start = nul + 1
        oid_end = oid_start + 20
        if mode not in valid_modes or oid_end > len(raw):
            fail(f"{label} contains an invalid literal tree mode/object id")
        if name in entries or name in {b".", b".."} or b"/" in name:
            fail(f"{label} contains an invalid or duplicate literal tree name")
        entries[name] = (mode.decode("ascii"), raw[oid_start:oid_end].hex())
        offset = oid_end
    return entries


def raw_tree_path_entry(
    reader: RawObjectReader, tree: str, path: str, label: str
) -> tuple[str, str] | None:
    """Resolve a normalized path by reading literal tree objects component-wise."""
    components = path.split("/")
    if not components or any(
        not component or component in {".", ".."} for component in components
    ):
        fail(f"{label} requested malformed raw tree path {path!r}")
    current_tree = tree
    for index, component in enumerate(components):
        entries = parse_raw_tree(
            reader.read(current_tree, "tree", f"{label} tree"), label
        )
        entry = entries.get(component.encode("utf-8"))
        if entry is None:
            return None
        mode, oid = entry
        if index == len(components) - 1:
            return mode, oid
        if mode != "40000":
            fail(
                f"{label} path prefix {'/'.join(components[:index + 1])!r} "
                f"must be a tree, not mode {mode}"
            )
        current_tree = oid
    raise AssertionError("non-empty path resolution must return")


def require_optional_string(value: object, label: str) -> str | None:
    if value is None:
        return None
    return require_nonempty_string(value, label)


def require_relative_path(value: object, label: str) -> str:
    path = require_nonempty_string(value, label)
    pure = PurePosixPath(path)
    if pure.is_absolute() or path != pure.as_posix() or any(part in {"", ".", ".."} for part in pure.parts):
        fail(f"{label} must be a normalized non-parent relative POSIX path")
    return path


def canonical_json(value: object) -> str:
    return json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=True)


def first_party_url(raw: object, label: str, *, allow_alias: bool = False) -> str | None:
    """Return a repository name, rejecting recognizable non-canonical aliases."""
    if not isinstance(raw, str):
        return None
    value = raw[4:] if raw.startswith("git+") else raw
    for name, (_path, canonical) in SUBMODULES.items():
        if value == canonical:
            return name
    parsed_locator = urlsplit(value)
    has_network_scheme = re.match(r"^[A-Za-z][A-Za-z0-9+.-]*://", value) is not None
    is_scp_locator = re.match(r"^[^/@:\\]+@[^/:\\]+:.+", value) is not None
    is_windows_path = re.match(r"^[A-Za-z]:[\\/]", value) is not None
    if (
        parsed_locator.scheme.lower() == "file"
        or is_windows_path
        or (not has_network_scheme and not is_scp_locator)
    ):
        # Rust's own Cargo fixtures contain synthetic local Git locators such
        # as `[ROOTURL]/git-package`.  They are external test data, not part of
        # the nine-repository authority graph.  Reject only local locators that
        # can name a first-party repository; treating every unrelated local
        # fixture as authority made the old checker unusable on the real tree.
        decoded_local, excessive = repeatedly_unquote(value.lower())
        normalized_local = decoded_local.replace("\\", "/").rstrip("/")
        local_name = PurePosixPath(normalized_local.removeprefix("file://")).name
        if excessive or "first-party/" in normalized_local or local_name in SUBMODULES:
            fail(
                f"{label} uses unsupported local/file Git locator {value!r}; "
                "committed first-party Git authority must use a canonical network URL"
            )
        return None
    match = re.fullmatch(
        r"(?:https?://github\.com/alabsystems/|"
        r"ssh://git@github\.com(?::22)?/alabsystems/|"
        r"git@github\.com:alabsystems/)"
        r"([A-Za-z0-9._-]+?)(?:\.git)?/?",
        value,
    )
    if match is not None and match.group(1) in SUBMODULES:
        if allow_alias:
            return match.group(1)
        expected = SUBMODULES[match.group(1)][1]
        fail(f"{label} uses first-party URL alias {value!r}; expected exactly {expected!r}")
    decoded_value, excessive = repeatedly_unquote(value)
    if excessive:
        fail(f"{label} uses excessively encoded URL authority {value!r}")
    decoded_value = decoded_value.lower()
    if "alabsystems" in decoded_value:
        fail(
            f"{label} uses malformed or out-of-policy first-party URL {value!r}; "
            "only the exact nine canonical repositories are permitted"
        )
    return None


def committed_blob(repo: Path, commit: str, path: str) -> bytes:
    return run_git(repo, ["show", f"{commit}:{path}"])


def committed_tree_entries(repo: Path, commit: str) -> dict[str, tuple[str, str, str]]:
    raw = run_git(repo, ["ls-tree", "-r", "-z", commit])
    entries: dict[str, tuple[str, str, str]] = {}
    for raw_row in raw.split(b"\0"):
        if not raw_row:
            continue
        metadata, separator, raw_path = raw_row.partition(b"\t")
        fields = metadata.split()
        if separator != b"\t" or len(fields) != 3:
            fail(f"malformed committed tree row in {repo}: {raw_row!r}")
        try:
            mode, object_type, oid = (field.decode("ascii", "strict") for field in fields)
            path = raw_path.decode("utf-8", "strict")
        except UnicodeDecodeError as error:
            fail(f"tracked tree inventory in {repo} is not valid UTF-8/ASCII: {error}")
        if path in entries:
            fail(f"committed tree in {repo} repeats path {path!r}")
        entries[path] = (mode, object_type, oid)
    return entries


def changed_committed_tree_paths(repo: Path, before: str, after: str) -> list[str]:
    """Compare literal committed entry maps without consulting diff config.

    In particular, ``submodule.*.ignore`` must not be able to hide an extra
    gitlink change from either side of the terminal publication cut.
    """
    before_entries = committed_tree_entries(repo, before)
    after_entries = committed_tree_entries(repo, after)
    return sorted(
        path
        for path in set(before_entries) | set(after_entries)
        if before_entries.get(path) != after_entries.get(path)
    )


def require_regular_committed_authority(
    repo: Path, commit: str, path: str, label: str
) -> None:
    entry = committed_tree_entries(repo, commit).get(path)
    if entry is None:
        fail(f"{label} is not committed")
    mode, object_type, _oid = entry
    if object_type != "blob" or mode not in {"100644", "100755"}:
        fail(f"{label} must be a regular committed blob, not mode {mode} type {object_type}")


def committed_gitlink(repo: Path, commit: str, path: str, label: str) -> str:
    entry = committed_tree_entries(repo, commit).get(path)
    if entry is None:
        fail(f"{label} is not committed")
    mode, object_type, oid = entry
    if mode != "160000" or object_type != "commit":
        fail(f"{label} must be a committed gitlink, not mode {mode} type {object_type}")
    return require_sha(oid, label)


def require_unmodified_history_view(repo: Path, label: str) -> None:
    """Reject local Git mechanisms that can rewrite or truncate ancestry."""
    replacements = decode_text(
        run_git(repo, ["for-each-ref", "--format=%(refname)", "refs/replace/"]),
        f"{label} replacement-ref inventory",
    ).splitlines()
    if replacements:
        fail(f"{label} carries forbidden replacement refs: {replacements[:10]}")

    common_dir_text = decode_text(
        run_git(repo, ["rev-parse", "--path-format=absolute", "--git-common-dir"]),
        f"{label} Git common directory",
    ).strip()
    common_dir = Path(common_dir_text)
    if not common_dir.is_absolute():
        common_dir = lexical_absolute(repo / common_dir)
    grafts = common_dir / "info" / "grafts"
    if grafts.exists() or grafts.is_symlink():
        fail(f"{label} carries forbidden legacy graft authority at {grafts}")

    # Environment alternates are stripped by ``authority_git_environment``, but
    # a repository can also acquire objects implicitly through files below its
    # own common object directory.  Those files are ambient authority just as
    # much as a replacement ref or graft: without this refusal, deleting the
    # borrowed store can change whether the exact history is accepted.
    for alternate_name in ("alternates", "http-alternates"):
        alternates = common_dir / "objects" / "info" / alternate_name
        if alternates.exists() or alternates.is_symlink():
            fail(
                f"{label} carries forbidden repository-local alternate object "
                f"authority at {alternates}"
            )

    shallow = decode_text(
        run_git(repo, ["rev-parse", "--is-shallow-repository"]),
        f"{label} shallow-repository verdict",
    ).strip()
    if shallow not in {"true", "false"}:
        fail(f"{label} returned malformed shallow-repository verdict {shallow!r}")
    if shallow == "true":
        fail(f"{label} is shallow; complete parent authority is required")


def raw_commit_parents(repo: Path, commit: str, label: str) -> list[str]:
    """Read literal parent headers with replacement/graft semantics disabled."""
    commit = require_sha(commit, f"{label} commit")
    object_type = decode_text(
        run_git(repo, ["cat-file", "-t", commit]), f"{label} object type"
    ).strip()
    if object_type != "commit":
        fail(f"{label} {commit} is not a commit object")
    raw = run_git(repo, ["cat-file", "commit", commit])
    header, separator, _message = raw.partition(b"\n\n")
    if separator != b"\n\n":
        fail(f"{label} {commit} has no raw commit header terminator")
    parents: list[str] = []
    tree_rows = 0
    for line in header.split(b"\n"):
        if line.startswith(b"tree "):
            tree_rows += 1
            try:
                require_sha(line[5:].decode("ascii", "strict"), f"{label} tree")
            except UnicodeDecodeError as error:
                fail(f"{label} tree header is not ASCII: {error}")
        elif line.startswith(b"parent "):
            try:
                parent = line[7:].decode("ascii", "strict")
            except UnicodeDecodeError as error:
                fail(f"{label} parent header is not ASCII: {error}")
            parents.append(require_sha(parent, f"{label} parent"))
        elif line.startswith(b"parent"):
            fail(f"{label} contains malformed raw parent header {line!r}")
    if tree_rows != 1:
        fail(f"{label} must contain exactly one raw tree header; observed {tree_rows}")
    return parents


def parse_wp_depends_lock(raw: bytes) -> dict[str, str]:
    """Parse the terminal TrustWP cycle authority without accepting aliases.

    The five-row shape is part of TrustWP's spike-suite reproducibility guard.
    Only the ``trust`` row supplies the root-cycle edge here, but accepting a
    duplicate, unknown, or malformed sibling row would make that row ambiguous
    under a future parser or hand audit.
    """
    text = decode_text(raw, "trust-wp:spikes/DEPENDS.lock")
    pins: dict[str, str] = {}
    for line_number, authored in enumerate(text.splitlines(), start=1):
        line = authored.strip()
        if not line or line.startswith("#"):
            continue
        fields = line.split()
        if len(fields) != 3:
            fail(
                "trust-wp:spikes/DEPENDS.lock "
                f"line {line_number} must be '<repository> main <full commit>'"
            )
        repository, branch, commit = fields
        if repository not in WP_DEPENDS_REPOSITORIES:
            fail(
                "trust-wp:spikes/DEPENDS.lock "
                f"line {line_number} names unsupported repository {repository!r}"
            )
        if repository in pins:
            fail(
                "trust-wp:spikes/DEPENDS.lock contains duplicate "
                f"{repository!r} authority"
            )
        if branch != "main":
            fail(
                "trust-wp:spikes/DEPENDS.lock "
                f"{repository} branch must be exactly 'main'"
            )
        pins[repository] = require_sha(
            commit, f"trust-wp:spikes/DEPENDS.lock {repository} commit"
        )
    if set(pins) != WP_DEPENDS_REPOSITORIES:
        fail(
            "trust-wp:spikes/DEPENDS.lock must name exactly its five authority rows: "
            f"missing={sorted(WP_DEPENDS_REPOSITORIES - set(pins))}, "
            f"extra={sorted(set(pins) - WP_DEPENDS_REPOSITORIES)}"
        )
    return pins


def active_manifest_git_revisions(
    data: dict[str, Any], dependency: str, label: str
) -> list[str]:
    """Return direct active Git revisions for one dependency in a Cargo root."""
    tables: list[tuple[str, object]] = []
    for section in ("dependencies", "dev-dependencies", "build-dependencies"):
        tables.append((f"/{section}", data.get(section)))
    workspace = data.get("workspace")
    if isinstance(workspace, dict):
        for section in ("dependencies", "dev-dependencies", "build-dependencies"):
            tables.append((f"/workspace/{section}", workspace.get(section)))
    target = data.get("target")
    if isinstance(target, dict):
        for target_name, target_table in target.items():
            if not isinstance(target_table, dict):
                continue
            for section in ("dependencies", "dev-dependencies", "build-dependencies"):
                tables.append(
                    (f"/target/{target_name}/{section}", target_table.get(section))
                )
    patches = data.get("patch")
    if isinstance(patches, dict):
        for source, table in patches.items():
            tables.append((f"/patch/{source}", table))
    tables.append(("/replace", data.get("replace")))

    revisions: list[str] = []
    for base, table in tables:
        if not isinstance(table, dict):
            continue
        for alias, spec in table.items():
            if not isinstance(spec, dict) or "git" not in spec:
                continue
            repository = first_party_url(
                spec["git"], f"{label}:{base}/{alias}.git"
            )
            if repository == dependency:
                revisions.append(
                    require_sha(spec.get("rev"), f"{label}:{base}/{alias}.rev")
                )
    return revisions


def validate_wp_terminal_authority_bindings(
    repo_root: Path,
    wp_checkout: Path,
    terminal_wp: str,
    commits: dict[str, str],
) -> None:
    """Bind W1's active TrustIR and AY claims to the terminal constellation."""
    cargo_raw = committed_blob(wp_checkout, terminal_wp, "Cargo.toml")
    cargo = parse_toml(cargo_raw, "terminal TrustWP Cargo.toml")
    trust_ir_revisions = active_manifest_git_revisions(
        cargo, "trust-ir", "terminal TrustWP Cargo.toml"
    )
    if not trust_ir_revisions:
        fail("terminal TrustWP Cargo.toml has no active TrustIR Git revision")
    stale_ir = sorted(
        revision for revision in trust_ir_revisions if revision != commits["trust-ir"]
    )
    if stale_ir:
        fail(
            "terminal TrustWP Cargo.toml active TrustIR Git revisions must all "
            f"equal the root terminal trust-ir binding {commits['trust-ir']}; "
            f"observed={sorted(trust_ir_revisions)}"
        )

    ay_checkout = repo_root / SUBMODULES["ay"][0]
    require_regular_committed_authority(
        ay_checkout,
        commits["ay"],
        "Cargo.toml",
        "terminal AY workspace manifest authority",
    )
    ay_manifest = parse_toml(
        committed_blob(ay_checkout, commits["ay"], "Cargo.toml"),
        "terminal AY Cargo.toml",
    )
    ay_workspace = ay_manifest.get("workspace")
    ay_package = (
        ay_workspace.get("package") if isinstance(ay_workspace, dict) else None
    )
    ay_version = ay_package.get("version") if isinstance(ay_package, dict) else None
    if (
        not isinstance(ay_version, str)
        or re.fullmatch(r"[0-9A-Za-z.+-]+", ay_version) is None
    ):
        fail("terminal AY Cargo.toml workspace.package.version is missing or malformed")

    cargo_text = decode_text(cargo_raw, "terminal TrustWP Cargo.toml")
    ay_marker_lines = []
    for line in cargo_text.splitlines():
        normalized_line = unicodedata.normalize("NFKC", line)
        if re.match(
            r"^\s*#+\s*current(?:[\s_-]+)ay(?:[\s_-]+)authority\b",
            normalized_line,
            flags=re.IGNORECASE,
        ):
            ay_marker_lines.append(line)
    if len(ay_marker_lines) != 1:
        fail(
            "terminal TrustWP Cargo.toml must contain exactly one machine-checkable "
            "Current AY authority marker and no case/punctuation lookalikes"
        )
    ay_claim = re.fullmatch(
        r"# Current AY authority: version=(\S+) commit=([0-9a-f]{40})",
        ay_marker_lines[0],
    )
    if ay_claim is None:
        fail(
            "terminal TrustWP Cargo.toml AY authority marker must use the exact "
            "case, punctuation, and two-field shape"
        )
    observed_ay_claim = ay_claim.groups()
    if observed_ay_claim != (ay_version, commits["ay"]):
        fail(
            "terminal TrustWP Cargo.toml Current AY authority marker differs from "
            f"the committed AY authority: marker={observed_ay_claim}, "
            f"expected={(ay_version, commits['ay'])}"
        )

    vision_text = decode_text(
        committed_blob(wp_checkout, terminal_wp, "VISION.md"),
        "terminal TrustWP VISION.md",
    )
    vision_rows = []
    for line in vision_text.splitlines():
        cells = line.split("|")
        if len(cells) >= 3 and unicodedata.normalize(
            "NFKC", cells[1].strip()
        ).casefold() == "trust-wp-ay":
            vision_rows.append(line)
    if len(vision_rows) != 1:
        fail(
            "terminal TrustWP VISION.md must contain exactly one active "
            "trust-wp-ay row"
        )
    expected_vision_claim = (
        f"AY v{ay_version} backend at `{commits['ay'][:WP_AY_SHORT_WIDTH]}` "
        "on current `main`"
    )
    expected_vision_row = (
        "| trust-wp-ay | Building | See current review artifacts | "
        f"AYEncoder with native ADT theory, {expected_vision_claim}, "
        "separation logic encoding |"
    )
    if vision_rows[0] != expected_vision_row:
        fail(
            "terminal TrustWP VISION.md trust-wp-ay row must exactly bind the "
            f"committed AY authority; expected {expected_vision_row!r}"
        )


def render_terminal_policy_v2_armed(
    predecessor_commit: str, root_bindings: dict[str, str]
) -> bytes:
    """Render the one canonical armed-v2 marker.

    R0 commits this independently reviewable policy value.  Receipt material is
    later derived from it; it is never permitted to select these identities.
    """
    predecessor = require_sha(
        predecessor_commit, "terminal-policy v2 predecessor P"
    )
    if set(root_bindings) != set(SUBMODULES):
        fail(
            "terminal-policy v2 root binding vector must name exactly all nine "
            f"repositories: missing={sorted(set(SUBMODULES) - set(root_bindings))}, "
            f"extra={sorted(set(root_bindings) - set(SUBMODULES))}"
        )
    bindings = {
        name: require_sha(root_bindings[name], f"terminal-policy v2 root.{name}")
        for name in sorted(SUBMODULES)
    }
    if bindings["trust-wp"] != TERMINAL_POLICY_V2_W0:
        fail(
            "terminal-policy v2 armed R0 must preserve the exact W0 gitlink: "
            f"expected={TERMINAL_POLICY_V2_W0}, observed={bindings['trust-wp']}"
        )
    lines = [
        "trust.constellation.terminal-policy.v2",
        "state=armed",
        "policy=trust-wp-root-cycle-forward",
        f"w0={TERMINAL_POLICY_V2_W0}",
        f"preservation-floor={TERMINAL_POLICY_V2_PRESERVATION_FLOOR}",
        f"predecessor={predecessor}",
    ]
    lines.extend(f"root.{name}={bindings[name]}" for name in sorted(bindings))
    return ("\n".join(lines) + "\n").encode("ascii")


def parse_terminal_policy_v2_armed(raw: bytes) -> dict[str, Any]:
    """Parse armed-v2 only by round-tripping its canonical byte spelling."""
    try:
        text = raw.decode("ascii", "strict")
    except UnicodeDecodeError as error:
        fail(f"terminal-policy v2 marker is not ASCII: {error}")
    lines = text.splitlines()
    expected_prefix = [
        "trust.constellation.terminal-policy.v2",
        "state=armed",
        "policy=trust-wp-root-cycle-forward",
        f"w0={TERMINAL_POLICY_V2_W0}",
        f"preservation-floor={TERMINAL_POLICY_V2_PRESERVATION_FLOOR}",
    ]
    expected_count = len(expected_prefix) + 1 + len(SUBMODULES)
    if lines[: len(expected_prefix)] != expected_prefix or len(lines) != expected_count:
        fail(
            "terminal-policy v2 armed marker has malformed fixed fields or row "
            f"count; expected={expected_count}, observed={len(lines)}"
        )
    predecessor_row = lines[len(expected_prefix)]
    if not predecessor_row.startswith("predecessor="):
        fail("terminal-policy v2 armed marker is missing canonical predecessor row")
    predecessor = require_sha(
        predecessor_row.removeprefix("predecessor="),
        "terminal-policy v2 predecessor P",
    )
    binding_lines = lines[len(expected_prefix) + 1 :]
    expected_names = sorted(SUBMODULES)
    bindings: dict[str, str] = {}
    for expected_name, row in zip(expected_names, binding_lines):
        prefix = f"root.{expected_name}="
        if not row.startswith(prefix):
            fail(
                "terminal-policy v2 armed root vector is not in canonical exact "
                f"order; expected row for {expected_name!r}, observed={row!r}"
            )
        bindings[expected_name] = require_sha(
            row.removeprefix(prefix), f"terminal-policy v2 root.{expected_name}"
        )
    canonical = render_terminal_policy_v2_armed(predecessor, bindings)
    if raw != canonical:
        fail(
            "terminal-policy v2 armed marker differs from its canonical bytes "
            "(including final newline and duplicate/extra-field policy)"
        )
    return {"predecessor_commit": predecessor, "root_bindings": bindings}


def raw_commit_is_ancestor(
    reader: RawObjectReader, ancestor: str, descendant: str, label: str
) -> bool:
    """Literal, bounded ancestry without replacement views or lazy acquisition."""
    ancestor = require_sha(ancestor, f"{label} ancestor")
    descendant = require_sha(descendant, f"{label} descendant")
    pending = [descendant]
    visited: set[str] = set()
    while pending:
        current = pending.pop()
        if current == ancestor:
            return True
        if current in visited:
            continue
        if len(visited) >= TERMINAL_POLICY_HISTORY_LIMIT:
            fail(
                f"{label} raw ancestry walk exceeded bounded limit "
                f"{TERMINAL_POLICY_HISTORY_LIMIT}"
            )
        visited.add(current)
        _tree, parents = parse_raw_commit(reader, current, label)
        pending.extend(parent for parent in parents if parent not in visited)
    return False


def validate_terminal_policy_v2_wp_history(
    repo_root: Path, predecessor: str
) -> None:
    """Prove W0 -> ... -> B -> ... -> P from literal local TrustWP objects."""
    wp_checkout = repo_root / SUBMODULES["trust-wp"][0]
    require_unmodified_history_view(wp_checkout, "terminal-policy v2 TrustWP history")
    with RawObjectReader(wp_checkout, "terminal-policy v2 TrustWP history") as reader:
        if not raw_commit_is_ancestor(
            reader,
            TERMINAL_POLICY_V2_W0,
            TERMINAL_POLICY_V2_PRESERVATION_FLOOR,
            "terminal-policy v2 W0-to-B preservation",
        ):
            fail(
                "terminal-policy v2 preservation floor B is not a raw descendant "
                f"of exact W0: W0={TERMINAL_POLICY_V2_W0}, "
                f"B={TERMINAL_POLICY_V2_PRESERVATION_FLOOR}"
            )
        if not raw_commit_is_ancestor(
            reader,
            TERMINAL_POLICY_V2_PRESERVATION_FLOOR,
            predecessor,
            "terminal-policy v2 B-to-P preservation",
        ):
            fail(
                "terminal-policy v2 predecessor P does not preserve published "
                f"floor B: B={TERMINAL_POLICY_V2_PRESERVATION_FLOOR}, P={predecessor}"
            )


def terminal_wp_policy_v2_state(
    repo_root: Path, root_commit: str, commits: dict[str, str]
) -> dict[str, Any]:
    """Authenticate the forward-only PreV2 -> Armed(R0) -> Terminal(R1) state.

    The pre marker may propagate through ordinary raw merges.  Exactly one raw
    single-parent commit may replace it with a canonical armed marker; that
    commit is R0.  Once armed, the only further admissible judged revision is
    R0's raw sole child R1, so an intervening commit, merge, second cut, or
    move/revert history cannot be reinterpreted as the terminal publication.
    """
    require_unmodified_history_view(repo_root, "Trust terminal-policy v2 history")
    root_commit = require_sha(root_commit, "Trust terminal-policy v2 HEAD")
    with RawObjectReader(repo_root, "Trust terminal-policy v2 history") as reader:
        snapshots: dict[
            str,
            tuple[
                str,
                list[str],
                str,
                tuple[str, str] | None,
                dict[str, Any] | None,
            ],
        ] = {}

        def snapshot(
            commit: str, label: str
        ) -> tuple[
            str,
            list[str],
            str,
            tuple[str, str] | None,
            dict[str, Any] | None,
        ]:
            cached = snapshots.get(commit)
            if cached is not None:
                return cached
            tree, parents = parse_raw_commit(reader, commit, label)
            entry = raw_tree_path_entry(
                reader, tree, TERMINAL_POLICY_V2_MARKER_PATH, f"{label} marker"
            )
            policy: dict[str, Any] | None = None
            if entry is None:
                kind = "absent"
            else:
                mode, oid = entry
                if mode != "100644":
                    fail(
                        "Trust terminal-policy v2 marker must be a non-executable "
                        f"regular blob (mode 100644), not mode {mode} at {commit}"
                    )
                raw = reader.read(oid, "blob", f"{label} marker")
                if raw == TERMINAL_POLICY_V2_PRE_MARKER:
                    kind = "pre"
                else:
                    policy = parse_terminal_policy_v2_armed(raw)
                    kind = "armed"
            cached = (tree, parents, kind, entry, policy)
            snapshots[commit] = cached
            return cached

        pending = [root_commit]
        visited: set[str] = set()
        while pending:
            current = pending.pop()
            if current in visited:
                continue
            if len(visited) >= TERMINAL_POLICY_HISTORY_LIMIT:
                fail(
                    "Trust terminal-policy v2 raw DAG walk exceeded its bounded "
                    f"limit of {TERMINAL_POLICY_HISTORY_LIMIT} commits"
                )
            visited.add(current)
            _tree, parents, _kind, _entry, _policy = snapshot(
                current, "Trust terminal-policy v2 raw DAG history"
            )
            pending.extend(parent for parent in parents if parent not in visited)

        introductions: list[str] = []
        transitions: list[str] = []
        for commit in sorted(visited):
            _tree, parents, kind, entry, policy = snapshots[commit]
            parent_kinds = [snapshots[parent][2] for parent in parents]
            marked_parents = [
                parent
                for parent, parent_kind in zip(parents, parent_kinds)
                if parent_kind != "absent"
            ]
            if kind == "absent":
                if marked_parents:
                    fail(
                        "Trust terminal-policy v2 marker was deleted on a raw DAG "
                        f"edge: child={commit}, marked_parents={marked_parents}"
                    )
                continue
            if kind == "pre":
                armed_parents = [
                    parent
                    for parent, parent_kind in zip(parents, parent_kinds)
                    if parent_kind == "armed"
                ]
                if armed_parents:
                    fail(
                        "Trust terminal-policy v2 armed state was downgraded to "
                        f"PreV2: child={commit}, armed_parents={armed_parents}"
                    )
                if not marked_parents:
                    if len(parents) != 1 or parent_kinds != ["absent"]:
                        fail(
                            "Trust terminal-policy v2 PreV2 introduction must be a "
                            f"raw single-parent commit: commit={commit}, "
                            f"parents={parents}, parent_states={parent_kinds}"
                        )
                    introductions.append(commit)
                continue

            assert kind == "armed" and entry is not None and policy is not None
            armed_parents = [
                parent
                for parent, parent_kind in zip(parents, parent_kinds)
                if parent_kind == "armed"
            ]
            if not armed_parents:
                if len(parents) != 1 or parent_kinds != ["pre"]:
                    fail(
                        "Trust terminal-policy v2 Armed R0 transition must be a "
                        f"raw single-parent PreV2 child: commit={commit}, "
                        f"parents={parents}, parent_states={parent_kinds}"
                    )
                transitions.append(commit)
            else:
                if len(armed_parents) != len(parents):
                    fail(
                        "Trust terminal-policy v2 armed history may not merge an "
                        f"unarmed lineage: commit={commit}, parents={parents}, "
                        f"parent_states={parent_kinds}"
                    )
                changed_markers = {
                    parent: snapshots[parent][3]
                    for parent in armed_parents
                    if snapshots[parent][3] != entry
                }
                if changed_markers:
                    fail(
                        "Trust terminal-policy v2 armed marker changed after R0: "
                        f"child={commit}, mismatched_parents={changed_markers}"
                    )

        if not introductions:
            if any(snapshots[commit][2] != "absent" for commit in visited):
                fail("Trust terminal-policy v2 marked history has no PreV2 introduction")
            return {"state": "PreV2", "introduced": False}
        if len(introductions) != 1:
            fail(
                "Trust terminal-policy v2 must have one unique PreV2 raw "
                f"introduction; observed={introductions}"
            )
        head_kind = snapshots[root_commit][2]
        if head_kind == "absent":
            fail(
                "Trust terminal-policy v2 HEAD is unmarked after its unique "
                f"introduction {introductions[0]}"
            )
        if not transitions:
            if head_kind != "pre":
                fail("Trust terminal-policy v2 armed HEAD has no authenticated R0")
            return {
                "state": "PreV2",
                "introduced": True,
                "introduction_commit": introductions[0],
            }
        if len(transitions) != 1:
            fail(
                "Trust terminal-policy v2 must have one unique Armed R0 "
                f"transition; observed={transitions}"
            )
        r0 = transitions[0]
        policy = snapshots[r0][4]
        assert policy is not None
        r0_submodules = committed_submodules(repo_root, r0)
        r0_bindings = {
            name: commit for name, (_path, _url, commit) in r0_submodules.items()
        }
        if r0_bindings != policy["root_bindings"]:
            fail(
                "Trust terminal-policy v2 Armed R0 tree differs from the exact "
                f"nine-vector committed by its policy: policy={policy['root_bindings']}, "
                f"observed={r0_bindings}"
            )
        # Re-evaluate the preserved v1 tripwire at R0 itself, even when the
        # candidate under judgement is Terminal R1.  Looking only at R1 makes
        # the required W0 -> W1 move true while losing the distinction between
        # a clean PreV2 history and an earlier W0 -> X -> W0 move/revert that
        # was laundered before arming.
        if terminal_wp_policy_claimed(repo_root, r0, r0_bindings):
            fail(
                "terminal-policy v2 Armed R0 has prior v1 TrustWP-move history; "
                "R0 must still bind exact W0 with no move/revert claim"
            )
        validate_terminal_policy_v2_wp_history(
            repo_root, policy["predecessor_commit"]
        )
        result = {
            "r0": r0,
            "policy": policy,
            "introduction_commit": introductions[0],
        }
        if root_commit == r0:
            if commits != policy["root_bindings"]:
                fail("Trust terminal-policy v2 Armed R0 current bindings drifted")
            result["state"] = "Armed"
            return result
        root_parents = snapshots[root_commit][1]
        if root_parents != [r0]:
            fail(
                "Trust terminal-policy v2 Terminal R1 must be R0's direct raw "
                f"sole child; R0={r0}, candidate={root_commit}, parents={root_parents}"
            )
        expected_terminal_bindings = dict(policy["root_bindings"])
        expected_terminal_bindings["trust-wp"] = commits["trust-wp"]
        if commits != expected_terminal_bindings:
            fail(
                "Trust terminal-policy v2 Terminal R1 changed a non-TrustWP member "
                f"of the armed nine-vector: expected={expected_terminal_bindings}, "
                f"observed={commits}"
            )
        if commits["trust-wp"] == TERMINAL_POLICY_V2_W0:
            fail("Trust terminal-policy v2 Terminal R1 did not advance TrustWP from W0")
        result["state"] = "Terminal"
        result["r1"] = root_commit
        return result


def derive_wp_root_anchor(
    repo_root: Path,
    root_commit: str,
    commits: dict[str, str],
) -> dict[str, str]:
    """Authenticate the one permitted TrustWP -> Trust generation cut.

    W1 is taken only from R1's committed gitlink and R0 only from R1's raw sole
    parent.  The committed ``W1:spikes/DEPENDS.lock`` Trust row must independently
    agree with that R0.  The hash cycle is broken in exactly one place: R1's
    complete tree delta must be the TrustWP gitlink from W0 to W1.
    """
    require_unmodified_history_view(repo_root, "Trust root")
    root_type = run_git(repo_root, ["cat-file", "-t", root_commit]).decode(
        "ascii", "strict"
    ).strip()
    if root_type != "commit":
        fail(f"root terminal {root_commit} is not a commit object")

    terminal_wp = commits["trust-wp"]
    linked_terminal_wp = committed_gitlink(
        repo_root, root_commit, WP_ROOT_DELTA_PATH, "root terminal TrustWP gitlink"
    )
    if linked_terminal_wp != terminal_wp:
        fail(
            "root terminal TrustWP gitlink differs from the terminal repository binding: "
            f"gitlink={linked_terminal_wp}, binding={terminal_wp}"
        )

    wp_checkout = repo_root / SUBMODULES["trust-wp"][0]
    require_unmodified_history_view(wp_checkout, "terminal TrustWP")
    root_parents = raw_commit_parents(repo_root, root_commit, "root terminal R1")
    if len(root_parents) != 1:
        fail(
            "root terminal must have exactly one raw parent R0; "
            f"terminal={root_commit}, parents={root_parents}"
        )
    anchor = root_parents[0]
    anchor_type = run_git(repo_root, ["cat-file", "-t", anchor]).decode(
        "ascii", "strict"
    ).strip()
    if anchor_type != "commit":
        fail(f"root terminal raw parent R0 {anchor} is not a local commit object")

    changed = changed_committed_tree_paths(repo_root, anchor, root_commit)
    if changed != [WP_ROOT_DELTA_PATH]:
        fail(
            "root terminal's only tree delta from the TrustWP anchor must be "
            f"{WP_ROOT_DELTA_PATH!r}; observed={changed}"
        )

    anchor_wp = committed_gitlink(
        repo_root, anchor, WP_ROOT_DELTA_PATH, "root anchor TrustWP gitlink"
    )
    if anchor_wp == terminal_wp:
        fail("root terminal TrustWP gitlink did not advance from its anchor value")
    anchor_wp_type = decode_text(
        run_git(wp_checkout, ["cat-file", "-t", anchor_wp]),
        "root anchor TrustWP W0 object type",
    ).strip()
    if anchor_wp_type != "commit":
        fail(f"root anchor TrustWP W0 {anchor_wp} is not a local commit object")
    wp_parents = raw_commit_parents(wp_checkout, terminal_wp, "terminal TrustWP W1")
    if wp_parents != [anchor_wp]:
        fail(
            "terminal TrustWP W1 must be the root anchor gitlink W0's direct "
            f"single-parent child: W1={terminal_wp}, W0={anchor_wp}, "
            f"parents={wp_parents}"
        )

    wp_changed = changed_committed_tree_paths(wp_checkout, anchor_wp, terminal_wp)
    missing_required = sorted(WP_W1_REQUIRED_DELTAS - set(wp_changed))
    disallowed = sorted(
        path
        for path in wp_changed
        if path not in WP_W1_REQUIRED_DELTAS
        and PurePosixPath(path).name != "Cargo.lock"
    )
    if missing_required or disallowed:
        fail(
            "terminal TrustWP W0 -> W1 tree delta violates the exact publication "
            "allow-policy: required non-lock changes are Cargo.toml, VISION.md, "
            f"and {WP_DEPENDS_PATH}; every other change must be a Cargo.lock; "
            f"missing_required={missing_required}, disallowed={disallowed}"
        )
    for path in sorted(WP_W1_REQUIRED_DELTAS):
        require_regular_committed_authority(
            wp_checkout, anchor_wp, path, f"TrustWP W0 required authority {path}"
        )
        require_regular_committed_authority(
            wp_checkout, terminal_wp, path, f"TrustWP W1 required authority {path}"
        )
    for path in wp_changed:
        if PurePosixPath(path).name == "Cargo.lock":
            require_regular_committed_authority(
                wp_checkout, anchor_wp, path, f"TrustWP W0 tracked lock {path}"
            )
            require_regular_committed_authority(
                wp_checkout, terminal_wp, path, f"TrustWP W1 lock delta {path}"
            )

    pins = parse_wp_depends_lock(
        committed_blob(wp_checkout, terminal_wp, WP_DEPENDS_PATH)
    )
    if pins["trust"] != anchor:
        fail(
            "terminal TrustWP spikes/DEPENDS.lock Trust pin must exactly equal "
            f"root terminal's raw sole parent R0: pin={pins['trust']}, R0={anchor}"
        )
    for repository in sorted(WP_DEPENDS_REPOSITORIES - {"trust"}):
        if pins[repository] != commits[repository]:
            fail(
                "terminal TrustWP spikes/DEPENDS.lock sibling pin differs from "
                f"the root terminal binding for {repository}: "
                f"pin={pins[repository]}, binding={commits[repository]}"
            )
    validate_wp_terminal_authority_bindings(
        repo_root, wp_checkout, terminal_wp, commits
    )

    return {
        "authority_repository": "trust-wp",
        "authority_commit": terminal_wp,
        "authority_path": WP_DEPENDS_PATH,
        "anchor_repository": "trust",
        "anchor_commit": anchor,
        "terminal_repository": "trust",
        "terminal_commit": root_commit,
        "only_tree_delta": WP_ROOT_DELTA_PATH,
        "anchor_gitlink": anchor_wp,
        "terminal_gitlink": terminal_wp,
    }


def derive_wp_root_anchor_v2(
    repo_root: Path,
    root_commit: str,
    commits: dict[str, str],
    policy_state: dict[str, Any],
) -> dict[str, Any]:
    """Authenticate the forward-only P -> W1 and R0 -> R1 publication cut."""
    if policy_state.get("state") != "Terminal":
        fail("terminal-policy v2 root-anchor derivation requires Terminal state")
    r0 = require_sha(policy_state.get("r0"), "terminal-policy v2 R0")
    policy = policy_state.get("policy")
    if not isinstance(policy, dict):
        fail("terminal-policy v2 Terminal state is missing its armed policy")
    predecessor = require_sha(
        policy.get("predecessor_commit"), "terminal-policy v2 predecessor P"
    )
    root_bindings_value = policy.get("root_bindings")
    if not isinstance(root_bindings_value, dict):
        fail("terminal-policy v2 armed policy is missing its root binding vector")
    root_bindings = {
        name: require_sha(root_bindings_value.get(name), f"terminal-policy v2 root.{name}")
        for name in sorted(SUBMODULES)
    }
    if set(root_bindings_value) != set(SUBMODULES):
        fail("terminal-policy v2 armed policy root binding vector is not exact")

    require_unmodified_history_view(repo_root, "Trust terminal-policy v2 root")
    root_parents = raw_commit_parents(
        repo_root, root_commit, "terminal-policy v2 root terminal R1"
    )
    if root_parents != [r0]:
        fail(
            "terminal-policy v2 root terminal R1 must have exact raw sole parent "
            f"R0={r0}; observed={root_parents}"
        )
    changed = changed_committed_tree_paths(repo_root, r0, root_commit)
    if changed != [WP_ROOT_DELTA_PATH]:
        fail(
            "terminal-policy v2 R0 -> R1 only tree delta must be "
            f"{WP_ROOT_DELTA_PATH!r}; observed={changed}"
        )
    anchor_wp = committed_gitlink(
        repo_root, r0, WP_ROOT_DELTA_PATH, "terminal-policy v2 R0 TrustWP gitlink"
    )
    if anchor_wp != TERMINAL_POLICY_V2_W0:
        fail(
            "terminal-policy v2 R0 TrustWP gitlink differs from exact W0: "
            f"expected={TERMINAL_POLICY_V2_W0}, observed={anchor_wp}"
        )
    terminal_wp = committed_gitlink(
        repo_root,
        root_commit,
        WP_ROOT_DELTA_PATH,
        "terminal-policy v2 R1 TrustWP gitlink",
    )
    if terminal_wp != commits["trust-wp"]:
        fail(
            "terminal-policy v2 R1 TrustWP gitlink differs from the current "
            f"repository binding: gitlink={terminal_wp}, binding={commits['trust-wp']}"
        )

    wp_checkout = repo_root / SUBMODULES["trust-wp"][0]
    require_unmodified_history_view(wp_checkout, "terminal-policy v2 TrustWP")
    wp_parents = raw_commit_parents(
        wp_checkout, terminal_wp, "terminal-policy v2 TrustWP W1"
    )
    if wp_parents != [predecessor]:
        fail(
            "terminal-policy v2 TrustWP W1 must have exact raw sole parent P: "
            f"W1={terminal_wp}, P={predecessor}, parents={wp_parents}"
        )

    wp_changed = changed_committed_tree_paths(wp_checkout, predecessor, terminal_wp)
    missing_required = sorted(WP_W1_REQUIRED_DELTAS - set(wp_changed))
    disallowed = sorted(
        path
        for path in wp_changed
        if path not in WP_W1_REQUIRED_DELTAS
        and PurePosixPath(path).name != "Cargo.lock"
    )
    if missing_required or disallowed:
        fail(
            "terminal-policy v2 TrustWP P -> W1 tree delta violates the exact "
            "publication allow-policy: required non-lock changes are Cargo.toml, "
            f"VISION.md, and {WP_DEPENDS_PATH}; every other change must be a "
            f"Cargo.lock; missing_required={missing_required}, disallowed={disallowed}"
        )
    for path in sorted(WP_W1_REQUIRED_DELTAS):
        require_regular_committed_authority(
            wp_checkout, predecessor, path, f"TrustWP P required authority {path}"
        )
        require_regular_committed_authority(
            wp_checkout, terminal_wp, path, f"TrustWP W1 required authority {path}"
        )
    for path in wp_changed:
        if PurePosixPath(path).name == "Cargo.lock":
            require_regular_committed_authority(
                wp_checkout, predecessor, path, f"TrustWP P tracked lock {path}"
            )
            require_regular_committed_authority(
                wp_checkout, terminal_wp, path, f"TrustWP W1 lock delta {path}"
            )

    pins = parse_wp_depends_lock(
        committed_blob(wp_checkout, terminal_wp, WP_DEPENDS_PATH)
    )
    if pins["trust"] != r0:
        fail(
            "terminal-policy v2 TrustWP spikes/DEPENDS.lock Trust pin must "
            f"exactly equal R0: pin={pins['trust']}, R0={r0}"
        )
    for repository in sorted(WP_DEPENDS_REPOSITORIES - {"trust"}):
        if pins[repository] != root_bindings[repository]:
            fail(
                "terminal-policy v2 TrustWP spikes/DEPENDS.lock sibling pin "
                f"differs from armed R0 for {repository}: pin={pins[repository]}, "
                f"R0-binding={root_bindings[repository]}"
            )
    validate_wp_terminal_authority_bindings(
        repo_root, wp_checkout, terminal_wp, commits
    )

    return {
        "authority_repository": "trust-wp",
        "authority_commit": terminal_wp,
        "authority_path": WP_DEPENDS_PATH,
        "anchor_repository": "trust",
        "anchor_commit": r0,
        "terminal_repository": "trust",
        "terminal_commit": root_commit,
        "only_tree_delta": WP_ROOT_DELTA_PATH,
        "anchor_gitlink": TERMINAL_POLICY_V2_W0,
        "terminal_gitlink": terminal_wp,
        "policy_version": "trust.constellation.terminal-policy.v2",
        "preservation_floor": TERMINAL_POLICY_V2_PRESERVATION_FLOOR,
        "predecessor_commit": predecessor,
        "root_bindings": root_bindings,
    }


def terminal_wp_policy_claimed(
    repo_root: Path, root_commit: str, commits: dict[str, str]
) -> bool:
    """Persistently select terminal mode after the marker-authorized WP move.

    The exact marker has one unique raw single-parent introduction in the
    complete ancestry DAG.  It may propagate through a merge whose first parent
    is an older unmarked branch: every marked parent must descend from that same
    introduction, while every unmarked parent must publish no TrustWP binding
    the pre-activation history had not already published.  The merge must retain
    the marked binding.  Thus merging an old branch cannot erase the regime or
    smuggle a side-branch WP move into it.

    THE MARKED SUBGRAPH IS WHAT DECIDES THE JUDGED BINDING, and it decides it
    alone.  HEAD must be marked; every marked commit must descend through a
    marked parent; a marked commit with several parents must retain every marked
    parent's binding; and the only shape that may change the binding is an
    ordinary one-parent marked commit, which sets the claim.  By induction the
    judged revision therefore carries the pre-activation binding unless the claim
    is set, whatever an unmarked lineage did.  The inactive-lineage audit below
    is that lineage's own hygiene -- it refuses a pin authored off the regime --
    and it must not be read as the thing that protects the tip.

    Every commit, parent, tree, marker, and relevant WP gitlink is read as a
    literal local object under the shared no-lazy-fetch authority environment.
    The whole raw DAG walk is bounded.  A WP move on the ordinary marked line
    permanently selects terminal mode; an ambiguous merge or a minted
    inactive-lineage binding is rejected instead of being interpreted as a valid
    R1 claim.
    """
    require_unmodified_history_view(repo_root, "Trust terminal-policy history")
    root_commit = require_sha(root_commit, "Trust terminal-policy HEAD")
    terminal_wp = require_sha(
        commits["trust-wp"], "Trust terminal-policy current TrustWP binding"
    )
    if (
        not isinstance(TERMINAL_POLICY_HISTORY_LIMIT, int)
        or isinstance(TERMINAL_POLICY_HISTORY_LIMIT, bool)
        or TERMINAL_POLICY_HISTORY_LIMIT < 1
    ):
        fail("terminal-policy raw history walk limit must be a positive integer")

    with RawObjectReader(repo_root, "Trust terminal-policy history") as reader:
        snapshots: dict[
            str, tuple[str, list[str], str, tuple[str, str] | None]
        ] = {}
        marker_oid: str | None = None

        def snapshot(
            commit: str, label: str
        ) -> tuple[str, list[str], str, tuple[str, str] | None]:
            cached = snapshots.get(commit)
            if cached is not None:
                return cached
            tree, parents = parse_raw_commit(reader, commit, label)
            marker_entry = raw_tree_path_entry(
                reader, tree, TERMINAL_POLICY_MARKER_PATH, f"{label} marker"
            )
            if marker_entry is None:
                marker_state = "absent"
            elif marker_oid is not None and marker_entry == ("100644", marker_oid):
                marker_state = "exact"
            else:
                marker_state = "invalid"
            cached = (tree, parents, marker_state, marker_entry)
            snapshots[commit] = cached
            return cached

        head_tree, head_parents = parse_raw_commit(
            reader, root_commit, "Trust terminal-policy HEAD"
        )
        head_marker = raw_tree_path_entry(
            reader,
            head_tree,
            TERMINAL_POLICY_MARKER_PATH,
            "Trust terminal-policy HEAD marker",
        )
        if head_marker is None:
            fail(
                f"Trust terminal-policy HEAD is missing required committed marker "
                f"{TERMINAL_POLICY_MARKER_PATH!r}"
            )
        head_marker_mode, marker_oid = head_marker
        if head_marker_mode != "100644":
            fail(
                f"Trust terminal-policy marker must be a non-executable regular "
                f"blob (mode 100644), not mode {head_marker_mode}"
            )
        marker_raw = reader.read(
            marker_oid, "blob", "Trust terminal-policy HEAD marker"
        )
        if marker_raw != TERMINAL_POLICY_MARKER:
            fail(
                "Trust terminal-policy marker content differs from the exact "
                "committed v1 policy"
            )
        snapshots[root_commit] = (
            head_tree,
            head_parents,
            "exact",
            head_marker,
        )

        # Authenticate the complete ancestry DAG, not only whichever parent a
        # merge happened to publish as first.  The 3c2c11e530 landing is the
        # motivating shape: its first parent predates the policy while its
        # second parent contains the ratified single-parent introduction.
        pending = [root_commit]
        visited: set[str] = set()
        while pending:
            current = pending.pop()
            if current in visited:
                continue
            if len(visited) >= TERMINAL_POLICY_HISTORY_LIMIT:
                fail(
                    "Trust terminal-policy raw DAG walk exceeded its bounded "
                    f"limit of {TERMINAL_POLICY_HISTORY_LIMIT} commits"
                )
            visited.add(current)
            _tree, parents, _state, _entry = snapshot(
                current, "Trust terminal-policy raw DAG history"
            )
            pending.extend(parent for parent in parents if parent not in visited)

        invalid = sorted(
            (commit, snapshots[commit][3])
            for commit in visited
            if snapshots[commit][2] == "invalid"
        )
        if invalid:
            fail(
                "Trust terminal-policy raw DAG contains malformed marker state: "
                f"commit={invalid[0][0]}, entry={invalid[0][1]}"
            )

        introductions: list[str] = []
        for commit in sorted(visited):
            _tree, parents, state, _entry = snapshots[commit]
            parent_states = [snapshots[parent][2] for parent in parents]
            if state == "absent":
                marked_parents = [
                    parent
                    for parent, parent_state in zip(parents, parent_states)
                    if parent_state == "exact"
                ]
                if marked_parents:
                    fail(
                        "Trust terminal-policy marker was deleted on a raw DAG "
                        f"edge: child={commit}, marked_parents={marked_parents}"
                    )
                continue

            marked_parents = [
                parent
                for parent, parent_state in zip(parents, parent_states)
                if parent_state == "exact"
            ]
            if not marked_parents:
                if len(parents) != 1 or parent_states != ["absent"]:
                    fail(
                        "Trust terminal-policy marker introduction must be a raw "
                        f"single-parent commit: commit={commit}, parents={parents}, "
                        f"parent_states={parent_states}"
                    )
                introductions.append(commit)

        if len(introductions) != 1:
            fail(
                "Trust terminal-policy marker must have one unique raw "
                f"single-parent introduction; observed={introductions}"
            )
        activation_commit = introductions[0]
        activation_tree, activation_parents, _state, _entry = snapshots[
            activation_commit
        ]
        activation_parent = activation_parents[0]

        def wp_gitlink(
            commit: str,
            tree: str,
            label: str,
        ) -> str:
            entry = raw_tree_path_entry(reader, tree, WP_ROOT_DELTA_PATH, label)
            if entry is None:
                fail(f"{label} is missing committed TrustWP gitlink")
            mode, oid = entry
            if mode != "160000":
                fail(
                    f"{label} must be a committed gitlink (mode 160000), "
                    f"not mode {mode}"
                )
            return require_sha(oid, f"{label} object id at {commit}")

        current_wp = wp_gitlink(
            root_commit, head_tree, "Trust terminal-policy HEAD TrustWP binding"
        )
        if current_wp != terminal_wp:
            fail(
                "root terminal-mode TrustWP gitlink differs from the current "
                f"repository binding: gitlink={current_wp}, binding={terminal_wp}"
            )

        wp_cache: dict[str, str] = {root_commit: current_wp}

        def commit_wp(commit: str, label: str) -> str:
            cached = wp_cache.get(commit)
            if cached is not None:
                return cached
            tree = snapshots[commit][0]
            value = wp_gitlink(commit, tree, label)
            wp_cache[commit] = value
            return value

        ancestor_cache: dict[str, frozenset[str]] = {}

        def ancestors(start: str) -> frozenset[str]:
            cached = ancestor_cache.get(start)
            if cached is not None:
                return cached
            reachable: set[str] = set()
            todo = [start]
            while todo:
                commit = todo.pop()
                if commit in reachable:
                    continue
                if commit not in snapshots:
                    fail(
                        "Trust terminal-policy raw DAG ancestry escaped the "
                        f"authenticated walk at {commit}"
                    )
                reachable.add(commit)
                todo.extend(snapshots[commit][1])
            result = frozenset(reachable)
            ancestor_cache[start] = result
            return result

        preactivation_ancestors = ancestors(activation_parent)

        def audit_inactive_parent(child: str, inactive_parent: str) -> None:
            """Prove one unmarked merge parent MINTS no TrustWP binding.

            The frontier is where this parent's exclusive ancestry rejoins
            ancestry already present before activation.  The lineage must reach
            it -- an exclusive set that never rejoins is an unauthenticated
            import -- and no exclusive commit may publish a TrustWP gitlink that
            none of its own raw parents already carried.  By induction from the
            frontier, every binding on the branch is one the pre-activation
            history had already published, so the branch cannot introduce a pin
            the regime never saw.  An authored move is refused by that rule
            directly, and so is a move later reverted, because the move commit
            mints on its own.

            THE RULE IS PER-COMMIT, NOT PER-EDGE, and that distinction is the
            whole repair.  A merge inside the exclusive set has parents with
            different bindings whenever an older branch takes a newer main --
            the branch is behind on the pin and the merge adopts the newer one.
            That shape publishes nothing new, yet a rule that made every
            exclusive edge agree read it as a move and refused every push whose
            history contained it (b387a4c0e5, 2026-08-30).  For the same reason
            the frontier is no longer required to be a single commit: a branch
            forked at one pre-activation commit and merged with main at another
            has two frontiers by construction, their bindings legitimately
            differ, and the value was never compared to anything -- only
            authenticated, which is now done for every frontier commit.

            None of this weakens the tip: an inactive lineage cannot reach the
            judged binding at all (see this function's own docstring).
            """
            inactive_ancestors = ancestors(inactive_parent)
            exclusive = inactive_ancestors - preactivation_ancestors
            if not exclusive:
                frontier = {inactive_parent}
            else:
                frontier: set[str] = set()
                for side_child in exclusive:
                    if snapshots[side_child][2] != "absent":
                        fail(
                            "Trust terminal-policy inactive merge lineage carries "
                            f"marker state at {side_child}"
                        )
                    child_wp = commit_wp(
                        side_child,
                        f"Trust terminal-policy inactive child {side_child}",
                    )
                    parent_wps: dict[str, str] = {}
                    for side_parent in snapshots[side_child][1]:
                        if side_parent in preactivation_ancestors:
                            frontier.add(side_parent)
                        elif side_parent not in exclusive:
                            fail(
                                "Trust terminal-policy inactive lineage has an "
                                f"unauthenticated ancestry frontier at {side_parent}"
                            )
                        parent_wps[side_parent] = commit_wp(
                            side_parent,
                            f"Trust terminal-policy inactive parent {side_parent}",
                        )
                    if child_wp not in parent_wps.values():
                        # A parentless exclusive commit lands here too: it
                        # publishes a binding out of nowhere, which is the same
                        # defect with an emptier witness.
                        fail(
                            "Trust terminal-policy inactive merge lineage minted a "
                            "TrustWP gitlink no raw parent published: "
                            f"merge={child}, commit={side_child}, "
                            f"commit_wp={child_wp}, parent_wps={parent_wps}"
                        )
            if not frontier:
                fail(
                    "Trust terminal-policy inactive merge lineage never rejoins "
                    f"pre-activation ancestry: merge={child}, "
                    f"parent={inactive_parent}"
                )
            # Authenticate every frontier binding, including the case where the
            # inactive parent is itself a pre-activation ancestor and
            # `exclusive` is empty.
            for frontier_commit in sorted(frontier):
                commit_wp(
                    frontier_commit,
                    "Trust terminal-policy inactive pre-activation frontier",
                )

        claimed = False
        activation_wp = commit_wp(
            activation_commit, "Trust terminal-policy activation child"
        )
        activation_parent_wp = commit_wp(
            activation_parent, "Trust terminal-policy activation parent"
        )
        if activation_wp != activation_parent_wp:
            claimed = True

        for child in sorted(visited):
            child_tree, parents, state, _entry = snapshots[child]
            if state != "exact" or child == activation_commit:
                continue
            marked_parents = [
                parent for parent in parents if snapshots[parent][2] == "exact"
            ]
            inactive_parents = [
                parent for parent in parents if snapshots[parent][2] == "absent"
            ]
            if not marked_parents:
                fail(
                    "Trust terminal-policy marked commit does not descend through "
                    f"a marked raw parent: commit={child}"
                )
            child_wp = commit_wp(
                child, f"Trust terminal-policy marked child {child}"
            )
            marked_parent_wps = {
                parent: commit_wp(
                    parent, f"Trust terminal-policy marked parent {parent}"
                )
                for parent in marked_parents
            }

            if len(marked_parents) > 1 or inactive_parents:
                mismatched = {
                    parent: parent_wp
                    for parent, parent_wp in marked_parent_wps.items()
                    if parent_wp != child_wp
                }
                if mismatched:
                    fail(
                        "Trust terminal-policy propagation merge did not retain "
                        "every marked-parent TrustWP binding: "
                        f"child={child}, child_wp={child_wp}, mismatched={mismatched}"
                    )
            elif next(iter(marked_parent_wps.values())) != child_wp:
                # An ordinary one-parent marked commit is the only admissible
                # shape for R1.  Remember the move permanently; the exact R1
                # validator will decide whether this commit is that cut.
                claimed = True

            for inactive_parent in inactive_parents:
                audit_inactive_parent(child, inactive_parent)
        return claimed


def committed_submodules(
    repo_root: Path, root_revision: str = "HEAD"
) -> dict[str, tuple[str, str, str]]:
    raw = committed_blob(repo_root, root_revision, ".gitmodules")
    try:
        text = raw.decode("utf-8", "strict")
    except UnicodeDecodeError as error:
        fail(f"committed .gitmodules is not valid UTF-8: {error}")
    parser = configparser.RawConfigParser(strict=True)
    parser.optionxform = str
    try:
        parser.read_string(text)
    except configparser.Error as error:
        fail(f"committed .gitmodules is invalid: {error}")

    declarations: dict[str, tuple[str, str]] = {}
    for section in parser.sections():
        match = re.fullmatch(r'submodule "([^"]+)"', section)
        if match is None:
            fail(f"unexpected committed .gitmodules section {section!r}")
        values = dict(parser.items(section))
        if set(values) != {"path", "url"}:
            fail(f"submodule {section!r} must contain exactly path and url")
        logical_name = match.group(1)
        if logical_name in declarations:
            fail(f"duplicate submodule declaration {logical_name!r}")
        declarations[logical_name] = (values["path"], values["url"])

    expected = {f"first-party/{name}": details for name, details in SUBMODULES.items()}
    if declarations != expected:
        fail(
            "committed .gitmodules differs from exact nine-repository policy: "
            f"missing={sorted(set(expected) - set(declarations))}, "
            f"extra={sorted(set(declarations) - set(expected))}, "
            f"mismatched={sorted(k for k in set(expected) & set(declarations) if expected[k] != declarations[k])}"
        )

    rows: dict[str, tuple[str, str, str]] = {}
    tree = run_git(repo_root, ["ls-tree", "-r", "-z", root_revision])
    gitlinks: dict[str, str] = {}
    for raw_row in tree.split(b"\0"):
        if not raw_row:
            continue
        metadata, separator, raw_path = raw_row.partition(b"\t")
        fields = metadata.split()
        if fields and fields[0] == b"160000":
            if separator != b"\t" or len(fields) != 3 or fields[1] != b"commit":
                fail(f"malformed committed 160000 row {raw_row!r}")
            try:
                path = raw_path.decode("utf-8", "strict")
                commit = fields[2].decode("ascii", "strict")
            except UnicodeDecodeError as error:
                fail(f"malformed committed gitlink row: {error}")
            require_sha(commit, f"gitlink {path}")
            gitlinks[path] = commit
    declared_paths = {path for path, _url in declarations.values()}
    if set(gitlinks) != declared_paths:
        fail(
            "committed 160000 gitlinks differ from exact nine declarations: "
            f"missing={sorted(declared_paths - set(gitlinks))}, "
            f"extra={sorted(set(gitlinks) - declared_paths)}"
        )
    for name, (path, url) in SUBMODULES.items():
        rows[name] = (path, url, gitlinks[path])
    return rows


def validate_nested_submodules(
    repository: str,
    checkout: Path,
    commit: str,
    entries: dict[str, tuple[str, str, str]],
    roots: dict[str, Path],
    symlink_paths: set[Path],
) -> None:
    """Reject nested pins that duplicate the root's nine-repository authority."""
    gitlinks: dict[str, str] = {}
    for path, (mode, object_type, oid) in entries.items():
        if mode != "160000":
            continue
        if object_type != "commit":
            fail(f"{repository} nested gitlink {path} has type {object_type}, not commit")
        require_relative_path(path, f"{repository} nested gitlink path")
        gitlinks[path] = require_sha(oid, f"{repository} nested gitlink {path}")

    if ".gitmodules" not in entries:
        if gitlinks:
            fail(f"{repository} has nested gitlinks without committed .gitmodules")
        return

    raw = committed_blob(checkout, commit, ".gitmodules")
    text = decode_text(raw, f"{repository}:.gitmodules")
    parser = configparser.RawConfigParser(strict=True)
    try:
        parser.read_string(text)
    except configparser.Error as error:
        fail(f"{repository}:.gitmodules is invalid: {error}")
    declarations: dict[str, str] = {}
    for section in parser.sections():
        match = re.fullmatch(r'submodule "([^"]+)"', section, flags=re.IGNORECASE)
        if match is None:
            fail(f"{repository}:.gitmodules has unexpected section {section!r}")
        values = dict(parser.items(section))
        if not isinstance(values.get("path"), str) or not isinstance(values.get("url"), str):
            fail(f"{repository}:.gitmodules section {section!r} requires path and url")
        path = require_relative_path(
            values["path"], f"{repository}:.gitmodules {section}.path"
        )
        if path in declarations:
            fail(f"{repository}:.gitmodules declares duplicate path {path!r}")
        url = values["url"]
        declarations[path] = url

        dependency = first_party_url(url, f"{repository}:.gitmodules {section}.url")
        decoded_url, excessive = repeatedly_unquote(url)
        decoded_url = decoded_url.lower().rstrip("/")
        relative_name = PurePosixPath(decoded_url).name.removesuffix(".git")
        if excessive or dependency is not None or (
            decoded_url.startswith(("./", "../")) and relative_name in SUBMODULES
        ):
            target = dependency if dependency is not None else relative_name or "encoded URL"
            fail(
                f"{repository}:.gitmodules creates unsupported nested first-party "
                f"gitlink authority to {target}"
            )

        mapped = map_dependency_path(
            repository,
            ".gitmodules",
            path,
            roots,
            relative_base=".",
            symlink_paths=symlink_paths,
        )
        if mapped is not None and mapped[0] != repository:
            fail(
                f"{repository}:.gitmodules path {path!r} resolves outside its repository "
                f"into {mapped[0]}"
            )

    if set(declarations) != set(gitlinks):
        fail(
            f"{repository} nested .gitmodules/gitlink paths differ: "
            f"declared_only={sorted(set(declarations) - set(gitlinks))}, "
            f"gitlink_only={sorted(set(gitlinks) - set(declarations))}"
        )


def validate_exclusions(exclusions_value: object) -> list[dict[str, str]]:
    if not isinstance(exclusions_value, list):
        fail("exclusions must be an array")
    exclusions: list[dict[str, str]] = []
    for index, entry in enumerate(exclusions_value):
        label = f"exclusions[{index}]"
        if not isinstance(entry, dict):
            fail(f"{label} must be an object")
        require_exact_keys(entry, {"repository", "path", "reason"}, label)
        repository = require_nonempty_string(entry["repository"], f"{label}.repository")
        if repository not in CONSUMERS:
            fail(f"{label}.repository is unknown")
        reason = require_nonempty_string(entry["reason"], f"{label}.reason")
        if len(reason) < 20:
            fail(f"{label}.reason must be a substantive explanation")
        exclusions.append(
            {
                "repository": repository,
                "path": require_relative_path(entry["path"], f"{label}.path"),
                "reason": reason,
            }
        )
    exclusion_keys = [(row["repository"], row["path"]) for row in exclusions]
    if len(exclusion_keys) != len(set(exclusion_keys)):
        fail("exclusions contains a duplicate repository/path")
    for repository, path in exclusion_keys:
        protected = {"Cargo.toml", "Cargo.lock", ".gitmodules", ".cargo"}
        if repository == "trust":
            protected.update(
                {
                    RECEIPT_PATH,
                    EXTERNAL_RECEIPT_PATH,
                    "scripts/check_dependency_cycle_anchor.py",
                    "scripts/hooks",
                    "scripts/hooks-pin",
                    "scripts/install-git-hooks.sh",
                    "scripts/install-pin-hook.sh",
                }
            )
        if any(
            path == authority
            or path.startswith(authority + "/")
            or authority.startswith(path + "/")
            for authority in protected
        ):
            fail(
                f"exclusion {repository}:{path} overlaps repository-root dependency authority"
            )
        if repository == "ny" and any(
            proof_path == path
            or proof_path.startswith(path + "/")
            or path.startswith(proof_path + "/")
            for proof_path in NY_IDENTITY_PATHS
        ):
            fail(f"NY Clean proof identity path {path!r} may not be excluded")
        for other_repository, other_path in exclusion_keys:
            if (repository, path) != (other_repository, other_path) and repository == other_repository:
                if path.startswith(other_path + "/"):
                    fail(f"exclusions overlap in {repository}: {other_path!r} contains {path!r}")
    return sorted(exclusions, key=lambda row: (row["repository"], row["path"]))


def validate_receipt(value: object) -> dict[str, Any]:
    if not isinstance(value, dict):
        fail("receipt top level must be an object")
    require_exact_keys(
        value,
        {
            "schema",
            "self",
            "repositories",
            "root_bindings",
            "exclusions",
            "surfaces",
            "direct_edges",
            "anchors",
        },
        "receipt",
    )
    if value["schema"] != SCHEMA:
        fail(f"schema must be exactly {SCHEMA!r}")

    self_value = value["self"]
    if not isinstance(self_value, dict):
        fail("self must be an object")
    require_exact_keys(self_value, {"repository", "commit"}, "self")
    if self_value != {"repository": "trust", "commit": SELF_SENTINEL}:
        fail("self must bind trust to the literal CONTAINING_COMMIT sentinel")

    repositories = value["repositories"]
    if not isinstance(repositories, dict):
        fail("repositories must be an object")
    if set(repositories) != set(SUBMODULES):
        fail(
            "repositories must name exactly the nine first-party repositories: "
            f"missing={sorted(set(SUBMODULES) - set(repositories))}, "
            f"extra={sorted(set(repositories) - set(SUBMODULES))}"
        )
    commits: dict[str, str] = {}
    for name, entry in repositories.items():
        if not isinstance(entry, dict):
            fail(f"repositories.{name} must be an object")
        require_exact_keys(entry, {"url", "commit"}, f"repositories.{name}")
        if entry["url"] != SUBMODULES[name][1]:
            fail(f"repositories.{name}.url is not the canonical URL")
        commits[name] = require_sha(entry["commit"], f"repositories.{name}.commit")

    bindings = value["root_bindings"]
    if not isinstance(bindings, list):
        fail("root_bindings must be an array")
    normalized_bindings: list[dict[str, str]] = []
    for index, entry in enumerate(bindings):
        label = f"root_bindings[{index}]"
        if not isinstance(entry, dict):
            fail(f"{label} must be an object")
        require_exact_keys(entry, {"repository", "path", "url", "commit"}, label)
        name = require_nonempty_string(entry["repository"], f"{label}.repository")
        if name not in SUBMODULES:
            fail(f"{label}.repository is not first-party")
        normalized_bindings.append(
            {
                "repository": name,
                "path": require_relative_path(entry["path"], f"{label}.path"),
                "url": require_nonempty_string(entry["url"], f"{label}.url"),
                "commit": require_sha(entry["commit"], f"{label}.commit"),
            }
        )
    if len({row["repository"] for row in normalized_bindings}) != len(normalized_bindings):
        fail("root_bindings contains a duplicate repository")

    exclusions = validate_exclusions(value["exclusions"])

    surfaces_value = value["surfaces"]
    if not isinstance(surfaces_value, list):
        fail("surfaces must be an array")
    surfaces = [validate_surface(row, f"surfaces[{index}]") for index, row in enumerate(surfaces_value)]
    surface_ids = [row["id"] for row in surfaces]
    if len(surface_ids) != len(set(surface_ids)):
        fail("surfaces contains a duplicate id")

    edges_value = value["direct_edges"]
    if not isinstance(edges_value, list):
        fail("direct_edges must be an array")
    edges = [validate_edge(row, f"direct_edges[{index}]") for index, row in enumerate(edges_value)]
    edge_keys = [(row["consumer"], row["dependency"]) for row in edges]
    if len(edge_keys) != len(set(edge_keys)):
        fail("direct_edges contains a split or duplicate consumer/dependency pair")

    anchors_value = value["anchors"]
    if not isinstance(anchors_value, list):
        fail("anchors must be an array")
    anchors = [validate_anchor(row, f"anchors[{index}]") for index, row in enumerate(anchors_value)]
    anchor_keys = [(row["consumer"], row["dependency"]) for row in anchors]
    if len(anchor_keys) != len(set(anchor_keys)):
        fail("anchors contains a duplicate consumer/dependency pair")

    return {
        "repositories": commits,
        "root_bindings": normalized_bindings,
        "exclusions": exclusions,
        "surfaces": surfaces,
        "direct_edges": edges,
        "anchors": anchors,
    }


def validate_wp_root_anchor(value: object, label: str = "wp_trust_anchor") -> dict[str, Any]:
    if not isinstance(value, dict):
        fail(f"{label} must be an object")
    is_v2 = "policy_version" in value
    expected_keys = (
        WP_ROOT_ANCHOR_KEYS | WP_ROOT_ANCHOR_V2_EXTRA_KEYS
        if is_v2
        else WP_ROOT_ANCHOR_KEYS
    )
    require_exact_keys(value, expected_keys, label)
    constants = {
        "authority_repository": "trust-wp",
        "authority_path": WP_DEPENDS_PATH,
        "anchor_repository": "trust",
        "terminal_repository": "trust",
        "only_tree_delta": WP_ROOT_DELTA_PATH,
    }
    for key, expected in constants.items():
        if value[key] != expected:
            fail(f"{label}.{key} must be exactly {expected!r}")
    normalized = {
        **constants,
        "authority_commit": require_sha(
            value["authority_commit"], f"{label}.authority_commit"
        ),
        "anchor_commit": require_sha(value["anchor_commit"], f"{label}.anchor_commit"),
        "terminal_commit": require_sha(
            value["terminal_commit"], f"{label}.terminal_commit"
        ),
        "anchor_gitlink": require_sha(
            value["anchor_gitlink"], f"{label}.anchor_gitlink"
        ),
        "terminal_gitlink": require_sha(
            value["terminal_gitlink"], f"{label}.terminal_gitlink"
        ),
    }
    if normalized["authority_commit"] != normalized["terminal_gitlink"]:
        fail(f"{label} authority commit and terminal gitlink must be identical")
    if normalized["anchor_gitlink"] == normalized["terminal_gitlink"]:
        fail(f"{label} must record a real TrustWP gitlink advance")
    if normalized["anchor_commit"] == normalized["terminal_commit"]:
        fail(f"{label} root anchor and terminal commits must differ")
    if is_v2:
        if value["policy_version"] != "trust.constellation.terminal-policy.v2":
            fail(
                f"{label}.policy_version must be exactly "
                "'trust.constellation.terminal-policy.v2'"
            )
        if value["preservation_floor"] != TERMINAL_POLICY_V2_PRESERVATION_FLOOR:
            fail(
                f"{label}.preservation_floor must equal exact published B "
                f"{TERMINAL_POLICY_V2_PRESERVATION_FLOOR}"
            )
        predecessor = require_sha(
            value["predecessor_commit"], f"{label}.predecessor_commit"
        )
        root_bindings_value = value["root_bindings"]
        if not isinstance(root_bindings_value, dict):
            fail(f"{label}.root_bindings must be an object")
        require_exact_keys(root_bindings_value, set(SUBMODULES), f"{label}.root_bindings")
        root_bindings = {
            name: require_sha(
                root_bindings_value[name], f"{label}.root_bindings.{name}"
            )
            for name in sorted(SUBMODULES)
        }
        if normalized["anchor_gitlink"] != TERMINAL_POLICY_V2_W0:
            fail(
                f"{label}.anchor_gitlink must equal exact W0 "
                f"{TERMINAL_POLICY_V2_W0}"
            )
        if root_bindings["trust-wp"] != TERMINAL_POLICY_V2_W0:
            fail(f"{label}.root_bindings.trust-wp must equal exact W0")
        normalized.update(
            {
                "policy_version": "trust.constellation.terminal-policy.v2",
                "preservation_floor": TERMINAL_POLICY_V2_PRESERVATION_FLOOR,
                "predecessor_commit": predecessor,
                "root_bindings": root_bindings,
            }
        )
    return normalized


def validate_external_receipt(
    value: object, *, require_wp_trust_anchor: bool = False
) -> dict[str, Any]:
    """Validate the untracked v3 evidence shape.

    V3 deliberately carries the concrete Trust commit instead of a
    self-referential sentinel.  It is therefore external evidence and cannot
    be made a tracked blob in the commit it authenticates.
    """
    if not isinstance(value, dict):
        fail("external receipt top level must be an object")
    external_keys = {
        "schema",
        "self",
        "repositories",
        "root_bindings",
        "exclusions",
        "surfaces",
        "direct_edges",
        "anchors",
        "wp_trust_anchor",
    }
    require_exact_keys(value, external_keys, "external receipt")
    if value["schema"] != EXTERNAL_SCHEMA:
        fail(f"external receipt schema must be exactly {EXTERNAL_SCHEMA!r}")
    self_value = value["self"]
    if not isinstance(self_value, dict):
        fail("external receipt self must be an object")
    require_exact_keys(self_value, {"repository", "commit"}, "external receipt self")
    if self_value["repository"] != "trust":
        fail("external receipt self.repository must be exactly 'trust'")
    self_commit = require_sha(self_value["commit"], "external receipt self.commit")

    anchor_value = value["wp_trust_anchor"]
    if anchor_value is None:
        if require_wp_trust_anchor:
            fail("external receipt omits required TrustWP Trust anchor evidence")
        root_anchor = None
    else:
        root_anchor = validate_wp_root_anchor(anchor_value)
        if root_anchor["terminal_commit"] != self_commit:
            fail("wp_trust_anchor terminal commit must equal external receipt self.commit")

    legacy_value = {
        key: item
        for key, item in value.items()
        if key not in {"schema", "self", "wp_trust_anchor"}
    }
    legacy_value.update(
        {
            "schema": SCHEMA,
            "self": {"repository": "trust", "commit": SELF_SENTINEL},
        }
    )
    normalized = validate_receipt(legacy_value)
    if (
        root_anchor is not None
        and root_anchor["terminal_gitlink"] != normalized["repositories"]["trust-wp"]
    ):
        fail(
            "wp_trust_anchor terminal gitlink must equal repositories.trust-wp.commit"
        )
    if root_anchor is not None and root_anchor.get("policy_version") == (
        "trust.constellation.terminal-policy.v2"
    ):
        armed_bindings = root_anchor["root_bindings"]
        assert isinstance(armed_bindings, dict)
        mismatched = {
            name: {
                "armed_r0": armed_bindings[name],
                "terminal_r1": normalized["repositories"][name],
            }
            for name in sorted(set(SUBMODULES) - {"trust-wp"})
            if armed_bindings[name] != normalized["repositories"][name]
        }
        if mismatched:
            fail(
                "wp_trust_anchor v2 armed R0 vector differs from terminal R1 "
                f"for non-TrustWP repositories: {mismatched}"
            )
    normalized.update(
        {
            "self_commit": self_commit,
            "wp_trust_anchor": root_anchor,
        }
    )
    return normalized


def validate_surface(value: object, label: str) -> dict[str, Any]:
    if not isinstance(value, dict):
        fail(f"{label} must be an object")
    require_exact_keys(value, SURFACE_KEYS, label)
    repository = require_nonempty_string(value["repository"], f"{label}.repository")
    dependency = require_nonempty_string(value["dependency"], f"{label}.dependency")
    kind = require_nonempty_string(value["kind"], f"{label}.kind")
    scope = require_nonempty_string(value["scope"], f"{label}.scope")
    if repository not in CONSUMERS or dependency not in SUBMODULES:
        fail(f"{label} names an unknown repository")
    if kind not in SURFACE_KINDS:
        fail(f"{label}.kind is unsupported")
    if scope not in {"canonical", "excluded"}:
        fail(f"{label}.scope must be canonical or excluded")
    optional = value["optional"]
    if optional is not None and not isinstance(optional, bool):
        fail(f"{label}.optional must be boolean or null")
    rev = value["rev"]
    if rev is not None:
        rev = require_sha(rev, f"{label}.rev")
    return {
        "id": require_nonempty_string(value["id"], f"{label}.id"),
        "repository": repository,
        "scope": scope,
        "kind": kind,
        "path": require_relative_path(value["path"], f"{label}.path"),
        "locator": require_nonempty_string(value["locator"], f"{label}.locator"),
        "dependency": dependency,
        "package": require_nonempty_string(value["package"], f"{label}.package"),
        "url": require_optional_string(value["url"], f"{label}.url"),
        "rev": rev,
        "dependency_path": require_optional_string(
            value["dependency_path"], f"{label}.dependency_path"
        ),
        "subdir": require_optional_string(value["subdir"], f"{label}.subdir"),
        "optional": optional,
    }


def validate_edge(value: object, label: str) -> dict[str, Any]:
    if not isinstance(value, dict):
        fail(f"{label} must be an object")
    require_exact_keys(value, {"consumer", "dependency", "commit", "surfaces"}, label)
    consumer = require_nonempty_string(value["consumer"], f"{label}.consumer")
    dependency = require_nonempty_string(value["dependency"], f"{label}.dependency")
    if consumer not in CONSUMERS or dependency not in SUBMODULES or consumer == dependency:
        fail(f"{label} names an invalid cross-repository edge")
    surface_ids = value["surfaces"]
    if not isinstance(surface_ids, list) or not surface_ids:
        fail(f"{label}.surfaces must be a non-empty array")
    if not all(isinstance(item, str) and item for item in surface_ids):
        fail(f"{label}.surfaces must contain non-empty strings")
    if len(surface_ids) != len(set(surface_ids)):
        fail(f"{label}.surfaces contains a duplicate")
    return {
        "consumer": consumer,
        "dependency": dependency,
        "commit": require_sha(value["commit"], f"{label}.commit"),
        "surfaces": sorted(surface_ids),
    }


def validate_anchor(value: object, label: str) -> dict[str, str]:
    if not isinstance(value, dict):
        fail(f"{label} must be an object")
    require_exact_keys(value, {"consumer", "dependency", "commit", "terminal", "reason"}, label)
    consumer = require_nonempty_string(value["consumer"], f"{label}.consumer")
    dependency = require_nonempty_string(value["dependency"], f"{label}.dependency")
    if consumer not in CONSUMERS or dependency not in SUBMODULES or consumer == dependency:
        fail(f"{label} names an invalid cross-repository edge")
    if value["reason"] != GENERATION_CUT_REASON:
        fail(f"{label}.reason must be the exact generation-cut policy text")
    commit = require_sha(value["commit"], f"{label}.commit")
    terminal = require_sha(value["terminal"], f"{label}.terminal")
    if commit == terminal:
        fail(f"{label} may not anchor a terminal edge")
    return {
        "consumer": consumer,
        "dependency": dependency,
        "commit": commit,
        "terminal": terminal,
        "reason": GENERATION_CUT_REASON,
    }


def scope_for(repository: str, path: str, exclusions: list[dict[str, str]]) -> str:
    for exclusion in exclusions:
        prefix = exclusion["path"]
        if exclusion["repository"] == repository and (path == prefix or path.startswith(prefix + "/")):
            return "excluded"
    return "canonical"


def lexical_absolute(path: Path) -> Path:
    return Path(os.path.abspath(os.path.normpath(os.fspath(path))))


def map_dependency_path(
    repository: str,
    manifest_path: str,
    raw_path: str,
    roots: dict[str, Path],
    *,
    relative_base: str | None = None,
    symlink_paths: set[Path] | None = None,
    allow_absolute_external: bool = False,
) -> tuple[str, str] | None:
    source_root = roots[repository]
    base = (
        PurePosixPath(manifest_path).parent
        if relative_base is None
        else PurePosixPath(relative_base)
    )
    authored = PurePosixPath(raw_path)
    if authored.is_absolute():
        if not allow_absolute_external:
            fail(f"{repository}:{manifest_path} path {raw_path!r} must be relative")
        target = lexical_absolute(Path(raw_path))
        if symlink_paths is not None:
            traversed = next(
                (link for link in symlink_paths if target == link or link in target.parents),
                None,
            )
            if traversed is not None:
                fail(
                    f"{repository}:{manifest_path} path {raw_path!r} traverses committed "
                    f"symlink {traversed}"
                )
    else:
        cursor = lexical_absolute(source_root / base)
        for part in authored.parts:
            if part in {"", "."}:
                continue
            cursor = cursor.parent if part == ".." else cursor / part
            if symlink_paths is not None and cursor in symlink_paths:
                fail(
                    f"{repository}:{manifest_path} path {raw_path!r} traverses committed "
                    f"symlink {cursor}"
                )
        target = lexical_absolute(source_root / base / raw_path)
    candidates = sorted(roots.items(), key=lambda item: len(os.fspath(item[1])), reverse=True)
    target_folded = os.fspath(target).casefold()
    for target_repository, root in candidates:
        absolute_root = lexical_absolute(root)
        root_folded = os.fspath(absolute_root).casefold()
        try:
            folded_common = os.path.commonpath([target_folded, root_folded])
            exact_common = Path(os.path.commonpath([target, absolute_root]))
        except ValueError:
            continue
        if folded_common == root_folded and exact_common != absolute_root:
            fail(
                f"{repository}:{manifest_path} path {raw_path!r} targets first-party "
                f"repository {target_repository!r} with noncanonical casing"
            )
    for target_repository, root in candidates:
        absolute_root = lexical_absolute(root)
        try:
            common = Path(os.path.commonpath([target, absolute_root]))
        except ValueError:
            continue
        if common == absolute_root:
            relative = target.relative_to(absolute_root).as_posix()
            return target_repository, relative or "."
    return None


def make_surface(
    *,
    repository: str,
    scope: str,
    kind: str,
    path: str,
    locator: str,
    dependency: str,
    package: str,
    url: str | None,
    rev: str | None,
    dependency_path: str | None,
    subdir: str | None,
    optional: bool | None,
) -> dict[str, Any]:
    surface_id = f"{repository}:{path}:{locator}:{kind}"
    return {
        "id": surface_id,
        "repository": repository,
        "scope": scope,
        "kind": kind,
        "path": path,
        "locator": locator,
        "dependency": dependency,
        "package": package,
        "url": url,
        "rev": rev,
        "dependency_path": dependency_path,
        "subdir": subdir,
        "optional": optional,
    }


def validate_workspace_exclusions(
    repository: str,
    files: list[str],
    root_manifest: dict[str, Any] | None,
    exclusions: list[dict[str, str]],
) -> None:
    if root_manifest is None or not isinstance(root_manifest.get("workspace"), dict):
        return
    workspace = root_manifest["workspace"]
    members = workspace.get("members", [])
    cargo_excludes = workspace.get("exclude", [])
    if not isinstance(members, list) or not all(isinstance(item, str) for item in members):
        fail(f"{repository}:Cargo.toml workspace.members must be an array of strings")
    if not isinstance(cargo_excludes, list) or not all(
        isinstance(item, str) for item in cargo_excludes
    ):
        fail(f"{repository}:Cargo.toml workspace.exclude must be an array of strings")

    def manifest_pattern(pattern: str) -> str:
        normalized = pattern.rstrip("/")
        return normalized if normalized.endswith("Cargo.toml") else normalized + "/Cargo.toml"

    member_manifests = {
        path
        for path in files
        if path.endswith("Cargo.toml")
        and any(fnmatch.fnmatchcase(path, manifest_pattern(pattern)) for pattern in members)
        and not any(fnmatch.fnmatchcase(path, manifest_pattern(pattern)) for pattern in cargo_excludes)
    }
    for exclusion in exclusions:
        if exclusion["repository"] != repository:
            continue
        hidden_members = sorted(
            path
            for path in member_manifests
            if path == exclusion["path"] or path.startswith(exclusion["path"] + "/")
        )
        if hidden_members:
            fail(
                f"exclusion {repository}:{exclusion['path']} hides Cargo workspace members "
                f"{hidden_members[:5]}"
            )


def scan_cargo_manifest(
    repository: str,
    path: str,
    data: dict[str, Any],
    scope: str,
    roots: dict[str, Path],
    *,
    config_only: bool = False,
    relative_base: str | None = None,
    symlink_paths: set[Path] | None = None,
) -> tuple[list[dict[str, Any]], list[tuple[str, str, str, str]]]:
    surfaces: list[dict[str, Any]] = []
    path_links: list[tuple[str, str, str, str]] = []

    def dependency(
        alias: str,
        spec: object,
        locator: str,
        relation: str,
        patch_source: str | None = None,
    ) -> None:
        if not isinstance(spec, dict):
            return
        git_value = spec.get("git")
        path_value = spec.get("path")
        git_repository = first_party_url(git_value, f"{repository}:{path}:{locator}.git")
        source_repository = (
            None
            if patch_source is None
            or re.fullmatch(r"[A-Za-z0-9_-]+", patch_source) is not None
            else first_party_url(
                patch_source,
                f"{repository}:{path}:{locator}.patch-source",
                allow_alias=True,
            )
        )
        mapped: tuple[str, str] | None = None
        if path_value is not None:
            if not isinstance(path_value, str):
                fail(f"{repository}:{path}:{locator}.path must be a string")
            mapped = map_dependency_path(
                repository,
                path,
                path_value,
                roots,
                relative_base=relative_base,
                symlink_paths=symlink_paths,
            )
            if mapped is not None:
                path_links.append((repository, path, mapped[0], mapped[1]))

        mapped_repository = mapped[0] if mapped is not None else None
        if mapped_repository == "trust" and repository != "trust":
            fail(
                f"{repository}:{path}:{locator} creates a subrepository-to-root Cargo path edge"
            )
        candidates = {name for name in (git_repository, source_repository, mapped_repository) if name in SUBMODULES}
        if not candidates:
            return
        if len(candidates) != 1:
            fail(
                f"{repository}:{path}:{locator} splits one dependency across first-party repositories {sorted(candidates)}"
            )
        dependency_repository = next(iter(candidates))
        if git_value is not None and path_value is not None:
            fail(f"{repository}:{path}:{locator} combines git and path authority")
        if mapped_repository == repository and source_repository is None and git_repository is None:
            return  # ordinary intra-repository path dependency
        if source_repository is not None and mapped_repository not in {None, source_repository}:
            fail(f"{repository}:{path}:{locator} patch source and target repositories differ")

        package = spec.get("package", alias)
        if not isinstance(package, str) or not package:
            fail(f"{repository}:{path}:{locator}.package must be a non-empty string")
        rev: str | None = None
        url: str | None = None
        normalized_path: str | None = None
        if git_value is not None:
            if git_repository is None:
                fail(f"{repository}:{path}:{locator} has an unsupported first-party git target")
            url = SUBMODULES[git_repository][1]
            rev = require_sha(spec.get("rev"), f"{repository}:{path}:{locator}.rev")
            kind = f"cargo-{relation}-git" if relation != "direct" else "cargo-git"
        elif path_value is not None:
            normalized_path = posixpath.normpath(path_value)
            # Cargo source identities with/without .git and via SSH are distinct.
            # Root deliberately patches each identity, so inventory the authored
            # patch key verbatim while keeping direct Git/Lake declarations strict.
            url = patch_source if source_repository is not None else None
            kind = f"cargo-{relation}-path" if relation != "direct" else "cargo-path"
        else:
            # A patch source URL without a git/path target is not reproducible.
            if source_repository is not None:
                fail(f"{repository}:{path}:{locator} first-party patch has no git/path target")
            return
        optional = spec.get("optional", False)
        if not isinstance(optional, bool):
            fail(f"{repository}:{path}:{locator}.optional must be boolean")
        surfaces.append(
            make_surface(
                repository=repository,
                scope=scope,
                kind=kind,
                path=path,
                locator=locator,
                dependency=dependency_repository,
                package=package,
                url=url,
                rev=rev,
                dependency_path=normalized_path,
                subdir=None,
                optional=optional,
            )
        )

    if not config_only:
        direct_sections: list[tuple[str, object]] = []
        for section in ("dependencies", "dev-dependencies", "build-dependencies"):
            direct_sections.append((f"/{section}", data.get(section)))
        workspace = data.get("workspace")
        if isinstance(workspace, dict):
            for section in ("dependencies", "dev-dependencies", "build-dependencies"):
                direct_sections.append((f"/workspace/{section}", workspace.get(section)))
        target = data.get("target")
        if isinstance(target, dict):
            for target_name, target_table in target.items():
                if not isinstance(target_table, dict):
                    continue
                for section in ("dependencies", "dev-dependencies", "build-dependencies"):
                    direct_sections.append(
                        (f"/target/{target_name}/{section}", target_table.get(section))
                    )
        for base, table in direct_sections:
            if not isinstance(table, dict):
                continue
            for alias, spec in table.items():
                dependency(str(alias), spec, f"{base}/{alias}", "direct")

    patches = data.get("patch")
    if isinstance(patches, dict):
        for source, table in patches.items():
            if not isinstance(table, dict):
                continue
            for alias, spec in table.items():
                dependency(
                    str(alias),
                    spec,
                    f"/patch/{source}/{alias}",
                    "patch",
                    str(source),
                )
    replacements = data.get("replace")
    if config_only and replacements is not None:
        fail(f"{repository}:{path} may not declare Cargo [replace]; inline a supported [patch]")
    if not config_only and isinstance(replacements, dict):
        for alias, spec in replacements.items():
            dependency(str(alias).split(":", 1)[0], spec, f"/replace/{alias}", "replace")
    return surfaces, path_links


def scan_cargo_config(
    repository: str,
    path: str,
    data: dict[str, Any],
    scope: str,
    roots: dict[str, Path],
    symlink_paths: set[Path],
) -> tuple[list[dict[str, Any]], list[tuple[str, str, str, str]]]:
    config_path = PurePosixPath(path)
    # Cargo resolves relative config paths from the parent of the containing
    # .cargo directory, not from .cargo itself.
    relative_base = config_path.parent.parent.as_posix()
    if "include" in data:
        fail(f"{repository}:{path} Cargo config include is unsupported; inline [patch]")
    if "paths" in data:
        fail(f"{repository}:{path} Cargo config paths overrides are unsupported; use [patch]")

    sources = data.get("source")
    if sources is not None and not isinstance(sources, dict):
        fail(f"{repository}:{path} Cargo config [source] must be a table")
    if isinstance(sources, dict):
        for source_name, source in sources.items():
            if not isinstance(source, dict):
                fail(f"{repository}:{path} source.{source_name} must be a table")
            for key in ("git", "registry"):
                if key not in source:
                    continue
                value = source[key]
                if not isinstance(value, str):
                    fail(f"{repository}:{path} source.{source_name}.{key} must be a string")
                dependency = first_party_url(
                    value,
                    f"{repository}:{path}:source.{source_name}.{key}",
                )
                if dependency is not None:
                    fail(
                        f"{repository}:{path} first-party Cargo [source] redirect to "
                        f"{dependency} is unsupported; use [patch]"
                    )
            for key in ("directory", "local-registry"):
                if key not in source:
                    continue
                value = source[key]
                if not isinstance(value, str):
                    fail(f"{repository}:{path} source.{source_name}.{key} must be a string")
                mapped = map_dependency_path(
                    repository,
                    path,
                    value,
                    roots,
                    relative_base=relative_base,
                    symlink_paths=symlink_paths,
                )
                if mapped is not None and (
                    mapped[0] in SUBMODULES or (mapped[0] == "trust" and repository != "trust")
                ):
                    fail(
                        f"{repository}:{path} first-party Cargo [source] {key} redirect "
                        f"to {mapped[0]} is unsupported; use [patch]"
                    )

    return scan_cargo_manifest(
        repository,
        path,
        data,
        scope,
        roots,
        config_only=True,
        relative_base=relative_base,
        symlink_paths=symlink_paths,
    )


def scan_cargo_lock(
    repository: str,
    path: str,
    data: dict[str, Any],
    scope: str,
) -> list[dict[str, Any]]:
    packages = data.get("package", [])
    if not isinstance(packages, list):
        fail(f"{repository}:{path}: package must be an array")
    surfaces: list[dict[str, Any]] = []
    for index, package in enumerate(packages):
        if not isinstance(package, dict):
            fail(f"{repository}:{path}:package[{index}] must be a table")
        source = package.get("source")
        if not isinstance(source, str) or not source.startswith("git+"):
            continue
        payload = source[4:]
        parsed = urlsplit(payload)
        base_url = urlunsplit((parsed.scheme, parsed.netloc, parsed.path, "", ""))
        dependency = first_party_url(
            base_url, f"{repository}:{path}:package[{index}].source"
        )
        if dependency is None:
            continue
        if base_url != SUBMODULES[dependency][1]:
            fail(f"{repository}:{path}:package[{index}] lock URL is not canonical")
        query = parse_qs(parsed.query, keep_blank_values=True)
        if set(query) != {"rev"} or len(query["rev"]) != 1:
            fail(f"{repository}:{path}:package[{index}] lock source must contain only one rev query")
        query_rev = require_sha(query["rev"][0], f"{repository}:{path}:package[{index}] query rev")
        fragment_rev = require_sha(parsed.fragment, f"{repository}:{path}:package[{index}] fragment rev")
        if query_rev != fragment_rev:
            fail(f"{repository}:{path}:package[{index}] lock query/fragment revisions split")
        name = require_nonempty_string(package.get("name"), f"{repository}:{path}:package[{index}].name")
        version = require_nonempty_string(
            package.get("version"), f"{repository}:{path}:package[{index}].version"
        )
        surfaces.append(
            make_surface(
                repository=repository,
                scope=scope,
                kind="cargo-lock",
                path=path,
                locator=f"/package/{index}:{name}@{version}",
                dependency=dependency,
                package=name,
                url=SUBMODULES[dependency][1],
                rev=query_rev,
                dependency_path=None,
                subdir=None,
                optional=None,
            )
        )
    return surfaces


def scan_lakefile(
    repository: str,
    path: str,
    data: dict[str, Any],
    scope: str,
    roots: dict[str, Path],
    symlink_paths: set[Path],
) -> tuple[list[dict[str, Any]], list[tuple[str, str, str, str]]]:
    requirements = data.get("require", [])
    if not isinstance(requirements, list):
        fail(f"{repository}:{path}: require must be an array")
    surfaces: list[dict[str, Any]] = []
    path_links: list[tuple[str, str, str, str]] = []
    for index, requirement in enumerate(requirements):
        if not isinstance(requirement, dict):
            fail(f"{repository}:{path}:require[{index}] must be a table")
        git_value = requirement.get("git")
        path_value = requirement.get("path")
        dependency = first_party_url(git_value, f"{repository}:{path}:require[{index}].git")
        mapped: tuple[str, str] | None = None
        if path_value is not None:
            if not isinstance(path_value, str):
                fail(f"{repository}:{path}:require[{index}].path must be a string")
            mapped = map_dependency_path(
                repository,
                path,
                path_value,
                roots,
                symlink_paths=symlink_paths,
                allow_absolute_external=True,
            )
            if mapped is not None:
                path_links.append((repository, path, mapped[0], mapped[1]))
        mapped_repository = mapped[0] if mapped is not None else None
        if mapped_repository == "trust" and repository != "trust":
            fail(f"{repository}:{path}:require[{index}] creates a subrepository-to-root Lake path edge")
        if git_value is not None and path_value is not None:
            fail(f"{repository}:{path}:require[{index}] combines git and path authority")
        candidates = {
            candidate
            for candidate in (dependency, mapped_repository)
            if candidate in SUBMODULES
        }
        if not candidates:
            continue
        if len(candidates) != 1:
            fail(
                f"{repository}:{path}:require[{index}] splits one Lake dependency across "
                f"first-party repositories {sorted(candidates)}"
            )
        dependency = next(iter(candidates))
        if mapped_repository == repository and git_value is None:
            continue
        package = require_nonempty_string(
            requirement.get("name"), f"{repository}:{path}:require[{index}].name"
        )
        rev = (
            require_sha(
                requirement.get("rev"), f"{repository}:{path}:require[{index}].rev"
            )
            if git_value is not None
            else None
        )
        subdir = requirement.get("subDir")
        if subdir is not None:
            subdir = require_relative_path(subdir, f"{repository}:{path}:require[{index}].subDir")
        surfaces.append(
            make_surface(
                repository=repository,
                scope=scope,
                kind="lake-require" if git_value is not None else "lake-path",
                path=path,
                locator=f"/require/{index}:{package}",
                dependency=dependency,
                package=package,
                url=SUBMODULES[dependency][1] if git_value is not None else None,
                rev=rev,
                dependency_path=(
                    None if path_value is None else posixpath.normpath(path_value)
                ),
                subdir=subdir,
                optional=None,
            )
        )
    return surfaces, path_links


def scan_lake_manifest(
    repository: str,
    path: str,
    value: object,
    scope: str,
    roots: dict[str, Path],
    symlink_paths: set[Path],
) -> tuple[list[dict[str, Any]], list[tuple[str, str, str, str]]]:
    if not isinstance(value, dict) or not isinstance(value.get("packages"), list):
        fail(f"{repository}:{path} must contain a packages array")
    surfaces: list[dict[str, Any]] = []
    path_links: list[tuple[str, str, str, str]] = []
    for index, package in enumerate(value["packages"]):
        if not isinstance(package, dict):
            fail(f"{repository}:{path}:packages[{index}] must be an object")
        package_type = package.get("type")
        path_keys = [key for key in ("path", "dir") if key in package]
        is_path_package = package_type == "path" or bool(path_keys)
        dependency: str | None = None
        dependency_path: str | None = None
        if is_path_package:
            if package_type not in {None, "path"}:
                fail(f"{repository}:{path}:packages[{index}] mixes type {package_type!r} with path/dir")
            candidate_values: list[tuple[str, str]] = []
            for key in ("path", "dir", "url"):
                raw_value = package.get(key)
                if raw_value is None:
                    continue
                if not isinstance(raw_value, str):
                    fail(f"{repository}:{path}:packages[{index}].{key} must be a string")
                candidate_values.append((key, raw_value))
            if not candidate_values:
                fail(f"{repository}:{path}:packages[{index}] path package has no path/dir/url")
            mapped_rows: list[tuple[str, str, str]] = []
            for key, raw_value in candidate_values:
                mapped = map_dependency_path(
                    repository,
                    path,
                    raw_value,
                    roots,
                    symlink_paths=symlink_paths,
                    allow_absolute_external=True,
                )
                if mapped is not None:
                    path_links.append((repository, path, mapped[0], mapped[1]))
                    if mapped[0] in SUBMODULES:
                        mapped_rows.append((mapped[0], key, raw_value))
                    elif mapped[0] == "trust" and repository != "trust":
                        fail(
                            f"{repository}:{path}:packages[{index}] creates a "
                            "subrepository-to-root Lake path edge"
                        )
            mapped_repositories = {row[0] for row in mapped_rows}
            if not mapped_repositories:
                continue
            if len(mapped_repositories) != 1:
                fail(
                    f"{repository}:{path}:packages[{index}] path/dir values split across "
                    f"first-party repositories {sorted(mapped_repositories)}"
                )
            dependency = next(iter(mapped_repositories))
            if dependency == repository:
                continue
            dependency_path = posixpath.normpath(mapped_rows[0][2])
        else:
            dependency = first_party_url(
                package.get("url"), f"{repository}:{path}:packages[{index}].url"
            )
            if dependency is None:
                continue
        name = require_nonempty_string(
            package.get("name"), f"{repository}:{path}:packages[{index}].name"
        )
        rev: str | None = None
        if not is_path_package:
            rev = require_sha(package.get("rev"), f"{repository}:{path}:packages[{index}].rev")
            input_rev = require_sha(
                package.get("inputRev"), f"{repository}:{path}:packages[{index}].inputRev"
            )
            if rev != input_rev:
                fail(f"{repository}:{path}:packages[{index}] rev/inputRev split")
        subdir = package.get("subDir")
        if subdir is not None:
            subdir = require_relative_path(subdir, f"{repository}:{path}:packages[{index}].subDir")
        surfaces.append(
            make_surface(
                repository=repository,
                scope=scope,
                kind="lake-path-lock" if is_path_package else "lake-lock",
                path=path,
                locator=f"/packages/{index}:{name}",
                dependency=dependency,
                package=name,
                url=None if is_path_package else SUBMODULES[dependency][1],
                rev=rev,
                dependency_path=dependency_path,
                subdir=subdir,
                optional=None,
            )
        )
    return surfaces, path_links


def scan_proof_identity(
    repository: str,
    path: str,
    value: object,
    scope: str,
) -> list[dict[str, Any]]:
    if not isinstance(value, dict):
        fail(f"{repository}:{path} top level must be an object")
    corpus = value.get("corpus")
    if not isinstance(corpus, dict) or corpus.get("source") != "lake-git-dependency":
        return []
    dependency = first_party_url(corpus.get("git"), f"{repository}:{path}:corpus.git")
    if dependency is None:
        return []
    package = require_nonempty_string(corpus.get("package"), f"{repository}:{path}:corpus.package")
    rev = require_sha(corpus.get("rev"), f"{repository}:{path}:corpus.rev")
    subdir = corpus.get("subDir")
    if subdir is not None:
        subdir = require_relative_path(subdir, f"{repository}:{path}:corpus.subDir")
    return [
        make_surface(
            repository=repository,
            scope=scope,
            kind="proof-identity",
            path=path,
            locator="/corpus",
            dependency=dependency,
            package=package,
            url=SUBMODULES[dependency][1],
            rev=rev,
            dependency_path=None,
            subdir=subdir,
            optional=None,
        )
    ]


def exactly_one_match(pattern: str, text: str, label: str, *, flags: int = 0) -> tuple[str, ...]:
    matches = re.findall(pattern, text, flags)
    if len(matches) != 1:
        fail(f"{label} must contain exactly one authoritative identity row; observed {len(matches)}")
    match = matches[0]
    return (match,) if isinstance(match, str) else tuple(match)


def ny_proof_surface(
    *,
    path: str,
    locator: str,
    scope: str,
    rev: str,
    url: str | None,
    subdir: str | None,
) -> dict[str, Any]:
    return make_surface(
        repository="ny",
        scope=scope,
        kind="proof-identity",
        path=path,
        locator=locator,
        dependency="clean",
        package="crownproof",
        url=url,
        rev=rev,
        dependency_path=None,
        subdir=subdir,
        optional=None,
    )


def scan_ny_spec(path: str, raw: bytes, scope: str) -> list[dict[str, Any]]:
    text = decode_text(raw, f"ny:{path}")
    (rev_value,) = exactly_one_match(
        r"uses\s+private\s+Clean\s+commit\s+`([^`]+)`\s+with",
        text,
        f"ny:{path}:private Clean commit",
        flags=re.MULTILINE,
    )
    (subdir_value,) = exactly_one_match(
        r"`subDir\s*=\s*\"([^\"]+)\"`",
        text,
        f"ny:{path}:Clean subDir",
    )
    return [
        ny_proof_surface(
            path=path,
            locator="/private-clean-commit",
            scope=scope,
            rev=require_sha(rev_value, f"ny:{path}:Clean rev"),
            url=None,
            subdir=require_relative_path(subdir_value, f"ny:{path}:Clean subDir"),
        )
    ]


def scan_ny_proof_readme(path: str, raw: bytes, scope: str) -> list[dict[str, Any]]:
    text = decode_text(raw, f"ny:{path}")
    (rev_value,) = exactly_one_match(
        r"Clean's\s+`Crownproof`\s+library[\s\S]*?at\s+exact\s+commit\s+`([^`]+)`",
        text,
        f"ny:{path}:Clean exact commit",
    )
    return [
        ny_proof_surface(
            path=path,
            locator="/clean-exact-commit",
            scope=scope,
            rev=require_sha(rev_value, f"ny:{path}:Clean rev"),
            url=None,
            subdir=None,
        )
    ]


def scan_ny_provenance(path: str, raw: bytes, scope: str) -> list[dict[str, Any]]:
    text = decode_text(raw, f"ny:{path}")
    (url_value,) = exactly_one_match(
        r"^repository:\s*(\S+)\s*$",
        text,
        f"ny:{path}:repository",
        flags=re.MULTILINE,
    )
    (rev_value,) = exactly_one_match(
        r"^revision:\s*(\S+)\s*$",
        text,
        f"ny:{path}:revision",
        flags=re.MULTILINE,
    )
    (subdir_value,) = exactly_one_match(
        r"^subDir:\s*(\S+)\s*$",
        text,
        f"ny:{path}:subDir",
        flags=re.MULTILINE,
    )
    dependency = first_party_url(url_value, f"ny:{path}:repository")
    if dependency != "clean":
        fail(f"ny:{path}:repository must be the canonical Clean URL")
    return [
        ny_proof_surface(
            path=path,
            locator="/provenance/clean",
            scope=scope,
            rev=require_sha(rev_value, f"ny:{path}:revision"),
            url=SUBMODULES["clean"][1],
            subdir=require_relative_path(subdir_value, f"ny:{path}:subDir"),
        )
    ]


def scan_ny_cite_source(path: str, raw: bytes, scope: str) -> list[dict[str, Any]]:
    text = decode_text(raw, f"ny:{path}")

    def constant(name: str) -> str:
        (value,) = exactly_one_match(
            rf'^pub\s+const\s+{re.escape(name)}:\s*&str\s*=\s*"([^"\n]*)";\s*$',
            text,
            f"ny:{path}:{name}",
            flags=re.MULTILINE,
        )
        return value

    package = constant("CLEAN_LAKE_PACKAGE")
    if package != "crownproof":
        fail(f"ny:{path}:CLEAN_LAKE_PACKAGE must be exactly 'crownproof'")
    url_value = constant("CLEAN_GIT_URL")
    dependency = first_party_url(url_value, f"ny:{path}:CLEAN_GIT_URL")
    if dependency != "clean":
        fail(f"ny:{path}:CLEAN_GIT_URL must be the canonical Clean URL")
    rev = require_sha(constant("CLEAN_GIT_REV"), f"ny:{path}:CLEAN_GIT_REV")
    subdir = require_relative_path(
        constant("CLEAN_LAKE_SUBDIR"), f"ny:{path}:CLEAN_LAKE_SUBDIR"
    )
    return [
        ny_proof_surface(
            path=path,
            locator="/const/CLEAN_GIT_IDENTITY",
            scope=scope,
            rev=rev,
            url=SUBMODULES["clean"][1],
            subdir=subdir,
        )
    ]


def validate_ny_identity_bundle(surfaces: list[dict[str, Any]]) -> None:
    rows = [
        row
        for row in surfaces
        if row["repository"] == "ny"
        and row["dependency"] == "clean"
        and row["kind"] in {"proof-identity", "lake-require", "lake-lock"}
    ]
    paths = {row["path"] for row in rows}
    if len(rows) != 7 or paths != NY_IDENTITY_PATHS:
        fail(
            "NY Clean proof identity must contain exactly seven committed surfaces: "
            f"missing={sorted(NY_IDENTITY_PATHS - paths)}, "
            f"extra={sorted(paths - NY_IDENTITY_PATHS)}, rows={len(rows)}"
        )
    revisions = {row["rev"] for row in rows}
    if len(revisions) != 1:
        fail(f"NY Clean proof identity revisions split across seven surfaces: {sorted(revisions)}")
    by_path = {row["path"]: row for row in rows}
    canonical_url_paths = NY_IDENTITY_PATHS - {
        "crates/ny-cert/SPEC.md",
        "crates/ny-cert/proofs/README.md",
    }
    subdir_paths = NY_IDENTITY_PATHS - {"crates/ny-cert/proofs/README.md"}
    for path, row in by_path.items():
        expected_url = SUBMODULES["clean"][1] if path in canonical_url_paths else None
        expected_subdir = "crown-proofs/lean" if path in subdir_paths else None
        if row["package"] != "crownproof" or row["url"] != expected_url or row["subdir"] != expected_subdir:
            fail(f"NY Clean proof identity surface {path} has malformed package/URL/subDir")


def is_committed_authority_path(repository: str, path: str) -> bool:
    pure = PurePosixPath(path)
    if path == ".gitmodules" or path.endswith(("Cargo.toml", "Cargo.lock")):
        return True
    if pure.name in {"config", "config.toml"} and pure.parent.name == ".cargo":
        return True
    if path.endswith(
        ("lakefile.toml", "lakefile.lean", "lake-manifest.json", "cite-map.json")
    ):
        return True
    if repository == "ny" and path in NY_IDENTITY_PATHS:
        return True
    if repository != "trust":
        return False
    return path in {
        RECEIPT_PATH,
        EXTERNAL_RECEIPT_PATH,
        "scripts/check_dependency_cycle_anchor.py",
        "scripts/install-git-hooks.sh",
        "scripts/install-pin-hook.sh",
    } or path.startswith(("scripts/hooks/", "scripts/hooks-pin/"))


def scan_constellation(
    repo_root: Path,
    root_commit: str,
    commits: dict[str, str],
    exclusions: list[dict[str, str]],
) -> list[dict[str, Any]]:
    roots = {"trust": repo_root}
    for name, (path, _url) in SUBMODULES.items():
        checkout = repo_root / path
        if not checkout.is_dir():
            fail(f"{path} is not checked out")
        roots[name] = checkout
    scan_commits = {"trust": root_commit, **commits}
    surfaces: list[dict[str, Any]] = []
    path_links: list[tuple[str, str, str, str]] = []
    entries_by_repository: dict[str, dict[str, tuple[str, str, str]]] = {}
    symlink_paths: set[Path] = set()
    for repository in sorted(scan_commits):
        checkout = roots[repository]
        commit = scan_commits[repository]
        require_unmodified_history_view(checkout, repository)
        object_type = run_git(checkout, ["cat-file", "-t", commit]).decode("ascii", "strict").strip()
        expected_types = {"commit", "tree"} if repository == "trust" else {"commit"}
        if object_type not in expected_types:
            fail(f"{repository} terminal {commit} is not a committed tree/commit object")
        entries = committed_tree_entries(checkout, commit)
        entries_by_repository[repository] = entries
        for path, (mode, entry_type, _oid) in entries.items():
            if mode == "120000":
                symlink_paths.add(lexical_absolute(checkout / path))
            if is_committed_authority_path(repository, path) and (
                entry_type != "blob" or mode not in {"100644", "100755"}
            ):
                fail(
                    f"{repository}:{path} dependency authority must be a regular committed "
                    f"blob, not mode {mode} type {entry_type}"
                )

    for repository in sorted(scan_commits):
        checkout = roots[repository]
        commit = scan_commits[repository]
        entries = entries_by_repository[repository]
        files = sorted(entries)
        if repository != "trust":
            validate_nested_submodules(
                repository,
                checkout,
                commit,
                entries,
                roots,
                symlink_paths,
            )
        root_manifest: dict[str, Any] | None = None
        if "Cargo.toml" in files:
            raw_root_manifest = committed_blob(checkout, commit, "Cargo.toml")
            try:
                root_manifest = parse_toml(raw_root_manifest, f"{repository}:Cargo.toml")
            except AnchorError:
                if might_reference_first_party(raw_root_manifest):
                    raise
        validate_workspace_exclusions(repository, files, root_manifest, exclusions)
        for path in files:
            scope = scope_for(repository, path, exclusions)
            # An exclusion is an explicit, substantive receipt row for a
            # non-workspace fixture/spike.  Do not interpret authority syntax
            # inside it: these trees intentionally contain historical, local,
            # or symlinked locators.  Canonical manifests are still forbidden
            # from reaching an excluded path (checked through `path_links`
            # below), and workspace members cannot be excluded.
            if scope == "excluded":
                continue
            if repository == "ny" and path == "crates/ny-cert/SPEC.md":
                surfaces.extend(scan_ny_spec(path, committed_blob(checkout, commit, path), scope))
            elif repository == "ny" and path == "crates/ny-cert/proofs/README.md":
                surfaces.extend(
                    scan_ny_proof_readme(path, committed_blob(checkout, commit, path), scope)
                )
            elif repository == "ny" and path == "crates/ny-cert/proofs/lean/PROVENANCE.md":
                surfaces.extend(
                    scan_ny_provenance(path, committed_blob(checkout, commit, path), scope)
                )
            elif repository == "ny" and path == "crates/ny-cert/src/cite_check.rs":
                surfaces.extend(
                    scan_ny_cite_source(path, committed_blob(checkout, commit, path), scope)
                )
            elif (
                PurePosixPath(path).name in {"config", "config.toml"}
                and PurePosixPath(path).parent.name == ".cargo"
            ):
                found, links = scan_cargo_config(
                    repository,
                    path,
                    parse_toml(
                        committed_blob(checkout, commit, path),
                        f"{repository}:{path}",
                    ),
                    scope,
                    roots,
                    symlink_paths,
                )
                surfaces.extend(found)
                path_links.extend(links)
            elif path.endswith("Cargo.toml"):
                raw = committed_blob(checkout, commit, path)
                try:
                    manifest = parse_toml(raw, f"{repository}:{path}")
                except AnchorError:
                    if might_reference_first_party(raw):
                        raise
                    continue  # unrelated compiler/test fixture with intentionally invalid TOML
                found, links = scan_cargo_manifest(
                    repository,
                    path,
                    manifest,
                    scope,
                    roots,
                    symlink_paths=symlink_paths,
                )
                surfaces.extend(found)
                path_links.extend(links)
            elif path.endswith("Cargo.lock"):
                # Lock authority is workspace-relative.  Scanning every lock
                # in the Rust/compiler fixture corpus conflates unrelated
                # workspaces and produces thousands of false split revisions.
                # The exact nearest lock for each observed first-party Git
                # manifest is derived below after all manifests are known.
                continue
            elif path.endswith("lakefile.toml"):
                found, links = scan_lakefile(
                    repository,
                    path,
                    parse_toml(
                        committed_blob(checkout, commit, path), f"{repository}:{path}"
                    ),
                    scope,
                    roots,
                    symlink_paths,
                )
                surfaces.extend(found)
                path_links.extend(links)
            elif path.endswith("lake-manifest.json"):
                found, links = scan_lake_manifest(
                    repository,
                    path,
                    parse_json(
                        committed_blob(checkout, commit, path), f"{repository}:{path}"
                    ),
                    scope,
                    roots,
                    symlink_paths,
                )
                surfaces.extend(found)
                path_links.extend(links)
            elif path.endswith("cite-map.json"):
                surfaces.extend(
                    scan_proof_identity(
                        repository,
                        path,
                        parse_json(committed_blob(checkout, commit, path), f"{repository}:{path}"),
                        scope,
                    )
                )
            elif path.endswith("lakefile.lean"):
                raw = committed_blob(checkout, commit, path)
                text = decode_text(raw, f"{repository}:{path}")
                decoded, excessive = repeatedly_unquote(text.lower())
                local_locator = re.search(
                    r"\bfrom\s+(?:git\s+)?[\"']?(?:file:|\.{1,2}/|/)", decoded
                )
                if excessive or local_locator is not None or might_reference_first_party(raw):
                    fail(f"{repository}:{path} contains an unsupported first-party Lake declaration")

    scanned_locks: set[tuple[str, str]] = set()
    for manifest_surface in list(surfaces):
        if manifest_surface["scope"] != "canonical" or manifest_surface["kind"] != "cargo-git":
            continue
        repository = manifest_surface["repository"]
        manifest_dir = cargo_authority_dir(manifest_surface["path"])
        candidates = [
            path
            for path in entries_by_repository[repository]
            if path.endswith("Cargo.lock")
            and scope_for(repository, path, exclusions) == "canonical"
            and path_is_within(manifest_dir, PurePosixPath(path).parent)
        ]
        if not candidates:
            continue
        depth = max(len(PurePosixPath(path).parent.parts) for path in candidates)
        nearest = sorted(
            path for path in candidates if len(PurePosixPath(path).parent.parts) == depth
        )
        if len(nearest) != 1:
            fail(
                f"{repository}:{manifest_surface['path']} has ambiguous nearest Cargo.lock authority {nearest}"
            )
        lock_path = nearest[0]
        lock_key = (repository, lock_path)
        if lock_key in scanned_locks:
            continue
        scanned_locks.add(lock_key)
        checkout = roots[repository]
        commit = scan_commits[repository]
        raw = committed_blob(checkout, commit, lock_path)
        try:
            lock = parse_toml(raw, f"{repository}:{lock_path}")
        except AnchorError:
            if might_reference_first_party(raw):
                raise
            continue
        surfaces.extend(scan_cargo_lock(repository, lock_path, lock, "canonical"))

    by_id: dict[str, dict[str, Any]] = {}
    for surface in surfaces:
        if surface["id"] in by_id:
            fail(f"independent scan produced duplicate surface id {surface['id']!r}")
        by_id[surface["id"]] = surface
    validate_ny_identity_bundle(surfaces)
    if any(
        row["repository"] == "ny"
        and row["dependency"] == "clean"
        and row["kind"] in {"proof-identity", "lake-require", "lake-lock"}
        and row["scope"] != "canonical"
        for row in surfaces
    ):
        fail("NY's seven Clean proof identity surfaces may not be excluded")

    for exclusion in exclusions:
        excluded_entries = entries_by_repository[exclusion["repository"]]
        hidden_authority = [
            path
            for path in excluded_entries
            if (path == exclusion["path"] or path.startswith(exclusion["path"] + "/"))
            and is_committed_authority_path(exclusion["repository"], path)
        ]
        if not hidden_authority:
            fail(
                f"exclusion {exclusion['repository']}:{exclusion['path']} hides no committed dependency-authority file"
            )
    for source_repository, source_path, target_repository, target_path in path_links:
        if scope_for(source_repository, source_path, exclusions) != "canonical":
            continue
        for exclusion in exclusions:
            if exclusion["repository"] == target_repository and (
                target_path == exclusion["path"] or target_path.startswith(exclusion["path"] + "/")
            ):
                fail(
                    f"canonical {source_repository}:{source_path} reaches excluded "
                    f"{target_repository}:{exclusion['path']} by first-party path dependency"
                )
    return sorted(surfaces, key=lambda row: row["id"])


def patch_commit(surface: dict[str, Any], commits: dict[str, str]) -> str:
    if surface["kind"] in {"cargo-patch-path", "cargo-replace-path"}:
        return commits[surface["dependency"]]
    assert surface["rev"] is not None
    return surface["rev"]


def path_is_within(path: PurePosixPath, directory: PurePosixPath) -> bool:
    """Return whether `path` is at/below a normalized repository directory."""
    directory_parts = tuple(part for part in directory.parts if part != ".")
    path_parts = tuple(part for part in path.parts if part != ".")
    return path_parts[: len(directory_parts)] == directory_parts


def cargo_authority_dir(path: str) -> PurePosixPath:
    pure = PurePosixPath(path)
    parent = pure.parent
    if parent.name == ".cargo":
        return parent.parent
    return parent


def matching_patches(surface: dict[str, Any], surfaces: list[dict[str, Any]]) -> list[dict[str, Any]]:
    candidates = [
        candidate
        for candidate in surfaces
        if candidate["scope"] == "canonical"
        and candidate["repository"] == surface["repository"]
        and candidate["dependency"] == surface["dependency"]
        and candidate["package"] == surface["package"]
        and candidate["kind"] in {
            "cargo-patch-git",
            "cargo-patch-path",
            "cargo-replace-git",
            "cargo-replace-path",
        }
    ]
    manifest_dir = cargo_authority_dir(surface["path"])
    applicable = [
        candidate
        for candidate in candidates
        if path_is_within(manifest_dir, cargo_authority_dir(candidate["path"]))
    ]
    if not applicable:
        return []
    depth = max(len(cargo_authority_dir(row["path"]).parts) for row in applicable)
    return [
        row for row in applicable if len(cargo_authority_dir(row["path"]).parts) == depth
    ]


def validate_resolutions(surfaces: list[dict[str, Any]], commits: dict[str, str]) -> None:
    locks: dict[tuple[str, str, str], list[dict[str, Any]]] = {}
    for surface in surfaces:
        if surface["scope"] == "canonical" and surface["kind"] == "cargo-lock":
            locks.setdefault(
                (surface["repository"], surface["dependency"], surface["package"]), []
            ).append(surface)
    for surface in surfaces:
        if surface["scope"] != "canonical" or surface["kind"] != "cargo-git":
            continue
        patches = matching_patches(surface, surfaces)
        patch_revisions = {patch_commit(patch, commits) for patch in patches}
        if len(patch_revisions) > 1:
            fail(f"{surface['id']} has split patch resolutions {sorted(patch_revisions)}")
        expected = next(iter(patch_revisions), surface["rev"])
        manifest_dir = cargo_authority_dir(surface["path"])
        lock_candidates = [
            row
            for row in locks.get(
                (surface["repository"], surface["dependency"], surface["package"]), []
            )
            if path_is_within(manifest_dir, PurePosixPath(row["path"]).parent)
        ]
        if lock_candidates:
            lock_depth = max(len(PurePosixPath(row["path"]).parent.parts) for row in lock_candidates)
            observed = {
                row["rev"]
                for row in lock_candidates
                if len(PurePosixPath(row["path"]).parent.parts) == lock_depth
            }
        else:
            observed = set()
        if patches:
            # Cargo's lockfile preserves the original Git source identity when
            # a workspace `[patch]` redirects that package to a path.  The
            # effective commit is the patch target; demanding that every Git
            # lock row equal the sibling terminal incorrectly rejects the
            # normal, reproducible path-patch pattern used across Trust.
            continue
        elif expected not in observed and surface["locator"].startswith("/workspace/"):
            # Cargo resolves only workspace dependencies that a member actually
            # inherits.  An unused `[workspace.dependencies]` declaration is
            # still an authority edge, but legitimately has no lock row.
            continue
        elif expected not in observed:
            fail(
                f"{surface['id']} manifest rev {expected} is absent from its nearest Cargo.lock; "
                f"observed={sorted(observed)}"
            )

    requires = [row for row in surfaces if row["scope"] == "canonical" and row["kind"] == "lake-require"]
    lake_locks = [row for row in surfaces if row["scope"] == "canonical" and row["kind"] == "lake-lock"]
    path_requires = [
        row for row in surfaces if row["scope"] == "canonical" and row["kind"] == "lake-path"
    ]
    path_locks = [
        row
        for row in surfaces
        if row["scope"] == "canonical" and row["kind"] == "lake-path-lock"
    ]
    proofs = [row for row in surfaces if row["scope"] == "canonical" and row["kind"] == "proof-identity"]
    for requirement in requires:
        directory = PurePosixPath(requirement["path"]).parent
        matches = [
            row
            for row in lake_locks
            if row["repository"] == requirement["repository"]
            and PurePosixPath(row["path"]).parent == directory
            and row["dependency"] == requirement["dependency"]
            and row["package"] == requirement["package"]
        ]
        if len(matches) != 1:
            fail(f"{requirement['id']} must have exactly one matching first-party lake lock row")
        lock = matches[0]
        for field in ("url", "rev", "subdir"):
            if lock[field] != requirement[field]:
                fail(f"{requirement['id']} and {lock['id']} split field {field}")
    for requirement in path_requires:
        directory = PurePosixPath(requirement["path"]).parent
        matches = [
            row
            for row in path_locks
            if row["repository"] == requirement["repository"]
            and PurePosixPath(row["path"]).parent == directory
            and row["dependency"] == requirement["dependency"]
            and row["package"] == requirement["package"]
        ]
        if len(matches) != 1:
            fail(
                f"{requirement['id']} must have exactly one matching first-party "
                "Lake path lock row"
            )
    for proof in proofs:
        matches = [
            row
            for row in requires
            if row["repository"] == proof["repository"]
            and row["dependency"] == proof["dependency"]
            and row["package"] == proof["package"]
            and row["rev"] == proof["rev"]
            and (proof["url"] is None or row["url"] == proof["url"])
            and (proof["subdir"] is None or row["subdir"] == proof["subdir"])
        ]
        if not matches:
            fail(f"{proof['id']} is not bound to a matching canonical Lake requirement")


def derive_direct_edges(
    surfaces: list[dict[str, Any]], commits: dict[str, str]
) -> list[dict[str, Any]]:
    grouped: dict[tuple[str, str], dict[str, set[str]]] = {}
    for surface in surfaces:
        if surface["scope"] != "canonical" or surface["kind"] not in {
            "cargo-git",
            "cargo-path",
            "cargo-patch-git",
            "cargo-patch-path",
            "cargo-replace-git",
            "cargo-replace-path",
            "lake-require",
            "lake-path",
        }:
            continue
        consumer = surface["repository"]
        dependency = surface["dependency"]
        if consumer == dependency:
            continue
        ids = {surface["id"]}
        if surface["kind"] == "cargo-git":
            patches = matching_patches(surface, surfaces)
            revisions = {patch_commit(patch, commits) for patch in patches}
            if len(revisions) > 1:
                fail(f"{surface['id']} has split effective revisions {sorted(revisions)}")
            commit = next(iter(revisions), surface["rev"])
            ids.update(patch["id"] for patch in patches)
        elif surface["kind"] == "cargo-path":
            commit = commits[dependency]
        elif surface["kind"] in {
            "cargo-patch-git",
            "cargo-patch-path",
            "cargo-replace-git",
            "cargo-replace-path",
        }:
            commit = patch_commit(surface, commits)
        elif surface["kind"] == "lake-path":
            commit = commits[dependency]
            ids.update(
                row["id"]
                for row in surfaces
                if row["scope"] == "canonical"
                and row["repository"] == consumer
                and row["dependency"] == dependency
                and row["package"] == surface["package"]
                and row["kind"] == "lake-path-lock"
                and PurePosixPath(row["path"]).parent
                == PurePosixPath(surface["path"]).parent
            )
        else:
            commit = surface["rev"]
            ids.update(
                row["id"]
                for row in surfaces
                if row["scope"] == "canonical"
                and row["repository"] == consumer
                and row["dependency"] == dependency
                and row["rev"] == commit
                and row["kind"] in {"lake-lock", "proof-identity"}
            )
        assert isinstance(commit, str)
        grouped.setdefault((consumer, dependency), {}).setdefault(commit, set()).update(ids)

    edges: list[dict[str, Any]] = []
    for (consumer, dependency), revisions in sorted(grouped.items()):
        if len(revisions) != 1:
            fail(
                f"direct edge {consumer}->{dependency} has split revisions {sorted(revisions)}"
            )
        commit, ids = next(iter(revisions.items()))
        edges.append(
            {
                "consumer": consumer,
                "dependency": dependency,
                "commit": commit,
                "surfaces": sorted(ids),
            }
        )
    return edges


def required_anchors(
    edges: list[dict[str, Any]], commits: dict[str, str]
) -> list[dict[str, str]]:
    return [
        {
            "consumer": edge["consumer"],
            "dependency": edge["dependency"],
            "commit": edge["commit"],
            "terminal": commits[edge["dependency"]],
            "reason": GENERATION_CUT_REASON,
        }
        for edge in edges
        if edge["commit"] != commits[edge["dependency"]]
    ]


def validate_generation_graph(
    edges: list[dict[str, Any]], commits: dict[str, str]
) -> None:
    """Require terminal-generation edges to be acyclic after finite SHA cuts."""
    adjacency: dict[str, set[str]] = {name: set() for name in CONSUMERS}
    for edge in edges:
        if edge["commit"] == commits[edge["dependency"]]:
            adjacency[edge["consumer"]].add(edge["dependency"])

    visiting: list[str] = []
    visited: set[str] = set()

    def visit(node: str) -> None:
        if node in visiting:
            start = visiting.index(node)
            cycle = visiting[start:] + [node]
            fail(
                "terminal-generation first-party dependency cycle has no finite exact-SHA "
                f"cut: {' -> '.join(cycle)}"
            )
        if node in visited:
            return
        visiting.append(node)
        for dependency in sorted(adjacency[node]):
            visit(dependency)
        visiting.pop()
        visited.add(node)

    for node in sorted(adjacency):
        visit(node)


def verify_local_objects(
    repo_root: Path,
    surfaces: list[dict[str, Any]],
    edges: list[dict[str, Any]],
    commits: dict[str, str],
) -> None:
    for dependency, terminal in commits.items():
        checkout = repo_root / SUBMODULES[dependency][0]
        if run_git(checkout, ["cat-file", "-t", terminal]).decode().strip() != "commit":
            fail(f"{dependency} terminal {terminal} is not a local commit object")
    references: set[tuple[str, str]] = {
        (row["dependency"], row["rev"])
        for row in surfaces
        if row["scope"] == "canonical" and row["rev"] is not None
    }
    references.update((edge["dependency"], edge["commit"]) for edge in edges)
    for dependency, commit in sorted(references):
        checkout = repo_root / SUBMODULES[dependency][0]
        object_type = run_git(checkout, ["cat-file", "-t", commit]).decode().strip()
        if object_type != "commit":
            fail(f"{dependency} referenced object {commit} is not a commit")
        terminal = commits[dependency]
        if commit != terminal:
            ancestor = subprocess.run(
                ["git", "-C", str(checkout), "merge-base", "--is-ancestor", commit, terminal],
                stdout=subprocess.DEVNULL,
                stderr=subprocess.PIPE,
                env=authority_git_environment(),
                check=False,
            )
            if ancestor.returncode != 0:
                detail = ancestor.stderr.decode("utf-8", "replace").strip()
                fail(
                    f"{dependency} referenced commit {commit} is not an ancestor of terminal {terminal}"
                    + (f": {detail}" if detail else "")
                )


def compare_inventory(label: str, expected: list[dict[str, Any]], actual: list[dict[str, Any]]) -> None:
    expected_rows = [canonical_json(row) for row in expected]
    actual_rows = [canonical_json(row) for row in actual]
    if len(expected_rows) != len(set(expected_rows)):
        fail(f"receipt {label} contains a duplicate semantic row")
    if set(expected_rows) != set(actual_rows):
        missing = sorted(set(actual_rows) - set(expected_rows))
        extra = sorted(set(expected_rows) - set(actual_rows))
        fail(
            f"receipt {label} differs from independently observed committed state: "
            f"missing={missing[:5]}, extra={extra[:5]}"
        )


def github_authorization_header(url: str, ceiling: Path) -> str | None:
    """Obtain GitHub credentials separately from the isolated transport config."""
    parsed = urlsplit(url)
    try:
        port = parsed.port
    except ValueError as error:
        fail(f"canonical remote URL has malformed port authority: {error}")
    if not (
        parsed.scheme == "https"
        and parsed.hostname == "github.com"
        and parsed.username is None
        and parsed.password is None
        and port is None
        and not parsed.query
        and not parsed.fragment
    ):
        return None
    request = (
        f"protocol=https\nhost=github.com\npath={parsed.path.lstrip('/')}\n\n"
    ).encode("utf-8")
    completed = subprocess.run(
        ["git", "credential", "fill"],
        cwd=ceiling,
        input=request,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        env=credential_git_environment(ceiling),
        check=False,
    )
    if completed.returncode != 0:
        return None
    fields: dict[str, str] = {}
    for raw_row in completed.stdout.splitlines():
        raw_key, separator, raw_value = raw_row.partition(b"=")
        if separator != b"=":
            fail("Git credential helper returned a malformed protocol row")
        try:
            key = raw_key.decode("ascii", "strict")
            value = raw_value.decode("utf-8", "strict")
        except UnicodeDecodeError as error:
            fail(f"Git credential helper returned malformed text: {error}")
        if key in fields:
            fail(f"Git credential helper returned duplicate field {key!r}")
        fields[key] = value
    if fields.get("protocol", "https") != "https" or fields.get(
        "host", "github.com"
    ) != "github.com":
        fail("Git credential helper changed the canonical GitHub authority")
    username = fields.get("username")
    password = fields.get("password")
    auth_type = fields.get("authtype")
    credential = fields.get("credential")
    has_basic = username is not None or password is not None
    has_typed = auth_type is not None or credential is not None
    if has_basic and has_typed:
        fail("Git credential helper returned conflicting credential sources")
    if has_basic:
        if not username or not password:
            fail("Git credential helper returned an incomplete Basic credential")
        if any(character in username + password for character in "\r\n\0"):
            fail("Git credential helper returned malformed Basic credential text")
        encoded = base64.b64encode(f"{username}:{password}".encode("utf-8")).decode(
            "ascii"
        )
        return f"Authorization: Basic {encoded}"
    if has_typed:
        if not auth_type or not credential:
            fail("Git credential helper returned an incomplete typed credential")
        if not re.fullmatch(r"[!#$%&'*+.^_`|~0-9A-Za-z-]+", auth_type):
            fail("Git credential helper returned a malformed authorization type")
        if any(character in credential for character in "\r\n\0"):
            fail("Git credential helper returned a malformed authorization credential")
        return f"Authorization: {auth_type} {credential}"
    return None


def verify_one_remote_main(name: str, url: str, commit: str) -> None:
    with tempfile.TemporaryDirectory(prefix="trust-remote-main-") as temporary:
        ceiling = Path(temporary)

        def probe(authorization_header: str | None) -> subprocess.CompletedProcess[bytes]:
            return subprocess.run(
                ["git", "ls-remote", "--exit-code", url, "refs/heads/main"],
                cwd=temporary,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                env=remote_git_environment(
                    ceiling, authorization_header=authorization_header
                ),
                check=False,
            )

        authorization: str | None = None
        completed = probe(None)
        if completed.returncode != 0:
            authorization = github_authorization_header(url, ceiling)
            if authorization is not None:
                completed = probe(authorization)
    if completed.returncode != 0:
        detail = (completed.stderr or completed.stdout).decode("utf-8", "replace").strip()
        if authorization is not None:
            secret = authorization.rpartition(" ")[2]
            detail = detail.replace(authorization, "Authorization: <redacted>")
            detail = detail.replace(secret, "<redacted>")
        fail(f"cannot resolve {name} remote main at {url}: {detail}")
    rows = completed.stdout.decode("ascii", "strict").splitlines()
    expected = f"{commit}\trefs/heads/main"
    if rows != [expected]:
        fail(f"{name} terminal {commit} is not exactly remote main; observed={rows}")


def verify_remote_main(
    commits: dict[str, str], *, root_commit: str | None = None
) -> None:
    for name, commit in sorted(commits.items()):
        verify_one_remote_main(name, SUBMODULES[name][1], commit)
    if root_commit is not None:
        verify_one_remote_main("trust", ROOT_URL, root_commit)


def verify_terminal_policy_v2_remote_main(
    repo_root: Path,
    policy_state: dict[str, Any],
    commits: dict[str, str],
    *,
    root_commit: str,
    prospective_root_old: str | None,
) -> None:
    """Verify v2 endpoints, with real pre-push old-main semantics.

    Before R1, TrustWP remote main is P while R0 deliberately still binds W0.
    During a Trust-main push, the remote cannot already name the new commit; the
    hook therefore authenticates the advertised old SHA both against the raw
    required parent and a fresh canonical ``ls-remote`` sample.  A normal
    post-push invocation instead requires the judged revision itself to be
    remote main.
    """
    state = policy_state.get("state")
    if state not in {"Armed", "Terminal"}:
        fail("terminal-policy v2 remote verification requires Armed or Terminal state")
    policy = policy_state.get("policy")
    if not isinstance(policy, dict):
        fail("terminal-policy v2 remote verification is missing armed policy")
    bindings_value = policy.get("root_bindings")
    if not isinstance(bindings_value, dict) or set(bindings_value) != set(SUBMODULES):
        fail("terminal-policy v2 remote verification has malformed root bindings")
    bindings = {
        name: require_sha(bindings_value[name], f"terminal-policy v2 root.{name}")
        for name in sorted(SUBMODULES)
    }
    for name in sorted(set(SUBMODULES) - {"trust-wp"}):
        if commits[name] != bindings[name]:
            fail(
                f"terminal-policy v2 current {name} binding differs from Armed R0"
            )
        verify_one_remote_main(name, SUBMODULES[name][1], bindings[name])
    if state == "Armed":
        wp_remote = require_sha(
            policy.get("predecessor_commit"), "terminal-policy v2 predecessor P"
        )
    else:
        wp_remote = require_sha(
            commits["trust-wp"], "terminal-policy v2 terminal TrustWP W1"
        )
    verify_one_remote_main("trust-wp", SUBMODULES["trust-wp"][1], wp_remote)

    if prospective_root_old is None:
        expected_remote_root = root_commit
    else:
        parents = raw_commit_parents(
            repo_root, root_commit, f"terminal-policy v2 prospective {state} root"
        )
        if len(parents) != 1:
            fail(
                "terminal-policy v2 prospective root publication requires a raw "
                f"single-parent transition; state={state}, parents={parents}"
            )
        expected_old = parents[0]
        if prospective_root_old != expected_old:
            fail(
                "terminal-policy v2 advertised old Trust remote main differs from "
                f"the required direct parent: advertised={prospective_root_old}, "
                f"required={expected_old}, state={state}"
            )
        expected_remote_root = prospective_root_old
    verify_one_remote_main("trust", ROOT_URL, expected_remote_root)


def load_exclusion_policy(
    repo_root: Path, root_revision: str, exclusions_path: str, revision_label: str
) -> list[dict[str, str]]:
    # Absence gets its own refusal, ahead of the generic authority check. It is
    # the one failure here that is usually a fact about the REVISION THE GATE
    # WAS POINTED AT rather than about the constellation — the policy landed on
    # `main` after this clone's HEAD — and "is not committed" with no next step
    # is what taught three pushes in one day to reach for `--no-verify`.
    if committed_tree_entries(repo_root, root_revision).get(exclusions_path) is None:
        raise UnresolvableAtRevision(
            f"constellation exclusion policy {exclusions_path} is not committed at "
            f"{revision_label} [{root_revision}]",
            [
                "This gate resolves its policy at exactly ONE revision and refuses",
                "rather than guessing which one you meant. Options:",
                "  * judging a push: let the pre-push hook pass the refs and add",
                "      --push-context   (it judges the revision being PUSHED, which",
                "      is what the lane is asking about, not this clone's HEAD)",
                "  * judging a named revision:",
                f"      --rev origin/main      # or any commit-ish carrying {exclusions_path}",
                "  * the policy really is absent at that revision: commit it there,",
                "      or point somewhere else with --exclusions-path <path>",
                "A STALE LOCAL HEAD is the common cause. This clone's HEAD can predate",
                "the policy while every revision you would push carries it; compare with",
                "  git cat-file -t HEAD:" + exclusions_path,
                "  git cat-file -t origin/main:" + exclusions_path,
            ],
        )
    require_regular_committed_authority(
        repo_root, root_revision, exclusions_path, "constellation exclusion policy"
    )
    value = parse_json(
        committed_blob(repo_root, root_revision, exclusions_path),
        "constellation exclusion policy",
    )
    if not isinstance(value, dict):
        fail("exclusion policy top level must be an object")
    require_exact_keys(value, {"schema", "exclusions"}, "exclusion policy")
    if value["schema"] != EXCLUSIONS_SCHEMA:
        fail(f"exclusion policy schema must be exactly {EXCLUSIONS_SCHEMA!r}")
    return validate_exclusions(value["exclusions"])


def derive_receipt(
    repo_root: Path,
    root_revision: str,
    exclusions: list[dict[str, str]],
    *,
    verify_remote: bool = False,
    require_wp_trust_anchor: bool = False,
    external_evidence: bool = True,
    prospective_root_old: str | None = None,
) -> dict[str, object]:
    if require_wp_trust_anchor and not verify_remote:
        fail(
            "terminal TrustWP anchor evidence requires remote-main verification; "
            "derive_receipt(require_wp_trust_anchor=True) must also set "
            "verify_remote=True"
        )
    root_revision = require_sha(root_revision, "judged root revision")
    if external_evidence:
        clean_head = committed_clean_head(repo_root)
        if root_revision != clean_head:
            fail(
                "external receipt evidence must derive from the checkout's clean "
                f"committed HEAD: requested={root_revision}, HEAD={clean_head}"
            )
    root_type = run_git(repo_root, ["cat-file", "-t", root_revision]).decode(
        "ascii", "strict"
    ).strip()
    if root_type != "commit":
        fail("constellation derivation must use one committed Trust revision")
    require_regular_committed_authority(
        repo_root, root_revision, ".gitmodules", "root .gitmodules authority"
    )
    submodules = committed_submodules(repo_root, root_revision)
    commits = {name: commit for name, (_path, _url, commit) in submodules.items()}
    if external_evidence:
        for name, (path, _url, commit) in sorted(submodules.items()):
            require_clean_checkout(
                repo_root / path,
                commit,
                f"{name} terminal checkout",
            )
    v1_terminal_wp_mode = terminal_wp_policy_claimed(
        repo_root, root_revision, commits
    )
    v2_state = terminal_wp_policy_v2_state(repo_root, root_revision, commits)
    v2_phase = v2_state["state"]
    v2_active = v2_phase in {"Armed", "Terminal"}
    if v2_phase == "Armed" and v1_terminal_wp_mode:
        fail(
            "terminal-policy v2 Armed R0 has prior v1 TrustWP-move history; "
            "R0 must still bind exact W0 with no move/revert claim"
        )
    if v2_phase == "Terminal" and not v1_terminal_wp_mode:
        fail(
            "terminal-policy v2 Terminal R1 did not activate the preserved v1 "
            "TrustWP-move tripwire"
        )
    if v2_phase == "Armed" and require_wp_trust_anchor:
        fail("terminal-policy v2 is Armed at R0 but has no Terminal R1 anchor yet")
    terminal_wp_mode = (
        require_wp_trust_anchor
        or v1_terminal_wp_mode
        or v2_phase == "Terminal"
    )
    remote_mode = verify_remote or v1_terminal_wp_mode or v2_active
    require_external_receipt_untracked(
        repo_root,
        root_revision,
        terminal_wp_mode=terminal_wp_mode or v2_active,
    )
    bindings = [
        {"repository": name, "path": path, "url": url, "commit": commit}
        for name, (path, url, commit) in sorted(submodules.items())
    ]
    surfaces = scan_constellation(repo_root, root_revision, commits, exclusions)
    edges = derive_direct_edges(surfaces, commits)
    validate_generation_graph(edges, commits)
    validate_resolutions(surfaces, commits)
    anchors = required_anchors(edges, commits)
    verify_local_objects(repo_root, surfaces, edges, commits)
    if v2_phase == "Terminal":
        wp_trust_anchor = derive_wp_root_anchor_v2(
            repo_root, root_revision, commits, v2_state
        )
    elif terminal_wp_mode:
        wp_trust_anchor = derive_wp_root_anchor(repo_root, root_revision, commits)
    else:
        wp_trust_anchor = None
    if remote_mode:
        if v2_active:
            verify_terminal_policy_v2_remote_main(
                repo_root,
                v2_state,
                commits,
                root_commit=root_revision,
                prospective_root_old=prospective_root_old,
            )
        else:
            verify_remote_main(commits, root_commit=root_revision)
    receipt: dict[str, object] = {
        "schema": EXTERNAL_SCHEMA,
        "self": {"repository": "trust", "commit": root_revision},
        "repositories": {
            name: {"url": SUBMODULES[name][1], "commit": commits[name]}
            for name in sorted(SUBMODULES)
        },
        "root_bindings": bindings,
        "exclusions": exclusions,
        "surfaces": surfaces,
        "direct_edges": edges,
        "anchors": anchors,
        "wp_trust_anchor": wp_trust_anchor,
    }
    validate_external_receipt(
        receipt,
        require_wp_trust_anchor=terminal_wp_mode or v2_phase == "Terminal",
    )
    return receipt


def index_tree(repo: Path, label: str) -> str:
    tree = run_git(repo, ["write-tree"]).decode("ascii", "strict").strip()
    return require_sha(tree, f"{label} index tree")


def require_no_hidden_index_entries(repo: Path, label: str) -> None:
    """Reject index flags that can conceal a tracked worktree mutation."""
    hidden: list[str] = []
    for row in run_git(repo, ["ls-files", "-v", "-z", "--"]).split(b"\0"):
        if not row:
            continue
        if len(row) < 3 or row[1:2] != b" ":
            fail(f"{label} returned malformed ls-files -v row {row!r}")
        marker = row[:1]
        # `S` is skip-worktree.  A lowercase marker is the documented
        # assume-unchanged rendering (including `s` when both flags are set).
        if marker == b"S" or marker.islower():
            hidden.append(row[2:].decode("utf-8", "backslashreplace"))
    if hidden:
        fail(
            f"{label} carries forbidden assume-unchanged/skip-worktree index flags: "
            f"{hidden[:10]}"
        )


def require_clean_checkout(repo: Path, expected_commit: str, label: str) -> None:
    """Require HEAD, index, and non-ignored worktree state to be one commit.

    Ignored untracked files are intentionally permitted: all dependency and
    cycle authority is read from committed objects, never from those paths.
    Non-ignored untracked files fail closed so a would-be evidence artifact or
    newly authored authority file cannot be mistaken for committed input.
    """
    require_unmodified_history_view(repo, label)
    expected_commit = require_sha(expected_commit, f"{label} expected commit")
    head = decode_text(
        run_git(repo, ["rev-parse", "--verify", "HEAD^{commit}"]),
        f"{label} HEAD",
    ).strip()
    require_sha(head, f"{label} HEAD")
    if head != expected_commit:
        fail(
            f"{label} HEAD does not equal its committed root gitlink: "
            f"HEAD={head}, gitlink={expected_commit}"
        )

    require_no_hidden_index_entries(repo, label)
    expected_tree = decode_text(
        run_git(repo, ["rev-parse", "--verify", f"{expected_commit}^{{tree}}"]),
        f"{label} committed tree",
    ).strip()
    require_sha(expected_tree, f"{label} committed tree")
    staged_tree = index_tree(repo, label)
    if staged_tree != expected_tree:
        fail(
            f"{label} receipt generation requires the staged index to equal committed "
            f"HEAD; HEAD tree={expected_tree}, index tree={staged_tree}"
        )

    tracked = subprocess.run(
        [
            "git",
            "-C",
            str(repo),
            "diff-files",
            "--quiet",
            "--ignore-submodules=none",
            "--",
        ],
        stdout=subprocess.DEVNULL,
        stderr=subprocess.PIPE,
        env=authority_git_environment(),
        check=False,
    )
    if tracked.returncode not in {0, 1}:
        detail = tracked.stderr.decode("utf-8", "replace").strip()
        fail(f"cannot compare {label} worktree with the staged index: {detail}")
    untracked = run_git(repo, ["ls-files", "--others", "--exclude-standard", "-z"])
    if tracked.returncode == 1 or untracked:
        untracked_paths = [
            row.decode("utf-8", "backslashreplace")
            for row in untracked.split(b"\0")
            if row
        ]
        fail(
            f"{label} receipt generation requires index and worktree to equal "
            f"committed HEAD; tracked_changes={tracked.returncode == 1}, "
            f"untracked={untracked_paths[:10]}"
        )


def committed_clean_head(repo_root: Path) -> str:
    """Return committed HEAD only when index and worktree are exactly that tree.

    ``write-tree`` is the non-negotiable index comparison: local submodule
    ignore configuration can make status/diff conceal a staged gitlink.
    Assume-unchanged and skip-worktree are refused separately.  Ignored
    untracked paths are allowed because no authority is read from the worktree.
    """
    head = run_git(repo_root, ["rev-parse", "--verify", "HEAD^{commit}"]).decode(
        "ascii", "strict"
    ).strip()
    require_sha(head, "root HEAD commit")
    require_clean_checkout(repo_root, head, "root checkout")
    return head


def require_external_receipt_untracked(
    repo_root: Path, root_commit: str, *, terminal_wp_mode: bool
) -> None:
    entries = committed_tree_entries(repo_root, root_commit)
    forbidden = {EXTERNAL_RECEIPT_PATH}
    if terminal_wp_mode:
        # A legacy v2 receipt also cannot survive R0 -> R1: it would either
        # bind W0 forever or require a second R1 tree delta.  Refuse it rather
        # than let a conditional harness select the weaker historical mode.
        forbidden.add(RECEIPT_PATH)
    tracked = sorted(forbidden & set(entries))
    if tracked:
        fail(
            "v3 constellation evidence must remain external/untracked"
            + (" in terminal TrustWP anchor mode" if terminal_wp_mode else "")
            + f"; tracked={tracked}"
        )


# ---------------------------------------------------------------------------
# WHICH REVISION IS THE GATE ASKING ABOUT?
#
# Until 2026-08-29 there was no answer to that question: verification read the
# clone's `HEAD` and receipt generation read the clone's staged index, both
# implicitly, with no way to say otherwise. In a shared checkout whose HEAD sits
# behind `origin/main` that is the wrong revision for every question anyone
# asks — the lane went red for every push regardless of what was being pushed,
# because the exclusion policy landed on `main` after that HEAD. A gate that
# must be routinely bypassed protects nothing and trains everyone to bypass it;
# three commits in one day went out under `--no-verify` for exactly this.
#
# So the revision is now SELECTED, and every read in one judgement takes the
# same one:
#
#   --rev REV        an explicit commit-ish (or tree-ish)
#   --push-context   the revision(s) the push in flight would publish
#   (neither)        HEAD; external generation separately requires a clean
#                    index/worktree equal to that commit
#
# `--push-context` mirrors fast.revert-rationale / fast.measurement-provenance /
# fast.pin-regression: a manifest command string is fixed and gets no stdin, so
# scripts/hooks/pre-push exports the ref lines as TRUST_PUSHED_REFS and the same
# row text runs in both runners. UNSET means no push is in flight and the
# subject WIDENS to HEAD rather than narrowing to nothing, and a `SUBJECT:` line
# always says which reading was taken.
#
# WHICH PUSHED REF IS A TERMINAL-STATE CANDIDATE. This gate judges whether a
# revision may become the repository's terminal state. That is a property of
# WHERE a sha lands, not of the sha — so the discriminator is the REMOTE ref
# (git's third field), never the local one, which for `git push <sha>:<ref>` is
# not a ref name at all.
#
# Two namespaces cannot become the terminal state by construction: nothing
# resolves `origin/main` through them, and no build, pin, or receipt reads them.
#
#   refs/archive/*  retired branches, preserved verbatim (the convention is
#                   refs/archive/<date>/<branch>; 27 such refs predate this gate)
#   refs/pins/*     durable anchors naming one commit by its own sha, so that a
#                   pin a branch no longer reaches stays fetchable
#
# Retired history is retired precisely BECAUSE it does not meet today's policy —
# it predates the marker, or carries the pin moves that made it unlandable. So
# judging an archive push as a landing candidate does not protect anything; it
# makes preservation impossible and pushes people to `--no-verify`, which is
# how a gate stops being a gate. Measured 2026-08-31: after the marker activated
# on 2026-08-29, NO archive ref could be pushed through this hook at all.
#
# This is an ALLOWLIST and it fails closed twice over. An unrecognised namespace
# is judged, a missing remote ref is judged, and if filtering leaves nothing the
# subject WIDENS to HEAD rather than passing on an empty set — so the exemption
# can only ever remove refs that were never terminal candidates, and can never
# be the reason a push passes.
# ---------------------------------------------------------------------------
PUSH_REFS_ENV = "TRUST_PUSHED_REFS"

NON_TERMINAL_REF_PREFIXES = ("refs/archive/", "refs/pins/")


def ref_is_terminal_candidate(remote_ref: str) -> bool:
    """Could a sha published at ``remote_ref`` become the terminal state?

    Fail-closed: anything not on the allowlist of preservation namespaces is a
    candidate, including an empty or malformed ref.
    """
    if not remote_ref:
        return True
    return not remote_ref.startswith(NON_TERMINAL_REF_PREFIXES)


def rev_parse(repo_root: Path, revision: str, label: str) -> str:
    completed = subprocess.run(
        [
            "git",
            "-C",
            str(repo_root),
            "rev-parse",
            "--verify",
            "--quiet",
            f"{revision}^{{commit}}",
        ],
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        env=authority_git_environment(),
        check=False,
    )
    resolved = completed.stdout.decode("ascii", "replace").strip()
    if completed.returncode != 0 or not SHA_RE.match(resolved):
        raise UnresolvableAtRevision(
            f"{label} {revision!r} does not name a commit in this checkout",
            [
                "Options:",
                "  * name a revision this clone has:  --rev origin/main",
                "  * fetch it first:                  git fetch origin",
                "  * drop --rev to judge this clone's HEAD (the historical default)",
            ],
        )
    return resolved


def pushed_revisions() -> list[tuple[str, str]] | None:
    """The (sha, ref) pairs a push in flight would publish.

    ``None`` means no push is in flight — the variable is UNSET, so the caller
    widens to its historical default.  An empty LIST means a push that updates
    no ref (empty-but-set), which also has nothing narrower to judge.  Deletions
    publish no tree and are dropped; duplicate shas are judged once.

    A revision landing outside a terminal-state namespace is dropped too, and
    the drop is PRINTED rather than silent — see ``NON_TERMINAL_REF_PREFIXES``.
    The test is on the REMOTE ref (git's third field): a `git push <sha>:<ref>`
    has no local ref name to test, and where the sha lands is what decides
    whether it can become the terminal state.  A line with no remote ref is
    judged, not skipped.
    """
    raw = os.environ.get(PUSH_REFS_ENV)
    if raw is None:
        return None
    revisions: list[tuple[str, str]] = []
    seen: set[str] = set()
    for line in raw.splitlines():
        fields = line.split()
        if len(fields) < 2:
            continue
        local_ref, local_sha = fields[0], fields[1]
        remote_ref = fields[2] if len(fields) >= 3 else ""
        if not local_sha or set(local_sha) == {"0"}:
            continue
        if not ref_is_terminal_candidate(remote_ref):
            print(
                f"SUBJECT: not a terminal-state candidate, not judged: "
                f"{remote_ref} [{local_sha[:12]}]"
            )
            continue
        if local_sha in seen:
            continue
        seen.add(local_sha)
        revisions.append((local_sha, remote_ref or local_ref))
    return revisions


def pushed_main_old_for_source(source: str) -> str | None:
    """Return the advertised old Trust main for this prospective source.

    Only an actual ``refs/heads/main`` update gets prospective semantics.
    Topic/archive publication cannot claim that the new revision is in flight
    toward canonical main, and therefore remains subject to ordinary post-push
    remote equality.
    """
    raw = os.environ.get(PUSH_REFS_ENV)
    if raw is None:
        return None
    source = require_sha(source, "prospective pushed Trust revision")
    matches: list[str] = []
    for line in raw.splitlines():
        fields = line.split()
        if len(fields) < 3 or fields[1] != source or fields[2] != "refs/heads/main":
            continue
        if len(fields) != 4:
            fail(
                "terminal-policy v2 prospective main push row must contain exactly "
                f"local-ref local-sha remote-ref remote-sha; observed={fields}"
            )
        old = fields[3]
        if old == "0" * 40:
            fail("terminal-policy v2 refuses creation of canonical Trust main")
        matches.append(require_sha(old, "prospective advertised old Trust main"))
    if len(matches) > 1:
        fail(
            "terminal-policy v2 prospective push repeats canonical Trust main "
            f"for one revision: advertised_old={matches}"
        )
    return matches[0] if matches else None


def authenticate_terminal_policy_v2_main_transition(
    repo_root: Path,
    root_commit: str,
    new_state: dict[str, Any],
    advertised_old: str,
) -> None:
    """Bind every canonical-main update to its fresh old v2 state.

    Candidate-only policy selection is insufficient for a pre-push hook: a
    force/replacement update can point canonical main from an Armed/Terminal
    revision to a disconnected unmarked or PreV2 commit.  Authenticate the
    advertised old SHA against canonical remote main, parse that exact local
    commit with the same raw-history policy, and permit only monotone movement
    within the identical marker introduction and R0 lineage.
    """
    root_commit = require_sha(root_commit, "prospective pushed Trust revision")
    advertised_old = require_sha(advertised_old, "prospective advertised old Trust main")
    old_submodules = committed_submodules(repo_root, advertised_old)
    old_commits = {
        name: commit for name, (_path, _url, commit) in old_submodules.items()
    }
    old_state = terminal_wp_policy_v2_state(repo_root, advertised_old, old_commits)

    # Do not impose v2's networked transition protocol on legacy history that
    # predates the marker on both sides.  The moment either side has introduced
    # v2, however, the advertised old identity must be freshly authenticated.
    if (
        old_state.get("introduction_commit") is None
        and new_state.get("introduction_commit") is None
    ):
        return
    verify_one_remote_main("trust", ROOT_URL, advertised_old)

    old_phase = old_state.get("state")
    new_phase = new_state.get("state")
    if old_phase in {"Armed", "Terminal"} and new_phase not in {"Armed", "Terminal"}:
        fail(
            "terminal-policy v2 canonical main may not downgrade an active old "
            f"state: old={old_phase}, new={new_phase}"
        )
    old_intro = old_state.get("introduction_commit")
    new_intro = new_state.get("introduction_commit")
    if old_intro is not None and new_intro != old_intro:
        fail(
            "terminal-policy v2 canonical main may not delete, replace, or re-add "
            "its authenticated marker lineage: "
            f"old_introduction={old_intro}, new_introduction={new_intro}"
        )
    if old_phase not in {"Armed", "Terminal"}:
        return
    if old_state.get("r0") != new_state.get("r0") or old_state.get("policy") != new_state.get("policy"):
        fail(
            "terminal-policy v2 canonical main changed its authenticated Armed "
            "R0 policy lineage"
        )
    if old_phase == "Terminal" and (
        new_phase != "Terminal" or root_commit != advertised_old
    ):
        fail(
            "terminal-policy v2 canonical main is already Terminal and may not "
            f"move or be replaced: old={advertised_old}, candidate={root_commit}"
        )


def select_sources(repo_root: Path, args: argparse.Namespace) -> list[tuple[str, str]]:
    """Every (committed revision, human label) this invocation judges, in order."""
    if args.rev is not None:
        return [(rev_parse(repo_root, args.rev, "--rev"), f"--rev {args.rev}")]
    if args.push_context:
        pushed = pushed_revisions()
        if pushed is None:
            print(f"SUBJECT: HEAD (no push in flight; {PUSH_REFS_ENV} unset)")
        elif not pushed:
            # Set but yielding nothing: a push whose refs are all deletions, or
            # one with no ref updates at all. Either way it publishes no tree,
            # so there is nothing narrower than HEAD to judge — and widening is
            # the fail-closed choice, because an empty subject would PASS.
            print(f"SUBJECT: HEAD (push in flight updates no ref that publishes a tree)")
        else:
            print(f"SUBJECT: push ({len(pushed)} ref update(s))")
            return [
                (
                    rev_parse(repo_root, sha, f"pushed ref {ref}"),
                    f"pushed {ref} [{sha[:12]}]",
                )
                for sha, ref in pushed
            ]
    if args.print_receipt or args.write_receipt:
        clean_head = committed_clean_head(repo_root)
        return [(clean_head, f"clean committed HEAD [{clean_head[:12]}]")]
    head = run_git(repo_root, ["rev-parse", "HEAD"]).decode("ascii", "strict").strip()
    require_sha(head, "root HEAD")
    return [(head, f"HEAD [{head[:12]}]")]


def judge_source(repo_root: Path, args: argparse.Namespace, source: str, label: str) -> None:
    """Validate the constellation at ONE commit; every read takes that one."""
    generating = args.print_receipt or args.write_receipt
    derived_only = False
    source_submodules = committed_submodules(repo_root, source)
    source_commits = {
        name: commit
        for name, (_path, _url, commit) in source_submodules.items()
    }
    auto_terminal_wp_mode = terminal_wp_policy_claimed(
        repo_root, source, source_commits
    )
    v2_state = terminal_wp_policy_v2_state(repo_root, source, source_commits)
    auto_v2_mode = v2_state["state"] in {"Armed", "Terminal"}
    auto_policy_mode = auto_terminal_wp_mode or auto_v2_mode
    prospective_root_old = (
        pushed_main_old_for_source(source) if args.push_context else None
    )
    if prospective_root_old is not None:
        authenticate_terminal_policy_v2_main_transition(
            repo_root, source, v2_state, prospective_root_old
        )
    if not generating and args.derive_when_receipt_absent:
        # Presence is asked of the SAME revision every other read takes. The
        # shell conditional this replaced asked `test -f` of the WORKING TREE,
        # which is a third revision again and answers wrong in any clone whose
        # checkout differs from the revision under judgement.
        if committed_tree_entries(repo_root, source).get(args.receipt_path) is None:
            generating = True
            derived_only = True

    # Once the immutable history records any WP move, validation may never
    # choose the legacy receipt lane again.  A tracked/stale receipt is itself
    # rejected by derive_receipt's terminal policy instead of becoming a
    # downgrade switch.
    if auto_policy_mode and not generating:
        generating = True
        derived_only = True

    if generating:
        exclusions = load_exclusion_policy(repo_root, source, args.exclusions_path, label)
        receipt = derive_receipt(
            repo_root,
            source,
            exclusions,
            verify_remote=args.verify_remote,
            require_wp_trust_anchor=args.require_wp_trust_anchor,
            external_evidence=not derived_only,
            prospective_root_old=(prospective_root_old if auto_v2_mode else None),
        )
        rendered = render_receipt(receipt)
        if derived_only:
            suffix = " + REMOTE MAIN" if args.verify_remote or auto_policy_mode else ""
            reason = (
                "immutable terminal policy"
                if auto_policy_mode
                else "no committed receipt"
            )
            print(f"DEPENDENCY CONSTELLATION OK{suffix} ({label}; derived, {reason})")
            print("  root gitlinks: 9/9 exact")
            print("  committed Cargo/Lake surfaces, direct edges, and generation cuts: exact")
        elif args.print_receipt:
            print(rendered, end="")
        else:
            external_path = require_relative_path(
                args.external_receipt_path, "external receipt output path"
            )
            if external_path in committed_tree_entries(repo_root, source):
                fail(
                    f"external v3 receipt output {external_path} is tracked; "
                    "terminal cycle evidence must remain outside the authenticated tree"
                )
            write_receipt(repo_root, external_path, rendered)
            print(
                "DEPENDENCY CONSTELLATION EXTERNAL RECEIPT WRITTEN: "
                f"{external_path}"
            )
            print(f"  source: {label} (do not stage this self-binding evidence)")
        return

    verify_constellation(
        repo_root,
        root_commit=source,
        revision_label=label,
        print_observed=args.print_observed,
        verify_remote=args.verify_remote,
        receipt_path=args.receipt_path,
    )
    if not args.print_observed:
        suffix = " + REMOTE MAIN" if args.verify_remote else ""
        print(f"DEPENDENCY CONSTELLATION OK{suffix} ({label})")
        print("  root gitlinks: 9/9 exact")
        print("  committed Cargo/Lake surfaces, direct edges, and generation cuts: exact")


def render_receipt(receipt: dict[str, object]) -> str:
    return json.dumps(receipt, indent=2, sort_keys=True, ensure_ascii=True) + "\n"


def write_receipt(repo_root: Path, receipt_path: str, content: str) -> None:
    relative = require_relative_path(receipt_path, "receipt output path")
    destination = repo_root / relative
    if destination.is_symlink():
        fail(f"receipt output {relative} may not be a symlink")
    destination.parent.mkdir(parents=True, exist_ok=True)
    temporary = destination.with_name(destination.name + ".tmp")
    temporary.write_text(content, encoding="utf-8")
    os.replace(temporary, destination)


def verify_constellation(
    repo_root: Path,
    *,
    root_commit: str,
    revision_label: str,
    print_observed: bool = False,
    verify_remote: bool = False,
    receipt_path: str = RECEIPT_PATH,
) -> tuple[list[dict[str, Any]], list[dict[str, Any]], list[dict[str, str]]]:
    if committed_tree_entries(repo_root, root_commit).get(receipt_path) is None:
        raise UnresolvableAtRevision(
            f"committed constellation receipt {receipt_path} is not committed at "
            f"{revision_label} [{root_commit}]",
            [
                "Options:",
                "  * judging a push:            add --push-context",
                "  * judging a named revision:  --rev <commit-ish>",
                "  * no receipt exists yet at that revision and that is expected:",
                "      --derive-when-receipt-absent  derives and validates the",
                "      constellation from that same revision instead of comparing",
                "      it to an inventory that is not there. It still refuses an",
                "      incoherent constellation; it only stops requiring the",
                "      committed inventory to exist.",
                f"  * write one:  --write-receipt --rev <commit-ish>",
            ],
        )
    require_regular_committed_authority(
        repo_root, root_commit, receipt_path, "committed constellation receipt"
    )
    require_regular_committed_authority(
        repo_root, root_commit, ".gitmodules", "committed root .gitmodules"
    )
    receipt = validate_receipt(
        parse_json(committed_blob(repo_root, root_commit, receipt_path), "committed receipt")
    )
    # Trust: read the gitlinks at the SAME revision as the receipt. This call
    # used to take committed_submodules' `HEAD` default while root_commit was
    # separately resolved from HEAD — identical by accident, and silently two
    # different revisions the moment a caller names one.
    submodules = committed_submodules(repo_root, root_commit)
    expected_bindings = [
        {"repository": name, "path": path, "url": url, "commit": commit}
        for name, (path, url, commit) in sorted(submodules.items())
    ]
    compare_inventory("root_bindings", receipt["root_bindings"], expected_bindings)
    for name, (_path, _url, commit) in submodules.items():
        if receipt["repositories"][name] != commit:
            fail(
                f"repositories.{name}.commit={receipt['repositories'][name]} does not match root gitlink {commit}"
            )

    surfaces = scan_constellation(
        repo_root, root_commit, receipt["repositories"], receipt["exclusions"]
    )
    edges = derive_direct_edges(surfaces, receipt["repositories"])
    validate_generation_graph(edges, receipt["repositories"])
    validate_resolutions(surfaces, receipt["repositories"])
    anchors = required_anchors(edges, receipt["repositories"])
    verify_local_objects(repo_root, surfaces, edges, receipt["repositories"])
    if verify_remote:
        verify_remote_main(receipt["repositories"], root_commit=root_commit)

    if print_observed:
        print(
            json.dumps(
                {"surfaces": surfaces, "direct_edges": edges, "anchors": anchors},
                indent=2,
                sort_keys=True,
            )
        )
        return surfaces, edges, anchors

    compare_inventory("surfaces", receipt["surfaces"], surfaces)
    compare_inventory("direct_edges", receipt["direct_edges"], edges)
    compare_inventory("anchors", receipt["anchors"], anchors)
    return surfaces, edges, anchors


# ---------------------------------------------------------------------------
# SELFTEST — mutation-prove that this gate can still REFUSE, and that it judges
# the revision it was POINTED AT rather than the clone's HEAD.
#
# The repair this exercises traded one failure mode for another if done
# carelessly: a gate that resolves its policy somewhere more convenient can go
# green by looking at the wrong thing, which is strictly worse than the red it
# replaced.  So every assertion below is stated in BOTH directions on the SAME
# synthetic constellation — the green revision must pass and the red revision
# must fail, through each selector — and a selector that judged HEAD regardless
# would fail half of them whichever way HEAD pointed.
#
# It builds a complete nine-repository constellation in a tmpdir rather than
# probing the real one, because the real one is a moving target: measured
# 2026-08-29, `origin/main` is itself incoherent (`ay` and `trust-wp` pin
# `trust-ir` revisions on lines no terminal contains), so a probe against it can
# only ever watch this gate say no.
# ---------------------------------------------------------------------------
# A lock alone yields nothing: `scan_constellation` derives lock authority from
# the MANIFEST that declares a first-party git dependency and only then consults
# the nearest lock, so the fixture must carry both — which is also the shape the
# real finding takes.
SELFTEST_MANIFEST = """[package]
name = "ay-selftest"
version = "0.1.0"
edition = "2021"

[dependencies]
trust-ir = {{ git = "{url}", rev = "{rev}" }}
"""

SELFTEST_LOCK = """version = 3

[[package]]
name = "ay-selftest"
version = "0.1.0"
dependencies = [
 "trust-ir",
]

[[package]]
name = "trust-ir"
version = "0.8.0"
source = "git+{url}?rev={rev}#{rev}"
"""


def _st_run(repo: Path, args: Sequence[str]) -> str:
    completed = subprocess.run(
        [
            "git",
            "-C",
            str(repo),
            "-c",
            "user.name=trust selftest",
            "-c",
            "user.email=selftest@invalid",
            "-c",
            "commit.gpgsign=false",
            *args,
        ],
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )
    if completed.returncode != 0:
        detail = (completed.stderr or completed.stdout).decode("utf-8", "replace").strip()
        raise SystemExit(f"selftest git failure: git {' '.join(args)}: {detail}")
    return completed.stdout.decode("utf-8", "replace").strip()


def _st_sibling(root: Path, name: str, files: dict[str, str], message: str) -> str:
    checkout = root / SUBMODULES[name][0]
    checkout.mkdir(parents=True, exist_ok=True)
    if not (checkout / ".git").exists():
        _st_run(checkout, ["init", "-q", "-b", "main"])
    for relative, content in files.items():
        destination = checkout / relative
        destination.parent.mkdir(parents=True, exist_ok=True)
        destination.write_text(content, encoding="utf-8")
    _st_run(checkout, ["add", "-A"])
    _st_run(checkout, ["commit", "-q", "--no-verify", "-m", message])
    return _st_run(checkout, ["rev-parse", "HEAD"])


def _st_root_commit(root: Path, pins: dict[str, str], policy: str | None, message: str) -> str:
    gitmodules = "".join(
        f'[submodule "{path}"]\n\tpath = {path}\n\turl = {url}\n'
        for _name, (path, url) in sorted(SUBMODULES.items(), key=lambda row: row[1][0])
    )
    (root / ".gitmodules").write_text(gitmodules, encoding="utf-8")
    _st_run(root, ["add", "--", ".gitmodules"])
    policy_file = root / EXCLUSIONS_PATH
    policy_file.parent.mkdir(parents=True, exist_ok=True)
    if policy is None:
        if policy_file.exists():
            policy_file.unlink()
            _st_run(root, ["rm", "-q", "--cached", "--", EXCLUSIONS_PATH])
    else:
        policy_file.write_text(policy, encoding="utf-8")
        _st_run(root, ["add", "--", EXCLUSIONS_PATH])
    for name, commit in sorted(pins.items()):
        _st_run(root, ["update-index", "--add", "--cacheinfo", f"160000,{commit},{SUBMODULES[name][0]}"])
    _st_run(root, ["commit", "-q", "--no-verify", "-m", message])
    return _st_run(root, ["rev-parse", "HEAD"])


def _st_judge(root: Path, argv: Sequence[str], pushed: str | None) -> tuple[int, str]:
    """Run the real CLI in-process and return (exit code, everything it printed)."""
    import contextlib
    import io

    saved = os.environ.get(PUSH_REFS_ENV)
    if pushed is None:
        os.environ.pop(PUSH_REFS_ENV, None)
    else:
        os.environ[PUSH_REFS_ENV] = pushed
    out, err = io.StringIO(), io.StringIO()
    try:
        with contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
            code = main(["--repo-root", str(root), *argv])
    finally:
        os.environ.pop(PUSH_REFS_ENV, None)
        if saved is not None:
            os.environ[PUSH_REFS_ENV] = saved
    return code, out.getvalue() + err.getvalue()


# `validate_ny_identity_bundle` demands a seven-surface Clean proof-identity
# bundle in `ny`, agreeing on one Clean revision, before any assertion below is
# reached. Hand-writing those seven files would mirror four scanners' regexes
# into this function, where they would rot silently and the selftest would go
# green on a fixture that no longer resembles the thing it certifies. So they
# are COPIED from the real `ny` checkout with the Clean revision they name
# rewritten to the synthetic `clean` head — real formats, synthetic identity.
#
# An object-shared CLONE of `ny` was tried first and is wrong: a real sibling
# carries nested first-party gitlinks, and `validate_nested_submodules` then
# resolves them against the synthetic siblings, which do not have those objects.
# Copying the seven files into a from-scratch repo keeps the fixture free of
# nested pins, which is what makes the constellation controllable at all.
def _st_ny_identity(source_root: Path, clean_head: str) -> dict[str, str]:
    origin = source_root / SUBMODULES["ny"][0]
    files: dict[str, str] = {}
    for relative in sorted(NY_IDENTITY_PATHS):
        candidate = origin / relative
        if not candidate.is_file():
            raise SystemExit(
                f"SELFTEST INCONCLUSIVE: cannot read {relative} from {origin}.\n"
                "  The synthetic constellation copies ny's Clean proof-identity bundle so\n"
                "  its seven surfaces stay in step with the four scanners that read them.\n"
                "  Options:\n"
                "    * git submodule update --init first-party/ny\n"
                "    * bash scripts/submodule_sync.sh --restore\n"
                "  Refusing to report a pass or a failure from an unbuilt fixture."
            )
        files[relative] = candidate.read_text(encoding="utf-8")
    provenance = files["crates/ny-cert/proofs/lean/PROVENANCE.md"]
    match = re.search(r"^revision:\s*([0-9a-f]{40})\s*$", provenance, flags=re.MULTILINE)
    if match is None:
        raise SystemExit(
            "SELFTEST INCONCLUSIVE: ny's PROVENANCE.md declares no 40-hex `revision:`.\n"
            "  The fixture rewrites that revision to the synthetic clean head; without it\n"
            "  the seven surfaces would name a Clean commit the fixture does not contain."
        )
    return {path: text.replace(match.group(1), clean_head) for path, text in files.items()}


def selftest() -> int:
    import tempfile

    failures: list[str] = []

    def check(label: str, condition: bool, detail: str = "") -> None:
        if condition:
            print(f"  ok   {label}")
        else:
            print(f"  FAIL {label}{(' — ' + detail) if detail else ''}")
            failures.append(label)

    print("dependency-constellation gate selftest:")
    source_root = Path(
        subprocess.run(
            ["git", "-C", str(Path(__file__).resolve().parent), "rev-parse", "--show-toplevel"],
            stdout=subprocess.PIPE,
            stderr=subprocess.DEVNULL,
            check=False,
        ).stdout.decode("utf-8", "replace").strip()
        or "."
    )
    with tempfile.TemporaryDirectory(prefix="trust-constellation-selftest-") as raw:
        root = Path(raw).resolve() / "trust"
        root.mkdir(parents=True)
        _st_run(root, ["init", "-q", "-b", "main"])

        pins: dict[str, str] = {}
        for name in sorted(SUBMODULES):
            pins[name] = _st_sibling(root, name, {"README.md": f"{name}\n"}, f"{name} base")
        # ny's seven Clean surfaces must name a revision `clean` actually holds;
        # naming clean's head makes the reference terminal, so the fixture's
        # coherence never depends on clean's real history.
        pins["ny"] = _st_sibling(
            root, "ny", _st_ny_identity(source_root, pins["clean"]), "ny Clean proof identity"
        )

        # A trust-ir commit that is NOT an ancestor of the pin: the exact shape
        # of the real finding this gate exists to catch.
        ir = root / SUBMODULES["trust-ir"][0]
        _st_run(ir, ["checkout", "-q", "-b", "divergent", "HEAD~0"])
        (ir / "divergent.txt").write_text("off the pinned line\n", encoding="utf-8")
        _st_run(ir, ["add", "-A"])
        _st_run(ir, ["commit", "-q", "--no-verify", "-m", "divergent"])
        divergent = _st_run(ir, ["rev-parse", "HEAD"])
        _st_run(ir, ["checkout", "-q", "main"])

        policy = json.dumps({"schema": EXCLUSIONS_SCHEMA, "exclusions": []}, indent=2) + "\n"
        _st_root_commit(root, pins, policy, "coherent pre-policy constellation")
        marker = root / TERMINAL_POLICY_MARKER_PATH
        marker.write_bytes(TERMINAL_POLICY_MARKER)
        _st_run(root, ["add", "--", TERMINAL_POLICY_MARKER_PATH])
        _st_run(
            root,
            ["commit", "-q", "--no-verify", "-m", "activate immutable terminal policy"],
        )
        good = _st_run(root, ["rev-parse", "HEAD"])

        pins_bad = dict(pins)
        pins_bad["ay"] = _st_sibling(
            root,
            "ay",
            {
                "Cargo.toml": SELFTEST_MANIFEST.format(
                    url=SUBMODULES["trust-ir"][1], rev=divergent
                ),
                "Cargo.lock": SELFTEST_LOCK.format(
                    url=SUBMODULES["trust-ir"][1], rev=divergent
                ),
            },
            "ay references a divergent trust-ir",
        )
        bad = _st_root_commit(root, pins_bad, policy, "incoherent constellation")

        no_policy = _st_root_commit(root, pins_bad, None, "policy deleted")
        # Leave the checkout on the LAST commit, so every --rev/--push-context
        # assertion below that names an earlier revision is also a statement
        # that HEAD was not what got judged.
        head = _st_run(root, ["rev-parse", "HEAD"])
        check("selftest fixture: HEAD is the policy-less revision", head == no_policy)

        derive = ["--derive-when-receipt-absent"]

        # 1. GREEN: a coherent constellation passes, at a revision that is NOT HEAD.
        code, text = _st_judge(root, ["--rev", good, *derive], None)
        check(
            "GREEN  --rev <coherent> passes while HEAD is incoherent",
            code == 0 and "DEPENDENCY CONSTELLATION OK" in text,
            f"exit {code}: {text.strip().splitlines()[:2]}",
        )

        # 2. RED: the same selector, pointed at the incoherent revision, refuses.
        code, text = _st_judge(root, ["--rev", bad, *derive], None)
        check(
            "RED    --rev <incoherent> refuses (divergent trust-ir reference)",
            code == 1 and "is not an ancestor of terminal" in text,
            f"exit {code}: {text.strip().splitlines()[:2]}",
        )

        # 3. The pre-push path judges the revision being PUSHED, not HEAD —
        #    proven in both directions so it cannot be passing by accident.
        code, text = _st_judge(root, ["--push-context", *derive], f"refs/heads/main {good} refs/heads/main {bad}")
        check(
            "GREEN  --push-context judges the pushed coherent revision",
            code == 0 and "SUBJECT: push (1 ref update(s))" in text,
            f"exit {code}: {text.strip().splitlines()[:2]}",
        )
        code, text = _st_judge(root, ["--push-context", *derive], f"refs/heads/main {bad} refs/heads/main {good}")
        check(
            "RED    --push-context judges the pushed incoherent revision",
            code == 1 and "is not an ancestor of terminal" in text,
            f"exit {code}: {text.strip().splitlines()[:2]}",
        )

        # 4. A deletion publishes no tree, so it must not be judged as one — and
        #    with nothing left to judge the subject WIDENS to HEAD rather than
        #    silently passing on an empty set.
        code, text = _st_judge(
            root, ["--push-context", *derive], f"refs/heads/main {'0' * 40} refs/heads/main {good}"
        )
        check(
            "RED    a push that only DELETES widens to HEAD, never passes vacuously",
            code == 1 and "no push in flight" not in text and "updates no ref" in text,
            f"exit {code}: {text.strip().splitlines()[:2]}",
        )

        # 5. UNSET means no push is in flight: widen to HEAD, the historical
        #    default. HEAD here has no policy, so this is also the fail-closed
        #    case — and its refusal must carry the fix (v7/D3).
        code, text = _st_judge(root, ["--push-context", *derive], None)
        check(
            f"RED    ${PUSH_REFS_ENV} unset widens to HEAD and says so",
            code == 1 and f"SUBJECT: HEAD (no push in flight; {PUSH_REFS_ENV} unset)" in text,
            f"exit {code}: {text.strip().splitlines()[:2]}",
        )
        check(
            "FIX    a policy that will not resolve names the revision and the options",
            "exclusion policy" in text
            and no_policy[:12] in text
            and "--push-context" in text
            and "--rev" in text,
            "the refusal did not carry revision + options",
        )

        # 6. The gate must not be satisfiable by pointing it at nothing.
        code, text = _st_judge(root, ["--rev", "refs/heads/does-not-exist", *derive], None)
        check(
            "RED    an unresolvable --rev refuses rather than falling back to HEAD",
            code == 1 and "does not name a commit" in text,
            f"exit {code}: {text.strip().splitlines()[:2]}",
        )

        # 7. --derive-when-receipt-absent must not be a way to pass: it removes
        #    the inventory comparison, never the coherence check. Assertion 2
        #    already carries it; this asserts the receipt-absent REFUSAL is the
        #    only thing it suppressed.
        code, text = _st_judge(root, ["--rev", good], None)
        check(
            "RED    without --derive-when-receipt-absent, an absent receipt refuses",
            code == 1 and "constellation receipt" in text and "--derive-when-receipt-absent" in text,
            f"exit {code}: {text.strip().splitlines()[:2]}",
        )

        # 8. RETIRED HISTORY IS ARCHIVABLE. A sha published where nothing can
        #    resolve it as the terminal state is not a landing candidate, so it
        #    is not judged as one — while the coherent main update in the SAME
        #    push still is. Proven together, because an exemption that also
        #    stopped judging main would pass this row by disabling the gate.
        code, text = _st_judge(
            root,
            ["--push-context", *derive],
            f"refs/heads/main {good} refs/heads/main {good}\n"
            f"{bad} {bad} refs/archive/2026-08-31/retired {'0' * 40}",
        )
        check(
            "GREEN  an archive ref is not judged, while main in the same push IS",
            code == 0
            and "not a terminal-state candidate, not judged: refs/archive/" in text
            and "SUBJECT: push (1 ref update(s))" in text,
            f"exit {code}: {text.strip().splitlines()[:3]}",
        )

        # 9. The exemption is scoped to the NAMESPACE, never to the sha: the
        #    very revision archived above is still refused at refs/heads/main.
        code, text = _st_judge(
            root, ["--push-context", *derive], f"{bad} {bad} refs/heads/main {good}"
        )
        check(
            "RED    the same sha pushed to refs/heads/main is still refused",
            code == 1 and "is not an ancestor of terminal" in text,
            f"exit {code}: {text.strip().splitlines()[:2]}",
        )

        # 10. An archive-only push must not pass VACUOUSLY. With every pushed
        #     ref exempt the subject widens to HEAD, exactly as a delete-only
        #     push does — the fixture's HEAD carries no policy, so it refuses.
        code, text = _st_judge(
            root,
            ["--push-context", *derive],
            f"{bad} {bad} refs/archive/2026-08-31/retired {'0' * 40}",
        )
        check(
            "RED    an archive-ONLY push widens to HEAD, never passes vacuously",
            code == 1 and "updates no ref" in text,
            f"exit {code}: {text.strip().splitlines()[:3]}",
        )

        # 11. The allowlist is a PREFIX on the remote ref and nothing looser. A
        #     branch merely NAMED archive/... lives under refs/heads/ and is an
        #     ordinary landing candidate; it must still be judged.
        code, text = _st_judge(
            root,
            ["--push-context", *derive],
            f"{bad} {bad} refs/heads/archive/2026-08-31/retired {'0' * 40}",
        )
        check(
            "RED    a lookalike refs/heads/archive/... branch is judged, not exempt",
            code == 1 and "is not an ancestor of terminal" in text,
            f"exit {code}: {text.strip().splitlines()[:2]}",
        )

    if failures:
        print(f"SELFTEST FAILED: {len(failures)} assertion(s): {failures}")
        return 1
    print("SELFTEST OK: the gate passes a coherent constellation, refuses an incoherent")
    print("one, and judges the revision it is pointed at rather than this clone's HEAD.")
    return 0


def parse_args(argv: Sequence[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--repo-root",
        type=Path,
        default=Path(__file__).resolve().parents[1],
        help="root Trust checkout (default: script parent)",
    )
    parser.add_argument(
        "--receipt-path",
        default=RECEIPT_PATH,
        help="committed receipt path relative to root (default: %(default)s)",
    )
    parser.add_argument(
        "--print-observed",
        action="store_true",
        help="print independently derived surfaces/edges/anchors without comparing those arrays",
    )
    generation = parser.add_mutually_exclusive_group()
    generation.add_argument(
        "--print-receipt",
        action="store_true",
        help=(
            "render untracked v3 evidence from committed, clean HEAD; any WP "
            "gitlink move after the immutable policy marker automatically enables "
            "terminal/remote mode"
        ),
    )
    generation.add_argument(
        "--write-receipt",
        action="store_true",
        help=(
            "atomically write untracked v3 evidence from committed, clean HEAD "
            "with the same marker-persistent terminal/remote upgrade as "
            "--print-receipt"
        ),
    )
    parser.add_argument(
        "--external-receipt-path",
        default=EXTERNAL_RECEIPT_PATH,
        help="untracked output used by --write-receipt (default: %(default)s)",
    )
    parser.add_argument(
        "--exclusions-path",
        default=EXCLUSIONS_PATH,
        help="committed exclusion-policy path used by receipt generation (default: %(default)s)",
    )
    parser.add_argument(
        "--verify-remote",
        action="store_true",
        help="also require Trust and every terminal dependency to equal canonical remote main (networked, non-mutating)",
    )
    parser.add_argument(
        "--require-wp-trust-anchor",
        action="store_true",
        help=(
            "terminal R1 mode: authenticate W1:spikes/DEPENDS.lock's Trust anchor "
            "and require R1 to be its direct WP-gitlink-only child; requires "
            "--verify-remote"
        ),
    )
    revision = parser.add_mutually_exclusive_group()
    revision.add_argument(
        "--rev",
        default=None,
        help="judge this commit-ish instead of HEAD; external receipt output still "
        "requires it to be the clean checked-out HEAD",
    )
    revision.add_argument(
        "--push-context",
        action="store_true",
        help=f"judge the revision(s) the push in flight would publish, read from "
        f"${PUSH_REFS_ENV}; with it unset the subject widens to HEAD",
    )
    parser.add_argument(
        "--selftest",
        action="store_true",
        help="mutation-prove on a synthetic nine-repository constellation that this gate "
        "still refuses, and that it judges the revision it is pointed at",
    )
    parser.add_argument(
        "--derive-when-receipt-absent",
        action="store_true",
        help="when --receipt-path is not committed at the judged revision, derive and "
        "validate the constellation from that revision instead of refusing (still "
        "refuses an incoherent constellation)",
    )
    return parser.parse_args(argv)


def main(argv: Sequence[str] | None = None) -> int:
    args = parse_args(sys.argv[1:] if argv is None else argv)
    if args.selftest:
        return selftest()
    try:
        repo_root = Path(
            run_git(args.repo_root, ["rev-parse", "--show-toplevel"])
            .decode("utf-8", "strict")
            .strip()
        )
        if (args.print_receipt or args.write_receipt) and args.print_observed:
            fail("--print-observed cannot be combined with receipt generation")
        generating = args.print_receipt or args.write_receipt
        if args.require_wp_trust_anchor and not generating:
            fail("--require-wp-trust-anchor requires --print-receipt or --write-receipt")
        if args.require_wp_trust_anchor and not args.verify_remote:
            fail(
                "--require-wp-trust-anchor also requires --verify-remote so R1 and W1 "
                "are authenticated as canonical remote main"
            )
        sources = select_sources(repo_root, args)
        if generating and len(sources) > 1:
            fail("external receipt generation judges one revision; a multi-ref push names several")
        for source, label in sources:
            judge_source(repo_root, args, source, label)
    except (AnchorError, OSError, UnicodeDecodeError) as error:
        print("DEPENDENCY CONSTELLATION FAILED:", file=sys.stderr)
        print(f"  - CONSTELLATION-INVALID  {error}", file=sys.stderr)
        # v7/D3: the refusal carries its own fix options when it has them.
        for line in getattr(error, "options", ()):
            print(f"    {line}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
