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
import os as _floor_os
import shutil as _floor_shutil
import sys as _floor_sys

# Trust: python floor, second half. `python3 check_dependency_cycle_anchor.py` reads the sh block above
# as a string, so an old `python3` (3.9 on macOS CommandLineTools) re-execs here.
if __name__ == "__main__" and _floor_sys.version_info < (3, 11):
    for _floor_candidate in ("python3.14", "python3.13", "python3.12", "python3.11"):
        _floor_path = _floor_shutil.which(_floor_candidate)
        if _floor_path:
            _floor_argv = [_floor_path, _floor_os.path.abspath(__file__), *_floor_sys.argv[1:]]
            _floor_os.execv(_floor_path, _floor_argv)
    _floor_sys.exit("check_dependency_cycle_anchor.py requires Python 3.11+ (tomllib); none found on PATH")
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
Constellation derivation is deterministic and offline except for ONE live
sample per judged revision: trust-wp's canonical remote ``main``, taken by a
config-isolated, non-mutating ``git ls-remote`` (P1 below), and, only when the
bound trust-wp store lacks a commit the judgement reads, one by-sha fetch of
those commits that writes no ref (``fetch_absent_trust_wp_objects``).  ``--verify-remote``
additionally requires Trust and every pin to be exactly canonical remote main.

THE REVISION IS SELECTED, NOT ASSUMED.  Every read in one judgement — receipt,
``.gitmodules``, gitlinks, exclusion policy, manifests, policy markers — is
taken at the same tree-ish, and which one is a choice:

    --rev REV        an explicit commit-ish
    --push-context   the revision(s) the push in flight would publish, read
                     from $TRUST_PUSHED_REFS (exported by scripts/hooks/pre-push)
    (neither)        HEAD; external generation additionally proves the index
                     and worktree equal that committed HEAD

``--derive-when-receipt-absent`` derives and validates from the judged revision
when no receipt is committed there, which is the same coherence check without
the inventory comparison.  It never weakens what counts as incoherent.

TRUSTWP TERMINAL POLICY v3 (2026-09-21, recorded in
docs/first-party-pin-ledger.md under "TrustWP forward publication policy v2",
amendment block).  ``first-party/trust-wp`` is the one sibling whose own
``spikes/DEPENDS.lock`` points back into this repository, so its gitlink gets
these rules on top of the cohort rule every sibling gets:

  P1  PRESERVATION FLOOR.  trust-wp remote ``main``, sampled live at every
      judging, must contain B ``1de995e192…`` (hence W0 ``e7c353690e…``).  The
      ancestry is read from the bound submodule's object store.  A TrustWP
      commit the judgement reads (this main, B, every judged move's ends) that
      the store lacks is first fetched BY SHA from the canonical URL, writing
      no ref (``fetch_absent_trust_wp_objects``, 2026-10-24); one still absent
      is a refusal that names the fetch.  This is the whole of what
      "published history is never rewritten" needs.
  P2  FORWARD OR CANONICAL PIN MOVES.  Every single-parent move X -> Y of the
      gitlink in the judged history since the v1 marker's activation is
      admissible iff (a) X is a raw ancestor of Y; or (b) Y is an
      ancestor-or-equal of trust-wp remote ``main`` and ``spikes/DEPENDS.lock``
      is byte-identical at X and Y (a re-anchoring onto the canonical line with
      unchanged bindings); or (c) it is a same-lock backward move restored by
      an immediate single-parent child.  Anything else is refused with X, Y and
      the clause that failed.  A marked merge may adopt one marked parent's
      binding when every other marked parent's is (a)- or (b)-admissible away
      from it.  Backward moves are otherwise ``fast.pin-regression``'s business.
  P3  BINDING COHERENCE — the same cohort rule as every other sibling.  At the
      pinned trust-wp commit ``spikes/DEPENDS.lock`` must parse (five rows,
      branch ``main``, 40-hex) and each row must be an ancestor-or-equal of the
      gitlink it names (the ``trust`` row: of the judged Trust commit).
  P4  NO TERMINAL STATE.  ``.trust-terminal-policy-v3`` must be present and
      byte-exact at the judged revision; an edited or deleted copy anywhere in
      the judged history is refused.  The v1 and v2 markers stay as history: the
      v1 marker still names where the judged history begins, the v2 marker is
      only accepted as its historical ``state=pre-v2`` bytes, and an ``armed``
      v2 marker anywhere in the judged history is refused outright.  There is
      no R0/W1/R1, no Armed/Terminal state and no terminal claim.

Everything the v1/v2 terminal cut carried is DELETED, not dormant: the external
receipt (``trust.constellation.first-party.v3``) no longer has a
``wp_trust_anchor`` member at all (it was ``null`` outside a terminal cut and
never tracked), ``--require-wp-trust-anchor`` is gone, and a ``refs/heads/main``
push is judged like any other push (no prospective old-main authentication).
"""

import argparse
import configparser
import fnmatch
import hashlib
import json
import os
import posixpath
import re
import subprocess
import sys
import tempfile
from pathlib import Path, PurePosixPath
from typing import Any, BinaryIO, NoReturn, Sequence
from urllib.parse import parse_qs, unquote, urlsplit, urlunsplit

sys.path.insert(0, str(Path(__file__).resolve().parent / "lib"))
import remote_tips as rt

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
# The v1 marker (2026-08-29) names where the judged TrustWP history BEGINS: the
# gitlink moves judged by P2 are those on the marked subgraph since its unique
# activation.  Its bytes are immutable history.
TERMINAL_POLICY_MARKER_PATH = ".trust-terminal-policy-v1"
TERMINAL_POLICY_MARKER = (
    b"trust.constellation.terminal-policy.v1\n"
    b"policy=trust-wp-root-cycle\n"
)
# The v2 marker (2026-09-02) is history under v3.  The checker reads it only to
# refuse anything but its historical pre-v2 bytes: an `armed` v2 marker is the
# state machine the 2026-09-21 ruling deleted, and is refused outright (P4).
TERMINAL_POLICY_V2_MARKER_PATH = ".trust-terminal-policy-v2"
TERMINAL_POLICY_V2_PRE_MARKER = (
    b"trust.constellation.terminal-policy.v2\n"
    b"state=pre-v2\n"
    b"policy=trust-wp-root-cycle-forward\n"
    b"w0=e7c353690e1b58a4e830edc9facb0e4396164585\n"
    b"preservation-floor=1de995e192aabec74646d4d53642df05fa59466f\n"
)
# W0 is the frozen pin the v1/v2 policies were written against; B is the
# published floor every later TrustWP main must contain (P1).  Both are ratified
# constants of the 2026-09-21 ruling and are spelled into the v3 marker.
TRUST_WP_W0 = "e7c353690e1b58a4e830edc9facb0e4396164585"
TRUST_WP_PRESERVATION_FLOOR = "1de995e192aabec74646d4d53642df05fa59466f"
# Three pushed merges that recorded a TrustWP binding neither marked parent
# carried, landed while no push lane judged v3 (docs/DECISION_QUEUE.md
# TRUSTWP-MERGE-MINT-ADMITTED).  Pushed history is not rewritten, so each EXACT
# (merge, binding) pair is judged as a merge that adopted that binding: every
# marked parent's binding must still be retained by it, through (a) or (b).
# Any other merge that mints, including one of these with another binding or
# another merge with one of these bindings, is still refused.
TRUST_WP_ADMITTED_MERGE_MINTS = {
    "543a69d86babc39175a31b6d8337695f4b6fce48": "af8bad3fed08d92fcf94542a75391bc925901997",
    "7385559b83501afe7ce0e4a2e0f21725e6791b5b": "2605e3c0d457f6f4f23058752857b5ede926ecc7",
    "6e82620248f35f01c5c01b7e59155a17270b5380": "889a9db3c560e9033114e20bbb21ecd2da88f2bf",
}
TERMINAL_POLICY_V3_MARKER_PATH = ".trust-terminal-policy-v3"
TERMINAL_POLICY_V3_POLICY_ID = "trust.constellation.terminal-policy.v3"


def render_terminal_policy_v3_marker(w0: str, preservation_floor: str) -> bytes:
    """The one canonical v3 marker: every row fixed by the 2026-09-21 ruling."""
    return (
        f"{TERMINAL_POLICY_V3_POLICY_ID}\n"
        "policy=trust-wp-cohort-forward\n"
        "supersedes=trust-wp-root-cycle-forward\n"
        f"w0={w0}\n"
        f"preservation-floor={preservation_floor}\n"
        "ruled=2026-09-21\n"
    ).encode("ascii")


TERMINAL_POLICY_V3_MARKER = render_terminal_policy_v3_marker(
    TRUST_WP_W0, TRUST_WP_PRESERVATION_FLOOR
)
TERMINAL_POLICY_HISTORY_LIMIT = 100_000
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


class HistoryFinding(AnchorError):
    """Refusals that are properties of the judged HISTORY alone, all of them.

    A history finding is recorded only where the refused fact is read from
    committed objects (and, for P2's clause (b), the one live trust-wp main
    sample), never where an object, a remote or a host could not be read.  The
    same history judged from any clone gives the same messages, so ``main``
    prints each as a ``FINDING:`` line, which the pre-push hook compares
    between a push and its destination (INHERITED-RED, docs/DECISION_QUEUE.md).
    Every other refusal prints none, so the hook can never take an unreadable
    store for a red the destination already has.

    THE SET IS COMPLETE OR IT SAYS SO (2026-10-25, docs/DECISION_QUEUE.md
    CONSTELLATION-ALL-FINDINGS).  A history finding no longer stops the
    judgement: the walk records it and goes on, so a red destination's finding
    can never hide a refusal the push adds behind it (until then the gate
    stopped at its first refusal and printed that one key as the complete set,
    so a push adding a P2 move, a later-sorting mint or any later check's red
    to a red main was graded INHERITED).  ``main`` prints ``FINDINGS:
    complete`` only when every check of every judged revision ran to its end
    and every refusal was a history finding.
    """

    def __init__(self, messages: Sequence[str]) -> None:
        super().__init__("\n".join(messages))
        self.findings = list(messages)


def fail(message: str) -> NoReturn:
    raise AnchorError(message)


def finding_key(message: str) -> str:
    """The one-line ``FINDING:`` key of a history finding's message."""
    return " | ".join(line.strip() for line in message.splitlines() if line.strip())


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


def remote_git_environment(ceiling: Path) -> dict[str, str]:
    """Return a config-isolated environment for canonical remote probes.

    In particular, ``url.*.insteadOf`` must not be able to redirect a named
    GitHub authority to an attacker-controlled repository.  A remote probe has
    no repository cwd and reads neither system nor user Git configuration.
    Config-selected credential helpers are deliberately absent from this
    transport process. GitHub authentication belongs to native Agh.
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


def require_regular_committed_authority(
    repo: Path, commit: str, path: str, label: str
) -> None:
    entry = committed_tree_entries(repo, commit).get(path)
    if entry is None:
        fail(f"{label} is not committed")
    mode, object_type, _oid = entry
    if object_type != "blob" or mode not in {"100644", "100755"}:
        fail(f"{label} must be a regular committed blob, not mode {mode} type {object_type}")


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


def parse_wp_depends_lock(raw: bytes) -> dict[str, str]:
    """Parse TrustWP's ``spikes/DEPENDS.lock`` without accepting aliases.

    The five-row shape is part of TrustWP's spike-suite reproducibility guard,
    and under v3 every row is a cohort binding judged by P3 (the ``trust`` row
    is the edge back into this repository).  Accepting a duplicate, unknown, or
    malformed row would make a binding ambiguous under a future parser or hand
    audit, so the shape is exact.
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


def git_blob_oid(content: bytes) -> str:
    """The SHA-1 object id Git assigns to ``content`` stored as a blob."""
    return hashlib.sha1(b"blob %d\0" % len(content) + content).hexdigest()


def parse_terminal_policy_v3(raw: bytes) -> None:
    """Accept only the canonical v3 marker bytes, naming the first difference.

    The marker carries no state and no variable field: every row is fixed by
    the 2026-09-21 ruling.  It is still read row by row rather than compared
    once, so a forged or edited marker is refused with the row that differs --
    duplicate, reordered, extra, short, uppercase, or non-terminated authority
    lands on a named row or on the row count -- and the byte comparison at the
    end is the round trip that closes anything the rows did not (the same
    strictness the v2 armed-marker parser applied).
    """
    try:
        text = raw.decode("ascii", "strict")
    except UnicodeDecodeError as error:
        fail(f"terminal-policy v3 marker is not ASCII: {error}")
    if not text.endswith("\n"):
        fail("terminal-policy v3 marker is not newline-terminated")
    rows = text[:-1].split("\n")
    expected_rows = TERMINAL_POLICY_V3_MARKER.decode("ascii")[:-1].split("\n")
    if len(rows) != len(expected_rows):
        fail(
            "terminal-policy v3 marker row count differs from canonical: "
            f"observed={len(rows)}, expected={len(expected_rows)}"
        )
    for index, (row, expected) in enumerate(zip(rows, expected_rows), start=1):
        if row != expected:
            fail(
                f"terminal-policy v3 marker row {index} differs from canonical: "
                f"observed={row!r}, expected={expected!r}"
            )
    if raw != TERMINAL_POLICY_V3_MARKER:
        fail("terminal-policy v3 marker differs from its canonical bytes")


def local_commit_type(checkout: Path, commit: str) -> str | None:
    """``cat-file -t`` under the authority environment; ``None`` when absent."""
    completed = subprocess.run(
        ["git", "-C", str(checkout), "cat-file", "-t", commit],
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        env=authority_git_environment(),
        check=False,
    )
    if completed.returncode != 0:
        return None
    return completed.stdout.decode("ascii", "replace").strip()


def local_is_ancestor(checkout: Path, ancestor: str, descendant: str) -> tuple[bool, str]:
    """``git merge-base --is-ancestor`` in one checkout's own object store.

    This is the cohort reading every sibling gets (``verify_local_objects``):
    containment through any parent.  Returns the verdict and any diagnostic.
    """
    if ancestor == descendant:
        return True, ""
    completed = subprocess.run(
        ["git", "-C", str(checkout), "merge-base", "--is-ancestor", ancestor, descendant],
        stdout=subprocess.DEVNULL,
        stderr=subprocess.PIPE,
        env=authority_git_environment(),
        check=False,
    )
    return completed.returncode == 0, completed.stderr.decode("utf-8", "replace").strip()


def validate_trust_wp_binding_coherence(
    repo_root: Path, root_commit: str, commits: dict[str, str]
) -> dict[str, str]:
    """P3: every ``spikes/DEPENDS.lock`` row is behind-or-at the pin it names.

    The lock at the PINNED trust-wp commit must parse, and each of its five
    rows must be an ancestor-or-equal of the corresponding root gitlink -- the
    ``trust`` row of the judged Trust commit itself -- read from that sibling's
    own object store exactly as the cohort rule reads every other referenced
    commit.  Equality is not required: siblings advance between trust-wp
    refreshes, and a row that is merely behind is coherent.  A row that is
    AHEAD of its gitlink, or off its line, is the incoherence this refuses.

    Each store is read with replacement refs, legacy grafts, shallow history
    and alternates refused (``require_unmodified_history_view``), as the
    trust-wp store is: a graft in ``.git/modules/first-party/<name>`` could
    otherwise make an ahead row read as an ancestor.
    """
    root_commit = require_sha(root_commit, "Trust binding-coherence root")
    wp_path = SUBMODULES["trust-wp"][0]
    wp_checkout = repo_root / wp_path
    pinned_wp = require_sha(commits["trust-wp"], f"{wp_path} gitlink")
    require_regular_committed_authority(
        wp_checkout,
        pinned_wp,
        WP_DEPENDS_PATH,
        f"trust-wp:{WP_DEPENDS_PATH} at the pinned TrustWP commit {pinned_wp}",
    )
    pins = parse_wp_depends_lock(committed_blob(wp_checkout, pinned_wp, WP_DEPENDS_PATH))
    for repository in sorted(WP_DEPENDS_REPOSITORIES):
        row = pins[repository]
        if repository == "trust":
            checkout = repo_root
            terminal = root_commit
            store = "the Trust checkout"
            subject = f"the judged Trust commit {root_commit}"
        else:
            checkout = repo_root / SUBMODULES[repository][0]
            terminal = commits[repository]
            store = SUBMODULES[repository][0]
            subject = f"the {store} gitlink {terminal}"
        require_unmodified_history_view(checkout, f"{repository} binding-coherence store")
        object_type = local_commit_type(checkout, row)
        if object_type != "commit":
            fail(
                f"trust-wp:{WP_DEPENDS_PATH} {repository} row {row} is not a local "
                f"commit object in {store}"
                + (f" (found {object_type})" if object_type else "")
                + " (P3 binding coherence)"
            )
        ancestor, detail = local_is_ancestor(checkout, row, terminal)
        if not ancestor:
            fail(
                f"trust-wp:{WP_DEPENDS_PATH} {repository} row {row} is not an "
                f"ancestor-or-equal of {subject} (P3 binding coherence: the row "
                "is ahead of, or off the line of, the pin it names)"
                + (f": {detail}" if detail else "")
            )
    return pins


def validate_trust_wp_policy(
    repo_root: Path,
    root_commit: str,
    commits: dict[str, str],
    wp_remote_main: str,
    findings: list[str] | None = None,
) -> dict[str, object]:
    """Judge ``first-party/trust-wp`` under terminal-policy v3: P1, P2 and P4.

    EVERY HISTORY FINDING, NOT THE FIRST (HistoryFinding).  A refusal that is
    a property of the history is recorded and the judgement goes on to its
    end.  With ``findings`` given, each distinct one is appended there as it is
    found and the call returns normally, so the caller can run its later checks
    and still print what was found if one of those fails; without it, the call
    raises one ``HistoryFinding`` carrying them all once the judgement is done.
    Any other refusal raises at once, as before.

    ``wp_remote_main`` is the live sample of trust-wp's canonical ``main``
    (``sample_trust_wp_remote_main``); everything else is read from literal
    local objects with replacement refs, grafts, shallow history, alternates
    and lazy fetch disabled, and every walk is bounded.

    WHERE THE JUDGED HISTORY BEGINS.  The v1 marker has one unique raw
    single-parent introduction in the complete ancestry DAG; that activation is
    where TrustWP gitlink moves start being judged.  It may propagate through a
    merge whose first parent is an older unmarked branch: every marked parent
    must descend from that same introduction, while every unmarked parent must
    publish no TrustWP binding the pre-activation history had not already
    published (``audit_inactive_parent``: each commit's binding is a raw
    parent's or one its own pre-activation ancestry carried, a restoration).  Deleting, editing, or ambiguously
    re-introducing the marker is refused exactly as before.

    THE MARKED SUBGRAPH DECIDES THE JUDGED BINDING, alone.  HEAD must be
    marked; every marked commit must descend through a marked parent; and the
    binding changes along the marked subgraph in exactly two shapes:

      * a ONE-PARENT marked commit that moves the gitlink X -> Y.  It is
        admissible (P2) iff
          (a) Y contains X in its raw ancestry (forward, through any parent --
              the reading ``fast.pin-regression`` gives every other gitlink);
          (b) Y is an ancestor-or-equal of trust-wp remote ``main`` and the
              committed ``spikes/DEPENDS.lock`` is byte-identical at X and Y
              -- a re-anchoring onto the canonical line with unchanged
              bindings (the ``8325008ba62`` shape, ``9cbcc2cb -> 684821d0``);
          (c) Y is a strict raw ancestor of X, the lock is byte-identical, and
              an immediate single-parent marked child of that root commit
              restores exactly X (the same-lock backward recovery, per root
              edge: a later identical rollback needs its own restoration).
        Anything else is refused, naming X, Y and which clause failed.  A
        side with no regular committed lock is never read as "identical".
      * a marked MERGE that adopts one marked parent's binding while every
        other marked parent's binding is (a)- or (b)-admissible away from it.
        That is the shape a merge-heavy main produces after any admissible
        move -- a branch forked before the move merged with main after it, in
        either direction.  A merge may not publish a binding no marked parent
        carried, and may not drop a binding that is not so advanced.

    By induction the judged revision therefore carries the pre-activation
    binding advanced only by admissible moves, whatever an unmarked lineage
    did.  Nothing here asks trust-wp a stricter question than the lane asks of
    ``ay`` or ``trust-mc``: forward is the cohort reading, (b) is the same
    "on canonical main" fact ``fast.submodule-remote-reachability`` publishes,
    and the lock's bindings are P3's cohort question.

    THE MARKERS (P4).  ``.trust-terminal-policy-v3`` must be present and
    byte-exact at the judged revision (a missing marker is a refusal that
    carries the fix; an edited one names the row) and may be neither edited
    nor deleted anywhere in the judged history.  ``.trust-terminal-policy-v2``
    is accepted only as its historical ``state=pre-v2`` bytes; an ``armed``
    v2 marker anywhere in the judged history is refused outright.

    THE FLOOR (P1).  trust-wp remote ``main`` must contain B.  The object must
    be present in the bound submodule's store (the refusal names the fetch);
    a main that does not contain B is rewritten published history.
    """
    require_unmodified_history_view(repo_root, "Trust terminal-policy history")
    root_commit = require_sha(root_commit, "Trust terminal-policy HEAD")
    terminal_wp = require_sha(
        commits["trust-wp"], "Trust terminal-policy current TrustWP binding"
    )
    wp_remote_main = require_sha(wp_remote_main, "trust-wp remote main")
    if (
        not isinstance(TERMINAL_POLICY_HISTORY_LIMIT, int)
        or isinstance(TERMINAL_POLICY_HISTORY_LIMIT, bool)
        or TERMINAL_POLICY_HISTORY_LIMIT < 1
    ):
        fail("terminal-policy raw history walk limit must be a positive integer")
    v3_oid = git_blob_oid(TERMINAL_POLICY_V3_MARKER)
    pre_v2_oid = git_blob_oid(TERMINAL_POLICY_V2_PRE_MARKER)
    wp_path = SUBMODULES["trust-wp"][0]
    # This judgement's own findings, and the caller's sink (which may already
    # hold an earlier revision's): a finding both share is still this one's.
    found_here: list[str] = []
    sink: list[str] = found_here if findings is None else findings

    def history_finding(message: str) -> None:
        """Record one history refusal; the judgement goes on (HistoryFinding)."""
        if message not in found_here:
            found_here.append(message)
        if sink is not found_here and message not in sink:
            sink.append(message)

    with RawObjectReader(repo_root, "Trust terminal-policy history") as reader:
        # Per commit: tree, parents, v1 state, v1 entry, v3 state, v3 entry,
        # v2 state ("absent" or "pre"; anything else has already refused).
        snapshots: dict[
            str,
            tuple[str, list[str], str, tuple[str, str] | None, str, tuple[str, str] | None, str],
        ] = {}
        marker_oid: str | None = None

        def refuse_non_historical_v2_marker(commit: str, tree: str, label: str) -> str:
            entry = raw_tree_path_entry(
                reader, tree, TERMINAL_POLICY_V2_MARKER_PATH, f"{label} v2 marker"
            )
            if entry is None:
                return "absent"
            if entry == ("100644", pre_v2_oid):
                return "pre"
            mode, oid = entry
            raw = b""
            if mode in {"100644", "100755"}:
                raw = reader.read(oid, "blob", f"{label} v2 marker")
            if raw.startswith(
                b"trust.constellation.terminal-policy.v2\nstate=armed\n"
            ):
                fail(
                    f"Trust terminal-policy v2 marker at {commit} is ARMED; the v2 "
                    "Armed/Terminal state machine is superseded by v3 and an armed "
                    "v2 marker is refused outright (P4, ruling 2026-09-21)"
                )
            fail(
                f"Trust terminal-policy v2 marker at {commit} is not the historical "
                f"pre-v2 bytes: entry={entry}; under v3 the v2 marker is history and "
                "may only be carried unedited (P4)"
            )

        def snapshot(
            commit: str, label: str
        ) -> tuple[str, list[str], str, tuple[str, str] | None, str, tuple[str, str] | None, str]:
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
            v2_state = refuse_non_historical_v2_marker(commit, tree, label)
            v3_entry = raw_tree_path_entry(
                reader, tree, TERMINAL_POLICY_V3_MARKER_PATH, f"{label} v3 marker"
            )
            if v3_entry is None:
                v3_state = "absent"
            elif v3_entry == ("100644", v3_oid):
                v3_state = "exact"
            else:
                v3_state = "invalid"
            cached = (tree, parents, marker_state, marker_entry, v3_state, v3_entry, v2_state)
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
        head_v3 = raw_tree_path_entry(
            reader,
            head_tree,
            TERMINAL_POLICY_V3_MARKER_PATH,
            "Trust terminal-policy v3 HEAD marker",
        )
        if head_v3 is None:
            raise UnresolvableAtRevision(
                f"Trust terminal-policy v3 marker {TERMINAL_POLICY_V3_MARKER_PATH!r} "
                f"is missing at the judged revision {root_commit}; v3 governs every "
                "judging since the 2026-09-21 ruling (docs/first-party-pin-ledger.md) "
                "and there is no pre-v3 lane to fall back to",
                [
                    "Options:",
                    "  * judging a push: --push-context judges the revision being PUSHED;",
                    "      a topic that predates v3 must merge main first",
                    "  * judging a named revision: --rev origin/main (or any commit",
                    "      carrying the marker)",
                    "  * this clone's HEAD is stale: git fetch origin, then compare",
                    f"      git cat-file -t HEAD:{TERMINAL_POLICY_V3_MARKER_PATH}",
                    f"      git cat-file -t origin/main:{TERMINAL_POLICY_V3_MARKER_PATH}",
                ],
            )
        head_v3_mode, head_v3_oid = head_v3
        if head_v3_mode != "100644":
            fail(
                "Trust terminal-policy v3 marker must be a non-executable regular "
                f"blob (mode 100644), not mode {head_v3_mode}"
            )
        parse_terminal_policy_v3(
            reader.read(head_v3_oid, "blob", "Trust terminal-policy v3 HEAD marker")
        )
        head_v2 = refuse_non_historical_v2_marker(
            root_commit, head_tree, "Trust terminal-policy HEAD"
        )
        snapshots[root_commit] = (
            head_tree,
            head_parents,
            "exact",
            head_marker,
            "exact",
            head_v3,
            head_v2,
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
            _tree, parents, _state, _entry, _v3, _v3_entry, _v2 = snapshot(
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
        invalid_v3 = sorted(
            (commit, snapshots[commit][5])
            for commit in visited
            if snapshots[commit][4] == "invalid"
        )
        if invalid_v3:
            fail(
                "Trust terminal-policy v3 raw DAG contains a forged or edited "
                f"marker: commit={invalid_v3[0][0]}, entry={invalid_v3[0][1]} (P4)"
            )

        introductions: list[str] = []
        for commit in sorted(visited):
            _tree, parents, state, _entry, v3_state, _v3_entry, v2_state = snapshots[commit]
            parent_states = [snapshots[parent][2] for parent in parents]
            if v3_state == "absent":
                v3_marked_parents = [
                    parent for parent in parents if snapshots[parent][4] == "exact"
                ]
                if v3_marked_parents:
                    fail(
                        "Trust terminal-policy v3 marker was deleted on a raw DAG "
                        f"edge: child={commit}, marked_parents={v3_marked_parents} (P4)"
                    )
            if v2_state == "absent":
                # The v2 marker stays in the tree unedited as history (P4);
                # deleting it is refused exactly as deleting v1 or v3 is, and
                # re-adding it later does not launder the edge.
                v2_marked_parents = [
                    parent for parent in parents if snapshots[parent][6] == "pre"
                ]
                if v2_marked_parents:
                    fail(
                        "Trust terminal-policy v2 marker was deleted on a raw DAG "
                        f"edge: child={commit}, marked_parents={v2_marked_parents}; "
                        "under v3 the v2 marker is history and stays in the tree "
                        "unedited (P4)"
                    )
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
        _activation_tree, activation_parents, _state, _entry, _v3, _v3_entry, _v2 = snapshots[
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

        published_cache: dict[str, str | None] = {}

        def preactivation_published(side_child: str, child_wp: str) -> bool:
            """True iff a PRE-ACTIVATION raw ancestor of ``side_child`` carried ``child_wp``.

            A commit that RESTORES a binding its own pre-activation ancestry
            already published introduces nothing the regime never saw, so it is
            no mint (2026-10-24, docs/DECISION_QUEUE.md CONSTELLATION-RESTORE).
            The search is confined to ``side_child``'s own raw ancestry
            intersected with the pre-activation history: a binding seen only on
            a parallel pre-activation line, only on the marked line after
            activation, or nowhere at all still mints.  It runs only for a
            commit that failed the parent test, nearest ancestors first, so a
            restoration is found in a few tree reads; a refusal reads every
            pre-activation ancestor's binding once (cached across calls).
            """
            seen: set[str] = set()
            queue = list(snapshots[side_child][1])
            head = 0
            while head < len(queue):
                ancestor = queue[head]
                head += 1
                if ancestor in seen:
                    continue
                seen.add(ancestor)
                if ancestor not in snapshots:
                    fail(
                        "Trust terminal-policy raw DAG ancestry escaped the "
                        f"authenticated walk at {ancestor}"
                    )
                queue.extend(snapshots[ancestor][1])
                if ancestor not in preactivation_ancestors:
                    continue
                if ancestor not in published_cache:
                    entry = raw_tree_path_entry(
                        reader,
                        snapshots[ancestor][0],
                        WP_ROOT_DELTA_PATH,
                        f"Trust terminal-policy pre-activation ancestor {ancestor}",
                    )
                    published_cache[ancestor] = (
                        entry[1] if entry is not None and entry[0] == "160000" else None
                    )
                if published_cache[ancestor] == child_wp:
                    return True
            return False

        def audit_inactive_parent(child: str, inactive_parent: str) -> None:
            """Prove one unmarked merge parent MINTS no TrustWP binding.

            The frontier is where this parent's exclusive ancestry rejoins
            ancestry already present before activation.  The lineage must reach
            it -- an exclusive set that never rejoins is an unauthenticated
            import -- and no exclusive commit may publish a TrustWP gitlink that
            neither one of its own raw parents nor one of its own pre-activation
            raw ancestors already carried.  By induction from the frontier,
            every binding on the branch is one the pre-activation history had
            already published, so the branch cannot introduce a pin the regime
            never saw.  An authored move is refused by that rule directly, and
            so is a move later reverted, because the move commit mints on its
            own.

            RESTORATION IS NOT A MINT (2026-10-24, docs/DECISION_QUEUE.md
            CONSTELLATION-RESTORE).  Until then the test was the parent clause
            alone, which is stronger than the invariant above: a commit that
            goes BACK to a binding its own pre-activation ancestry had already
            published satisfies the invariant yet failed the test.  The one
            commit in Trust's history of that shape is the July `git stash`
            index commit 1b0fe79fc1 (parent 38cb00023f binds 5443d384; the
            index binds eb18c757, which R1 e58771678e, an ancestor of that
            parent, pinned), recorded on main by the preservation merge
            1fedcff19d; it made every push red.  The clause is confined to the
            commit's OWN ancestry (``preactivation_published``): a binding
            only a parallel pre-activation line pinned, only the marked line
            pinned after activation, or nobody pinned still mints, a parentless
            commit has no ancestry to restore from, and marked merges still
            only adopt.  MAIN-REDS-1's addendum (5d882bda04) allowed any binding
            some pre-activation commit carried; the merge that met it kept this
            narrower clause, which admits the same history and refuses the
            parallel-line shape that one admitted.

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
            def inactive_wp(commit: str, label: str) -> str | None:
                """The TrustWP binding an inactive-lineage commit publishes.

                None for a PARENTLESS commit whose tree has no
                ``first-party/trust-wp`` entry at all (2026-11-11,
                docs/DECISION_QUEUE.md CONSTELLATION-UNBOUND-ROOT): it carries
                no binding, so it can mint none. It contributes no binding as a
                parent either, so a child must still justify its own binding
                from its other parents or its own pre-activation ancestry, and
                it adds no frontier. The shape on main is a ``git stash -u``
                untracked-files commit, kept reachable by the preservation merge
                ``3ca41eb1a3``. A commit with a parent that drops the gitlink, or
                a parentless one that carries any entry at that path, is still
                refused.
                """
                tree, parents = snapshots[commit][0], snapshots[commit][1]
                if not parents and raw_tree_path_entry(reader, tree, WP_ROOT_DELTA_PATH, label) is None:
                    return None
                return commit_wp(commit, label)

            inactive_ancestors = ancestors(inactive_parent)
            exclusive = inactive_ancestors - preactivation_ancestors
            if not exclusive:
                frontier = {inactive_parent}
            else:
                frontier: set[str] = set()
                for side_child in sorted(exclusive):
                    if snapshots[side_child][2] != "absent":
                        history_finding(
                            "Trust terminal-policy inactive merge lineage carries "
                            f"marker state at {side_child}"
                        )
                    child_wp = inactive_wp(
                        side_child,
                        f"Trust terminal-policy inactive child {side_child}",
                    )
                    parent_wps: dict[str, str] = {}
                    for side_parent in snapshots[side_child][1]:
                        if side_parent in preactivation_ancestors:
                            frontier.add(side_parent)
                        elif side_parent not in exclusive:
                            history_finding(
                                "Trust terminal-policy inactive lineage has an "
                                f"unauthenticated ancestry frontier at {side_parent}"
                            )
                        parent_wp = inactive_wp(
                            side_parent,
                            f"Trust terminal-policy inactive parent {side_parent}",
                        )
                        if parent_wp is not None:
                            parent_wps[side_parent] = parent_wp
                    if child_wp is not None and child_wp not in parent_wps.values() and not preactivation_published(
                        side_child, child_wp
                    ):
                        # A parentless exclusive commit lands here too: it
                        # publishes a binding out of nowhere, which is the same
                        # defect with an emptier witness.
                        history_finding(
                            "Trust terminal-policy inactive merge lineage minted a "
                            "TrustWP gitlink no raw parent published: "
                            f"merge={child}, commit={side_child}, "
                            f"commit_wp={child_wp}, parent_wps={parent_wps}"
                        )
            # The frontier anchors the induction over the lineage's bindings. A
            # lineage that is one unbound root carries no binding, so there is
            # nothing to anchor: the untracked-files parent of a `git stash -u`
            # commit taken on the marked line (CONSTELLATION-UNBOUND-ROOT).
            # Every other lineage that never rejoins is still refused.
            unbound_root = exclusive == {inactive_parent} and inactive_wp(
                inactive_parent, f"Trust terminal-policy inactive parent {inactive_parent}"
            ) is None
            if not frontier and not unbound_root:
                history_finding(
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

        # Every binding change on the marked subgraph, as TrustWP
        # (before, after) pairs.  Whether a pair is admissible cannot be read
        # from the root tree; it is decided from TrustWP's own literal objects
        # once the marked subgraph has been authenticated in full.
        # Single-parent moves and merge adoptions are kept apart because the
        # recovery clause (c) exists for moves only.  The root child identity
        # is kept: restoring one occurrence must never clear a later occurrence
        # of the same WP (before, after) pair.
        moves: list[tuple[str, str, str, str]] = []
        adoptions: list[tuple[str, str, dict[str, str]]] = []
        activation_wp = commit_wp(
            activation_commit, "Trust terminal-policy activation child"
        )
        activation_parent_wp = commit_wp(
            activation_parent, "Trust terminal-policy activation parent"
        )
        if activation_wp != activation_parent_wp:
            moves.append(
                (
                    activation_commit,
                    activation_parent_wp,
                    activation_wp,
                    f"Trust terminal-policy activation {activation_commit}",
                )
            )

        for child in sorted(visited):
            _child_tree, parents, state, _entry, _v3, _v3_entry, _v2 = snapshots[child]
            if state != "exact" or child == activation_commit:
                continue
            marked_parents = [
                parent for parent in parents if snapshots[parent][2] == "exact"
            ]
            inactive_parents = [
                parent for parent in parents if snapshots[parent][2] == "absent"
            ]
            if not marked_parents:
                history_finding(
                    "Trust terminal-policy marked commit does not descend through "
                    f"a marked raw parent: commit={child}"
                )
                # No marked parent: no move or adoption to read here, but what
                # its unmarked parents carry is still judged, to the end.
                for inactive_parent in inactive_parents:
                    audit_inactive_parent(child, inactive_parent)
                continue
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
                if (
                    child_wp not in marked_parent_wps.values()
                    and TRUST_WP_ADMITTED_MERGE_MINTS.get(child) == child_wp
                ):
                    # An admitted pushed mint: every marked parent's binding
                    # differs from child_wp and is judged for retention below.
                    adoptions.append((child, child_wp, mismatched))
                elif child_wp not in marked_parent_wps.values():
                    # A merge may adopt a marked parent's binding, never mint
                    # one -- whatever an unmarked parent or a conflict
                    # resolution carried.  A new binding takes a one-parent
                    # commit, where it is judged as a move.
                    history_finding(
                        "Trust terminal-policy propagation merge did not retain "
                        "every marked-parent TrustWP binding: "
                        f"child={child}, child_wp={child_wp}, mismatched={mismatched} "
                        "(no marked parent published child_wp)"
                    )
                elif mismatched:
                    adoptions.append((child, child_wp, mismatched))
            elif next(iter(marked_parent_wps.values())) != child_wp:
                moves.append(
                    (
                        child,
                        next(iter(marked_parent_wps.values())),
                        child_wp,
                        f"Trust terminal-policy marked child {child}",
                    )
                )

            for inactive_parent in inactive_parents:
                audit_inactive_parent(child, inactive_parent)

        single_parent_children: dict[str, list[str]] = {}
        for child in sorted(visited):
            _tree, parents, state, _entry, _v3, _v3_entry, _v2 = snapshots[child]
            if state == "exact" and len(parents) == 1:
                single_parent_children.setdefault(parents[0], []).append(child)
        restorations = {
            child: [
                restoration
                for restoration in single_parent_children.get(child, [])
                if commit_wp(
                    restoration,
                    f"Trust terminal-policy restoration child {restoration}",
                ) == before
            ]
            for child, before, _after, _label in moves
        }

    # From here every fact is TrustWP's own: commits, parents, lock blobs and
    # ancestry, read as literal objects from the bound checkout.
    wp_checkout = repo_root / wp_path
    require_unmodified_history_view(
        wp_checkout, "Trust terminal-policy TrustWP binding history"
    )
    # Every TrustWP commit read below, fetched by sha first when this store
    # lacks it (fetch_absent_trust_wp_objects; no ref is written).
    wanted_wp = [wp_remote_main, TRUST_WP_PRESERVATION_FLOOR]
    for _child, before, after, _label in moves:
        wanted_wp.extend((before, after))
    for _child, adopted_wp, mismatched_wps in adoptions:
        wanted_wp.append(adopted_wp)
        wanted_wp.extend(mismatched_wps.values())
    _absent_wp, fetch_detail = fetch_absent_trust_wp_objects(
        wp_checkout, [require_sha(sha, "TrustWP commit to read") for sha in wanted_wp]
    )
    recovered: list[dict[str, object]] = []
    with RawObjectReader(
        wp_checkout, "Trust terminal-policy TrustWP binding history"
    ) as wp_reader:
        # P1: the preservation floor.
        if local_commit_type(wp_checkout, wp_remote_main) != "commit":
            fail(
                f"trust-wp remote main {wp_remote_main} is not present in the bound "
                f"{wp_path} object store, so the preservation floor cannot be "
                f"judged ({fetch_detail or 'no fetch was attempted'}); fetch it "
                f"first: git -C {wp_path} fetch origin main (P1)"
            )
        if not raw_commit_is_ancestor(
            wp_reader,
            TRUST_WP_PRESERVATION_FLOOR,
            wp_remote_main,
            "terminal-policy v3 preservation floor",
        ):
            fail(
                f"trust-wp remote main {wp_remote_main} does not contain the "
                f"preservation floor B {TRUST_WP_PRESERVATION_FLOOR} (hence W0 "
                f"{TRUST_WP_W0}): published TrustWP history has been rewritten, or "
                "the sampled main is not the canonical line (P1)"
            )

        lock_cache: dict[str, str | None] = {}

        def committed_lock(commit: str, label: str) -> str | None:
            """The lock blob id at one TrustWP commit; None unless a regular blob."""
            if commit in lock_cache:
                return lock_cache[commit]
            tree, _parents = parse_raw_commit(wp_reader, commit, label)
            entry = raw_tree_path_entry(
                wp_reader, tree, WP_DEPENDS_PATH, f"{label} {WP_DEPENDS_PATH}"
            )
            value: str | None = None
            if entry is not None and entry[0] in {"100644", "100755"}:
                value = entry[1]
            lock_cache[commit] = value
            return value

        def same_lock(x: str, y: str, label: str) -> bool:
            lock_x = committed_lock(x, f"{label} TrustWP {x}")
            lock_y = committed_lock(y, f"{label} TrustWP {y}")
            return lock_x is not None and lock_y is not None and lock_x == lock_y

        def describe_lock(commit: str, label: str) -> str:
            value = committed_lock(commit, f"{label} TrustWP {commit}")
            return "absent-or-non-regular" if value is None else value

        def forward(x: str, y: str, label: str) -> bool:
            return raw_commit_is_ancestor(wp_reader, x, y, f"{label} forward ancestry")

        def canonical(y: str, label: str) -> bool:
            return raw_commit_is_ancestor(
                wp_reader, y, wp_remote_main, f"{label} canonical-main ancestry"
            )

        for child, before, after, label in moves:
            before = require_sha(before, f"{label} TrustWP gitlink before the move")
            after = require_sha(after, f"{label} TrustWP gitlink after the move")
            if forward(before, after, label):
                continue
            lock_same = same_lock(before, after, label)
            if lock_same and canonical(after, label):
                continue
            backward = raw_commit_is_ancestor(
                wp_reader, after, before, f"{label} recovery reverse ancestry"
            )
            if lock_same and backward and restorations[child]:
                recovered.append(
                    {
                        "backward_root_commit": child,
                        "before_wp": before,
                        "after_wp": after,
                        "restoration_root_commits": restorations[child],
                        "regular_identical_depends_lock": True,
                    }
                )
                continue
            lock_note = (
                f"{WP_DEPENDS_PATH} differs (X={describe_lock(before, label)}, "
                f"Y={describe_lock(after, label)})"
            )
            clause_b = (
                lock_note
                if not lock_same
                else f"Y is not an ancestor-or-equal of trust-wp remote main {wp_remote_main}"
            )
            if not lock_same:
                clause_c = lock_note
            elif not backward:
                clause_c = "Y is not a strict raw ancestor of X"
            else:
                clause_c = (
                    f"no immediate single-parent child of {child} restores X"
                )
            history_finding(
                f"Trust terminal-policy v3 refuses the {wp_path} gitlink move at "
                f"{child}: X={before} -> Y={after}; "
                "(a) not forward: X is not a raw ancestor of Y; "
                f"(b) not a canonical re-anchoring: {clause_b}; "
                f"(c) not a recovered same-lock backward move: {clause_c} (P2)"
            )

        for child, child_wp, mismatched in adoptions:
            label = f"Trust terminal-policy propagation merge {child}"
            dropped = {
                parent: parent_wp
                for parent, parent_wp in mismatched.items()
                if not (
                    forward(parent_wp, child_wp, label)
                    or (
                        same_lock(parent_wp, child_wp, label)
                        and canonical(child_wp, label)
                    )
                )
            }
            if dropped:
                history_finding(
                    "Trust terminal-policy propagation merge did not retain "
                    "every marked-parent TrustWP binding: "
                    f"child={child}, child_wp={child_wp}, mismatched={dropped} "
                    "(retained means equal to child_wp, or admissibly advanced to "
                    "it: child_wp contains the parent's, or child_wp is on trust-wp "
                    f"remote main with the same {WP_DEPENDS_PATH})"
                )

    if found_here and findings is None:
        raise HistoryFinding(found_here)
    if recovered and not found_here:
        # Keep --print-receipt stdout machine-readable.  This is a diagnostic
        # of rechecked raw objects, never a receipt or alternative authority.
        print(
            "DEPENDENCY CONSTELLATION SAME-LOCK RECOVERY "
            + json.dumps(
                {"root_commit": root_commit, "recovered_edges": recovered},
                sort_keys=True,
            ),
            file=sys.stderr,
        )
    return {
        "activation_commit": activation_commit,
        "moves": len(moves),
        "recovered": len(recovered),
        "wp_remote_main": wp_remote_main,
        # Non-empty only when ``findings`` was given (otherwise it raised).
        "findings": list(found_here),
    }

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


def validate_external_receipt(value: object) -> dict[str, Any]:
    """Validate the untracked v3 evidence shape.

    V3 deliberately carries the concrete Trust commit instead of a
    self-referential sentinel.  It is therefore external evidence and cannot
    be made a tracked blob in the commit it authenticates.

    SCHEMA CHANGE (2026-09-21).  Receipts written before terminal-policy v3
    carried a ``wp_trust_anchor`` member -- ``null`` outside a terminal cut,
    and under the v2 cut extended with ``policy_version``,
    ``preservation_floor``, ``predecessor_commit`` and ``root_bindings``.  The
    cut is deleted, so the member is gone rather than left permanently null;
    the schema id is unchanged because no receipt of this shape is ever
    tracked or read back (it is printed, compared once, and discarded).
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

    legacy_value = {
        key: item for key, item in value.items() if key not in {"schema", "self"}
    }
    legacy_value.update(
        {
            "schema": SCHEMA,
            "self": {"repository": "trust", "commit": SELF_SENTINEL},
        }
    )
    normalized = validate_receipt(legacy_value)
    normalized["self_commit"] = self_commit
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
        ancestor, detail = local_is_ancestor(checkout, commit, terminal)
        if not ancestor:
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


def sample_remote_main(name: str, url: str) -> str:
    """Sample canonical main through the shared authenticated Agh inventory.

    Local fixtures retain the isolated Git probe. Neither route adopts caller
    configuration or substitutes a tracking ref for the actual live sample.
    """
    try:
        github = rt.github_repository(url) is not None
    except ValueError as error:
        fail(f"invalid canonical {name} remote: {error}")
    with tempfile.TemporaryDirectory(prefix="trust-remote-main-") as temporary:
        ceiling = Path(temporary)
        environment = remote_git_environment(ceiling)
        if github:
            store = ceiling / "witness.git"
            initialized = subprocess.run(
                ["git", "init", "--quiet", "--bare", "--template=", str(store)],
                cwd=temporary, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                env=environment, check=False,
            )
            if initialized.returncode != 0:
                detail = initialized.stderr.decode("utf-8", "replace").strip()
                fail(f"cannot prepare {name} remote type witnesses: {detail}")
            completed = rt.remote_refs(
                url, git_dir=store, env=environment, cwd=ceiling,
                timeout=rt.LS_REMOTE_TIMEOUT_S,
            )
            rows = completed.stdout.splitlines()
            # The shared reader validates the complete heads/pins inventory;
            # this policy still judges exactly its single canonical main.
            rows = [row for row in rows if row.partition("\t")[2] == "refs/heads/main"]
            detail = (completed.stderr or completed.stdout).strip()
        else:
            completed = subprocess.run(
                ["git", "ls-remote", "--exit-code", url, "refs/heads/main"],
                cwd=temporary, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                env=environment, check=False,
            )
            rows = completed.stdout.decode("ascii", "strict").splitlines()
            detail = (completed.stderr or completed.stdout).decode("utf-8", "replace").strip()
    if completed.returncode != 0:
        fail(f"cannot resolve {name} remote main at {url}: {detail}")
    if len(rows) != 1:
        fail(
            f"{name} remote main probe must return exactly one refs/heads/main row; "
            f"observed={rows}"
        )
    sha, separator, ref = rows[0].partition("\t")
    if separator != "\t" or ref != "refs/heads/main":
        fail(f"{name} remote main probe returned a malformed row: {rows[0]!r}")
    return require_sha(sha, f"{name} remote main")


def verify_one_remote_main(name: str, url: str, commit: str) -> None:
    observed = sample_remote_main(name, url)
    if observed != commit:
        fail(
            f"{name} terminal {commit} is not exactly remote main; "
            f"observed={[observed + chr(9) + 'refs/heads/main']}"
        )


def sample_trust_wp_remote_main() -> str:
    """The one live sample every judging takes: trust-wp's canonical main.

    P1 and P2(b) are stated against this value.  It is a separate function so
    the self-tests can replace exactly this network read and nothing else.
    """
    return sample_remote_main("trust-wp", SUBMODULES["trust-wp"][1])


def trust_wp_fetch_url() -> str:
    """Where absent TrustWP commits are fetched from, by sha: the canonical URL.

    A separate function so the self-tests point it at their own fixture
    remote; nothing else about the fetch is replaced.
    """
    return SUBMODULES["trust-wp"][1]


TRUST_WP_FETCH_TIMEOUT_S = 180
# What a server says when it will not serve a sha, as opposed to "I could not
# reach the server" (scripts/lib/remote_tips.py reads the same markers).
FETCH_REFUSAL_MARKERS = (
    "not our ref",
    "couldn't find remote ref",
    "no such remote ref",
    "unadvertised object",
)


def absent_commits(checkout: Path, shas: Sequence[str]) -> list[str]:
    """The subset of ``shas`` that ``checkout``'s own store does not hold as commits."""
    wanted = list(dict.fromkeys(shas))
    if not wanted:
        return []
    completed = subprocess.run(
        ["git", "-C", str(checkout), "cat-file", "--batch-check=%(objectname) %(objecttype)"],
        input="".join(f"{sha}\n" for sha in wanted).encode("ascii"),
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        env=authority_git_environment(),
        check=False,
    )
    held = set()
    for row in completed.stdout.decode("ascii", "replace").splitlines():
        fields = row.split()
        if len(fields) == 2 and fields[1] == "commit":
            held.add(fields[0])
    return [sha for sha in wanted if sha not in held]


def incomplete_trust_wp_sources(checkout: Path, shas: Sequence[str]) -> list[str]:
    """Source snapshots P1/P2 cannot yet read, including commit-only intake.

    A genuinely absent lock path stays a policy refusal. Missing Git objects
    along that path are acquisition failures, never proof that the path is absent.
    """
    wanted = list(dict.fromkeys(shas))
    for sha in wanted:
        require_sha(sha, "TrustWP source identity")
    missing = set(absent_commits(checkout, wanted))
    for sha in wanted:
        if sha in missing:
            continue
        entries = subprocess.run(
            ["git", "-C", str(checkout), "ls-tree", "-r", "-z", sha, "--", WP_DEPENDS_PATH],
            capture_output=True, env=authority_git_environment(), check=False,
        )
        if entries.returncode != 0:
            missing.add(sha)
            continue
        for entry in entries.stdout.split(b"\0"):
            if not entry:
                continue
            metadata, separator, _path = entry.partition(b"\t")
            fields = metadata.split()
            if separator != b"\t" or len(fields) != 3:
                fail("Git returned malformed TrustWP source inventory")
            available = subprocess.run(
                ["git", "-C", str(checkout), "cat-file", "-e", fields[2].decode("ascii")],
                capture_output=True, env=authority_git_environment(), check=False,
            )
            if available.returncode != 0:
                missing.add(sha)
    return [sha for sha in wanted if sha in missing]


def fetch_absent_trust_wp_objects(checkout: Path, shas: Sequence[str]) -> tuple[list[str], str]:
    """Acquire missing exact TrustWP source objects through native Agh.

    P1/P2 read DEPENDS.lock blobs, so commit-only ancestry is insufficient.
    The shared source intake preserves caller refs, HEAD and FETCH_HEAD and
    checks the requested commit and tree. Literal local fixtures keep their
    isolated Git route and the existing per-operation timeout.
    """
    absent = incomplete_trust_wp_sources(checkout, shas)
    if not absent:
        return [], ""
    url = trust_wp_fetch_url()
    details: list[str] = []
    try:
        github = rt.github_repository(url) is not None
    except ValueError as error:
        fail(f"invalid canonical trust-wp remote: {error}")
    with tempfile.TemporaryDirectory(prefix="trust-wp-fetch-") as temporary:
        ceiling = Path(temporary)
        environment = remote_git_environment(ceiling)
        if github:
            for sha in absent:
                completed = rt.fetch_exact_source(
                    url, checkout, sha, env=environment,
                    timeout=TRUST_WP_FETCH_TIMEOUT_S,
                )
                if completed.returncode != 0:
                    detail = (completed.stderr or completed.stdout).strip()
                    details.append(f"{sha[:12]}: {detail or f'Agh source intake exit {completed.returncode}'}")
        else:
            git_dir = decode_text(
                run_git(checkout, ["rev-parse", "--absolute-git-dir"]),
                "trust-wp absolute git dir",
            ).strip()

            def fetch(batch: Sequence[str]) -> tuple[int, str]:
                try:
                    completed = subprocess.run(
                        [
                            "git", "--git-dir", git_dir, "fetch", "--quiet",
                            "--no-write-fetch-head", "--no-tags", "--no-recurse-submodules",
                            "--no-prune", "--no-auto-maintenance", "--refmap=", url, *batch,
                        ],
                        cwd=temporary, stdin=subprocess.DEVNULL,
                        stdout=subprocess.PIPE, stderr=subprocess.PIPE, env=environment,
                        timeout=TRUST_WP_FETCH_TIMEOUT_S, check=False,
                    )
                except subprocess.TimeoutExpired:
                    return 124, f"timed out after {TRUST_WP_FETCH_TIMEOUT_S}s"
                detail = (completed.stderr or completed.stdout).decode("utf-8", "replace").strip()
                return completed.returncode, detail.splitlines()[-1] if detail else ""

            code, detail = fetch(absent)
            if code != 0 and len(absent) > 1 and any(
                marker in detail.lower() for marker in FETCH_REFUSAL_MARKERS
            ):
                for sha in incomplete_trust_wp_sources(checkout, absent):
                    one_code, one_detail = fetch([sha])
                    if one_code != 0:
                        details.append(f"{sha[:12]}: {one_detail}")
            elif code != 0:
                details.append(detail or f"git fetch exit {code}")
    still = incomplete_trust_wp_sources(checkout, absent)
    fetched = [sha for sha in absent if sha not in still]
    if fetched:
        print(
            f"trust-wp: fetched {len(fetched)} absent commit(s) by sha from {url} "
            f"(no ref, no FETCH_HEAD written): {', '.join(sha[:12] for sha in fetched)}",
            file=sys.stderr,
        )
    if github:
        for sha in still:
            if not any(detail.startswith(sha[:12] + ":") for detail in details):
                details.append(f"{sha[:12]}: complete source still unavailable after Agh source intake")
    summary = "; ".join(details)
    if still:
        summary = (
            f"a by-sha fetch from {url} did not bring {', '.join(sha[:12] for sha in still)}"
            + (f" ({summary})" if summary else "")
        )
    return absent, summary


def verify_remote_main(
    commits: dict[str, str], *, root_commit: str | None = None
) -> None:
    for name, commit in sorted(commits.items()):
        verify_one_remote_main(name, SUBMODULES[name][1], commit)
    if root_commit is not None:
        verify_one_remote_main("trust", ROOT_URL, root_commit)


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
    external_evidence: bool = True,
) -> dict[str, object]:
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
    require_external_receipt_untracked(repo_root, root_revision)
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
    if verify_remote:
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
    }
    validate_external_receipt(receipt)
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


def require_external_receipt_untracked(repo_root: Path, root_commit: str) -> None:
    entries = committed_tree_entries(repo_root, root_commit)
    if EXTERNAL_RECEIPT_PATH in entries:
        fail(
            "v3 constellation evidence must remain external/untracked; "
            f"tracked={[EXTERNAL_RECEIPT_PATH]}"
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
# always says which reading was taken. SET but publishing no terminal-state
# candidate (see below) judges the terminal state the push leaves in place —
# the destination's main — never nothing.
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
# is judged, and a missing remote ref is judged. And if filtering leaves nothing
# — an archive-only, pin-only or delete-only push — the subject is still never
# empty: it becomes the terminal state that push LEAVES IN PLACE, the
# destination's main as this clone last fetched it (`refs/remotes/<remote>/main`),
# so the exemption can only ever remove refs that were never terminal
# candidates, and can never be the reason a push passes.
#
# Why the destination's main and not this clone's HEAD. Until 2026-09-27 such a
# push widened to HEAD — which such a push does not publish, so the verdict
# depended only on what happened to be checked out. Archiving the CHECKED-OUT
# retired branch (`git push origin HEAD:refs/archive/<date>/<branch>`) was then
# refused on the very sha the exemption had just set aside, and deleting a
# remote branch was refused whenever the clone sat on a stale or WIP commit:
# the "judge HEAD regardless of what is pushed" pathology above, on an
# unquarantinable lane. The destination's main is what every consumer resolves
# the terminal state through, and such a push leaves it unchanged.
#
# The destination. The hook exports git's second pre-push argument as
# TRUST_PUSH_REMOTE, and git's second argument is the remote's URL, not its
# name; so the name is recovered by matching that value against this clone's
# `remote.<name>.url` / `remote.<name>.pushurl` (or taking it verbatim when it
# already IS a configured name), with `origin` when nothing matches.
#
# Two cases still widen to HEAD, so nothing passes on an empty or stale set:
# the destination's main does not resolve in this clone (never fetched, or no
# such remote), and the push DELETES the destination's main (`refs/heads/main`
# with an all-zero local sha) — the remote-tracking copy then names a main that
# will not survive the push, and judging it would judge a ghost.
# ---------------------------------------------------------------------------
PUSH_REFS_ENV = "TRUST_PUSHED_REFS"
PUSH_REMOTE_ENV = "TRUST_PUSH_REMOTE"
TERMINAL_MAIN_REF = "refs/heads/main"

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
    widens to its historical default.  An empty LIST means a push that
    publishes no terminal-state candidate (empty-but-set, or every line a
    deletion or a preservation-namespace ref); the caller then judges the
    terminal state that push leaves in place (``push_left_terminal_state``).
    Deletions publish no tree and are dropped; duplicate shas are judged once.

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


def push_deletes_terminal_main() -> bool:
    """Does the push in flight DELETE the destination's main?

    Fail-closed on shape: a deletion line (all-zero local sha) whose remote ref
    is missing counts, because it cannot be shown NOT to be main.
    """
    for line in os.environ.get(PUSH_REFS_ENV, "").splitlines():
        fields = line.split()
        if len(fields) < 2:
            continue
        local_sha = fields[1]
        remote_ref = fields[2] if len(fields) >= 3 else ""
        if set(local_sha) == {"0"} and remote_ref in ("", TERMINAL_MAIN_REF):
            return True
    return False


def push_destination_remote(repo_root: Path) -> tuple[str, str]:
    """(remote name, how it was found) for the push in flight.

    ``TRUST_PUSH_REMOTE`` carries git's second pre-push argument, which is the
    destination URL (the name is the first).  A value that is a configured
    remote NAME is taken as is; otherwise it is matched against every
    ``remote.<name>.url`` / ``remote.<name>.pushurl`` in this clone.  Several
    matches prefer ``origin``, else the first by name; none falls back to
    ``origin``.  Every outcome is reported, so the reading is never silent.
    """
    value = os.environ.get(PUSH_REMOTE_ENV, "").strip()
    if not value:
        return "origin", f"{PUSH_REMOTE_ENV} unset; assuming origin"
    listed = run_git(
        repo_root,
        ["config", "--null", "--get-regexp", r"^remote\..*\.(push)?url$"],
        check=False,
    ).decode("utf-8", "replace")
    names: set[str] = set()
    by_url: set[str] = set()
    for entry in listed.split("\0"):
        if not entry:
            continue
        key, _sep, url = entry.partition("\n")
        match = re.fullmatch(r"remote\.(.+)\.(?:push)?url", key)
        if match is None:
            continue
        names.add(match.group(1))
        if url == value:
            by_url.add(match.group(1))
    if value in names:
        return value, f"{PUSH_REMOTE_ENV} names remote {value!r}"
    if by_url:
        chosen = "origin" if "origin" in by_url else sorted(by_url)[0]
        return chosen, f"{PUSH_REMOTE_ENV} is the URL of remote {chosen!r}"
    return "origin", f"{PUSH_REMOTE_ENV} {value!r} matches no configured remote; assuming origin"


def push_left_terminal_state(repo_root: Path) -> tuple[str, str] | None:
    """The terminal state a push that publishes no candidate leaves in place.

    That is the destination's main as this clone last fetched it.  ``None``
    (after printing the reason) when it cannot stand for that state — the push
    deletes main, or the remote-tracking ref does not resolve — and the caller
    then widens to HEAD, so the subject is never empty.
    """
    if push_deletes_terminal_main():
        print(
            "SUBJECT: HEAD (push in flight publishes no terminal-state candidate and "
            f"DELETES {TERMINAL_MAIN_REF}; the remote-tracking main would not survive it)"
        )
        return None
    remote, how = push_destination_remote(repo_root)
    tracking = f"refs/remotes/{remote}/main"
    completed = subprocess.run(
        ["git", "-C", str(repo_root), "rev-parse", "--verify", "--quiet", f"{tracking}^{{commit}}"],
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        env=authority_git_environment(),
        check=False,
    )
    resolved = completed.stdout.decode("ascii", "replace").strip()
    if completed.returncode != 0 or not SHA_RE.match(resolved):
        print(
            "SUBJECT: HEAD (push in flight publishes no terminal-state candidate, and "
            f"{tracking} does not resolve in this clone; {how})"
        )
        return None
    print(
        f"SUBJECT: {remote}/main [{resolved[:12]}] (push in flight publishes no "
        f"terminal-state candidate; judging the terminal state it leaves in place; {how})"
    )
    return resolved, f"{remote}/main [{resolved[:12]}] (left in place by the push)"


def select_sources(repo_root: Path, args: argparse.Namespace) -> list[tuple[str, str]]:
    """Every (committed revision, human label) this invocation judges, in order."""
    if args.rev is not None:
        return [(rev_parse(repo_root, args.rev, "--rev"), f"--rev {args.rev}")]
    if args.push_context:
        pushed = pushed_revisions()
        if pushed is None:
            print(f"SUBJECT: HEAD (no push in flight; {PUSH_REFS_ENV} unset)")
        elif not pushed:
            # Set but yielding nothing: every line a deletion or a
            # preservation-namespace ref, or no ref updates at all. Such a push
            # publishes no terminal-state candidate, so what it leaves as the
            # terminal state is the destination's main — judge THAT, never an
            # empty set (which would PASS) and never this clone's HEAD (which
            # the push does not publish). HEAD only when that main is unknown.
            left = push_left_terminal_state(repo_root)
            if left is not None:
                return [left]
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


def judge_source(
    repo_root: Path,
    args: argparse.Namespace,
    source: str,
    label: str,
    findings: list[str],
) -> bool:
    """Validate the constellation at ONE commit; every read takes that one.

    A history finding (HistoryFinding) is appended to ``findings`` and every
    later check still runs; any other refusal raises.  A revision with a
    finding prints no OK line and writes no receipt.  Returns False only when a
    finding stopped a check short of its end (``--print-observed``, which
    compares nothing), so ``main`` withholds ``FINDINGS: complete``.
    """
    generating = args.print_receipt or args.write_receipt
    derived_only = False
    source_submodules = committed_submodules(repo_root, source)
    source_commits = {
        name: commit
        for name, (_path, _url, commit) in source_submodules.items()
    }
    # TrustWP terminal policy v3, once per judged revision and ahead of either
    # lane: the live trust-wp main sample (P1, P2b), the marker and move
    # judgement (P1, P2, P4), then the lock's cohort bindings (P3).
    wp_policy = validate_trust_wp_policy(
        repo_root, source, source_commits, sample_trust_wp_remote_main(), findings
    )
    found = bool(wp_policy["findings"])
    validate_trust_wp_binding_coherence(repo_root, source, source_commits)
    policy_line = (
        "  trust-wp terminal-policy v3: remote main "
        f"{str(wp_policy['wp_remote_main'])[:12]} contains B (P1); "
        f"{wp_policy['moves']} gitlink move(s) since v1 activation admissible"
        + (f", {wp_policy['recovered']} by same-lock recovery" if wp_policy["recovered"] else "")
        + f" (P2); {WP_DEPENDS_PATH} rows 5/5 ancestor-or-equal (P3); marker exact (P4)"
    )
    if not generating and args.derive_when_receipt_absent:
        # Presence is asked of the SAME revision every other read takes. The
        # shell conditional this replaced asked `test -f` of the WORKING TREE,
        # which is a third revision again and answers wrong in any clone whose
        # checkout differs from the revision under judgement.
        if committed_tree_entries(repo_root, source).get(args.receipt_path) is None:
            generating = True
            derived_only = True

    if generating:
        exclusions = load_exclusion_policy(repo_root, source, args.exclusions_path, label)
        receipt = derive_receipt(
            repo_root,
            source,
            exclusions,
            verify_remote=args.verify_remote,
            external_evidence=not derived_only,
        )
        if found:
            # Every check ran; a refused history prints no OK and writes
            # no receipt.
            return True
        rendered = render_receipt(receipt)
        if derived_only:
            suffix = " + REMOTE MAIN" if args.verify_remote else ""
            print(f"DEPENDENCY CONSTELLATION OK{suffix} ({label}; derived, no committed receipt)")
            print("  root gitlinks: 9/9 exact")
            print("  committed Cargo/Lake surfaces, direct edges, and generation cuts: exact")
            print(policy_line)
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
        return True

    if found and args.print_observed:
        # The observed inventory is a diagnostic of an accepted history; a
        # refused one stops here, so this judgement is not a complete one.
        return False
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
        if not found:
            print(f"DEPENDENCY CONSTELLATION OK{suffix} ({label})")
            print("  root gitlinks: 9/9 exact")
            print("  committed Cargo/Lake surfaces, direct edges, and generation cuts: exact")
            print(policy_line)
    return True


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


def _st_run(repo: Path, args: Sequence[str], stdin: bytes | None = None) -> str:
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
        input=stdin,
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


def _st_judge(
    root: Path, argv: Sequence[str], pushed: str | None, push_remote: str | None = None
) -> tuple[int, str]:
    """Run the real CLI in-process and return (exit code, everything it printed).

    Both push-context variables are set exactly as given (``None`` = unset) and
    restored afterwards, so the hook's own values, present when this selftest
    runs as a push-profile lane, never leak into a fixture judgement.
    """
    import contextlib
    import io

    wanted = {PUSH_REFS_ENV: pushed, PUSH_REMOTE_ENV: push_remote}
    saved = {name: os.environ.get(name) for name in wanted}
    for name, value in wanted.items():
        if value is None:
            os.environ.pop(name, None)
        else:
            os.environ[name] = value
    out, err = io.StringIO(), io.StringIO()
    try:
        with contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
            code = main(["--repo-root", str(root), *argv])
    finally:
        for name, value in saved.items():
            os.environ.pop(name, None)
            if value is not None:
                os.environ[name] = value
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
        # A genesis commit first: trust-wp's lock names a Trust commit, and P3
        # needs that row to be an ancestor of every judged revision.
        _st_run(root, ["commit", "-q", "--allow-empty", "--no-verify", "-m", "trust genesis"])
        genesis = _st_run(root, ["rev-parse", "HEAD"])

        pins: dict[str, str] = {}
        for name in sorted(SUBMODULES):
            if name == "trust-wp":
                continue
            pins[name] = _st_sibling(root, name, {"README.md": f"{name}\n"}, f"{name} base")
        # trust-wp last, so its lock can bind every cohort row to a real
        # sibling commit (each an ancestor-or-equal of the gitlink, P3) and
        # the trust row to genesis.  Its base commit plays W0.
        wp_lock = "".join(
            f"{name} main {sha}\n"
            for name, sha in (
                ("clean", pins["clean"]),
                ("trust-ir", pins["trust-ir"]),
                ("trust-cg", pins["trust-cg"]),
                ("trust", genesis),
                ("ay", pins["ay"]),
            )
        )
        w0 = _st_sibling(
            root, "trust-wp", {"README.md": "trust-wp\n", WP_DEPENDS_PATH: wp_lock}, "trust-wp W0"
        )
        pins["trust-wp"] = w0
        wp = root / SUBMODULES["trust-wp"][0]
        # Published floor B is W0's child on main; main then advances past B.
        floor = _st_sibling(root, "trust-wp", {"published.txt": "floor B\n"}, "published floor B")
        wp_main = _st_sibling(root, "trust-wp", {"later.txt": "past B\n"}, "trust-wp main past B")
        # Off-main lines from W0: two same-lock commits for the backward and
        # sideways shapes, and one whose lock blob differs but still parses
        # to the same rows (a comment) so P2 -- not P3 -- is what refuses it.
        _st_run(wp, ["checkout", "-q", "-b", "side", w0])
        side_one = _st_sibling(root, "trust-wp", {"side-one.txt": "side\n"}, "side line one")
        side_two = _st_sibling(root, "trust-wp", {"side-two.txt": "more\n"}, "side line two")
        _st_run(wp, ["checkout", "-q", "-b", "relocked", w0])
        relocked = _st_sibling(
            root, "trust-wp", {WP_DEPENDS_PATH: "# refreshed\n" + wp_lock}, "lock blob differs"
        )
        _st_run(wp, ["checkout", "-q", "main"])
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
        pre_policy = _st_root_commit(root, pins, policy, "coherent pre-policy constellation")
        # Two pre-activation side lines, each pinning its own trust-wp commit,
        # recorded on main by an `-s ours` merge that keeps W0: the history a
        # restoration (rows 30-32) may and may not reach back into.
        side_lines: list[str] = []
        for side_pin, label in ((side_one, "line one"), (side_two, "line two")):
            _st_run(root, ["checkout", "-q", "--detach", pre_policy])
            side_lines.append(
                _st_root_commit(root, {**pins, "trust-wp": side_pin}, policy, f"pre-activation side {label}")
            )
        _st_run(root, ["checkout", "-q", "main"])
        pre_merge = _st_run(
            root,
            [
                "commit-tree", f"{pre_policy}^{{tree}}", "-p", pre_policy,
                "-p", side_lines[0], "-p", side_lines[1],
                "-m", "pre-activation merge of both side lines (-s ours, keeps W0)",
            ],
        )
        _st_run(root, ["update-ref", "refs/heads/main", pre_merge, pre_policy])
        marker = root / TERMINAL_POLICY_MARKER_PATH
        marker.write_bytes(TERMINAL_POLICY_MARKER)
        _st_run(root, ["add", "--", TERMINAL_POLICY_MARKER_PATH])
        _st_run(
            root,
            ["commit", "-q", "--no-verify", "-m", "activate immutable terminal policy"],
        )
        pre_v3 = _st_run(root, ["rev-parse", "HEAD"])
        # The v3 marker names W0 and B; here those are the synthetic commits,
        # so the marker and the module constants are rebound together below.
        synthetic_marker = render_terminal_policy_v3_marker(w0, floor)
        (root / TERMINAL_POLICY_V3_MARKER_PATH).write_bytes(synthetic_marker)
        _st_run(root, ["add", "--", TERMINAL_POLICY_V3_MARKER_PATH])
        _st_run(root, ["commit", "-q", "--no-verify", "-m", "declare terminal-policy v3"])
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

        # trust-wp commits for the P3 negatives: a lock whose ay row is AHEAD
        # of the ay gitlink the root will pin, and one that does not parse.
        _st_run(wp, ["checkout", "-q", "-b", "ahead", w0])
        lock_ahead = _st_sibling(
            root,
            "trust-wp",
            {WP_DEPENDS_PATH: wp_lock.replace(pins["ay"], pins_bad["ay"])},
            "lock row ahead of its gitlink",
        )
        _st_run(wp, ["checkout", "-q", "-b", "garbage", w0])
        lock_garbage = _st_sibling(
            root, "trust-wp", {WP_DEPENDS_PATH: "not a lock\n"}, "unparseable lock"
        )
        _st_run(wp, ["checkout", "-q", "main"])

        def root_child(
            parent: str,
            child_pins: dict[str, str],
            message: str,
            *,
            v3_marker: bytes | None = None,
            v2_marker: bytes | None = None,
        ) -> str:
            """One root commit on top of ``parent``, off main, with its own pins."""
            _st_run(root, ["checkout", "-q", "--detach", parent])
            if v3_marker is not None:
                (root / TERMINAL_POLICY_V3_MARKER_PATH).write_bytes(v3_marker)
                _st_run(root, ["add", "--", TERMINAL_POLICY_V3_MARKER_PATH])
            if v2_marker is not None:
                (root / TERMINAL_POLICY_V2_MARKER_PATH).write_bytes(v2_marker)
                _st_run(root, ["add", "--", TERMINAL_POLICY_V2_MARKER_PATH])
            return _st_root_commit(root, child_pins, policy, message)

        forged = root_child(
            good, pins, "forge the v3 marker",
            v3_marker=synthetic_marker.replace(b"ruled=2026-09-21", b"ruled=2026-09-22"),
        )
        armed = root_child(
            good, pins, "arm the superseded v2 policy",
            v2_marker=(
                b"trust.constellation.terminal-policy.v2\nstate=armed\n"
                b"policy=trust-wp-root-cycle-forward\n"
                + f"w0={w0}\npreservation-floor={floor}\npredecessor={wp_main}\n".encode("ascii")
            ),
        )
        relock_forward = root_child(
            good, {**pins, "trust-wp": relocked}, "forward move with a changed lock"
        )
        off_main = root_child(good, {**pins, "trust-wp": side_two}, "forward move off main")
        rolled_back = root_child(
            off_main, {**pins, "trust-wp": side_one}, "backward move, off main"
        )
        restored = root_child(rolled_back, {**pins, "trust-wp": side_two}, "restore the pin")
        sideways_relock = root_child(
            off_main, {**pins, "trust-wp": relocked}, "sideways move with a differing lock"
        )
        reanchored = root_child(
            off_main, {**pins, "trust-wp": floor}, "sideways re-anchoring onto canonical main"
        )
        ahead = root_child(good, {**pins, "trust-wp": lock_ahead}, "pin a lock row ahead of ay")
        garbage = root_child(good, {**pins, "trust-wp": lock_garbage}, "pin an unparseable lock")

        def stash_merge(index_pin: str, label: str) -> tuple[str, str]:
            """The 1fedcff19d shape: a `git stash` on pre-activation side line
            one (which pins side one) whose index commit carries ``index_pin``,
            recorded on the marked line by an `-s ours` merge keeping good's
            tree.  Returns (index commit, merge)."""
            index = root_child(side_lines[0], {**pins, "trust-wp": index_pin}, f"index on side: {label}")
            wip = _st_run(
                root,
                ["commit-tree", f"{index}^{{tree}}", "-p", side_lines[0], "-p", index,
                 "-m", f"WIP on side: {label}"],
            )
            merge = _st_run(
                root,
                ["commit-tree", f"{good}^{{tree}}", "-p", good, "-p", wip,
                 "-m", f"Merge preserve/stash ({label}; ancestry only, -s ours)"],
            )
            return index, merge

        def untracked_stash_merge(untracked_tree: str, label: str) -> tuple[str, str]:
            """A `git stash -u` on side line one, recorded like stash_merge: its
            index commit stages nothing (side one's pin) and its third parent is a
            PARENTLESS untracked-files commit with ``untracked_tree``.
            Returns (untracked commit, merge)."""
            # Nothing staged: the index commit has its parent's tree.
            index = _st_run(root, ["commit-tree", f"{side_lines[0]}^{{tree}}", "-p", side_lines[0],
                                   "-m", f"index on side: {label}"])
            untracked = _st_run(root, ["commit-tree", untracked_tree, "-m", f"untracked files on side: {label}"])
            wip = _st_run(
                root,
                ["commit-tree", f"{index}^{{tree}}", "-p", side_lines[0], "-p", index, "-p", untracked,
                 "-m", f"WIP on side: {label}"],
            )
            merge = _st_run(
                root,
                ["commit-tree", f"{good}^{{tree}}", "-p", good, "-p", wip,
                 "-m", f"Merge preserve/stash -u ({label}; ancestry only, -s ours)"],
            )
            return untracked, merge

        # Row 38: an untracked-files tree holds only untracked files, no first-party/.
        untracked_blob = _st_run(root, ["hash-object", "-w", "--stdin"], stdin=b"fn untracked() {}\n")
        untracked_src = _st_run(root, ["mktree"], stdin=f"100644 blob {untracked_blob}\tlib.rs\n".encode())
        untracked_tree = _st_run(root, ["mktree"], stdin=f"040000 tree {untracked_src}\tcrates\n".encode())
        unbound_untracked, unbound_root_merge = untracked_stash_merge(untracked_tree, "untracked files")
        # Row 41: the main-history shape (3ca41eb1a3): a `git stash -u` taken ON
        # the marked line, so the stash commit is itself marked and its
        # untracked-files commit is a direct unmarked parent, a lineage of one.
        marked_index = _st_run(root, ["commit-tree", f"{good}^{{tree}}", "-p", good, "-m", "index on main: nothing staged"])
        marked_untracked = _st_run(root, ["commit-tree", untracked_tree, "-m", "untracked files on main"])
        marked_stash = _st_run(
            root,
            ["commit-tree", f"{good}^{{tree}}", "-p", good, "-p", marked_index, "-p", marked_untracked,
             "-m", "WIP on main: stash -u"],
        )
        marked_stash_merge = _st_run(
            root,
            ["commit-tree", f"{good}^{{tree}}", "-p", good, "-p", marked_stash,
             "-m", "Preserve rescued local work (ancestry only, -s ours)"],
        )
        # Row 39: the same shape whose parentless commit DOES carry a binding,
        # one nobody published: it mints, as any parentless commit with one does.
        bound_tree = _st_run(root, ["rev-parse", f"{root_child(side_lines[0], {**pins, 'trust-wp': relocked}, 'scratch')}^{{tree}}"])
        bound_untracked, bound_root_merge = untracked_stash_merge(bound_tree, "parentless binding")
        # Row 42: the same position, but the lone parentless parent carries a
        # binding: it still never rejoins, and it mints.
        bound_marked_stash = _st_run(
            root,
            ["commit-tree", f"{good}^{{tree}}", "-p", good, "-p", marked_index, "-p", bound_untracked,
             "-m", "WIP on main: stash -u of a bound tree"],
        )
        # Row 40: an inactive commit WITH a parent that drops the gitlink is no
        # unbound root: it is refused before any mint test.
        dropped_tree = _st_run(root, ["mktree"], stdin=b"".join(
            line.encode() + b"\n"
            for line in _st_run(root, ["ls-tree", f"{side_lines[0]}^{{tree}}"]).splitlines()
            if not line.endswith("\tfirst-party")
        ))
        dropped = _st_run(root, ["commit-tree", dropped_tree, "-p", side_lines[0], "-m", "side drops first-party/"])
        dropped_merge = _st_run(
            root,
            ["commit-tree", f"{good}^{{tree}}", "-p", good, "-p", dropped,
             "-m", "Merge a side line that dropped the TrustWP gitlink (-s ours)"],
        )
        # Restores W0, which the side line's own pre-activation ancestry pinned.
        restore_index, restore_merge = stash_merge(w0, "restores W0")
        # Pins side two: pre-activation, but only on the OTHER side line.
        parallel_index, parallel_merge = stash_merge(side_two, "parallel line's pin")
        # Pins a commit no pre-activation commit ever pinned.
        fresh_index, fresh_merge = stash_merge(relocked, "unpublished pin")
        # Rows 34-37: pushes on top of a destination already red on an inactive
        # mint (parallel_merge), each adding a red of its own behind it
        # (CONSTELLATION-ALL-FINDINGS).  A refused P2 move: forward off main,
        # then sideways onto a differing lock.
        red_forward = root_child(
            parallel_merge, {**pins, "trust-wp": side_two}, "red main: forward move off main"
        )
        red_plus_move = root_child(
            red_forward, {**pins, "trust-wp": relocked}, "red main: sideways move, differing lock"
        )
        # A second, new mint, merged on top of the red one; two of them, so one
        # merge sorts after parallel_merge whatever the shas come out as.
        red_plus_mints: list[tuple[str, str]] = []
        for tag in ("a", "b"):
            mint_index = root_child(
                side_lines[0], {**pins, "trust-wp": relocked}, f"red main: new mint {tag}"
            )
            red_plus_mints.append(
                (
                    mint_index,
                    _st_run(
                        root,
                        ["commit-tree", f"{parallel_merge}^{{tree}}", "-p", parallel_merge,
                         "-p", mint_index, "-m", f"red main: merge new mint {tag} (-s ours)"],
                    ),
                )
            )
        # A red a later check finds (P3: a lock row ahead of its gitlink),
        # reached by an admissible forward move.
        red_plus_p3 = root_child(
            parallel_merge, {**pins, "trust-wp": lock_ahead}, "red main: lock row ahead of ay"
        )

        # trust-wp's "canonical remote" for the by-sha fetch (row 33): a bare
        # clone of the store holding one commit the store does not, a main
        # that advanced past the store's last fetch.
        wp_remote = Path(raw).resolve() / "remotes" / "trust-wp.git"
        _st_run(root, ["clone", "-q", "--bare", "--no-local", str(wp), str(wp_remote)])
        remote_only = _st_run(
            wp_remote,
            ["commit-tree", f"{wp_main}^{{tree}}", "-p", wp_main, "-m", "remote main advances"],
        )
        _st_run(wp_remote, ["update-ref", "refs/heads/main", remote_only])

        # Leave the checkout on the LAST main commit, so every --rev and
        # --push-context assertion below that names another revision is also
        # a statement that HEAD was not what got judged.
        _st_run(root, ["checkout", "-q", "main"])
        head = _st_run(root, ["rev-parse", "HEAD"])
        check("selftest fixture: HEAD is the policy-less revision", head == no_policy)

        derive = ["--derive-when-receipt-absent"]

        # ONLY the live trust-wp ls-remote sample is stubbed (to the synthetic
        # trust-wp main), and W0/B are rebound to the synthetic base and floor
        # the fixture's marker names.  Every other read is the real one.
        print("  note: the live trust-wp remote-main sample is STUBBED to the synthetic")
        print("        trust-wp main, and the by-sha fetch URL to a bare clone of it;")
        print("        W0/B are the synthetic base/floor; nothing else is")
        remote = {"main": wp_main}
        module_globals = globals()
        rebound = {
            "TRUST_WP_W0": w0,
            "TRUST_WP_PRESERVATION_FLOOR": floor,
            "TERMINAL_POLICY_V3_MARKER": synthetic_marker,
            "sample_trust_wp_remote_main": lambda: remote["main"],
            "trust_wp_fetch_url": lambda: str(wp_remote),
        }
        originals = {name: module_globals[name] for name in rebound}
        module_globals.update(rebound)
        try:
            _selftest_assertions(
                check, root, derive,
                dict(
                    genesis=genesis, pre_v3=pre_v3, good=good, bad=bad,
                    no_policy=no_policy, forged=forged, armed=armed,
                    relock_forward=relock_forward, off_main=off_main,
                    rolled_back=rolled_back, restored=restored,
                    sideways_relock=sideways_relock, reanchored=reanchored,
                    ahead=ahead, garbage=garbage, w0=w0, floor=floor,
                    wp_main=wp_main, side_one=side_one, side_two=side_two,
                    restore_merge=restore_merge, restore_index=restore_index,
                    unbound_root_merge=unbound_root_merge, unbound_untracked=unbound_untracked,
                    bound_root_merge=bound_root_merge, bound_untracked=bound_untracked,
                    dropped_merge=dropped_merge, dropped=dropped,
                    marked_stash_merge=marked_stash_merge, bound_marked_stash=bound_marked_stash,
                    parallel_merge=parallel_merge, parallel_index=parallel_index,
                    fresh_merge=fresh_merge, fresh_index=fresh_index,
                    relocked=relocked, remote_only=remote_only,
                    red_forward=red_forward, red_plus_move=red_plus_move,
                    red_plus_mint_a=red_plus_mints[0][1], red_mint_index_a=red_plus_mints[0][0],
                    red_plus_mint_b=red_plus_mints[1][1], red_mint_index_b=red_plus_mints[1][0],
                    red_plus_p3=red_plus_p3,
                ),
                remote,
            )
        finally:
            module_globals.update(originals)

    if failures:
        print(f"SELFTEST FAILED: {len(failures)} assertion(s): {failures}")
        return 1
    print("SELFTEST OK: the gate passes a coherent constellation, refuses an incoherent")
    print("one, judges the revision it is pointed at rather than this clone's HEAD, and")
    print("holds trust-wp to terminal-policy v3 (P1-P4) with each negative refused.")
    return 0


def _selftest_assertions(
    check: Any,
    root: Path,
    derive: list[str],
    n: dict[str, str],
    remote: dict[str, str],
) -> None:
    good, bad, no_policy = n["good"], n["bad"], n["no_policy"]

    def first_lines(text: str, count: int = 2) -> list[str]:
        return text.strip().splitlines()[:count]

    # 1. GREEN: a coherent constellation passes, at a revision that is NOT HEAD.
    code, text = _st_judge(root, ["--rev", good, *derive], None)
    check(
        "GREEN  --rev <coherent> passes while HEAD is incoherent",
        code == 0 and "DEPENDENCY CONSTELLATION OK" in text
        and "trust-wp terminal-policy v3" in text,
        f"exit {code}: {first_lines(text)}",
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

    # 4. A deletion publishes no tree, so it must not be judged as one. With
    #    nothing left to judge, the subject is the terminal state the push
    #    leaves in place (origin/main) — and this fixture has NO remote-tracking
    #    main, so it WIDENS to HEAD rather than silently passing on an empty set.
    code, text = _st_judge(
        root, ["--push-context", *derive], f"(delete) {'0' * 40} refs/heads/topic {good}"
    )
    check(
        "RED    a delete-only push with no remote-tracking main widens to HEAD, never passes vacuously",
        code == 1 and "no push in flight" not in text
        and "refs/remotes/origin/main does not resolve" in text,
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
    #     ref exempt the subject is the destination's main, and with no
    #     remote-tracking main it widens to HEAD, exactly as a delete-only
    #     push does — the fixture's HEAD carries no policy, so it refuses.
    #     Rows 25-29 judge the same pushes WITH a remote-tracking main.
    code, text = _st_judge(
        root,
        ["--push-context", *derive],
        f"{bad} {bad} refs/archive/2026-08-31/retired {'0' * 40}",
    )
    check(
        "RED    an archive-ONLY push with no remote-tracking main widens to HEAD, never passes vacuously",
        code == 1 and "refs/remotes/origin/main does not resolve" in text,
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

    # ---- terminal-policy v3 (P1-P4): each negative refused with its named
    # ---- message, each admissible shape green.  Numbering continues.

    # 12. RED: no v3 marker at the judged revision (the v1-only commit).  The
    #     refusal carries the fix, like every other stale-revision refusal.
    code, text = _st_judge(root, ["--rev", n["pre_v3"], *derive], None)
    check(
        "RED    P4 a revision without the v3 marker is refused, with options",
        code == 1 and "terminal-policy v3 marker" in text and "is missing" in text
        and "--rev origin/main" in text,
        f"exit {code}: {first_lines(text)}",
    )

    # 13. RED: a forged/edited v3 marker names the row that differs.
    code, text = _st_judge(root, ["--rev", n["forged"], *derive], None)
    check(
        "RED    P4 a forged v3 marker is refused naming the differing row",
        code == 1 and "terminal-policy v3 marker row 6 differs" in text,
        f"exit {code}: {first_lines(text)}",
    )

    # 14. RED: an armed v2 marker is refused outright.
    code, text = _st_judge(root, ["--rev", n["armed"], *derive], None)
    check(
        "RED    P4 an armed v2 marker is refused outright",
        code == 1 and "v2 marker" in text and "ARMED" in text and "refused outright" in text,
        f"exit {code}: {first_lines(text)}",
    )

    # 15. RED: trust-wp remote main that does not contain B (W0 itself).
    remote["main"] = n["w0"]
    code, text = _st_judge(root, ["--rev", good, *derive], None)
    remote["main"] = n["wp_main"]
    check(
        "RED    P1 a remote main missing the preservation floor B is refused",
        code == 1 and "does not contain the preservation floor B" in text,
        f"exit {code}: {first_lines(text)}",
    )

    # 16. RED: the sampled main is not in the local object store: name the fetch.
    remote["main"] = "f" * 40
    code, text = _st_judge(root, ["--rev", good, *derive], None)
    remote["main"] = n["wp_main"]
    check(
        "RED    P1 a remote main absent from the object store names the fetch",
        code == 1 and "is not present in the bound first-party/trust-wp object store" in text
        and "git -C first-party/trust-wp fetch origin main" in text
        # An unreadable store is no finding about the history: no FINDING
        # line, so the hook can never grade it a red main already has.
        and "FINDING:" not in text,
        f"exit {code}: {first_lines(text)}",
    )

    # 17. GREEN: a forward move whose lock blob CHANGED is admissible (P2a);
    #     the bindings inside it are P3's question, and here they still hold.
    code, text = _st_judge(root, ["--rev", n["relock_forward"], *derive], None)
    check(
        "GREEN  P2(a) a forward move with a changed lock is admissible",
        code == 0 and "1 gitlink move(s) since v1 activation admissible" in text,
        f"exit {code}: {first_lines(text)}",
    )

    # 18. GREEN then RED: forward off main, then backward without a restoration.
    code, text = _st_judge(root, ["--rev", n["off_main"], *derive], None)
    check(
        "GREEN  P2(a) a forward move onto an off-main line is admissible",
        code == 0 and "DEPENDENCY CONSTELLATION OK" in text,
        f"exit {code}: {first_lines(text)}",
    )
    code, text = _st_judge(root, ["--rev", n["rolled_back"], *derive], None)
    check(
        "RED    P2 a backward move without recovery is refused naming X, Y and the clauses",
        code == 1
        and f"X={n['side_two']} -> Y={n['side_one']}" in text
        and "(a) not forward" in text
        and "(b) not a canonical re-anchoring: Y is not an ancestor-or-equal" in text
        and "(c) not a recovered same-lock backward move: no immediate single-parent child" in text,
        f"exit {code}: {first_lines(text)}",
    )

    # 19. GREEN: the same backward move, restored by an immediate child (P2c).
    code, text = _st_judge(root, ["--rev", n["restored"], *derive], None)
    check(
        "GREEN  P2(c) a same-lock backward move restored by its immediate child is admissible",
        code == 0 and "1 by same-lock recovery" in text
        and "DEPENDENCY CONSTELLATION SAME-LOCK RECOVERY" in text,
        f"exit {code}: {first_lines(text, 3)}",
    )

    # 20. RED: a sideways move whose lock differs.
    code, text = _st_judge(root, ["--rev", n["sideways_relock"], *derive], None)
    check(
        "RED    P2 a sideways move with a differing lock is refused on the lock",
        code == 1 and "(b) not a canonical re-anchoring: spikes/DEPENDS.lock differs" in text
        and "(c) not a recovered same-lock backward move: spikes/DEPENDS.lock differs" in text,
        f"exit {code}: {first_lines(text)}",
    )

    # 21. GREEN: the 8325008ba62 shape -- sideways onto canonical main with the
    #     lock byte-identical (P2b).
    code, text = _st_judge(root, ["--rev", n["reanchored"], *derive], None)
    check(
        "GREEN  P2(b) a same-lock sideways move onto canonical main is admissible",
        code == 0 and "2 gitlink move(s) since v1 activation admissible" in text,
        f"exit {code}: {first_lines(text)}",
    )

    # 22. RED: a lock row AHEAD of the gitlink it names (P3).
    code, text = _st_judge(root, ["--rev", n["ahead"], *derive], None)
    check(
        "RED    P3 a lock row ahead of its gitlink is refused",
        code == 1 and "spikes/DEPENDS.lock ay row" in text
        and "is not an ancestor-or-equal of the first-party/ay gitlink" in text,
        f"exit {code}: {first_lines(text)}",
    )

    # 23. RED: an unparseable lock at the pinned trust-wp commit (P3).
    code, text = _st_judge(root, ["--rev", n["garbage"], *derive], None)
    check(
        "RED    P3 an unparseable lock at the pinned trust-wp commit is refused",
        code == 1 and "trust-wp:spikes/DEPENDS.lock line 1" in text,
        f"exit {code}: {first_lines(text)}",
    )

    # 24. The pre-push row on the SAME shapes: the judged revision is the one
    #     being pushed, for an admissible and a refused move alike.
    code, text = _st_judge(
        root, ["--push-context", *derive],
        f"refs/heads/main {n['reanchored']} refs/heads/main {n['off_main']}",
    )
    check(
        "GREEN  --push-context judges a pushed canonical re-anchoring green",
        code == 0 and "SUBJECT: push (1 ref update(s))" in text,
        f"exit {code}: {first_lines(text)}",
    )
    code, text = _st_judge(
        root, ["--push-context", *derive],
        f"refs/heads/main {n['rolled_back']} refs/heads/main {n['off_main']}",
    )
    check(
        "RED    --push-context judges a pushed unrecovered backward move red",
        code == 1 and "(a) not forward" in text,
        f"exit {code}: {first_lines(text)}",
    )

    # ---- an UNMARKED merge parent (audit_inactive_parent): a restoration of
    # ---- a binding the commit's own pre-activation ancestry pinned is no
    # ---- mint; every other new binding is (docs/DECISION_QUEUE.md
    # ---- CONSTELLATION-RESTORE, 2026-10-24).

    # 30. GREEN: the stash-shaped lineage whose index commit restores W0.
    code, text = _st_judge(root, ["--rev", n["restore_merge"], *derive], None)
    check(
        "GREEN  an inactive lineage RESTORING its own pre-activation binding is no mint",
        code == 0 and "DEPENDENCY CONSTELLATION OK" in text,
        f"exit {code}: {first_lines(text)}",
    )

    # 31. RED: the same shape pinning what only a PARALLEL pre-activation line
    #     pinned -- the clause reads the commit's own ancestry, not all history.
    code, text = _st_judge(root, ["--rev", n["parallel_merge"], *derive], None)
    check(
        "RED    an inactive lineage pinning only a parallel line's binding mints",
        code == 1 and "minted a TrustWP gitlink no raw parent published" in text
        and f"commit={n['parallel_index']}" in text
        and f"commit_wp={n['side_two']}" in text
        # A history finding prints its one-line key for the hook (INHERITED-RED).
        and "FINDING: CONSTELLATION-INVALID Trust terminal-policy inactive merge lineage minted" in text,
        f"exit {code}: {first_lines(text)}",
    )

    # 32. RED: the same shape pinning a commit no pre-activation commit pinned.
    code, text = _st_judge(root, ["--rev", n["fresh_merge"], *derive], None)
    check(
        "RED    an inactive lineage pinning an unpublished binding mints",
        code == 1 and "minted a TrustWP gitlink no raw parent published" in text
        and f"commit={n['fresh_index']}" in text
        and f"commit_wp={n['relocked']}" in text,
        f"exit {code}: {first_lines(text)}",
    )

    # 38. GREEN: a `git stash -u` lineage whose parentless untracked-files
    #     commit has no first-party/trust-wp entry: it carries no binding, so
    #     it mints none (CONSTELLATION-UNBOUND-ROOT, 2026-11-11).
    code, text = _st_judge(root, ["--rev", n["unbound_root_merge"], *derive], None)
    check(
        "GREEN  an inactive parentless commit with no TrustWP entry mints nothing",
        code == 0 and "DEPENDENCY CONSTELLATION OK" in text,
        f"exit {code}: {first_lines(text)}",
    )

    # 39. RED: the same shape whose parentless commit carries a binding nobody
    #     published: parentless, it has no ancestry to restore from.
    code, text = _st_judge(root, ["--rev", n["bound_root_merge"], *derive], None)
    check(
        "RED    an inactive parentless commit carrying an unpublished binding mints",
        code == 1 and "minted a TrustWP gitlink no raw parent published" in text
        and f"commit={n['bound_untracked']}" in text and "parent_wps={}" in text,
        f"exit {code}: {first_lines(text)}",
    )

    # 40. RED: an inactive commit WITH a parent that drops the gitlink is
    #     refused; only a parentless commit may carry no binding.
    code, text = _st_judge(root, ["--rev", n["dropped_merge"], *derive], None)
    check(
        "RED    an inactive commit that drops the TrustWP gitlink is refused",
        code == 1 and f"inactive child {n['dropped']} is missing committed TrustWP gitlink" in text,
        f"exit {code}: {first_lines(text)}",
    )

    # 41. GREEN: the main-history shape, a `git stash -u` taken on the marked
    #     line: its untracked-files commit is a lone unbound root and needs no
    #     frontier (CONSTELLATION-UNBOUND-ROOT).
    code, text = _st_judge(root, ["--rev", n["marked_stash_merge"], *derive], None)
    check(
        "GREEN  a marked `git stash -u` commit's unbound untracked parent needs no frontier",
        code == 0 and "DEPENDENCY CONSTELLATION OK" in text,
        f"exit {code}: {first_lines(text)}",
    )

    # 42. RED: the same position with a parentless parent that carries a
    #     binding: it never rejoins, and it mints.
    code, text = _st_judge(root, ["--rev", n["bound_marked_stash"], *derive], None)
    check(
        "RED    a lone parentless parent carrying a binding never rejoins and mints",
        code == 1 and "never rejoins pre-activation ancestry" in text
        and "minted a TrustWP gitlink no raw parent published" in text,
        f"exit {code}: {first_lines(text)}",
    )

    # 33. GREEN: trust-wp's remote main moved past this store's last fetch.
    #     The judgement fetches that commit by sha first and writes no ref
    #     (PUSH-PATH-CLONE-STATE, 2026-10-24); before, this was row 16's refusal.
    wp_store = root / SUBMODULES["trust-wp"][0]
    refs_before = _st_run(wp_store, ["for-each-ref"])
    absent_before = absent_commits(wp_store, [n["remote_only"]])
    remote["main"] = n["remote_only"]
    code, text = _st_judge(root, ["--rev", good, *derive], None)
    remote["main"] = n["wp_main"]
    git_dir = Path(_st_run(wp_store, ["rev-parse", "--absolute-git-dir"]))
    check(
        "GREEN  P1 a remote main this store never fetched is fetched by sha, writing no ref",
        absent_before == [n["remote_only"]]
        and code == 0 and "DEPENDENCY CONSTELLATION OK" in text
        and f"fetched 1 absent commit(s) by sha" in text
        and not absent_commits(wp_store, [n["remote_only"]])
        and _st_run(wp_store, ["for-each-ref"]) == refs_before
        and not (git_dir / "FETCH_HEAD").exists(),
        f"exit {code}: {first_lines(text, 3)}",
    )

    # ---- EVERY history finding, not the first (HistoryFinding,
    # ---- CONSTELLATION-ALL-FINDINGS, 2026-10-25).  The hook grades a red
    # ---- INHERITED when the push's keys are all the destination's and the
    # ---- set says `complete`; so a push that adds a red behind a red main's
    # ---- must print that red's key, or withhold `complete`.  Until this
    # ---- change the gate stopped at its first refusal and printed that one
    # ---- key as the complete set: rows 34, 35 and 37 printed exactly the
    # ---- destination's key, and row 36 printed it with `complete`.

    def finding_keys(text: str) -> set[str]:
        return {
            line[len("FINDING: "):]
            for line in text.splitlines()
            if line.startswith("FINDING: ")
        }

    def says_complete(text: str) -> bool:
        return "FINDINGS: complete" in text.splitlines()

    dest_code, dest_text = _st_judge(root, ["--rev", n["parallel_merge"], *derive], None)
    dest_keys = finding_keys(dest_text)
    check(
        "RED    a red destination names its one finding, complete",
        dest_code == 1 and len(dest_keys) == 1 and says_complete(dest_text),
        f"exit {dest_code}: keys={sorted(dest_keys)}",
    )

    # 34. A refused P2 move on top of the red destination: the P2 pass runs
    #     after the merge audit, so it was never reached.
    code, text = _st_judge(root, ["--rev", n["red_forward"], *derive], None)
    check(
        "RED    an admissible move on a red destination adds no key",
        code == 1 and finding_keys(text) == dest_keys and says_complete(text),
        f"exit {code}: keys={sorted(finding_keys(text))}",
    )
    code, text = _st_judge(root, ["--rev", n["red_plus_move"], *derive], None)
    added = finding_keys(text) - dest_keys
    check(
        "RED    a refused P2 move behind a red destination's finding prints its own key, complete",
        code == 1 and dest_keys <= finding_keys(text) and says_complete(text)
        and len(added) == 1
        and f"v3 refuses the first-party/trust-wp gitlink move at {n['red_plus_move']}"
        in next(iter(added), ""),
        f"exit {code}: added={sorted(added)}",
    )

    # 35. A second, new mint merged on top of the red one, in both sha orders.
    for tag in ("a", "b"):
        code, text = _st_judge(root, ["--rev", n[f"red_plus_mint_{tag}"], *derive], None)
        added = finding_keys(text) - dest_keys
        check(
            f"RED    a new mint behind a red destination's mint prints its own key ({tag})",
            code == 1 and dest_keys <= finding_keys(text) and says_complete(text)
            and any(
                f"merge={n[f'red_plus_mint_{tag}']}, commit={n[f'red_mint_index_{tag}']}" in key
                for key in added
            ),
            f"exit {code}: added={sorted(added)}",
        )

    # 36. A red a LATER check finds (P3, after the policy pass): named, and
    #     the set is not complete, so it can never be inherited.
    code, text = _st_judge(root, ["--rev", n["red_plus_p3"], *derive], None)
    check(
        "RED    a later check's red behind a red destination's finding withholds complete",
        code == 1 and "spikes/DEPENDS.lock ay row" in text
        and finding_keys(text) == dest_keys and not says_complete(text),
        f"exit {code}: {first_lines(text, 4)}",
    )

    # 37. A two-ref push whose first ref carries the red destination's finding:
    #     the second ref is judged too, and its own red is keyed.
    code, text = _st_judge(
        root, ["--push-context", *derive],
        f"refs/heads/main {n['parallel_merge']} refs/heads/main {good}\n"
        f"refs/heads/topic {n['sideways_relock']} refs/heads/topic {'0' * 40}",
    )
    added = finding_keys(text) - dest_keys
    check(
        "RED    a multi-ref push judges every ref past the first one's red, complete",
        code == 1 and "SUBJECT: push (2 ref update(s))" in text
        and dest_keys <= finding_keys(text) and says_complete(text)
        and any(f"gitlink move at {n['sideways_relock']}" in key for key in added),
        f"exit {code}: added={sorted(added)}",
    )

    # ---- a push that publishes NO terminal-state candidate (archive-only,
    # ---- delete-only) is judged on the terminal state it leaves in place,
    # ---- the destination's main — never on this clone's HEAD, never on nothing.
    #
    # The clone sits on the retired pre-v3 commit (the checked-out branch being
    # archived), which the lane refuses on its own; the destination's main is
    # coherent.  Before 2026-09-27 rows 25 and 26 refused on that HEAD.
    zero = "0" * 40
    pre_v3 = n["pre_v3"]
    _st_run(root, ["remote", "add", "origin", "/nonexistent/trust.git"])
    _st_run(root, ["remote", "add", "canon", "https://example.invalid/canon/trust.git"])
    _st_run(root, ["update-ref", "refs/remotes/origin/main", good])
    _st_run(root, ["checkout", "-q", "--detach", pre_v3])
    try:
        archive_head = f"HEAD {pre_v3} refs/archive/2026-09-27/retired {zero}"
        delete_topic = f"(delete) {zero} refs/heads/topic {good}"

        # 25. GREEN: archiving the checked-out retired branch.
        code, text = _st_judge(root, ["--push-context", *derive], archive_head)
        check(
            "GREEN  an archive-only push of a retired HEAD is judged on origin/main, not HEAD",
            code == 0
            and "not a terminal-state candidate, not judged: refs/archive/" in text
            and f"SUBJECT: origin/main [{good[:12]}]" in text
            and "DEPENDENCY CONSTELLATION OK" in text,
            f"exit {code}: {first_lines(text, 3)}",
        )

        # 26. GREEN: deleting a remote branch from a clone on a stale commit.
        code, text = _st_judge(root, ["--push-context", *derive], delete_topic)
        check(
            "GREEN  a delete-only push from a stale HEAD is judged on origin/main, not HEAD",
            code == 0 and f"SUBJECT: origin/main [{good[:12]}]" in text,
            f"exit {code}: {first_lines(text, 3)}",
        )

        # 27. RED: deleting main itself. The remote-tracking main will not
        #     survive the push, so it is not what gets judged: HEAD is.
        code, text = _st_judge(
            root, ["--push-context", *derive], f"(delete) {zero} refs/heads/main {good}"
        )
        check(
            "RED    a push that DELETES main never judges the deleted main; it widens to HEAD",
            code == 1 and "DELETES refs/heads/main" in text
            and "SUBJECT: origin/main" not in text
            and "terminal-policy v3 marker" in text,
            f"exit {code}: {first_lines(text, 3)}",
        )

        # 28. The destination is recovered from the URL the hook exports (git's
        #     second pre-push argument), never assumed: with `canon` coherent
        #     and origin incoherent, the URL of `canon` judges canon/main, and
        #     a URL no remote carries falls back to origin — and refuses.
        _st_run(root, ["update-ref", "refs/remotes/canon/main", good])
        _st_run(root, ["update-ref", "refs/remotes/origin/main", bad])
        code, text = _st_judge(
            root, ["--push-context", *derive], archive_head,
            "https://example.invalid/canon/trust.git",
        )
        check(
            "GREEN  TRUST_PUSH_REMOTE as a URL resolves to its remote name (canon/main judged)",
            code == 0 and f"SUBJECT: canon/main [{good[:12]}]" in text
            and "is the URL of remote 'canon'" in text,
            f"exit {code}: {first_lines(text, 3)}",
        )
        code, text = _st_judge(
            root, ["--push-context", *derive], archive_head, "https://example.invalid/other.git",
        )
        check(
            "RED    an unmatched TRUST_PUSH_REMOTE falls back to origin/main and judges it",
            code == 1 and f"SUBJECT: origin/main [{bad[:12]}]" in text
            and "matches no configured remote" in text
            and "is not an ancestor of terminal" in text,
            f"exit {code}: {first_lines(text, 3)}",
        )

        # 29. RED: the same archive-only and delete-only pushes, with the
        #     destination's main itself incoherent, still refuse — the reading
        #     moved off HEAD, never onto nothing.
        for label, pushed in (("archive-only", archive_head), ("delete-only", delete_topic)):
            code, text = _st_judge(root, ["--push-context", *derive], pushed)
            check(
                f"RED    the {label} push still refuses when its destination main is incoherent",
                code == 1 and f"SUBJECT: origin/main [{bad[:12]}]" in text
                and "is not an ancestor of terminal" in text,
                f"exit {code}: {first_lines(text, 3)}",
            )
    finally:
        _st_run(root, ["checkout", "-q", "main"])
        _st_run(root, ["update-ref", "-d", "refs/remotes/origin/main"])
        _st_run(root, ["update-ref", "-d", "refs/remotes/canon/main"])
        _st_run(root, ["remote", "remove", "canon"])
        _st_run(root, ["remote", "remove", "origin"])




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
        help="render untracked v3 evidence from committed, clean HEAD",
    )
    generation.add_argument(
        "--write-receipt",
        action="store_true",
        help="atomically write untracked v3 evidence from committed, clean HEAD",
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
    # Every judged revision's history findings, in the order found; each is
    # one FINDING key (HistoryFinding).
    findings: list[str] = []
    complete = True
    try:
        repo_root = Path(
            run_git(args.repo_root, ["rev-parse", "--show-toplevel"])
            .decode("utf-8", "strict")
            .strip()
        )
        if (args.print_receipt or args.write_receipt) and args.print_observed:
            fail("--print-observed cannot be combined with receipt generation")
        generating = args.print_receipt or args.write_receipt
        sources = select_sources(repo_root, args)
        if generating and len(sources) > 1:
            fail("external receipt generation judges one revision; a multi-ref push names several")
        for source, label in sources:
            # Every revision is judged to its end, whatever an earlier one
            # found: a multi-ref push's later ref is never hidden behind the
            # first one's red.
            if not judge_source(repo_root, args, source, label, findings):
                complete = False
    except (AnchorError, OSError, UnicodeDecodeError) as error:
        print("DEPENDENCY CONSTELLATION FAILED:", file=sys.stderr)
        for message in findings:
            print(f"  - CONSTELLATION-INVALID  {message}", file=sys.stderr)
        print(f"  - CONSTELLATION-INVALID  {error}", file=sys.stderr)
        # Any other refusal is unkeyed: the findings are named, but the set is
        # not complete, so the hook can never grade this red INHERITED.
        print_finding_keys(findings, complete=False)
        # v7/D3: the refusal carries its own fix options when it has them.
        for line in getattr(error, "options", ()):
            print(f"    {line}", file=sys.stderr)
        return 1
    if findings:
        print("DEPENDENCY CONSTELLATION FAILED:", file=sys.stderr)
        for message in findings:
            print(f"  - CONSTELLATION-INVALID  {message}", file=sys.stderr)
        print_finding_keys(findings, complete=complete)
        return 1
    return 0


def print_finding_keys(findings: Sequence[str], *, complete: bool) -> None:
    """The stable keys the pre-push hook compares with the destination's.

    One line per history finding, whatever its message holds.  ``FINDINGS:
    complete`` follows only when every check of every judged revision ran to
    its end and nothing else refused (HistoryFinding): the hook grades a red
    INHERITED only from a complete set (scripts/hooks/pre-push INHERITED-RED).
    """
    for message in findings:
        print(f"FINDING: CONSTELLATION-INVALID {finding_key(message)}", file=sys.stderr)
    if findings and complete:
        print("FINDINGS: complete", file=sys.stderr)


if __name__ == "__main__":
    raise SystemExit(main())
