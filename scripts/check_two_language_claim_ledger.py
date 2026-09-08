#!/usr/bin/env python3
"""Fail-closed validator for the TRUST-TWO-LANGUAGE-100 claim ledger.

The per-claim refs are discovery mirrors.  The cross-claim serialization point
is the first-parent history of ``refs/heads/goals/TRUST-TWO-LANGUAGE-100``.
This checker validates either a candidate worktree claim directory or an actual
ledger commit.  In commit mode it also checks forward-only lifecycle history and,
when requested, every published mirror.

This is coordination evidence, not compiler-completion evidence.  A green result
does not satisfy any G1--G8 product gate.

WHAT ``base_revision`` PROTECTS, and what it does not
----------------------------------------------------

An active claim reserves ``exact_files`` against concurrent machines.  Its
``base_revision`` records the tree that reservation was taken against, and the
directive's reason for caring is stated in the goal document: *"Another machine
may have changed the residue, denominator, or prerequisite while the increment
was being built."*  That is a statement about CHANGE, not about the clock.

Until 2026-09-01 this checker required ``base_revision == integration head``
for every active claim, which is not that property and cannot be satisfied in a
repository where lanes land continuously:

* IT CONTRADICTED THE CHECKER'S OWN CONTAINMENT RULE.  ``validate_current``
  requires every claim's ``integration_head`` to be an ancestor of the LEDGER
  commit, and ``base_revision`` to be an ancestor of ``integration_head``.  So
  the newest revision an active claim may legally name is
  ``merge-base(ledger commit, integration ref)`` -- while this rule demanded it
  name the integration ref's TIP.  Both hold only when the goals branch already
  contains the integration tip, which is not its normal state: it carries
  producer commits of its own.  Measured 2026-09-01, the live claims named
  ``142906f4a355``, which IS that merge-base exactly, so they were already as
  fresh as the ledger could express, and merging ``origin/main`` into the goals
  branch to satisfy the other half CONFLICTED.  The gate was not narrow, it was
  unsatisfiable, and a lane polling for its window to open was waiting for
  something waiting does not produce;
* the reference is a MOVING tip nobody controls, so the predicate is true only
  inside a window that the next commit -- including the pushing lane's own --
  closes again;
* the reference read was ``refs/remotes/origin/main``, a CLONE-LOCAL CACHE, so
  a clone that had not fetched could satisfy the gate while an up-to-date one
  could not.  A gate that is easier to pass the more out of date you are has
  its incentive backwards (the same shape as the 2026-08-30 reachability lane);
* it collapsed two distinct fields.  With both forced equal to one commit,
  ``base_revision`` and ``integration_head`` could never differ, so the
  ancestry relation between them was vacuous;
* measured on the live ledger, every sync commit stamped the SAME sha onto
  every active claim, so the field degenerated into a global "last sync"
  marker and the check into "has anything at all landed since".  On
  2026-09-01 that reported eight identical refusals of which seven were pure
  clock drift -- and it reported the ONE genuine event (W1's reserved
  ``crates/trust-thir-lower/src/lib.rs`` taken by three commits) in exactly the
  same words, so the true positive was indistinguishable from the noise.

The operator was already applying the right rule by hand.  Every sync commit's
``validation_at_integration.results`` justifies the base move with a sentence of
the form *"synchronization head X leaves the complete W3 exact-file tree
byte-identical to parent Y; the integrated producer delta is ... outside this
claim"*.  This checker now computes that sentence instead of trusting it:

  an active claim's ``base_revision`` and ``integration_head`` must be on the
  integration line (ancestors of the OBSERVED integration head -- a diverged,
  forked or rewound base is refused), and the observed integration head's tree
  must be BYTE-IDENTICAL to the base's over every path in ``exact_files``.

The OBSERVED integration head is ``merge-base(ledger commit, integration ref)``
in ledger mode, and the given ref in candidate/worktree mode where no ledger
bounds it.  That is the newest integration revision the ledger can reference at
all, so it is the only one a claim can be held to -- and because a merge-base
does not move when the integration branch merely advances, an unrelated lane
landing can no longer re-stale anybody, and a fresher fetch can no longer
worsen the verdict.  A collision that lands beyond the observed head is not
lost: it is refused at the moment the goals branch integrates it, which is what
the directive means by "the completed integration control".

So a claim that merely lags is fine; a claim whose reserved territory moved
under it is refused, by name, with the commit and path that took it, and with
the refresh command that repairs it.  Both halves are mutation-proved in
``scripts/tests/two_language_claim_ledger_test.py``.

WHAT THIS STILL DOES NOT BOUND, stated rather than implied: nothing forces the
goals branch to merge the integration branch, so a ledger that never integrates
keeps an ancient observed head and its claims stay green while ``main`` churns
their reserved files.  The lag is REPORTED as a note on every run, and the
collision refuses the moment the goals branch merges.  This is not a regression
-- under the old rule that ledger could not be green at all, so no refusal is
lost -- but a rule that bounded the lag would have to be a clock rule again, and
it would deadlock on exactly the merge conflict measured above.  If that bound
is wanted it belongs on the goals branch's own integration cadence, not here.

LEASE EXPIRY IS A CLIFF, AND UNTIL 2026-09-01 IT ARRIVED WITHOUT AN APPROACH
---------------------------------------------------------------------------

An expired active lease is an ERROR, and this lane runs in the ``fast``, ``push``
and ``release`` profiles -- so the moment a lease lapses, every push in every
repo that runs the lane is refused until the ledger records that claim's fate.
That is the correct behaviour for a reservation nobody is renewing.  What was
missing is that it said NOTHING beforehand: the run before the lapse and the run
a year before it were byte-identical, so the first news of a fleet-wide stop was
the stop.

That defect is independent of who owns the claims, and it is made worse by how
leases actually move.  Measured over the ledger's whole first-parent history on
2026-09-01: ``lease_expires_at`` changed exactly TWICE in 47 children, both times
as a bulk operator bump that set every then-active claim to ONE round wall-clock
instant (``5541299649`` -> 2026-09-03T20:00-07:00, ``0b16376af6`` ->
2026-09-04T00:00-07:00).  The 44 children in between are titled "renew active
claims" and move ``base_revision``, never the lease.  So a lease is in practice a
mint-time TTL, claims minted together lapse together, and the ledger had eight
active claims expiring inside one 11-hour window.

``--lease-warn-hours`` is the approach.  Every active claim whose lease falls
inside the horizon produces a ``WARN:`` line -- on stdout when the ledger is
otherwise valid, on stderr when it is not -- naming the claim, its owner, the
instant, and the time remaining; claims sharing an instant are additionally
reported as a cluster, because that is the shape that turns one lapse into a
fleet stop.  A warning is never an error: the horizon must not become a second,
earlier cliff.  ``0`` disables it.

The warning is only as good as its delivery, and the harness prints nothing at
all from a lane that PASSES.  ``tests/run_trust_comprehensive_harness.sh``
therefore surfaces ``WARN:`` lines out of a passing lane's log; that half is
controlled end-to-end by ``scripts/tests/gate_warning_surface_test.sh``, and
this half -- fires inside the horizon, SILENT outside it, and names only the
claims that are actually close -- by
``scripts/tests/two_language_claim_ledger_test.py``.

Examples::

    python3 scripts/check_two_language_claim_ledger.py \
      --claims-dir coordination/claims --integration-ref HEAD

    python3 scripts/check_two_language_claim_ledger.py \
      --ledger-ref refs/remotes/origin/goals/TRUST-TWO-LANGUAGE-100 \
      --integration-ref origin/main --require-mirrors \
      --mirror-ref-prefix refs/remotes/origin/claims

Exit codes: 0 valid, 1 invalid ledger, 2 invocation/environment failure.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import sys
import unicodedata
from dataclasses import dataclass, field
from datetime import datetime, timedelta, timezone
from pathlib import Path, PurePosixPath
from typing import Any, Dict, Iterable, List, Mapping, Optional, Sequence, Set, Tuple


GOAL_ID = "TRUST-TWO-LANGUAGE-100"
SCHEMA = "trust.two-language.work-claim/v1"
LEDGER_REF = "refs/heads/goals/TRUST-TWO-LANGUAGE-100"
CLAIM_TREE_DIR = "coordination/claims"
VALIDATOR_PATH = "scripts/check_two_language_claim_ledger.py"
REFRESH_TOOL = "scripts/refresh_two_language_claim_bases.py"
# A manifest command string is fixed and gets no stdin, so scripts/hooks/pre-push
# exports the "<local-ref> <local-sha> <remote-ref> <remote-sha>" lines git feeds
# it. Mirrors fast.revert-rationale / fast.measurement-provenance /
# fast.pin-regression / fast.dependency-constellation /
# fast.submodule-remote-reachability.
PUSH_REFS_ENV = "TRUST_PUSHED_REFS"
DEFAULT_PUSH_INTEGRATION_REF = "refs/heads/main"
BOOTSTRAP_COMMIT = "e6f6f1e9c465b54a639154e18642fe5a086fbe4d"
MAX_CLAIM_BYTES = 1_048_576
MAX_JSON_DEPTH = 64
MAX_HISTORY_COMMITS = 10_000
MAX_ACTIVE_LEASE = timedelta(hours=72)
# How far ahead of a lapse this gate says so. See the LEASE EXPIRY block in the
# module docstring: expiry was a cliff with no approach, and the approach is the
# only part a lane can act on. 48 of the 72-hour policy maximum means a claim
# spends its last two thirds announcing itself.
DEFAULT_LEASE_WARN_HOURS = 48.0

REQUIRED_LEDGER_PATHS = {
    "AGENTS.md",
    "docs/TWO_LANGUAGE_100_PERCENT_GOAL.md",
    VALIDATOR_PATH,
}
REQUIRED_KEYS = {
    "schema",
    "claim_id",
    "goal_id",
    "ledger_ref",
    "owner",
    "base_revision",
    "integration_head",
    "owning_branch",
    "exact_files",
    "semantic_boundary",
    "dependencies",
    "baseline_population",
    "expected_population",
    "expected_evidence",
    "narrow_validation_rung",
    "downstream_gate_not_exercised",
    "tcb_change",
    "created_at",
    "lease_expires_at",
    "status",
}
OPTIONAL_KEYS = {"validation_at_integration"}
ALLOWED_KEYS = REQUIRED_KEYS | OPTIONAL_KEYS
IMMUTABLE_KEYS = {
    "schema",
    "claim_id",
    "goal_id",
    "ledger_ref",
    "owner",
    "owning_branch",
    "created_at",
    "semantic_boundary",
    "dependencies",
    "baseline_population",
    "tcb_change",
}
TERMINAL_STATUSES = {"released", "abandoned"}
ALL_STATUSES = {"active"} | TERMINAL_STATUSES

CLAIM_ID_RE = re.compile(
    r"^TRUST-TWO-LANGUAGE-100/(W[0-7])/([a-z0-9][a-z0-9-]{0,95})$"
)
HEX40_RE = re.compile(r"^[0-9a-f]{40}$")
CONTROL_RE = re.compile(r"[\x00-\x1f\x7f]")
RFC3339_RE = re.compile(
    r"^\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}(?:\.\d{1,9})?(?:Z|[+-]\d{2}:\d{2})$"
)
SAFE_REVISION_RE = re.compile(
    r"^(?:[0-9a-f]{40}|HEAD|refs/[A-Za-z0-9._/-]+|[A-Za-z0-9][A-Za-z0-9._/-]*)$"
)


class DuplicateJsonKey(ValueError):
    pass


class GitFailure(RuntimeError):
    pass


@dataclass
class Claim:
    path: str
    data: Dict[str, Any]

    @property
    def claim_id(self) -> str:
        value = self.data.get("claim_id")
        return value if isinstance(value, str) else f"<invalid:{self.path}>"

    @property
    def status(self) -> str:
        value = self.data.get("status")
        return value if isinstance(value, str) else "<invalid>"


@dataclass
class Report:
    source: str
    integration_commit: Optional[str] = None
    ledger_commit: Optional[str] = None
    claim_count: int = 0
    active_count: int = 0
    errors: List[str] = field(default_factory=list)
    notes: List[str] = field(default_factory=list)
    warnings: List[str] = field(default_factory=list)

    @property
    def valid(self) -> bool:
        return not self.errors

    def as_dict(self) -> Dict[str, Any]:
        return {
            "schema": "trust.two-language.claim-ledger-check/v1",
            "valid": self.valid,
            "source": self.source,
            "integration_commit": self.integration_commit,
            "ledger_commit": self.ledger_commit,
            "claim_count": self.claim_count,
            "active_count": self.active_count,
            "errors": self.errors,
            "notes": self.notes,
            "warnings": self.warnings,
        }


def _strict_object(pairs: Sequence[Tuple[str, Any]]) -> Dict[str, Any]:
    result: Dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise DuplicateJsonKey(f"duplicate JSON key {key!r}")
        result[key] = value
    return result


def strict_json_loads(raw: bytes, label: str) -> Dict[str, Any]:
    if len(raw) > MAX_CLAIM_BYTES:
        raise ValueError(f"{label}: claim exceeds {MAX_CLAIM_BYTES} bytes")
    try:
        text = raw.decode("utf-8", "strict")
    except UnicodeDecodeError as exc:
        raise ValueError(f"{label}: claim is not UTF-8: {exc}") from exc

    def reject_constant(value: str) -> None:
        raise ValueError(f"non-finite JSON number {value!r}")

    try:
        value = json.loads(
            text,
            object_pairs_hook=_strict_object,
            parse_constant=reject_constant,
        )
    except (json.JSONDecodeError, DuplicateJsonKey, ValueError) as exc:
        raise ValueError(f"{label}: invalid strict JSON: {exc}") from exc
    if not isinstance(value, dict):
        raise ValueError(f"{label}: top-level value must be an object")

    def depth(item: Any, current: int = 0) -> int:
        if current > MAX_JSON_DEPTH:
            raise ValueError(f"{label}: JSON nesting exceeds {MAX_JSON_DEPTH}")
        if isinstance(item, dict):
            for key, child in item.items():
                depth(key, current + 1)
                depth(child, current + 1)
        elif isinstance(item, list):
            for child in item:
                depth(child, current + 1)
        return current

    depth(value)
    return value


def _git(
    repo: Path,
    args: Sequence[str],
    check: bool = True,
    input_bytes: Optional[bytes] = None,
) -> subprocess.CompletedProcess:
    env = os.environ.copy()
    env["GIT_OPTIONAL_LOCKS"] = "0"
    env["GIT_NO_REPLACE_OBJECTS"] = "1"
    env["LC_ALL"] = "C"
    try:
        result = subprocess.run(
            ["git", "-C", str(repo), *args],
            input=input_bytes,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            check=False,
            timeout=30,
            env=env,
        )
    except (OSError, subprocess.TimeoutExpired) as exc:
        raise GitFailure(f"git {' '.join(args)} failed to execute: {exc}") from exc
    if check and result.returncode != 0:
        stderr = result.stderr.decode("utf-8", "replace").strip()
        raise GitFailure(
            f"git {' '.join(args)} exited {result.returncode}: {stderr or '<no stderr>'}"
        )
    return result


def resolve_commit(repo: Path, revision: str) -> str:
    if (
        not revision
        or revision.startswith("-")
        or CONTROL_RE.search(revision)
        or not SAFE_REVISION_RE.fullmatch(revision)
        or ".." in revision
        or "//" in revision
        or revision.endswith(("/", "."))
    ):
        raise GitFailure(f"unsafe or empty revision {revision!r}")
    result = _git(
        repo,
        ["rev-parse", "--verify", "--quiet", "--end-of-options", f"{revision}^{{commit}}"],
        False,
    )
    if result.returncode != 0:
        raise GitFailure(f"revision {revision!r} does not resolve to a commit")
    value = result.stdout.decode("ascii", "strict").strip()
    if not HEX40_RE.fullmatch(value):
        raise GitFailure(f"revision {revision!r} resolved to malformed object id {value!r}")
    return value


def is_ancestor(repo: Path, older: str, newer: str) -> bool:
    result = _git(repo, ["merge-base", "--is-ancestor", older, newer], False)
    if result.returncode not in (0, 1):
        stderr = result.stderr.decode("utf-8", "replace").strip()
        raise GitFailure(
            f"could not compare ancestry {older}..{newer}: {stderr or result.returncode}"
        )
    return result.returncode == 0


def paths_changed_between(
    repo: Path, older: str, newer: str, paths: Sequence[str]
) -> List[str]:
    """Every path under ``paths`` whose blob/gitlink differs between two trees.

    This is the byte-identical-tree test the ledger operator has been writing
    out by hand in every sync commit's ``validation_at_integration.results``.
    A change that is later reverted leaves the tree identical and is therefore
    NOT a territory move, which is the operator's own criterion.

    ``--ignore-submodules=none`` is not optional.  This repository's local
    config sets ``diff.ignoreSubmodules = all`` and ``submodule.<name>.ignore =
    all`` for every sibling (see CLAUDE.md), so without the override a claim
    reserving a ``first-party/*`` gitlink -- W3 reserves ``first-party/ty``
    today -- would have its territory check silently blinded by clone-local
    configuration.
    """
    if not paths:
        return []
    result = _git(
        repo,
        [
            "diff",
            "--name-only",
            "-z",
            "--ignore-submodules=none",
            "--end-of-options",
            older,
            newer,
            "--",
            *paths,
        ],
    )
    changed: List[str] = []
    for row in result.stdout.split(b"\0"):
        if not row:
            continue
        try:
            changed.append(row.decode("utf-8", "strict"))
        except UnicodeDecodeError as exc:
            raise GitFailure(f"malformed diff path between {older} and {newer}: {exc}")
    return sorted(set(changed))


def commits_touching(
    repo: Path, older: str, newer: str, paths: Sequence[str], limit: int = 4
) -> List[str]:
    """``<short-sha> <subject>`` for the commits that moved ``paths``.

    Explanation only: the refusal is decided by :func:`paths_changed_between`.
    A range can diff non-empty while ``git log`` names nothing (a merge that
    resolves the path), so an empty list here never suppresses a refusal.
    """
    if not paths:
        return []
    result = _git(
        repo,
        [
            "log",
            f"--max-count={limit}",
            "--format=%h %s",
            "--end-of-options",
            f"{older}..{newer}",
            "--",
            *paths,
        ],
        False,
    )
    if result.returncode != 0:
        return []
    return [
        line.strip()
        for line in result.stdout.decode("utf-8", "replace").splitlines()
        if line.strip()
    ]


def merge_base(repo: Path, left: str, right: str) -> str:
    result = _git(repo, ["merge-base", "--end-of-options", left, right], False)
    value = result.stdout.decode("ascii", "replace").strip()
    if result.returncode != 0 or not HEX40_RE.fullmatch(value):
        stderr = result.stderr.decode("utf-8", "replace").strip()
        raise GitFailure(f"no merge base for {left} and {right}: {stderr or 'unrelated histories'}")
    return value


def count_commits(repo: Path, older: str, newer: str) -> int:
    result = _git(repo, ["rev-list", "--count", "--end-of-options", f"{older}..{newer}"], False)
    try:
        return int(result.stdout.decode("ascii", "replace").strip())
    except ValueError:
        return -1


def first_parent(repo: Path, commit: str) -> Optional[str]:
    line = _git(repo, ["rev-list", "--parents", "-n", "1", commit]).stdout
    fields = line.decode("ascii", "strict").strip().split()
    return fields[1] if len(fields) > 1 else None


def commit_parents(repo: Path, commit: str) -> List[str]:
    line = _git(repo, ["rev-list", "--parents", "-n", "1", commit]).stdout
    fields = line.decode("ascii", "strict").strip().split()
    return fields[1:]


def is_first_parent_ancestor(repo: Path, older: str, newer: str) -> bool:
    cursor: Optional[str] = newer
    for _depth in range(MAX_HISTORY_COMMITS):
        if cursor == older:
            return True
        if cursor is None:
            return False
        cursor = first_parent(repo, cursor)
    raise GitFailure(f"first-parent history exceeds {MAX_HISTORY_COMMITS} commits")


def validate_repo_safety(repo: Path) -> None:
    shallow = _git(repo, ["rev-parse", "--is-shallow-repository"]).stdout
    if shallow.decode("ascii", "strict").strip() == "true":
        raise GitFailure("claim-ledger validation refuses a shallow repository")

    graft_path = _git(repo, ["rev-parse", "--git-path", "info/grafts"]).stdout
    graft = Path(graft_path.decode("utf-8", "strict").strip())
    if not graft.is_absolute():
        graft = repo / graft
    if graft.is_file() and graft.stat().st_size:
        raise GitFailure("claim-ledger validation refuses .git/info/grafts")

    replacements = _git(repo, ["for-each-ref", "--format=%(refname)", "refs/replace/"])
    if replacements.stdout.strip():
        raise GitFailure("claim-ledger validation refuses repositories with replace refs")


def tree_has_path(repo: Path, commit: str, path: str) -> bool:
    result = _git(repo, ["cat-file", "-e", f"{commit}:{path}"], False)
    return result.returncode == 0


def tree_entry_mode(repo: Path, commit: str, path: str) -> Optional[str]:
    result = _git(repo, ["ls-tree", "-z", commit, "--", path])
    for row in result.stdout.split(b"\0"):
        if not row:
            continue
        try:
            meta, raw_path = row.split(b"\t", 1)
            mode, _kind, _object_id = meta.decode("ascii", "strict").split()
            actual_path = raw_path.decode("utf-8", "strict")
        except (ValueError, UnicodeDecodeError) as exc:
            raise GitFailure(f"malformed ls-tree row for {path!r}: {exc}") from exc
        if actual_path == path:
            return mode
    return None


def tree_has_regular_blob(repo: Path, commit: str, path: str) -> bool:
    return tree_entry_mode(repo, commit, path) == "100644"


def read_blob(repo: Path, commit: str, path: str) -> bytes:
    result = _git(repo, ["cat-file", "blob", f"{commit}:{path}"])
    if len(result.stdout) > MAX_CLAIM_BYTES:
        raise GitFailure(f"{commit}:{path} exceeds {MAX_CLAIM_BYTES} bytes")
    return result.stdout


def claim_documents_from_tree(repo: Path, commit: str) -> Dict[str, bytes]:
    result = _git(
        repo,
        ["ls-tree", "-r", "-z", "--full-tree", commit, "--", CLAIM_TREE_DIR],
    )
    documents: Dict[str, bytes] = {}
    for row in result.stdout.split(b"\0"):
        if not row:
            continue
        try:
            meta, raw_path = row.split(b"\t", 1)
            mode, kind, _object_id = meta.decode("ascii", "strict").split()
            path = raw_path.decode("utf-8", "strict")
        except (ValueError, UnicodeDecodeError) as exc:
            raise GitFailure(f"malformed ls-tree claim row {row!r}: {exc}") from exc
        if kind != "blob" or mode != "100644":
            raise GitFailure(f"claim entry {path!r} must be a non-executable regular blob")
        parent = str(PurePosixPath(path).parent)
        if parent != CLAIM_TREE_DIR or not path.endswith(".json"):
            raise GitFailure(f"unexpected entry in claim directory: {path!r}")
        documents[path] = read_blob(repo, commit, path)
    return documents


def claim_documents_from_directory(repo: Path, directory: Path) -> Dict[str, bytes]:
    root = directory if directory.is_absolute() else repo / directory
    if not root.is_dir():
        raise ValueError(f"claim directory does not exist: {root}")
    documents: Dict[str, bytes] = {}
    for entry in sorted(root.iterdir(), key=lambda item: item.name):
        if entry.is_symlink() or not entry.is_file() or entry.suffix != ".json":
            raise ValueError(f"unexpected entry in claim directory: {entry}")
        relative = entry.relative_to(repo).as_posix()
        raw = entry.read_bytes()
        if len(raw) > MAX_CLAIM_BYTES:
            raise ValueError(f"{relative}: claim exceeds {MAX_CLAIM_BYTES} bytes")
        documents[relative] = raw
    return documents


def parse_timestamp(value: Any, label: str) -> datetime:
    if not isinstance(value, str) or not value or not RFC3339_RE.fullmatch(value):
        raise ValueError(f"{label} must be a non-empty RFC3339 timestamp")
    candidate = value[:-1] + "+00:00" if value.endswith("Z") else value
    try:
        parsed = datetime.fromisoformat(candidate)
    except ValueError as exc:
        raise ValueError(f"{label} is not RFC3339: {value!r}") from exc
    if parsed.tzinfo is None or parsed.utcoffset() is None:
        raise ValueError(f"{label} must include an explicit UTC offset")
    return parsed.astimezone(timezone.utc)


def expected_claim_path(claim_id: str) -> Optional[str]:
    match = CLAIM_ID_RE.fullmatch(claim_id)
    if not match:
        return None
    workstream, increment = match.groups()
    return f"{CLAIM_TREE_DIR}/{GOAL_ID}.{workstream}.{increment}.json"


def validate_exact_path(value: Any, label: str) -> Optional[str]:
    if not isinstance(value, str) or not value:
        return f"{label} must be a non-empty string"
    if len(value.encode("utf-8")) > 512:
        return f"{label} exceeds 512 UTF-8 bytes"
    if value != unicodedata.normalize("NFC", value):
        return f"{label} must use Unicode NFC"
    if "\\" in value or CONTROL_RE.search(value):
        return f"{label} contains a backslash or control character"
    if value.endswith("/") or value.startswith("/"):
        return f"{label} must be a normalized repository-relative file path"
    raw_parts = value.split("/")
    if any(part in ("", ".", "..") for part in raw_parts):
        return f"{label} contains an empty, '.' or '..' component"
    parsed = PurePosixPath(value)
    if parsed.is_absolute() or parsed.as_posix() != value:
        return f"{label} is not a normalized repository-relative POSIX path"
    if raw_parts[0] == ".git" or value.startswith(f"{CLAIM_TREE_DIR}/"):
        return f"{label} targets reserved Git/coordination state"
    return None


def paths_overlap(left: str, right: str) -> bool:
    left_key = unicodedata.normalize("NFC", left).casefold()
    right_key = unicodedata.normalize("NFC", right).casefold()
    return (
        left_key == right_key
        or left_key.startswith(right_key + "/")
        or right_key.startswith(left_key + "/")
    )


def _nonempty_string(data: Mapping[str, Any], key: str, label: str, errors: List[str]) -> None:
    value = data.get(key)
    if not isinstance(value, str) or not value.strip():
        errors.append(f"{label}.{key} must be a non-empty string")
    elif CONTROL_RE.search(value):
        errors.append(f"{label}.{key} must not contain control characters")


def _string_list(
    value: Any,
    label: str,
    errors: List[str],
    require_nonempty: bool,
) -> List[str]:
    if not isinstance(value, list):
        errors.append(f"{label} must be an array of strings")
        return []
    if require_nonempty and not value:
        errors.append(f"{label} must not be empty")
    strings: List[str] = []
    for index, item in enumerate(value):
        if not isinstance(item, str) or not item.strip():
            errors.append(f"{label}[{index}] must be a non-empty string")
        elif CONTROL_RE.search(item):
            errors.append(f"{label}[{index}] must not contain control characters")
        else:
            strings.append(item)
    if len(set(strings)) != len(strings):
        errors.append(f"{label} contains duplicate values")
    return strings


class LedgerValidator:
    def __init__(
        self,
        repo: Path,
        integration_commit: str,
        now: datetime,
        ledger_commit: Optional[str] = None,
        bootstrap_commit: Optional[str] = None,
        observed_commit: Optional[str] = None,
        lease_warn: timedelta = timedelta(hours=DEFAULT_LEASE_WARN_HOURS),
    ) -> None:
        self.repo = repo
        self.integration_commit = integration_commit
        # The newest point on the integration line the LEDGER ITSELF observes.
        # See validate_active_base: judging a ledger commit against a tip it
        # structurally cannot reference is what made this gate unsatisfiable.
        self.observed_commit = observed_commit or integration_commit
        self.now = now.astimezone(timezone.utc)
        self.ledger_commit = ledger_commit
        self.bootstrap_commit = bootstrap_commit
        self.lease_warn = lease_warn
        self.errors: List[str] = []
        self.notes: List[str] = []
        self.warnings: List[str] = []
        self._commit_cache: Dict[str, Optional[str]] = {}

    def error(self, message: str) -> None:
        self.errors.append(message)

    def warn(self, message: str) -> None:
        self.warnings.append(message)

    def resolve_claim_commit(self, revision: str, label: str) -> Optional[str]:
        if revision in self._commit_cache:
            return self._commit_cache[revision]
        try:
            resolved = resolve_commit(self.repo, revision)
        except GitFailure as exc:
            self.error(f"{label}: {exc}")
            resolved = None
        self._commit_cache[revision] = resolved
        return resolved

    def parse_claims(self, documents: Mapping[str, bytes]) -> Dict[str, Claim]:
        if not documents:
            self.error("claim ledger contains zero claim records")
            return {}
        claims: Dict[str, Claim] = {}
        for path in sorted(documents):
            try:
                data = strict_json_loads(documents[path], path)
            except ValueError as exc:
                self.error(str(exc))
                continue
            claim = Claim(path=path, data=data)
            self.validate_claim_shape(claim)
            if claim.claim_id in claims:
                self.error(
                    f"duplicate claim_id {claim.claim_id!r} in {claims[claim.claim_id].path} "
                    f"and {path}"
                )
            else:
                claims[claim.claim_id] = claim
        return claims

    def validate_claim_shape(self, claim: Claim) -> None:
        data = claim.data
        label = claim.path
        missing = sorted(REQUIRED_KEYS - set(data))
        unknown = sorted(set(data) - ALLOWED_KEYS)
        if missing:
            self.error(f"{label}: missing required keys: {', '.join(missing)}")
        if unknown:
            self.error(f"{label}: unknown keys require a schema bump: {', '.join(unknown)}")

        if data.get("schema") != SCHEMA:
            self.error(f"{label}.schema must equal {SCHEMA!r}")
        if data.get("goal_id") != GOAL_ID:
            self.error(f"{label}.goal_id must equal {GOAL_ID!r}")
        if data.get("ledger_ref") != LEDGER_REF:
            self.error(f"{label}.ledger_ref must equal {LEDGER_REF!r}")

        claim_id = data.get("claim_id")
        if not isinstance(claim_id, str) or not CLAIM_ID_RE.fullmatch(claim_id):
            self.error(f"{label}.claim_id is not a canonical {GOAL_ID}/W<0-7>/<increment> id")
        else:
            expected = expected_claim_path(claim_id)
            if expected != label:
                self.error(f"{label}: filename does not match claim_id; expected {expected}")

        for key in (
            "owner",
            "owning_branch",
            "semantic_boundary",
            "narrow_validation_rung",
            "downstream_gate_not_exercised",
            "tcb_change",
        ):
            _nonempty_string(data, key, label, self.errors)
        tcb_change = data.get("tcb_change")
        if isinstance(tcb_change, str) and not (
            tcb_change == "none"
            or (tcb_change.startswith("yes: ") and bool(tcb_change[5:].strip()))
        ):
            self.error(f"{label}.tcb_change must be 'none' or 'yes: <disclosure>'")

        for key in ("base_revision", "integration_head"):
            value = data.get(key)
            if not isinstance(value, str) or not HEX40_RE.fullmatch(value):
                self.error(f"{label}.{key} must be a lowercase 40-hex commit id")

        exact_files = _string_list(data.get("exact_files"), f"{label}.exact_files", self.errors, True)
        for index, path in enumerate(exact_files):
            problem = validate_exact_path(path, f"{label}.exact_files[{index}]")
            if problem:
                self.error(problem)
        for left_index, left in enumerate(exact_files):
            for right in exact_files[left_index + 1 :]:
                if paths_overlap(left, right):
                    self.error(f"{label}.exact_files has overlapping entries {left!r} and {right!r}")

        dependencies = _string_list(
            data.get("dependencies"), f"{label}.dependencies", self.errors, False
        )
        for dependency in dependencies:
            if not CLAIM_ID_RE.fullmatch(dependency):
                self.error(f"{label}.dependencies contains non-canonical id {dependency!r}")
            if dependency == claim_id:
                self.error(f"{label}.dependencies must not contain its own claim_id")

        for key in ("baseline_population", "expected_population"):
            value = data.get(key)
            if not isinstance(value, dict) or not value:
                self.error(f"{label}.{key} must be a non-empty object")
        _string_list(
            data.get("expected_evidence"),
            f"{label}.expected_evidence",
            self.errors,
            True,
        )

        status = data.get("status")
        if status not in ALL_STATUSES:
            self.error(f"{label}.status must be one of {sorted(ALL_STATUSES)}")

        created: Optional[datetime] = None
        lease: Optional[datetime] = None
        try:
            created = parse_timestamp(data.get("created_at"), f"{label}.created_at")
        except ValueError as exc:
            self.error(str(exc))
        try:
            lease = parse_timestamp(data.get("lease_expires_at"), f"{label}.lease_expires_at")
        except ValueError as exc:
            self.error(str(exc))
        if created and lease and lease <= created:
            self.error(f"{label}.lease_expires_at must be after created_at")
        if status == "active" and lease and lease - self.now > MAX_ACTIVE_LEASE:
            self.error(
                f"{label}: remaining active lease exceeds the 72-hour policy maximum"
            )
        if created and created > self.now:
            self.error(f"{label}.created_at is in the future relative to --now")

        validation = data.get("validation_at_integration")
        if validation is not None:
            if not isinstance(validation, dict):
                self.error(f"{label}.validation_at_integration must be an object")
            else:
                expected_keys = {"integration_head", "observed_at", "results", "limitations"}
                if set(validation) != expected_keys:
                    self.error(
                        f"{label}.validation_at_integration must contain exactly "
                        f"{sorted(expected_keys)}"
                    )
                if validation.get("integration_head") != data.get("integration_head"):
                    self.error(
                        f"{label}.validation_at_integration.integration_head must equal "
                        "the claim integration_head"
                    )
                try:
                    observed = parse_timestamp(
                        validation.get("observed_at"),
                        f"{label}.validation_at_integration.observed_at",
                    )
                    if observed > self.now:
                        self.error(f"{label}.validation_at_integration.observed_at is in the future")
                    if created and observed < created:
                        self.error(
                            f"{label}.validation_at_integration.observed_at precedes created_at"
                        )
                except ValueError as exc:
                    self.error(str(exc))
                _string_list(
                    validation.get("results"),
                    f"{label}.validation_at_integration.results",
                    self.errors,
                    True,
                )
                _string_list(
                    validation.get("limitations"),
                    f"{label}.validation_at_integration.limitations",
                    self.errors,
                    False,
                )

    def validate_active_base(
        self,
        claim: Claim,
        base_commit: Optional[str],
        claim_integration_commit: Optional[str],
    ) -> None:
        """The two refusals an active claim's recorded base must survive.

        1. ON THE LINE.  ``base_revision`` and ``integration_head`` must be
           ancestors of the OBSERVED integration head.  A base that is not is a
           claim reserving work against a fork, a rewound commit, or a sha this
           integration line never carried -- and until this rule existed it was
           only ever refused incidentally, because the equality check made the
           ancestry question vacuous.

        2. TERRITORY INTACT.  The observed integration head's tree must be
           byte-identical to the base's over every reserved path.  This is the
           property the directive actually names -- another machine changing the
           residue, denominator or prerequisite under an in-flight increment --
           and it is per-claim, so a lane that lands nowhere near a reservation
           does not invalidate it.

        WHY "OBSERVED", AND WHY THE OLD RULE COULD NOT BE SATISFIED AT ALL.
        ``validate_current`` separately requires every claim's
        ``integration_head`` to be an ancestor of the LEDGER commit, and
        ``base_revision`` must be an ancestor of ``integration_head``.  So the
        newest revision an active claim is even ALLOWED to name is
        ``merge-base(ledger commit, integration ref)``.  The old rule demanded
        it name the integration ref's TIP.  Whenever the goals branch was not
        already merged up -- its normal state, since it carries producer
        commits of its own -- those two rules contradicted each other, and the
        only way to satisfy both was a merge of the integration branch into the
        goals branch.  Measured 2026-09-01: the claims already named
        ``142906f4a355``, which IS ``merge-base(ledger, origin/main)`` exactly,
        so they were as fresh as the ledger could express; and that merge did
        not apply cleanly (``scripts/trust_ir_producer_ui_pins.txt`` conflicts).
        A lane polling for the push window to open was waiting on something no
        amount of waiting produces.

        Judging against the observed head also removes the incentive inversion
        by construction: ``merge-base(ledger, main)`` does not move when ``main``
        advances, so an unrelated lane landing cannot re-stale anybody, and a
        fresher fetch cannot worsen the verdict.
        """
        for label, commit in (
            ("base_revision", base_commit),
            ("integration_head", claim_integration_commit),
        ):
            if not commit:
                continue
            try:
                if not is_ancestor(self.repo, commit, self.observed_commit):
                    self.error(
                        f"{claim.path}: active {label} {commit[:12]} is not an ancestor of "
                        f"the observed integration head {self.observed_commit[:12]}; the claim "
                        "is based on a diverged, rewound, or foreign revision. Re-take the "
                        "claim against the integration line."
                    )
            except GitFailure as exc:
                self.error(f"{claim.path}: active {label}: {exc}")

        if not base_commit:
            return
        try:
            if not is_ancestor(self.repo, base_commit, self.observed_commit):
                return
        except GitFailure:
            return

        exact_files = claim.data.get("exact_files")
        reserved = (
            [item for item in exact_files if isinstance(item, str) and item]
            if isinstance(exact_files, list)
            else []
        )
        if not reserved:
            return
        try:
            moved = paths_changed_between(
                self.repo, base_commit, self.observed_commit, reserved
            )
        except GitFailure as exc:
            self.error(f"{claim.path}: reserved-path comparison failed: {exc}")
            return
        if not moved:
            return
        witnesses = commits_touching(
            self.repo, base_commit, self.observed_commit, moved
        )
        detail = "; ".join(witnesses) if witnesses else "(no single-parent commit; merge resolution)"
        self.error(
            f"{claim.path}: active base_revision {base_commit[:12]} is OVERTAKEN -- "
            f"reserved path(s) {', '.join(moved[:4])} changed between it and the observed "
            f"integration head {self.observed_commit[:12]} [{detail}]. Remeasure on the "
            f"integration commit and republish the claim, or advance the base with "
            f"`python3 {REFRESH_TOOL} --publish`, which refuses to move an overtaken "
            f"reservation without `--accept-overtaken` and publishes the acceptance when given."
        )

    def validate_current(self, claims: Mapping[str, Claim]) -> None:
        for claim_id, claim in claims.items():
            data = claim.data
            base = data.get("base_revision")
            integration = data.get("integration_head")
            base_commit = (
                self.resolve_claim_commit(base, f"{claim.path}.base_revision")
                if isinstance(base, str) and HEX40_RE.fullmatch(base)
                else None
            )
            integration_commit = (
                self.resolve_claim_commit(integration, f"{claim.path}.integration_head")
                if isinstance(integration, str) and HEX40_RE.fullmatch(integration)
                else None
            )
            if base_commit and integration_commit:
                try:
                    if not is_ancestor(self.repo, base_commit, integration_commit):
                        self.error(
                            f"{claim.path}: base_revision is not an ancestor of integration_head"
                        )
                except GitFailure as exc:
                    self.error(f"{claim.path}: {exc}")

            if claim.status == "active":
                self.validate_active_base(claim, base_commit, integration_commit)
                try:
                    lease = parse_timestamp(
                        data.get("lease_expires_at"), f"{claim.path}.lease_expires_at"
                    )
                    if lease <= self.now:
                        self.error(f"{claim.path}: active lease is expired")
                except ValueError:
                    pass

            if self.ledger_commit and integration_commit:
                try:
                    if not is_ancestor(self.repo, integration_commit, self.ledger_commit):
                        self.error(
                            f"{claim.path}: integration_head is not an ancestor of ledger commit"
                        )
                except GitFailure as exc:
                    self.error(f"{claim.path}: {exc}")

            exact_files = data.get("exact_files")
            if isinstance(exact_files, list):
                for owned_path in exact_files:
                    if not isinstance(owned_path, str) or validate_exact_path(owned_path, "path"):
                        continue
                    parts = owned_path.split("/")
                    for depth in range(1, len(parts)):
                        ancestor = "/".join(parts[:depth])
                        try:
                            if tree_entry_mode(self.repo, self.integration_commit, ancestor) == "120000":
                                self.error(
                                    f"{claim.path}.exact_files path {owned_path!r} has symlink "
                                    f"ancestor {ancestor!r}"
                                )
                                break
                        except GitFailure as exc:
                            self.error(f"{claim.path}.exact_files path {owned_path!r}: {exc}")
                            break

        active = [claim for claim in claims.values() if claim.status == "active"]
        for left_index, left in enumerate(active):
            left_files = left.data.get("exact_files")
            if not isinstance(left_files, list):
                continue
            for right in active[left_index + 1 :]:
                right_files = right.data.get("exact_files")
                if not isinstance(right_files, list):
                    continue
                for left_path in left_files:
                    if not isinstance(left_path, str):
                        continue
                    for right_path in right_files:
                        if isinstance(right_path, str) and paths_overlap(left_path, right_path):
                            self.error(
                                f"active claims {left.claim_id} and {right.claim_id} overlap at "
                                f"{left_path!r} / {right_path!r}"
                            )

        self.warn_on_approaching_leases(claims)
        self.validate_dependencies(claims)

    def warn_on_approaching_leases(self, claims: Mapping[str, Claim]) -> None:
        """Say a lapse is coming while it can still be acted on.

        An expired lease is refused above, and that refusal is fleet-wide: this
        lane carries the ``fast``, ``push`` and ``release`` profiles.  Before
        this existed the run before a lapse was byte-identical to the run a year
        before it, so a dated, synchronized fleet stop announced itself by
        stopping the fleet.

        Three rules keep this from becoming decoration.  It is never an error --
        a horizon that refuses is just an earlier cliff.  It reports only claims
        actually inside the horizon, so a run that warns about everything (or
        about nothing) is distinguishable from a run that warns about the two
        that matter.  And it names the CLUSTER separately, because claims minted
        together carry one instant, and one instant is what turns a lapse into a
        stop rather than a notice.
        """
        if self.lease_warn <= timedelta(0):
            return
        approaching: List[Tuple[datetime, str, Claim]] = []
        for claim_id in sorted(claims):
            claim = claims[claim_id]
            if claim.status != "active":
                continue
            try:
                lease = parse_timestamp(
                    claim.data.get("lease_expires_at"), f"{claim.path}.lease_expires_at"
                )
            except ValueError:
                continue
            remaining = lease - self.now
            if remaining <= timedelta(0) or remaining > self.lease_warn:
                continue
            approaching.append((lease, claim_id, claim))
        if not approaching:
            return
        for lease, claim_id, claim in sorted(approaching, key=lambda row: (row[0], row[1])):
            remaining = lease - self.now
            hours, seconds = divmod(int(remaining.total_seconds()), 3600)
            owner = claim.data.get("owner")
            owner_text = owner if isinstance(owner, str) else "<unreadable owner>"
            self.warn(
                f"lease-expiry: {claim_id} expires in {hours}h{seconds // 60:02d}m "
                f"({claim.data.get('lease_expires_at')}), owner {owner_text}. Renew it "
                "before then, or record its fate as released/abandoned; once it lapses "
                "this lane refuses every push in every repo that runs it."
            )
        by_instant: Dict[str, List[str]] = {}
        for _lease, claim_id, claim in approaching:
            instant = claim.data.get("lease_expires_at")
            if isinstance(instant, str):
                by_instant.setdefault(instant, []).append(claim_id)
        for instant in sorted(by_instant):
            shared = sorted(by_instant[instant])
            if len(shared) < 2:
                continue
            self.warn(
                f"lease-expiry CLUSTER: {len(shared)} active claims share the single "
                f"instant {instant} -- {', '.join(shared)}. They were minted or bumped "
                "together, so they lapse together and the refusal arrives as one "
                "fleet-wide stop rather than one claim's problem. Stagger them when you "
                "renew."
            )

    def validate_dependencies(self, claims: Mapping[str, Claim]) -> None:
        graph: Dict[str, List[str]] = {}
        for claim_id, claim in claims.items():
            raw_dependencies = claim.data.get("dependencies")
            dependencies = raw_dependencies if isinstance(raw_dependencies, list) else []
            graph[claim_id] = [item for item in dependencies if isinstance(item, str)]
            for dependency in graph[claim_id]:
                target = claims.get(dependency)
                if target is None:
                    self.error(f"{claim.path}: missing dependency claim {dependency}")
                # An abandoned dependent is a historical cancellation record, not a live
                # integration consumer. Its immutable dependency list must not pin a still-live
                # dependency's integration head or prevent that dependency from later being
                # abandoned. Missing IDs remain invalid above, and cycle detection still runs
                # over every record below.
                elif claim.status == "abandoned":
                    continue
                elif target.status == "abandoned":
                    self.error(f"{claim.path}: dependency {dependency} is abandoned")
                elif claim.status == "released" and target.status != "released":
                    self.error(
                        f"{claim.path}: released claim depends on non-released {dependency}"
                    )
                elif target is not None:
                    dependent_head = claim.data.get("integration_head")
                    dependency_head = target.data.get("integration_head")
                    if (
                        isinstance(dependent_head, str)
                        and HEX40_RE.fullmatch(dependent_head)
                        and isinstance(dependency_head, str)
                        and HEX40_RE.fullmatch(dependency_head)
                    ):
                        try:
                            if not is_ancestor(self.repo, dependency_head, dependent_head):
                                self.error(
                                    f"{claim.path}: dependency {dependency} integration_head "
                                    "is not an ancestor of the dependent"
                                )
                        except GitFailure as exc:
                            self.error(f"{claim.path}: dependency {dependency}: {exc}")

        visiting: Set[str] = set()
        visited: Set[str] = set()

        def visit(node: str, trail: List[str]) -> None:
            if node in visiting:
                cycle_start = trail.index(node) if node in trail else 0
                cycle = trail[cycle_start:] + [node]
                self.error(f"claim dependency cycle: {' -> '.join(cycle)}")
                return
            if node in visited:
                return
            visiting.add(node)
            for dependency in graph.get(node, []):
                if dependency in graph:
                    visit(dependency, trail + [node])
            visiting.remove(node)
            visited.add(node)

        for claim_id in sorted(graph):
            visit(claim_id, [])

    def compare_transition(
        self,
        previous_commit: str,
        previous: Mapping[str, Claim],
        current_commit: str,
        current: Mapping[str, Claim],
    ) -> None:
        previous_ids = set(previous)
        added_ids = sorted(set(current) - previous_ids)
        if len(added_ids) > 1:
            self.error(
                "ledger acquisition added multiple claim IDs in one child: "
                + ", ".join(added_ids)
            )
        for claim_id in added_ids:
            added = current[claim_id]
            if added.status != "active":
                self.error(f"new claim {claim_id} must be acquired with active status")
            raw_dependencies = added.data.get("dependencies")
            dependencies = raw_dependencies if isinstance(raw_dependencies, list) else []
            for dependency in dependencies:
                if isinstance(dependency, str) and dependency not in previous_ids:
                    self.error(
                        f"new claim {claim_id} depends on {dependency}, which did not exist "
                        "in the parent ledger"
                    )

        for claim_id in sorted(previous):
            if claim_id not in current:
                self.error(
                    f"ledger history removed claim {claim_id} between "
                    f"{previous_commit[:12]} and {current_commit[:12]}"
                )
                continue
            old = previous[claim_id]
            new = current[claim_id]
            for key in sorted(IMMUTABLE_KEYS):
                if old.data.get(key) != new.data.get(key):
                    self.error(
                        f"ledger history mutated immutable {claim_id}.{key} between "
                        f"{previous_commit[:12]} and {current_commit[:12]}"
                    )

            old_status = old.status
            new_status = new.status
            if old_status in TERMINAL_STATUSES:
                if new.data != old.data:
                    self.error(f"terminal claim {claim_id} was mutated or reactivated")
                continue
            if new_status not in ALL_STATUSES:
                continue

            old_files = old.data.get("exact_files")
            new_files = new.data.get("exact_files")
            if isinstance(old_files, list) and isinstance(new_files, list):
                removed = sorted(set(old_files) - set(new_files))
                if removed:
                    self.error(
                        f"active claim {claim_id} silently removed owned files: {removed}"
                    )

            old_evidence = old.data.get("expected_evidence")
            new_evidence = new.data.get("expected_evidence")
            if isinstance(old_evidence, list) and isinstance(new_evidence, list):
                removed_evidence = sorted(set(old_evidence) - set(new_evidence))
                if removed_evidence:
                    self.error(
                        f"active claim {claim_id} silently removed expected evidence: "
                        f"{removed_evidence}"
                    )

            try:
                old_lease = parse_timestamp(
                    old.data.get("lease_expires_at"), f"{old.path}.lease_expires_at"
                )
                new_lease = parse_timestamp(
                    new.data.get("lease_expires_at"), f"{new.path}.lease_expires_at"
                )
                if new_lease < old_lease:
                    self.error(f"claim {claim_id} shortened its lease")
            except ValueError:
                pass

            old_integration = old.data.get("integration_head")
            new_integration = new.data.get("integration_head")
            if (
                isinstance(old_integration, str)
                and HEX40_RE.fullmatch(old_integration)
                and isinstance(new_integration, str)
                and HEX40_RE.fullmatch(new_integration)
            ):
                try:
                    if not is_ancestor(self.repo, old_integration, new_integration):
                        self.error(f"claim {claim_id} rewound or diverged its integration_head")
                except GitFailure as exc:
                    self.error(f"claim {claim_id}: {exc}")

            old_base = old.data.get("base_revision")
            new_base = new.data.get("base_revision")
            if (
                isinstance(old_base, str)
                and HEX40_RE.fullmatch(old_base)
                and isinstance(new_base, str)
                and HEX40_RE.fullmatch(new_base)
            ):
                try:
                    if not is_ancestor(self.repo, old_base, new_base):
                        self.error(f"claim {claim_id} rewound or diverged its base_revision")
                except GitFailure as exc:
                    self.error(f"claim {claim_id}: {exc}")

    def validate_history(self, current_commit: str, current: Mapping[str, Claim]) -> None:
        if not self.bootstrap_commit:
            self.error("history validation requires an explicit bootstrap commit")
            return
        try:
            bootstrap = resolve_commit(self.repo, self.bootstrap_commit)
            if not is_first_parent_ancestor(self.repo, bootstrap, current_commit):
                self.error(
                    f"bootstrap commit {bootstrap} is not on the ledger first-parent chain"
                )
                return
        except GitFailure as exc:
            self.error(f"invalid bootstrap commit: {exc}")
            return

        child_commit = current_commit
        child_claims = current
        for _depth in range(MAX_HISTORY_COMMITS):
            if child_commit == bootstrap:
                self.notes.append(
                    f"history enforcement bootstrap boundary at {bootstrap[:12]} "
                    "(earlier lifecycle is explicitly grandfathered)"
                )
                return
            try:
                parents = commit_parents(self.repo, child_commit)
            except GitFailure as exc:
                self.error(f"ledger history {child_commit[:12]}: {exc}")
                return
            if not parents:
                self.error("ledger history reached a root before the bootstrap commit")
                return
            if len(parents) > 2:
                self.error(
                    f"ledger commit {child_commit[:12]} has {len(parents)} parents; "
                    "post-bootstrap octopus updates are forbidden"
                )
            if len(parents) == 2:
                active_heads = {
                    claim.data.get("integration_head")
                    for claim in child_claims.values()
                    if claim.status == "active"
                    and isinstance(claim.data.get("integration_head"), str)
                }
                if len(active_heads) == 1 and parents[1] not in active_heads:
                    expected_integration = next(iter(active_heads))
                    self.error(
                        f"ledger commit {child_commit[:12]} second parent is {parents[1]}, "
                        f"expected active integration head {expected_integration}"
                    )
            parent = parents[0]
            if parent != bootstrap and not tree_has_regular_blob(self.repo, parent, VALIDATOR_PATH):
                self.error(
                    f"ledger history parent {parent[:12]} lacks regular validator blob "
                    f"{VALIDATOR_PATH}"
                )
                return
            try:
                parent_documents = claim_documents_from_tree(self.repo, parent)
            except GitFailure as exc:
                self.error(f"ledger history {parent[:12]}: {exc}")
                return
            historical = LedgerValidator(
                repo=self.repo,
                integration_commit=self.integration_commit,
                now=self.now,
                ledger_commit=parent,
                bootstrap_commit=bootstrap,
            )
            parent_claims = historical.parse_claims(parent_documents)
            if historical.errors:
                self.errors.extend(
                    f"ledger history {parent[:12]}: {error}" for error in historical.errors
                )
                return
            self.compare_transition(parent, parent_claims, child_commit, child_claims)
            child_commit = parent
            child_claims = parent_claims
        self.error(f"ledger first-parent history exceeds {MAX_HISTORY_COMMITS} commits")

    def validate_mirrors(
        self,
        claims: Mapping[str, Claim],
        mirror_ref_prefix: str,
    ) -> None:
        if not self.ledger_commit:
            self.error("mirror validation requires a ledger commit")
            return
        prefix = mirror_ref_prefix.rstrip("/")
        if not prefix.startswith("refs/") or CONTROL_RE.search(prefix):
            self.error(f"unsafe mirror ref prefix {mirror_ref_prefix!r}")
            return

        known_refs: Set[str] = set()
        initial_targets: Dict[str, str] = {}
        for claim_id, claim in claims.items():
            mirror_ref = f"{prefix}/{claim_id}"
            known_refs.add(mirror_ref)
            try:
                mirror_commit = resolve_commit(self.repo, mirror_ref)
                initial_targets[mirror_ref] = mirror_commit
            except GitFailure as exc:
                self.error(f"claim mirror {mirror_ref}: {exc}")
                continue
            try:
                if not is_first_parent_ancestor(self.repo, mirror_commit, self.ledger_commit):
                    self.error(
                        f"claim mirror {mirror_ref} is not on the ledger first-parent chain"
                    )
            except GitFailure as exc:
                self.error(f"claim mirror {mirror_ref}: {exc}")
                continue
            try:
                mirrored = strict_json_loads(read_blob(self.repo, mirror_commit, claim.path), mirror_ref)
            except (GitFailure, ValueError) as exc:
                self.error(f"claim mirror {mirror_ref}: {exc}")
                continue
            if mirrored != claim.data:
                self.error(f"claim mirror {mirror_ref} does not carry the current claim record")

        result = _git(self.repo, ["for-each-ref", "--format=%(refname)", prefix])
        for line in result.stdout.decode("utf-8", "strict").splitlines():
            ref = line.strip()
            if ref and ref not in known_refs:
                self.error(f"orphan claim mirror not present in ledger: {ref}")
        for mirror_ref, initial in initial_targets.items():
            try:
                final = resolve_commit(self.repo, mirror_ref)
            except GitFailure as exc:
                self.error(f"claim mirror {mirror_ref} changed or disappeared: {exc}")
                continue
            if final != initial:
                self.error(f"claim mirror {mirror_ref} changed during validation")


def validate(
    repo: Path,
    documents: Mapping[str, bytes],
    integration_commit: str,
    now: datetime,
    source: str,
    ledger_commit: Optional[str] = None,
    check_history: bool = False,
    mirror_ref_prefix: Optional[str] = None,
    expected_parent: Optional[str] = None,
    bootstrap_commit: Optional[str] = None,
    lease_warn: timedelta = timedelta(hours=DEFAULT_LEASE_WARN_HOURS),
) -> Report:
    report = Report(
        source=source,
        integration_commit=integration_commit,
        ledger_commit=ledger_commit,
    )
    try:
        validate_repo_safety(repo)
    except GitFailure as exc:
        report.errors = [str(exc)]
        return report

    # The newest integration revision this ledger can legally reference. A
    # claim's integration_head must be contained in the ledger commit, so
    # holding an active claim to anything past the merge-base is holding it to
    # a sha it is separately forbidden to name. Candidate/worktree mode has no
    # ledger to bound it, and there the caller's ref IS the subject.
    observed_commit = integration_commit
    if ledger_commit:
        try:
            observed_commit = merge_base(repo, ledger_commit, integration_commit)
        except GitFailure as exc:
            report.errors = [
                f"ledger commit {ledger_commit[:12]} and integration head "
                f"{integration_commit[:12]} share no history: {exc}"
            ]
            return report
        if observed_commit != integration_commit:
            report.notes.append(
                f"observed integration head {observed_commit[:12]} = "
                f"merge-base(ledger, integration); the integration ref is "
                f"{count_commits(repo, observed_commit, integration_commit)} commit(s) "
                "ahead of what this ledger references"
            )

    validator = LedgerValidator(
        repo,
        integration_commit,
        now,
        ledger_commit,
        bootstrap_commit=bootstrap_commit,
        observed_commit=observed_commit,
        lease_warn=lease_warn,
    )
    claims = validator.parse_claims(documents)
    validator.validate_current(claims)

    if ledger_commit:
        for path in sorted(REQUIRED_LEDGER_PATHS):
            if not tree_has_regular_blob(repo, ledger_commit, path):
                validator.error(f"ledger commit is missing regular required blob {path}")
        if expected_parent:
            try:
                expected = resolve_commit(repo, expected_parent)
                actual = first_parent(repo, ledger_commit)
                if actual != expected:
                    validator.error(
                        f"ledger first parent is {actual}, expected serialized tip {expected}"
                    )
            except GitFailure as exc:
                validator.error(str(exc))
        if check_history:
            validator.validate_history(ledger_commit, claims)
        if mirror_ref_prefix:
            validator.validate_mirrors(claims, mirror_ref_prefix)
    elif check_history or mirror_ref_prefix or expected_parent:
        validator.error("history, mirror, and expected-parent checks require --ledger-ref")

    report.claim_count = len(claims)
    report.active_count = sum(claim.status == "active" for claim in claims.values())
    report.errors = validator.errors
    report.notes = report.notes + validator.notes
    report.warnings = validator.warnings
    return report


def pushed_remote_sha(integration_ref: str) -> Optional[Tuple[str, str]]:
    """``(remote-sha, reason)`` for the integration ref this push updates.

    ``reason`` is a human note for the ``SUBJECT:`` line.  ``None`` means no
    push is in flight at all.  A ``remote-sha`` of ``None`` inside the tuple is
    not representable: when a line exists but publishes nothing usable the
    caller is told, via ``reason``, that the subject WIDENED to the ref.
    """
    raw = os.environ.get(PUSH_REFS_ENV)
    if raw is None:
        return None
    for line in raw.splitlines():
        fields = line.split()
        if len(fields) < 4:
            continue
        remote_ref, remote_sha = fields[2], fields[3]
        if remote_ref != integration_ref:
            continue
        if not HEX40_RE.fullmatch(remote_sha):
            return ("", f"{remote_ref} carries a malformed remote sha {remote_sha!r}")
        if set(remote_sha) == {"0"}:
            return ("", f"{remote_ref} does not exist on the remote yet")
        return (remote_sha, "")
    return ("", f"this push updates no {integration_ref}")


def select_integration_commit(
    repo: Path, args: argparse.Namespace
) -> Tuple[str, Optional[str]]:
    """The integration head every read in this judgement takes.

    Default: whatever ``--integration-ref`` resolves to.  Under
    ``--push-context`` the subject is the sha the REMOTE actually holds for the
    integration branch, which git reports over the connection in the pre-push
    ref lines -- not this clone's ``refs/remotes/origin/main`` cache.

    That distinction is the whole point.  Reading the cache made a behind clone
    audit an older, systematically greener integration line than the one it was
    publishing into; under the equality rule it was the ONLY way to pass.  Here
    a clone that lacks the remote's commit is REFUSED and told to fetch, so
    being out of date can never buy a verdict.
    """
    if not args.push_context:
        print(f"SUBJECT: --integration-ref {args.integration_ref}")
        return resolve_commit(repo, args.integration_ref), args.integration_ref

    selected = pushed_remote_sha(args.push_integration_ref)
    if selected is None:
        print(
            f"SUBJECT: --integration-ref {args.integration_ref} "
            f"(no push in flight; {PUSH_REFS_ENV} unset)"
        )
        return resolve_commit(repo, args.integration_ref), args.integration_ref
    remote_sha, reason = selected
    if not remote_sha:
        print(f"SUBJECT: --integration-ref {args.integration_ref} ({reason})")
        return resolve_commit(repo, args.integration_ref), args.integration_ref

    probe = _git(
        repo,
        ["rev-parse", "--verify", "--quiet", "--end-of-options", f"{remote_sha}^{{commit}}"],
        False,
    )
    if probe.returncode != 0:
        raise GitFailure(
            f"the remote holds {args.push_integration_ref} at {remote_sha}, which this clone "
            "does not have. The ledger cannot be judged against an integration line you have "
            "not fetched -- and a behind clone must never get the greener verdict. Fetch and "
            "retry:\n"
            "  git fetch origin\n"
            "  git pull --rebase"
        )
    print(
        f"SUBJECT: push ({args.push_integration_ref} at remote {remote_sha[:12]})"
    )
    return remote_sha, None


def parse_now(value: Optional[str]) -> datetime:
    if value is None:
        return datetime.now(timezone.utc)
    return parse_timestamp(value, "--now")


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    source = parser.add_mutually_exclusive_group()
    source.add_argument(
        "--claims-dir",
        default=None,
        help="candidate worktree claim directory (default: coordination/claims)",
    )
    source.add_argument("--ledger-ref", help="commit/ref containing the authoritative ledger tree")
    parser.add_argument("--repo", default=str(Path(__file__).resolve().parents[1]))
    parser.add_argument("--integration-ref", default="HEAD")
    parser.add_argument("--now", help="RFC3339 clock override for deterministic tests")
    parser.add_argument(
        "--mirror-ref-prefix",
        default="refs/remotes/origin/claims",
        help="prefix before /TRUST-TWO-LANGUAGE-100/W... mirror refs",
    )
    parser.add_argument("--require-mirrors", action="store_true")
    parser.add_argument(
        "--push-context",
        action="store_true",
        help=(
            "take the integration head from the remote sha git reports for "
            f"--push-integration-ref in ${PUSH_REFS_ENV}, instead of this clone's "
            "cached --integration-ref"
        ),
    )
    parser.add_argument(
        "--push-integration-ref",
        default=DEFAULT_PUSH_INTEGRATION_REF,
        help="the remote-side ref whose push line carries the integration head",
    )
    parser.add_argument(
        "--lease-warn-hours",
        type=float,
        default=DEFAULT_LEASE_WARN_HOURS,
        help=(
            "warn (never fail) about every active lease lapsing within this many "
            "hours; 0 disables the approach entirely and restores the cliff"
        ),
    )
    parser.add_argument("--no-history", action="store_true")
    parser.add_argument("--expected-parent")
    parser.add_argument(
        "--bootstrap-commit",
        default=BOOTSTRAP_COMMIT,
        help="explicit first-parent boundary before which lifecycle history is grandfathered",
    )
    parser.add_argument("--json", action="store_true", dest="json_output")
    return parser


def main(argv: Optional[Sequence[str]] = None) -> int:
    args = build_parser().parse_args(argv)
    repo = Path(args.repo).resolve()
    try:
        integration_commit, integration_recheck_ref = select_integration_commit(repo, args)
        now = parse_now(args.now)
        if args.lease_warn_hours < 0:
            raise ValueError("--lease-warn-hours must not be negative")
        lease_warn = timedelta(hours=args.lease_warn_hours)
        if args.ledger_ref:
            ledger_commit = resolve_commit(repo, args.ledger_ref)
            documents = claim_documents_from_tree(repo, ledger_commit)
            report = validate(
                repo=repo,
                documents=documents,
                integration_commit=integration_commit,
                now=now,
                source=f"git:{args.ledger_ref}",
                ledger_commit=ledger_commit,
                check_history=not args.no_history,
                mirror_ref_prefix=args.mirror_ref_prefix if args.require_mirrors else None,
                expected_parent=args.expected_parent,
                bootstrap_commit=args.bootstrap_commit,
                lease_warn=lease_warn,
            )
            if resolve_commit(repo, args.ledger_ref) != ledger_commit:
                report.errors.append(f"ledger ref {args.ledger_ref!r} changed during validation")
        else:
            claims_dir = Path(args.claims_dir or CLAIM_TREE_DIR)
            documents = claim_documents_from_directory(repo, claims_dir)
            report = validate(
                repo=repo,
                documents=documents,
                integration_commit=integration_commit,
                now=now,
                source=f"worktree:{claims_dir}",
                expected_parent=args.expected_parent,
                lease_warn=lease_warn,
            )
        if (
            integration_recheck_ref
            and resolve_commit(repo, integration_recheck_ref) != integration_commit
        ):
            report.errors.append(
                f"integration ref {integration_recheck_ref!r} changed during validation"
            )
    except (GitFailure, OSError, ValueError) as exc:
        if args.json_output:
            print(
                json.dumps(
                    {
                        "schema": "trust.two-language.claim-ledger-check/v1",
                        "valid": False,
                        "environment_error": str(exc),
                    },
                    sort_keys=True,
                )
            )
        else:
            print(f"CLAIM LEDGER ERROR: {exc}", file=sys.stderr)
        return 2

    if args.json_output:
        print(json.dumps(report.as_dict(), indent=2, sort_keys=True))
    elif report.valid:
        expiring = (
            f", {len(report.warnings)} lease warning(s) within "
            f"{args.lease_warn_hours:g}h"
            if report.warnings
            else ""
        )
        print(
            f"CLAIM LEDGER OK: {report.claim_count} records, "
            f"{report.active_count} active{expiring}, "
            f"integration {report.integration_commit}"
        )
        # WARN: lines go to STDOUT on the valid path on purpose. The comprehensive
        # harness prints nothing at all from a lane that PASSES except the lines it
        # deliberately surfaces out of that lane's log, and it reads that log from
        # both streams. A notice that only a failing run shows is not a notice.
        for warning in report.warnings:
            print(f"WARN: {warning}")
        for note in report.notes:
            print(f"  note: {note}")
    else:
        print("CLAIM LEDGER FAIL", file=sys.stderr)
        for error in report.errors:
            print(f"  {error}", file=sys.stderr)
        for warning in report.warnings:
            print(f"WARN: {warning}", file=sys.stderr)
        for note in report.notes:
            print(f"  note: {note}", file=sys.stderr)
    return 0 if report.valid else 1


if __name__ == "__main__":
    sys.exit(main())
