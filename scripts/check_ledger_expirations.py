#!/usr/bin/env python3
"""Fail-fast gate on stale Trust test-parity ledger entries.

Trust's upstream-Rust compatibility methodology (see CLAUDE.md →
"Upstream test parity") accepts test divergences only when justified by a
ledger entry. Every entry carries an `expires_on` date; once that date
passes, the entry must be re-reviewed and either renewed with a fresh
expiration or retired (because the underlying issue was fixed).

This script walks every known ledger file, parses each entry, returns
non-zero if any *active* entry's `expires_on` is in the past, and reports
near-expiration entries inside the warning window. It's the missing
automated gate that closes the loop on the methodology.

Usage:
    scripts/check_ledger_expirations.py
    scripts/check_ledger_expirations.py --warn-days 14    # also warn on
                                                          # entries lapsing
                                                          # within 14 days
    scripts/check_ledger_expirations.py --json            # machine output
    scripts/check_ledger_expirations.py --as-of YYYY-MM-DD  # test against
                                                            # a hypothetical
                                                            # release date

WHICH TREE IS JUDGED (2026-09-28). With TRUST_PUSHED_REFS unset or empty (no
push in flight) the ledgers on disk are read, as always. With it set (the
pre-push hook exports git's `<local_ref> <local_sha> <remote_ref> <remote_sha>`
lines) every distinct non-deletion pushed tree is judged from git objects on
its own, after a `SUBJECT:` line naming the refs; the working tree is never
read. There a walked ledger the pushed tree lacks is MISSING and fails, not an
empty ledger, and one that cannot be read fails naming it. A push of deletions
only prints `SKIPPED: ` and exits 0.

Exit codes:
    0   all active entries valid
    1   one or more entries expired (release gate fail); in a push, also a
        ledger the pushed tree lacks or that cannot be read from it
    2   warnings only (no entries expired, but some near expiration);
        only emitted with --strict-warn. Also: a malformed TRUST_PUSHED_REFS
        line, or push context in a directory git cannot read

Author: Andrew Yates | Copyright 2026 Andrew Yates | License: Apache-2.0
"""

from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import sys
from dataclasses import dataclass, field
from datetime import date, datetime, timezone
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[1]

# Each ledger file declares a top-level key whose value is a list of
# entries. The schema isn't uniform (some use `exceptions`, others use
# `divergences` or `items`), so we register each file with its key and
# the field name that scopes the entry id for diagnostics.
LEDGERS: tuple[tuple[Path, str, str], ...] = (
    (
        REPO_ROOT / "tests" / "upstream-rust" / "test-exceptions.toml",
        "exceptions",
        "id",
    ),
    (
        REPO_ROOT / "tests" / "upstream-rust" / "exceptions.toml",
        "exceptions",
        "id",
    ),
    (
        REPO_ROOT / "tests" / "upstream-rust" / "divergence-audit.toml",
        "items",
        "id",
    ),
    (
        REPO_ROOT / "tests" / "upstream-rust" / "patches.toml",
        "patches",
        "id",
    ),
    (
        REPO_ROOT / "tests" / "upstream-rust" / "upstream-fixes.toml",
        "fixes",
        "id",
    ),
    (
        REPO_ROOT / "tests" / "trust-comprehensive" / "divergences.toml",
        "divergences",
        "id",
    ),
    (
        REPO_ROOT / "tests" / "trust-added" / "compiletest-exceptions.toml",
        "exceptions",
        "path",
    ),
)

# Ledger-shaped files this gate deliberately does NOT walk, each with the
# reason. Silence is indistinguishable from coverage, so the exemption is
# stated here and then CHECKED: an exempt file that grows an `expires_on` has
# become an expiring ledger and the exemption is no longer true, which fails.
EXEMPT_LEDGERS: tuple[tuple[Path, str], ...] = (
    (
        REPO_ROOT / "tests" / "upstream-rust" / "baseline.toml",
        "the adopted-upstream alignment record, not an exception ledger: its "
        "`entries` carry a BaselineStatus (compatible/diverged/missing_*/unknown), "
        "which is a classification of a surface, not the active/retired lifecycle "
        "this gate reads, and no row has or should have an expiry. Its 13 seed "
        "`unknown` statuses are populated by a domination scorecard run, and "
        "scripts/tests/upstream_revision_consistency_test.py is what holds its "
        "revision honest",
    ),
)

def _reexec_under_a_toml_capable_python() -> None:
    """Re-exec under an interpreter that HAS a TOML parser, if this one lacks one.

    `tomllib` is stdlib only from 3.11. This gate is invoked as a bare `python3`
    from the comprehensive harness (`fast.ledger-expirations`), and on a macOS
    box `python3` is the 3.9 CommandLineTools build — so the lane hard-FAILED
    with "no TOML parser available" while a perfectly good 3.14 sat on the same
    PATH. A pre-push gate that refuses because of the interpreter that happened
    to invoke it reports nothing about the tree, and blocks every push on the
    machine until someone reads the message closely enough to notice it is not
    about the code.

    Re-exec is preferred over telling each caller which python to use: the
    callers disagree (`${PY}`, bare `python3`), and a fix in one leaves the
    others broken. A no-op when this interpreter already parses TOML, and it
    never recurses -- the child has a parser, or is the same interpreter and is
    left to raise the ordinary error.
    """
    import importlib.util
    import os
    import shutil
    import sys

    if importlib.util.find_spec("tomllib") or importlib.util.find_spec("tomli"):
        return
    if os.environ.get("TRUST_LEDGER_PY_REEXEC"):
        return
    for candidate in ("python3.14", "python3.13", "python3.12", "python3.11"):
        found = shutil.which(candidate)
        if not found:
            continue
        os.environ["TRUST_LEDGER_PY_REEXEC"] = "1"
        os.execv(found, [found, os.path.abspath(__file__), *sys.argv[1:]])
    # No better interpreter exists: fall through and raise TOML_PARSER_ERROR,
    # which names the real fix.


_reexec_under_a_toml_capable_python()

TOML_PARSER_ERROR = (
    "error: no TOML parser available for ledger checks; use Python 3.11+ "
    "for stdlib tomllib, or install tomli for this Python environment"
)


@dataclass
class EntryStatus:
    ledger: Path
    entry_id: str
    expires_on: date | None
    status: str  # "expired" | "expiring_soon" | "ok" | "no_expiry"
    days_remaining: int | None = None
    note: str = ""
    owner: str = ""
    issue: str = ""
    gate_id: str = ""
    reviewed_on: str = ""
    classification: str = ""
    compatibility_status: str = ""
    reason: str = ""
    required_action: str = ""


@dataclass
class Report:
    expired: list[EntryStatus] = field(default_factory=list)
    expiring_soon: list[EntryStatus] = field(default_factory=list)
    ok: list[EntryStatus] = field(default_factory=list)
    no_expiry: list[EntryStatus] = field(default_factory=list)

    def as_dict(self) -> dict[str, Any]:
        def serialize(es: EntryStatus) -> dict[str, Any]:
            return {
                "ledger": str(es.ledger.relative_to(REPO_ROOT)),
                "entry_id": es.entry_id,
                "expires_on": es.expires_on.isoformat() if es.expires_on else None,
                "status": es.status,
                "days_remaining": es.days_remaining,
                "note": es.note,
                "owner": es.owner,
                "issue": es.issue,
                "gate_id": es.gate_id,
                "reviewed_on": es.reviewed_on,
                "classification": es.classification,
                "compatibility_status": es.compatibility_status,
                "reason": es.reason,
                "required_action": es.required_action,
            }

        return {
            "summary": {
                "expired": len(self.expired),
                "expiring_soon": len(self.expiring_soon),
                "ok": len(self.ok),
                "no_expiry": len(self.no_expiry),
            },
            "expired": [serialize(e) for e in self.expired],
            "expiring_soon": [serialize(e) for e in self.expiring_soon],
            "no_expiry": [serialize(e) for e in self.no_expiry],
        }


JSON_ENTRY_KEYS = {
    "ledger",
    "entry_id",
    "expires_on",
    "status",
    "days_remaining",
    "note",
    "owner",
    "issue",
    "gate_id",
    "reviewed_on",
    "classification",
    "compatibility_status",
    "reason",
    "required_action",
}
JSON_TOP_LEVEL_KEYS = {"summary", "expired", "expiring_soon", "no_expiry"}


def self_check_json_contract() -> int:
    sample = EntryStatus(
        ledger=LEDGERS[0][0],
        entry_id="self-check.entry",
        expires_on=date(2026, 6, 7),
        status="expiring_soon",
        days_remaining=6,
        note="self-check note",
        owner="@trust-release",
        issue="local:self-check",
        gate_id="self-check-gate",
        reviewed_on="2026-06-01",
        classification="self_check",
        compatibility_status="blocker",
        reason="exercise JSON contract fields",
        required_action="keep JSON remediation fields stable",
    )
    payload = Report(expiring_soon=[sample]).as_dict()
    expected_summary = {
        "expired": 0,
        "expiring_soon": 1,
        "ok": 0,
        "no_expiry": 0,
    }
    errors: list[str] = []
    missing_top_level = sorted(JSON_TOP_LEVEL_KEYS - set(payload))
    extra_top_level = sorted(set(payload) - JSON_TOP_LEVEL_KEYS)
    if missing_top_level:
        errors.append(f"missing top-level keys: {', '.join(missing_top_level)}")
    if extra_top_level:
        errors.append(f"unexpected top-level keys: {', '.join(extra_top_level)}")
    if payload.get("summary") != expected_summary:
        errors.append(f"summary mismatch: {payload.get('summary')!r}")
    for bucket in ("expired", "expiring_soon", "no_expiry"):
        if bucket not in payload:
            errors.append(f"missing top-level bucket: {bucket}")
    entry = payload.get("expiring_soon", [{}])[0]
    missing = sorted(JSON_ENTRY_KEYS - set(entry))
    extra = sorted(set(entry) - JSON_ENTRY_KEYS)
    if missing:
        errors.append(f"missing entry keys: {', '.join(missing)}")
    if extra:
        errors.append(f"unexpected entry keys: {', '.join(extra)}")
    if entry.get("expires_on") != "2026-06-07":
        errors.append(f"expires_on was not ISO serialized: {entry.get('expires_on')!r}")
    if entry.get("owner") != "@trust-release":
        errors.append("owner field did not round-trip")
    if entry.get("required_action") != "keep JSON remediation fields stable":
        errors.append("required_action field did not round-trip")

    if errors:
        print("JSON contract self-check failed:", file=sys.stderr)
        for error in errors:
            print(f"  {error}", file=sys.stderr)
        return 1

    print("JSON contract self-check passed.")
    return 0


def parse_date(value: Any) -> date | None:
    if value is None:
        return None
    if isinstance(value, date):
        return value
    if isinstance(value, datetime):
        return value.date()
    if isinstance(value, str):
        try:
            return date.fromisoformat(value)
        except ValueError:
            return None
    return None


def entry_is_active(entry: dict[str, Any]) -> bool:
    """Only live, expiring entries count toward the gate.

    `status = "active"` is the live state in most ledgers; `status = "blocker"`
    is divergence-audit.toml's live expiring state (its category-blocker rows
    carry `expires_on` and must be renewed or resolved like any other live
    row). Retired/resolved/superseded/etc. entries are historical and
    shouldn't trigger expirations. If `status` is missing we assume active
    (conservative — better to surface a missing-field issue than silently
    skip).
    """
    status = entry.get("status")
    if status is None:
        return True
    return str(status).lower() in ("active", "blocker")


def render_value(value: Any) -> str:
    if isinstance(value, (date, datetime)):
        return value.isoformat()
    if value is None:
        return ""
    return str(value)


def load_toml(path: Path) -> dict[str, Any]:
    try:
        import tomllib
    except ModuleNotFoundError:
        try:
            import tomli as tomllib
        except ModuleNotFoundError as exc:
            raise RuntimeError(TOML_PARSER_ERROR) from exc

    return tomllib.loads(path.read_text(encoding="utf-8"))


def toml_loads(text: str) -> dict[str, Any]:
    try:
        import tomllib
    except ModuleNotFoundError:
        try:
            import tomli as tomllib
        except ModuleNotFoundError as exc:
            raise RuntimeError(TOML_PARSER_ERROR) from exc
    return tomllib.loads(text)


def classify(
    expires_on: date | None,
    as_of: date,
    warn_days: int,
) -> tuple[str, int | None]:
    if expires_on is None:
        return ("no_expiry", None)
    delta = (expires_on - as_of).days
    if delta < 0:
        return ("expired", delta)
    if delta <= warn_days:
        return ("expiring_soon", delta)
    return ("ok", delta)


def walk_ledger(
    path: Path, list_key: str, id_field: str, as_of: date, warn_days: int
) -> list[EntryStatus]:
    if not path.exists():
        return []
    data = load_toml(path)
    return walk_entries(path, data, list_key, id_field, as_of, warn_days)


def walk_entries(
    path: Path,
    data: dict[str, Any],
    list_key: str,
    id_field: str,
    as_of: date,
    warn_days: int,
) -> list[EntryStatus]:
    """The active entries of one parsed ledger, reported under `path`."""
    entries = data.get(list_key) or []
    out: list[EntryStatus] = []
    for raw in entries:
        if not isinstance(raw, dict):
            continue
        if not entry_is_active(raw):
            continue
        entry_id = str(raw.get(id_field, raw.get("id", raw.get("path", "<unknown>"))))
        expires_on = parse_date(raw.get("expires_on"))
        status, days = classify(expires_on, as_of, warn_days)
        note = ""
        if status == "no_expiry":
            note = f"active entry has no `expires_on` — every ledger entry must carry an expiration"
        out.append(
            EntryStatus(
                ledger=path,
                entry_id=entry_id,
                expires_on=expires_on,
                status=status,
                days_remaining=days,
                note=note,
                owner=render_value(raw.get("owner")),
                issue=render_value(raw.get("issue")),
                gate_id=render_value(raw.get("gate_id")),
                reviewed_on=render_value(raw.get("reviewed_on")),
                classification=render_value(raw.get("classification")),
                compatibility_status=render_value(raw.get("compatibility_status")),
                reason=render_value(raw.get("reason")),
                required_action=render_value(raw.get("required_action")),
            )
        )
    return out


def check_exemptions() -> list[str]:
    """An exempt ledger must still have no `expires_on` anywhere in it."""
    problems: list[str] = []
    for path, reason in EXEMPT_LEDGERS:
        if not path.exists():
            problems.append(f"{path.relative_to(REPO_ROOT)}: exempt file is missing")
            continue
        if "expires_on" in path.read_text(encoding="utf-8"):
            problems.append(exempt_with_expiry(path, reason))
    return problems


def exempt_with_expiry(path: Path, reason: str) -> str:
    return (
        f"{path.relative_to(REPO_ROOT)} carries `expires_on` but is exempt "
        f"from this gate ({reason}). Either drop the expiry or move the file "
        f"into LEDGERS; an expiring row nobody checks is worse than no row."
    )


def same_day_clusters(report: Report, limit: int) -> list[tuple[date, int]]:
    """Dates on which MORE THAN `limit` still-active entries expire together.

    Trust (2026-08-10): a cliff is a different failure from an expiry. One expired
    row blocks pushes until one row is reviewed; seventy-three expiring on one date
    blocks every push until seventy-three are reviewed, and a reviewer facing that
    on a deadline renews the batch. That is exactly how the 71 `sysroot-skew` rows
    came to waive a defect that had already been fixed — one label, one copy-pasted
    reason, one date, no re-measurement.

    Counts only entries that still lie ahead (`ok` + `expiring_soon`). Already-expired
    rows are the other check's business and would double-report here.
    """
    if limit <= 0:
        return []
    counts: dict[date, int] = {}
    for es in [*report.ok, *report.expiring_soon]:
        if es.expires_on is None:
            continue
        counts[es.expires_on] = counts.get(es.expires_on, 0) + 1
    return sorted(((d, n) for d, n in counts.items() if n > limit), key=lambda t: t[0])


def file_report(report: Report, statuses: list[EntryStatus]) -> None:
    for es in statuses:
        bucket = {
            "expired": report.expired,
            "expiring_soon": report.expiring_soon,
            "ok": report.ok,
            "no_expiry": report.no_expiry,
        }[es.status]
        bucket.append(es)


def build_report(as_of: date, warn_days: int) -> Report:
    report = Report()
    for path, list_key, id_field in LEDGERS:
        for es in walk_ledger(path, list_key, id_field, as_of, warn_days):
            bucket = {
                "expired": report.expired,
                "expiring_soon": report.expiring_soon,
                "ok": report.ok,
                "no_expiry": report.no_expiry,
            }[es.status]
            bucket.append(es)
    return report


def render_text(report: Report, as_of: date, warn_days: int) -> str:
    lines = [
        f"Ledger expiration check  as_of={as_of.isoformat()}  warn_days={warn_days}",
        "",
        f"  active entries reviewed: {len(report.expired) + len(report.expiring_soon) + len(report.ok) + len(report.no_expiry)}",
        f"  expired:        {len(report.expired)}",
        f"  expiring soon:  {len(report.expiring_soon)}",
        f"  no expiry set:  {len(report.no_expiry)}",
        f"  ok:             {len(report.ok)}",
        "",
        f"  ledgers walked: {len(LEDGERS)}",
        f"  exempt:         {len(EXEMPT_LEDGERS)} "
        f"({', '.join(str(p.relative_to(REPO_ROOT)) for p, _ in EXEMPT_LEDGERS)})",
    ]

    def add_entry_context(es: EntryStatus) -> None:
        owner = es.owner or "<missing>"
        issue = es.issue or "<missing>"
        reviewed_on = es.reviewed_on or "<missing>"
        lines.append(f"    owner={owner}  issue={issue}  reviewed_on={reviewed_on}")
        context_parts = [
            part
            for part in (es.gate_id, es.classification, es.compatibility_status)
            if part
        ]
        if context_parts or es.reason:
            context = " / ".join(context_parts) if context_parts else "context"
            if es.reason:
                lines.append(f"    context={context}: {es.reason}")
            else:
                lines.append(f"    context={context}")
        if es.required_action:
            lines.append(f"    required_action={es.required_action}")

    if report.expired:
        lines.append("")
        lines.append("EXPIRED — release gate FAIL:")
        for es in report.expired:
            rel = es.ledger.relative_to(REPO_ROOT)
            lines.append(
                f"  • {rel}  {es.entry_id}  "
                f"expired={es.expires_on}  ({-es.days_remaining} days ago)"
            )
            add_entry_context(es)
        lines.append(
            "Remediation: re-review each expired entry, then either retire it "
            "if the divergence is fixed or renew `expires_on` with current owner/issue context."
        )
    if report.expiring_soon:
        lines.append("")
        lines.append(f"EXPIRING within {warn_days} days — warning, review required:")
        for es in report.expiring_soon:
            rel = es.ledger.relative_to(REPO_ROOT)
            lines.append(
                f"  • {rel}  {es.entry_id}  "
                f"expires={es.expires_on}  ({es.days_remaining} days remaining)"
            )
            add_entry_context(es)
        lines.append(
            "Remediation: review before `expires_on`; renew active exceptions "
            "with updated justification or retire entries whose divergence is fixed."
        )
        lines.append(
            "Default check_all/CI treats these as warnings. They become failures "
            "after expiration, or immediately when this script runs with --strict-warn."
        )
    if report.no_expiry:
        lines.append("")
        lines.append("NO EXPIRY SET — schema violation (active entries must expire):")
        for es in report.no_expiry:
            rel = es.ledger.relative_to(REPO_ROOT)
            lines.append(f"  • {rel}  {es.entry_id}")
            add_entry_context(es)
        lines.append("Remediation: add `expires_on` to active entries or retire them.")
    return "\n".join(lines) + "\n"


# ---------------------------------------------------------------------------
# The push reading (TRUST_PUSHED_REFS set and non-empty).
#
# Everything above reads the ledgers on DISK, which judges the checkout, not the
# push (docs/issues/2026-09-28-push-lanes-judge-the-checkout-not-the-push.md,
# case L): a non-HEAD ref carrying an expired exception passed (`expired: 0`),
# as did HEAD with the renewal uncommitted or the ledger deleted locally, and an
# uncommitted expiry edit refused a clean push. In a push each distinct pushed
# tree is judged from git objects on its own, with the same buckets, the same
# text and the same exit rule. Two things are stricter than the disk reading,
# on purpose: a walked ledger (or the exempt file) the pushed tree LACKS is
# named MISSING and fails, where `walk_ledger` reads a missing path as an empty
# ledger; and a ledger that cannot be read (not a regular file, not UTF-8, not
# TOML) fails naming the path, where the disk reading dies in a traceback.
# Deletions have no tree and are not judged; a push of deletions only prints
# `SKIPPED: `. A malformed TRUST_PUSHED_REFS line is exit 2.
# ---------------------------------------------------------------------------

ZERO_SHA = re.compile(r"^0+$")
HEX_SHA = re.compile(r"^(?:[0-9a-f]{40}|[0-9a-f]{64})$")
REGULAR_FILE_MODES = ("100644", "100755")


class PushContextError(Exception):
    """The push context itself cannot be used (exit 2)."""


class TreeReadError(Exception):
    """One file of one pushed tree could not be read. Never a pass."""


_GIT_ENV: dict[str, str] | None = None


def git_env() -> dict[str, str]:
    """The environment minus git's repository-local variables (GIT_DIR, ...).

    A caller's stray GIT_DIR would point every read below at another object
    store; git names its own list, so none is hard-coded here.
    """
    global _GIT_ENV
    if _GIT_ENV is None:
        proc = subprocess.run(
            ["git", "rev-parse", "--local-env-vars"], capture_output=True, text=True
        )
        if proc.returncode != 0:
            raise PushContextError(
                f"`git rev-parse --local-env-vars` failed: {proc.stderr.strip()}"
            )
        local = set(proc.stdout.split())
        _GIT_ENV = {k: v for k, v in os.environ.items() if k not in local}
    return _GIT_ENV


def run_git(args: list[str]) -> bytes:
    proc = subprocess.run(
        ["git", "-C", str(REPO_ROOT), *args], capture_output=True, env=git_env()
    )
    if proc.returncode != 0:
        err = proc.stderr.decode("utf-8", "replace").strip()
        raise TreeReadError(f"`git {' '.join(args)}` failed (exit {proc.returncode}): {err}")
    return proc.stdout


def parse_pushed_refs(raw: str) -> list[tuple[str, str]]:
    """(local_ref, local_sha) per `<local_ref> <local_sha> <remote_ref> <remote_sha>` line."""
    pushed: list[tuple[str, str]] = []
    for line in raw.splitlines():
        if not line.strip():
            continue
        fields = line.split()
        if len(fields) != 4 or not HEX_SHA.match(fields[1]) or not HEX_SHA.match(fields[3]):
            raise PushContextError(
                f"malformed TRUST_PUSHED_REFS line {line!r}; expected "
                "`<local_ref> <local_sha> <remote_ref> <remote_sha>`"
            )
        pushed.append((fields[0], fields[1]))
    return pushed


def read_tree_file(tree: str, rel: str) -> str | None:
    """`rel` in `tree` as text; None when the tree has no such path."""
    listing = run_git(["ls-tree", "-z", tree, "--", rel])
    if not listing:
        return None
    meta, _, _name = listing.rstrip(b"\0").partition(b"\t")
    mode, kind, sha = meta.decode("ascii", "replace").split()
    if kind != "blob" or mode not in REGULAR_FILE_MODES:
        raise TreeReadError(f"not a regular file in the pushed tree ({mode} {kind})")
    try:
        return run_git(["cat-file", "blob", sha]).decode("utf-8")
    except UnicodeDecodeError as exc:
        raise TreeReadError(f"not UTF-8: {exc}") from exc


@dataclass
class TreeVerdict:
    label: str
    tree: str | None
    report: Report = field(default_factory=Report)
    missing: list[str] = field(default_factory=list)
    unreadable: list[str] = field(default_factory=list)
    exemption_problems: list[str] = field(default_factory=list)


def judge_tree(label: str, tree: str, as_of: date, warn_days: int) -> TreeVerdict:
    verdict = TreeVerdict(label=label, tree=tree)
    for path, list_key, id_field in LEDGERS:
        rel = path.relative_to(REPO_ROOT).as_posix()
        try:
            text = read_tree_file(tree, rel)
        except TreeReadError as exc:
            verdict.unreadable.append(f"{rel}: {exc}")
            continue
        if text is None:
            verdict.missing.append(rel)
            continue
        try:
            data = toml_loads(text)
        except RuntimeError:
            raise
        except Exception as exc:  # the parser's own decode error, whichever parser
            verdict.unreadable.append(f"{rel}: not TOML: {exc}")
            continue
        file_report(verdict.report, walk_entries(path, data, list_key, id_field, as_of, warn_days))
    for path, reason in EXEMPT_LEDGERS:
        rel = path.relative_to(REPO_ROOT).as_posix()
        try:
            text = read_tree_file(tree, rel)
        except TreeReadError as exc:
            verdict.unreadable.append(f"{rel}: {exc}")
            continue
        if text is None:
            verdict.exemption_problems.append(f"{rel}: exempt file is missing")
        elif "expires_on" in text:
            verdict.exemption_problems.append(exempt_with_expiry(path, reason))
    return verdict


def judge_pushed(args: argparse.Namespace, as_of: date, raw: str) -> int:
    pushed = parse_pushed_refs(raw)
    live = [(ref, sha) for ref, sha in pushed if not ZERO_SHA.match(sha)]
    deletions = len(pushed) - len(live)
    if not live:
        subject = f"the pushed trees (TRUST_PUSHED_REFS: {deletions} deletion(s), nothing else)"
        if args.json:
            json.dump({"subject": subject, "skipped": True, "trees": []}, sys.stdout, indent=2)
            sys.stdout.write("\n")
        else:
            print(f"SUBJECT: {subject}")
            print("SKIPPED: deletion(s) only, no tree pushed — nothing to judge")
        return 0
    try:
        run_git(["rev-parse", "--git-dir"])
    except TreeReadError as exc:
        raise PushContextError(f"TRUST_PUSHED_REFS is set but {REPO_ROOT} is not a git repository: {exc}")

    # One verdict per distinct tree; refs sharing a tree share its label.
    groups: dict[str, list[str]] = {}
    verdicts: list[TreeVerdict] = []
    for ref, sha in live:
        try:
            tree = run_git(["rev-parse", "--verify", "--quiet", f"{sha}^{{tree}}"]).decode().strip()
        except TreeReadError:
            verdicts.append(TreeVerdict(label=f"{ref} {sha[:12]}", tree=None, unreadable=[
                f"pushed object {sha} does not name a tree here; a push this gate "
                "cannot read is not a pass"
            ]))
            continue
        groups.setdefault(tree, []).append(f"{ref} {sha[:12]}")
    for tree, refs in groups.items():
        verdicts.append(judge_tree(", ".join(refs), tree, as_of, args.warn_days))

    names = ", ".join(v.label for v in verdicts)
    extra = f"; {deletions} deletion(s) not judged" if deletions else ""
    subject = f"the pushed trees (TRUST_PUSHED_REFS: {names}{extra}), not the working tree"

    worst = 0
    # FINDING KEYS (2026-10-24, docs/DECISION_QUEUE.md INHERITED-RED): each red
    # cause that is a fact of the pushed tree and the date (an expired row, a
    # row with no expiry, a ledger the tree lacks) prints `FINDING: <key>`;
    # the others (an unreadable ledger, an exemption problem, an expiry cliff)
    # are unkeyed, and `FINDINGS: complete` is printed only when there is none,
    # so the pre-push hook never grades an unkeyed red as one main already has.
    finding_keys: set[str] = set()
    unkeyed = False
    if args.json:
        payload = {"subject": subject, "skipped": False, "trees": []}
    else:
        print(f"SUBJECT: {subject}")
    for verdict in verdicts:
        report = verdict.report
        clusters = same_day_clusters(report, args.max_same_day)
        failed = bool(
            report.expired or report.no_expiry or clusters or verdict.missing
            or verdict.unreadable or verdict.exemption_problems
        )
        if failed:
            worst = 1
            for es in report.expired:
                finding_keys.add(
                    f"EXPIRED {es.ledger.relative_to(REPO_ROOT)} {es.entry_id} {es.expires_on}"
                )
            for es in report.no_expiry:
                finding_keys.add(f"NO-EXPIRY {es.ledger.relative_to(REPO_ROOT)} {es.entry_id}")
            for rel in verdict.missing:
                finding_keys.add(f"MISSING {rel}")
            if clusters or verdict.unreadable or verdict.exemption_problems:
                unkeyed = True
        elif args.strict_warn and report.expiring_soon and worst == 0:
            worst = 2
        tree12 = verdict.tree[:12] if verdict.tree else "unresolved"
        if args.json:
            payload["trees"].append({
                "refs": verdict.label,
                "tree": verdict.tree,
                "missing_ledgers": verdict.missing,
                "unreadable_ledgers": verdict.unreadable,
                "exemption_problems": verdict.exemption_problems,
                "report": report.as_dict(),
            })
        else:
            print()
            print(f"=== {verdict.label} (tree {tree12}) ===")
            if verdict.tree is not None:
                sys.stdout.write(render_text(report, as_of, args.warn_days))
            if verdict.missing:
                print("")
                print("MISSING — ledgers this gate walks that the pushed tree lacks "
                      "(an absent ledger is not an empty one):")
                for rel in verdict.missing:
                    print(f"  • {rel}")
                print("Remediation: restore the ledger, or retire it from LEDGERS in "
                      "scripts/check_ledger_expirations.py in the same commit.")
            if verdict.unreadable:
                print("")
                print("UNREADABLE — a ledger this gate cannot read is not a pass:")
                for problem in verdict.unreadable:
                    print(f"  • {problem}")
        sys.stdout.flush()
        if verdict.exemption_problems:
            print(f"EXEMPT LEDGER NO LONGER EXEMPT ({verdict.label}):", file=sys.stderr)
            for problem in verdict.exemption_problems:
                print(f"  {problem}", file=sys.stderr)
        if clusters:
            print(f"EXPIRY CLIFF ({verdict.label}) — too many active rows share one date:",
                  file=sys.stderr)
            for when, count in clusters:
                print(
                    f"  {when.isoformat()}: {count} entries (limit {args.max_same_day}). "
                    f"On that date every push blocks until all {count} are reviewed, which "
                    f"is how a batch gets renewed unexamined. Stagger them by cluster, each "
                    f"with its own review question.",
                    file=sys.stderr,
                )
    if args.json:
        json.dump(payload, sys.stdout, indent=2, default=str)
        sys.stdout.write("\n")
    elif worst == 1:
        print()
        for key in sorted(finding_keys):
            print(f"FINDING: {key}")
        if finding_keys and not unkeyed:
            print("FINDINGS: complete")
    return worst


def parse_args() -> argparse.Namespace:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument(
        "--warn-days",
        type=int,
        default=14,
        help="Warning window for entries close to expiration (default: 14).",
    )
    p.add_argument(
        "--as-of",
        default=None,
        help="Override today's date (ISO YYYY-MM-DD). Useful for testing the gate "
        "against a future release date.",
    )
    p.add_argument(
        "--json",
        action="store_true",
        help="Machine-readable JSON output.",
    )
    p.add_argument(
        "--strict-warn",
        action="store_true",
        help="Return exit code 2 when entries are expiring soon (default: don't fail).",
    )
    p.add_argument(
        "--max-same-day",
        type=int,
        default=0,
        help="Fail when more than N ACTIVE entries share one `expires_on` (0 = off). "
        "A cluster all expiring on one date blocks every push at once and so forces "
        "the mass rubber-stamp renewal this gate exists to prevent.",
    )
    p.add_argument(
        "--self-check-json-contract",
        action="store_true",
        help="Validate the machine-readable JSON shape without reading ledger files.",
    )
    return p.parse_args()


def main() -> int:
    args = parse_args()
    if args.self_check_json_contract:
        return self_check_json_contract()
    today = datetime.now(timezone.utc).date()
    as_of = parse_date(args.as_of) if args.as_of else today
    if as_of is None:
        print(f"error: invalid --as-of value: {args.as_of!r}", file=sys.stderr)
        return 1
    raw = os.environ.get("TRUST_PUSHED_REFS", "")
    if raw.strip():
        try:
            return judge_pushed(args, as_of, raw)
        except PushContextError as exc:
            print(f"error: {exc}", file=sys.stderr)
            return 2
        except RuntimeError as exc:
            print(exc, file=sys.stderr)
            return 1
    try:
        report = build_report(as_of, args.warn_days)
    except RuntimeError as exc:
        print(exc, file=sys.stderr)
        return 1
    exemption_problems = check_exemptions()
    if args.json:
        json.dump(report.as_dict(), sys.stdout, indent=2, default=str)
        sys.stdout.write("\n")
    else:
        sys.stdout.write(render_text(report, as_of, args.warn_days))
    if exemption_problems:
        print("EXEMPT LEDGER NO LONGER EXEMPT:", file=sys.stderr)
        for problem in exemption_problems:
            print(f"  {problem}", file=sys.stderr)
        return 1
    clusters = same_day_clusters(report, args.max_same_day)
    if clusters:
        print("EXPIRY CLIFF — too many active rows share one date:", file=sys.stderr)
        for when, count in clusters:
            print(
                f"  {when.isoformat()}: {count} entries (limit {args.max_same_day}). "
                f"On that date every push blocks until all {count} are reviewed, which "
                f"is how a batch gets renewed unexamined. Stagger them by cluster, each "
                f"with its own review question.",
                file=sys.stderr,
            )
    if report.expired or report.no_expiry:
        return 1
    if clusters:
        return 1
    if args.strict_warn and report.expiring_soon:
        return 2
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
