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

Exit codes:
    0   all active entries valid
    1   one or more entries expired (release gate fail)
    2   warnings only (no entries expired, but some near expiration);
        only emitted with --strict-warn

Author: Andrew Yates | Copyright 2026 Andrew Yates | License: Apache-2.0
"""

from __future__ import annotations

import argparse
import json
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
    """Only `status = "active"` entries count toward the gate.

    Retired/superseded/etc. entries are historical and shouldn't trigger
    expirations. If `status` is missing we assume active (conservative
    — better to surface a missing-field issue than silently skip).
    """
    status = entry.get("status")
    if status is None:
        return True
    return str(status).lower() == "active"


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
            problems.append(
                f"{path.relative_to(REPO_ROOT)} carries `expires_on` but is exempt "
                f"from this gate ({reason}). Either drop the expiry or move the file "
                f"into LEDGERS; an expiring row nobody checks is worse than no row."
            )
    return problems


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
    if report.expired or report.no_expiry:
        return 1
    if args.strict_warn and report.expiring_soon:
        return 2
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
