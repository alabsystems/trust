#!/usr/bin/env python3
"""Check a direct compiler run's complete wire inventory without granting proof credit."""

from __future__ import annotations

import argparse
from collections import Counter
import json
from pathlib import Path
import sys


PREFIX = "TRUST_JSON:"
IDENTITIES = "trustc.coverage-function-identities.v1"
MEMORY = "trust-memory-summary/v1"
OUTCOMES = ("proved", "failed", "unknown", "timeout", "skipped", "runtime_checked",
            "unsupported", "canceled", "rejected")
UNKNOWN_OUTCOMES = ("unknown", "timeout", "skipped", "unsupported", "canceled", "rejected")


class WireError(ValueError):
    pass


def _object(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise WireError(f"duplicate JSON key: {key}")
        result[key] = value
    return result


def _constant(value):
    raise WireError(f"non-JSON number: {value}")


def _count(row, name):
    value = row.get(name)
    if type(value) is not int or value < 0:
        raise WireError(f"{name} must be a nonnegative integer")
    return value


def _names(value, name):
    if not isinstance(value, list) or not all(isinstance(x, str) and x for x in value):
        raise WireError(f"{name} must be a list of nonempty function identities")
    if value != sorted(set(value)):
        raise WireError(f"{name} must be sorted without duplicates")
    return value


def inspect_wire(stderr, stdout, *, crate_name, session, required_functions):
    """Reconcile every observed function; required bodies are a floor, never a filter.

    This validates accounting and reported outcomes, not proof artifacts or the
    independent Lean registry. An empty obligation list earns zero proved rows.
    """
    if not required_functions or not all(isinstance(x, str) and x for x in required_functions):
        raise WireError("at least one expected fixture function is required")
    if "TRUST_JSON" in stdout:
        raise WireError("verification transport appeared on stdout")
    messages = []
    phase = "functions"
    for number, line in enumerate(stderr.splitlines(), 1):
        if "TRUST_JSON" not in line:
            continue
        if not line.startswith(PREFIX):
            raise WireError(f"noncanonical transport at stderr line {number}")
        try:
            row = json.loads(line[len(PREFIX):], object_pairs_hook=_object, parse_constant=_constant)
        except (ValueError, TypeError) as error:
            raise WireError(f"invalid transport at stderr line {number}: {error}") from error
        if not isinstance(row, dict):
            raise WireError(f"transport at stderr line {number} is not an object")
        if row.get("type") not in ("function_result", "coverage_summary", "crate_summary"):
            raise WireError(f"unsupported transport type: {row.get('type')!r}")
        if row.get("crate_name") != crate_name or row.get("verification_session", "") != session:
            raise WireError("transport crate/session does not match this compiler invocation")
        # The coverage row closes the function inventory and the crate summary
        # closes transport. Matching final counts cannot repair reordered rows.
        if row["type"] == "function_result":
            if phase != "functions":
                raise WireError("function_result appeared after coverage or terminal summary")
        elif row["type"] == "coverage_summary":
            if phase != "functions":
                raise WireError("coverage_summary is duplicated or follows terminal summary")
            phase = "coverage"
        else:
            if phase != "coverage":
                raise WireError("crate_summary must follow coverage_summary exactly once")
            phase = "terminal"
        messages.append(row)

    coverage = [x for x in messages if x["type"] == "coverage_summary"]
    summaries = [x for x in messages if x["type"] == "crate_summary"]
    if len(coverage) != 1 or len(summaries) != 1:
        raise WireError("exactly one coverage_summary and crate_summary are required")
    coverage = coverage[0]
    identities = coverage.get("function_identities")
    if not isinstance(identities, dict) or identities.get("schema") != IDENTITIES:
        raise WireError("missing current function-identity inventory")
    eligible = _names(identities.get("eligible_functions"), "eligible_functions")
    processed = _names(identities.get("processed_functions"), "processed_functions")
    if not eligible or eligible != processed:
        raise WireError("function coverage is empty or incomplete")
    if _count(coverage, "eligible") != len(eligible) or _count(coverage, "processed") != len(processed):
        raise WireError("coverage counts disagree with their function inventories")
    if not set(required_functions) <= set(eligible):
        raise WireError("expected fixture function is missing from coverage")
    # T3 L4 C09w: the coverage row carries a required memory summary.
    memory = coverage.get("memory")
    if not isinstance(memory, dict) or memory.get("schema") != MEMORY \
            or not isinstance(memory.get("counters"), dict):
        raise WireError("missing current memory summary")

    functions = {}
    totals = Counter({outcome: 0 for outcome in OUTCOMES})
    nonclean = []
    verified = 0
    for row in messages:
        if row["type"] != "function_result":
            continue
        name = row.get("function")
        if not isinstance(name, str) or not name.startswith(crate_name + "::"):
            raise WireError("function_result lacks this crate's canonical function identity")
        if name in functions:
            raise WireError(f"duplicate function_result: {name}")
        results = row.get("results")
        if not isinstance(results, list):
            raise WireError(f"{name}: results must be a list")
        observed = Counter({outcome: 0 for outcome in OUTCOMES})
        for result in results:
            if not isinstance(result, dict) or result.get("outcome") not in OUTCOMES:
                raise WireError(f"{name}: malformed or unsupported obligation outcome")
            kind = result.get("kind")
            if not isinstance(kind, str) or not kind:
                raise WireError(f"{name}: obligation kind must be a nonempty string")
            outcome = result["outcome"]
            observed[outcome] += 1
            if outcome != "proved":
                nonclean.append({"function": name, "kind": kind, "outcome": outcome})
        counts = {
            "proved": observed["proved"], "failed": observed["failed"],
            "unknown": sum(observed[k] for k in UNKNOWN_OUTCOMES),
            "timed_out": observed["timeout"], "skipped": observed["skipped"],
            "runtime_checked": observed["runtime_checked"], "total": len(results),
        }
        if any(_count(row, key) != value for key, value in counts.items()):
            raise WireError(f"{name}: function counts disagree with obligation rows")
        totals.update(observed)
        verified += bool(results) and observed["proved"] == len(results)
        functions[name] = row
    if sorted(functions) != eligible:
        raise WireError("function_result population differs from complete coverage inventory")
    expected_summary = {
        "functions_analyzed": len(functions), "functions_verified": verified,
        "total_proved": totals["proved"], "total_failed": totals["failed"],
        "total_unknown": sum(totals[k] for k in UNKNOWN_OUTCOMES),
        "total_timed_out": totals["timeout"], "total_skipped": totals["skipped"],
        "total_runtime_checked": totals["runtime_checked"], "total_obligations": sum(totals.values()),
    }
    if any(_count(summaries[0], key) != value for key, value in expected_summary.items()):
        raise WireError("crate summary disagrees with complete function result population")
    return {"functions": sorted(functions), "counts": dict(totals), "nonclean": nonclean}


def acceptable(report, allowed_unknown_kind=None):
    return report["counts"]["proved"] > 0 and all(
        row["outcome"] == "unknown" and row["kind"] == allowed_unknown_kind
        for row in report["nonclean"])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--stderr", type=Path, required=True)
    parser.add_argument("--stdout", type=Path, required=True)
    parser.add_argument("--crate-name", required=True)
    parser.add_argument("--session", required=True)
    parser.add_argument("--require-function", action="append", required=True)
    parser.add_argument("--allow-unknown-kind", choices=["native-verification-gap"])
    parser.add_argument("--check-accounting-only", action="store_true",
                        help="Validate transport structure only; the caller must still grade outcomes")
    args = parser.parse_args()
    try:
        report = inspect_wire(args.stderr.read_text(), args.stdout.read_text(), crate_name=args.crate_name,
                              session=args.session, required_functions=args.require_function)
    except (OSError, UnicodeError, WireError) as error:
        print(f"invalid verification wire: {error}", file=sys.stderr)
        return 2
    counts = report["counts"]
    if args.check_accounting_only:
        print("transport accounting valid; outcomes not graded")
        return 0
    kinds = ",".join(sorted({x["kind"] for x in report["nonclean"]})) or "-"
    print(f"wire: {len(report['functions'])} fns, {counts['proved']} proved, "
          f"{counts['unknown']} unknown, {counts['failed']} failed, "
          f"{counts['timeout']} timed out, {counts['skipped']} skipped, "
          f"{counts['runtime_checked']} runtime-checked | nonclean={kinds}")
    return 0 if acceptable(report, args.allow_unknown_kind) else 1


if __name__ == "__main__":
    raise SystemExit(main())
