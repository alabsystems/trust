#!/usr/bin/env python3
"""Ratchet compiler-reported Clean certification for the aterm leaf crates.

Each count comes from a completed compiler invocation with reconciled wire
summaries and stable local obligation IDs. The scoreboard compares those
reports. Independent kernel replay and release proof authority remain separate.
"""

import argparse
from collections import Counter
import json
import os
from pathlib import Path
import re
import secrets
import subprocess
import sys
import tempfile

sys.path.insert(0, str(Path(__file__).resolve().parent / "lib"))
from trust_program_wire import OUTCOMES, UNKNOWN_OUTCOMES, WireError, inspect_wire


REPO_ROOT = Path(__file__).resolve().parent.parent
SCHEMA = "trust.certified-scoreboard.compiler-report/v1"
EVIDENCE_SCOPE = "compiler-report-only"
LOCAL_ID = re.compile(r"[0-9a-f]{16}")
DEFAULT_CRATES = (
    "aterm-bidi", "aterm-bits", "aterm-codec", "aterm-cap",
    "aterm-rle", "aterm-log", "aterm-buffer", "aterm-hash", "aterm-sixel",
)


class ScoreboardError(ValueError):
    pass


def tally(rows):
    outcomes = Counter(row["outcome"] for row in rows)
    assurances = Counter(row["reported_assurance"] for row in rows)
    return {
        "obligations": len(rows),
        "proved": outcomes["proved"],
        "failed": outcomes["failed"],
        "unknown": sum(outcomes[kind] for kind in UNKNOWN_OUTCOMES),
        "timed_out": outcomes["timeout"],
        "runtime_checked": outcomes["runtime_checked"],
        "kernel_certified": assurances["CleanCertified"],
        "smt_backed": assurances["SmtBacked"],
    }


def reported_assurance(function, row):
    proof = row.get("proof_evidence")
    if proof is None:
        return None
    if not isinstance(proof, dict):
        raise ScoreboardError("malformed obligation proof_evidence")
    strength = proof.get("strength")
    if strength is None:
        return None
    if not isinstance(strength, dict):
        raise ScoreboardError("malformed obligation proof strength")
    assurance = strength.get("assurance")
    if isinstance(assurance, dict) and set(assurance) == {"BoundedSound"}:
        bound = assurance["BoundedSound"]
        if (isinstance(bound, dict) and set(bound) == {"depth"}
                and type(bound["depth"]) is int and 0 <= bound["depth"] < 2**64):
            return None
    if not isinstance(assurance, str):
        raise ScoreboardError("malformed obligation proof assurance")
    if assurance not in ("Certified", "SmtBacked"):
        return None
    if row["outcome"] != "proved" or proof.get("status") != "proved":
        raise ScoreboardError(f"{assurance} assurance without matching proved outcomes")
    if assurance != "Certified":
        return "SmtBacked"
    if (proof.get("suite"), proof.get("backend")) != ("trust-certify", "clean-kernel"):
        return None
    grade = row.get("grade")
    if grade is not None and (not isinstance(grade, dict) or "premises" not in grade):
        raise ScoreboardError("malformed grade on Certified row")
    for premises in (function.get("modeled_facts", []), row.get("assumes", []),
                     grade["premises"] if grade is not None else []):
        if not isinstance(premises, list) or any(not isinstance(item, str) for item in premises):
            raise ScoreboardError("malformed premise disclosure on Certified row")
        if premises:
            return None
    return "CleanCertified"


def measure_report(process, crate_name, session):
    if process.returncode != 0:
        raise ScoreboardError(f"compiler exited {process.returncode}")
    try:
        report = inspect_wire(process.stderr, process.stdout, crate_name=crate_name,
                              session=session, required_functions=None)
    except (WireError, RecursionError) as error:
        raise ScoreboardError(f"invalid verification wire: {error}") from error
    obligations = []
    for name in report["functions"]:
        function = report["function_results"][name]
        if function.get("transport_budget") is not None:
            raise ScoreboardError(f"{name}: transport withheld part of the report")
        results = function["results"]
        ids = function.get("stable_ids", [])
        if (not isinstance(ids, list) or len(ids) != len(results)
                or any(not isinstance(value, str) or not LOCAL_ID.fullmatch(value) for value in ids)
                or len(set(ids)) != len(ids)):
            raise ScoreboardError(f"{name}: missing, malformed or duplicate stable obligation IDs")
        for stable_id, row in zip(ids, results):
            obligations.append({
                "function": name, "stable_id": stable_id,
                "kind": row["kind"], "outcome": row["outcome"],
                "reported_assurance": reported_assurance(function, row),
            })
    return {"functions": report["functions"], "rows": obligations, "counts": tally(obligations)}


def run_crate(trustc, source, crate_name, output):
    session = secrets.token_hex(16)
    env = dict(os.environ, RUST_LOG="off")
    try:
        process = subprocess.run(
            [str(trustc), "--crate-type=lib", "--edition=2021", "--crate-name", crate_name,
             "-Ztrust-verify=on", "-Ztrust-verify-output=json", f"-Ztrust-verify-session={session}",
             "-Ztrust-verify-function-budget-ms=600000", "-Ztrust-verify-worker-threads=1",
             "-A", "warnings", str(source), "-o", str(output)],
            env=env, capture_output=True, encoding="utf-8", timeout=1800,
        )
        return measure_report(process, crate_name, session)
    except subprocess.TimeoutExpired as error:
        raise ScoreboardError(f"{crate_name}: compiler timed out") from error
    except (OSError, UnicodeError, ScoreboardError) as error:
        raise ScoreboardError(f"{crate_name}: {error}") from error


def make_board(crates):
    totals = Counter()
    for report in crates.values():
        totals.update(report["counts"])
    return {"schema": SCHEMA, "evidence_scope": EVIDENCE_SCOPE,
            "totals": dict(totals), "per_crate": crates}


def unique_fields(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise ScoreboardError(f"duplicate baseline field {key}")
        result[key] = value
    return result


def require_counts(actual, expected, where):
    if (not isinstance(actual, dict) or actual != expected
            or any(type(value) is not int for value in actual.values())):
        raise ScoreboardError(f"{where} counts do not match the obligation rows")


def load_floor(path):
    try:
        value = json.loads(path.read_text(encoding="utf-8"), object_pairs_hook=unique_fields)
    except (OSError, UnicodeError, ValueError, RecursionError) as error:
        raise ScoreboardError(f"invalid baseline {path}: {error}") from error
    if (not isinstance(value, dict) or set(value) != {"schema", "evidence_scope", "totals", "per_crate"}
            or value["schema"] != SCHEMA or value["evidence_scope"] != EVIDENCE_SCOPE):
        raise ScoreboardError(f"baseline {path} requires {SCHEMA} with complete compiler-report data")
    crates = value.get("per_crate")
    if not isinstance(crates, dict) or set(crates) != set(DEFAULT_CRATES):
        raise ScoreboardError("baseline crate roster differs from the fixed aterm leaves")
    for name, report in crates.items():
        if not isinstance(report, dict) or set(report) != {"functions", "rows", "counts"}:
            raise ScoreboardError(f"baseline {name}: missing function/obligation inventory")
        functions, rows = report["functions"], report["rows"]
        crate_prefix = name.replace("-", "_") + "::"
        if (not isinstance(functions, list) or not functions
                or any(not isinstance(fn, str) or not fn.startswith(crate_prefix) for fn in functions)
                or functions != sorted(set(functions)) or not isinstance(rows, list)):
            raise ScoreboardError(f"baseline {name}: invalid function/obligation inventory")
        owners, seen = set(functions), set()
        for row in rows:
            if (not isinstance(row, dict) or set(row) != {
                    "function", "stable_id", "kind", "outcome", "reported_assurance"}
                    or not isinstance(row["function"], str) or row["function"] not in owners
                    or not isinstance(row["stable_id"], str) or not LOCAL_ID.fullmatch(row["stable_id"])
                    or not isinstance(row["kind"], str) or not row["kind"]
                    or row["outcome"] not in OUTCOMES
                    or row["reported_assurance"] not in (None, "CleanCertified", "SmtBacked")
                    or (row["reported_assurance"] is not None and row["outcome"] != "proved")):
                raise ScoreboardError(f"baseline {name}: invalid obligation row")
            key = (row["function"], row["stable_id"])
            if key in seen:
                raise ScoreboardError(f"baseline {name}: duplicate obligation identity {key}")
            seen.add(key)
        require_counts(report["counts"], tally(rows), f"baseline {name}")
    expected = make_board(crates)["totals"]
    require_counts(value.get("totals"), expected, "baseline")
    if expected["kernel_certified"] == 0:
        raise ScoreboardError("baseline has no compiler-reported Clean-certified rows")
    return expected["kernel_certified"]


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--trustc", type=Path, default=REPO_ROOT / "build/host/stage2/bin/trustc")
    parser.add_argument("--aterm", type=Path, default=REPO_ROOT.parent / "aterm")
    parser.add_argument("--baseline", type=Path)
    parser.add_argument("--out", type=Path)
    args = parser.parse_args(argv)

    try:
        floor = None if args.baseline is None else load_floor(args.baseline)
        if args.baseline is not None and args.out is not None:
            if (args.baseline.resolve() == args.out.resolve()
                    or (args.out.exists() and args.baseline.samefile(args.out))):
                raise ScoreboardError("--out must differ from --baseline")
        sources = {name: args.aterm / "crates" / name / "src/lib.rs" for name in DEFAULT_CRATES}
        missing = [str(source) for source in sources.values() if not source.is_file()]
        if missing:
            raise ScoreboardError(f"missing aterm leaf sources: {', '.join(missing)}")
        with tempfile.TemporaryDirectory(prefix="trust-certified-scoreboard-") as directory:
            crates = {
                name: run_crate(args.trustc, source, name.replace("-", "_"),
                                Path(directory) / f"{name}.rlib")
                for name, source in sources.items()
            }
        report = make_board(crates)
        observed = report["totals"]["kernel_certified"]
        data = json.dumps(report, indent=2) + "\n"
        if args.out is not None:
            args.out.write_text(data, encoding="utf-8")
    except (OSError, UnicodeError, ScoreboardError) as error:
        print(f"REFUSED: {error}", file=sys.stderr)
        return 2
    print(data, end="")
    print(f"Compiler-reported Clean-certified obligations: {observed}", file=sys.stderr)
    if floor is not None and observed < floor:
        print(f"REGRESSION: reported count {observed} < baseline {floor}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
