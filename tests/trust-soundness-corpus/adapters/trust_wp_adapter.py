#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Licensed under the Apache License, Version 2.0
"""trust-soundness-corpus adapter for trust-wp: run case files through trust-wp's
own adversarial harness (its scaffolding, its driver build, its output parsers)
and report, per case, which functions and proof_asserts trust-wp CREDITED.

It reads verdicts only with trust-wp's parsers (`verified_functions`,
`standing_assertion_credits`, `unproved_assertion_functions`), so a credit means
here exactly what it means to trust-wp's own gate. Needs python >= 3.11 (the
harness imports tomllib).

    trust_wp_adapter.py --trust-wp <checkout> --cases <dir> --json <out>
"""

from __future__ import annotations

import argparse
import json
import os
import shutil
import sys
import tempfile
from pathlib import Path


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--trust-wp", required=True)
    ap.add_argument("--cases", required=True)
    ap.add_argument("--json", required=True)
    ap.add_argument("--timeout", type=int, default=int(os.environ.get("TRUST_WP_CASE_TIMEOUT", "300")))
    ap.add_argument("--jobs", type=int, default=int(os.environ.get("TRUST_WP_JOBS", "4")))
    args = ap.parse_args()

    adv = Path(args.trust_wp).resolve() / "tests" / "adversarial"
    sys.path.insert(0, str(adv))
    import run_adversarial as ra  # noqa: E402  (trust-wp's runner; sets up its harness path)

    workspace = ra.harness.find_workspace_root()
    if Path(workspace).resolve() != Path(args.trust_wp).resolve():
        print(f"workspace root {workspace} is not {args.trust_wp}", file=sys.stderr)
        return 2
    cases = ra.load_cases(Path(args.cases).resolve(), None)
    ra.harness.ensure_harness_binaries(workspace, False)
    env_target = os.environ.get("TRUST_WP_HARNESS_TARGET_DIR")
    shared = Path(env_target) if env_target else Path(tempfile.mkdtemp(prefix="sbc_wp_target_"))
    shared.mkdir(parents=True, exist_ok=True)
    try:
        ra.harness_runner._warmup_shared_target(
            ra.harness._current_facade(), workspace, [c.path for c in cases], shared, False
        )
        try:
            cargo_trust_wp = ra.harness_runner.resolve_harness_binary(workspace, "cargo-trust-wp")
            if cargo_trust_wp.exists():
                ra.harness_runner._stable_harness_bin_dir(
                    workspace, cargo_trust_wp, ra.harness._current_facade()
                )
        except (OSError, AttributeError):
            pass
        outcomes = ra.run_cases_parallel(
            workspace, cases, shared, args.timeout, False, False, max(1, min(args.jobs, len(cases)))
        )
    finally:
        if not env_target:
            shutil.rmtree(shared, ignore_errors=True)

    out = {}
    for o in outcomes:
        text = o.output or ""
        out[o.case.name] = {
            "verdict": o.verdict,
            "verified_functions": ra.verified_functions(text),
            "assertion_credits": ra.standing_assertion_credits(text),
            "unproved_assertion_functions": sorted(ra.unproved_assertion_functions(text)),
            "trust_wp_lines": ra.trust_wp_lines(text)[:200],
            "error": None if ra.wire_telemetry(text) is not None else "no TRUST_WP_RESULT line (no verdict)",
        }
    Path(args.json).write_text(json.dumps(out, indent=1, sort_keys=True) + "\n")
    return 0


if __name__ == "__main__":
    sys.exit(main())
