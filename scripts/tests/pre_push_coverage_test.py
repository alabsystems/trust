"""Check live push obligations; scope regressions are explicit diagnostics.

A manifest declaration is inventory, not execution evidence. The retired scope
row is absent from development push, and its actual test module is selected by
validator diagnostics when the corresponding runner changes.

The push profile is the eight live verifier and proof-input integrity rows
DEV-MAIN-FOCUSED-VALIDATION-20261102 kept; the three history rows 4d802efa09c2
wired back in (the full hook had silently run none of them while the narrow
hook ran all three); and `fast.corpus-membership`
(CORPUS-MEMBERSHIP-AT-LANDING-1), `fast.ledger-pins`
(LEDGER-PIN-CURRENCY-AT-LANDING-1) and `fast.land-rows-coverage`
(LAND-ROWS-COVERAGE-AT-LANDING-1): git-objects checks that compile nothing,
kept apart below because each record argues it separately.
"""
from pathlib import Path
import subprocess
import unittest

REPO = Path(__file__).resolve().parents[2]
LIVE_PUSH_ROWS = {
    "fast.trust-ir-verifier-acceptance-pins": "python3 scripts/trust_ir_verifier_acceptance_pins.py --check",
    "fast.pin-coherence": "bash scripts/check_pin_coherence.sh",
    "fast.oracle-freeze": "bash scripts/check_frozen_files.sh",
    "fast.bridge-pin": "bash scripts/check_bridge_pin.sh --check",
    "fast.patch-binds": "python3 scripts/check_patch_binds.py",
    "fast.audited-trust-spec-sources": "python3 scripts/check_audited_trust_spec_sources.py",
    "fast.submodule-remote-reachability": "python3 scripts/check_submodule_remote_reachability.py --push-context",
    "verify.executes": "bash scripts/check_verifier_executes.sh",
}
# Each judges the pushed range's history or source when TRUST_PUSHED_REFS is
# set; 4d802efa09c2 (2026-11-12) made them push rows, and this table was not
# moved with them.
HISTORY_PUSH_ROWS = {
    "fast.cfg-test-caller-skew": "python3 scripts/check_cfg_test_caller_skew.py --push-context",
    "fast.revert-rationale": "bash scripts/check_revert_rationale.sh --push-context",
    "fast.measurement-provenance": "bash scripts/check_measurement_provenance.sh --push-context",
}
# A landing that moves a pinned corpus membership must carry its re-pin; only
# the push can see that, so this row is a push row (docs/DECISION_QUEUE.md
# CORPUS-MEMBERSHIP-AT-LANDING-1).
MEMBERSHIP_PUSH_ROWS = {
    "fast.corpus-membership": "python3 scripts/check_corpus_membership.py",
    # A landing that moves a blob the escape-audit ledger or the IR read set
    # pins must renew or explicitly lapse the entry in the same push
    # (LEDGER-PIN-CURRENCY-AT-LANDING-1).
    "fast.ledger-pins": "python3 scripts/check_ledger_pins.py",
    # A landing that adds a scripts/tests/*_test.py module registers it in
    # gates/land.toml in the same push (LAND-ROWS-COVERAGE-AT-LANDING-1).
    "fast.land-rows-coverage": "python3 -B scripts/land_gate.py rows --check",
}
SCOPE_ROW = "fast.scoped-lane-scope-selftest"
SCOPE_COMMAND = "python3 -B scripts/tests/scoped_lane_push_scope_test.py"


def parse_rows(output):
    rows = {}
    for line in output.splitlines():
        fields = line.split("\t", 4)
        if len(fields) != 5 or not fields[0] or not fields[4] or fields[2] not in {"true", "false"}:
            raise ValueError(f"invalid manifest row: {line!r}")
        if fields[0] in rows:
            raise ValueError(f"duplicate manifest row: {fields[0]}")
        rows[fields[0]] = (fields[2], fields[4])
    if not rows:
        raise ValueError("empty manifest profile")
    return rows


def profile_rows(profile):
    result = subprocess.run(
        ["bash", "tests/run_trust_comprehensive_harness.sh", "--list", profile],
        cwd=REPO, capture_output=True, text=True, check=True,
    )
    return parse_rows(result.stdout)


class HookCoverage(unittest.TestCase):
    def test_push_retains_only_live_verifier_proof_input_and_membership_rows(self):
        rows = profile_rows("push")
        expected = {**LIVE_PUSH_ROWS, **HISTORY_PUSH_ROWS, **MEMBERSHIP_PUSH_ROWS}
        self.assertEqual(rows, {key: ("true", command) for key, command in expected.items()})

    def test_scope_suite_is_explicit_inventory_not_a_push_execution_claim(self):
        self.assertNotIn(SCOPE_ROW, profile_rows("push"))
        self.assertEqual(profile_rows("fast")[SCOPE_ROW], ("true", SCOPE_COMMAND))

    def test_empty_malformed_and_duplicate_profiles_refuse(self):
        valid = "verify.executes\tsoundness\ttrue\tnever\tbash scripts/check_verifier_executes.sh\n"
        for output in ("", "verify.executes\n", valid + valid,
                       valid.replace("\ttrue\t", "\tmaybe\t"),
                       "verify.executes\tsoundness\ttrue\tnever\t\n"):
            with self.subTest(output=output):
                with self.assertRaises(ValueError):
                    parse_rows(output)
        self.assertEqual(parse_rows(valid)["verify.executes"], ("true", LIVE_PUSH_ROWS["verify.executes"]))


if __name__ == "__main__":
    unittest.main()
