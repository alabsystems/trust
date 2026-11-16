#!/usr/bin/env python3
"""Mutation controls for exact versus intentional-prefix tooling roles."""

from __future__ import annotations

import importlib.util
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock


SCRIPT = Path(__file__).resolve().parents[1] / "check_gate_lane_coverage.py"
SPEC = importlib.util.spec_from_file_location("check_gate_lane_coverage", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
coverage = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = coverage
SPEC.loader.exec_module(coverage)


class ToolingRoleControls(unittest.TestCase):
    def test_exact_tooling_role_does_not_hide_suffix_twin(self) -> None:
        for exact in (
            "scripts/machine_preflight.sh",
            "scripts/trust_upstream_test_inventory.py",
            "scripts/lean_island_census.py",
            "scripts/dispatch_cost.py",
            "scripts/prune_seal_symlinks.py",
            "scripts/trust_fast_iterate.sh",
        ):
            with self.subTest(exact=exact):
                self.assertTrue(coverage._is_tooling(exact))
                self.assertFalse(coverage._is_tooling(f"{exact}.evil.py"))

    def test_declared_directory_and_stem_roles_remain_prefixes(self) -> None:
        self.assertTrue(coverage._is_tooling("scripts/lib/process_tree.sh"))
        self.assertTrue(coverage._is_tooling("scripts/install-example.sh"))


class DivergenceGateIdControls(unittest.TestCase):
    def setUp(self) -> None:
        self.rows = coverage.manifest_rows()
        self.ledger = coverage.DIVERGENCES.read_text(encoding="utf-8")

    def test_real_ledger_names_only_manifest_gates(self) -> None:
        self.assertEqual(coverage.divergence_gate_errors(self.rows, self.ledger), [])

    def test_active_row_naming_a_nonexistent_gate_is_refused(self) -> None:
        # The row under test is SYNTHETIC, appended to the real ledger text, so
        # the check keeps its teeth whatever the real ledger holds. This test
        # used to mutate the real ledger's first `active` row and asserted one
        # existed — so it went RED on 2026-09-27 when 284ff7b208 retired the last
        # active divergence, i.e. it failed because the system got healthier.
        # Having zero open quarantines is the goal state, not a test defect.
        manifest_ids = sorted({row[0] for row in self.rows if len(row) == 6})
        self.assertTrue(manifest_ids, "the manifest has no rows to name")
        real_gate = manifest_ids[0]
        div_id = "synthetic.gate-lane-coverage-test.active-row"

        def with_active_row(gate_id: str) -> str:
            return (
                self.ledger.rstrip("\n")
                + "\n\n[[divergences]]\n"
                + f'id = "{div_id}"\n'
                + f'gate_id = "{gate_id}"\n'
                + 'status = "active"\n'
            )

        # Control: an active row naming a REAL manifest gate is accepted, so the
        # refusal below is about the gate id and nothing else.
        self.assertEqual(coverage.divergence_gate_errors(self.rows, with_active_row(real_gate)), [])
        self.assertIn((div_id, real_gate), coverage.active_divergences(with_active_row(real_gate)))

        errors = coverage.divergence_gate_errors(self.rows, with_active_row("no.such-gate"))
        self.assertEqual(len(errors), 1)
        self.assertIn(div_id, errors[0])
        self.assertIn("no.such-gate", errors[0])

    def test_retired_row_keeps_its_historical_gate_id_unchecked(self) -> None:
        # The verify.precision row names a gate that never existed and is retired
        # rather than re-pointed; only `active` rows can match in the harness.
        self.assertNotIn("verify.precision", [g for _i, g in coverage.active_divergences(self.ledger)])
        self.assertIn('gate_id = "verify.precision"', self.ledger)


class PrePushHookControls(unittest.TestCase):
    """scripts/hooks/pre-push derives its lanes; it keeps no second copy of any set.

    These controls mutate the hook's BEHAVIOR (its derivation commands and any
    enumeration of the derived reader set), never its comment prose. The
    pre-2026-11-03 controls anchored mutations inside a `# PUSH CONTEXT.`
    section delimited by `# WHY THE REACHABILITY LANE`; that prose went away
    when the hook header was rewritten on 2026-11-02,
    and every behavior it guarded was unchanged.
    """

    def setUp(self) -> None:
        self.rows = coverage.manifest_rows()
        self.hook = (coverage.REPO_ROOT / coverage.PRE_PUSH_HOOK).read_text(encoding="utf-8")
        self.readers = coverage.push_refs_reader_gate_ids(self.rows)

    def test_real_hook_keeps_no_lane_list(self) -> None:
        self.assertEqual(coverage.pre_push_hook_errors(self.rows, self.hook), [])

    def test_reader_set_is_derived_from_push_rows_and_their_scripts(self) -> None:
        self.assertTrue(self.readers, "no push row reads TRUST_PUSHED_REFS")
        by_id = {row[0]: row for row in self.rows if len(row) == 6}
        for gate_id in self.readers:
            row = by_id[gate_id]
            self.assertIn("push", row[1].split(","))
            self.assertNotRegex(row[5], r"(^|\s)--self")

    def test_flagless_readers_are_derived_too(self) -> None:
        # The `--push-context` flag alone found half the readers on 2026-09-28:
        # a check script that reads the variable whenever it is set takes no
        # flag. Proven on SYNTHETIC rows, so this control keeps its teeth
        # whatever profile mix the real manifest currently carries.
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "scripts").mkdir()
            (root / "scripts" / "check_reads.sh").write_text("echo $TRUST_PUSHED_REFS\n")
            rows = [
                ["fast.flagless", "fast,push", "c", "true", "never", "bash scripts/check_reads.sh"],
                ["fast.flagged", "fast,push", "c", "true", "never", "bash scripts/check_reads.sh --push-context"],
            ]
            self.assertEqual(
                coverage.push_refs_reader_gate_ids(rows, root),
                ["fast.flagless", "fast.flagged"],
            )

    def test_a_script_that_stops_reading_leaves_the_set(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "scripts").mkdir()
            (root / "scripts" / "check_reads.sh").write_text("echo $TRUST_PUSHED_REFS\n")
            (root / "scripts" / "check_ignores.sh").write_text("echo hi\n")
            rows = [
                ["fast.reads", "fast,push", "c", "true", "never", "bash scripts/check_reads.sh"],
                ["fast.reads-self", "fast,push", "c", "true", "never", "bash scripts/check_reads.sh --selftest"],
                ["fast.ignores", "fast,push", "c", "true", "never", "bash scripts/check_ignores.sh"],
                ["fast.not-push", "fast", "c", "true", "never", "bash scripts/check_reads.sh"],
            ]
            self.assertEqual(coverage.push_refs_reader_gate_ids(rows, root), ["fast.reads"])

    def test_a_landing_gate_push_row_reads_the_push(self) -> None:
        # New push checks are land_gate.py subcommands (fast.land-rows-coverage),
        # not new scripts/check_* files: the gate is a reader by the same rule.
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "scripts").mkdir()
            (root / "scripts" / "land_gate.py").write_text("os.environ['TRUST_PUSHED_REFS']\n")
            (root / "scripts" / "other_gate.py").write_text("os.environ['TRUST_PUSHED_REFS']\n")
            rows = [
                ["fast.gate", "fast,push", "c", "true", "never", "python3 -B scripts/land_gate.py rows --check"],
                ["fast.other", "fast,push", "c", "true", "never", "python3 scripts/other_gate.py"],
                # land_gate.py names the variable for push-rows: another
                # subcommand is not presumed to read the push.
                ["fast.explain", "fast,push", "c", "true", "never", "python3 -B scripts/land_gate.py explain x"],
                ["fast.bare", "fast,push", "c", "true", "never", "python3 -B scripts/land_gate.py"],
            ]
            self.assertEqual(coverage.push_refs_reader_gate_ids(rows, root), ["fast.gate"])
            (root / "scripts" / "land_gate.py").write_text("pass\n")
            self.assertEqual(coverage.push_refs_reader_gate_ids(rows, root), [])
        self.assertIn("fast.land-rows-coverage", self.readers)

    def test_enumerating_the_reader_set_is_refused(self) -> None:
        self.assertGreaterEqual(len(self.readers), 2, "need two readers to enumerate")
        mutated = self.hook + f"\nREADERS=\"{' '.join(self.readers[:2])}\"\n"
        errors = coverage.pre_push_hook_errors(self.rows, mutated)
        self.assertEqual(len(errors), 1, errors)
        for gate_id in self.readers[:2]:
            self.assertIn(gate_id, errors[0])

    def test_a_single_reader_named_for_its_own_behavior_is_not_a_copy(self) -> None:
        mutated = self.hook + f"\n# QUARANTINE note: see {self.readers[0]}.\n"
        self.assertEqual(coverage.pre_push_hook_errors(self.rows, mutated), [])

    def test_a_longer_id_sharing_the_prefix_is_not_a_match(self) -> None:
        self.assertGreaterEqual(len(self.readers), 2, "need two readers to enumerate")
        mutated = self.hook + "\n# see " + " and ".join(
            f"{gate_id}-selftest" for gate_id in self.readers[:2]
        ) + "\n"
        self.assertEqual(coverage.pre_push_hook_errors(self.rows, mutated), [])

    def test_a_longer_id_sharing_the_suffix_is_not_a_match(self) -> None:
        self.assertGreaterEqual(len(self.readers), 2, "need two readers to enumerate")
        mutated = self.hook + "\n# see " + " and ".join(
            f"x{gate_id}" for gate_id in self.readers[:2]
        ) + "\n"
        self.assertEqual(coverage.pre_push_hook_errors(self.rows, mutated), [])

    def test_a_hook_that_stops_deriving_its_lanes_is_refused(self) -> None:
        mutated = self.hook.replace("--list push", "--list fast")
        self.assertNotEqual(mutated, self.hook, "the real hook derives from --list push")
        errors = coverage.pre_push_hook_errors(self.rows, mutated)
        self.assertEqual(len(errors), 1, errors)
        self.assertIn("--list push", errors[0])

    def test_a_hook_that_stops_exporting_push_context_is_refused(self) -> None:
        mutated = self.hook.replace(
            "export TRUST_PUSHED_REFS=", "TRUST_PUSHED_REFS_LOCAL=", 1
        )
        self.assertNotEqual(mutated, self.hook, "the real hook exports TRUST_PUSHED_REFS")
        errors = coverage.pre_push_hook_errors(self.rows, mutated)
        self.assertEqual(len(errors), 1, errors)
        self.assertIn("does not export TRUST_PUSHED_REFS", errors[0])

    def test_a_hook_that_stops_deriving_its_readers_is_refused(self) -> None:
        mutated = self.hook.replace(
            "check_gate_lane_coverage.py --push-refs-readers",
            "check_gate_lane_coverage.py --list-uncovered",
        )
        self.assertNotEqual(mutated, self.hook, "the real hook derives its readers")
        errors = coverage.pre_push_hook_errors(self.rows, mutated)
        self.assertEqual(len(errors), 1, errors)
        self.assertIn("--push-refs-readers", errors[0])

    def test_literal_run_lane_is_refused(self) -> None:
        mutated = self.hook + "\nrun_lane fast.ledger-expirations true true\n"
        errors = coverage.pre_push_hook_errors(self.rows, mutated)
        self.assertEqual(len(errors), 1)
        self.assertIn("run_lane with a literal gate id", errors[0])


class NativeAdmissionGateControls(unittest.TestCase):
    def test_real_manifest_runs_oracle_controls_and_native_provenance(self) -> None:
        self.assertEqual(coverage.native_admission_gate_errors(coverage.manifest_rows()), [])

    def test_oracle_only_optional_or_unbound_native_rows_are_rejected(self) -> None:
        rows = coverage.manifest_rows()
        native = next(row for row in rows if row[0] == "release.native-admission-census")
        self.assertTrue(coverage.native_admission_gate_errors(
            [row for row in rows if row is not native]
        ))
        for column, value in (
            (1, "fast"), (1, "fast,push,release"), (3, "false"),
            (5, "python3 tests/native-admission-census/test_run.py"),
            (5, "python3 tests/native-admission-census/run.py --bin build/host/stage2/bin"),
        ):
            with self.subTest(column=column, value=value):
                mutated = [row.copy() for row in rows]
                target = next(row for row in mutated if row[0] == native[0])
                target[column] = value
                self.assertTrue(coverage.native_admission_gate_errors(mutated))


class ScriptTestDriverRowControls(unittest.TestCase):
    """scripts/tests/targo_dependency_filename_process.py, the real process
    regression DECISION_QUEUE names for 935dc6f944 and a243bae0a2, is not a
    *_test file, so the script-test aggregate never runs it: it came in with no
    row and the checker reported it (TARGO-FILENAME-PROCESS-ROW-1)."""

    PROBE = "scripts/tests/targo_dependency_filename_process.py"
    GATE = "slow.targo-dependency-filename-process"

    def test_the_filename_process_probe_is_a_row_with_explicit_producers(self) -> None:
        probe = coverage.REPO_ROOT / self.PROBE
        self.assertIn(probe, coverage.lane_inventory()["script-test"])
        self.assertFalse(probe.name.endswith(("_test.py", "_test.sh")))
        self.assertNotIn(self.PROBE, coverage.INDIRECT)
        self.assertNotIn(self.PROBE, coverage.MANUAL_ONLY)
        rows = coverage.manifest_rows()
        named = [row for row in rows if len(row) == 6 and coverage._named_by(self.PROBE, row[5])]
        self.assertEqual([row[0] for row in named], [self.GATE])
        _gate, profiles, _category, required, _last_green, command = named[0]
        self.assertIn("slow", profiles.split(","))
        self.assertEqual(required, "true")
        for producer in ('--targo "$(pwd -P)/build/host/stage2/bin/targo"',
                         '--rustc "$(pwd -P)/build/host/stage2/bin/trustc"',
                         '--evidence "$(mktemp -d)/evidence"'):
            self.assertIn(producer, command)
        _errors, uncovered = coverage.check()
        self.assertNotIn("script-test: " + self.PROBE, uncovered)
        # Control: without its row the checker reports the probe again.
        without = [row for row in rows if row[0] != self.GATE]
        with mock.patch.object(coverage, "manifest_rows", return_value=without):
            _errors, uncovered = coverage.check()
        self.assertIn("script-test: " + self.PROBE, uncovered)


if __name__ == "__main__":
    unittest.main()
