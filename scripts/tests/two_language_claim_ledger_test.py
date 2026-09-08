#!/usr/bin/env python3
"""Adversarial controls for the two-language coordination claim ledger."""

from __future__ import annotations

import copy
import importlib.util
import json
import os
import subprocess
import sys
import tempfile
import unittest
from datetime import datetime, timedelta, timezone
from pathlib import Path
from typing import Dict, Iterable, List, Mapping, Optional


REPO_ROOT = Path(__file__).resolve().parents[2]
SCRIPT = REPO_ROOT / "scripts" / "check_two_language_claim_ledger.py"
NOW = datetime(2026, 8, 31, 12, 0, tzinfo=timezone.utc)
MIRROR_PREFIX = "refs/test-remotes/origin/claims"


def at(offset: timedelta) -> str:
    """A fixture timestamp expressed against the pinned clock, never the calendar."""
    return (NOW + offset).strftime("%Y-%m-%dT%H:%M:%SZ")


# NOW IS DELIBERATELY IN THE WALL-CLOCK PAST, and every fixture timestamp is
# derived from it.
#
# This suite has two ways to reach the checker: in-process `ledger.validate(...)`
# calls, which pass `now=NOW`, and CLI subprocesses, which must pass `--now`.
# The CLI helper below did not, so it read the real clock while its fixture
# claim carried a hard-coded `2026-09-01T23:00:00Z` lease -- and at exactly
# 23:00Z on 2026-09-01 the lane went red on the calendar, in a fixture repo,
# for a claim id (`W0/alpha`) that exists in no ledger. A gate that fails at a
# wall-clock instant nobody chose is worse than one that never passes: it looks
# like live state and is not.
#
# Keeping NOW behind the present makes that class of defect fail IMMEDIATELY
# instead of at some future midnight: an unpinned run sees a lease that expired
# long ago and goes red on the spot. `test_cli_runs_are_clock_pinned` is the
# standing control for it.
NOW_ARG = at(timedelta())
DEFAULT_LEASE = at(timedelta(hours=24))


def load_validator_module():
    spec = importlib.util.spec_from_file_location("check_two_language_claim_ledger", SCRIPT)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


ledger = load_validator_module()


def git(repo: Path, *args: str) -> str:
    completed = subprocess.run(
        ["git", "-C", str(repo), *args],
        check=True,
        capture_output=True,
        text=True,
    )
    return completed.stdout.strip()


def claim_path(claim: Mapping[str, object]) -> str:
    path = ledger.expected_claim_path(str(claim["claim_id"]))
    assert path is not None
    return path


def encode_claim(claim: Mapping[str, object]) -> bytes:
    return (json.dumps(claim, indent=2, sort_keys=True, allow_nan=False) + "\n").encode(
        "utf-8"
    )


def claim_documents(*claims: Mapping[str, object]) -> Dict[str, bytes]:
    return {claim_path(claim): encode_claim(claim) for claim in claims}


def make_claim(
    integration: str,
    *,
    workstream: str = "W0",
    increment: str = "alpha",
    exact_files: Optional[List[str]] = None,
    dependencies: Optional[List[str]] = None,
    status: str = "active",
    lease_expires_at: str = DEFAULT_LEASE,
) -> Dict[str, object]:
    claim_id = f"{ledger.GOAL_ID}/{workstream}/{increment}"
    return {
        "schema": ledger.SCHEMA,
        "claim_id": claim_id,
        "goal_id": ledger.GOAL_ID,
        "ledger_ref": ledger.LEDGER_REF,
        "owner": f"fixture-{increment}",
        "base_revision": integration,
        "integration_head": integration,
        "owning_branch": f"fixture/{workstream}/{increment}",
        "exact_files": exact_files or [f"src/{increment}.rs"],
        "semantic_boundary": f"Fixture semantic boundary for {increment}",
        "dependencies": dependencies or [],
        "baseline_population": {"open": 1},
        "expected_population": {"open": 0},
        "expected_evidence": ["positive", "negative twin", "mutation control"],
        "narrow_validation_rung": "focused fixture controls",
        "downstream_gate_not_exercised": "full G1-G8 release acceptance",
        "tcb_change": "none",
        "created_at": at(timedelta(hours=-36)),
        "lease_expires_at": lease_expires_at,
        "status": status,
    }


class GitFixture:
    """Small real repository with a pinned integration commit and ledger helpers."""

    def __init__(self) -> None:
        self._temporary = tempfile.TemporaryDirectory()
        self.repo = Path(self._temporary.name) / "repo"
        self.repo.mkdir()
        git(self.repo, "init", "-q")
        git(self.repo, "config", "user.name", "Claim Ledger Test")
        git(self.repo, "config", "user.email", "claim-ledger@example.invalid")
        self.write("seed.txt", "root\n")
        self.commit("root")
        self.root_commit = git(self.repo, "rev-parse", "HEAD")
        self.write("integration.txt", "pinned integration\n")
        self.commit("integration")
        self.integration_commit = git(self.repo, "rev-parse", "HEAD")
        git(
            self.repo,
            "update-ref",
            "refs/heads/integration",
            self.integration_commit,
        )

    def __enter__(self) -> "GitFixture":
        return self

    def __exit__(self, *_args: object) -> None:
        self.cleanup()

    def cleanup(self) -> None:
        self._temporary.cleanup()

    def write(self, relative: str, text: str) -> None:
        path = self.repo / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text, encoding="utf-8")

    def commit(self, message: str) -> str:
        git(self.repo, "add", "-A")
        git(self.repo, "commit", "--allow-empty", "-qm", message)
        return git(self.repo, "rev-parse", "HEAD")

    def commit_ledger(
        self,
        claims: Iterable[Mapping[str, object]],
        *,
        message: str = "ledger",
        include_required_paths: bool = True,
    ) -> str:
        claims = list(claims)
        claims_dir = self.repo / ledger.CLAIM_TREE_DIR
        claims_dir.mkdir(parents=True, exist_ok=True)
        wanted = {Path(claim_path(claim)).name for claim in claims}
        for existing in claims_dir.iterdir():
            if existing.is_file() and existing.name not in wanted:
                existing.unlink()
        for claim in claims:
            path = self.repo / claim_path(claim)
            path.write_bytes(encode_claim(claim))
        if include_required_paths:
            self.write("AGENTS.md", "fixture coordination directive\n")
            self.write(
                "docs/TWO_LANGUAGE_100_PERCENT_GOAL.md",
                "fixture owner goal\n",
            )
            self.write(ledger.VALIDATOR_PATH, "# fixture validator marker\n")
        return self.commit(message)

    def validate_documents(self, documents: Mapping[str, bytes]):
        return ledger.validate(
            repo=self.repo,
            documents=documents,
            integration_commit=self.integration_commit,
            now=NOW,
            source="fixture-worktree",
        )

    def validate_ledger(
        self,
        commit: str,
        *,
        history: bool = False,
        mirrors: bool = False,
        expected_parent: Optional[str] = None,
        bootstrap_commit: Optional[str] = None,
    ):
        return ledger.validate(
            repo=self.repo,
            documents=ledger.claim_documents_from_tree(self.repo, commit),
            integration_commit=self.integration_commit,
            now=NOW,
            source=f"git:{commit}",
            ledger_commit=commit,
            check_history=history,
            mirror_ref_prefix=MIRROR_PREFIX if mirrors else None,
            expected_parent=expected_parent,
            bootstrap_commit=bootstrap_commit,
        )

    def set_mirror(self, claim_id: str, commit: str) -> str:
        ref = f"{MIRROR_PREFIX}/{claim_id}"
        git(self.repo, "update-ref", ref, commit)
        return ref

    def advance_integration(self, relative: str, text: str, message: str) -> str:
        """Move the integration head forward by one ordinary commit."""
        git(self.repo, "checkout", "-q", self.integration_commit)
        self.write(relative, text)
        self.integration_commit = self.commit(message)
        git(self.repo, "update-ref", "refs/heads/integration", self.integration_commit)
        return self.integration_commit

    def fork_commit(self, relative: str, text: str, message: str) -> str:
        """A commit on a branch the integration head does not contain."""
        git(self.repo, "checkout", "-q", "-B", "fork", self.root_commit)
        self.write(relative, text)
        forked = self.commit(message)
        git(self.repo, "checkout", "-q", self.integration_commit)
        return forked

    def stage_gitlink(self, path: str, commit: str, message: str) -> str:
        """Move a 160000 gitlink entry without materialising a submodule."""
        git(self.repo, "update-index", "--add", "--cacheinfo", f"160000,{commit},{path}")
        git(self.repo, "commit", "-qm", message)
        self.integration_commit = git(self.repo, "rev-parse", "HEAD")
        git(self.repo, "update-ref", "refs/heads/integration", self.integration_commit)
        return self.integration_commit


class LedgerTestCase(unittest.TestCase):
    def setUp(self) -> None:
        self.fixture = GitFixture()

    def tearDown(self) -> None:
        self.fixture.cleanup()

    def assert_error(self, report, fragment: str) -> None:
        self.assertFalse(report.valid)
        self.assertTrue(
            any(fragment in error for error in report.errors),
            f"missing diagnostic {fragment!r} in {report.errors!r}",
        )


class CurrentLedgerControls(LedgerTestCase):
    def test_green_worktree_claims_with_dependency_and_validation(self) -> None:
        alpha = make_claim(self.fixture.integration_commit)
        beta = make_claim(
            self.fixture.integration_commit,
            workstream="W1",
            increment="beta",
            dependencies=[str(alpha["claim_id"])],
        )
        beta["validation_at_integration"] = {
            "integration_head": self.fixture.integration_commit,
            "observed_at": at(timedelta(hours=-1)),
            "results": ["focused controls passed"],
            "limitations": ["release gate not exercised"],
        }

        report = self.fixture.validate_documents(claim_documents(alpha, beta))

        self.assertTrue(report.valid, report.errors)
        self.assertEqual(report.claim_count, 2)
        self.assertEqual(report.active_count, 2)

    def test_strict_json_rejects_ambiguous_or_nonstandard_inputs(self) -> None:
        path = claim_path(make_claim(self.fixture.integration_commit))
        cases = {
            "duplicate key": (b'{"schema": 1, "schema": 2}', "duplicate JSON key"),
            "non-finite number": (b'{"value": NaN}', "non-finite JSON number"),
            "non-utf8": (b"\xff", "claim is not UTF-8"),
            "non-object": (b"[]", "top-level value must be an object"),
        }
        for name, (raw, diagnostic) in cases.items():
            with self.subTest(name=name):
                report = self.fixture.validate_documents({path: raw})
                self.assert_error(report, diagnostic)

    def test_schema_and_filename_are_closed_to_extensions_or_aliases(self) -> None:
        malformed = make_claim(self.fixture.integration_commit)
        malformed.pop("tcb_change")
        malformed["invented_authority"] = True
        report = self.fixture.validate_documents(claim_documents(malformed))
        self.assert_error(report, "missing required keys: tcb_change")
        self.assert_error(report, "unknown keys require a schema bump: invented_authority")

        canonical = make_claim(self.fixture.integration_commit)
        wrong_path = (
            f"{ledger.CLAIM_TREE_DIR}/{ledger.GOAL_ID}.W0.not-alpha.json"
        )
        report = self.fixture.validate_documents({wrong_path: encode_claim(canonical)})
        self.assert_error(report, "filename does not match claim_id")

    def test_unsafe_and_non_normalized_owned_paths_are_rejected(self) -> None:
        cases = {
            ".git/config": "reserved Git/coordination state",
            "coordination/claims/forged.json": "reserved Git/coordination state",
            "src/../escape.rs": "contains an empty, '.' or '..' component",
            "/absolute.rs": "normalized repository-relative file path",
            "src/e\u0301.rs": "must use Unicode NFC",
        }
        for path, diagnostic in cases.items():
            with self.subTest(path=path):
                claim = make_claim(self.fixture.integration_commit, exact_files=[path])
                report = self.fixture.validate_documents(claim_documents(claim))
                self.assert_error(report, diagnostic)

    def test_intra_claim_and_cross_claim_prefix_overlaps_are_rejected(self) -> None:
        claim = make_claim(
            self.fixture.integration_commit,
            exact_files=["src/component", "src/component/generated.rs"],
        )
        report = self.fixture.validate_documents(claim_documents(claim))
        self.assert_error(report, "exact_files has overlapping entries")

        alpha = make_claim(
            self.fixture.integration_commit,
            exact_files=["Src/Shared"],
        )
        beta = make_claim(
            self.fixture.integration_commit,
            workstream="W1",
            increment="beta",
            exact_files=["src/shared/generated.rs"],
        )
        report = self.fixture.validate_documents(claim_documents(alpha, beta))
        self.assert_error(report, "active claims")
        self.assert_error(report, "overlap at")

    def test_active_claims_reject_expired_lease(self) -> None:
        expired = make_claim(
            self.fixture.integration_commit,
            lease_expires_at=at(timedelta(seconds=-1)),
        )
        report = self.fixture.validate_documents(claim_documents(expired))
        self.assert_error(report, "active lease is expired")

    def test_active_lease_window_rolls_forward_at_renewal(self) -> None:
        renewed = make_claim(
            self.fixture.integration_commit,
            lease_expires_at=at(timedelta(hours=72)),
        )
        report = self.fixture.validate_documents(claim_documents(renewed))
        self.assertTrue(report.valid, report.errors)

        too_long = make_claim(
            self.fixture.integration_commit,
            lease_expires_at=at(timedelta(hours=72, seconds=1)),
        )
        report = self.fixture.validate_documents(claim_documents(too_long))
        self.assert_error(report, "remaining active lease exceeds the 72-hour policy maximum")

    def test_missing_abandoned_and_cyclic_dependencies_are_rejected(self) -> None:
        missing_id = f"{ledger.GOAL_ID}/W2/missing"
        dependent = make_claim(
            self.fixture.integration_commit,
            dependencies=[missing_id],
        )
        report = self.fixture.validate_documents(claim_documents(dependent))
        self.assert_error(report, f"missing dependency claim {missing_id}")

        abandoned = make_claim(
            self.fixture.integration_commit,
            status="abandoned",
        )
        dependent = make_claim(
            self.fixture.integration_commit,
            workstream="W1",
            increment="beta",
            dependencies=[str(abandoned["claim_id"])],
        )
        report = self.fixture.validate_documents(claim_documents(abandoned, dependent))
        self.assert_error(report, f"dependency {abandoned['claim_id']} is abandoned")

        alpha = make_claim(
            self.fixture.integration_commit,
            dependencies=[f"{ledger.GOAL_ID}/W1/beta"],
        )
        beta = make_claim(
            self.fixture.integration_commit,
            workstream="W1",
            increment="beta",
            dependencies=[str(alpha["claim_id"])],
        )
        report = self.fixture.validate_documents(claim_documents(alpha, beta))
        self.assert_error(report, "claim dependency cycle")

    def test_abandoned_dependent_does_not_freeze_dependency_lifecycle(self) -> None:
        dependency = make_claim(
            self.fixture.integration_commit,
            status="released",
        )
        abandoned_dependent = make_claim(
            self.fixture.root_commit,
            workstream="W3",
            increment="abandoned-dependent",
            dependencies=[str(dependency["claim_id"])],
            status="abandoned",
        )

        report = self.fixture.validate_documents(
            claim_documents(dependency, abandoned_dependent)
        )
        self.assertTrue(report.valid, report.errors)

        abandoned_dependency = copy.deepcopy(dependency)
        abandoned_dependency["status"] = "abandoned"
        report = self.fixture.validate_documents(
            claim_documents(abandoned_dependency, abandoned_dependent)
        )
        self.assertTrue(report.valid, report.errors)

    def test_released_dependent_still_requires_dependency_head_ancestry(self) -> None:
        dependency = make_claim(
            self.fixture.integration_commit,
            status="released",
        )
        released_dependent = make_claim(
            self.fixture.root_commit,
            workstream="W1",
            increment="released-dependent",
            dependencies=[str(dependency["claim_id"])],
            status="released",
        )

        report = self.fixture.validate_documents(
            claim_documents(dependency, released_dependent)
        )
        self.assert_error(report, "integration_head is not an ancestor of the dependent")


class LedgerHistoryControls(LedgerTestCase):
    def test_first_validator_commit_establishes_explicit_bootstrap_boundary(self) -> None:
        claim = make_claim(self.fixture.integration_commit)
        candidate = self.fixture.commit_ledger([claim], message="first validated ledger")
        self.fixture.set_mirror(str(claim["claim_id"]), candidate)

        missing_anchor = self.fixture.validate_ledger(candidate, history=True)
        self.assert_error(
            missing_anchor,
            "history validation requires an explicit bootstrap commit",
        )

        report = self.fixture.validate_ledger(
            candidate,
            history=True,
            mirrors=True,
            expected_parent=self.fixture.integration_commit,
            bootstrap_commit=candidate,
        )

        self.assertTrue(report.valid, report.errors)
        self.assertTrue(
            any("history enforcement bootstrap boundary" in note for note in report.notes),
            report.notes,
        )

    def test_history_rejects_immutable_file_lease_and_terminal_mutations(self) -> None:
        cases = ("immutable", "file removal", "lease shortening", "reactivation")
        for case in cases:
            with self.subTest(case=case), GitFixture() as fixture:
                parent_claim = make_claim(fixture.integration_commit)
                if case == "file removal":
                    parent_claim["exact_files"] = ["src/alpha.rs", "tests/alpha.rs"]
                elif case == "lease shortening":
                    parent_claim["lease_expires_at"] = at(timedelta(hours=35))
                elif case == "reactivation":
                    parent_claim["status"] = "released"
                parent = fixture.commit_ledger([parent_claim], message=f"{case} parent")

                current_claim = copy.deepcopy(parent_claim)
                if case == "immutable":
                    current_claim["owner"] = "different-owner"
                    expected = "mutated immutable"
                elif case == "file removal":
                    current_claim["exact_files"] = ["src/alpha.rs"]
                    expected = "silently removed owned files"
                elif case == "lease shortening":
                    current_claim["lease_expires_at"] = at(timedelta(hours=34))
                    expected = "shortened its lease"
                else:
                    current_claim["status"] = "active"
                    expected = "was mutated or reactivated"

                candidate = fixture.commit_ledger([current_claim], message=f"{case} child")
                report = fixture.validate_ledger(
                    candidate,
                    history=True,
                    bootstrap_commit=parent,
                )
                self.assert_error(report, expected)

    def test_history_rejects_claim_removal(self) -> None:
        alpha = make_claim(self.fixture.integration_commit)
        beta = make_claim(
            self.fixture.integration_commit,
            workstream="W1",
            increment="beta",
        )
        parent = self.fixture.commit_ledger([alpha, beta], message="two claims")
        candidate = self.fixture.commit_ledger([beta], message="claim silently removed")

        report = self.fixture.validate_ledger(
            candidate,
            history=True,
            bootstrap_commit=parent,
        )

        self.assert_error(report, f"ledger history removed claim {alpha['claim_id']}")

    def test_ledger_commit_requires_governing_paths(self) -> None:
        claim = make_claim(self.fixture.integration_commit)
        candidate = self.fixture.commit_ledger(
            [claim],
            message="uncontrolled ledger",
            include_required_paths=False,
        )

        report = self.fixture.validate_ledger(candidate)

        self.assert_error(report, "ledger commit is missing regular required blob")


class MirrorAndParentControls(LedgerTestCase):
    def test_mirrors_allow_identical_ancestor_but_reject_missing_stale_or_orphan(self) -> None:
        claim = make_claim(self.fixture.integration_commit)
        first = self.fixture.commit_ledger([claim], message="claim acquisition")
        second = self.fixture.commit_ledger([claim], message="unrelated ledger append")

        report = self.fixture.validate_ledger(second, mirrors=True)
        self.assert_error(report, "claim mirror")
        self.assert_error(report, "does not resolve to a commit")

        mirror_ref = self.fixture.set_mirror(str(claim["claim_id"]), first)
        report = self.fixture.validate_ledger(second, mirrors=True)
        self.assertTrue(report.valid, report.errors)

        renewed = copy.deepcopy(claim)
        renewed["lease_expires_at"] = at(timedelta(hours=36))
        third = self.fixture.commit_ledger([renewed], message="lease renewal")
        report = self.fixture.validate_ledger(third, mirrors=True)
        self.assert_error(report, "does not carry the current claim record")

        self.fixture.set_mirror(str(claim["claim_id"]), third)
        orphan = f"{MIRROR_PREFIX}/{ledger.GOAL_ID}/W7/orphan"
        git(self.fixture.repo, "update-ref", orphan, third)
        report = self.fixture.validate_ledger(third, mirrors=True)
        self.assert_error(report, "orphan claim mirror not present in ledger")

        git(self.fixture.repo, "update-ref", "-d", orphan)
        descendant = self.fixture.commit("mirror incorrectly points past ledger")
        git(self.fixture.repo, "update-ref", mirror_ref, descendant)
        report = self.fixture.validate_ledger(third, mirrors=True)
        self.assert_error(report, "is not on the ledger first-parent chain")

    def test_expected_parent_must_equal_serialized_ledger_tip(self) -> None:
        claim = make_claim(self.fixture.integration_commit)
        first = self.fixture.commit_ledger([claim], message="first ledger")
        second = self.fixture.commit_ledger([claim], message="second ledger")

        valid = self.fixture.validate_ledger(second, expected_parent=first)
        self.assertTrue(valid.valid, valid.errors)

        invalid = self.fixture.validate_ledger(
            second,
            expected_parent=self.fixture.integration_commit,
        )
        self.assert_error(invalid, "expected serialized tip")


class ActiveBaseFreshnessControls(LedgerTestCase):
    """What ``base_revision`` staleness means, and what it must not mean.

    Until 2026-09-01 an active claim had to name the integration head EXACTLY.
    That refused every push in a continuously-landing repository, rewarded a
    clone that had not fetched, and -- because a claim's ``integration_head``
    must separately be an ancestor of the ledger commit -- contradicted the
    checker's own containment rule whenever the goals branch was not merged up.
    These controls pin the replacement in both directions.
    """

    def test_lagging_base_is_accepted_when_the_reserved_tree_did_not_move(self) -> None:
        # THE DEADLOCK CONTROL. The base is a real ancestor, several commits
        # behind, and nothing it reserves has been touched. That is not a
        # defect and must not refuse a push.
        self.fixture.advance_integration("unrelated/a.rs", "one\n", "unrelated one")
        self.fixture.advance_integration("unrelated/b.rs", "two\n", "unrelated two")
        lagging = make_claim(self.fixture.root_commit, exact_files=["src/alpha.rs"])
        report = self.fixture.validate_documents(claim_documents(lagging))
        self.assertTrue(report.valid, report.errors)

    def test_diverged_base_is_refused(self) -> None:
        forked = self.fixture.fork_commit("side/only.rs", "side\n", "off the line")
        diverged = make_claim(self.fixture.integration_commit, exact_files=["src/alpha.rs"])
        diverged["base_revision"] = forked
        diverged["integration_head"] = forked
        report = self.fixture.validate_documents(claim_documents(diverged))
        self.assert_error(report, "is not an ancestor of the observed integration head")
        self.assert_error(report, "diverged, rewound, or foreign revision")

    def test_overtaken_reservation_is_refused_and_names_path_commit_and_repair(self) -> None:
        # THE REAL DEFECT. Another machine changed the residue under an
        # in-flight increment: exactly what the directive says a stale base is
        # supposed to catch.
        base = self.fixture.integration_commit
        self.fixture.write("src/alpha.rs", "reserved, v1\n")
        self.fixture.commit("seed the reservation")
        base = git(self.fixture.repo, "rev-parse", "HEAD")
        git(self.fixture.repo, "update-ref", "refs/heads/integration", base)
        self.fixture.integration_commit = base
        self.fixture.advance_integration(
            "src/alpha.rs", "taken by another machine\n", "stomp the reservation"
        )
        overtaken = make_claim(base, exact_files=["src/alpha.rs"])
        report = self.fixture.validate_documents(claim_documents(overtaken))
        self.assert_error(report, "is OVERTAKEN")
        self.assert_error(report, "src/alpha.rs")
        self.assert_error(report, "stomp the reservation")
        self.assert_error(report, "refresh_two_language_claim_bases.py")

    def test_change_then_revert_inside_the_reservation_is_not_a_move(self) -> None:
        # The criterion is the operator's own: is the reserved TREE
        # byte-identical. A change that was undone leaves nothing to remeasure.
        self.fixture.write("src/alpha.rs", "reserved, v1\n")
        base = self.fixture.commit("seed the reservation")
        git(self.fixture.repo, "update-ref", "refs/heads/integration", base)
        self.fixture.integration_commit = base
        self.fixture.advance_integration("src/alpha.rs", "churn\n", "churn the reservation")
        self.fixture.advance_integration("src/alpha.rs", "reserved, v1\n", "put it back")
        claim = make_claim(base, exact_files=["src/alpha.rs"])
        report = self.fixture.validate_documents(claim_documents(claim))
        self.assertTrue(report.valid, report.errors)

    def test_reserved_gitlink_move_is_seen_through_ignore_submodules_config(self) -> None:
        # W3 reserves `first-party/ty`. This clone's config sets
        # diff.ignoreSubmodules=all, which would hide a gitlink move from the
        # territory check; the checker passes --ignore-submodules=none for
        # exactly this. Set the hostile config in the fixture and prove it.
        git(self.fixture.repo, "config", "diff.ignoreSubmodules", "all")
        base = self.fixture.stage_gitlink(
            "first-party/ty", self.fixture.root_commit, "reserve the gitlink"
        )
        self.fixture.stage_gitlink(
            "first-party/ty", self.fixture.integration_commit, "move the gitlink"
        )
        claim = make_claim(base, exact_files=["first-party/ty"])
        report = self.fixture.validate_documents(claim_documents(claim))
        self.assert_error(report, "is OVERTAKEN")
        self.assert_error(report, "first-party/ty")

    def test_observed_head_is_the_ledger_merge_base(self) -> None:
        # A claim can only name a revision its own ledger commit contains, so
        # it is judged against merge-base(ledger, integration) and not against
        # an integration tip the ledger has not merged. The same collision IS
        # refused once the ledger observes it.
        self.fixture.write("src/alpha.rs", "reserved, v1\n")
        base = self.fixture.commit("seed the reservation")
        git(self.fixture.repo, "update-ref", "refs/heads/integration", base)
        self.fixture.integration_commit = base

        claim = make_claim(base, exact_files=["src/alpha.rs"])
        ledger_commit = self.fixture.commit_ledger([claim], message="ledger at the base")

        # main runs ahead of the ledger and lands inside the reservation.
        git(self.fixture.repo, "checkout", "-q", base)
        self.fixture.write("src/alpha.rs", "taken after the ledger forked\n")
        ahead = self.fixture.commit("stomp beyond the observed head")
        git(self.fixture.repo, "update-ref", "refs/heads/integration", ahead)
        self.fixture.integration_commit = ahead
        git(self.fixture.repo, "checkout", "-q", ledger_commit)

        beyond = self.fixture.validate_ledger(ledger_commit)
        self.assertTrue(beyond.valid, beyond.errors)
        self.assertTrue(
            any("observed integration head" in note for note in beyond.notes),
            beyond.notes,
        )

        # Once the goals branch integrates that commit, the collision refuses.
        git(self.fixture.repo, "merge", "-q", "--no-edit", ahead)
        merged_ledger = self.fixture.commit_ledger([claim], message="ledger after integrating")
        refused = self.fixture.validate_ledger(merged_ledger)
        self.assert_error(refused, "is OVERTAKEN")


class PushContextSelection(unittest.TestCase):
    """The integration head must not be read from a clone-local cache.

    The gate used to resolve `refs/remotes/origin/main`, so a clone that had
    not fetched audited an older, systematically greener integration line than
    the one it was publishing into. Under `--push-context` the subject is the
    sha git reports for the remote side of the push, and a clone that does not
    have that commit is REFUSED rather than passed.
    """

    def setUp(self) -> None:
        self.fixture = GitFixture()

    def tearDown(self) -> None:
        self.fixture.cleanup()

    def run_checker(self, *args: str, pushed: Optional[str] = None):
        environment = dict(os.environ)
        environment.pop("TRUST_PUSHED_REFS", None)
        if pushed is not None:
            environment["TRUST_PUSHED_REFS"] = pushed
        # --now is not optional and is not the caller's choice: a CLI run that
        # reads the real clock is a lane whose verdict depends on the calendar.
        command = [
            sys.executable,
            str(SCRIPT),
            "--repo",
            str(self.fixture.repo),
            "--now",
            NOW_ARG,
            *args,
        ]
        assert "--now" in command, "every CLI run in this suite must pin the clock"
        return subprocess.run(command, capture_output=True, text=True, env=environment)

    def test_push_context_selects_the_remote_sha_and_refuses_an_unfetched_one(self) -> None:
        claim = make_claim(self.fixture.integration_commit, exact_files=["src/alpha.rs"])
        ledger_commit = self.fixture.commit_ledger([claim], message="ledger")
        base_args = (
            "--ledger-ref",
            ledger_commit,
            "--integration-ref",
            "refs/heads/integration",
            "--push-context",
            "--no-history",
        )

        unset = self.run_checker(*base_args)
        self.assertIn("no push in flight", unset.stdout)
        self.assertEqual(unset.returncode, 0, unset.stderr)

        line = (
            f"refs/heads/main {self.fixture.integration_commit} "
            f"refs/heads/main {self.fixture.root_commit}"
        )
        selected = self.run_checker(*base_args, pushed=line)
        self.assertIn(f"SUBJECT: push (refs/heads/main at remote {self.fixture.root_commit[:12]}",
                      selected.stdout)

        absent = "0" * 39 + "1"
        stale = self.run_checker(
            *base_args,
            pushed=f"refs/heads/main {self.fixture.integration_commit} refs/heads/main {absent}",
        )
        self.assertEqual(stale.returncode, 2, stale.stdout + stale.stderr)
        self.assertIn("which this clone does not have", stale.stderr)
        self.assertIn("git fetch origin", stale.stderr)

    def test_cli_runs_are_clock_pinned(self) -> None:
        """A CLI verdict must come from --now, never from the calendar.

        The lease here expired long ago on the wall clock and is still live
        against the pinned NOW, so this passes ONLY while the helper pins the
        clock. Drop `--now` and it goes red immediately -- which is the whole
        point: the defect it guards used to wait for a wall-clock instant and
        then present itself as live ledger state.
        """
        live_against_now = make_claim(
            self.fixture.integration_commit,
            exact_files=["src/alpha.rs"],
            lease_expires_at=at(timedelta(hours=1)),
        )
        self.assertLess(
            ledger.parse_timestamp(live_against_now["lease_expires_at"], "lease"),
            datetime.now(timezone.utc),
            "the fixture lease must be in the wall-clock PAST for this control to bite",
        )
        commit = self.fixture.commit_ledger([live_against_now], message="ledger")
        green = self.run_checker(
            "--ledger-ref", commit,
            "--integration-ref", "refs/heads/integration",
            "--no-history",
        )
        self.assertEqual(green.returncode, 0, green.stdout + green.stderr)

        # ...and pinning the clock must not have disabled the expiry refusal.
        expired = make_claim(
            self.fixture.integration_commit,
            exact_files=["src/alpha.rs"],
            lease_expires_at=at(timedelta(seconds=-1)),
        )
        commit = self.fixture.commit_ledger([expired], message="ledger, expired lease")
        red = self.run_checker(
            "--ledger-ref", commit,
            "--integration-ref", "refs/heads/integration",
            "--no-history",
        )
        self.assertEqual(red.returncode, 1, red.stdout + red.stderr)
        self.assertIn("active lease is expired", red.stderr)


class MutationProof(LedgerTestCase):
    """Disable each new check and confirm the matching refusal disappears.

    A gate without a demonstrated refusal is a claim. These reverse the
    controls above: with the check neutered the same fixture reports VALID,
    so the check is what is doing the work rather than some incidental rule.
    """

    def _overtaken_fixture(self):
        self.fixture.write("src/alpha.rs", "reserved, v1\n")
        base = self.fixture.commit("seed the reservation")
        git(self.fixture.repo, "update-ref", "refs/heads/integration", base)
        self.fixture.integration_commit = base
        self.fixture.advance_integration("src/alpha.rs", "taken\n", "stomp")
        return make_claim(base, exact_files=["src/alpha.rs"])

    def test_neutering_the_territory_check_loses_the_overtaken_refusal(self) -> None:
        claim = self._overtaken_fixture()
        self.assert_error(
            self.fixture.validate_documents(claim_documents(claim)), "is OVERTAKEN"
        )

        original = ledger.paths_changed_between
        ledger.paths_changed_between = lambda *_args, **_kwargs: []
        try:
            neutered = self.fixture.validate_documents(claim_documents(claim))
        finally:
            ledger.paths_changed_between = original
        self.assertTrue(
            neutered.valid,
            "the overtaken refusal survived the mutation, so it is not the territory "
            f"check that produced it: {neutered.errors}",
        )

    def test_neutering_the_ignore_submodules_override_loses_the_gitlink_refusal(self) -> None:
        # The refusal must come from the override, not from some other read.
        git(self.fixture.repo, "config", "diff.ignoreSubmodules", "all")
        base = self.fixture.stage_gitlink(
            "first-party/ty", self.fixture.root_commit, "reserve"
        )
        self.fixture.stage_gitlink(
            "first-party/ty", self.fixture.integration_commit, "move"
        )
        claim = make_claim(base, exact_files=["first-party/ty"])
        self.assert_error(
            self.fixture.validate_documents(claim_documents(claim)), "is OVERTAKEN"
        )

        original = ledger.paths_changed_between

        def without_override(repo, older, newer, paths):
            if not paths:
                return []
            result = ledger._git(
                repo,
                ["diff", "--name-only", "-z", "--end-of-options", older, newer, "--", *paths],
            )
            return sorted({row.decode() for row in result.stdout.split(b"\0") if row})

        ledger.paths_changed_between = without_override
        try:
            neutered = self.fixture.validate_documents(claim_documents(claim))
        finally:
            ledger.paths_changed_between = original
        self.assertTrue(
            neutered.valid,
            "the gitlink refusal survived dropping --ignore-submodules=none, so that "
            f"flag is not what makes the reservation visible: {neutered.errors}",
        )

    def test_neutering_the_ancestry_check_loses_the_diverged_refusal(self) -> None:
        forked = self.fixture.fork_commit("side/only.rs", "side\n", "off the line")
        claim = make_claim(self.fixture.integration_commit, exact_files=["src/alpha.rs"])
        claim["base_revision"] = forked
        claim["integration_head"] = forked
        self.assert_error(
            self.fixture.validate_documents(claim_documents(claim)),
            "is not an ancestor of the observed integration head",
        )

        original = ledger.is_ancestor
        ledger.is_ancestor = lambda *_args, **_kwargs: True
        try:
            neutered = self.fixture.validate_documents(claim_documents(claim))
        finally:
            ledger.is_ancestor = original
        self.assertTrue(
            neutered.valid,
            "the diverged refusal survived the mutation, so it is not the ancestry "
            f"check that produced it: {neutered.errors}",
        )


class LeaseExpiryWarningControls(LedgerTestCase):
    """The APPROACH to a lapse, in both directions.

    An expired active lease is an error, and this lane runs in the fast, push and
    release profiles -- so a lapse refuses every push in every repo that runs it.
    Until 2026-09-01 the run before a lapse was byte-identical to the run a year
    before it, and eight live claims were sitting on one 11-hour expiry window.

    Every control here is paired.  A warning that fires for everything is the
    same false comfort as no warning at all, so each positive is matched by the
    case that must stay SILENT: outside the horizon, disabled, already expired
    (that is an error, not a warning), and not-active.
    """

    def warn_report(self, *claims, now: datetime, hours: float = 48.0):
        return ledger.validate(
            repo=self.fixture.repo,
            documents=claim_documents(*claims),
            integration_commit=self.fixture.integration_commit,
            now=now,
            source="fixture-worktree",
            lease_warn=timedelta(hours=hours),
        )

    def test_warning_fires_inside_the_horizon_and_is_silent_outside_it(self) -> None:
        claim = make_claim(
            self.fixture.integration_commit,
            lease_expires_at="2026-09-02T00:00:00Z",
        )
        # 12 hours out: inside a 48h horizon.
        inside = self.warn_report(claim, now=datetime(2026, 9, 1, 12, 0, tzinfo=timezone.utc))
        self.assertTrue(inside.valid, inside.errors)
        self.assertTrue(
            any("lease-expiry" in w and claim["claim_id"] in w for w in inside.warnings),
            f"a lease 12h out produced no warning: {inside.warnings!r}",
        )
        self.assertTrue(
            any("12h00m" in w for w in inside.warnings),
            f"the warning does not carry the time remaining: {inside.warnings!r}",
        )

        # 72 hours out: outside the same horizon. This is the half that makes the
        # warning informative rather than decorative.
        outside = self.warn_report(claim, now=datetime(2026, 8, 30, 0, 0, tzinfo=timezone.utc))
        self.assertTrue(outside.valid, outside.errors)
        self.assertEqual(
            [],
            outside.warnings,
            f"a lease 72h out warned inside a 48h horizon: {outside.warnings!r}",
        )

    def test_horizon_zero_restores_the_silent_cliff(self) -> None:
        claim = make_claim(
            self.fixture.integration_commit,
            lease_expires_at="2026-09-02T00:00:00Z",
        )
        now = datetime(2026, 9, 1, 12, 0, tzinfo=timezone.utc)
        self.assertNotEqual([], self.warn_report(claim, now=now).warnings)
        self.assertEqual(
            [],
            self.warn_report(claim, now=now, hours=0).warnings,
            "--lease-warn-hours 0 must disable the approach entirely",
        )

    def test_an_expired_lease_is_an_error_and_not_merely_a_warning(self) -> None:
        claim = make_claim(
            self.fixture.integration_commit,
            lease_expires_at="2026-09-02T00:00:00Z",
        )
        report = self.warn_report(
            claim, now=datetime(2026, 9, 3, 0, 0, tzinfo=timezone.utc)
        )
        self.assert_error(report, "active lease is expired")
        self.assertEqual(
            [],
            report.warnings,
            "a lapse that already happened must be refused, never softened into a "
            f"warning: {report.warnings!r}",
        )

    def test_a_terminal_claim_never_warns(self) -> None:
        released = make_claim(
            self.fixture.integration_commit,
            increment="done",
            status="released",
            lease_expires_at="2026-09-02T00:00:00Z",
        )
        report = self.warn_report(
            released, now=datetime(2026, 9, 1, 12, 0, tzinfo=timezone.utc)
        )
        self.assertTrue(report.valid, report.errors)
        self.assertEqual(
            [],
            report.warnings,
            "a released claim's lease is history and must not be announced as "
            f"expiring: {report.warnings!r}",
        )

    def test_a_shared_instant_is_reported_as_a_cluster(self) -> None:
        """The shape that turns one lapse into a fleet stop gets its own line.

        Claims minted or bumped together carry one instant, so they lapse in one
        moment and the refusal arrives as a fleet-wide stop rather than as one
        claim's problem. Two claims on the SAME instant must say so; two claims
        on merely nearby instants must not, or the cluster line degenerates into
        a restatement of the per-claim warnings.
        """
        shared_a = make_claim(
            self.fixture.integration_commit,
            increment="alpha",
            exact_files=["src/alpha.rs"],
            lease_expires_at="2026-09-02T00:00:00Z",
        )
        shared_b = make_claim(
            self.fixture.integration_commit,
            workstream="W1",
            increment="beta",
            exact_files=["src/beta.rs"],
            lease_expires_at="2026-09-02T00:00:00Z",
        )
        now = datetime(2026, 9, 1, 12, 0, tzinfo=timezone.utc)
        clustered = self.warn_report(shared_a, shared_b, now=now)
        self.assertTrue(clustered.valid, clustered.errors)
        cluster_lines = [w for w in clustered.warnings if "CLUSTER" in w]
        self.assertEqual(
            1, len(cluster_lines), f"expected one cluster line: {clustered.warnings!r}"
        )
        self.assertIn(shared_a["claim_id"], cluster_lines[0])
        self.assertIn(shared_b["claim_id"], cluster_lines[0])

        staggered_b = dict(shared_b)
        staggered_b["lease_expires_at"] = "2026-09-02T03:00:00Z"
        staggered = self.warn_report(shared_a, staggered_b, now=now)
        self.assertTrue(staggered.valid, staggered.errors)
        self.assertEqual(
            [],
            [w for w in staggered.warnings if "CLUSTER" in w],
            "two distinct instants were reported as a cluster; the line then says "
            f"nothing about clustering: {staggered.warnings!r}",
        )
        self.assertEqual(
            2,
            len([w for w in staggered.warnings if "lease-expiry:" in w]),
            f"both staggered claims should still warn individually: {staggered.warnings!r}",
        )

    def test_neutering_the_warning_loses_the_notice_the_lane_prints(self) -> None:
        """MUTATION: the CLI's WARN: lines come from this warning and nothing else."""
        claim = make_claim(
            self.fixture.integration_commit,
            lease_expires_at="2026-09-02T00:00:00Z",
        )
        now = datetime(2026, 9, 1, 12, 0, tzinfo=timezone.utc)
        self.assertNotEqual([], self.warn_report(claim, now=now).warnings)

        original = ledger.LedgerValidator.warn_on_approaching_leases
        ledger.LedgerValidator.warn_on_approaching_leases = lambda *_a, **_k: None
        try:
            neutered = self.warn_report(claim, now=now)
        finally:
            ledger.LedgerValidator.warn_on_approaching_leases = original
        self.assertEqual(
            [],
            neutered.warnings,
            "the notice survived deleting the only thing that emits it, so it is "
            f"coming from somewhere else: {neutered.warnings!r}",
        )


if __name__ == "__main__":
    unittest.main(verbosity=2)
