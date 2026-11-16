#!/usr/bin/env python3
"""Exercise push provenance against actual advertised refs in a local bare remote."""

import os
from pathlib import Path
import subprocess
import tempfile
import unittest


CHECKER = Path(__file__).resolve().parents[1] / "check_measurement_provenance.sh"
ZERO = "0" * 40
SOURCE = "crates/trust-thir-lower/src/lib.rs"
LEDGER = "scripts/measurement-provenance-grandfathered.txt"


class PushScopeTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.repo = self.root / "repo"
        self.remote = self.root / "remote.git"
        self.env = {
            key: value for key, value in os.environ.items()
            if not key.startswith(("GIT_", "TRUST_PUSH"))
        }
        self.env.update(GIT_CONFIG_NOSYSTEM="1", GIT_CONFIG_GLOBAL=os.devnull)
        self.run_command(["git", "init", "--bare", "--quiet", str(self.remote)])
        self.run_command(["git", "init", "--quiet", "--initial-branch=main", str(self.repo)])
        self.git("config", "user.name", "test")
        self.git("config", "user.email", "test@example.invalid")
        self.git("config", "commit.gpgsign", "false")
        (self.repo / SOURCE).parent.mkdir(parents=True)
        self.base = self.commit("base", "fn base() {}\n")
        self.git("remote", "add", "origin", str(self.remote))
        self.git("push", "--quiet", "origin", "main", "HEAD:refs/heads/topic")
        self.published = self.commit("published historical claim\n\n3 passed, 2 failed", "fn published() {}\n")
        self.git("push", "--quiet", "origin", "main")
        self.git("checkout", "--quiet", "-b", "topic", self.base)
        self.local = self.commit("topic change", "fn topic() {}\n", "topic.rs")
        self.git("merge", "--quiet", "--no-edit", "main")

    def run_command(self, argv, **kwargs):
        return subprocess.run(
            argv, env=self.env, text=True, stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT, check=True, timeout=30, **kwargs,
        ).stdout.strip()

    def git(self, *args):
        return self.run_command(["git", "-C", str(self.repo), *args])

    def commit(self, message, source, path=SOURCE):
        (self.repo / path).write_text(source)
        self.git("add", "--", path)
        self.run_command(
            ["git", "-C", str(self.repo), "commit", "--quiet", "--file=-"],
            input=message + "\n",
        )
        return self.git("rev-parse", "HEAD")

    def check(self, old=None, *, destination=True, extra_lines="", mode="--pre-push"):
        head = self.git("rev-parse", "HEAD")
        row = f"refs/heads/topic {head} refs/heads/topic {old or self.base}\n" + extra_lines
        args = ["bash", str(CHECKER), mode]
        env = dict(self.env)
        if mode == "--push-context":
            env["TRUST_PUSHED_REFS"] = row
            if destination:
                env["TRUST_PUSH_REMOTE"] = str(self.remote)
        elif destination:
            args.extend(["--remote", str(self.remote)])
        return subprocess.run(
            args, cwd=self.repo, env=env, input=row, text=True,
            stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=30,
        )

    def test_published_unstamped_history_does_not_block_topic_alignment(self):
        result = self.check()
        self.assertEqual(result.returncode, 0, result.stdout)
        self.assertIn("commits introduced to the push destination", result.stdout)
        conservative = self.check(destination=False)
        self.assertEqual(conservative.returncode, 1, conservative.stdout)
        audit = subprocess.run(
            ["bash", str(CHECKER), f"{self.base}..HEAD"], cwd=self.repo,
            env=self.env, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
            timeout=30,
        )
        self.assertEqual(audit.returncode, 1, audit.stdout)
        self.assertIn(self.published, audit.stdout)

    def test_unpublished_claim_is_rejected_despite_forged_tracking_refs(self):
        bad = self.commit("new unstamped claim\n\n7 passed, 0 failed", "fn unmeasured() {}\n")
        self.git("update-ref", "refs/remotes/origin/main", bad)
        self.git("update-ref", "refs/remotes/elsewhere/main", bad)
        for old in [self.base, ZERO]:
            result = self.check(old)
            self.assertEqual(result.returncode, 1, result.stdout)
            self.assertIn(bad, result.stdout)
            self.assertIn("FAIL (R2)", result.stdout)

    def test_published_lying_stamp_remains_invalid_in_history_audits(self):
        self.git("checkout", "--quiet", "main")
        bad = self.commit(
            f"published false stamp\n\nMeasured-on: {SOURCE}@{'1' * 40}",
            "fn false_stamp() {}\n",
        )
        self.git("push", "--quiet", "origin", "main")
        self.git("checkout", "--quiet", "topic")
        self.git("merge", "--quiet", "--no-edit", "main")
        for old in [self.base, ZERO]:
            result = self.check(old)
            self.assertEqual(result.returncode, 0, result.stdout)
            self.assertNotIn(bad, result.stdout)
        for mode in [[f"{self.base}..HEAD"], ["--history", self.base]]:
            audit = subprocess.run(
                ["bash", str(CHECKER), *mode], cwd=self.repo, env=self.env,
                text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=30,
            )
            self.assertEqual(audit.returncode, 1, audit.stdout)
            self.assertIn("FAIL (R1)", audit.stdout)
            self.assertIn(bad, audit.stdout)
        conservative = self.check(destination=False)
        self.assertEqual(conservative.returncode, 1, conservative.stdout)
        self.assertIn(bad, conservative.stdout)

    def test_new_lying_stamp_is_rejected_despite_tracking_refs_and_replacements(self):
        bad = self.commit(
            f"unpublished false stamp\n\nMeasured-on: {SOURCE}@{'1' * 40}",
            "fn false_stamp() {}\n",
        )
        self.git("update-ref", "refs/remotes/origin/main", bad)
        self.git("update-ref", "refs/remotes/elsewhere/main", bad)
        self.git("replace", bad, self.base)
        for old in [self.base, ZERO]:
            result = self.check(old)
            self.assertEqual(result.returncode, 1, result.stdout)
            self.assertIn("FAIL (R1)", result.stdout)
            self.assertIn(bad, result.stdout)

    def test_new_branch_cannot_hide_a_later_updated_branch(self):
        good = self.git("rev-parse", "HEAD")
        bad = self.commit("new unstamped claim\n\n7 passed, 0 failed", "fn later() {}\n")
        rows = (
            f"refs/heads/new {good} refs/heads/new {ZERO}\n"
            f"refs/heads/topic {bad} refs/heads/topic {self.base}\n"
        )
        result = subprocess.run(
            ["bash", str(CHECKER), "--pre-push", "--remote", str(self.remote)],
            cwd=self.repo, env=self.env, input=rows, text=True,
            stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=30,
        )
        self.assertEqual(result.returncode, 1, result.stdout)
        self.assertIn(bad, result.stdout)

    def test_atomic_push_with_lying_stamp_preserves_both_remote_refs(self):
        good = self.git("rev-parse", "HEAD")
        self.git("branch", "new", good)
        bad = self.commit(
            f"unpublished false stamp\n\nMeasured-on: {SOURCE}@{'1' * 40}",
            "fn false_stamp() {}\n",
        )
        # Run the real pre-push protocol, including the destination Git passes.
        # No product hook is installed or replaced by this temporary fixture.
        hook = self.repo / ".git/hooks/pre-push"
        hook.write_text(f'#!/bin/sh\nexec bash "{CHECKER}" --pre-push --remote "$2"\n')
        hook.chmod(0o700)
        before = self.git("ls-remote", "--refs", "origin")
        result = subprocess.run(
            ["git", "push", "--atomic", "origin", "new", "topic"],
            cwd=self.repo, env=self.env, text=True, stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT, timeout=30,
        )
        self.assertNotEqual(result.returncode, 0, result.stdout)
        self.assertIn("FAIL (R1)", result.stdout)
        self.assertIn(bad, result.stdout)
        self.assertEqual(self.git("ls-remote", "--refs", "origin"), before)

    def test_wrong_or_unavailable_destination_cannot_excuse_history(self):
        other = self.root / "other.git"
        self.run_command(["git", "init", "--bare", "--quiet", str(other)])
        self.remote = other
        result = self.check()
        self.assertEqual(result.returncode, 1, result.stdout)
        self.assertIn(self.published, result.stdout)
        self.remote = self.root / "missing.git"
        result = self.check()
        self.assertEqual(result.returncode, 2, result.stdout)

    def test_empty_destination_exclusions_preserve_clean_and_failing_ranges(self):
        self.remote = self.root / "empty.git"
        self.run_command(["git", "init", "--bare", "--quiet", str(self.remote)])
        # No advertised refs means no negative revisions, not one empty
        # revision argument (or an unset-array failure under Bash 3.2 -u).
        clean = self.check(old=self.published)
        self.assertEqual(clean.returncode, 0, clean.stdout)
        for old in [self.base, ZERO]:
            with self.subTest(old=old):
                failing = self.check(old=old)
                self.assertEqual(failing.returncode, 1, failing.stdout)
                self.assertIn("FAIL (R2)", failing.stdout)
                self.assertIn(self.published, failing.stdout)

    def test_push_context_carries_the_actual_destination(self):
        result = self.check(mode="--push-context")
        self.assertEqual(result.returncode, 0, result.stdout)
        self.assertIn("commits introduced to the push destination", result.stdout)

    def test_new_truthfully_stamped_claim_is_accepted(self):
        content = "fn measured() {}\n"
        (self.repo / SOURCE).write_text(content)
        blob = self.git("hash-object", SOURCE)
        self.commit(
            f"new measured claim\n\n7 passed, 0 failed\n\nMeasured-on: {SOURCE}@{blob}",
            content,
        )
        for old in [self.base, ZERO]:
            result = self.check(old)
            self.assertEqual(result.returncode, 0, result.stdout)

    def test_deletion_and_empty_push_do_not_need_remote_access(self):
        args = ["bash", str(CHECKER), "--pre-push", "--remote", str(self.root / "missing.git")]
        for rows in ["", f"(delete) {ZERO} refs/heads/topic {self.base}\n"]:
            result = subprocess.run(
                args, cwd=self.repo, env=self.env, input=rows, text=True,
                stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=30,
            )
            self.assertEqual(result.returncode, 0, result.stdout)


class AnchoredWaiverTests(unittest.TestCase):
    """Case R of docs/issues/2026-09-28-push-lanes-judge-the-checkout-not-the-push.md.

    Under push context the grandfather rows that apply are
    rows(anchor) & rows(pushed tip), the anchor being a tree the push cannot
    author. An uncommitted row, and a row committed in the same push, waive
    nothing. Each refusal arm has a standing-reading control showing the row is
    exactly the one the checkout's ledger would have honoured.
    """

    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.repo = self.root / "repo"
        self.remote = self.root / "remote.git"
        self.env = {
            key: value for key, value in os.environ.items()
            if not key.startswith(("GIT_", "TRUST_PUSH"))
        }
        self.env.update(GIT_CONFIG_NOSYSTEM="1", GIT_CONFIG_GLOBAL=os.devnull)
        self.run_command(["git", "init", "--bare", "--quiet", "--initial-branch=main", str(self.remote)])
        self.run_command(["git", "init", "--quiet", "--initial-branch=main", str(self.repo)])
        self.git("config", "user.name", "test")
        self.git("config", "user.email", "test@example.invalid")
        self.git("config", "commit.gpgsign", "false")
        (self.repo / SOURCE).parent.mkdir(parents=True)
        (self.repo / LEDGER).parent.mkdir(parents=True)
        self.base = self.commit("base", {SOURCE: "fn base() {}\n"})
        self.git("push", "--quiet", str(self.remote), "main")
        # The offender, on a side branch (main stays at base): a soundness-gate
        # commit that quotes a count and names no tree.
        self.git("checkout", "--quiet", "-b", "side")
        self.bad = self.commit("tighten the gate\n\n7 passed, 0 failed", {SOURCE: "fn bad() {}\n"})

    def run_command(self, argv, **kwargs):
        return subprocess.run(
            argv, env=self.env, text=True, stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT, check=True, timeout=30, **kwargs,
        ).stdout.strip()

    def git(self, *args):
        return self.run_command(["git", "-C", str(self.repo), *args])

    def commit(self, message, files):
        for path, text in files.items():
            (self.repo / path).parent.mkdir(parents=True, exist_ok=True)
            (self.repo / path).write_text(text)
            self.git("add", "--", path)
        self.run_command(
            ["git", "-C", str(self.repo), "commit", "--quiet", "--allow-empty", "--file=-"],
            input=message + "\n",
        )
        return self.git("rev-parse", "HEAD")

    @staticmethod
    def ledger(*shas):
        return "# fixture ledger\n" + "".join(sha + "\n" for sha in shas)

    def push_context(self, rows, destination=True):
        env = dict(self.env, TRUST_PUSHED_REFS=rows)
        if destination:
            env["TRUST_PUSH_REMOTE"] = str(self.remote)
        return subprocess.run(
            ["bash", str(CHECKER), "--push-context"], cwd=self.repo, env=env, text=True,
            stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=30,
        )

    def standing(self, rows):
        """The reading with no push context: --pre-push on stdin, the checkout's ledger."""
        return subprocess.run(
            ["bash", str(CHECKER), "--pre-push", "--remote", str(self.remote)], cwd=self.repo,
            env=self.env, input=rows, text=True,
            stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=30,
        )

    def assertRefused(self, result, sha):
        self.assertEqual(result.returncode, 1, result.stdout)
        self.assertIn("FAIL (R2)", result.stdout)
        self.assertIn(sha, result.stdout)

    def test_uncommitted_row_does_not_waive_the_pushed_claim(self):
        # R (1a): the row exists only in the checkout.
        (self.repo / LEDGER).write_text(self.ledger(self.bad))
        rows = f"refs/heads/main {self.bad} refs/heads/main {self.base}\n"
        control = self.standing(rows)
        self.assertEqual(control.returncode, 0, control.stdout)
        result = self.push_context(rows)
        self.assertRefused(result, self.bad)
        self.assertIn("0 grandfather row(s) apply", result.stdout)

    def test_row_committed_in_the_same_push_does_not_waive(self):
        # R (1b): the normal "push my branch" case, the row committed on HEAD.
        tip = self.commit("grandfather it", {LEDGER: self.ledger(self.bad)})
        rows = f"refs/heads/main {tip} refs/heads/main {self.base}\n"
        control = self.standing(rows)
        self.assertEqual(control.returncode, 0, control.stdout)
        self.assertRefused(self.push_context(rows), self.bad)
        # The SWAP form: the anchor already carries N rows and the push trades
        # one of them for the new sha, so a row count cannot see it.
        other = "1" * 40
        self.git("checkout", "--quiet", "main")
        anchor = self.commit("five rows", {LEDGER: self.ledger(other, "2" * 40, "3" * 40, "4" * 40, "5" * 40)})
        self.git("push", "--quiet", str(self.remote), "main")
        self.git("merge", "--quiet", "--no-edit", self.bad)
        swap = self.commit("swap", {LEDGER: self.ledger(self.bad, "2" * 40, "3" * 40, "4" * 40, "5" * 40)})
        swapped = f"refs/heads/main {swap} refs/heads/main {anchor}\n"
        self.assertEqual(self.standing(swapped).returncode, 0)
        self.assertRefused(self.push_context(swapped), self.bad)

    def test_row_at_the_anchor_and_the_tip_waives(self):
        # The legitimate shape: the destination's tip already grandfathers a
        # commit that sits on a side branch, and the push merges that branch.
        side = self.bad
        self.git("checkout", "--quiet", "main")
        anchor = self.commit("grandfather the side branch", {LEDGER: self.ledger(side)})
        self.git("push", "--quiet", str(self.remote), "main")
        self.git("merge", "--quiet", "--no-edit", side)
        merged = self.git("rev-parse", "HEAD")
        result = self.push_context(f"refs/heads/main {merged} refs/heads/main {anchor}\n")
        self.assertEqual(result.returncode, 0, result.stdout)
        self.assertIn("1 grandfathered", result.stdout)
        # A NEW ref is anchored at the merge-base with the destination's main.
        result = self.push_context(f"refs/heads/topic {merged} refs/heads/topic {ZERO}\n")
        self.assertEqual(result.returncode, 0, result.stdout)
        self.assertIn("merge-base with the destination's main", result.stdout)
        # The tip dropping the row: the intersection waives nothing.
        dropped = self.commit("retire the row", {LEDGER: self.ledger()})
        self.assertRefused(self.push_context(f"refs/heads/main {dropped} refs/heads/main {anchor}\n"), side)

    def test_new_ref_anchor_is_the_merge_base_not_the_tip(self):
        tip = self.commit("grandfather it", {LEDGER: self.ledger(self.bad)})
        rows = f"refs/heads/topic {tip} refs/heads/topic {ZERO}\n"
        self.assertEqual(self.standing(rows).returncode, 0)
        result = self.push_context(rows)
        self.assertRefused(result, self.bad)
        self.assertIn(f"anchor {self.base[:12]}", result.stdout)

    def test_no_anchor_means_no_waiver(self):
        tip = self.commit("grandfather it", {LEDGER: self.ledger(self.bad)})
        rows = f"refs/heads/topic {tip} refs/heads/topic {ZERO}\n"
        result = self.push_context(rows, destination=False)
        self.assertRefused(result, self.bad)
        self.assertIn("NO ANCHOR", result.stdout)
        # A destination that advertises no main anchors nothing either.
        self.remote = self.root / "empty.git"
        self.run_command(["git", "init", "--bare", "--quiet", str(self.remote)])
        self.assertEqual(self.standing(rows).returncode, 0)
        result = self.push_context(rows)
        self.assertRefused(result, self.bad)
        self.assertIn("advertises no main", result.stdout)

    def test_one_unanchored_ref_empties_the_waiver_set(self):
        side = self.bad
        self.git("checkout", "--quiet", "main")
        anchor = self.commit("grandfather the side branch", {LEDGER: self.ledger(side)})
        self.git("push", "--quiet", str(self.remote), "main")
        self.git("merge", "--quiet", "--no-edit", side)
        merged = self.git("rev-parse", "HEAD")
        self.git("checkout", "--quiet", "--orphan", "island")
        self.git("rm", "-rq", "--cached", ".")
        orphan = self.commit("unrelated history", {"island.txt": "island\n"})
        rows = (
            f"refs/heads/main {merged} refs/heads/main {anchor}\n"
            f"refs/heads/island {orphan} refs/heads/island {ZERO}\n"
        )
        result = self.push_context(rows)
        self.assertRefused(result, side)
        self.assertIn("no history in common", result.stdout)

    def test_malformed_pushed_ref_lines_are_refused_not_skipped(self):
        for rows in [
            "garbage\n",
            f"refs/heads/main {self.bad[:12]} refs/heads/main {self.base}\n",
            f"refs/heads/main {self.bad} refs/heads/main\n",
            f"refs/heads/main {self.bad} refs/heads/main {self.base} extra\n",
        ]:
            with self.subTest(rows=rows):
                result = self.push_context(rows)
                self.assertEqual(result.returncode, 2, result.stdout)
                self.assertIn("malformed pushed-ref line", result.stdout)

    def test_unterminated_last_line_is_judged(self):
        (self.repo / LEDGER).write_text(self.ledger(self.bad))
        result = subprocess.run(
            ["bash", str(CHECKER), "--pre-push", "--remote", str(self.remote)], cwd=self.repo,
            env=dict(self.env, TRUST_PUSHED_REFS=""), text=True,
            input=f"refs/heads/main {self.bad} refs/heads/main {self.base}",
            stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=30,
        )
        self.assertRefused(result, self.bad)

    def test_deletion_only_push_judges_nothing(self):
        result = self.push_context(f"(delete) {ZERO} refs/heads/gone {self.base}\n")
        self.assertEqual(result.returncode, 0, result.stdout)
        self.assertIn("nothing to judge", result.stdout)

    def test_waiver_anchors_mode_names_each_anchor(self):
        rows = (
            f"refs/heads/main {self.bad} refs/heads/main {self.base}\n"
            f"refs/heads/topic {self.bad} refs/heads/topic {ZERO}\n"
            f"(delete) {ZERO} refs/heads/gone {self.base}\n"
        )
        out = subprocess.run(
            ["bash", str(CHECKER), "--waiver-anchors", "--remote", str(self.remote)], cwd=self.repo,
            env=self.env, input=rows, text=True, stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT, timeout=30, check=True,
        ).stdout.splitlines()
        self.assertEqual(len(out), 2, out)
        self.assertTrue(out[0].startswith(f"ANCHOR {self.bad} {self.base} the destination's tip"), out)
        self.assertTrue(out[1].startswith(f"ANCHOR {self.bad} {self.base} merge-base"), out)
        out = subprocess.run(
            ["bash", str(CHECKER), "--waiver-anchors"], cwd=self.repo, env=self.env,
            input=f"refs/heads/topic {self.bad} refs/heads/topic {ZERO}\n", text=True,
            stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=30, check=True,
        ).stdout
        self.assertTrue(out.startswith(f"ANCHOR {self.bad} NONE NO ANCHOR"), out)


if __name__ == "__main__":
    unittest.main()
