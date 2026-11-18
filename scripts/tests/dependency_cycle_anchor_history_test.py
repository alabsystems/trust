#!/usr/bin/env python3
"""The real Trust history since v1 activation, judged by terminal-policy v3.

This method needs no fixture repositories, so it lives apart from
dependency_cycle_anchor_test's synthetic constellations: the land gate selects
this module whenever the trust-wp gitlink moves, at the cost of one history
walk (TRUSTWP-MERGE-MINT-ADMITTED in docs/DECISION_QUEUE.md). Like that
module, it stubs only the live ``ls-remote`` sample of trust-wp's canonical
main, with the submodule's remote-tracking ``origin/main``.
"""

from __future__ import annotations

import contextlib
import io
import unittest

from scripts.tests.dependency_cycle_anchor_test import REPO_ROOT, anchor, git, is_ancestor


class RealHistoryTests(unittest.TestCase):
    def test_real_origin_main_history_is_green_under_v3(self) -> None:
        """The real Trust history since v1 activation, judged by P1-P4 -- GREEN.

        ONLY the live ``ls-remote`` sample is stubbed: it is replaced by the
        trust-wp submodule's remote-tracking ``refs/remotes/origin/main``, the
        last fetched value of the very same ref.  Every marker, gitlink, lock
        blob and ancestry edge is read from this clone's real objects, and the
        constants are the ruling's own.  The moves the ledger records must
        each be admissible: ``f5599702`` (72274168 -> 04e6fffe, backward,
        same lock; on the canonical line, so clause (b)), its restoration,
        72274168 -> 9cbcc2cb (forward), and ``8325008ba62`` (9cbcc2cb ->
        684821d0, sideways onto main with the lock identical, clause (b)).
        """
        root_commit = git(REPO_ROOT, "rev-parse", "HEAD")
        self.assertEqual(
            git(REPO_ROOT, "cat-file", "-t", f"HEAD:{anchor.TERMINAL_POLICY_V3_MARKER_PATH}", check=False),
            "blob",
            "HEAD predates terminal-policy v3; this test judges the real history under v3",
        )
        wp = REPO_ROOT / anchor.SUBMODULES["trust-wp"][0]
        remote_main = git(wp, "rev-parse", "--verify", "refs/remotes/origin/main", check=False)
        self.assertRegex(
            remote_main, r"^[0-9a-f]{40}$",
            "first-party/trust-wp has no refs/remotes/origin/main; git -C first-party/trust-wp fetch origin main",
        )
        submodules = anchor.committed_submodules(REPO_ROOT, root_commit)
        commits = {name: commit for name, (_path, _url, commit) in submodules.items()}

        # The recorded shapes are really there.
        def wp_at(commit: str) -> str:
            return git(REPO_ROOT, "rev-parse", f"{commit}:{anchor.WP_ROOT_DELTA_PATH}")

        backward, restore, forward, sideways = (
            "f559970230e624c939f79eaa90685b0e50540e5b",
            "6ad0c5e76f76b47b22492ee68f7270526d3b8ada",
            "bfb7b5089a2faa87155df4fa807db7c82b0fda35",
            "8325008ba623c1ab3443eddd2c2ed99b2562da43",
        )
        a72, a04, a9c, a68 = (
            "72274168a37f133259f843941ef5f7d7615df67b",
            "04e6fffe64d93ba474f077ad7ba2be1341f3b00d",
            "9cbcc2cb47be6f7efd2ac110e3d5f3a4f259e1ff",
            "684821d0f2e2a31d640a0bdc9ab24977c539b1b7",
        )
        # These TrustWP commits are held by trust-wp's refs/pins/* anchors, which
        # neither a submodule update nor a default fetch brings. The judgement
        # below fetches what it reads, by sha (PUSH-PATH-CLONE-STATE); fetch the
        # same way before the recorded shapes are read here, or a clone without
        # the pins reads a missing object as "not an ancestor".
        recorded = (a72, a04, a9c, a68, anchor.TRUST_WP_PRESERVATION_FLOOR)
        _absent, detail = anchor.fetch_absent_trust_wp_objects(wp, recorded)
        self.assertEqual(anchor.absent_commits(wp, recorded), [], detail)
        for root_edge in (backward, restore, forward, sideways):
            self.assertTrue(is_ancestor(REPO_ROOT, root_edge, root_commit), root_edge)
        self.assertEqual((wp_at(f"{backward}^"), wp_at(backward)), (a72, a04))
        self.assertEqual((wp_at(f"{restore}^"), wp_at(restore)), (a04, a72))
        self.assertEqual((wp_at(f"{forward}^"), wp_at(forward)), (a72, a9c))
        self.assertEqual((wp_at(f"{sideways}^"), wp_at(sideways)), (a9c, a68))
        self.assertTrue(is_ancestor(wp, a04, a72))
        self.assertTrue(is_ancestor(wp, a72, a9c))
        self.assertFalse(is_ancestor(wp, a9c, a68), "8325008ba62 really is sideways")
        self.assertTrue(is_ancestor(wp, a68, remote_main))
        self.assertTrue(is_ancestor(wp, anchor.TRUST_WP_PRESERVATION_FLOOR, remote_main))
        locks = {commit: git(wp, "rev-parse", f"{commit}:{anchor.WP_DEPENDS_PATH}") for commit in (a72, a04, a9c, a68)}
        self.assertEqual(len(set(locks.values())), 1, locks)

        # TRUSTWP-MERGE-MINT-ADMITTED: each admitted merge is on main, binds
        # exactly what the admission names, has two parents whose bindings
        # differ from it, and its binding contains both of theirs and is on
        # trust-wp main.
        admitted_parent_wps = {
            "543a69d86babc39175a31b6d8337695f4b6fce48": (
                "10de7f0761cc674e6da7fb3dc2ecaa4a7c9d0931",
                "7e99ce0608cf4cab501cdfa22a69475d1f15fcea",
            ),
            "7385559b83501afe7ce0e4a2e0f21725e6791b5b": (
                "a33beda7f7b2bfb607bd6760dde2920212d393d5",
                "0717e843a0ad08b9d0e33e9db5420271bcf888bd",
            ),
            "6e82620248f35f01c5c01b7e59155a17270b5380": (
                "d7b1fb8d095ef367c83d2c0c3a8602a7fae18d24",
                "d78898c03098b2323c51205237b27b0662d4ac23",
            ),
        }
        self.assertEqual(set(admitted_parent_wps), set(anchor.TRUST_WP_ADMITTED_MERGE_MINTS))
        admitted_wps = [
            wp_sha
            for merge, minted in anchor.TRUST_WP_ADMITTED_MERGE_MINTS.items()
            for wp_sha in (minted, *admitted_parent_wps[merge])
        ]
        _absent, detail = anchor.fetch_absent_trust_wp_objects(wp, admitted_wps)
        self.assertEqual(anchor.absent_commits(wp, admitted_wps), [], detail)
        for merge, minted in anchor.TRUST_WP_ADMITTED_MERGE_MINTS.items():
            with self.subTest(admitted=merge):
                self.assertTrue(is_ancestor(REPO_ROOT, merge, root_commit), merge)
                self.assertEqual(wp_at(merge), minted)
                parents = git(REPO_ROOT, "log", "-1", "--format=%P", merge).split()
                self.assertEqual(tuple(wp_at(parent) for parent in parents), admitted_parent_wps[merge])
                for parent_wp in admitted_parent_wps[merge]:
                    self.assertNotEqual(parent_wp, minted)
                    self.assertTrue(is_ancestor(wp, parent_wp, minted), parent_wp)
                self.assertTrue(is_ancestor(wp, minted, remote_main), minted)

        # The two v1-era landings that once refused every push are still in
        # the judged DAG and are still accepted by the marked-subgraph walk.
        propagation = "3c2c11e530bb5e0253f8a412f4a0892528915091"
        landing = "e42bba0a61bbd72d97ebf9e27205bb0c58febb15"
        for commit in (propagation, landing):
            self.assertTrue(is_ancestor(REPO_ROOT, commit, root_commit), commit)

        # MAIN-REDS-1: the ``-s ours`` merge that keeps a July stash reachable.
        # Its index commit stages TrustWP eb18c757 back over its only parent's
        # 5443d384, a binding that parent's own pre-activation ancestry had
        # published at e5877167 (CONSTELLATION-RESTORE), so the inactive
        # lineage mints nothing and is accepted.
        stash_merge, stash, stash_index, stash_parent, first_publisher = (
            "1fedcff19d84ce1300047639ef40d56b878f6a5c",
            "50181df41833089a8f3c5d5e9f5a03c86de96951",
            "1b0fe79fc1ba9d3b14849bf132fdb267b35b1009",
            "38cb00023f7919397252374dc679597cc092de19",
            "e58771678ea1d25530f4755ad5e4232f67d0055a",
        )
        aeb, a54 = (
            "eb18c75702a8b60a411947296557c1405551ec1d",
            "5443d38463d267fdbd1d151e39c7fc091f1076f7",
        )
        self.assertTrue(is_ancestor(REPO_ROOT, stash_merge, root_commit))
        self.assertEqual(git(REPO_ROOT, "rev-parse", f"{stash_merge}^2"), stash)
        self.assertEqual(git(REPO_ROOT, "rev-parse", f"{stash}^2"), stash_index)
        self.assertEqual(git(REPO_ROOT, "rev-parse", f"{stash_index}^@"), stash_parent)
        self.assertEqual((wp_at(stash_parent), wp_at(stash_index)), (a54, aeb))
        self.assertEqual((wp_at(f"{first_publisher}^") != aeb, wp_at(first_publisher)), (True, aeb))
        self.assertTrue(is_ancestor(REPO_ROOT, first_publisher, stash_parent))

        # CONSTELLATION-UNBOUND-ROOT: the preservation merge 3ca41eb1a3 keeps
        # `git stash -u` commits reachable. Each stash's untracked-files parent
        # is parentless with no first-party/ tree, so it carries no binding.
        preservation, stash_u, untracked = (
            "3ca41eb1a339698a4777725f1b7cdad229771eb0",
            "32aa3e22ce659518a66c6c352c3e2283d4710aa0",
            "68cf95644cd6aab907c68bd469a71b65bc551872",
        )
        self.assertTrue(is_ancestor(REPO_ROOT, preservation, root_commit))
        self.assertIn(stash_u, git(REPO_ROOT, "rev-parse", f"{preservation}^@").split())
        self.assertEqual(git(REPO_ROOT, "rev-parse", f"{stash_u}^3"), untracked)
        self.assertEqual(git(REPO_ROOT, "rev-parse", f"{untracked}^@"), "")
        self.assertEqual(git(REPO_ROOT, "ls-tree", untracked, "first-party"), "")

        stderr = io.StringIO()
        with contextlib.redirect_stderr(stderr):
            verdict = anchor.validate_trust_wp_policy(REPO_ROOT, root_commit, commits, remote_main)
        self.assertTrue(is_ancestor(REPO_ROOT, first_publisher, f"{verdict['activation_commit']}^"))
        self.assertFalse(is_ancestor(REPO_ROOT, stash_merge, f"{verdict['activation_commit']}"))
        self.assertEqual(verdict["wp_remote_main"], remote_main)
        self.assertGreaterEqual(int(str(verdict["moves"])), 9)
        pins = anchor.validate_trust_wp_binding_coherence(REPO_ROOT, root_commit, commits)
        self.assertEqual(set(pins), anchor.WP_DEPENDS_REPOSITORIES)
        for repository, row in pins.items():
            checkout = REPO_ROOT if repository == "trust" else REPO_ROOT / anchor.SUBMODULES[repository][0]
            terminal = root_commit if repository == "trust" else commits[repository]
            self.assertTrue(is_ancestor(checkout, row, terminal), (repository, row))


if __name__ == "__main__":
    unittest.main()
