#!/usr/bin/env python3
"""Authenticated transport controls with actual Git object/ancestry decisions.

Only Agh's service boundary is replaced by a local repository. Production
profile selection, fresh collection, exact native reply binding, commit reader
and landing-main selector run here. Native Agh separately qualifies raw commit
intake, original parent traversal and the absence of tree/blob acquisition.
"""
from __future__ import annotations

import importlib.util
import json
import py_compile
import random
import signal
import subprocess
import sys
import tempfile
import threading
import types
import unittest
from pathlib import Path
from unittest.mock import patch

SCRIPTS = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(SCRIPTS))
sys.path.insert(0, str(SCRIPTS / "lib"))
import remote_tips as rt

spec = importlib.util.spec_from_file_location("agh_test_land_gate", SCRIPTS / "land_gate.py")
gate = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = gate
spec.loader.exec_module(gate)


class AghMetadataTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.donor = self.root / "donor"
        self.git("init", "-q", "-b", "main", str(self.donor))
        self.git("-C", str(self.donor), "config", "user.name", "Test")
        self.git("-C", str(self.donor), "config", "user.email", "test@example.invalid")
        self.revs = []
        for n in range(4):
            (self.donor / "source").write_text(str(n))
            self.git("-C", str(self.donor), "add", "source")
            self.git("-C", str(self.donor), "commit", "-qm", str(n))
            self.revs.append(self.git("-C", str(self.donor), "rev-parse", "HEAD"))
        self.pin, self.tip = self.revs[0], self.revs[-1]
        self.git("-C", str(self.donor), "switch", "-qc", "fork", self.pin)
        (self.donor / "source").write_text("fork")
        self.git("-C", str(self.donor), "commit", "-qam", "fork")
        self.fork = self.git("-C", str(self.donor), "rev-parse", "HEAD")
        self.store = self.root / "selected"
        self.git("init", "-q", "-b", "main", str(self.store))
        self.url = "https://github.com/Owner/Repo.git"
        self.git("-C", str(self.store), "remote", "add", "origin", self.url)
        self.refs = {"refs/heads/main": self.tip}
        self.provide_inventory_objects()
        self.api_exit = 0
        self.route = {"decision": {"send": {"profile": "fixture-profile"}}}
        self.calls = []
        self.native_requests = []
        self.actual_run = rt._run
        self.transport = patch.object(rt, "_run", side_effect=self.service)
        self.transport.start()
        self.addCleanup(self.transport.stop)
        # A transient failure is retried; these fixtures need not wait for it.
        pauses = patch.object(rt, "TRANSIENT_RETRY_DELAYS_S", (0.0, 0.0))
        pauses.start()
        self.addCleanup(pauses.stop)
        # The landing process intentionally has its own freshly compiled
        # namespace; use the same service boundary for these fixture calls.
        selected = patch.object(gate, "remote_tips", rt)
        selected.start()
        self.addCleanup(selected.stop)

    def git(self, *args):
        return subprocess.check_output(["git", *args], cwd=self.root, text=True, stderr=subprocess.DEVNULL).strip()

    def provide_inventory_objects(self):
        # Supply only original advertised object bodies, never their parents,
        # trees or refs. The existing incomplete-parent/native ancestry controls
        # therefore remain independent of this new object-type observation.
        for oid in set(self.refs.values()):
            body = subprocess.check_output(["git", "-C", str(self.donor), "cat-file", "commit", oid])
            actual = subprocess.check_output(["git", "-C", str(self.store), "hash-object", "-w", "-t", "commit", "--stdin"], input=body).decode().strip()
            self.assertEqual(actual, oid)

    def service(self, args, **kwargs):
        self.calls.append(list(args))
        if args[0] != "agh":
            self.assertFalse(any("github.com" in a for a in args), args)
            return self.actual_run(args, **kwargs)
        if args[1] == "whoami":
            return subprocess.CompletedProcess(args, 0, json.dumps(self.route), "")
        self.assertIn("--no-anonymous-api", args)
        self.assertNotIn("--anonymous", args)
        self.assertNotEqual(args[1], "api", "ref advertisements must not consume REST quota")
        if args[1:3] == ["repo", "refs"]:
            self.assertNotIn("--as", args)
            self.assertEqual(args[3], rt.github_repository(self.url))
            rows = [{"ref": ref, "oid": oid} for ref, oid in self.refs.items()]
            return subprocess.CompletedProcess(args, self.api_exit, json.dumps(rows), "collection unavailable")
        self.assertEqual(args[1:3], ["repo", "commit-ancestry"])
        self.assertNotIn("--as", args, "native repository reads own their routed credentials")
        destination = args[4]
        request = json.loads(Path(args[args.index("--input") + 1]).read_text())
        self.native_requests.append(request)
        # Agh's CommitRead::new refuses more than 128 queries in one request.
        self.assertLessEqual(len(request["queries"]), 128)
        self.assertLessEqual(len(request["queries"]), rt.ANCESTRY_BATCH)
        wanted = list(request["commits"])
        for query in request["queries"]:
            wanted.extend([query["ancestor"], query["descendant"]])
        # Match the native commit-only service: exact original commit bodies,
        # never ordinary fetch negotiation through a possibly shallow or
        # incomplete borrowed object graph. Native tests independently qualify
        # authenticated acquisition and the bounded transfer itself.
        for sha in dict.fromkeys(wanted):
            kind = subprocess.run(["git", "-C", str(self.donor), "cat-file", "-t", sha],
                                  capture_output=True, text=True)
            if kind.returncode or kind.stdout.strip() != "commit":
                return subprocess.CompletedProcess(args, 6, "", "native commit-only read refuses non-commit")
            result = subprocess.run(["git", "-C", str(self.donor), "cat-file", "commit", sha],
                                    capture_output=True)
            if result.returncode:
                return subprocess.CompletedProcess(args, 6, "", "not our ref")
            written = subprocess.check_output(["git", "--git-dir", destination,
                                               "hash-object", "-w", "-t", "commit", "--stdin"],
                                              input=result.stdout).decode().strip()
            self.assertEqual(written, sha)
        queries = []
        with tempfile.TemporaryDirectory(dir=self.root) as temporary:
            view = Path(temporary) / "view.git"
            self.git("init", "--quiet", "--bare", str(view))
            common = self.git("--git-dir", destination, "rev-parse", "--git-common-dir")
            (view / "objects/info/alternates").write_text(str(Path(common).resolve() / "objects") + "\n"
                                                        + str(self.donor / ".git/objects") + "\n")
            for query in request["queries"]:
                actual = self.actual_run(["git", "--git-dir", str(view), "-c", "core.commitGraph=false",
                                          "merge-base", "--is-ancestor", query["ancestor"], query["descendant"]])
                if actual.returncode not in (0, 1):
                    return subprocess.CompletedProcess(args, 3, "", "native ancestry unavailable")
                queries.append(dict(query, contained=actual.returncode == 0))
        return subprocess.CompletedProcess(args, 0, json.dumps({"schema": 1,
            "scope": "commit-parent-ancestry-only-v1", "commits": request["commits"], "queries": queries,
            "refs_written": False, "checkout_complete": False, "acquired_commits": 0, "api_body_bytes": 0}), "")

    def state(self):
        refs = self.git("-C", str(self.store), "for-each-ref", "--format=%(objectname) %(refname)")
        fetch_head = self.store / ".git/FETCH_HEAD"
        return refs, fetch_head.read_bytes() if fetch_head.exists() else None

    def test_authenticated_acquisition_ignores_stale_refs_and_writes_no_destination_ref(self):
        before = self.state()
        tips = rt.RemoteTips()
        self.assertEqual(tips.judge(self.store, self.pin, scope="main").state, rt.CONTAINED)
        self.git("-C", str(self.store), "update-ref", "refs/remotes/origin/main", self.pin)
        stale = self.state()
        self.assertEqual(tips.judge(self.store, self.fork, scope="main").state, rt.NOT_CONTAINED)
        self.assertEqual(self.state(), stale)
        self.assertEqual(before, ("", None))
        self.assertEqual(tips.ls_remote_calls, 1)
        self.assertEqual(sum(c[0:3] == ["agh", "repo", "refs"] for c in self.calls), 1)
        self.assertFalse(any(c[0:2] == ["agh", "api"] for c in self.calls))

    def test_complete_warm_store_uses_native_exact_query_without_temporary_refs(self):
        # Actual local objects are hints, while the fresh remote tip and exact
        # native query remain authoritative. This is caller custody, not a
        # measurement of the service stand-in's transfer behavior.
        self.git("-C", str(self.donor), "switch", "-q", "main")
        payload = random.Random(1729)
        for n in range(12):
            (self.donor / "payload").write_bytes(payload.randbytes(32768))
            self.git("-C", str(self.donor), "add", "payload")
            self.git("-C", str(self.donor), "commit", "-qm", f"warm-{n}")
        base = self.git("-C", str(self.donor), "rev-parse", "HEAD")
        self.git("-C", str(self.store), "fetch", "-q", str(self.donor), base)
        self.git("-C", str(self.store), "switch", "-q", "--detach", base)
        (self.donor / "payload").write_bytes(payload.randbytes(32768))
        self.git("-C", str(self.donor), "commit", "-qam", "unfetched-middle")
        (self.donor / "payload").write_bytes(payload.randbytes(32768))
        self.git("-C", str(self.donor), "commit", "-qam", "new-tip")
        tip = self.git("-C", str(self.donor), "rev-parse", "HEAD")
        self.refs = {"refs/heads/main": tip}
        self.provide_inventory_objects()
        # Only the advertised tip body is present; the intermediate original
        # parent is absent, so the exact ancestry query still needs native Agh.
        self.assertEqual(rt.RemoteTips.present(self.store / ".git", [tip]), {tip})
        before = self.state()
        config = (self.store / ".git/config").read_bytes()
        requests = []
        original = self.service

        def warm_service(args, **kwargs):
            if args[:3] == ["agh", "repo", "commit-ancestry"]:
                view = Path(args[4])
                self.assertNotEqual(view.resolve(), (self.store / ".git").resolve())
                self.assertEqual(rt.RemoteTips.present(view, [base]), {base})
                self.assertEqual(kwargs.get("cwd"), view.parents[1])
                self.assertEqual(rt.RemoteTips.present(self.store / ".git", [base]), {base})
                requests.append(json.loads(Path(args[args.index("--input") + 1]).read_text()))
            self.assertNotEqual(args[:3], ["agh", "repo", "fetch"])
            return original(args, **kwargs)

        with patch.object(rt, "_run", side_effect=warm_service):
            tips = rt.RemoteTips()
            self.assertEqual(tips.judge(self.store, base, scope="main").state, rt.CONTAINED)
        self.assertEqual(tips.ls_remote_calls, 1)
        self.assertEqual(requests, [{"commits": [], "queries": [{"ancestor": base, "descendant": tip}]}])
        self.assertEqual(self.state(), before)
        self.assertEqual((self.store / ".git/config").read_bytes(), config)
        self.assertFalse((self.store / ".git/objects/info/alternates").exists())
        self.assertFalse((self.store / ".git/shallow").exists())

    def test_native_query_retains_acquired_intermediate_originals_without_reusing_authority(self):
        before = self.state()
        config = (self.store / ".git/config").read_bytes()
        acquired = []
        original = self.service

        def acquiring(args, **kwargs):
            cold = []
            if args[:3] == ["agh", "repo", "commit-ancestry"]:
                view = Path(args[4])
                held = rt.RemoteTips.present(view, self.revs[1:-1])
                for oid in self.revs[1:-1]:
                    if oid not in held:
                        body = subprocess.check_output(["git", "-C", str(self.donor), "cat-file", "commit", oid])
                        written = subprocess.check_output(["git", "--git-dir", str(view), "hash-object", "-w", "-t", "commit", "--stdin"], input=body).decode().strip()
                        self.assertEqual(written, oid)
                        cold.append(oid)
                acquired.append(cold)
            return original(args, **kwargs)

        with patch.object(rt, "_run", side_effect=acquiring):
            first = rt._native_commit_read("Owner/Repo", self.store / ".git", [], [(self.pin, self.tip)], timeout=20)
            self.assertEqual(first.returncode, 0, first.stderr)
            self.assertEqual(rt.RemoteTips.present(self.store / ".git", self.revs), set(self.revs))
            second = rt._native_commit_read("Owner/Repo", self.store / ".git", [], [(self.pin, self.tip)], timeout=20)
            self.assertEqual(second.returncode, 0, second.stderr)
        self.assertEqual(acquired, [self.revs[1:-1], []])
        self.assertEqual(sum(c[:3] == ["agh", "repo", "commit-ancestry"] for c in self.calls), 2)
        self.assertEqual(self.state(), before)
        self.assertEqual((self.store / ".git/config").read_bytes(), config)
        self.assertFalse((self.store / ".git/objects/info/alternates").exists())
        self.assertEqual(subprocess.run(["git", "-C", str(self.store), "cat-file", "-e", self.tip + "^{tree}"], capture_output=True).returncode, 128)

    def test_native_commit_data_cache_refuses_unexpected_noncommit_objects(self):
        original = self.service
        unexpected = []
        def extra_blob(args, **kwargs):
            if args[:3] == ["agh", "repo", "commit-ancestry"]:
                unexpected.append(subprocess.check_output(["git", "--git-dir", args[4], "hash-object", "-w", "--stdin"], input=b"not original commit metadata\n").decode().strip())
            return original(args, **kwargs)
        before = self.state()
        with patch.object(rt, "_run", side_effect=extra_blob):
            done = rt._native_commit_read("Owner/Repo", self.store / ".git", [], [(self.pin, self.tip)], timeout=20)
        self.assertNotEqual(done.returncode, 0)
        self.assertEqual(self.state(), before)
        self.assertEqual(subprocess.run(["git", "-C", str(self.store), "cat-file", "-e", unexpected[0]], capture_output=True).returncode, 1)

    def test_native_store_refusals_preserve_config_and_never_start_full_fetch(self):
        # Native store admission owns these decisions. A native refusal must
        # stay unjudged for every existing store shape, without replacing it.
        original = self.service
        for shape in ("shallow", "promisor", "alternate", "promisor-marker"):
            with self.subTest(shape=shape):
                self.store = self.root / shape
                if shape == "shallow":
                    self.git("clone", "-q", "--depth=1", "--branch=main", self.donor.as_uri(), str(self.store))
                    self.git("-C", str(self.store), "remote", "set-url", "origin", self.url)
                else:
                    self.git("init", "-q", "-b", "main", str(self.store))
                    self.git("-C", str(self.store), "remote", "add", "origin", self.url)
                    self.git("-C", str(self.store), "fetch", "-q", str(self.donor), self.pin)
                    self.git("-C", str(self.store), "switch", "-q", "--detach", self.pin)
                self.provide_inventory_objects()
                if shape == "promisor":
                    self.git("-C", str(self.store), "config", "remote.origin.promisor", "true")
                elif shape == "alternate":
                    alternate = self.root / "empty-alternate.git"
                    self.git("init", "-q", "--bare", str(alternate))
                    (self.store / ".git/objects/info/alternates").write_text(str(alternate / "objects") + "\n")
                elif shape == "promisor-marker":
                    (self.store / ".git/objects/pack/unbound.promisor").touch()
                before = self.state()
                config = (self.store / ".git/config").read_bytes()
                calls = []

                def refused(args, **kwargs):
                    if args[:3] == ["agh", "repo", "commit-ancestry"]:
                        calls.append(args)
                        return subprocess.CompletedProcess(args, 3, "", "native store admission refused")
                    self.assertNotEqual(args[:3], ["agh", "repo", "fetch"])
                    return original(args, **kwargs)

                with patch.object(rt, "_run", side_effect=refused):
                    self.assertEqual(rt.RemoteTips().judge(self.store, self.pin, scope="main").state, rt.UNJUDGED)
                self.assertTrue(calls)
                self.assertEqual(self.state(), before)
                self.assertEqual((self.store / ".git/config").read_bytes(), config)

    def test_local_objects_cannot_hide_malformed_or_wrong_native_query_reply(self):
        self.git("-C", str(self.store), "fetch", "-q", str(self.donor), self.pin)
        self.git("-C", str(self.store), "switch", "-q", "--detach", self.pin)
        before = self.state()
        original = self.service
        for defect in ("malformed", "wrong-query"):
            with self.subTest(defect=defect):
                def broken_service(args, **kwargs):
                    if args[:3] != ["agh", "repo", "commit-ancestry"]:
                        return original(args, **kwargs)
                    if defect == "malformed":
                        return subprocess.CompletedProcess(args, 0, "", "")
                    result = original(args, **kwargs)
                    reply = json.loads(result.stdout)
                    reply["queries"][0]["descendant"] = self.pin
                    return subprocess.CompletedProcess(args, 0, json.dumps(reply), "")

                with patch.object(rt, "_run", side_effect=broken_service):
                    self.assertEqual(rt.RemoteTips().judge(self.store, self.pin, scope="main").state, rt.UNJUDGED)
                self.assertEqual(self.state(), before)

    def test_only_master_is_not_main_but_can_prove_durable_containment(self):
        self.refs = {"refs/heads/master": self.tip}
        tips = rt.RemoteTips()
        self.assertEqual(tips.judge(self.store, self.pin, scope="main").state, rt.NO_MAIN)
        self.assertEqual(tips.judge(self.store, self.pin).state, rt.CONTAINED)

    def test_private_local_anchor_never_substitutes_for_remote_inventory(self):
        self.git("-C", str(self.store), "fetch", "-q", str(self.donor), self.fork)
        self.git("-C", str(self.store), "update-ref", "refs/pins/" + self.fork, self.fork)
        before = self.state()
        self.assertEqual(rt.RemoteTips().judge(self.store, self.fork).state, rt.NOT_CONTAINED)
        self.assertEqual(before, self.state())

    def test_remote_pin_is_still_authority(self):
        self.refs["refs/pins/" + self.fork] = self.fork
        self.provide_inventory_objects()
        self.assertEqual(rt.RemoteTips().judge(self.store, self.fork).state, rt.CONTAINED)

    def test_absent_is_not_an_infrastructure_failure(self):
        self.assertEqual(rt.RemoteTips().judge(self.store, "1" * 40).state, rt.ABSENT)

    def test_incomplete_authenticated_collection_is_unjudged_without_fallback(self):
        self.api_exit = 14
        self.assertEqual(rt.RemoteTips().judge(self.store, self.pin).state, rt.UNJUDGED)
        self.assertFalse(any(c[0:3] == ["agh", "repo", "commit-ancestry"] for c in self.calls))

    def test_no_authenticated_route_is_unjudged_without_anonymous_fallback(self):
        self.route = {"decision": {"send": {"anonymous": True}}}
        self.assertEqual(rt.RemoteTips().judge(self.store, self.pin).state, rt.UNJUDGED)
        self.assertFalse(any(c[0:2] == ["agh", "api"] for c in self.calls))

    def test_shallow_destination_must_recover_real_ancestry(self):
        self.git("clone", "-q", "--depth=1", "--branch=main", self.donor.as_uri(), str(self.root / "shallow"))
        self.store = self.root / "shallow"
        self.git("-C", str(self.store), "remote", "set-url", "origin", self.url)
        before = self.state()
        tips = rt.RemoteTips()
        self.assertEqual(tips.judge(self.store, self.pin, scope="main").state, rt.CONTAINED)
        self.assertEqual(tips.judge(self.store, self.fork, scope="main").state, rt.NOT_CONTAINED)
        self.assertEqual(self.state(), before)
        self.assertIs(tips._is_shallow(self.store / ".git"), True)

    def test_landing_main_uses_the_shared_authority_and_rejects_master(self):
        before = self.state()
        self.assertEqual(gate.remote_main_tip(self.store, dict(rt._env())), (self.url, self.tip))
        self.assertEqual(before, self.state())
        self.refs = {"refs/heads/master": self.tip}
        with self.assertRaises(gate.LandingUnjudged):
            gate.remote_main_tip(self.store, dict(rt._env()))

    def test_landing_literal_relative_remote_is_resolved_from_selected_root(self):
        self.git("-C", str(self.store), "remote", "set-url", "origin", "../donor")
        self.assertEqual(gate.remote_main_tip(self.store, dict(rt._env())), ("../donor", self.tip))

    def test_route_and_operation_share_one_deadline(self):
        with patch.object(rt.time, "monotonic", side_effect=[0, 90]):
            done = rt._agh("Owner/Repo", ["api", "/unused"], timeout=90)
        self.assertEqual(done.returncode, 124)
        self.assertFalse(any(c[0:2] == ["agh", "api"] for c in self.calls))

    def canonical_ancestry_store(self):
        self.url = "https://github.com/Owner/ty.git"
        self.git("-C", str(self.store), "remote", "set-url", "origin", self.url)
        canonical = self.root / "ty"
        self.git("clone", "-q", str(self.donor), str(canonical))
        self.git("-C", str(canonical), "remote", "set-url", "origin", self.url)
        return canonical

    def canonical_state(self, canonical):
        return (self.git("-C", str(canonical), "for-each-ref", "--format=%(refname) %(objectname)"),
                {name: (canonical / ".git" / name).read_bytes() if (canonical / ".git" / name).exists() else None
                 for name in ("HEAD", "config", "index", "FETCH_HEAD", "shallow")})

    def test_canonical_original_parents_feed_same_native_query_without_source_copy(self):
        canonical = self.canonical_ancestry_store()
        before, caller = self.canonical_state(canonical), self.state()
        middle = self.revs[1]
        self.assertEqual(rt.RemoteTips.present(self.store / ".git", [middle]), set())
        original, observed = self.service, []
        def held(args, **kwargs):
            if args[:3] == ["agh", "repo", "commit-ancestry"]:
                view = Path(args[4])
                self.assertEqual(rt.RemoteTips.present(view, [middle]), {middle})
                self.assertFalse((view / "shallow").exists())
                observed.append(json.loads(Path(args[args.index("--input") + 1]).read_text()))
            return original(args, **kwargs)
        with patch.object(rt.Path, "home", return_value=self.root), patch.object(rt, "_run", side_effect=held):
            verdict = rt.RemoteTips().judge(self.store, self.pin, scope="main")
        self.assertEqual(verdict.state, rt.CONTAINED, verdict.detail)
        self.assertTrue(any(row["queries"] == [{"ancestor": self.pin, "descendant": self.tip}] for row in observed))
        self.assertEqual(sum(c[:3] == ["agh", "repo", "refs"] for c in self.calls), 1)
        self.assertFalse(any(c[:2] == ["agh", "api"] for c in self.calls))
        self.assertEqual(rt.RemoteTips.present(self.store / ".git", [middle]), set())
        self.assertEqual(self.canonical_state(canonical), before)
        self.assertEqual(self.state(), caller)
        self.assertFalse((self.store / ".git/objects/info/alternates").exists())

    def test_canonical_complete_negative_still_comes_from_exact_native_reply(self):
        self.canonical_ancestry_store()
        with patch.object(rt.Path, "home", return_value=self.root):
            verdict = rt.RemoteTips().judge(self.store, self.fork, scope="main")
        self.assertEqual(verdict.state, rt.NOT_CONTAINED, verdict.detail)
        self.assertTrue(any(c[:3] == ["agh", "repo", "commit-ancestry"] for c in self.calls))

    def test_wrong_canonical_repository_preserves_actual_native_quota_refusal(self):
        canonical = self.canonical_ancestry_store()
        self.git("-C", str(canonical), "remote", "set-url", "origin", "https://github.com/Other/ty.git")
        original = self.service
        def refused(args, **kwargs):
            if args[:3] == ["agh", "repo", "commit-ancestry"]:
                view = Path(args[4])
                self.assertEqual(rt.RemoteTips.present(view, [self.revs[1]]), set())
                return subprocess.CompletedProcess(args, 11, "", "core remaining999 reserve1000 reset1794656062")
            return original(args, **kwargs)
        with patch.object(rt.Path, "home", return_value=self.root), patch.object(rt, "_run", side_effect=refused):
            verdict = rt.RemoteTips().judge(self.store, self.pin, scope="main")
        self.assertEqual(verdict.state, rt.UNJUDGED, verdict.detail)
        self.assertIn("reset1794656062", verdict.detail)

    def test_canonical_replacement_after_native_answer_cannot_supply_result(self):
        canonical = self.canonical_ancestry_store()
        original, replaced = self.service, []
        def changed(args, **kwargs):
            done = original(args, **kwargs)
            if args[:3] == ["agh", "repo", "commit-ancestry"] and not replaced:
                canonical.rename(self.root / "old-ty")
                canonical.mkdir()
                replaced.append(True)
            return done
        with patch.object(rt.Path, "home", return_value=self.root), patch.object(rt, "_run", side_effect=changed):
            done = rt._native_commit_read("Owner/ty", self.store / ".git", [],
                                          [(self.pin, self.tip)], timeout=30)
        self.assertNotEqual(done.returncode, 0)
        self.assertIn("canonical source directory changed", done.stderr)
        self.assertTrue(replaced)

    def test_canonical_odb_replacement_after_native_answer_cannot_supply_result(self):
        canonical = self.canonical_ancestry_store()
        original, replaced = self.service, []
        def changed(args, **kwargs):
            done = original(args, **kwargs)
            if args[:3] == ["agh", "repo", "commit-ancestry"] and not replaced:
                (canonical / ".git/objects").rename(canonical / ".git/old-objects")
                (canonical / ".git/objects").mkdir()
                replaced.append(True)
            return done
        with patch.object(rt.Path, "home", return_value=self.root), patch.object(rt, "_run", side_effect=changed):
            done = rt._native_commit_read("Owner/ty", self.store / ".git", [],
                                          [(self.pin, self.tip)], timeout=30)
        self.assertNotEqual(done.returncode, 0)
        self.assertIn("original object directory changed", done.stderr)
        self.assertTrue(replaced)

    def test_canonical_shallow_and_replace_metadata_never_enter_native_view(self):
        canonical = self.canonical_ancestry_store()
        self.git("-C", str(canonical), "replace", self.tip, self.pin)
        (canonical / ".git/shallow").write_text(self.tip + "\n")
        (canonical / ".git/info/grafts").write_text(self.tip + "\n")
        before = self.canonical_state(canonical)
        original = self.service
        def original_only(args, **kwargs):
            if args[:3] == ["agh", "repo", "commit-ancestry"]:
                view = Path(args[4])
                self.assertFalse((view / "shallow").exists())
                self.assertFalse((view / "info/grafts").exists())
                self.assertEqual(self.git("--git-dir", str(view), "for-each-ref", "refs/replace"), "")
                self.assertEqual(rt.RemoteTips.present(view, self.revs), set(self.revs))
            return original(args, **kwargs)
        with patch.object(rt.Path, "home", return_value=self.root), patch.object(rt, "_run", side_effect=original_only):
            verdict = rt.RemoteTips().judge(self.store, self.pin, scope="main")
        self.assertEqual(verdict.state, rt.CONTAINED, verdict.detail)
        self.assertEqual(self.canonical_state(canonical), before)

    def test_unknown_fetch_failure_stays_unjudged(self):
        original = self.service
        def failed(args, **kwargs):
            if args[:3] == ["agh", "repo", "commit-ancestry"]:
                return subprocess.CompletedProcess(args, 3, "", "network could not run")
            return original(args, **kwargs)
        with patch.object(rt, "_run", side_effect=failed):
            self.assertEqual(rt.RemoteTips().judge(self.store, self.pin).state, rt.UNJUDGED)

    def test_malformed_ref_collection_never_supplies_a_tip(self):
        for rows in ("{}", '[{"ref":"refs/heads/main","oid":"bad"}]',
                     json.dumps([{"ref":"refs/heads/main", "oid":self.tip}] * 2),
                     json.dumps([{"ref":"refs/heads/../main", "oid":self.tip}]),
                     json.dumps([{"ref":"HEAD", "oid":self.tip}])):
            with self.subTest(rows=rows), patch.object(rt, "_agh", return_value=subprocess.CompletedProcess([], 0, rows, "")):
                self.assertNotEqual(rt.remote_refs(self.url).returncode, 0)

    def test_native_advertisement_preserves_heads_and_pins_but_not_tags(self):
        self.refs = {"refs/heads/main": self.tip,
                     "refs/heads/master": self.pin, "refs/pins/kept": self.fork,
                     "refs/tags/release": self.pin, "refs/tags/release^{}": self.tip}
        result = rt.remote_refs(self.url, git_dir=self.store / ".git")
        self.assertEqual(result.returncode, 0)
        self.assertEqual(dict((ref, oid) for oid, ref in
                              (line.split() for line in result.stdout.splitlines())),
                         {name: oid for name, oid in self.refs.items()
                          if name.startswith(("refs/heads/", "refs/pins/"))})
        self.assertFalse(any(c[:2] == ["agh", "api"] for c in self.calls))

    def test_advertised_unknown_object_does_not_establish_containment(self):
        self.refs = {"refs/heads/main": "1" * 40}
        before = self.state()
        self.assertEqual(rt.RemoteTips().judge(self.store, self.pin).state, rt.UNJUDGED)
        self.assertEqual(self.state(), before)
        self.assertTrue(any(c[:3] == ["agh", "repo", "commit-ancestry"] for c in self.calls))

    def test_noncommit_durable_ref_is_not_peeled_into_a_commit(self):
        self.git("-C", str(self.donor), "tag", "-a", "release", self.tip, "-m", "tag object")
        tag = self.git("-C", str(self.donor), "rev-parse", "refs/tags/release")
        self.git("-C", str(self.store), "fetch", "-q", str(self.donor), tag)
        self.assertEqual(rt.RemoteTips.present(self.store / ".git", [tag]), set())
        self.refs = {"refs/heads/main": tag}
        self.assertEqual(rt.RemoteTips().judge(self.store, self.pin).state, rt.UNJUDGED)
        self.assertTrue(any(c[:3] == ["agh", "repo", "commit-ancestry"] for c in self.calls))

    def test_commit_presence_requires_complete_matching_object_body(self):
        self.git("-C", str(self.store), "fetch", "-q", str(self.donor), self.pin)
        self.assertEqual(rt.RemoteTips.present(self.store / ".git", [self.pin]), {self.pin})
        for output in (f"{self.pin} commit 99\ntruncated".encode(), f"{self.pin} commit 3\nbad\n".encode()):
            with patch.object(rt, "_run", return_value=subprocess.CompletedProcess([], 0, output, "")):
                self.assertEqual(rt.RemoteTips.present(self.store / ".git", [self.pin]), set())

    def test_commit_bodies_preserve_crlf_bare_cr_and_non_utf8_bytes(self):
        self.git("-C", str(self.store), "fetch", "-q", str(self.donor), self.pin)
        tree = self.git("-C", str(self.store), "rev-parse", self.pin + "^{tree}")
        body = (f"tree {tree}\nauthor Test <test@example.invalid> 1600000000 +0000\n"
                "committer Test <test@example.invalid> 1600000000 +0000\n\n").encode() + b"message\r\nraw\rbytes\xff\n"
        oid = subprocess.check_output(["git", "-C", str(self.store), "hash-object", "-w", "-t", "commit", "--stdin"],
                                      input=body).decode().strip()
        self.assertEqual(rt.RemoteTips.present(self.store / ".git", [oid]), {oid})

    def test_transport_grammar_and_environment_do_not_allow_network_fallback(self):
        for value in ("https://github.com.evil/O/R.git", "https://token@github.com/O/R", "https://github.com/O/R?token=x",
                      "ssh://git@github.com:2222/O/R", "git://github.com/O/R", "https://other.example/O/R"):
            with self.subTest(value=value), self.assertRaises(ValueError):
                rt.github_repository(value)
        self.assertEqual(rt.github_repository("git@github.com:Owner/Repo.git"), "Owner/Repo")
        self.assertEqual(rt.github_repository("ssh://git@github.com/Owner/Repo.git"), "Owner/Repo")
        env = rt._env({"GIT_DIR":"wrong", "GIT_CONFIG_COUNT":"1", "GIT_CONFIG_KEY_0":"url.evil.insteadOf",
                       "GIT_ALLOW_PROTOCOL":"https", "GIT_GRAFT_FILE":"forged"})
        self.assertEqual(env["GIT_ALLOW_PROTOCOL"], "file")
        self.assertNotIn("GIT_DIR", env)
        self.assertNotIn("GIT_CONFIG_KEY_0", env)

    def test_binary_reader_bounds_deadline_and_output_and_reaps_its_child(self):
        children = []
        actual_spawn = subprocess.Popen
        def spawn(*args, **kwargs):
            child = actual_spawn(*args, **kwargs)
            children.append(child)
            return child
        with patch.object(rt, "MAX_OBJECT_READ_BYTES", 4), patch.object(rt.subprocess, "Popen", side_effect=spawn):
            oversized = rt._run([sys.executable, "-c", "import sys;sys.stdout.buffer.write(b'12345')"],
                                binary=True, timeout=5)
        self.assertEqual(oversized.returncode, 2)
        self.assertEqual(oversized.stdout, b"")
        with patch.object(rt.subprocess, "Popen", side_effect=spawn):
            timed = rt._run([sys.executable, "-c", "import time;time.sleep(10)"], binary=True, timeout=0.05)
        self.assertEqual(timed.returncode, 124)
        self.assertEqual(timed.stdout, b"")
        self.assertEqual(len(children), 2)
        self.assertTrue(all(child.poll() is not None and child.stdout.closed for child in children))

    def test_reader_thread_start_failure_reaps_the_already_spawned_child(self):
        children = []
        actual_spawn = subprocess.Popen
        def spawn(*args, **kwargs):
            child = actual_spawn(*args, **kwargs)
            children.append(child)
            return child
        with patch.object(rt.subprocess, "Popen", side_effect=spawn), patch.object(rt.threading.Thread, "start", side_effect=RuntimeError("thread unavailable")):
            done = rt._run([sys.executable, "-c", "import time;time.sleep(10)"], binary=True, timeout=5)
        self.assertEqual(done.returncode, 2)
        self.assertEqual(len(children), 1)
        self.assertIsNotNone(children[0].poll())
        self.assertTrue(children[0].stdout.closed)

    def test_acquisition_validation_timeout_is_unjudged(self):
        original = self.service
        def exhausted(args, **kwargs):
            if args[:3] == ["agh", "repo", "commit-ancestry"]:
                self.assertGreater(kwargs["timeout"], 0)
                self.assertLessEqual(kwargs["timeout"], rt.FETCH_TIMEOUT_S)
                return subprocess.CompletedProcess(args, 124, "", "deadline exhausted")
            return original(args, **kwargs)
        with patch.object(rt, "_run", side_effect=exhausted):
            self.assertEqual(rt.RemoteTips().judge(self.store, self.pin).state, rt.UNJUDGED)

    def test_exhausted_acquisition_does_not_start_any_more_children(self):
        with patch.object(rt, "FETCH_TIMEOUT_S", -1):
            self.assertEqual(rt.RemoteTips().judge(self.store, self.pin).state, rt.UNJUDGED)
        self.assertFalse(any("init" in args and "trust-remote-tips-" in " ".join(args) for args in self.calls))

    def test_native_unavailable_never_retries_the_old_full_fetch_transport(self):
        original = self.service
        def unavailable(args, **kwargs):
            if args[:3] == ["agh", "repo", "commit-ancestry"]:
                self.calls.append(list(args))
                return subprocess.CompletedProcess(args, 2, "", "unknown native operation")
            return original(args, **kwargs)
        with patch.object(rt, "_run", side_effect=unavailable):
            self.assertEqual(rt.RemoteTips().judge(self.store, self.pin).state, rt.UNJUDGED)
        self.assertFalse(any(args[:3] == ["agh", "repo", "fetch"] for args in self.calls))
        self.assertFalse(any("trust-remote-tips-" in " ".join(args) for args in self.calls))

    def test_native_query_population_scope_and_exact_tip_binding_are_required(self):
        original = self.service
        for mutate in (lambda r: r.update(scope="checkout-complete"),
                       lambda r: r.update(schema=True),
                       lambda r: r.update(checkout_complete=True),
                       lambda r: r.update(queries=[]),
                       lambda r: r["queries"][0].update(descendant=self.fork),
                       lambda r: r["queries"][0].update(contained="true")):
            with self.subTest(mutate=mutate):
                # A fresh store each time: once a store holds both commits it
                # proves the ancestry itself and the remote is not asked.
                self.store = Path(tempfile.mkdtemp(dir=self.root))
                self.git("init", "-q", "-b", "main", str(self.store))
                self.git("-C", str(self.store), "remote", "add", "origin", self.url)
                # Witness the advertised type without importing its parents:
                # this control must reach the malformed ancestry reply, not
                # pass because an earlier inventory type witness was absent.
                self.provide_inventory_objects()
                observed_queries = []
                def changed(args, **kwargs):
                    result = original(args, **kwargs)
                    if args[:3] == ["agh", "repo", "commit-ancestry"] and result.returncode == 0:
                        reply = json.loads(result.stdout)
                        if reply["queries"]:
                            observed_queries.append(list(reply["queries"]))
                            mutate(reply)
                            return subprocess.CompletedProcess(args, 0, json.dumps(reply), "")
                    return result
                with patch.object(rt, "_run", side_effect=changed):
                    self.assertEqual(rt.RemoteTips().judge(self.store, self.pin, scope="main").state, rt.UNJUDGED)
                self.assertTrue(observed_queries, "the corrupted native query must actually be judged")

    def side_pins(self, count):
        """``count`` commits off main, published only by refs/heads/side, beside
        refs/pins anchors on main: each needs the refs past main to be judged."""
        self.git("-C", str(self.donor), "switch", "-qc", "side", self.pin)
        shas = []
        for n in range(count):
            (self.donor / "side").write_text(str(n))
            self.git("-C", str(self.donor), "add", "side")
            self.git("-C", str(self.donor), "commit", "-qm", f"side-{n}")
            shas.append(self.git("-C", str(self.donor), "rev-parse", "HEAD"))
        self.refs.update({"refs/pins/" + self.revs[1]: self.revs[1], "refs/pins/" + self.revs[2]: self.revs[2],
                          "refs/heads/side": shas[-1]})
        self.provide_inventory_objects()
        return shas

    def fresh_store(self):
        self.store = Path(tempfile.mkdtemp(dir=self.root))
        self.git("init", "-q", "-b", "main", str(self.store))
        self.git("-C", str(self.store), "remote", "add", "origin", self.url)
        self.provide_inventory_objects()

    def test_ancestry_questions_are_batched_then_remembered_never_asked_one_per_tip(self):
        # 2026-11-13: one native read per (pin, tip), serially over every ref,
        # held the reach row for 1h41m. N pins off main now cost two reads
        # (main, then every other ref) at most, and a later run asks none.
        # Typed inventory supplies raw advertised bodies. Leave a real parent
        # gap above the old main tip so that those bodies alone cannot answer
        # the ancestry questions whose batching this test measures.
        self.git("-C", str(self.donor), "switch", "-q", "main")
        for n in range(2):
            (self.donor / "source").write_text("unfetched-main-" + str(n))
            self.git("-C", str(self.donor), "commit", "-qam", "unfetched-main")
        self.tip = self.git("-C", str(self.donor), "rev-parse", "HEAD")
        self.refs["refs/heads/main"] = self.tip
        shas = self.side_pins(3)
        memory = self.root / "memory"
        tips = rt.RemoteTips(memory=memory)
        verdicts = tips.judge_many(self.store, shas + [self.fork])
        self.assertEqual({sha: verdicts[sha].state for sha in shas}, dict.fromkeys(shas, rt.CONTAINED))
        self.assertEqual(verdicts[self.fork].state, rt.NOT_CONTAINED)
        self.assertEqual({verdicts[sha].refs for sha in shas[:-1]}, {("refs/heads/side",)})
        # shas[-1] is an exact anchor; unresolved pins share the main read
        # and at most one further batch. Retained original DATA can resolve a
        # pair without asking it again; it never requires one read per tip.
        self.assertGreater(tips.ancestry_calls, 0)
        self.assertLessEqual(tips.ancestry_calls, 2)
        self.assertLessEqual(tips.remote_questions, 12)
        initial_calls = tips.ancestry_calls
        self.assertEqual(tips.judge(self.store, shas[0]), verdicts[shas[0]])
        self.assertEqual(tips.ancestry_calls, initial_calls)
        # A second run reads the remote's refs afresh (they can move) but no
        # ancestry it already knows, in a store that holds none of it.
        self.fresh_store()
        again = rt.RemoteTips(memory=memory)
        self.assertEqual({sha: v.state for sha, v in again.judge_many(self.store, shas + [self.fork]).items()},
                         {sha: v.state for sha, v in verdicts.items()})
        self.assertEqual((again.ls_remote_calls, again.ancestry_calls), (1, 0))
        self.assertGreater(again.remembered, 0)
        # The refs are not remembered: an anchor the remote stopped publishing
        # is a finding at once, whatever an earlier run saw.
        del self.refs["refs/heads/side"]
        self.assertEqual(rt.RemoteTips(memory=memory).judge(self.store, shas[0]).state, rt.NOT_CONTAINED)

    def test_questions_past_main_go_to_the_remote_in_one_read(self):
        # With no complete local history to refute them, every question past
        # main for every unresolved pin is ONE native read, not one per ref.
        shas = self.side_pins(3)
        with patch.object(rt.RemoteTips, "_is_shallow", return_value=None):
            tips = rt.RemoteTips()
            verdicts = tips.judge_many(self.store, [shas[0], self.fork])
        self.assertEqual((verdicts[shas[0]].state, verdicts[self.fork].state), (rt.CONTAINED, rt.NOT_CONTAINED))
        # main: both in one read; then both against the three other refs
        # (this store does not hold refs/heads/side's tip) in one more.
        self.assertEqual((tips.ancestry_calls, tips.remote_questions), (2, 2 + 2 * 3))

    def test_a_complete_local_history_answers_without_the_remote(self):
        self.side_pins(1)
        self.git("-C", str(self.store), "fetch", "-q", str(self.donor), self.tip, self.fork, self.revs[1],
                 self.revs[2], self.refs["refs/heads/side"])
        tips = rt.RemoteTips()
        self.assertEqual(tips.judge(self.store, self.pin).state, rt.CONTAINED)
        self.assertEqual(tips.judge(self.store, self.fork).state, rt.NOT_CONTAINED)
        self.assertEqual(tips.ancestry_calls, 0)

    def test_a_store_missing_parents_proves_but_never_refutes_ancestry(self):
        # A commit-only intake can hold a commit without its parents and
        # without a shallow file; a 1 from merge-base there is not evidence.
        for sha in (self.tip, self.fork):
            body = subprocess.check_output(["git", "-C", str(self.donor), "cat-file", "commit", sha])
            subprocess.run(["git", "-C", str(self.store), "hash-object", "-w", "-t", "commit", "--stdin"],
                           input=body, check=True, stdout=subprocess.DEVNULL)
        tips = rt.RemoteTips()
        self.assertEqual(tips.judge(self.store, self.fork, scope="main").state, rt.NOT_CONTAINED)
        self.assertEqual(tips.ancestry_calls, 1)
        self.assertEqual(tips.commit_fetch_calls, 0, "an ancestry read is not a commit fetch")

    def witnessed(self):
        """Every commit an inventory or fetch asked native Agh to witness."""
        return [sha for request in self.native_requests for sha in request["commits"]]

    def test_main_scope_witnesses_only_main(self):
        # IR-COHORT-MAIN-WITNESS-1: a cold or unserved tip under another ref
        # is outside "R is an ancestor of the remote's main"; it used to
        # refuse the whole inventory, so every main-scope verdict was UNJUDGED.
        unserved = "1" * 40
        self.refs["refs/heads/claims/x"] = unserved
        tips = rt.RemoteTips()
        self.assertEqual(tips.judge(self.store, self.pin, scope="main").state, rt.CONTAINED)
        self.assertNotIn(unserved, self.witnessed())
        # main's tip is held here: witnessed as a commit, by no native read.
        self.assertEqual((tips.witnessed_tips, tips.native_witnessed_commits, tips.witness_reads), (1, 0, 0))

    def test_the_cohort_warm_and_judgment_share_one_main_inventory(self):
        self.refs["refs/heads/claims/x"] = "1" * 40
        tips = rt.RemoteTips()
        tips.warm(self.store, [self.pin], scope="main")
        verdicts = tips.judge_many(self.store, [self.pin], scope="main")
        self.assertEqual(verdicts[self.pin].state, rt.CONTAINED)
        self.assertEqual(tips.ls_remote_calls, 1)
        self.assertEqual(sum(c[0:3] == ["agh", "repo", "refs"] for c in self.calls), 1)

    def test_a_main_inventory_never_serves_a_durable_judgment(self):
        # The durable lane still needs every head and pin witnessed: an
        # inventory witnessed for main alone must not answer it, in a fresh
        # RemoteTips or in one that judged main first.
        self.refs["refs/heads/claims/x"] = "1" * 40
        self.assertEqual(rt.RemoteTips().judge(self.store, self.pin).state, rt.UNJUDGED)
        tips = rt.RemoteTips()
        self.assertEqual(tips.judge(self.store, self.pin, scope="main").state, rt.CONTAINED)
        verdict = tips.judge(self.store, self.pin)
        self.assertEqual(verdict.state, rt.UNJUDGED)
        self.assertIn("not our ref", verdict.detail)
        self.assertEqual(tips.ls_remote_calls, 2)

    def test_an_errored_durable_inventory_never_serves_a_main_judgment(self):
        # Only a durable inventory read without error is a witnessed superset
        # of main; one refused over an unserved side tip is read again, for
        # main alone.
        self.refs["refs/heads/claims/x"] = "1" * 40
        tips = rt.RemoteTips()
        self.assertEqual(tips.judge(self.store, self.pin).state, rt.UNJUDGED)
        self.assertEqual(tips.judge(self.store, self.pin, scope="main").state, rt.CONTAINED)
        self.assertEqual(tips.ls_remote_calls, 2)

    def test_a_later_failed_witness_batch_keeps_the_earlier_reads_accounting(self):
        # A durable inventory whose first witness batch was read and whose
        # second was refused still acquired what the first reported.
        self.refs.update({"refs/heads/cold": self.fork, "refs/heads/claims/x": "1" * 40})
        original = self.service

        def accounting(args, **kwargs):
            done = original(args, **kwargs)
            if args[:3] == ["agh", "repo", "commit-ancestry"] and done.returncode == 0:
                reply = json.loads(done.stdout)
                reply["acquired_commits"], reply["api_body_bytes"] = 1, 100
                done = subprocess.CompletedProcess(done.args, 0, json.dumps(reply), done.stderr)
            return done

        with patch.object(rt, "_run", side_effect=accounting), patch.object(rt, "ANCESTRY_BATCH", 1):
            tips = rt.RemoteTips()
            self.assertEqual(tips.judge(self.store, self.pin).state, rt.UNJUDGED)
        self.assertEqual(self.witnessed(), [self.fork, "1" * 40])
        self.assertEqual((tips.witness_reads, tips.native_witnessed_commits), (1, 1))
        self.assertEqual((tips.acquired_commits, tips.api_body_bytes), (1, 100))
        # A failed inventory witnessed no tip it can return.
        self.assertEqual(tips.witnessed_tips, 0)

    def test_a_durable_inventory_serves_a_later_main_judgment(self):
        # A durable inventory witnessed every head and pin, main among them.
        tips = rt.RemoteTips()
        self.assertEqual(tips.judge(self.store, self.pin).state, rt.CONTAINED)
        self.assertEqual(tips.judge(self.store, self.fork, scope="main").state, rt.NOT_CONTAINED)
        self.assertEqual(tips.ls_remote_calls, 1)

    def test_main_naming_a_blob_or_annotated_tag_is_unjudged_in_main_scope(self):
        # Narrowing the witness keeps it for main itself: a main that is not
        # an original commit is never CONTAINED or NOT_CONTAINED.
        def write(kind, body):
            return subprocess.check_output(["git", "-C", str(self.store), "hash-object", "-w", "-t", kind,
                                            "--stdin"], input=body).decode().strip()
        blob = write("blob", b"actual non-commit\n")
        tag = write("tag", (f"object {self.tip}\ntype commit\ntag named\n"
                            "tagger Test <t@example.invalid> 1 +0000\n\nactual tag\n").encode())
        for oid in (blob, tag):
            with self.subTest(oid=oid):
                self.refs = {"refs/heads/main": oid}
                verdict = rt.RemoteTips().judge(self.store, self.pin, scope="main")
                self.assertEqual(verdict.state, rt.UNJUDGED, verdict.detail)
                self.assertIn(oid, self.witnessed())

    def test_no_main_counts_the_heads_the_advertisement_named(self):
        self.refs = {"refs/heads/master": self.tip, "refs/heads/claims/x": "1" * 40}
        verdict = rt.RemoteTips().judge(self.store, self.pin, scope="main")
        self.assertEqual(verdict.state, rt.NO_MAIN)
        self.assertIn("(2 head(s) read)", verdict.detail)
        self.assertEqual(self.witnessed(), [])

    def test_a_failed_native_commit_fetch_is_not_repeated_as_a_plain_retry(self):
        # A native read has no shallow boundary to extend (`_fetch` ignores
        # `deepen`), so in a shallow store a failed GitHub commit fetch was
        # followed by an identical "plain retry": (1 + 1 + 2) reads, each
        # attempted 3 times on a transient exit. Now (1 + 2), each 3 times.
        reads = []

        def unavailable(args, **kwargs):
            if args[:3] == ["agh", "repo", "commit-ancestry"]:
                reads.append(json.loads(Path(args[args.index("--input") + 1]).read_text())["commits"])
                return subprocess.CompletedProcess(args, 3, "", "native commit read unavailable")
            return self.service(args, **kwargs)

        with patch.object(rt, "_run", side_effect=unavailable), \
                patch.object(rt.RemoteTips, "_is_shallow", return_value=True):
            tips = rt.RemoteTips()
            failed = tips.ensure(self.store, [self.pin, self.fork])
        self.assertEqual({sha: kind for sha, (kind, _why) in failed.items()},
                         {self.pin: "error", self.fork: "error"})
        attempts = 1 + len(rt.TRANSIENT_RETRY_DELAYS_S)
        self.assertEqual(reads, [[self.pin, self.fork]] * attempts + [[self.pin]] * attempts
                         + [[self.fork]] * attempts)
        self.assertEqual(len(reads), (1 + 2) * 3)
        self.assertEqual(tips.commit_fetch_calls, 3)

    def test_commit_fetches_ancestry_reads_and_witnesses_are_counted_apart(self):
        # Until 2026-11-15 one counter took every native read, so the cohort's
        # 5 ancestry reads were also reported as "5 fetch(es)", and the
        # inventory's witness reads, with what Agh acquired for them, were not
        # reported at all.
        # Advertised; this store lacks both, and one native read witnesses them.
        self.refs.update({"refs/heads/cold": self.fork, "refs/heads/cold2": self.revs[1]})
        original = self.service
        kinds = []

        def accounting(args, **kwargs):
            done = original(args, **kwargs)
            if args[:3] == ["agh", "repo", "commit-ancestry"] and done.returncode == 0:
                request = json.loads(Path(args[args.index("--input") + 1]).read_text())
                kind = ("ancestry" if request["queries"]
                        else "witness" if set(request["commits"]) == {self.fork, self.revs[1]} else "fetch")
                kinds.append(kind)
                reply = json.loads(done.stdout)
                reply["acquired_commits"], reply["api_body_bytes"] = {
                    "witness": (1, 100), "fetch": (1, 20), "ancestry": (2, 3000)}[kind]
                done = subprocess.CompletedProcess(done.args, 0, json.dumps(reply), done.stderr)
            return done

        with patch.object(rt, "_run", side_effect=accounting):
            tips = rt.RemoteTips()
            self.assertEqual(tips.judge(self.store, self.pin).state, rt.CONTAINED)
        self.assertEqual(kinds, ["witness", "fetch", "ancestry"])
        self.assertEqual((tips.ls_remote_calls, tips.witness_reads, tips.native_witnessed_commits), (1, 1, 2))
        self.assertEqual(tips.witnessed_tips, 3)  # main, held here, and the two cold tips
        self.assertEqual((tips.commit_fetch_calls, tips.ancestry_calls), (1, 1))
        self.assertEqual((tips.acquired_commits, tips.api_body_bytes), (1 + 1 + 2, 100 + 20 + 3000))

    def test_a_local_one_over_missing_parents_is_never_a_refutation_or_remembered(self):
        # Git before 2.45 (Apple CLT git among them) read an unparsable parent
        # as no parent, so merge-base could exit 1 over a store holding the
        # two commits without the history between them (git 2.56 exits 128).
        # Only a store where rev-list finds every parent may refute; anything
        # else goes to the remote, and the local 1 is never remembered.
        original = self.service
        handed = []
        remote_up = [True]

        def older_git(args, **kwargs):
            if (args[0] == "git" and "--is-ancestor" in args
                    and str(Path(args[args.index("--git-dir") + 1]).resolve()) == store):
                done = self.actual_run(args, **kwargs)
                if done.returncode == 128:
                    done = subprocess.CompletedProcess(args, 1, "", "")
                handed.append(done.returncode)
                return done
            if args[:3] == ["agh", "repo", "commit-ancestry"] and not remote_up[0]:
                return subprocess.CompletedProcess(args, 3, "", "native ancestry unavailable")
            return original(args, **kwargs)

        actual_put = rt.AncestryMemory.put
        puts = []

        def recorded_put(memory, ancestor, descendant, contained):
            puts.append((ancestor, descendant, contained))
            return actual_put(memory, ancestor, descendant, contained)

        for up in (True, False):
            with self.subTest(remote_up=up):
                # A non-shallow store holding pin and tip but none of the
                # commits between them (a commit-only intake).
                self.fresh_store()
                for sha in (self.pin, self.tip):
                    body = subprocess.check_output(["git", "-C", str(self.donor), "cat-file", "commit", sha])
                    subprocess.run(["git", "-C", str(self.store), "hash-object", "-w", "-t", "commit", "--stdin"],
                                   input=body, check=True, stdout=subprocess.DEVNULL)
                store = str((self.store / ".git").resolve())
                memory = Path(tempfile.mkdtemp(dir=self.root))
                handed.clear()
                puts.clear()
                remote_up[0] = up
                with patch.object(rt, "_run", side_effect=older_git), \
                        patch.object(rt.AncestryMemory, "put", recorded_put):
                    tips = rt.RemoteTips(memory=memory)
                    verdict = tips.judge(self.store, self.pin, scope="main")
                # The status==1 branch was reached over the parentless store.
                self.assertEqual(handed, [1])
                self.assertIs(tips._is_shallow(self.store / ".git"), False)
                # The verdict is the remote's, from one ancestry read; the
                # local 1 was never written to the memory.
                self.assertEqual(tips.ancestry_calls, 1)
                if up:
                    self.assertEqual(verdict.state, rt.CONTAINED)
                    self.assertEqual(puts, [(self.pin, self.tip, True)], "only the remote's answer")
                    self.assertIs(rt.AncestryMemory(memory).get(self.pin, self.tip), True)
                else:
                    self.assertEqual(verdict.state, rt.UNJUDGED)
                    self.assertEqual(puts, [])
                    self.assertIsNone(rt.AncestryMemory(memory).get(self.pin, self.tip))

    def test_refs_past_main_are_asked_in_reads_that_stop_once_a_pin_is_contained(self):
        # Agh caps one read at 128 questions; with a cap of 2 and two open
        # pins, each read asks one ref, and pins contained by an earlier ref
        # are not asked of later ones.
        shas = self.side_pins(3)
        with patch.object(rt.RemoteTips, "_is_shallow", return_value=None), \
                patch.object(rt, "ANCESTRY_BATCH", 2):
            tips = rt.RemoteTips()
            verdicts = tips.judge_many(self.store, [self.revs[1], shas[0], self.fork])
        self.assertEqual([verdicts[s].state for s in (self.revs[1], shas[0], self.fork)],
                         [rt.CONTAINED, rt.CONTAINED, rt.NOT_CONTAINED])
        # revs[1] is an exact anchor. main: 2 questions in 1 read; then one
        # ref per read for the 2 open pins over the 3 other refs.
        self.assertEqual((tips.ancestry_calls, tips.remote_questions), (4, 2 + 2 * 3))

    def test_a_pin_an_early_ref_past_main_contains_is_not_asked_of_later_refs(self):
        # A pin the first ref past main contains must not be asked of the refs
        # after it: one group per ref here (cap 2, three open pins), so the
        # serial loop's early stop survives batching.
        def branch(name, count):
            self.git("-C", str(self.donor), "switch", "-qc", name, self.pin)
            made = []
            for n in range(count):
                (self.donor / name).write_text(str(n))
                self.git("-C", str(self.donor), "add", name)
                self.git("-C", str(self.donor), "commit", "-qm", f"{name}-{n}")
                made.append(self.git("-C", str(self.donor), "rev-parse", "HEAD"))
            return made

        early, side, zeta = branch("early", 3), branch("side", 3), branch("zeta", 1)
        self.refs.update({"refs/pins/" + early[2]: early[2], "refs/heads/side": side[2],
                          "refs/heads/zeta": zeta[0]})
        self.provide_inventory_objects()
        self.assertEqual([ref for ref, _ in rt._order(self.refs.items())],
                         ["refs/heads/main", "refs/pins/" + early[2], "refs/heads/side", "refs/heads/zeta"])
        pins = [early[0], side[0], self.fork]
        asked = []
        original = self.service

        def recording(args, **kwargs):
            if args[:3] == ["agh", "repo", "commit-ancestry"]:
                request = json.loads(Path(args[args.index("--input") + 1]).read_text())
                asked.extend((q["ancestor"], q["descendant"]) for q in request["queries"])
            return original(args, **kwargs)

        with patch.object(rt, "_run", side_effect=recording), \
                patch.object(rt.RemoteTips, "_is_shallow", return_value=None), \
                patch.object(rt, "ANCESTRY_BATCH", 2):
            tips = rt.RemoteTips()
            verdicts = tips.judge_many(self.store, pins)
        self.assertEqual([verdicts[p].state for p in pins], [rt.CONTAINED, rt.CONTAINED, rt.NOT_CONTAINED])
        self.assertEqual(verdicts[early[0]].refs, ("refs/pins/" + early[2],))
        self.assertEqual(verdicts[side[0]].refs, ("refs/heads/side",))
        self.assertIn((early[0], early[2]), asked)
        for later in (side[2], zeta[0]):
            self.assertNotIn((early[0], later), asked)
        self.assertNotIn((side[0], zeta[0]), asked)
        # main 3, the anchor 3, side 2, zeta 1; never every pin against every ref.
        self.assertEqual(tips.remote_questions, len(asked))
        self.assertLess(tips.remote_questions, len(pins) * len(self.refs))

    def test_a_pending_stop_starts_and_retries_no_remote_read(self):
        # After SIGINT/SIGTERM a lost session must not be retried: no second
        # Agh child and no pause, whether the stop came before or during it.
        for arrives in ("before", "during"):
            with self.subTest(arrives=arrives):
                pending = [signal.SIGTERM if arrives == "before" else None]
                reads = []

                def read(timeout):
                    reads.append(timeout)
                    pending[0] = signal.SIGTERM
                    return subprocess.CompletedProcess([], 2, "", rt._OWNED_SESSION_LOST)

                with patch.object(rt, "_active_stop", pending), \
                        patch.object(rt, "TRANSIENT_RETRY_DELAYS_S", (5.0, 5.0)), \
                        patch.object(rt.time, "sleep") as pause:
                    done = rt.RemoteTips()._remote_read(read, 30)
                self.assertLessEqual(len(reads), 0 if arrives == "before" else 1)
                pause.assert_not_called()
                self.assertNotEqual(done.returncode, 0)
                self.assertNotIn(done.returncode, rt.TRANSIENT_EXITS)
                self.assertNotEqual(done.stderr, rt._OWNED_SESSION_LOST)

    def test_an_owned_read_stopped_by_the_operator_is_not_a_lost_session(self):
        # Only a child that died on its own is retried as a lost session; one
        # the operator's stop ended reports the stop, and none starts after it.
        pending = [None]
        with patch.object(rt, "_active_stop", pending):
            timer = threading.Timer(0.3, pending.__setitem__, (0, signal.SIGTERM))
            timer.start()
            try:
                done = rt._run_text_owned([sys.executable, "-c", "import time; time.sleep(30)"],
                                          timeout=30, input_text=None, env=None, cwd=None)
            finally:
                timer.cancel()
            if "unsupported on this host" in done.stderr:
                self.skipTest(done.stderr)
            self.assertEqual((done.returncode, done.stderr),
                             (rt._STOPPED_EXIT, f"remote operation stopped by signal {signal.SIGTERM}"))
            with patch.object(rt.subprocess, "Popen", side_effect=AssertionError("a child started after the stop")):
                again = rt._run_text_owned(["agh", "whoami"], timeout=30, input_text=None, env=None, cwd=None)
            self.assertEqual(again.returncode, rt._STOPPED_EXIT)

    def test_ancestry_memory_is_versioned_so_a_source_fix_retires_old_answers(self):
        memory = self.root / "memory"
        rt.AncestryMemory(memory).put(self.pin, self.tip, True)
        self.assertTrue((memory / rt.AncestryMemory.FORMAT / self.pin[:2] / f"{self.pin}-{self.tip}").is_file())
        with patch.object(rt.AncestryMemory, "FORMAT", "v-next"):
            self.assertIsNone(rt.AncestryMemory(memory).get(self.pin, self.tip))

    def test_spent_time_bound_starts_no_read_and_is_unjudged(self):
        tips = rt.RemoteTips(time_bound=0)
        verdict = tips.judge(self.store, self.pin)
        self.assertEqual(verdict.state, rt.UNJUDGED)
        self.assertIn("time bound", verdict.detail)
        self.assertFalse(any(c[0] == "agh" for c in self.calls))

    def test_transient_remote_failure_is_retried_then_unjudged_never_a_finding(self):
        original = self.service
        failures = []

        def flaky(args, **kwargs):
            if args[:3] == ["agh", "repo", "refs"] and failures:
                return subprocess.CompletedProcess(args, failures.pop(0), "", "[Errno 1] Operation not permitted")
            return original(args, **kwargs)

        with patch.object(rt, "_run", side_effect=flaky):
            failures[:] = [127, 3]
            self.assertEqual(rt.RemoteTips().judge(self.store, self.pin).state, rt.CONTAINED)
            failures[:] = [3, 3, 3]
            self.assertEqual(rt.RemoteTips().judge(self.store, self.fork).state, rt.UNJUDGED)
            self.assertEqual(failures, [])
            failures[:] = [11, 11]  # a rate limit is not waited out inside the bound
            self.assertEqual(rt.RemoteTips().judge(self.store, self.pin).state, rt.UNJUDGED)
            self.assertEqual(failures, [11])

    def test_authority_loader_ignores_stale_pyc_and_preloaded_module(self):
        # This fixture owns a captured reader subject; production outside-root
        # sources still refuse before and during the explicit fixture epoch.
        fixture = self.root.resolve()
        source = fixture / "authority.py"
        source.write_text("value = 'stale'\n")
        py_compile.compile(str(source), doraise=True, invalidation_mode=py_compile.PycInvalidationMode.UNCHECKED_HASH)
        source.write_text("value = 'actual'\n")
        digest = gate.hashlib.sha256(source.read_bytes()).hexdigest()
        name = "_trust_land_remote_tips_" + digest
        # The real loader refuses this fixture under its default production
        # root. A fixture import epoch must own its actual complete source tree.
        with self.assertRaises(ValueError):
            gate._load_captured_source(source)
        program = fixture / "scripts/land_gate.py"
        program.parent.mkdir()
        program.write_bytes((SCRIPTS / "land_gate.py").read_bytes())
        imports = gate._DiscoveryReaderImports(fixture)
        self.assertEqual(imports.program, gate.hashlib.sha256(program.read_bytes()).hexdigest())
        fake = types.ModuleType(name)
        fake.value = "preloaded"
        with patch.object(gate, "_DISCOVERY_SOURCE_IMPORTS", imports), \
                patch.dict(sys.modules, {name: fake, "remote_tips": fake}):
            loaded, captured, compiled = gate._load_captured_source(source)
            self.assertIsNot(loaded, fake)
            self.assertEqual(compiled, b"value = 'actual'\n")
            self.assertEqual(loaded.value, "actual")
            self.assertEqual(captured, digest)
            execution = imports.executions[loaded]
            self.assertEqual(imports.records[loaded], ("authority.py", ("100644", digest)))
            self.assertEqual(imports.kinds[loaded], "captured-source")
            self.assertEqual(execution.role, "implementation")
            self.assertTrue(execution.complete)
            self.assertIs(execution.module, loaded)
            self.assertIs(imports.importer(loaded.__dict__), execution)
            self.assertNotIn(loaded, imports.pending)
            self.assertNotIn(loaded, imports.created)
            self.assertIsNone(imports.implementation_problem(loaded, execution))
            source.write_text("value = 'changed later'\n")
            self.assertEqual(loaded.value, "actual")
            self.assertIn("source changed", imports.implementation_problem(loaded, execution))
            with tempfile.TemporaryDirectory() as outside:
                escaped = Path(outside) / "authority.py"
                escaped.write_text("value = 'outside'\n")
                with self.assertRaises(ValueError):
                    gate._load_captured_source(escaped)
        with patch.dict(gate._GATE_SNAPSHOT, {}, clear=True), patch.object(gate, "sha256_file", return_value="later-disk"):
            self.assertEqual(gate.gate_code_identity([])["scripts/lib/remote_tips.py"], gate._REMOTE_TIPS_SOURCE_SHA256)


if __name__ == "__main__":
    unittest.main()
