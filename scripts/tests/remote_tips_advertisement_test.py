#!/usr/bin/env python3
"""Real Git object types behind an authenticated native advertisement."""
from __future__ import annotations

import json
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "lib"))
import remote_tips as rt


class AdvertisementTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.store = self.root / "store"
        self.git("init", "-q", str(self.store))
        tree = self.git("-C", str(self.store), "mktree", input=b"")
        self.commit = self.object("commit", (f"tree {tree}\nauthor Test <t@example.invalid> 1 +0000\n"
                                              "committer Test <t@example.invalid> 1 +0000\n\n").encode()
                                  + b"original\r\nbytes\xff\n")
        self.entries = [{"ref": "refs/heads/main", "oid": self.commit}]
        self.actual_run = rt._run
        self.calls = []
        self.repository = "Owner/Repo"
        self.native_reply = None
        self.transport = patch.object(rt, "_run", side_effect=self.service)
        self.transport.start()
        self.addCleanup(self.transport.stop)

    def git(self, *args, input=None):
        return subprocess.check_output(["git", *args], input=input, cwd=self.root,
                                       stderr=subprocess.DEVNULL).decode().strip()

    def object(self, kind, body):
        return self.git("-C", str(self.store), "hash-object", "-w", "-t", kind, "--stdin", input=body)

    def service(self, args, **kwargs):
        self.calls.append(list(args))
        if args[0] != "agh":
            return self.actual_run(args, **kwargs)
        if args[1] == "whoami":
            return subprocess.CompletedProcess(args, 0, json.dumps({"decision": {"send": {"profile": "owner-profile"}}}), "")
        if args[1:3] == ["repo", "commit-ancestry"]:
            self.assertEqual(args[3], self.repository)
            self.assertNotIn("--as", args)
            request = json.loads(Path(args[args.index("--input") + 1]).read_text())
            self.assertEqual(request["queries"], [])
            self.last_native_request = request
            if self.native_reply is None:
                return subprocess.CompletedProcess(args, 6, "", "advertised object is not a commit")
            reply = self.native_reply(request)
            return subprocess.CompletedProcess(args, *reply)
        self.assertEqual(args[1:], ["repo", "refs", self.repository, "--no-anonymous-api"])
        return subprocess.CompletedProcess(args, 0, json.dumps(self.entries), "")

    def lookup(self, **kwargs):
        return rt.remote_refs("https://github.com/" + self.repository + ".git", **kwargs)

    def state(self):
        gd = self.store / ".git"
        return (self.git("-C", str(self.store), "for-each-ref", "--format=%(refname) %(objectname)"),
                {name: (gd / name).read_bytes() if (gd / name).exists() else None
                 for name in ("HEAD", "config", "index", "FETCH_HEAD", "shallow")})

    def test_complete_heads_and_pins_keep_names_without_rest_or_source_writes(self):
        self.entries += [{"ref": ref, "oid": self.commit} for ref in
                         ("refs/heads/master", "refs/pins/" + self.commit,
                          "refs/tags/release", "refs/tags/release^{}")]
        before = self.state()
        done = self.lookup(git_dir=self.store / ".git")
        self.assertEqual(done.returncode, 0, done.stderr)
        self.assertEqual(dict(rt.parse_ls_remote(done.stdout)), {
            "refs/heads/main": self.commit, "refs/heads/master": self.commit,
            "refs/pins/" + self.commit: self.commit})
        self.assertEqual(self.state(), before)
        self.assertEqual(sum(a[:3] == ["agh", "repo", "refs"] for a in self.calls), 1)

    def test_advertisement_does_not_adopt_or_change_the_callers_hooks_config(self):
        self.git("-C", str(self.store), "config", "core.hooksPath", "scripts/hooks")
        before = self.state()
        original = self.service
        contexts = []

        def guarded(args, **kwargs):
            if args[:3] == ["agh", "repo", "refs"]:
                directory = kwargs.get("cwd")
                contexts.append(directory)
                if directory is None or Path(directory) == self.store:
                    return subprocess.CompletedProcess(args, 1, "", "guarded core.hooksPath")
                self.assertEqual(Path(directory).stat().st_mode & 0o777, 0o700)
                self.assertFalse((Path(directory) / ".git").exists())
                self.assertNotIn("isolate_git_config", kwargs)
            return original(args, **kwargs)

        with patch.object(rt, "_run", side_effect=guarded):
            done = self.lookup(git_dir=self.store / ".git", cwd=self.store)
        self.assertEqual(done.returncode, 0, done.stderr)
        self.assertEqual(len(contexts), 1)
        self.assertFalse(Path(contexts[0]).exists())
        self.assertEqual(self.state(), before)

    def test_private_transport_refusal_is_returned_without_starting_a_read(self):
        refusal = subprocess.CompletedProcess([], 2, "", "private source transport root changed")
        with patch.object(rt, "_source_transport", side_effect=rt._PublicationSourceFailure(refusal)):
            done = self.lookup(git_dir=self.store / ".git")
        self.assertIs(done, refusal)
        self.assertFalse(any(a[0] == "agh" for a in self.calls))

    def test_native_commit_read_borrows_originals_without_adopting_caller_config(self):
        self.git("-C", str(self.store), "config", "core.hooksPath", "scripts/hooks")
        before = self.state()
        contexts = []
        original = self.service
        self.native_reply = self.native_success

        def guarded(args, **kwargs):
            if args[:3] == ["agh", "repo", "commit-ancestry"]:
                view = Path(args[4])
                if view.resolve() == (self.store / ".git").resolve():
                    return subprocess.CompletedProcess(args, 1, "", "guarded core.hooksPath")
                contexts.append(view)
                self.assertEqual(kwargs.get("cwd"), view.parents[1])
                self.assertEqual(view.parents[1].stat().st_mode & 0o777, 0o700)
                self.assertNotIn("hooksPath", (view / "config").read_text())
                self.assertEqual((view / "objects/info/alternates").read_text(),
                                 str((self.store / ".git/objects").resolve()) + "\n")
                self.assertEqual(rt.RemoteTips.present(view, [self.commit]), {self.commit})
                self.assertNotIn("isolate_git_config", kwargs)
            return original(args, **kwargs)

        with patch.object(rt, "_run", side_effect=guarded):
            done = rt._native_commit_read(self.repository, self.store / ".git", [self.commit],
                                          timeout=30, materialize=True)
        self.assertEqual(done.returncode, 0, done.stderr)
        self.assertEqual(len(contexts), 1)
        self.assertFalse(contexts[0].parents[1].exists())
        self.assertEqual(self.state(), before)
        self.assertFalse((self.store / ".git/objects/info/alternates").exists())

    def test_native_commit_read_refuses_replaced_original_objects(self):
        original = self.service
        self.native_reply = self.native_success

        def replaced(args, **kwargs):
            done = original(args, **kwargs)
            if args[:3] == ["agh", "repo", "commit-ancestry"]:
                objects = self.store / ".git/objects"
                objects.rename(self.store / ".git/old-objects")
                objects.mkdir()
            return done

        with patch.object(rt, "_run", side_effect=replaced):
            done = rt._native_commit_read(self.repository, self.store / ".git", [self.commit], timeout=30)
        self.assertEqual(done.returncode, 2, done.stderr)
        self.assertIn("original object directory changed", done.stderr)

    def test_native_commit_import_rechecks_raw_bytes_before_any_object_write(self):
        original = self.service
        self.native_reply = self.native_success
        writes = []
        before = self.state()

        def wrong_bytes(args, **kwargs):
            if "cat-file" in args and "--batch" in args and kwargs.get("binary"):
                body = b"not the requested original body"
                framed = self.commit.encode() + b" commit " + str(len(body)).encode() + b"\n" + body + b"\n"
                return subprocess.CompletedProcess(args, 0, framed, b"")
            if any(command in args for command in ("hash-object", "pack-objects", "index-pack")):
                writes.append(args)
            return original(args, **kwargs)

        with patch.object(rt, "_run", side_effect=wrong_bytes):
            done = rt._native_commit_read(self.repository, self.store / ".git", [self.commit],
                                          timeout=30, materialize=True)
        self.assertEqual(done.returncode, 2, done.stderr)
        self.assertIn("different hash", done.stderr)
        self.assertFalse(writes)
        self.assertEqual(self.state(), before)

    def test_native_commit_read_expired_deadline_starts_no_command(self):
        with patch.object(rt, "_run", side_effect=AssertionError("expired native read started a command")):
            done = rt._native_commit_read(self.repository, self.store / ".git", [self.commit], timeout=0)
        self.assertEqual(done.returncode, 124, done.stderr)

    def test_native_commit_private_context_refusal_starts_no_read(self):
        refusal = subprocess.CompletedProcess([], 2, "", "private source transport root changed")
        with patch.object(rt, "_source_transport", side_effect=rt._PublicationSourceFailure(refusal)):
            done = rt._native_commit_read(self.repository, self.store / ".git", [self.commit], timeout=30)
        self.assertIs(done, refusal)
        self.assertFalse(any(a[0] == "agh" for a in self.calls))

    def test_native_unavailable_for_missing_original_refuses_entire_inventory(self):
        self.entries.append({"ref": "refs/pins/missing", "oid": "1" * 40})
        before = self.state()
        done = self.lookup(git_dir=self.store / ".git")
        self.assertEqual((done.returncode, done.stdout), (6, ""))
        self.assertIn("not our ref", done.stderr)
        self.assertEqual(self.state(), before)

    def test_a_named_witness_narrows_only_the_witnessed_and_returned_refs(self):
        # IR-COHORT-MAIN-WITNESS-1: the cohort witnesses main alone; an
        # unserved pin it does not read no longer refuses its inventory, and
        # never leaves as a durable ref.
        self.entries.append({"ref": "refs/pins/missing", "oid": "1" * 40})
        self.last_native_request = None
        done = self.lookup(git_dir=self.store / ".git", witness=("refs/heads/main",))
        self.assertEqual(done.returncode, 0, done.stderr)
        self.assertEqual(done.stdout, self.commit + "\trefs/heads/main\n")
        self.assertEqual(done.commit_witness_reads, [])
        self.assertIn(("refs/pins/missing", "1" * 40), done.advertisement_refs)
        self.assertIsNone(self.last_native_request)
        # The default still witnesses every head and pin.
        self.assertEqual(self.lookup(git_dir=self.store / ".git").returncode, 6)

    def test_a_named_witness_still_validates_every_advertised_entry(self):
        for bad in ({"ref": "refs/heads/side^{}", "oid": self.commit},
                    {"ref": "refs/pins/x..y", "oid": self.commit},
                    {"ref": "refs/heads/main", "oid": self.commit}):
            with self.subTest(entry=bad):
                self.entries = [{"ref": "refs/heads/main", "oid": self.commit}, bad]
                done = self.lookup(git_dir=self.store / ".git", witness=("refs/heads/main",))
                self.assertEqual((done.returncode, done.stdout), (2, ""))

    def test_a_named_witness_still_refuses_a_noncommit_main(self):
        blob = self.object("blob", b"actual non-commit\n")
        self.entries = [{"ref": "refs/heads/main", "oid": blob}]
        done = self.lookup(git_dir=self.store / ".git", witness=("refs/heads/main",))
        self.assertEqual((done.returncode, done.stdout), (6, ""))
        self.assertEqual(self.last_native_request, {"commits": [blob], "queries": []})

    def test_real_blob_and_annotated_tag_pins_cannot_impersonate_commits(self):
        blob = self.object("blob", b"actual non-commit\n")
        tag = self.object("tag", (f"object {self.commit}\ntype commit\ntag named\n"
                                   "tagger Test <t@example.invalid> 1 +0000\n\nactual tag\n").encode())
        for oid in (blob, tag):
            with self.subTest(oid=oid):
                self.entries = [{"ref": "refs/heads/main", "oid": self.commit},
                                {"ref": "refs/pins/noncommit", "oid": oid}]
                done = self.lookup(git_dir=self.store / ".git")
                self.assertEqual((done.returncode, done.stdout), (6, ""))

    def test_no_context_cannot_infer_a_commit_type_from_a_branch_name(self):
        done = self.lookup()
        self.assertEqual((done.returncode, done.stdout), (2, ""))
        self.assertIn("actual Git store", done.stderr)

    def test_fresh_inventory_wins_over_local_refs_and_prior_reads(self):
        self.git("-C", str(self.store), "update-ref", "refs/heads/stale", self.commit)
        self.assertIn("refs/heads/main", self.lookup(cwd=self.store).stdout)
        self.entries = [{"ref": "refs/heads/master", "oid": self.commit}]
        done = self.lookup(cwd=self.store)
        self.assertEqual(done.stdout, self.commit + "\trefs/heads/master\n")

    def test_duplicate_unknown_malformed_and_peeled_durable_rows_refuse(self):
        good = {"ref": "refs/heads/main", "oid": self.commit}
        rows = [[good, good], [{**good, "object": {"type": "commit"}}],
                [{"ref": "refs/heads/main", "oid": "0" * 40}],
                [{"ref": "refs/heads/main", "oid": self.commit.upper()}]]
        rows += [[{"ref": name, "oid": self.commit}] for name in
                 ("refs/heads/", "refs/heads/.hidden", "refs/heads/a.lock", "refs/heads/a..b",
                  "refs/pins/name^{}", "refs/tags/bad name", "refs/heads/a\x7f", "foreign", "HEAD")]
        for entries in rows:
            with self.subTest(entries=entries):
                self.entries = entries
                done = self.lookup(git_dir=self.store / ".git")
                self.assertEqual((done.returncode, done.stdout), (2, ""))

    def test_duplicate_json_fields_are_ambiguous_even_if_last_value_is_valid(self):
        text = '[{"ref":"refs/heads/main","oid":"bad","oid":' + json.dumps(self.commit) + '}]'
        with patch.object(rt, "_agh", return_value=subprocess.CompletedProcess([], 0, text, "")):
            self.assertEqual(self.lookup(git_dir=self.store / ".git").returncode, 2)

    def test_wrong_hash_or_truncated_original_commit_cannot_supply_type(self):
        original = self.service
        for data in (f"{self.commit} commit 3\nbad\n".encode(),
                     f"{self.commit} commit 99\ntruncated".encode()):
            def corrupt(args, **kwargs):
                if args[0] == "git" and "--batch" in args:
                    return subprocess.CompletedProcess(args, 0, data, b"")
                return original(args, **kwargs)
            with self.subTest(data=data), patch.object(rt, "_run", side_effect=corrupt):
                self.assertNotEqual(self.lookup(git_dir=self.store / ".git").returncode, 0)

    @staticmethod
    def native_success(request):
        return (0, json.dumps({"schema": 1, "scope": "commit-parent-ancestry-only-v1",
                **request, "acquired_commits": len(request["commits"]), "api_body_bytes": 321,
                "refs_written": False, "checkout_complete": False}), "")

    def canonical(self, origin="https://github.com/Owner/trust.git"):
        canonical = self.root / "trust"
        self.git("init", "-q", str(canonical))
        self.git("-C", str(canonical), "remote", "add", "origin", origin)
        body = subprocess.check_output(["git", "-C", str(self.store), "cat-file", "commit", self.commit])
        self.assertEqual(self.git("-C", str(canonical), "hash-object", "-w", "-t", "commit",
                                  "--stdin", input=body), self.commit)
        return canonical

    def test_unsupported_descriptor_flags_skip_optional_canonical_hint(self):
        flag = rt.os.O_NOFOLLOW
        try:
            del rt.os.O_NOFOLLOW
            with patch.object(rt, "_run", side_effect=AssertionError("unsupported canonical probe")):
                self.assertEqual(rt._canonical_commit_witness("Owner/trust", [self.commit],
                                                              deadline=float("inf")), set())
        finally:
            rt.os.O_NOFOLLOW = flag

    def test_readonly_same_repository_originals_supply_types_without_copy_or_native(self):
        self.repository = "Owner/trust"
        canonical = self.canonical()
        receiver = self.root / "receiver"
        self.git("init", "-q", str(receiver))
        before = {name: (canonical / ".git" / name).read_bytes()
                  for name in ("HEAD", "config")}
        with patch.object(rt.Path, "home", return_value=self.root):
            done = self.lookup(git_dir=receiver / ".git")
        self.assertEqual(done.returncode, 0, done.stderr)
        self.assertEqual(done.stdout, self.commit + "\trefs/heads/main\n")
        self.assertEqual(rt.RemoteTips.present(receiver / ".git", [self.commit]), set())
        self.assertFalse(any(a[:3] == ["agh", "repo", "commit-ancestry"] for a in self.calls))
        self.assertEqual({name: (canonical / ".git" / name).read_bytes() for name in before}, before)

    def test_wrong_repository_or_replaced_canonical_hint_cannot_supply_types(self):
        self.repository = "Owner/trust"
        canonical = self.canonical("https://github.com/Other/trust.git")
        receiver = self.root / "receiver"
        self.git("init", "-q", str(receiver))
        with patch.object(rt.Path, "home", return_value=self.root):
            self.assertEqual(self.lookup(git_dir=receiver / ".git").returncode, 6)
        self.git("-C", str(canonical), "remote", "set-url", "origin", "https://github.com/Owner/trust.git")
        actual = self.actual_run
        def replaced(args, **kwargs):
            result = actual(args, **kwargs)
            if "--batch" in args and kwargs.get("cwd") == canonical:
                canonical.rename(self.root / "old-canonical")
                canonical.mkdir()
            return result
        with patch.object(rt.Path, "home", return_value=self.root), \
                patch.object(rt, "_run", side_effect=lambda a, **k: self.service(a, **k)
                             if a[0] == "agh" else replaced(a, **k)):
            self.assertEqual(self.lookup(git_dir=receiver / ".git").returncode, 6)

    def test_cold_native_types_bind_only_missing_original_snapshot_and_keep_accounting(self):
        missing = "1" * 40
        self.entries.append({"ref": "refs/pins/captured", "oid": missing})
        captured = list(self.entries)
        def reply(request):
            self.entries = [{"ref": "refs/heads/now-different", "oid": "2" * 40}]
            return self.native_success(request)
        self.native_reply = reply
        before = self.state()
        done = self.lookup(git_dir=self.store / ".git")
        self.assertEqual(done.returncode, 0, done.stderr)
        self.assertEqual(dict(rt.parse_ls_remote(done.stdout)), {r["ref"]: r["oid"] for r in captured})
        self.assertEqual(self.last_native_request, {"commits": [missing], "queries": []})
        self.assertEqual(done.commit_witness_reads, [{"commits": [missing], "acquired_commits": 1,
                                                     "api_body_bytes": 321}])
        self.assertEqual(sum(a[:3] == ["agh", "repo", "refs"] for a in self.calls), 1)
        self.assertEqual(self.state(), before)

    def test_a_bare_string_witness_is_refused(self):
        # A str is an Iterable[str] of characters: it would witness no ref and
        # read as an advertisement without main.
        with self.assertRaises(TypeError):
            self.lookup(git_dir=self.store / ".git", witness="refs/heads/main")

    def test_every_witnessed_tip_is_counted_however_it_was_witnessed(self):
        missing = "1" * 40
        self.entries.append({"ref": "refs/pins/captured", "oid": missing})
        self.native_reply = self.native_success
        done = self.lookup(git_dir=self.store / ".git")
        self.assertEqual(done.returncode, 0, done.stderr)
        self.assertEqual(done.witnessed_tips, len({e["oid"] for e in self.entries}))

    def test_a_later_failed_native_witness_batch_keeps_the_earlier_accounting(self):
        self.entries.extend([{"ref": "refs/pins/one", "oid": "1" * 40},
                             {"ref": "refs/pins/two", "oid": "2" * 40}])
        replies = iter([self.native_success, lambda request: (6, "", "actual guarded refusal")])
        self.native_reply = lambda request: next(replies)(request)
        with patch.object(rt, "ANCESTRY_BATCH", 1):
            done = self.lookup(git_dir=self.store / ".git")
        self.assertEqual(done.returncode, 6)
        self.assertEqual(done.commit_witness_reads, [{"commits": ["1" * 40], "acquired_commits": 1,
                                                     "api_body_bytes": 321}])

    def test_cold_native_duplicate_protocol_fields_refuse(self):
        self.entries.append({"ref": "refs/pins/cold", "oid": "1" * 40})
        def reply(request):
            text = self.native_success(request)[1]
            return 0, text[:-1] + ', "refs_written":false}', ""
        self.native_reply = reply
        self.assertEqual(self.lookup(git_dir=self.store / ".git").returncode, 2)

    def test_cold_native_refusals_or_wrong_scope_population_and_accounting_refuse_all(self):
        self.entries.append({"ref": "refs/pins/cold", "oid": "1" * 40})
        for status in (3, 6, 11, 124):
            with self.subTest(status=status):
                self.native_reply = lambda request: (status, "", "actual guarded refusal")
                done = self.lookup(git_dir=self.store / ".git")
                self.assertEqual((done.returncode, done.stdout), (status, ""))
        for field, value in (("scope", "other"), ("commits", [self.commit]),
                             ("refs_written", True), ("queries", [{}]),
                             ("acquired_commits", False), ("api_body_bytes", -1)):
            def bad(request):
                reply = json.loads(self.native_success(request)[1])
                reply[field] = value
                return 0, json.dumps(reply), ""
            with self.subTest(field=field):
                self.native_reply = bad
                self.assertEqual(self.lookup(git_dir=self.store / ".git").returncode, 2)

    def test_original_deadline_expiration_after_type_probe_starts_no_native_read(self):
        self.entries.append({"ref": "refs/pins/cold", "oid": "1" * 40})
        done = subprocess.CompletedProcess([], 0, json.dumps(self.entries), "")
        with patch.object(rt, "_agh", return_value=done), \
                patch.object(rt.RemoteTips, "present", return_value={self.commit}), \
                patch.object(rt, "_canonical_commit_witness", return_value=set()), \
                patch.object(rt.time, "monotonic", side_effect=[0, 1, 2, 91]), \
                patch.object(rt, "_native_commit_read", side_effect=AssertionError("late native read")):
            self.assertEqual(self.lookup(git_dir=self.store / ".git").returncode, 124)

    def test_expired_advertisement_deadline_starts_no_type_read(self):
        done = subprocess.CompletedProcess([], 0, json.dumps(self.entries), "")
        with patch.object(rt, "_agh", return_value=done), \
                patch.object(rt.time, "monotonic", side_effect=[10, 101]), \
                patch.object(rt.RemoteTips, "present", side_effect=AssertionError("late type read")):
            self.assertEqual(self.lookup(git_dir=self.store / ".git", timeout=90).returncode, 124)


if __name__ == "__main__":
    unittest.main()
