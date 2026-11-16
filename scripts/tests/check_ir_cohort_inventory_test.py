#!/usr/bin/env python3
"""Real-Git controls for complete cohort manifest inventory, and for the
batched, remembered, bounded containment judgment and the judged date.

Run: python3 -m unittest scripts.tests.check_ir_cohort_inventory_test
"""
from pathlib import Path
import contextlib
import datetime
import io
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
import time
import unittest
from unittest import mock

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import check_ir_cohort as gate

DECL = 'trust-ir = { git = "https://github.com/alabsystems/trust-ir", rev = "' + 'a' * 40 + '" }\n'


class ManifestInventoryTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(prefix="ir-inventory.")
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name).resolve() / "root"
        self.repo(self.root, {"README": "root\n"})

    def git(self, root, *args):
        return subprocess.check_output(["git", "-C", str(root), *args], text=True, stderr=subprocess.PIPE).strip()

    def repo(self, root, files):
        root.mkdir(parents=True, exist_ok=True)
        self.git(root, "init", "-q", "-b", "main")
        self.git(root, "config", "user.email", "test@example.invalid")
        self.git(root, "config", "user.name", "Test")
        for name, text in files.items():
            path = root / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(text)
        self.git(root, "add", "-A")
        self.git(root, "commit", "-qm", "fixture")

    def child(self, parent, relative, files=None):
        child = parent / relative
        self.repo(child, files or {"Cargo.toml": '[dependencies]\n' + DECL})
        head = self.git(child, "rev-parse", "HEAD")
        self.git(parent, "update-index", "--add", "--cacheinfo", f"160000,{head},{relative}")
        self.git(parent, "commit", "-qm", "tracked child")
        return child

    def test_unregistered_inactive_and_uninitialized_metadata_do_not_hide_a_populated_child(self):
        self.child(self.root, "first-party/dep")
        self.assertEqual(self.git(self.root, "ls-files", "--recurse-submodules", "*Cargo.toml"), "")
        for settings in ((), ("submodule.first-party/dep.active", "false"), ("submodule.active", ":!first-party/dep")):
            with self.subTest(settings=settings):
                if settings:
                    self.git(self.root, "config", *settings)
                rows = gate.find_declarations(self.root)
                self.assertEqual([row.where for row in rows], ["first-party/dep/Cargo.toml"])

    def test_nested_gitlinks_are_complete_and_sorted_without_activation(self):
        a = self.child(self.root, "first-party/a")
        self.child(a, "nested/leaf")
        self.child(self.root, "first-party/b with spaces")
        self.git(self.root, "config", "submodule.active", ":!first-party/*")
        self.git(a, "config", "submodule.nested/leaf.active", "false")
        self.assertEqual([row.where for row in gate.find_declarations(self.root)], [
            "first-party/a/Cargo.toml", "first-party/a/nested/leaf/Cargo.toml", "first-party/b with spaces/Cargo.toml",
        ])

    def test_untracked_nested_repository_is_not_a_consumer(self):
        self.repo(self.root / "untracked", {"Cargo.toml": '[dependencies]\n' + DECL})
        self.assertEqual(gate.find_declarations(self.root), [])

    def test_missing_or_nonrepository_gitlink_refuses_instead_of_returning_empty(self):
        child = self.child(self.root, "first-party/dep")
        shutil.rmtree(child / ".git")
        with self.assertRaises(gate.InventoryError):
            gate.find_declarations(self.root)
        shutil.rmtree(child)
        with self.assertRaises(gate.InventoryError):
            gate.find_declarations(self.root)

    def test_unreadable_index_and_missing_tracked_manifest_refuse(self):
        child = self.child(self.root, "first-party/dep")
        original = gate.run
        def failed(args, cwd, **kwargs):
            return (128, "") if args[1:2] == ["ls-files"] else original(args, cwd, **kwargs)
        with mock.patch.object(gate, "run", side_effect=failed), self.assertRaises(gate.InventoryError):
            gate.find_declarations(self.root)
        (child / "Cargo.toml").unlink()
        with self.assertRaises(gate.InventoryError):
            gate.find_declarations(self.root)
        error_output = io.StringIO()
        with mock.patch.object(sys, "argv", ["check_ir_cohort.py", "--root", str(self.root), "--report"]), contextlib.redirect_stderr(error_output):
            self.assertEqual(gate.main(), 2)
        self.assertIn("IR COHORT COULD NOT RUN", error_output.getvalue())

    def test_staged_manifest_is_inventoried_but_unmerged_index_refuses(self):
        manifest = self.root / "Cargo.toml"
        manifest.write_text('[dependencies]\n' + DECL)
        self.git(self.root, "add", "Cargo.toml")
        self.assertEqual([row.where for row in gate.find_declarations(self.root)], ["Cargo.toml"])
        oid = self.git(self.root, "hash-object", "Cargo.toml")
        subprocess.run(["git", "-C", str(self.root), "update-index", "--index-info"],
                       input=f"0 {'0' * 40}\tCargo.toml\n100644 {oid} 1\tCargo.toml\n100644 {oid} 2\tCargo.toml\n",
                       text=True, check=True)
        with self.assertRaises(gate.InventoryError):
            gate.find_declarations(self.root)

    def test_hook_environment_cannot_substitute_a_partial_index_or_repository(self):
        child = self.child(self.root, "first-party/dep")
        (self.root / "Cargo.toml").write_text('[dependencies]\n' + DECL)
        self.git(self.root, "add", "Cargo.toml")
        self.git(self.root, "commit", "-qm", "root manifest")
        alternate = Path(self.tmp.name) / "alternate-index"
        env = dict(os.environ, GIT_INDEX_FILE=str(alternate))
        subprocess.run(["git", "-C", str(self.root), "read-tree", "--empty"], env=env, check=True)
        subprocess.run(["git", "-C", str(self.root), "add", "Cargo.toml"], env=env, check=True)
        for overrides in ({"GIT_INDEX_FILE": str(alternate)},
                          {"GIT_DIR": str(child / ".git"), "GIT_WORK_TREE": str(child)}):
            with self.subTest(overrides=overrides), mock.patch.dict(os.environ, overrides):
                rows = gate.find_declarations(self.root)
                self.assertEqual([row.where for row in rows], ["Cargo.toml", "first-party/dep/Cargo.toml"])

    def test_missing_index_and_unborn_repository_are_not_empty_inventories(self):
        for state in ("missing-index", "unborn"):
            with self.subTest(state=state):
                child = self.child(self.root, "first-party/" + state)
                if state == "missing-index":
                    (child / ".git/index").unlink()
                else:
                    self.git(child, "update-ref", "-d", "refs/heads/main")
                with self.assertRaises(gate.InventoryError):
                    gate.find_declarations(self.root)
                if state == "missing-index":
                    self.git(child, "reset", "--mixed", "HEAD")

    def test_linked_worktree_index_is_read_from_its_own_administrative_directory(self):
        source = Path(self.tmp.name) / "store"
        self.repo(source, {"Cargo.toml": '[dependencies]\n' + DECL})
        linked = self.root / "first-party/linked"
        linked.parent.mkdir()
        self.git(source, "worktree", "add", "-q", "--detach", str(linked), "HEAD")
        head = self.git(linked, "rev-parse", "HEAD")
        self.git(self.root, "update-index", "--add", "--cacheinfo", f"160000,{head},first-party/linked")
        self.git(self.root, "commit", "-qm", "linked worktree")
        self.assertTrue((linked / ".git").is_file())
        self.assertEqual([row.where for row in gate.find_declarations(self.root)], ["first-party/linked/Cargo.toml"])

    def test_semantic_digest_retains_genuine_absence_and_distinguishes_present_source(self):
        absent = self.git(self.root, "rev-parse", "HEAD")
        absent_digest = gate.semantic_digest(self.root, absent, ("surface.rs",))
        self.assertIsNotNone(absent_digest)
        (self.root / "surface.rs").write_text("pub const SURFACE: u8 = 1;\n")
        self.git(self.root, "add", "surface.rs")
        self.git(self.root, "commit", "-qm", "present semantic source")
        present = self.git(self.root, "rev-parse", "HEAD")
        self.assertNotEqual(gate.semantic_digest(self.root, present, ("surface.rs",)), absent_digest)
        self.assertEqual(gate.semantic_digest(self.root, absent, ("surface.rs",)), absent_digest)

    def test_missing_semantic_blobs_refuse_until_their_exact_bytes_are_restored(self):
        for relative in ("surface.rs", "surface/extension.rs"):
            with self.subTest(relative=relative):
                source = self.root / relative
                source.parent.mkdir(parents=True, exist_ok=True)
                source.write_text("pub const SURFACE: u8 = 1;\n// " + relative + "\n")
                self.git(self.root, "add", relative)
                self.git(self.root, "commit", "-qm", "tracked semantic source")
                revision = self.git(self.root, "rev-parse", "HEAD")
                complete = gate.semantic_digest(self.root, revision, ("surface.rs",))
                self.assertIsNotNone(complete)
                blob = self.git(self.root, "rev-parse", "HEAD:" + relative)
                obj = self.root / ".git/objects" / blob[:2] / blob[2:]
                saved = obj.read_bytes()
                obj.unlink()
                try:
                    self.assertEqual(self.git(self.root, "cat-file", "-t", revision), "commit")
                    self.assertEqual(self.git(self.root, "cat-file", "-t", revision + "^{tree}"), "tree")
                    self.assertIsNone(gate.semantic_digest(self.root, revision, ("surface.rs",)))
                finally:
                    obj.write_bytes(saved)
                self.assertEqual(gate.semantic_digest(self.root, revision, ("surface.rs",)), complete)

    def test_missing_semantic_tree_refuses_until_restored(self):
        revision = self.git(self.root, "rev-parse", "HEAD")
        complete = gate.semantic_digest(self.root, revision, ("surface.rs",))
        tree = self.git(self.root, "rev-parse", "HEAD^{tree}")
        obj = self.root / ".git/objects" / tree[:2] / tree[2:]
        saved = obj.read_bytes()
        obj.unlink()
        try:
            self.assertEqual(self.git(self.root, "cat-file", "-t", revision), "commit")
            self.assertIsNone(gate.semantic_digest(self.root, revision, ("surface.rs",)))
        finally:
            obj.write_bytes(saved)
        self.assertEqual(gate.semantic_digest(self.root, revision, ("surface.rs",)), complete)

    def test_unreadable_ratified_surface_never_uses_the_consumer_group_as_authority(self):
        relative = "crates/trust-ir/src/ty.rs"
        store = self.child(self.root, "first-party/trust-ir", {
            "Cargo.toml": '[package]\nname = "trust-ir"\nversion = "0.1.0"\n',
            relative: "pub const SURFACE: u8 = 1;\n",
        })
        anchor_blob = self.git(store, "rev-parse", "HEAD:" + relative)
        (store / relative).write_text("pub const SURFACE: u8 = 2;\n")
        self.git(store, "add", relative)
        self.git(store, "commit", "-qm", "different consumer source")
        consumer = self.git(store, "rev-parse", "HEAD")
        remote = Path(self.tmp.name) / "remote.git"
        self.git(store, "init", "-q", "--bare", "-b", "main", str(remote))
        self.git(store, "remote", "add", "origin", str(remote))
        self.git(store, "push", "-q", "origin", "main")
        (self.root / "Cargo.toml").write_text('[dependencies]\n' + DECL.replace("a" * 40, consumer))
        self.git(self.root, "add", "Cargo.toml")
        self.git(self.root, "commit", "-qm", "consume a published descendant without moving the anchor")
        obj = store / ".git/objects" / anchor_blob[:2] / anchor_blob[2:]
        saved = obj.read_bytes()
        obj.unlink()
        output = io.StringIO()
        try:
            with mock.patch.object(sys, "argv", ["check_ir_cohort.py", "--root", str(self.root)]), \
                    contextlib.redirect_stdout(output), contextlib.redirect_stderr(output):
                self.assertEqual(gate.main(), 1)
            self.assertIn("RATIFIED SURFACE UNREADABLE", output.getvalue())
            self.assertNotIn("   COHERENT:", output.getvalue())
        finally:
            obj.write_bytes(saved)

    def coherent_semantic_cohort(self):
        store = self.child(self.root, "first-party/trust-ir", {
            "Cargo.toml": '[package]\nname = "trust-ir"\nversion = "0.1.0"\n',
            "crates/trust-ir/src/ty.rs": "pub const SURFACE: u8 = 1;\n",
        })
        revision = self.git(store, "rev-parse", "HEAD")
        remote = Path(self.tmp.name) / "remote.git"
        self.git(store, "init", "-q", "--bare", "-b", "main", str(remote))
        self.git(store, "remote", "add", "origin", str(remote))
        self.git(store, "push", "-q", "origin", "main")
        (self.root / "Cargo.toml").write_text('[dependencies]\n' + DECL.replace("a" * 40, revision))
        self.git(self.root, "add", "Cargo.toml")
        self.git(self.root, "commit", "-qm", "consume the recorded published anchor")
        return revision

    def semantic_gate_result(self):
        output = io.StringIO()
        with mock.patch.object(sys, "argv", ["check_ir_cohort.py", "--root", str(self.root)]), \
                contextlib.redirect_stdout(output), contextlib.redirect_stderr(output):
            status = gate.main()
        return status, output.getvalue()

    def test_unreadable_superproject_tree_refuses_and_exact_restoration_passes(self):
        self.coherent_semantic_cohort()
        self.assertEqual(self.semantic_gate_result()[0], 0)
        revision = self.git(self.root, "rev-parse", "HEAD")
        tree = self.git(self.root, "rev-parse", "HEAD^{tree}")
        obj = self.root / ".git/objects" / tree[:2] / tree[2:]
        saved = obj.read_bytes()
        obj.unlink()
        try:
            self.assertEqual(self.git(self.root, "cat-file", "-t", revision), "commit")
            status, output = self.semantic_gate_result()
            self.assertEqual(status, 2)
            self.assertIn("RATIFIED ANCHOR UNREADABLE", output)
            self.assertNotIn("COHERENT", output)
        finally:
            obj.write_bytes(saved)
        self.assertEqual(self.semantic_gate_result()[0], 0)

    def test_missing_ratified_gitlink_refuses_instead_of_electing_a_consumer(self):
        revision = self.coherent_semantic_cohort()
        self.git(self.root, "update-index", "--force-remove", "first-party/trust-ir")
        self.git(self.root, "commit", "-qm", "remove only the recorded anchor")
        status, output = self.semantic_gate_result()
        self.assertEqual(status, 2)
        self.assertIn("RATIFIED ANCHOR MISSING", output)
        self.assertNotIn("COHERENT", output)
        self.git(self.root, "update-index", "--add", "--cacheinfo", f"160000,{revision},first-party/trust-ir")
        self.git(self.root, "commit", "-qm", "restore the exact recorded anchor")
        self.assertEqual(self.semantic_gate_result()[0], 0)

    def test_report_and_audited_exclusion_rules_are_preserved(self):
        child = self.child(self.root, "first-party/dep", {
            "Cargo.toml": '[dependencies]\n' + DECL,
            "reports/old/Cargo.toml": '[dependencies]\n' + DECL,
            "spikes/old/Cargo.toml": '[dependencies]\n' + DECL,
        })
        config = self.root / gate.EXCLUSIONS_PATH
        config.parent.mkdir(parents=True)
        config.write_text(json.dumps({"schema": gate.EXCLUSIONS_SCHEMA, "exclusions": [
            {"repository": "dep", "path": "spikes/old"},
        ]}))
        # Excluded snapshots are not read, even when absent on disk.
        (child / "reports/old/Cargo.toml").unlink()
        (child / "spikes/old/Cargo.toml").unlink()
        with contextlib.redirect_stdout(io.StringIO()):
            rows = gate.find_declarations(self.root)
        self.assertEqual([row.where for row in rows], ["first-party/dep/Cargo.toml"])
        self.assertEqual(gate.EXCLUDED_MANIFESTS, ["first-party/dep/spikes/old/Cargo.toml"])


class BatchedJudgmentTests(unittest.TestCase):
    """Every store's revisions are judged in one batch, stores in parallel,
    with remembered ancestry and one bound; the verdicts and the report are
    those of the one-at-a-time loop (2026-11-15). The date waivers are judged
    on is max(--date, the UTC date), never the local date or an environment
    variable."""

    git = ManifestInventoryTests.git
    repo = ManifestInventoryTests.repo
    child = ManifestInventoryTests.child

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(prefix="ir-judgment.")
        self.addCleanup(self.tmp.cleanup)
        self.base = Path(self.tmp.name).resolve()
        self.root = self.base / "root"
        self.repo(self.root, {"README": "root\n"})

    def bare(self, name):
        remote = self.base / f"{name}.git"
        subprocess.run(["git", "init", "-q", "--bare", "-b", "main", str(remote)], check=True)
        return remote

    def declare(self, rel, repo, rev):
        path = self.root / rel
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(f'[dependencies]\nx = {{ git = "https://github.com/alabsystems/{repo}", rev = "{rev}" }}\n')
        self.git(self.root, "add", rel)
        self.git(self.root, "commit", "-qm", "declare " + rel)

    def undeclare(self, *rels):
        for rel in rels:
            self.git(self.root, "rm", "-q", f"{rel}/Cargo.toml")
        self.git(self.root, "commit", "-qm", "undeclare " + " ".join(rels))

    def commit(self, store, rel, text, message):
        (store / rel).parent.mkdir(parents=True, exist_ok=True)
        (store / rel).write_text(text)
        self.git(store, "add", rel)
        self.git(store, "commit", "-qm", message)
        return self.git(store, "rev-parse", "HEAD")

    def cohort(self, *, waiver=True, no_main=True):
        """A ratified anchor A, a waived divergence B, C (same surface as B,
        the remote's main), OFF-MAIN, ABSENT, and an ungated store whose remote
        publishes no main (NO_MAIN)."""
        surface = "crates/trust-ir/src/ty.rs"
        self.store = self.child(self.root, "first-party/trust-ir", {
            "Cargo.toml": '[package]\nname = "trust-ir"\nversion = "0.1.0"\n',
            surface: "pub const SURFACE: u8 = 1;\n",
        })
        a = self.git(self.store, "rev-parse", "HEAD")
        b = self.commit(self.store, surface, "pub const SURFACE: u8 = 2;\n", "B")
        c = self.commit(self.store, "README", "not surface\n", "C")
        self.remote = self.bare("trust-ir")
        self.git(self.store, "remote", "add", "origin", str(self.remote))
        self.git(self.store, "push", "-q", "origin", "main")
        self.git(self.store, "checkout", "-q", "-b", "fork", a)
        fork = self.commit(self.store, surface, "pub const SURFACE: u8 = 99;\n", "FORK")
        self.git(self.store, "checkout", "-q", "main")
        self.revs = {"A": a, "B": b, "C": c, "FORK": fork, "ABSENT": "0123456789abcdef" * 2 + "01234567"}
        self.declare("a/Cargo.toml", "trust-ir", a)
        self.declare("b/Cargo.toml", "trust-ir", b)
        self.declare("c/Cargo.toml", "trust-ir", c)
        self.declare("f/Cargo.toml", "trust-ir", fork)
        self.declare("u/Cargo.toml", "trust-ir", self.revs["ABSENT"])
        if no_main:
            clean = self.child(self.root, "first-party/clean", {"README": "clean\n"})
            clean_remote = self.bare("clean")
            self.git(clean, "remote", "add", "origin", str(clean_remote))
            self.git(clean, "push", "-q", "origin", "main:dev")
            self.declare("k/Cargo.toml", "clean", self.git(clean, "rev-parse", "HEAD"))
        if waiver:
            self.write_waiver(self.digest("B"), datetime.date(2099, 1, 1))
        return self.revs

    def digest(self, name):
        return gate.semantic_digest(self.store, self.revs[name], gate.SEMANTIC_SURFACE["trust-ir"])

    def write_waiver(self, digest, expires):
        path = self.root / gate.WAIVER_PATH
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(f"trust-ir | {digest} | {expires.isoformat()} | test | fixture\n")

    def run_gate(self, *argv, env=None):
        out, err = io.StringIO(), io.StringIO()
        with mock.patch.object(sys, "argv", ["check_ir_cohort.py", "--root", str(self.root), *argv]), \
                mock.patch.dict(os.environ, env or {}), \
                contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
            status = gate.main()
        return status, out.getvalue(), err.getvalue()

    def test_batched_judgment_matches_one_at_a_time_and_asks_each_store_once(self):
        revs = self.cohort()
        rt = gate.rt
        original_batch, original_one = rt.RemoteTips.judge_many, rt.RemoteTips._judge_many
        asked = []

        def counting(tips, path, shas, scope):
            asked.append((str(path), tuple(shas), scope))
            return original_one(tips, path, shas, scope)

        def one_at_a_time(tips, path, shas, *, scope="durable"):
            verdicts = {}
            for sha in shas:
                verdicts.update(original_batch(tips, path, [sha], scope=scope))
            return verdicts

        original_inventory = rt.RemoteTips.inventory
        scopes = []

        def recording(tips, path, **kwargs):
            scopes.append(kwargs.get("scope", "durable"))
            return original_inventory(tips, path, **kwargs)

        with mock.patch.object(gate, "ancestry_memory_dir", return_value=None), \
                mock.patch.object(rt.RemoteTips, "_judge_many", counting), \
                mock.patch.object(rt.RemoteTips, "inventory", recording):
            batched = self.run_gate()
        # warm and judge_many ask one main-scope inventory (witnessing main
        # alone for a GitHub remote; IR-COHORT-MAIN-WITNESS-1).
        self.assertEqual(set(scopes), {"main"}, scopes)
        stores = [path for path, _shas, _scope in asked]
        self.assertEqual(len(stores), 2, asked)
        self.assertEqual(len(set(stores)), 2, "one batch per store")
        self.assertTrue(all(scope == "main" for _p, _s, scope in asked))
        trust_ir = next(shas for path, shas, _ in asked if path.endswith("trust-ir"))
        self.assertEqual(set(trust_ir), set(revs.values()))  # the anchor A rides in the same batch
        with mock.patch.object(gate, "ancestry_memory_dir", return_value=None), \
                mock.patch.object(rt.RemoteTips, "judge_many", one_at_a_time):
            serial = self.run_gate()
        self.assertEqual(batched[:2], serial[:2])
        status, output, _ = batched
        self.assertEqual(status, 1, output)
        self.assertIn(f"trust-ir@{revs['FORK'][:8]}: OFF-MAIN", output)
        self.assertIn(f"trust-ir@{revs['ABSENT'][:8]}: UNRESOLVABLE", output)
        self.assertIn("CONTAINMENT UNRESOLVED", output)
        self.assertIn("   waived  ", output)
        self.assertNotIn(f"trust-ir@{revs['C'][:8]}", output.split("IR COHORT INCOHERENT")[1])
        self.assertIn("IR COHORT PHASES: inventory ", batched[2])
        # The one commit fetch is ABSENT's. These literal local remotes'
        # `git ls-remote` witnesses no tip, natively or otherwise.
        self.assertIn(" 1 commit fetch(es); ", batched[2])
        self.assertIn(" witnessing 0 tip(s) as commits (0 of them by 0 native read(s)), ", batched[2])
        self.assertIn("; 0 revision(s) UNJUDGED; ", batched[2])

    def test_parallel_stores_with_one_revision_and_different_mains_keep_their_own_verdicts(self):
        revs = self.cohort(waiver=False, no_main=False)
        twin = self.root / "first-party/ty"
        subprocess.run(["git", "clone", "-q", str(self.store), str(twin)], check=True)
        self.git(twin, "checkout", "-q", revs["C"])
        self.git(self.root, "update-index", "--add", "--cacheinfo", f"160000,{revs['C']},first-party/ty")
        self.git(self.root, "commit", "-qm", "twin store")
        twin_remote = self.bare("ty")
        self.git(twin, "remote", "set-url", "origin", str(twin_remote))
        self.git(twin, "push", "-q", "origin", revs["A"] + ":refs/heads/main")
        self.undeclare("a", "b", "f", "u")
        self.declare("t/Cargo.toml", "ty", revs["C"])
        status, output, _ = self.run_gate()
        self.assertEqual(status, 1, output)
        self.assertIn(f"ty@{revs['C'][:8]}: OFF-MAIN", output)
        self.assertNotIn(f"trust-ir@{revs['C'][:8]}: OFF-MAIN", output)

    def test_a_second_run_remembers_and_a_rewound_main_is_asked_afresh(self):
        revs = self.cohort(no_main=False)  # C shares B's waived surface
        self.undeclare("b", "f", "u")
        memory = self.root / ".git/trust-land/commit-ancestry"
        self.assertEqual(gate.ancestry_memory_dir(self.root), memory)
        first = self.run_gate()
        second = self.run_gate()
        self.assertEqual((first[0], second[0]), (0, 0), first[1])
        self.assertEqual(first[1], second[1])
        self.assertIn(" 0 remembered answer(s)", first[2])
        self.assertRegex(second[2], r" [1-9][0-9]* remembered answer\(s\)")
        self.assertTrue((memory / gate.rt.AncestryMemory.FORMAT).is_dir())
        # A rewound main: C was remembered as contained in the old tip only.
        self.git(self.remote, "update-ref", "refs/heads/main", revs["A"])
        status, output, _ = self.run_gate()
        self.assertEqual(status, 1, output)
        self.assertIn(f"trust-ir@{revs['C'][:8]}: OFF-MAIN", output)

    def test_a_memo_under_another_format_is_ignored(self):
        revs = self.cohort(waiver=False, no_main=False)
        self.undeclare("b", "c", "u")
        tip, fork = revs["C"], revs["FORK"]
        memory = self.root / ".git/trust-land/commit-ancestry"
        # Answers written under an older or other contract (the bare `v1` of
        # 2026-11-13, another Agh schema or scope) never answer for this one.
        for other in ("v1", "v1-agh2-commit-parent-ancestry-only-v1", "v1-agh1-another-scope"):
            self.assertNotEqual(other, gate.rt.AncestryMemory.FORMAT)
            forged = memory / other / fork[:2] / f"{fork}-{tip}"
            forged.parent.mkdir(parents=True, exist_ok=True)
            forged.write_text("contained\n")
        status, output, _ = self.run_gate()
        self.assertEqual(status, 1, output)
        self.assertIn(f"trust-ir@{fork[:8]}: OFF-MAIN", output)
        # Control: the same file under the current FORMAT is read (the trusted
        # class docs/DECISION_QUEUE.md REACH-MEMO-1 names), so the files above
        # sat where a memo would be found.
        current = memory / gate.rt.AncestryMemory.FORMAT / fork[:2] / f"{fork}-{tip}"
        self.assertEqual(current.read_text(), "not-contained\n")
        current.write_text("contained\n")
        status, output, _ = self.run_gate()
        self.assertNotIn("OFF-MAIN", output)
        self.assertIn(f"schema {self.digest('FORK')} diverges", output)

    def test_the_native_reply_contract_names_the_memory_format(self):
        rt = gate.rt
        self.assertEqual(rt.AncestryMemory.FORMAT,
                         f"v1-agh{rt.NATIVE_ANCESTRY_SCHEMA}-{rt.NATIVE_ANCESTRY_SCOPE}")
        self.assertEqual((rt.NATIVE_ANCESTRY_SCHEMA, rt.NATIVE_ANCESTRY_SCOPE),
                         (1, "commit-parent-ancestry-only-v1"))

    def test_a_spent_time_bound_leaves_every_revision_unjudged(self):
        revs = self.cohort(waiver=False)
        status, output, err = self.run_gate("--time-bound", "0")
        self.assertEqual(status, 2, output + err)
        self.assertNotRegex(output, r"OFF-MAIN|UNRESOLVABLE|CONTAINMENT UNRESOLVED|COHERENT|waived")
        rows = re.findall(r"^  \* (\S+)@([0-9a-f]{8}): (?:RATIFIED ANCHOR )?COULD NOT RUN", output, re.M)
        expected = {("trust-ir", rev[:8]) for rev in revs.values()}
        self.assertTrue(expected <= set(rows), rows)
        self.assertEqual(len(rows), len(expected) + 1, rows)  # the clean revision too
        self.assertIn("time bound", output)
        # Exit 1 would hide COULD NOT RUN behind a finding; the phase line
        # counts it whatever the exit.
        self.assertIn(f"; {len(rows)} revision(s) UNJUDGED; ", err)

    def test_waivers_are_judged_on_max_of_argv_and_utc_date_never_the_environment(self):
        self.cohort(no_main=False)
        self.undeclare("f", "u")
        today = gate.utc_today()
        day = datetime.timedelta(days=1)
        self.write_waiver(self.digest("B"), today - day)
        past = (today - 3 * day).isoformat()
        for argv, env in (((), {"TRUST_GATE_DATE": past}), (("--date", past), {"TRUST_GATE_DATE": past})):
            with self.subTest(argv=argv, env=env):
                status, output, _ = self.run_gate(*argv, env=env)
                self.assertEqual(status, 1, output)
                self.assertIn("EXPIRED", output)
        self.write_waiver(self.digest("B"), today + 2 * day)
        self.assertEqual(self.run_gate()[0], 0)
        status, output, _ = self.run_gate("--date", (today + 5 * day).isoformat())
        self.assertEqual(status, 1, output)
        self.assertIn("EXPIRED", output)
        with mock.patch.object(gate, "utc_today", return_value=today + 3 * day):
            status, output, _ = self.run_gate("--date", today.isoformat())
        self.assertEqual(status, 1, output)
        self.assertIn("EXPIRED", output)
        self.assertEqual(gate.judged_date(None), gate.utc_today())
        for bad in ("2026-1-5", "tomorrow", "2026-02-30"):
            with self.subTest(bad=bad), self.assertRaises(SystemExit):
                self.run_gate("--date", bad)

    def test_a_waiver_is_judged_on_the_date_after_the_remote_phase(self):
        # Review 1: the date was read at the run's start, before up to the
        # time bound of remote work, so a run crossing midnight still honoured
        # a waiver that expired at midnight. The clock here turns over once
        # the remote phase has judged anything.
        self.cohort(no_main=False)
        self.undeclare("f", "u")
        today = gate.utc_today()
        self.write_waiver(self.digest("B"), today)
        self.assertEqual(self.run_gate()[0], 0, "a waiver expiring today still holds today")
        judged = {"remote": False}
        original = gate.rt.RemoteTips.judge_many

        def judge_many(tips, *args, **kwargs):
            judged["remote"] = True
            return original(tips, *args, **kwargs)
        with mock.patch.object(gate.rt.RemoteTips, "judge_many", judge_many), \
                mock.patch.object(gate, "utc_today",
                                  lambda: today + datetime.timedelta(days=1) if judged["remote"] else today):
            status, output, _ = self.run_gate("--date", today.isoformat())
        self.assertTrue(judged["remote"])
        self.assertEqual(status, 1, output)
        self.assertIn("EXPIRED", output)

    def test_a_time_bound_that_bounds_nothing_is_refused(self):
        self.cohort(waiver=False)
        for bad in ("nan", "inf", "-inf", "-1", "soon"):
            with self.subTest(bad=bad), self.assertRaises(SystemExit):
                self.run_gate("--time-bound", bad)
        self.assertEqual(gate.time_bound_seconds("0"), 0.0)
        self.assertEqual(gate.time_bound_seconds("900"), 900.0)

    def test_the_local_time_zone_never_moves_the_judged_date(self):
        self.cohort(no_main=False)
        self.undeclare("f", "u")
        saved = os.environ.get("TZ")

        def restore():
            if saved is None:
                os.environ.pop("TZ", None)
            else:
                os.environ["TZ"] = saved
            time.tzset()
        self.addCleanup(restore)
        # UTC-12 and UTC+14: at every hour one of them names another local
        # date than UTC's, so a local-date judgment fails one case below.
        for zone in ("Etc/GMT+12", "Etc/GMT-14"):
            os.environ["TZ"] = zone
            time.tzset()
            today = gate.utc_today()
            for expires, want in ((today, 0), (today - datetime.timedelta(days=1), 1)):
                with self.subTest(zone=zone, expires=expires):
                    self.write_waiver(self.digest("B"), expires)
                    self.assertEqual(self.run_gate()[0], want)


if __name__ == "__main__":
    unittest.main()
