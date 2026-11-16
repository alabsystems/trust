#!/usr/bin/env python3
"""Real Git controls for recursive source stamps; no bootstrap/tool execution."""

import importlib.util
import ast
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch


REPO = Path(__file__).resolve().parents[2]
# macOS temp dirs live under the /var -> /private/var symlink, and the code
# under test canonicalizes paths; compare like with like.
tempfile.tempdir = os.path.realpath(tempfile.gettempdir())
SPEC = importlib.util.spec_from_file_location(
    "trust_build_provenance", REPO / "scripts/lib/trust_build_provenance.py")
provenance = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = provenance
SPEC.loader.exec_module(provenance)


class BuildSourceProvenanceTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix="trust-build-stamp-")
        self.addCleanup(self.temporary.cleanup)
        self.base = Path(self.temporary.name)
        self.root = self.base / "source"
        self.parent = self.base / "parent"
        self.leaf = self.base / "leaf"
        self.output = self.base / "build"
        for repo in (self.root, self.parent, self.leaf):
            repo.mkdir()
            self.git(repo, "init", "-q")
            self.git(repo, "config", "user.name", "Provenance fixture")
            self.git(repo, "config", "user.email", "fixture@example.invalid")
            (repo / "tracked").write_text("original\n")
            self.git(repo, "add", "tracked")
            self.git(repo, "commit", "-qm", "initial")
        self.leaf_pin = self.git(self.leaf, "rev-parse", "HEAD")
        self.git(self.leaf, "commit", "-qm", "later", "--allow-empty")
        self.later_leaf = self.git(self.leaf, "rev-parse", "HEAD")
        self.git(self.parent, "-c", "protocol.file.allow=always", "submodule", "add",
                 "-q", str(self.leaf), "third_party/leaf")
        self.git(self.parent / "third_party/leaf", "checkout", "-q", "--detach", self.leaf_pin)
        self.git(self.parent, "add", ".gitmodules", "third_party/leaf")
        self.git(self.parent, "commit", "-qm", "leaf pin")
        self.git(self.root, "-c", "protocol.file.allow=always", "submodule", "add",
                 "-q", str(self.parent), "first-party/parent")
        self.git(self.root, "commit", "-qam", "parent pin")
        self.checkout = self.root / "first-party/parent"
        self.nested = self.checkout / "third_party/leaf"
        self.head = self.git(self.root, "rev-parse", "HEAD")

    def git(self, root, *arguments):
        return subprocess.run(["git", *arguments], cwd=root, capture_output=True,
                              text=True, check=True, timeout=20).stdout.strip()

    def initialise(self):
        self.git(self.root, "-c", "protocol.file.allow=always", "submodule",
                 "update", "-q", "--init", "--recursive")

    def owner(self):
        return provenance.BuildStamp(self.root, self.output, ["build", "--stage", "2"])

    def completed(self):
        self.initialise()
        owner = self.owner()
        owner.start()
        owner.finish("ok")
        return owner, provenance.validate_record(owner.path.read_text(), self.head)

    def test_missing_nested_source_refuses_despite_unchanged_top_level_census(self):
        top_level = self.git(self.root, "submodule", "status")
        with self.assertRaisesRegex(provenance.ProvenanceError, "uninitialized"):
            provenance.source_facts(self.root)
        self.initialise()
        self.assertEqual(self.git(self.root, "submodule", "status"), top_level)
        facts, annotation = provenance.source_facts(self.root)
        self.assertEqual(facts["recursive_submodule_count"], "2")
        self.assertEqual(facts["submodule_census_scope"], provenance.CENSUS_SCOPE)
        self.assertEqual(facts["tree_state"], "clean")
        self.assertIn("first-party/parent/third_party/leaf", annotation)

    def test_complete_start_finish_and_admission_use_same_identity(self):
        owner, fields = self.completed()
        provenance.require_recursive_source(fields, self.root)
        before = owner.path.read_bytes()
        owner.finish("failed")
        self.assertEqual(owner.path.read_bytes(), before, "finish must be idempotent")

    def test_new_failed_census_invalidates_previous_completed_stamp(self):
        owner, _ = self.completed()
        self.git(self.checkout, "submodule", "deinit", "-q", "--", "third_party/leaf")
        replacement = self.owner()
        with self.assertRaisesRegex(provenance.ProvenanceError, "uninitialized"):
            replacement.start()
        replacement.finish("ok")
        with self.assertRaisesRegex(provenance.ProvenanceError, "incomplete"):
            provenance.validate_record(owner.path.read_text(), self.head)

    def test_unreadable_census_does_not_hash_empty_or_reuse_old_evidence(self):
        self.completed()
        replacement = self.owner()
        original = provenance._git

        def unreadable(root, *arguments):
            if root == self.nested and arguments[:1] == ("status",):
                raise provenance.ProvenanceError("injected nested status failure")
            return original(root, *arguments)

        with patch.object(provenance, "_git", side_effect=unreadable):
            with self.assertRaisesRegex(provenance.ProvenanceError, "nested status failure"):
                replacement.start()
        with self.assertRaisesRegex(provenance.ProvenanceError, "incomplete"):
            provenance.validate_record(replacement.path.read_text(), self.head)

    def test_failed_invalidation_is_an_error_before_source_census(self):
        self.output.mkdir()
        with patch.object(provenance, "_atomic_text", side_effect=OSError("read only")):
            with patch.object(provenance, "source_facts") as census:
                with self.assertRaisesRegex(OSError, "read only"):
                    self.owner()
                census.assert_not_called()

    def test_nested_staged_drift_checks_parent_commit_not_index(self):
        self.initialise()
        self.git(self.nested, "checkout", "-q", "--detach", self.later_leaf)
        self.git(self.checkout, "add", "third_party/leaf")
        with self.assertRaisesRegex(provenance.ProvenanceError, "committed pin"):
            provenance.source_facts(self.root)

    def test_parent_head_change_after_descendant_census_refuses(self):
        self.initialise()
        original = provenance._git

        def parent_changed(root, *arguments):
            result = original(root, *arguments)
            if root == self.root and arguments == ("submodule", "status"):
                self.git(self.root, "commit", "-qm", "concurrent parent commit", "--allow-empty")
            return result

        with patch.object(provenance, "_git", side_effect=parent_changed):
            with self.assertRaisesRegex(provenance.ProvenanceError, "HEAD changed"):
                provenance.source_facts(self.root)

    def test_diff_cannot_delegate_source_identity_to_external_driver(self):
        self.initialise()
        self.git(self.nested, "config", "diff.external", "/must-not-execute-provenance-diff")
        (self.nested / "tracked").write_text("changed source\n")
        facts, _ = provenance.source_facts(self.root)
        self.assertEqual(facts["tree_state"], "dirty")

    def test_submodule_ignore_all_cannot_hide_nested_dirty_content(self):
        self.initialise()
        before, _ = provenance.source_facts(self.root)
        self.git(self.root, "config", "submodule.first-party/parent.ignore", "all")
        self.git(self.checkout, "config", "submodule.third_party/leaf.ignore", "all")
        (self.nested / "tracked").write_text("changed while building\n")
        self.assertEqual(self.git(self.root, "status", "--porcelain"), "")
        after, _ = provenance.source_facts(self.root)
        self.assertEqual(after["tree_state"], "dirty")
        self.assertNotEqual(before["tree_fingerprint"], after["tree_fingerprint"])
        self.assertNotEqual(before["recursive_submodule_sha256"], after["recursive_submodule_sha256"])

    def test_nested_change_at_end_cannot_complete_clean(self):
        self.initialise()
        owner = self.owner()
        owner.start()
        (self.nested / "new-input").write_text("new source\n")
        owner.finish("ok")
        fields = provenance.validate_record(owner.path.read_text(), self.head)
        self.assertEqual(fields["tree_changed_during_build"], "YES")

    def test_missing_nested_source_at_end_cannot_complete(self):
        self.initialise()
        owner = self.owner()
        owner.start()
        self.git(self.checkout, "submodule", "deinit", "-q", "--", "third_party/leaf")
        owner.finish("ok")
        with self.assertRaisesRegex(provenance.ProvenanceError, "invalid fingerprint"):
            provenance.validate_record(owner.path.read_text(), self.head)

    def test_dirty_rename_status_is_counted_without_treating_second_path_as_record(self):
        self.initialise()
        self.git(self.nested, "mv", "tracked", "renamed file")
        facts, _ = provenance.source_facts(self.root)
        self.assertEqual(facts["tree_state"], "dirty")
        self.assertGreater(int(facts["dirty_tracked"]), 0)

    def test_legacy_fingerprint_keeps_its_exact_original_formula(self):
        import hashlib
        fields = dict(record_version="1", head="a" * 40,
                      diff_sha256="b" * 64, status_sha256="c" * 64,
                      submodule_sha256="d" * 64)
        expected = hashlib.sha256(("a" * 40 + "\n" + "b" * 64 + "\n" +
                                   "c" * 64 + "\n" + "d" * 64 + "\n").encode()).hexdigest()
        self.assertEqual(provenance.fingerprint(fields), expected)

    def x_functions(self):
        # Execute only the actual function definitions, never x.py's bootstrap
        # dispatch or candidate binaries. This covers the production wrapper.
        main = next(node for node in ast.parse((REPO / "x.py").read_text()).body
                    if isinstance(node, ast.If))
        functions = [node for node in main.body if isinstance(node, ast.FunctionDef)
                     and node.name in ("_trust_build_provenance_stamp", "_trust_build_provenance_finish")]
        self.assertEqual(len(functions), 2)
        namespace = dict(os=os, sys=sys, _prov={"owner": None})
        exec(compile(ast.Module(body=functions, type_ignores=[]), "x.py functions", "exec"), namespace)
        return namespace

    def test_x_entry_writes_v2_and_nonbuild_commands_stamp_nothing(self):
        self.initialise()
        namespace = self.x_functions()
        with patch.dict(sys.modules, {"scripts.lib.trust_build_provenance": provenance}):
            with patch.dict(os.environ, {"TRUST_BUILD_PROVENANCE_DIR": str(self.output),
                                         "TRUST_PREFLIGHT_ACTIVE": "0"}):
                namespace["_trust_build_provenance_stamp"](str(self.root), ["check"])
                self.assertFalse(self.output.exists())
                namespace["_trust_build_provenance_stamp"](str(self.root), ["build", "--stage", "2"])
                namespace["_trust_build_provenance_finish"]("ok")
        fields = provenance.validate_record((self.output / "trust-build-provenance").read_text(), self.head)
        self.assertEqual(fields["record_version"], "2")
        self.assertEqual(fields["submodule_census_scope"], provenance.CENSUS_SCOPE)

    def test_x_entry_invalidation_failure_stops_build(self):
        namespace = self.x_functions()
        with patch.dict(sys.modules, {"scripts.lib.trust_build_provenance": provenance}):
            with patch.dict(os.environ, {"TRUST_PREFLIGHT_ACTIVE": "0"}):
                with patch.object(provenance, "BuildStamp", side_effect=OSError("read only")):
                    with self.assertRaisesRegex(SystemExit, "refusing to build"):
                        namespace["_trust_build_provenance_stamp"](str(self.root), ["build"])
        self.assertIsNone(namespace["_prov"]["owner"])

    def test_x_entry_finds_its_record_writer_under_an_isolated_interpreter(self):
        # scripts/mint_and_prove_seed.sh runs `python -I -S x.py`: no script
        # directory on sys.path, and no sys.modules stand-in like the tests above.
        # Measured 2026-10-09: the first real mint stopped at this import.
        self.initialise()
        program = "\n".join((
            "import ast, os, sys",
            "rust_dir, output = sys.argv[1], sys.argv[2]",
            "source = open(os.path.join(rust_dir, 'x.py')).read()",
            "main = next(n for n in ast.parse(source).body if isinstance(n, ast.If))",
            "keep = ('_trust_build_provenance_stamp', '_trust_build_provenance_finish')",
            "body = [n for n in main.body if isinstance(n, ast.FunctionDef) and n.name in keep]",
            "namespace = dict(os=os, sys=sys, _prov={'owner': None})",
            "exec(compile(ast.Module(body=body, type_ignores=[]), 'x.py', 'exec'), namespace)",
            "os.environ['TRUST_BUILD_PROVENANCE_DIR'] = output",
            "os.environ['TRUST_PREFLIGHT_ACTIVE'] = '0'",
            "namespace['_trust_build_provenance_stamp'](rust_dir, ['build', '--stage', '2'])",
            "namespace['_trust_build_provenance_finish']('ok')",
        ))
        # rust_dir is this checkout (where scripts/lib lives); the record describes it.
        result = subprocess.run(
            [sys.executable, "-I", "-S", "-c", program, str(REPO), str(self.output)],
            cwd=self.base, capture_output=True, text=True, timeout=300,
            env={"PATH": os.environ.get("PATH", "/usr/bin:/bin"), "HOME": str(self.base)})
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertNotIn("No module named", result.stderr)
        record = (self.output / "trust-build-provenance").read_text()
        head = subprocess.run(["git", "rev-parse", "HEAD"], cwd=REPO, capture_output=True,
                              text=True, check=True).stdout.strip()
        self.assertIn(head, record)

    def test_record_reader_rejects_oversize_and_special_owners(self):
        record = self.base / "record"
        record.write_bytes(b"x" * 65537)
        with self.assertRaisesRegex(provenance.ProvenanceError, "oversized"):
            provenance.read_record(record)
        alias = self.base / "alias"
        alias.symlink_to(record)
        with self.assertRaisesRegex(provenance.ProvenanceError, "regular"):
            provenance.read_record(alias)
        with self.assertRaisesRegex(provenance.ProvenanceError, "regular"):
            provenance.read_record(self.root)


if __name__ == "__main__":
    unittest.main()
