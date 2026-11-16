#!/bin/sh
""":"
for candidate in python3.14 python3.13 python3.12 python3.11 python3; do
    if command -v "$candidate" >/dev/null 2>&1 \
        && "$candidate" -c 'import sys; raise SystemExit(sys.version_info < (3, 11))' 2>/dev/null; then
        exec "$candidate" "$0" "$@"
    fi
done
echo "freeze_toolchain_sources_test.py requires Python 3.11+ (tomllib)" >&2
exit 2
":"""
import os as _floor_os
import shutil as _floor_shutil
import sys as _floor_sys

# Trust: python floor, second half. `python3 freeze_toolchain_sources_test.py` reads the sh block above
# as a string, so an old `python3` (3.9 on macOS CommandLineTools) re-execs here.
if __name__ == "__main__" and _floor_sys.version_info < (3, 11):
    for _floor_candidate in ("python3.14", "python3.13", "python3.12", "python3.11"):
        _floor_path = _floor_shutil.which(_floor_candidate)
        if _floor_path:
            _floor_argv = [_floor_path, _floor_os.path.abspath(__file__), *_floor_sys.argv[1:]]
            _floor_os.execv(_floor_path, _floor_argv)
    _floor_sys.exit("freeze_toolchain_sources_test.py requires Python 3.11+ (tomllib); none found on PATH")
__doc__ = """Committed std-source closure, normalization and confinement controls."""
import importlib.util
from pathlib import Path
import subprocess
import runpy
import shutil
import sys
import tempfile
import tomllib
import unittest
from unittest import mock


SCRIPT = Path(__file__).resolve().parents[1] / "freeze_toolchain_sources.py"
SPEC = importlib.util.spec_from_file_location("freeze_toolchain_sources", SCRIPT)
freeze = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(freeze)


def git(root, *args):
    return subprocess.check_output(["git", "-C", str(root), *args], text=True,
                                   stderr=subprocess.DEVNULL).strip()


def init(root):
    root.mkdir(parents=True, exist_ok=True)
    subprocess.run(["git", "init", "-q", str(root)], check=True)
    git(root, "config", "user.name", "Source fixture")
    git(root, "config", "user.email", "fixture@example.invalid")
    git(root, "config", "core.hooksPath", "/dev/null")
    git(root, "config", "commit.gpgsign", "false")


def write(root, relative, text):
    path = root / relative
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text)
    return path


class FrozenSourcesTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix="freeze-sources-")
        self.root = Path(self.temporary.name).resolve()
        self.repo = self.repository(self.root / "repo", gitlink=True)
        self.commit = git(self.repo, "rev-parse", "HEAD")
        self.output = self.root / "output"
        self.output.mkdir()

    def tearDown(self):
        self.temporary.cleanup()

    def repository(self, root, gitlink):
        init(root)
        write(root, "library/core/src/lib.rs", "recorded std source\n")
        write(root, "compiler/rustc_driver/src/lib.rs", "recorded compiler source\n")
        write(root, "Cargo.toml", '[workspace.package]\nversion = "0.11.0"\n'
              'edition = "2021"\nlicense = "MIT"\nauthors = ["Source fixture"]\n')
        write(root, "crates/trust-bignum/Cargo.toml", '[package]\nname = "trust-bignum"\n'
              'version.workspace = true\nedition.workspace = true\nlicense.workspace = true\n'
              'authors.workspace = true\n[lints]\nworkspace = true\n'
              '[dev-dependencies]\nclean-kernel.workspace = true\n'
              '[features]\nrustc-dep-of-std = ["dep:core"]\n'
              '[dependencies.core]\nversion = "1.0.0"\noptional = true\n'
              'package = "rustc-std-workspace-core"\n')
        write(root, "crates/trust-bignum/src/lib.rs", "recorded bignum source\n")
        write(root, "crates/trust-memchr/Cargo.toml", '[package]\nname = "memchr"\n'
              'version = "2.8.3"\nedition = "2021"\n')
        write(root, "crates/trust-memchr/src/lib.rs", "recorded memchr source\n")
        if gitlink:
            llvm = self.root / (root.name + "-llvm")
            init(llvm)
            write(llvm, "libunwind/src/fixture.c", "recorded unwind source\n")
            git(llvm, "add", ".")
            git(llvm, "commit", "-qm", "recorded LLVM")
            git(root, "-c", "protocol.file.allow=always", "submodule", "add", "-q",
                str(llvm), "src/llvm-project")
            for key, value in (("user.name", "Source fixture"), ("user.email", "fixture@example.invalid"),
                               ("core.hooksPath", "/dev/null"), ("commit.gpgsign", "false")):
                git(root / "src/llvm-project", "config", key, value)
        else:
            write(root, "src/llvm-project/libunwind/src/fixture.c", "recorded vendored unwind\n")
        git(root, "add", ".")
        git(root, "commit", "-qm", "recorded source closure")
        return root

    def test_exact_commit_and_gitlink_ignore_live_worktree_changes(self):
        write(self.repo, "library/core/src/lib.rs", "live std mutation\n")
        workspace = write(self.repo, "Cargo.toml", '[workspace.package]\nversion = "999.0.0"\n')
        leaf = write(self.repo, "crates/trust-bignum/src/lib.rs", "live bignum mutation\n")
        llvm = self.repo / "src/llvm-project"
        write(llvm, "libunwind/src/fixture.c", "live LLVM mutation\n")
        git(llvm, "add", ".")
        git(llvm, "commit", "-qm", "newer LLVM worktree")
        result = freeze.freeze(self.repo, self.commit, self.output)
        self.assertEqual(result["source_commit"], self.commit)
        self.assertNotEqual(result["llvm_gitlink"], git(llvm, "rev-parse", "HEAD"))
        self.assertEqual((self.output / "library/core/src/lib.rs").read_text(), "recorded std source\n")
        self.assertEqual((self.output / "crates/trust-bignum/src/lib.rs").read_text(), "recorded bignum source\n")
        self.assertEqual((self.output / "src/llvm-project/libunwind/src/fixture.c").read_text(),
                         "recorded unwind source\n")
        manifest = tomllib.loads((self.output / "crates/trust-bignum/Cargo.toml").read_text())
        self.assertEqual(manifest["package"]["version"], "0.11.0")
        self.assertNotIn("lints", manifest)
        self.assertNotIn("dev-dependencies", manifest)
        self.assertEqual(manifest["features"]["rustc-dep-of-std"], ["dep:core"])
        self.assertEqual(manifest["dependencies"]["core"]["package"], "rustc-std-workspace-core")
        self.assertEqual(leaf.read_text(), "live bignum mutation\n")
        self.assertIn("999.0.0", workspace.read_text())

    def test_cli_preserves_clean_checkout_without_bytecode_flag(self):
        for relative in ("scripts/freeze_toolchain_sources.py",
                         "src/tools/trust-stage0-dist/prepare.py",
                         "src/tools/trust-stage0-dist/bootstrap_steps.py"):
            source = SCRIPT.parent.parent / relative
            destination = self.repo / relative
            destination.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(source, destination)
        git(self.repo, "add", ".")
        git(self.repo, "commit", "-qm", "source freezer and TOML owner")
        result = subprocess.run(
            [sys.executable, "-I", str(self.repo / "scripts/freeze_toolchain_sources.py"),
             str(self.repo), "HEAD", str(self.output)], capture_output=True, text=True)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(git(self.repo, "status", "--porcelain"), "")
        self.assertFalse(list(self.repo.rglob("__pycache__")))

    def test_vendored_libunwind_source_is_supported(self):
        repository = self.repository(self.root / "vendored", gitlink=False)
        result = freeze.freeze(repository, "HEAD", self.output)
        self.assertIsNone(result["llvm_gitlink"])
        self.assertEqual((self.output / "src/llvm-project/libunwind/src/fixture.c").read_text(),
                         "recorded vendored unwind\n")

    def test_missing_recorded_llvm_object_store_is_refused(self):
        llvm = self.repo / "src/llvm-project"
        llvm.rename(self.root / "retained-llvm")
        llvm.mkdir()
        with self.assertRaisesRegex(freeze.Refused, "object store is not initialized"):
            freeze.freeze(self.repo, self.commit, self.output)

    def test_missing_inherited_package_default_is_refused(self):
        with self.assertRaisesRegex(freeze.Refused, "without a committed default"):
            freeze.normalize_manifest('[package]\nname="leaf"\nversion.workspace=true\n', {}, None)

    def test_remaining_workspace_dependency_is_refused_before_serialization(self):
        writer = mock.Mock(side_effect=AssertionError("must refuse before serialization"))
        with self.assertRaisesRegex(freeze.Refused, "still inherits"):
            freeze.normalize_manifest('[package]\nname="leaf"\n'
                                      '[dependencies]\nforeign.workspace=true\n', {}, writer)
        writer.assert_not_called()

    def test_serializer_cannot_change_manifest_meaning(self):
        with self.assertRaisesRegex(freeze.Refused, "changed meaning"):
            freeze.normalize_manifest('[package]\nname="leaf"\n', {},
                                      lambda _value: '[package]\nname="other"\n')

    def test_committed_source_symlink_is_refused_without_following_it(self):
        outside = write(self.root, "outside", "untouched\n")
        (self.repo / "compiler/escape").symlink_to(outside)
        git(self.repo, "add", "compiler/escape")
        git(self.repo, "commit", "-qm", "source link negative control")
        with self.assertRaisesRegex(freeze.Refused, "link or special file"):
            freeze.freeze(self.repo, "HEAD", self.output)
        self.assertEqual(outside.read_text(), "untouched\n")

    def test_nonempty_output_is_retained(self):
        sentinel = write(self.output, "sentinel", "retained\n")
        with self.assertRaisesRegex(freeze.Refused, "not empty"):
            freeze.freeze(self.repo, self.commit, self.output)
        self.assertEqual(sentinel.read_text(), "retained\n")

    def test_destination_parent_symlink_is_refused(self):
        link = self.root / "alias"
        link.symlink_to(self.root, target_is_directory=True)
        with self.assertRaisesRegex(freeze.Refused, "traverses a link"):
            freeze.freeze(self.repo, self.commit, link / "output")
        self.assertFalse(any(self.output.iterdir()))

    def test_missing_supported_source_parser_refuses_before_any_snapshot(self):
        with mock.patch.dict(sys.modules, {"tomllib": None}), \
                mock.patch("shutil.which", return_value=None):
            with self.assertRaisesRegex(SystemExit, "requires Python 3.11"):
                runpy.run_path(str(SCRIPT), run_name="__main__")
        self.assertFalse(any(self.output.iterdir()))


if __name__ == "__main__":
    unittest.main()
