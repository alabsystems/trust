"""Selected-seed runtime admission, without executing a seed or requiring Homebrew."""
import os as _floor_os
import shutil as _floor_shutil
import sys as _floor_sys

# Trust: python floor. The recreator re-execs itself under Python >= 3.11 (ensure_python_311) and
# its lane (scripts/check_bootstrap_script_tests.sh) runs this file under one, so these tests judge
# that interpreter. `python3 <this file>` on macOS CommandLineTools is 3.9, which has no
# `tarfile.data_filter`; there the recreator's admission refuses before inspection, and five tests
# measured that interpreter instead of the recreator's. Re-exec as the recreator does.
if __name__ == "__main__" and _floor_sys.version_info < (3, 11):
    for _floor_candidate in ("python3.14", "python3.13", "python3.12", "python3.11"):
        _floor_path = _floor_shutil.which(_floor_candidate)
        if _floor_path:
            _floor_argv = [_floor_path, _floor_os.path.abspath(__file__), *_floor_sys.argv[1:]]
            _floor_os.execv(_floor_path, _floor_argv)
    _floor_sys.exit("seed_runtime_prerequisite_test.py requires Python 3.11+; none found on PATH")

import contextlib
import hashlib
import importlib.util
import io
import json
from pathlib import Path
import sys
import subprocess
import tarfile
import tempfile
import unittest
from unittest.mock import patch

SCRIPT = Path(__file__).resolve().parents[1] / "recreate_bootstrap.py"
SPEC = importlib.util.spec_from_file_location("seed_runtime_recreator", SCRIPT)
bootstrap = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = bootstrap
SPEC.loader.exec_module(bootstrap)

HOST = "aarch64-apple-darwin"
VERSION = "0.12.0-trust"
NAME = f"targo-{VERSION}-{HOST}"
MEMBER = f"{NAME}/targo/bin/targo"
BINARY = b"\xcf\xfa\xed\xfe" + b"pinned fixture payload"


class SeedRuntimePrerequisiteTests(unittest.TestCase):
    def fixture(self, root, members=None):
        archive = root / "bootstrap/trust-stage0/dist/date" / f"{NAME}.tar.xz"
        archive.parent.mkdir(parents=True)
        with tarfile.open(archive, "w:xz") as bundle:
            for name, kind, payload in members or [(MEMBER, tarfile.REGTYPE, BINARY)]:
                member = tarfile.TarInfo(name)
                member.type = kind
                member.size = len(payload) if kind == tarfile.REGTYPE else 0
                member.linkname = "elsewhere" if kind != tarfile.REGTYPE else ""
                bundle.addfile(member, io.BytesIO(payload))
        (root / "src").mkdir()
        (root / "src/stage0").write_text(
            f"compiler_version={VERSION}\ncompiler_date=date\n"
            f"dist/date/{NAME}.tar.xz={hashlib.sha256(archive.read_bytes()).hexdigest()}\n"
        )
        return archive

    def check(self, root, capture):
        with patch.object(bootstrap, "which", return_value="/fixture/otool"), patch.object(
            bootstrap, "_capture_darwin_dynamic_dependencies", side_effect=capture
        ):
            return bootstrap.selected_seed_runtime_prereq(
                root, HOST, bootstrap.Stage0Selection("seed", None, None)
            )

    def test_hash_bound_archive_bytes_reach_dependency_inspection_without_execution(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            self.fixture(root)
            seen = []

            def capture(paths, tool):
                seen.append(paths[0].read_bytes())
                self.assertEqual(tool, Path("/fixture/otool"))
                return {"status": "ready", "dependencies": []}

            result = self.check(root, capture)
            self.assertTrue(result.ok)
            self.assertTrue(result.required)
            self.assertEqual(seen, [BINARY])

    def test_changed_archive_cannot_reach_runtime_inspection(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            archive = self.fixture(root)
            archive.write_bytes(archive.read_bytes() + b"changed")
            result = self.check(root, lambda *_: self.fail("unbound bytes inspected"))
            self.assertFalse(result.ok)
            self.assertIn("digest", result.detail)

    def test_missing_duplicate_and_linked_entrypoints_fail_closed(self):
        cases = [
            [("different", tarfile.REGTYPE, BINARY)],
            [(MEMBER, tarfile.REGTYPE, BINARY)] * 2,
            [(MEMBER, tarfile.SYMTYPE, b"")],
        ]
        for members in cases:
            with self.subTest(members=members), tempfile.TemporaryDirectory() as directory:
                root = Path(directory)
                self.fixture(root, members)
                result = self.check(root, lambda *_: self.fail("ambiguous entry inspected"))
                self.assertFalse(result.ok)
                self.assertRegex(result.detail, "one regular|duplicate")

    def test_non_macho_entrypoint_cannot_claim_a_resolved_runtime(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            self.fixture(root, [(MEMBER, tarfile.REGTYPE, b"not an executable")])
            result = self.check(root, lambda *_: self.fail("non-Mach-O inspected"))
            self.assertFalse(result.ok)

    def test_missing_or_unresolved_runtime_dependency_remains_a_required_refusal(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            self.fixture(root)
            missing = root / "not-installed/libgit2.dylib"

            def otool(argv, **kwargs):
                output = f"{argv[-1]}:\n"
                if "-L" in argv:
                    output += f"\t{missing} (compatibility version 1.9.0, current version 1.9.0)\n"
                return subprocess.CompletedProcess(argv, 0, stdout=output, stderr="")

            with patch.object(bootstrap, "which", return_value="/fixture/otool"), patch.object(
                bootstrap.subprocess, "run", side_effect=otool
            ):
                result = bootstrap.selected_seed_runtime_prereq(
                    root, HOST, bootstrap.Stage0Selection("seed", None, None)
                )
            self.assertTrue(result.required)
            self.assertFalse(result.ok)
            self.assertIn("libgit2", result.detail)

    def test_missing_dependency_inspector_refuses(self):
        with tempfile.TemporaryDirectory() as directory, patch.object(
            bootstrap, "which", return_value=None
        ):
            result = bootstrap.selected_seed_runtime_prereq(
                Path(directory), HOST, bootstrap.Stage0Selection("seed", None, None)
            )
            self.assertTrue(result.required)
            self.assertFalse(result.ok)
            self.assertIn("otool", result.detail)

    def test_bundled_loader_relative_library_is_inspected_in_its_original_layout(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            library_name = f"{NAME}/targo/lib/libfixture.dylib"
            self.fixture(root, [
                (MEMBER, tarfile.REGTYPE, BINARY),
                (library_name, tarfile.REGTYPE, BINARY + b"library"),
            ])
            inspected = []

            def otool(argv, **kwargs):
                binary = Path(argv[-1])
                output = f"{binary}:\n"
                if "-L" in argv:
                    inspected.append(binary.name)
                    if binary.name == "targo":
                        output += "\t@loader_path/../lib/libfixture.dylib (compatibility version 1.0.0, current version 1.0.0)\n"
                    else:
                        self.assertEqual(binary.read_bytes(), BINARY + b"library")
                return subprocess.CompletedProcess(argv, 0, stdout=output, stderr="")

            with patch.object(bootstrap, "which", return_value="/fixture/otool"), patch.object(
                bootstrap.subprocess, "run", side_effect=otool
            ):
                result = bootstrap.selected_seed_runtime_prereq(
                    root, HOST, bootstrap.Stage0Selection("seed", None, None)
                )
            self.assertTrue(result.ok, result.detail)
            self.assertEqual(inspected, ["targo", "libfixture.dylib"])

    def test_subtree_link_cannot_escape_into_another_component(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            self.fixture(root, [
                (MEMBER, tarfile.REGTYPE, BINARY),
                (f"{NAME}/targo/lib", tarfile.SYMTYPE, b""),
            ])
            # fixture's link target "elsewhere" is inside the component, so
            # rewrite the immutable archive with an actual escaping target.
            archive = root / "bootstrap/trust-stage0/dist/date" / f"{NAME}.tar.xz"
            with tarfile.open(archive, "w:xz") as bundle:
                binary = tarfile.TarInfo(MEMBER)
                binary.size = len(BINARY)
                bundle.addfile(binary, io.BytesIO(BINARY))
                link = tarfile.TarInfo(f"{NAME}/targo/lib")
                link.type = tarfile.SYMTYPE
                link.linkname = "../../other-component"
                bundle.addfile(link)
            pins = root / "src/stage0"
            lines = pins.read_text().splitlines()
            lines[-1] = f"dist/date/{NAME}.tar.xz={hashlib.sha256(archive.read_bytes()).hexdigest()}"
            pins.write_text("\n".join(lines) + "\n")
            result = self.check(root, lambda *_: self.fail("escaping link reached inspection"))
            self.assertFalse(result.ok)
            self.assertIn("escapes", result.detail)

    # TG16 (TG14's note): the preflight must pass on a Mac with no Homebrew, because the
    # pinned seed's Targo links only Apple system libraries. f067e72f4e1 pinned that with a
    # no-guessed-prefix test, which the merge that kept de30a0bbe1b dropped (43a71a1626e).
    # These restore it against the current runtime inspection, using the linkage recorded for
    # the pinned seed itself rather than a hand-written fixture.
    REPO = Path(__file__).resolve().parents[2]
    HOMEBREW_PREFIXES = ("/opt/homebrew", "/usr/local")

    def recorded_seed_linkage(self):
        """The pinned seed Targo's recorded `otool -L`, bound to the commit src/stage0 pins."""
        surface = json.loads(
            (self.REPO / "bootstrap/trust-stage0/host-proofs" / HOST / "seed-surface.json").read_text()
        )
        pinned = dict(
            line.split("=", 1)
            for line in (self.REPO / "src/stage0").read_text().splitlines()
            if "=" in line and not line.startswith("#")
        )
        self.assertEqual(
            surface["native_tool_pair"]["source_commit"],
            pinned["compiler_git_commit_hash"],
            "the recorded linkage must describe the seed src/stage0 pins; re-record it with the seed",
        )
        return surface["loader_evidence"]["targo"]

    def without_homebrew(self, linkage, probes, commands):
        """Run with no Homebrew on the machine: every probe under a Homebrew prefix answers
        absent and is recorded, `brew` is not on PATH, and `otool -L` prints `linkage`."""
        real = {name: getattr(Path, name) for name in ("exists", "is_file", "is_dir")}

        def guarded(name):
            def probe(path, *args, **kwargs):
                if str(path).startswith(self.HOMEBREW_PREFIXES):
                    probes.append((name, str(path)))
                    return False
                return real[name](path, *args, **kwargs)
            return probe

        def otool(argv, **kwargs):
            commands.append(list(argv))
            output = f"{argv[-1]}:\n"
            if "-L" in argv:
                output = linkage.replace("{seed}/bin/targo", argv[-1]) + "\n"
            return subprocess.CompletedProcess(argv, 0, stdout=output, stderr="")

        stack = contextlib.ExitStack()
        for name in real:
            stack.enter_context(patch.object(Path, name, guarded(name)))
        stack.enter_context(patch.object(
            bootstrap, "which", side_effect=lambda tool, *a, **k: "/fixture/otool" if tool == "otool" else None
        ))
        stack.enter_context(patch.object(bootstrap.subprocess, "run", side_effect=otool))
        return stack

    def test_pinned_seed_recorded_linkage_passes_without_homebrew(self):
        linkage = self.recorded_seed_linkage()
        self.assertNotIn("homebrew", linkage.lower())
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            self.fixture(root)
            probes, commands = [], []
            with self.without_homebrew(linkage, probes, commands):
                result = bootstrap.selected_seed_runtime_prereq(
                    root, HOST, bootstrap.Stage0Selection("seed", None, None)
                )
            self.assertTrue(result.ok, result.detail)
            self.assertTrue(result.required)
            self.assertIn("(0 non-system libraries)", result.detail)
            self.assertEqual(probes, [], "the preflight must not look for Homebrew at all")
            self.assertTrue(commands and all(Path(argv[0]).name == "otool" for argv in commands))

    def test_homebrew_linked_seed_is_refused_when_homebrew_is_absent(self):
        """Negative control: the check reads the seed's real dependencies. A seed that does
        link a Homebrew keg (the 2026-07-13 seed linked libgit2 1.9) is refused on a machine
        without it, by name; the preflight assumes Homebrew in neither direction."""
        keg = "/opt/homebrew/opt/libgit2/lib/libgit2.1.9.dylib"
        linkage = (
            "{seed}/bin/targo:\n"
            f"\t{keg} (compatibility version 1.9.0, current version 1.9.7)\n"
            "\t/usr/lib/libSystem.B.dylib (compatibility version 1.0.0, current version 1359.0.0)"
        )
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            self.fixture(root)
            probes, commands = [], []
            with self.without_homebrew(linkage, probes, commands):
                result = bootstrap.selected_seed_runtime_prereq(
                    root, HOST, bootstrap.Stage0Selection("seed", None, None)
                )
            self.assertTrue(result.required)
            self.assertFalse(result.ok)
            self.assertIn(f"non-system Darwin dependency is missing: {keg}", result.detail)


if __name__ == "__main__":
    unittest.main()
