#!/usr/bin/env python3
"""Focused filesystem/stamp controls; these are not compiler or proof checks."""
import contextlib
import hashlib
import io
import importlib.util
import json
import os
import stat
from pathlib import Path
import tempfile
import time
import unittest
from unittest.mock import patch

spec = importlib.util.spec_from_file_location("retain_stage1_emission", Path(__file__).parents[1] / "retain_stage1_emission.py")
retain = importlib.util.module_from_spec(spec)
spec.loader.exec_module(retain)
HOST = "aarch64-apple-darwin"
OTHER = "x86_64-apple-darwin"


class RetentionTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.base = Path(self.temp.name).resolve()
        self.root = self.base / "source"
        self.root.mkdir()
        self.output = self.base / "output"
        self.output.mkdir()
        self.fd = os.open(self.output, os.O_RDONLY | os.O_DIRECTORY)
        self.addCleanup(os.close, self.fd)
        self.addCleanup(self.temp.cleanup)

    def file(self, relative="build/producer/image", data=b"current emitted image"):
        path = self.root / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(data)
        return path

    def capture(self, path):
        return retain.retain_file(self.root, self.fd, path.relative_to(self.root), time.time_ns())

    def entries(self, fields, role="compiler1-std", target=OTHER):
        return retain.stamp_entries(self.root, HOST, target, role, b"\0".join(fields) + b"\0")

    def test_stamp_preserves_all_three_tags_and_generation(self):
        build = self.root / "build" / HOST / "stage1-std"
        fields = [b"h" + os.fsencode(build / "dist/deps/host.dylib"),
                  b"t" + os.fsencode(build / OTHER / "dist/deps/current.rlib"),
                  b"s" + os.fsencode(build / OTHER / "dist/self-contained/crt.o")]
        rows = self.entries(fields)
        self.assertEqual([row["dependency_tag"] for row in rows], ["h", "t", "s"])
        self.assertEqual({row["producer_role"] for row in rows}, {"compiler1-std"})
        rustc = self.root / "build" / HOST / "stage1-rustc" / HOST / "release/deps/compiler.rmeta"
        self.assertEqual(self.entries([b"t" + os.fsencode(rustc)], "compiler0-rustc", HOST)[0]["producer_role"], "compiler0-rustc")

    def test_rejects_unknown_empty_unterminated_tags(self):
        for raw in (b"", b"t/path", b"x/path\0", b"t/path\0\0"):
            with self.subTest(raw=raw), self.assertRaises(retain.Refusal):
                retain.stamp_entries(self.root, HOST, HOST, "compiler1-std", raw)

    def test_rejects_wrong_target_or_generation(self):
        path = self.root / "build" / HOST / "stage1-std" / HOST / "dist/deps/current.rlib"
        with self.assertRaises(retain.Refusal):
            self.entries([b"t" + os.fsencode(path)])
        with self.assertRaises(retain.Refusal):
            self.entries([b"t" + os.fsencode(path)], "compiler0-rustc", HOST)

    def test_rejects_host_tag_in_target_namespace(self):
        path = self.root / "build" / HOST / "stage1-std" / OTHER / "dist/deps/current.rlib"
        with self.assertRaises(retain.Refusal):
            self.entries([b"h" + os.fsencode(path)])

    def test_rejects_lexical_traversal_relative_and_duplicate_paths(self):
        parent = self.root / "build" / HOST / "stage1-std" / OTHER / "dist"
        for path in ("relative.rlib", str(parent / "../outside.rlib")):
            with self.subTest(path=path), self.assertRaises(retain.Refusal):
                self.entries([b"t" + os.fsencode(path)])
        field = b"t" + os.fsencode(parent / "deps/same.rlib")
        with self.assertRaises(retain.Refusal):
            self.entries([field, field])

    def test_retains_distinct_readonly_image_and_both_source_identities(self):
        path = self.file()
        path.chmod(0o755)
        record = self.capture(path)
        target = self.output / path.relative_to(self.root)
        self.assertEqual(target.read_bytes(), path.read_bytes())
        self.assertNotEqual(path.stat().st_ino, target.stat().st_ino)
        self.assertEqual(record["sha256"], hashlib.sha256(path.read_bytes()).hexdigest())
        self.assertEqual(record["source_physical_before"], record["source_physical_after"])
        self.assertEqual(target.stat().st_mode & 0o777, 0o555)

    def test_retains_sanctioned_build_noindex_source_alias(self):
        path = self.file("build.noindex/producer/image")
        (self.root / "build").symlink_to("build.noindex")
        logical = self.root / "build/producer/image"
        record = self.capture(logical)
        self.assertEqual(record["source_relative"], "build/producer/image")
        self.assertEqual((self.output / "build/producer/image").read_bytes(), path.read_bytes())
        self.assertEqual(record["sha256"], hashlib.sha256(path.read_bytes()).hexdigest())

    def test_direct_absolute_build_noindex_alias_retains_exact_source(self):
        path = self.file("build.noindex/producer/image")
        (self.root / "build").symlink_to(self.root / "build.noindex")
        row = self.capture(self.root / "build/producer/image")
        self.assertEqual(row["source_build_alias"]["target"], str(self.root / "build.noindex"))
        self.assertEqual((self.output / "build/producer/image").read_bytes(), path.read_bytes())

    def test_chained_build_alias_refuses_even_if_it_resolves_to_build_noindex(self):
        self.file("build.noindex/producer/image")
        (self.root / "redirect").symlink_to("build.noindex")
        (self.root / "build").symlink_to("redirect")
        with self.assertRaises(retain.Refusal):
            self.capture(self.root / "build/producer/image")
        self.assertEqual(list(self.output.iterdir()), [])

    def test_dot_traversal_build_alias_spellings_still_refuse(self):
        self.file("build.noindex/producer/image")
        (self.root / "piece").mkdir()
        for target in ("./build.noindex", "piece/../build.noindex", str(self.root / "piece") + "/../build.noindex"):
            with self.subTest(target=target):
                link = self.root / "build"
                link.symlink_to(target)
                with self.assertRaises(retain.Refusal):
                    self.capture(self.root / "build/producer/image")
                link.unlink()
        self.assertEqual(list(self.output.iterdir()), [])

    def test_physical_stamp_spelling_maps_only_the_sanctioned_build_role(self):
        (self.root / "build.noindex").mkdir()
        (self.root / "build").symlink_to("build.noindex")
        physical = self.root / "build.noindex" / HOST / "stage1-std" / OTHER / "dist/deps/current.rlib"
        row = self.entries([b"t" + os.fsencode(physical)])[0]
        self.assertEqual(row["path"], f"build/{HOST}/stage1-std/{OTHER}/dist/deps/current.rlib")
        with self.assertRaises(retain.Refusal):
            self.entries([b"h" + os.fsencode(physical)])

    def test_physical_stamp_spelling_without_the_build_alias_still_refuses(self):
        physical = self.root / "build.noindex" / HOST / "stage1-std" / OTHER / "dist/deps/current.rlib"
        with self.assertRaises(retain.Refusal):
            self.entries([b"t" + os.fsencode(physical)])

    def test_source_build_alias_refuses_other_or_aliased_physical_roots(self):
        self.file("other/producer/image")
        (self.root / "build").symlink_to("other")
        with self.assertRaises(retain.Refusal):
            self.capture(self.root / "build/producer/image")
        (self.root / "build").unlink()
        (self.root / "build.noindex").symlink_to("other")
        (self.root / "build").symlink_to("build.noindex")
        with self.assertRaises(retain.Refusal):
            self.capture(self.root / "build/producer/image")
        self.assertEqual(list(self.output.iterdir()), [])

    def test_nested_source_alias_beneath_build_noindex_still_refuses(self):
        self.file("build.noindex/saved/image")
        (self.root / "build.noindex/producer").symlink_to("saved")
        (self.root / "build").symlink_to("build.noindex")
        with self.assertRaises(OSError):
            self.capture(self.root / "build/producer/image")
        self.assertEqual(list(self.output.iterdir()), [])

    def test_source_build_alias_replacement_during_copy_refuses(self):
        self.file("build.noindex/producer/image")
        link = self.root / "build"
        link.symlink_to("build.noindex")
        original_fstat = os.fstat
        changed = False
        def replace(fd):
            nonlocal changed
            info = original_fstat(fd)
            if not changed and stat.S_ISREG(info.st_mode):
                changed = True
                link.rename(self.root / "saved-build-link")
                link.symlink_to("build.noindex")
            return info
        with patch.object(retain.os, "fstat", side_effect=replace), self.assertRaisesRegex(retain.Refusal, "source build alias changed"):
            self.capture(self.root / "build/producer/image")
        self.assertTrue(changed)

    def test_refuses_replaced_after_emission(self):
        path = self.file()
        with self.assertRaises(retain.Refusal):
            retain.retain_file(self.root, self.fd, path.relative_to(self.root), path.stat().st_mtime_ns - 1)

    def test_refuses_missing_and_leaf_symlink(self):
        path = self.file()
        link = path.with_name("link")
        link.symlink_to(path.name)
        for item in (link, path.with_name("absent")):
            with self.subTest(path=item), self.assertRaises(OSError):
                self.capture(item)

    def test_refuses_same_target_parent_symlink(self):
        path = self.file()
        saved = path.parent.with_name("producer-saved")
        path.parent.rename(saved)
        path.parent.symlink_to(saved.name)
        with self.assertRaises(OSError):
            self.capture(path)
        self.assertFalse((self.output / path.relative_to(self.root)).exists())

    def test_refuses_retention_overwrite(self):
        path = self.file()
        self.capture(path)
        with self.assertRaises(FileExistsError):
            self.capture(path)

    def test_detects_source_mutation_during_capture(self):
        path = self.file()
        actual_fstat = os.fstat
        calls = 0
        def inspect(fd):
            nonlocal calls
            calls += 1
            if calls == 2:
                path.write_bytes(b"changed")
            return actual_fstat(fd)
        with patch.object(retain.os, "fstat", side_effect=inspect), self.assertRaises(retain.Refusal):
            self.capture(path)

    def test_output_dirfd_prevents_write_through_retargeted_path(self):
        path = self.file()
        outside = self.base / "outside"
        outside.mkdir()
        saved = self.base / "output-saved"
        self.output.rename(saved)
        self.output.symlink_to(outside.name)
        self.capture(path)
        self.assertEqual(list(outside.iterdir()), [])
        self.assertTrue((saved / path.relative_to(self.root)).is_file())

    def test_real_directory_refuses_output_alias(self):
        alias = self.base / "alias"
        alias.symlink_to(self.output.name)
        with self.assertRaises(OSError):
            with retain.real_directory(alias):
                self.fail("aliased output admitted")

    def cli_fixture(self):
        self.file("scripts/recreate_bootstrap.py", b"# synthetic source owner, patched only in this Python unit fixture\n")
        config = self.root / "bootstrap.toml"
        config.write_text('profile = "compiler"\n')
        build = self.root / "build" / HOST
        for name in ("trustc", "targo"):
            path = self.file(f"build/{HOST}/stage1/bin/{name}")
            path.chmod(0o755)
        self.file(f"build/{HOST}/stage1-rustc/{HOST}/release/rustc-main")
        driver = self.file(f"build/{HOST}/stage1-rustc/{HOST}/release/deps/librustc_driver-current.dylib")
        self.file(f"build/{HOST}/stage1-rustc/{HOST}/release/.librustc-stamp", b"t" + os.fsencode(driver) + b"\0")
        for target in (HOST, OTHER):
            library = self.file(f"build/{HOST}/stage1-std/{target}/dist/deps/libstd-current.rlib")
            self.file(f"build/{HOST}/stage1-std/{target}/dist/.libstd-stamp", b"t" + os.fsencode(library) + b"\0")
        for name in ("targo", "rust-analyzer-proc-macro-srv"):
            self.file(f"build/{HOST}/stage2-tools-bin/{HOST}/{name}")
        self.file(f"build/{HOST}/lld/bin/lld")
        row = {"path": ".", "commit": "a" * 40, "tree": "b" * 40, "tracked_status": ""}
        emission = {"exit": 0, "ended_unix": time.time(), "source_bookends_equal": True, "selected_public_commit": "a" * 40,
                    "source_before": [row], "source_after": [row], "bootstrap.toml": {"sha256": retain.digest(config)},
                    "phases": [{"phase": "emission", "exit": 0, "argv": [str(self.root / "scripts/recreate_bootstrap.py"),
                                "--stage", "1", "--require-seed", "--no-register", "--no-atpkg"]}]}
        record = self.base / "emission.json"
        record.write_text(json.dumps(emission))
        lineage = {"status": "immutable_release", "errors": [], "repositories": [
            {"path": ".", "head": "a" * 40, "head_tree": "b" * 40}]}
        owner = {"capture_source_lineage": lambda _: lineage,
                 "expected_public_stage_tools": lambda: {"trustc", "targo"},
                 "stage_tool_producers_for": lambda _: {"targo": "targo"}}
        output = self.base / "cli-output"
        argv = ["--repo-root", str(self.root), "--emission-result", str(record), "--host", HOST,
                "--target", HOST, "--target", OTHER, "--output", str(output)]
        return owner, output, argv

    def test_integrated_cli_retains_stamps_and_producers_with_honest_scope(self):
        owner, output, argv = self.cli_fixture()
        with patch.object(retain.runpy, "run_path", return_value=owner), contextlib.redirect_stdout(io.StringIO()):
            self.assertEqual(retain.main(argv), 0)
        result = json.loads((output / "RESULT.json").read_text())
        self.assertFalse(result["verified"])
        self.assertFalse(result["release_ready"])
        self.assertEqual(result["source_before"], result["source_after"])
        self.assertEqual(len(result["files"]), 10)
        self.assertFalse((output / "sdk").exists())
        self.assertEqual({role["producer_role"] for row in result["files"] for role in row["roles"]},
                         {"compiler0-entrypoint", "compiler0-rustc", "compiler0-rustc-stamp",
                          "compiler1-std", "compiler1-std-stamp", "compiler0-tool", "native-LLVM-LLD"})

    def test_integrated_cli_retains_the_sanctioned_build_noindex_layout(self):
        owner, output, argv = self.cli_fixture()
        (self.root / "build").rename(self.root / "build.noindex")
        (self.root / "build").symlink_to("build.noindex")
        with patch.object(retain.runpy, "run_path", return_value=owner), contextlib.redirect_stdout(io.StringIO()):
            self.assertEqual(retain.main(argv), 0)
        result = json.loads((output / "RESULT.json").read_text())
        self.assertEqual(len(result["files"]), 10)
        for row in result["files"]:
            self.assertTrue(row["source_relative"].startswith("build/"))
            self.assertTrue(row["physical_source_relative"].startswith("build.noindex/"))
            self.assertEqual(row["source_build_alias"]["physical_directory"], str(self.root / "build.noindex"))
        self.assertEqual(result["source_before"], result["source_after"])
        self.assertFalse(result["verified"])
        self.assertFalse(result["release_ready"])

    def test_integrated_llvm_runtime_alias_keeps_logical_build_namespace(self):
        owner, output, argv = self.cli_fixture()
        runtime = self.file(f"build/{HOST}/llvm/lib/libLLVM-current.dylib", b"actual native runtime bytes")
        runtime.with_name("libLLVM.dylib").symlink_to(runtime.name)
        # The positive fixture's emission ends after every original producer exists.
        record = Path(argv[argv.index("--emission-result") + 1])
        emission = json.loads(record.read_text())
        emission["ended_unix"] = time.time()
        record.write_text(json.dumps(emission))
        (self.root / "build").rename(self.root / "build.noindex")
        (self.root / "build").symlink_to("build.noindex")
        with patch.object(retain.runpy, "run_path", return_value=owner), contextlib.redirect_stdout(io.StringIO()):
            self.assertEqual(retain.main(argv), 0)
        result = json.loads((output / "RESULT.json").read_text())
        self.assertEqual(len(result["files"]), 11)
        alias = next(row for row in result["native_runtime_aliases"] if row["link"] is not None)
        self.assertEqual(alias["resolved"], f"build/{HOST}/llvm/lib/libLLVM-current.dylib")
        self.assertEqual((output / alias["resolved"]).read_bytes(), b"actual native runtime bytes")

    def test_integrated_llvm_runtime_alias_outside_its_namespace_still_refuses(self):
        owner, output, argv = self.cli_fixture()
        external = self.file("unrelated-runtime.dylib")
        alias = self.root / "build" / HOST / "llvm/lib/libLLVM.dylib"
        alias.parent.mkdir(parents=True)
        alias.symlink_to(external)
        (self.root / "build").rename(self.root / "build.noindex")
        (self.root / "build").symlink_to("build.noindex")
        with patch.object(retain.runpy, "run_path", return_value=owner), contextlib.redirect_stdout(io.StringIO()):
            self.assertEqual(retain.main(argv), 1)
        result = json.loads((output / "RESULT.json").read_text())
        self.assertIn("external LLVM runtime alias", result["error"])
        self.assertEqual(result["files"], [])

    def test_integrated_late_retained_output_mutation_refuses_success(self):
        owner, output, argv = self.cli_fixture()
        original_plan = retain.build_plan
        calls = 0
        def plan(*args):
            nonlocal calls
            calls += 1
            if calls == 2:
                image = output / "build" / HOST / "stage1-rustc" / HOST / "release/rustc-main"
                mode = image.stat().st_mode & 0o777
                image.chmod(0o600)
                image.write_bytes(b"later substituted emitted image")
                image.chmod(mode)
            return original_plan(*args)
        with patch.object(retain.runpy, "run_path", return_value=owner), patch.object(retain, "build_plan", side_effect=plan), contextlib.redirect_stdout(io.StringIO()):
            self.assertEqual(retain.main(argv), 1)
        result = json.loads((output / "RESULT.json").read_text())
        self.assertEqual(result["exit"], 1)
        self.assertIn("retained image", result["error"])

    def test_retained_stamp_read_refuses_leaf_and_parent_aliases(self):
        path = self.file()
        row = self.capture(path)
        relative = path.relative_to(self.root)
        self.assertEqual(retain.read_retained(self.fd, relative, row, collect=True), path.read_bytes())
        retained = self.output / relative
        saved = retained.with_name("saved-image")
        retained.rename(saved)
        retained.symlink_to(saved.name)
        with self.assertRaises(OSError):
            retain.read_retained(self.fd, relative, row, collect=True)
        retained.unlink()
        saved.rename(retained)
        saved_parent = retained.parent.with_name("saved-parent")
        retained.parent.rename(saved_parent)
        retained.parent.symlink_to(saved_parent.name)
        with self.assertRaises(OSError):
            retain.read_retained(self.fd, relative, row, collect=True)

    def test_integrated_cli_missing_producer_retains_failed_receipt(self):
        owner, output, argv = self.cli_fixture()
        (self.root / "build" / HOST / "lld/bin/lld").unlink()
        with patch.object(retain.runpy, "run_path", return_value=owner), contextlib.redirect_stdout(io.StringIO()):
            self.assertEqual(retain.main(argv), 1)
        result = json.loads((output / "RESULT.json").read_text())
        self.assertEqual(result["exit"], 1)
        self.assertIn("FileNotFoundError", result["error"])
        with self.assertRaises(retain.Refusal):
            retain.main(argv)

    def test_integrated_cli_refuses_output_inside_source(self):
        owner, output, argv = self.cli_fixture()
        argv[-1] = str(self.root / "build/retained-as-cache")
        with self.assertRaises(retain.Refusal):
            retain.main(argv)
        self.assertFalse((self.root / "build/retained-as-cache").exists())

    def test_record_reader_refuses_leaf_alias_and_binds_actual_bytes(self):
        path = self.base / "record.json"
        path.write_text('{"exit":0}')
        value, sha, physical = retain.read_record(path)
        self.assertEqual(value, {"exit": 0})
        self.assertEqual(sha, hashlib.sha256(path.read_bytes()).hexdigest())
        self.assertEqual(physical, list(retain.identity(path.stat())))
        alias = self.base / "alias.json"
        alias.symlink_to(path.name)
        with self.assertRaises(OSError):
            retain.read_record(alias)

    def test_source_books_bind_stage_selection_population_and_config(self):
        config = self.root / "bootstrap.toml"
        config.write_text('profile = "compiler"\n')
        row = {"path": ".", "commit": "a" * 40, "tree": "b" * 40, "tracked_status": ""}
        emission = {"exit": 0, "source_bookends_equal": True, "selected_public_commit": "a" * 40,
                    "source_before": [row], "source_after": [row],
                    "bootstrap.toml": {"sha256": retain.digest(config)},
                    "phases": [{"phase": "emission", "exit": 0,
                                "argv": [str(self.root / "scripts/recreate_bootstrap.py"), "--stage", "1", "--require-seed", "--no-register", "--no-atpkg"]}]}
        lineage = {"status": "immutable_release", "errors": [], "repositories": [
            {"path": ".", "head": "a" * 40, "head_tree": "b" * 40}]}
        owner = {"capture_source_lineage": lambda _: lineage}
        self.assertEqual(retain.source_book(self.root, emission, owner)["lineage"], lineage)
        emission["phases"][0]["argv"] += ["--no-build"]
        with self.assertRaises(retain.Refusal):
            retain.source_book(self.root, emission, owner)
        emission["phases"][0]["argv"].pop()
        config.write_text("changed")
        with self.assertRaises(retain.Refusal):
            retain.source_book(self.root, emission, owner)


if __name__ == "__main__":
    unittest.main()
