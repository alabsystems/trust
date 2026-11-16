#!/usr/bin/env python3
"""Real native ELF and checksum-pinned archive controls; no Trust build credit."""

from __future__ import annotations

import importlib.util
import argparse
import io
import json
import os
from pathlib import Path
import platform
import shutil
import struct
import subprocess
import sys
import tarfile
import tempfile
import unittest
from unittest import mock

SCRIPT = Path(__file__).resolve().parents[1] / "seed_staircase.py"
SPEC = importlib.util.spec_from_file_location("seed_staircase_linux_test_subject", SCRIPT)
staircase = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(staircase)
CC = shutil.which("cc")


@unittest.skipUnless(platform.system() == "Linux" and CC, "native Linux C/ELF controls")
class LinuxSeedTests(unittest.TestCase):
    def setUp(self):
        self.tmp = Path(tempfile.mkdtemp(prefix="trust-linux-seed-test-"))
        self.root = self.tmp / "seed"
        (self.root / "bin").mkdir(parents=True)
        (self.root / "lib").mkdir()
        self.source = self.tmp / "main.c"
        self.source.write_text("int main(void) { return 0; }\n")
        self.native = self.tmp / "native"
        subprocess.run([CC, str(self.source), "-o", str(self.native)], check=True)
        for name in ("trustc", "cargo"):
            shutil.copy2(self.native, self.root / "bin" / name)
        self.host = staircase.host_triple()
        self.support = staircase.linux_seed_support()

    def tearDown(self):
        shutil.rmtree(self.tmp)

    def linked_tool(self, libdir=None, *, old_rpath=False):
        libdir = libdir or self.root / "lib"
        libdir.mkdir(exist_ok=True)
        library = libdir / "libseed_fixture.so"
        source = self.tmp / "lib.c"
        source.write_text("int fixture(void) { return 7; }\n")
        subprocess.run([CC, "-shared", "-fPIC", str(source), "-o", str(library),
                        "-Wl,-soname,libseed_fixture.so"], check=True)
        self.source.write_text("int fixture(void); int main(void) { return fixture() == 7 ? 0 : 1; }\n")
        tool = self.root / "bin" / "linked"
        rpath = "$ORIGIN/../lib" if libdir == self.root / "lib" else str(libdir)
        arguments = [CC, str(self.source), "-L" + str(libdir), "-lseed_fixture",
                     "-Wl,-rpath," + rpath, "-o", str(tool)]
        if old_rpath:
            arguments.append("-Wl,--disable-new-dtags")
        subprocess.run(arguments, check=True)
        return tool, library

    def test_native_loader_binds_internal_and_system_providers(self):
        _tool, library = self.linked_tool()
        receipt = staircase.dylib_closure(self.root, [])
        self.assertTrue(receipt["checked"])
        self.assertEqual(receipt["format"], "elf")
        self.assertEqual(receipt["host"], self.host)
        self.assertFalse(receipt["unresolved"])
        internal = [r for r in receipt["non_system"] if r["provider"] == str(library)]
        self.assertTrue(internal)
        self.assertEqual(internal[0]["provider_sha256"], staircase.sha256_file(library))
        self.assertTrue(receipt["system"])
        self.support.unchanged(receipt)

    def test_native_dynamic_elf_without_needed_entries_is_bound_and_tamper_checked(self):
        source = self.tmp / "no-needed.c"
        source.write_text("int no_needed_fixture(void) { return 7; }\n")
        library = self.root / "lib/libno_needed_fixture.so"
        subprocess.run([CC, "-shared", "-fPIC", "-nostdlib", str(source), "-o", str(library)], check=True)
        info = self.support.metadata(library, self.host)
        self.assertTrue(info["dynamic"])
        self.assertEqual(info["needed"], [])
        receipt = staircase.dylib_closure(self.root, [])
        self.assertEqual(receipt["observations"][str(library)], staircase.sha256_file(library))
        self.assertFalse(receipt["unresolved"])
        self.support.unchanged(receipt)
        with library.open("ab") as stream:
            stream.write(b"changed no-needed image")
        with self.assertRaisesRegex(ValueError, "runtime input changed"):
            self.support.unchanged(receipt)

    def test_static_loader_marker_cannot_hide_a_real_needed_library(self):
        tool, _library = self.linked_tool()
        self.assertTrue(self.support.metadata(tool, self.host)["needed"])
        original = self.support.command
        def hide_needed(argv, **kwargs):
            if "--list" in argv and argv[-1] == str(tool):
                return "\tstatically linked\n"
            return original(argv, **kwargs)
        with mock.patch.object(self.support, "command", side_effect=hide_needed):
            with self.assertRaisesRegex(staircase.Refusal, "empty DT_NEEDED"):
                staircase.dylib_closure(self.root, [])

    def test_rpath_uses_the_actual_native_loader(self):
        self.linked_tool(old_rpath=True)
        self.assertFalse(staircase.dylib_closure(self.root, [])["unresolved"])

    def test_a_library_with_the_right_basename_in_the_wrong_directory_is_not_accepted(self):
        _tool, library = self.linked_tool()
        wrong = self.root / "other"
        wrong.mkdir()
        library.rename(wrong / library.name)
        with self.assertRaisesRegex(staircase.Refusal, "libseed_fixture.so"):
            staircase.dylib_closure(self.root, [])

    def test_a_foreign_runtime_provider_is_retained_as_unresolved(self):
        _tool, library = self.linked_tool(self.tmp / "foreign")
        receipt = staircase.dylib_closure(self.root, [])
        self.assertTrue(any(r["provider"] == str(library) for r in receipt["unresolved"]))

    def test_library_tamper_invalidates_the_observed_closure(self):
        _tool, library = self.linked_tool()
        receipt = staircase.dylib_closure(self.root, [])
        with library.open("ab") as stream:
            stream.write(b"changed library")
        with self.assertRaisesRegex(ValueError, "runtime input changed"):
            self.support.unchanged(receipt)

    def test_a_retargeted_provider_link_is_not_the_original_observation(self):
        _tool, library = self.linked_tool()
        original = library.with_name("lib-original.so")
        library.rename(original)
        library.symlink_to(original.name)
        receipt = staircase.dylib_closure(self.root, [])
        replacement = library.with_name("lib-copy.so")
        shutil.copy2(original, replacement)
        library.unlink()
        library.symlink_to(replacement.name)
        with self.assertRaisesRegex(ValueError, "provider path changed"):
            self.support.unchanged(receipt)

    def test_mismatched_elf_platform_is_refused_before_a_probe_executes(self):
        tool = self.root / "bin" / "trustc"
        raw = bytearray(tool.read_bytes())
        struct.pack_into("<H", raw, 18, 62 if self.host.startswith("aarch64") else 183)
        tool.write_bytes(raw)
        with self.assertRaisesRegex(staircase.Refusal, "ELF platform differs"):
            staircase.dylib_closure(self.root, [])

    def test_a_foreign_interpreter_is_not_executed(self):
        tool = self.root / "bin" / "trustc"
        subprocess.run([CC, str(self.source), "-Wl,--dynamic-linker=/tmp/unadmitted-ld.so",
                        "-o", str(tool)], check=True)
        with self.assertRaises(staircase.Refusal):
            staircase.dylib_closure(self.root, [])

    def test_embedded_audit_code_is_refused_before_loader_listing(self):
        tool = self.root / "bin" / "trustc"
        subprocess.run([CC, str(self.source), "-Wl,--audit,/tmp/unadmitted-audit.so",
                        "-o", str(tool)], check=True)
        with self.assertRaisesRegex(staircase.Refusal, "embedded ELF audit"):
            staircase.dylib_closure(self.root, [])

    def test_only_the_initial_named_elf_may_have_an_anonymous_loader_row(self):
        binary = self.root / "bin/trustc"
        self.assertEqual(self.support.loader_rows(" (0x123)\n", binary), [("trustc", binary)])
        with self.assertRaisesRegex(ValueError, "unrecognized ELF loader row"):
            self.support.loader_rows(" (0x123)\n (0x456)\n", binary)

    def test_optional_queried_elf_self_mapping_does_not_change_bound_closure(self):
        self.linked_tool()
        actual = staircase.dylib_closure(self.root, [])
        reader = self.support.loader_rows
        def with_optional_self_mapping(output, binary, *, needed=None):
            return [(binary.name, binary), *reader(output, binary, needed=needed)]
        with mock.patch.object(self.support, "loader_rows", side_effect=with_optional_self_mapping):
            repeated = staircase.dylib_closure(self.root, [])
        self.assertEqual(actual, repeated)
        self.assertIn(str(self.root / "bin/trustc"), actual["observations"])
        self.assertTrue(actual["system"])
        self.support.unchanged(repeated)

    def test_real_repeated_loader_observations_have_identical_file_and_edge_bindings(self):
        self.linked_tool()
        observed = [staircase.dylib_closure(self.root, []) for _ in range(3)]
        self.assertEqual(observed[0], observed[1])
        self.assertEqual(observed[0], observed[2])

    def test_cwd_search_paths_and_linux_compat_overrides_are_refused(self):
        tool, _library = self.linked_tool()
        subprocess.run([CC, str(self.source), "-L" + str(self.root / "lib"), "-lseed_fixture",
                        "-Wl,-rpath,lib", "-o", str(tool)], check=True)
        with self.assertRaisesRegex(staircase.Refusal, "cwd-dependent"):
            staircase.dylib_closure(self.root, [])
        with self.assertRaisesRegex(staircase.Refusal, "--compat-lib is unsupported"):
            staircase.dylib_closure(self.root, [self.root / "lib"])

    def test_glibc_listing_does_not_run_the_program_or_library_constructor(self):
        tool, library = self.linked_tool()
        marker = self.tmp / "executed"
        c = self.tmp / "lib.c"
        c.write_text('#include <stdio.h>\n__attribute__((constructor)) static void init(void) {'
                     f'FILE *f=fopen({json.dumps(str(marker))},"w"); if(f) fclose(f);'
                     '}\nint fixture(void) { return 7; }\n')
        subprocess.run([CC, "-shared", "-fPIC", str(c), "-o", str(library),
                        "-Wl,-soname,libseed_fixture.so"], check=True)
        staircase.dylib_closure(self.root, [])
        self.assertFalse(marker.exists())
        subprocess.run([str(tool)], check=True)
        self.assertTrue(marker.exists())

    def archives(self, host=None, *, member_override=None):
        host = host or self.host
        payloads = self.tmp / "payloads"
        payloads.mkdir()
        stage0 = self.tmp / "stage0"
        pins = ["compiler_date=2026-10-14", "compiler_version=1.99.0-trust",
                "compiler_git_commit_hash=" + "1" * 40]
        for component in ("trustc", "trust-std", "targo"):
            stem = f"{component}-1.99.0-trust-{host}"
            archive = payloads / (stem + ".tar.xz")
            entries = ({"bin/trustc": self.native.read_bytes()} if component == "trustc" else
                       {"lib/rustlib/" + host + "/lib/libstd-fixture.rlib": b"fixture std"}
                       if component == "trust-std" else
                       {"bin/cargo": self.native.read_bytes(), "bin/targo": self.native.read_bytes()})
            if member_override and component == "trustc":
                entries.update(member_override)
            with tarfile.open(archive, "w:xz") as tar:
                for relative, data in entries.items():
                    member = tarfile.TarInfo(stem + "/" + component + "/" + relative)
                    member.mode = 0o755 if relative.startswith("bin/") else 0o644
                    member.size = len(data)
                    tar.addfile(member, io.BytesIO(data))
            pins.append(f"dist/2026-10-14/{archive.name}=" + staircase.sha256_file(archive))
        stage0.write_text("\n".join(pins) + "\n")
        return payloads, stage0

    def test_native_linux_archives_materialize_only_the_pinned_host(self):
        payloads, pins = self.archives()
        out = self.tmp / "installed"
        receipt = staircase.seed_sysroot(payloads, pins, out)
        self.assertEqual(receipt["host"], self.host)
        self.assertEqual(len(receipt["payloads"]), 3)
        self.assertEqual(receipt["stage0_file_sha256"], staircase.sha256_file(pins))
        self.assertEqual((out / "bin/trustc").read_bytes(), self.native.read_bytes())
        with self.assertRaisesRegex(staircase.Refusal, "already exists"):
            staircase.seed_sysroot(payloads, pins, out)

    def test_macos_pins_do_not_admit_unpinned_linux_tools(self):
        payloads, pins = self.archives("aarch64-apple-darwin")
        out = self.tmp / "installed"
        with self.assertRaisesRegex(staircase.Refusal, "pins no.*unknown-linux-gnu"):
            staircase.seed_sysroot(payloads, pins, out)
        self.assertFalse(out.exists())

    def test_pinned_linux_root_rechecks_archives_pin_and_installed_bytes(self):
        payloads, pins = self.archives()
        out = self.tmp / "installed"
        receipt = staircase.seed_sysroot(payloads, pins, out)
        repo = self.tmp / "repo"
        (repo / "src").mkdir(parents=True)
        shutil.copy2(pins, repo / "src/stage0")
        admission = {"stage0": str(out), "commit": "1" * 40, "pinned_seed": receipt}
        staircase.require_pinned_root(admission, repo)
        with (out / "bin/trustc").open("ab") as stream:
            stream.write(b"changed compiler")
        with self.assertRaisesRegex(staircase.Refusal, "installed bytes"):
            staircase.require_pinned_root(admission, repo)

    def test_native_content_admission_cannot_replace_a_pinned_linux_root(self):
        with self.assertRaisesRegex(staircase.Refusal, "checksum-pinned extraction record"):
            staircase.require_pinned_root({"stage0": str(self.root), "commit": "1" * 40}, self.tmp)

    def test_a_stale_runtime_receipt_prevents_rung_dispatch(self):
        receipt = staircase.dylib_closure(self.root, [])
        admission = self.tmp / "admission.json"
        admission.write_text(json.dumps({"kind": "stage0-admission", "stage0": str(self.root),
                                         "dylib_closure": receipt}))
        with (self.root / "bin/trustc").open("ab") as stream:
            stream.write(b"changed")
        args = argparse.Namespace(worktree=str(self.root), ledger=str(self.tmp / "ledger"),
                                  stage0_admission=str(admission))
        with self.assertRaisesRegex(staircase.Refusal, "runtime input changed"):
            staircase.run_rung(args)
        self.assertFalse((self.tmp / "ledger").exists())

    def test_root_receipt_does_not_waive_a_changed_archive(self):
        payloads, pins = self.archives()
        out = self.tmp / "installed"
        receipt = staircase.seed_sysroot(payloads, pins, out)
        repo = self.tmp / "repo"
        (repo / "src").mkdir(parents=True)
        shutil.copy2(pins, repo / "src/stage0")
        archive = next(payloads.glob("targo-*.tar.xz"))
        with archive.open("ab") as stream:
            stream.write(b"changed archive")
        with self.assertRaisesRegex(staircase.Refusal, "archive changed"):
            staircase.require_pinned_root({"stage0": str(out), "commit": "1" * 40,
                                           "pinned_seed": receipt}, repo)

    def test_installed_std_bytes_are_part_of_pinned_root_identity(self):
        payloads, pins = self.archives()
        out = self.tmp / "installed"
        receipt = staircase.seed_sysroot(payloads, pins, out)
        repo = self.tmp / "repo"
        (repo / "src").mkdir(parents=True)
        shutil.copy2(pins, repo / "src/stage0")
        next(out.rglob("libstd-fixture.rlib")).write_bytes(b"different std")
        with self.assertRaisesRegex(staircase.Refusal, "installed bytes"):
            staircase.require_pinned_root({"stage0": str(out), "commit": "1" * 40,
                                           "pinned_seed": receipt}, repo)

    def test_archive_tamper_is_a_refusal_without_partial_installation(self):
        payloads, pins = self.archives()
        archive = next(payloads.glob("trustc-*.tar.xz"))
        with archive.open("ab") as stream:
            stream.write(b"not the pinned archive")
        out = self.tmp / "installed"
        with self.assertRaisesRegex(staircase.Refusal, "sha256"):
            staircase.seed_sysroot(payloads, pins, out)
        self.assertFalse(out.exists())

    def test_correct_archive_names_cannot_relabel_foreign_machine_bytes(self):
        raw = bytearray(self.native.read_bytes())
        struct.pack_into("<H", raw, 18, 62 if self.host.startswith("aarch64") else 183)
        self.native.write_bytes(raw)
        payloads, pins = self.archives()
        out = self.tmp / "installed"
        with self.assertRaisesRegex(staircase.Refusal, "ELF platform differs"):
            staircase.seed_sysroot(payloads, pins, out)
        self.assertFalse(out.exists())

    def test_pinned_archive_traversal_is_still_refused(self):
        payloads, pins = self.archives(member_override={"../../../../escape": b"escape"})
        with self.assertRaisesRegex(staircase.Refusal, "refusing archive member"):
            staircase.seed_sysroot(payloads, pins, self.tmp / "installed")
        self.assertFalse((self.tmp / "escape").exists())

    def test_proc_observations_name_the_real_executable_and_original_start_ticks(self):
        table = staircase.parse_tick(staircase.ps_listing(list(staircase.TICK_LISTING)))
        ppid, started, exe = table[os.getpid()]
        self.assertEqual(ppid, os.getppid())
        self.assertTrue(started.startswith("ticks:"))
        self.assertEqual(exe, os.path.realpath(sys.executable))
        self.assertGreaterEqual(staircase.available_gib(), 0)
        self.assertIn(os.getpid(), staircase.read_environments([os.getpid()]))

    def test_ambient_linux_loader_overrides_do_not_reach_admission_probes(self):
        with mock.patch.dict(os.environ, {"LD_PRELOAD": "/unadmitted.so", "LD_LIBRARY_PATH": "/foreign",
                                         "GLIBC_TUNABLES": "glibc.cpu.hwcaps=-ASIMD"}):
            environment = staircase.compat_env([])
        self.assertNotIn("LD_PRELOAD", environment)
        self.assertNotIn("LD_LIBRARY_PATH", environment)
        self.assertNotIn("GLIBC_TUNABLES", environment)


@unittest.skipUnless(platform.system() == "Linux", "the rung runner over a native stand-in stage0")
class RunOptionTests(unittest.TestCase):
    """`run --offline` and `run --clean-lean-lib` (the first Linux seed's builds):
    with neither, x.py gets the environment it always got and the record has the
    keys it always had; with them, exactly their variables and one record key."""

    XPY = "import json, os\njson.dump(dict(os.environ), open('env.json', 'w'))\n"
    # An olean header as mint_seed_support._lean_header_identity reads one (magic,
    # format version 1, a 40-hex world key). No Lean library is claimed.
    OLEAN = b"olean" + b"\x01" + b"b" * 40 + b"\0" * 16
    ALWAYS = {"HOME", "USER", "LOGNAME", "SHELL", "TERM", "LANG", "LC_ALL", "TMPDIR", "PATH", "CARGO_HOME",
              "RUSTUP_TOOLCHAIN", "RUSTUP_AUTO_INSTALL", "TRUST_STAIRCASE_RUNG", "SOURCE_DATE_EPOCH"}
    ADDED = {"CARGO_NET_OFFLINE", "CLEAN_OLEAN_PINNED_LEAN_LIB", "CLEAN_OLEAN_REQUIRE_PINNED_LEAN"}

    def setUp(self):
        self.tmp = Path(tempfile.mkdtemp(prefix="trust-linux-run-option-test-")).resolve()
        self.addCleanup(shutil.rmtree, self.tmp, ignore_errors=True)
        self.tree = self.tmp / "tree"
        self.tree.mkdir()
        (self.tree / "x.py").write_text(self.XPY)
        subprocess.run(["git", "-C", str(self.tree), "init", "-q"], check=True)
        subprocess.run(["git", "-C", str(self.tree), "-c", "user.name=t", "-c", "user.email=t@t",
                        "commit", "-q", "--allow-empty", "-m", "x"], check=True)
        head = subprocess.run(["git", "-C", str(self.tree), "rev-parse", "HEAD"], capture_output=True,
                              text=True, check=True).stdout.strip()
        stage0 = self.tmp / "stage0"
        (stage0 / "bin").mkdir(parents=True)
        for name in ("trustc", "cargo"):  # native OS stand-ins: no compiler is claimed
            shutil.copy2("/bin/true", stage0 / "bin" / name)
        self.admission = self.tmp / "admission.json"
        self.admission.write_text(json.dumps({
            "kind": "stage0-admission", "commit": head, "stage0": str(stage0),
            "sha256": staircase.sysroot_files(stage0), "dylib_closure": staircase.dylib_closure(stage0, [])}))
        clean = self.tree / "first-party" / "clean"
        (clean / "crates" / "clean-olean").mkdir(parents=True)
        (clean / "tests").mkdir()
        (clean / "lean-toolchain").write_text("leanprover/lean4:v9.9.9\n")
        (clean / "crates" / "clean-olean" / "lean_worlds.tsv").write_text(
            "v9.9.9\toracle\tleanprover/lean4:v9.9.9\ttests/oracle.olean\n")
        (clean / "tests" / "oracle.olean").write_bytes(self.OLEAN)
        self.library = self.tmp / "lean" / "leanprover--lean4---v9.9.9" / "lib" / "lean"
        (self.library / "Init").mkdir(parents=True)
        (self.library / "Init" / "Prelude.olean").write_bytes(self.OLEAN + b"prelude")

    def run_rung(self, label, *options):
        done = subprocess.run(
            [sys.executable, "-B", str(SCRIPT), "run", "--worktree", str(self.tree), "--label", label,
             "--ledger", str(self.tmp / "ledger"), "--stage0-admission", str(self.admission),
             "--min-available-gib", "0", *options, "--", "plain"],
            capture_output=True, text=True, timeout=180)
        return done, json.loads(done.stdout)

    def test_without_the_options_the_environment_and_record_are_unchanged_and_with_them_only_theirs_are_added(self):
        done, plain = self.run_rung("plain")
        self.assertEqual(done.returncode, 0, done.stderr)
        plain_env = json.loads((self.tree / "env.json").read_text())
        self.assertEqual(set(plain_env) - {"SSH_AUTH_SOCK"}, self.ALWAYS)
        self.assertEqual(plain["environment"], plain_env)
        self.assertNotIn("clean_lean", plain)
        done, record = self.run_rung("optioned", "--offline", "--clean-lean-lib", str(self.library))
        self.assertEqual(done.returncode, 0, done.stderr)
        env = json.loads((self.tree / "env.json").read_text())
        self.assertEqual(record["environment"], env)
        self.assertEqual({key: value for key, value in env.items() if key not in self.ADDED},
                         {**plain_env, "TRUST_STAIRCASE_RUNG": "optioned"})
        self.assertEqual({key: env[key] for key in self.ADDED}, {
            "CARGO_NET_OFFLINE": "true", "CLEAN_OLEAN_PINNED_LEAN_LIB": str(self.library),
            "CLEAN_OLEAN_REQUIRE_PINNED_LEAN": "1"})
        self.assertEqual(set(record) - set(plain), {"clean_lean"})
        self.assertEqual(set(plain) - set(record), set())
        lean = record["clean_lean"]
        self.assertEqual((lean["library"], lean["unchanged"]), (str(self.library), True))
        self.assertEqual(lean["before"], lean["after"])
        # What the record binds is what the mint's own function binds for the same library.
        bound = staircase.clean_lean_observation(self.tree, self.library)
        self.assertEqual(lean["before"], {key: bound[key] for key in ("fingerprint", "manifest_sha256")})
        self.assertEqual(bound["environment"], {key: env[key] for key in self.ADDED - {"CARGO_NET_OFFLINE"}})

    def test_a_changed_library_is_recorded_and_a_library_the_pin_does_not_name_starts_nothing(self):
        (self.tree / "x.py").write_text(self.XPY + (
            f"open({str(self.library / 'Init' / 'Prelude.olean')!r}, 'ab').write(b'changed')\n"))
        done, record = self.run_rung("changed", "--clean-lean-lib", str(self.library))
        self.assertEqual(done.returncode, 0, done.stderr)
        self.assertFalse(record["clean_lean"]["unchanged"])
        self.assertNotEqual(record["clean_lean"]["before"], record["clean_lean"]["after"])
        (self.tree / "env.json").unlink()
        rungs = (self.tmp / "ledger" / "rungs.jsonl").read_text()
        other = self.tmp / "lean" / "leanprover--lean4---v0.0.0" / "lib" / "lean"
        shutil.copytree(self.library, other)
        done, refused = self.run_rung("wrong", "--clean-lean-lib", str(other))
        self.assertEqual(done.returncode, 1)
        self.assertRegex(refused["refused"], r"--clean-lean-lib .* is not the Lean library .* exact pinned")
        self.assertFalse((self.tree / "env.json").exists())
        self.assertEqual((self.tmp / "ledger" / "rungs.jsonl").read_text(), rungs)

    def test_the_environment_function_adds_after_everything_else(self):
        ledger = self.tmp / "unit-ledger"
        base = staircase.scrubbed_env(ledger, "unit", [], sys.executable, source_date_epoch="17")
        self.assertEqual(staircase.scrubbed_env(ledger, "unit", [], sys.executable, source_date_epoch="17",
                                                offline=False, clean_lean=None), base)
        lean = {"CLEAN_OLEAN_PINNED_LEAN_LIB": "/lean/lib/lean", "CLEAN_OLEAN_REQUIRE_PINNED_LEAN": "1"}
        both = staircase.scrubbed_env(ledger, "unit", [], sys.executable, source_date_epoch="17",
                                      offline=True, clean_lean=lean)
        self.assertEqual(list(both), [*base, "CARGO_NET_OFFLINE", *lean])
        self.assertEqual(both, {**base, "CARGO_NET_OFFLINE": "true", **lean})
        self.assertFalse(self.ADDED & set(base))
        # `run --fifo-jobserver`'s MAKEFLAGS comes last, and only when given.
        self.assertNotIn("MAKEFLAGS", base)
        flags = staircase.fifo_jobserver_makeflags(staircase.fifo_jobserver_path(ledger), 20)
        self.assertEqual(flags, f"-j20 --jobserver-auth=fifo:{ledger}/tmp/jobserver.fifo")
        every = staircase.scrubbed_env(ledger, "unit", [], sys.executable, source_date_epoch="17",
                                       offline=True, clean_lean=lean, makeflags=flags)
        self.assertEqual(list(every), [*base, "CARGO_NET_OFFLINE", *lean, "MAKEFLAGS"])

    def test_the_run_options_together_add_only_their_own(self):
        # The first Linux seed's builds pass all three; its rung config names the job count.
        done, plain = self.run_rung("plain")
        self.assertEqual(done.returncode, 0, done.stderr)
        plain_env = json.loads((self.tmp / "tree" / "env.json").read_text())
        (self.tree / "bootstrap.toml").write_text("[build]\njobs = 2\n")
        done, record = self.run_rung("all", "--offline", "--clean-lean-lib", str(self.library), "--fifo-jobserver")
        self.assertEqual(done.returncode, 0, done.stderr)
        env = json.loads((self.tree / "env.json").read_text())
        fifo = self.tmp / "ledger" / "tmp" / "jobserver.fifo"
        self.assertEqual(set(env) - set(plain_env), self.ADDED | {"MAKEFLAGS"})
        self.assertEqual(env["MAKEFLAGS"], f"-j2 --jobserver-auth=fifo:{fifo}")
        self.assertEqual(set(record) - set(plain), {"clean_lean", "jobserver"})
        self.assertEqual((record["jobserver"]["tokens"], record["jobserver"]["tokens_at_end"]), (1, 1))
        self.assertFalse(fifo.exists())


class MacOSCompatibilityTests(unittest.TestCase):
    """The unchanged Mach-O classification policy, without pretending a Linux
    host ran native macOS tooling. Real otool/compiler tests stay host-specific.
    """

    def test_macos_internal_system_and_declared_compat_classification(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary) / "seed"
            (root / "bin").mkdir(parents=True)
            (root / "lib").mkdir()
            (root / "lib/libinternal.dylib").write_bytes(b"fixture")
            tool = root / "bin/trustc"
            tool.write_bytes(b"fixture")
            compat = Path(temporary) / "compat"
            compat.mkdir()
            library = compat / "libforeign.dylib"
            library.write_bytes(b"compat fixture")
            commands = ["/usr/lib/libSystem.B.dylib", "@rpath/libinternal.dylib",
                        "/unavailable/libforeign.dylib"]
            with mock.patch.object(staircase.platform, "system", return_value="Darwin"), \
                    mock.patch.object(staircase, "macho_files", return_value=[tool]), \
                    mock.patch.object(staircase, "macho_load_commands", return_value=commands):
                good = staircase.dylib_closure(root, [compat])
                bad = staircase.dylib_closure(root, [])
            self.assertEqual([r["kind"] for r in good["non_system"]], ["internal", "compat"])
            self.assertFalse(good["unresolved"])
            self.assertEqual(good["compat"][0]["provider_sha256"], staircase.sha256_file(library))
            self.assertEqual([r["load"] for r in bad["unresolved"]], [commands[-1]])

    def test_unknown_native_platform_is_never_an_unchecked_closure_success(self):
        with mock.patch.object(staircase.platform, "system", return_value="Other"):
            with self.assertRaisesRegex(staircase.Refusal, "unsupported"):
                staircase.dylib_closure(Path("/unused"), [])


if __name__ == "__main__":
    unittest.main()
