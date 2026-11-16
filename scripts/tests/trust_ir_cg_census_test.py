#!/usr/bin/env python3
"""Offline self-test for scripts/trust_ir_cg_census.py.

The census itself is a MEASUREMENT instrument (check_gate_lane_coverage.py
lists it under MANUAL_ONLY: it needs a built stage trustc and a backend dylib).
What this pins is the part that needs neither: the harness logic around the
compile, driven through a FAKE trustc that answers `--print sysroot` and
`-vV`, records the argv and the codegen-control env it was handed, and prints
a canned backend fatal.

  * `StaticRoots`: a refused STATIC (`static `path` (symbol `_RNv..`, defined
    at ..: L:C (#0)): msg`) keys on its mangled symbol. The fixture is one the
    function-root grammar alone cannot parse — asserted, so the test is not
    vacuous — which is how a static root used to land as `<unknown>`.
  * `ResolveDeps`: a recipe dep resolves from an explicit `--extern`, else from
    the compiler's own search path (recorded as a CANDIDATE, never as the path
    the compiler loaded), else it is a refusal naming both fixes. An undeclared
    or malformed `--extern` is refused. A search-path-changing `--extra-flag`
    is disclosed in the record.
  * `EndToEnd`: `--crate alloc` records `deps`; `--crate core` (a leaf) does
    not. `--diag-json` reaches the compiler as the TRACKED
    `-Ztrust-ir-cg-args=diag-json`, never as `TCG_DIAG_JSON` in its env (trustc
    refuses every `TCG_*`/`TRUST_CG_*` env var and aborts before measuring
    anything), and caller `TCG_*`/`TRUST_CG_*` vars are stripped.
  * `Reparse`: nothing is compiled, so every run-shaped fact is null and no
    `deps` are resolved; `--extern` under `--reparse` is refused.

Run directly (`python3 -B scripts/tests/trust_ir_cg_census_test.py`) or through
`scripts/check_script_tests.sh`.

Author: Andrew Yates | Copyright 2026 Andrew Yates | License: Apache-2.0 OR MIT
"""

from __future__ import annotations

import contextlib
import importlib.util
import io
import json
import os
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock

SCRIPT = Path(__file__).resolve().parents[1] / "trust_ir_cg_census.py"
_spec = importlib.util.spec_from_file_location("trust_ir_cg_census", SCRIPT)
census = importlib.util.module_from_spec(_spec)
assert _spec.loader is not None
_spec.loader.exec_module(census)

HOST = "aarch64-fake-darwin"
STATIC_ENTRY = (
    "static `sync::STATIC_INNER_SLICE` (symbol `_RNvNtCs1_5alloc4sync18STATIC_INNER_SLICE`, "
    "defined at /x/library/alloc/src/sync.rs:3786:1: 3786:50 (#0)): static requires 16-byte "
    "alignment, which exceeds the 8-byte data-section alignment of this slice"
)
FUNCTION_ENTRY = (
    "_RNvCs1_5alloc3foo (reachable Rust-internal monomorphization, not a std-internal shim): "
    "[TCG-ITER-UNMODELED] iterator adapter is not modelled"
)
CANNED_STDERR = (
    "error: [TCG-MIR-UNSUPPORTED] rustc_codegen_trust_cg: cannot compile required function with "
    "unsupported MIR (failing closed rather than miscompiling):\n"
    f"         - {STATIC_ENTRY}\n"
    f"         - {FUNCTION_ENTRY}\n"
    "\n"
    "error: aborting due to 1 previous error\n"
)


class FakeToolchain:
    """A temp dir holding a fake trustc and the sysroot it reports."""

    def __init__(self, root: Path, sysroot_crates: tuple[str, ...]):
        self.root = root
        self.sysroot = root / "sysroot"
        libdir = self.sysroot / "lib" / "rustlib" / HOST / "lib"
        libdir.mkdir(parents=True)
        self.rlibs = {}
        for i, name in enumerate(sysroot_crates):
            rlib = libdir / f"lib{name}-{i:08x}.rlib"
            rlib.write_bytes(b"")
            self.rlibs[name] = rlib
        self.record = root / "invocation.json"
        self.trustc = root / "trustc"
        self.trustc.write_text(
            f"#!{sys.executable}\n"
            "import json, os, sys\n"
            "args = sys.argv[1:]\n"
            "if args == ['--print', 'sysroot']:\n"
            f"    print({str(self.sysroot)!r}); sys.exit(0)\n"
            "if args == ['-vV']:\n"
            f"    print('rustc 1.99.0-fake (census self-test)\\nbinary: rustc\\nhost: {HOST}'); sys.exit(0)\n"
            f"with open({str(self.record)!r}, 'w') as f:\n"
            "    json.dump({'argv': args, 'env': {k: v for k, v in os.environ.items()\n"
            "               if k.startswith(('TCG_', 'TRUST_CG_')) or k == 'RUSTC_BOOTSTRAP'}}, f)\n"
            f"sys.stderr.write({CANNED_STDERR!r})\n"
            "sys.exit(1)\n"
        )
        self.trustc.chmod(0o755)
        self.src = root / "lib.rs"
        self.src.write_text("#![no_std]\n")


def run_main(argv: list[str]) -> int:
    with contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(io.StringIO()):
        return census.main(argv)


class StaticRoots(unittest.TestCase):
    def test_fixture_is_one_the_function_grammar_cannot_parse(self):
        self.assertIsNone(census.ROOT_RE.match(STATIC_ENTRY))

    def test_static_root_keys_on_its_mangled_symbol(self):
        row = census.split_root(STATIC_ENTRY)
        self.assertEqual(row["symbol"], "_RNvNtCs1_5alloc4sync18STATIC_INNER_SLICE")
        self.assertEqual(
            row["class"],
            "static `sync::STATIC_INNER_SLICE`, defined at /x/library/alloc/src/sync.rs:3786:1: 3786:50 (#0)",
        )
        self.assertEqual(
            row["reason"],
            "static requires <n>-byte alignment, which exceeds the <n>-byte data-section alignment of this slice",
        )

    def test_function_root_is_unchanged(self):
        row = census.split_root(FUNCTION_ENTRY)
        self.assertEqual(row["symbol"], "_RNvCs1_5alloc3foo")
        self.assertEqual(row["class"], "reachable Rust-internal monomorphization, not a std-internal shim")
        self.assertEqual(row["reason"], "[TCG-ITER-UNMODELED]")


class ResolveDeps(unittest.TestCase):
    def setUp(self):
        self._tmp = tempfile.TemporaryDirectory()
        self.tmp = Path(self._tmp.name)

    def tearDown(self):
        self._tmp.cleanup()

    def resolve(self, tc: FakeToolchain, deps, externs=(), extra=()):
        return census.resolve_deps(list(deps), list(externs), tc.trustc, dict(os.environ), list(extra))

    def test_leaf_crate_resolves_nothing(self):
        tc = FakeToolchain(self.tmp, ())
        self.assertEqual(self.resolve(tc, []), ([], {}, []))

    def test_sysroot_dep_needs_no_flag_and_names_no_path_as_fact(self):
        tc = FakeToolchain(self.tmp, ("core", "compiler_builtins"))
        flags, record, errors = self.resolve(tc, ["core", "compiler_builtins"])
        self.assertEqual((flags, errors), ([], []))
        for dep in ("core", "compiler_builtins"):
            self.assertEqual(
                record[dep], {"resolved_by": "compiler", "default_sysroot_candidate": str(tc.rlibs[dep])}
            )

    def test_explicit_extern_wins_and_is_forwarded_verbatim(self):
        tc = FakeToolchain(self.tmp, ("core", "compiler_builtins"))
        mine = self.tmp / "libcore-mine.rlib"
        mine.write_bytes(b"")
        flags, record, errors = self.resolve(tc, ["core", "compiler_builtins"], [f"core={mine}"])
        self.assertEqual(errors, [])
        self.assertEqual(flags, ["--extern", f"core={mine}"])
        self.assertEqual(record["core"], {"resolved_by": "explicit", "path": str(mine)})
        self.assertEqual(record["compiler_builtins"]["resolved_by"], "compiler")

    def test_unresolvable_dep_is_a_refusal_naming_both_fixes(self):
        tc = FakeToolchain(self.tmp, ("core",))
        flags, record, errors = self.resolve(tc, ["core", "compiler_builtins"])
        self.assertEqual(len(errors), 1)
        self.assertIn("--extern compiler_builtins=", errors[0])
        self.assertIn("--trustc", errors[0])

    def test_undeclared_malformed_and_missing_externs_are_refused(self):
        tc = FakeToolchain(self.tmp, ("core", "compiler_builtins"))
        std = self.tmp / "libstd-x.rlib"
        std.write_bytes(b"")
        _, _, errors = self.resolve(
            tc,
            ["core", "compiler_builtins"],
            [f"std={std}", "core", f"core={self.tmp / 'absent.rlib'}"],
        )
        self.assertEqual(len(errors), 3, errors)
        self.assertIn("not a declared dep", errors[0])
        self.assertIn("must be DEP=PATH", errors[1])
        self.assertIn("no such file", errors[2])

    def test_search_path_extra_flag_is_disclosed(self):
        tc = FakeToolchain(self.tmp, ("core", "compiler_builtins"))
        for extra in ("--sysroot=/elsewhere", "-L/elsewhere", "--target=x", "--extern=core=/x"):
            _, record, _ = self.resolve(tc, ["core"], extra=[extra])
            self.assertTrue(record["core"].get("search_path_overridden_by_extra_flags"), extra)
        _, record, _ = self.resolve(tc, ["core"], extra=["-Ztrust-ir-cg-args=no-proof-certs"])
        self.assertNotIn("search_path_overridden_by_extra_flags", record["core"])


class EndToEnd(unittest.TestCase):
    def setUp(self):
        self._tmp = tempfile.TemporaryDirectory()
        self.tmp = Path(self._tmp.name)
        self.tc = FakeToolchain(self.tmp / "tc", ("core", "compiler_builtins"))

    def tearDown(self):
        self._tmp.cleanup()

    def census_run(self, crate: str, *extra: str) -> tuple[int, Path]:
        out = self.tmp / f"out-{crate}"
        argv = [
            "--trustc", str(self.tc.trustc), "--crate", crate, "--src", str(self.tc.src),
            "--backend", "/fake/backend.dylib", "--out-dir", str(out), *extra,
        ]
        with mock.patch.dict(os.environ, {"TCG_DIAG_JSON": "1", "TRUST_CG_KNOB": "1"}):
            rc = run_main(argv)
        return rc, out

    def test_alloc_records_deps_and_diag_json_is_the_tracked_option(self):
        rc, out = self.census_run("alloc", "--diag-json", "--extra-flag=-Ztrust-ir-cg-args=no-proof-certs")
        self.assertEqual(rc, 0)
        seen = json.loads(self.tc.record.read_text())
        self.assertEqual(seen["env"], {"RUSTC_BOOTSTRAP": "1"})
        argv = seen["argv"]
        self.assertNotIn("--extern", argv)
        self.assertIn("-Ztrust-ir-cg-args=diag-json", argv)
        self.assertLess(
            argv.index("-Ztrust-ir-cg-args=diag-json"), argv.index("-Ztrust-ir-cg-args=no-proof-certs")
        )
        self.assertEqual(argv[-1], str(self.tc.src.resolve()))
        prov = json.loads((out / "provenance.json").read_text())
        self.assertEqual(prov["env"], {"RUSTC_BOOTSTRAP": "1"})
        self.assertEqual(prov["exit_code"], 1)
        self.assertIs(prov["timed_out"], False)
        self.assertEqual(set(prov["deps"]), {"core", "compiler_builtins"})
        roots = [json.loads(line) for line in (out / "failed_roots.jsonl").read_text().splitlines()]
        self.assertEqual(
            [r["symbol"] for r in roots], ["_RNvNtCs1_5alloc4sync18STATIC_INNER_SLICE", "_RNvCs1_5alloc3foo"]
        )
        self.assertEqual(prov["failed_root_count"], 2)

    def test_leaf_provenance_carries_no_deps(self):
        rc, out = self.census_run("core")
        self.assertEqual(rc, 0)
        prov = json.loads((out / "provenance.json").read_text())
        self.assertNotIn("deps", prov)
        self.assertNotIn("-Ztrust-ir-cg-args=diag-json", json.loads(self.tc.record.read_text())["argv"])

    def test_unresolvable_dep_refuses_before_compiling(self):
        tc = FakeToolchain(self.tmp / "bare", ("core",))
        out = self.tmp / "out-refused"
        rc = run_main(["--trustc", str(tc.trustc), "--crate", "alloc", "--src", str(tc.src), "--out-dir", str(out)])
        self.assertEqual(rc, 2)
        self.assertFalse(tc.record.exists(), "the compiler must not run when a dep does not resolve")
        self.assertFalse((out / "provenance.json").exists())


class Reparse(unittest.TestCase):
    # `--src` is passed so the test does not depend on this checkout's
    # `library/` tree: the census checks the crate source exists before it
    # decides whether it is reparsing.
    def setUp(self):
        self._tmp = tempfile.TemporaryDirectory()
        self.tmp = Path(self._tmp.name)
        self.tc = FakeToolchain(self.tmp / "tc", ("core", "compiler_builtins"))
        self.log = self.tmp / "stderr.log"
        self.log.write_text(CANNED_STDERR)

    def tearDown(self):
        self._tmp.cleanup()

    def test_reparse_records_nulls_and_resolves_nothing(self):
        out = self.tmp / "out"
        rc = run_main(
            [
                "--trustc", str(self.tc.trustc), "--crate", "alloc", "--src", str(self.tc.src),
                "--reparse", str(self.log), "--out-dir", str(out),
            ]
        )
        self.assertEqual(rc, 0)
        self.assertFalse(self.tc.record.exists(), "a reparse must not invoke the compiler")
        prov = json.loads((out / "provenance.json").read_text())
        for key in ("exit_code", "timed_out", "wall_seconds", "emitted_objects", "source"):
            self.assertIsNone(prov[key], key)
        self.assertEqual(prov["command"], str(self.log.resolve()))
        self.assertEqual(prov["backend"], "reparse: unknown")
        self.assertTrue(prov["reparsed"])
        self.assertNotIn("deps", prov)
        self.assertEqual(prov["failed_root_count"], 2)

    def test_extern_under_reparse_is_refused(self):
        rc = run_main(
            [
                "--trustc", str(self.tc.trustc), "--crate", "alloc", "--src", str(self.tc.src),
                "--reparse", str(self.log),
                "--extern", f"core={self.tc.rlibs['core']}", "--out-dir", str(self.tmp / "out"),
            ]
        )
        self.assertEqual(rc, 2)


if __name__ == "__main__":
    unittest.main()
