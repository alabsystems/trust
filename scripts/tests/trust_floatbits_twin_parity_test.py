#!/usr/bin/env python3
"""The single-source preflight accepts both build-script forms and refuses the rest.

scripts/trust_floatbits_twin_parity.py is the preflight of the four native-contract
strict gates (trust-floatbits, trust-intbound, trust-widthconv, trust-budget). A crate
may have no build script, the form c133258d3c7 gave three of them by declaring
`cfg(trust_verify)` in the workspace `[lints.rust]`, or exactly the check-cfg-only
build.rs that trust-floatbits keeps. Before this test the preflight read build.rs
unconditionally, so it refused every crate without one and the three gates could not
run. This holds the real crates of this tree to a pass, and copies of one of them to a
refusal when a build.rs mints the cfg or a `[package] build` key names another program.

The same script materializes mutation G's candidate workspace (a consumer whose edge to
the verified crate the gate then deletes). It copied only `crates/`, so after the
workspace manifest and lock moved to the repository root (992ace29547) it refused
every candidate; this holds the candidate to a workspace of the consumer alone.

Run: python3 -B scripts/tests/trust_floatbits_twin_parity_test.py

Author: Andrew Yates <andrewyates.name@gmail.com>
Copyright 2026 Andrew Yates | License: Apache-2.0 OR MIT
"""

from __future__ import annotations

import importlib.util
import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "scripts" / "trust_floatbits_twin_parity.py"
CRATES = ("trust-floatbits", "trust-intbound", "trust-widthconv", "trust-budget")

# Each spells the key Cargo reads as `[package] build`, naming a program other than build.rs.
NAMED_BUILD_PROGRAM = {
    "bare key": '[package]\nname = "x"\nbuild = "gen.rs"\n',
    "basic-quoted key": '[package]\nname = "x"\n"build" = "gen.rs"\n',
    "literal-quoted key": "[package]\nname = \"x\"\n'build' = \"gen.rs\"\n",
    "escaped key": '[package]\nname = "x"\n"bui\\u006Cd" = "gen.rs"\n',
    "spaced header": '[ package ]\nname = "x"\nbuild = "gen.rs"\n',
    "quoted header": '["package"]\nname = "x"\nbuild = "gen.rs"\n',
    "root dotted key": 'package.name = "x"\npackage.build = "gen.rs"\n',
    "inline table": 'package = { name = "x", build = "gen.rs" }\n',
    "header inside a string": '[package]\nname = "x"\ndescription = """\n[note]\n"""\nbuild = "gen.rs"\n',
    "build = true": '[package]\nname = "x"\nbuild = true\n',
}
NO_NAMED_BUILD_PROGRAM = {
    "absent": '[package]\nname = "x"\n\n[build-dependencies]\n',
    "false": '[package]\nname = "x"\nbuild = false  # no build script\n',
}


def load_script():
    spec = importlib.util.spec_from_file_location("trust_floatbits_twin_parity", SCRIPT)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def run(crate_root: Path) -> subprocess.CompletedProcess[str]:
    lib = crate_root / "src" / "lib.rs"
    return subprocess.run(
        [sys.executable, "-B", str(SCRIPT), str(lib), str(lib.parent / "contracts.rs")],
        capture_output=True,
        text=True,
        check=False,
    )


class TwinParityBuildScriptForms(unittest.TestCase):
    def test_every_crate_of_this_tree_passes(self) -> None:
        for crate in CRATES:
            with self.subTest(crate=crate):
                result = run(ROOT / "crates" / crate)
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertIn("13 structural controls rejected", result.stdout)

    def test_both_forms_are_present_in_this_tree(self) -> None:
        # The pass above covers both forms only while the tree has both.
        forms = {(ROOT / "crates" / crate / "build.rs").exists() for crate in CRATES}
        self.assertEqual(forms, {True, False})

    def copy_of(self, crate: str) -> Path:
        parent = Path(tempfile.mkdtemp(prefix="twin-parity-"))
        self.addCleanup(shutil.rmtree, parent)
        target = parent / crate
        shutil.copytree(ROOT / "crates" / crate, target)
        return target

    def test_a_build_script_that_mints_the_cfg_is_refused(self) -> None:
        crate = self.copy_of("trust-intbound")
        self.assertFalse((crate / "build.rs").exists())
        (crate / "build.rs").write_text(
            'fn main() {\n    println!("cargo::rustc-cfg=trust_verify");\n}\n',
            encoding="utf-8",
        )
        result = run(crate)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("check-cfg-only program", result.stderr)

    def test_the_check_cfg_only_build_script_is_accepted(self) -> None:
        crate = self.copy_of("trust-intbound")
        shutil.copy(ROOT / "crates" / "trust-floatbits" / "build.rs", crate / "build.rs")
        result = run(crate)
        self.assertEqual(result.returncode, 0, result.stderr)

    def test_every_spelling_of_a_named_build_program_is_refused(self) -> None:
        # Both readers: tomllib's, and the line scan Python 3.10 and older get.
        module = load_script()
        readers = {"line scan": None}
        if module.tomllib is not None:
            readers["tomllib"] = module.tomllib
            for spelling, text in NAMED_BUILD_PROGRAM.items():
                with self.subTest(fixture=spelling):
                    # The fixture really sets the key Cargo reads.
                    self.assertIn(module.tomllib.loads(text)["package"]["build"], ("gen.rs", True))
        for reader, toml in readers.items():
            module.tomllib = toml
            for spelling, text in NAMED_BUILD_PROGRAM.items():
                with self.subTest(reader=reader, spelling=spelling):
                    with self.assertRaises(module.Refusal):
                        module.refuse_named_build_program(Path("Cargo.toml"), text)
            for spelling, text in NO_NAMED_BUILD_PROGRAM.items():
                with self.subTest(reader=reader, spelling=spelling):
                    module.refuse_named_build_program(Path("Cargo.toml"), text)
            for crate in CRATES:
                with self.subTest(reader=reader, crate=crate):
                    manifest = ROOT / "crates" / crate / "Cargo.toml"
                    module.refuse_named_build_program(manifest, manifest.read_text(encoding="utf-8"))

    def test_a_package_build_key_naming_another_program_is_refused(self) -> None:
        crate = self.copy_of("trust-intbound")
        manifest = crate / "Cargo.toml"
        text = manifest.read_text(encoding="utf-8")
        self.assertIn("[package]\n", text)
        manifest.write_text(
            text.replace("[package]\n", '[package]\nbuild = "gen.rs"\n', 1),
            encoding="utf-8",
        )
        result = run(crate)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("names a build script", result.stderr)

    def test_the_mutation_g_candidate_is_a_workspace_of_the_consumer_alone(self) -> None:
        # The strict gates' mutation G drops a consumer's edge to the verified crate
        # in this copy and checks that the consumer stops compiling. The workspace
        # manifest and lock are at the repository root, not under crates/.
        for consumer in ("trust-ir-bridge", "trust-router", "trust-coordinator", "trust-vcgen"):
            with self.subTest(consumer=consumer):
                candidate = Path(tempfile.mkdtemp(prefix="twin-parity-candidate-"))
                self.addCleanup(shutil.rmtree, candidate)
                result = subprocess.run(
                    [
                        sys.executable,
                        "-B",
                        str(SCRIPT),
                        "--materialize-consumer-candidate",
                        str(ROOT),
                        str(candidate),
                        consumer,
                    ],
                    capture_output=True,
                    text=True,
                    check=False,
                )
                self.assertEqual(result.returncode, 0, result.stderr)
                manifest = (candidate / "Cargo.toml").read_text(encoding="utf-8")
                self.assertIn(f'\nmembers = ["crates/{consumer}"]\n', manifest)
                self.assertNotIn("default-members", manifest)
                self.assertIn("[patch.", manifest)
                self.assertEqual(
                    (candidate / "Cargo.lock").read_bytes(), (ROOT / "Cargo.lock").read_bytes()
                )
                for copied in ("Cargo.toml", "Cargo.lock", f"crates/{consumer}/Cargo.toml"):
                    self.assertFalse((candidate / copied).is_symlink(), copied)
                bridge = (candidate / "crates/trust-ir-bridge/Cargo.toml").read_text(
                    encoding="utf-8"
                )
                self.assertNotIn('compiler-context = ["dep:trust-mir-extract"]', bridge)
                self.assertNotIn("\ntrust-mir-extract = {", bridge)

    def test_a_candidate_root_that_is_not_empty_is_refused(self) -> None:
        candidate = Path(tempfile.mkdtemp(prefix="twin-parity-candidate-"))
        self.addCleanup(shutil.rmtree, candidate)
        (candidate / "stray").write_text("", encoding="utf-8")
        result = subprocess.run(
            [
                sys.executable,
                "-B",
                str(SCRIPT),
                "--materialize-consumer-candidate",
                str(ROOT),
                str(candidate),
                "trust-ir-bridge",
            ],
            capture_output=True,
            text=True,
            check=False,
        )
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("not empty", result.stderr)

    def test_build_false_is_accepted(self) -> None:
        crate = self.copy_of("trust-intbound")
        manifest = crate / "Cargo.toml"
        text = manifest.read_text(encoding="utf-8")
        manifest.write_text(
            text.replace("[package]\n", "[package]\nbuild = false\n", 1), encoding="utf-8"
        )
        result = run(crate)
        self.assertEqual(result.returncode, 0, result.stderr)


if __name__ == "__main__":
    unittest.main()
