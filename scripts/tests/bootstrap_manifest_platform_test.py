#!/bin/sh
""":"
for candidate in python3.14 python3.13 python3.12 python3.11 python3; do
    if command -v "$candidate" >/dev/null 2>&1 \
        && "$candidate" -c 'import sys; raise SystemExit(sys.version_info < (3, 11))' 2>/dev/null; then
        exec "$candidate" "$0" "$@"
    fi
done
echo "bootstrap_manifest_platform_test.py requires Python 3.11+ (tomllib)" >&2
exit 2
":"""
import os as _floor_os
import shutil as _floor_shutil
import sys as _floor_sys

# Trust: python floor, second half. `python3 bootstrap_manifest_platform_test.py` reads the sh block above
# as a string, so an old `python3` (3.9 on macOS CommandLineTools) re-execs here.
if __name__ == "__main__" and _floor_sys.version_info < (3, 11):
    for _floor_candidate in ("python3.14", "python3.13", "python3.12", "python3.11"):
        _floor_path = _floor_shutil.which(_floor_candidate)
        if _floor_path:
            _floor_argv = [_floor_path, _floor_os.path.abspath(__file__), *_floor_sys.argv[1:]]
            _floor_os.execv(_floor_path, _floor_argv)
    _floor_sys.exit("bootstrap_manifest_platform_test.py requires Python 3.11+ (tomllib); none found on PATH")
__doc__ = """Bootstrap's manifest gives a platform every crate its scheduler source names there.

`src/bootstrap/src/utils/metadata_scheduler.rs` gates each use of
`trust_resource_controller` with a `#[cfg(...)]` of its own, and
`src/bootstrap/Cargo.toml` declares the crate under a `[target.'cfg(...)']` table.
The two predicates are written in different files and nothing compared them: from
32e722797d (2026-11-08) the source said macOS or Linux and the manifest said
Apple silicon only, so Bootstrap did not compile on Linux (E0433, six uses) and no
landing noticed, because no landing builds Bootstrap there.

This reads both files and evaluates both predicates on four targets. It is a
source check, not a build: it finds the predicate that governs a use as the
nearest `#[cfg(...)]` attribute above it, which is how this file is written, and
it does not look inside modules gated where they are declared (`host_graph`,
`bounded`). A use with no attribute above it must be an unconditional dependency.

Author: Andrew Yates <andrewyates.name@gmail.com>
Copyright 2026 Andrew Yates | License: Apache-2.0 OR MIT
"""
import re
import tomllib
import unittest
from pathlib import Path

REPO = Path(__file__).resolve().parents[2]
MANIFEST = REPO / "src/bootstrap/Cargo.toml"
SCHEDULER = REPO / "src/bootstrap/src/utils/metadata_scheduler.rs"
CRATE = "trust_resource_controller"

TARGETS = [
    {"target_os": "linux", "target_arch": "aarch64", "target_family": "unix"},
    {"target_os": "linux", "target_arch": "x86_64", "target_family": "unix"},
    {"target_os": "macos", "target_arch": "aarch64", "target_family": "unix"},
    {"target_os": "macos", "target_arch": "x86_64", "target_family": "unix"},
]


class Unsupported(Exception):
    """A predicate this reader cannot evaluate; never read as true or false."""


def tokens(text: str) -> list[str]:
    found = re.findall(r'\s*([A-Za-z_][A-Za-z0-9_]*|"[^"]*"|[(),=])', text)
    if "".join(found) != re.sub(r"\s+", "", text):
        raise Unsupported(text)
    return found


def evaluate(predicate: str, target: dict[str, str]) -> bool:
    """`all(..)`, `any(..)`, `not(..)`, `key = "value"`, `unix`, `windows`, `test`."""
    stream = tokens(predicate)
    position = 0

    def take(expected: str | None = None) -> str:
        nonlocal position
        if position >= len(stream) or (expected is not None and stream[position] != expected):
            raise Unsupported(predicate)
        position += 1
        return stream[position - 1]

    def expression() -> bool:
        name = take()
        if name in ("all", "any", "not"):
            take("(")
            values = []
            while position < len(stream) and stream[position] != ")":
                values.append(expression())
                if position < len(stream) and stream[position] == ",":
                    take(",")
            take(")")
            if name == "not":
                if len(values) != 1:
                    raise Unsupported(predicate)
                return not values[0]
            return all(values) if name == "all" else any(values)
        if position < len(stream) and stream[position] == "=":
            take("=")
            value = take()
            if name not in target or not value.startswith('"'):
                raise Unsupported(predicate)
            return target[name] == value.strip('"')
        if name in ("unix", "windows"):
            return target["target_family"] == name
        if name == "test":
            return False
        raise Unsupported(predicate)

    result = expression()
    if position != len(stream):
        raise Unsupported(predicate)
    return result


def declared(manifest: dict, target: dict[str, str]) -> set[str]:
    """The crates the manifest makes available to the library on `target`."""
    names = set(manifest.get("dependencies", {}))
    for key, table in manifest.get("target", {}).items():
        match = re.fullmatch(r"cfg\((.*)\)", key, flags=re.S)
        if match is None:
            raise Unsupported(key)  # a bare triple: none is used here
        if evaluate(match[1], target):
            names.update(table.get("dependencies", {}))
    return {name.replace("-", "_") for name in names}


def governing_predicates(source: str, crate: str) -> list[tuple[int, str | None]]:
    """For each line naming `crate::`, its line number and the nearest `#[cfg(...)]`
    attribute above it (None when the top of the file comes first)."""
    lines = source.splitlines()
    found = []
    for number, line in enumerate(lines, 1):
        if line.lstrip().startswith("//") or not re.search(r"\b" + crate + r"::", line):
            continue
        predicate = None
        for above in range(number - 1, 0, -1):
            attribute = re.fullmatch(r"\s*#\[cfg\((.*)\)\]\s*", lines[above - 1])
            if attribute is not None:
                predicate = attribute[1]
                break
        found.append((number, predicate))
    return found


class EvaluatorTests(unittest.TestCase):
    def test_the_predicates_this_manifest_and_source_use(self):
        linux, mac_arm = TARGETS[0], TARGETS[2]
        both = 'any(target_os = "macos", target_os = "linux")'
        apple_silicon = 'all(target_arch = "aarch64", target_os = "macos")'
        self.assertTrue(evaluate(both, linux))
        self.assertFalse(evaluate(apple_silicon, linux))
        self.assertTrue(evaluate(apple_silicon, mac_arm))
        self.assertFalse(evaluate(f"not({both})", linux))
        self.assertTrue(evaluate("unix", linux))
        self.assertFalse(evaluate("windows", linux))
        self.assertFalse(evaluate(f"all(test, {both})", linux))

    def test_an_unknown_predicate_is_refused_not_guessed(self):
        for predicate in ('feature = "x"', "target_os", 'any(target_os = "linux"', "debug_assertions",
                          'target_os = "linux" extra'):
            with self.subTest(predicate=predicate), self.assertRaises(Unsupported):
                evaluate(predicate, TARGETS[0])


class ManifestTests(unittest.TestCase):
    def setUp(self):
        self.manifest = tomllib.loads(MANIFEST.read_text(encoding="utf-8"))
        self.uses = governing_predicates(SCHEDULER.read_text(encoding="utf-8"), CRATE)

    def test_the_instrument_finds_the_uses_and_their_predicates(self):
        self.assertGreaterEqual(len(self.uses), 6)
        self.assertIn('any(target_os = "macos", target_os = "linux")', {p for _, p in self.uses})

    def test_every_platform_that_compiles_a_use_is_given_the_crate(self):
        for target in TARGETS:
            available = declared(self.manifest, target)
            for line, predicate in self.uses:
                with self.subTest(os=target["target_os"], arch=target["target_arch"], line=line):
                    if predicate is None or evaluate(predicate, target):
                        self.assertIn(CRATE, available,
                                      f"{SCHEDULER.name}:{line} is compiled on this target "
                                      f"(cfg({predicate})) and src/bootstrap/Cargo.toml does not declare "
                                      f"{CRATE.replace('_', '-')} for it")

    def test_the_manifest_before_the_fix_fails_this_check_on_linux(self):
        # The control: the crate under the Apple-silicon table only, as 32e722797d left it.
        old = {"dependencies": {},
               "target": {'cfg(all(target_arch = "aarch64", target_os = "macos"))': {
                   "dependencies": {"trust-resource-controller": {}}}}}
        self.assertNotIn(CRATE, declared(old, TARGETS[0]))
        self.assertNotIn(CRATE, declared(old, TARGETS[3]))
        self.assertIn(CRATE, declared(old, TARGETS[2]))


if __name__ == "__main__":
    unittest.main()
