#!/usr/bin/env python3
"""A change to any file a seal ships changes its content identity (plan T13a).

Exercises scripts/lib/seal_content_identity.py directly, and the promotion script's own
`prov_artifact_fingerprint` (sliced out of scripts/promote-toolchain.sh, no copied logic)
on two seals that differ only where the old six-file fingerprint could not see.
"""

# Author: Andrew Yates <andrewyates.name@gmail.com>
# Copyright 2026 Andrew Yates | License: Apache-2.0 OR MIT

import importlib.util
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest


SCRIPTS = Path(__file__).resolve().parents[1]
REPO = SCRIPTS.parent
LIBRARY = SCRIPTS / "lib" / "seal_content_identity.py"
PROMOTE = SCRIPTS / "promote-toolchain.sh"
SPEC = importlib.util.spec_from_file_location("seal_content_identity", LIBRARY)
sci = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = sci
SPEC.loader.exec_module(sci)

HOST = "aarch64-apple-darwin"
OTHER = "x86_64-apple-darwin"

# A seal shaped like a promoted stage2: every class of file a real one carries.
EXECUTABLES = (
    "bin/trustc", "bin/targo", "bin/targo-trust", "bin/trustd", "bin/trustdoc",
    "bin/ay", "bin/clean", "bin/ty", "bin/tippy", "bin/targo-tippy", "bin/tippy-driver",
    "bin/trustfmt", "bin/targo-fmt", "bin/trust-analyzer",
    "libexec/trust-analyzer-proc-macro-srv",
    f"lib/rustlib/{HOST}/bin/rust-lld", f"lib/rustlib/{HOST}/bin/gcc-ld/ld64.lld",
    f"lib/rustlib/{HOST}/bin/rust-objcopy",
)
# Stock names, each a hard link to its Trust tool in the same bin/ (T13c's layout).
STOCK_LINKS = {"bin/rustc": "bin/trustc", "bin/cargo": "bin/targo", "bin/rustdoc": "bin/trustdoc"}
DATA = (
    "lib/librustc_driver-0123456789abcdef.dylib",
    "lib/libstd-0123456789abcdef.dylib",
    f"lib/rustlib/{HOST}/lib/libstd-0123456789abcdef.rlib",
    f"lib/rustlib/{HOST}/lib/libcore-0123456789abcdef.rlib",
    f"lib/rustlib/{HOST}/lib/liballoc-0123456789abcdef.rlib",
    f"lib/rustlib/{HOST}/lib/librustc_public-0123456789abcdef.rmeta",
    f"lib/rustlib/{HOST}/lib/libserde_derive-0123456789abcdef.dylib",
    f"lib/rustlib/{HOST}/lib/self-contained/crt2.o",
    f"lib/rustlib/{HOST}/codegen-backends/librustc_codegen_trust_cg-0123456789abcdef.dylib",
    f"lib/rustlib/{OTHER}/lib/libstd-fedcba9876543210.rlib",
    f"lib/rustlib/{OTHER}/lib/libcore-fedcba9876543210.rlib",
    "lib/rustlib/src/rust/library/core/src/lib.rs",
    "lib/rustlib/rustc-src.json",
    "share/man/man1/trustc.1",
    # A name promotion writes at the ROOT is content anywhere else.
    "share/doc/PROVENANCE",
)
SYMLINKS = {"lib/rustlib/rustc-src/rust": "../src/rust"}
RECORDS = ("PROVENANCE", "PROVENANCE.build-status", "SEED-MINT", "STAGE0-LINEAGE")


def build_seal(root: Path) -> None:
    for rel in EXECUTABLES:
        path = root / rel
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(f"#!/bin/sh\n# {rel}\n".encode())
        path.chmod(0o755)
    for stock, trust in STOCK_LINKS.items():
        os.link(root / trust, root / stock)
    for rel in DATA:
        path = root / rel
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(f"payload of {rel}\n".encode())
        path.chmod(0o644)
    for rel, target in SYMLINKS.items():
        path = root / rel
        path.parent.mkdir(parents=True, exist_ok=True)
        os.symlink(target, path)
    for rel in RECORDS:
        (root / rel).write_text(f"record {rel}\n")


def flip_last_byte(path: Path) -> None:
    data = bytearray(path.read_bytes())
    data[-1] ^= 0x01
    # Write through the inode, as an in-place rebuild would: a hard-linked stock
    # name sees the change too.
    with open(path, "r+b") as handle:
        handle.write(bytes(data))


class SealContentIdentityTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix="seal-identity-")
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.seal = self.root / "trust-fixture"
        build_seal(self.seal)
        self.baseline = sci.identity(self.seal)

    def fresh(self, name: str) -> Path:
        copy = self.root / name
        shutil.copytree(self.seal, copy, symlinks=True)
        # copytree breaks hard links into copies, which must not move the identity.
        self.assertEqual(sci.identity(copy), self.baseline, "a copy of the same bytes")
        return copy

    def test_every_covered_file_moves_the_identity(self):
        covered = (*EXECUTABLES, *STOCK_LINKS, *DATA)
        for rel in covered:
            with self.subTest(file=rel):
                copy = self.fresh("byte-" + rel.replace("/", "_"))
                flip_last_byte(copy / rel)
                self.assertNotEqual(sci.identity(copy)[0], self.baseline[0], rel)
                shutil.rmtree(copy)

    def test_the_mode_is_content(self):
        # Every permission and special bit but group/other write: the owner's execute
        # bit, setuid, setgid, sticky, and group/other read and execute, on a file and
        # on a directory.
        flips = {
            "owner-x": 0o100, "setuid": 0o4000, "setgid": 0o2000, "sticky": 0o1000,
            "group-x": 0o010, "other-r": 0o004,
        }
        for rel in ("bin/targo-trust", "bin/trustd", DATA[2], f"lib/rustlib/{HOST}/lib"):
            for name, bit in flips.items():
                if name == "owner-x" and rel.endswith("/lib"):
                    continue  # a directory its owner cannot search cannot be read at all
                with self.subTest(entry=rel, bit=name):
                    copy = self.fresh(f"mode-{name}-" + rel.replace("/", "_"))
                    path = copy / rel
                    path.chmod(path.stat().st_mode ^ bit)
                    self.assertNotEqual(sci.identity(copy)[0], self.baseline[0])
                    shutil.rmtree(copy)

    def test_group_and_other_write_bits_are_not(self):
        # Promotion clears them (`chmod -R go-w`), so a stage2 and its seal agree.
        copy = self.fresh("go-w")
        for rel in (*EXECUTABLES, *DATA, "bin", f"lib/rustlib/{HOST}/lib"):
            path = copy / rel
            path.chmod(path.stat().st_mode | 0o022)
        self.assertEqual(sci.identity(copy), self.baseline)

    def test_added_removed_renamed_and_relinked_entries_move_it(self):
        mutations = {
            "added": lambda c: (c / "bin" / "trust-wp").write_text("new tool\n"),
            "added-rlib": lambda c: (c / f"lib/rustlib/{HOST}/lib/libextra-1.rlib").write_text("x"),
            "removed": lambda c: (c / "bin" / "trustd").unlink(),
            "removed-rlib": lambda c: (c / DATA[3]).unlink(),
            "renamed": lambda c: (c / "bin/ty").rename(c / "bin/ty2"),
            "relinked": lambda c: (
                (c / "lib/rustlib/rustc-src/rust").unlink(),
                os.symlink("../src", c / "lib/rustlib/rustc-src/rust"),
            ),
            # An empty directory is an entry (removing one is the same comparison).
            "empty-dir-added": lambda c: (c / f"lib/rustlib/{HOST}/lib/self-contained/empty").mkdir(),
            "link-replaced-by-copy": lambda c: (
                (c / "lib/rustlib/rustc-src/rust").unlink(),
                shutil.copytree(c / "lib/rustlib/src/rust", c / "lib/rustlib/rustc-src/rust"),
            ),
        }
        for name, mutate in mutations.items():
            with self.subTest(mutation=name):
                copy = self.fresh(name)
                mutate(copy)
                self.assertNotEqual(sci.identity(copy)[0], self.baseline[0], name)

    def test_the_seal_records_are_not_content(self):
        copy = self.fresh("records")
        for rel in RECORDS:
            (copy / rel).write_text("rewritten after the identity was read\n")
        (copy / "SEED-MINT").unlink()
        self.assertEqual(sci.identity(copy), self.baseline)

    def test_a_hard_link_and_a_copy_are_the_same_content(self):
        copy = self.fresh("copies")
        for stock, trust in STOCK_LINKS.items():
            (copy / stock).unlink()
            shutil.copy2(copy / trust, copy / stock)
        self.assertEqual(sci.identity(copy), self.baseline)

    def test_the_name_the_seal_is_reached_by_is_not_content(self):
        link = self.root / "trust-current"
        os.symlink(self.seal, link)
        self.assertEqual(sci.identity(link), self.baseline)

    def test_a_file_no_toolchain_ships_is_refused(self):
        copy = self.fresh("fifo")
        os.mkfifo(copy / "bin" / "pipe")
        with self.assertRaisesRegex(sci.SealContentError, "neither a regular file"):
            sci.identity(copy)
        result = subprocess.run([sys.executable, "-B", str(LIBRARY), str(copy)],
                                capture_output=True, text=True, timeout=60)
        self.assertEqual(result.returncode, 1, result.stderr)
        self.assertEqual(result.stdout, "")
        self.assertIn("bin/pipe", result.stderr)

    def test_counts_and_manifest(self):
        sha, files, links, directories = self.baseline
        self.assertEqual(files, len(EXECUTABLES) + len(STOCK_LINKS) + len(DATA))
        self.assertEqual(links, len(SYMLINKS))
        self.assertEqual(directories, sum(
            1 for parent, names, _ in os.walk(self.seal) for name in names
            if not os.path.islink(os.path.join(parent, name))))
        result = subprocess.run([sys.executable, "-B", str(LIBRARY), "--manifest", str(self.seal)],
                                capture_output=True, timeout=60, check=True)
        lines = result.stdout.decode().splitlines()
        self.assertEqual(len(lines), files + links + directories)
        self.assertIn("L - ../src/rust lib/rustlib/rustc-src/rust", lines)
        self.assertIn("D 0755 - bin", lines)
        self.assertTrue(any(line.startswith("F 0755 ") and line.endswith(" bin/targo-trust")
                            for line in lines))
        self.assertTrue(any(line.startswith("F 0644 ") and line.endswith(" " + DATA[2])
                            for line in lines))
        self.assertFalse(any(line.endswith(" PROVENANCE") and " share/" not in line
                             for line in lines))

    def test_a_named_prefix_names_the_lines_and_keeps_the_identity(self):
        result = subprocess.run(
            [sys.executable, "-B", str(LIBRARY), "--prefix", "private_sysroot_content",
             str(self.seal)],
            capture_output=True, text=True, timeout=60, check=True)
        sha, files, links, directories = self.baseline
        self.assertEqual(result.stdout.splitlines(), [
            f"private_sysroot_content_sha256={sha}",
            f"private_sysroot_content_files={files}",
            f"private_sysroot_content_links={links}",
            f"private_sysroot_content_dirs={directories}",
            f"private_sysroot_content_scope={sci.SCOPE}",
        ])
        refused = subprocess.run(
            [sys.executable, "-B", str(LIBRARY), "--prefix", "a-b", str(self.seal)],
            capture_output=True, text=True, timeout=60)
        self.assertEqual(refused.returncode, 2)
        self.assertEqual(refused.stdout, "")


class PromotionFingerprintTests(unittest.TestCase):
    """The defect T13a closes, through the promotion script's own function."""

    @classmethod
    def setUpClass(cls):
        cls.temporary = tempfile.TemporaryDirectory(prefix="seal-fingerprint-")
        cls.addClassCleanup(cls.temporary.cleanup)
        cls.root = Path(cls.temporary.name)
        source = PROMOTE.read_text()
        begin = source.index("\nprov_sha256() {") + 1
        end = source.index("\n# Read one snapshot:", begin)
        cls.helpers = cls.root / "fingerprint.sh"
        cls.helpers.write_text(source[begin:end] + "\n")

    def fingerprint(self, seal: Path) -> dict[str, str]:
        shell = 'set -euo pipefail\nsource "$1"\nREPO="$2"\nprov_artifact_fingerprint "$3"\n'
        result = subprocess.run(["bash", "-c", shell, "fingerprint", str(self.helpers),
                                 str(REPO), str(seal)],
                                capture_output=True, text=True, timeout=120)
        self.assertEqual(result.returncode, 0, result.stderr)
        return dict(line.split("=", 1) for line in result.stdout.splitlines())

    def test_seals_that_differ_only_where_the_old_fingerprint_was_blind(self):
        base = self.root / "base"
        build_seal(base)
        base_fields = self.fingerprint(base)
        self.assertEqual(base_fields["artifact_content_sha256"], sci.identity(base)[0])
        old_fields = {key for key in base_fields if not key.startswith("artifact_content_")}
        self.assertTrue({"artifact_driver_sha256", "artifact_bin_trustc_sha256",
                         "artifact_bin_targo_sha256"} <= old_fields)
        for rel in ("bin/targo-trust", "bin/trustd", DATA[2], DATA[3], DATA[9]):
            with self.subTest(file=rel):
                other = self.root / ("other-" + rel.replace("/", "_"))
                shutil.copytree(base, other, symlinks=True)
                flip_last_byte(other / rel)
                fields = self.fingerprint(other)
                # Every per-file line agrees: the old identity could not tell them apart.
                self.assertEqual({k: fields[k] for k in old_fields},
                                 {k: base_fields[k] for k in old_fields})
                self.assertNotEqual(fields["artifact_content_sha256"],
                                    base_fields["artifact_content_sha256"])

    def test_an_unidentifiable_seal_fails_and_prints_nothing(self):
        seal = self.root / "unidentifiable"
        build_seal(seal)
        os.mkfifo(seal / "lib" / "pipe")
        shell = 'set -euo pipefail\nsource "$1"\nREPO="$2"\nprov_artifact_fingerprint "$3"\n'
        result = subprocess.run(["bash", "-c", shell, "fingerprint", str(self.helpers),
                                 str(REPO), str(seal)],
                                capture_output=True, text=True, timeout=120)
        self.assertNotEqual(result.returncode, 0)
        self.assertEqual(result.stdout, "")


if __name__ == "__main__":
    unittest.main()
