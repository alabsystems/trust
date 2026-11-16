#!/usr/bin/env python3
"""Controls for scripts/trust_core/specr/regen.py (RM1: the specr → Clean translator v2 regenerates
byte for byte).

* The REAL driver on the REAL tree: every committed output is regenerated from the pinned inputs by the
  committed translator, and it is byte-identical; the manifest matches.
* Negative controls, each on a temporary copy of the translator directory beside the unmutated control:
  one changed byte of a committed output, one changed emission in the translator, and one changed pinned
  input each make the check exit 1 and name exactly what drifted.
* `write` on a mutated copy regenerates it, and the check then passes on that copy (the driver repairs
  what it reports, so a red is never a stuck red).
* The pinned gzip encoding is deterministic.
* The rest of the driver has negative controls too: a stray file in generated/, an edit to the driver
  itself, a prelude edit against Clean's TrustSem fixture copy (with the manifest refreshed), the
  `--from-source` front-end comparison, pin check and `write`, and every acceptance condition of
  `--clean` (a fake `clean` prints canned reports; one never exits and is killed by the timeout).

Needs Python 3.11 or later; run with /opt/homebrew/bin/python3 (3.14).

Author: Andrew Yates <andrewyates.name@gmail.com>
Copyright 2026 Andrew Yates | License: Apache-2.0 OR MIT
"""

import contextlib
import gzip
import importlib.util
import io
import json
import os
import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
SPECR = ROOT / "scripts" / "trust_core" / "specr"
SCRIPT = SPECR / "regen.py"
SPEC = importlib.util.spec_from_file_location("trust_core_specr_regen", SCRIPT)
regen = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(regen)


def own_fixture(root: Path, extra: tuple) -> tuple:
    """A temporary copy is judged against the fixture its test names, never the
    pinned first-party/clean's (the driver's default): with that submodule
    checked out, a copy's deliberate mutation also drifted against the real
    fixture, so every expectation here held only where the submodule was absent."""
    if Path(root).resolve() == SPECR.resolve() or "--fixture" in extra:
        return extra
    return (*extra, "--fixture", str(Path(root).parent / "no-clean-fixture"))


def check(root: Path, *extra: str) -> subprocess.CompletedProcess:
    return subprocess.run([sys.executable, "-B", str(SCRIPT), "check", "--root", str(root), *own_fixture(root, extra)],
                          stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, check=False)


def write(root: Path, *extra: str) -> subprocess.CompletedProcess:
    return subprocess.run([sys.executable, "-B", str(SCRIPT), "write", "--root", str(root), *own_fixture(root, extra)],
                          stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, check=False)


def executable(path: Path, body: str) -> Path:
    path.write_text(f"#!{sys.executable}\n{body}")
    path.chmod(0o755)
    return path


def drifted(out: str) -> set[str]:
    return {line.split(None, 1)[1].strip() for line in out.splitlines() if line.startswith("DRIFT    ")}


class SpecrRegenTest(unittest.TestCase):
    def copy(self) -> Path:
        tmp = Path(tempfile.mkdtemp(prefix="specr-regen-test-"))
        self.addCleanup(shutil.rmtree, tmp, True)
        dst = tmp / "specr"
        shutil.copytree(SPECR, dst, ignore=shutil.ignore_patterns("__pycache__", "target"))
        # the copy's `--from-source` would import trust_core/common.py from its parent
        return dst

    def test_committed_tree_regenerates_byte_for_byte(self):
        proc = check(SPECR)
        self.assertEqual(proc.returncode, 0, proc.stdout + proc.stderr)
        self.assertIn("regen: byte-identical", proc.stdout)
        self.assertEqual(drifted(proc.stdout), set())
        for f in regen.OUTPUTS:
            self.assertIn(f"identical  {f}", proc.stdout)

    def test_one_changed_output_byte_drifts(self):
        root = self.copy()
        self.assertEqual(check(root).returncode, 0, "control: the unmutated copy is identical")
        p = root / "generated" / "MiniRustSlice.lean"
        data = bytearray(p.read_bytes())
        i = data.index(b"SPick.choose")
        data[i + 6] = ord("K")  # SPick.choose -> SPick.Khoose
        p.write_bytes(bytes(data))
        proc = check(root)
        self.assertEqual(proc.returncode, 1, proc.stdout)
        self.assertEqual(drifted(proc.stdout), {"generated/MiniRustSlice.lean"})

    def test_one_changed_translator_emission_drifts(self):
        root = self.copy()
        p = root / "specr2clean" / "calls.py"
        src = p.read_text()
        self.assertIn("call = f'SPick.choose (σ := ", src)
        p.write_text(src.replace("call = f'SPick.choose (σ := ", "call = f'SPick.int (σ := ", 1))
        proc = check(root)
        self.assertEqual(proc.returncode, 1, proc.stdout)
        # the census counts the library constructs each emission reaches
        self.assertEqual(drifted(proc.stdout),
                         {"generated/MiniRustSlice.lean", "generated/census.json",
                          "generated/MANIFEST.json [translator]", "generated/MANIFEST.json [outputs]"})

    def test_one_changed_pinned_input_drifts(self):
        root = self.copy()
        p = root / "pinned" / "ast.json.gz"
        ast = gzip.decompress(p.read_bytes())
        needle = b'asking for a too large allocation'
        self.assertIn(needle, ast)
        p.write_bytes(regen.gz_bytes(ast.replace(needle, b'asking for a too big allocation', 1)))
        proc = check(root)
        self.assertEqual(proc.returncode, 1, proc.stdout)
        self.assertEqual(drifted(proc.stdout),
                         {"generated/MiniRustSlice.lean", "generated/census.json",
                          "generated/MANIFEST.json [pinned]", "generated/MANIFEST.json [outputs]"})

    def test_write_repairs_what_check_reports(self):
        root = self.copy()
        p = root / "specr2clean" / "calls.py"
        p.write_text(p.read_text().replace("call = f'SPick.choose (σ := ", "call = f'SPick.int (σ := ", 1))
        self.assertEqual(check(root).returncode, 1)
        w = subprocess.run([sys.executable, "-B", str(SCRIPT), "write", "--root", str(root)],
                           stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, check=False)
        self.assertEqual(w.returncode, 0, w.stdout + w.stderr)
        self.assertEqual(check(root).returncode, 0)
        self.assertIn(b"SPick.int (", (root / "generated" / "MiniRustSlice.lean").read_bytes())

    def test_gzip_encoding_is_deterministic(self):
        data = b"specr\n" * 1000
        self.assertEqual(regen.gz_bytes(data), regen.gz_bytes(data))
        self.assertEqual(gzip.decompress(regen.gz_bytes(data)), data)
        self.assertEqual((SPECR / "pinned" / "ast.json.gz").read_bytes(),
                         regen.gz_bytes(gzip.decompress((SPECR / "pinned" / "ast.json.gz").read_bytes())))

    # ---- the rest of the driver ----

    def tmpdir(self) -> Path:
        tmp = Path(tempfile.mkdtemp(prefix="specr-regen-aux-"))
        self.addCleanup(shutil.rmtree, tmp, True)
        return tmp

    def test_a_stray_file_in_generated_drifts(self):
        root = self.copy()
        (root / "generated" / "Stale.lean").write_text("-- left over\n")
        proc = check(root)
        self.assertEqual(proc.returncode, 1, proc.stdout)
        self.assertEqual(drifted(proc.stdout), {"generated/Stale.lean  (not an output of this translator)"})

    def test_an_edit_to_the_driver_drifts(self):
        root = self.copy()
        p = root / "regen.py"
        p.write_text(p.read_text().replace("STEPS, FUEL = 200000, 2000", "STEPS, FUEL = 200000, 2000  # edited", 1))
        proc = check(root)
        self.assertEqual(proc.returncode, 1, proc.stdout)
        self.assertEqual(drifted(proc.stdout), {"generated/MANIFEST.json [translator]"})

    def fixture_of(self, root: Path) -> Path:
        fx = self.tmpdir() / "trust_sem"
        fx.mkdir()
        for name, ours in regen.FIXTURE_COPIES:
            shutil.copyfile(root / ours, fx / name)
        return fx

    def test_a_prelude_edit_drifts_against_the_clean_fixture(self):
        root = self.copy()
        fx = self.fixture_of(root)
        proc = check(root, "--fixture", str(fx))
        self.assertEqual(proc.returncode, 0, "control: identical copies " + proc.stdout)
        for name, ours in regen.FIXTURE_COPIES:
            self.assertIn(f"identical  clean fixture {name}  (= {ours})", proc.stdout)
        # a semantic edit to the runtime, with the manifest refreshed so only the copy can see it
        p = root / "SpecrPrelude.lean"
        src = p.read_text()
        self.assertIn("    (fun _ ih => SOut.searchNat bound 0 ih)\n    (fun _ ih => SOut.searchNat bound 0 ih)", src)
        p.write_text(src.replace("    (fun _ ih => SOut.searchNat bound 0 ih)\n    (fun _ ih => SOut.searchNat bound 0 ih)",
                                 "    (fun _ ih => SOut.searchNat bound 0 ih)\n    (fun _ ih => SOut.searchNat bound 1 ih)", 1))
        self.assertEqual(write(root).returncode, 0)
        self.assertEqual(check(root).returncode, 0, "without the copy, the refreshed manifest hides the edit")
        proc = check(root, "--fixture", str(fx))
        self.assertEqual(proc.returncode, 1, proc.stdout)
        self.assertEqual(drifted(proc.stdout), {"clean fixture SpecrPrelude.lean  (= SpecrPrelude.lean)"})

    def test_the_clean_fixture_is_pending_only_when_no_copy_exists(self):
        root = self.copy()
        empty = self.tmpdir()
        proc = check(root, "--fixture", str(empty))
        self.assertEqual(proc.returncode, 0, proc.stdout)
        self.assertEqual(sum(line.startswith("PENDING") for line in proc.stdout.splitlines()), 2)
        fx = self.fixture_of(root)
        (fx / "MiniRustSlice.lean").unlink()
        proc = check(root, "--fixture", str(fx))
        self.assertEqual(proc.returncode, 1, proc.stdout)
        self.assertEqual(drifted(proc.stdout), {"clean fixture MiniRustSlice.lean  (= generated/MiniRustSlice.lean)"})

    def fake_minirust(self) -> Path:
        """A git checkout with a `spec/` directory; returns it (its HEAD is not the real pin)."""
        mr = self.tmpdir() / "minirust"
        (mr / "spec").mkdir(parents=True)
        (mr / "spec" / "README.md").write_text("fake\n")
        env = {**os.environ, "GIT_AUTHOR_NAME": "t", "GIT_AUTHOR_EMAIL": "t@t", "GIT_COMMITTER_NAME": "t",
               "GIT_COMMITTER_EMAIL": "t@t"}
        for cmd in (["init", "-q"], ["add", "."], ["commit", "-q", "-m", "fake"]):
            subprocess.run(["git", "-C", str(mr), *cmd], check=True, env=env, stdout=subprocess.PIPE)
        return mr

    def fake_frontend(self, ast: bytes) -> Path:
        tmp = self.tmpdir()
        (tmp / "ast.json").write_bytes(ast)
        return executable(tmp / "frontend", f"import sys\nsys.stdout.buffer.write(open({str(tmp / 'ast.json')!r}, 'rb').read())\n")

    def pin_copy_to(self, root: Path, mr: Path) -> None:
        rev = subprocess.run(["git", "-C", str(mr), "rev-parse", "HEAD"], stdout=subprocess.PIPE, text=True,
                             check=True).stdout.strip()
        p = root / "slice.json"
        cfg = json.loads(p.read_text())
        cfg["minirust_revision"] = rev
        p.write_text(json.dumps(cfg, indent=2) + "\n")

    def test_from_source_compares_the_front_end_ast(self):
        root = self.copy()
        mr = self.fake_minirust()
        self.pin_copy_to(root, mr)
        pinned = gzip.decompress((root / "pinned" / "ast.json.gz").read_bytes())
        same = check(root, "--from-source", "--frontend", str(self.fake_frontend(pinned)), "--minirust", str(mr))
        self.assertIn("identical  pinned/ast.json.gz", same.stdout, "control: the same AST " + same.stdout + same.stderr)
        other = pinned.replace(b"asking for a too large allocation", b"asking for a too big allocation", 1)
        self.assertNotEqual(other, pinned)
        proc = check(root, "--from-source", "--frontend", str(self.fake_frontend(other)), "--minirust", str(mr))
        self.assertEqual(proc.returncode, 1, proc.stdout)
        self.assertIn(f"pinned/ast.json.gz  (front end on {mr})", drifted(proc.stdout))

    def test_from_source_refuses_a_checkout_off_the_pin(self):
        root = self.copy()
        mr = self.fake_minirust()  # its HEAD is not slice.json's pin
        pinned = gzip.decompress((root / "pinned" / "ast.json.gz").read_bytes())
        proc = check(root, "--from-source", "--frontend", str(self.fake_frontend(pinned)), "--minirust", str(mr))
        self.assertNotEqual(proc.returncode, 0, proc.stdout)
        self.assertIn("not the pin", proc.stderr)
        self.assertNotIn("identical  pinned/ast.json.gz", proc.stdout)

    def test_write_from_source_rewrites_the_pinned_ast(self):
        root = self.copy()
        mr = self.fake_minirust()
        self.pin_copy_to(root, mr)
        pinned = gzip.decompress((root / "pinned" / "ast.json.gz").read_bytes())
        other = pinned.replace(b"asking for a too large allocation", b"asking for a too big allocation", 1)
        w = write(root, "--from-source", "--frontend", str(self.fake_frontend(other)), "--minirust", str(mr))
        self.assertEqual(w.returncode, 0, w.stdout + w.stderr)
        self.assertEqual(gzip.decompress((root / "pinned" / "ast.json.gz").read_bytes()), other)
        self.assertEqual(check(root).returncode, 0, "write left a consistent tree")

    # `--clean`: each acceptance condition, judged on a canned report

    GOOD = {"failed_count": 0, "success_count": 1, "decl_count": 1, "errors": [], "assumptions": [],
            "diverged": False, "trust_summary": {"sorry_axioms": 0, "sorry_terms_minted": 0,
                                                 "kernel_check_failures": 0}}

    def fake_clean(self, report: dict, sleep: float = 0) -> Path:
        tmp = self.tmpdir()
        (tmp / "report.json").write_text(json.dumps(report))
        return executable(tmp / "clean", f"import sys, time\ntime.sleep({sleep})\n"
                                         f"sys.stdout.write(open({str(tmp / 'report.json')!r}).read())\n")

    def clean_ok(self, report, timeout: float = 60, sleep: float = 0) -> bool:
        return regen.clean_check(SPECR, self.fake_clean(report, sleep), timeout)

    def with_(self, **changes) -> dict:
        rep = json.loads(json.dumps(self.GOOD))
        for k, v in changes.items():
            if k in rep["trust_summary"]:
                rep["trust_summary"][k] = v
            else:
                rep[k] = v
        return rep

    def test_clean_accepts_only_a_clean_report(self):
        self.assertTrue(self.clean_ok(self.GOOD), "control: the clean report is accepted")
        theorem = json.loads((SPECR / "generated" / "conformance_index.json").read_text())["theorems"][0]["theorem"]
        for name, rep in [("a failed declaration", self.with_(failed_count=1)),
                          ("a sorry axiom", self.with_(sorry_axioms=1)),
                          ("a sorry term", self.with_(sorry_terms_minted=1)),
                          ("a kernel-check failure", self.with_(kernel_check_failures=1)),
                          ("an assumption", self.with_(assumptions=["Classical.em"])),
                          ("a divergence", self.with_(diverged=True)),
                          ("a failed conformance theorem", self.with_(errors=[f"{theorem}: type mismatch"]))]:
            with self.subTest(name):
                self.assertFalse(self.clean_ok(rep), name)

    def test_clean_without_the_sorry_counter_fails_closed(self):
        for drop in ("sorry_terms_minted", "trust_summary"):
            rep = self.with_()
            if drop == "trust_summary":
                del rep["trust_summary"]
            else:
                del rep["trust_summary"][drop]
            out = io.StringIO()
            with contextlib.redirect_stdout(out):
                self.assertFalse(self.clean_ok(rep), drop)
            # the refusal names why, so an old clean is not mistaken for a red proof
            self.assertIn("older than this check needs", out.getvalue(), drop)

    def test_clean_with_no_report_fails(self):
        self.assertFalse(regen.clean_check(SPECR, executable(self.tmpdir() / "clean", "print('not json')\n"), 60))

    def test_a_clean_that_never_finishes_is_killed(self):
        self.assertTrue(self.clean_ok(self.GOOD, timeout=60, sleep=0.1), "control: a slow but finishing run")
        self.assertFalse(self.clean_ok(self.GOOD, timeout=1, sleep=30))



if __name__ == "__main__":
    unittest.main()
