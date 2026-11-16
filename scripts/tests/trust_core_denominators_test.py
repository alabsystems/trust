#!/usr/bin/env python3
"""Controls for scripts/trust_core/denominators.py (E0.12, the Stage 0.5 denominators).

* The REAL checker on the REAL inputs: every record under docs/trust-core/denominators/ re-measured
  at its pin by its own script, the design at HEAD and DENOMINATORS.md. It exits 0 and publishes the
  counts asserted here.
* Every mutation of a temporary copy of a record, the document or the design makes the CHECKER report
  the violation it introduces, beside an unmutated control: a drifted value (the record's own script
  re-measures and refuses it), a dropped or empty predicate, an unpinned input, a pin that is not a
  commit, a blocked row without its reason or unblock condition, a status outside the vocabulary, a
  measured row without a value, a row no Stage 0.5 item owns, an unregistered or missing record, a
  design item without a denominator, a changed design number, a stale document block, and an unchecked
  or drifted citation.
* Each record script's own self-test, where it has one (templates, std-surface, odt).
* The artifact cache: imports re-measures from the cache alone, with build/ and the atpkg store unseen.
* odt's -Zbuild-std inputs, on the real module: only crates.io archives with library/Cargo.lock's sha256
  reach cargo (another digest refuses, no cache is exit 3), and the export holds exactly the crates/
  directories library/'s manifests name.
* HOST-BOUND INPUTS. imports (its pinned dylibs), std-surface (its stage1-std build) and odt (a Trust
  toolchain built from the pinned library/ tree with its targo, Lean 4.8.0, the crates.io archives
  library/Cargo.lock pins in the cargo cache) re-measure only on a host that holds
  them. Each script then exits 3 and the gate reports the record NOT RE-MEASURED and exits 3: never
  drift, never a pass. The exit-3 paths are exercised here on every host (hermetically). On a host that
  lacks the inputs, the two real-input tests assert exactly that behaviour and are then reported as
  SKIPPED with the missing inputs named; on the measuring host they run in full.

Needs Python 3.11 or later (common.py); scripts/check_script_tests.sh runs it with python3.14.

Author: Andrew Yates <andrewyates.name@gmail.com>
Copyright 2026 Andrew Yates | License: Apache-2.0 OR MIT
"""

import contextlib
import hashlib
import importlib.util
import io
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock

ROOT = Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "scripts" / "trust_core" / "denominators.py"
SPEC = importlib.util.spec_from_file_location("trust_core_denominators", SCRIPT)
M = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(M)
C = M.C
RECORDS, DOC = ROOT / M.RECORDS_REL, ROOT / M.DOC_REL

# The published counts (DENOMINATORS.md's pass line). A change here is a change to a record.
PUBLISHED = {
    "items": 10, "items_unmapped": 0, "records": 7, "rows": 365, "measured": 348, "blocked": 17,
    "without_predicate": 0, "blocked_unexplained": 0, "inputs_unpinned": 0, "readings": 23,
}


def replace_once(text, old, new):
    assert text.count(old) == 1, (old, text.count(old))
    return text.replace(old, new)


def bump_once(text, pattern):
    """`text` with the one integer `pattern`'s group 1 matches raised by one."""
    hits = list(re.finditer(pattern, text))
    assert len(hits) == 1, (pattern, len(hits))
    m = hits[0]
    return text[:m.start(1)] + str(int(m.group(1)) + 1) + text[m.end(1):]


def bump_value(block):
    """A [[row]] block with its `value` raised by one."""
    return bump_once(block, r"\nvalue = (\d+)\n")


def edit_row(text, name, edit):
    """`edit` applied to the [[row]] block of the record text whose name is `name`."""
    parts = re.split(r"\n(?=\[\[)", text)
    hits = [i for i, p in enumerate(parts) if p.startswith("[[row]]") and f'\nname = "{name}"\n' in p + "\n"]
    assert len(hits) == 1, (name, len(hits))
    parts[hits[0]] = edit(parts[hits[0]])
    return "\n".join(parts)


def edit_table(text, header, edit):
    """`edit` applied to the body of the TOML table `[header]` (up to the next table header)."""
    start = text.index(f"\n[{header}]\n") + len(f"\n[{header}]\n")
    end = text.find("\n[", start)
    end = len(text) if end < 0 else end
    return text[:start] + edit(text[start:end]) + text[end:]


class RealInputs(unittest.TestCase):
    def test_every_record_reproduces_at_its_pin_and_the_counts_are_published(self):
        result = M.check()
        self.assertEqual(result.findings.violations, [])
        self.assertEqual(result.counts, PUBLISHED)
        self.assertEqual(sorted(result.runs), sorted(M.RECORDS))
        if result.unavailable:
            # Only the records with host-bound inputs may be unavailable, each by its script's exit 3.
            self.assertLessEqual(set(result.unavailable), HOST_BOUND, result.unavailable)
            for key in result.unavailable:
                self.assertEqual(result.runs[key][0], M.UNAVAILABLE_EXIT, result.runs[key][1][-2000:])
            self.assertTrue(all(code == 0 for key, (code, _o, _s) in result.runs.items()
                                if key not in result.unavailable), result.runs)
            self.skipTest("not re-measured on this host (pinned inputs absent): "
                          + "; ".join(f"{k}: {v}" for k, v in sorted(result.unavailable.items())))
        self.assertTrue(all(code == 0 for code, _out, _secs in result.runs.values()), result.runs)
        self.assertIn(f"* Records: {PUBLISHED['records']}; rows: {PUBLISHED['rows']} ({PUBLISHED['measured']} measured, "
                      f"{PUBLISHED['blocked']} blocked).", DOC.read_text(encoding="utf-8"))

    def test_cli_without_re_measurement_exits_zero(self):
        run = subprocess.run([sys.executable, str(SCRIPT), "--no-run"], capture_output=True, text=True)
        self.assertEqual(run.returncode, 0, run.stderr)
        self.assertIn(f"denominators: OK (E0.12: {PUBLISHED['items']} Stage 0.5 items, {PUBLISHED['records']} records, "
                      f"{PUBLISHED['rows']} rows: {PUBLISHED['measured']} measured, {PUBLISHED['blocked']} blocked, "
                      "0 without a predicate", run.stdout)

    def test_the_design_list_is_the_item_table(self):
        findings = C.Findings()
        items = M.stage_items(findings, M.design_text(ROOT, None))
        self.assertEqual(findings.violations, [])
        self.assertEqual([text for _line, text in items], [item.bullet for item in M.ITEMS])

    def test_record_scripts_pass_their_self_tests(self):
        pin = C.tomllib.loads((RECORDS / "templates.toml").read_text(encoding="utf-8"))["measured_at_commit"]
        # templates' self-test mutates trust-cg's sources at the gitlink the pin names.
        for key, argv in (("templates", ["--self-test", "--rev", pin]), ("std-surface", ["--self-test"]),
                          ("odt", ["--self-test"])):
            with self.subTest(key):
                run = subprocess.run([sys.executable, str(ROOT / M.SCRIPTS_REL / f"{key}.py"), *argv],
                                     capture_output=True, text=True, cwd=ROOT)
                self.assertEqual(run.returncode, 0, run.stdout[-2000:] + run.stderr[-2000:])

    def test_imports_re_measures_from_the_artifact_cache_alone(self):
        cache = M.artifacts_root(None) / "imports"
        if not cache.is_dir():
            self.skipTest(f"the artifact cache {cache} is not on this host: fill it with `python3.14 "
                          "scripts/trust_core/denominators.py --stash` on a host whose build/ holds the pinned inputs "
                          "(the exit-3 path without it is HostBound.test_imports_without_its_inputs_exits_3)")
        record = RECORDS / "imports.toml"
        pin = C.tomllib.loads(record.read_text(encoding="utf-8"))["measured_at_commit"]
        with tempfile.TemporaryDirectory() as tmp:
            run = subprocess.run([sys.executable, str(ROOT / M.SCRIPTS_REL / "imports.py"), "--check", "--rev", pin,
                                  "--record", str(record), "--build-dir", str(Path(tmp) / "build"),
                                  "--atpkg-store", str(Path(tmp) / "store"), "--artifact-dir", str(cache)],
                                 capture_output=True, text=True, cwd=ROOT)
        self.assertEqual(run.returncode, 0, run.stderr[-3000:])
        self.assertIn("(artifact dir)", run.stderr)


# The records whose scripts read inputs outside git that only some hosts hold.
HOST_BOUND = {"imports", "std-surface", "odt"}


class HostBound(unittest.TestCase):
    """The exit-3 contract, on every host: a pinned input this host does not hold is reported as such by the
    record's script (exit 3, UNAVAILABLE) and by the gate (exit 3, NOT RE-MEASURED, no OK line)."""

    def script(self, key, *argv):
        return subprocess.run([sys.executable, str(ROOT / M.SCRIPTS_REL / f"{key}.py"), *argv],
                              capture_output=True, text=True, cwd=ROOT)

    def test_imports_without_its_inputs_exits_3(self):
        pin = C.tomllib.loads((RECORDS / "imports.toml").read_text(encoding="utf-8"))["measured_at_commit"]
        with tempfile.TemporaryDirectory() as tmp:
            run = self.script("imports", "--check", "--rev", pin, "--record", str(RECORDS / "imports.toml"),
                              "--build-dir", str(Path(tmp) / "build"), "--atpkg-store", str(Path(tmp) / "store"))
        self.assertEqual(run.returncode, 3, run.stderr[-2000:])
        self.assertIn("imports: UNAVAILABLE:", run.stderr)

    def test_std_surface_without_its_host_build_exits_3(self):
        with tempfile.TemporaryDirectory() as tmp:
            run = self.script("std-surface", "--check", "--record", str(RECORDS / "std-surface.toml"),
                              "--host-build", str(Path(tmp) / "no-build"))
        self.assertEqual(run.returncode, 3, run.stderr[-2000:])
        self.assertIn("std-surface: UNAVAILABLE:", run.stderr)

    def test_odt_without_its_toolchain_exits_3(self):
        pin = C.tomllib.loads((RECORDS / "odt.toml").read_text(encoding="utf-8"))["measured_at_commit"]
        run = self.script("odt", "--check", "--rev", pin, "--record", str(RECORDS / "odt.toml"),
                          "--trustc", "/nonexistent/trustc")
        self.assertEqual(run.returncode, 3, run.stderr[-2000:])
        self.assertIn("odt: UNAVAILABLE:", run.stderr)

    def test_odt_without_a_cargo_registry_exits_3(self):
        # std's per-target rows need the crates.io archives library/Cargo.lock pins, from the host's cargo cache.
        pin = C.tomllib.loads((RECORDS / "odt.toml").read_text(encoding="utf-8"))["measured_at_commit"]
        with tempfile.TemporaryDirectory() as tmp:
            run = subprocess.run([sys.executable, str(ROOT / M.SCRIPTS_REL / "odt.py"), "--check", "--rev", pin,
                                  "--record", str(RECORDS / "odt.toml")], capture_output=True, text=True, cwd=ROOT,
                                 env={**os.environ, "CARGO_HOME": tmp})
        self.assertEqual(run.returncode, 3, run.stderr[-2000:])
        self.assertIn("odt: UNAVAILABLE:", run.stderr)

    def test_the_gate_reports_an_unavailable_record_and_is_not_ok(self):
        fake = [sys.executable, "-c", "import sys; print('x: UNAVAILABLE: a pinned input is absent', file=sys.stderr); "
                                      "sys.exit(3)"]
        out, err = io.StringIO(), io.StringIO()
        with mock.patch.object(M, "run_argv", lambda *a, **k: fake), \
                contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
            code = M.main(["--only", "ui-tests"])
        self.assertEqual(code, M.UNAVAILABLE_EXIT, err.getvalue())
        self.assertIn("NOT RE-MEASURED on this host", err.getvalue())
        self.assertIn("ui-tests: x: UNAVAILABLE: a pinned input is absent", err.getvalue())
        self.assertNotIn("denominators: OK", out.getvalue())

    def test_a_failing_record_is_a_violation_not_unavailable(self):
        fake = [sys.executable, "-c", "import sys; sys.exit(1)"]
        with mock.patch.object(M, "run_argv", lambda *a, **k: fake):
            result = M.check(only=("ui-tests",))
        self.assertEqual(result.unavailable, {})
        self.assertTrue(any(v.startswith("RUN: ui-tests") for v in result.findings.violations), result.findings.violations)


class OdtBuildStd(unittest.TestCase):
    """odt's -Zbuild-std inputs, on the REAL module: the crates.io archives it hands cargo are the ones
    library/Cargo.lock pins (a cached archive with another sha256 refuses the run, no cache is exit 3), and the
    export holds exactly what library/'s manifests name outside library/."""

    @classmethod
    def setUpClass(cls):
        spec = importlib.util.spec_from_file_location("trust_core_denominators_odt", ROOT / M.SCRIPTS_REL / "odt.py")
        cls.O = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(cls.O)
        cls.pin = C.tomllib.loads((RECORDS / "odt.toml").read_text(encoding="utf-8"))["measured_at_commit"]

    def registry(self, tmp, archive):
        index = Path(tmp) / "registry" / "index" / "index.crates.io-0000000000000000"
        (index / ".cache" / "li" / "bc").mkdir(parents=True)
        (index / ".cache" / "li" / "bc" / "libc").write_bytes(b"index entry")
        cache = Path(tmp) / "registry" / "cache" / index.name
        cache.mkdir(parents=True)
        (cache / "libc-0.2.1.crate").write_bytes(archive)
        return index.name

    def seed(self, tmp, home):
        lock = [("libc", "0.2.1", "registry+https://github.com/rust-lang/crates.io-index", hashlib.sha256(b"pinned").hexdigest()),
                ("std", "0.0.0", "", "")]
        with mock.patch.dict(os.environ, {"CARGO_HOME": tmp}):
            return self.O.seed_cargo_home(home, lock)

    def test_an_archive_with_the_lock_checksum_is_seeded(self):
        with tempfile.TemporaryDirectory() as tmp, tempfile.TemporaryDirectory() as home:
            name = self.registry(tmp, b"pinned")
            self.assertEqual(list(self.seed(tmp, home)), [("libc", "0.2.1")])
            self.assertEqual((Path(home) / "registry" / "cache" / name / "libc-0.2.1.crate").read_bytes(), b"pinned")
            self.assertTrue((Path(home) / "registry" / "index" / name / ".cache" / "li" / "bc" / "libc").is_file())

    def test_an_archive_that_is_not_the_lock_checksum_refuses(self):
        with tempfile.TemporaryDirectory() as tmp, tempfile.TemporaryDirectory() as home:
            self.registry(tmp, b"tampered")
            with self.assertRaises(self.O.Refusal) as refused:
                self.seed(tmp, home)
            self.assertNotIsInstance(refused.exception, self.O.Unavailable)
            self.assertIn("not library/Cargo.lock's", str(refused.exception))

    def test_no_registry_is_unavailable(self):
        with tempfile.TemporaryDirectory() as tmp, tempfile.TemporaryDirectory() as home:
            with self.assertRaises(self.O.Unavailable):
                self.seed(tmp, home)

    def test_the_export_is_what_library_names_outside_library(self):
        saved = self.O.REV
        try:
            self.O.REV = self.pin
            self.assertEqual(sorted(self.O.library_external_paths()), ["crates/trust-bignum", "crates/trust-memchr"])
            real = self.O.git_blobs

            def outside(paths, rev=None, repo=self.O.REPO):
                blobs = real(paths, rev, repo)
                blobs["library/Cargo.toml"] += b"\nzz = { path = '../vendor/zz' }\n"
                return blobs
            with mock.patch.object(self.O, "git_blobs", outside), self.assertRaises(self.O.Refusal) as refused:
                self.O.library_external_paths()
            self.assertIn("not a crates/ crate", str(refused.exception))
        finally:
            self.O.REV = saved


class HostsRoster(unittest.TestCase):
    """hosts.py compares only the roster facts of this host's recorded probe: an OS update is an observation
    carried from the record, a changed roster fact (memory, CPU, Rosetta) is a failure."""

    @classmethod
    def setUpClass(cls):
        spec = importlib.util.spec_from_file_location("trust_core_denominators_hosts", ROOT / M.SCRIPTS_REL / "hosts.py")
        cls.H = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(cls.H)
        record = C.tomllib.loads((RECORDS / "hosts.toml").read_text(encoding="utf-8"))
        cls.probe = json.loads(record["confirmed"][0]["probe_json"])

    def test_an_os_update_is_an_observation_not_a_roster_fact(self):
        live = json.loads(json.dumps(self.probe))
        live["kernel_release"] = "99.0.0"
        live.setdefault("darwin", {})["kern.osproductversion"] = "99.0"
        self.assertEqual(self.H.roster_facts(live), self.H.roster_facts(self.probe))
        self.assertEqual(self.H.observation_changes(self.probe, live), ["darwin.kern.osproductversion", "kernel_release"])

    def test_a_roster_fact_change_is_seen(self):
        for section, key, value in (("darwin", "hw.memsize", 1), ("rosetta", "executes", True),
                                    ("x86isa", "acl2_on_path", True), ("", "machine", "x86_64")):
            with self.subTest(key):
                live = json.loads(json.dumps(self.probe))
                (live if section == "" else live.setdefault(section, {}))[key] = value
                self.assertNotEqual(self.H.roster_facts(live), self.H.roster_facts(self.probe))


class Units(unittest.TestCase):
    def test_pins_are_object_ids_and_digests_only(self):
        hex40, hex64 = "a" * 40, "b" * 64
        self.assertEqual(M.pins_in({"x": f"commit {hex40}", "y": [f"sha256:{hex64}", {"z": hex64}]}),
                         [hex40, f"sha256:{hex64}", hex64])
        self.assertEqual(M.pins_in({"short": "a" * 39, "long": "a" * 41, "word": "superproject HEAD", "n": 40}), [])

    def test_the_pinned_run_passes_the_pin_and_the_current_run_passes_head(self):
        records = M.load_records(C.Findings(), ROOT, RECORDS, ())
        for key, rec in records.items():
            with self.subTest(key):
                pinned, current = (M.run_argv(ROOT, rec, flag, Path("/nonexistent")) for flag in (False, True))
                self.assertIn("--check", pinned)
                if key == "std-surface":  # its --check re-measures at its recorded commit
                    self.assertNotIn("--rev", pinned)
                    self.assertIn("--current", current)
                else:
                    self.assertEqual(pinned[pinned.index("--rev") + 1], rec.data["measured_at_commit"])
                    self.assertEqual(current[current.index("--rev") + 1], "HEAD")

    def test_the_stash_refuses_bytes_that_are_not_the_pin(self):
        with tempfile.TemporaryDirectory() as tmp:
            src, dest = Path(tmp) / "src", Path(tmp) / "out" / "dest"
            src.write_bytes(b"pinned")
            good = M.sha256_file(src)
            self.assertIsNotNone(M.copy_checked(src, dest, "0" * 64))
            self.assertFalse(dest.exists())
            self.assertIsNone(M.copy_checked(src, dest, good))
            self.assertEqual(dest.read_bytes(), b"pinned")


class Mutations(unittest.TestCase):
    def setUp(self):
        self._tmp = tempfile.TemporaryDirectory()
        self.tmp = Path(self._tmp.name)
        self.records = self.tmp / "records"
        shutil.copytree(RECORDS, self.records)
        self.doc = self.tmp / "DENOMINATORS.md"
        shutil.copyfile(DOC, self.doc)
        self.design = M.design_text(ROOT, None)

    def tearDown(self):
        self._tmp.cleanup()

    def mutate(self, key, edit):
        path = self.records / f"{key}.toml"
        path.write_text(edit(path.read_text(encoding="utf-8")), encoding="utf-8")

    def check(self, run=False, only=(), design=None, doc_text=None):
        if doc_text is not None:
            self.doc.write_text(doc_text, encoding="utf-8")
        design_path = None
        if design is not None:
            design_path = self.tmp / "design.md"
            design_path.write_text(design, encoding="utf-8")
        return M.check(ROOT, self.records, self.doc, design_path, tuple(only), run=run).findings.violations

    def assert_violation(self, violations, *fragments):
        for fragment in fragments:
            self.assertTrue(any(fragment in v for v in violations), f"{fragment!r} not in {violations}")

    def test_control_copies_pass(self):
        self.assertEqual(self.check(), [])

    def test_a_drifted_value_fails_the_pinned_re_measurement(self):
        # The recorded value plus one, whatever the last re-measurement recorded (a value spelled here
        # stops matching the record the next time its pin moves).
        self.mutate("ui-tests", lambda t: edit_row(t, "strict-pass.nll", bump_value))
        self.mutate("checkpoint-a", lambda t: edit_row(t, "bridge-corpus.files", bump_value))
        violations = self.check(run=True, only=("ui-tests", "checkpoint-a"))
        self.assert_violation(violations, "RUN: ui-tests:", "RUN: checkpoint-a:")
        self.assertFalse(any(v.startswith("RUN: templates") for v in violations), violations)

    def test_an_unmutated_record_reproduces_from_its_copy(self):
        self.assertEqual(self.check(run=True, only=("ui-tests",)), [])

    def test_a_dropped_or_empty_predicate_fails(self):
        self.mutate("templates", lambda t: edit_row(t, "reloc.coff.x86_64", lambda b: re.sub(r"\npredicate = .*", "", b, count=1)))
        self.mutate("hosts", lambda t: edit_row(t, "scan.occurrences", lambda b: re.sub(r'\npredicate = .*', '\npredicate = " "', b, count=1)))
        self.assert_violation(self.check(), "templates.toml row 'reloc.coff.x86_64': no predicate",
                              "hosts.toml row 'scan.occurrences': no predicate")

    def test_an_unpinned_input_fails(self):
        self.mutate("ui-tests", lambda t: edit_table(t, "inputs.trust", lambda b: re.sub(r"[0-9a-f]{40,64}", "unpinned", b)))
        self.assert_violation(self.check(), "ui-tests.toml: inputs.trust carries no pin")

    def test_a_pin_that_is_not_a_commit_fails(self):
        self.mutate("templates", lambda t: re.sub(r'(?m)^measured_at_commit = "[0-9a-f]{40}"$',
                                                  f'measured_at_commit = "{"0" * 40}"', t))
        self.mutate("odt", lambda t: re.sub(r'(?m)^measured_at_commit = .*\n', "", t))
        self.assert_violation(self.check(), f"templates.toml: measured_at_commit {'0' * 40} is not a commit",
                              "odt.toml: `measured_at_commit` is None")

    def test_a_blocked_row_needs_its_reason_and_unblock_condition(self):
        self.mutate("checkpoint-a", lambda t: edit_row(t, "straight-line.population", lambda b: re.sub(r"\nunblock = .*", "", b)))
        self.mutate("imports", lambda t: edit_row(t, "imports.std.x86_64-unknown-linux-gnu", lambda b: re.sub(r"\nblocked = .*", "", b)))
        self.assert_violation(self.check(), "checkpoint-a.toml row 'straight-line.population': blocked with no `unblock`",
                              "imports.toml row 'imports.std.x86_64-unknown-linux-gnu': blocked with no `blocked`")

    def test_status_and_value_shape(self):
        self.mutate("hosts", lambda t: edit_row(t, "x86-64-amd.shortfall", lambda b: replace_once(b, 'status = "blocked"', 'status = "blocked: owner"')))
        self.mutate("std-surface", lambda t: edit_row(t, "S.std", lambda b: re.sub(r"\nvalue = \d+", "", b)))
        self.assert_violation(self.check(), "hosts.toml row 'x86-64-amd.shortfall': status 'blocked: owner' is neither",
                              "std-surface.toml row 'S.std': measured with no integer `value`")

    def test_a_row_no_item_owns_fails(self):
        self.mutate("templates", lambda t: edit_row(t, "unwind.seh.coff.x86_64", lambda b: replace_once(b, 'name = "unwind.seh.coff.x86_64"', 'name = "seh.coff.x86_64"')))
        self.assert_violation(self.check(), "templates.toml row 'seh.coff.x86_64' belongs to 0 items",
                              "item record-kinds: headline row templates.toml 'unwind.seh.coff.x86_64' is not one of its rows")

    def test_a_dropped_census_row_fails(self):
        # The prelude's `Quot` and std's per-target rows are headline rows of the ODT item: dropping one fails.
        def drop(text, name):
            parts = re.split(r"\n(?=\[\[)", text)
            kept = [p for p in parts if not (p.startswith("[[row]]") and f'\nname = "{name}"\n' in p + "\n")]
            assert len(kept) == len(parts) - 1, name
            return "\n".join(kept)
        self.mutate("odt", lambda t: drop(drop(t, "clean.prelude.quot_type_formers"), "rust.std.adts@x86_64-unknown-linux-gnu"))
        self.assert_violation(self.check(),
                              "item odt: headline row odt.toml 'clean.prelude.quot_type_formers' is not one of its rows",
                              "item odt: headline row odt.toml 'rust.std.adts@x86_64-unknown-linux-gnu' is not one of its rows")

    def test_records_and_scripts_are_one_set(self):
        shutil.copyfile(self.records / "ui-tests.toml", self.records / "extra.toml")
        (self.records / "hosts.toml").unlink()
        self.assert_violation(self.check(), "REGISTRY: docs/trust-core/denominators/extra.toml is not a registered record",
                              "REGISTRY: record hosts:")

    def test_a_design_item_without_a_denominator_fails(self):
        design = replace_once(self.design, "\n* **E0.12** All published", "\n* The Checkpoint B relocation census.\n* **E0.12** All published")
        self.assert_violation(self.check(design=design), "Stage 0.5 item 'The Checkpoint B relocation census.' has no denominator")

    def test_a_changed_design_number_fails(self):
        design = replace_once(self.design, "starting from 294 and 232 opcode variants", "starting from 295 and 232 opcode variants")
        design = replace_once(design, "finds 215 [M†]", "finds 216 [M†]")
        self.assert_violation(self.check(design=design),
                              "ITEMS: item templates: the design's Stage 0.5 list has no item",
                              "MDAGGER: reading templates/a64.opcode-variants (294): the quote",
                              "MDAGGER: reading ui-tests/loose-pass (215): the quote")

    def test_each_reading_kind_refuses_a_value_it_does_not_describe(self):
        # other-predicate: the design's number must be the value; not-reproduced: it must not be;
        # blocked: the row must be blocked.
        self.mutate("imports", lambda t: edit_row(t, "imports.rustc_driver.aarch64-apple-darwin.cxx_mangled",
                                                  lambda b: replace_once(b, "value = 93", "value = 94")))
        self.mutate("imports", lambda t: edit_row(t, "imports.rustc_driver.aarch64-apple-darwin.bound_to.libc++",
                                                  lambda b: replace_once(b, "value = 96", "value = 93")))
        self.mutate("checkpoint-a", lambda t: edit_row(t, "llvm-differential.suite-programs",
                                                       lambda b: replace_once(b, 'status = "blocked"',
                                                                              'value = 129\nstatus = "measured"')))
        self.assert_violation(self.check(),
                              "reading imports/imports.rustc_driver.aarch64-apple-darwin.cxx_mangled (93): an "
                              "`other-predicate` reading needs the value 93",
                              "reading imports/imports.rustc_driver.aarch64-apple-darwin.bound_to.libc++ (93): a "
                              "`not-reproduced` reading needs a value other than 93",
                              "reading llvm-differential/llvm-differential.suite-programs (129): a `blocked` reading "
                              "needs a blocked row")

    def test_a_value_the_design_reading_contradicts_fails(self):
        self.mutate("imports", lambda t: edit_row(t, "imports.std.aarch64-apple-darwin", lambda b: replace_once(b, "value = 195", "value = 196")))
        self.mutate("templates", lambda t: edit_row(t, "a64.opcode-variants", lambda b: replace_once(b, '  "TlsDescCall",\n', "")))

        def drop_first_added(block):
            dropped, n = re.subn(r'(\nadded_since_design_pin = \[\n)  "[^"\n]*",\n', r"\1", block, count=1)
            assert n == 1, "strict-pass records no path added since the design's pin"
            return dropped

        self.mutate("ui-tests", lambda t: edit_row(t, "strict-pass", drop_first_added))
        self.assert_violation(self.check(),
                              "MDAGGER: reading imports/imports.std.aarch64-apple-darwin (195): the design says 195, the row measures 196",
                              "MDAGGER: reading templates/a64.opcode-variants (294): at the design's pin the row gives 295",
                              "MDAGGER: reading ui-tests/strict-pass (193): at the design's pin the row gives 194")

    def test_a_design_header_pin_the_record_was_not_measured_at_fails(self):
        header = "**Written read-only against** superproject `1b603b73bf`"
        moved = replace_once(self.design, header, "**Written read-only against** superproject `8c39674bbb`")
        self.assert_violation(self.check(design=moved),
                              "MDAGGER: ui-tests: [inputs.design].revision '1b603b73bf5af3758e11bce8fe91c491d6dc9156' "
                              "is not 8c39674bbb73659e90920bab17e090bd5b70231f, the commit the design header names")
        unknown = replace_once(self.design, header, "**Written read-only against** superproject `0000000000`")
        self.assert_violation(self.check(design=unknown),
                              "MDAGGER: ui-tests: [inputs.design] records the design's pin "
                              "'1b603b73bf5af3758e11bce8fe91c491d6dc9156', but the design header names 0000000000, "
                              "which is not one commit of this clone")

    def test_document_mutations(self):
        text = self.doc.read_text(encoding="utf-8")
        cases = [
            ("stale block", bump_once(text, r"\| `strict-pass` \| (\d+) \| measured \|"),
             "DOC: the published `denominators-item-ui-tests` block differs"),
            ("unchecked citation", replace_once(text, "## Limits\n", "## Limits\n\nSee design:4029.\n"),
             "line citation 'design:4029' is not in the checked"),
            ("quote drift", replace_once(text, "design:4015 «Relocation and unwind record kinds.»", "design:4015 «Relocation kinds.»"),
             "design:4015 does not contain"),
            ("missing block", replace_once(text, "<!-- denominators-blocked:end -->\n", ""), "the `denominators-blocked` block markers are missing"),
        ]
        for label, doc, fragment in cases:
            with self.subTest(label):
                self.assert_violation(self.check(doc_text=doc), fragment)


if __name__ == "__main__":
    unittest.main(verbosity=1)
