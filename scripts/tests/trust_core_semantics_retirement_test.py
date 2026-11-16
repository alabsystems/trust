#!/usr/bin/env python3
"""Controls for scripts/trust_core/semantics_retirement.py (D0.4, the retirement plan of Rust's partial semantics).

* The REAL checker on the REAL inputs (this repository at HEAD, the submodules at their HEAD gitlinks, the
  pinned MiniRust clone, the table, the document and the review registry) exits 0 and publishes the measured
  values asserted here.
* Every mutation, of a temporary copy of the table, document or registry or of a repository tree (a real commit
  built in a temporary repository that borrows the repository's objects, so every git grep and batched read the
  checker runs is the real one), makes the checker report the violation it introduces, beside an unmutated
  control. A mechanical mutation names its predicate. A judgment mutation (a changed role, reason, option, prose
  section or section order) passes every mechanical predicate and fails REVIEW only, and passes once a new
  review record reviews its digest.

The shared layers (pins, citations, uniqueness, blocks, reviews) are tested in trust_core_common_test.py. The
crate graph runs `targo metadata`; a missing targo is a FAILURE that says so, never a skip.

Author: Andrew Yates <andrewyates.name@gmail.com>
Copyright 2026 Andrew Yates | License: Apache-2.0 OR MIT
"""

import importlib.util
import os
import re
import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "scripts" / "trust_core" / "semantics_retirement.py"
SPEC = importlib.util.spec_from_file_location("trust_core_semantics_retirement", SCRIPT)
SR = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(SR)
C = SR.C
TABLE, DOC, REGISTRY = ROOT / SR.TABLE_REL, ROOT / SR.DOC_REL, ROOT / SR.REGISTRY_REL
TREES: dict = {}  # shared by every run, so repeated runs reuse the trees' caches
MEASURE = object()  # run_inputs(metadata=MEASURE) runs `targo metadata` on the mutated trees instead of reusing the real graph
REAL = {}

# The published measurements (the counts block of SEMANTICS_RETIREMENT.md): each is recorded in the table or held to
# it by a predicate, so none moves without a review record. Hit counts, probe keys, the manifest's size, an unfrozen
# row's files at HEAD and the gitlinks at HEAD move unreviewed, so they are neither published nor pinned here.
PUBLISHED_ROWS = {
    "S1": ((49, 22437, "768968bedf13"), (58, 31814, "00216f886130"), "follows 4 recorded change(s)"),
    "S2": ((35, 78248, "2fed6873d5c6"), (36, 78633, "106ae98e492d"), "follows 6 recorded change(s)"),
    "S3": ((288, 95124, "cb89babf3d59"), (288, 95124, "cb89babf3d59"), "unchanged"),
    "S6": ((1, 14030, "ea5cdca2ea9f"), (5, 21668, "327da5e809c5"), "follows 3 recorded change(s)"),
    "A1": ((11, 48262, "dc67ea9662ea"), (11, 48309, "d9657b917fb3"), "follows 5 recorded change(s)"),
    "A3": ((123, 39413, "410ba632643f"), (174, 49702, "38cde8e6ea2a"), "follows 3 recorded change(s)"),
}
PUBLISHED_HOSTS = {"trust-cg:crates/trust-cg-verify": ((185, 138), (277, 166)), "clean:crates/clean-kernel": ((1899, 780), (1950, 791))}
PUBLISHED_SEARCH = {"S1": (47, 2), "S5": (14, 0), "A3": (178, 6)}  # consumers that are hits, consumers beyond the search
PUBLISHED_JUDGMENTS = 208


def setUpModule():
    if not (os.environ.get("PATH") and SR.shutil.which("targo")) and not os.environ.get("ATPKG_BIN"):
        raise AssertionError("targo is not on PATH or in $ATPKG_BIN; the crate graph needs `targo metadata`")
    result = SR.collect(SR.Options(trees=TREES))
    REAL["result"] = result
    REAL["packages"] = next(v for k, v in SR._CACHE.items() if isinstance(k, tuple) and k[0] == "metadata")[0]


def replace_once(text, old, new):
    assert text.count(old) == 1, (old[:80], text.count(old))
    return text.replace(old, new)


def block(text, kind, line):
    """The [[kind]] block of the table holding the exact line `line`."""
    for part in re.split(r"\n(?=\[\[)", text):
        if part.startswith(f"[[{kind}]]") and f"\n{line}\n" in part + "\n":
            return part
    raise AssertionError((kind, line))


def synthesize(base, files, where):
    """A GitTree of a real commit: `base`'s tree with files added or replaced (str or bytes) or removed (None),
    committed in a bare repository under `where` whose objects/info/alternates borrows base's objects."""
    def git(*args, stdin=None, env=None):
        run = subprocess.run(["git", *args], input=stdin, capture_output=True, env={**C.git_environment(), **(env or {})})
        assert run.returncode == 0, (args[:4], run.stderr[-400:])
        return run.stdout.decode().strip()
    base_dir = ["--git-dir", str(base.repo)] if base.git_dir else ["-C", str(base.repo)]
    objects = git(*base_dir, "rev-parse", "--path-format=absolute", "--git-path", "objects")
    commit = git(*base_dir, "rev-parse", f"{base.rev}^{{commit}}")
    repo = Path(tempfile.mkdtemp(prefix="synth-", dir=where))
    git("init", "-q", "--bare", str(repo))
    (repo / "objects" / "info" / "alternates").write_text(objects + "\n", encoding="utf-8")
    here = ["--git-dir", str(repo)]
    index = {"GIT_INDEX_FILE": str(repo / "synth-index")}
    git(*here, "read-tree", f"{commit}^{{tree}}", env=index)
    entries = b""
    for path, data in files.items():
        if data is None:
            entries += b"0 " + b"0" * 40 + b"\t" + path.encode() + b"\0"
        else:
            blob = git(*here, "hash-object", "-w", "--stdin", stdin=data.encode() if isinstance(data, str) else data)
            entries += b"100644 " + blob.encode() + b"\t" + path.encode() + b"\0"
    git(*here, "update-index", "-z", "--index-info", stdin=entries, env=index)
    tree = git(*here, "write-tree", env=index)
    identity = {"GIT_AUTHOR_NAME": "t", "GIT_AUTHOR_EMAIL": "t@example.invalid", "GIT_COMMITTER_NAME": "t", "GIT_COMMITTER_EMAIL": "t@example.invalid"}
    return C.GitTree(repo, git(*here, "commit-tree", tree, "-p", commit, "-m", "mutation", env=identity), git_dir=True)


class RealInputs(unittest.TestCase):
    def test_real_inputs_pass_and_publish_the_measurements(self):
        result = REAL["result"]
        self.assertEqual(result.violations, [])
        for rid, (base, head, status) in PUBLISHED_ROWS.items():
            got = result.counts["rows"][rid]
            self.assertEqual((got[0][:2], got[0][2][:12]), (base[:2], base[2]), rid)
            self.assertEqual((got[1][:2], got[1][2][:12]), (head[:2], head[2]), rid)
            self.assertEqual(got[2], status, rid)
        for key, (base, head) in PUBLISHED_HOSTS.items():
            self.assertEqual(result.counts["host"][key][:2], (base, head), key)
        for rid, (consumers, beyond) in PUBLISHED_SEARCH.items():
            got = result.counts["search"][rid]
            self.assertEqual((got["consumers"], got["beyond"]), (consumers, beyond), rid)
        self.assertNotIn("uncovered", result.counts["probe"])
        self.assertEqual(result.counts["dependents"], {"S3": 2, "S5": 2, "P1": 5, "P2": 17})
        self.assertEqual(result.counts["reviews"]["judgments"], PUBLISHED_JUDGMENTS)
        self.assertIn("| S1 | E1.1.3 | E1.3.3 (OQ-11), E1.3.4 (OQ-11) | not named (OQ-2) |", result.counts_text)
        self.assertIn("| P2 | none | 371 / 291546 / `7cc778bcb94d` | - | not frozen |", result.counts_text)
        self.assertIn("| trust-mc | `5aec7f89b9be` |\n", result.counts_text)

    def test_cli_exits_zero_and_a_missing_targo_exits_two(self):
        run = subprocess.run([sys.executable, str(SCRIPT)], capture_output=True, text=True)
        self.assertEqual(run.returncode, 0, run.stderr[-2000:])
        self.assertIn(f"semantics_retirement: OK (11 rows, ", run.stdout)
        self.assertIn(f"{PUBLISHED_JUDGMENTS} reviewed judgments)", run.stdout)
        env = {k: v for k, v in os.environ.items() if k != "ATPKG_BIN"}
        # Remove Targo while retaining the Git that the positive case used.
        # A fixed system PATH can select an older Git lacking --no-lazy-fetch,
        # which tests unreadable pins instead of the intended missing tool.
        git_binary = shutil.which("git")
        self.assertIsNotNone(git_binary)
        with tempfile.TemporaryDirectory(prefix="retirement-without-targo-") as tools:
            (Path(tools) / "git").symlink_to(Path(git_binary).resolve())
            env["PATH"] = tools
            self.assertIsNone(shutil.which("targo", path=env["PATH"]))
            run = subprocess.run([sys.executable, str(SCRIPT)], capture_output=True, text=True, env=env)
        self.assertEqual(run.returncode, 2, run.stderr[-2000:])
        self.assertIn("targo is not on PATH or in $ATPKG_BIN", run.stderr)

    def test_unreadable_repository_names_are_a_violation_even_with_no_paths(self):
        for paths in [[], ["model.lean"]]:
            with self.subTest(paths=paths):
                checker = SR.Checker(SR.Options(trees={("clean", "HEAD"): None}))
                self.assertEqual(checker.texts("NAMESPACE", "clean", paths), {})
                self.assertEqual(checker.f.violations, [
                    "NAMESPACE: clean: repository tree at HEAD is unreadable, so its names are unknown",
                ])


class Mutations(unittest.TestCase):
    def setUp(self):
        self._tmp = tempfile.TemporaryDirectory()
        self.tmp = Path(self._tmp.name)
        self.table, self.doc, self.registry = (p.read_text(encoding="utf-8") for p in (TABLE, DOC, REGISTRY))

    def tearDown(self):
        self._tmp.cleanup()

    def run_inputs(self, table=None, doc=None, registry=None, trees=None, metadata=None):
        paths = {}
        for name, text in (("table.toml", table or self.table), ("doc.md", doc or self.doc), ("registry.toml", registry or self.registry)):
            paths[name] = self.tmp / name
            paths[name].write_text(text, encoding="utf-8")
        options = SR.Options(table=paths["table.toml"], doc=paths["doc.md"], registry=paths["registry.toml"], trees={**TREES, **(trees or {})},
                             metadata=None if metadata is MEASURE else REAL["packages"] if metadata is None else metadata,
                             check_pin_state=False, check_history=False)
        return SR.collect(options).violations

    def overlay(self, repo, files):
        """The repository at HEAD, replaced by a real commit that carries `files`."""
        return {(repo, "HEAD"): synthesize(TREES[(repo, "HEAD")], files, self.tmp)}

    def assert_violation(self, violations, *fragments):
        for fragment in fragments:
            self.assertTrue(any(fragment in v for v in violations), f"{fragment!r} not in {violations[:12]}")

    def mechanical(self, violations):
        return [v for v in violations if not v.startswith("REVIEW:") and "published `semantics-retirement-counts` block" not in v]

    def review(self, jids, table=None, doc=None, record="mutation-review"):
        """The registry with a new record's review of each judgment's current content appended."""
        f = C.Findings()
        sections = SR.document_sections(f, doc or self.doc)
        now = SR.judgments(f, table or self.table, sections)
        text = self.registry.replace("[judgment]", f'[record.{record}]\nround = "test"\ndate = "2026-09-17"\nevidence = ["the mutation"]\nreason = "a mutation test"\n\n[judgment]')
        for jid in jids:
            line = next(l for l in text.split("\n") if l.startswith(f'"{jid}" = '))
            digest = C.digest(jid, now[jid])
            old = line.split('digest = "')[1].split('"')[0]
            text = text.replace(line, line.replace(f'digest = "{old}"', f'digest = "{digest}"')[:-4] + f'], ["{record}", "{digest}"]] }}')
        return text

    def section(self, sid):
        return re.search(rf"<!-- reviewed:prose:{sid} -->\n.*?<!-- /reviewed:prose:{sid} -->\n", self.doc, re.S).group(0)

    def test_control_copies_pass(self):
        self.assertEqual(self.run_inputs(), [])
        # A commit that changes nothing, built the way every tree mutation below is, introduces nothing either.
        self.assertEqual(self.run_inputs(trees=self.overlay("super", {})), [])

    # ---- judgments: visible, reviewed, never silent
    def test_a_changed_judgment_fails_only_review_until_reviewed(self):
        cases = [
            ("semantics:S5", replace_once(self.table, 'role_class = "differential-oracle"\nrole = """\nMeasured: the only Cargo edge',
                                          'role_class = "seed-then-delete"\nrole = """\nMeasured: the only Cargo edge'), None),
            ("owner_question:OQ-3", replace_once(self.table, '"(b) Keep until E4.3.2.",', '"(b) Keep until E4.3.1.",'), None),
            ("search:S4", replace_once(self.table, '"A test uses the string mir_semantics as an arbitrary axiom label."', '"An unrelated label."'), None),
            ("prose:limitations", None, replace_once(self.doc, "* **The probe is by name**, over Trust-owned trees.\n", "")),
            # Two reviewed sections exchanged between unchanged headings: each keeps its content, the outline places them.
            ("outline:document", None, self.doc.replace(self.section("s4"), "\0").replace(self.section("s5"), self.section("s4")).replace("\0", self.section("s5"))),
        ]
        for jid, table, doc in cases:
            with self.subTest(jid):
                violations = self.run_inputs(table, doc)
                self.assertEqual(self.mechanical(violations), [])
                self.assert_violation(violations, f"REVIEW: judgment {jid}: its content changed")
                self.assertEqual(self.run_inputs(table, doc, registry=self.review([jid], table, doc)), [])

    # ---- pins, citations, table shape
    def test_pins_citations_and_shape(self):
        cases = [
            ("PIN", self.table.replace('"clean" = "a1c2b17c0bdf15fafa19bce7dbff6096268951ea"', '"clean" = "237fb1dfa50bb58555a79405ed09083147f39681"'), "PIN: [pins].gitlinks_at_base.clean"),
            ("CITE", replace_once(self.table, 'quote = "abbrev Addr := Nat" }', 'quote = "abbrev Addr := Int" }'), "does not contain 'abbrev Addr := Int'"),
            ("free-text line", replace_once(self.table, '"Nothing is deleted: the design keeps it as an untrusted producer."', '"Nothing is deleted (design line 4421)."'), "TABLE: table.semantics[10].deleted_at.reason"),
            ("empty list", replace_once(self.table, 'owner_questions = ["OQ-6", "OQ-13", "OQ-14"]', 'owner_questions = []'), "is empty; a list names something"),
            ("duplicate row", self.table.replace("[[probe_negative]]\nrepo = \"ay\"", "[[probe_negative]]\nrepo = \"ay\"\nkey = \"*\"\ndisposition = \"not-rust\"\nreason = \"dup\"\n\n[[probe_negative]]\nrepo = \"ay\"", 1), "TABLE: probe_negative[1]: duplicate row 'ay:*'"),
            ("unknown key", replace_once(self.table, 'schema = "trust.core.semantics-retirement.v4"', 'schema = "trust.core.semantics-retirement.v4"\nextra = 1'), "top-level key 'extra'"),
        ]
        for label, table, fragment in cases:
            with self.subTest(label):
                self.assert_violation(self.run_inputs(table), fragment)

    # ---- the design's exits
    def test_design_exit_rules(self):
        s2 = block(self.table, "semantics", 'id = "S2"')
        cases = [
            ("proposed marked design", s2.replace('{ id = "E2.5.1", basis = "proposed", owner_question = "OQ-11", ', '{ id = "E2.5.1", basis = "design", '), "S2: exit E2.5.1 is marked design"),
            ("design exit dropped", re.sub(r'  \{ id = "E4.3.2", basis = "design".*\n', "", s2), "S2: §5 exit E4.3.2 names the row but is neither listed"),
            ("citation outside the exit", s2.replace('{ id = "E2.4.2", basis = "proposed", owner_question = "OQ-11", ref = "design:4417"', '{ id = "E2.4.2", basis = "proposed", owner_question = "OQ-11", ref = "design:4415"'), "exit E2.4.2 must cite its own text"),
            ("proposal not asked", s2.replace('{ id = "E2.5.1", basis = "proposed", owner_question = "OQ-11"', '{ id = "E2.5.1", basis = "proposed", owner_question = "OQ-3"'), "OQ-3's text does not name E2.5.1"),
            ("RC-6 item uncited", s2.replace('rc6_item = 2', 'rc6_item = 0'), "RC-6 item 2"),
        ]
        for label, new, fragment in cases:
            with self.subTest(label):
                self.assert_violation(self.run_inputs(replace_once(self.table, s2, new)), fragment)

    # ---- the freeze by content, change classes, host crates, namespaces
    def test_growth_of_a_frozen_row_fails(self):
        path = "crates/trust-semantics/src/lib.rs"
        text = TREES[("super", "HEAD")].text(path)
        grown = self.overlay("super", {path: text + "\npub const EXTRA: &str = \"RustVIR.extra\";\n"})
        self.assert_violation(self.run_inputs(trees=grown), "FREEZE: S5: own files at HEAD are 1 files / 842 lines")
        # A second model reached from an own file by #[path] is an own file too.
        with_mod = self.overlay("super", {path: text + '\n#[path = "model2.rs"]\nmod model2;\n', "crates/trust-semantics/src/model2.rs": "pub fn eval2() {}\n"})
        self.assert_violation(self.run_inputs(trees=with_mod), "FREEZE: S5: own files at HEAD are 2 files")

    def test_change_classes(self):
        s1 = block(self.table, "semantics", 'id = "S1"')
        cases = [
            ("wrong names", s1.replace('names_added = ["TrustIr.Ty.Handle"]', 'names_added = []'), "names_added must be ['TrustIr.Ty.Handle']"),
            ("wrong digest", s1.replace('digest_after = "cda84580d020d6cad03fcca7685f69376624fce3d6c9648add9d3cd5989e7bee"', 'digest_after = "' + "0" * 64 + '"'), "FREEZE: S1 size_change[0]: records 0 files / 16 lines / 000000000000"),
            ("wrong last digest", s1.replace('digest_after = "00216f88613072b91ddbd4073f2c70bfe63c97f263988eb7820119cc6139cdd8"', 'digest_after = "' + "0" * 64 + '"'), "FREEZE: S1: own files at HEAD"),
            ("an earlier entry without its commit", s1.replace('at = "fdda1f3616c5618c764d6a30bf1e9bdeb17a93c8", ', ""), "FREEZE: S1 size_change[0]: an entry a later entry follows names the superproject commit it measures"),
            ("retirement that grows", s1.replace('change_class = "recorded-extension", owner_question = "OQ-17"', 'change_class = "retirement", authority = "OQ-2"'), "a retirement only deletes lines"),
            ("oracle bug fix adding a constructor", s1.replace('change_class = "recorded-extension", owner_question = "OQ-17"', 'change_class = "oracle-bug-fix", regression_test = { ref = "worktree:crates/trust-clean/tests/lean_clean_bridge.rs:113", quote = "run_bridge_gate" }'),
             "an oracle bug fix adds no kernel name, but adds ['TrustIr.Ty.Handle']"),
            ("growth without an exit", s1.replace('change_class = "recorded-extension", owner_question = "OQ-17"', 'change_class = "growth", authority = "E1.1.3"'), "growth's authority is an exit of growth_allowed"),
            ("rename that is no rename", s1.replace('change_class = "recorded-extension", owner_question = "OQ-17"', 'change_class = "mechanical-rename", renames = [["Addr", "Address"]], forced_by = [{ ref = "design:4843", quote = "Writing or extending" }]'),
             "applying the recorded renames does not yield the files"),
            ("no size_change", re.sub(r"size_change = \[\n.*?\n\]\n", "", s1, flags=re.S), "an edit to a frozen semantics needs a dated size_change entry"),
        ]
        for label, new, fragment in cases:
            with self.subTest(label):
                self.assert_violation(self.run_inputs(replace_once(self.table, s1, new)), fragment)

    def test_change_items_are_multisets(self):
        # Round 22: interpret.rs gained two `fn fmt` (two Display impls), so S6's items_added lists it twice. The
        # uniqueness rule refused that list while FREEZE required it; the items lists are multisets, compared by count.
        # The mutations touch that round-22 entry only: a later entry (T0, 2026-09-28) lists `fn fmt` twice too.
        s6 = block(self.table, "semantics", 'id = "S6"')
        entry0 = next(line for line in s6.split("\n") if 'digest_after = "181da82063b1' in line)
        self.assertEqual(entry0.count('"fn fmt", "fn fmt"'), 1)

        def in_entry0(old, new):
            return s6.replace(entry0, entry0.replace(old, new))

        cases = [
            ("one of two dropped", in_entry0('"fn fmt", "fn fmt"', '"fn fmt"'), "FREEZE: S6 size_change[0]: items_added / items_removed must be"),
            ("a third added", in_entry0('"fn fmt", "fn fmt"', '"fn fmt", "fn fmt", "fn fmt"'), "FREEZE: S6 size_change[0]: items_added / items_removed must be"),
            ("a repeated element elsewhere in the entry", in_entry0('evidence = [{ ref = "first-party:trust-ir/crates/trust-ir/src/interpret.rs:361", quote = "pub trait HostCalls: Sync {" }',
                                                                     'evidence = [{ ref = "first-party:trust-ir/crates/trust-ir/src/interpret.rs:361", quote = "pub trait HostCalls: Sync {" }, { ref = "first-party:trust-ir/crates/trust-ir/src/interpret.rs:361", quote = "pub trait HostCalls: Sync {" }'),
             "TABLE: semantics[5] S6: size_change.evidence repeats"),
        ]
        for label, new, fragment in cases:
            with self.subTest(label):
                self.assertNotEqual(new, s6)
                self.assert_violation(self.run_inputs(replace_once(self.table, s6, new)), fragment)
        found = self.run_inputs()
        self.assertEqual([v for v in found if "repeats 'fn fmt'" in v], [])  # control: the real table's repeat is admitted

    def test_host_crate_and_namespaces(self):
        smt = "crates/trust-cg-verify/src/smt.rs"
        text = TREES[("trust-cg", "HEAD")].text(smt)
        inline = self.overlay("trust-cg", {smt: text + "\npub mod mir_model2 {\n    pub enum MirRvalue2 { Use, Add, Shl }\n}\n"})
        self.assert_violation(self.run_inputs(trees=inline), "HOST: host crate trust-cg:crates/trust-cg-verify: the library module tree changed (added ['trust-cg:crates/trust-cg-verify/src/smt.rs::mir_model2']")
        hc = block(self.table, "host_crate", 'dir = "crates/trust-ir"')
        self.assert_violation(self.run_inputs(replace_once(self.table, hc, re.sub(r"changes = \[\n.*\n\]\n", "changes = []\n", hc, flags=re.S))),
                              "HOST: host crate trust-ir:crates/trust-ir: the library module tree changed")
        # Round 22: a new own file of a frozen row that its host crate compiles as a module is the row's
        # size_change (FREEZE), not a module beside the semantics (HOST); before, neither record could pass.
        core_mod = "crates/clean-verify/src/spec/core_spec/mod.rs"
        mtext = TREES[("clean", "HEAD")].text(core_mod)
        own_module = self.overlay("clean", {core_mod: replace_once(mtext, "mod eval_ir_machine;\n", "mod eval_ir_machine;\nmod eval_ir_d04extra;\n"),
                                            "crates/clean-verify/src/spec/core_spec/eval_ir_d04extra.rs": "pub fn d04_extra() {}\n"})
        found = self.run_inputs(trees=own_module)
        self.assert_violation(found, "FREEZE: A3: own files at HEAD are")
        self.assertEqual([v for v in found if v.startswith("HOST: host crate clean:crates/clean-verify")], [])
        # Control: the same module under a name no row owns is a module beside A3, which HOST refuses.
        beside = self.overlay("clean", {core_mod: replace_once(mtext, "mod eval_ir_machine;\n", "mod eval_ir_machine;\nmod d04_beside;\n"),
                                        "crates/clean-verify/src/spec/core_spec/d04_beside.rs": "pub fn d04_beside() {}\n"})
        self.assert_violation(self.run_inputs(trees=beside), "HOST: host crate clean:crates/clean-verify: the library module tree changed (added ['clean:crates/clean-verify/src/spec/core_spec/d04_beside.rs']")
        # F6: a new EvalIR definition registered from a clean-verify module that is no own file of A3.
        bundles = "crates/clean-verify/src/spec/core_spec/bundles.rs"
        btext = TREES[("clean", "HEAD")].text(bundles)
        literal = self.overlay("clean", {bundles: btext + '\npub const D04_EXTRA_EVAL_DEF: &str = "def ir_exec_extra (s : IRState) : IRState := s";\n'})
        self.assert_violation(self.run_inputs(trees=literal), "NAMESPACE: namespace EvalIR: clean:crates/clean-verify/src/spec/core_spec/bundles.rs names 1 kernel name(s)")
        comment = self.overlay("clean", {bundles: btext + "\n// def ir_exec_extra (s : IRState) : IRState := s\n"})
        self.assertEqual([v for v in self.run_inputs(trees=comment) if "NAMESPACE" in v], [])  # control: a comment declares nothing
        # A new name under a prefix namespace outside the rows.
        other = self.overlay("super", {"crates/trust-router/src/d04_extra.rs": 'pub const X: &str = "Trust.MirSem.extraStep";\n'})
        self.assert_violation(self.run_inputs(trees=other), "NAMESPACE: namespace Trust.MirSem: super:crates/trust-router/src/d04_extra.rs names 1 kernel name(s)")

    def test_integration_a_name_declared_in_a_namespace_block_is_read(self):
        # The verification of 9ed1cf6168: a name declared inside `namespace X ... end X` never wrote `X.`, so the prefix
        # grep did not select its file and the dotted-name scan did not read it; in EvalIR a namespaced or one-line
        # declaration in a Rust literal escaped the line-anchored reader. Each commit below exited 0 there.
        bridge = "crates/trust-clean/src/trustir_bridge.rs"
        temporal = "crates/trust-spec-temporal/src/literal_refinement.rs"
        bundles = "crates/clean-verify/src/spec/core_spec/bundles.rs"
        super_head, clean_head = TREES[("super", "HEAD")], TREES[("clean", "HEAD")]
        cases = [
            ("N1 a Lean file", "super", {"crates/trust-router/lean/D04Extra.lean": "namespace TrustIr\ndef extraStep : Nat := 0\ntheorem extraStep_pos : True := trivial\nend TrustIr\n"},
             "NAMESPACE: namespace TrustIr: super:crates/trust-router/lean/D04Extra.lean names 2 kernel name(s)"),
            ("N2 a literal in another crate", "super", {temporal: super_head.text(temporal) + '\npub const D04: &str = "namespace Trust\\ndef MirSem.extraStep : Nat := 0\\nend Trust";\n'},
             f"NAMESPACE: namespace Trust.MirSem: super:{temporal} names 1 kernel name(s)"),
            ("N3 a literal in a recorded outside definer", "super", {bridge: super_head.text(bridge) + '\npub const D04: &str = "namespace TrustIr\\ntheorem extraThm : True := trivial\\nend TrustIr";\n'},
             f"NAMESPACE: namespace TrustIr: outside definer super:{bridge} records 1 names"),
            ("E1 EvalIR in a namespace block", "clean", {bundles: clean_head.text(bundles) + '\npub const D04: &str = "namespace IRMachine2\\ndef step (s : IRState) : IRState := s\\nend IRMachine2";\n'},
             f"NAMESPACE: namespace EvalIR: clean:{bundles} names 1 kernel name(s)"),
            ("E2 EvalIR after a command prefix on one line", "clean", {bundles: clean_head.text(bundles) + '\npub const D04: &str = "set_option maxHeartbeats 400000 in theorem IRStep_extra : True := trivial";\n'},
             f"NAMESPACE: namespace EvalIR: clean:{bundles} names 1 kernel name(s)"),
            ("prose between the literals cannot close the namespace", "super",
             {"crates/trust-router/src/d04_prose.rs": 'pub const A: &str = "namespace TrustIr\\n";\npub const B: &str = "unexpected end of input";\npub const C: &str = "def extraAfterProse : Nat := 0";\n'},
             "NAMESPACE: namespace TrustIr: super:crates/trust-router/src/d04_prose.rs names 1 kernel name(s)"),
        ]
        for label, repo, files, fragment in cases:
            with self.subTest(label):
                self.assert_violation(self.run_inputs(trees=self.overlay(repo, files)), fragment)
        # Controls: a namespace block that declares only names the rows declare, and a Rust comment, add nothing.
        mirror = {"crates/trust-router/src/d04_mirror.rs": 'pub const M: &str = "namespace TrustIr\\ninductive Permission where | owned : Permission\\nend TrustIr";\n'}
        self.assertEqual([v for v in self.run_inputs(trees=self.overlay("super", mirror)) if "NAMESPACE" in v], [])
        comment = {"crates/trust-router/src/d04_comment.rs": "// namespace TrustIr def extraInComment : Nat := 0\npub fn f() {}\n"}
        self.assertEqual([v for v in self.run_inputs(trees=self.overlay("super", comment)) if "NAMESPACE" in v], [])

    def test_integration_lean_declarations_are_read_with_their_namespaces(self):
        read = SR.declared_names  # every file but a row's own: a declaration is read under every namespace opened before it
        self.assertEqual(read("x.lean", "namespace A\n@[simp] private theorem t : True := trivial\nprotected def B.c := 1\nmutual\ndef m : Nat := 0\nend\ndef d : Nat := 0\nend A\ndef top : Nat := 0\n"),
                         {"A.t", "A.B.c", "A.m", "A.d", "A.top", "top"})
        # A row's own files are read precisely, so a name they do not declare cannot exempt a declaration elsewhere.
        self.assertEqual(read("x.lean", "namespace A\ndef inside : Nat := 0\nend A\ndef top : Nat := 0\n", over=False), {"A.inside", "top"})
        # In a Lean file a command starts a line: a keyword in a string or a comment starts none, and the strings stay.
        self.assertEqual(read("x.lean", 'namespace A\n#eval "end of it"\n-- end A\ndef x : Nat := 0\nend A\n'), {"A.x"})
        self.assertEqual(read("x.lean", "namespace A\nprivate class «private.class» : Prop where\n  x : Nat\nend A\n"), {"A.«private.class»"})
        self.assertEqual(read("x.lean", "namespace A\ninstance : BEq T := ⟨fun _ _ => true⟩\ninstance (priority := low) named : Repr T := ⟨⟩\nderiving instance Repr, BEq for T\nend A\n"),
                         {"A.instance : BEq T", "A.named", "A.T.deriving Repr", "A.T.deriving BEq"})
        self.assertEqual(read("x.rs", 'const S: &str = "namespace A \\\n  inductive P where | p | q deriving DecidableEq end A";\nconst T: &str = "def after : Nat := 0";\n'),
                         {"A.P", "A.P.p", "A.P.q", "A.after", "after"})  # a Rust file's literals: read under every namespace opened before

    # ---- searches, crate graph, gates, gate sources, probe
    def test_searches(self):
        s5 = block(self.table, "search", 'row = "S5"')
        cases = [
            ("consumer removed", replace_once(self.table, s5, s5.replace('  { repo = "super", path = "scripts/trust_self_verify_crate.sh", kind = "script" },\n', "")),
             "SEARCH: search S5: hit super:'scripts/trust_self_verify_crate.sh' is matched by 0 consumer(s) and 0 mention glob(s)"),
            ("stale mention", replace_once(self.table, s5, s5.replace('mentions = [\n', 'mentions = [\n  { repo = "ty", glob = "nothing/*", reason = "stale" },\n')),
             "SEARCH: search S5: mention glob ty:nothing/* matches no hit (stale)"),
            ("stale consumer", replace_once(self.table, s5, s5.replace('consumers = [\n', 'consumers = [\n  { repo = "super", path = "crates/trust-router/src/lib.rs", kind = "module" },\n')),
             "SEARCH: search S5: consumer super:crates/trust-router/src/lib.rs is no hit of the search (stale)"),
            ("two dispositions", replace_once(self.table, s5, s5.replace('mentions = [\n', 'mentions = [\n  { repo = "super", glob = "scripts/trust_self_verify_*", reason = "overlap" },\n')),
             "hit super:'scripts/trust_self_verify_crate.sh' is matched by 1 consumer(s) and 1 mention glob(s)"),
        ]
        for label, table, fragment in cases:
            with self.subTest(label):
                self.assert_violation(self.run_inputs(table), fragment)
        new = self.overlay("super", {"crates/trust-router/src/d04_consumer.rs": "use trust_semantics::noOverflow_violation_formula;\n"})
        self.assert_violation(self.run_inputs(trees=new), "SEARCH: search S5: hit super:'crates/trust-router/src/d04_consumer.rs' is matched by 0 consumer(s)")
        s1 = block(self.table, "search", 'row = "S1"')
        beyond_hit = s1.replace('  { repo = "super", path = "scripts/check_bridge_pin.sh", kind = "script" },\n', "").replace(
            'beyond_search = [\n', 'beyond_search = [\n  { repo = "super", path = "scripts/check_bridge_pin.sh", kind = "script", reason = "r", evidence = [{ ref = "worktree:scripts/check_all.sh:74", quote = "ARGS=(trust gate check-all" }] },\n')
        self.assert_violation(self.run_inputs(replace_once(self.table, s1, beyond_hit)), "beyond_search consumer super:scripts/check_bridge_pin.sh is a hit of the search")
        # The oracle's consuming test must be a recorded consumer.
        s4 = block(self.table, "search", 'row = "S4"')
        self.assert_violation(self.run_inputs(replace_once(self.table, s4, s4.replace('  { repo = "trust-cg", path = "crates/rustc-codegen-trust-cg/src/mem_refine.rs", kind = "module" },\n', "").replace(
            'mentions = [\n', 'mentions = [\n  { repo = "trust-cg", glob = "crates/rustc-codegen-trust-cg/src/mem_refine.rs", reason = "r" },\n'))),
            "SEARCH: S4: the oracle's consuming test trust-cg:crates/rustc-codegen-trust-cg/src/mem_refine.rs is no recorded consumer")

    def test_no_hit_is_dropped_for_its_bytes_or_its_name(self):
        trees = self.overlay("super", {
            "crates/trust-router/src/d04_latin1.rs": b"// caf\xe9: a Latin-1 comment\nuse trust_semantics::noOverflow_violation_formula;\n",
            "crates/trust-router/src/d04_caf\u00e9.rs": "use trust_semantics::noOverflow_violation_formula;\n",
            "crates/trust-router/src/d04_binary.txt": b"\0\1trust_semantics\0",
            "crates/trust-router/src/d04_names.rs": b'// \xe9\npub const X: &str = "Trust.MirSem.extraStep";\n',
            "crates/trust-router/src/d04\nnewline.rs": "pub fn f() {}\n",
        })
        trees.update(self.overlay("clean", {"crates/clean-verify/tests/d04_latin1.rs": b'// \xe9\npub const D: &str = "def ir_exec_extra (s : IRState) : IRState := s";\n'}))
        violations = self.run_inputs(trees=trees)
        self.assert_violation(
            violations,
            # A file that is not UTF-8, a name git would quote, and a file git calls binary are hits all the same.
            "SEARCH: search S5: hit super:'crates/trust-router/src/d04_latin1.rs' is matched by 0 consumer(s) and 0 mention glob(s)",
            "SEARCH: search S5: hit super:'crates/trust-router/src/d04_caf\u00e9.rs' is matched by 0 consumer(s) and 0 mention glob(s)",
            "SEARCH: search S5: hit super:'crates/trust-router/src/d04_binary.txt' is matched by 0 consumer(s) and 0 mention glob(s)",
            # A namespace never reads an undecodable file as empty.
            "NAMESPACE: super:'crates/trust-router/src/d04_names.rs' is not UTF-8 text at HEAD",
            "NAMESPACE: clean:'crates/clean-verify/tests/d04_latin1.rs' is not UTF-8 text at HEAD",
            # A path with a newline would shift every later file of a batched read.
            "has a path holding a newline, which no batched read can address: 'crates/trust-router/src/d04\\nnewline.rs'",
        )

    def test_host_crates_are_enumerated(self):
        hc = block(self.table, "host_crate", 'dir = "crates/trust-ir"')
        stale = hc + '\n[[host_crate]]\nrepo = "super"\ndir = "crates/trust-router"\nrows = ["S5"]\nfiles = 1\ninline_modules = 0\ndigest = "' + "0" * 64 + '"\nchanges = []\n'
        cases = [
            ("row removed", replace_once(self.table, hc, ""), "HOST: crate trust-ir:crates/trust-ir holds own files of ['S6'] and has no [[host_crate]] row"),
            ("rows wrong", replace_once(self.table, hc, hc.replace('rows = ["S6"]', 'rows = ["S6", "A2"]')), "HOST: host crate trust-ir:crates/trust-ir: rows ['S6', 'A2'], but it holds own files of ['S6']"),
            ("stale row", replace_once(self.table, hc, stale), "HOST: host crate super:crates/trust-router: holds no own file of a frozen row at HEAD (stale)"),
        ]
        for label, table, fragment in cases:
            with self.subTest(label):
                self.assert_violation(self.run_inputs(table), fragment)

    def test_gate_rows_are_matched_as_git_grep_reads_a_pattern(self):
        checker = SR.Checker(SR.Options())
        # -F for terms (`x|y` is a string), -E for patterns (a POSIX class Python's re does not read).
        self.assertEqual(checker.matching_lines(["a b", "ab", "x|y", "x"], ["x|y"], ["a[[:space:]]b"]), {0, 2})
        self.assertEqual(checker.f.violations, [])

    def test_crate_graph(self):
        s3 = block(self.table, "search", 'row = "S3"')
        dropped = s3.replace('  { workspace = "clean:Cargo.toml", package = "clean-cli", crate = "clean-rust-sem", kinds = ["normal"] },\n', "")
        self.assert_violation(self.run_inputs(replace_once(self.table, s3, dropped)), "CRATES: search S3: clean-cli (clean:Cargo.toml) depends on clean-rust-sem (normal), and is not a recorded dependent")
        packages = REAL["packages"]
        fake = {w: list(p) for w, p in packages.items()}
        fake["clean:Cargo.toml"] = fake["clean:Cargo.toml"] + [{"name": "d04-new", "manifest": "clean:crates/d04-new/Cargo.toml", "dependencies": [("clean-rust-sem", "normal", "clean:crates/clean-rust-sem")]}]
        self.assert_violation(self.run_inputs(metadata=fake), "CRATES: search S3: d04-new (clean:Cargo.toml) depends on clean-rust-sem")
        self.assertEqual(self.run_inputs(metadata=packages), [])  # control
        # A path dependency written through the tracked link first-party/trust -> .. is the crate it names: the
        # materialized tree carries the link, so the real crate graph resolves it rather than failing to load it.
        manifest = "crates/clean-c-sem/Cargo.toml"
        linked = replace_once(TREES[("clean", "HEAD")].text(manifest), "\n[dev-dependencies]\n",
                              '\n[dev-dependencies]\ntrust-semantics = { path = "../../../trust/crates/trust-semantics" }\n')
        self.assert_violation(self.run_inputs(trees=self.overlay("clean", {manifest: linked}), metadata=MEASURE),
                              "CRATES: search S5: clean-c-sem (clean:Cargo.toml) depends on trust-semantics (dev), and is not a recorded dependent")

    def test_gates_and_gate_sources(self):
        s1 = block(self.table, "search", 'row = "S1"')
        cases = [
            ("matched row undispositioned", replace_once(self.table, s1, re.sub(r'  \{ unit = "fast.bridge-pin".*\n', "", s1)), "GATES: search S1: gate manifest row fast.bridge-pin matches the search and has no recorded disposition"),
            ("beyond but matched", replace_once(self.table, s1, s1.replace('gates_beyond_search = [\n', 'gates_beyond_search = [\n  { source = "super:tests/run_trust_comprehensive_harness.sh", unit = "fast.bridge-pin", role = "exercises", reason = "r", evidence = [{ ref = "worktree:scripts/check_all.sh:74", quote = "ARGS=(trust gate check-all" }] },\n')),
             "gate fast.bridge-pin beyond the search is matched by the search"),
            ("gate source dropped", re.sub(r'\[\[gate_source\]\]\nrepo = "trust-cg"\npath = "hooks/pre-push"\n.*?\n\n', "", self.table, flags=re.S), "SOURCES: trust-cg:hooks/pre-push is a git hook"),
        ]
        for label, table, fragment in cases:
            with self.subTest(label):
                self.assert_violation(self.run_inputs(table), fragment)
        harness = "tests/run_trust_comprehensive_harness.sh"
        text = TREES[("super", "HEAD")].text(harness)
        added = self.overlay("super", {harness: replace_once(text, "fast.bridge-pin|", "fast.bridge-pin-2|fast|supply-chain|true|never|bash scripts/check_bridge_pin.sh --fix\nfast.bridge-pin|")})
        self.assert_violation(self.run_inputs(trees=added), "GATES: search S1: gate manifest row fast.bridge-pin-2 matches the search")
        hook = self.overlay("super", {"tools/d04-hooks/pre-commit": "#!/bin/sh\nexit 0\n"})
        self.assert_violation(self.run_inputs(trees=hook), "SOURCES: super:tools/d04-hooks/pre-commit is a git hook")

    def test_probe(self):
        new = self.overlay("super", {"crates/trust-d04sem/src/lib.rs": "pub fn step() {}\n"})
        self.assert_violation(self.run_inputs(trees=new), "PROBE: probe key super:crates/trust-d04sem/ is covered by no row")
        table = re.sub(r'\[\[probe_negative\]\]\nrepo = "ny"\nkey = "crates/\*"\n.*?\n\n', "", self.table, flags=re.S)
        self.assert_violation(self.run_inputs(table), "PROBE: probe key ny:")
        stale = self.table.replace('[[probe_negative]]\nrepo = "ay"', '[[probe_negative]]\nrepo = "ty"\nkey = "d04/*"\ndisposition = "not-rust"\nreason = "stale"\n\n[[probe_negative]]\nrepo = "ay"', 1)
        self.assert_violation(self.run_inputs(stale), "PROBE: probe_negative ty:d04/* covers no probe key (stale)")

    def test_what_moves_unreviewed_leaves_the_counts_block_alone(self):
        # An unfrozen producer's own file edited, a manifest row no search matches dropped (a blank line, so no cited
        # line moves) and a submodule moved: every predicate accepts them, and the block prints none of them.
        vcgen, harness = "crates/trust-vcgen/src/lib.rs", "tests/run_trust_comprehensive_harness.sh"
        sweep = "supply-chain.fleet-pin-drift-sweep|release|supply-chain|true|2026-08-31|python3 scripts/sweep_pin_drift.py\n"
        head = TREES[("super", "HEAD")]
        trees = {**self.overlay("super", {vcgen: head.text(vcgen) + "// an unreviewed edit\n", harness: replace_once(head.text(harness), sweep, "\n")}),
                 **self.overlay("trust-mc", {"d04-unrelated.txt": "nothing here\n"})}
        self.assertEqual(self.run_inputs(trees=trees), [])

    # ---- the document
    def test_document(self):
        cases = [
            ("counts", replace_once(self.doc, "| S2 | design | 35 / 78248 /", "| S2 | design | 36 / 78248 /"), "DOC: the published `semantics-retirement-counts` block differs"),
            ("unreviewed line", replace_once(self.doc, "## 9. Limitations\n", "## 9. Limitations\n\nAn unreviewed ruling.\n"), "DOC: line"),
            ("bare citation", replace_once(self.doc, "is stale\nagainst the shipped gate.", "is stale\nagainst the shipped gate (prove.rs:827)."), "line citation 'prove.rs:827' is not in the checked"),
            ("quote drift", replace_once(self.doc, "«It is the witness-schema seed,» not the semantics", "«It is the witness seed,» not the semantics"), "does not contain 'It is the witness seed,'"),
        ]
        for label, doc, fragment in cases:
            with self.subTest(label):
                self.assert_violation(self.run_inputs(doc=doc), fragment)


if __name__ == "__main__":
    unittest.main(verbosity=1)
