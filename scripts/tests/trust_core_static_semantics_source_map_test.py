#!/usr/bin/env python3
"""Controls for scripts/trust_core/static_semantics_source_map.py (D0.7, design exit E0.8b).

* The REAL checker on the REAL inputs (the pinned FLS, Reference, a-mir-formality, rfcs and
  rust-lang/rust clones, this repository at HEAD, the ledger, the document and the review
  registry) exits 0 and publishes the counts asserted here.
* Every mutation of a copy of an input makes the CHECKER report what it introduces, beside
  an unmutated control. A mechanical mutation names its predicate; a judgment mutation (a
  mapping, a label, a disposition, a selection rule, a count's predicate text, a prose
  section) passes every mechanical predicate, fails REVIEW, and passes once a new review
  record reviews its digest. The verification of e230894b77 left eight owner-facing texts
  editable with exit 0 (D9, D10, M13, M13b, M19, M21, M22, M23); each is a case here. The
  verification of 2a2aa81809 found std: citations read past the library roots, RFC status
  evidence whose expect went unchecked, stale rows accepted once reviewed, and a snapshot URL
  no longer compared; each is a mechanical case here that fails even when reviewed.

The shared layers are tested in scripts/tests/trust_core_common_test.py. A missing source
clone is a FAILURE that prints the command that creates it, never a skip; the clones are
never modified (a source mutation overlays a file on a read-only tree).

Author: Andrew Yates <andrewyates.name@gmail.com>
Copyright 2026 Andrew Yates | License: Apache-2.0 OR MIT
"""

import importlib.util
import re
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "scripts" / "trust_core" / "static_semantics_source_map.py"
SPEC = importlib.util.spec_from_file_location("trust_core_static_semantics_source_map", SCRIPT)
SSM = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(SSM)
C = SSM.C
LEDGER, DOC, REGISTRY = ROOT / SSM.LEDGER_REL, ROOT / SSM.DOC_REL, ROOT / SSM.REGISTRY_REL
TREES: dict = {}

# The published counts (STATIC_SEMANTICS_SOURCE_MAP.md). A change here is a change to the map.
PUBLISHED = {
    "universe.fls.chapters": 21, "universe.fls.sections": 304, "universe.fls.paragraphs": 3755, "universe.reference.files": 119,
    "universe.reference.rules": 3016, "universe.std.members": 221, "universe.std-docs.sections": 164, "universe.std-docs.files": 31,
    "universe.design.parts": 12, "universe.formality.judgments": 78, "unmapped.fls.paragraphs": 0, "unmapped.fls.sections": 0,
    "unmapped.reference.rules": 0, "unmapped.std.members": 0, "unmapped.std-docs.sections": 0, "unmapped.design.parts": 0,
    "unmapped.formality.judgments": 0, "rows": 193, "rows.compat-candidate": 4, "rows.de-facto": 0, "rows.with-conflicts": 21,
    "conflicts.fls-reference": 9, "conflicts.fls-std": 1, "conflicts.document-rustc": 4, "conflicts.formality-rustc": 7,
    "conflicts.document-gap": 2, "members.st": 5395, "members.outside-st": 1761, "outside-st.dispositioned": 1356,
    "outside-st.dispositioned.std": 192, "outside-st.twin-required": 264, "twins.groups": 99, "outside-st.kind.library-api": 155,
    "outside-st.kind.no-rejection": 35, "outside-st.kind.lint-level": 44, "rustc-error-tests.citing-outside-st-reference-rules": 28,
    "grammar.side-conditions": 41, "grammar.candidates": 306, "grammar.candidates.cited": 131, "grammar.candidates.dismissed": 175,
    "formality.notes": 58, "rfcs.registered": 8, "rfcs.not-stabilized": 1, "ui-tests.bound-to-rows": 3,
    "post-alignment.fls.added": 0, "post-alignment.fls.removed": 0, "post-alignment.fls.changed": 0,
    "design.parts.rank-1": 10, "design.parts.rank-1-gap": 2, "doc_citations": 25,
}
PUBLISHED_JUDGMENTS = 712
STD = "library/core/src/default.rs"


def setUpModule():
    pins = C.load_pins()
    try:
        clones = C.locate_clones(pins, sorted(SSM.READS))
    except C.MissingClone as error:
        raise AssertionError(str(error)) from None
    rust = C.sources_root() / "rust"
    if not (rust / ".git").exists():
        raise AssertionError(f"the rust clone is missing at {rust}; run the checker for the command that creates it")
    for name, path in clones.items():
        source = pins.sources[name]
        TREES[SSM.READS[name]] = C.GitTree(path, source.revision)
    TREES["std"] = C.GitTree(rust, pins.alignment)
    TREES["worktree"] = TREES["trust-test"] = C.GitTree(ROOT, "HEAD")


class Overlay:
    """A pinned tree with some files replaced or added (a source mutation that leaves the clone untouched)."""

    def __init__(self, base, files: dict) -> None:
        self.base, self.overlay = base, files

    def files(self, prefix="", suffixes=()):
        extra = {r for r in self.overlay if r.startswith(prefix) and (not suffixes or r.endswith(suffixes))}
        return sorted(set(self.base.files(prefix, suffixes)) | extra)

    def prefetch(self, rels):
        self.base.prefetch([r for r in rels if r not in self.overlay])

    def text(self, rel):
        return self.overlay[rel] if rel in self.overlay else self.base.text(rel)

    def lines(self, rel):
        text = self.text(rel)
        return None if text is None else text.split("\n")


def replace_once(text, old, new):
    assert text.count(old) == 1, (old, text.count(old))
    return text.replace(old, new)


def row_block(text, rid):
    start = text.index(f'[[row]]\nid = "{rid}"\n')
    end = text.find("\n[[", start + 1)
    while text.startswith("\n[[row.", end):
        end = text.find("\n[[", end + 1)
    return text[start:end]


class RealInputs(unittest.TestCase):
    def test_real_inputs_pass_and_publish_the_counts(self):
        result = SSM.collect()
        self.assertEqual(result.violations, [])
        for key, value in PUBLISHED.items():
            self.assertEqual(result.counts[key], value, key)
        self.assertEqual(result.counts["reviews"]["judgments"], PUBLISHED_JUDGMENTS)

    def test_cli_exits_zero_and_each_missing_clone_exits_two(self):
        run = subprocess.run([sys.executable, str(SCRIPT)], capture_output=True, text=True)
        self.assertEqual(run.returncode, 0, run.stderr)
        self.assertIn(f"static_semantics_source_map: OK ({PUBLISHED['doc_citations']} document citations, {PUBLISHED_JUDGMENTS} reviewed judgments)", run.stdout)
        for flag, command in (("--fls", "git clone https://github.com/rust-lang/fls"), ("--rfcs", "git clone https://github.com/rust-lang/rfcs"),
                              ("--rust", "sparse-checkout set")):
            with self.subTest(flag), tempfile.TemporaryDirectory() as tmp:
                run = subprocess.run([sys.executable, str(SCRIPT), flag, str(Path(tmp) / "absent")], capture_output=True, text=True)
                self.assertEqual(run.returncode, 2)
                self.assertIn(command, run.stderr)


class Mutations(unittest.TestCase):
    def setUp(self):
        self._tmp = tempfile.TemporaryDirectory()
        self.tmp = Path(self._tmp.name)
        self.ledger, self.doc, self.registry = (p.read_text(encoding="utf-8") for p in (LEDGER, DOC, REGISTRY))

    def tearDown(self):
        self._tmp.cleanup()

    def run_inputs(self, ledger=None, doc=None, registry=None, trees=None, result=False, pins=None):
        paths = {}
        for name, text in (("ledger.toml", ledger or self.ledger), ("doc.md", doc or self.doc), ("registry.toml", registry or self.registry),
                           ("pins.toml", pins or (ROOT / C.PINS_REL).read_text(encoding="utf-8"))):
            paths[name] = self.tmp / name
            paths[name].write_text(text, encoding="utf-8")
        options = SSM.Options(ledger=paths["ledger.toml"], doc=paths["doc.md"], registry=paths["registry.toml"], pins=paths["pins.toml"],
                              trees={**TREES, **(trees or {})}, check_pin_state=False, check_history=False)
        found = SSM.collect(options)
        return found if result else found.violations

    def regenerated(self, ledger, doc=None):
        """The document with its generated blocks rendered from `ledger` (what --write-blocks writes)."""
        doc = doc or self.doc
        for name, body in self.run_inputs(ledger, doc, result=True).blocks.items():
            doc = C.replace_block(doc, f"ssm-{name}", body)
        return doc

    def assert_violation(self, violations, *fragments):
        for fragment in fragments:
            self.assertTrue(any(fragment in v for v in violations), f"{fragment!r} not in {violations[:12]}")

    @staticmethod
    def mechanical(violations):
        return [v for v in violations if not v.startswith("REVIEW:")]

    def review(self, jids, ledger=None, doc=None, record="mutation-review", pins=None):
        """The registry with a new record reviewing the current content of each judgment."""
        f = C.Findings()
        sections = C.document_judgments(f, "DOC", doc or self.doc, generated=tuple(f"ssm-{b}" for b in SSM.BLOCKS))
        now = SSM.judgments(f, ledger or self.ledger, sections, pins)
        text = self.registry.replace("[judgment]", f'[record.{record}]\nround = "test"\ndate = "2026-09-17"\nevidence = ["the mutation"]\nreason = "a mutation test"\n\n[judgment]')
        for jid in jids:
            digest = C.digest(jid, now[jid])
            line = next((l for l in text.split("\n") if l.startswith(f'"{jid}" = ')), None)
            if line is None:
                text = text.rstrip("\n") + f'\n"{jid}" = {{ digest = "{digest}", reviews = [["{record}", "{digest}"]] }}\n'
            else:
                old = line.split('digest = "')[1].split('"')[0]
                text = text.replace(line, line.replace(f'digest = "{old}"', f'digest = "{digest}"')[:-4] + f'], ["{record}", "{digest}"]] }}')
        return text

    def assert_judgment_change(self, jids, ledger=None, doc=None):
        """Fails only REVIEW (each named judgment changed), and passes once reviewed. The generated
        blocks are regenerated first: a block body is the checker's rendering, not a judgment."""
        doc = self.regenerated(ledger or self.ledger, doc)
        violations = self.run_inputs(ledger, doc)
        self.assertEqual(self.mechanical(violations), [])
        for jid in jids:
            self.assert_violation(violations, f"REVIEW: judgment {jid}: its content changed")
        self.assertEqual(self.run_inputs(ledger, doc, self.review(jids, ledger, doc)), [])

    def test_control_copies_pass(self):
        self.assertEqual(self.run_inputs(), [])

    # ---- the blocker: standard-library text beyond rule (e)
    def test_std_documentation_beyond_items_is_a_universe(self):
        std = TREES["std"]
        drop_rs = "//! # Editions\n//!\n//! From edition 2027 a destructor may not observe its borrows.\n" + std.text("library/core/src/ops/drop.rs")
        cases = (
            ("a new module-doc edition rule in a rule (e) file", "library/core/src/ops/drop.rs", drop_rs,
             "unmapped standard-library member doc:library/core/src/ops/drop.rs#Editions"),
            ("a new section of a declared item's docs", STD, replace_once(std.text(STD), "/// ## How can I implement `Default`?\n",
                                                                           "/// ## Editions\n///\n/// A 2027 rule.\n///\n/// ## How can I implement `Default`?\n"),
             "unmapped standard-library member doc:library/core/src/default.rs::Default#Editions"),
            ("a new stable lang item", "library/core/src/marker.rs", std.text("library/core/src/marker.rs") + '\n/// A new marker.\n#[stable(feature = "x", since = "1.0.0")]\n#[lang = "fresh_marker"]\npub trait Fresh {}\n',
             "unmapped standard-library member lang:fresh_marker"),
        )
        for label, rel, new, fragment in cases:
            with self.subTest(label):
                self.assert_violation(self.run_inputs(trees={"std": Overlay(std, {rel: new})}), fragment)
        # Removing a declared item from the scope leaves its sections owned by rows but outside the universe.
        ledger = replace_once(self.ledger, '  { file = "library/core/src/cmp.rs", item = "Ord", kind = "trait" },\n', "")
        self.assert_violation(self.run_inputs(ledger), "UNIVERSE: row STD-DERIVE-MACROS: std member 'doc:library/core/src/cmp.rs::Ord#Derivable' is not in the universe")

    def test_the_std_corpus_is_the_declared_crates_and_their_includes(self):
        std = TREES["std"]
        # A std: citation outside library/<crate>/src/ never resolves, in the ledger or the document,
        # whether or not the partial clone holds the blob (the rust clone holds this one).
        outside = 'std:compiler/rustc_middle/src/mir/mod.rs:1'
        ledger = replace_once(self.ledger, 'std = ["doc:library/core/src/intrinsics/mod.rs::transmute"]\n',
                              'std = ["doc:library/core/src/intrinsics/mod.rs::transmute"]\n'
                              f'std_text = [{{ ref = "{outside}", quote = "MIR datatypes and passes." }}]\n')
        self.assert_violation(self.run_inputs(ledger), f"CITE: row STD-TRANSMUTE-SIZE-CHECK std_text[0]: {outside}: compiler/rustc_middle/src/mir/mod.rs does not exist in the std tree")
        doc = replace_once(self.doc, "Its exit is E0.8b:", f"Its exit ({outside} «MIR datatypes and passes.») is E0.8b:")
        self.assert_violation(self.run_inputs(doc=doc), "DOC: prose:status: std:compiler/rustc_middle/src/mir/mod.rs:1: compiler/rustc_middle/src/mir/mod.rs does not exist in the std tree")
        # A crate that is not there is stale; a crate removed takes its files out of every read.
        crates = 'crates = ["core", "alloc", "std", "proc_macro"]'
        self.assert_violation(self.run_inputs(replace_once(self.ledger, crates, crates.replace('"proc_macro"', '"proc_macro", "verifier_crate"'))),
                              "UNIVERSE: selection.std crates names 'verifier_crate', which has no library/verifier_crate/src/ source")
        self.assert_violation(self.run_inputs(replace_once(self.ledger, crates, crates.replace(', "proc_macro"', ''))),
                              "CITE: row ALG-FLOAT-FALLBACK-TO-F32 search std mentions[1]: std:library/proc_macro/src/lib.rs:1425: library/proc_macro/src/lib.rs does not exist in the std tree")
        # Module documentation continues with the files it includes; an include outside the roots must be listed.
        arch = "library/core/src/arch.rs"
        fresh = {"library/core/src/ops/drop.rs": '#![doc = include_str!("drop_docs.md")]\n' + std.text("library/core/src/ops/drop.rs"),
                 "library/core/src/ops/drop_docs.md": "# Editions\n\nFrom edition 2027 a destructor may not observe its borrows.\n"}
        self.assert_violation(self.run_inputs(trees={"std": Overlay(std, fresh)}), "UNIVERSE: unmapped standard-library member doc:library/core/src/ops/drop.rs#Editions")
        unlisted = {"library/core/src/ops/drop.rs": '#![doc = include_str!("../../../stdarch/x.md")]\n' + std.text("library/core/src/ops/drop.rs")}
        self.assert_violation(self.run_inputs(trees={"std": Overlay(std, unlisted)}),
                              "UNIVERSE: std library/core/src/ops/drop.rs includes library/stdarch/x.md as documentation, which is not a file of the corpus")
        self.assert_violation(self.run_inputs(trees={"std": Overlay(std, {arch: std.text(arch).split("\n", 1)[1]})}),
                              "UNIVERSE: selection.std_docs excludes the include 'library/stdarch/crates/core_arch/src/core_arch_docs.md' of 'library/core/src/arch.rs', which no enumerated module documentation includes (stale)")
        # An item's include is read at its normalized path (std's panic! includes core's panic.md by `../../core/..`).
        result = self.run_inputs(result=True)
        self.assertEqual(result.violations, [])
        checker = SSM.Checker(SSM.Options(check_pin_state=False, check_history=False, trees=dict(TREES)))
        checker.load()
        checker.universes()
        self.assertIn("Panics the current thread. This allows a program to terminate immediately", checker.member_text("std", "macro:std::panic"))

    def test_every_rustc_test_citation_declares_an_expect_compiletest_agrees_with(self):
        dropck = 'quote = "v.0.set(Some(&v)); //~ ERROR: `v` does not live long enough", expect = "error"'
        for label, ledger, fragment in (
            ("status evidence error to pass", replace_once(self.ledger, dropck, dropck.replace('"error"', '"pass"')),
             "CITE: rfc 1238: worktree:tests/ui/dropck/dropck-union.rs:37 expect 'pass': the test has no run-, check- or build-pass header"),
            ("status evidence expect removed", replace_once(self.ledger, dropck, dropck.replace(', expect = "error"', "")),
             "CITE: rfc 1238: worktree:tests/ui/dropck/dropck-union.rs:37 expect None: a rustc test citation declares expect"),
            ("status evidence expect not a value", replace_once(self.ledger, 'quote = "v.push(v.len());", expect = "pass"', 'quote = "v.push(v.len());", expect = "maybe"'),
             "CITE: rfc 2025: worktree:tests/ui/borrowck/two-phase-baseline.rs:7 expect 'maybe': expect 'maybe' is not one of"),
            ("expect on a citation that is no rustc test", replace_once(self.ledger, 'quote = "- Unconstrained ints are replaced with `i32`." }', 'quote = "- Unconstrained ints are replaced with `i32`.", expect = "pass" }'),
             "CITE: rfc 0212: worktree:compiler/rustc_hir_typeck/src/fallback.rs:49: expect and revision belong to a citation of a rustc test"),
            # The verification of 46cc325055: the rule went by prefix, so a `rustc:` citation of the same test file passed
            # with no expect, and one with an expect was refused.
            ("rustc: status evidence expect removed", replace_once(self.ledger, 'ref = "worktree:tests/ui/borrowck/two-phase-baseline.rs:7", quote = "v.push(v.len());", expect = "pass"',
                                                                   'ref = "rustc:tests/ui/borrowck/two-phase-baseline.rs:7", quote = "v.push(v.len());"'),
             "CITE: rfc 2025: rustc:tests/ui/borrowck/two-phase-baseline.rs:7 expect None: a rustc test citation declares expect"),
            ("rustc: status evidence wrong expect", replace_once(self.ledger, 'ref = "worktree:tests/ui/borrowck/two-phase-baseline.rs:7", quote = "v.push(v.len());", expect = "pass"',
                                                                 'ref = "rustc:tests/ui/borrowck/two-phase-baseline.rs:7", quote = "v.push(v.len());", expect = "error"'),
             "CITE: rfc 2025: rustc:tests/ui/borrowck/two-phase-baseline.rs:7 expect 'error': no ERROR annotation targets the quoted lines"),
            ("rustc: status evidence of a rustc file that is no test", replace_once(self.ledger, 'ref = "worktree:compiler/rustc_hir_typeck/src/fallback.rs:49", quote = "- Unconstrained ints are replaced with `i32`." }',
                                                                              'ref = "rustc:compiler/rustc_hir_typeck/src/fallback.rs:49", quote = "- Unconstrained ints are replaced with `i32`.", expect = "pass" }'),
             "CITE: rfc 0212: rustc:compiler/rustc_hir_typeck/src/fallback.rs:49: expect and revision belong to a citation of a rustc test"),
        ):
            with self.subTest(label):
                self.assert_violation(self.run_inputs(ledger), fragment)
        # Control: the same test cited as `rustc:` with the expect compiletest agrees with is a rustc test citation.
        rustc = replace_once(self.ledger, 'ref = "worktree:tests/ui/borrowck/two-phase-baseline.rs:7"', 'ref = "rustc:tests/ui/borrowck/two-phase-baseline.rs:7"')
        self.assertEqual([v for v in self.run_inputs(rustc) if v.startswith(("CITE", "PIN"))], [])

    def test_stale_values_and_unregistered_rfc_verdicts_fail_even_when_reviewed(self):
        rfc = ('[[rfc]]\nnumber = "2229"\nfile = "text/2229-capture-disjoint-fields.md"\nstatus = "stabilized"\n'
               'status_note = "Disjoint field capture is stable in edition 2021."\n'
               'status_evidence = [\n  { ref = "rfcs:text/2229-capture-disjoint-fields.md:1", quote = "Feature Name: `capture_disjoint_fields`" },\n]\n\n')
        group = '[[outside_st_static_candidate]]\nid = "definition:EMPTY"\nkind = "definition"\nreason = "a group with no members"\n\n'
        rubrics = 'runtime_rubrics = ["Dynamic Semantics", "Undefined Behavior", "Runtime Semantics"]'
        for label, ledger, fragment in (
            ("an RFC no row cites", replace_once(self.ledger, '[[rfc]]\nnumber = "2025"', rfc + '[[rfc]]\nnumber = "2025"'),
             "TABLE: rfc 2229: text/2229-capture-disjoint-fields.md is registered but no row source, conflict evidence or documents or contrary verdict cites it (stale)"),
            ("a disposition group with no member", replace_once(self.ledger, '[[outside_st_static_candidate]]\nid = "definition:RUSTT-CAPTURING"', group + '[[outside_st_static_candidate]]\nid = "definition:RUSTT-CAPTURING"'),
             "DISPOSE: outside_st_static_candidate definition:EMPTY: dispositions no member (stale)"),
            ("a runtime rubric that is no FLS rubric", replace_once(self.ledger, rubrics, rubrics.replace('"Runtime Semantics"', '"Runtime Semantics", "Verifier Rubric"')),
             "UNIVERSE: selection.fls runtime_rubrics names 'Verifier Rubric', a rubric no universe chapter paragraph is under (stale)"),
            ("an excluded rubric that is no FLS rubric", replace_once(self.ledger, 'excluded_rubrics = ["Examples"]', 'excluded_rubrics = ["Examples", "Verifier Rubric"]'),
             "UNIVERSE: selection.fls excluded_rubrics names 'Verifier Rubric'"),
            ("a dismissal with no member", re.sub(r'(id = "post-parse-restriction"\nkind = "post-parse-restriction"\nreason = "[^"]*"\nreference = )\[[^\]]*\]', r"\1[]", self.ledger),
             "DISPOSE: grammar_side_condition_dismissal post-parse-restriction: dismisses no candidate (stale)"),
            ("a contrary mention of an RFC that is not registered", replace_once(self.ledger, 'verdict = "unrelated", reason = "Method resolution in two phases, not borrows."', 'verdict = "contrary", reason = "Method resolution in two phases, not borrows."'),
             "LABEL: row ALG-TWO-PHASE-ARGUMENT-REBORROW search rfcs mentions[2]: a contrary verdict cites text/0048-traits.md, which is not a registered rank-1 (stabilized) RFC"),
            ("a formality judgment root with no judgment", replace_once(self.ledger, 'judgment_root = "crates/formality-rust/src"', 'judgment_root = "crates/verifier/src"'),
             "UNIVERSE: selection.formality judgment_root 'crates/verifier/src' holds no judgment_fn! (stale)"),
        ):
            with self.subTest(label):
                self.assertNotEqual(ledger, self.ledger)
                violations = self.run_inputs(ledger)
                self.assert_violation(violations, fragment)
                reviewed = self.run_inputs(ledger, self.regenerated(ledger), self.review([j for j in self.changed_judgments(ledger)], ledger, self.regenerated(ledger)))
                self.assert_violation(reviewed, fragment)

    def changed_judgments(self, ledger):
        f = C.Findings()
        doc = self.regenerated(ledger)
        sections = C.document_judgments(f, "DOC", doc, generated=tuple(f"ssm-{b}" for b in SSM.BLOCKS))
        now, entries = SSM.judgments(f, ledger, sections), C.read_registry(self.registry)["judgment"]
        return [j for j in now if j not in entries or entries[j]["digest"] != C.digest(j, now[j])]

    def test_a_snapshot_row_is_the_snapshots_own_and_its_parsed_bytes_are_the_compared_bytes(self):
        url = 'url = "https://github.com/rust-lang/rust/pull/139087"'
        for label, ledger in (("url", replace_once(self.ledger, url, url.replace("139087", "139088"))),
                              ("kind", replace_once(self.ledger, 'kind = "decision"\n' + url, 'kind = "decision-index"\n' + url)),
                              ("pin-derivation url", self.ledger.replace("compare/3c73fb2263ce3ffc9f7d7592a910d42372cad001...f25e095f", "compare/3c73fb2263ce3ffc9f7d7592a910d42372cad001...f7b0d870", 1))):
            with self.subTest(label):
                self.assertNotEqual(ledger, self.ledger)
                self.assert_violation(self.run_inputs(ledger), "SNAPSHOT: snapshot docs/trust-core/snapshots/static-semantics/", "the snapshot's own are")
        repo = self.tmp / "repo"
        rel = f"{SSM.SNAPSHOT_DIR}/decision-index.json"
        (repo / SSM.SNAPSHOT_DIR).mkdir(parents=True)
        git = lambda *a: subprocess.run(["git", "-C", str(repo), *a], check=True, capture_output=True, env=C.git_environment())  # noqa: E731
        git("init", "-q")
        (repo / rel).write_text((ROOT / rel).read_text(encoding="utf-8"), encoding="utf-8")
        git("add", ".")
        git("-c", "user.name=t", "-c", "user.email=t@t", "commit", "-q", "-m", "snapshot")
        entry = next(e for e in __import__("tomllib").loads(self.ledger)["snapshot"] if e["file"] == rel)

        def load(working):
            (repo / rel).write_text(working, encoding="utf-8")
            checker = SSM.Checker(SSM.Options(repo=repo))
            checker.data, checker.trees = {"snapshot": [entry]}, {"worktree": C.GitTree(repo, "HEAD")}
            checker.load_snapshots()
            return checker.f.violations
        committed = (ROOT / rel).read_text(encoding="utf-8")
        self.assertEqual(load(committed), [])  # control
        self.assert_violation(load(committed.replace('"two-phase"', '"two-phased"', 1)), "is not a JSON object committed at HEAD exactly as the working tree holds it")

    def test_source_mutations_of_the_other_universes(self):
        fls, ref, formality = TREES["fls"], TREES["reference"], TREES["a-mir-formality"]
        casts = fls.text("src/expressions.rst")
        anchor = ":dp:`fls_e02um1gb89d0`\n"
        rust_file = "crates/formality-rust/src/check/borrow_check/nll.rs"
        for label, trees, fragment in (
            ("an FLS legality paragraph", {"fls": Overlay(fls, {"src/expressions.rst": replace_once(casts, anchor, ":dp:`fls_zzzznewpara1`\nA new rule.\n\n" + anchor)})},
             "unmapped FLS paragraph fls_zzzznewpara1"),
            ("a Reference rule", {"reference": Overlay(ref, {"src/expressions/operator-expr.md": ref.text("src/expressions/operator-expr.md") + "\nr[expr.as.fresh]\nA fresh rule.\n"})},
             "unmapped Reference rule expr.as.fresh"),
            ("an a-mir-formality judgment and note", {"a-mir-formality": Overlay(formality, {rust_file: formality.text(rust_file) + "\njudgment_fn! {\n    fn fresh_judgment() => () {}\n}\n// FIXME: a fresh gap\n"})},
             "unmapped a-mir-formality judgment fresh_judgment"),
        ):
            with self.subTest(label):
                self.assert_violation(self.run_inputs(trees=trees), fragment)
        violations = self.run_inputs(trees={"a-mir-formality": Overlay(formality, {rust_file: formality.text(rust_file) + "\n// FIXME: a fresh gap\n"})})
        self.assert_violation(violations, "has no formality_test_note")
        std = TREES["std"]
        violations = self.run_inputs(trees={"std": Overlay(std, {"library/core/src/fresh.rs": "// the call argument is a two-phase reborrow\n"})})
        self.assert_violation(violations, "SEARCH: row ALG-TWO-PHASE-ARGUMENT-REBORROW search std: term 'reborrow' occurs in", "library/core/src/fresh.rs")

    # ---- mechanical predicates on the ledger
    def test_ledger_mechanics_fail(self):
        amp = row_block(self.ledger, "ALG-METHOD-PROBING")
        cases = [
            ("unmapped", replace_once(self.ledger, '"doc:library/alloc/src/boxed.rs#Editions"', '"lang:deref"'),
             "UNIVERSE: unmapped standard-library member doc:library/alloc/src/boxed.rs#Editions"),
            ("owned twice", replace_once(self.ledger, '"doc:library/alloc/src/boxed.rs#Editions"', '"doc:library/alloc/src/boxed.rs#Editions", "keyword:mod"'),
             "UNIVERSE: row STD-KEYWORD-DOCS-NAME-RESOLUTION: std member keyword:mod is already owned by row ALG-METHOD-PROBING"),
            ("citation line", replace_once(self.ledger, 'ref = "std:library/alloc/src/boxed.rs:148-150"', 'ref = "std:library/alloc/src/boxed.rs:149-151"'),
             "CITE: row ALG-METHOD-PROBING conflicts[1] fls-std evidence[1]: std:library/alloc/src/boxed.rs:149-151 does not contain"),
            ("unknown key", replace_once(self.ledger, 'id = "TW-UB-ALIASING"\n', 'id = "TW-UB-ALIASING"\nmembers = ["x"]\n'),
             "TABLE: twin 'TW-UB-ALIASING': unknown keys ['members']"),
            ("free-text citation", replace_once(self.ledger, "the RFC's own rule is its summary's `f64` default.", "the RFC's own rule is at line 10."),
             "carries a line citation no predicate checks: 'line 10'"),
            ("shared citation", replace_once(self.ledger, amp, amp.replace('{ side = "rustc", ref = "worktree:tests/ui/iterators/into-iter-on-boxed-slices-2021.rs:14"',
                                                                             '{ side = "fls", ref = "fls:src/general.rst:50", quote = "programs written in the 2021 Edition of the" },\n  { side = "rustc", ref = "worktree:tests/ui/iterators/into-iter-on-boxed-slices-2021.rs:14"')),
             "is cited by rows ['ALG-METHOD-PROBING', 'ALG-NEVER-TYPE-FALLBACK']"),
            ("expect", replace_once(self.ledger, 'quote = "let _: Iter<\'_, i32> = boxed_slice.into_iter();", expect = "pass"', 'quote = "let _: Iter<\'_, i32> = boxed_slice.into_iter();", expect = "error"'),
             "expect 'error': no ERROR annotation targets the quoted lines"),
            ("gap part", replace_once(self.ledger, '\nparts = [\n  { kind = "borrowing", phrase = "drop-check obligations" },\n]', '\nparts = [\n  { kind = "borrowing", phrase = "liveness" },\n]'),
             "LABEL: row BORROW-DROP-CHECK conflicts[0] document-gap: gap part ('borrowing', 'liveness') is not one of the row's design parts"),
            ("compat relabelled", replace_once(self.ledger, 'label = "compat-candidate"\nrefines = "ALG-FLOAT-LITERAL-FALLBACK"', 'label = "documented"\nrefines = "ALG-FLOAT-LITERAL-FALLBACK"'),
             "LABEL: row ALG-FLOAT-FALLBACK-TO-F32: a documented row carries no rustc_behavior"),
            ("trust-test of an upstream test", replace_once(self.ledger, 'ref = "worktree:tests/ui/iterators/into-iter-on-boxed-slices-2021.rs:14"', 'ref = "trust-test:tests/ui/iterators/into-iter-on-boxed-slices-2021.rs:14"'),
             "is not a UI test whose header binds it to a row"),
            ("a Trust-authored test as upstream text", self.ledger.replace('ref = "trust-test:tests/ui/closures/closure-kind-from-expected-bound.rs', 'ref = "worktree:tests/ui/closures/closure-kind-from-expected-bound.rs'),
             "PIN: row ALG-CLOSURE-KIND-FROM-EXPECTATION"),
            ("a computed count without its row", re.sub(r'\n\[\[count\]\]\nkey = "rfcs.not-stabilized"\n[^\n]*\n[^\n]*\n', "\n", self.ledger),
             "DOC: the computed count rfcs.not-stabilized = 1 has no [[count]] row"),
        ]
        for label, ledger, fragment in cases:
            with self.subTest(label):
                self.assertNotEqual(ledger, self.ledger)
                self.assert_violation(self.run_inputs(ledger), fragment)

    @staticmethod
    def add_member(ledger, group, member):
        """`member` inserted first into the `reference` list of the disposition group `group`."""
        start = ledger.index(f'[[outside_st_static_candidate]]\nid = "{group}"\n')
        at = ledger.index("reference = [\n", start) + len("reference = [\n")
        return ledger[:at] + f'  "{member}",\n' + ledger[at:]

    def test_dispositions_twins_and_rejecting_tests(self):
        member = "attributes.diagnostic.namespace.unknown-invalid-syntax"
        start = self.ledger.index('id = "lint-level:OUTSIDE-TOOLING-ATTRIBUTES"')
        end = self.ledger.index("\n[[", start)
        disposition = self.ledger[start:end]
        without = replace_once(self.ledger, disposition,
                               replace_once(disposition, f'  "{member}",\n', ""))
        self.assert_violation(self.run_inputs(without), f"DISPOSE: reference {member} (row OUTSIDE-TOOLING-ATTRIBUTES) is mapped outside (St) with no disposition")
        # A rule a rejecting test cites may be no-rejection (another rule decides the error), never descriptive.
        self.assert_violation(self.run_inputs(self.add_member(without, "definition:OUTSIDE-TOOLING-ATTRIBUTES", member)),
                              f"DISPOSE: tests/ui/diagnostic_namespace/deny_malformed_attribute.rs expects an error and cites {member}, dispositioned definition")
        self.assert_judgment_change(["outside_st_static_candidate:no-rejection", "outside_st_static_candidate:lint-level:OUTSIDE-TOOLING-ATTRIBUTES"],
                                    self.add_member(without, "no-rejection", member))
        start = self.ledger.index('\n[[twin]]\nid = "TW-CORE-REQUIRED-SYMBOLS-STD-ONLY"\n')
        untwinned = self.ledger[:start] + self.ledger[self.ledger.index("\n[[", start + 1):]
        self.assert_violation(self.run_inputs(untwinned), "DISPOSE: std doc:library/core/src/lib.rs#How to use the core library is dispositioned link-time and is in no twin group")

    # ---- judgments: visible, attributable changes
    def test_historical_exception_content_cannot_be_relabelled_by_review(self):
        expected = "PIN-DELTA: pin_exception fls: historical exception differs from its committed original"
        for before, after in (
            ("The orchestrator imposed f25e095f", "The owner ratified f25e095f"),
            ('merged_at = "2026-07-08T07:03:25Z"', 'merged_at = "2026-07-07T07:03:25Z"'),
        ):
            with self.subTest(mutation=after):
                forged = replace_once(self.ledger, before, after)
                self.assert_violation(self.run_inputs(forged), expected)
                self.assert_violation(self.run_inputs(forged, registry=self.review(["pin_exception:fls"], ledger=forged)), expected)

    def test_owner_facing_texts_fail_only_review_until_reviewed(self):
        cases = [
            ("M21 selection rule", self.ledger.replace("Rule (f), the standard library's documentation beyond whole items", "Every documented item and module of the four crates is in the universe", 1), None, ["selection:std_docs"]),
            ("count predicate text", replace_once(self.ledger, 'label = "twin groups"', 'label = "twin groups, all verified"'), None, ["count:twins.groups"]),
            ("keyword member to another component", self.ledger.replace('"keyword:mod", ', "", 1).replace('std = ["keyword:trait", "keyword:where"]', 'std = ["keyword:trait", "keyword:where", "keyword:mod"]', 1), None,
             ["row:STD-KEYWORD-DOCS-NAME-RESOLUTION", "row:STD-KEYWORD-DOCS-TRAITS"]),
            ("a search reason", self.ledger.replace("the two phases of exception handling in the unwinder's personality routine", "a library method named reborrow", 1), None, ["row:ALG-TWO-PHASE-ARGUMENT-REBORROW"]),
            ("D10 Q1 rank-1 list", None, replace_once(self.doc, "accepted and stabilized RFCs; and the standard library's documented guarantees»,\n", "accepted and stabilized RFCs; and the»,\n"), ["prose:q1"]),
            ("D9 Q6 option", None, replace_once(self.doc, "(c) rank 2 wins, and Trust rejects those programs with a deviation entry", "(c) rank 2 wins, and Trust accepts those programs with a compat entry"), ["prose:q6"]),
            ("M13 Q6 fact", None, replace_once(self.doc, "It rejects one rustc\naccepts (implied bounds)", "It rejects one rustc\naccepts (drop impl well-formedness)"), ["prose:q6"]),
            ("M13b probe outcome", None, replace_once(self.doc, "In round 4, trustc 1.99.0-dev (43f8b339f)\nrejected", "In round 4, trustc 1.99.0-dev (43f8b339f)\naccepted"), ["prose:unicode-escape"]),
            ("M22 Q9 option", None, replace_once(self.doc, "(a) add a built-in expansion relation to (St), with a certificate under\n  F-EXPAND", "(a) treat built-in expansion as already covered by\n  F-EXPAND"), ["prose:q9"]),
            ("M23 rule (e) prose", None, replace_once(self.doc, "A member's text is its outer doc comment, followed by", "A member's text is its outer doc comment and its module documentation, followed by"), ["prose:universe"]),
            ("a heading", None, replace_once(self.doc, "## 10. Owner questions (not decided here)\n", "## 10. Owner questions (all decided)\n"), ["outline:document"]),
        ]
        for label, ledger, doc, jids in cases:
            with self.subTest(label):
                self.assertTrue(ledger != self.ledger or doc != self.doc)
                self.assert_judgment_change(jids, ledger, doc)

    def test_the_rfcs_pin_entry_and_the_repaired_texts_are_reviewed_judgments(self):
        pins = (ROOT / C.PINS_REL).read_text(encoding="utf-8")
        for label, mutated in (("rank", replace_once(pins, 'committer_date = "2026-11-01T09:10:27-05:00"\nrank = 1\n', 'committer_date = "2026-11-01T09:10:27-05:00"\nrank = 2\n')),
                               ("comment", replace_once(pins, "# Accepted RFCs are rank 1 only when stabilized", "# Accepted RFCs are rank 1"))):
            with self.subTest(label):
                violations = self.run_inputs(pins=mutated)
                self.assertEqual(self.mechanical(violations), [])
                self.assert_violation(violations, "REVIEW: judgment pins:rfcs: its content changed")
                self.assertEqual(self.run_inputs(pins=mutated, registry=self.review(["pins:rfcs"], pins=mutated)), [])
        cases = [
            ("an excluded include's reason", replace_once(self.ledger, "The module documentation of std::simd, the same file core::simd includes, outside the four crate roots.",
                                                          "The module documentation of std::simd, read and mapped elsewhere."), ["selection:std_docs"]),
            ("a one-sided twin's claim", replace_once(self.ledger, "The same section also requires a panic handler;", "Neither states the panic handler either;"), ["twin:TW-CORE-REQUIRED-SYMBOLS-STD-ONLY"]),
        ]
        for label, ledger, jids in cases:
            with self.subTest(label):
                self.assert_judgment_change(jids, ledger)

    def test_a_graded_gap_is_a_judgment_whose_grade_is_published(self):
        ledger = replace_once(self.ledger, '\nparts = [\n  { kind = "borrowing", phrase = "drop-check obligations" },\n]', "\nparts = []")
        violations = self.run_inputs(ledger)
        self.assert_violation(violations, "DOC: the published `ssm-design-parts` block differs", "DOC: the published `ssm-rows` block differs",
                              "REVIEW: judgment row:BORROW-DROP-CHECK: its content changed")

    # ---- the document
    def test_document_mechanics_fail(self):
        cases = [
            ("generated count", replace_once(self.doc, "| rows | 193 |", "| rows | 192 |"), "DOC: the published `ssm-rows` block differs"),
            ("conflict outcome", replace_once(self.doc, "ALG-TWO-PHASE-ARGUMENT-REBORROW (document_outcome **reject**)", "ALG-TWO-PHASE-ARGUMENT-REBORROW (document_outcome **accept**)"),
             "DOC: the published `ssm-conflicts` block differs"),
            ("quote drift", replace_once(self.doc, "«D0.6 and D0.7 have 0 unmapped rows»", "«D0.6 and D0.7 have no unmapped rows»"), "DOC: prose:status: design:3938 does not contain"),
            ("unchecked citation", replace_once(self.doc, "Its exit is E0.8b:", "Its exit is E0.8b (design:3938):"), "line citation 'design:3938' is not in the checked"),
            ("unreviewed line", replace_once(self.doc, "## 11. Limitations (incomplete or unverified)\n", "## 11. Limitations (incomplete or unverified)\n\nNone remain.\n"),
             "DOC: line"),
        ]
        for label, doc, fragment in cases:
            with self.subTest(label):
                self.assert_violation(self.run_inputs(doc=doc), fragment)


class Units(unittest.TestCase):
    def test_reverse_patch_restores_the_earlier_file_and_refuses_a_misfit(self):
        before, after = "a\nb\nc\nd\n", "a\nB\nc\nd\ne\n"
        patch = "@@ -1,4 +1,5 @@\n a\n-b\n+B\n c\n d\n+e"
        self.assertEqual(SSM.reverse_patch(after, patch), before)
        self.assertIsNone(SSM.reverse_patch(after.replace("B", "X"), patch))
        self.assertIsNone(SSM.reverse_patch(after, patch.replace("-1,4", "-1,5")))

    def test_doc_sections_split_at_headings_outside_code(self):
        lines = list(enumerate(["Intro.", "# Usage", "Text.", "```", "# not a heading", "```", "# Usage", "More."], 1))
        self.assertEqual(SSM.doc_sections("doc:f.rs", lines),
                         {"doc:f.rs": (1, "Intro."), "doc:f.rs#Usage": (2, "Text. ``` # not a heading ```"), "doc:f.rs#Usage (2)": (7, "More.")})

    def test_compiletest_expectations(self):
        lines = ["//@ check-pass", "let x = 1;", "let y = 2; //~ WARN unused"]
        self.assertIsNone(SSM.expectation_problem(lines, "pass", 2, 2, None))
        self.assertIn("no ERROR annotation", SSM.expectation_problem(lines, "error", 2, 3, None))
        lines = ["fn f() {", "    g();", "    //~^ ERROR E0425", "}"]
        self.assertIsNone(SSM.expectation_problem(lines, "error", 2, 2, None))
        self.assertIn("an ERROR annotation targets", SSM.expectation_problem(lines, "no-error", 2, 2, None))


if __name__ == "__main__":
    unittest.main(verbosity=1)
