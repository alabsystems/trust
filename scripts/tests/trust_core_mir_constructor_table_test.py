#!/usr/bin/env python3
"""Controls for scripts/trust_core/mir_constructor_table.py (D0.3, the MIR constructor table).

* The REAL checker on the REAL inputs (the pinned MiniRust clone, this repository's design,
  rustc and library at HEAD, the vocabulary, the table, the document and the review registry)
  exits 0 and publishes the counts asserted here.
* Every mutation of a temporary copy of an input, or of a source read through an overlay of
  HEAD, makes the CHECKER report the violation it introduces, beside an unmutated control. A
  mechanical mutation names its predicate; a judgment mutation (a changed disposition, name,
  case or prose section) passes every mechanical predicate, fails REVIEW, and passes once a
  review record of its new digest is appended.

The shared layers (pins, citations, the Trust-marker guard, uniqueness, blocks, reviews and
their history) are tested in scripts/tests/trust_core_common_test.py. A missing source clone
is a FAILURE that prints the clone command, never a skip.

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
SCRIPT = ROOT / "scripts" / "trust_core" / "mir_constructor_table.py"
SPEC = importlib.util.spec_from_file_location("trust_core_mir_constructor_table", SCRIPT)
M = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(M)
C = M.C
TABLE, DOC, REGISTRY = ROOT / M.TABLE_REL, ROOT / M.DOC_REL, ROOT / M.REGISTRY_REL
SYNTAX, MIR_MOD = M.SYNTAX_REL, "compiler/rustc_middle/src/mir/mod.rs"

# The published counts (MIR_CONSTRUCTOR_TABLE.md). A change here is a change to the table.
PUBLISHED = {'variants': 182, 'fields': 29, 'in_scope': 32, 'boundary': 24, 'intrinsics': 279, 'construct_rows': 235, 'intrinsic_rows': 282, 'totals': (211, 123, 18, 46, 14, 10, 0), 'intrinsic_dispositions': {'core': 49, 'refusal': 210, 'no_op': 0, 'fallback': 17, 'split': 3}, 'seed': (93, 26, 116), 'intrinsic_seed': (10, 3, 269), 'doc_units': 525, 'doc_units_ruled': 81, 'minimize_hits': 113, 'design_commit': '5d5d8ad811e3f8220dded363c897b04d5375f004', 'citations': 977, 'doc_citations': 36}
PUBLISHED_JUDGMENTS = 737


class Overlay:
    """This repository at HEAD with some files replaced or added: the interface of common.GitTree."""

    def __init__(self, files: dict) -> None:
        self.base, self.overlay = C.GitTree(ROOT, "HEAD"), dict(files)

    def files(self, prefix="", suffixes=()):
        return sorted(set(self.base.files(prefix, suffixes)) | {r for r in self.overlay if r.startswith(prefix) and (not suffixes or r.endswith(suffixes))})

    def prefetch(self, rels):
        self.base.prefetch([r for r in rels if r not in self.overlay])

    def text(self, rel):
        return self.overlay[rel] if rel in self.overlay else self.base.text(rel)

    def lines(self, rel):
        text = self.text(rel)
        return None if text is None else text.split("\n")


def head(rel):
    return C.GitTree(ROOT, "HEAD").text(rel)


def replace_once(text, old, new):
    assert text.count(old) == 1, (old, text.count(old))
    return text.replace(old, new)


def block(text, kind, line):
    """The [[kind]] block of the table holding the exact line `line`."""
    found = [p for p in re.split(r"\n(?=\[\[)", text) if p.startswith(f"[[{kind}]]") and f"\n{line}\n" in p + "\n"]
    assert len(found) == 1, (kind, line, len(found))
    return found[0]


def edit_block(text, kind, line, edit, containing=None):
    parts = [p for p in re.split(r"\n(?=\[\[)", text) if p.startswith(f"[[{kind}]]") and f"\n{line}\n" in p + "\n" and (containing is None or containing in p)]
    assert len(parts) == 1, (kind, line, containing, len(parts))
    return replace_once(text, parts[0], edit(parts[0]))


class VocabularyRefusal(unittest.TestCase):
    def check(self, row, maps_to=(), refusals=("BoxDerefValidityUnsupported",)):
        checker = M.Checker(M.Options())
        checker.vocab = {"CastOp.Transmute": ["Built", "Promoted", "Runtime"]}
        checker.vocab_ops = {
            "CastKind::BoxDerefTransmute": {"maps_to": set(maps_to), "refusals": set(refusals)},
        }
        checker.used_refusals = set()
        checker.disposition(
            "box cast", row, "CastKind::BoxDerefTransmute",
            M.Member("BoxDerefTransmute", 1, []), ["Built", "Promoted", "Runtime"],
            {"BoxDerefValidityUnsupported": {}},
        )
        return checker.f.violations

    def test_exact_refusal_preserves_an_unrepresented_validity_obligation(self):
        row = {"disposition": "refusal", "refusal": "BoxDerefValidityUnsupported"}
        self.assertEqual(self.check(row), [])
        for maps_to, refusals in [(["CastOp.Transmute"], ["BoxDerefValidityUnsupported"]),
                                  ([], []), ([], ["AnotherRefusal"]),
                                  ([], ["BoxDerefValidityUnsupported", "AnotherRefusal"])]:
            with self.subTest(maps_to=maps_to, refusals=refusals):
                self.assertTrue(self.check(row, maps_to, refusals))

    def test_refusal_cannot_be_erased_or_replaced_by_transmute(self):
        self.assertTrue(self.check({"disposition": "core", "core": ["CastOp.Transmute"]}))
        self.assertTrue(self.check({"disposition": "refusal", "refusal": "AnotherRefusal"}))
        self.assertTrue(self.check({"disposition": "no_op", "no_op": {}}))


class DesignCommit(unittest.TestCase):
    """The D0.3 snapshot comparison on a small repository: what is a difference and what is not."""

    SCOPE = "compiler/rustc_middle/src/mir/syntax.rs"
    FILES = {SCOPE: "enum A {}\n", "library/core/src/intrinsics/mod.rs": "fn a() {}\n",
             "library/Cargo.lock": 'name = "trust-bignum"\nversion = "0.13.0"\n', "library/core/Cargo.lock": "inner\n"}

    def git(self, repo, *args):
        return subprocess.run(["git", "-C", str(repo), "-c", "user.name=t", "-c", "user.email=t@example.invalid",
                               "-c", "commit.gpgsign=false", "-c", "core.hooksPath=/dev/null", *args],
                              check=True, capture_output=True, text=True, env=C.git_environment()).stdout.strip()

    def findings(self, change):
        """The PIN findings when HEAD differs from the snapshot commit by `change` (path -> new text)."""
        with tempfile.TemporaryDirectory() as tmp:
            repo = Path(tmp)
            self.git(repo, "init", "-q", "--template=")
            for step in (self.FILES, change):
                for rel, text in step.items():
                    (repo / rel).parent.mkdir(parents=True, exist_ok=True)
                    (repo / rel).write_text(text)
                self.git(repo, "add", "-A")
                self.git(repo, "commit", "-q", "--allow-empty", "-m", "step")
            checker = M.Checker(M.Options(repo=repo))
            checker.d03_commit, checker.scope_files = self.git(repo, "rev-parse", "HEAD~1"), [self.SCOPE]
            checker.design_commit()
            self.assertEqual(checker.counts["design_commit"], checker.d03_commit)
            return [v for v in checker.f.violations if v.startswith("PIN: ")]

    def test_only_the_library_lock_may_differ_from_the_snapshot(self):
        self.assertEqual(M.PIN_UNCOMPARED, ("library/Cargo.lock",))
        self.assertEqual(self.findings({}), [])
        # A release bump rewrites the lock's own-version line and nothing the table reads.
        self.assertEqual(self.findings({"library/Cargo.lock": 'name = "trust-bignum"\nversion = "0.14.0"\n'}), [])
        for rel in (self.SCOPE, "library/core/src/intrinsics/mod.rs", "library/core/Cargo.lock", "library/Cargo.toml",
                    "library/new.rs"):
            with self.subTest(rel=rel):
                found = self.findings({rel: "changed\n", "library/Cargo.lock": "also changed\n"})
                self.assertEqual(len(found), 1, found)
                self.assertIn(f"differ from HEAD there: [{rel!r}]", found[0])

    def test_a_snapshot_commit_that_is_not_in_the_repository_is_a_finding(self):
        with tempfile.TemporaryDirectory() as tmp:
            repo = Path(tmp)
            self.git(repo, "init", "-q", "--template=")
            self.git(repo, "commit", "-q", "--allow-empty", "-m", "only")
            for commit in ("0" * 40, None):
                with self.subTest(commit=commit):
                    checker = M.Checker(M.Options(repo=repo))
                    checker.d03_commit, checker.scope_files = commit, [self.SCOPE]
                    checker.design_commit()
                    self.assertEqual(len([v for v in checker.f.violations if v.startswith("PIN: ")]), 1)


class RealInputs(unittest.TestCase):
    def test_real_inputs_pass_and_publish_the_counts(self):
        result = M.collect()
        self.assertEqual(result.violations, [])
        for key, value in PUBLISHED.items():
            self.assertEqual(result.counts[key], value, key)
        self.assertEqual(result.counts["reviews"]["judgments"], PUBLISHED_JUDGMENTS)
        self.assertIn("| **Total** | 211 | 123 | 18 | 46 | 14 | 10 | 0 |", result.table_text)

    def test_cli_exits_zero_on_real_inputs(self):
        run = subprocess.run([sys.executable, str(SCRIPT)], capture_output=True, text=True)
        self.assertEqual(run.returncode, 0, run.stderr)
        self.assertIn(f"mir_constructor_table: OK ({PUBLISHED['citations']} row citations, {PUBLISHED['doc_citations']} document citations, {PUBLISHED_JUDGMENTS} reviewed judgments)", run.stdout)

    def test_a_missing_clone_exits_two_with_its_clone_command(self):
        with tempfile.TemporaryDirectory() as tmp:
            run = subprocess.run([sys.executable, str(SCRIPT), "--minirust", str(Path(tmp) / "absent")], capture_output=True, text=True)
            self.assertEqual(run.returncode, 2)
            self.assertIn(f"git clone https://github.com/minirust/minirust {Path(tmp) / 'absent'}", run.stderr)


class Mutations(unittest.TestCase):
    def setUp(self):
        self._tmp = tempfile.TemporaryDirectory()
        self.tmp = Path(self._tmp.name)
        self.table, self.doc, self.registry = (p.read_text(encoding="utf-8") for p in (TABLE, DOC, REGISTRY))

    def tearDown(self):
        self._tmp.cleanup()

    def run_inputs(self, table=None, doc=None, registry=None, trees=None):
        paths = {}
        for name, text in (("table.toml", table or self.table), ("doc.md", doc or self.doc), ("registry.toml", registry or self.registry)):
            paths[name] = self.tmp / name
            paths[name].write_text(text, encoding="utf-8")
        options = M.Options(table=paths["table.toml"], doc=paths["doc.md"], registry=paths["registry.toml"], trees=trees or {},
                            check_pin_state=False, check_history=False, check_vocabulary=False)
        return M.collect(options).violations

    def assert_violation(self, violations, *fragments):
        for fragment in fragments:
            self.assertTrue(any(fragment in v for v in violations), f"{fragment!r} not in {violations[:12]}")

    def mechanical(self, violations):
        return [v for v in violations if not v.startswith("REVIEW:") and "published `mir-constructor-table-counts` block" not in v]

    def review(self, jids, table=None, doc=None, record="mutation-review"):
        """The registry with a new record's review of each judgment's current content appended."""
        f = C.Findings()
        now = M.judgments(f, table or self.table, C.document_judgments(f, "DOC", doc or self.doc, generated=(M.COUNTS_BLOCK,)))
        text = self.registry.replace("[judgment]", f'[record.{record}]\nround = "test"\ndate = "2026-09-17"\nevidence = ["the mutation"]\nreason = "a mutation test"\n\n[judgment]')
        for jid in jids:
            digest = C.digest(jid, now[jid])
            key = C.canonical(jid)
            line = next((l for l in text.split("\n") if l.startswith(f"{key} = ")), None)
            if line is None:
                text = text.rstrip("\n") + f'\n{key} = {{ digest = "{digest}", reviews = [["{record}", "{digest}"]] }}\n'
            else:
                old = line.split('digest = "')[1].split('"')[0]
                text = text.replace(line, line.replace(f'digest = "{old}"', f'digest = "{digest}"')[:-4] + f'], ["{record}", "{digest}"]] }}')
        return text

    def assert_judgment_change(self, table=None, doc=None, jids=()):
        """A judgment change passes every mechanical predicate, fails REVIEW for exactly `jids`, and passes once reviewed
        (a published count it moves is the counts block's, which the test does not regenerate)."""
        violations = self.run_inputs(table, doc)
        self.assertEqual(self.mechanical(violations), [])
        reviews = [v for v in violations if v.startswith("REVIEW:")]
        self.assertEqual(sorted(re.match(r"REVIEW: judgment (.*): its content changed", v).group(1) for v in reviews), sorted(jids))
        self.assertEqual([v for v in self.run_inputs(table, doc, registry=self.review(jids, table, doc)) if v.startswith("REVIEW:") or v in self.mechanical([v])], [])

    def test_control_copies_pass(self):
        self.assertEqual(self.run_inputs(), [])

    def test_constant_conversion_citations_require_the_complete_upstream_function(self):
        rel = "compiler/rustc_const_eval/src/const_eval/eval_queries.rs"
        original = head(rel)
        first, last = M.read_function_region(original, "op_to_const")
        changes = [
            ("control", original, True),
            ("unrelated marker", "// Trust: another file-level note\n" + original, True),
            ("unmarked body edit", replace_once(original, "if op.layout.is_zst() {", "if !op.layout.is_zst() {"), False),
            ("body marker", replace_once(original, "// Handle ZST consistently and early.", "// Trust: Handle ZST consistently and early."), False),
            ("leading doc marker", replace_once(original, "/// This function converts an interpreter value into a MIR constant.", "/// Trust: This function converts an interpreter value into a MIR constant."), False),
            ("missing function", original.replace("fn op_to_const<", "fn other_conversion<"), False),
            ("duplicate function", original + "\nfn op_to_const() {}\n", False),
        ]
        for label, text, accepted in changes:
            with self.subTest(label):
                checker = M.Checker(M.Options())
                checker.pins = C.load_pins(ROOT / C.PINS_REL)
                checker.rustc = Overlay({rel: text})
                checker.upstream = C.GitTree(C.sources_root() / "rust", checker.pins.alignment)
                checker.resolver = C.Resolver(ROOT, {"worktree": checker.rustc})
                checker.constant_evidence_region()
                self.assertEqual(not checker.f.violations, accepted, checker.f.violations)
                if accepted:
                    a, b = M.read_function_region(text, "op_to_const")
                    self.assertEqual(checker.resolver.verified[rel], [(a, b)])
                    self.assertEqual(b - a, last - first)
                    self.assertIsNone(checker.resolver.check(f"rustc:{rel}:{a + 19}", "// All scalar types"))
                    self.assertIsNotNone(checker.resolver.check(f"rustc:{rel}:{a - 1}", "}"))
                else:
                    self.assertNotIn(rel, checker.resolver.verified)

    def test_function_region_ignores_nested_and_quoted_definitions(self):
        for extra in [
            'const DECOY: &str = "fn op_to_const() {}";',
            'macro_rules! decoy { () => { fn op_to_const() {} } }',
            'mod nested { fn op_to_const() {} }',
        ]:
            with self.subTest(extra):
                text = extra + '\n// function docs\n#[instrument]\npub(super) fn op_to_const<T>() { let s = "}"; }\n'
                self.assertEqual(M.read_function_region(text, "op_to_const"), (1, 4))
                with self.assertRaises(M.LexError):
                    M.read_function_region(extra, "op_to_const")
        for text in ['fn op_to_const();', 'fn op_to_const() {', 'fn op_to_const() {} fn op_to_const() {}']:
            with self.subTest(text), self.assertRaises(M.LexError):
                M.read_function_region(text, "op_to_const")

    def test_changed_constant_conversion_fails_the_real_checker(self):
        rel = "compiler/rustc_const_eval/src/const_eval/eval_queries.rs"
        changed = replace_once(head(rel), "if op.layout.is_zst() {", "if !op.layout.is_zst() {")
        self.assert_violation(self.run_inputs(trees={"worktree": Overlay({rel: changed})}),
                              "function op_to_const: complete function text differs from the aligned upstream source")

    # ---- the universe
    def test_a_new_variant_or_field_needs_a_row_and_a_stale_row_fails(self):
        syntax, mod = head(SYNTAX), head(MIR_MOD)
        for label, trees, fragment in (
            ("variant", {"worktree": Overlay({SYNTAX: replace_once(syntax, "    Continue,\n", "    Continue,\n    Retry,\n")})},
             "UNIVERSE: UnwindAction::Retry (compiler/rustc_middle/src/mir/syntax.rs:"),
            ("Body field", {"worktree": Overlay({MIR_MOD: replace_once(mod, "    pub spread_arg: Option<Local>,\n", "    pub spread_arg: Option<Local>,\n    pub resumed: bool,\n")})},
             "UNIVERSE: Body.resumed (compiler/rustc_middle/src/mir/mod.rs:"),
        ):
            with self.subTest(label):
                self.assert_violation(self.run_inputs(trees=trees), fragment)
        self.assertEqual(self.run_inputs(trees={"worktree": Overlay({SYNTAX: syntax})}), [])  # control
        stale = edit_block(self.table, "construct", 'mir = "Body.span"', lambda b: b.replace('mir = "Body.span"', 'mir = "Body.spans"'))
        self.assert_violation(self.run_inputs(stale), "UNIVERSE: construct Body.spans Built,Promoted,Runtime: names no variant", "UNIVERSE: Body.span (")
        moved = edit_block(self.table, "construct", 'mir = "Body.span"', lambda b: b.replace("mod.rs:271", "mod.rs:270"))
        self.assert_violation(self.run_inputs(moved), "UNIVERSE: construct Body.span Built,Promoted,Runtime: at and mir_phases must be compiler/rustc_middle/src/mir/mod.rs:271")
        deleted = edit_block(self.table, "construct", 'mir = "Body.spread_arg"', lambda b: "")
        self.assert_violation(self.run_inputs(deleted), "UNIVERSE: Body.spread_arg (compiler/rustc_middle/src/mir/mod.rs:265) has no [[construct]] row")

    def test_a_trust_edit_inside_an_enumerated_region_fails_pin(self):
        syntax, mod = head(SYNTAX), head(MIR_MOD)
        for label, rel, text in (
            ("enum", SYNTAX, replace_once(syntax, "    /// No action is to be taken. Continue unwinding.\n", "    // Trust: no action\n")),
            ("container", MIR_MOD, replace_once(mod, "    /// Mark an argument local (which must be a tuple) as getting passed as\n", "    // Trust: spread\n")),
        ):
            with self.subTest(label):
                violations = self.run_inputs(trees={"worktree": Overlay({rel: text})})
                self.assert_violation(violations, f"PIN: {rel}: the parsed region of ")
        intrinsics = "library/core/src/intrinsics/mod.rs"
        marked = replace_once(head(intrinsics), "#[rustc_intrinsic]\npub const fn aggregate_raw_ptr", "// Trust: raw\n#[rustc_intrinsic]\npub const fn aggregate_raw_ptr")
        self.assert_violation(self.run_inputs(trees={"worktree": Overlay({intrinsics: marked})}),
                              f"PIN: {intrinsics}: the parsed region of intrinsic core::intrinsics::aggregate_raw_ptr carries a `Trust:` edit")

    def test_scope_boundary_and_absent_rows_are_derived(self):
        cases = [
            ("boundary", edit_block(self.table, "boundary", 'type = "ScalarInt"', lambda b: ""), "SCOPE: payload type ScalarInt"),
            ("absent", edit_block(self.table, "absent", 'name = "NullOp"', lambda b: ""), "SCOPE: NullOp is named by the design"),
            ("scope files", replace_once(self.table, '  "compiler/rustc_middle/src/mir/visit.rs",\n', ""), "SCOPE: [scope] scope_files must be the derived scope files"),
            ("container list", replace_once(self.table, '"Terminator", "SourceInfo"]', '"Terminator"]'), "UNIVERSE: construct SourceInfo.span Built,Promoted,Runtime: names no variant"),
        ]
        for label, table, fragment in cases:
            with self.subTest(label):
                self.assert_violation(self.run_inputs(table), fragment)
        added = replace_once(head(SYNTAX), "pub enum UnwindAction {", "pub enum NullOp { SizeOf }\n\npub enum UnwindAction {")
        self.assert_violation(self.run_inputs(trees={"worktree": Overlay({SYNTAX: added})}), "SCOPE: [[absent]] NullOp is stale")

    def test_table_shape_and_citations(self):
        cases = [
            ("duplicate", self.table.replace('[[refusal]]\nname = "AsyncDrop"', '[[refusal]]\nname = "Breakpoint"\nreason = "x"\nevidence = [\n  { ref = "design:1175", quote = "A construct not yet specified" },\n]\n\n[[refusal]]\nname = "AsyncDrop"', 1),
             "duplicate row 'Breakpoint'"),
            ("repeated element", edit_block(self.table, "construct", 'mir = "BasicBlockData.is_cleanup"', lambda b: b.replace('"BbKind.Regular"]', '"BbKind.Regular", "BbKind.Cleanup"]')),
             "TABLE: construct[", ),
            ("free text", edit_block(self.table, "construct", 'mir = "Body.span"', lambda b: b.replace("minimize = \"no arm\"", "minimize = \"no arm\"\nnote = \"see mod.rs:270\"")),
             "note must be non-empty text without an unchecked line citation"),
            ("unknown key", edit_block(self.table, "construct", 'mir = "Body.span"', lambda b: b + 'alias = "x"\n'), "unknown keys ['alias']"),
            ("quote", replace_once(self.table, 'quote = "/// A span representing this MIR, for error reporting."', 'quote = "/// A span representing this MIR, for errors."'),
             "CITATION: construct Body.span Built,Promoted,Runtime no_op: rustc:compiler/rustc_middle/src/mir/mod.rs:270 does not contain"),
            ("marked file", replace_once(self.table, '{ ref = "rustc:compiler/rustc_middle/src/mir/mod.rs:270", quote = "/// A span representing this MIR, for error reporting." }',
                                         '{ ref = "rustc:compiler/rustc_middle/src/mir/mod.rs:53", quote = "Trust" }'),
             "PIN: construct Body.span Built,Promoted,Runtime no_op: rustc:compiler/rustc_middle/src/mir/mod.rs:53: compiler/rustc_middle/src/mir/mod.rs carries a `Trust:` edit"),
        ]
        for label, table, fragment in cases:
            with self.subTest(label):
                self.assert_violation(self.run_inputs(table), fragment)

    # ---- phases
    def test_phase_rules_doc_pin_conflicts_and_coverage(self):
        cases = [
            ("uncited unit", edit_block(self.table, "phase_rule", 'id = "pr-body-pass-count-doc"', lambda b: ""),
             "PHASE: compiler/rustc_middle/src/mir/mod.rs:226-226 is a doc unit of Body matching phase_words"),
            ("doc pin", replace_once(self.table, "units = 525", "units = 524"), "PHASE: exactly one [[doc_pin]] in-scope-docs pins the doc text read: 525 units"),
            ("stale conflict", edit_block(self.table, "phase_conflict", 'id = "pc-raw-ptr-aggregate"', lambda b: b.replace('phases = ["Runtime(Initial)", "Runtime(PostCleanup)", "Runtime(Optimized)"]', 'phases = ["Built", "Analysis(Initial)", "Analysis(PostCleanup)", "Runtime(Initial)", "Runtime(PostCleanup)", "Runtime(Optimized)"]')),
             "PHASE: phase_conflict pc-raw-ptr-aggregate: for AggregateKind::RawPtr its phases"),
            ("coverage", edit_block(self.table, "construct", 'mir = "TerminatorKind::Yield"', lambda b: b.replace('s_phases = ["Built", "Promoted"]', 's_phases = ["Built"]')),
             "PHASE: TerminatorKind::Yield: its rows cover S phases ['Built'], but it is admitted in ['Built', 'Promoted']"),
            ("semantic obligation", edit_block(self.table, "construct", 'mir = "TerminatorKind::Yield"', lambda b: b.replace('phase_semantics = ["ps-coroutine-bodies"]\n', '')),
             "PHASE: construct TerminatorKind::Yield ['Built', 'Promoted']: the semantic rule ps-coroutine-bodies applies to it"),
        ]
        for label, table, fragment in cases:
            with self.subTest(label):
                self.assert_violation(self.run_inputs(table), fragment)
        new_word = replace_once(head(MIR_MOD), "    /// A span representing this MIR, for error reporting.\n", "    /// A span representing this MIR, for error reporting in runtime MIR.\n")
        self.assert_violation(self.run_inputs(trees={"worktree": Overlay({MIR_MOD: new_word})}),
                              "PHASE: compiler/rustc_middle/src/mir/mod.rs:270-270 is a doc unit of Body matching phase_words", "PHASE: exactly one [[doc_pin]]")

    # ---- dispositions and retags
    def test_dispositions_retags_and_refusals(self):
        cases = [
            ("vocabulary name", edit_block(self.table, "construct", 'mir = "BasicBlockData.is_cleanup"', lambda b: b.replace('"BbKind.Cleanup"', '"BbKind.Cleanupp"')),
             "DISPOSITION: construct BasicBlockData.is_cleanup Built,Promoted,Runtime: 'BbKind.Cleanupp' is not a Core vocabulary entry"),
            ("vocabulary operator", edit_block(self.table, "construct", 'mir = "BinOp::Sub"', lambda b: re.sub(r'core = \[[^\]]*\]', 'core = ["Rvalue.BinOp"]', b, count=1)),
             "DISPOSITION: construct BinOp::Sub Built,Promoted,Runtime: core and case_refusals must be the vocabulary's maps_to"),
            ("undeclared refusal", edit_block(self.table, "construct", 'mir = "Body.tainted_by_errors"', lambda b: b.replace('refusal = "ErroneousBody"', 'refusal = "Erroneous"'), containing="refusal ="),
             "DISPOSITION: construct Body.tainted_by_errors Built,Promoted,Runtime the field is Some: rustc reported an error for the body: refusal 'Erroneous' is not a declared [[refusal]]"),
            ("dispatch_via", edit_block(self.table, "construct", 'mir = "BasicBlockData.statements"', lambda b: re.sub(r'dispatch_via = \[\n(?:  .*\n)*\]\n', '', b)),
             "DISPOSITION: construct BasicBlockData.statements Built,Promoted,Runtime: dispatch_via cites the conversion into StatementKind"),
            ("retag names", edit_block(self.table, "construct", 'mir = "StatementKind::Assign"', lambda b: b.replace('core = ["Stmt.Assign", "Stmt.Validate"]', 'core = ["Stmt.Assign"]'), containing='s_phases = ["Runtime"]\ncase = "otherwise"'),
             None),
            ("retag forbids", edit_block(self.table, "construct", 'mir = "Rvalue::Ref"', lambda b: b.replace('core = ["Rvalue.AddrOf"]', 'core = ["Rvalue.AddrOf", "Stmt.Validate"]'), containing='s_phases = ["Runtime"]'),
             "RETAG: retag_site interp-ref-two-phase: no core row of Rvalue::Ref names ['Rvalue.AddrOf'], or one names a name it forbids ['Stmt.Validate']"),
        ]
        for label, table, fragment in cases:
            with self.subTest(label):
                violations = self.run_inputs(table)
                if fragment is None:  # one core row of Assign still names Stmt.Validate: a judgment change, not a retag violation
                    self.assertEqual(self.mechanical(violations), [])
                else:
                    self.assert_violation(violations, fragment)
        both = edit_block(self.table, "construct", 'mir = "StatementKind::Assign"', lambda b: b.replace('core = ["Stmt.Assign", "Stmt.Validate"]', 'core = ["Stmt.Assign"]'), containing='s_phases = ["Runtime"]\ncase = "otherwise"')
        both = edit_block(both, "construct", 'mir = "StatementKind::Assign"', lambda b: b.replace('core = ["Stmt.Assign", "Stmt.Validate"]', 'core = ["Stmt.Assign"]'), containing='s_phases = ["Built", "Promoted"]\ncase = "otherwise"')
        self.assert_violation(self.run_inputs(both), "RETAG: retag_site codegen-assign-place: no core row of StatementKind::Assign names ['Stmt.Validate']")
        unused = self.table.replace("[[refusal]]\nname = \"AsyncDrop\"", '[[refusal]]\nname = "Unused"\nreason = "x"\nevidence = [\n  { ref = "design:1175", quote = "A construct not yet specified" },\n]\n\n[[refusal]]\nname = "AsyncDrop"', 1)
        self.assert_violation(self.run_inputs(unused), "TABLE: refusal Unused: an UpperCamel name some row uses (else stale)")

    # ---- minimize and intrinsics
    def test_minimize_search_and_intrinsics(self):
        cases = [
            ("uncited hit", edit_block(self.table, "construct", 'mir = "TerminatorKind::Yield"', lambda b: b.replace('minimize = [\n  { ref = "minirust:tooling/minimize/src/bb.rs:269", arm = "| rs::TerminatorKind::Yield { .. }" },\n]\narm_class = "refuses"', 'minimize = "no arm"')),
             "MINIMIZE: construct TerminatorKind::Yield Built,Promoted: says no arm, but minimize names it at [('tooling/minimize/src/bb.rs', 269)]"),
            ("stale arm not stale", replace_once(self.table, 'token = "rs::StatementKind::Retag"', 'token = "rs::StatementKind::Assign"'),
             "MINIMIZE: stale_arm minirust:tooling/minimize/src/bb.rs:104 rs::StatementKind::Assign: 'rs::StatementKind::Assign' is no hit"),
            ("class without divergence", edit_block(self.table, "construct", 'mir = "Rvalue::Use"', lambda b: b.replace('arm_class = "translates"', 'arm_class = "refuses"')),
             "MINIMIZE: construct Rvalue::Use Built,Promoted,Runtime: its minimize arms refuses and it is core, so it states `divergence`"),
            ("arm text", replace_once(self.table, 'arm = "| rs::TerminatorKind::Yield { .. }"', 'arm = "| rs::TerminatorKind::Yield { value, .. }"'),
             "CITATION: construct TerminatorKind::Yield Built,Promoted minimize: minirust:tooling/minimize/src/bb.rs:269 does not contain"),
            ("intrinsic row deleted", edit_block(self.table, "intrinsic", 'path = "core::intrinsics::abort_immediate"', lambda b: ""),
             "INTRINSIC: #[rustc_intrinsic] core::intrinsics::abort_immediate (library/core/src/intrinsics/mod.rs:"),
            ("fallback", edit_block(self.table, "intrinsic", 'path = "core::intrinsics::abort_immediate"', lambda b: re.sub(r'disposition = "[a-z_]+"\n(?:refusal|core) = [^\n]*\n', 'disposition = "fallback"\n', b)),
             "INTRINSIC: intrinsic core::intrinsics::abort_immediate: fallback requires a body marked"),
        ]
        for label, table, fragment in cases:
            with self.subTest(label):
                self.assert_violation(self.run_inputs(table), fragment)
        intrinsics = "library/core/src/intrinsics/mod.rs"
        added = head(intrinsics) + "\n#[rustc_intrinsic]\npub fn trust_probe();\n"
        self.assert_violation(self.run_inputs(trees={"worktree": Overlay({intrinsics: added})}), "INTRINSIC: #[rustc_intrinsic] core::intrinsics::trust_probe")

    def test_integration_producer_paths_and_smir_enums_are_checked(self):
        # The verification of 1d935fac03: a [[producer]] path naming no file, and a [scope] smir_enums element naming no
        # enum, each passed once a review record reviewed them.
        built = 'exclude = ["compiler/rustc_mir_build/src/builder/custom"]\nevidence = [\n  { ref = "design:1679"'
        for label, table, jid, fragment in (
            ("producer path", replace_once(self.table, '  "compiler/rustc_mir_transform/src/coroutine/by_move_body.rs",\n]\n' + built,
                                           '  "compiler/rustc_mir_transform/src/coroutine/by_move_body_renamed.rs",\n]\n' + built),
             "producer:Built", "PHASE: producer Built: 'compiler/rustc_mir_transform/src/coroutine/by_move_body_renamed.rs' is no file or directory at HEAD"),
            ("producer exclude", replace_once(self.table, built, built.replace("builder/custom", "builder/customs")),
             "producer:Built", "PHASE: producer Built: 'compiler/rustc_mir_build/src/builder/customs' is no file or directory at HEAD"),
            ("smir enum", replace_once(self.table, '  "RuntimeChecks",\n  "Rvalue",\n]', '  "RuntimeChecks",\n  "Rvalu",\n]'),
             "scope:smir_enums", "SCOPE: [scope] smir_enums 'Rvalu': minimize writes no `smir::Rvalu::Variant` at the pin (stale or misspelled)"),
        ):
            with self.subTest(label):
                self.assert_violation(self.run_inputs(table, registry=self.review([jid], table)), fragment)

    def test_deferred_checks_and_divergences(self):
        cases = [
            ("exit", edit_block(self.table, "deferred_check", 'id = "producers"', lambda b: b.replace('checked_by = ["E2.3.1"]', 'checked_by = ["E2.3.1", "E1.2.3"]')),
             "DEFERRED: deferred_check producers: checked_by 'E1.2.3' is an exit id quoted"),
            ("field", edit_block(self.table, "deferred_check", 'id = "producers"', lambda b: b.replace('"producer.exclude"', '"producer.excluded"')),
             "DEFERRED: deferred_check producers: 'producer.excluded' is not a <row kind>.<field>"),
            ("divergence", edit_block(self.table, "intrinsic", 'path = "core::intrinsics::atomic_xsub"', lambda b: b.replace('spec_divergence = ["sd-atomic-fetch-wraps"]\n', ''), containing="spec_divergence"),
             "DIVERGENCE: spec_divergence sd-atomic-fetch-wraps: cites MiniRust's spec/ and rustc or the library, and applies_to"),
        ]
        for label, table, fragment in cases:
            with self.subTest(label):
                self.assert_violation(self.run_inputs(table), fragment)

    # ---- the content defects of round 4, as judgments
    def test_round4_content_fixes_change_only_by_review(self):
        fake = edit_block(self.table, "construct", 'mir = "Rvalue::Ref"', lambda b: b.replace('disposition = "no_op"', 'disposition = "core"\ncore = ["Rvalue.AddrOf"]').replace(
            re.search(r'no_op = \{[^\n]*\}\n', b).group(0), ""), containing='case = "the borrow kind is BorrowKind::Fake"')
        self.assert_judgment_change(fake, jids=["construct:Rvalue::Ref Built,Promoted the borrow kind is BorrowKind::Fake"])
        scalar = edit_block(self.table, "construct", 'mir = "Scalar::Int"', lambda b: replace_once(b, '  "Rvalue.Tuple",\n', ''))
        self.assert_judgment_change(scalar, jids=["construct:Scalar::Int Built,Promoted,Runtime"])
        spread = edit_block(self.table, "construct", 'mir = "Body.spread_arg"', lambda b: re.sub(r'disposition = "core"\ncore = \[[^\]]*\]\n', 'disposition = "no_op"\nno_op = { ref = "rustc:compiler/rustc_middle/src/mir/mod.rs:264", quote = "/// This is used for the \\"rust-call\\" ABI." }\n', b))
        self.assert_judgment_change(spread, jids=["construct:Body.spread_arg Built,Promoted,Runtime"])
        conflict = edit_block(self.table, "retag_site", 'id = "miri-ambient"', lambda b: b.replace('realized_by = ["StatementKind::Assign", "TerminatorKind::Call"]', 'realized_by = ["StatementKind::Assign"]'))
        self.assert_judgment_change(conflict, jids=["retag_site:miri-ambient"])
        follows = edit_block(self.table, "phase_conflict", 'id = "pc-ptr-metadata"', lambda b: b.replace('follows = "evidence"', 'follows = "validator"'))
        self.assert_judgment_change(follows, jids=["phase_conflict:pc-ptr-metadata"])
        # widening a declared search scope is a judgment whose hit set the checker re-runs
        wider = replace_once(self.table, '  "Rvalue",\n]\nphase_words', '  "Rvalue",\n  "Mutability",\n]\nphase_words')
        self.assert_violation(self.run_inputs(wider), "MINIMIZE: tooling/minimize/src/ty.rs:335 names ['smir::Mutability::Mut'] in minimize, and no row", "REVIEW: judgment scope:smir_enums: its content changed")

    # ---- the document
    def test_document_mutations(self):
        cases = [
            ("counts", self.doc.replace("| **Total** | 211 |", "| **Total** | 212 |"), "DOC: the published `mir-constructor-table-counts` block differs"),
            ("unchecked citation", replace_once(self.doc, "The invariant is\n", "The invariant is (see design:1812)\n"), "line citation 'design:1812' is not in the checked"),
            ("quote drift", replace_once(self.doc, "design:3934 «**E0.6** Zero unmapped MIR enum variants; the count is published.»", "design:3934 «**E0.6** Zero unmapped MIR enum variants.»"),
             "DOC: prose:what-this-is: design:3934 does not contain"),
            ("unreviewed prose", replace_once(self.doc, "## Owner questions\n", "## Owner questions\n\nAll resolved.\n"), "DOC: line"),
            ("pin", self.doc.replace("`d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed`", "`d821c6e3`"), "DOC: the document does not record the pin `d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed`"),
        ]
        for label, doc, fragment in cases:
            with self.subTest(label):
                self.assert_violation(self.run_inputs(doc=doc), fragment)
        prose = replace_once(self.doc, "  should it? Scalar-typed ADT constants", "  should it? Scalar-typed ADT constants, already decided,")
        self.assert_judgment_change(doc=prose, jids=["prose:mq-3"])
        comment = replace_once(self.table, 'schema = "trust.core.mir-constructor-table.v1"', '# OWNER DECISION: MQ-3 is closed.\nschema = "trust.core.mir-constructor-table.v1"')
        self.assert_judgment_change(comment, jids=["comments:table"])


if __name__ == "__main__":
    unittest.main(verbosity=1)
