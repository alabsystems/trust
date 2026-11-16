#!/usr/bin/env python3
"""Controls for scripts/trust_core/language_decisions.py (D0.1, the LD ledger and I-PRECEDENCE).

* The REAL checker on the REAL inputs (the pinned MiniRust, Reference, FLS, a-mir-formality and
  rust-lang/rfcs clones, this repository's design, library and tests at HEAD, the table, the
  document, the snapshots and the review registry) exits 0 and publishes the counts asserted here.
* Every mutation of a temporary copy of an input makes the CHECKER report the violation it
  introduces, beside an unmutated control on the same layout. A mechanical mutation must name
  its predicate; a judgment mutation (a role, a reason, a scope, a prose section) must pass every
  mechanical predicate and fail REVIEW, and pass once a new review record reviews it, which is
  what makes a judgment change visible.
* The three defects of the round-4 verification each have a control: a ranked source outside its
  kind's declared search scope, a Reference admonition ranked without a rule, and the reading of
  the recursive-async team decision, whose label consequence is computed. So do the two gaps the
  round-18 verification of the port found: an [[rfc]] record no source names, and a Reference
  source inside an untagged admonition indented under a rule.

The shared layers (pins, the full-clone pin, citations with markers, blocks, reviews, immutable
snapshots) are tested in scripts/tests/trust_core_common_test.py. A missing source clone is a
FAILURE that prints the clone command, never a skip.

Author: Andrew Yates <andrewyates.name@gmail.com>
Copyright 2026 Andrew Yates | License: Apache-2.0 OR MIT
"""

import importlib.util
import json
import re
import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "scripts" / "trust_core" / "language_decisions.py"
SPEC = importlib.util.spec_from_file_location("trust_core_language_decisions", SCRIPT)
LD = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(LD)
C = LD.C
TABLE, DOC, REGISTRY = ROOT / LD.TABLE_REL, ROOT / LD.DOC_REL, ROOT / LD.REGISTRY_REL
TREES: dict = {}


class ImportBoundaries(unittest.TestCase):
    def test_only_complete_top_level_imports_are_compared(self):
        imports = '#[path = "other.rs"]\nmod other;\npub use other::{One, Two};\n'
        decoys = 'const S: &str = "mod fake;";\nfn f() { mod nested {} }\n'
        original = imports + decoys
        current = '// Trust: a different crate header\n' + original
        self.assertEqual(LD.identical_import_region(current, original, 2, 2), (2, 3))
        self.assertEqual(LD.identical_import_region(current, original, 4, 4), (4, 4))
        self.assertIsNone(LD.identical_import_region(current, original, 5, 5))
        self.assertIsNone(LD.identical_import_region(current, original, 6, 6))

    def test_changed_attributes_body_and_ambiguous_upstream_imports_refuse(self):
        original = '#[cfg(feature = "one")]\npub mod m { pub use inner::One; }\n'
        for current in [original.replace('"one"', '"two"'),
                        original.replace('inner::One', 'inner::Two')]:
            self.assertIsNone(LD.identical_import_region(current, original, 2, 2))
        self.assertIsNone(LD.identical_import_region(original, original * 2, 2, 2))
        self.assertIsNone(LD.identical_import_region(original, '', 2, 2))

    def test_file_guard_opens_only_for_the_verified_import(self):
        class Tree:
            def __init__(self, text):
                self.value = text

            def text(self, _):
                return self.value

            def lines(self, _):
                return self.value.split('\n')

        rel = 'library/core/src/lib.rs'
        original = '#[path = "other.rs"]\nmod other;\n'
        current = '// Trust: modified crate header\n' + original
        checker = LD.Checker(LD.Options())
        checker.trees = {'worktree': Tree(current), 'upstream': Tree(original)}
        checker.resolver = C.Resolver(ROOT, checker.trees)
        ref = 'rustc:' + rel + ':2'
        self.assertIsInstance(checker.resolver.check(ref, '#[path'), C.PinProblem)
        checker.verify_corpus_import(ref)
        self.assertIsNone(checker.resolver.check(ref, '#[path'))
        self.assertIsInstance(checker.resolver.check('rustc:' + rel + ':1', 'Trust:'), C.PinProblem)
        self.assertEqual(checker.f.violations, [])

# The published counts (LANGUAGE_DECISIONS.md, block ld-counts). A change here is a change to the ledger.
PUBLISHED = {'entries': 13, 'entries_by_status': {'Required': 7, 'Recorded': 6}, 'entries_by_label': {'normative': 6, 'team-decision': 2, 'team-model': 0, 'de-facto': 0, 'de-facto-open': 1, 'trust-choice': 4, 'compat': 0}, 'aspects': 29, 'aspects_by_label': {'normative': 19, 'team-decision': 4, 'team-model': 1, 'de-facto': 0, 'de-facto-open': 1, 'trust-choice': 4, 'compat': 0}, 'aspects_by_resolution': {'settled': 14, 'choose': 3, 'filled': 8, 'unaddressed': 4}, 'de_facto_entries': 1, 'de_facto_aspects': 1, 'compat_candidates': 2, 'sources': 159, 'sources_by_rank': {1: 108, 2: 37, 3: 14}, 'sources_by_kind': {'fls': 15, 'minirust': 20, 'reference': 28, 'rfc': 32, 'rustc-test': 14, 'std-doc': 33, 'team-decision': 17}, 'readings_by_role': {'settles': 67, 'open': 28, 'contrary': 8, 'context': 69, 'pins': 11}, 'related': 20, 'team_decisions': 14, 'rfcs': 8, 'rfcs_by_stabilization': {'accepted-feature': 3, 'checked-step': 1, 'no-feature-gate': 3, 'stable-item': 1}, 'issue_snapshots': 19, 'index_records': 884, 'index_by_fcp': {'before-pin': 830, 'after-pin': 0, 'no-notice': 54}, 'opsem_dispositioned': 41, 'records_dispositioned': 168, 'records_dispositioned_by_fcp': {'before-pin': 162, 'after-pin': 0, 'no-notice': 6}, 'search_searches': 91, 'search_hits': 488, 'search_cited': 50, 'search_uncited': 438, 'search_lines': 1766, 'search_lines_cited': 66, 'search_lines_reason': 1700, 'corpora': 7, 'conflicts': ['LD-10.S8', 'LD-13.S2', 'LD-2.S3', 'LD-3.S12', 'LD-3.S4', 'LD-4.S6'], 'divergences': [], 'od5_items': 8, 'rulings_pending': 0, 'owner_questions': 10, 'deferred_checks': 2, 'doc_citations': 17, 'citations': 324}
PUBLISHED_JUDGMENTS = 1054


def setUpModule():
    pins = C.load_pins()
    try:
        clones = C.locate_clones(pins, list(LD.READS))
    except C.MissingClone as error:
        raise AssertionError(str(error)) from None
    TREES.update({"worktree": C.GitTree(ROOT, "HEAD"), **{LD.READS[n]: C.GitTree(p, pins.sources[n].revision) for n, p in clones.items()}})


class Overlay:
    """A tree with some files replaced; it shares its base's search-scope cache, so it changes what a
    citation reads, not a search's hit set."""

    def __init__(self, base, files: dict) -> None:
        self.base, self.over = base, files
        self._ld_scopes = base.__dict__.setdefault("_ld_scopes", {})

    def files(self, prefix="", suffixes=()):
        return self.base.files(prefix, suffixes)

    def prefetch(self, rels):
        self.base.prefetch([r for r in rels if r not in self.over])

    def text(self, rel):
        return self.over[rel] if rel in self.over else self.base.text(rel)

    def lines(self, rel):
        text = self.text(rel)
        return None if text is None else text.split("\n")


def replace_once(text, old, new):
    assert text.count(old) == 1, (old[:80], text.count(old))
    return text.replace(old, new)


def block(text, header, line):
    """The `[[header]]` block of the table holding the exact line `line`."""
    for part in re.split(r"\n(?=\[)", text):
        if part.startswith(f"[[{header}]]") and f"\n{line}\n" in part + "\n":
            return part
    raise AssertionError((header, line))


def edit_block(text, header, line, edit):
    old = block(text, header, line)
    return replace_once(text, old, edit(old))


class RealInputs(unittest.TestCase):
    def test_real_inputs_pass_and_publish_the_counts(self):
        result = LD.collect()  # every clone located and verified at its pin
        self.assertEqual(result.violations, [])
        for key, value in PUBLISHED.items():
            self.assertEqual(result.counts[key], value, key)
        self.assertEqual(result.counts["reviews"]["judgments"], PUBLISHED_JUDGMENTS)
        self.assertIn("de-facto (V11, de-facto + de-facto-open): entries 1, aspects 1", result.blocks["ld-counts"])

    def test_cli_exits_zero_and_the_e08_pass_line_fails_while_conflicts_remain(self):
        run = subprocess.run([sys.executable, str(SCRIPT)], capture_output=True, text=True)
        self.assertEqual(run.returncode, 0, run.stderr)
        self.assertIn(f"language_decisions: OK ({PUBLISHED['citations']} citations, {PUBLISHED['doc_citations']} document citations, "
                      f"{PUBLISHED_JUDGMENTS} reviewed judgments)", run.stdout)
        ruled = LD.collect(LD.Options(trees=TREES, require_ruled=True, check_pin_state=False))
        # Every OD-5 item is ruled (2026-10-02); the six computed precedence conflicts remain.
        self.assertEqual(sorted(v.split(":")[0] for v in ruled.violations), ["CONFLICT-UNRULED"])

    def test_a_missing_clone_exits_two_with_its_clone_command(self):
        with tempfile.TemporaryDirectory() as tmp:
            run = subprocess.run([sys.executable, str(SCRIPT), "--rfcs", str(Path(tmp) / "absent")], capture_output=True, text=True)
            self.assertEqual(run.returncode, 2)
            self.assertIn(f"git clone https://github.com/rust-lang/rfcs {Path(tmp) / 'absent'}", run.stderr)


class Mutations(unittest.TestCase):
    def setUp(self):
        self._tmp = tempfile.TemporaryDirectory()
        self.tmp = Path(self._tmp.name)
        self.table, self.doc, self.registry = (p.read_text(encoding="utf-8") for p in (TABLE, DOC, REGISTRY))

    def tearDown(self):
        self._tmp.cleanup()

    def run_inputs(self, table=None, doc=None, registry=None, trees=None, **options):
        paths = {}
        for name, text in (("table.toml", table or self.table), ("doc.md", doc or self.doc), ("registry.toml", registry or self.registry)):
            paths[name] = self.tmp / name
            paths[name].write_text(text, encoding="utf-8")
        return LD.collect(LD.Options(table=paths["table.toml"], doc=paths["doc.md"], registry=paths["registry.toml"],
                                     trees={**TREES, **(trees or {})}, check_pin_state=False, check_history=False, **options))

    def assert_violation(self, violations, *fragments):
        for fragment in fragments:
            self.assertTrue(any(fragment in v for v in violations), f"{fragment!r} not in {violations}")

    def fresh_source_id(self, entry):
        """A mutation's invented row must not shadow newly added real evidence."""
        numbers = [int(n) for n in re.findall(rf'id = "{re.escape(entry)}\.S(\d+)"', self.table)]
        return f"{entry}.S{max(numbers, default=0) + 1}"

    @staticmethod
    def mechanical(violations):
        return [v for v in violations if not v.startswith("REVIEW:") and not v.startswith("DOC: the published `ld-")]

    def review(self, jids, table=None, doc=None, record="mutation-review"):
        """The registry with a new record's review of each judgment's current content appended."""
        f = C.Findings()
        now = LD.judgments(f, table or self.table, C.document_judgments(f, "DOC", doc or self.doc, generated=LD.BLOCKS))
        text = self.registry.replace("[judgment]", f'[record.{record}]\nround = "test"\ndate = "2026-09-17"\nevidence = ["the mutation"]\nreason = "a mutation test"\n\n[judgment]')
        for jid in jids:
            line = next((l for l in text.split("\n") if l.startswith(f"{json.dumps(jid)} = ")), None)
            digest = C.digest(jid, now[jid])
            if line is None:
                text = text.rstrip("\n") + f'\n{json.dumps(jid)} = {{ digest = "{digest}", reviews = [["{record}", "{digest}"]] }}\n'
            else:
                old = line.split('digest = "')[1].split('"')[0]
                text = text.replace(line, line.replace(f'digest = "{old}"', f'digest = "{digest}"')[:-4] + f'], ["{record}", "{digest}"]] }}')
        return text

    def test_control_copies_pass(self):
        self.assertEqual(self.run_inputs().violations, [])

    # ---- the three defects of the round-4 verification
    def test_d1_a_ranked_source_outside_its_kinds_declared_scope_is_refused(self):
        three = '  { path = "library/std/src/", suffix = ".rs" },\n'
        table = edit_block(self.table, "corpus", 'name = "std-doc"', lambda b: re.sub(r'  \{ path = "library/(stdarch|portable-simd|backtrace|std_detect)[^\n]*\n', "", b))
        self.assertIn(three, block(table, "corpus", 'name = "std-doc"'))
        violations = self.run_inputs(table, registry=self.review(["corpus:std-doc"], table)).violations
        for sid in ("LD-12.S1", "LD-12.S2", "LD-4.S12"):
            self.assert_violation(violations, f"CORPUS: source {sid}: library/stdarch/crates/core_arch/src/x86/sse.rs lies outside every declared search scope of kind std-doc")
        self.assert_violation(violations, "SEARCH: search LD-12.Q4 (std-doc): library/stdarch/crates/core_arch/src/x86/sse.rs is recorded but not matched")
        # A ranked std-doc source in a library tree no scope declares, whatever its quote.
        table = edit_block(self.table, "entry.related", 'id = "LD-12.R1"', lambda b: b.replace("[[entry.related]]", "[[entry.source]]").replace(
            'kind = "library-source"', 'aspects = ["changed-environment-ub"]\nrole = "context"\nkind = "std-doc"\nrank = 1').replace('id = "LD-12.R1"', 'id = "LD-12.S17"').replace("why_unranked = ", "note = "))
        self.assert_violation(self.run_inputs(table).violations, "CORPUS: source LD-12.S17: library/compiler-builtins/libm/src/math/support/env.rs lies outside every declared search scope")

    def test_d2_reading_the_recursive_async_decision_as_settling_is_visible_and_recounts_v11(self):
        table = edit_block(self.table, "entry.source", 'id = "LD-9.S13"', lambda b: b.replace('role = "context"', 'role = "settles"'))
        self.assert_violation(self.run_inputs(table).violations,
                              "PRECEDENCE: aspect LD-9/in-object: is labelled 'de-facto-open'; the precedence predicates compute 'team-decision'")
        table = edit_block(table, "entry.aspect", 'id = "in-object"', lambda b: b.replace('label = "de-facto-open"', 'label = "team-decision"'))
        table = replace_once(table, 'label = "de-facto-open"\nquestion = "Where does a coroutine', 'label = "team-decision"\nquestion = "Where does a coroutine')
        changed = ["source:LD-9.S13", "aspect:LD-9/in-object", "entry:LD-9"]
        result = self.run_inputs(table)
        self.assertEqual(self.mechanical(result.violations), [])
        self.assertEqual(sorted(v.split(": its content")[0] for v in result.violations if v.startswith("REVIEW:")), sorted(f"REVIEW: judgment {j}" for j in changed))
        result = self.run_inputs(table, registry=self.review(changed, table))
        self.assertEqual(self.mechanical(result.violations), [])
        self.assertEqual((result.counts["de_facto_entries"], result.counts["de_facto_aspects"]), (0, 0))

    def test_d2_a_team_decision_record_dismissed_without_citation_or_reason_is_refused(self):
        table = edit_block(self.table, "entry.search.hit", 'at = "rust-lang/rust#117703"', lambda b: b.replace('use = ["LD-9.S13"]', "use = []"))
        self.assert_violation(self.run_inputs(table).violations, "SEARCH: hit LD-9.Q7/rust-lang/rust#117703 is not cited and gives no reason")

    def test_d3_a_reference_source_is_a_rule_by_rule_id(self):
        sid = self.fresh_source_id("LD-3")
        admonition = edit_block(self.table, "entry.related", 'id = "LD-3.R3"', lambda b: b.replace("[[entry.related]]", "[[entry.source]]").replace(
            'id = "LD-3.R3"\nkind = "reference"', f'id = "{sid}"\naspects = ["per-access"]\nrole = "open"\nkind = "reference"\nrank = 1').replace("why_unranked = ", "note = "))
        self.assert_violation(self.run_inputs(admonition).violations, f"RULE-ID: source {sid}: a Reference source is a rule, by rule id; lines 698-699 are not inside the text of r[None]")
        tagged = admonition.replace('rank = 1\nref = "reference:src/expressions/operator-expr.md:698-699"', 'rank = 1\nref = "reference:src/expressions/operator-expr.md:698-699"\nrule = "expr.as.int-as-pointer"')
        self.assert_violation(self.run_inputs(tagged).violations, f"RULE-ID: source {sid}: a Reference source is a rule, by rule id; lines 698-699 are not inside the text of r[expr.as.int-as-pointer] (lines 693-696, 701-715)")
        note = edit_block(self.table, "entry.related", 'id = "LD-9.R3"', lambda b: b.replace('kind = "reference"\n', 'kind = "reference"\n').replace("\nquote = ", '\nrule = "expr.block.async.layout-unspecified"\nquote = ', 1))
        self.assert_violation(self.run_inputs(note).violations, "RULE-ID: related LD-9.R3: lines 179-179 are not inside the text of r[expr.block.async.layout-unspecified]")

    def test_r18_an_indented_admonition_is_not_rule_text_and_the_text_resumes_after_an_admonition(self):
        sid = self.fresh_source_id("LD-2")
        indented = replace_once(self.table, '\n[[entry.source]]\nid = "LD-2.S18"', f'\n[[entry.source]]\nid = "{sid}"\naspects = ["wide-metadata"]\nrole = "context"\n'
                                'kind = "reference"\nrank = 1\nref = "reference:src/behavior-considered-undefined.md:158"\nrule = "undefined.validity.wide"\n'
                                'quote = "This bound is on the size of the entire pointed-to value, not just its unsized tail"\n\n[[entry.source]]\nid = "LD-2.S18"')
        self.assert_violation(self.run_inputs(indented).violations, f"RULE-ID: source {sid}: a Reference source is a rule, by rule id; lines 158-158 are not "
                                                                    "inside the text of r[undefined.validity.wide] (lines 151-156, 159-159)")
        # Control: the same row at the rule's own line 155 is rule text.
        control = indented.replace('ref = "reference:src/behavior-considered-undefined.md:158"', 'ref = "reference:src/behavior-considered-undefined.md:155"').replace(
            'quote = "This bound is on the size of the entire pointed-to value, not just its unsized tail"', 'quote = "the metadata is invalid if it makes the total size of the pointed-to value"')
        self.assertFalse([v for v in self.run_inputs(control).violations if v.startswith("RULE-ID")])
        # Rule text after an unindented note, with no marker of its own, is the rule's.
        table = edit_block(self.table, "entry.related", 'id = "LD-9.R3"', lambda b: b + '\n[[entry.related]]\nid = "LD-9.R4"\nkind = "reference"\n'
                           'ref = "reference:src/macros-by-example.md:435"\nrule = "macro.decl.scope.macro_use.prelude"\n'
                           'quote = "When using the [MetaWord] syntax, all exported macros are imported."\nwhy_unranked = "A control row."\n')
        self.assertEqual(self.mechanical(self.run_inputs(table).violations), [])
        note = table.replace('ref = "reference:src/macros-by-example.md:435"', 'ref = "reference:src/macros-by-example.md:431"').replace(
            'quote = "When using the [MetaWord] syntax, all exported macros are imported."', 'quote = "`rustc` currently prefers the last macro imported in case of conflict."')
        self.assert_violation(self.run_inputs(note).violations, "RULE-ID: related LD-9.R4: lines 431-431 are not inside the text of r[macro.decl.scope.macro_use.prelude]")

    def test_integration_a_legacy_blockquote_admonition_is_not_rule_text(self):
        # The verification of a89b89f85e: the Reference's one legacy `> **Example**:` blockquote (types/closure.md:673,
        # inside r[type.closure.async.traits.fn-family]) was accepted as rank-1 rule text, since only `> [!...]` began an
        # admonition. Any blockquote is one now; the rule's text before it is still its text.
        sid = self.fresh_source_id("LD-2")
        source = (f'\n[[entry.source]]\nid = "{sid}"\naspects = ["wide-metadata"]\nrole = "context"\n'
                  'kind = "reference"\nrank = 1\nref = "reference:src/types/closure.md:672"\nrule = "type.closure.async.traits.fn-family"\n'
                  'quote = "The first clause for a mutable capture can be illustrated with the following:"\n\n[[entry.source]]\nid = "LD-2.S18"')
        legacy = replace_once(self.table, '\n[[entry.source]]\nid = "LD-2.S18"', source)
        self.assert_violation(self.run_inputs(legacy).violations, f"RULE-ID: source {sid}: a Reference source is a rule, by rule id; lines 672-672 are not "
                                                                  "inside the text of r[type.closure.async.traits.fn-family] (lines 663-671")
        for line, quote in ((670, "If the async closure is lending to its `Future`, then [`FnMut`] and [`Fn`] are *not* implemented."),
                            (663, "Async closures have a further restriction of whether or not they implement [`FnMut`] or [`Fn`].")):
            with self.subTest(control=line):  # the rule's own lines before the blockquote
                control = legacy.replace('ref = "reference:src/types/closure.md:672"', f'ref = "reference:src/types/closure.md:{line}"').replace(
                    'quote = "The first clause for a mutable capture can be illustrated with the following:"', f"quote = {json.dumps(quote)}")
                self.assertFalse([v for v in self.run_inputs(control).violations if v.startswith("RULE-ID")])

    def test_r18_a_stale_rfc_record_and_an_unpaired_notices_snapshot_are_refused(self):
        orphan = ('[[rfc]]\nnumber = 2045\nfile = "text/2045-target-feature.md"\n'
                  'pr = { ref = "rfcs:text/2045-target-feature.md:3", quote = "RFC PR: [rust-lang/rfcs#2045](https://github.com/rust-lang/rfcs/pull/2045)" }\n'
                  'tracking_issue = "rust-lang/rust#44839"\n'
                  'tracking = { ref = "rfcs:text/2045-target-feature.md:4", quote = "[rust-lang/rust#44839](https://github.com/rust-lang/rust/issues/44839)" }\n'
                  'stabilization = "accepted-feature"\n'
                  'evidence = { ref = "rustc:compiler/rustc_feature/src/accepted.rs:48", quote = "(accepted, aarch64_target_feature, \\"1.61.0\\", Some(44839))," }\n\n')
        table = replace_once(self.table, "[[rfc]]\nnumber = 320\n", orphan + "[[rfc]]\nnumber = 320\n")
        result = self.run_inputs(table)
        self.assertEqual(self.mechanical(result.violations), ["RFC: rfc 2045: no ranked rfc source names it (stale); an [[rfc]] record is an RFC the ledger cites"])
        # Reviewing the stale record does not make it pass.
        self.assert_violation(self.run_inputs(table, registry=self.review(["rfc:2045"], table)).violations, "RFC: rfc 2045: no ranked rfc source names it (stale)")
        # A second snapshot of rfcbot's notices naming the one index.
        root = self.tmp / "root"
        shutil.copytree(ROOT / LD.SNAPSHOT_PREFIX, root / LD.SNAPSHOT_PREFIX)
        shutil.copy(root / LD.SNAPSHOT_PREFIX / "decisions-fcp.json", root / LD.SNAPSHOT_PREFIX / "decisions-fcp-2.json")
        row = block(self.table, "snapshot", 'file = "docs/trust-core/snapshots/decisions-fcp.json"')
        table = self.table.replace(row, row + "\n" + row.replace("decisions-fcp.json", "decisions-fcp-2.json"), 1)
        self.assert_violation(self.run_inputs(table, snapshot_root=root).violations,
                              "DECISION-FCP: snapshot docs/trust-core/snapshots/decisions-index.json: 2 snapshots of rfcbot's completion notices name this index; exactly one does")

    def test_integration_every_line_of_a_scope_is_searched_on_its_own(self):
        # The verification of a89b89f85e: a whole-file shortcut skipped a file whose joined lines a pattern did not
        # match, although one of its lines did; with `\z`, or an anchor after an escaped `\[`, a reviewed pattern
        # missed the "without running drop glue" line and passed. The re-run is a plain per-line search.
        self.assertFalse(hasattr(LD, "joinable"))
        pin = "library/core/src/intrinsics/mod.rs"
        self.assertTrue(TREES["worktree"].lines(pin)[804].endswith("without running drop glue."))
        old = 'pattern = "(?i)drop flag|drop obligation|dynamic drop|partially (moved|initiali[sz]ed)|move path"'
        # Use \Z, the strict end anchor also supported by Python 3.11-3.13.
        # Each tail is TOML text: the regex `\.$`, `\.\Z`, `\.(?:\[|$)(?:x]|)`, `\.(?=$)`, `\.(?!.)`.
        for tail in (r"\\.$", r"\\.\\Z", r"\\.(?:\\[|$)(?:x]|)", r"\\.(?=$)", r"\\.(?!.)"):
            with self.subTest(tail=tail):
                table = edit_block(self.table, "entry.search", 'id = "LD-8.Q4"', lambda b: replace_once(b, old, old[:-1] + "|without running drop glue" + tail + '"'))
                violations = self.run_inputs(table, registry=self.review(["search:LD-8.Q4"], table)).violations
                self.assert_violation(violations, f"SEARCH: search LD-8.Q4 (std-doc): {pin} matches lines [805] and is not recorded")
        # The per-line re-run of every declared pattern equals a plain search of each line of its scope.
        checker = LD.Checker(LD.Options(trees=TREES, check_pin_state=False, check_history=False))
        self.assertTrue(checker.load())
        checker.rows()
        checker.corpora()
        for entry in checker.entries:
            for search in entry.get("search", []):
                corpus = checker.t["corpus"][search["corpus"]]
                if corpus["source"] == "decisions":  # searched by title, not by lines
                    continue
                tree = TREES["worktree" if corpus["source"] == "rustc" else corpus["source"]]
                files = sorted({f for i in corpus["include"] for f in tree.files(i["path"], (i["suffix"],))})
                compiled, plain = re.compile(search["pattern"]), {}
                for f in files:
                    matched = [n for n, line in enumerate(tree.lines(f) or [], 1)
                               if (corpus["lines"] != "doc-comment" or line.strip().startswith(("///", "//!"))) and compiled.search(line)]
                    if matched:
                        plain[f] = matched
                with self.subTest(search=search["id"]):
                    self.assertEqual(checker.corpus_hits(search["corpus"], search["pattern"]), plain)

    def test_citations_resolve_at_their_pins_in_tight_ranges(self):
        cases = [
            ("changed quote", edit_block(self.table, "entry.source", 'id = "LD-10.S10"', lambda b: b.replace("usually aborts", "always aborts")), "SOURCE: source LD-10.S10: rustc:library/std/src/sync/poison/mutex.rs:42-43 does not contain"),
            ("wider range", edit_block(self.table, "entry.source", 'id = "LD-10.S10"', lambda b: b.replace("mutex.rs:42-43", "mutex.rs:41-43")), "SOURCE: source LD-10.S10: rustc:library/std/src/sync/poison/mutex.rs:41-43 is wider than its quote"),
            ("rank of kind", edit_block(self.table, "entry.source", 'id = "LD-10.S10"', lambda b: b.replace("rank = 1", "rank = 2")), "SOURCE: source LD-10.S10: kind 'std-doc' is not a ranked kind, or rank 2 is not its rank"),
            ("source tree of kind", edit_block(self.table, "entry.source", 'id = "LD-10.S10"', lambda b: b.replace('kind = "std-doc"', 'kind = "rustc-test"').replace("rank = 1", "rank = 3")), "SOURCE: source LD-10.S10: a rustc-test source cites `rustc:tests/...`"),
            ("key of another kind", edit_block(self.table, "entry.source", 'id = "LD-10.S10"', lambda b: b.replace("rank = 1\n", 'rank = 1\nsection = "Summary"\n')), "SOURCE: source LD-10.S10: section does not belong to a std-doc source"),
            ("two rows, one text", self.table.replace('[[entry.source]]\nid = "LD-10.S11"', block(self.table, "entry.source", 'id = "LD-10.S10"').replace('id = "LD-10.S10"', 'id = "LD-10.S12"') + '\n[[entry.source]]\nid = "LD-10.S11"', 1),
             "DUPLICATE: LD-10.S12 and LD-10.S10 quote one text of library/std/src/sync/poison/mutex.rs"),
        ]
        for label, table, fragment in cases:
            with self.subTest(label):
                self.assert_violation(self.run_inputs(table).violations, fragment)

    def test_design_cells_ids_and_exits(self):
        design = TREES["worktree"].text(C.DESIGN_REL)
        cases = [
            ("title", replace_once(self.table, 'title = "Data races"', 'title = "Data races (settled)"'), None, "DESIGN: entry LD-4: title is not the design's"),
            ("status", edit_block(self.table, "entry", 'id = "LD-5"', lambda b: b.replace('status = "Recorded"', 'status = "Required"', 1)), None, "DESIGN: entry LD-5: status 'Required' is not the design cell's"),
            ("entry removed", re.sub(r'\n\[\[entry\]\]\nid = "LD-13"\n.*', "\n", self.table, flags=re.S), None, "DESIGN: the entries are"),
            ("exit dropped", "\n[[entry]]\nid = \"LD-2\"".join([re.sub(r'\n\[\[entry\.exit\]\]\nid = "E0\.8"\n[^\n]*\n[^\n]*\n[^\n]*\n', "\n", self.table.split('\n[[entry]]\nid = "LD-2"', 1)[0], count=1),
                                                          self.table.split('\n[[entry]]\nid = "LD-2"', 1)[1]]), None, "DESIGN-EXIT: exit E0.8 (design:3936) names LD-1, but LD-1 does not list it"),
            ("design line naming an entry", None, replace_once(design, "**Stage 0.3: kernel and producer feasibility probes.**", "**Stage 0.3: kernel and producer feasibility probes** (they do not revisit LD-6)."),
             "DESIGN-EXIT: design:3940 names LD-6, but no verified design quote of LD-6 or of the rule covers it"),
            ("OD-5 against E0.8", None, replace_once(design, "LD-8, LD-11, LD-12 and the\n    precedence rule (OD-5).", "LD-8, LD-11 and the\n    precedence rule (OD-5)."), "DESIGN: the OD-5 row lists"),
        ]
        for label, table, mutated, fragment in cases:
            with self.subTest(label):
                trees = {"design": Overlay(TREES["worktree"], {C.DESIGN_REL: mutated})} if mutated else None
                self.assert_violation(self.run_inputs(table, trees=trees).violations, fragment)

    def test_i_precedence_fixture_an_entry_citing_only_rustc_behavior_without_the_de_facto_label_fails(self):
        # The design's mutation fixture (I-PRECEDENCE): LD-9/in-object keeps only its rustc tests.
        table = self.table
        for sid in ("LD-9.S8", "LD-9.S9", "LD-9.S11", "LD-9.S12", "LD-9.S13"):
            table = edit_block(table, "entry.source", f'id = "{sid}"', lambda b: b.replace('aspects = ["in-object"]', 'aspects = ["layout-offsets"]'))
        table = edit_block(table, "entry.source", 'id = "LD-9.S7"', lambda b: b.replace('aspects = ["in-object", "layout-offsets"]', 'aspects = ["layout-offsets"]').replace('roles = { in-object = "open", layout-offsets = "open" }', 'role = "open"'))
        self.assert_violation(self.run_inputs(table).violations, "PRECEDENCE: aspect LD-9/in-object: is labelled 'de-facto-open'; the precedence predicates compute 'de-facto'")

    def test_search_hit_sets_and_line_dispositions(self):
        hit = 'at = "library/stdarch/crates/core_arch/src/x86/fxsr.rs"'
        cases = [
            ("hit dropped", edit_block(self.table, "entry.search.hit", hit, lambda b: ""), "SEARCH: search LD-12.Q4 (std-doc): library/stdarch/crates/core_arch/src/x86/fxsr.rs matches lines [14, 34] and is not recorded"),
            ("line without disposition", edit_block(self.table, "entry.search.hit", hit, lambda b: b.replace("{ lines = [14, 34], reason", "{ lines = [14], reason")), "matches lines [34], which no citation covers and no reason disposes of"),
            ("line with two dispositions", edit_block(self.table, "entry.search.hit", hit, lambda b: b.replace("  { lines = [14, 34], reason", '  { lines = [34], reason = "twice" },\n  { lines = [14, 34], reason')), "lists line 34, which is not matched or already has a disposition"),
            ("recorded lines", edit_block(self.table, "entry.search.hit", hit, lambda b: b.replace("\nlines = [14, 34]", "\nlines = [14]")), "SEARCH: hit LD-12.Q4/library/stdarch/crates/core_arch/src/x86/fxsr.rs: records lines [14]"),
            ("citation covering no matched line", edit_block(self.table, "entry.search.hit", 'at = "library/stdarch/crates/core_arch/src/x86/sse.rs"\nlines = [1436]', lambda b: b.replace('use = ["LD-4.S12"]', 'use = ["LD-4.S12", "LD-4.S3"]')),
             "SEARCH: hit LD-4.Q4/library/stdarch/crates/core_arch/src/x86/sse.rs: is cited by LD-4.S3, which is not a verified LD-4 row at library/stdarch/crates/core_arch/src/x86/sse.rs"),
            ("narrowed pattern", edit_block(self.table, "entry.search", 'id = "LD-12.Q4"', lambda b: b.replace("|MXCSR", "")), "SEARCH: search LD-12.Q4 (std-doc): library/stdarch/crates/core_arch/src/x86/fxsr.rs is recorded but not matched"),
            ("scope without a search", edit_block(self.table, "entry.search", 'id = "LD-12.Q6"', lambda b: ""), "SEARCH: aspect LD-12/default-environment has no search of ['a-mir-formality']"),
            ("undeclared scope", edit_block(self.table, "entry.search", 'id = "LD-12.Q6"', lambda b: b.replace('corpus = "a-mir-formality"', 'corpus = "zulip"')), "SEARCH: search LD-12.Q6: an id LD-12.Q<n>, a declared corpus and aspects of LD-12"),
        ]
        for label, table, fragment in cases:
            with self.subTest(label):
                self.assert_violation(self.run_inputs(table).violations, fragment)

    def test_decision_timing_and_the_opsem_universe(self):
        cases = [
            ("status disagrees with rfcbot", edit_block(self.table, "entry.search.hit", 'at = "rust-lang/rust#157641"', lambda b: b.replace('fcp = "before-pin"', 'fcp = "after-pin"')),
             "DECISION-FCP: hit LD-13.Q7/rust-lang/rust#157641 declares fcp 'after-pin'; rfcbot's completion notices give 'before-pin'"),
            ("opsem record without disposition", edit_block(self.table, "decision", 'at = "rust-lang/reference#1387"', lambda b: ""), "DECISIONS: rust-lang/reference#1387 is an opsem record of the decision index with no disposition"),
        ]
        for label, table, fragment in cases:
            with self.subTest(label):
                self.assert_violation(self.run_inputs(table).violations, fragment)

        # Every real completion in this frozen index now predates the alignment.
        # Keep the future-completion boundary under test using an explicit synthetic
        # status, without mislabelling a real decision or changing its evidence.
        at, where = "rust-lang/rust#999999", "synthetic future decision"
        for extra, refused in (({}, False), ({"reason": "closed later"}, True),
                               ({"reason": ""}, True), ({"use": ["LD-2.S1"]}, True)):
            with self.subTest(future_completion=extra):
                checker = LD.Checker(LD.Options())
                checker.fcp_status = {at: "after-pin"}
                checker.fcp_disposition(where, {"fcp": "after-pin", "use": [], **extra}, at, "SEARCH")
                if refused:
                    self.assert_violation(checker.f.violations,
                                          "DECISION-FCP: synthetic future decision completed after the alignment timestamp")
                else:
                    self.assertEqual(checker.f.violations, [])
                self.assertEqual(checker.verified_issues, {at})

    def test_team_decision_admission(self):
        source = 'id = "LD-9.S13"'
        cases = [
            ("team not on the record", lambda b: b.replace('team = "types"', 'team = "opsem"'), "TEAM-DECISION: source LD-9.S13: the index record rust-lang/rust#117703 is not labelled T-opsem"),
            ("completion notice", lambda b: b.replace("fcp_complete = 1868329463", "fcp_complete = 1838944601"), "TEAM-DECISION: source LD-9.S13: comment 1838944601 is not rfcbot's notice"),
            ("text by rfcbot", lambda b: b.replace("#issuecomment-1838944601", "#issuecomment-1826393881").replace(
                re.search(r'quote = "[^\n]*"', b).group(0), 'quote = "No concerns currently listed."'), "TEAM-DECISION: source LD-9.S13: the quoted text is by rfcbot, neither the proposer nor a listed team member"),
            ("quote not in the comment", lambda b: b.replace("some indirection. Coroutines", "some indirection. All coroutines"), "TEAM-DECISION: source LD-9.S13: https://github.com/rust-lang/rust/pull/117703#issuecomment-1838944601 is not a kept comment"),
        ]
        for label, edit, fragment in cases:
            with self.subTest(label):
                self.assert_violation(self.run_inputs(edit_block(self.table, "entry.source", source, edit)).violations, fragment)

    def test_rfc_records(self):
        cases = [
            ("tracking issue", edit_block(self.table, "rfc", "number = 2394", lambda b: b.replace('tracking_issue = "rust-lang/rust#50547"', 'tracking_issue = "rust-lang/rust#62290"')),
             "RFC: rfc 2394: (accepted-feature) evidence is not"),
            ("header citation outside the header", edit_block(self.table, "rfc", "number = 2394", lambda b: b.replace('pr = { ref = "rfcs:text/2394-async_await.md:3"', 'pr = { ref = "rfcs:text/2394-async_await.md:3"', 1).replace(
                'tracking = { ref = "rfcs:text/2394-async_await.md:5", quote = "[rust-lang/rust#50547](https://github.com/rust-lang/rust/issues/50547)" }',
                'tracking = { ref = "rfcs:text/2394-async_await.md:39", quote = "futures" }')), "RFC: rfc 2394: tracking is a citation, in the header of text/2394-async_await.md"),
            ("section", edit_block(self.table, "entry.source", 'id = "LD-9.S8"', lambda b: b.replace('section = "Return type of `async` functions, closures, and blocks"', 'section = "Summary"')),
             "RFC: source LD-9.S8: names RFC 2394 (an [[rfc]] record of text/2394-async_await.md) and its nearest heading 'Return type of `async` functions, closures, and blocks'"),
        ]
        for label, table, fragment in cases:
            with self.subTest(label):
                self.assert_violation(self.run_inputs(table).violations, fragment)

    def test_std_doc_and_rustc_test_admission(self):
        mutex = "library/std/src/sync/poison/mutex.rs"
        text = TREES["worktree"].text(mutex)
        plain = replace_once(text, "///   lock is held will leave the mutex unpoisoned. Note that while double panic\n", "//   lock is held will leave the mutex unpoisoned. Note that while double panic\n")
        self.assertEqual(self.run_inputs(trees={"worktree": Overlay(TREES["worktree"], {mutex: text})}).violations, [])  # control: the overlay itself
        self.assert_violation(self.run_inputs(trees={"worktree": Overlay(TREES["worktree"], {mutex: plain})}).violations, "STD-DOC: source LD-10.S10: line 42 is not doc-comment prose")
        test = "tests/ui/panics/panic-in-cleanup.rs"
        gated = TREES["worktree"].text(test).replace("//@ run-crash\n", "//@ run-crash\n#![feature(never_type)]\n", 1)
        violations = self.run_inputs(trees={"worktree": Overlay(TREES["worktree"], {test: gated})}).violations
        self.assert_violation(violations, "TEST: source LD-10.S6: a pinning test runs the program")
        table = edit_block(self.table, "entry.source", 'id = "LD-10.S4"', lambda b: b.replace('"ignore-msvc", ', ""))
        self.assert_violation(self.run_inputs(table).violations, "TEST: source LD-10.S4: restrictions are ['ignore-emscripten', 'needs-unwind']")

    def test_owner_questions_ratification_and_state(self):
        cases = [
            ("undefined question", edit_block(self.table, "entry.aspect", 'id = "in-object"', lambda b: b.replace('owner_questions = ["OQ-1", "OQ-2"]', 'owner_questions = ["OQ-1", "OQ-2", "OQ-99"]')), "OQ: LD-9/in-object reference OQ-99, which is not defined"),
            ("demanded question removed", edit_block(self.table, "entry.aspect", 'id = "in-object"', lambda b: b.replace('owner_questions = ["OQ-1", "OQ-2"]', 'owner_questions = ["OQ-1"]')), "OQ: aspect LD-9/in-object: needs an owner question of kind 'open-reading'"),
            ("draft state while ruled", replace_once(self.table, 'state = "ruled-for-OD-5"', 'state = "draft-for-OD-5"'), "STATE: state is 'draft-for-OD-5'; with 0 ruling(s) pending it is 'ruled-for-OD-5'"),
            ("ruling without record", edit_block(self.table, "ratify", 'item = "LD-2"', lambda b: re.sub(r'ruling_record = .*\n', '', b)), "RATIFY: ratify LD-2: ruling in"),
            ("pending with a record", edit_block(self.table, "ratify", 'item = "LD-2"', lambda b: b.replace('ruling = "ratified"', 'ruling = "pending"')), "RATIFY: ratify LD-2: ruling in"),
            ("unknown evidence", edit_block(self.table, "owner_question", 'id = "OQ-9"', lambda b: b.replace('"LD-4.S4", ', '"LD-4.S99", ')), "EVIDENCE: owner_question OQ-9: cites LD-4.S99"),
        ]
        for label, table, fragment in cases:
            with self.subTest(label):
                self.assert_violation(self.run_inputs(table).violations, fragment)

    def test_prose_tokens_in_rows_resolve(self):
        cases = [
            ("unknown id", "[LD-9.S99]", "PROSE: aspect LD-9/in-object: [LD-9.S99] is not a source, related or rule quote id"),
            ("invented quote", "'saved locals are always inline'", "PROSE: aspect LD-9/in-object: the quoted 'saved locals are always inline' is not text of a verified quote"),
            ("misattributed quote", "'Closures have no layout guarantees.' [LD-9.S7]", "is not text of [LD-9.S7]"),
            ("unquoted design line", "(design:1)", "PROSE: aspect LD-9/in-object: design:1 is not inside a verified design quote"),
            ("bare line citation", "(see block-expr.md:194)", "PROSE: aspect LD-9/in-object: 'block-expr.md:194' is a line citation"),
            ("unrecorded RFC", "RFC 2349", "PROSE: aspect LD-9/in-object: RFC 2349 has no [[rfc]] record"),
            ("unverified issue", "rust-lang/rust#1", "PROSE: aspect LD-9/in-object: rust-lang/rust#1 is not a verified snapshot"),
        ]
        for label, token, fragment in cases:
            with self.subTest(label):
                table = edit_block(self.table, "entry.aspect", 'id = "in-object"', lambda b: b.replace("None is a placement rule.", f"None is a placement rule {token}."))
                self.assert_violation(self.run_inputs(table).violations, fragment)

    def test_snapshot_edits_and_rows_are_refused(self):
        root = self.tmp / "root"
        shutil.copytree(ROOT / LD.SNAPSHOT_PREFIX, root / LD.SNAPSHOT_PREFIX)
        fcp = root / LD.SNAPSHOT_PREFIX / "decisions-fcp.json"
        fcp.write_text(replace_once(fcp.read_text(encoding="utf-8"), '"id": 1868329463', '"id": 1868329464'), encoding="utf-8")
        violations = self.run_inputs(snapshot_root=root).violations
        self.assert_violation(violations, "SNAPSHOT: docs/trust-core/snapshots/decisions-fcp.json does not match its sha256 pin",
                              "DECISION-FCP: docs/trust-core/snapshots/decisions-fcp.json keeps a comment on rust-lang/rust#117703 that is not an rfcbot completion notice",
                              "SNAPSHOT: snapshot docs/trust-core/snapshots/decisions-fcp.json: has no committed version")
        table = edit_block(self.table, "snapshot", 'file = "docs/trust-core/snapshots/rust-lang-rust-117703.json"', lambda b: b.replace("1838944601, ", ""))
        self.assert_violation(self.run_inputs(table).violations, "SNAPSHOT: snapshot docs/trust-core/snapshots/rust-lang-rust-117703.json: the file does not hold what its row records")

    def test_rows_keys_duplicates_and_deferred_checks(self):
        cases = [
            ("unknown key", edit_block(self.table, "entry.source", 'id = "LD-9.S13"', lambda b: b.replace('team = "types"', 'team = "types"\nratified = true')), "TABLE: source LD-9.S13: unknown keys ['ratified']"),
            ("repeated element", edit_block(self.table, "entry.source", 'id = "LD-9.S5"', lambda b: b.replace('aspects = ["in-object", "layout-offsets"]', 'aspects = ["in-object", "layout-offsets", "in-object"]')), "TABLE: source LD-9.S5: aspects repeats 'in-object'"),
            ("duplicate row", self.table.replace("\n[[decision]]\n", "\n" + block(self.table, "decision", 'at = "rust-lang/reference#1387"') + "\n[[decision]]\n", 1), "TABLE: decision rust-lang/reference#1387: duplicate row"),
            ("deferred exit", edit_block(self.table, "deferred_check", 'id = "quote-boundaries"', lambda b: b.replace('checked_by = ["E0.8"]', 'checked_by = ["E0.8", "E2.3.3"]')), "DEFERRED: deferred_check quote-boundaries: checked_by 'E2.3.3' is a design exit quoted by one of its citations"),
            ("deferred field", edit_block(self.table, "deferred_check", 'id = "quote-boundaries"', lambda b: b.replace('"related.quote"', '"related.wording"')), "DEFERRED: deferred_check quote-boundaries: 'related.wording' is not a <row kind>.<field> of the table"),
        ]
        for label, table, fragment in cases:
            with self.subTest(label):
                self.assert_violation(self.run_inputs(table).violations, fragment)

    # ---- the judgment layer and the document
    def test_a_changed_judgment_fails_only_review_until_reviewed(self):
        hit = 'at = "library/stdarch/crates/core_arch/src/x86/fxsr.rs"'
        for label, table, doc, jid in (
            ("reason", edit_block(self.table, "entry.search.hit", hit, lambda b: b.replace("states no rule on the environment", "states the rule")), None, "hit:LD-12.Q4/library/stdarch/crates/core_arch/src/x86/fxsr.rs"),
            ("scope", edit_block(self.table, "corpus", 'name = "reference"', lambda b: b.replace("Every chapter", "Each chapter")), None, "corpus:reference"),
            ("prose", None, replace_once(self.doc, "ruling (option 1) keeps it.", "ruling (option 1) drops it."), "prose:this-revision"),
            ("heading", None, replace_once(self.doc, "## Limitations\n", "## Limitations (none remain)\n"), "outline:document"),
            ("table comment", replace_once(self.table, 'schema = "trust.core.language-decisions.v4"', '# OWNER RULING: LD-9 is team-decision.\nschema = "trust.core.language-decisions.v4"'), None, "comments:table"),
        ):
            with self.subTest(label):
                violations = self.run_inputs(table, doc).violations
                self.assertEqual(self.mechanical(violations), [])
                self.assertEqual([v.split(": its content")[0] for v in violations if v.startswith("REVIEW:")], [f"REVIEW: judgment {jid}"])
                self.assertEqual(self.mechanical(self.run_inputs(table, doc, registry=self.review([jid], table, doc)).violations), [])

    def test_document_blocks_sections_and_pins(self):
        cases = [
            ("counts block", replace_once(self.doc, "matched lines: 1766", "matched lines: 1765"), "DOC: the published `ld-counts` block differs"),
            ("unreviewed line", replace_once(self.doc, "## Limitations\n", "## Limitations\n\nAn unreviewed ruling.\n"), "DOC: line"),
            ("unchecked citation", replace_once(self.doc, "ruling (option 1) keeps it.", "ruling (option 1) keeps it (design:1109)."), "line citation 'design:1109' is not in the checked"),
            ("quote drift", replace_once(self.doc, "design:778 «A lower rank never overrides a higher one.»", "design:778 «A lower rank may override a higher one.»"), "DOC: prose:resolutions: design:778 does not contain"),
            ("pin", replace_once(self.doc, "`3bdcd22feea6848a7920fa06d17ad4c6ada9db89`", "`3bdcd22feea6`"), "DOC: the document does not record the pin `3bdcd22feea6848a7920fa06d17ad4c6ada9db89`"),
        ]
        for label, doc, fragment in cases:
            with self.subTest(label):
                self.assert_violation(self.run_inputs(doc=doc).violations, fragment)

    def test_recorded_rulings_clear_the_pending_count(self):
        # The real table: every OD-5 item ruled (2026-10-02), state ruled-for-OD-5.
        result = self.run_inputs(self.table, require_ruled=True)
        self.assert_violation(result.violations, "CONFLICT-UNRULED")
        self.assertFalse(any(v.startswith(("RULING-PENDING", "STATE", "RATIFY")) for v in result.violations))
        # Withdraw one ruling: the pending count comes back, and the state must follow it.
        table = edit_block(self.table, "ratify", 'item = "LD-12"', lambda b: re.sub(r'ruling = "ratified"\nruling_record = .*\n', 'ruling = "pending"\n', b))
        result = self.run_inputs(table, require_ruled=True)
        self.assert_violation(result.violations, "RULING-PENDING", "STATE: state is 'ruled-for-OD-5'; with 1 ruling(s) pending it is 'draft-for-OD-5'")
        table = replace_once(table, 'state = "ruled-for-OD-5"', 'state = "draft-for-OD-5"')
        self.assertFalse(any(v.startswith(("STATE", "RATIFY")) for v in self.run_inputs(table).violations))


if __name__ == "__main__":
    unittest.main(verbosity=1)
