#!/usr/bin/env python3
"""Controls for scripts/trust_core/ub_coverage_matrix.py (D0.2, the UB coverage matrix).

* The REAL checker on the REAL inputs (the pinned MiniRust and Reference clones, this repository's
  design, vocabulary, Miri tree and rustc at HEAD, the table, the document and the review registry)
  exits 0 and publishes the counts asserted here, and the content fixes of the port hold.
* Every mutation of an input (a temporary copy of the table, document or registry, or a source tree
  with one file changed) makes the CHECKER report the violation it introduces, beside an unmutated
  control. A mechanical mutation names its predicate; a judgment mutation passes every mechanical
  predicate, fails REVIEW, and passes once a new review record of its digest is appended.

The shared layers (pins, citations, uniqueness, blocks, reviews) are tested in
scripts/tests/trust_core_common_test.py. A missing source clone is a FAILURE that prints the clone
command, never a skip.

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
SCRIPT = ROOT / "scripts" / "trust_core" / "ub_coverage_matrix.py"
SPEC = importlib.util.spec_from_file_location("trust_core_ub_coverage_matrix", SCRIPT)
M = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(M)
C = M.C
TABLE, DOC, REGISTRY = ROOT / M.TABLE_REL, ROOT / M.DOC_REL, ROOT / M.REGISTRY_REL
CLONES = {}
PINS = None
CHAPTER = M.CHAPTER

# The published counts (UB_COVERAGE_MATRIX.md). A change here is a change to the matrix.
PUBLISHED = {'ub_list': {'total': 20,
             'reason': 9,
             'ld': 0,
             'both': 11,
             'none': 0,
             'unmapped': 0,
             'effects': '16 / 4 / 0 / 0 / 0'},
 'validity_list': {'total': 15,
                   'reason': 13,
                   'ld': 1,
                   'both': 1,
                   'none': 0,
                   'unmapped': 0,
                   'effects': '14 / 1 / 0 / 0 / 0'},
 'chapter_other': {'total': 15,
                   'reason': 8,
                   'ld': 0,
                   'both': 0,
                   'none': 7,
                   'unmapped': 0,
                   'effects': '2 / 4 / 2 / 7 / 0'},
 'other_reference': {'total': 63,
                     'reason': 41,
                     'ld': 0,
                     'both': 4,
                     'none': 18,
                     'unmapped': 0,
                     'effects': '39 / 0 / 6 / 17 / 1'},
 'ub_list_top': 11,
 'validity_top': 13,
 'chapter_rules': 39,
 'miri_files': 556,
 'miri_revisioned': 56,
 'miri_outcomes': 620,
 'by_disposition': {'reason': 455, 'ld': 103, 'no-core-ub': 5, 'non-ub': 57},
 'by_basis': {'miri-internal': 0, 'miri-analysis-mode': 1, 'minirust-divergence': 4},
 'stacked_files': (84, 38),
 'stacked_outcomes': 84,
 'tree_files': (99, 53),
 'tree_outcomes': 105,
 'both_specific': 46,
 'by_tracker': {'stacked': 440, 'tree': 105, 'none': 75},
 'tb_forms': {'child': 63, 'foreign': 25, 'dealloc': 5, 'no-exposed': 9},
 'tb_protected': (7, 52),
 'reasons': (174, 19, 119, 69, 47),
 'citations': 439,
 'doc_citations': 45}
PUBLISHED_CLASSES = {'ub': (340, 336),
 'ub-stacked-borrows': (80, 80),
 'ub-tree-borrows': (102, 96),
 'ub-data-race': (40, 36),
 'const-eval-error': (4, 4),
 'abort': (19, 18),
 'unsupported': (17, 17),
 'resource-exhaustion': (0, 0),
 'memory-leak': (5, 5),
 'deadlock': (1, 1),
 'post-monomorphization-error': (1, 1),
 'link-error': (5, 5),
 'compile-error': (5, 5),
 'no-entry-point': (1, 1)}
PUBLISHED_LD_USE = {'LD-1': (13, 189),
 'LD-2': (2, 4),
 'LD-3': (1, 42),
 'LD-4': (1, 40),
 'LD-5': (1, 1),
 'LD-6': (0, 0),
 'LD-7': (0, 0),
 'LD-8': (0, 0),
 'LD-9': (0, 1),
 'LD-10': (0, 1),
 'LD-11': (0, 0),
 'LD-12': (1, 0),
 'LD-13': (0, 0)}
PUBLISHED_JUDGMENTS = 757


def setUpModule():
    global PINS
    PINS = C.load_pins()
    try:
        CLONES.update(C.locate_clones(PINS, sorted(M.READS)))
    except C.MissingClone as error:
        raise AssertionError(str(error)) from None


class Overlay:
    """A tree with some files replaced, added (text) or removed (None)."""

    def __init__(self, base, files: dict) -> None:
        self.base, self.over = base, dict(files)

    def files(self, prefix: str = "", suffixes: tuple = ()) -> list[str]:
        found = set(self.base.files(prefix, suffixes)) | {r for r in self.over if r.startswith(prefix) and (not suffixes or r.endswith(suffixes))}
        return sorted(r for r in found if self.over.get(r, "") is not None)

    def prefetch(self, rels) -> None:
        self.base.prefetch([r for r in rels if r not in self.over])

    def text(self, rel: str):
        return self.over[rel] if rel in self.over else self.base.text(rel)

    def lines(self, rel: str):
        text = self.text(rel)
        return None if text is None else text.split("\n")


def replace_once(text: str, old: str, new: str) -> str:
    assert text.count(old) == 1, (old, text.count(old))
    return text.replace(old, new)


def sub_once(text: str, pattern: str, repl: str) -> str:
    out, n = re.subn(pattern, repl, text)
    assert n == 1, (pattern, n)
    return out


def row_block(text: str, kind: str, line: str) -> str:
    """The [[kind]] block of the table holding the exact line `line`."""
    for part in re.split(r"\n(?=\[\[)", text):
        if part.startswith(f"[[{kind}]]") and f"\n{line}\n" in part + "\n":
            return part
    raise AssertionError((kind, line))


def edit_row(text: str, kind: str, line: str, edit) -> str:
    old = row_block(text, kind, line)
    return replace_once(text, old, edit(old))


def changed(violations) -> list[str]:
    """The judgment ids of `violations`, each of which must be a REVIEW content change."""
    violations = [v for v in violations if "block differs from its computed rendering" not in v]
    ids = [m.group(1) for v in violations for m in [re.match(r"^REVIEW: judgment (.+?): its content changed", v)] if m]
    assert len(ids) == len(violations), violations
    return sorted(ids)


def move_section(text: str, jid: str, after: str) -> str:
    """`text` with the reviewed section `jid` and its following blank line moved to just after `after`."""
    start = text.index(f"<!-- reviewed:{jid} -->\n")
    end = text.index(f"<!-- /reviewed:{jid} -->\n\n") + len(f"<!-- /reviewed:{jid} -->\n\n")
    section, rest = text[start:end], text[:start] + text[end:]
    return replace_once(rest, after, after + section)


def move_table_header(text: str) -> str:
    """The table with its header comment moved from the top to just above the first [[miri]] row."""
    top = text.index("\nschema = ") + 1
    header, rest = text[:top], text[top:]
    first = rest.index("\n[[miri]]\n") + 1
    return rest[:first] + header + rest[first:]


def reference_tree():
    return C.GitTree(CLONES["rust-reference"], PINS.sources["rust-reference"].revision)


def head():
    return C.GitTree(ROOT, "HEAD")


class RealInputs(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.result = M.collect()

    def test_real_inputs_pass_and_publish_the_counts(self):
        r = self.result
        self.assertEqual(r.violations, [])
        for key, value in PUBLISHED.items():
            self.assertEqual(r.counts[key], value, key)
        self.assertEqual(r.counts["by_class"], PUBLISHED_CLASSES)
        self.assertEqual(r.counts["ld_use"], PUBLISHED_LD_USE)
        self.assertEqual(r.counts["reviews"]["judgments"], PUBLISHED_JUDGMENTS)

    def test_the_port_content_fixes_hold(self):
        data = C.tomllib.loads(TABLE.read_text(encoding="utf-8"))
        rows = {(r["file"], r["line"]): r for r in data["reference"]}
        # Blocker: the runtime bullets name only what the Reference makes UB.
        self.assertEqual(rows[(CHAPTER, 66)]["reasons"], ["UbReason.UnwindIntoUnreachable"])
        bottom = {"UbReason.UnwindOutOfBottomFrame", "UbReason.StartFunctionReturned", "UbReason.StopUnwindPayloadStackEmpty"}
        self.assertFalse(bottom & {n for r in data["reference"] for n in r["reasons"]})
        # The intrinsics bullet names the reason of Miri's simd_extract outcome.
        self.assertIn("UbReason.IndexOutOfBounds", rows[(CHAPTER, 50)]["reasons"])
        # The design count is a reviewed judgment, and no document text claims a reworded count cannot escape.
        self.assertEqual(data["design_count"]["count"], 556)
        self.assertNotIn("a reworded or added count fails", DOC.read_text(encoding="utf-8"))
        registry = C.read_registry(REGISTRY.read_text(encoding="utf-8"))["judgment"]
        for jid in (f"reference:{CHAPTER}:59", f"reference:{CHAPTER}:60", f"reference:{CHAPTER}:44", "design_count:table",
                    "prose:finding-bottom-frame", "prose:oq-13"):
            self.assertIn("d02-port-content-fixes", [r[0] for r in registry[jid]["reviews"]], jid)

    def test_current_external_obligations_and_native_funnel_are_distinct(self):
        data = C.tomllib.loads(TABLE.read_text(encoding="utf-8"))
        rows = {r["path"]: r for r in data["miri"]}
        for path, reason in (
            ("extern-extra-track-caller.rs", "CallTrackCallerMismatch"),
            ("extern-missing-track-caller.rs", "CallTrackCallerMismatch"),
            ("extern_static/mut_mismatch1.rs", "ExternalStaticDeclarationMismatch"),
            ("extern_static/wrong_size.rs", "ExternalStaticDeclarationMismatch"),
            ("extern_static/wrong_type.rs", "ExternalStaticDeclarationMismatch"),
            ("intrinsics/funnel_shl.rs", "ShiftUncheckedOverflow"),
            ("intrinsics/funnel_shr.rs", "ShiftUncheckedOverflow"),
        ):
            with self.subTest(path=path):
                outcome, = rows["tests/fail/" + path]["outcomes"]
                self.assertEqual(outcome["disposition"], "reason")
                self.assertEqual(outcome["reasons"], ["UbReason." + reason])
        variadic, = [r for r in data["reference"] if r.get("rule") == "items.fn.c-variadic.next-arg-safety"]
        self.assertIn("UbReason.VariadicArgumentValueUnrepresentable", variadic["reasons"])
        dangling, = [r for r in data["reference"] if r.get("rule") == "undefined.dangling.def"]
        self.assertIn("UbReason.PointeeSizeExceedsIsizeMax", dangling["reasons"])
        self.assertIn("zero-sized", dangling["note"])

    def test_cli_exits_zero_on_real_inputs(self):
        run = subprocess.run([sys.executable, str(SCRIPT)], capture_output=True, text=True)
        self.assertEqual(run.returncode, 0, run.stderr)
        self.assertIn(f"ub_coverage_matrix: OK ({PUBLISHED['citations']} row citations, {PUBLISHED['doc_citations']} document citations, {PUBLISHED_JUDGMENTS} reviewed judgments)", run.stdout)

    def test_a_missing_clone_exits_two_with_its_clone_command(self):
        with tempfile.TemporaryDirectory() as tmp:
            run = subprocess.run([sys.executable, str(SCRIPT), "--reference", str(Path(tmp) / "absent")], capture_output=True, text=True)
            self.assertEqual(run.returncode, 2)
            self.assertIn(f"git clone https://github.com/rust-lang/reference {Path(tmp) / 'absent'}", run.stderr)


class Mutations(unittest.TestCase):
    def setUp(self):
        self._tmp = tempfile.TemporaryDirectory()
        self.tmp = Path(self._tmp.name)
        self.table, self.doc, self.registry = (p.read_text(encoding="utf-8") for p in (TABLE, DOC, REGISTRY))

    def tearDown(self):
        self._tmp.cleanup()

    def run_inputs(self, table=None, doc=None, registry=None, trees=None, pins=False):
        paths = {}
        for name, text in (("table.toml", table or self.table), ("doc.md", doc or self.doc), ("registry.toml", registry or self.registry)):
            paths[name] = self.tmp / name
            paths[name].write_text(text, encoding="utf-8")
        return M.collect(M.Options(table=paths["table.toml"], doc=paths["doc.md"], registry=paths["registry.toml"],
                                   trees=trees or {}, check_pin_state=pins, check_history=False))

    def found(self, violations, *fragments):
        for fragment in fragments:
            self.assertTrue(any(fragment in v for v in violations), f"{fragment!r} not in {violations}")

    @staticmethod
    def mechanical(violations):
        return [v for v in violations if not v.startswith("REVIEW:") and "block differs from its computed rendering" not in v]

    def review(self, jids, table=None, doc=None, trees=None, record="mutation-review"):
        """The registry with a new record's review of each judgment's current content appended."""
        now = self.run_inputs(table, doc, trees=trees).judgments
        text = self.registry.replace("\n[judgment]\n", f'\n[record.{record}]\nround = "test"\ndate = "2026-09-17"\nevidence = ["the mutation"]\nreason = "a mutation test"\n\n[judgment]\n', 1)
        for jid in jids:
            digest = C.digest(jid, now[jid])
            line = next((l for l in text.split("\n") if l.startswith(f'"{jid}" = ')), None)
            if line is None:
                text = text.replace("\n[judgment]\n", f'\n[judgment]\n"{jid}" = {{ digest = "{digest}", reviews = [["{record}", "{digest}"]] }}\n', 1)
            else:
                old = line.split('digest = "')[1].split('"')[0]
                text = text.replace(line, line.replace(f'digest = "{old}"', f'digest = "{digest}"')[:-4] + f'], ["{record}", "{digest}"]] }}')
        return text

    def test_control_copies_pass(self):
        self.assertEqual(self.run_inputs().violations, [])

    # ---- REFERENCE: the universe and stale rows
    def test_reference_universe_mutations(self):
        chapter = reference_tree().text(CHAPTER)
        other = "src/types/boolean.md"
        other_text = reference_tree().text(other)
        cases = [
            ("fake bullet", {CHAPTER: replace_once(chapter, "* Invoking undefined behavior via compiler intrinsics.\n",
                                                   "* Invoking undefined behavior via compiler intrinsics.\n  * Calling a fake intrinsic.\n")},
             ["REFERENCE: unmapped Reference unit: src/behavior-considered-undefined.md:51 undefined.intrinsic 'Calling a fake intrinsic.'"]),
            ("changed bullet", {CHAPTER: replace_once(chapter, "* Data races.\n", "* Data races between threads.\n")},
             ["REFERENCE: reference src/behavior-considered-undefined.md:16 undefined.race: names no unit", "unmapped Reference unit: src/behavior-considered-undefined.md:16 undefined.race 'Data races between threads.'"]),
            ("new rule elsewhere", {other: other_text + "\nr[type.bool.fake]\nBehavior is undefined if a bool is observed twice.\n"},
             ["unmapped Reference unit: src/types/boolean.md:"]),
            ("changed body", {other: replace_once(other_text, "is always sound", "is always sound (always)")},
             ["REFERENCE: reference src/types/boolean.md:116 type.bool.validity: body_sha256 is"]),
        ]
        for label, files, fragments in cases:
            with self.subTest(label):
                self.found(self.run_inputs(trees={"reference": Overlay(reference_tree(), files)}).violations, *fragments)

    def test_units_that_share_a_key_are_told_apart_by_line(self):
        # The verifier's M defect on 25d2ef0573: units were keyed by (file, rule, item, text) alone,
        # so a second identical unit collapsed into the first, had no row, and counted as mapped.
        chapter = reference_tree().text(CHAPTER)
        glossary = "src/glossary.md"
        glossary_lines = reference_tree().lines(glossary)
        self.assertEqual((glossary_lines[251], glossary_lines[252]), ("", "### Undefined behavior"))
        repeated_heading = "\n".join(glossary_lines[:251] + ["### Undefined behavior"] + glossary_lines[252:])
        repeated_bullet = replace_once(chapter, "* Data races.\n\nr[undefined.pointer-access]", "* Data races.\n* Data races.\nr[undefined.pointer-access]")
        for label, files, unmapped, kept in (
            ("repeated bullet", {CHAPTER: repeated_bullet}, f"REFERENCE: unmapped Reference unit: {CHAPTER}:17 undefined.race 'Data races.'", f"{CHAPTER}:16 undefined.race: line is"),
            ("repeated line", {glossary: repeated_heading}, f"REFERENCE: unmapped Reference unit: {glossary}:252 (no rule) '### Undefined behavior'", f"{glossary}:253"),
        ):
            with self.subTest(label):
                violations = self.run_inputs(trees={"reference": Overlay(reference_tree(), files)}).violations
                self.found(violations, unmapped)
                self.assertFalse([v for v in violations if kept in v], violations)  # the existing row keeps its own unit
        trees = {"reference": Overlay(reference_tree(), {glossary: repeated_heading})}
        row = row_block(self.table, "reference", 'text = "### Undefined behavior"')
        # A row for the second unit maps it; once reviewed, and the counts regenerated, nothing is left.
        both = replace_once(self.table, row + "\n", row + "\n" + row.replace("line = 253", "line = 252") + "\n")
        result = self.run_inputs(both, trees=trees)
        self.assertEqual(self.mechanical(result.violations), [])
        self.assertEqual([v for v in result.violations if v.startswith("REVIEW:")],
                         [f"REVIEW: judgment reference:{glossary}:252 is not registered in registry.toml; register it with a review record"])
        regenerated = self.doc
        for name, body in result.blocks.items():
            regenerated = C.replace_block(regenerated, name, body)
        self.assertEqual(self.run_inputs(both, regenerated, registry=self.review([f"reference:{glossary}:252"], both, regenerated, trees=trees), trees=trees).violations, [])
        # A row whose line is none of the units that share its rule, item and text names no unit.
        astray = replace_once(self.table, row + "\n", row + "\n" + row.replace("line = 253", "line = 254") + "\n")
        self.found(self.run_inputs(astray, trees=trees).violations,
                   f"REFERENCE: reference {glossary}:254 (no rule): the units at lines [252, 253] share its rule, item and text, and its line is none of them",
                   f"REFERENCE: unmapped Reference unit: {glossary}:252")

    def test_reference_row_mutations(self):
        race = row_block(self.table, "reference", 'item = "Data races."')
        cases = [
            ("deleted row", replace_once(self.table, race + "\n", ""), ["REFERENCE: unmapped Reference unit: src/behavior-considered-undefined.md:16", f"REVIEW: judgment reference:{CHAPTER}:16: is registered, but no such judgment exists"]),
            ("duplicated row", replace_once(self.table, race + "\n", race + "\n" + race + "\n"), ["duplicate row 'src/behavior-considered-undefined.md:16'", "REVIEW: judgment id reference:src/behavior-considered-undefined.md:16 is produced twice"]),
            ("wrong line", replace_once(self.table, race, race.replace("line = 16", "line = 17")), ["REFERENCE: reference src/behavior-considered-undefined.md:17 undefined.race: line is 17; derived 16"]),
            ("narrowed search", replace_once(self.table, "words = '\\bundefined\\b|\\bUB\\b'", "words = '\\bundefined\\b'"), ["names no unit of the Reference at the pin (stale row)"]),
        ]
        for label, table, fragments in cases:
            with self.subTest(label):
                self.found(self.run_inputs(table).violations, *fragments)

    # ---- MIRI: the universe, stale rows and classes
    def test_miri_universe_mutations(self):
        fail = M.MIRI + M.FAIL
        stderr = head().text(fail + "intrinsics/simd-extract.stderr")
        aliasing = head().text(fail + "both_borrows/alias_through_mutation.rs")
        cases = [
            # Revisions that repeat, or two revision lists, would give two outcomes one stderr and one row.
            ("repeated revision", {fail + "both_borrows/alias_through_mutation.rs": replace_once(aliasing, "//@revisions: stack tree\n", "//@revisions: stack tree tree\n")},
             ["MIRI: tests/fail/both_borrows/alias_through_mutation.rs: its //@revisions lines [['stack', 'tree', 'tree']] are not one list of distinct revisions"]),
            ("second revision list", {fail + "both_borrows/alias_through_mutation.rs": replace_once(aliasing, "//@revisions: stack tree\n", "//@revisions: stack tree\n//@revisions: tree\n")},
             ["MIRI: tests/fail/both_borrows/alias_through_mutation.rs: its //@revisions lines [['stack', 'tree'], ['tree']] are not one list of distinct revisions"]),
            ("fake test", {fail + "fake.rs": "fn main() {}\n", fail + "fake.stderr": stderr}, ["MIRI: unmapped Miri tests/fail file: tests/fail/fake.rs"]),
            ("missing stderr", {fail + "intrinsics/simd-extract.stderr": None}, ["MIRI: tests/fail/intrinsics/simd-extract.rs: its stderr simd-extract.stderr does not exist"]),
            ("orphan stderr", {fail + "orphan.stderr": stderr}, ["MIRI: tests/fail/orphan.stderr is the stderr of no test revision"]),
            ("stray file", {fail + "notes.txt": "x\n"}, ["MIRI: tests/fail/notes.txt is neither a test nor a stderr file"]),
            ("unknown error form", {fail + "intrinsics/simd-extract.stderr": stderr.replace("error: Undefined Behavior:", "error: Something else:", 1)},
             ["MIRI: tests/fail/intrinsics/simd-extract.rs: the error line 'error: Something else: `simd_extract` index 4 is out-of-bounds of vector with length 4' matches the class forms [], not exactly one"]),
            ("changed error", {fail + "intrinsics/simd-extract.stderr": stderr.replace("index 4", "index 5", 1)}, ["MIRI: miri tests/fail/intrinsics/simd-extract.rs: error is"]),
        ]
        for label, files, fragments in cases:
            with self.subTest(label):
                self.found(self.run_inputs(trees={"worktree": Overlay(head(), files)}).violations, *fragments)

    def test_miri_table_mutations(self):
        simd = row_block(self.table, "miri", 'path = "tests/fail/intrinsics/simd-extract.rs"')
        cases = [
            ("deleted row", replace_once(self.table, simd + "\n", ""), ["MIRI: unmapped Miri tests/fail file: tests/fail/intrinsics/simd-extract.rs"]),
            ("class form removed", edit_row(self.table, "class_form", 'id = "ub"', lambda b: b.replace("error = '^error: Undefined Behavior: '", "error = '^error: Undefined behaviour: '")),
             ["matches the class forms [], not exactly one"]),
            ("tb form removed", edit_row(self.table, "tb_form", 'form = "dealloc"', lambda b: b.replace("disallows deallocations$", "disallows deallocation$")),
             ["the Tree Borrows stderr carries the detail forms [], not exactly one"]),
        ]
        for label, table, fragments in cases:
            with self.subTest(label):
                self.found(self.run_inputs(table).violations, *fragments)

    # ---- MAPPING: names, effects, dispositions and declared scopes
    def test_mapping_mutations(self):
        def miri(path, edit):
            return edit_row(self.table, "miri", f'path = "{path}"', edit)
        cases = [
            ("bullet relabelled scope", edit_row(self.table, "reference", 'item = "Data races."', lambda b: b.replace('effect = "ub"', 'effect = "scope"').replace('reasons = ["UbReason.DataRace"]', "reasons = []").replace('ld = ["LD-4"]', "ld = []")),
             "a bullet of the list list maps to a reason or an LD entry"),
            ("unknown reason", edit_row(self.table, "reference", 'item = "Data races."', lambda b: b.replace('"UbReason.DataRace"', '"UbReason.DataRaces"')), "UbReason.DataRaces is no UB reason of the Core vocabulary"),
            ("unknown LD", edit_row(self.table, "reference", 'item = "Data races."', lambda b: b.replace('"LD-4"', '"LD-14"')), "LD-14 is no entry of the design's LD table"),
            ("settled LD named", edit_row(self.table, "reference", 'rule = "undefined.validity.scalar"', lambda b: b.replace("ld = []", 'ld = ["LD-7"]')), "LD-7 is settled by rank 1"),
            ("inclusion", self.table.replace('"UbReason.RawEqArgCount", ', "", 1), "inclusion intrinsics-bullet: reference src/behavior-considered-undefined.md:50 must include ['UbReason.RawEqArgCount']"),
            ("intrinsic test reason no bullet names", self.table.replace(', "UbReason.IndexOutOfBounds"]', "]", 1),
             "miri_coverage tests/fail/intrinsics/: tests/fail/intrinsics/simd-extract.rs[] names ['UbReason.IndexOutOfBounds']"),
            ("name rule", edit_row(self.table, "reference", 'rule = "interior-mut.mut-unsafe-cell"', lambda b: b.replace('reasons = ["UbReason.AliasViolation"]', 'reasons = ["TreeBorrowsUb.LocalWriteUnprotectedFrozen"]')),
             "a TreeBorrowsUb reason is named only with ['UbReason.AliasViolation'] and ['LD-1']"),
            ("stacked borrows as reason", miri("tests/fail/stacked_borrows/illegal_read1.rs", lambda b: b.replace('disposition = "ld", reasons = []', 'disposition = "reason", reasons = ["UbReason.AliasViolation"]')),
             "a Stacked Borrows verdict is decided by LD-1"),
            ("implicit-writes twin judged apart", miri("tests/fail/tree_borrows/cell-inside-struct.rs", lambda b: b.replace('revision = "tree_implicit_writes", stderr = "cell-inside-struct.tree_implicit_writes.stderr", error = "error: Undefined Behavior: write access through <TAG> (a) at ALLOC[0x0] is forbidden", class = "ub-tree-borrows", disposition = "reason", reasons = ["UbReason.AliasViolation", "TreeBorrowsUb.LocalWriteUnprotectedFrozen"], ld = ["LD-1"], tb_protected = false',
                                                                                                                'revision = "tree_implicit_writes", stderr = "cell-inside-struct.tree_implicit_writes.stderr", error = "error: Undefined Behavior: write access through <TAG> (a) at ALLOC[0x0] is forbidden", class = "ub-tree-borrows", disposition = "reason", reasons = ["UbReason.AliasViolation", "TreeBorrowsUb.LocalWriteUnprotectedFrozen"], ld = ["LD-1"], tb_protected = true')),
             "prints the byte-identical report without -Zmiri-tree-borrows-implicit-writes"),
            ("retag race without LD-1", miri("tests/fail/stacked_borrows/retag_data_race_read.rs", lambda b: b.replace('ld = ["LD-4", "LD-1"]', 'ld = ["LD-4"]')), "a race with a retag carries LD-1"),
            ("wildcard without LD-3", miri("tests/fail/tree_borrows/wildcard/dealloc.rs", lambda b: b.replace(', "LD-3"]', "]")), "an access through a wildcard provenance carries LD-3"),
            ("basis without switch", miri("tests/fail/alloc/global_system_mixup.rs", lambda b: b.replace('basis = "minirust-divergence"', 'basis = "miri-analysis-mode"')), "basis miri-analysis-mode needs -Zmiri-symbolic-alignment-check"),
        ]
        for label, table, fragment in cases:
            with self.subTest(label):
                self.assertNotEqual(table, self.table)
                self.found(self.run_inputs(table).violations, "MAPPING: ", fragment)

    # ---- COUNT and PIN
    def test_count_and_pin_mutations(self):
        design = head().text(M.DESIGN_REL)
        cases = [
            ("count", replace_once(self.table, "count = 556", "count = 557"), None, ["COUNT: [design_count] records 557; 556 tests/fail files are read at HEAD", "does not state the count 557"]),
            ("design count reworded", None, {"design": C.DirTree(self.tmp, {M.DESIGN_REL: replace_once(design, "`tests/fail` (556) with UB class [M];", "`tests/fail` (557) with UB class [M];")})},
             ["CITE: [design_count]: design:4955 does not contain"]),
            ("deferred exit", edit_row(self.table, "deferred_check", 'id = "rustc-intrinsic-operations"', lambda b: b.replace('checked_by = ["E2.1.2"]', 'checked_by = ["E2.1.3"]')), None,
             ["COUNT: deferred_check rustc-intrinsic-operations: checked_by 'E2.1.3' is an exit id quoted"]),
            # Appended to [added_reasons].names itself: the list's last entry and the `why` prose after
            # it both change as the vocabulary grows (an anchor on them stopped matching on 11-02).
            ("added reason", sub_once(self.table, r'(\n\[added_reasons\]\nnames = \[[^\]\n]*)\]', r'\1, "UbReason.DataRace"]'), None,
             ["COUNT: [added_reasons] UbReason.DataRace is no trust-extension vocabulary reason"]),
        ]
        for label, table, trees, fragments in cases:
            with self.subTest(label):
                self.found(self.run_inputs(table, trees=trees).violations, *fragments)
        pinned = replace_once(self.table, 'tests_fail_tree = "68d30ebdd91e8348da4bdba4c02004a937874cc4"', 'tests_fail_tree = "' + "0" * 40 + '"')
        self.found(self.run_inputs(pinned, pins=True).violations, "PIN: HEAD:src/tools/miri/tests/fail is tree 68d30ebdd91e8348da4bdba4c02004a937874cc4, not the recorded")

    # ---- REVIEW: a judgment change is visible, and passes once reviewed
    def test_a_changed_judgment_fails_only_review_until_reviewed(self):
        cases = [
            ("row note", edit_row(self.table, "reference", 'item = "Data races."', lambda b: b.replace("LD-4 settles the definition", "LD-4 settles its definition")), None, [f"reference:{CHAPTER}:16"]),
            ("miri disposition", edit_row(self.table, "miri", 'path = "tests/fail/tree_borrows/protector-write-lazy.rs"', lambda b: b.replace("tb_protected = false", "tb_protected = true")), None,
             ["miri:tests/fail/tree_borrows/protector-write-lazy.rs"]),
            # The verifier's M13b: a Finding's claim inverted, and its heading reworded.
            ("finding inverted", None, replace_once(self.doc, "* **Rank 1 vs rank 1: dereferencing", "* **Rank 1 agrees: dereferencing"), ["prose:finding-zero-sized-deref"]),
            # The verifier's M13: an owner question's citation replaced by a resolvable, unrelated one.
            ("oq citation swapped", None, replace_once(self.doc, "(design:870 «Their kinds are Stack, Heap, Global,»)", "(design:3935 «**E0.7** Every Reference UB bullet maps to a reason or an LD entry: 0 unmapped.»)"), ["prose:oq-4"]),
            ("heading", None, replace_once(self.doc, "## Open questions\n", "## Open questions (all resolved)\n"), ["outline:document"]),
            # The verifier's J defect on 25d2ef0573: a reviewed section moved under another heading.
            ("owner questions moved under Limitations", None, replace_once(replace_once(self.doc, "<!-- /reviewed:prose:oq-13 -->\n\n## Limitations\n", "<!-- /reviewed:prose:oq-13 -->\n"),
                                                                           "<!-- reviewed:prose:oq-10 -->\n", "## Limitations\n\n<!-- reviewed:prose:oq-10 -->\n"), ["outline:document"]),
            ("finding moved under Limitations", None, move_section(self.doc, "prose:finding-bottom-frame", "## Limitations\n\n"), ["outline:document"]),
            # The table's header comment moved down to head the Miri rows alone.
            ("table comment moved", move_table_header(self.table), None, ["comments:table"]),
            ("search scope", replace_once(self.table, 'excluded = ["src/SUMMARY.md"]', 'excluded = ["src/SUMMARY.md", "src/glossary.md"]'), None, ["reference_search:table"]),
        ]
        for label, table, doc, jids in cases:
            with self.subTest(label):
                violations = self.run_inputs(table, doc).violations
                if label != "search scope":
                    self.assertEqual(self.mechanical(violations), [])
                    self.assertEqual(changed(violations), sorted(jids))
                if label == "search scope":
                    stale = self.run_inputs(table, doc, registry=self.review(jids, table, doc)).violations
                    self.found(stale, "REFERENCE: reference src/glossary.md:253 (no rule): names no unit")
                    continue
                blocks = self.run_inputs(table, doc).blocks
                regenerated = doc or self.doc
                for name, body in blocks.items():
                    regenerated = C.replace_block(regenerated, name, body)
                self.assertEqual(self.run_inputs(table, regenerated, registry=self.review(jids, table, regenerated)).violations, [])

    def test_an_amended_ld_row_needs_every_relying_row_reviewed(self):
        design = head().text(M.DESIGN_REL)
        amended = replace_once(design, "| LD-5 | Union validity | Unconstrained bytes.", "| LD-5 | Union validity | Unconstrained bytes, preserved by typed copies.")
        trees = {"design": C.DirTree(self.tmp, {M.DESIGN_REL: amended})}
        relying = sorted([f"reference:{CHAPTER}:145", f"reference:{CHAPTER}:59", "miri:tests/fail/uninit/padding-union.rs"])
        violations = self.run_inputs(trees=trees).violations
        self.assertEqual(self.mechanical(violations), [])
        self.assertEqual(changed(violations), relying)
        self.assertEqual(self.run_inputs(trees=trees, registry=self.review(relying, trees=trees)).violations, [])

    # ---- DOC
    def test_document_mutations(self):
        cases = [
            ("counts", self.doc.replace("| `.rs` files / of which with revisions / outcomes (one per revision) | 556 / 56 / 620 |", "| `.rs` files / of which with revisions / outcomes (one per revision) | 557 / 56 / 620 |"),
             "DOC: the published `ub-coverage-matrix-counts` block differs"),
            ("added-reasons block", self.doc.replace("«Mutating immutable bytes.»", "«Mutating bytes.»", 1), "DOC: the published `ub-coverage-matrix-added-reasons` block differs"),
            ("unreviewed line", replace_once(self.doc, "## Open questions\n", "## Open questions\n\nEvery question is answered.\n"), "DOC: line"),
            ("wrong quote", replace_once(self.doc, "design:870 «Their kinds are Stack, Heap, Global,»", "design:870 «Their kinds are Stack and Heap,»"), "DOC: prose:oq-4: design:870 does not contain"),
            ("bare citation", replace_once(self.doc, "(design:870 «Their kinds are Stack, Heap, Global,»)", "(design:870)"), "DOC: prose:oq-4: line citation 'design:870' is not in the checked"),
            ("unknown reason", replace_once(self.doc, "so neither raises `UbReason.DeallocKindMismatch`", "so neither raises `UbReason.DeallocKindMismatches`"), "DOC: the document names `UbReason.DeallocKindMismatches`"),
            ("pin", self.doc.replace("`68d30ebdd91e8348da4bdba4c02004a937874cc4`", "`68d30ebd`"), "DOC: the document does not record the pin `68d30ebdd91e8348da4bdba4c02004a937874cc4`"),
        ]
        for label, doc, fragment in cases:
            with self.subTest(label):
                self.assertNotEqual(doc, self.doc)
                self.found(self.run_inputs(doc=doc).violations, fragment)


if __name__ == "__main__":
    unittest.main(verbosity=1)
