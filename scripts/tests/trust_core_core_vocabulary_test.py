#!/usr/bin/env python3
"""Controls for scripts/trust_core/core_vocabulary.py (Core vocabulary v0).

* The REAL checker on the REAL inputs (the pinned MiniRust and Reference clones, this
  repository's design and rustc at HEAD, the table, the document and the review registry)
  exits 0 and publishes the counts asserted here.
* Every mutation of a temporary copy of an input makes the CHECKER report the violation it
  introduces, beside an unmutated control on the same layout. A mechanical mutation must
  name its predicate; a judgment mutation (a changed mapping, name, split or prose section)
  must pass every mechanical predicate and fail REVIEW, and must pass once a review record
  of its new digest is appended, which is what makes a judgment change visible.

The shared layers (pins, citations, uniqueness, blocks, reviews) are tested in
scripts/tests/trust_core_common_test.py. A missing source clone is a FAILURE that prints the
clone command, never a skip.

Author: Andrew Yates <andrewyates.name@gmail.com>
Copyright 2026 Andrew Yates | License: Apache-2.0 OR MIT
"""

import os as _floor_os
import shutil as _floor_shutil
import sys as _floor_sys

# Trust: python floor (scripts/tests/python_floor_test.py). This file needs tomllib (3.11+) and plain
# `python3` is 3.9 on macOS CommandLineTools, so an old interpreter re-execs here, before any import
# that needs 3.11 runs.
if __name__ == "__main__" and _floor_sys.version_info < (3, 11):
    for _floor_candidate in ("python3.14", "python3.13", "python3.12", "python3.11"):
        _floor_path = _floor_shutil.which(_floor_candidate)
        if _floor_path:
            _floor_argv = [_floor_path, _floor_os.path.abspath(__file__), *_floor_sys.argv[1:]]
            _floor_os.execv(_floor_path, _floor_argv)
    _floor_sys.exit("trust_core_core_vocabulary_test.py requires Python 3.11+ (tomllib); none found on PATH")

import importlib.util
import re
import shutil
import subprocess
import sys
import tempfile
import tomllib
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "scripts" / "trust_core" / "core_vocabulary.py"
SPEC = importlib.util.spec_from_file_location("trust_core_core_vocabulary", SCRIPT)
CV = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(CV)
C = CV.C
TABLE, DOC, REGISTRY = ROOT / CV.TABLE_REL, ROOT / CV.DOC_REL, ROOT / CV.REGISTRY_REL
CLONES = {}

# The published counts (CORE_VOCABULARY.md). A change here is a change to the vocabulary.
PUBLISHED_GROUPS = {
    "Program": (11, 0, 8, 9, 9), "Body": (6, 4, 3, 10, 1), "Place": (1, 5, 2, 0, 0), "Operand": (4, 8, 5, 0, 0),
    "Rvalue": (11, 51, 20, 0, 0), "Stmt": (1, 7, 0, 0, 0), "Terminator": (8, 34, 24, 0, 0), "Ty": (6, 15, 11, 2, 0),
    "InstEnv": (1, 0, 0, 0, 4),
}
PUBLISHED = {
    "ub_reasons": 174, "ub_extension": 22, "ub_sites": 156, "ub_distinct_messages": 151, "ub_raised_by": 94,
    "ub_intrinsic": 71, "ub_call_shape": 65, "scanned": 150, "layout_carrying": 10, "not_in_core": 9, "payload_parts": 12,
    "operators": 55, "operators_extension": 16, "operators_flavoured": 13, "mir_variants": 54, "mir_pairs": 137,
    "mir_rows": 75, "mir_renamed": 23, "mir_refusals": 2, "mir_composition": 73, "mirrored_variants": 26,
    "design_phrases": 21, "containers": (14, 3, 1), "design_words": 192, "design_function": 43, "design_outside": 20,
    "design_restriction": 10, "design_covered": 87, "design_ignored": 21, "design_phrase": 21, "design_derived": 59,
    "design_flavour": 2, "design_ub": 4, "design_ambiguous": 4, "design_item_kind": 3, "design_restrictions": 2,
    "extension_names": 124, "extension_by_consumer": 97, "extension_justified": 27, "grounds_cited": 95,
    "grounds_rule": 4, "grounds_alias": 3, "item_kinds": 15, "doc_citations": 172, "citations": 831, "wrappers": 8,
}
PUBLISHED_JUDGMENTS = 921


def setUpModule():
    pins = C.load_pins()
    try:
        CLONES.update(C.locate_clones(pins, sorted(CV.READS)))
    except C.MissingClone as error:
        raise AssertionError(str(error)) from None


def replace_once(text, old, new):
    assert text.count(old) == 1, (old, text.count(old))
    return text.replace(old, new)


# The comment block that heads the table's [[entry]] rows.
ENTRY_HEADER = ("# ----------------------------------------------------------------------------\n"
                "# One row per constructor (kind = variant) or record field (kind = field).\n"
                "# ----------------------------------------------------------------------------\n\n")


def block(text, kind, line):
    """The [[kind]] block of the table holding the exact line `line`."""
    for part in re.split(r"\n(?=\[\[)", text):
        if part.startswith(f"[[{kind}]]") and f"\n{line}\n" in part + "\n":
            return part
    raise AssertionError((kind, line))


def edit_block(text, kind, line, edit):
    old = block(text, kind, line)
    return replace_once(text, old, edit(old))


class RealInputs(unittest.TestCase):
    def test_real_inputs_pass_and_publish_the_counts(self):
        result = CV.collect()
        self.assertEqual(result.violations, [])
        self.assertEqual(result.counts["groups"], PUBLISHED_GROUPS)
        for key, value in PUBLISHED.items():
            self.assertEqual(result.counts[key], value, key)
        self.assertEqual(result.counts["reviews"]["judgments"], PUBLISHED_JUDGMENTS)
        self.assertIn("| **Syntax total** | 48 | 124 | 73 | 21 | 10 | 228 |", result.table_text)

    def test_new_cross_item_obligations_are_unimplemented_extensions(self):
        data = tomllib.loads(TABLE.read_text())
        reasons = {r["name"]: r for r in data["ub_reason"]}
        grounds = {r["name"]: r for r in data["extension_justification"]}
        for leaf, source in (
            ("ExternalStaticDeclarationMismatch", "extern_static/mut_mismatch1.stderr"),
            ("CallTrackCallerMismatch", "extern-extra-track-caller.stderr"),
            ("VariadicArgumentValueUnrepresentable", "library/core/src/ffi/va_list.rs"),
        ):
            with self.subTest(reason=leaf):
                name = "UbReason." + leaf
                row = reasons[name]
                self.assertEqual(row["origin"], "trust-extension")
                self.assertTrue(row["upstream_proposal"])
                self.assertIn("unimplemented", row["note"])
                self.assertFalse(row.get("sites"))
                self.assertTrue(any(source in c["ref"] for c in grounds[name]["cites"]))

    def test_cli_exits_zero_on_real_inputs(self):
        run = subprocess.run([sys.executable, str(SCRIPT)], capture_output=True, text=True)
        self.assertEqual(run.returncode, 0, run.stderr)
        self.assertIn(f"core_vocabulary: OK ({PUBLISHED['citations']} row citations, {PUBLISHED['doc_citations']} document citations, {PUBLISHED_JUDGMENTS} reviewed judgments)", run.stdout)

    def test_each_missing_clone_exits_two_with_its_clone_command(self):
        for flag, url in (("--minirust", "https://github.com/minirust/minirust"), ("--reference", "https://github.com/rust-lang/reference")):
            with self.subTest(flag), tempfile.TemporaryDirectory() as tmp:
                run = subprocess.run([sys.executable, str(SCRIPT), flag, str(Path(tmp) / "absent")], capture_output=True, text=True)
                self.assertEqual(run.returncode, 2)
                self.assertIn(f"git clone {url} {Path(tmp) / 'absent'}", run.stderr)


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
        options = CV.Options(table=paths["table.toml"], doc=paths["doc.md"], registry=paths["registry.toml"],
                             trees=trees or {}, check_pin_state=False, check_history=False)
        return CV.collect(options)

    def assert_violation(self, violations, *fragments):
        for fragment in fragments:
            self.assertTrue(any(fragment in v for v in violations), f"{fragment!r} not in {violations}")

    def mechanical(self, violations):
        return [v for v in violations if not v.startswith("REVIEW:") and "published `core-vocabulary-counts` block" not in v]

    def review(self, jids, table=None, doc=None, record="mutation-review"):
        """The registry with a new record's review of each judgment's current content appended."""
        f = C.Findings()
        sections = C.document_judgments(f, "DOC", doc or self.doc, generated=(CV.COUNTS_BLOCK,))
        now = CV.judgments(f, table or self.table, sections)
        text = self.registry.replace("[judgment]", f'[record.{record}]\nround = "test"\ndate = "2026-09-17"\nevidence = ["the mutation"]\nreason = "a mutation test"\n\n[judgment]')
        for jid in jids:
            line = next((l for l in text.split("\n") if l.startswith(f'"{jid}" = ')), None)
            digest = C.digest(jid, now[jid])
            if line is None:
                text = text.rstrip("\n") + f'\n"{jid}" = {{ digest = "{digest}", reviews = [["{record}", "{digest}"]] }}\n'
            else:
                old = line.split('digest = "')[1].split('"')[0]
                text = text.replace(line, line.replace(f'digest = "{old}"', f'digest = "{digest}"')[:-4] + f'], ["{record}", "{digest}"]] }}')
        return text

    def test_control_copies_pass(self):
        self.assertEqual(self.run_inputs().violations, [])

    def test_new_function_flag_is_counted_and_cannot_be_omitted(self):
        entry = block(self.table, "entry", 'name = "Body.implicit_writes"')
        self.assertIn('minirust_token = "implicit_writes"', entry)
        result = self.run_inputs(table=self.table.replace(entry, "", 1))
        self.assert_violation(self.mechanical(result.violations),
                              "Function::implicit_writes", "is claimed 0 times")

    def test_box_deref_transmute_keeps_its_separate_validity_refusal(self):
        operator = block(self.table, "mir_operator", 'mir = "CastKind::BoxDerefTransmute"')
        self.assertIn('maps_to = []', operator)
        self.assertIn('refusal = "BoxDerefValidityUnsupported"', operator)
        forged = operator.replace('maps_to = []', 'maps_to = ["CastOp.Transmute"]')
        forged = forged.replace('refusal = "BoxDerefValidityUnsupported"', 'op = "CastOp.Transmute"')
        result = self.run_inputs(table=self.table.replace(operator, forged, 1))
        self.assert_violation(self.mechanical(result.violations),
                              "BoxDerefTransmute", "not CastOp.Transmute")

    # ---- the round-5 findings
    def test_s31_split_claims_and_swapped_minirust_refs_fail_only_review(self):
        table = edit_block(self.table, "inductive", 'name = "Program"', lambda b: b + 'minirust_split_from = "Function"\n')
        table = edit_block(table, "inductive", 'name = "Body"', lambda b: b + 'minirust_split_from = "Program"\n')
        start, body_start = block(table, "entry", 'name = "Program.start"'), block(table, "entry", 'name = "Body.start"')
        ref_a = re.search(r'minirust_ref = "[^"]+"', start).group(0)
        ref_b = re.search(r'minirust_ref = "[^"]+"', body_start).group(0)
        table = replace_once(table, start, start.replace(ref_a, ref_b))
        table = replace_once(table, body_start, body_start.replace(ref_b, ref_a))
        violations = self.run_inputs(table).violations
        self.assertEqual(self.mechanical(violations), [])
        changed = ["inductive:Program", "inductive:Body", "entry:Program.start", "entry:Body.start"]
        for jid in changed:
            self.assert_violation(violations, f"REVIEW: judgment {jid}: its content changed")
        self.assertEqual(len([v for v in violations if v.startswith("REVIEW:")]), 4)
        self.assertEqual(self.run_inputs(table, registry=self.review(changed, table)).violations, [])

    def test_s23_s24_s26_false_split_claims_fail(self):
        for name, split in (("Config", "ValueExpr"), ("UbReason", "Statement"), ("Program", "Function")):
            with self.subTest(name):
                table = edit_block(self.table, "inductive", f'name = "{name}"', lambda b: b + f'minirust_split_from = "{split}"\n')
                violations = self.run_inputs(table).violations
                self.assert_violation(violations, f"REVIEW: judgment inductive:{name}: its content changed")

    def test_s1_s12_a_ub_inductive_that_is_a_record_fails_mechanically(self):
        for name in ("UbReason", "TreeBorrowsUb"):
            with self.subTest(name):
                table = edit_block(self.table, "inductive", f'name = "{name}"', lambda b: b.replace('shape = "enum"', 'shape = "record"'))
                violations = self.run_inputs(table, registry=self.review([f"inductive:{name}"], table)).violations
                self.assert_violation(violations, f"NAME: inductive {name}: a UB inductive's reasons are UpperCamel variants, so it is an enum, not a record",
                                      f"NAME: ub_reason {name}.")

    def test_u6_u7_u8_ub_renames_fail_only_review(self):
        for old, new in (("UbReason.DerefWithoutProvenance", "UbReason.PointerWithoutProvenance"),
                         ("UbReason.AssumeViolated", "UbReason.AssumeCalled"),
                         ("UbReason.DivExactRemainder", "UbReason.ExactDivision")):
            with self.subTest(old):
                table = replace_once(self.table, f'name = "{old}"\n', f'name = "{new}"\n')
                violations = self.run_inputs(table).violations
                self.assertEqual(self.mechanical(violations), [])
                self.assert_violation(violations, f"REVIEW: judgment ub_reason:{old}: is registered, but no such judgment exists",
                                      f"REVIEW: judgment ub_reason:{new} is not registered")

    # ---- mechanical predicates
    def test_completeness_citations_and_table_shape(self):
        cases = [
            ("COMPLETENESS", edit_block(self.table, "entry", 'name = "IntBinOp.AddUnchecked"', lambda b: ""),
             "COMPLETENESS: MiniRust IntBinOp::AddUnchecked (variant, spec/lang/syntax.md:141) is claimed 0 times"),
            ("RUSTC-REF", replace_once(self.table, '{ ref = "compiler/rustc_target/src/spec/mod.rs:820", token = "PanicStrategy" },\n]\nupstream_proposal = true\n\n[[inductive]]\nname = "Edition"',
                                       '{ ref = "compiler/rustc_target/src/spec/mod.rs:819", token = "PanicStrategy" },\n]\nupstream_proposal = true\n\n[[inductive]]\nname = "Edition"'),
             "RUSTC-REF: inductive PanicStrategy: rustc:compiler/rustc_target/src/spec/mod.rs:819 does not contain the word 'PanicStrategy'"),
            ("MINIRUST-REF", edit_block(self.table, "entry", 'name = "Program.start"', lambda b: re.sub(r'minirust_ref = "spec/lang/syntax.md:(\d+)"', lambda m: f'minirust_ref = "spec/lang/syntax.md:{int(m.group(1)) + 1}"', b)),
             "MINIRUST-REF: entry Program.start: minirust:spec/lang/syntax.md:"),
            ("DESIGN-PHRASE", replace_once(self.table, 'quote = "The locals of this function, and their type."', 'quote = "The locals of this function, and their types."'),
             "DESIGN-PHRASE: design_phrase 843 typed locals: minirust:spec/lang/syntax.md:477 does not contain"),
            ("TABLE duplicate", self.table.replace("[[entry]]\nname = \"Ty.Str\"", "[[entry]]\nname = \"Ty.Str\"\nkind = \"variant\"\norigin = \"trust-extension\"\nphases = [\"Built\", \"Promoted\", \"Runtime\"]\nupstream_proposal = true\n\n[[entry]]\nname = \"Ty.Str\"", 1),
             "TABLE: entry[", ),
            ("TABLE unknown key", edit_block(self.table, "entry", 'name = "Ty.Str"', lambda b: b + 'alias = "Str"\n'), "unknown keys ['alias']"),
            ("TABLE free text", edit_block(self.table, "not_in_core", 'minirust_token = "Tuple"', lambda b: b.replace('reason = "', 'reason = "see types.md:31. ')),
             "reason carries an unchecked line citation"),
            ("TABLE repeated element", edit_block(self.table, "mir_operator", 'mir = "BinOp::Add"', lambda b: b.replace('operand = ["Int", "Uint"]', 'operand = ["Int", "Uint", "Int"]', 1)),
             "TABLE: mir_operator[0] BinOp::Add Int,Uint,Int: operand repeats 'Int'"),
        ]
        for label, table, fragment in cases:
            with self.subTest(label):
                self.assert_violation(self.run_inputs(table).violations, fragment)

    def test_wrappers_libspecr_enums_not_layout_and_the_adopted_rule(self):
        """Decisions 18 and 19: each rule fails on a mutated copy of the table."""
        stale = self.table.replace("[[not_layout]]", '[[not_layout]]\nminirust_ref = "spec/lang/types.md:95"\nminirust_token = "signed"\n'
                                   'cites = [\n  { ref = "minirust:spec/lang/types.md:95", quote = "pub signed: Signedness," },\n]\nwhy = "stale"\n\n[[not_layout]]', 1)
        cases = [
            ("wrapper missing", edit_block(self.table, "inductive", 'name = "LocalName"', lambda b: ""),
             "COMPLETENESS: MiniRust wrapper `LocalName` (spec/lang/syntax.md:472) is claimed by []"),
            ("wrapper citing a braced struct", edit_block(self.table, "inductive", 'name = "BbName"', lambda b: b.replace("spec/lang/syntax.md:473", "spec/lang/syntax.md:496").replace('minirust_token = "BbName"', 'minirust_token = "BasicBlock"')),
             "MINIRUST-REF: inductive BbName: spec/lang/syntax.md:496 does not define `BasicBlock` as a one-field tuple struct of Name or an alias of Int"),
            ("wrapper with an entry", self.table.replace('[[entry]]\nname = "IntType.signed"', '[[entry]]\nname = "LocalName.name"\nkind = "field"\norigin = "trust-extension"\nphases = ["Built", "Promoted", "Runtime"]\nupstream_proposal = true\n\n[[entry]]\nname = "IntType.signed"', 1),
             "NAME: entry LocalName.name: a field is a lower_snake leaf of a record inductive"),
            ("exemption removed", edit_block(self.table, "not_layout", 'minirust_token = "size"', lambda b: ""),
             "LAYOUT: MiniRust IntType::size (spec/lang/types.md:96) carries layout but is a Core entry"),
            ("stale exemption", stale, "LAYOUT: not_layout spec/lang/types.md:95 signed: is no scanned MiniRust part whose payload names a layout type (stale)"),
            ("libspecr variant without its path", edit_block(self.table, "entry", 'name = "Signedness.Unsigned"', lambda b: b.replace("spec/lang/types.md:300", "spec/lang/representation.md:116")),
             "MINIRUST-REF: entry Signedness.Unsigned: a variant of the libspecr enum Signedness cites a line writing `Signedness::Unsigned`"),
            ("libspecr pin", self.table.replace('quote = "version = \\"0.1.41\\""', 'quote = "version = \\"0.1.40\\""', 1),
             "MINIRUST-REF: inductive Signedness libspecr_refs: minirust:tooling/Cargo.lock:428 does not contain"),
            ("libspecr enum as a record", edit_block(self.table, "inductive", 'name = "Mutability"', lambda b: b.replace('shape = "enum"', 'shape = "record"')),
             "NAME: inductive Mutability: a libspecr-defined inductive is an enum"),
            ("adopted rule", replace_once(self.table, 'prefix = "minirust::"\n', ""), "TABLE: [adopted] holds exactly a prefix, a note and design_refs"),
        ]
        for label, table, fragment in cases:
            with self.subTest(label):
                self.assertNotEqual(table, self.table)
                self.assert_violation(self.run_inputs(table).violations, fragment)

    def test_names_origins_and_extensions(self):
        cases = [
            ("NAME", edit_block(self.table, "entry", 'name = "Ty.Str"', lambda b: b.replace('name = "Ty.Str"', 'name = "Tyy.Str"')), "NAME: entry Tyy.Str: a name is <Inductive>.<Leaf> of a declared inductive"),
            ("ORIGIN", edit_block(self.table, "entry", 'name = "Ty.Str"', lambda b: b.replace("upstream_proposal = true\n", "")), "ORIGIN: entry Ty.Str: a trust-extension row sets upstream_proposal = true"),
            ("RENAME", edit_block(self.table, "entry", 'name = "BbKind.Regular"', lambda b: b.replace('name = "BbKind.Regular"', 'name = "BbKind.Normal"')), "RENAME: entry BbKind.Normal: renames MiniRust `Regular` to `Normal`"),
            ("EXT-NAME", edit_block(self.table, "extension_alias", 'name = "Program.adts"', lambda b: ""), "EXT-NAME: entry Program.adts: `adts` is no cited rustc token"),
            ("REQUIRED", self.table.replace("[[extension_justification]]", '[[extension_justification]]\nname = "Ty.Str"\ncites = [\n  { ref = "design:862", quote = "`str`" },\n]\nwhy = "stale"\n\n[[extension_justification]]', 1),
             "REQUIRED: extension_justification Ty.Str: a consumer already requires it (stale)"),
            ("LAYOUT", edit_block(self.table, "layout_home", 'definition = "VTable"', lambda b: b.replace('home = "InstEnv.vtable_layout"', 'home = "InstEnv.layout_of"')), "LAYOUT: not_in_core spec/lang/syntax.md:"),
            ("PHASE", edit_block(self.table, "entry", 'name = "Terminator.Drop"', lambda b: b.replace('phases = ["Built", "Promoted"]', 'phases = ["Built", "Promoted", "Runtime"]')), "PHASE: entry Terminator.Drop: phases ['Built', 'Promoted', 'Runtime'] but the design restricts it to ['Built', 'Promoted']"),
            ("DEFERRED", edit_block(self.table, "deferred_check", 'id = "coroutine-terminators"', lambda b: b.replace('checked_by = ["E2.3.1"]', 'checked_by = ["E2.3.1", "E1.2.5"]')), "DEFERRED: deferred_check coroutine-terminators: checked_by 'E1.2.5' is an exit id quoted"),
        ]
        for label, table, fragment in cases:
            with self.subTest(label):
                self.assert_violation(self.run_inputs(table).violations, fragment)

    def test_ub_operators_mir_and_design_items(self):
        cases = [
            ("UB-SITE message", replace_once(self.table, 'message = "overflow in unchecked add" }', 'message = "overflow in unchecked addition" }'),
             "raises 'overflow in unchecked add', the table says 'overflow in unchecked addition'"),
            ("UB-SITE unclaimed", edit_block(self.table, "ub_reason", 'name = "UbReason.InvalidFnPointer"', lambda b: ""), "UB-SITE: MiniRust UB at spec/lang/machine.md:335 ('invalid pointer for function lookup') is claimed by [], not exactly one reason"),
            ("OPERATOR", edit_block(self.table, "operator", 'name = "FloatBinOp.Add"', lambda b: b.replace('classes = ["Float"]', 'classes = ["Float", "Int"]')), "OPERATOR: operator FloatBinOp.Add: admits Float together with other classes"),
            ("MIR-OPERATOR family", edit_block(self.table, "mir_operator", 'mir = "BinOp::Div"', lambda b: b.replace("IntBinOp.Div", "IntBinOp.Rem")), "MIR-OPERATOR: mir_operator BinOp::Div Int,Uint: BinOp::Div over Int is the leaf named Div"),
            ("MIR-OPERATOR missing", edit_block(self.table, "mir_operator", 'mir = "BinOp::Shl"', lambda b: ""), "MIR-OPERATOR: BinOp::Shl has no mir_operator row"),
            ("COMPOSITION", edit_block(self.table, "mir_operator", 'mir = "BinOp::Sub"', lambda b: b.replace('"BinOp.Int", "IntBinOp.Sub"', '"BinOp.Float", "IntBinOp.Sub"', 1)), "COMPOSITION: mir_operator BinOp::Sub Int,Uint: maps_to must be exactly"),
            ("DESIGN-SYNTAX", edit_block(self.table, "design_item", "line = 845\ntoken = \"Deref\"", lambda b: b.replace('covered_by = ["Place.Deref"]', 'covered_by = ["Place.Field"]')), "DESIGN-SYNTAX: design_item 845 'Deref': its construct words name exactly ['Place.Deref']"),
            ("ITEMS", edit_block(self.table, "item_kind", 'kind = "Union"', lambda b: ""), "ITEMS: item kind Union: the Reference has it and no item_kind classifies it"),
            ("FAMILY", self.table.replace('[[entry]]\nname = "IntBinOp.Add"\n', '[[entry]]\nname = "IntBinOp.Pow"\nkind = "variant"\norigin = "trust-extension"\nphases = ["Built", "Promoted", "Runtime"]\nrustc_refs = [\n  { ref = "compiler/rustc_middle/src/mir/syntax.rs:1366", token = "Use" },\n]\nupstream_proposal = true\n\n[[entry]]\nname = "IntBinOp.Add"\n', 1),
             "FAMILY: IntBinOp.Pow: MiniRust's IntBinOp implements MIR operators by name, so its leaves are MiniRust's"),
            ("UB-SITE inductive", replace_once(self.table, 'name = "UbReason.InvalidFnPointer"\n', 'name = "TreeBorrowsUb.InvalidFnPointer"\n'),
             "UB-SITE: ub_reason TreeBorrowsUb.InvalidFnPointer: its sites (['spec/lang/machine.md']) make it a UbReason reason, not a TreeBorrowsUb reason"),
            ("UB-MECHANISM", edit_block(self.table, "ub_mechanism", 'role = "macro"', lambda b: b.replace('role = "macro"', 'role = "helper"')), "UB-MECHANISM: exactly one ub_mechanism has role 'macro'"),
        ]
        for label, table, fragment in cases:
            with self.subTest(label):
                self.assert_violation(self.run_inputs(table).violations, fragment)

    def test_source_mutations_fail_on_copies(self):
        minirust = self.tmp / "minirust"
        shutil.copytree(CLONES["minirust"], minirust, ignore=shutil.ignore_patterns(".git"))
        self.assertEqual(self.run_inputs(trees={"minirust": C.DirTree(minirust)}).violations, [])  # control
        syntax = minirust / "spec/lang/syntax.md"
        text = syntax.read_text(encoding="utf-8")
        syntax.write_text(replace_once(text, "    Cleanup,\n", "    Cleanup,\n    Warm,\n"), encoding="utf-8")
        self.assert_violation(self.run_inputs(trees={"minirust": C.DirTree(minirust)}).violations, "COMPLETENESS: MiniRust BbKind::Warm (variant")
        syntax.write_text(text, encoding="utf-8")
        ops = minirust / "spec/lang/step/operators.md"
        ops_text = ops.read_text(encoding="utf-8")
        ops.write_text(replace_once(ops_text, 'throw_ub!("overflow in unchecked add");', 'throw_ub!["overflow in unchecked add"];'), encoding="utf-8")
        self.assert_violation(self.run_inputs(trees={"minirust": C.DirTree(minirust)}).violations, "throw_ub! is not a parenthesized literal message")
        syntax_rs = C.GitTree(ROOT, "HEAD").text(CV.RUSTC_MIR_SYNTAX)
        self.assertEqual(self.run_inputs(trees={"worktree": C.DirTree(ROOT, {CV.RUSTC_MIR_SYNTAX: syntax_rs})}).violations, [])  # control
        worktree = C.DirTree(ROOT, {CV.RUSTC_MIR_SYNTAX: replace_once(syntax_rs, "    Continue,\n", "    Continue,\n    Retry,\n")})
        self.assert_violation(self.run_inputs(trees={"worktree": worktree}).violations, "MIRRORED: rustc UnwindAction::Retry")
        # A `Trust:` edit inside an enumerated enum that changes no variant (a mirrored enum,
        # then a MIR enum) is refused as not the upstream text, and so is every citation of
        # the file outside the regions still verified (what those citations grounded fails too).
        for enum, old in (("UnwindAction", "    /// No action is to be taken. Continue unwinding.\n"),
                          ("BinOp", "    /// The `+` operator (addition)\n")):
            with self.subTest(enum):
                marked = replace_once(syntax_rs, old, old.replace("///", "// Trust:"))
                line = marked[:marked.index("// Trust:")].count("\n") + 1
                violations = self.run_inputs(trees={"worktree": C.DirTree(ROOT, {CV.RUSTC_MIR_SYNTAX: marked})}).violations
                self.assertEqual(violations[0], f"PIN: {CV.RUSTC_MIR_SYNTAX}: the parsed region of enum {enum} carries a `Trust:` edit (line {line}), so it is not the pinned upstream text")
                pins = [v for v in violations if v.startswith("PIN:")]
                self.assertGreater(len(pins), 1)
                self.assertTrue(all(f"carries a `Trust:` edit (line {line})" in v for v in pins))
        reference = self.tmp / "reference"
        shutil.copytree(CLONES["rust-reference"], reference, ignore=shutil.ignore_patterns(".git"))
        items = reference / "src/items.md"
        items.write_text(replace_once(items.read_text(encoding="utf-8"), "    | Union\n", "    | Union\n    | Record\n"), encoding="utf-8")
        self.assert_violation(self.run_inputs(trees={"reference": C.DirTree(reference)}).violations, "ITEMS: item kind Record: the Reference has it")

    def test_citations_of_trust_marked_rustc_fail_pin(self):
        """The verifier's three attacks on the round-18 guard, each beside a control that passes."""
        syntax_rs = C.GitTree(ROOT, "HEAD").text(CV.RUSTC_MIR_SYNTAX)
        lines = syntax_rs.split("\n")

        def worktree(edits):
            out = list(lines)
            for number, (old, new) in edits.items():
                self.assertEqual(out[number - 1], old)
                out[number - 1] = new
            return {"worktree": C.DirTree(ROOT, {CV.RUSTC_MIR_SYNTAX: "\n".join(out)})}

        def pins(violations):
            return [v for v in violations if v.startswith("PIN:")]

        # 1. A marked Trust edit rewrites cited line 1026, keeping its quoted words, with the
        #    marker on the line above.
        reworded = {1026: ("/// The reason we are terminating the process during unwinding.",
                           "/// The reason we are terminating the process during unwinding. Trust builds also use it for aborts.")}
        self.assertEqual(self.run_inputs(trees=worktree(reworded)).violations, [])  # control: no marker
        marked = {**reworded, 1025: ("", "// Trust: the terminate reason now also covers aborts on a failed proof")}
        found = pins(self.run_inputs(trees=worktree(marked)).violations)
        self.assert_violation(found, f"PIN: {CV.RUSTC_MIR_SYNTAX}: the parsed region of enum UnwindTerminateReason carries a `Trust:` edit (line 1025)",
                              f"PIN: design_phrase 858 Terminate reason: rustc:{CV.RUSTC_MIR_SYNTAX}:1026: {CV.RUSTC_MIR_SYNTAX} carries a `Trust:` edit (line 1025)")

        # 2. A marked Trust edit adds UnwindAction::Abort, with the marker in the doc comment above
        #    the enum, and an entry cites the new variant (reviewed, so only the marker can fail).
        added = {1012: ("    ///", "    Abort,")}
        table = self.table.replace('[[entry]]\nname = "UnwindAction.Continue"\n',
                                   '[[entry]]\nname = "UnwindAction.Abort"\nkind = "variant"\norigin = "trust-extension"\nphases = ["Built", "Promoted", "Runtime"]\n'
                                   f'rustc_refs = [\n  {{ ref = "{CV.RUSTC_MIR_SYNTAX}:1012", token = "Abort" }},\n]\nupstream_proposal = true\n\n'
                                   '[[entry]]\nname = "UnwindAction.Continue"\n', 1)
        self.assertNotEqual(table, self.table)
        registry = self.review(["entry:UnwindAction.Abort"], table)
        control = self.run_inputs(table, registry=registry, trees=worktree(added)).violations
        self.assertEqual(pins(control), [])  # control: no marker
        self.assertEqual(self.mechanical(control), [])
        found = pins(self.run_inputs(table, registry=registry, trees=worktree({**added, 1007: ("/// Action to be taken when a stack unwind happens.",
                                                                                          "/// Action to be taken when a stack unwind happens. // Trust: adds Abort")})).violations)
        self.assert_violation(found, f"PIN: {CV.RUSTC_MIR_SYNTAX}: the parsed region of enum UnwindAction carries a `Trust:` edit (line 1007)",
                              f"PIN: entry UnwindAction.Abort: rustc:{CV.RUSTC_MIR_SYNTAX}:1012: {CV.RUSTC_MIR_SYNTAX} carries a `Trust:` edit (line 1007)")

        # 3. A row cites validate.rs:127, a field Trust added under the marker at line 124.
        def edition_ref(ref, token):
            return edit_block(self.table, "inductive", 'name = "Edition"', lambda b: b.replace(
                '  { ref = "compiler/rustc_span/src/edition.rs:9", token = "Edition" },\n',
                f'  {{ ref = "compiler/rustc_span/src/edition.rs:9", token = "Edition" }},\n  {{ ref = "{ref}", token = "{token}" }},\n'))
        for label, table, expected in (
            ("control: an unmarked file", edition_ref(f"{CV.RUSTC_MIR_SYNTAX}:1366", "Use"), None),
            ("Trust-added validate.rs:127", edition_ref("compiler/rustc_mir_transform/src/validate.rs:127", "locals_with_def"),
             "PIN: inductive Edition: rustc:compiler/rustc_mir_transform/src/validate.rs:127: compiler/rustc_mir_transform/src/validate.rs carries a `Trust:` edit (line 124)"),
        ):
            with self.subTest(label):
                violations = self.run_inputs(table, registry=self.review(["inductive:Edition"], table)).violations
                if expected is None:
                    self.assertEqual(violations, [])
                else:
                    self.assertEqual(len(violations), 1)
                    self.assert_violation(violations, expected)

    def test_design_mutations_fail(self):
        design = C.GitTree(ROOT, "HEAD").text(CV.DESIGN_REL)
        self.assertEqual(self.run_inputs(trees={"design": C.DirTree(self.tmp, {CV.DESIGN_REL: design})}).violations, [])  # control
        for label, mutated, fragment in (
            ("new construct word", replace_once(design, "`Deinit`, `StorageLive`, `StorageDead`", "`Deinit`, `Nop`, `StorageLive`, `StorageDead`"),
             "DESIGN-SYNTAX: design line 853 word 'Nop' lies in no design_item"),
            ("dropped phase restriction", replace_once(design, "Terminate reason, Cleanup bb}`, and adds `TailCall`, `Drop` (phases Built and",
                                                       "Terminate reason, Cleanup bb}`, and adds `TailCall`, `Drop` (phase  Built and"),
             "PHASE: entry Terminator.Drop: phases ['Built', 'Promoted'] but the design states no restriction for it"),
        ):
            with self.subTest(label):
                self.assert_violation(self.run_inputs(trees={"design": C.DirTree(self.tmp, {CV.DESIGN_REL: mutated})}).violations, fragment)

    def test_stale_and_empty_rows_fail_mechanically(self):
        cases = [
            ("design_flavour", self.table + '\n[[design_flavour]]\nphrase = "saturates"\nrequires = { overflow = ["not-ub"] }\n',
             "DESIGN-SYNTAX: design_flavour 'saturates': no word or design_item of the Syntax list uses it (stale)"),
            ("design_ub_phrase", self.table + '\n[[design_ub_phrase]]\nphrase = "is never UB"\nfollows = "operator"\nrequires = { overflow = ["not-ub"] }\n',
             "DESIGN-SYNTAX: design_ub_phrase 'is never UB': no word or design_item of the Syntax list uses it (stale)"),
            ("design_keyword", self.table + '\n[[design_keyword]]\nword = "impl"\nleaf = "TraitObject"\ncite = { ref = "minirust:spec/lang/types.md:90", quote = "A `dyn TraitName`." }\n',
             "DESIGN-SYNTAX: design_keyword 'impl': no word or design_item of the Syntax list uses it (stale)"),
            ("function word", replace_once(self.table, 'function_words = ["a", "an",', 'function_words = ["a", "about", "an",'),
             "DESIGN-SYNTAX: function word 'about': no word or design_item of the Syntax list uses it (stale)"),
            ("mir_family unused", self.table + '\n[[mir_family]]\nenum = "Operand"\noperands = "float"\ninductives = ["Operand"]\n',
             "FAMILY: mir_family Operand float: Operand implements no MIR row by name"),
            ("mir_family unused element", replace_once(self.table, 'inductives = ["CastOp", "IntrinsicOp"]', 'inductives = ["CastOp", "IntrinsicOp", "RelOp"]'),
             "FAMILY: mir_family CastKind other: RelOp implements no MIR row by name"),
            ("mir_family empty", self.table + '\n[[mir_family]]\nenum = "Operand"\noperands = "float"\ninductives = []\n',
             "TABLE: mir_family[8] Operand float: inductives is empty"),
            ("deferred_check empty", edit_block(self.table, "deferred_check", 'id = "coroutine-terminators"', lambda b: re.sub(r"checked_by = \[[^\]]*\]", "checked_by = []", re.sub(r"fields = \[[^\]]*\]", "fields = []", b))),
             "TABLE: deferred_check[4] coroutine-terminators: checked_by is empty"),
            ("ub_mechanism role", self.table + '\n[[ub_mechanism]]\nref = "spec/prelude/main.md:44"\ntext = "($($tt:tt)*) => {"\nrole = "other"\n',
             "UB-MECHANISM: ub_mechanism spec/prelude/main.md:44: role 'other' is not one of"),
            ("mirrored UB phrase requirements", replace_once(self.table, 'follows = "mirrored"\nrequires = {  }', 'follows = "mirrored"\nrequires = { overflow = ["ub"] }'),
             "DESIGN-SYNTAX: design phrase 'unwinding with none is UB': follows an operator with requirements"),
            ("flavour requirement type", replace_once(self.table, 'phrase = "wraps"\nrequires = { overflow = ["not-ub"]', 'phrase = "wraps"\nrequires = { overflow = "not-ub"'),
             "DESIGN-SYNTAX: design phrase 'wraps': follows an operator with requirements"),
        ]
        for label, table, fragment in cases:
            with self.subTest(label):
                self.assertIn(fragment.split(":")[0], {v.split(":")[0] for v in self.mechanical(self.run_inputs(table).violations)})
                self.assert_violation(self.run_inputs(table).violations, fragment)

    def test_judgment_text_outside_rows_and_sections_fails_review_or_doc(self):
        # A heading, a new `#` line, a moved section and a table comment are judgments (the outline, the
        # table's comments): each fails REVIEW only, and passes once a new record reviews it.
        for label, table, doc, jid in (
            ("heading", None, replace_once(self.doc, "## Open questions\n", "## Open questions (all resolved; no action needed)\n"), "outline:document"),
            ("hash line", None, replace_once(self.doc, "## Open questions\n", "## Open questions\n\n# NOTE: every owner question below was answered.\n"), "outline:document"),
            # A section moved under another heading: `## Limitations` above OQ-15 puts OQ-15 to OQ-18 under it.
            ("section moved", None, replace_once(replace_once(self.doc, "<!-- /reviewed:prose:oq-18 -->\n\n## Limitations\n", "<!-- /reviewed:prose:oq-18 -->\n"),
                                                 "<!-- reviewed:prose:oq-15 -->\n", "## Limitations\n\n<!-- reviewed:prose:oq-15 -->\n"), "outline:document"),
            ("table comment", replace_once(self.table, 'schema = "trust.core.vocabulary.v1"', '# OWNER DECISION: OQ-3 is closed.\nschema = "trust.core.vocabulary.v1"'), None, "comments:table"),
            # A comment moved to head other rows: the entry rows' header above the last inductive row.
            ("table comment moved", replace_once(replace_once(self.table, ENTRY_HEADER, ""), '[[inductive]]\nname = "TreeBorrowsUb"\n', ENTRY_HEADER + '[[inductive]]\nname = "TreeBorrowsUb"\n'),
             None, "comments:table"),
        ):
            with self.subTest(label):
                violations = self.run_inputs(table, doc).violations
                self.assertEqual(self.mechanical(violations), [])
                self.assertEqual([v for v in violations if v.startswith("REVIEW:")], [v for v in violations if v.startswith(f"REVIEW: judgment {jid}: its content changed")])
                self.assertEqual(len(violations), 1)
                self.assertEqual(self.run_inputs(table, doc, registry=self.review([jid], table, doc)).violations, [])
        # A marker-shaped comment outside a section, and a section under a row's id, fail DOC.
        for label, doc, fragment in (
            ("marker-shaped comment", replace_once(self.doc, "## Open questions\n", "## Open questions\n\n<!-- note:begin the owner approved every decision -->\n"), "DOC: line"),
            ("row id section", replace_once(self.doc, "## Open questions\n", "## Open questions\n\n<!-- reviewed:entry:Program.start -->\nA note.\n<!-- /reviewed:entry:Program.start -->\n"),
             "section entry:Program.start is not a `prose:` section"),
        ):
            with self.subTest(label):
                violations = self.run_inputs(doc=doc).violations
                self.assert_violation(violations, fragment)
                self.assert_violation(self.run_inputs(doc=doc, registry=self.review([], doc=doc)).violations, fragment)
        doc = replace_once(self.doc, "## Open questions\n", "## Open questions\n\n<!-- reviewed:entry:Program.start -->\nA note.\n<!-- /reviewed:entry:Program.start -->\n")
        self.assert_violation(self.run_inputs(doc=doc).violations, "REVIEW: judgment id entry:Program.start is produced twice")

    # ---- the document
    def test_document_mutations(self):
        cases = [
            ("counts", replace_once(self.doc, "| **Syntax total** | 48 |", "| **Syntax total** | 49 |"), "DOC: the published `core-vocabulary-counts` block differs"),
            ("unchecked citation", replace_once(self.doc, "  and `Ty` (design:840 «", "  and `Ty` (see design:840) (design:840 «"), "line citation 'design:840' is not in the checked"),
            ("quote drift", replace_once(self.doc, "design:840 «*Syntax*, as first-order Clean inductives:»", "design:840 «*Syntax*, as first-order Lean inductives:»"), "DOC: prose:naming-scheme: design:840 does not contain"),
            ("unknown name", replace_once(self.doc, "for example\n  `Body.phase`.", "for example\n  `Body.stage`."), "DOC: the document names `Body.stage`, which is not in the vocabulary"),
            ("unreviewed prose", replace_once(self.doc, "## Open questions\n", "## Open questions\n\nAn unreviewed ruling.\n"), "DOC: line"),
            ("pin", self.doc.replace("`d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed`", "`d821c6e3`"), "DOC: the document does not record the pin `d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed`"),
        ]
        for label, doc, fragment in cases:
            with self.subTest(label):
                self.assert_violation(self.run_inputs(doc=doc).violations, fragment)

    def test_a_changed_prose_section_fails_only_review_until_reviewed(self):
        doc = replace_once(self.doc, "v0 keeps the four leaves. A boolean decided later would remove two names.",
                           "v0 keeps the four leaves.")
        violations = self.run_inputs(doc=doc).violations
        self.assertEqual(self.mechanical(violations), [])
        self.assert_violation(violations, "REVIEW: judgment prose:oq-1: its content changed")
        self.assertEqual(self.run_inputs(doc=doc, registry=self.review(["prose:oq-1"], doc=doc)).violations, [])


if __name__ == "__main__":
    unittest.main(verbosity=1)
