#!/usr/bin/env python3
"""Controls for scripts/trust_core/minirust_baseline.py (D0.6, design exit E0.8b).

* The REAL checker on the REAL inputs (the pinned MiniRust and Reference clones, this repository's
  design, vocabulary and rustc at HEAD, the table, the document and the review registry with its
  committed history) exits 0 and publishes the counts asserted here.
* Every mutation of a temporary copy of an input makes the CHECKER report the violation it
  introduces, beside an unmutated control. A mechanical mutation names its predicate; a judgment
  mutation (a changed row, external row, prose section, heading or table comment) passes every
  mechanical predicate, fails REVIEW, and passes once a review record of its new digest is
  appended, which is what makes a judgment change visible.
* Every run, real or mutated, publishes a universe table whose rows add up and whose Unmapped column
  is exactly its UNMAPPED violations (exit E0.8b cannot pass with a non-zero column).

The shared layers (pins, citations, uniqueness, blocks, reviews and their history) are tested in
scripts/tests/trust_core_common_test.py. A missing source clone is a FAILURE that prints the clone
command, never a skip.

Author: Andrew Yates <andrewyates.name@gmail.com>
Copyright 2026 Andrew Yates | License: Apache-2.0 OR MIT
"""

import importlib.util
import re
import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "scripts" / "trust_core" / "minirust_baseline.py"
SPEC = importlib.util.spec_from_file_location("trust_core_minirust_baseline", SCRIPT)
MB = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MB)
C = MB.C
TABLE, DOC, REGISTRY, VOCABULARY, DECISIONS = (ROOT / rel for rel in (MB.TABLE_REL, MB.DOC_REL, MB.REGISTRY_REL, MB.VOCABULARY_REL, MB.DECISIONS_REL))
CLONES = {}

# The published counts (MINIRUST_BASELINE.md). A change here is a change to the published baseline.
PUBLISHED = {'members.def.syntax': 45,
 'members.variant.syntax': 141,
 'members.field.syntax': 44,
 'members.def.domain': 47,
 'members.variant.domain': 53,
 'members.field.domain': 56,
 'members.fn.operation': 210,
 'members.assoc-type.operation': 12,
 'members.assoc-const.operation': 12,
 'members.macro.operation': 7,
 'members.fn.derived-case': 81,
 'members.fn.derived-dispatcher': 9,
 'mapped.syntax': 230,
 'mapped.domain': 156,
 'mapped.operation': 241,
 'mapped.derived-case': 81,
 'mapped.derived-dispatcher': 9,
 'mapped.extensions': 131,
 'ub-sites': 156,
 'ub-sites.claimed': 8,
 'ub-sites.derived': 148,
 'ub-sites.inside-divergence': 62,
 'ub-sites.kept': 56,
 'extensions': 124,
 'design-extensions': 7,
 'unmapped': 0,
 'unmapped.syntax': 0,
 'unmapped.domain': 0,
 'unmapped.operation': 0,
 'unmapped.derived-case': 0,
 'unmapped.derived-dispatcher': 0,
 'unmapped.ub': 0,
 'unmapped.extensions': 0,
 'rows.core': 33,
 'rows.trust-extends': 25,
 'rows.trust-restricts': 1,
 'rows.trust-differs': 23,
 'members.trust-extends': 142,
 'members.trust-restricts': 10,
 'members.trust-differs': 210,
 'core.members': 404,
 'core.adopted': 237,
 'rows.upstream-proposal': 42,
 'rows.LD-1': 3,
 'rows.LD-3': None,
 'rows.LD-4': 1,
 'rows.LD-8': 1,
 'rows.LD-10': 1,
 'rows.LD-12': 1,
 'rulings.rows-resting': 9,
 'rulings.rejustified': 0,
 'files': 27,
 'fences.rust': 141,
 'fences.other': 1,
 'doc-citations': 25}
PUBLISHED_JUDGMENTS = 145


def setUpModule():
    try:
        CLONES.update(C.locate_clones(C.load_pins(), sorted(MB.READS)))
    except C.MissingClone as error:
        raise AssertionError(str(error)) from None


def replace_once(text, old, new):
    assert text.count(old) == 1, (old, text.count(old))
    return text.replace(old, new)


def unmapped_column(test, result):
    """The published universe table adds up row by row, and its Unmapped column is exactly the
    UNMAPPED violations: a published unmapped count can never pass (the defect the verification of
    ef745c6037 reproduced). Returns the published total."""
    lines = result.counts_text.split("\n\n")[0].split("\n")[2:]
    cells = [[c.strip() for c in line.strip("|").split("|")] for line in lines]
    column = 0
    for label, members, mapped, derived, unmapped in cells[:-1]:
        test.assertEqual(sum(int(n) for n in members.split(" / ")), int(mapped) + int(derived) + int(unmapped), label)
        column += int(unmapped)
    total = int(cells[-1][4].strip("*"))
    test.assertEqual((column, total), (result.counts["unmapped"], result.counts["unmapped"]))
    test.assertEqual(total, sum(v.startswith("UNMAPPED: ") for v in result.violations), result.violations[:8])
    return total


def row_block(text, rid):
    """The [[row]] block of the table (with its divergence) whose id is `rid`."""
    start = text.index(f'[[row]]\nid = "{rid}"\n')
    end = text.find("\n[[row]]\n", start + 1)
    return text[start:end + 1 if end >= 0 else len(text)]


class RealInputs(unittest.TestCase):
    def test_real_inputs_pass_and_publish_the_counts(self):
        result = MB.collect()
        self.assertEqual(result.violations, [])
        self.assertEqual(unmapped_column(self, result), 0)
        self.assertEqual({k: result.counts.get(k) for k in PUBLISHED}, PUBLISHED)
        self.assertEqual(result.counts["reviews"]["judgments"], PUBLISHED_JUDGMENTS)
        self.assertIn("| **Total** | 1004 | | | **0** |", result.counts_text)
        self.assertEqual(result.counts_text.count("\n| divergence `"), 4)

    def test_cli_exits_zero_and_each_missing_clone_exits_two(self):
        run = subprocess.run([sys.executable, str(SCRIPT)], capture_output=True, text=True)
        self.assertEqual(run.returncode, 0, run.stderr)
        self.assertIn(f"minirust_baseline: OK (unmapped 0; {PUBLISHED['doc-citations']} document citations; {PUBLISHED_JUDGMENTS} reviewed judgments", run.stdout)
        for flag, url in (("--minirust", "https://github.com/minirust/minirust"), ("--reference", "https://github.com/rust-lang/reference")):
            with self.subTest(flag), tempfile.TemporaryDirectory() as tmp:
                run = subprocess.run([sys.executable, str(SCRIPT), flag, str(Path(tmp) / "absent")], capture_output=True, text=True)
                self.assertEqual(run.returncode, 2)
                self.assertIn(f"git clone {url} {Path(tmp) / 'absent'}", run.stderr)


class Reader(unittest.TestCase):
    def parse(self, code):
        toks = MB.tokenize(code, 1, "t.md")
        items = MB.Parser(toks, "t.md").items(len(toks))
        for item in items:
            MB.attach(item, toks)
        return items

    def test_tokenizer_keeps_strings_lifetimes_and_drops_comments(self):
        toks = MB.tokenize('/* a /* nested */ b */ let s = "doesn\'t // x"; f::<\'static>(\'c\'); // tail\n/// doc', 1, "t.md")
        kinds = [(t.kind, t.text) for t in toks]
        self.assertIn(("str", '"doesn\'t // x"'), kinds)
        self.assertIn(("lifetime", "'static"), kinds)
        self.assertIn(("char", "'c'"), kinds)
        self.assertEqual(toks[-1].kind, "doc")
        self.assertNotIn("tail", [t.text for t in toks])

    def test_enums_structs_generics_and_attributes(self):
        e, n, u, s = self.parse(
            "pub enum E<T> {\n  /// doc\n  #[specr::indirection]\n  A(Map<Int, List<T>>, T),\n  B { x: Option<List<T>>, },\n  C,\n}\n"
            "pub struct N(pub libspecr::Name);\nstruct U;\npub struct S { pub f: Map<A, B>, g: (Offset, Type) }\n")
        self.assertEqual([(v[0], v[1]) for v in e.variants], [("A", 4), ("B", 5), ("C", 6)])
        self.assertEqual([f[0] for f in e.variants[1][2]], ["x"])
        self.assertEqual((n.shape, [f[0] for f in n.fields]), ("tuple", ["0"]))
        self.assertEqual(u.shape, "unit")
        self.assertEqual([name for name, _ in MB.type_names(s.fields[1][2], set())], ["Offset", "Type"])

    def test_traits_impls_argmatch_and_external_enums(self):
        items = self.parse(
            "pub struct Program { s: Sign }\n"
            "pub trait T { type A: Default; const C: Size; fn f(&self) -> Result; }\n"
            "impl<M: Memory> T for X<M> { type A = (); fn f(&self) -> Result { ret(()) } }\n"
            "impl Machine { #[specr::argmatch(op)]\n fn ev(&mut self, op: Op) -> R { .. }\n"
            " fn ev(&mut self, Op::Lock(LockOp::Create): Op) -> R { let x = Sign::Plus; throw_ub!(\"x\"); }\n}\n"
            "enum Op { Lock(LockOp) }\nenum LockOp { Create }\n")
        f = C.Findings()
        members = MB.derive_universe(items, {"Sign": {"class": "enum", "variants": ["Plus", "Minus"]}}, f)
        self.assertEqual(f.violations, ["UNIVERSE: external Sign: its variant Minus is written `Sign::Minus` in no fence at the pin"])
        self.assertEqual((members["def:Sign"].klass, members["variant:Sign::Plus"].line), ("syntax", 6))
        self.assertIn("fn:<X as T>::f", members)
        self.assertIn("assoc-const:T::C", members)
        self.assertEqual(members["case:Machine::ev[LockOp::Create]"].derived_from, "variant:LockOp::Create")
        self.assertEqual(members["dispatcher:Machine::ev"].derived_from, "def:Op")
        self.assertEqual(MB.ub_sites(items, members, f)[1], {"t.md:6": "case:Machine::ev[LockOp::Create]"})

    def test_unbalanced_code_is_refused(self):
        for code in ("pub enum Broken { A,\n", "struct S { f: Map<A, B }\n"):
            with self.subTest(code), self.assertRaises(MB.SpecrError):
                self.parse(code)


class Mutations(unittest.TestCase):
    def setUp(self):
        self._tmp = tempfile.TemporaryDirectory()
        self.tmp = Path(self._tmp.name)
        self.table, self.doc, self.registry, self.vocabulary, self.decisions = (p.read_text(encoding="utf-8") for p in (TABLE, DOC, REGISTRY, VOCABULARY, DECISIONS))

    def tearDown(self):
        self._tmp.cleanup()

    def run_inputs(self, table=None, doc=None, registry=None, vocabulary=None, trees=None, decisions=None):
        paths = {}
        for name, text in (("table", table or self.table), ("doc", doc or self.doc), ("registry", registry or self.registry),
                           ("vocabulary", vocabulary or self.vocabulary), ("decisions", decisions or self.decisions)):
            paths[name] = self.tmp / f"{name}.txt"
            paths[name].write_text(text, encoding="utf-8")
        result = MB.collect(MB.Options(table=paths["table"], doc=paths["doc"], registry=paths["registry"], vocabulary=paths["vocabulary"],
                                       decisions=paths["decisions"], trees=trees or {}, check_pin_state=False, check_history=False))
        if result.counts_text:
            unmapped_column(self, result)
        return result

    def assert_violation(self, violations, *fragments):
        for fragment in fragments:
            self.assertTrue(any(fragment in v for v in violations), f"{fragment!r} not in {violations[:8]}")

    def mechanical(self, violations):
        return [v for v in violations if not v.startswith("REVIEW:") and "block differs from its computed rendering" not in v]

    def review(self, jids, table=None, doc=None):
        """The registry with a new record's review of each judgment's current content appended."""
        f = C.Findings()
        now = MB.judgments(f, table or self.table, C.document_judgments(f, "DOC", doc or self.doc, generated=(MB.COUNTS_BLOCK, MB.LEDGER_BLOCK)))
        text = self.registry.replace("[judgment]", '[record.mutation]\nround = "test"\ndate = "2026-09-17"\nevidence = ["the mutation"]\nreason = "a mutation test"\n\n[judgment]')
        for jid in jids:
            line = next(l for l in text.split("\n") if l.startswith(f'"{jid}" = '))
            new = C.digest(jid, now[jid])
            text = text.replace(line, re.sub(r'digest = "[^"]+"', f'digest = "{new}"', line, count=1)[:-4] + f'], ["mutation", "{new}"]] }}')
        return text

    def minirust(self, edits):
        """A DirTree copy of the MiniRust clone with each (file, old, new) edit applied once."""
        copy = self.tmp / "minirust"
        if not copy.exists():
            shutil.copytree(CLONES["minirust"], copy, ignore=shutil.ignore_patterns(".git"))
        for rel, old, new in edits:
            path = copy / rel
            path.write_text(replace_once(path.read_text(encoding="utf-8"), old, new), encoding="utf-8")
        return {"minirust": C.DirTree(copy)}

    def test_control_copies_pass(self):
        self.assertEqual(self.run_inputs().violations, [])
        self.assertEqual(self.run_inputs(trees=self.minirust([])).violations, [])

    def test_source_mutations_fail(self):
        cases = [
            ("syntax variant", [("spec/lang/syntax.md", "    Cleanup,\n", "    Cleanup,\n    Warm,\n")], "UNMAPPED: MiniRust variant BbKind::Warm (spec/lang/syntax.md:508): no row claims it"),
            ("memory-interface fn", [("spec/mem/interface.md", "    fn leak_check(&self) -> Result;\n", "    fn leak_check(&self) -> Result;\n    fn forget(&self) -> Result;\n")],
             "UNMAPPED: MiniRust fn Memory::forget (spec/mem/interface.md:159): no row claims it"),
            ("UB message", [("spec/mem/basic.md", 'throw_ub!("double-free");', 'throw_ub!("double free");')],
             "VOCABULARY: UB site spec/mem/basic.md:160: the pin raises 'double free', the vocabulary lists 'double-free'"),
            ("UB mechanism", [("spec/mem/basic.md", 'throw_ub!("double-free");', 'throw_ub!["double-free"];')],
             "UB-MECHANISM: spec/mem/basic.md:160: `throw_ub` used other than as its definition or a parenthesized call"),
            ("retagged fence", [("spec/mem/intptrcast.md", "\n```rust\npub struct IntPtrCast", "\n```text\npub struct IntPtrCast")],
             "UNIVERSE: spec/mem/intptrcast.md:13: a fence with info string 'text' holds a specr item"),
            ("unparsable fence", [("spec/mem/intptrcast.md", "pub struct IntPtrCast<Provenance> {", "pub struct IntPtrCast<Provenance> {{")], "UNIVERSE: spec/mem/intptrcast.md:"),
            ("undeclared external", [("spec/lang/syntax.md", "    pub kind: BbKind,\n", "    pub kind: BbKind,\n    pub label: Blob,\n")],
             "UNIVERSE: syntax reaches `Blob` (spec/lang/syntax.md:500), which MiniRust does not define and no [[external]] row classifies"),
            ("undeclared libspecr variant", [("spec/lang/types.md", "IntType { signed: Signedness::Unsigned, size: T::PTR_SIZE }", "IntType { signed: Signedness::Either, size: T::PTR_SIZE }")],
             "UNIVERSE: spec/lang/types.md:300: `Signedness::Either` names no variant the [[external]] row Signedness declares"),
            ("orphan case fn", [("spec/lang/step/statements.md", "    #[specr::argmatch(statement)]\n", "")], "matches a variant in a parameter but no argmatch dispatcher owns it"),
        ]
        for label, edits, fragment in cases:
            with self.subTest(label):
                shutil.rmtree(self.tmp / "minirust", ignore_errors=True)
                self.assert_violation(self.run_inputs(trees=self.minirust(edits)).violations, fragment)
        (self.tmp / "minirust/spec/extra.rs").write_text("fn hidden() {}\n", encoding="utf-8")
        self.assert_violation(self.run_inputs(trees={"minirust": C.DirTree(self.tmp / "minirust")}).violations,
                              "UNIVERSE: spec/extra.rs: a file under spec/ that is not Markdown")

    def test_mapping_mutations_fail(self):
        lookup = '  { member = "fn:Machine::vtable_from_ptr", ref = "spec/lang/machine.md:347", token = "vtable_from_ptr" },\n'
        cases = [
            ("deleted row", replace_once(self.table, row_block(self.table, "R-DIV-DEADLOCK"), ""), "UNMAPPED: MiniRust fn Machine::step (spec/lang/machine.md:197): no row claims it"),
            ("misspelled Core name", replace_once(self.table, 'core = ["Rvalue.Tuple"]', 'core = ["Rvalue.Tupel"]'), "'Rvalue.Tupel' is neither a Core vocabulary name"),
            ("refused core list", replace_once(self.table, 'core = ["Rvalue.Tuple"]', 'core = "Rvalue.Tuple"'),
             "UNMAPPED: MiniRust variant ValueExpr::Tuple (spec/lang/syntax.md:21): row R-SYNTAX-RVALUE-CONSTRUCTS claims it but its mapping is refused"),
            ("unclaimed variant and its case fn", replace_once(self.table, '  { member = "variant:Terminator::ResumeUnwind", ref = "spec/lang/syntax.md:384", token = "ResumeUnwind" },\n', ""),
             "UNMAPPED: derived case:Machine::eval_terminator[Terminator::ResumeUnwind] maps as variant:Terminator::ResumeUnwind, which no row maps"),
            ("unclaimed extension", replace_once(self.table, '  { member = "extension:UbReason" },\n', ""), "UNMAPPED: extension:UbReason: no trust-extends row claims it"),
            ("another member's adopted name", replace_once(self.table, 'core = ["minirust::BasicMemory::load"]', 'core = ["minirust::BasicMemory::new"]'),
             "'minirust::BasicMemory::new' is neither a Core vocabulary name nor this non-syntax member's own adopted name 'minirust::BasicMemory::load'"),
            ("syntax member off its vocabulary name", replace_once(self.table, 'core = ["Rvalue.Tuple"]', 'core = ["Rvalue.Union"]'),
             "MAPPING: row R-SYNTAX-RVALUE-CONSTRUCTS variant:ValueExpr::Tuple: the vocabulary names this member ['Rvalue.Tuple'], the row maps it to ['Rvalue.Union']"),
            ("extension outside trust-extends", replace_once(self.table, row_block(self.table, "R-EXT-OPERANDS"), row_block(self.table, "R-EXT-OPERANDS").replace('kind = "trust-extends"', 'kind = "trust-differs"')),
             "MAPPING: row R-EXT-OPERANDS extension:Operand: a trust-extension name is claimed only by a trust-extends divergence"),
            ("undecided site", replace_once(self.table, '"spec/lang/machine.md:335", ', ""),
             "UNMAPPED: UB site spec/lang/machine.md:335 ("),
            ("changed site in trust-extends", replace_once(replace_once(self.table, lookup, ""), '  { member = "extension:UbReason" },\n', lookup + '  { member = "extension:UbReason" },\n'),
             "MAPPING: UB site spec/lang/machine.md:349 is claimed as changed, but its member fn:Machine::vtable_from_ptr is in trust-extends row R-EXT-UB-REASONS"),
            ("site claimed by a core row", replace_once(self.table, '  { member = "fn:BasicMemory::load",', '  { member = "ub-site:spec/mem/basic.md:153", ref = "spec/mem/basic.md:153", token = "deallocating invalid pointer" },\n  { member = "fn:BasicMemory::load",'),
             "MAPPING: row R-ADOPT-BASIC-MEMORY ub-site:spec/mem/basic.md:153: a UB site maps by derivation"),
            ("stale ref", replace_once(self.table, 'ref = "spec/mem/basic.md:144", token = "deallocate"', 'ref = "spec/mem/basic.md:145", token = "deallocate"'), "are stale; the pin has spec/mem/basic.md:144 'deallocate'"),
            ("resolution", replace_once(self.table, 'resolution = "LD-4"', 'resolution = "LD-99"'), "resolution 'LD-99' is neither upstream-proposal nor an LD-n row"),
            ("kind", replace_once(self.table, row_block(self.table, "R-DIV-DEADLOCK"), row_block(self.table, "R-DIV-DEADLOCK").replace('kind = "trust-differs"', 'kind = "trust-maybe"')),
             "divergence kind 'trust-maybe' is not one of"),
            ("design quote", replace_once(self.table, 'quote = "Operational, as in Miri" }', 'quote = "Axiomatic, as in Miri" }'), "MAPPING: row R-DIV-DATA-RACES: design:1112 does not contain"),
            ("row citation", replace_once(self.table, 'quote = "pub provenance: Option<Provenance>," }', 'quote = "pub provenance: Provenance," }'), "CITE: row R-ADOPT-PER-CAST-PROVENANCE: minirust:spec/mem/pointer.md:33 does not contain"),
            ("free-text citation", replace_once(self.table, 'note = "LD-3 is ruled', 'note = "See basic.md:153. LD-3 is ruled'), "TABLE: row R-ADOPT-PER-CAST-PROVENANCE: free text carries a line citation"),
            ("external removed", re.sub(r'\[\[external\]\]\nname = "Option"\n.*?\n\n', "", self.table, count=1, flags=re.S), "UNIVERSE: syntax reaches `Option`"),
            ("external variant removed", replace_once(self.table, 'variants = ["Signed", "Unsigned"]', 'variants = ["Signed"]'), "`Signedness::Unsigned` names no variant the [[external]] row Signedness declares"),
            ("external class", replace_once(self.table, 'name = "Option"\nclass = "container"', 'name = "Option"\nclass = "enum"'), "TABLE: external Option: an external row is"),
        ]
        for label, table, fragment in cases:
            with self.subTest(label):
                self.assertNotEqual(table, self.table)
                self.assert_violation(self.run_inputs(table).violations, fragment)

    def ruled(self, item, ruling, record=None):
        """The Language Decisions ledger with `item`'s [[ratify]] ruling (and, given, its ruling_record) replaced."""
        start = self.decisions.index(f'[[ratify]]\nitem = "{item}"\n')
        end = self.decisions.index("\n[[", start + 1)
        block = re.sub(r'^ruling = "[a-z]+"$', f'ruling = "{ruling}"', self.decisions[start:end], count=1, flags=re.M)
        if record is not None:
            block = re.sub(r'^ruling_record = ".*"$', f'ruling_record = "{record}"', block, count=1, flags=re.M)
        return self.decisions[:start] + block + self.decisions[end:]

    def test_rulings_hold_and_each_contradiction_of_a_ruled_entry_fails(self):
        """RULING (the proven-core plan's RM0): no row contradicts a ruled Language Decisions entry."""
        rulings = lambda result: [v for v in result.violations if v.startswith("RULING:")]  # noqa: E731
        self.assertEqual(rulings(self.run_inputs()), [])  # control: the real table and ledger
        ld3_cite = '  { ref = "minirust:spec/mem/intptrcast.md:23", quote = "pub fn expose(&mut self, ptr: ThinPointer<Provenance>) {" },\n'
        cites_ld3 = replace_once(self.table, ld3_cite, ld3_cite + '  { ref = "design:1111", quote = "| LD-3 | Exposed provenance | Per-access wildcard resolution (angelic) | **Required** |" },\n')
        rejustify = lambda table, quote: replace_once(table, 'note = "The set of exposed provenances',  # noqa: E731
                                                      f'rulings = [{{ item = "LD-3", quote = "{quote}" }}]\nnote = "The set of exposed provenances')
        revised_quote = "Revised from the recommended per-access wildcard to per-cast angelic prediction"
        races = row_block(self.table, "R-DIV-DATA-RACES")
        for label, inputs, fragment in (
            ("a row citing the revised LD-3 cell (the negative control)", {"table": cites_ld3},
             "RULING: row R-ADOPT-INTPTRCAST: contradicts the ruled LD-3: its citation design:1111 rests on the design's LD-3 recommendation, which the ledger ruled 'revised'"),
            ("a divergence resolved by the revised LD-3",
             {"table": replace_once(self.table, races, races.replace('resolution = "LD-4"', 'resolution = "LD-3"'))},
             "RULING: row R-DIV-DATA-RACES: contradicts the ruled LD-3: its resolution LD-3"),
            ("LD-4 revised under its rows", {"decisions": self.ruled("LD-4", "revised")}, "RULING: row R-DIV-DATA-RACES: contradicts the ruled LD-4: its resolution LD-4"),
            ("LD-1 rejected under its rows", {"decisions": self.ruled("LD-1", "rejected")}, "RULING: row R-DIV-BASIC-MEMORY-MODEL: contradicts the ruled LD-1"),
            ("a divergence resolved by a pending ruling", {"decisions": self.ruled("LD-4", "pending", "")}, "RULING: row R-DIV-DATA-RACES: resolves to LD-4, whose ruling is pending"),
            ("a ratify row out of shape", {"decisions": self.ruled("LD-4", "pending")}, "[[ratify]] LD-4: ruling 'pending' is not one of"),
            ("a quote the ruling record lacks", {"table": rejustify(cites_ld3, "per-access stays")}, "RULING: row R-ADOPT-INTPTRCAST: rulings LD-3: the quote is not text of the ruling_record (stale)"),
            ("a re-justification of a decision the row does not rest on", {"table": rejustify(self.table, revised_quote)},
             "RULING: row R-ADOPT-INTPTRCAST: rulings names LD-3, which the row does not rest on (stale)"),
            ("a re-justification of an unruled decision", {"table": rejustify(cites_ld3, revised_quote).replace('item = "LD-3", quote', 'item = "LD-9", quote')},
             "RULING: row R-ADOPT-INTPTRCAST: rulings names LD-9, which the ledger has not ruled (stale)"),
            ("an unreadable ledger", {"decisions": "not = [toml"}, "the ruling states cannot be read"),
        ):
            with self.subTest(label):
                self.assert_violation(self.run_inputs(**inputs).violations, fragment)
        # positive control: a re-justification quoting the ruling record lifts exactly the contradiction
        self.assertEqual(rulings(self.run_inputs(table=rejustify(cites_ld3, revised_quote))), [])

    def test_other_input_mutations_fail(self):
        vocabulary = replace_once(self.vocabulary, 'name = "LocalName"\ngroup = "Body"\nshape = "wrapper"\norigin = "minirust"\nminirust_ref = "spec/lang/syntax.md:472"\n',
                                  'name = "LocalName"\ngroup = "Body"\nshape = "wrapper"\norigin = "minirust"\nminirust_ref = "spec/lang/syntax.md:473"\n')
        self.assert_violation(self.run_inputs(vocabulary=vocabulary).violations, "VOCABULARY: vocabulary inductive LocalName: cites spec/lang/syntax.md:473 'LocalName'",
                              "MAPPING: row R-SYNTAX-NAMES def:LocalName: a syntax member maps in a core row only to the Core names the vocabulary cites for it, and the vocabulary cites none")
        self.assert_violation(self.run_inputs(vocabulary=replace_once(self.vocabulary, 'message = "double-free" }', 'message = "double free" }')).violations,
                              "VOCABULARY: UB site spec/mem/basic.md:160: the pin raises 'double-free', the vocabulary lists 'double free'")
        design = C.GitTree(ROOT, "HEAD").text(C.DESIGN_REL)
        self.assertEqual(self.run_inputs(trees={"design": C.DirTree(self.tmp, {C.DESIGN_REL: design})}).violations, [])  # control
        for label, mutated, fragment in (
            ("LD row", replace_once(design, "| LD-4 | Data races |", "| LD-4b | Data races |"), "resolution 'LD-4' is neither upstream-proposal nor an LD-n row"),
            ("extension list", replace_once(design, "`Terminate` reasons, concurrency, the const machine", "`Terminate` reasons, the const machine"),
             "MAPPING: row R-EXT-CONCURRENCY design-extension:concurrency: an extension member carries only `member` and is a vocabulary trust-extension name or an extension the design lists"),
        ):
            with self.subTest(label):
                self.assert_violation(self.run_inputs(trees={"design": C.DirTree(self.tmp, {C.DESIGN_REL: mutated})}).violations, fragment)
        for label, doc, fragment in (
            ("counts", replace_once(self.doc, "| **Total** | 1004 |", "| **Total** | 1005 |"), "DOC: the published `minirust-baseline-counts` block differs"),
            ("ledger", replace_once(self.doc, "`R-DIV-DEADLOCK` Deadlock is not an outcome | trust-differs", "`R-DIV-DEADLOCK` Deadlock is not an outcome | trust-extends"),
             "DOC: the published `minirust-baseline-ledger` block differs"),
            ("unreviewed line", replace_once(self.doc, "## Open questions\n", "## Open questions\n\nEvery owner question below is answered.\n"), "DOC: line"),
            ("unchecked citation", replace_once(self.doc, "(open question OQ-3).", "(open question OQ-3, see design:4080)."), "line citation 'design:4080' is not in the checked"),
            ("quote drift", replace_once(self.doc, "design:869 «Allocations are nondeterministic, aligned, non-overlapping, at nonzero»", "design:869 «Allocations are deterministic»"), "DOC: prose:oq-13: design:869 does not contain"),
            ("pin", replace_once(self.doc, "`d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed`", "`d821c6e3`"), "DOC: the document does not record the pin `d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed`"),
        ):
            with self.subTest(label):
                self.assert_violation(self.run_inputs(doc=doc).violations, fragment)

    def test_a_reviewed_rename_of_a_derived_reason_leaves_its_sites_unmapped_and_fails(self):
        """Tree Borrows sites derive to UbReason.AliasViolation and their own reason. A rename of that
        reason in the vocabulary and in R-EXT-ALIAS-REASONS, reviewed and with regenerated blocks, leaves
        the 11 sites unmapped: the checker fails with exactly one UNMAPPED violation per site, and the
        published column counts them."""
        vocabulary = replace_once(self.vocabulary, '[[ub_reason]]\nname = "UbReason.AliasViolation"\n', '[[ub_reason]]\nname = "UbReason.AliasBreach"\n')
        table = replace_once(self.table, '{ member = "extension:UbReason.AliasViolation" }', '{ member = "extension:UbReason.AliasBreach" }')
        blocks = self.run_inputs(table, vocabulary=vocabulary)
        doc = C.replace_block(C.replace_block(self.doc, MB.COUNTS_BLOCK, blocks.counts_text), MB.LEDGER_BLOCK, blocks.ledger_text)
        result = self.run_inputs(table, doc, self.review(["row:R-EXT-ALIAS-REASONS"], table, doc), vocabulary)
        self.assertEqual(len(result.violations), 11, result.violations)
        self.assertTrue(all(v.startswith("UNMAPPED: UB site spec/mem/tree_borrows/") and v.endswith("and UbReason.AliasViolation is no Core vocabulary name")
                            for v in result.violations), result.violations)
        self.assertIn("| **Total** | 1004 | | | **11** |", result.counts_text)

    def test_judgment_changes_fail_only_review_until_reviewed(self):
        """The three prose mutations that survived the last verification, a row, an external row, a
        table comment and a heading: each is mechanically valid, fails REVIEW, and passes reviewed."""
        cases = [
            ("prose:kind-trust-extends", None, replace_once(self.doc, "every behaviour\n  MiniRust gives the row's MiniRust members is kept", "some behaviour\n  MiniRust gives the row's MiniRust members may change")),
            ("prose:rule-4", None, replace_once(self.doc, "cannot be derived silently", "may be derived silently")),
            ("prose:oq-13", None, re.sub(r"(<!-- reviewed:prose:oq-13 -->\n).*?(<!-- /reviewed:prose:oq-13 -->)",
                                         r"\1* **OQ-13, zero-sized allocation addresses.** The design already settles this: Core keeps distinct addresses.\n\2", self.doc, flags=re.S)),
            ("row:R-DIV-DATA-RACES", re.sub(r'(id = "R-DIV-DATA-RACES".*?explanation = )"[^"]*"', r'\1"MiniRust flags exactly the traces Miri flags, so nothing differs."', self.table, count=1, flags=re.S), None),
            ("external:Signedness", replace_once(self.table, "libspecr's signedness, whose two variants", "libspecr's signedness, whose variants"), None),
            ("comments:table", replace_once(self.table, "# This table is also the seed", "# OWNER DECISION: OQ-2 is closed.\n# This table is also the seed"), None),
            ("outline:document", None, replace_once(self.doc, "## Open questions\n", "## Open questions (all answered)\n")),
        ]
        for jid, table, doc in cases:
            with self.subTest(jid):
                self.assertTrue(table != self.table if table else doc != self.doc)
                violations = self.run_inputs(table, doc).violations
                self.assertEqual(self.mechanical(violations), [])
                self.assertEqual(len(violations), 1, violations)
                self.assert_violation(violations, f"REVIEW: judgment {jid}: its content changed")
                self.assertEqual(self.run_inputs(table, doc, registry=self.review([jid], table, doc)).violations, [])


if __name__ == "__main__":
    unittest.main(verbosity=1)
