#!/usr/bin/env python3
"""Tests for scripts/two_language_producer_ratchets.py (roadmap WS5.1).

Positive: the judge, re-run over the ARCHIVED Part A measurement of the audit
compiler (5b45b83b8), reproduces that run's features.txt verdict for verdict
and class for class; and every pin in every tests/two-language-programs/ir-*
row either equals the audit verdict or carries a named `moved` reason, while
every audit row is pinned by exactly one row or excluded with a reason.

Negative twin: a STANDALONE refusal whose class changes
(`[gate/target-shape]` -> `[carrier/no-total-carrier]`) reads FAIL against its
pin, never "the same GAP".

Mutation: re-enabling the proof program's unconditional `repair_fndef` (a
module rewrite, ported here as the MUTATION only; the judge has none) turns the
GENERAL `.validate` rows of the modules that are correct AS EMITTED red.  This
one needs the judges built from the gitlinks (`two_language_producer_ratchets.py
tools --build`); without them it is skipped and says why.

Standard library only.
"""

from __future__ import annotations

import copy
import importlib.util
import json
import os
import re
import shutil
import stat
import sys
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
SPEC = importlib.util.spec_from_file_location("two_language_producer_ratchets",
                                              ROOT / "scripts" / "two_language_producer_ratchets.py")
J = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = J
SPEC.loader.exec_module(J)

AUDIT = ROOT / "tests" / "two-language-programs" / "ir-audit"
REPORT = AUDIT / "parta-5b45b83b8.report.json"
FEATURES = AUDIT / "parta-5b45b83b8.features.txt"


class ReplayReproducesTheAudit(unittest.TestCase):
    """The port is faithful: the archived measurement re-judged == the archived judgment."""

    @classmethod
    def setUpClass(cls):
        cls.report = json.loads(REPORT.read_text())
        cls.features = J.parse_features(FEATURES)

    def test_replay_reproduces_features_row_for_row(self):
        n, bad = J.replay_mismatches(self.report, self.features)
        self.assertEqual(bad, [])
        # native / emit / validate / roundtrip / exec / twins over 23 probes + dep/app/app_max/app_exec,
        # plus the surface, format and attrib rows
        self.assertGreaterEqual(n, 230)

    def test_replay_is_not_vacuous_a_changed_measurement_is_a_mismatch(self):
        # mutation control of the replay itself: a text parse error at a site that is not a name
        report = copy.deepcopy(self.report)
        rt = report["units"]["p06_rust_closure"]["module"]["roundtrip"]["text"]
        rt["message"] = "error: text parse error: parse error at 3:1: expected 'fn', got 'x'"
        n, bad = J.replay_mismatches(report, self.features)
        self.assertEqual(len(bad), 1, bad)
        self.assertIn("a.rust.closure.roundtrip: archive GAP/producer-gap, replay FAIL", bad[0])

    def test_replay_names_the_text_leg_by_its_parse_site(self):
        rows = {r["id"]: r for r in J.replay_parta(self.report)}
        self.assertEqual(rows["a.rust.closure.roundtrip"]["signature"], "roundtrip:text-parse:fn-name")
        self.assertEqual(rows["a.lean.nat_structural.roundtrip"]["signature"], "roundtrip:text-parse:struct-name")
        self.assertEqual(rows["a.lean.nat_structural.roundtrip"]["class"], "format-gap")


class PinsAgainstTheAudit(unittest.TestCase):
    def test_every_row_is_pinned_and_every_move_is_named(self):
        self.assertEqual(J.audit_problems(), [])

    def test_a_move_without_a_reason_is_refused(self):
        audit = {"a.x.native": ("GAP", "refused")}
        pin = {"verdict": "PASS", "audit": "GAP"}
        self.assertTrue(any("without a named reason" in p for p in J.pin_problems("a.x.native", pin, audit)))
        pin["moved"] = "UNREVIEWED: audit GAP, measured PASS"
        self.assertTrue(any("without a named reason" in p for p in J.pin_problems("a.x.native", pin, audit)))
        pin["moved"] = "closed upstream by abc123: the island inductive became nameable"
        self.assertEqual(J.pin_problems("a.x.native", pin, audit), [])

    def test_the_audit_field_cannot_be_rewritten(self):
        audit = {"a.x.native": ("GAP", "refused")}
        pin = {"verdict": "PASS", "audit": "PASS"}
        self.assertTrue(any("audit corpus says 'GAP'" in p for p in J.pin_problems("a.x.native", pin, audit)))

    def test_a_gap_class_change_is_a_move(self):
        audit = {"a.x.exec": ("GAP", "producer-gap")}
        pin = {"verdict": "GAP", "class": "consumer-gap", "signature": "s", "audit": "GAP"}
        self.assertTrue(any("without a named reason" in p for p in J.pin_problems("a.x.exec", pin, audit)))

    def test_fail_and_unsigned_gaps_are_not_pinnable(self):
        self.assertTrue(J.pin_problems("a.y", {"verdict": "FAIL", "audit": None, "moved": "x"}, {}))
        self.assertTrue(any("named signature" in p for p in J.pin_problems(
            "a.y", {"verdict": "GAP", "class": "producer-gap", "audit": None, "moved": "x"}, {})))

    def test_excluded_rows_are_the_attribution_experiments_only(self):
        self.assertIsNotNone(J.not_ported_reason("a.rust.contracts.carry_experiment"))
        self.assertIsNotNone(J.not_ported_reason("a.rust.contracts.carry_experiment.text"))
        self.assertIsNotNone(J.not_ported_reason("a.lean.select.repair_experiment"))
        self.assertIsNotNone(J.not_ported_reason("a.rust.std_call.upstream_body_experiment"))
        for fid in ("a.rust.contracts.carried", "a.surface.summary", "STANDALONE.p02_if_select", "GENERAL.p02_if_select.min2.validate"):
            self.assertIsNone(J.not_ported_reason(fid), fid)


def row(fid, verdict, klass=None, sig=None):
    r = {"id": fid, "verdict": verdict, "detail": "d"}
    if klass:
        r["class"] = klass
    if sig:
        r["signature"] = sig
    return r


class CompareSemantics(unittest.TestCase):
    PIN = {"ratchets": {"a.g": {"verdict": "GAP", "class": "producer-gap", "signature": "carried:absent:['x']"},
                        "a.p": {"verdict": "PASS"}}}

    def status(self, rows):
        return {i: s for i, s, _ in J.compare(rows, self.PIN)}

    def test_pins_hold(self):
        self.assertEqual(self.status([row("a.g", "GAP", "producer-gap", "carried:absent:['x']"), row("a.p", "PASS")]),
                         {"a.g": "OK", "a.p": "OK"})

    def test_a_gap_that_turns_pass_is_red_until_repinned(self):
        self.assertEqual(self.status([row("a.g", "PASS"), row("a.p", "PASS")])["a.g"], "FLIPPED")

    def test_a_gap_matches_only_its_signature(self):
        st = self.status([row("a.g", "GAP", "producer-gap", "carried:absent:['y']"), row("a.p", "PASS")])
        self.assertEqual(st["a.g"], "FAIL")
        st = self.status([row("a.g", "GAP", "consumer-gap", "carried:absent:['x']"), row("a.p", "PASS")])
        self.assertEqual(st["a.g"], "FAIL")

    def test_fail_unpinned_and_unmeasured_are_red(self):
        st = self.status([row("a.g", "FAIL"), row("a.new", "PASS")])
        self.assertEqual(st, {"a.g": "FAIL", "a.new": "FAIL", "a.p": "FAIL"})


class MeasuredOnlyWhenSemantics(unittest.TestCase):
    """`measured_only_when` is the third answer the CONDITIONAL table asked for: a ratchet that only EXISTS on
    one side of a build matrix. `ir-ta-f1` is the case — a build shipping the opt-in trust-cg codegen backend
    emits four `a.f1.codegen.*` rows, a default build emits the collapsed `a.f1.codegen` GAP instead, and before
    this there was no expected.json green on both. It excuses ABSENCE only; it can never admit a result."""

    PIN = {"ratchets": {
        "a.f1.codegen": {"verdict": "GAP", "class": "consumer-gap", "signature": "f1:no-trust-cg-backend",
                         "measured_only_when": "the build does NOT ship trust-cg"},
        "a.f1.codegen.backend": {"verdict": "PASS", "measured_only_when": "the build SHIPS trust-cg"},
    }}

    def status(self, rows):
        return {i: s for i, s, _ in J.compare(rows, self.PIN)}

    def test_each_side_of_the_build_matrix_is_green(self):
        present = self.status([row("a.f1.codegen.backend", "PASS")])
        self.assertEqual(present, {"a.f1.codegen.backend": "OK", "a.f1.codegen": "SKIP"})
        absent = self.status([row("a.f1.codegen", "GAP", "consumer-gap", "f1:no-trust-cg-backend")])
        self.assertEqual(absent, {"a.f1.codegen": "OK", "a.f1.codegen.backend": "SKIP"})

    def test_it_never_excuses_a_measured_result(self):
        """The marker tolerates absence, never a verdict. A measured row still has to match its pin."""
        st = self.status([row("a.f1.codegen.backend", "GAP", "consumer-gap", "whatever")])
        self.assertEqual(st["a.f1.codegen.backend"], "FLIPPED")
        st = self.status([row("a.f1.codegen.backend", "FAIL")])
        self.assertEqual(st["a.f1.codegen.backend"], "FAIL")

    def test_an_unpinned_measurement_is_still_red(self):
        """Absence is excused; a NEW ratchet nobody pinned is not."""
        st = self.status([row("a.f1.codegen.backend", "PASS"), row("a.f1.codegen.brand_new", "PASS")])
        self.assertEqual(st["a.f1.codegen.brand_new"], "FAIL")

    def test_a_row_that_measured_nothing_is_red_not_skipped(self):
        """The vacuity guard. With no measured rows at all, every pin would SKIP and the row would read green
        off an empty measurement; `compare` refuses to skip and the row fails as it did before."""
        self.assertEqual(self.status([]), {"a.f1.codegen": "FAIL", "a.f1.codegen.backend": "FAIL"})

    def test_a_repin_does_not_drop_the_marker(self):
        """`--write-expected` rebuilds a pin from the measurement. The marker is a fact about the build matrix,
        not about the verdict, so losing it would silently redden the other side."""
        old = {"verdict": "PASS", "measured_only_when": "the build SHIPS trust-cg"}
        pin = J.pin_for(row("a.f1.codegen.backend", "PASS"), old, {})
        self.assertEqual(pin.get("measured_only_when"), "the build SHIPS trust-cg")
        moved = J.pin_for(row("a.f1.codegen.backend", "GAP", "consumer-gap", "sig"), old, {})
        self.assertEqual(moved.get("measured_only_when"), "the build SHIPS trust-cg")


class EvidenceArtifact(unittest.TestCase):
    """The completion-gate artifact aggregates only what ONE run measured; it never fills a row from a pin."""

    def test_gate_tags(self):
        self.assertEqual(J.ratchet_gates("a.rust.contracts.validate"), ["G1", "G3"])
        self.assertEqual(J.ratchet_gates("a.rust.contracts.carried"), ["G1", "G3", "G6"])
        self.assertEqual(J.ratchet_gates("a.two_lang.x.exec"), ["G3", "G5"])
        self.assertEqual(J.ratchet_gates("STANDALONE.p02_if_select"), ["G2", "G3"])
        self.assertEqual(J.ratchet_gates("a.surface.summary"), ["G6"])
        self.assertEqual(J.ratchet_gates("a.island_mutant.control.differential_fails"), ["G3", "G5"])

    def test_missing_rows_make_it_incomplete_and_a_red_row_makes_it_red(self):
        with tempfile.TemporaryDirectory(dir=str(ROOT / "build") if (ROOT / "build").is_dir() else None) as td:
            rep = Path(td) / "reports"
            rep.mkdir()
            first, second = J.ALL_ROWS[0], J.ALL_ROWS[1]
            judge = J.sha256_file(J.__file__)
            ids = {"trustc": "trustc 1.99.0-dev (deadbeef 2026-09-19)"}
            (rep / (first + ".json")).write_text(json.dumps({
                "rows": [row("a.rust.contracts.native", "PASS")], "identities": ids, "judge_sha256": judge,
                "results": [{"id": "a.rust.contracts.native", "status": "OK", "text": "PASS"}]}))
            doc = J.build_evidence(td)
            self.assertFalse(doc["complete"])
            self.assertIn(second, doc["missing_rows"])
            self.assertFalse(doc["green"])
            self.assertEqual(doc["rows"][0]["ratchets"][0]["gates"], ["G1", "G3"])
            self.assertEqual(doc["by_gate"]["G1"]["PASS"], 1)
            for r in J.ALL_ROWS[1:]:
                (rep / (r + ".json")).write_text(json.dumps({"rows": [], "identities": ids, "judge_sha256": judge,
                                                             "results": [{"id": "x", "status": "OK", "text": "PASS"}]}))
            doc = J.build_evidence(td)
            self.assertTrue(doc["green"], doc["skew"])
            self.assertEqual(doc["identities"], ids)
            (rep / (second + ".json")).write_text(json.dumps({"rows": [], "identities": ids, "judge_sha256": judge,
                                                              "results": [{"id": "x", "status": "FLIPPED", "text": "pinned GAP, measured PASS"}]}))
            doc = J.build_evidence(td)
            self.assertTrue(doc["complete"])
            self.assertFalse(doc["green"])

    def test_two_compilers_or_two_judges_in_one_work_dir_are_skew_not_evidence(self):
        with tempfile.TemporaryDirectory(dir=str(ROOT / "build") if (ROOT / "build").is_dir() else None) as td:
            rep = Path(td) / "reports"
            rep.mkdir()
            judge = J.sha256_file(J.__file__)
            ids = {"trustc": "trustc 1.99.0-dev (deadbeef 2026-09-19)"}
            ok = {"rows": [], "identities": ids, "judge_sha256": judge, "results": [{"id": "x", "status": "OK", "text": "PASS"}]}
            for r in J.ALL_ROWS:
                (rep / (r + ".json")).write_text(json.dumps(ok))
            self.assertTrue(J.build_evidence(td)["green"])
            # one row measured on ANOTHER compiler: the first row's identities must not be attributed to it
            other = dict(ok, identities={"trustc": "trustc 1.99.0-dev (cafef00d 2026-09-20)"})
            (rep / (J.ALL_ROWS[3] + ".json")).write_text(json.dumps(other))
            doc = J.build_evidence(td)
            self.assertFalse(doc["complete"])
            self.assertFalse(doc["green"])
            self.assertEqual(len(doc["skew"]), 1, doc["skew"])
            self.assertIn(J.ALL_ROWS[3], doc["skew"][0])
            self.assertIn("identities differ", doc["skew"][0])
            # one row written by ANOTHER judge (or none): the artifact's judge_sha256 would otherwise vouch for it
            (rep / (J.ALL_ROWS[3] + ".json")).write_text(json.dumps(dict(ok, judge_sha256="0" * 64)))
            doc = J.build_evidence(td)
            self.assertFalse(doc["green"])
            self.assertIn("written by judge", doc["skew"][0])
            (rep / (J.ALL_ROWS[3] + ".json")).write_text(json.dumps({k: v for k, v in ok.items() if k != "judge_sha256"}))
            self.assertFalse(J.build_evidence(td)["complete"])


def stub_targo(path, build_output, build_rc=1):
    """A `targo` that PROVES every check and prints the given refusal for every build."""
    path.write_text("#!/bin/sh\n"
                    "case \"$2\" in\n"
                    "  check) echo \"PROVED $3 — 1 declaration(s)\"; exit 0;;\n"
                    "  build) cat <<'EOF'\n%s\nEOF\n  exit %d;;\n"
                    "esac\nexit 2\n" % (build_output, build_rc))
    path.chmod(path.stat().st_mode | stat.S_IXUSR)


REFUSAL = ("error: no library artifact was emitted; 1 of 1 computational declaration(s) refused:\n"
           "  | `min2` [%s]: independent source/SSA gate refused this body\n"
           "The whole artifact was refused; no partial library is written.")


class FakeTools:
    def __init__(self, targo):
        self.targo, self.cli, self.cc, self.trustc = str(targo), "/nonexistent/trust-ir", "cc", None


class StandaloneRefusalClassChange(unittest.TestCase):
    """The negative twin of the STANDALONE rows: the needle is the WHOLE refusal, pinned by expected.json."""

    def measure(self, klass):
        with tempfile.TemporaryDirectory(dir=str(ROOT / "build") if (ROOT / "build").is_dir() else None) as td:
            targo = Path(td) / "targo"
            stub_targo(targo, REFUSAL % klass)
            pl = J.PartALean(td, FakeTools(targo))
            R = J.Rows()
            pl.standalone(R, "p02_if_select")
            return R.rows

    def test_pinned_refusal_holds(self):
        rows = self.measure("gate/target-shape")
        self.assertEqual(rows[0]["verdict"], "GAP")
        self.assertEqual(rows[0]["signature"], "`min2` [gate/target-shape]:independent source/SSA gate refused this body")

    def test_class_change_reads_fail_not_gap(self):
        pin = {"ratchets": {"STANDALONE.p02_if_select": {
            "verdict": "GAP", "class": "producer-gap",
            "signature": "`min2` [gate/target-shape]:independent source/SSA gate refused this body"}}}
        rows = self.measure("carrier/no-total-carrier")
        self.assertEqual(rows[0]["verdict"], "GAP")          # still a named refusal of the pinned declaration ...
        status = {i: s for i, s, _ in J.compare(rows, pin)}
        self.assertEqual(status["STANDALONE.p02_if_select"], "FAIL")   # ... but NOT the pinned one

    def test_a_refusal_that_names_another_declaration_is_fail(self):
        with tempfile.TemporaryDirectory(dir=str(ROOT / "build") if (ROOT / "build").is_dir() else None) as td:
            targo = Path(td) / "targo"
            stub_targo(targo, (REFUSAL % "gate/target-shape").replace("`min2`", "`other`"))
            R = J.Rows()
            J.PartALean(td, FakeTools(targo)).standalone(R, "p02_if_select")
        self.assertEqual(R.rows[0]["verdict"], "FAIL")


# ---- the MUTATION: the proof program's repair_fndef.py, applied unconditionally (F-120 (1)).  It lives in
# this test and nowhere else; the judge rewrites no module.
def unconditional_repair_fndef(text):
    lines = text.split("\n")
    fn_ty, idx = {}, 0
    for l in lines:
        m = re.match(r'^(?:[\w"-]+ )*fn @.*\(functy\.(\d+)\) \{', l)
        if m:
            fn_ty[idx] = int(m.group(1))
            idx += 1
    ph = set(int(m.group(1)) for l in lines for m in [re.search(r"const functy\.(\d+) fndef<", l)] if m)
    out = []
    for l in lines:
        m = re.match(r"^(functy\.\d+ = )\((.*)\)( -> .*)$", l)
        if m:
            params = [("ptr" if re.fullmatch(r"functy\.(\d+)", p.strip()) and int(p.strip()[7:]) in ph else p.strip())
                      for p in m.group(2).split(",")] if m.group(2).strip() else []
            l = "%s(%s)%s" % (m.group(1), ", ".join(params), m.group(3))
        out.append(l)
    lines, out, n, i = out, [], 0, 0
    while i < len(lines):
        l = lines[i]
        if re.match(r'^(?:[\w"-]+ )*fn @', l):
            j = i
            while lines[j] != "}":
                j += 1
            body = lines[i:j + 1]
            ids = [int(x) for b in body for x in re.findall(r"%(\d+)", b)]
            nxt = max(ids) + 1 if ids else 0
            nb, ren = [], {}
            for b in body:
                m = re.match(r"^(\s*)%(\d+) = const functy\.(\d+) fndef<func\.(\d+)>(.*)$", b)
                if m:
                    want = fn_ty[int(m.group(4))]
                    nb.append("%s%%%s = const functy.%d fndef<func.%s>%s" % (m.group(1), m.group(2), want, m.group(4), m.group(5)))
                    nb.append("%s%%%d = reify_fn_pointer functy.%d %%%s to ptr" % (m.group(1), nxt, want, m.group(2)))
                    ren[m.group(2)] = str(nxt)
                    nxt += 1
                    n += 1
                    continue
                if (ren and "=" in b) or (ren and re.match(r"^\s*(call|ret|br|store)", b)):
                    head, sep, tail = b.partition(" = ")
                    if not sep:
                        head, tail = "", b
                    tail = re.sub(r"%(\d+)\b", lambda mm: "%" + ren.get(mm.group(1), mm.group(1)), tail)
                    b = head + sep + tail
                nb.append(b)
            out += nb
            i = j + 1
        else:
            out.append(l)
            i += 1
    return "\n".join(out), n


def gitlink_tools():
    tools_dir = os.environ.get("TRUST_IR_RATCHET_TOOLS_DIR", str(J.DEFAULT_TOOLS_DIR))
    targo = os.environ.get("TRUST_IR_RATCHET_TARGO") or shutil.which("targo")
    try:
        return J.Tools(tools_dir, None, targo, need=("trust-ir", "clean", "trust-cg"))
    except J.ToolError as e:
        return str(e)


class UnconditionalRepairMutation(unittest.TestCase):
    def test_unconditional_repair_turns_the_correct_general_modules_red(self):
        tools = gitlink_tools()
        if isinstance(tools, str):
            self.skipTest("gitlink-built judges unavailable (run `scripts/two_language_producer_ratchets.py tools --build`): " + tools)
        (ROOT / "build" / "tmp").mkdir(parents=True, exist_ok=True)
        with tempfile.TemporaryDirectory(dir=str(ROOT / "build" / "tmp")) as td:
            pl = J.PartALean(td, tools)
            decls = [(n, d) for n, _, _, ds in J.TL_PROBES for d in ds]
            base = J.Rows()
            for n, d in decls:
                pl.general_decl(base, n, d)
            as_emitted = {r["id"]: r["verdict"] for r in base.rows if r["id"].endswith(".validate")}
            correct = sorted(i for i, v in as_emitted.items() if v == "PASS")
            real_validate = pl.validate
            touched = set()

            def mutated_validate(path, fmt=None):
                if path.endswith(".trust_ir") and os.sep + "general" + os.sep in path:
                    text, count = unconditional_repair_fndef(Path(path).read_text())
                    if count:
                        touched.add(os.path.basename(path)[:-len(".trust_ir")])
                    mpath = path[:-len(".trust_ir")] + ".mutated.trust_ir"
                    Path(mpath).write_text(text)
                    return real_validate(mpath, fmt)
                return real_validate(path, fmt)
            pl.validate = mutated_validate
            mut = J.Rows()
            for n, d in decls:
                pl.general_decl(mut, n, d)
            mutated = {r["id"]: r["verdict"] for r in mut.rows if r["id"].endswith(".validate")}
        rewritten = sorted("GENERAL.%s.validate" % stem.replace("__", ".") for stem in touched)
        # every module the rewrite touches was correct AS EMITTED, and the rewrite turns each one red
        self.assertTrue(rewritten)
        self.assertEqual([i for i in rewritten if as_emitted.get(i) != "PASS"], [])
        self.assertEqual({i: mutated[i] for i in rewritten}, {i: "FAIL" for i in rewritten})
        # the modules it does not touch keep their verdict: the red is the rewrite's doing
        self.assertEqual({i: mutated[i] for i in correct if i not in rewritten}, {i: "PASS" for i in correct if i not in rewritten})
        # WHICH modules carry a closure FnDef, not HOW MANY. The count used to be asserted as a bare 18
        # ("18 of the pinned clean's 20 emitted modules"), measured against the 5b45b83b8 audit corpus. It went
        # stale the moment a probe was ADDED: `2f8624bd83f` (2026-09-21) added `p12b_width_conversion`, which
        # carries a closure FnDef, so the shape became 19 of 21 and this assertion had been red ever since —
        # while the three assertions above, which are the actual mutation invariant, kept passing. A count told
        # us a number moved; it could not say whether a rewrite had gone inert or a probe had been added, and
        # those need opposite responses.
        #
        # So name the EXCEPTIONS instead. These two emit no closure FnDef for the rewrite to touch, and that is
        # a fact about their Lean bodies, not about the probe list — adding a probe that carries one (the
        # ordinary case) no longer reddens this test, while a module that STOPS carrying one still does, and the
        # failure names it. Adding a probe that legitimately carries none is a real shape change: add it here
        # with the reason.
        no_closure_fndef = {"GENERAL.p09_array_list.arrSize.validate",
                            "GENERAL.p10_closure_higher_order.applyTwice.validate"}
        self.assertEqual(set(correct) - set(rewritten), no_closure_fndef,
                         "the set of emitted modules with no closure FnDef moved; rewritten=%s" % rewritten)


# ---- WS8.8: the "mutating the Clean body changes the value" control, as a ratchet
ROWS = ROOT / "tests" / "two-language-programs"


def unit_view(native, interp, lane="emit"):
    """A load_unit-shaped view: both native lanes print `native`; the verified-emit module's interpreter run
    returns `interp` (None = no module / run failed)."""
    v = {"expect": None, "module_lane": lane,
         "native": {l: {"build_rc": 0, "exec_rc": 0, "stdout": native} for l in ("native-off", "native-adv")}}
    if interp is not None:
        v["module"] = {"run": {"rc": 0, "value": interp}}
    else:
        v["module"] = {"run": {"rc": 1, "error": "no value"}}
    return v


class IslandMutationControl(unittest.TestCase):
    """ir-ta-island_mutant: p10 with ONE island line edited. The control is evidence that the reference
    interpreter executes the Clean body the producer emitted FROM THE SOURCE, and it can only PASS when the
    value moves on every leg it should and stays on every leg it should not."""

    ORIG = (ROWS / "ir-ta10_lean_wrapping_uint64" / "p10_lean_wrapping_uint64.rs").read_text()
    MUT = (ROWS / "ir-ta-island_mutant" / (J.ISLAND_MUTANT_UNIT + ".rs")).read_text()

    def verdicts(self, orig, mut, orig_src=None, mut_src=None):
        R = J.Rows()
        J.island_mutant_control(R, orig, mut, orig_src or self.ORIG, mut_src or self.MUT)
        return {r["id"][len(J.ISLAND_MUTANT_FID) + 1:]: (r["verdict"], r["detail"]) for r in R.rows}

    def test_the_fixture_differs_from_p10_by_exactly_one_island_line(self):
        changed, inside = J.island_line_diff(self.ORIG, self.MUT)
        self.assertEqual(len(changed), 1, changed)
        self.assertTrue(inside)
        self.assertIn("def addmul", changed[0][1])
        # and the row is registered where the battery lists it, after the p10 unit it reads
        self.assertIn("ir-ta-island_mutant", J.ALL_ROWS)
        self.assertLess(J.ALL_ROWS.index("ir-ta10_lean_wrapping_uint64"), J.ALL_ROWS.index("ir-ta-island_mutant"))

    def test_positive_the_value_moves_with_the_island_body(self):
        v = self.verdicts(unit_view("92", "92"), unit_view("93", "93"))
        self.assertEqual({k: x[0] for k, x in v.items()},
                         {"control.one_island_line": "PASS", "control.native_differs": "PASS", "control.differential_fails": "PASS"})

    def test_an_interpreter_that_does_not_track_the_island_is_a_fail(self):
        # the mutant's native value moved, but the interpreter prints the ORIGINAL value on the mutant module:
        # the interpreter is not executing the emitted Clean body (a stub, a folded constant, a copied body)
        v = self.verdicts(unit_view("92", "92"), unit_view("93", "92"))
        self.assertEqual(v["control.native_differs"][0], "PASS")
        self.assertEqual(v["control.differential_fails"][0], "FAIL")
        self.assertIn("did NOT move", v["control.differential_fails"][1])

    def test_a_straight_differential_failure_is_a_fail_not_a_pass(self):
        # interpreter(mutant) differs from BOTH natives: the cross differential "fails" but so does the straight one
        v = self.verdicts(unit_view("92", "92"), unit_view("93", "94"))
        self.assertEqual(v["control.differential_fails"][0], "FAIL")
        self.assertIn("STRAIGHT", v["control.differential_fails"][1])

    def test_an_island_edit_that_does_not_change_the_native_value_is_a_fail(self):
        v = self.verdicts(unit_view("92", "92"), unit_view("92", "92"))
        self.assertEqual(v["control.native_differs"][0], "FAIL")
        self.assertEqual(v["control.differential_fails"][0], "FAIL")

    def test_no_module_on_either_side_is_a_fail_never_a_gap(self):
        v = self.verdicts(unit_view("92", "92"), unit_view("93", None, lane="emit-off"))
        self.assertEqual(v["control.differential_fails"][0], "FAIL")

    def test_a_rust_side_edit_is_not_an_island_mutation(self):
        rust_edit = self.MUT.replace("m::wsum(40, 2)", "m::wsum(41, 2)")
        v = self.verdicts(unit_view("92", "92"), unit_view("94", "94"), mut_src=rust_edit)
        self.assertEqual(v["control.one_island_line"][0], "FAIL")
        # an unchanged twin is not a mutation either
        v = self.verdicts(unit_view("92", "92"), unit_view("92", "92"), mut_src=self.ORIG)
        self.assertEqual(v["control.one_island_line"][0], "FAIL")
        # the header comment block is not part of the comparison: a longer header is not a changed line
        v = self.verdicts(unit_view("92", "92"), unit_view("93", "93"), mut_src="// one\n// two\n// three\n" + self.MUT)
        self.assertEqual(v["control.one_island_line"][0], "PASS")

    def test_a_deleted_island_line_is_a_fail_never_a_traceback(self):
        # WS8.8 review: island_line_diff aligns by line NUMBER, so a twin that DROPS the last line of a
        # trailing island yields exactly one changed pair whose mutant side is None, and `inside` is
        # True. That is a DELETION, not the one-line edit this control is about — and it used to reach
        # `y.strip()` and crash the judge, taking the whole row down with a traceback instead of
        # refusing it. A control that cannot be measured is a FAIL, never a GAP and never a crash.
        island = "fn main() {\n    clean {\n        def f := 1\n        def g := 2\n"
        dropped = "fn main() {\n    clean {\n        def f := 1\n"
        changed, inside = J.island_line_diff(island, dropped)
        self.assertEqual(len(changed), 1, changed)
        self.assertTrue(inside)
        self.assertIsNone(changed[0][2])
        v = self.verdicts(unit_view("92", "92"), unit_view("93", "93"), orig_src=island, mut_src=dropped)
        self.assertEqual(v["control.one_island_line"][0], "FAIL")
        # the mirror (a line APPENDED past the island) was already a FAIL, and stays one
        v = self.verdicts(unit_view("92", "92"), unit_view("93", "93"), orig_src=dropped, mut_src=island)
        self.assertEqual(v["control.one_island_line"][0], "FAIL")


class LinkSymbolEntry(unittest.TestCase):
    """WS5.2: `Function.name` is the link-time symbol, so the judge finds a row's function by its
    `display_path` and hands the CLI the SYMBOL as `--entry` (the CLI binds entries by name)."""

    MODULE = {"functions": [
        {"name": "_RNvCs0_4demo7program", "display_path": "program", "producer": "Trust", "blocks": [{}]},
        {"name": "_RNvNtCs0_4demo1m7program", "display_path": "program", "producer": "Clean", "blocks": [{}]},
        {"name": "!trust_unlinked_callee::00", "display_path": "core::fmt::write", "producer": None, "blocks": []},
    ]}

    def test_the_entry_is_the_rust_definitions_symbol_not_the_clean_rows(self):
        self.assertEqual(J.entry_symbol(self.MODULE), "_RNvCs0_4demo7program")

    def test_a_module_that_names_its_entry_directly_keeps_it(self):
        legacy = {"functions": [{"name": "program", "producer": "Trust", "blocks": [{}]}]}
        self.assertEqual(J.entry_symbol(legacy), "program")
        self.assertEqual(J.entry_symbol(None), "program")

    def test_two_rust_rows_displaying_the_entry_are_not_guessed_between(self):
        twin = copy.deepcopy(self.MODULE)
        twin["functions"].append(dict(twin["functions"][0], name="_RNvCs0_4demo7program2"))
        self.assertEqual(J.entry_symbol(twin), "program", "ambiguity falls back to the label; the CLI then refuses")

    def test_labels_read_the_display_path_and_fall_back_to_the_name(self):
        self.assertEqual(J.fn_label(self.MODULE["functions"][2]), "core::fmt::write")
        self.assertEqual(J.fn_label({"name": "drive"}), "drive")
        self.assertEqual(J.fn_label(None), "")


if __name__ == "__main__":
    unittest.main()
