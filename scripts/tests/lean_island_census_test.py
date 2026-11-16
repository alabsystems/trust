#!/usr/bin/env python3
"""Simulated wire-format controls; no real compiler execution or acceptance claim.

Builders follow trust_lean_census.rs and clean_census.rs. Payload and environment
hashes are synthetic diagnostic labels, not independently checked kernel evidence.
"""

import copy
import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest import mock


ROOT = Path(__file__).resolve().parents[2]
SPEC = importlib.util.spec_from_file_location("lean_island_census", ROOT / "scripts/lean_island_census.py")
census = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(census)
INPUT = "/simulated/lean-islands.rs"


def digest(raw):
    return hashlib.sha256(raw).hexdigest()


def identity(name):
    return {"Str": ["Anon", name]}


def identity_digest(names):
    raw = json.dumps([identity(name) for name in sorted(names)], sort_keys=True,
                     ensure_ascii=False, separators=(",", ":")).encode("utf-8")
    return digest(raw)


def consumed(sources):
    return [{"unit": unit, "bytes": len(source.encode("utf-8")),
             "sha256": digest(source.encode("utf-8"))}
            for unit, source in enumerate(sources)]


def roster(sources, names, *, sequential=False, rejected=False, before=(), tainted=False):
    declarations = []
    source_declarations = []
    for index, name in enumerate(names):
        unit = index % len(sources)
        declarations.append({
            "identity": identity(name), "name": name, "kernel_role": "constant",
            "constant_kind": "Definition", "has_value": True, "noncomputable": False,
            "kernel_payload_sha256": digest(("simulated payload:" + name).encode("utf-8")),
            "ownership": "unattributed" if sequential else "elaborator-introduces",
            "source_declarations": [] if sequential else [index],
            "type_value_and_recursor_dependencies": [], "unresolved_dependencies": [],
            "kernel_classification": {"kind": "computational-candidate"},
            "runtime_classification": "unmeasured",
        })
        if not sequential:
            source_declarations.append({
                "source_declaration": index, "unit": unit,
                "start": 0, "end": len(sources[unit].encode("utf-8")),
                "identity": identity(name), "name": name, "status": "registered",
                "introduced_identities": [identity(name)],
                "resolved_type_and_value_dependencies": [],
            })
    return {
        "schema": census.ROSTER_SCHEMA, "authority": "diagnostic-only",
        "scope": "new-owned-kernel-identities",
        "kernel_payload_hash_format": census.PAYLOAD_HASH_FORMAT,
        "kernel_classification_schema": "trust.lean.kernel-classification/v1",
        "kernel_classification_limits": dict(census.CLASSIFICATION_LIMITS),
        "inputs": consumed(sources),
        "check_execution_schema": "trust.lean.kernel-check-execution/v1",
        "check_mode": "sequential-island" if sequential else "header-first-batch",
        "registration_semantics": "nontransactional-per-declaration" if sequential else "transactional-module",
        "check_rejected": rejected,
        "batch_committed": None if sequential else not rejected,
        "batch_rejected": None if sequential else rejected,
        "sequential_outcome": {
            "registered": list(names),
            "errors": [{"start": 0, "end": 1, "message": "simulated rejection"}] if rejected else [],
        } if sequential else None,
        "source_declaration_metadata": "unavailable-sequential-checker" if sequential else "elaborator-module-outcome",
        "session_tainted": rejected or tainted,
        "owned_before": {"count": len(before), "identities_sha256": identity_digest(before)},
        "owned_after": {"count": len(before) + len(names), "identities_sha256": identity_digest([*before, *names])},
        "removed_owned_identities": [], "source_declarations": source_declarations,
        "declarations": declarations,
        "unattributed_declarations": len(declarations) if sequential else 0,
        "has_lazy_constant_source": False, "discovered_lazy_identities": [],
        "lazy_import_enumeration": "unverified", "runtime_body_universe": "unmeasured",
        "denominator_status": "denominator_unverified",
        "limitations": list(census.ROSTER_LIMITATIONS), "errors": [],
    }


def check(ids, sources, names, *, sequential=False, verification=True,
          rejected=False, before=(), tainted=False):
    mode = "pre-walk-header-first"
    if sequential:
        mode = "post-admission-sequential" if verification else "verification-disabled-sequential"
    return {
        "event": "check", "mode": mode, "islands": list(ids), "rejected": rejected,
        "consumed_inputs": consumed(sources),
        "kernel_roster": roster(sources, names, sequential=sequential, rejected=rejected,
                                 before=before, tainted=tainted),
    }


def boundary():
    return {"event": "program_admissions_boundary", "program_admission_population": "unmeasured",
            "environment_mutation_between_checks": "not-a-complete-payload-census"}


def footer(count):
    return {
        "event": "complete", "status": "island-check-events-complete", "island_count": count,
        "loaded_sources": [{"file": INPUT, "source_map_checksum_sha256": digest(b"simulated source"),
                            "raw_auxiliary_input_bytes": "unmeasured"}],
        "source_map_checksum_scope": census.SOURCE_MAP_CHECKSUM_SCOPE,
        "other_inputs": {"tracked_files": [], "environment_variable_names": [],
                         "raw_file_bytes": "unmeasured", "environment_values": "unmeasured",
                         "general_build_and_proc_macro_io": "unmeasured"},
        "runtime_body_universe": "unmeasured", "denominator_status": "denominator_unverified",
        "unmeasured": list(census.UNMEASURED),
    }


def fixture(*, verification=True, lowering=False, sequential=False, empty=False):
    sources = [] if empty else ["def alpha : Nat := 1", "def beta : Nat := 2"]
    if sequential and not empty:
        sources.append("def gamma : Nat := beta")
    begin = {
        "event": "begin", "input": INPUT, "compiler_version": "simulated transcript; no compiler executed",
        "target": "aarch64-apple-darwin", "edition": "2024",
        "verification_enabled": verification, "direct_lowering": lowering,
        "authority": "diagnostic-only", "scope": "actual-hir-admitted-island-checks",
        "runtime_body_universe": "unmeasured", "denominator_status": "denominator_unverified",
    }
    rows = [{"island": i, "span_lo": i * 100, "span_hi": i * 100 + len(source.encode("utf-8")),
             "def_path_hash": f"DefPathHash(simulated-{i})",
             "parser_text_sha256": digest(source.encode("utf-8")),
             "parser_text_bytes": len(source.encode("utf-8"))}
            for i, source in enumerate(sources)]
    records = [begin, {"event": "inventory", "islands": rows}]
    if sources:
        count = 1 if sequential else len(sources)
        records.append(check(range(count), sources[:count], ["alpha", "beta"][:count]))
    if verification:
        records.append(boundary())
    if sequential and sources:
        records.append(check([1], sources[1:2], ["beta"], sequential=True,
                             verification=verification, before=["alpha"]))
        records.append(check([2], sources[2:], ["gamma"], sequential=True,
                             verification=verification, before=["alpha", "beta"]))
    records.append(footer(len(sources)))
    return records


def encode(records, *, schema=census.SCHEMA):
    """Hash exact independently serialized record bytes, including each newline."""
    previous = None
    lines = []
    for sequence, record in enumerate(copy.deepcopy(records)):
        record.update(schema=schema, sequence=sequence, previous_record_sha256=previous)
        line = json.dumps(record, sort_keys=True, ensure_ascii=False,
                          separators=(",", ":"), allow_nan=False).encode("utf-8") + b"\n"
        lines.append(line)
        previous = digest(line)
    return b"".join(lines)


def decoded(raw):
    return [json.loads(line) for line in raw.splitlines()]


def bind_inventory_text(records, island, source):
    raw = source.encode("utf-8")
    row = records[1]["islands"][island]
    row.update(parser_text_bytes=len(raw), parser_text_sha256=digest(raw),
               span_hi=row["span_lo"] + len(raw))


def poison_line(raw, index, mutate):
    """Keep a malformed JSON spelling, then repair every later chain link.

    This prevents duplicate-key/Unicode tests from passing merely because a
    downstream checksum notices the mutation instead of the parser rejecting it.
    """
    lines = raw.splitlines(keepends=True)
    lines[index] = mutate(lines[index])
    for current in range(index + 1, len(lines)):
        record = json.loads(lines[current])
        record["previous_record_sha256"] = digest(lines[current - 1])
        lines[current] = json.dumps(record, sort_keys=True, ensure_ascii=False,
                                    separators=(",", ":")).encode("utf-8") + b"\n"
    return b"".join(lines)


class LeanIslandCensus(unittest.TestCase):
    def parse(self, records=None, *, raw=None, **kwargs):
        defaults = {"input_path": INPUT, "verification": True, "lowering": False, "exit_code": 0}
        defaults.update(kwargs)
        return census.parse_census(encode(fixture() if records is None else records) if raw is None else raw,
                                   **defaults)

    def diagnostic_only(self, result):
        self.assertEqual(result["binding_status"], "unverified")
        self.assertEqual(result["authority"], "diagnostic-only")
        self.assertEqual(result["runtime_body_universe"], "unmeasured")
        self.assertEqual(result["denominator_status"], "denominator_unverified")
        self.assertIs(result["whole_program_complete"], False)

    def reject(self, mutation, *, records=None, **kwargs):
        records = copy.deepcopy(fixture() if records is None else records)
        mutation(records)
        result = self.parse(records, **kwargs)
        self.assertEqual(result["record_status"], "malformed", result)
        self.assertTrue(result["errors"], result)
        self.diagnostic_only(result)
        return result

    def test_batch_unicode_and_distinct_structural_names_are_observations_only(self):
        records = fixture()
        # The wire preserves UTF-8 text sizes and structural names, including
        # the distinction between the segment "A.B" and two segments A then B.
        source = "def α : Nat := 1 -- λ"
        records[1]["islands"][0].update(parser_text_bytes=len(source.encode()),
                                         parser_text_sha256=digest(source.encode()),
                                         span_hi=len(source.encode()))
        records[2] = check([0, 1], [source, "def beta : Nat := 2"], ["A.B", "α"])
        nested = {"Str": [{"Str": ["Anon", "A"]}, "B"]}
        report = records[2]["kernel_roster"]
        report["declarations"][1].update(identity=nested, name="A.B")
        report["source_declarations"][1].update(identity=nested, name="A.B", introduced_identities=[nested])
        result = self.parse(records)
        self.assertEqual(result["record_status"], "observed-complete", result)
        self.assertEqual(len(result["declarations"]), 2)
        self.assertEqual(result["missing_islands"], [])
        self.assertEqual(result["validated_prefix"], decoded(encode(records)))
        self.diagnostic_only(result)

    def test_zero_island_and_both_sequential_lanes(self):
        for verification in (False, True):
            for empty, sequential in ((True, False), (False, True)):
                with self.subTest(verification=verification, empty=empty):
                    records = fixture(verification=verification, empty=empty, sequential=sequential)
                    result = self.parse(records, verification=verification)
                    self.assertEqual(result["record_status"], "observed-complete", result)
                    self.assertEqual(len(result["checks"]), 0 if empty else 3)
                    self.diagnostic_only(result)
        # Parser-carried empty text and recovered consumed text are distinct
        # measurements; equality is required only with the nested check input.
        records = fixture()
        records[1]["islands"][0].update(parser_text_bytes=0, parser_text_sha256=digest(b""))
        self.assertEqual(self.parse(records)["record_status"], "observed-complete")

    def test_simulated_off_lane_suffix_marker_and_missing_import_keep_sequential_mode(self):
        for source, name in (("def beta : Nat := 2 -- trust_import_comment", "beta"),
                             ("def trust_import_value : Nat := 2", "trust_import_value")):
            with self.subTest(source=source):
                records = fixture(verification=False)
                bind_inventory_text(records, 1, source)
                records[2] = check([0], ["def alpha : Nat := 1"], ["alpha"])
                records.insert(3, check([1], [source], [name], sequential=True,
                                        verification=False, before=["alpha"]))
                result = self.parse(records, verification=False)
                self.assertEqual(result["record_status"], "observed-complete", result)
                suffix = result["checks"][-1]
                self.assertEqual(suffix["mode"], "verification-disabled-sequential")
                self.assertIsNone(suffix["kernel_roster"]["batch_committed"])
                self.assertIsNone(suffix["kernel_roster"]["batch_rejected"])
                self.assertEqual(suffix["kernel_roster"]["sequential_outcome"]["registered"], [name])
                self.diagnostic_only(result)
        records = fixture(verification=False)
        missing_import = "import DefinitelyMissing\n-- trust_import_deferred"
        bind_inventory_text(records, 1, missing_import)
        records[2] = check([0], ["def alpha : Nat := 1"], ["alpha"])
        records[-1] = check([1], [missing_import], [], sequential=True,
                            verification=False, rejected=True, before=["alpha"])
        result = self.parse(records, verification=False, exit_code=1)
        self.assertEqual(result["record_status"], "incomplete", result)
        self.assertEqual(result["process_status"], "failed")
        self.assertEqual(result["missing_islands"], [])
        self.assertTrue(result["checks"][-1]["rejected"])
        self.assertTrue(result["checks"][-1]["kernel_roster"]["sequential_outcome"]["errors"])
        self.assertEqual(len(result["declarations"]), 1)
        self.diagnostic_only(result)

    def test_process_failure_and_unmeasured_exit_preserve_complete_records(self):
        raw = encode(fixture())
        for code, status in ((0, "success"), (1, "failed"), (101, "failed"), (-9, "failed"), (None, "unmeasured")):
            with self.subTest(code=code):
                result = self.parse(raw=raw, exit_code=code)
                self.assertEqual(result["record_status"], "observed-complete", result)
                self.assertEqual(result["process_status"], status)
                self.assertEqual(result["validated_prefix"], decoded(raw))
                self.assertEqual(len(result["declarations"]), 2)
                self.diagnostic_only(result)

    def test_rejected_sequential_retains_partial_registration_and_taint(self):
        records = fixture(sequential=True)
        rejected_source = "def earlier : Nat := later\ndef later : Nat := 1"
        following_source = "def gamma : Nat := later"
        for island, source in ((1, rejected_source), (2, following_source)):
            bind_inventory_text(records, island, source)
        records[4] = check([1], [rejected_source], ["later"],
                           sequential=True, rejected=True, before=["alpha"])
        records = records[:5]
        result = self.parse(records, exit_code=1)
        self.assertEqual(result["record_status"], "incomplete", result)
        self.assertEqual(result["process_status"], "failed")
        self.assertEqual(result["missing_islands"], [2])
        self.assertEqual(result["checks"][-1]["kernel_roster"]["sequential_outcome"]["registered"], ["later"])
        self.assertEqual(result["declarations"][-1],
                         {"check_sequence": 4, "declaration": records[4]["kernel_roster"]["declarations"][0]})
        self.assertTrue(result["checks"][-1]["kernel_roster"]["session_tainted"])
        self.diagnostic_only(result)
        # A later successful check does not clear an earlier rejection.
        records.append(check([2], [following_source], ["gamma"], sequential=True,
                             before=["alpha", "later"], tainted=True))
        self.assertEqual(self.parse(records, exit_code=1)["record_status"], "incomplete")
        self.reject(lambda rows: rows[-1]["kernel_roster"].update(session_tainted=False), records=records)
        self.reject(lambda rows: rows.append(footer(3)), records=records)

    def test_missing_and_damaged_suffix_preserve_exact_validated_prefix(self):
        for raw in (None, b""):
            result = census.parse_census(raw, input_path=INPUT, verification=True, lowering=False, exit_code=1)
            self.assertEqual(result["record_status"], "missing", result)
            self.assertEqual(result["validated_prefix"], [])
        records = fixture()
        prefix = encode(records[:3])
        self.assertEqual(self.parse(records[:1], exit_code=1)["record_status"], "incomplete")
        for tail, kind in ((b'{"unfinished":', "truncated"), (b'{broken}\n', "json"), (b'\xff\n', "json")):
            with self.subTest(kind=kind):
                result = self.parse(raw=prefix + tail, exit_code=-9)
                self.assertNotEqual(result["record_status"], "observed-complete")
                self.assertEqual(result["validated_prefix"], decoded(prefix))
                self.assertEqual(len(result["declarations"]), 2)
                self.assertTrue(any(error["kind"] == kind for error in result["errors"]), result)
        complete = encode(records)
        result = self.parse(raw=complete[:-1])
        self.assertEqual(result["validated_prefix"], decoded(encode(records[:-1])))

    def test_source_recovery_hole_is_retained_but_cannot_complete(self):
        records = fixture(sequential=True)
        del records[4]  # Island 1 could not be recovered; island 2 still ran.
        records[4]["kernel_roster"]["owned_before"] = {"count": 1, "identities_sha256": identity_digest(["alpha"])}
        records[4]["kernel_roster"]["owned_after"] = {"count": 2, "identities_sha256": identity_digest(["alpha", "gamma"])}
        result = self.parse(records[:-1], exit_code=1)
        self.assertEqual(result["record_status"], "incomplete", result)
        self.assertEqual(result["missing_islands"], [1])
        self.assertEqual([row["islands"] for row in result["checks"]], [[0], [2]])
        self.reject(lambda rows: None, records=records)
        self.reject(lambda rows: rows[2].update(islands=[0, 0]))
        self.reject(lambda rows: rows[2].update(islands=[1, 0]))
        self.reject(lambda rows: rows[2].update(islands=[0, 2]))
        self.reject(lambda rows: rows[1]["islands"][1].update(island=0))

    def test_ambiguous_inventory_is_retained_as_a_failed_run_observation(self):
        for lo, hi in ((0, 20), (10, 30)):
            with self.subTest(span=(lo, hi)):
                records = fixture()
                records[1]["islands"][1].update(span_lo=lo, span_hi=hi)
                raw = encode(records[:2])
                result = self.parse(raw=raw, exit_code=1)
                self.assertEqual(result["record_status"], "incomplete", result)
                self.assertIs(result["inventory_ambiguous"], True)
                self.assertEqual(len(result["inventory"]), 2)
                self.assertEqual(result["validated_prefix"], decoded(raw))
                self.assertEqual(result["missing_islands"], [0, 1])
                self.diagnostic_only(result)
                # Rebuilding the complete hash chain cannot authorize checking
                # the ambiguous source order that the compiler would refuse.
                self.reject(lambda rows: None, records=records[:3])
                self.reject(lambda rows: None, records=[*records[:2], boundary(), footer(2)])

    def test_raw_chain_sequence_and_record_order_cannot_be_relabelled(self):
        records = fixture()
        raw = encode(records)
        lines = raw.splitlines(keepends=True)
        for key, value in (("sequence", 17), ("sequence", True), ("previous_record_sha256", "0" * 64)):
            with self.subTest(key=key, value=value):
                changed = json.loads(lines[2])
                changed[key] = value
                poisoned = b"".join(lines[:2]) + json.dumps(changed).encode() + b"\n" + b"".join(lines[3:])
                result = self.parse(raw=poisoned)
                self.assertEqual(result["record_status"], "malformed", result)
                self.assertEqual(result["validated_prefix"], decoded(b"".join(lines[:2])))
                self.assertTrue(any(error["kind"] == "chain" for error in result["errors"]), result)
        # Whitespace leaves JSON meaning intact but changes the chained bytes.
        result = self.parse(raw=lines[0] + b" " + b"".join(lines[1:]))
        self.assertEqual(result["record_status"], "malformed", result)
        self.reject(lambda rows: rows.append(footer(2)))
        self.reject(lambda rows: rows.insert(2, copy.deepcopy(rows[1])))

    def test_strict_json_unicode_nesting_and_unknown_fields(self):
        raw = encode(fixture())
        duplicate = poison_line(raw, 0, lambda line: line.replace(
            b'"event":"begin"', b'"event":"begin","event":"begin"', 1))
        nested_duplicate = poison_line(raw, 2, lambda line: line.replace(
            b'"has_value":true', b'"has_value":true,"has_value":true', 1))
        nonfinite = poison_line(raw, 1, lambda line: line.replace(b'"span_lo":0', b'"span_lo":NaN', 1))
        surrogate = poison_line(raw, 0, lambda line: line.replace(
            b'simulated transcript; no compiler executed', b'\\ud800', 1))
        for malformed in (duplicate, nested_duplicate, nonfinite, surrogate, b'\xff\n', b'\n',
                          b'[' * 2000 + b'0' + b']' * 2000 + b'\n'):
            with self.subTest(prefix=malformed[:50]):
                result = self.parse(raw=malformed)
                self.assertEqual(result["record_status"], "malformed", result)
                self.diagnostic_only(result)
        self.reject(lambda rows: rows[2]["kernel_roster"].update(verified=True))
        self.reject(lambda rows: rows[2]["kernel_roster"]["declarations"][0].update(hidden_body="opaque"))

    def test_small_resource_limits_preserve_the_valid_prefix_and_name_the_limit(self):
        raw = encode(fixture())
        lines = raw.splitlines(keepends=True)
        checked_prefix = b"".join(lines[:3])
        record_limit = max(map(len, lines[:2]))
        self.assertGreater(len(lines[2]), record_limit)
        # A cap one byte into the next record retains the completed check and
        # its declarations. Invalid bytes beyond the cap must not be parsed.
        byte_limit = len(checked_prefix) + 1
        beyond_cap = checked_prefix + b"{" + b"\xff invalid JSON outside byte cap\n"
        cases = (
            ("MAX_BYTES", byte_limit, 3, raw),
            ("MAX_BYTES", byte_limit, 3, beyond_cap),
            ("MAX_RECORD_BYTES", record_limit, 2, raw),
            ("MAX_RECORDS", 3, 3, raw),
            ("MAX_JSON_DEPTH", 3, 2, raw),
            ("MAX_JSON_NODES", 100, 2, raw),
        )
        for constant, limit, prefix_count, candidate in cases:
            with self.subTest(constant=constant, limit=limit, bytes=len(candidate)):
                with mock.patch.object(census, constant, limit):
                    result = self.parse(raw=candidate, exit_code=1)
                self.assertEqual(result["record_status"], "malformed", result)
                self.assertEqual(result["process_status"], "failed")
                self.assertEqual([error["kind"] for error in result["errors"]], ["resource-limit"], result)
                self.assertEqual(result["errors"][0]["record"], prefix_count)
                self.assertEqual(result["validated_prefix"], decoded(b"".join(lines[:prefix_count])))
                self.assertEqual(len(result["inventory"]), 2)
                self.assertEqual(len(result["checks"]), int(prefix_count == 3))
                self.assertEqual(len(result["declarations"]), 2 if prefix_count == 3 else 0)
                self.assertEqual(result["missing_islands"], [] if prefix_count == 3 else [0, 1])
                self.diagnostic_only(result)

    def test_invocation_schema_and_authority_are_not_self_asserted(self):
        for key, value in (("schema", "unknown/v1"), ("input", "/another/source.rs"),
                           ("verification_enabled", False), ("direct_lowering", True),
                           ("authority", "kernel"), ("denominator_status", "verified"),
                           ("runtime_body_universe", "complete"), ("compiler_version", "unknown")):
            with self.subTest(key=key):
                if key == "schema":
                    raw = encode(fixture()).replace(census.SCHEMA.encode(), value.encode(), 1)
                    self.assertEqual(self.parse(raw=raw)["record_status"], "malformed")
                else:
                    self.reject(lambda rows: rows[0].update({key: value}))
        for kwargs in ({"exit_code": False}, {"verification": 1}, {"lowering": 0}, {"input_path": "relative.rs"}):
            result = self.parse(**kwargs)
            self.assertEqual(result["record_status"], "malformed", result)
            self.assertTrue(any(error["kind"] == "invocation" for error in result["errors"]), result)

    def test_phase_splices_and_missing_or_double_admissions_refuse(self):
        self.reject(lambda rows: rows.pop(3))
        self.reject(lambda rows: rows.insert(3, boundary()))
        off = fixture(verification=False, sequential=True)
        self.reject(lambda rows: rows.insert(3, boundary()), records=off, verification=False)
        self.reject(lambda rows: rows[3].update(mode="post-admission-sequential"), records=off, verification=False)
        on = fixture(sequential=True)
        self.reject(lambda rows: rows[4].update(mode="verification-disabled-sequential"), records=on)
        # An increasing island ID is insufficient to permit a late batch.
        off[4] = check([2], ["def gamma : Nat := beta"], ["gamma"], before=["alpha", "beta"])
        self.reject(lambda rows: None, records=off, verification=False)

    def test_spliced_nested_check_semantics_and_outcomes_refuse(self):
        sequential = fixture(sequential=True)
        for key, value in (("batch_committed", False), ("batch_rejected", False),
                           ("check_mode", "header-first-batch"), ("check_rejected", True),
                           ("registration_semantics", "transactional-module"),
                           ("source_declaration_metadata", "elaborator-module-outcome")):
            with self.subTest(key=key):
                self.reject(lambda rows: rows[4]["kernel_roster"].update({key: value}), records=sequential)
        self.reject(lambda rows: rows[2]["kernel_roster"].update(sequential_outcome={"registered": [], "errors": []}))
        self.reject(lambda rows: rows[4]["kernel_roster"].update(source_declarations=[copy.deepcopy(rows[2]["kernel_roster"]["source_declarations"][0])]), records=sequential)

    def test_exact_input_units_lengths_hashes_and_counts(self):
        self.reject(lambda rows: rows[2]["kernel_roster"]["inputs"][0].update(sha256="f" * 64))
        self.reject(lambda rows: rows[2]["kernel_roster"]["inputs"].pop())
        for key, value in (("unit", True), ("unit", 3), ("bytes", -1), ("sha256", "A" * 64)):
            with self.subTest(key=key, value=value):
                def mutate(rows):
                    rows[2]["consumed_inputs"][0][key] = value
                    rows[2]["kernel_roster"]["inputs"][0][key] = value
                self.reject(mutate)
        for count in (True, 1, 3):
            self.reject(lambda rows: rows[-1].update(island_count=count))
        self.reject(lambda rows: rows[2]["kernel_roster"]["owned_after"].update(count=99))
        self.reject(lambda rows: rows[2]["kernel_roster"].update(unattributed_declarations=1))

    def test_structural_identity_owner_and_source_references_are_checked(self):
        self.reject(lambda rows: rows[2]["kernel_roster"]["declarations"][1].update(identity=identity("alpha")))
        self.reject(lambda rows: rows[2]["kernel_roster"]["declarations"][0].update(source_declarations=[99]))
        self.reject(lambda rows: rows[2]["kernel_roster"]["declarations"][0].update(source_declarations=[0, 0]))
        self.reject(lambda rows: rows[2]["kernel_roster"]["declarations"][0].update(identity={"Str": ["Anon", 7]}))
        self.reject(lambda rows: rows[2]["kernel_roster"]["source_declarations"][0].update(unit=2))
        self.reject(lambda rows: rows[2]["kernel_roster"]["source_declarations"][0].update(end=10000))
        self.reject(lambda rows: rows[2]["kernel_roster"]["source_declarations"][1].update(source_declaration=0))
        self.reject(lambda rows: rows[2]["kernel_roster"]["declarations"][0].update(kernel_classification={"kind": "gate"}))

    def test_source_and_unmeasured_populations_cannot_be_silently_replaced(self):
        self.reject(lambda rows: rows[-1].update(loaded_sources=[]))
        self.reject(lambda rows: rows[-1]["loaded_sources"].append(copy.deepcopy(rows[-1]["loaded_sources"][0])))
        self.reject(lambda rows: rows[-1]["loaded_sources"][0].update(file="relative.rs"))
        self.reject(lambda rows: rows[-1]["loaded_sources"][0].update(source_map_checksum_sha256="fake"))
        self.reject(lambda rows: rows[-1].update(source_map_checksum_scope="raw bytes attested"))
        self.reject(lambda rows: rows[-1].update(unmeasured=[]))
        self.reject(lambda rows: rows[-1]["other_inputs"].update(environment_values="verified"))
        self.reject(lambda rows: rows[-1]["other_inputs"].update(tracked_files=["/a", "/a"]))
        self.reject(lambda rows: rows[-1]["other_inputs"].update(environment_variable_names=["FLAG", "FLAG"]))
        self.reject(lambda rows: rows[2]["kernel_roster"].update(limitations=[]))

    def test_simulated_local_labels_and_binary_surrogate_do_not_attest_raw_bytes(self):
        # These absolute labels model a relative root/module invocation and
        # remapped display paths. This fixture does not execute either behavior.
        records = fixture()
        root = "/simulated/project/src/root.rs"
        module = "/simulated/project/src/leaf.rs"
        binary = "/simulated/project/assets/non-utf8.bin"
        records[0]["input"] = root
        records[-1]["loaded_sources"] = sorted([
            {"file": root, "source_map_checksum_sha256": digest(b"mod leaf;"),
             "raw_auxiliary_input_bytes": "unmeasured"},
            {"file": module, "source_map_checksum_sha256": digest(b"simulated module source"),
             "raw_auxiliary_input_bytes": "unmeasured"},
            {"file": binary, "source_map_checksum_sha256": digest(b""),
             "raw_auxiliary_input_bytes": "unmeasured"},
        ], key=lambda row: row["file"])
        records[-1]["other_inputs"].update(tracked_files=[binary], environment_variable_names=["BUILD_LABEL"])
        result = self.parse(records, input_path=root)
        self.assertEqual(result["record_status"], "observed-complete", result)
        source = next(row for row in result["validated_prefix"][-1]["loaded_sources"] if row["file"] == binary)
        self.assertEqual(source["source_map_checksum_sha256"], digest(b""))
        self.assertNotEqual(source["source_map_checksum_sha256"], digest(b"\xff\x80\x00"))
        self.assertEqual(source["raw_auxiliary_input_bytes"], "unmeasured")
        self.assertEqual(result["validated_prefix"][-1]["other_inputs"], records[-1]["other_inputs"])
        self.diagnostic_only(result)
        self.reject(lambda rows: rows[-1]["loaded_sources"][0].update(file="assets/non-utf8.bin"),
                    records=records, input_path=root)
        self.reject(lambda rows: rows[-1]["loaded_sources"][0].update(raw_auxiliary_input_bytes="attested"),
                    records=records, input_path=root)

    def test_kernel_gaps_remain_observed_without_becoming_executable_evidence(self):
        records = fixture()
        report = records[2]["kernel_roster"]
        first, second = report["declarations"]
        first.update(noncomputable=True, has_value=False, constant_kind="Axiom", kernel_payload_sha256=None,
                     kernel_classification={"kind": "unknown", "reason": "simulated classification bound"},
                     type_value_and_recursor_dependencies=[identity("external")],
                     unresolved_dependencies=[identity("external")])
        second.update(kernel_role="recursor", has_value=False,
                      kernel_classification={"kind": "primitive-candidate"})
        report.update(has_lazy_constant_source=True, discovered_lazy_identities=[identity("external")],
                      errors=["simulated payload serialization failure"])
        result = self.parse(records)
        self.assertEqual(result["record_status"], "observed-complete", result)
        self.assertEqual([row["declaration"] for row in result["declarations"]], report["declarations"])
        self.assertEqual(result["checks"][0]["kernel_roster"]["errors"], report["errors"])
        self.diagnostic_only(result)

    def test_cli_renders_diagnostics_and_rejects_deep_or_surrogate_json(self):
        regular = encode(fixture())
        surrogate = poison_line(regular, 0, lambda line: line.replace(
            b'simulated transcript; no compiler executed', b'\\ud800', 1))
        deep = b'[' * 2000 + b'0' + b']' * 2000 + b'\n'
        with tempfile.TemporaryDirectory(prefix="lean-census-simulated-test-") as directory:
            path = Path(directory) / "simulated.jsonl"
            for raw, code, process_status, record_status in (
                (regular, None, "unmeasured", "observed-complete"),
                (regular, 0, "success", "observed-complete"),
                (regular, 1, "failed", "observed-complete"),
                (surrogate, 0, "success", "malformed"),
                (deep, 0, "success", "malformed"),
            ):
                with self.subTest(record_status=record_status, code=code):
                    path.write_bytes(raw)
                    command = [sys.executable, "-B", str(ROOT / "scripts/lean_island_census.py"),
                               "--census", str(path), "--input", INPUT,
                               "--verification", "on", "--lowering", "off"]
                    if code is not None:
                        command += ["--compiler-exit-code", str(code)]
                    completed = subprocess.run(command, capture_output=True, text=True, timeout=10)
                    self.assertEqual(completed.returncode, 2 if record_status == "malformed" else 0,
                                     completed.stderr)
                    result = json.loads(completed.stdout)
                    self.assertEqual(result["record_status"], record_status)
                    self.assertEqual(result["process_status"], process_status)
                    self.diagnostic_only(result)

def resolver_fixture(*, verification=False, empty=False, deferred=False):
    records = fixture(verification=verification, empty=empty)
    records[0]["scope"] = "actual-root-fragment-and-hir-island-checks"
    records[-1]["unmeasured"] = list(census.UNMEASURED_V2)
    rows = []
    for source in records[1]["islands"]:
        row = {key: value for key, value in source.items() if key != "def_path_hash"}
        row["reported_at_parse"] = False
        rows.append(row)
    root = {"event": "resolver_inventory", "islands": rows,
            "check_islands": [] if deferred else list(range(len(rows)))}
    extra = [root]
    if rows and not deferred:
        observed = copy.deepcopy(records[2])
        observed.update(event="resolver_check", mode="root-fragment-header-first")
        extra.append(observed)
    return [records[0], *extra, *records[1:]]


class ResolverIslandCensus(unittest.TestCase):
    def parse(self, records=None, *, exit_code=0, raw=None, verification=False):
        records = resolver_fixture(verification=verification) if records is None else records
        raw = encode(records, schema=census.SCHEMA_V2) if raw is None else raw
        return census.parse_census(raw, input_path=INPUT, verification=verification,
                                   lowering=False, exit_code=exit_code)

    def test_fresh_sessions_keep_same_names_separate_without_count_inflation(self):
        for verification in (False, True):
            with self.subTest(verification=verification):
                result = self.parse(verification=verification)
                self.assertEqual(result["record_status"], "observed-complete", result)
                self.assertEqual(len(result["declarations"]), 2)
                self.assertEqual(len(result["resolver_declarations"]), 2)
                self.assertEqual([x["declaration"]["identity"] for x in result["declarations"]],
                                 [x["declaration"]["identity"] for x in result["resolver_declarations"]])
                self.assertEqual(len(result["checks"]), 1)
                self.assertEqual(len(result["resolver_checks"]), 1)
                self.assertNotEqual(result["checks"][0]["kernel_roster"]["owned_before"],
                                    result["resolver_checks"][0]["kernel_roster"]["owned_after"])
                self.assertFalse(result["whole_program_complete"])
                self.assertEqual(result["denominator_status"], "denominator_unverified")

    def test_rejected_resolver_attempt_retains_sources_without_hir_or_footer(self):
        records = resolver_fixture()[:3]
        root = records[2]
        root["rejected"] = True
        roster = root["kernel_roster"]
        roster.update(check_rejected=True, session_tainted=True,
                      batch_rejected=True, batch_committed=False, declarations=[])
        roster["owned_after"] = copy.deepcopy(roster["owned_before"])
        for row in roster["source_declarations"]:
            row["status"] = "refused"
        result = self.parse(records, exit_code=1)
        self.assertEqual(result["record_status"], "incomplete", result)
        self.assertEqual(result["process_status"], "failed")
        self.assertEqual(len(result["validated_prefix"]), 3)
        self.assertIsNone(result["inventory"])
        self.assertEqual(result["declarations"], [])
        self.assertEqual(len(result["resolver_checks"][0]["kernel_roster"]["source_declarations"]), 2)
        self.assertTrue(result["resolver_checks"][0]["rejected"])
        self.assertEqual(result["missing_resolver_islands"], [])

    def test_empty_and_deferred_roots_do_not_fabricate_a_kernel_check(self):
        for options in ({"empty": True}, {"deferred": True}):
            with self.subTest(options=options):
                result = self.parse(resolver_fixture(**options))
                self.assertEqual(result["record_status"], "observed-complete", result)
                self.assertEqual(result["resolver_checks"], [])
                self.assertEqual(result["resolver_declarations"], [])
                self.assertEqual(result["missing_resolver_islands"], [])

    def test_early_failure_or_timeout_retains_unchecked_selected_prefix(self):
        records = resolver_fixture()[:2]
        for code in (1, None):
            result = self.parse(records, exit_code=code)
            self.assertEqual(result["record_status"], "incomplete", result)
            self.assertEqual(result["missing_resolver_islands"], [0, 1])
            self.assertEqual(result["resolver_checks"], [])
            self.assertEqual(len(result["resolver_inventory"]), 2)

    def test_parser_failure_can_remain_begin_only(self):
        result = self.parse(resolver_fixture()[:1], exit_code=1)
        self.assertEqual(result["record_status"], "incomplete", result)
        self.assertIsNone(result["resolver_inventory"])
        self.assertIsNone(result["inventory"])

    def test_resolver_and_hir_populations_may_differ_without_implicit_matching(self):
        records = resolver_fixture()
        # A later expansion can add HIR islands; neither set is inferred from
        # the other. Preserve a smaller actual root-fragment observation.
        records[1]["islands"].pop()
        records[1]["check_islands"] = [0]
        source = "def alpha : Nat := 1"
        records[2].update(islands=[0], consumed_inputs=consumed([source]),
                          kernel_roster=roster([source], ["alpha"]))
        result = self.parse(records)
        self.assertEqual(result["record_status"], "observed-complete", result)
        self.assertEqual(len(result["resolver_inventory"]), 1)
        self.assertEqual(len(result["inventory"]), 2)
        self.assertEqual(len(result["resolver_declarations"]), 1)
        self.assertEqual(len(result["declarations"]), 2)

    def test_proof_primitive_unknown_and_bodyless_resolver_rows_are_retained(self):
        for kind in ("proof-only", "primitive-candidate", "unknown"):
            records = resolver_fixture()
            row = records[2]["kernel_roster"]["declarations"][0]
            row["kernel_classification"] = {"kind": kind}
            if kind == "unknown":
                row["kernel_classification"]["reason"] = "simulated classification budget exhausted"
            elif kind == "primitive-candidate":
                row.update(kernel_role="recursor", has_value=False)
            else:
                row["constant_kind"] = "Theorem"
            result = self.parse(records)
            self.assertEqual(result["record_status"], "observed-complete", result)
            self.assertEqual(result["resolver_declarations"][0]["declaration"], row)
            self.assertEqual(row["runtime_classification"], "unmeasured")

    def test_resolver_phase_prefix_and_source_splices_are_refused(self):
        mutations = [
            lambda r: r.pop(1),
            lambda r: r.pop(2),
            lambda r: r.insert(2, copy.deepcopy(r[1])),
            lambda r: r.insert(3, copy.deepcopy(r[2])),
            lambda r: r[1].update(check_islands=[1]),
            lambda r: r[2].update(islands=[0]),
            lambda r: r[2].update(mode="pre-walk-header-first"),
            lambda r: r[2]["consumed_inputs"][0].update(sha256="0" * 64),
            lambda r: r[2]["kernel_roster"]["inputs"][0].update(bytes=999),
            lambda r: r[2].update(rejected=True),
            lambda r: r[1]["islands"][0].update(def_path_hash="invented"),
            lambda r: r[1]["islands"][0].update(reported_at_parse="false"),
            lambda r: r[-1].update(unmeasured=list(census.UNMEASURED)),
        ]
        for index, mutate in enumerate(mutations):
            with self.subTest(mutation=index):
                records = resolver_fixture()
                mutate(records)
                result = self.parse(records)
                self.assertEqual(result["record_status"], "malformed", result)
                self.assertFalse(result["whole_program_complete"])

    def test_resolver_rejection_and_taint_cannot_gain_completion(self):
        for rejected in (False, True):
            records = resolver_fixture()
            root = records[2]
            root["rejected"] = rejected
            root["kernel_roster"].update(check_rejected=rejected, session_tainted=True,
                                         batch_rejected=rejected)
            result = self.parse(records)
            self.assertEqual(result["record_status"], "malformed", result)
            # Retain both independently valid observed sessions. Root taint
            # forbids completion; it does not taint the fresh HIR environment.
            self.assertEqual(len(result["resolver_checks"]), 1)
            self.assertEqual(len(result["checks"]), 1)
            self.assertFalse(result["checks"][0]["kernel_roster"]["session_tainted"])

    def test_legacy_v1_remains_strict_and_schema_changes_preserve_prefix(self):
        legacy = census.parse_census(encode(fixture()), input_path=INPUT,
                                    verification=True, lowering=False, exit_code=0)
        self.assertEqual(legacy["record_status"], "observed-complete", legacy)
        self.assertIsNone(legacy["resolver_inventory"])
        legacy_event = fixture()
        legacy_event.insert(1, resolver_fixture()[1])
        result = census.parse_census(encode(legacy_event), input_path=INPUT,
                                    verification=True, lowering=False, exit_code=0)
        self.assertEqual(result["record_status"], "malformed")
        self.assertEqual(len(result["validated_prefix"]), 1)
        raw = encode(resolver_fixture(), schema=census.SCHEMA_V2)
        raw = poison_line(raw, 2, lambda line: line.replace(census.SCHEMA_V2.encode(), census.SCHEMA.encode()))
        result = self.parse(raw=raw)
        self.assertEqual(result["record_status"], "malformed")
        self.assertEqual(len(result["validated_prefix"]), 2)


# LEAN-CENSUS-IMPORT-BATCH-1: census v3. The resolver checks the root prefix
# [0]; HIR checks the same prefix header-first, records the admission boundary
# (both lanes: TG3 mints admissions with verification off too), then checks the
# deferred suffix [1, 2] as TG14's ONE import batch.
IMPORT_SOURCES = ["def alpha : Nat := 1",
                  "theorem beta : trust_import_probe__first 1 = 1 := rfl",
                  "def gamma : Nat := alpha"]
ADMITTED = "trust_import_probe__first"


def import_roster(sources, names, *, refused=(), rejected=None, before=(), tainted=False):
    """`check_import_islands_with_census`: no module outcome, every declaration
    unattributed, and the refused original units named."""
    rejected = bool(refused) if rejected is None else rejected
    report = roster(sources, names, rejected=rejected, before=before)
    for row in report["declarations"]:
        row.update(ownership="unattributed", source_declarations=[])
    report.update(source_declarations=[], unattributed_declarations=len(names),
                  batch_committed=not rejected,
                  source_declaration_metadata="unavailable-from-import-wrapper",
                  session_tainted=tainted,
                  import_recovery={"refused_units": list(refused),
                                   "all_original_sources_retained": True,
                                   "survivors_checked_together": True})
    return report


def import_check(ids, sources, names, *, verification=True, refused=(), rejected=None,
                 before=(), tainted=False):
    rejected = bool(refused) if rejected is None else rejected
    return {
        "event": "check",
        "mode": "post-admission-import-batch" if verification else "verification-disabled-import-batch",
        "islands": list(ids), "rejected": rejected, "consumed_inputs": consumed(sources),
        "kernel_roster": import_roster(sources, names, refused=refused, rejected=rejected,
                                       before=before, tainted=tainted),
    }


def import_fixture(*, verification=True, refused=(), rejected=None, tainted=False, complete=True):
    """[begin, resolver_inventory, resolver_check, inventory, check [0], boundary,
    import batch [1, 2], footer]; unit u of the batch is island u + 1."""
    sources = IMPORT_SOURCES
    rejected = bool(refused) if rejected is None else rejected
    survivors = [] if rejected and not refused else [
        name for unit, name in enumerate(["beta", "gamma"]) if unit not in refused]
    begin = {
        "event": "begin", "input": INPUT, "compiler_version": "simulated transcript; no compiler executed",
        "target": "aarch64-apple-darwin", "edition": "2024",
        "verification_enabled": verification, "direct_lowering": False,
        "authority": "diagnostic-only", "scope": "actual-root-fragment-and-hir-island-checks",
        "runtime_body_universe": "unmeasured", "denominator_status": "denominator_unverified",
    }
    rows = [{"island": i, "span_lo": i * 100, "span_hi": i * 100 + len(source.encode("utf-8")),
             "def_path_hash": f"DefPathHash(simulated-{i})",
             "parser_text_sha256": digest(source.encode("utf-8")),
             "parser_text_bytes": len(source.encode("utf-8"))}
            for i, source in enumerate(sources)]
    root_rows = [{**{key: value for key, value in row.items() if key != "def_path_hash"},
                  "reported_at_parse": False} for row in rows]
    records = [
        begin,
        {"event": "resolver_inventory", "islands": root_rows, "check_islands": [0]},
        {"event": "resolver_check", "mode": "root-fragment-header-first", "islands": [0],
         "rejected": False, "consumed_inputs": consumed(sources[:1]),
         "kernel_roster": roster(sources[:1], ["alpha"])},
        {"event": "inventory", "islands": rows},
        check([0], sources[:1], ["alpha"]),
        boundary(),
        import_check([1, 2], sources[1:], survivors, verification=verification, refused=refused,
                     rejected=rejected, before=["alpha", ADMITTED], tainted=tainted),
    ]
    if complete:
        records.append(import_footer(len(sources)))
    return records


def import_footer(count):
    record = footer(count)
    record["unmeasured"] = list(census.UNMEASURED_V2)
    return record


def no_suffix_fixture(verification):
    """A v3 crate whose islands name no `trust_import_*`: boundary, no suffix."""
    records = import_fixture(verification=verification)
    del records[6]
    records[1]["islands"] = records[1]["islands"][:1]
    records[3]["islands"] = records[3]["islands"][:1]
    records[-1]["island_count"] = 1
    return records


class ImportBatchCensus(unittest.TestCase):
    def parse(self, records, *, verification=True, exit_code=0, schema=census.SCHEMA_V3):
        return census.parse_census(encode(records, schema=schema), input_path=INPUT,
                                   verification=verification, lowering=False, exit_code=exit_code)

    def reject(self, mutation, *, records=None, verification=True, schema=census.SCHEMA_V3):
        records = copy.deepcopy(import_fixture(verification=verification) if records is None else records)
        mutation(records)
        result = self.parse(records, verification=verification, schema=schema)
        self.assertEqual(result["record_status"], "malformed", result)
        self.assertTrue(result["errors"], result)
        self.assertFalse(result["whole_program_complete"])
        return result

    @staticmethod
    def names(result):
        return [row["declaration"]["name"] for row in result["declarations"]]

    def test_both_lanes_record_one_import_batch_after_the_boundary(self):
        for verification in (False, True):
            with self.subTest(verification=verification):
                result = self.parse(import_fixture(verification=verification), verification=verification)
                self.assertEqual(result["record_status"], "observed-complete", result)
                self.assertEqual([row["islands"] for row in result["checks"]], [[0], [1, 2]])
                self.assertEqual([row["mode"] for row in result["checks"]], [
                    "pre-walk-header-first",
                    "post-admission-import-batch" if verification else "verification-disabled-import-batch"])
                self.assertEqual(sum(event["event"] == "program_admissions_boundary"
                                     for event in result["validated_prefix"]), 1)
                self.assertEqual(self.names(result), ["alpha", "beta", "gamma"])
                self.assertEqual(result["missing_islands"], [])
                self.assertEqual(result["checks"][1]["kernel_roster"]["import_recovery"]["refused_units"], [])
                self.assertEqual(result["denominator_status"], "denominator_unverified")

    def test_v3_completion_requires_the_boundary_in_both_lanes(self):
        for verification in (False, True):
            with self.subTest(verification=verification):
                records = no_suffix_fixture(verification)
                result = self.parse(records, verification=verification)
                self.assertEqual(result["record_status"], "observed-complete", result)
                self.reject(lambda rows: rows.pop(5), records=records, verification=verification)

    def test_a_refused_unit_is_excluded_and_its_survivors_commit_without_taint(self):
        for verification in (False, True):
            with self.subTest(verification=verification):
                records = import_fixture(verification=verification, refused=(0,), complete=False)
                result = self.parse(records, verification=verification, exit_code=1)
                self.assertEqual(result["record_status"], "incomplete", result)
                self.assertEqual(result["process_status"], "failed")
                self.assertEqual(result["missing_islands"], [])
                suffix = result["checks"][-1]
                self.assertTrue(suffix["rejected"])
                self.assertFalse(suffix["kernel_roster"]["session_tainted"])
                self.assertFalse(suffix["kernel_roster"]["batch_committed"])
                self.assertEqual(suffix["kernel_roster"]["import_recovery"]["refused_units"], [0])
                self.assertEqual(self.names(result), ["alpha", "gamma"])
                # A rejected suffix never earns the completion footer.
                self.reject(lambda rows: rows.append(import_footer(3)), records=records,
                            verification=verification)

    def test_an_unattributed_rejection_must_keep_its_taint(self):
        self.reject(lambda rows: None, records=import_fixture(rejected=True, complete=False))
        tainted = import_fixture(rejected=True, tainted=True, complete=False)
        self.assertEqual(self.parse(tainted, exit_code=1)["record_status"], "incomplete")
        # A refused unit with a retained global taint is an observation too.
        both = import_fixture(refused=(0,), tainted=True, complete=False)
        self.assertEqual(self.parse(both, exit_code=1)["record_status"], "incomplete")

    def test_an_earlier_taint_cannot_disappear_through_an_import_batch(self):
        records = import_fixture(refused=(0, 1), complete=False)
        records[4] = check([0], IMPORT_SOURCES[:1], ["alpha"], rejected=True)
        self.reject(lambda rows: None, records=records)
        records[-1]["kernel_roster"]["session_tainted"] = True
        result = self.parse(records, exit_code=1)
        self.assertEqual(result["record_status"], "incomplete", result)

    def test_mismatched_import_rosters_are_refused(self):
        def recovery(rows):
            return rows[6]["kernel_roster"]["import_recovery"]

        def suffix(rows):
            return rows[6]["kernel_roster"]

        accepted = import_fixture()
        refused = import_fixture(refused=(0, 1), complete=False)
        cases = [
            ("unit outside the batch", refused, lambda rows: recovery(rows).update(refused_units=[0, 2])),
            ("unsorted units", refused, lambda rows: recovery(rows).update(refused_units=[1, 0])),
            ("duplicate units", refused, lambda rows: recovery(rows).update(refused_units=[0, 0])),
            ("non-integer unit", refused, lambda rows: recovery(rows).update(refused_units=["0"])),
            ("refused unit without a rejection", accepted,
             lambda rows: recovery(rows).update(refused_units=[0])),
            ("lost original sources", accepted,
             lambda rows: recovery(rows).update(all_original_sources_retained=False)),
            ("survivors checked apart", accepted,
             lambda rows: recovery(rows).update(survivors_checked_together=False)),
            ("extra recovery claim", accepted, lambda rows: recovery(rows).update(survivors_committed=True)),
            ("missing recovery", accepted, lambda rows: suffix(rows).pop("import_recovery")),
            ("module metadata", accepted,
             lambda rows: suffix(rows).update(source_declaration_metadata="elaborator-module-outcome")),
            ("uncommitted accepted batch", accepted, lambda rows: suffix(rows).update(batch_committed=False)),
            ("committed rejected batch", refused, lambda rows: suffix(rows).update(batch_committed=True)),
            ("sequential roster", accepted, lambda rows: suffix(rows).update(check_mode="sequential-island")),
            ("per-declaration registration", accepted,
             lambda rows: suffix(rows).update(registration_semantics="nontransactional-per-declaration")),
            ("outer/kernel rejection mismatch", accepted, lambda rows: rows[6].update(rejected=True)),
            ("claimed source ownership", accepted, lambda rows: suffix(rows)["declarations"][0].update(
                ownership="elaborator-introduces", source_declarations=[0])),
            ("recovery on the pre-walk batch", accepted,
             lambda rows: rows[4]["kernel_roster"].update(import_recovery=copy.deepcopy(recovery(rows)))),
        ]
        for label, records, mutate in cases:
            with self.subTest(label):
                self.reject(mutate, records=records)

    def test_an_import_batch_claims_no_source_declaration_rows(self):
        # The wrapper has no module outcome. Source rows on its roster are
        # refused by the import-batch metadata rule itself, not by an earlier
        # ownership rule (this case declares no ownership).
        def mutate(rows):
            rows[6]["kernel_roster"].update(
                source_declarations=roster(IMPORT_SOURCES[1:], ["beta"])["source_declarations"])

        result = self.reject(mutate)
        self.assertIn({"kind": "record", "record": 6, "message": "import batch claims module metadata"},
                      result["errors"])

    def test_import_batch_phase_lane_and_cardinality_are_exact(self):
        def split(verification):
            def mutate(rows):
                rows[6:7] = [
                    import_check([1], IMPORT_SOURCES[1:2], ["beta"], verification=verification,
                                 before=["alpha", ADMITTED]),
                    import_check([2], IMPORT_SOURCES[2:], ["gamma"], verification=verification,
                                 before=["alpha", ADMITTED, "beta"]),
                ]
            return mutate

        def swap(first, second):
            def mutate(rows):
                rows[first], rows[second] = rows[second], rows[first]
            return mutate

        for verification in (False, True):
            other = "verification-disabled-import-batch" if verification else "post-admission-import-batch"
            sequential = "post-admission-sequential" if verification else "verification-disabled-sequential"
            for label, mutate in (
                ("no boundary", lambda rows: rows.pop(5)),
                ("duplicate boundary", lambda rows: rows.insert(5, boundary())),
                ("boundary after the suffix", lambda rows: rows.insert(7, boundary())),
                ("suffix before the boundary", swap(5, 6)),
                ("header batch after the boundary", swap(4, 5)),
                ("two suffix batches", split(verification)),
                ("the other lane's suffix", lambda rows: rows[6].update(mode=other)),
                ("a v2 sequential mode under v3", lambda rows: rows[6].update(mode=sequential)),
                ("an empty suffix", lambda rows: rows[6].update(islands=[], consumed_inputs=[])),
            ):
                with self.subTest(verification=verification, mutation=label):
                    self.reject(mutate, verification=verification)

    def test_v2_keeps_one_meaning_and_v1_v2_transcripts_still_parse(self):
        for verification in (False, True):
            with self.subTest(verification=verification):
                result = self.parse(import_fixture(verification=verification), verification=verification,
                                    schema=census.SCHEMA_V2)
                self.assertEqual(result["record_status"], "malformed", result)
                self.assertTrue(any(error["message"] == "unknown check mode" for error in result["errors"])
                                or not verification, result)
        # v2 has no boundary with verification off; a v3 one is not v2.
        result = self.parse(no_suffix_fixture(False), verification=False, schema=census.SCHEMA_V2)
        self.assertEqual(result["record_status"], "malformed", result)
        # The sequential transcripts the v1/v2 reader accepted are unchanged.
        for records, schema, verification in ((fixture(sequential=True), census.SCHEMA, True),
                                              (fixture(verification=False, sequential=True), census.SCHEMA, False),
                                              (resolver_fixture(), census.SCHEMA_V2, False),
                                              (resolver_fixture(verification=True), census.SCHEMA_V2, True)):
            with self.subTest(schema=schema, verification=verification):
                result = self.parse(records, verification=verification, schema=schema)
                self.assertEqual(result["record_status"], "observed-complete", result)
        # A v2 sequential suffix still parses as v2, and relabelled v3 it is
        # refused: v3 has no sequential suffix mode.
        sequential = resolver_fixture(verification=True)
        sequential[4] = check([0], ["def alpha : Nat := 1"], ["alpha"])
        sequential.insert(6, check([1], ["def beta : Nat := 2"], ["beta"], sequential=True, before=["alpha"]))
        self.assertEqual(self.parse(sequential, schema=census.SCHEMA_V2)["record_status"], "observed-complete")
        result = self.parse(sequential, schema=census.SCHEMA_V3)
        self.assertEqual(result["record_status"], "malformed", result)
        self.assertEqual([error["message"] for error in result["errors"]], ["unknown check mode"])


if __name__ == "__main__":
    unittest.main()
