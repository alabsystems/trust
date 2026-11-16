#!/usr/bin/env python3
"""Strict, reporting-only reader for the compiler's Lean island census.

The hash chain checks transcript consistency, not its provenance. Expected
invocation fields and process exits supplied to this reader are assertions, not
authenticated receipts. A separate bound compiler/input/process harness is
required before relying on the observations. No result grants a runtime-body
denominator, source/producer/proof authority, or a product-completion verdict.

Parse valid prefix records even after compiler failure or a malformed suffix;
never turn a lost check, declaration, or file into an empty measured population.

Schemas: v1 has no resolver records; v2 adds them; v3 (LEAN-CENSUS-IMPORT-BATCH-1)
records the deferred `trust_import_*` suffix as ONE header-first import batch
after the program-admission boundary, which both lanes record. Each schema
accepts only its own check modes and boundary lanes, so no record is read
under another schema's meaning.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re

SCHEMA = "trust.lean.compiler-island-census/v1"
SCHEMA_V2 = "trust.lean.compiler-island-census/v2"
SCHEMA_V3 = "trust.lean.compiler-island-census/v3"
RESOLVER_SCHEMAS = (SCHEMA_V2, SCHEMA_V3)
# The checker each HIR check mode names. A v1/v2 suffix is one sequential
# island per check; a v3 suffix is TG14's single header-first import batch.
CHECK_MODES = {"pre-walk-header-first": "batch", "post-admission-sequential": "sequential",
               "verification-disabled-sequential": "sequential"}
CHECK_MODES_V3 = {"pre-walk-header-first": "batch", "post-admission-import-batch": "import-batch",
                  "verification-disabled-import-batch": "import-batch"}
ROSTER_SCHEMA = "trust.lean.kernel-roster/v1"
MAX_BYTES = 64 * 1024 * 1024
MAX_RECORD_BYTES = 32 * 1024 * 1024
MAX_RECORDS = 100_000
MAX_JSON_DEPTH = 128
MAX_JSON_NODES = 1_000_000
MAX_POPULATION = 1_000_000
UNMEASURED = [
    "pre-hir-resolver-root-fragment-checks-and-minting", "pre-hir-rejected-populations",
    "program-admission-payloads", "preexisting-payload-mutations", "lazy-import-closure",
    "runtime-erasure-specialization-helpers", "general-proc-macro-and-build-io",
]
UNMEASURED_V2 = [
    "pre-root-parser-rejected-populations", "resolver-rust-callee-declaration-payloads",
    "program-admission-payloads", "preexisting-payload-mutations", "lazy-import-closure",
    "runtime-erasure-specialization-helpers", "general-proc-macro-and-build-io",
]
CLASSIFICATION_LIMITS = {
    "type_nodes": 16_384, "type_depth": 128, "telescope_binders": 128,
    "kernel_heartbeats": 100_000,
}
PAYLOAD_HASH_FORMAT = (
    "canonical-json tuple [ConstantInfo, InductiveVal?, ConstructorVal?, RecursorVal?, QuotVal?]"
)
SOURCE_MAP_CHECKSUM_SCOPE = (
    "compiler source-map checksum; binary inputs may have text surrogates, not raw-byte attestation"
)
ROSTER_LIMITATIONS = [
    "Owned identity delta does not measure changed payloads of preexisting identities.",
    "Source ownership is incomplete where public elaboration/kernel metadata omits generated owners.",
    "Sequential checks retain partial registrations on rejection; their registered-name list does not establish source ownership or completeness, and batch transaction fields are inapplicable.",
    "Lazy names are advisory; the kernel source API does not certify exhaustive enumeration.",
    "Dependencies include types and proofs; they are not executable reachability.",
    "Kernel classification describes declaration types only: proof-only/type-family are erasure candidates, never exclusions from this roster or runtime-completeness evidence.",
    "Kernel classification does not check declaration values or grant axiom-policy/source acceptance.",
    "Noncomputable, bodyless and primitive declarations retain their flags/roles independently of kernel classification; an unknown classification remains unmeasured.",
    "Erasure, closure conversion, specialization and runtime/ABI helpers require a separate body census.",
]
COMMON = {"schema", "event", "sequence", "previous_record_sha256"}


class CensusError(ValueError):
    def __init__(self, kind, message):
        super().__init__(message)
        self.kind = kind


def _require(condition, message, kind="record"):
    if not condition:
        raise CensusError(kind, message)


def _keys(value, fields, context):
    _require(type(value) is dict and set(value) == set(fields.split()),
             f"invalid {context} fields")


def _text(value, context, *, empty=False):
    _require(type(value) is str and (empty or bool(value)), f"invalid {context}")
    try:
        value.encode("utf-8")
    except UnicodeError as error:
        raise CensusError("json", f"invalid Unicode in {context}") from error
    return value


def _path(value):
    _text(value, "absolute local input label")
    _require("\0" not in value and Path(value).is_absolute(), "non-absolute or NUL input label")
    return value


def _integer(value, context, maximum=MAX_POPULATION):
    _require(type(value) is int and 0 <= value <= maximum, f"invalid {context}")
    return value


def _boolean(value, context):
    _require(type(value) is bool, f"invalid {context}")
    return value


def _digest(value, context, *, nullable=False):
    _require((nullable and value is None) or (
        type(value) is str and re.fullmatch(r"[0-9a-f]{64}", value)), f"invalid {context}")


def _list(value, context):
    _require(type(value) is list and len(value) <= MAX_POPULATION, f"invalid {context}")
    return value


def _strings(value, context, *, paths=False, unique=False):
    rows = _list(value, context)
    for row in rows:
        _path(row) if paths else _text(row, context)
    if unique:
        _require(len(rows) == len(set(rows)), f"duplicate {context}")
    return rows


def _unique_object(pairs):
    result = {}
    for key, value in pairs:
        _require(key not in result, f"duplicate JSON key: {key}", "json")
        result[key] = value
    return result


def _reject_number(value):
    raise CensusError("json", f"non-integer/nonfinite JSON number: {value}")


def _json_record(line):
    _require(len(line) <= MAX_RECORD_BYTES, "record byte limit exceeded", "resource-limit")
    try:
        value = json.loads(line.decode("utf-8"), object_pairs_hook=_unique_object,
                           parse_constant=_reject_number, parse_float=_reject_number)
    except (UnicodeError, json.JSONDecodeError, RecursionError, ValueError) as error:
        if isinstance(error, CensusError):
            raise
        raise CensusError("json", f"invalid JSON record: {error}") from error
    pending = [(value, 0)]
    nodes = 0
    while pending:
        item, depth = pending.pop()
        nodes += 1
        _require(depth <= MAX_JSON_DEPTH and nodes <= MAX_JSON_NODES,
                 "JSON depth/node limit exceeded", "resource-limit")
        if type(item) is str:
            _text(item, "JSON string", empty=True)
        elif type(item) is dict:
            pending.extend((key, depth + 1) for key in item)
            pending.extend((child, depth + 1) for child in item.values())
        elif type(item) is list:
            pending.extend((child, depth + 1) for child in item)
    return value


def _name(value):
    """Validate actual Clean Name serde; never identify declarations by display name."""
    parts = []
    while value != "Anon":
        _require(type(value) is dict and len(value) == 1, "invalid structural kernel Name")
        tag, pair = next(iter(value.items()))
        _require(tag in {"Str", "Num"} and type(pair) is list and len(pair) == 2,
                 "invalid structural kernel Name component")
        if tag == "Str":
            _text(pair[1], "kernel Name string component", empty=True)
        else:
            _integer(pair[1], "kernel Name numeric component", (1 << 64) - 1)
        parts.append((tag, pair[1]))
        _require(len(parts) <= MAX_JSON_DEPTH, "kernel Name depth limit exceeded", "resource-limit")
        value = pair[0]
    return tuple(reversed(parts))


def _names(values, context):
    keys = [_name(value) for value in _list(values, context)]
    _require(len(keys) == len(set(keys)), f"duplicate {context}")
    return set(keys)


def _inputs(value):
    rows = _list(value, "check inputs")
    for unit, row in enumerate(rows):
        _keys(row, "unit bytes sha256", "check input")
        _require(_integer(row["unit"], "check input unit") == unit, "check units are not consecutive")
        _integer(row["bytes"], "check input bytes", (1 << 32) - 1)
        _digest(row["sha256"], "consumed input hash")
    return rows


def _validate_roster(roster, inputs, kind, rejected, prior_taint):
    import_batch = kind == "import-batch"
    _keys(roster, "schema authority scope kernel_payload_hash_format kernel_classification_schema "
          "kernel_classification_limits inputs check_execution_schema check_mode registration_semantics "
          "check_rejected batch_committed batch_rejected sequential_outcome source_declaration_metadata "
          "session_tainted owned_before owned_after removed_owned_identities source_declarations "
          "declarations unattributed_declarations has_lazy_constant_source discovered_lazy_identities "
          "lazy_import_enumeration runtime_body_universe denominator_status limitations errors"
          + (" import_recovery" if import_batch else ""), "kernel roster")
    fixed = {
        "schema": ROSTER_SCHEMA, "authority": "diagnostic-only", "scope": "new-owned-kernel-identities",
        "kernel_payload_hash_format": PAYLOAD_HASH_FORMAT,
        "kernel_classification_schema": "trust.lean.kernel-classification/v1",
        "check_execution_schema": "trust.lean.kernel-check-execution/v1",
        "lazy_import_enumeration": "unverified", "runtime_body_universe": "unmeasured",
        "denominator_status": "denominator_unverified", "limitations": ROSTER_LIMITATIONS,
    }
    for field, expected in fixed.items():
        _require(roster[field] == expected, f"wrong kernel roster {field}")
    limits = roster["kernel_classification_limits"]
    _keys(limits, "type_nodes type_depth telescope_binders kernel_heartbeats", "classification limits")
    for key, expected in CLASSIFICATION_LIMITS.items():
        _require(type(limits[key]) is int and limits[key] == expected, "wrong classification budget")
    _require(_inputs(roster["inputs"]) == inputs, "roster does not bind consumed inputs")
    _require(_boolean(roster["check_rejected"], "kernel rejection") == rejected,
             "outer/kernel rejection mismatch")
    tainted = _boolean(roster["session_tainted"], "session taint")
    if import_batch:
        # TG14 (check_import_islands): a refused unit is excluded, every original
        # source is kept, and the survivors are checked together. Excluding a
        # unit restores the session's prior taint, so only a rejection
        # attributed to refused units may leave the session untainted.
        recovery = roster["import_recovery"]
        _keys(recovery, "refused_units all_original_sources_retained survivors_checked_together",
              "import recovery")
        refused = [_integer(unit, "refused import unit")
                   for unit in _list(recovery["refused_units"], "refused import units")]
        _require(refused == sorted(set(refused)), "duplicate or unordered refused import units")
        _require(all(unit < len(inputs) for unit in refused), "refused import unit outside the consumed inputs")
        _require(recovery["all_original_sources_retained"] is True
                 and recovery["survivors_checked_together"] is True, "import recovery lost its inputs")
        _require(not refused or rejected, "refused import unit without a rejection")
        _require(tainted or not prior_taint, "session taint disappeared")
        _require(tainted or not rejected or bool(refused), "unattributed import rejection lost its taint")
    else:
        _require(tainted or not (rejected or prior_taint), "session rejection/taint disappeared")
    _boolean(roster["has_lazy_constant_source"], "lazy source flag")
    _names(roster["discovered_lazy_identities"], "lazy identities")
    errors = _strings(roster["errors"], "kernel census errors")
    source_rows = _list(roster["source_declarations"], "source declarations")
    if kind == "sequential":
        _require(roster["check_mode"] == "sequential-island"
                 and roster["registration_semantics"] == "nontransactional-per-declaration"
                 and roster["batch_committed"] is None and roster["batch_rejected"] is None
                 and roster["source_declaration_metadata"] == "unavailable-sequential-checker"
                 and source_rows == [], "sequential roster claims batch metadata")
        outcome = roster["sequential_outcome"]
        _keys(outcome, "registered errors", "sequential outcome")
        _strings(outcome["registered"], "sequential registered display names")
        for error in _list(outcome["errors"], "sequential errors"):
            _keys(error, "start end message", "sequential error")
            start = _integer(error["start"], "error byte start", inputs[0]["bytes"])
            end = _integer(error["end"], "error byte end", inputs[0]["bytes"])
            _require(start <= end, "reversed diagnostic byte span")
            _text(error["message"], "error message")
        _require(bool(outcome["errors"]) == rejected, "sequential rejection lost its exact errors")
    else:
        _require(roster["check_mode"] == "header-first-batch"
                 and roster["registration_semantics"] == "transactional-module"
                 and roster["sequential_outcome"] is None, "batch roster has sequential metadata")
        committed = _boolean(roster["batch_committed"], "batch committed")
        _require(_boolean(roster["batch_rejected"], "batch rejected") == rejected,
                 "batch/outer rejection mismatch")
        _require(committed or rejected, "uncommitted batch with no rejection")
        if import_batch:
            # batch_committed is TG14's: the WHOLE original suffix committed.
            # With refused units, the survivors' commit shows only in the
            # declarations delta. The wrapper has no module outcome, so it
            # claims no source-declaration ownership.
            _require(committed == (not rejected)
                     and roster["source_declaration_metadata"] == "unavailable-from-import-wrapper"
                     and not source_rows, "import batch claims module metadata")
        else:
            _require(roster["source_declaration_metadata"] in {
                "elaborator-module-outcome", "unavailable-before-module-outcome"}, "invalid batch metadata mode")
            if roster["source_declaration_metadata"] == "unavailable-before-module-outcome":
                _require(not committed and not source_rows, "absent module outcome acquired metadata")
    introduced = []
    for index, source in enumerate(source_rows):
        _keys(source, "source_declaration unit start end identity name status introduced_identities "
              "resolved_type_and_value_dependencies", "source declaration")
        _require(_integer(source["source_declaration"], "source index") == index, "wrong source index")
        unit = _integer(source["unit"], "source unit")
        _require(unit < len(inputs), "source owner outside consumed inputs")
        start = _integer(source["start"], "source span start", inputs[unit]["bytes"])
        end = _integer(source["end"], "source span end", inputs[unit]["bytes"])
        _require(start <= end, "reversed source declaration span")
        if source["identity"] is None:
            _require(source["name"] is None, "anonymous declaration has a display name")
        else:
            _name(source["identity"])
            _text(source["name"], "source display name")
        _require(source["status"] in {"registered", "refused", "no-header", "lexical-or-command"},
                 "unknown source declaration status")
        introduced.append(_names(source["introduced_identities"], "introduced identities"))
        _names(source["resolved_type_and_value_dependencies"], "source dependencies")
    rows = _list(roster["declarations"], "kernel declarations")
    identities = set()
    unattributed = 0
    for row in rows:
        _keys(row, "identity name kernel_role constant_kind has_value noncomputable kernel_payload_sha256 "
              "ownership source_declarations type_value_and_recursor_dependencies unresolved_dependencies "
              "kernel_classification runtime_classification", "kernel declaration")
        identity = _name(row["identity"])
        _require(identity not in identities, "duplicate kernel declaration identity")
        identities.add(identity)
        _text(row["name"], "kernel display name")
        _require(row["constant_kind"] in {"Definition", "Theorem", "Opaque", "Axiom"}, "unknown constant kind")
        _require(row["kernel_role"] in {"inductive", "constructor", "recursor", "quotient-primitive", "constant"},
                 "unknown kernel role")
        _boolean(row["has_value"], "body-presence flag")
        _boolean(row["noncomputable"], "noncomputable flag")
        _digest(row["kernel_payload_sha256"], "kernel payload digest", nullable=True)
        _require(row["kernel_payload_sha256"] is not None or errors, "missing payload hash without census error")
        dependencies = _names(row["type_value_and_recursor_dependencies"], "kernel dependencies")
        _require(_names(row["unresolved_dependencies"], "unresolved dependencies") <= dependencies,
                 "unresolved identity outside dependencies")
        owners = _list(row["source_declarations"], "kernel owners")
        for owner in owners:
            _integer(owner, "kernel owner index")
            _require(owner < len(source_rows), "kernel owner outside source declaration roster")
        _require(owners == sorted(set(owners)), "duplicate or unordered kernel owners")
        if row["ownership"] == "unattributed":
            unattributed += 1
            _require(not owners, "unattributed declaration has an owner")
        elif row["ownership"] == "elaborator-introduces":
            _require(bool(owners) and all(identity in introduced[index] for index in owners),
                     "introduced ownership not supported by source metadata")
        elif row["ownership"] == "kernel-inductive-owner":
            _require(bool(owners) and row["kernel_role"] in {"constructor", "recursor"},
                     "invalid primitive ownership metadata")
        else:
            raise CensusError("record", "unknown ownership category")
        classification = row["kernel_classification"]
        _require(type(classification) is dict, "malformed kernel classification")
        if classification.get("kind") == "unknown":
            _keys(classification, "kind reason", "unknown classification")
            _text(classification["reason"], "classification refusal")
        else:
            _keys(classification, "kind", "kernel classification")
            _require(classification["kind"] in {"proof-only", "type-family", "computational-candidate", "primitive-candidate"},
                     "unknown kernel classification")
        _require(row["runtime_classification"] == "unmeasured", "kernel row acquired runtime authority")
    _require(_integer(roster["unattributed_declarations"], "unattributed count") == unattributed,
             "wrong unattributed population")
    removed = _names(roster["removed_owned_identities"], "removed kernel identities")
    _require(not (removed & identities), "kernel identity both added and removed")
    for key in ("owned_before", "owned_after"):
        _keys(roster[key], "count identities_sha256", key)
        _integer(roster[key]["count"], key + " count")
        _digest(roster[key]["identities_sha256"], key + " digest", nullable=True)
        _require(roster[key]["identities_sha256"] is not None or errors,
                 "missing identity hash without census error")
    _require(roster["owned_before"]["count"] >= len(removed)
             and roster["owned_after"]["count"] == roster["owned_before"]["count"] + len(rows) - len(removed),
             "owned kernel population arithmetic mismatch")
    return tainted


def parse_census(raw: bytes | None, *, input_path: str, verification: bool,
                 lowering: bool, exit_code: int | None) -> dict:
    """Validate a transcript without authenticating its source or process claims."""
    result = {
        "record_status": "missing", "process_status": "unmeasured", "binding_status": "unverified",
        "authority": "diagnostic-only", "whole_program_complete": False,
        "runtime_body_universe": "unmeasured", "denominator_status": "denominator_unverified",
        "validated_prefix": [], "inventory": None, "checks": [], "declarations": [],
        "inventory_ambiguous": False, "missing_islands": [], "errors": [],
        # Different fresh kernel sessions: resolver additions never contribute
        # to HIR declaration counts or its environment-continuity checks.
        "resolver_inventory": None, "resolver_checks": [], "resolver_declarations": [],
        "missing_resolver_islands": [],
    }
    index = None
    checked = set()
    resolver_expected = None
    resolver_checked = False
    try:
        _require(type(verification) is bool and type(lowering) is bool,
                 "expected lane flags must be booleans", "invocation")
        _require(type(exit_code) is int or exit_code is None,
                 "process exit must be an integer or unknown", "invocation")
        try:
            _path(input_path)
        except CensusError as error:
            raise CensusError("invocation", str(error)) from error
        result["process_status"] = "unmeasured" if exit_code is None else ("success" if exit_code == 0 else "failed")
        if raw is None or raw == b"":
            result["errors"].append({"kind": "missing", "record": None, "message": "census missing"})
            return result
        _require(type(raw) is bytes, "census must be exact JSONL bytes", "invocation")
        oversized = len(raw) > MAX_BYTES
        # Preserve complete records inside the bounded prefix of an oversized
        # input; never parse or credit the truncated remainder as an event.
        raw = raw[:MAX_BYTES]
        result["record_status"] = "incomplete"
        previous = None
        inventory = None
        inventory_ambiguous = False
        batch_seen = suffix_seen = admissions_seen = rejected_seen = tainted = complete = False
        previous_environment = None
        schema = None
        resolver_inventory = None
        resolver_rejected = resolver_tainted = False
        # LF only: Unicode line separators are legal inside JSON strings.
        lines = raw.split(b"\n")
        for index, line in enumerate(lines[:-1]):
            _require(index < MAX_RECORDS, "record limit exceeded", "resource-limit")
            _require(bool(line) and not line.endswith(b"\r"), "blank or non-LF JSONL record", "json")
            exact_line = line + b"\n"
            event = _json_record(exact_line)
            _require(type(event) is dict, "event is not an object")
            if index == 0:
                schema = event.get("schema")
                _require(schema in (SCHEMA, *RESOLVER_SCHEMAS), "wrong compiler census schema")
            _require(event.get("schema") == schema, "changed compiler census schema")
            _require(type(event.get("sequence")) is int and event["sequence"] == index
                     and event.get("previous_record_sha256") == previous,
                     "record sequence or previous-byte digest mismatch", "chain")
            _require(not complete, "event after completion")
            tag = event.get("event")
            _text(tag, "event type")
            common = {key: value for key, value in event.items() if key not in COMMON}
            _require(COMMON <= event.keys(), "missing common event fields")
            if index == 0:
                _require(tag == "begin", "first event is not begin")
                _keys(common, "input compiler_version target edition verification_enabled direct_lowering "
                      "authority scope runtime_body_universe denominator_status", "begin")
                _require(_path(event["input"]) == input_path, "wrong invocation input")
                _require(_boolean(event["verification_enabled"], "verification flag") == verification
                         and _boolean(event["direct_lowering"], "lowering flag") == lowering, "wrong invocation lane")
                _text(event["compiler_version"], "compiler version")
                _require(event["compiler_version"] != "unknown", "unknown compiler identity")
                _text(event["target"], "target")
                _require(event["edition"] in {"2015", "2018", "2021", "2024"}, "unknown Rust edition")
                _require(event["authority"] == "diagnostic-only" and event["scope"] == ("actual-root-fragment-and-hir-island-checks" if schema in RESOLVER_SCHEMAS
                                                 else "actual-hir-admitted-island-checks")
                         and event["runtime_body_universe"] == "unmeasured"
                         and event["denominator_status"] == "denominator_unverified", "begin acquired broader authority")
            elif tag == "resolver_inventory":
                _require(schema in RESOLVER_SCHEMAS, "resolver event in legacy transcript")
                _keys(common, "islands check_islands", "resolver inventory")
                _require(index == 1 and resolver_inventory is None and inventory is None,
                         "duplicate or misplaced resolver inventory")
                rows = _list(event["islands"], "resolver islands")
                last = None
                for island, row in enumerate(rows):
                    _keys(row, "island span_lo span_hi parser_text_sha256 parser_text_bytes reported_at_parse",
                          "resolver island")
                    _require(_integer(row["island"], "resolver island ID") == island,
                             "resolver IDs are not consecutive")
                    lo = _integer(row["span_lo"], "resolver span low", (1 << 32) - 1)
                    hi = _integer(row["span_hi"], "resolver span high", (1 << 32) - 1)
                    _require(lo <= hi and (last is None or (lo, hi) >= last),
                             "invalid or unordered resolver span")
                    # Ambiguous spans remain observations; they do not define
                    # a cross-stage correspondence or erase either occurrence.
                    last = lo, hi
                    _digest(row["parser_text_sha256"], "resolver source digest")
                    size = _integer(row["parser_text_bytes"], "resolver source bytes", (1 << 32) - 1)
                    _require(size != 0 or row["parser_text_sha256"] == hashlib.sha256(b"").hexdigest(),
                             "empty resolver source has nonempty digest")
                    _boolean(row["reported_at_parse"], "resolver parser diagnostic flag")
                selected = _list(event["check_islands"], "resolver selected islands")
                for island in selected:
                    _integer(island, "resolver selected island ID")
                _require(selected == list(range(len(selected))) and len(selected) <= len(rows),
                         "resolver selected islands are not a bounded prefix")
                resolver_inventory = rows
                resolver_expected = selected
                result["resolver_inventory"] = rows
            elif tag == "resolver_check":
                _require(schema in RESOLVER_SCHEMAS, "resolver event in legacy transcript")
                _keys(common, "mode islands rejected consumed_inputs kernel_roster", "resolver check")
                _require(resolver_inventory is not None and inventory is None and not resolver_checked,
                         "missing, duplicate or misplaced resolver check")
                _require(event["mode"] == "root-fragment-header-first", "wrong resolver check mode")
                ids = _list(event["islands"], "resolver checked islands")
                for island in ids:
                    _integer(island, "resolver checked island ID")
                _require(bool(ids) and ids == resolver_expected, "resolver check lost its exact selected prefix")
                inputs = _inputs(event["consumed_inputs"])
                _require(len(inputs) == len(ids), "resolver check/input population mismatch")
                for island, consumed in zip(ids, inputs):
                    row = resolver_inventory[island]
                    _require(consumed["bytes"] == row["parser_text_bytes"]
                             and consumed["sha256"] == row["parser_text_sha256"],
                             "resolver inventory/consumed text mismatch")
                rejected = _boolean(event["rejected"], "resolver rejection")
                roster = event["kernel_roster"]
                root_taint = _validate_roster(roster, inputs, "batch", rejected, False)
                resolver_checked = True
                resolver_rejected = rejected
                resolver_tainted = root_taint
                result["resolver_checks"].append(event)
                result["resolver_declarations"].extend(
                    {"check_sequence": index, "declaration": row} for row in roster["declarations"])
            elif tag == "inventory":
                _keys(common, "islands", "inventory")
                if schema in RESOLVER_SCHEMAS:
                    _require(resolver_inventory is not None and resolver_checked == bool(resolver_expected),
                             "HIR inventory without expected resolver observations")
                else:
                    _require(index == 1, "misplaced legacy inventory")
                _require(inventory is None, "duplicate inventory")
                inventory = _list(event["islands"], "island inventory")
                identities = set()
                last = None
                for island, row in enumerate(inventory):
                    _keys(row, "island span_lo span_hi def_path_hash parser_text_sha256 parser_text_bytes", "island")
                    _require(_integer(row["island"], "island ID") == island, "inventory IDs are not consecutive")
                    lo = _integer(row["span_lo"], "span low", (1 << 32) - 1)
                    hi = _integer(row["span_hi"], "span high", (1 << 32) - 1)
                    _require(lo <= hi and (last is None or (lo, hi) >= last), "invalid or unordered inventory span")
                    if last is not None and (lo == last[0] or last[1] > lo):
                        inventory_ambiguous = True
                    last = lo, hi
                    identity = _text(row["def_path_hash"], "HIR definition identity")
                    _require(identity not in identities, "duplicate HIR definition identity")
                    identities.add(identity)
                    _digest(row["parser_text_sha256"], "parser text digest")
                    size = _integer(row["parser_text_bytes"], "parser text bytes", (1 << 32) - 1)
                    _require(size != 0 or row["parser_text_sha256"] == hashlib.sha256(b"").hexdigest(),
                             "empty parser payload has nonempty digest")
                result["inventory"] = inventory
                # The compiler records ambiguous HIR spans before its ordinary
                # source-order refusal. Keep that real failed-run inventory,
                # but no subsequent language check or completion can be valid.
                result["inventory_ambiguous"] = inventory_ambiguous
            elif tag == "program_admissions_boundary":
                _keys(common, "program_admission_population environment_mutation_between_checks", "admission phase")
                # v3: TG3 mints program admissions in both lanes, so both record
                # the boundary. v1/v2 recorded it with verification on only.
                _require(inventory is not None and (verification or schema == SCHEMA_V3)
                         and not admissions_seen and not suffix_seen,
                         "misplaced or duplicate program admission phase")
                _require(event["program_admission_population"] == "unmeasured"
                         and event["environment_mutation_between_checks"] == "not-a-complete-payload-census",
                         "program admission phase acquired a measured population")
                admissions_seen = True
                previous_environment = None  # This explicitly UNMEASURED mutation breaks continuity.
            elif tag == "check":
                _keys(common, "mode islands rejected consumed_inputs kernel_roster", "check")
                _require(inventory is not None, "check before inventory")
                _require(not inventory_ambiguous, "language check after ambiguous source-order inventory")
                mode = event["mode"]
                _require(type(mode) is str, "invalid check mode")
                kind = (CHECK_MODES_V3 if schema == SCHEMA_V3 else CHECK_MODES).get(mode)
                if kind is None:
                    raise CensusError("record", "unknown check mode")
                enabled_phase = mode.startswith("post-admission-")
                if kind == "batch":
                    _require(not batch_seen and not admissions_seen and not suffix_seen,
                             "header-first check after its phase")
                elif kind == "import-batch":
                    # One import batch, after the boundary, in the lane that ran.
                    _require(admissions_seen and not suffix_seen and verification == enabled_phase,
                             "import batch outside its admission phase or lane")
                elif enabled_phase:
                    _require(verification and admissions_seen, "sequential check before program admissions")
                else:
                    _require(not verification and not admissions_seen, "verification-disabled check in enabled lane")
                ids = _list(event["islands"], "checked island IDs")
                _require(bool(ids) and (kind != "sequential" or len(ids) == 1), "wrong checked island population")
                for island in ids:
                    _integer(island, "checked island ID")
                _require(ids == sorted(set(ids)) and not checked.intersection(ids)
                         and all(island < len(inventory) for island in ids)
                         and (not checked or ids[0] > max(checked)), "duplicate, missing or reordered checked island")
                inputs = _inputs(event["consumed_inputs"])
                _require(len(inputs) == len(ids), "check/input population mismatch")
                for island, consumed in zip(ids, inputs):
                    row = inventory[island]
                    if row["parser_text_bytes"] != 0:
                        _require(consumed["bytes"] == row["parser_text_bytes"]
                                 and consumed["sha256"] == row["parser_text_sha256"], "nonempty parser/consumed text mismatch")
                    # A zero parser payload can use source-map snippet recovery;
                    # its consumed hash is deliberately retained separately.
                rejected = _boolean(event["rejected"], "check rejection")
                roster = event["kernel_roster"]
                next_taint = _validate_roster(roster, inputs, kind, rejected, tainted)
                if previous_environment is not None:
                    _require(roster["owned_before"] == previous_environment,
                             "kernel identity state changed between sequential checks")
                # Commit observation only after the entire record validates.
                checked.update(ids)
                batch_seen |= kind == "batch"
                suffix_seen |= kind != "batch"
                rejected_seen |= rejected
                tainted = next_taint
                previous_environment = roster["owned_after"]
                result["checks"].append(event)
                result["declarations"].extend({"check_sequence": index, "declaration": row}
                                              for row in roster["declarations"])
            elif tag == "complete":
                _keys(common, "status island_count loaded_sources source_map_checksum_scope other_inputs "
                      "runtime_body_universe denominator_status unmeasured", "complete")
                if schema in RESOLVER_SCHEMAS:
                    _require(resolver_inventory is not None and resolver_checked == bool(resolver_expected)
                             and not resolver_rejected and not resolver_tainted,
                             "completion after resolver rejection/taint or missing resolver check")
                # v3: a completed analysis reached the admission mint in either lane.
                _require(inventory is not None and not inventory_ambiguous and not rejected_seen and not tainted
                         and (admissions_seen if schema == SCHEMA_V3 else (not verification or admissions_seen)),
                         "completion after rejection/taint or missing phase")
                _require(checked == set(range(len(inventory))) and
                         _integer(event["island_count"], "complete island count") == len(inventory), "missing inventoried check at completion")
                _require(event["status"] == "island-check-events-complete" and event["runtime_body_universe"] == "unmeasured"
                         and event["denominator_status"] == "denominator_unverified"
                         and event["unmeasured"] == (UNMEASURED_V2 if schema in RESOLVER_SCHEMAS else UNMEASURED)
                         and event["source_map_checksum_scope"] == SOURCE_MAP_CHECKSUM_SCOPE, "wrong completion scope/disclosure")
                paths = []
                for source in _list(event["loaded_sources"], "loaded source checksums"):
                    _keys(source, "file source_map_checksum_sha256 raw_auxiliary_input_bytes", "loaded source")
                    paths.append(_path(source["file"]))
                    _digest(source["source_map_checksum_sha256"], "source-map checksum")
                    _require(source["raw_auxiliary_input_bytes"] == "unmeasured", "source-map checksum acquired raw-byte authority")
                _require(paths == sorted(set(paths)) and input_path in paths,
                         "duplicate/unordered source label or absent root input")
                other = event["other_inputs"]
                _keys(other, "tracked_files environment_variable_names raw_file_bytes environment_values general_build_and_proc_macro_io", "other inputs")
                for field, is_path in (("tracked_files", True), ("environment_variable_names", False)):
                    values = _strings(other[field], field, paths=is_path, unique=True)
                    _require(values == sorted(values), "unordered tracked input labels")
                _require(all(other[field] == "unmeasured" for field in (
                    "raw_file_bytes", "environment_values", "general_build_and_proc_macro_io")), "auxiliary inputs acquired complete coverage")
                complete = True
            else:
                raise CensusError("record", f"unknown or misplaced event {tag}")
            result["validated_prefix"].append(event)
            previous = hashlib.sha256(exact_line).hexdigest()
        if oversized:
            index = len(result["validated_prefix"])
            raise CensusError("resource-limit", "census byte limit exceeded")
        if lines[-1]:
            index = len(result["validated_prefix"])
            raise CensusError("truncated", "unterminated final record")
        result["record_status"] = "observed-complete" if complete else "incomplete"
        if not complete:
            result["errors"].append({"kind": "missing", "record": len(result["validated_prefix"]),
                                     "message": "missing complete footer"})
    except (CensusError, RecursionError, TypeError, KeyError) as error:
        kind = error.kind if isinstance(error, CensusError) else "record"
        result["record_status"] = "incomplete" if kind == "truncated" else "malformed"
        result["errors"].append({"kind": kind, "record": index, "message": str(error)})
    if result["inventory"] is not None:
        result["missing_islands"] = sorted(set(range(len(result["inventory"]))) - checked)
    if resolver_expected is not None and not resolver_checked:
        result["missing_resolver_islands"] = list(resolver_expected)
    return result


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--census", type=Path, required=True)
    parser.add_argument("--input", required=True, help="exact absolute root input label")
    parser.add_argument("--verification", choices=("on", "off"), required=True)
    parser.add_argument("--lowering", choices=("on", "off"), required=True)
    parser.add_argument("--compiler-exit-code", type=int, default=None,
                        help="observed process exit, not an authenticated acceptance claim")
    args = parser.parse_args(argv)
    try:
        with args.census.open("rb") as stream:
            raw = stream.read(MAX_BYTES + 1)
    except OSError as error:
        parser.exit(2, f"cannot read census: {error}\n")
    result = parse_census(raw, input_path=args.input, verification=args.verification == "on",
                          lowering=args.lowering == "on", exit_code=args.compiler_exit_code)
    # Pre-serialize before printing, and use ASCII escapes for every Unicode
    # label: malformed input cannot partially emit an invalid Unicode report.
    print(json.dumps(result, sort_keys=True, ensure_ascii=True, allow_nan=False))
    return 2 if result["record_status"] == "malformed" else 0


if __name__ == "__main__":
    raise SystemExit(main())
