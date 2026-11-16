#!/usr/bin/env python3
"""Parse the independent actual-collector census; never award G1 completeness.

The compiler's fingerprints are diagnostic identities, not cryptographic body
certificates. Caller-supplied exit codes and files are not acceptance receipts.
Use a bound compiler/process/input harness before relying on these observations.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re

SCHEMA = "trust.rust.mono-item-census.v1"
SCHEMA_V2 = "trust.rust.mono-item-census.v2"
SCHEMA_V3 = "trust.rust.mono-item-census.v3"
DEPENDENCY_IDENTITY = "typed-instances-and-vtables-stable-128-allocations-invocation-local"
DEPENDENCY_SCOPE = "existing-collector-visits-including-cached-query-results"
EAGER_CONST_ROOT_SCOPE = "successful-existing-eager-free-const-value-scans"
EAGER_CONST_ROOT_IDENTITY = "rustc-def-path-hash-128-diagnostic-only"
SCOPE = "actual-local-codegen-collector"
MAX_BYTES = 32 * 1024 * 1024
UNMEASURED = [
    "constant-allocations", "vtables", "caller-expanded-intrinsics",
    "external-linked-bodies-and-foreign-calls", "backend-synthesized-functions",
    "runtime-startup-and-linker-inputs", "pre-optimization-computational-population",
    "dependency-and-build-input-closure",
]
UNMEASURED_V2 = [
    "constant-allocations-outside-visited-collector-results",
    "eager-constant-root-dependencies",
    "unvisited-or-backend-synthesized-vtables",
    "constant-evaluation-interpreter-execution",
    "allocation-bytes-and-relocation-codegen-semantics",
    "caller-expanded-intrinsics", "external-linked-and-foreign-bodies",
    "indirect-runtime-call-targets", "backend-synthesized-functions",
    "runtime-startup-and-linker-inputs", "pre-optimization-computational-population",
    "dependency-and-build-input-closure",
]
KINDS = {
    "item", "intrinsic", "virtual", "static", "global-asm", "shim-vtable",
    "shim-reify", "shim-fn-ptr", "shim-closure-once", "shim-construct-coroutine",
    "shim-thread-local", "shim-future-drop-poll", "shim-drop-glue", "shim-clone",
    "shim-fn-ptr-addr", "shim-async-drop-ctor", "shim-async-drop",
}


def _require(condition, message):
    if not condition:
        raise ValueError(message)


def _object(pairs):
    result = {}
    for key, value in pairs:
        _require(key not in result, f"duplicate JSON key: {key}")
        result[key] = value
    return result


def _keys(value, keys, context):
    _require(type(value) is dict and set(value) == set(keys.split()),
             f"invalid {context} fields")


def _text(value, context, *, empty=False):
    _require(type(value) is str and (empty or bool(value)) and "\x00" not in value,
             f"invalid {context}")


def _ids(values, context):
    _require(type(values) is list, f"invalid {context} list")
    _require(all(type(v) is str and re.fullmatch(r"[0-9a-f]{32}", v) for v in values),
             f"invalid {context} identity")
    _require(values == sorted(set(values)), f"duplicate or unordered {context}")
    return set(values)


def _u64(value, context):
    _require(type(value) is int and 0 <= value < 2**64, f"invalid {context}")


def _dependencies(snapshot, collected_ids, *, eager_roots=False, strategy=None):
    """Check v2's observed dependency graph independently of the usage graph.

    Allocation IDs name this invocation only. Neither their metadata nor the
    collector's dispatch policy establishes value semantics or runtime calls.
    In particular, distinct equal-content allocations must remain distinct.
    """
    nodes, owners, occurrences = (snapshot["dependency_" + name]
                                 for name in ("nodes", "owners", "occurrences"))
    for name, rows in (("node", nodes), ("owner", owners), ("occurrence", occurrences)):
        _require(type(rows) is list, f"invalid dependency {name} table")
        declared = snapshot["dependency_" + name + "_count"]
        _require(type(declared) is int and declared == len(rows), f"dependency {name} count mismatch")

    def unique_table(rows, label):
        _require(all(type(row) is dict and type(row.get("id")) is str for row in rows),
                 f"invalid {label} row")
        keys = [row["id"] for row in rows]
        _require(keys == sorted(set(keys)), f"duplicate or unordered {label}")
        return {row["id"]: row for row in rows}

    node_map = unique_table(nodes, "dependency node")
    owner_map = unique_table(owners, "dependency owner")
    eager_owners, eager_occurrences = [], []
    if eager_roots:
        eager_owners = snapshot["eager_const_root_owners"]
        eager_occurrences = snapshot["eager_const_root_occurrences"]
        for label, rows in (("owner", eager_owners), ("occurrence", eager_occurrences)):
            _require(type(rows) is list, f"invalid eager const root {label} table")
            count = snapshot[f"eager_const_root_{label}_count"]
            _require(type(count) is int and count == len(rows), f"eager const root {label} count mismatch")
        _require(strategy == "eager" or not eager_owners, "eager const roots on lazy strategy")
    eager_owner_map = unique_table(eager_owners, "eager const root owner")
    _require(not (set(owner_map) & set(eager_owner_map)), "root owner overlaps mono-body owner")
    allocation_kinds = {"memory-allocation", "function-allocation", "static-allocation",
                        "vtable-allocation", "type-id-allocation"}
    item_fields = ("mono_item_kind instance_detail generic_args def def_path_hash def_kind "
                   "definition_is_local collected")
    fields = {
        "item": item_fields,
        "memory-allocation": "size_bytes align_bytes mutable",
        "function-allocation": "target", "static-allocation": "target",
        "vtable-allocation": "impl_ty trait_type", "type-id-allocation": "ty",
        "static-initializer": "static size_bytes align_bytes mutable",
        "vtable": "impl_ty trait_type",
    }
    collected = {"item:" + row["id"]: row for row in snapshot["items"]}
    adjacency = {key: set() for key in node_map}

    def reference(value, allowed, label):
        _require(type(value) is str and value in node_map, f"missing {label} endpoint")
        _require(node_map[value]["kind"] in allowed, f"wrong {label} endpoint kind")
        return node_map[value]

    # Validate each node's own fields before examining cross references.
    for node in nodes:
        kind = node.get("kind")
        _require(type(kind) is str and kind in fields, "unknown dependency node kind")
        _keys(node, "id kind " + fields[kind], "dependency node")
        identity = node["id"]
        if kind in allocation_kinds:
            _require(re.fullmatch(r"alloc:[1-9][0-9]*", identity), "invalid allocation identity")
            _u64(int(identity.removeprefix("alloc:")), "allocation identity")
        else:
            prefix = {"item": "item", "static-initializer": "initializer", "vtable": "vtable"}[kind]
            _require(re.fullmatch(prefix + r":[0-9a-f]{32}", identity), "invalid typed dependency identity")
        if kind == "item":
            mono_kind = node["mono_item_kind"]
            _require(type(mono_kind) is str and mono_kind in KINDS, "unknown dependency item kind")
            for field in ("def", "def_path_hash", "def_kind"):
                _text(node[field], field)
            for field in ("instance_detail", "generic_args"):
                _text(node[field], field, empty=mono_kind in ("static", "global-asm"))
            _require(type(node["definition_is_local"]) is bool, "invalid dependency definition locality")
            _require(type(node["collected"]) is bool and node["collected"] == (identity in collected),
                     "dependency collected membership mismatch")
            if identity in collected:
                expected = collected[identity]
                _require(mono_kind == expected["kind"], "collected item kind mismatch")
                for field in ("instance_detail", "generic_args", "def", "def_path_hash", "def_kind",
                              "definition_is_local"):
                    _require(node[field] == expected[field], "collected item metadata mismatch")
        elif kind in ("memory-allocation", "static-initializer"):
            _u64(node["size_bytes"], "allocation size")
            _u64(node["align_bytes"], "allocation alignment")
            align = node["align_bytes"]
            _require(align > 0 and align & (align - 1) == 0, "invalid allocation alignment")
            _require(type(node["mutable"]) is bool, "invalid allocation mutability")
        elif kind in ("vtable", "vtable-allocation"):
            _text(node["impl_ty"], "vtable implementation type")
            _text(node["trait_type"], "vtable trait type")
        elif kind == "type-id-allocation":
            _text(node["ty"], "type-id type")
    for node in nodes:
        kind = node["kind"]
        if kind in ("function-allocation", "static-allocation"):
            target = reference(node["target"], {"item"}, kind)
            if kind == "static-allocation":
                _require(target["mono_item_kind"] == "static", "static allocation targets non-static")
            else:
                _require(target["mono_item_kind"] not in ("static", "global-asm"),
                         "function allocation targets non-function")
            adjacency[node["id"]].add(node["target"])
        elif kind == "static-initializer":
            target = reference(node["static"], {"item"}, "static initializer")
            _require(target["mono_item_kind"] == "static", "initializer belongs to non-static")
            _require(node["id"] == "initializer:" + target["id"].removeprefix("item:"),
                     "initializer identity disagrees with static owner")
            adjacency[node["id"]].add(target["id"])

    used_owner_items = set()
    roots = set()
    for owner in owners:
        _keys(owner, "id item collection_mode collected", "dependency owner")
        item = reference(owner["item"], {"item"}, "owner")
        mode = owner["collection_mode"]
        _require(mode in ("used", "mentioned"), "unknown owner collection mode")
        _require(owner["id"] == owner["item"] + ":" + mode, "owner identity mismatch")
        _require(type(owner["collected"]) is bool and owner["collected"] == item["collected"],
                 "owner collected membership mismatch")
        if mode == "used":
            _require(owner["collected"], "used owner outside collected population")
            used_owner_items.add(owner["item"].removeprefix("item:"))
        else:
            _require(item["mono_item_kind"] != "global-asm", "global assembly cannot have a mentioned pass")
        roots.add(owner["item"])
    _require(used_owner_items == collected_ids, "missing used observer owner")

    # Root visits keep their actual const owner and explicit observed-empty
    # count. They do not contribute to the recursive used-owner equality above.
    for owner in eager_owners:
        _keys(owner, "id kind phase def def_path_hash definition_is_local collection_mode collected dependency_count",
              "eager const root owner")
        _require(owner["kind"] == "free-const" and owner["phase"] == "root-discovery",
                 "wrong eager const root owner kind or phase")
        digest = owner["def_path_hash"]
        _require(type(digest) is str and re.fullmatch(r"[0-9a-f]{32}", digest),
                 "invalid eager const definition hash")
        _require(owner["id"] == "eager-const:" + digest, "eager const owner identity mismatch")
        _text(owner["def"], "eager const definition")
        _require(owner["definition_is_local"] is True and owner["collected"] is False,
                 "eager const is external or falsely collected")
        _require(owner["collection_mode"] == "used", "wrong eager const collection mode")
        _u64(owner["dependency_count"], "eager const dependency count")

    # Validate each independently ordered table before combining them for the
    # shared endpoint/pairing checks. Sorting must never repair malformed input.
    for rows, expected_owners in ((occurrences, owner_map), (eager_occurrences, eager_owner_map)):
        order = []
        for row in rows:
            _require(type(row) is dict and type(row.get("owner")) is str
                     and row["owner"] in expected_owners, "occurrence in wrong owner population")
            _u64(row.get("ordinal"), "occurrence ordinal")
            order.append((row["owner"], row["ordinal"]))
        _require(order == sorted(set(order)), "duplicate or unordered dependency occurrences")
    all_owners = owner_map | eager_owner_map
    all_occurrences = sorted(occurrences + eager_occurrences, key=lambda row: (row["owner"], row["ordinal"]))

    occurrence_fields = {
        "allocation": "target",
        "allocation-root": "target offset_bytes form metadata immutable shared_ref",
        "static-initializer": "target",
        "relocation": "source target offset_bytes immutable shared_ref",
        "vtable": "target entry_count",
        "vtable-entry": "source slot entry_kind target trait_ref local_codegen",
        "vtable-materialization": "source target",
        "instance-use": "target site collector_direct_call local_codegen",
    }
    next_ordinal = {key: 0 for key in all_owners}
    previous = None
    encountered_allocations = set()
    initialized_statics = set()
    requested_vtables = set()
    vtable_slots = {}
    pending_materializations = {}
    allocation_sources = set()
    expected_next = None
    sites = {"instance-use", "closure", "thread-local-static", "language-item", "asm-static",
             "intrinsic-panic", "intrinsic-fallback", "vtable-method", "allocation-static",
             "allocation-function", "thread-local-shim"}
    for row in all_occurrences:
        _require(type(row) is dict, "invalid dependency occurrence")
        kind = row.get("kind")
        _require(type(kind) is str and kind in occurrence_fields, "unknown dependency occurrence kind")
        _keys(row, "owner ordinal mode origin kind " + occurrence_fields[kind], "dependency occurrence")
        _require(type(row["owner"]) is str and row["owner"] in all_owners, "missing occurrence owner")
        owner = all_owners[row["owner"]]
        _u64(row["ordinal"], "occurrence ordinal")
        _require(row["ordinal"] == next_ordinal[row["owner"]], "noncontiguous occurrence ordinals")
        next_ordinal[row["owner"]] += 1
        order = (row["owner"], row["ordinal"])
        _require(previous is None or previous < order, "unordered dependency occurrences")
        previous = order
        mode, origin = row["mode"], row["origin"]
        _require(mode in ("used", "mentioned"), "unknown occurrence mode")
        if row["owner"] in eager_owner_map:
            _require(mode == "used" and origin == "eager-const-root", "wrong eager const occurrence context")
            _require(kind in ("allocation-root", "allocation", "relocation", "vtable-materialization", "instance-use"),
                     "unexpected eager const dependency kind")
            if kind == "instance-use":
                _require(row["site"] in ("allocation-function", "allocation-static"),
                         "unexpected eager const instance-use site")
        else:
            _require(origin in ("mir", "debug-info", "required-const", "mentioned-item", "static", "global-asm"),
                     "unknown dependency origin")
            if origin in ("required-const", "mentioned-item"):
                _require(mode == "mentioned", "semantic mention promoted to used dependency")
            else:
                _require(mode == "used" and owner["collection_mode"] == "used", "used dependency on mentioned pass")
            if origin in ("static", "global-asm"):
                _require(node_map[owner["item"]]["mono_item_kind"] == origin,
                         "dependency origin disagrees with owner kind")
            else:
                _require(node_map[owner["item"]]["mono_item_kind"] not in ("static", "global-asm"),
                         "MIR origin on non-function owner")
        # These pairs follow unconditional calls in the collector. A reference
        # observed in another owner or mode cannot supply the missing encounter.
        matched_expected = expected_next is not None
        if expected_next is not None:
            _require(all(row.get(key) == value for key, value in expected_next.items()),
                     "missing or mismatched paired dependency occurrence")
            expected_next = None

        def expect(kind, **fields):
            return dict(owner=row["owner"], mode=mode, origin=origin, kind=kind, **fields)

        def endpoint(field, allowed):
            result = reference(row[field], allowed, kind + " " + field)
            roots.add(row[field])
            return result

        if kind in ("allocation", "allocation-root"):
            target = endpoint("target", allocation_kinds)
            if kind == "allocation":
                _require(matched_expected, "allocation encounter without its caller")
                encountered_allocations.add(row["target"])
                if target["kind"] == "memory-allocation":
                    allocation_sources.add((row["owner"], mode, origin, row["target"]))
                if target["kind"] == "vtable-allocation":
                    key = (row["owner"], mode, origin, row["target"])
                    pending_materializations[key] = pending_materializations.get(key, 0) + 1
                    expected_next = expect("vtable-materialization", source=row["target"])
                elif target["kind"] in ("function-allocation", "static-allocation"):
                    site = "allocation-function" if target["kind"] == "function-allocation" else "allocation-static"
                    expected_next = expect("instance-use", target=target["target"], site=site)
            if kind == "allocation-root":
                expected_next = expect("allocation", target=row["target"])
                _u64(row["offset_bytes"], "allocation root offset")
                form = row["form"]
                _require(form in ("pointer", "indirect", "slice"), "unknown allocation root form")
                if form == "pointer":
                    _require(row["metadata"] is None and type(row["immutable"]) is bool
                             and type(row["shared_ref"]) is bool, "invalid pointer root metadata")
                    _require(not row["immutable"] or row["shared_ref"], "immutable pointer without shared provenance")
                else:
                    _require(target["kind"] == "memory-allocation", "non-pointer root targets non-memory")
                    _require(row["immutable"] is None and row["shared_ref"] is None,
                             "invalid non-pointer root provenance")
                    if form == "slice":
                        _u64(row["metadata"], "slice metadata")
                        _require(row["offset_bytes"] == 0, "nonzero slice allocation offset")
                    else:
                        _require(row["metadata"] is None, "invalid indirect allocation metadata")
        elif kind == "static-initializer":
            target = endpoint("target", {"static-initializer"})
            _require(origin == "static" and target["static"] == owner["item"],
                     "initializer occurrence belongs to wrong owner")
            initialized_statics.add(row["target"])
            allocation_sources.add((row["owner"], mode, origin, row["target"]))
        elif kind == "relocation":
            source = endpoint("source", {"memory-allocation", "static-initializer"})
            endpoint("target", allocation_kinds)
            _u64(row["offset_bytes"], "relocation offset")
            _require(row["offset_bytes"] < source["size_bytes"], "relocation outside source allocation")
            _require(type(row["immutable"]) is bool and type(row["shared_ref"]) is bool,
                     "invalid relocation provenance")
            _require(not row["immutable"] or row["shared_ref"], "immutable relocation without shared provenance")
            _require((row["owner"], mode, origin, row["source"]) in allocation_sources,
                     "relocation source not encountered in this owner and mode")
            expected_next = expect("allocation", target=row["target"])
            if source["kind"] == "static-initializer":
                _require(origin == "static" and source["static"] == owner["item"],
                         "initializer relocation belongs to wrong owner")
        elif kind == "vtable":
            endpoint("target", {"vtable"})
            requested_vtables.add(row["target"])
            count = row["entry_count"]
            if count is not None:
                _u64(count, "vtable entry count")
                _require(count >= 3, "vtable is missing common metadata entries")
            key = (row["owner"], row["target"])
            if key in vtable_slots:
                previous_request = vtable_slots[key]
                _require(previous_request[0] == (previous_request[1] or 0), "incomplete preceding vtable request")
            vtable_slots[key] = [0, count, mode, origin]
        elif kind == "vtable-entry":
            endpoint("source", {"vtable"})
            _u64(row["slot"], "vtable slot")
            request = (row["owner"], row["source"])
            _require(request in vtable_slots, "vtable entry without request")
            slots = vtable_slots[request]
            _require(slots[1] is not None and row["slot"] == slots[0] and row["slot"] < slots[1],
                     "vtable slot missing its request or preceding slots")
            _require((mode, origin) == (slots[2], slots[3]), "vtable entry changed request mode or origin")
            slots[0] += 1
            entry = row["entry_kind"]
            _require(entry in ("drop-in-place", "size", "align", "vacant", "method", "trait-vptr"),
                     "unknown vtable entry kind")
            common = ("drop-in-place", "size", "align")
            _require(entry == common[row["slot"]] if row["slot"] < 3 else entry not in common,
                     "vtable common metadata position mismatch")
            if entry == "method":
                target = endpoint("target", {"item"})
                _require(target["mono_item_kind"] not in ("static", "global-asm"),
                         "vtable method targets non-function")
                _require(type(row["local_codegen"]) is bool and row["trait_ref"] is None,
                         "invalid vtable method metadata")
                expected_next = expect("instance-use", target=row["target"], site="vtable-method",
                                       local_codegen=row["local_codegen"])
            else:
                _require(row["target"] is None and row["local_codegen"] is None,
                         "invalid non-method vtable target")
                if entry == "trait-vptr":
                    _text(row["trait_ref"], "vtable trait reference")
                else:
                    _require(row["trait_ref"] is None, "invalid vtable metadata trait reference")
        elif kind == "vtable-materialization":
            _require(matched_expected, "materialization without preceding symbolic allocation")
            endpoint("source", {"vtable-allocation"})
            endpoint("target", {"memory-allocation"})
            key = (row["owner"], mode, origin, row["source"])
            _require(pending_materializations.get(key, 0) > 0, "materialization without matching allocation encounter")
            pending_materializations[key] -= 1
            expected_next = expect("allocation", target=row["target"])
        elif kind == "instance-use":
            target = endpoint("target", {"item"})
            _require(type(row["site"]) is str and row["site"] in sites, "unknown instance use site")
            if row["site"] in ("allocation-function", "allocation-static", "vtable-method"):
                _require(matched_expected, "filter decision without preceding allocation or vtable entry")
            if row["site"] == "instance-use":
                _require(type(row["collector_direct_call"]) is bool, "missing collector direct-call policy")
            else:
                _require(row["collector_direct_call"] is None, "unqueried collector direct-call policy")
            if row["site"] == "thread-local-shim":
                _require(row["local_codegen"] is None, "unqueried local-codegen decision")
                _require(target["mono_item_kind"] == "shim-thread-local", "wrong thread-local shim kind")
            else:
                _require(type(row["local_codegen"]) is bool, "missing local-codegen decision")
            if row["site"] in ("thread-local-static", "asm-static", "allocation-static"):
                _require(target["mono_item_kind"] == "static", "static use targets non-static")
            else:
                _require(target["mono_item_kind"] not in ("static", "global-asm"),
                         "function use targets non-function")
    _require(expected_next is None, "missing final paired dependency occurrence")
    for owner in eager_owners:
        _require(next_ordinal[owner["id"]] == owner["dependency_count"], "eager const dependency count mismatch")
    _require(encountered_allocations == {node["id"] for node in nodes if node["kind"] in allocation_kinds},
             "missing allocation encounter")
    _require(initialized_statics == {node["id"] for node in nodes if node["kind"] == "static-initializer"},
             "missing static initializer occurrence")
    _require(requested_vtables == {node["id"] for node in nodes if node["kind"] == "vtable"},
             "missing vtable request")
    _require(all(seen == (count or 0) for seen, count, _, _ in vtable_slots.values()),
             "missing final vtable entries")
    _require(not any(pending_materializations.values()), "missing vtable materialization")
    reached, pending = set(roots), list(roots)
    while pending:
        for target in adjacency[pending.pop()]:
            if target not in reached:
                reached.add(target)
                pending.append(target)
    _require(reached == set(node_map), "orphan dependency node")


def parse_census(raw: bytes | None, *, input_path: str, exit_code: int | None,
                 lowering: bool = False, verification: bool = False):
    result = {"status": "incomplete", "whole_program_complete": False,
              "unmeasured": list(UNMEASURED), "errors": []}
    try:
        _require(type(lowering) is bool and type(verification) is bool, "invalid expected lane")
        _require(type(exit_code) is int or exit_code is None, "invalid process exit code")
        if exit_code != 0:
            result.update(status="compiler_failed", errors=["compiler did not exit successfully"])
            return result
        if raw is None or raw == b"":
            result.update(status="missing", errors=["missing census"])
            return result
        _require(type(raw) is bytes and len(raw) <= MAX_BYTES, "invalid or oversized census")
        _require(raw.endswith(b"\n"), "truncated final record")
        lines = raw.splitlines(keepends=True)
        _require(len(lines) in (1, 2, 3), "wrong record population")
        records = [json.loads(line, object_pairs_hook=_object,
                              parse_constant=lambda _: (_ for _ in ()).throw(ValueError("nonfinite JSON")))
                   for line in lines]
        header = records[0]
        _require(type(header) is dict, "invalid header")
        schema = header.get("schema")
        _require(schema in (SCHEMA, SCHEMA_V2, SCHEMA_V3), "unknown census schema")
        header_fields = "schema event scope input compiler_version target edition direct_lowering " \
              "verification_enabled collection_strategy optimization incremental codegen_requested "
        header_fields += "identity_scheme unmeasured"
        if schema in (SCHEMA_V2, SCHEMA_V3):
            header_fields += " dependency_identity_scheme dependency_scope"
        if schema == SCHEMA_V3:
            header_fields += " eager_const_root_scope eager_const_root_identity_scheme"
        _keys(header, header_fields, "header")
        _require(header["event"] == "begin"
                 and header["scope"] == SCOPE, "wrong census schema/event/scope")
        _require(header["input"] == input_path and Path(input_path).is_absolute(), "wrong input")
        for field in ("compiler_version", "target", "optimization"):
            _text(header[field], field)
        _require(header["compiler_version"] != "unknown", "unknown compiler version")
        _require(header["edition"] in ("2015", "2018", "2021", "2024"), "unknown edition")
        for field in ("direct_lowering", "verification_enabled", "incremental", "codegen_requested"):
            _require(type(header[field]) is bool, f"invalid {field}")
        _require(header["direct_lowering"] == lowering and header["verification_enabled"] == verification,
                 "wrong compiler lane")
        _require(header["collection_strategy"] in ("eager", "lazy"), "unknown collection strategy")
        _require(header["identity_scheme"] == "rustc-stable-mono-item-fingerprint-128-diagnostic-only",
                 "wrong identity scheme")
        unmeasured = UNMEASURED if schema == SCHEMA else UNMEASURED_V2
        _require(header["unmeasured"] == unmeasured, "missing unmeasured populations")
        if schema in (SCHEMA_V2, SCHEMA_V3):
            _require(header["dependency_identity_scheme"] == DEPENDENCY_IDENTITY,
                     "wrong dependency identity scheme")
            _require(header["dependency_scope"] == DEPENDENCY_SCOPE, "wrong dependency scope")
        if schema == SCHEMA_V3:
            _require(header["eager_const_root_scope"] == EAGER_CONST_ROOT_SCOPE,
                     "wrong eager const root scope")
            _require(header["eager_const_root_identity_scheme"] == EAGER_CONST_ROOT_IDENTITY,
                     "wrong eager const root identity scheme")
        result["unmeasured"] = list(unmeasured)
        result["header"] = header
        if len(records) == 1:
            result["errors"] = ["missing collection and completion records"]
            return result
        footer = records[-1]
        _keys(footer, "schema event status item_count snapshot_sha256 sources unmeasured whole_program_complete",
              "footer")
        _require(footer["schema"] == schema and footer["event"] == "complete", "missing completion footer")
        _require(footer["unmeasured"] == unmeasured and footer["whole_program_complete"] is False,
                 "invalid whole-program claim")
        _require(type(footer["sources"]) is dict, "invalid loaded sources")
        for path, digest in footer["sources"].items():
            _require(Path(path).is_absolute() and "\x00" not in path, "invalid loaded source path")
            _require(type(digest) is str and re.fullmatch(r"sha256=[0-9a-f]{64}", digest),
                     "invalid consumption-time source digest")
        _require(input_path in footer["sources"], "input not in loaded sources")
        result["sources"] = footer["sources"]
        if len(records) == 2:
            _require(footer["status"] == "unmeasured" and footer["item_count"] is None
                     and footer["snapshot_sha256"] is None, "unmeasured footer claims a population")
            result.update(status="unmeasured", errors=["normal compiler path did not collect mono items"])
            return result
        _require(footer["status"] == "collector_observed", "invalid collector status")
        snapshot = records[1]
        snapshot_fields = "schema event item_count items roots usage_edges codegen_units unplaced_items"
        if schema in (SCHEMA_V2, SCHEMA_V3):
            snapshot_fields += (" dependency_nodes dependency_owners dependency_occurrences"
                                " dependency_node_count dependency_owner_count dependency_occurrence_count")
        if schema == SCHEMA_V3:
            snapshot_fields += (" eager_const_root_owners eager_const_root_occurrences"
                                " eager_const_root_owner_count eager_const_root_occurrence_count")
        _keys(snapshot, snapshot_fields, "snapshot")
        _require(snapshot["schema"] == schema and snapshot["event"] == "mono_snapshot", "wrong snapshot")
        _require(footer["snapshot_sha256"] == hashlib.sha256(lines[1]).hexdigest(), "snapshot digest mismatch")
        _require(type(snapshot["items"]) is list, "invalid items")
        count = len(snapshot["items"])
        for declared in (snapshot["item_count"], footer["item_count"]):
            _require(type(declared) is int and declared == count, "item count mismatch")
        kinds = {}
        item_ids = []
        for row in snapshot["items"]:
            _keys(row, "id kind instance_detail generic_args def def_path_hash def_kind definition_is_local symbol", "item")
            _require(type(row["kind"]) is str and row["kind"] in KINDS, "unknown instance kind")
            for field in ("def", "def_path_hash", "def_kind", "symbol"):
                _text(row[field], field)
            for field in ("instance_detail", "generic_args"):
                _text(row[field], field, empty=row["kind"] in ("static", "global-asm"))
            _require(type(row["definition_is_local"]) is bool, "invalid local-definition flag")
            item_ids.append(row["id"])
            kinds[row["kind"]] = kinds.get(row["kind"], 0) + 1
        ids = _ids(item_ids, "item")
        roots = _ids(snapshot["roots"], "root")
        _require(roots <= ids, "root outside collected population")
        edges = snapshot["usage_edges"]
        _require(type(edges) is list and all(type(e) is list and len(e) == 2 for e in edges), "invalid usage edges")
        _require(all(type(a) is str and type(b) is str and a in ids and b in ids for a, b in edges),
                 "usage edge outside collected population")
        edge_tuples = [tuple(edge) for edge in edges]
        _require(edge_tuples == sorted(set(edge_tuples)), "duplicate or unordered usage edge")
        adjacency = {item: [] for item in ids}
        for a, b in edges:
            adjacency[a].append(b)
        reached, pending = set(roots), list(roots)
        while pending:
            for target in adjacency[pending.pop()]:
                if target not in reached:
                    reached.add(target)
                    pending.append(target)
        _require(reached == ids, "collected item not reachable from recorded roots")
        units = snapshot["codegen_units"]
        _require(type(units) is dict and bool(units), "missing codegen units")
        placed = set()
        for name, entries in units.items():
            _text(name, "codegen-unit name")
            _require(type(entries) is list, "invalid CGU placements")
            placement_ids = []
            for entry in entries:
                _keys(entry, "id linkage visibility inlined", "placement")
                _require(entry["linkage"] in ("External", "AvailableExternally", "LinkOnceAny", "LinkOnceODR", "WeakAny",
                         "WeakODR", "Internal", "ExternalWeak", "Common"), "unknown linkage")
                _require(entry["visibility"] in ("Default", "Hidden", "Protected"), "unknown visibility")
                _require(type(entry["inlined"]) is bool, "invalid inlined flag")
                placement_ids.append(entry["id"])
            placed |= _ids(placement_ids, "CGU placement")
        unplaced = _ids(snapshot["unplaced_items"], "unplaced item")
        _require(not (placed & unplaced) and (placed | unplaced) == ids,
                 "CGU/unplaced partition differs from collector population")
        if schema in (SCHEMA_V2, SCHEMA_V3):
            _dependencies(snapshot, ids, eager_roots=schema == SCHEMA_V3,
                          strategy=header["collection_strategy"])
        result.update(status="collector_observed", item_count=count, kinds=kinds, snapshot=snapshot)
    except (ValueError, TypeError, KeyError, RecursionError, UnicodeError) as error:
        result.update(status="malformed", errors=[str(error)])
    return result


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("report", type=Path)
    parser.add_argument("--input", required=True)
    parser.add_argument("--compiler-exit-code", required=True, type=int)
    parser.add_argument("--lowering", action="store_true")
    parser.add_argument("--verification", action="store_true")
    args = parser.parse_args(argv)
    try:
        with args.report.open("rb") as report:
            raw = report.read(MAX_BYTES + 1)
    except OSError as error:
        parser.exit(2, f"cannot read census: {error}\n")
    result = parse_census(raw, input_path=args.input, exit_code=args.compiler_exit_code,
                          lowering=args.lowering, verification=args.verification)
    print(json.dumps(result, indent=2, sort_keys=True))
    return 0 if result["status"] == "collector_observed" else 1


if __name__ == "__main__":
    raise SystemExit(main())
