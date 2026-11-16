#!/usr/bin/env python3
"""Structural mutation tests. Compiler observations are a separate live rung."""

import copy
import hashlib
import importlib.util
import json
from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parents[2]
SPEC = importlib.util.spec_from_file_location("instance_census", ROOT / "scripts/rust_instance_census.py")
census = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(census)


def fixture():
    ids = [f"{i:032x}" for i in range(1, 4)]
    header = dict(schema=census.SCHEMA, event="begin", scope=census.SCOPE,
                  input="/fixture/instances.rs", compiler_version="trustc fixture",
                  target="aarch64-apple-darwin", edition="2024", direct_lowering=False,
                  verification_enabled=False, collection_strategy="lazy", optimization="No",
                  incremental=False, codegen_requested=True,
                  identity_scheme="rustc-stable-mono-item-fingerprint-128-diagnostic-only",
                  unmeasured=list(census.UNMEASURED))
    items = [dict(id=identity, kind=kind, instance_detail=kind, generic_args=args,
                  # Two instantiations deliberately share a definition.
                  **{"def": "fixture::generic" if i < 2 else "core::drop_in_place"},
                  def_path_hash="same-definition" if i < 2 else "drop-definition",
                  def_kind="Fn", definition_is_local=i < 2, symbol=f"_symbol_{i}")
             for i, (identity, kind, args) in enumerate(zip(ids,
                    ("item", "item", "shim-drop-glue"), ("[u8]", "[u16]", "[Owner]")))]
    placements = [dict(id=i, linkage="Internal", visibility="Default", inlined=False) for i in ids]
    snapshot = dict(schema=census.SCHEMA, event="mono_snapshot", item_count=3, items=items,
                    roots=ids[:1], usage_edges=[[ids[0], ids[1]], [ids[1], ids[2]]],
                    codegen_units={"fixture-cgu.0": placements}, unplaced_items=[])
    footer = dict(schema=census.SCHEMA, event="complete", status="collector_observed", item_count=3,
                  snapshot_sha256=None, sources={header["input"]: "sha256=" + "a" * 64},
                  unmeasured=list(census.UNMEASURED), whole_program_complete=False)
    return [header, snapshot, footer]


def encode(records, *, rehash=True):
    records = copy.deepcopy(records)
    lines = [json.dumps(record).encode() + b"\n" for record in records]
    if rehash and len(records) == 3:
        records[-1]["snapshot_sha256"] = hashlib.sha256(lines[1]).hexdigest()
        lines[-1] = json.dumps(records[-1]).encode() + b"\n"
    return b"".join(lines)


class InstanceCensus(unittest.TestCase):
    def parse(self, records=None, *, raw=None, **kwargs):
        return census.parse_census(encode(fixture() if records is None else records) if raw is None else raw,
                                   input_path="/fixture/instances.rs", exit_code=kwargs.pop("exit_code", 0), **kwargs)

    def reject(self, mutation):
        records = fixture()
        mutation(records)
        result = self.parse(records)
        self.assertEqual(result["status"], "malformed", result)
        self.assertFalse(result["whole_program_complete"])

    def test_distinct_instantiations_and_generated_shim_are_not_defid_deduplicated(self):
        result = self.parse()
        self.assertEqual(result["status"], "collector_observed", result)
        self.assertEqual(result["item_count"], 3)
        self.assertEqual(result["kinds"], {"item": 2, "shim-drop-glue": 1})
        self.assertFalse(result["whole_program_complete"])
        self.assertEqual(result["unmeasured"], census.UNMEASURED)

    def test_explicit_empty_collector_is_not_whole_program_completion(self):
        records = fixture()
        records[1].update(items=[], item_count=0, roots=[], usage_edges=[], codegen_units={"empty": []})
        records[2]["item_count"] = 0
        result = self.parse(records)
        self.assertEqual(result["status"], "collector_observed", result)
        self.assertEqual(result["item_count"], 0)
        self.assertFalse(result["whole_program_complete"])

    def test_non_codegen_path_is_unmeasured_never_zero(self):
        header, _, footer = fixture()
        header["codegen_requested"] = False
        footer.update(status="unmeasured", item_count=None, snapshot_sha256=None)
        result = self.parse([header, footer])
        self.assertEqual(result["status"], "unmeasured", result)
        self.assertNotIn("item_count", result)

    def test_failed_and_interrupted_process_cannot_use_complete_report(self):
        for code in (1, 101, -9, None):
            self.assertEqual(self.parse(exit_code=code)["status"], "compiler_failed")
        self.assertEqual(self.parse(exit_code=False)["status"], "malformed")

    def test_begin_only_missing_and_truncated_are_not_success(self):
        self.assertEqual(self.parse(fixture()[:1])["status"], "incomplete")
        self.assertEqual(self.parse(raw=b"")["status"], "missing")
        self.assertEqual(self.parse(raw=encode(fixture())[:-1])["status"], "malformed")

    def test_missing_footer_and_extra_record_are_not_success(self):
        self.assertEqual(self.parse(fixture()[:2])["status"], "malformed")
        self.assertEqual(self.parse(fixture() + [fixture()[-1]])["status"], "malformed")

    def test_schema_input_lane_and_populations_cannot_be_relabelled(self):
        for key, value in (("schema", "hir-census"), ("scope", "whole-program"),
                           ("input", "/swapped.rs"), ("direct_lowering", True),
                           ("verification_enabled", True), ("incremental", 1),
                           ("compiler_version", "unknown"), ("unmeasured", []),
                           ("identity_scheme", "source-refinement-sha256")):
            with self.subTest(key=key):
                self.reject(lambda r: r[0].update({key: value}))
        self.reject(lambda r: r[2].update(whole_program_complete=True))
        self.reject(lambda r: r[2].update(unmeasured=[]))

    def test_digest_and_counts_bind_raw_snapshot(self):
        records = fixture()
        records[2]["snapshot_sha256"] = "0" * 64
        self.assertEqual(self.parse(raw=encode(records, rehash=False))["status"], "malformed")
        for index in (1, 2):
            self.reject(lambda r: r[index].update(item_count=4))
            self.reject(lambda r: r[index].update(item_count=True))

    def test_unknown_kind_and_duplicate_identity_are_refused_even_after_rehash(self):
        self.reject(lambda r: r[1]["items"][0].update(kind="unknown-shim"))
        self.reject(lambda r: r[1]["items"][1].update(id=r[1]["items"][0]["id"]))
        self.reject(lambda r: r[1]["items"][0].update(instance_detail=""))

    def test_dropped_or_extra_roots_and_unreachable_rows_refuse(self):
        self.reject(lambda r: r[1].update(roots=[]))
        self.reject(lambda r: r[1]["roots"].append("f" * 32))
        self.reject(lambda r: r[1]["roots"].append(r[1]["roots"][0]))
        self.reject(lambda r: r[1]["usage_edges"].pop())

    def test_cycles_are_ordinary_collector_graphs(self):
        records = fixture()
        ids = [item["id"] for item in records[1]["items"]]
        records[1]["usage_edges"].append([ids[2], ids[0]])
        self.assertEqual(self.parse(records)["status"], "collector_observed")

    def test_forged_or_duplicate_edge_refuses(self):
        self.reject(lambda r: r[1]["usage_edges"].append(["e" * 32, "f" * 32]))
        self.reject(lambda r: r[1]["usage_edges"].append(r[1]["usage_edges"][0]))

    def test_cgu_population_is_exact_but_cross_cgu_copies_are_allowed(self):
        records = fixture()
        records[1]["codegen_units"]["second"] = copy.deepcopy(records[1]["codegen_units"]["fixture-cgu.0"])
        self.assertEqual(self.parse(records)["status"], "collector_observed")
        self.reject(lambda r: r[1]["codegen_units"]["fixture-cgu.0"].pop())
        self.reject(lambda r: r[1]["codegen_units"]["fixture-cgu.0"].append(r[1]["codegen_units"]["fixture-cgu.0"][0]))
        self.reject(lambda r: r[1].update(codegen_units={}))

    def test_cgu_metadata_is_typed(self):
        for key, value in (("linkage", "???"), ("visibility", "???"), ("inlined", 1)):
            self.reject(lambda r: r[1]["codegen_units"]["fixture-cgu.0"][0].update({key: value}))

    def test_unplaced_collector_items_are_retained_not_dropped_or_fatal(self):
        records = fixture()
        unplaced = records[1]["codegen_units"]["fixture-cgu.0"].pop()["id"]
        records[1]["unplaced_items"] = [unplaced]
        result = self.parse(records)
        self.assertEqual(result["status"], "collector_observed", result)
        self.assertEqual(result["item_count"], 3)
        self.assertFalse(result["whole_program_complete"])
        self.reject(lambda r: r[1]["unplaced_items"].append(r[1]["items"][0]["id"]))
        self.reject(lambda r: r[1]["unplaced_items"].append("e" * 32))
        records[1]["unplaced_items"].append(unplaced)
        self.assertEqual(self.parse(records)["status"], "malformed")

    def test_sources_cannot_be_omitted_or_re_read_hashes_misrepresented(self):
        self.reject(lambda r: r[2].update(sources={}))
        self.reject(lambda r: r[2]["sources"].update({r[0]["input"]: "a" * 64}))
        self.reject(lambda r: r[2]["sources"].update({"relative.rs": "sha256=" + "a" * 64}))

    def test_duplicate_keys_unknown_fields_invalid_and_deep_json(self):
        raw = encode(fixture()).replace(b'"event": "begin"', b'"event": "begin", "event": "begin"')
        self.assertEqual(self.parse(raw=raw)["status"], "malformed")
        for raw in (b"[" * 2000 + b"0" + b"]" * 2000 + b"\n", b"NaN\n", b"\xff\n"):
            self.assertEqual(self.parse(raw=raw)["status"], "malformed")
        self.reject(lambda r: r[0].update(authority="kernel"))


def fixture_v2():
    records = fixture()
    header, snapshot, footer = records
    for record in records:
        record["schema"] = census.SCHEMA_V2
    for record in (header, footer):
        record["unmeasured"] = list(census.UNMEASURED_V2)
    header.update(dependency_identity_scheme=census.DEPENDENCY_IDENTITY,
                  dependency_scope=census.DEPENDENCY_SCOPE)
    item_id = lambda n: "item:" + f"{n:032x}"
    for n, kind in ((4, "static"), (5, "global-asm")):
        row = dict(id=f"{n:032x}", kind=kind, instance_detail="", generic_args="",
                   **{"def": f"fixture::{kind}"}, def_path_hash=f"definition-{n}",
                   def_kind=kind, definition_is_local=True, symbol=f"symbol-{n}")
        snapshot["items"].append(row)
        snapshot["usage_edges"].append([f"{1:032x}", row["id"]])
        snapshot["codegen_units"]["fixture-cgu.0"].append(
            dict(id=row["id"], linkage="Internal", visibility="Default", inlined=False))
    snapshot["usage_edges"].sort()
    snapshot["item_count"] = footer["item_count"] = 5
    nodes = [dict(id="item:" + row["id"], kind="item", mono_item_kind=row["kind"], collected=True,
                  **{key: row[key] for key in ("instance_detail", "generic_args", "def", "def_path_hash",
                                               "def_kind", "definition_is_local")})
             for row in snapshot["items"]]
    for n, kind, name in ((6, "item", "mentioned_only"), (7, "item", "foreign_abs"),
                          (8, "static", "foreign_static")):
        nodes.append(dict(id=item_id(n), kind="item", mono_item_kind=kind, collected=False,
                          instance_detail="" if kind == "static" else "Item",
                          generic_args="" if kind == "static" else "[]",
                          **{"def": name}, def_path_hash=f"definition-{n}", def_kind=kind,
                          definition_is_local=n != 8))
    initializer = "initializer:" + f"{4:032x}"
    vtable = "vtable:" + "f" * 32
    nodes.extend([
        dict(id="alloc:1", kind="memory-allocation", size_bytes=16, align_bytes=8, mutable=False),
        dict(id="alloc:2", kind="memory-allocation", size_bytes=16, align_bytes=8, mutable=False),
        dict(id="alloc:3", kind="function-allocation", target=item_id(7)),
        dict(id="alloc:4", kind="static-allocation", target=item_id(8)),
        dict(id="alloc:5", kind="vtable-allocation", impl_ty="Concrete", trait_type="dyn Trait"),
        dict(id="alloc:6", kind="type-id-allocation", ty="u64"),
        dict(id=initializer, kind="static-initializer", static=item_id(4),
             size_bytes=8, align_bytes=8, mutable=False),
        dict(id=vtable, kind="vtable", impl_ty="Concrete", trait_type="dyn Trait"),
    ])
    owners = [dict(id=item_id(n) + ":used", item=item_id(n), collection_mode="used", collected=True)
              for n in range(1, 6)]
    owners.append(dict(id=item_id(6) + ":mentioned", item=item_id(6), collection_mode="mentioned", collected=False))
    occurrences = []

    def event(n, kind, *, owner_mode="used", mode="used", origin="mir", **fields):
        owner = item_id(n) + ":" + owner_mode
        ordinal = sum(row["owner"] == owner for row in occurrences)
        occurrences.append(dict(owner=owner, ordinal=ordinal, kind=kind, mode=mode, origin=origin, **fields))

    def allocation(n, target, **context):
        event(n, "allocation", target=target, **context)
        if target == "alloc:1":
            for offset, dependency in ((0, "alloc:3"), (8, "alloc:4")):
                event(n, "relocation", source=target, target=dependency, offset_bytes=offset,
                      immutable=True, shared_ref=True, **context)
                allocation(n, dependency, **context)
        elif target in ("alloc:3", "alloc:4"):
            function = target == "alloc:3"
            event(n, "instance-use", target=item_id(7 if function else 8),
                  site="allocation-function" if function else "allocation-static",
                  collector_direct_call=None, local_codegen=False, **context)
        elif target == "alloc:5":
            event(n, "vtable-materialization", source=target, target="alloc:1", **context)
            allocation(n, "alloc:1", **context)

    def root(n, target, *, form="pointer", offset_bytes=0, metadata=None, **context):
        event(n, "allocation-root", target=target, form=form, offset_bytes=offset_bytes,
              metadata=metadata, immutable=False if form == "pointer" else None,
              shared_ref=False if form == "pointer" else None, **context)
        allocation(n, target, **context)

    event(1, "instance-use", target=item_id(7), site="instance-use", collector_direct_call=True, local_codegen=False)
    root(1, "alloc:3")
    root(1, "alloc:1", form="indirect", offset_bytes=8)
    root(1, "alloc:2", form="slice", metadata=16)
    root(1, "alloc:6")
    event(1, "vtable", target=vtable, entry_count=6)
    for slot, kind in enumerate(("drop-in-place", "size", "align", "vacant", "method", "trait-vptr")):
        event(1, "vtable-entry", source=vtable, slot=slot, entry_kind=kind,
              target=item_id(2) if kind == "method" else None,
              local_codegen=True if kind == "method" else None,
              trait_ref="Concrete: SuperTrait" if kind == "trait-vptr" else None)
        if kind == "method":
            event(1, "instance-use", target=item_id(2), site="vtable-method",
                  collector_direct_call=None, local_codegen=True)
    root(1, "alloc:5")
    root(1, "alloc:1", mode="mentioned", origin="required-const")
    event(4, "static-initializer", origin="static", target=initializer)
    event(4, "relocation", origin="static", source=initializer, target="alloc:1", offset_bytes=0,
          immutable=True, shared_ref=True)
    allocation(4, "alloc:1", origin="static")
    event(5, "instance-use", origin="global-asm", target=item_id(8), site="asm-static",
          collector_direct_call=None, local_codegen=False)
    root(6, "alloc:2", form="indirect", owner_mode="mentioned", mode="mentioned", origin="required-const")
    snapshot.update(dependency_nodes=sorted(nodes, key=lambda row: row["id"]),
                    dependency_owners=sorted(owners, key=lambda row: row["id"]),
                    dependency_occurrences=sorted(occurrences, key=lambda row: (row["owner"], row["ordinal"])))
    recount_dependencies(records)
    return records


def recount_dependencies(records):
    for singular, plural in (("node", "nodes"), ("owner", "owners"), ("occurrence", "occurrences")):
        records[1]["dependency_" + singular + "_count"] = len(records[1]["dependency_" + plural])


class InstanceDependencies(unittest.TestCase):
    def parse(self, records=None):
        return census.parse_census(encode(fixture_v2() if records is None else records),
                                   input_path="/fixture/instances.rs", exit_code=0)

    def reject(self, mutation):
        records = fixture_v2()
        mutation(records)
        result = self.parse(records)
        self.assertEqual(result["status"], "malformed", result)
        self.assertFalse(result["whole_program_complete"])

    @staticmethod
    def node(records, identity):
        return next(row for row in records[1]["dependency_nodes"] if row["id"] == identity)

    @staticmethod
    def occurrence(records, kind, **fields):
        return next(row for row in records[1]["dependency_occurrences"]
                    if row["kind"] == kind and all(row.get(key) == value for key, value in fields.items()))

    def test_allocations_vtables_and_foreign_references_are_separate_from_bodies(self):
        result = self.parse()
        self.assertEqual(result["status"], "collector_observed", result)
        self.assertEqual(result["item_count"], 5)
        self.assertFalse(result["whole_program_complete"])
        self.assertEqual(result["unmeasured"], census.UNMEASURED_V2)
        records = fixture_v2()
        a, b = (self.node(records, name) for name in ("alloc:1", "alloc:2"))
        self.assertEqual({k: v for k, v in a.items() if k != "id"}, {k: v for k, v in b.items() if k != "id"})
        self.assertNotEqual(a["id"], b["id"])

    def test_invocation_local_allocation_ids_may_change_without_merging_nodes(self):
        records = fixture_v2()
        for row in records[1]["dependency_nodes"] + records[1]["dependency_occurrences"]:
            for field, value in list(row.items()):
                if type(value) is str and value.startswith("alloc:"):
                    row[field] = "alloc:" + str(int(value.split(":")[1]) + 100)
        records[1]["dependency_nodes"].sort(key=lambda row: row["id"])
        self.assertEqual(self.parse(records)["status"], "collector_observed")

    def test_schema_versions_cannot_mix_or_discard_residual_gaps(self):
        for index in range(3):
            self.reject(lambda r: r[index].update(schema=census.SCHEMA))
        for value in ([], census.UNMEASURED):
            self.reject(lambda r: r[0].update(unmeasured=value))
            self.reject(lambda r: r[2].update(unmeasured=value))
        for key in ("dependency_identity_scheme", "dependency_scope"):
            self.reject(lambda r: r[0].pop(key))
            self.reject(lambda r: r[0].update({key: "whole-program-proof"}))
        self.reject(lambda r: r[2].update(whole_program_complete=True))

    def test_missing_empty_or_duplicate_owner_cannot_hide_uninstrumented_query(self):
        def empty(r):
            for key in ("nodes", "owners", "occurrences"):
                r[1]["dependency_" + key] = []
            recount_dependencies(r)
        self.reject(empty)
        def missing_empty_owner(r):
            r[1]["dependency_owners"].pop(1)
            recount_dependencies(r)
        self.reject(missing_empty_owner)
        def duplicate(r):
            r[1]["dependency_owners"].insert(0, r[1]["dependency_owners"][0])
            recount_dependencies(r)
        self.reject(duplicate)
        def mentioned_assembly(r):
            item = "item:" + f"{5:032x}"
            r[1]["dependency_owners"].append(dict(id=item + ":mentioned", item=item,
                                                collection_mode="mentioned", collected=True))
            r[1]["dependency_owners"].sort(key=lambda row: row["id"])
            recount_dependencies(r)
        self.reject(mentioned_assembly)

    def test_counts_are_exact_integers_and_fields_are_closed(self):
        for key in ("node", "owner", "occurrence"):
            for value in (True, -1, "0", 999):
                self.reject(lambda r: r[1].update({"dependency_" + key + "_count": value}))
        self.reject(lambda r: r[1]["dependency_occurrences"][0].update(proved=True))
        self.reject(lambda r: r[1]["dependency_nodes"][0].update(content_is_complete=True))

    def test_item_metadata_and_membership_must_agree_with_collected_population(self):
        identity = "item:" + f"{1:032x}"
        for key, value in (("collected", False), ("collected", 1), ("generic_args", "[u128]"),
                           ("mono_item_kind", "shim-reify"), ("def_path_hash", "another")):
            self.reject(lambda r: self.node(r, identity).update({key: value}))
        self.reject(lambda r: r[1]["dependency_owners"][0].update(collected=False))
        self.reject(lambda r: r[1]["dependency_owners"][0].update(item="item:" + "a" * 32))
        self.reject(lambda r: r[1]["dependency_owners"][0].update(id="arbitrary-owner"))

    def test_mentions_are_not_promoted_to_used_edges(self):
        self.reject(lambda r: self.occurrence(r, "allocation", origin="required-const").update(mode="used"))
        self.reject(lambda r: r[1]["dependency_occurrences"][-1].update(mode="used", origin="mir"))
        self.reject(lambda r: self.occurrence(r, "static-initializer").update(origin="mir"))
        self.reject(lambda r: r[1]["dependency_occurrences"][0].update(origin="invented"))

    def test_missing_wrong_kind_and_orphan_dependency_nodes_refuse(self):
        self.reject(lambda r: self.occurrence(r, "allocation").update(target="alloc:999"))
        self.reject(lambda r: self.occurrence(r, "allocation").update(target="item:" + f"{1:032x}"))
        self.reject(lambda r: self.node(r, "alloc:3").update(target="item:" + f"{4:032x}"))
        self.reject(lambda r: self.node(r, "alloc:4").update(target="item:" + f"{1:032x}"))
        def orphan(r):
            r[1]["dependency_nodes"].append(dict(id="alloc:999", kind="type-id-allocation", ty="u32"))
            r[1]["dependency_nodes"].sort(key=lambda row: row["id"])
            recount_dependencies(r)
        self.reject(orphan)

    def test_allocation_identity_metadata_and_relocation_offsets_are_typed(self):
        for field, value in (("id", "alloc:01"), ("id", "alloc:0"), ("id", "alloc:-1"),
                             ("size_bytes", True), ("size_bytes", 2**64), ("align_bytes", 3),
                             ("align_bytes", 0), ("mutable", 1)):
            self.reject(lambda r: self.node(r, "alloc:1").update({field: value}))
        for value in (-1, 16, True, "8"):
            self.reject(lambda r: self.occurrence(r, "relocation").update(offset_bytes=value))
        self.reject(lambda r: self.occurrence(r, "relocation").update(shared_ref=0))

    def test_pointer_indirect_and_slice_root_metadata_stay_distinct(self):
        for form, field, value in (("pointer", "metadata", 4), ("pointer", "immutable", None),
                                   ("indirect", "shared_ref", False), ("indirect", "metadata", 0),
                                   ("slice", "offset_bytes", 1), ("slice", "metadata", True),
                                   ("slice", "metadata", None), ("slice", "form", "unknown")):
            self.reject(lambda r: self.occurrence(r, "allocation-root", form=form).update({field: value}))

    def test_static_initializers_are_attached_to_the_actual_static(self):
        self.reject(lambda r: self.occurrence(r, "static-initializer").update(target="alloc:1"))
        identity = "initializer:" + f"{4:032x}"
        self.reject(lambda r: self.node(r, identity).update(static="item:" + f"{8:032x}"))
        self.reject(lambda r: self.node(r, identity).update(static="item:" + f"{1:032x}"))

    def test_vtable_entries_and_materialization_have_typed_endpoints(self):
        for entry, field, value in (("method", "target", "alloc:1"), ("method", "local_codegen", None),
                                    ("method", "trait_ref", "not-a-trait-vptr"), ("size", "local_codegen", True),
                                    ("vacant", "target", "item:" + f"{1:032x}"),
                                    ("trait-vptr", "trait_ref", None), ("align", "slot", True),
                                    ("drop-in-place", "entry_kind", "unknown")):
            self.reject(lambda r: self.occurrence(r, "vtable-entry", entry_kind=entry).update({field: value}))
        self.reject(lambda r: self.occurrence(r, "vtable-materialization").update(target="alloc:3"))
        self.reject(lambda r: self.occurrence(r, "vtable-materialization").update(source="alloc:1"))

    def test_dispatch_policy_is_not_a_fabricated_local_codegen_decision(self):
        for key, value in (("local_codegen", None), ("local_codegen", 1), ("collector_direct_call", 0),
                           ("site", "unknown")):
            self.reject(lambda r: self.occurrence(r, "instance-use").update({key: value}))
        records = fixture_v2()
        use = self.occurrence(records, "instance-use")
        use.update(site="thread-local-shim", local_codegen=None, collector_direct_call=None)
        self.node(records, use["target"])["mono_item_kind"] = "shim-thread-local"
        self.assertEqual(self.parse(records)["status"], "collector_observed")
        self.reject(lambda r: self.occurrence(r, "instance-use").update(site="thread-local-shim", local_codegen=True))

    def test_occurrence_order_and_owner_cannot_be_rewritten(self):
        for value in (True, 1, -1, "0"):
            self.reject(lambda r: r[1]["dependency_occurrences"][0].update(ordinal=value))
        self.reject(lambda r: r[1]["dependency_occurrences"][0].update(owner="missing:used"))
        self.reject(lambda r: r[1]["dependency_occurrences"].reverse())
        def duplicate(r):
            r[1]["dependency_occurrences"].insert(0, r[1]["dependency_occurrences"][0])
            recount_dependencies(r)
        self.reject(duplicate)

    def test_dependencies_require_their_actual_encounters_and_vtable_request(self):
        def remove_and_reindex(records, row):
            records[1]["dependency_occurrences"].remove(row)
            ordinals = {}
            for occurrence in records[1]["dependency_occurrences"]:
                owner = occurrence["owner"]
                occurrence["ordinal"] = ordinals.get(owner, 0)
                ordinals[owner] = occurrence["ordinal"] + 1
            recount_dependencies(records)
        for kind, filters in (("allocation", {"target": "alloc:3"}),
                              ("static-initializer", {}), ("vtable", {}),
                              ("vtable-entry", {"slot": 1}), ("vtable-entry", {"slot": 5}),
                              ("vtable-materialization", {})):
            self.reject(lambda r: remove_and_reindex(r, self.occurrence(r, kind, **filters)))
        self.reject(lambda r: self.occurrence(r, "vtable-entry", slot=1).update(slot=0))

    def test_request_metadata_and_initializer_ownership_cannot_be_reassigned(self):
        self.reject(lambda r: self.occurrence(r, "vtable-entry", slot=0).update(entry_kind="size"))
        self.reject(lambda r: self.occurrence(r, "vtable-entry", slot=3).update(mode="mentioned", origin="required-const"))
        self.reject(lambda r: self.occurrence(r, "relocation").update(source="initializer:" + f"{4:032x}"))
        for value in (True, 2, 7):
            self.reject(lambda r: self.occurrence(r, "vtable").update(entry_count=value))
        self.reject(lambda r: self.occurrence(r, "instance-use").update(collector_direct_call=None))
        self.reject(lambda r: self.occurrence(r, "instance-use", site="asm-static").update(collector_direct_call=True))

    def test_reference_pairs_cannot_borrow_another_owner_or_mode_observation(self):
        def remove(r, kind, **fields):
            row = self.occurrence(r, kind, **fields)
            r[1]["dependency_occurrences"].remove(row)
            next_ordinal = {}
            for remaining in r[1]["dependency_occurrences"]:
                owner = remaining["owner"]
                remaining["ordinal"] = next_ordinal.get(owner, 0)
                next_ordinal[owner] = remaining["ordinal"] + 1
            recount_dependencies(r)
        # A mentioned owner still observes alloc:2; it cannot replace this use.
        self.reject(lambda r: remove(r, "allocation", target="alloc:2", mode="used"))
        # Required-const and static visits still observe alloc:1 independently.
        self.reject(lambda r: remove(r, "allocation", target="alloc:1", origin="mir"))
        self.reject(lambda r: remove(r, "instance-use", site="allocation-function"))
        self.reject(lambda r: remove(r, "instance-use", site="allocation-static"))
        self.reject(lambda r: remove(r, "instance-use", site="vtable-method"))
        self.reject(lambda r: self.occurrence(r, "instance-use", site="vtable-method").update(local_codegen=False))

    def test_allocation_form_and_provenance_obey_interpreter_invariants(self):
        self.reject(lambda r: self.occurrence(r, "allocation-root", form="indirect").update(target="alloc:3"))
        self.reject(lambda r: self.occurrence(r, "allocation-root", form="slice").update(target="alloc:3"))
        self.reject(lambda r: self.occurrence(r, "allocation-root", form="pointer").update(immutable=True, shared_ref=False))
        self.reject(lambda r: self.occurrence(r, "relocation").update(immutable=True, shared_ref=False))

    def test_empty_collector_and_metadata_only_path_keep_distinct_outcomes(self):
        header, snapshot, footer = fixture_v2()
        snapshot.update(items=[], roots=[], usage_edges=[], unplaced_items=[], item_count=0,
                        codegen_units={"empty": []}, dependency_nodes=[], dependency_owners=[],
                        dependency_occurrences=[])
        footer["item_count"] = 0
        records = [header, snapshot, footer]
        recount_dependencies(records)
        self.assertEqual(self.parse(records)["status"], "collector_observed")
        header["codegen_requested"] = False
        footer.update(item_count=None, snapshot_sha256=None, status="unmeasured")
        self.assertEqual(self.parse([header, footer])["status"], "unmeasured")



def fixture_v3():
    records = fixture_v2()
    header, snapshot, footer = records
    for record in records:
        record["schema"] = census.SCHEMA_V3
    header.update(collection_strategy="eager", eager_const_root_scope=census.EAGER_CONST_ROOT_SCOPE,
                  eager_const_root_identity_scheme=census.EAGER_CONST_ROOT_IDENTITY)
    snapshot["dependency_nodes"].extend([
        dict(id="alloc:77", kind="memory-allocation", size_bytes=8, align_bytes=1, mutable=False),
        dict(id="alloc:78", kind="function-allocation", target="item:" + f"{2:032x}"),
    ])
    snapshot["dependency_nodes"].sort(key=lambda row: row["id"])
    owners, occurrences = [], []
    for n, target in ((1, "alloc:77"), (2, "alloc:78"), (3, "alloc:78"), (4, None)):
        owner = "eager-const:" + f"{n:032x}"
        count = 0 if target is None else 2 if target == "alloc:77" else 3
        owners.append(dict(id=owner, kind="free-const", phase="root-discovery",
                           **{"def": f"fixture::ROOT{n}"}, def_path_hash=f"{n:032x}",
                           definition_is_local=True, collected=False, collection_mode="used",
                           dependency_count=count))
        if target is not None:
            context = dict(owner=owner, mode="used", origin="eager-const-root")
            memory = target == "alloc:77"
            occurrences.extend([
                dict(**context, ordinal=0, kind="allocation-root", target=target,
                     form="indirect" if memory else "pointer", offset_bytes=0,
                     metadata=None, immutable=None if memory else False,
                     shared_ref=None if memory else False),
                dict(**context, ordinal=1, kind="allocation", target=target),
            ])
            if not memory:
                occurrences.append(dict(**context, ordinal=2, kind="instance-use",
                                        target="item:" + f"{2:032x}", site="allocation-function",
                                        collector_direct_call=None, local_codegen=True))
    snapshot.update(eager_const_root_owners=owners, eager_const_root_occurrences=occurrences)
    recount_dependencies(records)
    recount_eager_roots(records)
    return records


def recount_eager_roots(records):
    snapshot = records[1]
    for singular, plural in (("owner", "owners"), ("occurrence", "occurrences")):
        snapshot["eager_const_root_" + singular + "_count"] = len(snapshot["eager_const_root_" + plural])


class EagerConstRoots(unittest.TestCase):
    def parse(self, records=None):
        return census.parse_census(encode(fixture_v3() if records is None else records),
                                   input_path="/fixture/instances.rs", exit_code=0)

    def reject(self, mutation):
        records = fixture_v3()
        mutation(records)
        result = self.parse(records)
        self.assertEqual(result["status"], "malformed", result)
        self.assertFalse(result["whole_program_complete"])

    def test_distinct_const_owners_shared_allocation_and_empty_scan(self):
        records = fixture_v3()
        result = self.parse(records)
        self.assertEqual(result["status"], "collector_observed", result)
        self.assertEqual(result["item_count"], 5)
        self.assertEqual(len(records[1]["dependency_owners"]), 6)
        self.assertEqual(records[1]["eager_const_root_owners"][-1]["dependency_count"], 0)
        self.assertEqual(sum(r["kind"] == "allocation" and r["target"] == "alloc:78"
                             for r in records[1]["eager_const_root_occurrences"]), 2)

    def test_strict_old_wire_contracts_are_not_broadened(self):
        for schema in (census.SCHEMA, census.SCHEMA_V2):
            self.reject(lambda r: [row.update(schema=schema) for row in r])
        for records in (fixture(), fixture_v2()):
            result = self.parse(records)
            self.assertEqual(result["status"], "collector_observed", result)
        for index in range(3):
            self.reject(lambda r: r[index].update(schema=census.SCHEMA_V2))

    def test_scope_and_root_identity_scheme_are_exact(self):
        self.reject(lambda r: r[0].update(eager_const_root_scope="all-constant-evaluation"))
        self.reject(lambda r: r[0].update(eager_const_root_identity_scheme="content-hash"))
        self.reject(lambda r: r[0].pop("eager_const_root_scope"))
        self.reject(lambda r: r[0].update(collection_strategy="lazy"))

    def test_root_owner_is_local_free_const_not_collected_item(self):
        for field, value in (("kind", "item"), ("phase", "recursive-body"),
                             ("collected", True), ("collected", 0),
                             ("definition_is_local", False), ("definition_is_local", 1),
                             ("collection_mode", "mentioned"), ("def", ""),
                             ("def_path_hash", "not-a-hash"), ("id", "item:" + "1" * 32)):
            with self.subTest(field=field, value=value):
                self.reject(lambda r: r[1]["eager_const_root_owners"][0].update({field: value}))
        self.reject(lambda r: r[1]["eager_const_root_owners"][0].update(item="item:" + "1" * 32))
        self.reject(lambda r: r[1]["eager_const_root_owners"][0].update(def_path_hash="a" * 32))

    def test_table_and_per_owner_counts_are_exact(self):
        for key in ("eager_const_root_owner_count", "eager_const_root_occurrence_count"):
            for value in (-1, True, 0, 100):
                self.reject(lambda r: r[1].update({key: value}))
        for value in (-1, True, 0, 100):
            self.reject(lambda r: r[1]["eager_const_root_owners"][0].update(dependency_count=value))
        self.reject(lambda r: r[1].pop("eager_const_root_owners"))

    def test_owner_and_occurrence_tables_keep_exact_order(self):
        self.reject(lambda r: r[1]["eager_const_root_owners"].reverse())
        self.reject(lambda r: r[1]["eager_const_root_occurrences"].reverse())
        def duplicate(r):
            r[1]["eager_const_root_owners"].insert(0, r[1]["eager_const_root_owners"][0])
            recount_eager_roots(r)
        self.reject(duplicate)
        self.reject(lambda r: r[1]["eager_const_root_occurrences"][0].update(ordinal=True))
        self.reject(lambda r: r[1]["eager_const_root_occurrences"][0].update(ordinal=1))

    def test_occurrences_cannot_cross_population_boundaries(self):
        def move_root(r):
            r[1]["dependency_occurrences"].insert(0, r[1]["eager_const_root_occurrences"].pop(0))
            recount_dependencies(r)
            recount_eager_roots(r)
        self.reject(move_root)
        self.reject(lambda r: r[1]["dependency_occurrences"][0].update(origin="eager-const-root"))
        self.reject(lambda r: r[1]["eager_const_root_occurrences"][0].update(owner=r[1]["dependency_owners"][0]["id"]))

    def test_root_occurrence_context_and_allowed_sites(self):
        for field, value in (("mode", "mentioned"), ("origin", "mir"), ("origin", "required-const")):
            self.reject(lambda r: r[1]["eager_const_root_occurrences"][0].update({field: value}))
        self.reject(lambda r: r[1]["eager_const_root_occurrences"][4].update(site="instance-use", collector_direct_call=True))
        self.reject(lambda r: r[1]["eager_const_root_occurrences"][4].update(collector_direct_call=False))

    def test_pairing_and_filter_decisions_remain_required(self):
        def remove(r, index):
            rows = r[1]["eager_const_root_occurrences"]
            removed = rows.pop(index)
            remaining = [row for row in rows if row["owner"] == removed["owner"]]
            for ordinal, row in enumerate(remaining):
                row["ordinal"] = ordinal
            for owner in r[1]["eager_const_root_owners"]:
                if owner["id"] == removed["owner"]:
                    owner["dependency_count"] = len(remaining)
            recount_eager_roots(r)
        self.reject(lambda r: remove(r, 1))  # paired memory encounter
        self.reject(lambda r: remove(r, 4))  # function allocation's filter decision
        self.reject(lambda r: r[1]["eager_const_root_occurrences"][1].update(target="alloc:2"))
        self.reject(lambda r: r[1]["eager_const_root_occurrences"][4].update(target="item:" + f"{3:032x}"))

    def test_root_only_nodes_cannot_be_missing_or_orphaned(self):
        def missing(r):
            r[1]["dependency_nodes"] = [row for row in r[1]["dependency_nodes"] if row["id"] != "alloc:77"]
            recount_dependencies(r)
        self.reject(missing)
        def orphan(r):
            r[1]["dependency_nodes"].append(dict(id="alloc:99", kind="memory-allocation",
                                                size_bytes=8, align_bytes=1, mutable=False))
            r[1]["dependency_nodes"].sort(key=lambda row: row["id"])
            recount_dependencies(r)
        self.reject(orphan)

    def test_root_relocation_requires_source_encounter_in_same_owner(self):
        def wrong_source(r):
            owner = r[1]["eager_const_root_owners"][0]
            row = dict(owner=owner["id"], ordinal=2, mode="used", origin="eager-const-root",
                       kind="relocation", source="alloc:1", target="alloc:3", offset_bytes=0,
                       immutable=True, shared_ref=True)
            r[1]["eager_const_root_occurrences"].insert(2, row)
            owner["dependency_count"] += 1
            recount_eager_roots(r)
        self.reject(wrong_source)

    def test_root_rows_cannot_replace_recursive_used_owner_population(self):
        def remove_used(r):
            r[1]["dependency_owners"].pop(1)
            recount_dependencies(r)
        self.reject(remove_used)

    def test_existing_vtable_allocation_materialization_keeps_root_context(self):
        records = fixture_v3()
        rows = records[1]["dependency_occurrences"]
        start = next(i for i, row in enumerate(rows)
                     if row["kind"] == "allocation-root" and row["target"] == "alloc:5")
        end = next(i for i in range(start + 1, len(rows)) if rows[i]["kind"] == "allocation-root")
        visits = copy.deepcopy(rows[start:end])
        owner = records[1]["eager_const_root_owners"][-1]
        for ordinal, row in enumerate(visits):
            row.update(owner=owner["id"], ordinal=ordinal, mode="used", origin="eager-const-root")
        owner["dependency_count"] = len(visits)
        records[1]["eager_const_root_occurrences"].extend(visits)
        recount_eager_roots(records)
        result = self.parse(records)
        self.assertEqual(result["status"], "collector_observed", result)
        # A request in another recursive owner cannot replace this particular
        # symbolic allocation's actual materialization encounter.
        visits = [row for row in visits if row["kind"] != "vtable-materialization"]
        for ordinal, row in enumerate(visits):
            row["ordinal"] = ordinal
        records[1]["eager_const_root_occurrences"] = [
            row for row in records[1]["eager_const_root_occurrences"] if row["owner"] != owner["id"]
        ] + visits
        owner["dependency_count"] = len(visits)
        recount_eager_roots(records)
        self.assertEqual(self.parse(records)["status"], "malformed")

    def test_residual_disclosures_and_claim_boundary_stay_intact(self):
        for index in (0, 2):
            self.reject(lambda r: r[index]["unmeasured"].remove("eager-constant-root-dependencies"))
        self.reject(lambda r: r[2].update(whole_program_complete=True))

    def test_no_eager_scans_and_metadata_unmeasured_remain_distinct(self):
        records = fixture_v3()
        snapshot = records[1]
        snapshot["eager_const_root_owners"] = []
        snapshot["eager_const_root_occurrences"] = []
        snapshot["dependency_nodes"] = [row for row in snapshot["dependency_nodes"] if row["id"] not in ("alloc:77", "alloc:78")]
        records[0]["collection_strategy"] = "lazy"
        recount_eager_roots(records)
        recount_dependencies(records)
        self.assertEqual(self.parse(records)["status"], "collector_observed")
        records[0]["codegen_requested"] = False
        records[2].update(item_count=None, snapshot_sha256=None, status="unmeasured")
        self.assertEqual(self.parse([records[0], records[2]])["status"], "unmeasured")


if __name__ == "__main__":
    unittest.main()
