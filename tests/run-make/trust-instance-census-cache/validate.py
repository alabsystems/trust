"""Compare real cold/warm v3 dependency censuses; requires Python 3.10 or newer.

The Rust driver owns actual compiler exits and the opaque query-kind assertion.
This adds no claim that each owner loaded from disk or that the census is complete.
"""

from pathlib import Path
import hashlib
import importlib.util
import sys


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


def one(rows):
    assert len(rows) == 1, rows
    return rows[0]


def used_owner_rows(snapshot, item, origin):
    owner = one([row for row in snapshot["dependency_owners"]
                 if row["item"] == item and row["collection_mode"] == "used"])
    rows = [row for row in snapshot["dependency_occurrences"] if row["owner"] == owner["id"]]
    assert all(row["mode"] == "used" and row["origin"] == origin for row in rows)
    return rows


def static_object_method(snapshot):
    """Follow OBJECT's actual static allocation path, without inventing a request.

    collector::collect_alloc handles GlobalAlloc::VTable by materializing it
    and traversing its pointer relocations. It does not call the separate
    create_mono_items_for_vtable_methods symbolic-request observer.
    """
    nodes = {node["id"]: node for node in snapshot["dependency_nodes"]}
    obj = one([node for node in nodes.values() if node["kind"] == "item"
               and node["def"].endswith("::OBJECT")])
    assert obj["mono_item_kind"] == "static" and obj["definition_is_local"] and obj["collected"]
    rows = used_owner_rows(snapshot, obj["id"], "static")
    initializer = nodes[one([row for row in rows if row["kind"] == "static-initializer"])["target"]]
    assert initializer["kind"] == "static-initializer" and initializer["static"] == obj["id"]
    pointer = initializer["align_bytes"]
    assert pointer in (4, 8) and initializer["size_bytes"] == 2 * pointer
    assert initializer["mutable"] is False
    roots = [row for row in rows if row["kind"] == "relocation" and row["source"] == initializer["id"]]
    assert len(roots) == 2 and {row["offset_bytes"] for row in roots} == {0, pointer}
    data = nodes[one([row for row in roots if row["offset_bytes"] == 0])["target"]]
    assert data["kind"] == "memory-allocation" and data["size_bytes"] == 8 and data["mutable"] is False
    symbolic = nodes[one([row for row in roots if row["offset_bytes"] == pointer])["target"]]
    assert symbolic["kind"] == "vtable-allocation" and symbolic["impl_ty"] == "u64"
    assert "Trait(Value)" in symbolic["trait_type"] and "::marker::Sync)" in symbolic["trait_type"]
    materialization = one([row for row in rows if row["kind"] == "vtable-materialization"
                           and row["source"] == symbolic["id"]])
    memory = nodes[materialization["target"]]
    # rustc's vtable provider reserves drop/size/align, then Value's one method.
    assert memory["kind"] == "memory-allocation" and memory["mutable"] is False
    assert memory["size_bytes"] == 4 * pointer and memory["align_bytes"] == pointer
    method_edge = one([row for row in rows if row["kind"] == "relocation" and row["source"] == memory["id"]])
    assert method_edge["offset_bytes"] == 3 * pointer
    allocation = nodes[method_edge["target"]]
    assert allocation["kind"] == "function-allocation"
    method = nodes[allocation["target"]]
    assert method["kind"] == "item" and method["def_kind"] == "AssocFn"
    assert method["def"].endswith("::{impl#0}::value") and method["definition_is_local"] and method["collected"]
    decision = one([row for row in rows if row["kind"] == "instance-use"
                    and row["site"] == "allocation-function" and row["target"] == method["id"]])
    assert decision["local_codegen"] is True and decision["collector_direct_call"] is None
    # The strict reader separately verifies each immediate allocation/decision
    # pair. Keep the source-specific path and its method identity here.
    return method["id"]


def direct_object_method(snapshot, method):
    """Require the explicit MIR coercion and its exact method/filter decision."""
    nodes = {node["id"]: node for node in snapshot["dependency_nodes"]}
    function = one([node for node in nodes.values() if node["kind"] == "item"
                    and node["def"].endswith("::direct_object")])
    assert function["definition_is_local"] and function["collected"]
    rows = used_owner_rows(snapshot, function["id"], "mir")
    request = one([row for row in rows if row["kind"] == "vtable"])
    vtable = nodes[request["target"]]
    assert vtable["kind"] == "vtable" and vtable["impl_ty"] == "u64"
    assert "Trait(Value)" in vtable["trait_type"] and "::marker::Sync)" in vtable["trait_type"]
    assert request["entry_count"] == 4
    entries = [row for row in rows if row["kind"] == "vtable-entry" and row["source"] == vtable["id"]]
    assert [(row["slot"], row["entry_kind"]) for row in entries] == [
        (0, "drop-in-place"), (1, "size"), (2, "align"), (3, "method")]
    assert entries[3]["target"] == method and entries[3]["local_codegen"] is True
    decision = one([row for row in rows if row["kind"] == "instance-use"
                    and row["site"] == "vtable-method" and row["target"] == method])
    assert decision["local_codegen"] is True and decision["collector_direct_call"] is None


def main():
    root, source, opt, cold, warm = sys.argv[1:]
    root, source = Path(root), Path(source)
    assert source.is_absolute() and opt in ("0", "3")
    census = load("cache_census_reader", root / "scripts/rust_instance_census.py")
    live = load("cache_census_live", root / "scripts/tests/rust_instance_census_live.py")
    snapshots = []
    for report in (Path(cold), Path(warm)):
        with report.open("rb") as stream:
            raw = stream.read(census.MAX_BYTES + 1)
        parsed = census.parse_census(raw, input_path=str(source), exit_code=0)
        assert parsed["status"] == "collector_observed" and not parsed["errors"], parsed
        header = parsed["header"]
        assert header["schema"] == census.SCHEMA_V3
        assert header["collection_strategy"] == "lazy"
        assert header["incremental"] and header["codegen_requested"]
        assert not header["verification_enabled"] and not header["direct_lowering"]
        assert header["optimization"] == ("No" if opt == "0" else "Aggressive")
        assert parsed["sources"][str(source)] == "sha256=" + hashlib.sha256(source.read_bytes()).hexdigest()
        snapshot = parsed["snapshot"]
        assert snapshot["eager_const_root_owner_count"] == 0
        assert snapshot["eager_const_root_occurrence_count"] == 0
        assert snapshot["eager_const_root_owners"] == []
        assert snapshot["eager_const_root_occurrences"] == []
        assert all(snapshot["dependency_" + table] for table in ("nodes", "owners", "occurrences"))
        nodes = {node["id"]: node for node in snapshot["dependency_nodes"]}
        kinds = {node["kind"] for node in nodes.values()}
        assert {"function-allocation", "static-allocation", "static-initializer", "vtable-allocation", "vtable"} <= kinds
        occurrences = snapshot["dependency_occurrences"]
        assert any(row["kind"] == "allocation-root" and row["form"] == "pointer" for row in occurrences)
        assert any(row["kind"] == "vtable-entry" for row in occurrences)
        direct_object_method(snapshot, static_object_method(snapshot))
        # Pointer-free statics are still dependencies. Require the actual BYTES
        # initializer and its allocation metadata, with no fabricated relocation.
        byte_initializers = [node for node in nodes.values()
                             if node["kind"] == "static-initializer"
                             and nodes[node["static"]]["def"].endswith("::BYTES")]
        assert len(byte_initializers) == 1
        byte_initializer = byte_initializers[0]
        assert byte_initializer["size_bytes"] == 8 and byte_initializer["align_bytes"] == 1
        assert byte_initializer["mutable"] is False
        assert any(row["kind"] == "static-initializer" and row["target"] == byte_initializer["id"]
                   for row in occurrences)
        assert not any(row["kind"] == "relocation" and row["source"] == byte_initializer["id"]
                       for row in occurrences)
        # The foreign declaration has a local DefId, but the collector's actual
        # direct-call decision excludes its body from local code generation.
        foreign = [node for node in nodes.values() if node["kind"] == "item"
                   and node["def"].endswith("::abs")]
        assert len(foreign) == 1 and foreign[0]["collected"] is False
        assert any(row["kind"] == "instance-use" and row["target"] == foreign[0]["id"]
                   and row["site"] == "instance-use" and row["mode"] == "used"
                   and row["origin"] == "mir" and row["collector_direct_call"] is True
                   and row["local_codegen"] is False for row in occurrences)
        # The real function-pointer static must retain both distinct function
        # relocations. Neither metadata equality nor canonicalization may merge them.
        initializers = [node for node in nodes.values() if node["kind"] == "static-initializer"
                        and nodes[node["static"]]["def"].endswith("::FUNCTIONS")]
        assert len(initializers) == 1
        relocations = [row for row in occurrences if row["kind"] == "relocation"
                       and row["source"] == initializers[0]["id"]]
        assert len(relocations) == 2 and len({row["target"] for row in relocations}) == 2
        assert len({row["offset_bytes"] for row in relocations}) == 2
        functions = []
        for row in relocations:
            allocation = nodes[row["target"]]
            assert allocation["kind"] == "function-allocation"
            functions.append(nodes[allocation["target"]]["def"].rsplit("::", 1)[-1])
        assert set(functions) == {"plus_one", "twice"}
        snapshots.append(live.comparable_snapshot(snapshot))
    # This is the production live helper's bijective allocation renaming. It
    # preserves IDs' alias relationships, occurrence order, owners and typed edges.
    assert snapshots[0] == snapshots[1], "cold/warm typed dependency populations differ"


if __name__ == "__main__":
    main()
