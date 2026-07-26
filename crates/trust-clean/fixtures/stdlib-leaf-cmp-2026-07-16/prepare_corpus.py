#!/usr/bin/env python3
"""Slice exact cmp/SOURCE bodies and derive the fail-closed forgery corpus."""

from copy import deepcopy
import json
import os
from pathlib import Path
import re
import sys


CORE_PATHS = {
    "cmp::min",
    "cmp::max",
    "cmp::Ord::min",
    "cmp::Ord::max",
    "cmp::Ord::clamp",
    "cmp::min_by",
    "cmp::max_by",
    "cmp::min_by_key",
    "cmp::max_by_key",
    "<num::nonzero::NonZero<T> as cmp::Ord>::min",
    "<num::nonzero::NonZero<T> as cmp::Ord>::max",
    "<num::nonzero::NonZero<T> as cmp::Ord>::clamp",
}
CONTROL_PATHS = {
    "ctl_min_i32",
    "ctl_max_i32",
    "ctl_clamp_i32",
    "ctl_min_u8",
    "ctl_max_u8",
}
WRAPPER_PATHS = {
    "w_ord_min_i32",
    "w_ord_max_i32",
    "w_cmp_min_i32",
    "w_cmp_max_i32",
    "w_clamp_i32",
    "w_min_u8",
    "w_max_u8",
}
CORE_TOKEN = re.compile(r"(?<![0-9A-Za-z_])core::")
SOURCE_TOKEN = re.compile(r"(?<![0-9A-Za-z_])stdlib_leaf_cmp_source::")


def json_paths(root: Path) -> list[Path]:
    return sorted(path for path in root.rglob("*.json") if path.is_file())


def normalize_identities(node: object, token: re.Pattern[str]) -> object:
    if isinstance(node, list):
        return [normalize_identities(value, token) for value in node]
    if not isinstance(node, dict):
        return node
    result = {}
    for key, value in node.items():
        if key in {"def_path", "func"} and isinstance(value, str):
            result[key] = token.sub("", value)
        elif key == "name" and isinstance(value, str) and token.search(value):
            # Type/ADT identities use `name`; ordinary local and variant names
            # are left byte-for-byte unchanged.
            result[key] = token.sub("", value)
        else:
            result[key] = normalize_identities(value, token)
    return result


def load_exact(
    root: Path,
    expected_scan_count: int,
    raw_wanted: set[str],
    token: re.Pattern[str],
    wanted: set[str],
) -> dict[str, dict]:
    paths = json_paths(root)
    if len(paths) != expected_scan_count:
        raise SystemExit(
            f"recursive dump inventory mismatch for {root}: "
            f"expected {expected_scan_count}, found {len(paths)}"
        )
    selected: dict[str, dict] = {}
    for path in paths:
        try:
            raw = json.loads(path.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError) as error:
            raise SystemExit(f"cannot parse extracted JSON {path}: {error}") from error
        raw_def_path = raw.get("def_path")
        if raw_def_path not in raw_wanted:
            continue
        body = normalize_identities(raw, token)
        def_path = body.get("def_path")
        if def_path not in wanted:
            raise SystemExit(f"identity normalization produced unexpected path: {def_path!r}")
        if def_path in selected:
            raise SystemExit(f"duplicate target body: {def_path}")
        selected[def_path] = body
    if set(selected) != wanted:
        raise SystemExit(
            f"target inventory mismatch: "
            f"missing={sorted(wanted - set(selected))} "
            f"extra={sorted(set(selected) - wanted)}"
        )
    return selected


def output_name(def_path: str) -> str:
    return re.sub(r"[^0-9A-Za-z]+", "_", def_path).strip("_") + ".json"


def write_bodies(destination: Path, bodies: dict[str, dict], prefix: str = "") -> None:
    destination.mkdir()
    for def_path in sorted(bodies):
        path = destination / (prefix + output_name(def_path))
        path.write_text(
            json.dumps(bodies[def_path], indent=2, ensure_ascii=False) + "\n",
            encoding="utf-8",
        )


def block(body: dict, block_id: int) -> dict:
    matches = [value for value in body["body"]["blocks"] if value.get("id") == block_id]
    if len(matches) != 1:
        raise SystemExit(f"expected exactly one basic block {block_id}")
    return matches[0]


def only_assign(body: dict, block_id: int) -> dict:
    statements = block(body, block_id).get("stmts")
    if not isinstance(statements, list) or len(statements) != 1:
        raise SystemExit(f"expected one statement in basic block {block_id}")
    assign = statements[0].get("Assign")
    if not isinstance(assign, dict):
        raise SystemExit(f"expected Assign in basic block {block_id}")
    return assign


def assert_min_control(body: dict) -> None:
    if body.get("def_path") != "ctl_min_i32" or body.get("name") != "ctl_min_i32":
        raise SystemExit("forgery base is not ctl_min_i32")
    compare = only_assign(body, 0)["rvalue"]
    if compare != {
        "BinaryOp": [
            "Lt",
            {"Copy": {"local": 2, "projections": []}},
            {"Copy": {"local": 1, "projections": []}},
        ]
    }:
        raise SystemExit("ctl_min_i32 comparison shape drifted")
    if block(body, 0).get("terminator", {}).get("SwitchInt") is None:
        raise SystemExit("ctl_min_i32 no longer has the expected select terminator")
    if only_assign(body, 1)["rvalue"] != {"Use": {"Copy": {"local": 2, "projections": []}}}:
        raise SystemExit("ctl_min_i32 false arm drifted")
    if only_assign(body, 2)["rvalue"] != {"Use": {"Copy": {"local": 1, "projections": []}}}:
        raise SystemExit("ctl_min_i32 true arm drifted")
    if only_assign(body, 3)["rvalue"] != {"Use": {"Copy": {"local": 3, "projections": []}}}:
        raise SystemExit("ctl_min_i32 return join drifted")


def named_copy(base: dict, name: str) -> dict:
    value = deepcopy(base)
    value["name"] = name
    value["def_path"] = name
    return value


def make_forgeries(base: dict) -> dict[str, dict]:
    assert_min_control(base)
    result = {}

    name = "C1_dangling_local"
    value = named_copy(base, name)
    only_assign(value, 0)["rvalue"]["BinaryOp"][1]["Copy"]["local"] = 9
    result[name] = value

    name = "C2_type_lie_bool_from_add"
    value = named_copy(base, name)
    value["body"]["locals"][0]["ty"] = "Bool"
    value["body"]["return_ty"] = "Bool"
    only_assign(value, 3)["rvalue"] = {
        "BinaryOp": [
            "Add",
            {"Copy": {"local": 1, "projections": []}},
            {"Copy": {"local": 2, "projections": []}},
        ]
    }
    result[name] = value

    name = "C3_div_by_zero"
    value = named_copy(base, name)
    only_assign(value, 1)["rvalue"] = {
        "BinaryOp": [
            "Div",
            {"Copy": {"local": 2, "projections": []}},
            {"Constant": {"Int": 0}},
        ]
    }
    result[name] = value

    name = "C4_opaque_call"
    value = named_copy(base, name)
    target = block(value, 1)
    span = only_assign(value, 1)["span"]
    target["stmts"] = []
    target["terminator"] = {
        "Call": {
            "func": "evil::opaque_oracle",
            "args": [{"Copy": {"local": 2, "projections": []}}],
            "dest": {"local": 3, "projections": []},
            "target": 3,
            "span": span,
            "atomic": None,
            "is_foreign": False,
            "is_unsafe_sig": False,
        }
    }
    result[name] = value

    name = "C5_unchecked_overflow_add"
    value = named_copy(base, name)
    only_assign(value, 2)["rvalue"] = {
        "BinaryOp": [
            "Add",
            {"Copy": {"local": 1, "projections": []}},
            {"Constant": {"Int": 2147483647}},
        ]
    }
    result[name] = value

    name = "C6_valid_select_control"
    result[name] = named_copy(base, name)
    return result


def main() -> None:
    if len(sys.argv) != 5:
        raise SystemExit(
            f"usage: {Path(sys.argv[0]).name} "
            "<core-dump> <core-count> <source-dump> <candidate-root>"
        )
    core_root = Path(sys.argv[1])
    core_count = int(sys.argv[2])
    source_root = Path(sys.argv[3])
    destination = Path(sys.argv[4])
    destination.mkdir(exist_ok=True)
    if any(destination.iterdir()):
        raise SystemExit(f"candidate root is not empty: {destination}")

    core = load_exact(
        core_root,
        core_count,
        {f"core::{path}" for path in CORE_PATHS if not path.startswith("<")}
        | {
            path.replace("<num::", "<core::num::").replace(" as cmp::", " as core::cmp::")
            for path in CORE_PATHS
            if path.startswith("<")
        },
        CORE_TOKEN,
        CORE_PATHS,
    )
    source_wanted = CONTROL_PATHS | WRAPPER_PATHS
    source = load_exact(
        source_root,
        len(source_wanted),
        {f"stdlib_leaf_cmp_source::{path}" for path in source_wanted},
        SOURCE_TOKEN,
        source_wanted,
    )

    write_bodies(destination / "dumps", core)
    write_bodies(
        destination / "controls",
        {path: source[path] for path in CONTROL_PATHS},
    )
    write_bodies(
        destination / "wrappers",
        {path: source[path] for path in WRAPPER_PATHS},
    )
    forgeries = make_forgeries(source["ctl_min_i32"])
    write_bodies(destination / "forgeries", forgeries, prefix="forgery__")
    print(
        f"scanned {core_count} exact core bodies and {len(source_wanted)} exact "
        f"SOURCE bodies; selected {len(core)} real, {len(CONTROL_PATHS)} controls, "
        f"{len(WRAPPER_PATHS)} wrappers, and derived {len(forgeries)} forgeries"
    )


if __name__ == "__main__":
    main()
