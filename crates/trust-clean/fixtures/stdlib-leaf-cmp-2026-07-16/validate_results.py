#!/usr/bin/env python3
"""Validate one cmp corpus lane against complete FF-gate and census records."""

import csv
import json
from pathlib import Path
import sys


FF_HEADER = [
    "def_path",
    "cluster_tag",
    "via_ir_shape",
    "via_ir_safety",
    "via_mirsem_shape",
    "via_mirsem_sl_safety_discharged",
    "via_mirsem_call_requires",
    "via_mirsem_loop_full",
    "fully_faithful",
]
CENSUS_HEADER = [
    "def_path",
    "total",
    "inhabited",
    "type_grounded_not_inhabited",
    "not_grounded",
    "kernel_rejected",
    "safety_obligations",
    "safety_discharged",
    "fully_faithful",
    "via_trustir",
    "mirsem_fallback",
    "declined",
    "expr_fold_decline",
]
EXPECTED_HEADER = FF_HEADER + [
    "total",
    "inhabited",
    "type_grounded_not_inhabited",
    "not_grounded",
    "kernel_rejected",
    "safety_obligations",
    "safety_discharged",
    "census_fully_faithful",
    "via_trustir",
    "mirsem_fallback",
    "declined",
    "expr_fold_decline",
]


def read_tsv(path: Path) -> tuple[list[str], list[list[str]]]:
    with path.open(encoding="utf-8", newline="") as stream:
        rows = list(csv.reader(stream, delimiter="\t"))
    if not rows:
        raise SystemExit(f"empty TSV: {path}")
    if any(not row for row in rows):
        raise SystemExit(f"blank row in TSV: {path}")
    return rows[0], rows[1:]


def keyed(path: Path, rows: list[list[str]], width: int) -> dict[str, list[str]]:
    result = {}
    for row in rows:
        if len(row) != width:
            raise SystemExit(f"wrong TSV width in {path}: expected {width}, got {len(row)}")
        if row[0] in result:
            raise SystemExit(f"duplicate TSV row in {path}: {row[0]}")
        result[row[0]] = row
    return result


def main() -> None:
    if len(sys.argv) != 5:
        raise SystemExit(
            f"usage: {Path(sys.argv[0]).name} "
            "<expected.tsv> <corpus-directory> <ff.tsv> <census.tsv>"
        )
    expected_path, corpus_path, ff_path, census_path = map(Path, sys.argv[1:])

    expected_header, expected_rows = read_tsv(expected_path)
    if expected_header not in (EXPECTED_HEADER, EXPECTED_HEADER + ["wall"]):
        raise SystemExit(f"expected-result schema drift in {expected_path}")
    expected = keyed(expected_path, expected_rows, len(expected_header))

    ff_header, ff_rows = read_tsv(ff_path)
    if ff_header != FF_HEADER:
        raise SystemExit(f"FF-gate schema drift in {ff_path}")
    ff = keyed(ff_path, ff_rows, len(FF_HEADER))

    census_header, census_rows = read_tsv(census_path)
    if census_header != CENSUS_HEADER:
        raise SystemExit(f"census schema drift in {census_path}")
    census = keyed(census_path, census_rows, len(CENSUS_HEADER))

    corpus = {}
    for path in sorted(corpus_path.rglob("*.json")):
        try:
            value = json.loads(path.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError) as error:
            raise SystemExit(f"cannot parse corpus JSON {path}: {error}") from error
        def_path = value.get("def_path")
        if not isinstance(def_path, str):
            raise SystemExit(f"missing string def_path in {path}")
        if def_path in corpus:
            raise SystemExit(f"duplicate corpus def_path {def_path}: {corpus[def_path]}, {path}")
        corpus[def_path] = path

    if set(expected) != set(corpus) or set(expected) != set(ff) or set(expected) != set(census):
        raise SystemExit(
            "lane inventory mismatch: "
            f"expected={sorted(expected)} corpus={sorted(corpus)} "
            f"ff={sorted(ff)} census={sorted(census)}"
        )

    for def_path, row in expected.items():
        if ff[def_path] != row[: len(FF_HEADER)]:
            raise SystemExit(f"FF-gate result drift for {def_path}")
        expected_census = [def_path] + row[len(FF_HEADER) : len(EXPECTED_HEADER)]
        if census[def_path] != expected_census:
            raise SystemExit(f"census result drift for {def_path}")
        expected_faithful = "1" if row[8] == "true" else "0"
        if row[1] == "FULLY_FAITHFUL" and row[8] != "true":
            raise SystemExit(f"inconsistent FULLY_FAITHFUL record for {def_path}")
        if row[1] != "FULLY_FAITHFUL" and row[8] != "false":
            raise SystemExit(f"inconsistent non-FF record for {def_path}")
        if row[16] != expected_faithful:
            raise SystemExit(f"FF-gate/census faithful mismatch for {def_path}")

    print(f"validated {len(expected)} exact rows from {expected_path.name}")


if __name__ == "__main__":
    main()
