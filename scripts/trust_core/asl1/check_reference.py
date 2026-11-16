#!/usr/bin/env python3
"""Check the immutable BSD source population and the explicit leaf denominator.

This checks source custody and classification, not OCaml/Lean refinement.
"""
import hashlib
import json
from pathlib import Path
import re


def check(root: Path) -> dict:
    manifest = json.loads((root / "reference/SOURCE.json").read_text())
    assert manifest["repository"] == "herd/herdtools7"
    assert manifest["tag"] == "ASLRefEAC1"
    assert manifest["commit"] == "ffad2692c4580538e8db7bf6631aa886edfc7423"
    assert manifest["license"] == "BSD-3-Clause"
    assert manifest["licensed_arm_package_ingested"] is False
    expected = set()
    for row in manifest["files"]:
        path = root / row["path"]
        assert path.parent == root / "reference/aslref" and not path.is_symlink()
        data = path.read_bytes()
        assert len(data) == row["bytes"]
        assert hashlib.sha256(data).hexdigest() == row["sha256"], path
        assert row["path"] not in expected
        expected.add(row["path"])
    actual = {str(p.relative_to(root)) for p in (root / "reference/aslref").iterdir()}
    assert actual == expected
    ast = (root / "reference/aslref/AST.mli").read_text()
    ops_text = ast.split("type binop =", 1)[1].split(
        "(** Operations on base value of arity two.", 1
    )[0]
    operators = re.findall(r"`([A-Z_]+)", ops_text)
    assert len(operators) == len(set(operators)) == 26
    fixtures = (root / "Asl1/Fixtures.lean").read_text()
    unsupported_text = fixtures.split("def unsupportedOps : List RawOp :=", 1)[1].split(
        "theorem unsupported_ops_refuse", 1
    )[0]
    unsupported = re.findall(r"\.([A-Z_]+)", unsupported_text)
    assert len(unsupported) == len(set(unsupported)) == 24
    assert set(operators) == set(unsupported) | {"ADD", "SUB"}
    assert not set(unsupported) & {"ADD", "SUB"}
    importer = (root / "Asl1/Import.lean").read_text()
    raw_op_text = importer.split("inductive RawOp where", 1)[1].split(
        "deriving DecidableEq", 1
    )[0]
    assert re.findall(r"\| ([A-Z_]+)", raw_op_text) == operators
    literal_text = ast.split("type literal =", 1)[1].split(
        "(* -------------------------------------------------------------------------", 1
    )[0]
    literals = re.findall(r"\| (L_[A-Za-z]+)", literal_text)
    assert len(literals) == 6
    return {
        "status": "BSD_SOURCE_CUSTODY_AND_DENOMINATOR_PASS",
        "source_commit": manifest["commit"],
        "retained_source_files": len(expected),
        "binary_operator_tags": operators,
        "supported_operator_tags": ["ADD", "SUB"],
        "explicitly_refused_operator_tags": unsupported,
        "literal_constructors": literals,
        "supported_literal_constructors": ["L_Int", "L_BitVector", "L_Bool"],
        "scope": "Source custody and bounded classification; no ASLRef full-test, OCaml refinement or ISA authority claim",
    }


if __name__ == "__main__":
    print(json.dumps(check(Path(__file__).resolve().parent), indent=2))
