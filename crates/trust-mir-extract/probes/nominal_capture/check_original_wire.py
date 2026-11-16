#!/usr/bin/env python3
"""Exact test-data custody only; no source semantics or nominal authority."""
import argparse
import hashlib
import json
from pathlib import Path

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("source", type=Path)
parser.add_argument("source_mutant", type=Path)
parser.add_argument("wire", type=Path)
parser.add_argument("mutant_wire", type=Path)
args = parser.parse_args()
for path, limit in [(args.source, 1048576), (args.source_mutant, 1048576),
                    (args.wire, 65536), (args.mutant_wire, 65536)]:
    if path.stat().st_size > limit:
        raise SystemExit("refused: input exceeds bounded test-data profile")
# A real source edit passed through the compiler, not a patched wire artifact.
original = args.source.read_bytes()
old = b"        ObligationKindShape::Precondition\n            | ObligationKindShape::Postcondition"
new = b"        ObligationKindShape::Postcondition"
if original.count(old) != 1 or args.source_mutant.read_bytes() != original.replace(old, new):
    raise SystemExit("refused: mutant is not the exact first-alternative source edit")
root = Path(__file__).resolve().parents[3]
lean = (root / "trust-source-contract/lean/LiveHelperEnumWire.lean").read_text()
for name, path in [("originalBytes", args.wire), ("mutantBytes", args.mutant_wire)]:
    literal = lean.split("def " + name + " : List Nat := ", 1)[1].splitlines()[0]
    if path.read_bytes() != bytes(json.loads(literal)):
        raise SystemExit("refused: producer bytes differ from checked literal: " + name)
if args.wire.read_bytes() == args.mutant_wire.read_bytes():
    raise SystemExit("refused: source mutant produced the same wire")
print("PASS exact original/source-mutant compiler wire equals both checked literals")
print("source SHA256 (data correlation only):", hashlib.sha256(original).hexdigest())
