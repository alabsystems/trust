#!/usr/bin/env python3
"""Self-test for `scripts/regen_raw_enum_tag_fixtures.py`.

The oracle half of that script needs a `trustc`; the REWRITE half — which decides
what a stored fixture's bytes become — does not, and it is the half that can
silently corrupt a corpus. Every case below drives `rewrite_body` directly with a
synthetic oracle, so the decisions are pinned without a compiler.

Author: Andrew Yates <andrewyates.name@gmail.com>
Copyright 2026 Andrew Yates | License: Apache-2.0 OR MIT
"""

from __future__ import annotations

import copy
import importlib.util
import json
import sys
from pathlib import Path

MODULE_PATH = Path(__file__).resolve().parent.parent / "regen_raw_enum_tag_fixtures.py"
spec = importlib.util.spec_from_file_location("regen_raw_enum_tag_fixtures", MODULE_PATH)
regen = importlib.util.module_from_spec(spec)
assert spec.loader is not None
spec.loader.exec_module(regen)

ORACLE = {"cmp::Ordering": [("Less", -1), ("Equal", 0), ("Greater", 1)]}

FAILURES: list[str] = []


def check(condition: bool, message: str) -> None:
    if not condition:
        FAILURES.append(message)


def ordering_adt(name: str, tags: tuple[int, int, int]) -> dict:
    return {
        "Adt": {
            "name": name,
            "fields": [["__tag", {"Int": {"width": 64, "signed": True}}]],
            "variants": [
                {"name": "Less", "discriminant": tags[0], "fields": []},
                {"name": "Equal", "discriminant": tags[1], "fields": []},
                {"name": "Greater", "discriminant": tags[2], "fields": []},
            ],
        }
    }


def membership(tags: list[int], var: str = "_3") -> dict:
    return {"Or": [{"Eq": [{"Var": [var, "Int"]}, {"Int": t}]} for t in tags]}


def body(locals_ty: list[dict], preconditions: list) -> dict:
    return {"body": {"locals": [{"index": i, "ty": t} for i, t in enumerate(locals_ty)]},
            "preconditions": preconditions}


def run(fixture: dict) -> tuple[dict, list]:
    subject = copy.deepcopy(fixture)
    changes: list = []
    regen.rewrite_body(subject, ORACLE, changes, "<test>")
    return subject, changes


# 1. The stale raw spelling is decoded, in BOTH fields, under every path
#    qualification the corpora use.
for spelling in ("cmp::Ordering", "core::cmp::Ordering", "std::cmp::Ordering"):
    stale = body([ordering_adt(spelling, (255, 0, 1))], [membership([255, 0, 1])])
    fixed, changes = run(stale)
    variants = fixed["body"]["locals"][0]["ty"]["Adt"]["variants"]
    check(
        [v["discriminant"] for v in variants] == [-1, 0, 1],
        f"{spelling}: variants not decoded",
    )
    check(
        [d["Eq"][1]["Int"] for d in fixed["preconditions"][0]["Or"]] == [-1, 0, 1],
        f"{spelling}: membership not decoded",
    )
    check(len(changes) == 2, f"{spelling}: expected 2 changes, got {len(changes)}")

# 2. IDEMPOTENCE — already-decoded input is not touched. A regeneration step that
#    rewrites on every run cannot be used as a `--check` gate.
fixed_once, _ = run(body([ordering_adt("cmp::Ordering", (255, 0, 1))], [membership([255, 0, 1])]))
fixed_twice, changes = run(fixed_once)
check(fixed_twice == fixed_once and not changes, "not idempotent on decoded input")

# 3. A DELIBERATELY MUTATED discriminant is left alone. `forgeries/G2` sets
#    `Less = 1`, which is not a raw encoding of `-1` at any width; rewriting it
#    would delete the mutation the fixture exists to test.
mutated = body([ordering_adt("cmp::Ordering", (1, 0, 2))], [])
after, changes = run(mutated)
check(after == mutated and not changes, "a mutated discriminant was rewritten")

# 4. A raw encoding at a WIDER width decodes too (a `repr(Rust)`/isize tag).
wide = body([ordering_adt("cmp::Ordering", (2**64 - 1, 0, 1))], [membership([2**64 - 1, 0, 1])])
after, changes = run(wide)
check(
    [v["discriminant"] for v in after["body"]["locals"][0]["ty"]["Adt"]["variants"]] == [-1, 0, 1]
    and [d["Eq"][1]["Int"] for d in after["preconditions"][0]["Or"]] == [-1, 0, 1],
    "an isize-width raw tag was not decoded",
)

# 5. An enum the oracle does not know is untouched unless it is a declared MIRROR.
unknown = body([ordering_adt("other::Sign", (255, 0, 1))], [])
after, changes = run(unknown)
check(after == unknown and not changes, "an unknown enum was rewritten")
check("forgery::EvilSign" in regen.MIRRORED_ENUMS, "the G3 mirror is no longer declared")
mirror = body([ordering_adt("forgery::EvilSign", (255, 0, 1))], [])
after, _ = run(mirror)
check(
    [v["discriminant"] for v in after["body"]["locals"][0]["ty"]["Adt"]["variants"]] == [-1, 0, 1],
    "the declared mirror enum was not decoded",
)

# 6. A variant-name mismatch declines the WHOLE adt — the tags are only
#    positionally meaningful if the variants line up.
renamed = body([ordering_adt("cmp::Ordering", (255, 0, 1))], [])
renamed["body"]["locals"][0]["ty"]["Adt"]["variants"][1]["name"] = "Same"
after, changes = run(renamed)
check(after == renamed and not changes, "an ADT with mismatched variant names was rewritten")

# 7. A `Le(x, 255)` TYPE-RANGE precondition is not a tag membership. There are
#    hundreds of these in the corpus (every `u8` parameter has one) and rewriting
#    one would state that a `u8` can be `-1`.
u8_range = body([], [{"And": [{"Ge": [{"Var": ["x", "Int"]}, {"Int": 0}]},
                             {"Le": [{"Var": ["x", "Int"]}, {"Int": 255}]}]}])
after, changes = run(u8_range)
check(after == u8_range and not changes, "a u8 type-range bound was rewritten as a tag")

# 8. A disjunction over TWO DIFFERENT variables is not a tag membership.
mixed = {"Or": [{"Eq": [{"Var": ["_3", "Int"]}, {"Int": 255}]},
                {"Eq": [{"Var": ["_4", "Int"]}, {"Int": 0}]},
                {"Eq": [{"Var": ["_3", "Int"]}, {"Int": 1}]}]}
check(regen.membership_tags(mixed) is None, "a two-subject disjunction read as a tag membership")

# 8b. Nor is a disjunction of equalities to NON-CONSTANTS. `Eq(_3, _9)` carries no
#     tag to compare, and reading one out of it is how a rewrite lands on a
#     formula that is not a tag set at all.
symbolic = {"Or": [{"Eq": [{"Var": ["_3", "Int"]}, {"Var": ["_9", "Int"]}]},
                   {"Eq": [{"Var": ["_3", "Int"]}, {"Int": 0}]}]}
check(regen.membership_tags(symbolic) is None, "a symbolic disjunct read as a tag")

# 9. `is_raw_encoding` itself: the gate that separates stale from mutated.
check(regen.is_raw_encoding(255, -1), "255 must be the i8 raw encoding of -1")
check(regen.is_raw_encoding(2**32 - 1, -1), "2^32-1 must be a raw encoding of -1")
check(not regen.is_raw_encoding(1, -1), "1 must not read as a raw encoding of -1")
check(not regen.is_raw_encoding(0, 0), "an unchanged value is not a raw encoding")
check(not regen.is_raw_encoding(256, -1), "256 exceeds every width whose pattern it could be")

if FAILURES:
    for failure in FAILURES:
        print(f"FAIL: {failure}", file=sys.stderr)
    sys.exit(1)
print("regen_raw_enum_tag_fixtures: all checks passed")
