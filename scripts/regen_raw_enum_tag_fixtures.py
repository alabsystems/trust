#!/usr/bin/env python3
"""Re-decode raw two's-complement enum tags in checked-in `-Ztrust-dump=mir:` fixtures.

WHY THIS FILE EXISTS
--------------------
`VariantDef::discriminant` used to carry rustc's `Discr::val` verbatim — a `u128`
holding the tag's two's-complement BIT PATTERN at the discriminant type's width.
`#[repr(i8)] cmp::Ordering::Less = -1` therefore reached every consumer as `255`.
The extraction boundary now DECODES that value (`trust_mir_extract::ty_convert`),
so a freshly-dumped `Ordering` spells `Less` as `-1`, and the `_d in {tags}`
precondition derived from a `Discriminant` read spells the same tag `Int(-1)`
instead of `Int(255)`.

Fixtures harvested before that change still hold the raw spelling. They are not
wrong about the program — they are written in a convention no producer emits any
more, so consumers that read the decoded convention stop recognizing them.
Re-harvesting the corpora is not the fix: most are extractions of external crates
at a pinned compiler, and a fresh harvest would move thousands of unrelated bytes,
destroying their value as pinned regression inputs. Exactly two fields moved
(verified by a two-compiler dump differential over one source), and exactly those
two are rewritten here.

THE VALUES ARE THE COMPILER'S, NOT THIS SCRIPT'S
------------------------------------------------
Nothing below hardcodes a decoded tag. Every replacement value is read out of an
ORACLE dump produced by running the current `trustc` on the probe source embedded
in this file. What the script contributes is the decision of WHERE a value
applies, and that decision is gated:

  * an ADT's variants are rewritten only if their names match the oracle's in
    order AND each differing value is a raw two's-complement encoding of the
    oracle's decoded value at some integer width. A deliberately-mutated
    discriminant (`stdlib-leaf-num-2026-07-16/forgeries/G2`, `Less = 1`) is not a
    raw encoding of `-1` at any width, so it is left alone — which is the point
    of that fixture.
  * a `_d in {tags}` membership disjunction in `preconditions` is rewritten only
    if its tag list is positionally the RAW encoding of an oracle enum's tag list.
  * a file is rewritten only if its untouched content re-serializes byte-for-byte,
    so the diff can contain nothing but the tags.

`--check` rewrites nothing and exits 1 if anything would move, so the decode
convention can be gated rather than remembered.

Author: Andrew Yates <andrewyates.name@gmail.com>
Copyright 2026 Andrew Yates | License: Apache-2.0 OR MIT
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import platform
import re
import subprocess
import sys
import tempfile
from pathlib import Path

# Hand-built forgery enums that MIRROR an oracle enum's tag encoding rather than
# being extractor output of that enum. `forgeries/G3` is documented in
# `stdlib-leaf-num-2026-07-16/PROVENANCE.md` as "non-`Ordering` enum (right
# variants/discs, wrong name)": its job is to differ from `Ordering` in the NAME
# ONLY, so that its decline isolates the name check. Leaving it in the raw
# convention while `Ordering` moves would make it differ in the tags too, and it
# would then decline for two reasons instead of one.
MIRRORED_ENUMS = {"forgery::EvilSign": "cmp::Ordering"}

WIDTHS = (8, 16, 32, 64, 128)

# The probe the oracle is taken from. It must mention every enum whose tags this
# script may rewrite, and must `match` on one of them so the `_d in {tags}`
# membership precondition is emitted too.
ORACLE_PROBE = """#![crate_type = "lib"]
use std::cmp::Ordering;

pub fn tag(o: Ordering) -> i8 {
    o as i8
}

pub fn membership(o: Ordering) -> i32 {
    match o {
        Ordering::Less => -1,
        Ordering::Equal => 0,
        Ordering::Greater => 1,
    }
}
"""


def enum_suffix_key(name: str) -> str:
    """The harvest-independent identity of an enum type.

    One `cmp::Ordering` is spelled `cmp::Ordering`, `core::cmp::Ordering` and
    `std::cmp::Ordering` across the corpora, depending on how each harvest's
    compiler qualified paths. Keying on the last two segments joins all three
    while keeping `forgery::EvilSign` distinct.
    """
    parts = name.split("::")
    return "::".join(parts[-2:]) if len(parts) >= 2 else name


def find_trustc(repo_root: Path, explicit: str | None) -> Path:
    if explicit:
        return Path(explicit)
    env = os.environ.get("TRUSTC")
    if env:
        return Path(env)
    machine = platform.machine()
    arch = "aarch64" if machine in ("arm64", "aarch64") else machine
    candidates = [
        repo_root / "build" / "host" / "stage2" / "bin" / "trustc",
        repo_root / "build" / f"{arch}-apple-darwin" / "stage2" / "bin" / "trustc",
        repo_root / "build" / "host" / "stage1" / "bin" / "trustc",
    ]
    for candidate in candidates:
        if candidate.is_file():
            return candidate
    raise SystemExit(
        "no trustc found; set TRUSTC or pass --trustc. Tried:\n  "
        + "\n  ".join(str(c) for c in candidates)
    )


def walk_adts(node, on_adt) -> None:
    if isinstance(node, dict):
        adt = node.get("Adt")
        if isinstance(adt, dict) and isinstance(adt.get("variants"), list) and adt["variants"]:
            on_adt(adt)
        for value in node.values():
            walk_adts(value, on_adt)
    elif isinstance(node, list):
        for value in node:
            walk_adts(value, on_adt)


def membership_tags(node):
    """The tag list of a `_d in {tags}` disjunction, or None.

    Shape: `Or[Eq(v, Int(t0)), Eq(v, Int(t1)), ...]` over ONE `v` — what
    `trust_mir_extract::enum_discriminant_range_preconditions` builds for a
    `_d = Discriminant(src)` local.
    """
    if not isinstance(node, dict) or list(node.keys()) != ["Or"]:
        return None
    disjuncts = node["Or"]
    if not isinstance(disjuncts, list) or len(disjuncts) < 2:
        return None
    subjects, tags = set(), []
    for disjunct in disjuncts:
        if not isinstance(disjunct, dict) or list(disjunct.keys()) != ["Eq"]:
            return None
        operands = disjunct["Eq"]
        if not isinstance(operands, list) or len(operands) != 2:
            return None
        lhs, rhs = operands
        if not (isinstance(rhs, dict) and list(rhs.keys()) == ["Int"]):
            return None
        subjects.add(json.dumps(lhs, sort_keys=True))
        tags.append(rhs["Int"])
    return tags if len(subjects) == 1 else None


def is_raw_encoding(recorded: int, decoded: int) -> bool:
    """Is `recorded` the two's-complement bit pattern of `decoded` at some width?

    True exactly when they differ and some width `w` has
    `recorded == decoded mod 2**w` with `recorded` in `[0, 2**w)`. This is what
    separates a STALE tag from a deliberately mutated one.
    """
    if recorded == decoded or recorded < 0:
        return False
    return any(
        recorded < (1 << width) and (recorded - decoded) % (1 << width) == 0 for width in WIDTHS
    )


def raw_encodings(decoded: list[int]) -> list[list[int]]:
    """Every width's raw spelling of a decoded tag list, excluding the identity."""
    out: list[list[int]] = []
    for width in WIDTHS:
        raw = [d if d >= 0 else d + (1 << width) for d in decoded]
        if raw != decoded and raw not in out:
            out.append(raw)
    return out


def build_oracle(trustc: Path) -> dict[str, list[tuple[str, int]]]:
    """(enum key) -> [(variant name, DECODED discriminant)], from the compiler."""
    with tempfile.TemporaryDirectory() as tmp:
        tmp_path = Path(tmp)
        probe = tmp_path / "trust_tag_oracle.rs"
        probe.write_text(ORACLE_PROBE, encoding="utf-8")
        out = tmp_path / "dump"
        out.mkdir()
        subprocess.run(
            [
                str(trustc),
                "--edition",
                "2021",
                "--emit=metadata",
                f"-Ztrust-dump=mir:{out}",
                "-Ztrust-policy=advisory",
                "-o",
                str(tmp_path / "probe.meta"),
                str(probe),
            ],
            cwd=tmp_path,
            stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL,
            check=False,
        )
        dumps = sorted(out.glob("*.json"))
        if not dumps:
            raise SystemExit(f"oracle dump produced no bodies with {trustc}")
        oracle: dict[str, list[tuple[str, int]]] = {}

        def record(adt) -> None:
            key = enum_suffix_key(adt.get("name") or "")
            variants = [(v.get("name"), v.get("discriminant")) for v in adt["variants"]]
            if any(name is None or not isinstance(disc, int) for name, disc in variants):
                return
            previous = oracle.setdefault(key, variants)
            if previous != variants:
                raise SystemExit(f"oracle disagrees with itself about {key}")

        for dump in dumps:
            walk_adts(json.loads(dump.read_text(encoding="utf-8")), record)
    return oracle


def rewrite_body(body, oracle, changes: list, rel: str) -> None:
    """Apply both rewrites in place, appending `(rel, where, old, new)` rows."""

    def on_adt(adt) -> None:
        name = adt.get("name") or ""
        expected = oracle.get(enum_suffix_key(MIRRORED_ENUMS.get(name, name)))
        if expected is None:
            return
        recorded = [(v.get("name"), v.get("discriminant")) for v in adt["variants"]]
        if [n for n, _ in recorded] != [n for n, _ in expected]:
            return
        stale = [
            (i, r, d) for i, ((_, r), (_, d)) in enumerate(zip(recorded, expected)) if r != d
        ]
        if not stale or not all(is_raw_encoding(r, d) for _, r, d in stale):
            return
        for index, recorded_value, decoded_value in stale:
            adt["variants"][index]["discriminant"] = decoded_value
            changes.append(
                (
                    rel,
                    f"Adt({name}).variants[{index}:{recorded[index][0]}].discriminant",
                    recorded_value,
                    decoded_value,
                )
            )

    walk_adts(body, on_adt)

    # Keyed off the ORACLE, not off the ADTs present in this body: a body can
    # carry the derived membership fact while its `Discriminant` source local no
    # longer carries the enum's own `Ty::Adt`.
    tag_lists = [
        (raw, [d for _, d in variants])
        for variants in oracle.values()
        for raw in raw_encodings([d for _, d in variants])
    ]

    def rewrite(node, path: str) -> None:
        if isinstance(node, dict):
            tags = membership_tags(node)
            if tags is not None:
                for raw, decoded in tag_lists:
                    if tags == raw:
                        for i, value in enumerate(decoded):
                            node["Or"][i]["Eq"][1]["Int"] = value
                        changes.append((rel, f"{path} (tag membership)", raw, decoded))
                        return
            for name, value in node.items():
                rewrite(value, f"{path}/{name}")
        elif isinstance(node, list):
            for i, value in enumerate(node):
                rewrite(value, f"{path}[{i}]")

    if "preconditions" in body:
        rewrite(body["preconditions"], "preconditions")


def reseal_manifests(roots: list[Path], touched: set[str], check: bool) -> list[str]:
    """Re-hash `sha256sum`-format manifest rows that bind a rewritten fixture.

    Three corpora seal their bytes (`ARTIFACTS.sha256`, `MANIFEST.sha256`), and a
    manifest that still names the pre-decode bytes is a false claim about the
    tree — the one failure mode a hash manifest exists to make impossible. Only
    rows whose path resolves to a file this run rewrote are touched; every other
    byte of the manifest, including its separator, is preserved.
    """
    resealed: list[str] = []
    pending = set(touched)
    # A fixpoint, because one corpus seals its own manifest: `expr-fold-corpus`'s
    # `TOOLCHAIN.sha256` carries a `<hash> corpus_manifest MANIFEST.sha256` row
    # and `tests/expr_fold_corpus.rs` checks it, so resealing the manifest without
    # the row that binds it would trade one false claim for another.
    while pending:
        next_pending: set[str] = set()
        for root in roots:
            for manifest in sorted(root.rglob("*.sha256")):
                lines = manifest.read_text(encoding="utf-8").splitlines(keepends=True)
                changed = False
                for i, line in enumerate(lines):
                    match = re.match(r"^([0-9a-f]{64})(\s+)(.*?)(\r?\n?)$", line)
                    if not match:
                        continue
                    digest, sep, rest, eol = match.groups()
                    # `<hash><sep><path>` in a plain manifest; the sealed-manifest
                    # row is `<hash><sep><label><sep><name>`, so the last field is
                    # the candidate path there.
                    for rel in dict.fromkeys((rest, rest.split("\t")[-1])):
                        target = manifest.parent / rel
                        if str(target) not in pending:
                            continue
                        fresh = hashlib.sha256(target.read_bytes()).hexdigest()
                        if fresh == digest:
                            break
                        lines[i] = f"{fresh}{sep}{rest}{eol}"
                        changed = True
                        resealed.append(f"{manifest}\n    {rest}: {digest[:12]}… -> {fresh[:12]}…")
                        break
                if changed and not check:
                    manifest.write_text("".join(lines), encoding="utf-8")
                    next_pending.add(str(manifest))
        pending = next_pending
    return resealed


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument(
        "--check", action="store_true", help="report, rewrite nothing, exit 1 if stale"
    )
    parser.add_argument("--trustc", help="the trustc whose decode convention is authoritative")
    parser.add_argument("roots", nargs="*", help="fixture roots (default: trust-clean fixtures)")
    args = parser.parse_args()

    repo_root = Path(__file__).resolve().parent.parent
    roots = [Path(r) for r in args.roots] or [repo_root / "crates" / "trust-clean" / "fixtures"]
    oracle = build_oracle(find_trustc(repo_root, args.trustc))
    print("oracle:", json.dumps({k: v for k, v in sorted(oracle.items())}))

    changes: list[tuple[str, str, object, object]] = []
    touched: set[str] = set()
    unformattable: list[str] = []
    for root in roots:
        for path in sorted(root.rglob("*.json")):
            text = path.read_text(encoding="utf-8")
            try:
                body = json.loads(text)
            except json.JSONDecodeError:
                continue
            before = len(changes)
            rewrite_body(body, oracle, changes, str(path))
            if len(changes) == before:
                continue
            serialized = json.dumps(body, indent=2, ensure_ascii=False)
            # The whole-file re-serialization must reproduce this file's own
            # layout, or the diff would carry formatting churn the review cannot
            # separate from the tags. Refuse rather than reformat.
            probe = json.dumps(json.loads(text), indent=2, ensure_ascii=False)
            if text == probe:
                rendered = serialized
            elif text == probe + "\n":
                rendered = serialized + "\n"
            else:
                unformattable.append(str(path))
                del changes[before:]
                continue
            touched.add(str(path))
            if not args.check:
                path.write_text(rendered, encoding="utf-8")

    for rel, where, old, new in changes:
        print(f"{rel}\n    {where}: {old} -> {new}")
    resealed = reseal_manifests(roots, touched, args.check)
    for row in resealed:
        print(row)
    print(f"\n{len(changes)} field(s) in {len(touched)} file(s); {len(resealed)} manifest row(s)")
    if unformattable:
        print(
            "REFUSED (re-serialization would reformat unrelated bytes):\n  "
            + "\n  ".join(unformattable),
            file=sys.stderr,
        )
        return 2
    if args.check and changes:
        print("--check: fixtures still carry the raw tag convention", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
