#!/usr/bin/env python3
"""Trust (L1, artifact-lineage attestation): the CONSUMER-SIDE reconciliation gate.

The compiler mints one lineage digest per green body at the `mir_built` hook
(`trust_thir_lower::lineage::body_lineage_digest`, over the intact per-body
mini-module plus its callee ledger) and states it in two places that are
otherwise unrelated objects:

  * the flip event  -- `trust-ir-flip: compiled from trust-ir, did=..., lineage=sha256:...`
    (an `info!` line from `rustc_mir_transform::trust_ir_flip`), emitted for the
    body whose MIR the codegen path actually consumed;
  * the artifact    -- the `lineage` field of the matching row in
    `<crate>.coverage.json`, plus `func_id`, that row's index into the ASSEMBLED
    `module.functions` of `<crate>.trust-ir.bin` / `.txt`.

Equal digests make "which row of the artifact is the body the flip selected?" a
question with a mechanical answer. Nothing in the compiler ASKS that question,
though: `record_green`'s gates and `splice_ok`'s gates are different predicates,
so a body can flip (its machine code derived from trust-ir) while its row is
never spliced into the artifact -- and then the shipped code came from a
trust-ir body that is NOT IN the artifact at all. That is the gap this script
closes, from outside the compiler, over artifacts alone.

It is deliberately a CONSUMER-side check written against the published bytes:
the party that consumes the artifact must not have to trust the producer's log.
A passing result is diagnostic artifact-lineage evidence, not proof of G7
executable authority.

WHAT IT PROVES

  A. Set integrity      -- the publication manifest names exactly the required
                           binary module and canonical text for this crate;
                           both are present and hash to their declared digests
                           under the producer's domain, recomputed here from
                           first principles (`sha256-domain-v1`), not by
                           calling the producer's own code.
  B. Coverage           -- every flipped body's lineage digest appears in the
                           coverage rows, exactly once.
  C. Presence           -- that row is SPLICED (`func_id` is not null): the body
                           whose code shipped is actually in the artifact.
  D. Address fidelity   -- `func_id` addresses a function in the assembled
                           module whose DISPLAY PATH is that row's `def_path`
                           (with the `{const-init}`/`{static-init}` marker the
                           assembler appends for initializer bodies). Since
                           WS5.2 the function's NAME is its link-time symbol,
                           so the def path lives in `; #display-path: "..."`.

WHAT IT DOES NOT PROVE (do not quote it as more than it is)

  * The canonical-remapping certificate. Assembly sorts bodies, assigns fresh
    dense `FuncId`s, re-interns the type/enum/struct tables and rewrites
    callees. D pins the ADDRESS and the NAME of the assembled function; nothing
    here proves the assembled function still MEANS what the pre-assembly
    mini-module meant. That certificate must live in the compiler, because the
    pre-assembly object is never published.
  * Tamper evidence against an adversary who controls the producer. The
    publication manifest lives inside `coverage.json`, so a party that rewrites
    the artifact can rewrite its digest. This is a lineage record for a
    cooperating toolchain; A detects corruption, truncation, a stale/mixed
    generation, and a post-hoc edit of one file of the set -- not a forger.
  * Anything about the emitted machine code. The digests bind trust-ir to
    trust-ir; the MIR->codegen leg is the differential gate's business.

USAGE

    trustc -Ztrust-ir-lower=on -Ztrust-dump=ir:DUMPDIR --crate-name C ... 2>FLIP.log
    # (with RUSTC_LOG=rustc_mir_transform::trust_ir_flip=info)
    scripts/trust_ir_lineage_reconcile.py --dump DUMPDIR --flip-log FLIP.log

Exit status is 0 only when every check passes. Every failure mode is fatal:
this is a gate, not a report.

Author: Andrew Yates <andrewyates.name@gmail.com> | Copyright 2026 | License: Apache-2.0
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import struct
import sys
from dataclasses import dataclass, field
from pathlib import Path

# The producer's framing, restated here on purpose. Importing it would make the
# check circular; the whole point is an independent recomputation.
#   trust_ir::ProofDigest::sha256_domain(domain, bytes)
#     = SHA256( b"trust-ir.sha256-domain.v1\0"
#             || be64(len(domain)) || domain
#             || be64(len(bytes))  || bytes )
# (first-party/trust-ir/crates/trust-ir/src/proof/evidence.rs)
SHA256_DOMAIN_PREFIX = b"trust-ir.sha256-domain.v1\x00"

# `crate_module.rs::coverage_publication_manifest` emits this exact v1 shape;
# dump mode names the two data files from the coverage crate.
EXPECTED_PUBLICATION_SCHEMA = "trust.thir-lower.artifact-set.v1"
EXPECTED_DIGEST_ALGORITHM = "sha256-domain-v1"
EXPECTED_DIGEST_DOMAIN = "trust.thir-lower.artifact.v1"
PUBLICATION_KEYS = {
    "schema", "digest_algorithm", "digest_domain", "commit_marker", "artifacts"
}
ARTIFACT_KEYS = {"name", "bytes", "digest"}

# `rustc_mir_transform::trust_ir_flip`'s two `info!` lines. Both seams count:
# the codegen seam selects the body codegen consumes, the CTFE seam selects the
# body the const-eval interpreter consumes. A body that flipped on either seam
# had its shipped behaviour derived from trust-ir.
FLIP_LINE = re.compile(
    r"trust-ir-flip: (?:CTFE )?compiled from trust-ir, "
    r"did=(?P<did>[^,]+), asserts=\d+, lineage=(?P<lineage>sha256:[0-9a-f]{64})"
)

# One `rustcc fn @name(...)`/`fn @name(...)` header per function in
# `<crate>.trust-ir.txt`, in `module.functions` order -- which is exactly what
# `func_id` indexes (crate_module.rs: declarations are appended last so
# `module.functions[i].id == i` holds end to end).
TEXT_FN = re.compile(r"^(?:[a-z]+ )?fn @(?P<name>.+?)\(", re.MULTILINE)

# WS5.2: the canonical text carries a function's def path as a quoted (Rust
# `Debug`-escaped) `; #display-path:` directive right under its header.
TEXT_DISPLAY_PATH = re.compile(r'^\s*; #display-path: (?P<quoted>".*")\s*$', re.MULTILINE)

_RUST_ESCAPES = {"n": "\n", "r": "\r", "t": "\t", "0": "\0", "\\": "\\", '"': '"', "'": "'"}


def rust_debug_unquote(quoted: str) -> str | None:
    """Invert Rust's `{:?}` string escaping (the `#display-path` spelling), or None."""
    if len(quoted) < 2 or quoted[0] != '"' or quoted[-1] != '"':
        return None
    body, out, i = quoted[1:-1], [], 0
    while i < len(body):
        ch = body[i]
        if ch != "\\":
            out.append(ch)
            i += 1
            continue
        if i + 1 >= len(body):
            return None
        esc = body[i + 1]
        if esc == "u":
            close = body.find("}", i + 2)
            if body[i + 2 : i + 3] != "{" or close < 0:
                return None
            try:
                out.append(chr(int(body[i + 3 : close], 16)))
            except ValueError:
                return None
            i = close + 1
            continue
        if esc not in _RUST_ESCAPES:
            return None
        out.append(_RUST_ESCAPES[esc])
        i += 2
    return "".join(out)


def sha256_domain(domain: str, payload: bytes) -> str:
    digest = hashlib.sha256()
    digest.update(SHA256_DOMAIN_PREFIX)
    domain_bytes = domain.encode("utf-8")
    digest.update(struct.pack(">Q", len(domain_bytes)))
    digest.update(domain_bytes)
    digest.update(struct.pack(">Q", len(payload)))
    digest.update(payload)
    return "sha256:" + digest.hexdigest()


@dataclass
class Reconciliation:
    failures: list[str] = field(default_factory=list)
    notes: list[str] = field(default_factory=list)
    flipped: int = 0
    rows: int = 0
    artifacts: int = 0

    def fail(self, message: str) -> None:
        self.failures.append(message)

    def note(self, message: str) -> None:
        self.notes.append(message)


def check_publication(dump: Path, coverage: dict, out: Reconciliation) -> None:
    """A -- set integrity, recomputed from the bytes on disk."""
    publication = coverage.get("publication")
    if publication is None:
        out.fail(
            "coverage.json carries no `publication` block: the artifact set has no commit "
            "marker, so a consumer cannot tell a current generation from a stale or partial one"
        )
        return
    if not isinstance(publication, dict):
        out.fail("coverage.json `publication` block is not an object")
        return
    if set(publication) != PUBLICATION_KEYS:
        out.fail("publication block does not have the producer schema's exact fields")
    if publication.get("schema") != EXPECTED_PUBLICATION_SCHEMA:
        out.fail(
            f"publication schema is {publication.get('schema')!r}, expected "
            f"{EXPECTED_PUBLICATION_SCHEMA!r} -- refusing to guess at an unknown framing"
        )
        return
    if publication.get("digest_algorithm") != EXPECTED_DIGEST_ALGORITHM:
        out.fail(
            f"publication digest_algorithm is {publication.get('digest_algorithm')!r}, "
            f"expected {EXPECTED_DIGEST_ALGORITHM!r} -- this verifier implements only that one"
        )
        return
    if publication.get("commit_marker") is not True:
        out.fail("publication block is not a commit marker: the set is incomplete by its own claim")
        return
    domain = publication.get("digest_domain")
    if domain != EXPECTED_DIGEST_DOMAIN:
        out.fail(
            f"publication digest domain is {domain!r}, expected "
            f"{EXPECTED_DIGEST_DOMAIN!r} from the producer schema"
        )
        return

    artifacts = publication.get("artifacts")
    if not isinstance(artifacts, list):
        out.fail("publication artifacts is not a list")
        return

    crate = coverage["crate"]
    required = {f"{crate}.trust-ir.bin", f"{crate}.trust-ir.txt"}
    seen: set[str] = set()
    for artifact in artifacts:
        if not isinstance(artifact, dict):
            out.fail("publication artifact entry is not an object")
            continue
        if set(artifact) != ARTIFACT_KEYS:
            out.fail("publication artifact entry does not have the producer schema's exact fields")
        name = artifact.get("name")
        if not isinstance(name, str) or name not in required:
            out.fail(f"unexpected publication artifact {name!r}; expected only {sorted(required)}")
            continue
        if name in seen:
            out.fail(f"duplicate publication artifact {name!r}")
            continue
        seen.add(name)
        path = dump / name
        if path.is_symlink() or not path.is_file():
            out.fail(f"required artifact {name!r} is not a regular file in the dump directory")
            continue
        payload = path.read_bytes()
        declared_bytes = artifact.get("bytes")
        if type(declared_bytes) is not int or declared_bytes < 0:
            out.fail(f"artifact {name!r} has no valid byte count in the commit marker")
        elif declared_bytes != len(payload):
            out.fail(
                f"artifact {name!r} is {len(payload)} bytes on disk, "
                f"{declared_bytes} in the commit marker"
            )
        recomputed = sha256_domain(domain, payload)
        if recomputed != artifact.get("digest"):
            out.fail(
                f"artifact {name!r} DIGEST MISMATCH: commit marker says "
                f"{artifact.get('digest')}, the bytes on disk digest to {recomputed}"
            )
        out.artifacts += 1
    for name in sorted(required - seen):
        out.fail(f"required publication artifact {name!r} is missing from the commit marker")


def assembled_function_names(dump: Path, coverage: dict) -> list[str] | None:
    """`module.functions` order, read out of the canonical text artifact."""
    crate = coverage.get("crate")
    text = dump / f"{crate}.trust-ir.txt"
    if not text.is_file():
        return None
    return TEXT_FN.findall(text.read_text(encoding="utf-8", errors="replace"))


def assembled_display_paths(dump: Path, coverage: dict) -> list[str | None] | None:
    """Each function's `#display-path` (None when absent), in `module.functions` order."""
    crate = coverage.get("crate")
    text_path = dump / f"{crate}.trust-ir.txt"
    if not text_path.is_file():
        return None
    text = text_path.read_text(encoding="utf-8", errors="replace")
    headers = list(TEXT_FN.finditer(text))
    paths: list[str | None] = []
    for index, header in enumerate(headers):
        end = headers[index + 1].start() if index + 1 < len(headers) else len(text)
        found = TEXT_DISPLAY_PATH.search(text, header.end(), end)
        paths.append(rust_debug_unquote(found.group("quoted")) if found else None)
    return paths


def expected_assembled_name(row: dict) -> str:
    """The display path `assemble` gives a spliced body (crate_module.rs)."""
    kind = row.get("kind")
    if kind == "const-init":
        return f"{row['def_path']}::{{const-init}}"
    if kind == "static-init":
        return f"{row['def_path']}::{{static-init}}"
    return row["def_path"]


def reconcile(dump: Path, flip_log: Path | None) -> Reconciliation:
    out = Reconciliation()

    coverage_files = sorted(dump.glob("*.coverage.json"))
    if len(coverage_files) != 1:
        out.fail(
            f"expected exactly one *.coverage.json in {dump}, found {len(coverage_files)} -- "
            "a dump directory holds one artifact set"
        )
        return out
    coverage = json.loads(coverage_files[0].read_text(encoding="utf-8"))
    if not isinstance(coverage, dict):
        out.fail("coverage.json is not an object")
        return out
    crate = coverage.get("crate")
    if not isinstance(crate, str) or not crate or coverage_files[0].name != f"{crate}.coverage.json":
        out.fail("coverage crate does not match its <crate>.coverage.json commit marker path")
        return out

    check_publication(dump, coverage, out)

    rows = coverage.get("bodies") or []
    out.rows = len(rows)

    # A lineage digest must address at most ONE row. Two rows sharing one digest
    # would make "which row is the flipped body?" ambiguous again, which is the
    # exact question the digest exists to answer.
    by_lineage: dict[str, list[dict]] = {}
    for row in rows:
        lineage = row.get("lineage")
        if lineage:
            by_lineage.setdefault(lineage, []).append(row)
    for lineage, sharing in by_lineage.items():
        if len(sharing) > 1:
            paths = ", ".join(r.get("def_path", "?") for r in sharing)
            out.fail(
                f"lineage {lineage} is claimed by {len(sharing)} coverage rows ({paths}): the "
                "digest no longer names one object"
            )

    names = assembled_display_paths(dump, coverage)
    if names is None:
        out.fail(
            f"no {coverage.get('crate')}.trust-ir.txt in {dump}: `func_id` cannot be resolved "
            "to a function, so the address half of the attestation is uncheckable"
        )

    # D -- every SPLICED row's func_id addresses the function it claims. Checked
    # for all spliced rows, not only flipped ones: a row that mis-addresses is a
    # defect in the artifact whether or not that body's code shipped from
    # trust-ir today.
    if names is not None:
        for row in rows:
            func_id = row.get("func_id")
            if func_id is None:
                continue
            if not isinstance(func_id, int) or func_id < 0 or func_id >= len(names):
                out.fail(
                    f"row {row.get('def_path')!r} claims func_id {func_id}, which is outside "
                    f"the assembled module's {len(names)} functions"
                )
                continue
            expected = expected_assembled_name(row)
            if names[func_id] != expected:
                out.fail(
                    f"row {row.get('def_path')!r} claims func_id {func_id}, but the assembled "
                    f"module's function at that index has display path {names[func_id]!r}, "
                    f"not {expected!r}"
                )

    if flip_log is None:
        out.note(
            "no --flip-log given: set integrity (A) and address fidelity (D) were checked, "
            "coverage (B) and presence (C) were NOT -- nothing said which bodies shipped"
        )
        return out

    if not flip_log.is_file():
        out.fail(f"flip log {flip_log} does not exist")
        return out

    # B + C -- every body whose shipped code was derived from trust-ir must be
    # IN the artifact, and spliced.
    seen: set[tuple[str, str]] = set()
    for line in flip_log.read_text(encoding="utf-8", errors="replace").splitlines():
        match = FLIP_LINE.search(line)
        if match is None:
            continue
        key = (match.group("did"), match.group("lineage"))
        if key in seen:
            continue
        seen.add(key)
        out.flipped += 1
        lineage = match.group("lineage")
        sharing = by_lineage.get(lineage)
        if not sharing:
            out.fail(
                f"body {match.group('did')} FLIPPED with lineage {lineage}, but no coverage row "
                "carries that digest: its machine code was derived from a trust-ir body the "
                "artifact does not contain"
            )
            continue
        row = sharing[0]
        if row.get("func_id") is None:
            out.fail(
                f"body {match.group('did')} FLIPPED with lineage {lineage}, and its coverage row "
                f"({row.get('def_path')!r}) is NOT SPLICED: the shipped body is described by the "
                "artifact but absent from it"
            )

    if out.flipped == 0:
        out.note(
            "the flip log contains no `compiled from trust-ir` line: nothing shipped from "
            "trust-ir in this build, so B and C are vacuously satisfied"
        )

    return out


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Reconcile trust-ir flip events against the published artifact set."
    )
    parser.add_argument(
        "--dump", required=True, type=Path, help="the -Ztrust-dump=ir:<dir> directory"
    )
    parser.add_argument(
        "--flip-log",
        type=Path,
        default=None,
        help="stderr of the compile, with RUSTC_LOG=rustc_mir_transform::trust_ir_flip=info",
    )
    args = parser.parse_args()

    if not args.dump.is_dir():
        print(f"FAIL: dump directory {args.dump} does not exist", file=sys.stderr)
        return 2

    out = reconcile(args.dump, args.flip_log)

    for note in out.notes:
        print(f"note: {note}")
    if out.failures:
        for failure in out.failures:
            print(f"FAIL: {failure}", file=sys.stderr)
        print(
            f"\nlineage reconciliation FAILED: {len(out.failures)} finding(s) over "
            f"{out.artifacts} artifact(s), {out.rows} coverage row(s), {out.flipped} flipped body(ies)",
            file=sys.stderr,
        )
        return 1
    print(
        f"lineage reconciliation OK: {out.artifacts} artifact(s) hash as published, "
        f"{out.rows} coverage row(s), {out.flipped} flipped body(ies) each present, spliced, "
        "and correctly addressed in the assembled module"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
