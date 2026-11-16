#!/usr/bin/env python3
"""Reproduce and retain the complete MF-R5 marker-authority corpus.

This is the durable successor to the focused five-probe measurement in
``reports/mf-invariant-r5-resolution-2026-08-14.md``.  It deliberately accepts
no ambient evidence:

* the root checkout and every initialized recursive submodule must be clean;
* the 27 probe paths of the REVIEWED MF-R5 union — and their bytes — are
  ratcheted here.  That union is a deliberate SUBSET of
  ``crates/trust-thir-lower/probes/`` (45 files tracked there as of
  ``a3c7b63c1c``), because ``EXPECTED_BODY_COUNT`` below is derived from the
  reviewed union and from nothing else.  Probes added for unrelated waves are
  recorded in the receipt as ``tracked_but_unpinned`` and are not asserted on;
  a pinned probe that goes missing, or whose bytes move, still fails closed;
* the selected stage-1 ``trustc`` must identify the root HEAD exactly, and every
  entry in its complete stage1 tree is hashed before and after the sweep.  A dev
  stage-1 build names its sources rather than HEAD (bootstrap's
  ``src/bootstrap/src/utils/trust_source_identity.rs``); its build directory's
  ``trust-source-identity`` record must then digest to that name, have been taken
  at the root HEAD, and name no uncommitted change;
* every probe is freshly compiled at O0 and O3 into a nonexistent destination;
* every run must publish exactly one v2 coverage document, and the independent
  consumer-side lineage gate must validate set integrity, coverage, presence,
  and address fidelity against the compile's authenticated flip log;
* all 1,160 source-derived body classifications must be tuple-identical between
  O0 and O3 and match the reviewed per-body digest, with the reviewed bucket
  census and no admitted-and-wrong row.

Only after every check, including a final source/tool snapshot, passes is a JSON
receipt published read-only with an atomic same-directory link; the retained
evidence tree is sealed read-only and inventoried.  The printed receipt hash
is over canonical JSON with the ``receipt_sha256`` field omitted; this avoids an
impossible self-referential digest while binding every evidentiary field.

Run from anywhere inside the repository, for example:

    python3 scripts/mf_r5_full_union.py

The default evidence directory and receipt live under ignored ``reports/build``.
Both must be absent before the run; the gate never reuses or overwrites evidence.

Copyright 2026 Andrew Yates | License: Apache-2.0 OR MIT
"""

from __future__ import annotations

import argparse
import collections
import hashlib
import json
import os
import re
import secrets
import stat
import subprocess
import sys
from pathlib import Path
from typing import Any, Mapping, Sequence


SCHEMA = "trust.mf-r5.full-union-receipt.v2"
COVERAGE_SCHEMA = "trust.thir-lower.crate-module.coverage.v2"
PUBLICATION_SCHEMA = "trust.thir-lower.artifact-set.v1"
EXPECTED_BODY_COUNT = 1_160

# Source-derived six-case classifier.  The five-number review ratchet aggregates
# the two honest "other" cases; keeping them separate here prevents one from
# silently trading mass with the other.
BUCKETS = (
    "agreed_exact",
    "marker_free_refusal",
    "unsupported",
    "other_non_agreed",
    "marker_channel_other",
    "admitted_wrong",
)
EXPECTED_BUCKET_COUNTS = {
    "agreed_exact": 504,
    "marker_free_refusal": 302,
    "unsupported": 343,
    "other_non_agreed": 5,
    "marker_channel_other": 6,
    "admitted_wrong": 0,
}
REVIEW_RATCHET_ORDER = (
    "agreed_exact",
    "marker_free_refusal",
    "unsupported",
    "other_fail_closed",
    "admitted_wrong",
)
EXPECTED_REVIEW_RATCHET = (504, 302, 343, 11, 0)
EXPECTED_ROW_TUPLE_SHA256 = (
    "73c40c1bf30a3518d19f764613b20f5ea4c6ee1f306d2c37d1db3c08435adad5"
)

# These are the exact flags used by the reviewed release-shape sweep.  In
# particular, debug assertions must be stated at O0: trustc otherwise infers
# them on there but off at O3, changing the source program under measurement.
COMMON_COMPILE_OPTIONS = (
    "--edition=2021",
    "--crate-type=lib",
    "-Ztrust-ir-lower=on",
    "-Ztrust-verify=off",
    "-Cdebuginfo=0",
    "-Cdebug-assertions=off",
    "-Coverflow-checks=on",
)
OPT_LEVELS = (0, 3)

# A path+byte inventory, not merely a count.  Adding, deleting, renaming, or
# editing a probe requires an explicit review and ratchet update in this file.
#
# 2026-08-30: NINE probes re-pinned after 9fc06acc40 ("fmt: tree-wide reformat")
# edited them without the ratchet update this comment requires, leaving the gate
# red — mb_joinhead, mf_multiblock, mfr3_bind, mfr3_perm, mfr4_expr, mfr5_branch,
# mfr5_mixed, rmfz_adversarial, rmfz_adversarial2.
#
# REVIEWED, not rubber-stamped. Each drift was proved to be EXACTLY the
# formatter's output: the pre-commit blob was extracted with `git show 9fc06acc40^:`,
# reformatted with this repo's own rustfmt.toml, and compared byte-for-byte
# against the current file. All nine matched, so no probe carries a semantic
# change and the THIR/MIR each one lowers to is unchanged.
#
# The config path is load-bearing in that proof and cost a wrong answer first
# time: formatting the extracted blobs in a scratch directory made all nine
# report DIFFERS, because rustfmt walks UP from the file to find rustfmt.toml and
# a copy in /tmp has no repo above it. With `--config-path` naming this repo's
# config (style_edition 2024, use_small_heuristics = "Max" — which is what
# collapses these small bodies onto one line) all nine match. `git diff -w` is NOT
# a substitute: a formatter reflows tokens across lines, which whitespace-
# insensitive diffing does not neutralize, and -w reported the full line count
# for all nine.
EXPECTED_CORPUS_SHA256 = {
    "crates/trust-thir-lower/probes/mb_adversarial.rs":
        "bcf770689247f81c85b0ba4b1a3e7870b4d146fbbde47c91eea48c41d4b0d3fd",
    "crates/trust-thir-lower/probes/mb_hazard3.rs":
        "bad3f0b6b513d076bb55328cca9e974fa51a7f9b289aefcd86cdd2165809858f",
    "crates/trust-thir-lower/probes/mb_joinhead.rs":
        "0ffed887339c9c304370ce566f3a234128fcd3f65b52100a694701c57e812866",
    "crates/trust-thir-lower/probes/mf_aggregate_adversarial.rs":
        "3eb2cfc5da8c07720d29316cd261c7d21b3c13a2f5511d70caba9a34fae73001",
    "crates/trust-thir-lower/probes/mf_aggregate_temps.rs":
        "f8e8d128ac31d4ed2a3e0fb7ddb9d59fc159a80a768c6fba50d019d2ec8429de",
    "crates/trust-thir-lower/probes/mf_multiblock.rs":
        "ee92913a9bd20b1bfe23e1752523adcca2259974a4589fc6c95cf9b25797ca41",
    "crates/trust-thir-lower/probes/mf_operand_temps.rs":
        "e14d384370319d0c6ad2ff93717d139b50536e88fd7ba344e9f06b3736ce48ae",
    "crates/trust-thir-lower/probes/mf_residual.rs":
        "fab7d5f576a52a61f74066ea31286587ff94832b06a6d6ac16710ac36bb7e1f3",
    "crates/trust-thir-lower/probes/mfr3_bind.rs":
        "d94f63af94e51bf888a300eb741ca2fc432adc5ade39890fef150046a9482fe6",
    "crates/trust-thir-lower/probes/mfr3_perm.rs":
        "7c729dd569012d1370a65ebf6ce728b9b3b0c0710e072d2a28dbed73462510b2",
    "crates/trust-thir-lower/probes/mfr3_wclass.rs":
        "a4cd6ff655d003bf71a370eeae388e8465fab28e28ecaffbe9bfa7f1d4d11da5",
    "crates/trust-thir-lower/probes/mfr3_write.rs":
        "a28b42a6298e0c2034f0eecab3c8ca637cd4aebce90639224b304cf23ab20c8e",
    "crates/trust-thir-lower/probes/mfr4_expr.rs":
        "6aad6a667596320aa7419de0dc5473ea09cbecd8436acf15bc221962bde72e2b",
    "crates/trust-thir-lower/probes/mfr4_flow.rs":
        "d49430dcb4fb081dade92b1aa592cd4ebda4c26c07396ab950a2451262bb7272",
    "crates/trust-thir-lower/probes/mfr4_mix.rs":
        "4b86c7abb146b939ce587a8da8583a1d4ab72c732f2726429426ccc040525b14",
    "crates/trust-thir-lower/probes/mfr4_proj.rs":
        "6b9d21555dadd7aef127fd880515c286a11224a74517f7fe04048e880beb4b0b",
    "crates/trust-thir-lower/probes/mfr5_branch.rs":
        "49848827db847fa389b529ccd2f91f2757683b78d876c24bf254f9a5e1011654",
    "crates/trust-thir-lower/probes/mfr5_mixed.rs":
        "8652272a730de80acc9bc69b872ab40289ff3fbcfea790b39e22f3bc9a02c220",
    "crates/trust-thir-lower/probes/mfr5_pair.rs":
        "db401ed9369d15e4b36978b81c267859827f50dd9bcc739d33244f12a567c9c8",
    "crates/trust-thir-lower/probes/mfr5_plan.rs":
        "29ce45f769dd4cbe4403c2042d78f0346940d45f404edc2f3a08e9d5c76a76f4",
    "crates/trust-thir-lower/probes/mfr5_write.rs":
        "c3db1866e6977f0437f2e076aed16634367d607ff05cf1d90b1a142155ae29ad",
    "crates/trust-thir-lower/probes/mfz2_residual.rs":
        "3bf37d005d88b0bf113e1dd83076e0ec3a6c69fd391ec1d8b944fbc1d49ecb8c",
    "crates/trust-thir-lower/probes/mfz3_gate.rs":
        "66970d0975554d1faaaac2a5c201c655c421f67b2eef4c26188e683da0b76c87",
    "crates/trust-thir-lower/probes/rmfz_adversarial.rs":
        "4bc1e384b7f8203ad9410ad14682974086a16af0eed85fd6b70d7bcfb56c7ca0",
    "crates/trust-thir-lower/probes/rmfz_adversarial2.rs":
        "948e06eebfdab7878ef67159eb878ed64841a1f943614aa3719f1081952791e8",
    "crates/trust-thir-lower/probes/rmfz_borrow4.rs":
        "43b990e3c74013f561afa3a3fc791ac68af9cdb6a3b9e2772306841a0718276b",
    "crates/trust-thir-lower/probes/rmfz_write3.rs":
        "bec60c82f48e7aea470e76e844b4d04ef15cda1af78dac84c06824305950e1e6",
}

# Unique `(did, lineage)` events emitted by the reviewed compiler under the
# exact RUSTC_LOG channel below.  This makes B/C lineage evidence non-vacuous
# for every run and detects a silently disabled or truncated flip log.
EXPECTED_FLIP_COUNTS = {
    0: {
        "mb_adversarial.rs": 16,
        "mb_hazard3.rs": 3,
        "mb_joinhead.rs": 5,
        "mf_aggregate_adversarial.rs": 21,
        "mf_aggregate_temps.rs": 20,
        "mf_multiblock.rs": 12,
        "mf_operand_temps.rs": 15,
        "mf_residual.rs": 39,
        "mfr3_bind.rs": 33,
        "mfr3_perm.rs": 57,
        "mfr3_wclass.rs": 21,
        "mfr3_write.rs": 60,
        "mfr4_expr.rs": 45,
        "mfr4_flow.rs": 27,
        "mfr4_mix.rs": 24,
        "mfr4_proj.rs": 13,
        "mfr5_branch.rs": 20,
        "mfr5_mixed.rs": 13,
        "mfr5_pair.rs": 22,
        "mfr5_plan.rs": 35,
        "mfr5_write.rs": 18,
        "mfz2_residual.rs": 60,
        "mfz3_gate.rs": 35,
        "rmfz_adversarial.rs": 96,
        "rmfz_adversarial2.rs": 61,
        "rmfz_borrow4.rs": 3,
        "rmfz_write3.rs": 16,
    },
    3: {
        "mb_adversarial.rs": 8,
        "mb_hazard3.rs": 1,
        "mb_joinhead.rs": 2,
        "mf_aggregate_adversarial.rs": 13,
        "mf_aggregate_temps.rs": 14,
        "mf_multiblock.rs": 7,
        "mf_operand_temps.rs": 11,
        "mf_residual.rs": 24,
        "mfr3_bind.rs": 8,
        "mfr3_perm.rs": 41,
        "mfr3_wclass.rs": 3,
        "mfr3_write.rs": 44,
        "mfr4_expr.rs": 28,
        "mfr4_flow.rs": 9,
        "mfr4_mix.rs": 13,
        "mfr4_proj.rs": 9,
        "mfr5_branch.rs": 11,
        "mfr5_mixed.rs": 8,
        "mfr5_pair.rs": 16,
        "mfr5_plan.rs": 26,
        "mfr5_write.rs": 10,
        "mfz2_residual.rs": 40,
        "mfz3_gate.rs": 21,
        "rmfz_adversarial.rs": 71,
        "rmfz_adversarial2.rs": 28,
        "rmfz_borrow4.rs": 2,
        "rmfz_write3.rs": 14,
    },
}

EXACT_MARKERS = re.compile(r"^[0-9]+ marker line\(s\) identical$")
REFUSAL = re.compile(
    r"^markers differ: line 0: built `mk b[0-9]+\.[0-9]+:(?:live|dead) "
    r"s[0-9]+:[^`\n]+` vs derived `<end>`$"
)
COMMIT_HASH = re.compile(r"^[0-9a-f]{40}$")
FLIP_LINE = re.compile(
    r"trust-ir-flip: (?:CTFE )?compiled from trust-ir, "
    r"did=(?P<did>[^,\n]+), asserts=[0-9]+, "
    r"lineage=(?P<lineage>sha256:[0-9a-f]{64})(?:,|$)"
)
RUSTC_DRIVER_REFERENCE = re.compile(
    rb"(?:lib)?rustc_driver-[0-9a-f]+\.(?:dylib|so|dll)"
)
ALLOWED_STAGE1_SOURCE_LINKS = {
    "lib/rustlib/rustc-src/rust",
    "lib/rustlib/src/rust",
}


class GateError(RuntimeError):
    """A fail-closed evidence-gate refusal."""


def authority_environment() -> dict[str, str]:
    """Return the complete, non-inherited environment for identity commands."""

    return {
        "HOME": "/nonexistent",
        "TMPDIR": "/tmp",
        "PATH": "/usr/bin:/bin",
        "LC_ALL": "C",
        "LANG": "C",
        "TZ": "UTC",
        "GIT_CONFIG_GLOBAL": "/dev/null",
        "GIT_CONFIG_NOSYSTEM": "1",
        "GIT_OPTIONAL_LOCKS": "0",
        "GIT_TERMINAL_PROMPT": "0",
    }


def sha256_bytes(payload: bytes) -> str:
    return hashlib.sha256(payload).hexdigest()


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def canonical_json(payload: Any) -> bytes:
    return (
        json.dumps(payload, sort_keys=True, separators=(",", ":"), ensure_ascii=False)
        + "\n"
    ).encode("utf-8")


def _reject_duplicate_object(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    out: dict[str, Any] = {}
    for key, value in pairs:
        if key in out:
            raise GateError(f"JSON object repeats key {key!r}")
        out[key] = value
    return out


def load_json_strict(path: Path) -> dict[str, Any]:
    try:
        value = json.loads(
            path.read_text(encoding="utf-8"),
            object_pairs_hook=_reject_duplicate_object,
            parse_constant=lambda value: (_ for _ in ()).throw(
                GateError(f"JSON contains non-finite number {value}")
            ),
        )
    except (OSError, UnicodeError, json.JSONDecodeError) as error:
        raise GateError(f"cannot read strict JSON {path}: {error}") from error
    if not isinstance(value, dict):
        raise GateError(f"JSON root is not an object: {path}")
    return value


def run_capture(
    argv: Sequence[str],
    *,
    cwd: Path,
    env: Mapping[str, str] | None = None,
) -> subprocess.CompletedProcess[bytes]:
    try:
        return subprocess.run(
            list(argv),
            cwd=cwd,
            env=dict(authority_environment() if env is None else env),
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            check=False,
        )
    except OSError as error:
        raise GateError(f"could not execute {argv[0]!r}: {error}") from error


def git(root: Path, *args: str) -> str:
    result = run_capture(
        (
            "git",
            "-c",
            "core.fsmonitor=false",
            "-c",
            "core.untrackedCache=false",
            "-C",
            str(root),
            *args,
        ),
        cwd=root,
    )
    if result.returncode != 0:
        stderr = result.stderr.decode("utf-8", "replace").strip()
        raise GateError(f"git {' '.join(args)} failed: {stderr}")
    # Preserve the leading status byte from `git submodule status`.  A generic
    # `.strip()` would erase the first checkout's required clean-prefix space.
    return result.stdout.decode("utf-8", "strict").rstrip("\n")


def regular_file(path: Path, label: str, *, executable: bool = False) -> None:
    try:
        info = path.lstat()
    except OSError as error:
        raise GateError(f"{label} is unavailable at {path}: {error}") from error
    if stat.S_ISLNK(info.st_mode) or not stat.S_ISREG(info.st_mode):
        raise GateError(f"{label} must be one non-symlink regular file: {path}")
    if executable and not info.st_mode & 0o111:
        raise GateError(f"{label} is not executable: {path}")


def classify_body(body: Mapping[str, Any]) -> str:
    """Apply the review's source-derived total six-case marker rule.

    Anything outside the producer's v2 spellings is a schema error, not a new
    bucket guessed by this consumer.
    """

    differentials = body.get("differentials")
    if not isinstance(differentials, dict):
        raise GateError("coverage body has no object `differentials`")
    derived = differentials.get("derived_mir")
    if not isinstance(derived, dict):
        raise GateError("coverage body has no object `differentials.derived_mir`")
    verdict = derived.get("verdict")
    markers_exact = derived.get("markers_exact")
    detail = derived.get("markers_detail")
    if verdict not in {"agreed", "mismatch", "unsupported"}:
        raise GateError(f"unknown derived-MIR verdict {verdict!r}")
    if not isinstance(markers_exact, bool) or not isinstance(detail, str):
        raise GateError("derived-MIR marker fields have the wrong v2 types")

    if verdict == "unsupported":
        if markers_exact or detail:
            raise GateError("unsupported row unexpectedly carries marker-channel evidence")
        return "unsupported"
    if verdict != "agreed":
        if markers_exact or detail:
            raise GateError("non-agreed row unexpectedly carries marker-channel evidence")
        return "other_non_agreed"
    if markers_exact:
        if EXACT_MARKERS.fullmatch(detail) is None:
            raise GateError(f"exact marker row has unknown detail {detail!r}")
        return "agreed_exact"
    if REFUSAL.fullmatch(detail) is not None:
        return "marker_free_refusal"
    if detail.startswith("markers differ: "):
        return "admitted_wrong"
    if detail.startswith("marker channel(built): ") or detail.startswith(
        "marker channel(derived): "
    ):
        return "marker_channel_other"
    raise GateError(f"agreed non-exact row has unknown marker detail {detail!r}")


def flip_event_count(log: bytes) -> int:
    """Count unique authenticated flip events and reject near-match log grammar."""

    events: set[tuple[str, str]] = set()
    for line in log.decode("utf-8", "replace").splitlines():
        if "trust-ir-flip:" not in line or "compiled from trust-ir" not in line:
            continue
        match = FLIP_LINE.search(line)
        if match is None:
            raise GateError(f"malformed trust-ir flip event: {line!r}")
        events.add((match.group("did"), match.group("lineage")))
    return len(events)


def require_flip_count(probe: str, opt: int, actual: int) -> int:
    expected_names = {Path(path).name for path in EXPECTED_CORPUS_SHA256}
    if len(expected_names) != len(EXPECTED_CORPUS_SHA256):
        raise GateError("internal flip-count ratchet has colliding probe basenames")
    if set(EXPECTED_FLIP_COUNTS) != set(OPT_LEVELS):
        raise GateError("internal flip-count ratchet does not cover exactly O0/O3")
    for level, counts in EXPECTED_FLIP_COUNTS.items():
        if set(counts) != expected_names or any(value <= 0 for value in counts.values()):
            raise GateError(f"internal O{level} flip-count ratchet is incomplete or vacuous")
    name = Path(probe).name
    expected = EXPECTED_FLIP_COUNTS[opt][name]
    if actual != expected:
        raise GateError(
            f"O{opt} {probe} flip-event count drifted: {actual}, expected {expected}"
        )
    return expected


def validate_and_project(
    coverage: Mapping[str, Any], probe: str
) -> tuple[list[tuple[str, int, str, str, str]], collections.Counter[str]]:
    if coverage.get("schema") != COVERAGE_SCHEMA:
        raise GateError(
            f"{probe}: coverage schema {coverage.get('schema')!r}, expected {COVERAGE_SCHEMA!r}"
        )
    bodies = coverage.get("bodies")
    totals = coverage.get("totals")
    if not isinstance(bodies, list) or not isinstance(totals, dict):
        raise GateError(f"{probe}: v2 coverage lacks bodies/totals objects")
    if totals.get("bodies") != len(bodies):
        raise GateError(
            f"{probe}: totals.bodies={totals.get('bodies')!r}, parsed {len(bodies)} rows"
        )

    rows: list[tuple[str, int, str, str, str]] = []
    counts: collections.Counter[str] = collections.Counter()
    identities: set[tuple[int, str, str]] = set()
    for body in bodies:
        if not isinstance(body, dict):
            raise GateError(f"{probe}: coverage body is not an object")
        def_index = body.get("def_index")
        kind = body.get("kind")
        def_path = body.get("def_path")
        if not isinstance(def_index, int) or isinstance(def_index, bool) or def_index < 0:
            raise GateError(f"{probe}: invalid def_index {def_index!r}")
        if kind not in {"fn", "const-init", "static-init"}:
            raise GateError(f"{probe}: invalid body kind {kind!r}")
        if not isinstance(def_path, str) or not def_path or "\n" in def_path:
            raise GateError(f"{probe}: invalid def_path {def_path!r}")
        identity = (def_index, kind, def_path)
        if identity in identities:
            raise GateError(f"{probe}: duplicate body identity {identity!r}")
        identities.add(identity)
        bucket = classify_body(body)
        rows.append((probe, def_index, kind, def_path, bucket))
        counts[bucket] += 1
    rows.sort()
    return rows, counts


def review_ratchet(counts: Mapping[str, int]) -> tuple[int, int, int, int, int]:
    return (
        counts.get("agreed_exact", 0),
        counts.get("marker_free_refusal", 0),
        counts.get("unsupported", 0),
        counts.get("other_non_agreed", 0) + counts.get("marker_channel_other", 0),
        counts.get("admitted_wrong", 0),
    )


def require_opt_parity(
    rows_by_opt: Mapping[int, Sequence[tuple[str, int, str, str, str]]]
) -> None:
    if set(rows_by_opt) != set(OPT_LEVELS):
        raise GateError(f"row sets do not cover exactly O0/O3: {sorted(rows_by_opt)}")
    control = list(rows_by_opt[0])
    subject = list(rows_by_opt[3])
    if control == subject:
        return
    control_set = set(control)
    subject_set = set(subject)
    lost = sorted(control_set - subject_set)[:5]
    gained = sorted(subject_set - control_set)[:5]
    raise GateError(f"O0/O3 row-tuple parity failed; O0-only={lost!r}, O3-only={gained!r}")


def row_tuple_digest(rows: Sequence[tuple[str, int, str, str, str]]) -> str:
    return sha256_bytes(canonical_json([list(row) for row in rows]))


def require_row_tuple_ratchet(
    rows_by_opt: Mapping[int, Sequence[tuple[str, int, str, str, str]]]
) -> dict[int, str]:
    """Bind both optimization levels to the reviewed per-body baseline."""

    if set(rows_by_opt) != set(OPT_LEVELS):
        raise GateError(f"row sets do not cover exactly O0/O3: {sorted(rows_by_opt)}")
    digests = {opt: row_tuple_digest(rows_by_opt[opt]) for opt in OPT_LEVELS}
    for opt, digest in digests.items():
        if digest != EXPECTED_ROW_TUPLE_SHA256:
            raise GateError(
                f"O{opt} row-tuple digest drifted: {digest}, "
                f"expected {EXPECTED_ROW_TUPLE_SHA256}"
            )
    return digests


def _lexists(path: Path) -> bool:
    return os.path.lexists(path)


def require_fresh_destinations(output: Path, receipt: Path) -> None:
    if output == receipt or output in receipt.parents or receipt in output.parents:
        raise GateError("output and receipt paths must be separate and non-nested")
    if _lexists(output):
        raise GateError(f"output destination already exists: {output}")
    if _lexists(receipt):
        raise GateError(f"receipt destination already exists: {receipt}")


def atomic_write_new(path: Path, payload: bytes) -> None:
    """Atomically create a receipt, refusing every preexisting destination."""

    path.parent.mkdir(parents=True, exist_ok=True)
    if _lexists(path):
        raise GateError(f"receipt destination already exists: {path}")
    temporary = path.parent / f".{path.name}.{secrets.token_hex(16)}.tmp"
    descriptor: int | None = None
    try:
        descriptor = os.open(temporary, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600)
        with os.fdopen(descriptor, "wb") as stream:
            descriptor = None
            os.fchmod(stream.fileno(), 0o444)
            stream.write(payload)
            stream.flush()
            os.fsync(stream.fileno())
        # Linking a fully written same-directory temporary into its final name
        # is atomic and, unlike `os.replace`, cannot overwrite a destination
        # that races into existence after the initial absence check.
        try:
            os.link(temporary, path, follow_symlinks=False)
        except FileExistsError as error:
            raise GateError(f"receipt destination appeared during run: {path}") from error
        temporary.unlink()
        directory = os.open(path.parent, os.O_RDONLY)
        try:
            os.fsync(directory)
        finally:
            os.close(directory)
    finally:
        if descriptor is not None:
            os.close(descriptor)
        try:
            temporary.unlink()
        except FileNotFoundError:
            pass


def seal_evidence_tree(root: Path) -> None:
    """Make retained evidence read-only and reject links or special entries."""

    paths: list[Path] = []
    for current, directories, files in os.walk(root, topdown=True, followlinks=False):
        directories.sort()
        files.sort()
        base = Path(current)
        paths.extend(base / name for name in directories)
        paths.extend(base / name for name in files)
    for path in paths:
        info = path.lstat()
        if stat.S_ISLNK(info.st_mode) or not (
            stat.S_ISREG(info.st_mode) or stat.S_ISDIR(info.st_mode)
        ):
            raise GateError(f"retained evidence contains a link or special entry: {path}")
    for path in paths:
        if path.is_file():
            path.chmod(0o444)
    for path in sorted(
        (path for path in paths if path.is_dir()),
        key=lambda value: len(value.parts),
        reverse=True,
    ):
        path.chmod(0o555)
    root.chmod(0o555)


def retained_tree_inventory(root: Path) -> list[dict[str, Any]]:
    """Inventory the sealed evidence tree after its read-only policy is applied."""

    root_info = root.lstat()
    if not stat.S_ISDIR(root_info.st_mode) or stat.S_IMODE(root_info.st_mode) & 0o222:
        raise GateError(f"retained evidence root is not a sealed directory: {root}")
    entries: list[dict[str, Any]] = [
        {"path": ".", "kind": "directory", "mode": _mode(root_info)}
    ]
    paths: list[Path] = []
    for current, directories, files in os.walk(root, topdown=True, followlinks=False):
        directories.sort()
        files.sort()
        base = Path(current)
        paths.extend(base / name for name in directories)
        paths.extend(base / name for name in files)
    for path in sorted(paths, key=lambda value: str(value.relative_to(root))):
        relative = str(path.relative_to(root))
        info = path.lstat()
        if stat.S_ISREG(info.st_mode):
            if stat.S_IMODE(info.st_mode) & 0o222:
                raise GateError(f"retained evidence file is writable after sealing: {path}")
            entries.append(_stable_file_record(path, relative))
        elif stat.S_ISDIR(info.st_mode):
            if stat.S_IMODE(info.st_mode) & 0o222:
                raise GateError(f"retained evidence directory is writable after sealing: {path}")
            entries.append({"path": relative, "kind": "directory", "mode": _mode(info)})
        else:
            raise GateError(f"retained evidence changed type after sealing: {path}")
    return entries


def parse_gitlinks(root: Path) -> dict[str, str]:
    links: dict[str, str] = {}
    for line in git(root, "ls-files", "--stage").splitlines():
        left, separator, path = line.partition("\t")
        fields = left.split()
        if not separator or len(fields) != 3:
            raise GateError(f"cannot parse git index row {line!r}")
        mode, object_id, _stage = fields
        if mode == "160000":
            links[path] = object_id
    return dict(sorted(links.items()))


def repository_identity(root: Path) -> dict[str, Any]:
    head = git(root, "rev-parse", "HEAD")
    tree = git(root, "rev-parse", "HEAD^{tree}")
    if COMMIT_HASH.fullmatch(head) is None or COMMIT_HASH.fullmatch(tree) is None:
        raise GateError("Git returned a non-SHA1 HEAD/tree identity")
    if git(root, "status", "--porcelain=v1", "--untracked-files=all"):
        raise GateError("root Git checkout is dirty")

    status = git(root, "submodule", "status", "--recursive")
    submodules: list[dict[str, str]] = []
    for line in status.splitlines():
        match = re.fullmatch(r"(?P<prefix>.)(?P<sha>[0-9a-f]{40}) (?P<path>.+?)(?: \(.+\))?", line)
        if match is None:
            raise GateError(f"cannot parse recursive submodule status {line!r}")
        if match.group("prefix") != " ":
            raise GateError(f"recursive submodule is absent, conflicted, or off-pin: {line}")
        relative = match.group("path")
        checkout = root / relative
        if git(checkout, "status", "--porcelain=v1", "--untracked-files=all"):
            raise GateError(f"recursive submodule checkout is dirty: {relative}")
        actual = git(checkout, "rev-parse", "HEAD")
        if actual != match.group("sha"):
            raise GateError(f"recursive submodule HEAD changed while inspected: {relative}")
        submodules.append({"path": relative, "commit": actual})
    return {
        "head": head,
        "tree": tree,
        "gitlinks": parse_gitlinks(root),
        "recursive_submodules": sorted(submodules, key=lambda row: row["path"]),
    }


def corpus_inventory(root: Path) -> list[dict[str, Any]]:
    """Ratchet the REVIEWED MF-R5 probe union — a deliberate SUBSET of the probes directory.

    Scope, stated because this function previously conflated two different sets.
    ``EXPECTED_CORPUS_SHA256`` is the union the MF-R5 review actually covered
    (``reports/mf-invariant-r5-resolution-2026-08-14.md``), and
    ``EXPECTED_BODY_COUNT`` is derived from exactly that union — the two must
    describe the SAME set or the body ratchet asserts a number nothing measured.

    It is therefore NOT "every probe in the directory". That equality held
    incidentally in 2026-08 and has not held since: probes are added there for
    unrelated waves (wave-EP's ``ep_review_corpus_*``, the ``mfr6``/``mfr7``/
    ``mfr8`` rounds, ``sw_order_corpus``, …), none of which the MF-R5 review
    measured and none of which contributes to the 1,160-body figure. Requiring
    set EQUALITY made an unrelated probe redden this gate, which is a false red,
    not a caught regression.

    What is still fail-closed, because these are the directions that mean
    something: a pinned probe that is no longer tracked (deleted or renamed), and
    a pinned probe whose BYTES moved. Both raise. The count of tracked-but-
    unpinned probes is recorded in the receipt rather than asserted, so growth of
    the directory stays VISIBLE without being fatal.
    """
    tracked = git(root, "ls-files", "--", "crates/trust-thir-lower/probes/*.rs").splitlines()
    tracked = sorted(path for path in tracked if path)
    expected = sorted(EXPECTED_CORPUS_SHA256)
    missing = sorted(set(expected) - set(tracked))
    if missing:
        raise GateError(f"reviewed MF-R5 probe corpus lost tracked files: missing={missing!r}")
    inventory: list[dict[str, Any]] = []
    for relative in expected:
        path = root / relative
        regular_file(path, f"probe {relative}")
        digest = sha256_file(path)
        if digest != EXPECTED_CORPUS_SHA256[relative]:
            raise GateError(
                f"probe corpus bytes drifted for {relative}: {digest}, "
                f"expected {EXPECTED_CORPUS_SHA256[relative]}"
            )
        inventory.append({"path": relative, "bytes": path.stat().st_size, "sha256": digest})
    # Stated against the pin table itself, never against a literal: a literal here
    # can only ever restate the size of the constant beside it, and drifts the
    # moment the table is re-pinned (it read `!= 27` while the table said 27 and
    # the directory said 45 — three numbers, one of them load-bearing).
    if len(inventory) != len(EXPECTED_CORPUS_SHA256):
        raise GateError(
            f"internal corpus ratchet is not {len(EXPECTED_CORPUS_SHA256)} files: {len(inventory)}"
        )
    return inventory


def unpinned_probes(root: Path) -> list[str]:
    """Probe files tracked under the probes directory that the reviewed union does not pin.

    Reported in the receipt, never asserted — see `corpus_inventory` for why.
    """
    tracked = git(root, "ls-files", "--", "crates/trust-thir-lower/probes/*.rs").splitlines()
    return sorted(path for path in tracked if path and path not in EXPECTED_CORPUS_SHA256)


def select_trustc(root: Path, supplied: str | None) -> Path:
    root = root.resolve(strict=True)
    if supplied is not None:
        selected = Path(supplied).expanduser()
        if not selected.is_absolute():
            selected = root / selected
        regular_file(selected, "stage1 trustc", executable=True)
        try:
            path = selected.resolve(strict=True)
        except OSError as error:
            raise GateError(f"cannot resolve stage1 trustc {selected}: {error}") from error
    else:
        candidates = sorted(root.glob("build/*/stage1/bin/trustc"))
        resolved_candidates: dict[Path, list[Path]] = {}
        for candidate in candidates:
            if not candidate.is_file():
                continue
            try:
                canonical = candidate.resolve(strict=True)
            except OSError as error:
                raise GateError(
                    f"cannot resolve default stage1 trustc {candidate}: {error}"
                ) from error
            resolved_candidates.setdefault(canonical, []).append(candidate)
        if len(resolved_candidates) != 1:
            raise GateError(
                "default stage1 trustc selection is ambiguous; pass --trustc explicitly: "
                + ", ".join(str(path) for path in sorted(resolved_candidates))
            )
        path = next(iter(resolved_candidates))
    regular_file(path, "stage1 trustc", executable=True)
    try:
        path.relative_to(root)
    except ValueError as error:
        raise GateError(f"stage1 trustc must be repository-local: {path}") from error
    if path.parent.name != "bin" or path.parent.parent.name != "stage1":
        raise GateError(f"selected compiler is not a stage1/bin/trustc: {path}")
    return path


def _mode(info: os.stat_result) -> str:
    return f"{stat.S_IMODE(info.st_mode):04o}"


def _stable_file_record(path: Path, relative: str) -> dict[str, Any]:
    """Hash one regular file and reject a mutation during the read."""

    before = path.lstat()
    if not stat.S_ISREG(before.st_mode):
        raise GateError(f"entry changed type before hashing: {path}")
    digest = sha256_file(path)
    after = path.lstat()
    before_identity = (
        before.st_dev,
        before.st_ino,
        before.st_mode,
        before.st_size,
        before.st_mtime_ns,
        before.st_ctime_ns,
    )
    after_identity = (
        after.st_dev,
        after.st_ino,
        after.st_mode,
        after.st_size,
        after.st_mtime_ns,
        after.st_ctime_ns,
    )
    if before_identity != after_identity:
        raise GateError(f"file changed while hashing: {path}")
    return {
        "path": relative,
        "kind": "file",
        "mode": _mode(after),
        "bytes": after.st_size,
        "sha256": digest,
    }


def stage1_inventory(root: Path, trustc: Path) -> dict[str, Any]:
    """Bind every byte and link in the selected compiler's complete stage1 tree."""

    root = root.resolve(strict=True)
    trustc = trustc.resolve(strict=True)
    stage1 = trustc.parent.parent.resolve(strict=True)
    try:
        stage1_relative = str(stage1.relative_to(root))
    except ValueError as error:
        raise GateError(f"stage1 tree is outside the repository: {stage1}") from error

    paths: list[Path] = []
    for current, directories, files in os.walk(stage1, topdown=True, followlinks=False):
        directories.sort()
        files.sort()
        base = Path(current)
        paths.extend(base / name for name in directories)
        paths.extend(base / name for name in files)
    paths.sort(key=lambda path: str(path.relative_to(stage1)))

    entries: list[dict[str, Any]] = []
    driver_files: list[Path] = []
    for path in paths:
        relative_stage1 = str(path.relative_to(stage1))
        relative_root = str(path.relative_to(root))
        info = path.lstat()
        if stat.S_ISLNK(info.st_mode):
            target = os.readlink(path)
            try:
                resolved = path.resolve(strict=True)
                resolved_relative = str(resolved.relative_to(root))
            except (OSError, ValueError) as error:
                raise GateError(
                    f"stage1 symlink must resolve inside the repository: {path} -> {target}"
                ) from error
            if relative_stage1 not in ALLOWED_STAGE1_SOURCE_LINKS or resolved != root:
                raise GateError(
                    "stage1 symlink is not a recognized source link resolving to the "
                    f"repository root: {path} -> {target}"
                )
            entries.append(
                {
                    "path": relative_root,
                    "kind": "symlink",
                    "mode": _mode(info),
                    "target": target,
                    "resolved_repository_path": resolved_relative or ".",
                }
            )
        elif stat.S_ISDIR(info.st_mode):
            entries.append({"path": relative_root, "kind": "directory", "mode": _mode(info)})
        elif stat.S_ISREG(info.st_mode):
            entries.append(_stable_file_record(path, relative_root))
            if RUSTC_DRIVER_REFERENCE.fullmatch(path.name.encode("utf-8")):
                driver_files.append(path)
        else:
            raise GateError(f"stage1 contains a special filesystem entry: {path}")

    try:
        launcher = trustc.read_bytes()
    except OSError as error:
        raise GateError(f"cannot read stage1 trustc launcher {trustc}: {error}") from error
    references = sorted(set(RUSTC_DRIVER_REFERENCE.findall(launcher)))
    if len(references) != 1:
        raise GateError(
            "stage1 trustc must name exactly one rustc_driver runtime, found "
            f"{[value.decode('ascii', 'replace') for value in references]!r}"
        )
    driver_name = references[0].decode("ascii")
    if len(driver_files) != 1 or driver_files[0].name != driver_name:
        raise GateError(
            "stage1 must contain exactly the rustc_driver named by trustc; "
            f"launcher={driver_name!r}, "
            f"files={[str(path.relative_to(stage1)) for path in driver_files]!r}"
        )

    inventory_digest = sha256_bytes(canonical_json(entries))
    return {
        "root": stage1_relative,
        "entry_count": len(entries),
        "entries": entries,
        "inventory_sha256": inventory_digest,
        "launcher_path": str(trustc.relative_to(root)),
        "driver_path": str(driver_files[0].relative_to(root)),
    }


def trustc_identity(root: Path, trustc: Path, expected_head: str) -> dict[str, Any]:
    result = run_capture((str(trustc), "-Vv"), cwd=root)
    if result.returncode != 0 or result.stderr:
        raise GateError(
            f"stage1 trustc -Vv failed or wrote stderr: rc={result.returncode}, "
            f"stderr={result.stderr.decode('utf-8', 'replace')!r}"
        )
    verbose = result.stdout.decode("utf-8", "strict")
    fields: dict[str, str] = {}
    for line in verbose.splitlines():
        key, separator, value = line.partition(": ")
        if separator:
            if key in fields:
                raise GateError(f"trustc -Vv repeats identity field {key!r}")
            fields[key] = value
    if fields.get("binary") != "trustc":
        raise GateError("stage1 compiler does not identify as canonical binary `trustc`")
    commit = fields.get("commit-hash", "")
    if COMMIT_HASH.fullmatch(commit) is None:
        raise GateError(f"stage1 trustc commit {commit!r} is not a 40-hex identity")
    sources = None if commit == expected_head else source_identity(trustc, commit, expected_head)
    return {
        "path": str(trustc.relative_to(root)),
        "sha256": sha256_file(trustc),
        "bytes": trustc.stat().st_size,
        "stage1": stage1_inventory(root, trustc),
        "verbose": verbose,
        "verbose_sha256": sha256_bytes(result.stdout),
        "commit_hash": commit,
        "source_identity": sources,
    }


# v2 (EW-9) digests the configuration with the checkout root written as a token; a
# build directory last built before it still holds a v1 record of the same shape.
SOURCE_IDENTITY_SCHEMAS = (
    b"trust-dev-source-identity/v1\n",
    b"trust-dev-source-identity/v2\n",
)


def source_identity(trustc: Path, commit: str, expected_head: str) -> dict[str, Any]:
    """Bind a dev stage-1 ``trustc``'s source identity to the root HEAD.

    The build directory (``<out>/<host>/stage1/bin/trustc``) holds the record that
    bootstrap digested into ``commit-hash``: ``head``, ``identity`` and ``date``
    lines, then the record itself.
    """
    record_file = trustc.parents[3] / "trust-source-identity"
    try:
        data = record_file.read_bytes()
    except OSError as error:
        raise GateError(
            f"stage1 trustc commit {commit} is not root HEAD {expected_head}, and its build "
            f"directory holds no source-identity record ({record_file}): {error}"
        ) from error
    parts = data.split(b"\n", 3)
    if len(parts) != 4 or not parts[3].startswith(SOURCE_IDENTITY_SCHEMAS):
        raise GateError(f"{record_file} is not a source-identity record")
    head, identity, _date, record = parts
    if identity != f"identity {commit}".encode() or sha256_bytes(record)[:40] != commit:
        raise GateError(
            f"{record_file} names another build than stage1 trustc {commit}; "
            "rebuild stage 1"
        )
    if head != f"head {expected_head}".encode():
        raise GateError(
            f"stage1 trustc's sources were named at {head[5:].decode(errors='replace')}, "
            f"not root HEAD {expected_head}; `x.py build --stage 1` names them again "
            "(it rebuilds nothing when the commits since changed only docs/, reports/, "
            "scripts/, tests/ or top-level Markdown)"
        )
    # A departure from HEAD is a `path`, `submodule` or `repo` line (an edit, a
    # submodule's own commit or edit, an untracked repository).
    departures = (b"path ", b"submodule ", b"repo ")
    if any(line.startswith(departures) for line in record.split(b"\n")):
        raise GateError("stage1 trustc was built from a worktree with uncommitted changes")
    return {"record": str(record_file), "record_sha256": sha256_bytes(data)}


def clean_environment(home: Path, temporary: Path) -> dict[str, str]:
    home.mkdir(parents=True, exist_ok=False)
    temporary.mkdir(parents=True, exist_ok=False)
    return {
        "HOME": str(home),
        "TMPDIR": str(temporary),
        "PATH": "/usr/bin:/bin",
        "LC_ALL": "C",
        "LANG": "C",
        "TZ": "UTC",
        "GIT_CONFIG_GLOBAL": "/dev/null",
        "GIT_CONFIG_NOSYSTEM": "1",
        "GIT_OPTIONAL_LOCKS": "0",
        "GIT_TERMINAL_PROMPT": "0",
        "RUSTC_LOG": "rustc_mir_transform::trust_ir_flip=info",
    }


def safe_publication_artifacts(dump: Path, coverage: Mapping[str, Any]) -> list[dict[str, Any]]:
    publication = coverage.get("publication")
    if not isinstance(publication, dict) or publication.get("schema") != PUBLICATION_SCHEMA:
        raise GateError("coverage has no recognized publication commit marker")
    artifacts = publication.get("artifacts")
    if not isinstance(artifacts, list) or not artifacts:
        raise GateError("publication commit marker names no artifacts")
    out: list[dict[str, Any]] = []
    names: set[str] = set()
    for artifact in artifacts:
        if not isinstance(artifact, dict):
            raise GateError("publication artifact entry is not an object")
        name = artifact.get("name")
        if not isinstance(name, str) or not name or Path(name).name != name or name in names:
            raise GateError(f"unsafe or duplicate publication artifact name {name!r}")
        names.add(name)
        path = dump / name
        regular_file(path, f"published artifact {name}")
        if artifact.get("bytes") != path.stat().st_size:
            raise GateError(f"published artifact byte count disagrees for {name}")
        out.append(
            {
                "name": name,
                "bytes": path.stat().st_size,
                "sha256": sha256_file(path),
                "declared_digest": artifact.get("digest"),
            }
        )
    return sorted(out, key=lambda row: row["name"])


def one_run(
    *,
    root: Path,
    trustc: Path,
    lineage_gate: Path,
    output: Path,
    probe_relative: str,
    opt: int,
) -> tuple[dict[str, Any], list[tuple[str, int, str, str, str]], collections.Counter[str]]:
    probe = root / probe_relative
    stem = probe.stem
    run_dir = output / f"O{opt}" / stem
    run_dir.mkdir(parents=True, exist_ok=False)
    dump = run_dir / "IR"
    out_dir = run_dir / "OUT"
    dump.mkdir()
    out_dir.mkdir()
    environment = clean_environment(run_dir / "home", run_dir / "tmp")
    crate_name = f"p_{stem}_o{opt}"
    argv = [
        str(trustc),
        *COMMON_COMPILE_OPTIONS,
        f"--crate-name={crate_name}",
        f"-Copt-level={opt}",
        f"-Ztrust-dump=ir:{dump}",
        str(probe),
        "--out-dir",
        str(out_dir),
    ]
    compiled = run_capture(argv, cwd=root, env=environment)
    (run_dir / "compile.stdout").write_bytes(compiled.stdout)
    (run_dir / "compile.stderr").write_bytes(compiled.stderr)
    if compiled.returncode != 0:
        raise GateError(
            f"compile failed for O{opt} {probe_relative}: rc={compiled.returncode}; "
            f"see {run_dir / 'compile.stderr'}"
        )
    flips = flip_event_count(compiled.stderr)
    expected_flips = require_flip_count(probe_relative, opt, flips)

    coverage_files = sorted(dump.glob("*.coverage.json"))
    if len(coverage_files) != 1:
        raise GateError(
            f"O{opt} {probe_relative} published {len(coverage_files)} coverage documents, "
            "expected 1"
        )
    coverage_path = coverage_files[0]
    coverage = load_json_strict(coverage_path)
    rows, counts = validate_and_project(coverage, probe_relative)

    lineage_argv = [
        sys.executable,
        str(lineage_gate),
        "--dump",
        str(dump),
        "--flip-log",
        str(run_dir / "compile.stderr"),
    ]
    reconciled = run_capture(lineage_argv, cwd=root, env=environment)
    (run_dir / "lineage.stdout").write_bytes(reconciled.stdout)
    (run_dir / "lineage.stderr").write_bytes(reconciled.stderr)
    if reconciled.returncode != 0:
        raise GateError(
            f"lineage reconciliation failed for O{opt} {probe_relative}: "
            f"rc={reconciled.returncode}; see {run_dir / 'lineage.stderr'}"
        )

    publication_artifacts = safe_publication_artifacts(dump, coverage)
    record = {
        "probe": probe_relative,
        "optimization": opt,
        "crate_name": crate_name,
        "compiler_argv": argv,
        "environment": environment,
        "compile_status": "passed",
        "compile_stdout_sha256": sha256_bytes(compiled.stdout),
        "compile_stderr_sha256": sha256_bytes(compiled.stderr),
        "flip_events": {
            "identity": "unique (did, sha256-lineage) pairs",
            "actual": flips,
            "expected": expected_flips,
        },
        "coverage": {
            "path": str(coverage_path.relative_to(output)),
            "schema": coverage.get("schema"),
            "bytes": coverage_path.stat().st_size,
            "sha256": sha256_file(coverage_path),
            "rows": len(rows),
        },
        "publication_verification": {
            "status": "passed",
            "set_integrity": "passed",
            "coverage": "passed",
            "presence": "passed",
            "address_fidelity": "passed",
            "gate_argv": lineage_argv,
            "gate_stdout_sha256": sha256_bytes(reconciled.stdout),
            "gate_stderr_sha256": sha256_bytes(reconciled.stderr),
            "publication_block_sha256": sha256_bytes(canonical_json(coverage["publication"])),
            "artifacts": publication_artifacts,
        },
        "bucket_counts": {bucket: counts.get(bucket, 0) for bucket in BUCKETS},
    }
    return record, rows, counts


def repo_root() -> Path:
    here = Path(__file__).resolve().parent
    result = run_capture(
        (
            "git",
            "-c",
            "core.fsmonitor=false",
            "-c",
            "core.untrackedCache=false",
            "-C",
            str(here),
            "rev-parse",
            "--show-toplevel",
        ),
        cwd=here,
    )
    if result.returncode != 0:
        raise GateError("script is not inside a Git checkout")
    return Path(result.stdout.decode("utf-8", "strict").strip()).resolve()


def receipt_digest(payload: Mapping[str, Any]) -> str:
    unsigned = dict(payload)
    unsigned.pop("receipt_sha256", None)
    return sha256_bytes(canonical_json(unsigned))


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--trustc", help="repository-local stage1/bin/trustc")
    parser.add_argument(
        "--output",
        default="reports/build/mf-r5-full-union",
        help="fresh per-run artifact directory (must not exist)",
    )
    parser.add_argument(
        "--receipt",
        default="reports/build/mf-r5-full-union-receipt.json",
        help="new atomic JSON receipt path (must not exist)",
    )
    args = parser.parse_args(argv)

    try:
        root = repo_root()
        output = Path(args.output).expanduser()
        receipt = Path(args.receipt).expanduser()
        output = (
            (root / output).resolve(strict=False)
            if not output.is_absolute()
            else output.resolve(strict=False)
        )
        receipt = (
            (root / receipt).resolve(strict=False)
            if not receipt.is_absolute()
            else receipt.resolve(strict=False)
        )
        require_fresh_destinations(output, receipt)

        initial_repository = repository_identity(root)
        initial_corpus = corpus_inventory(root)
        initial_unpinned = unpinned_probes(root)
        trustc = select_trustc(root, args.trustc)
        initial_trustc = trustc_identity(root, trustc, initial_repository["head"])
        lineage_gate = root / "scripts/trust_ir_lineage_reconcile.py"
        regular_file(lineage_gate, "independent lineage reconciliation gate")

        output.parent.mkdir(parents=True, exist_ok=True)
        output.mkdir(exist_ok=False)
        runs: list[dict[str, Any]] = []
        rows_by_opt: dict[int, list[tuple[str, int, str, str, str]]] = {
            opt: [] for opt in OPT_LEVELS
        }
        counts_by_opt: dict[int, collections.Counter[str]] = {
            opt: collections.Counter() for opt in OPT_LEVELS
        }
        for opt in OPT_LEVELS:
            for probe in sorted(EXPECTED_CORPUS_SHA256):
                print(f"MF-R5: O{opt} {probe}", file=sys.stderr, flush=True)
                record, rows, counts = one_run(
                    root=root,
                    trustc=trustc,
                    lineage_gate=lineage_gate,
                    output=output,
                    probe_relative=probe,
                    opt=opt,
                )
                runs.append(record)
                rows_by_opt[opt].extend(rows)
                counts_by_opt[opt].update(counts)

        for opt in OPT_LEVELS:
            rows_by_opt[opt].sort()
            if len(rows_by_opt[opt]) != EXPECTED_BODY_COUNT:
                raise GateError(
                    f"O{opt} body ratchet is {len(rows_by_opt[opt])}, "
                    f"expected {EXPECTED_BODY_COUNT}"
                )
            actual = {bucket: counts_by_opt[opt].get(bucket, 0) for bucket in BUCKETS}
            if actual != EXPECTED_BUCKET_COUNTS:
                raise GateError(
                    f"O{opt} six-case census drifted: {actual!r}, "
                    f"expected {EXPECTED_BUCKET_COUNTS!r}"
                )
            if review_ratchet(actual) != EXPECTED_REVIEW_RATCHET:
                raise GateError(f"O{opt} aggregate review ratchet drifted")
            if actual["admitted_wrong"] != 0:
                raise GateError(f"O{opt} has admitted-and-wrong marker rows")
        require_opt_parity(rows_by_opt)
        tuple_digests = require_row_tuple_ratchet(rows_by_opt)

        # Detect changes during the sweep before retaining any receipt.
        final_repository = repository_identity(root)
        final_corpus = corpus_inventory(root)
        final_trustc = trustc_identity(root, trustc, initial_repository["head"])
        if final_repository != initial_repository:
            raise GateError("repository identity changed during the sweep")
        if final_corpus != initial_corpus:
            raise GateError("corpus inventory changed during the sweep")
        if final_trustc != initial_trustc:
            raise GateError("stage1 trustc bytes or identity changed during the sweep")

        opt_receipts: dict[str, Any] = {}
        for opt in OPT_LEVELS:
            tuples = [list(row) for row in rows_by_opt[opt]]
            counts = {bucket: counts_by_opt[opt].get(bucket, 0) for bucket in BUCKETS}
            opt_receipts[f"O{opt}"] = {
                "row_count": len(tuples),
                "row_tuple_sha256": tuple_digests[opt],
                "expected_row_tuple_sha256": EXPECTED_ROW_TUPLE_SHA256,
                "bucket_counts": counts,
                "review_ratchet": {
                    "order": list(REVIEW_RATCHET_ORDER),
                    "actual": list(review_ratchet(counts)),
                    "expected": list(EXPECTED_REVIEW_RATCHET),
                },
            }

        seal_evidence_tree(output)
        retained_inventory = retained_tree_inventory(output)

        payload: dict[str, Any] = {
            "schema": SCHEMA,
            "status": "passed",
            "repository": initial_repository,
            "trustc": initial_trustc,
            "corpus": {
                "reviewed_union_file_count": len(initial_corpus),
                # Probes tracked under the same directory that this reviewed union
                # does NOT cover. Recorded, never asserted: the body ratchet below
                # is derived from the reviewed union alone, so an unrelated probe
                # must stay visible without reddening the gate. See
                # `corpus_inventory` for why set equality was the wrong contract.
                "tracked_but_unpinned": sorted(initial_unpinned),
                "tracked_but_unpinned_count": len(initial_unpinned),
                "expected_body_count_per_optimization": EXPECTED_BODY_COUNT,
                "inventory": initial_corpus,
                "inventory_sha256": sha256_bytes(canonical_json(initial_corpus)),
            },
            "compile_contract": {
                "common_options": list(COMMON_COMPILE_OPTIONS),
                "optimization_levels": list(OPT_LEVELS),
                "run_count": len(runs),
                "environment_policy": (
                    "fresh HOME/TMPDIR; exact PATH/locale/timezone; no inherited environment"
                ),
            },
            "runs": runs,
            "retained_evidence": {
                "root": str(output),
                "mode_policy": "directories 0555; regular files 0444; no links or special files",
                "entry_count": len(retained_inventory),
                "inventory": retained_inventory,
                "inventory_sha256": sha256_bytes(canonical_json(retained_inventory)),
            },
            "optimization_evidence": opt_receipts,
            "o0_o3_exact_tuple_parity": True,
            "admitted_wrong": 0,
            "receipt_digest_domain": "sha256(canonical-json-without-receipt_sha256)",
        }
        digest = receipt_digest(payload)
        payload["receipt_sha256"] = digest
        atomic_write_new(receipt, canonical_json(payload))
        print(f"MF-R5 FULL UNION PASS receipt={receipt} sha256={digest}")
        return 0
    except GateError as error:
        print(f"MF-R5 FULL UNION FAIL: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
