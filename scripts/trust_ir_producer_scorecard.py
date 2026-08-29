#!/usr/bin/env python3
"""trust_ir_producer_scorecard.py — the trust-ir PRODUCER ratchet baseline.

Measures, with an EXISTING trustc stage binary (never builds anything), what fraction
of real Rust bodies the THIR -> trust_ir::Module producer (crates/trust-thir-lower,
behind `-Z trust-ir-lower`) lowers cleanly, by parsing the two per-body
`tracing::debug!` events the mir_built hook emits
(compiler/rustc_mir_build/src/builder/mod.rs:97-121):

    trust-ir-lower: unsupported THIR shapes, def=DefId(0:N ~ path), unsupported=<count>
    trust-ir-lower: differential, def=DefId(0:N ~ path), equal=<bool>, samples=<n>,
        mode=<NotRun|Agreed|MirOracle>, note="<last note>"

Since the 2026-07-01 post-baseline stage build the hook ALSO emits one event per
unsupported reason (BASELINE.md section 7 hook edit):

    trust-ir-lower: unsupported shape, def=DefId(0:N ~ path), at="<span-or-ty>", what="<tag>"

parsed into per-body `reasons` and the `reason_tag_histogram` /
`single_missing_shape_tag_histogram` aggregates. Against a pre-tag binary (e.g. the
be0ef04fdc baseline) those aggregates are simply empty.

Honesty rules baked in:
  * A file that fails to compile WITHOUT the flag is "excluded (does not compile
    standalone)" and leaves the denominator entirely.
  * A file that compiles WITHOUT the flag but fails WITH it (today: the closure
    `item_name` ICE, crates/trust-thir-lower/src/lib.rs:728) is a PRODUCER FAILURE,
    reported first-class ("flag_induced_*" outcomes), never silently excluded.
    Bodies logged before the abort are kept as `partial` and tallied separately.
  * Bodies are counted from the per-body differential event: one event == one THIR
    body reached (closures / nested consts included, when the producer survives them).
  * Every filter and flag is recorded in the JSON provenance block.
  * Campaign regression tests under tests/ui/trust/ are held OUT of the sampling
    population by `scripts/trust_ir_producer_ui_pins.txt`, so a slice may leave its
    pin in the tree without reshuffling the seeded sample. Adding one file to the
    population moves ~180-230 of the 2000 sampled files, which silently destroys
    comparability with every recorded sweep; that manifest replaces the hand-move
    procedure that used to be needed before each run. An eligible tests/ui/trust
    file classified in NEITHER manifest section is a HARD ERROR, so the next slice
    cannot forget. Audit it in ~1s without sweeping:

        python3 scripts/trust_ir_producer_scorecard.py --check-ui-pins
        python3 scripts/trust_ir_producer_scorecard.py --selftest-ui-pins

Usage (defaults reproduce the 2026-07-01 baseline):
  python3 scripts/trust_ir_producer_scorecard.py \
      --trustc build/aarch64-apple-darwin/stage1/bin/trustc \
      --out-dir reports/trust-ir-producer-baseline-2026-07-01 \
      --seed 20260701 --sample-size 2000 --jobs 8 \
      --corpus realcode=reports/2026-06-29-honest-real-code-coverage/corpus/realcode.rs \
      --corpus realcode_no_closure_bodies=reports/trust-ir-producer-baseline-2026-07-01/corpus-variant/realcode_no_closure_bodies.rs

Author: Andrew Yates | Copyright 2026 | License: Apache-2.0 OR MIT
"""

import argparse
import collections
import concurrent.futures
import datetime
import hashlib
import json
import os
import platform
import random
import re
import shutil
import signal
import subprocess
import sys
import tempfile
import threading

try:
    import resource
except ImportError:  # non-POSIX
    resource = None

# Trust: hard per-compile ADDRESS-SPACE cap. ROOT-CAUSE fix for the burn-in/scorecard OOM: these
# harnesses compile ~2000 corpus bodies, some of which are trait-solver-OVERFLOW torture tests
# (e.g. tests/ui/traits/next-solver/overflow/exponential-trait-goals.rs) that balloon ONE trustc to
# tens of GB DURING type-checking. The old `subprocess.run(timeout=...)` had NO memory cap (so a
# runaway could OOM the host before the timeout fired) and did not put the child in its own session
# (so the timeout's SIGKILL could not reap a trustc stuck mid-huge-allocation -> ORPHAN that keeps
# eating memory). `guarded_compile` caps address space via RLIMIT_AS (the runaway ABORTS at the cap
# and exits cleanly, so it can neither OOM the host nor orphan) and runs each trustc in a new session
# so a timeout reaps the WHOLE process group. Env-overridable for machines with more/less RAM.
GUARD_MEM_CAP_BYTES = int(float(os.environ.get("TRUST_COMPILE_MEM_CAP_GB", "20")) * (1024 ** 3))


def _guard_preexec():
    # New SESSION (setsid) so the child is a session+group leader (pgid == pid): a timeout or the RSS
    # watchdog can then reap the WHOLE process group with one killpg — no orphaned trustc/child.
    os.setsid()
    # Address-space cap. This is the LINUX enforcement path (the kernel aborts the allocation at the
    # cap). macOS/Darwin does NOT enforce RLIMIT_AS/RLIMIT_DATA — there the RSS watchdog below is the
    # real cap. Only simple syscalls here, so this is safe as a `preexec_fn` even under a threaded
    # parent (no malloc/lock touched).
    if resource is not None:
        try:
            resource.setrlimit(resource.RLIMIT_AS, (GUARD_MEM_CAP_BYTES, GUARD_MEM_CAP_BYTES))
        except (ValueError, OSError):
            pass  # best-effort; not every platform enforces RLIMIT_AS


def _group_rss_kb(pgid):
    """Total RSS (KB) of the session group led by `pgid`, or None if it can't be read."""
    try:
        out = subprocess.run(
            ["ps", "-o", "rss=", "-g", str(pgid)],
            capture_output=True, text=True, timeout=5,
        ).stdout
        return sum(int(x) for x in out.split())
    except (subprocess.SubprocessError, ValueError, OSError):
        return None


def guarded_compile(argv, cwd, env, timeout, poll=2.0):
    """`subprocess.run` replacement for a single corpus compile that CANNOT OOM the host or orphan a
    runaway. Runs the child in its own session, caps its total group RSS via a watchdog (the real cap
    on macOS, where RLIMIT_AS is unenforced) AND via RLIMIT_AS (the cap on Linux), and reaps the whole
    group on timeout. Returns (returncode_or_None, stderr_bytes); None means timeout or OOM-kill."""
    proc = subprocess.Popen(
        argv, cwd=cwd, env=env,
        stdout=subprocess.DEVNULL, stderr=subprocess.PIPE,
        preexec_fn=_guard_preexec,
    )
    cap_kb = GUARD_MEM_CAP_BYTES // 1024
    oom_killed = threading.Event()
    stop = threading.Event()

    def _watchdog():
        # setsid made pgid == pid; poll the WHOLE group's RSS so a runaway trustc is killed BEFORE it
        # can OOM the host (rather than only on the — possibly much later — compile timeout).
        while not stop.wait(poll):
            rss = _group_rss_kb(proc.pid)
            if rss is not None and rss > cap_kb:
                oom_killed.set()
                try:
                    os.killpg(proc.pid, signal.SIGKILL)
                except (ProcessLookupError, OSError):
                    pass
                return

    wd = threading.Thread(target=_watchdog, daemon=True)
    wd.start()
    try:
        _, stderr = proc.communicate(timeout=timeout)
        if oom_killed.is_set():
            return None, b""  # RSS watchdog reaped it — treat as a failed compile
        return proc.returncode, stderr
    except subprocess.TimeoutExpired:
        try:
            os.killpg(proc.pid, signal.SIGKILL)  # reap the whole group — no orphan
        except (ProcessLookupError, OSError):
            proc.kill()
        try:
            proc.communicate(timeout=10)
        except subprocess.TimeoutExpired:
            pass
        return None, b""
    finally:
        stop.set()

# Exact-event filter: the two trust-ir-lower events live in module
# rustc_mir_build::builder (builder/mod.rs); the noisy sub-modules are forced off.
RUSTC_LOG_FILTER = (
    "rustc_mir_build::builder::scope=off,"
    "rustc_mir_build::builder::expr=off,"
    "rustc_mir_build::builder::matches=off,"
    "rustc_mir_build::builder::block=off,"
    "rustc_mir_build::builder::custom=off,"
    "rustc_mir_build::builder::cfg=off,"
    "rustc_mir_build::builder=debug,"
    # Trust (#181): the producer's self-validation tripwire lives in the trust-thir-lower CRATE,
    # not in the rustc hook, so it needs its own filter entry. Without this the summary event
    # never appears and every module reports UNMEASURED — which is what the first run did, and
    # is exactly why the parser distinguishes "no summary event" from "total=0". A filter that
    # silently omits an instrument is the same failure as a gate that cannot fail.
    "trust_thir_lower::crate_module=debug,"
    # Trust: `differential` needs its own entry for the same reason `crate_module` does — a
    # filter that omits a module silences EVERY instrument in it. The aggregate-param batch
    # shipped `aggregate_name_split_probe` to convert P1's accepted residual (a zero-field
    # struct whose two sides render different names) from an assertion into a measurement. It
    # is gated on `tracing::enabled!(DEBUG)`, which is false when the filter does not name the
    # module — so the probe was DEAD ON ARRIVAL and every sweep since has silently measured
    # nothing. That is a +0-by-construction instrument: the worst kind, because its silence is
    # indistinguishable from a clean result.
    #
    # MEASURED before adding this: on tests/ui/array-slice-vec/infer_array_len.rs the probe
    # emits 0 events without this entry and 2 with it — and both are real:
    #   thir_name="A", oracle_name="infer_array_len::A", fields=0, zero_field=true
    # i.e. the renderer split P1 was designed around DOES occur on admitted zero-field params.
    # It is QUALIFICATION drift (same entity, two spellings), not two entities sharing a key,
    # which is the benign shape — and it is also why name-equality was rejected as the pin: it
    # would have refused these outright for a systematic +0.
    #
    # Cost measured, not assumed: `differential.rs` holds 6 debug/trace sites against
    # `crate_module.rs`'s 4, and the whole file's stderr came to 6 lines.
    "trust_thir_lower::differential=debug"
)

UNSUP_RE = re.compile(
    r"trust-ir-lower: unsupported THIR shapes, "
    r"def=DefId\([^~]*~\s*(?P<path>.+?)\), unsupported=(?P<count>\d+)"
)
# Per-reason tag event (landed 2026-07-01 post-baseline, the hook edit from
# BASELINE.md section 7): one event per (span, tag) pair in Lowered.unsupported.
#   trust-ir-lower: unsupported shape, def=DefId(0:N ~ path), at="<span-or-ty>", what="<tag>"
SHAPE_RE = re.compile(
    r"trust-ir-lower: unsupported shape, "
    r"def=DefId\([^~]*~\s*(?P<path>.+?)\), at=\"(?P<at>.*)\", what=\"(?P<what>[^\"]*)\"\s*$",
    re.MULTILINE,
)
# Trust (v2 Phase 0b): one aggregated event per (tag, class) from the COLLECT-ALL second pass
# on strict-failed bodies — the body's approach to FULL leaf demand (strict events above are the
# first-fail prefix). class is "cascade" for unbound-local echoes, "primary" otherwise.
#   trust-ir-lower: collect-all tag, def=DefId(0:N ~ path), what="<tag>", n=<count>, class="<c>"
COLLECT_RE = re.compile(
    r"trust-ir-lower: collect-all tag, "
    r"def=DefId\([^~]*~\s*(?P<path>.+?)\), what=\"(?P<what>[^\"]*)\", "
    r"n=(?P<n>\d+), class=\"(?P<cls>primary|cascade)\"\s*$",
    re.MULTILINE,
)
# Trust (measurement honesty): the per-body CLASS event. `symbolic=true` marks a body whose
# module carries a value-less opaque carrier (symbolic assoc const / const-generic param global,
# or the opaque `Ty::Unit` spelling of a bare generic param). Such a body can be tag-free —
# "lowered clean" — while being excluded from BOTH the interpretation differential and the
# executable splice. Reported separately so the clean-rate never silently conflates a modelled
# body with a placeholder one.
#   trust-ir-lower: body class, def=DefId(0:N ~ path), symbolic=<bool>, clean=<bool>
CLASS_RE = re.compile(
    r"trust-ir-lower: body class, "
    r"def=DefId\([^~]*~\s*(?P<path>.+?)\), symbolic=(?P<symbolic>true|false), "
    r"opaque=(?P<opaque>true|false), clean=(?P<clean>true|false)\s*$",
    re.MULTILINE,
)
# Trust (#181): the producer's SELF-VALIDATION tripwire. `validate_module` runs on the assembled
# crate module and emits one event per error CLASS plus a total. This is the ONLY instrument that
# answers "is the emitted module well-formed?" — the coverage ratchet answers "did the body lower
# without a fail-closed tag", a different question, and the gap between them hid ~31% of modules
# being REJECTED across four classes, two of them real defects.
#   trust-ir-lower: module validation error, class="<Variant>", n=<count>
#   trust-ir-lower: module validation summary, total=<count>
VALERR_RE = re.compile(
    # Accepts BOTH the quoted form (a `&str` field) and the bare form (a `Display`-formatted
    # `String` field, `class = %class`). The emitter switched from the former to the latter when
    # the hand-written class allowlist was removed, and this regex silently stopped matching —
    # the per-class histogram went empty while the TOTAL kept reporting, which is the only reason
    # it was visible at all. Tolerate both spellings so the parser cannot be desynced again by a
    # field-formatting change.
    r"trust-ir-lower: module validation error, class=\"?(?P<class>[A-Za-z_][A-Za-z0-9_]*)\"?, "
    r"n=(?P<n>\d+)"
)
VALSUM_RE = re.compile(r"trust-ir-lower: module validation summary, total=(?P<total>\d+)")
# Trust (extern-750 attribution): the row-1 dead-path probe. `crate_module.rs` has emitted this
# on EVERY sweep since the B8 split — `RUSTC_LOG_FILTER` already carries
# `trust_thir_lower::crate_module=debug` — and the scorecard threw it away. That discard is the
# whole reason the 750-row `extern` bucket, ~40% of the MODELLED->Agreed gap, has been costed
# from a hand-collected n=104 instead of from the corpus.
#
#   trust-ir-lower: row1 dead-path probe, def_index=3, def_path="ADD_A", declarations=1,
#                   outcome="divergence-or-trap", samples=0
#
# VALIDATED against real stderr before landing (tests/ui/consts/const-int-wrapping-rpass.rs,
# stage1 b38db06a6d: 16 events, outcomes divergence-or-trap / oracle-live-havoc / not-run).
# This is deliberately NOT how the seam-blocker parser was built — that one was written against
# a note format and only later measured, and the measurement found the margin was zero.
ROW1_PROBE_RE = re.compile(
    r'trust-ir-lower: row1 dead-path probe, '
    r'def_index=(?P<def_index>\d+), '
    r'def_path="(?P<def_path>[^"]*)", '
    r'declarations=(?P<declarations>\d+), '
    r'outcome="(?P<outcome>[^"]*)", '
    r'samples=(?P<samples>\d+)'
)
# The probe emits a BARE LEAF NAME (`ADD_A`) while a body is keyed by its full crate-qualified
# path (`const_int_wrapping_rpass[34f5]::ADD_A`). Joining on the leaf is the obvious move and it
# is WRONG: two modules can each hold a `foo`, so the leaf is not injective over bodies — the
# same two-entities-one-key hazard that has produced repeated false agreement in this project.
# The DefId text carries `0:3`, and the probe carries `def_index=3`; a DefIndex IS injective
# within a crate. So this recovers index -> path from the differential line and joins on the
# index. `DIFF_RE` is deliberately NOT modified — it is the core body parser, and a separate
# read-only regex cannot break it.
#
# MEASURED before landing: 16 probe events, 16 bodies, 16 joined on one file; a leaf-name join
# scored 0/16 because of the qualification mismatch, which is exactly the silent-empty result
# that would have read as "the probe found nothing".
DEFIDX_RE = re.compile(
    r'trust-ir-lower: differential, def=DefId\(\d+:(?P<index>\d+)\s*~\s*(?P<path>[^)]+)\)'
)
DIFF_RE = re.compile(
    r"trust-ir-lower: differential, "
    r"def=DefId\([^~]*~\s*(?P<path>.+?)\), equal=(?P<equal>true|false), "
    r"samples=(?P<samples>\d+), mode=(?P<mode>\w+), note=\"(?P<note>.*)\"\s*$",
    re.MULTILINE,
)

# Content filters for the tests/ui sample (crude but reproducible, per the baseline
# methodology). A file matching ANY pattern is excluded BEFORE sampling.
UI_CONTENT_FILTERS = [
    ("error-annotation", re.compile(r"//~")),
    ("aux-build", re.compile(r"aux-build|aux-crate|// aux-|//@ aux-")),
    ("ignore-directive", re.compile(r"ignore-")),
]

# The campaign-pin manifest. `random.sample` is a function of the population LENGTH,
# so ONE new file under tests/ui/trust reshuffles the whole seeded sample (measured:
# 179 of 2000 moved once; a slice-16 sweep was discarded after 233 shifted). The
# historical workaround was to hand-move the campaign's own pins out of tests/ui
# before every sweep — a count that went 8 -> 9 -> 13 -> 14 -> 15 -> 16 and was
# remembered nowhere mechanical. This manifest replaces it: [excluded] paths are
# dropped from the population BEFORE sampling, so the pins can live in the tree.
# The manifest's own header carries the rule and the measured identity claim.
UI_PIN_MANIFEST = os.path.join(
    os.path.dirname(os.path.abspath(__file__)), "trust_ir_producer_ui_pins.txt"
)
# The directory whose files the manifest is a CENSUS of. Every eligible .rs under it
# must be classified; an unclassified one is a hard error, so the next slice cannot
# silently widen the population.
UI_PIN_DIR = os.path.join("tests", "ui", "trust")


class UiPinManifestError(RuntimeError):
    """The manifest and the tree disagree. Fail closed: a sweep run against an
    unclassified population is not comparable to any recorded sweep, and that is
    invisible in the output — which is exactly how the tax was paid in silence."""


def load_ui_pin_manifest(path=UI_PIN_MANIFEST):
    """Parse the two-section manifest into (excluded, in_pool) path lists."""
    excluded, in_pool, section = [], [], None
    try:
        fh = open(path, encoding="utf-8")
    except OSError as e:
        raise UiPinManifestError(f"cannot read the campaign-pin manifest {path}: {e}") from e
    with fh:
        for lineno, raw in enumerate(fh, 1):
            line = raw.split("#", 1)[0].strip()
            if not line:
                continue
            if line.startswith("[") and line.endswith("]"):
                section = line[1:-1].strip().lower()
                if section not in ("excluded", "in-pool"):
                    raise UiPinManifestError(
                        f"{path}:{lineno}: unknown section [{section}];"
                        " expected [excluded] or [in-pool]"
                    )
                continue
            if section is None:
                raise UiPinManifestError(
                    f"{path}:{lineno}: entry {line!r} appears before any [section] header"
                )
            (excluded if section == "excluded" else in_pool).append(line)
    return excluded, in_pool


def audit_ui_pin_manifest(repo, eligible_rel, excluded, in_pool):
    """Cross-check the manifest against the tree. Returns (errors, notes).

    The load-bearing check is the LAST one: an eligible tests/ui/trust file in
    neither section would silently join the sampling population and reshuffle the
    seeded sample, which is the defect this whole mechanism exists to prevent."""
    errors, notes = [], []
    seen = {}
    for sect, paths in (("excluded", excluded), ("in-pool", in_pool)):
        for p in paths:
            if p in seen:
                errors.append(
                    f"{p}: listed twice ([{seen[p]}] and [{sect}]) — one entry per file"
                )
            seen[p] = sect
            if not os.path.isfile(os.path.join(repo, p)):
                errors.append(
                    f"{p}: listed in [{sect}] but does not exist —"
                    f" delete the stale line from {os.path.relpath(UI_PIN_MANIFEST, repo)}"
                )
    pin_prefix = UI_PIN_DIR + os.sep
    for p in eligible_rel:
        if not p.startswith(pin_prefix):
            continue
        if p not in seen:
            errors.append(
                f"{p}: eligible for the ui sample but classified in NEITHER section of"
                f" {os.path.relpath(UI_PIN_MANIFEST, repo)}. Admitting it would reshuffle the"
                " seeded sample and make this sweep incomparable to every recorded one."
                " Add it to [excluded] if it is a campaign pin minted after the baseline"
                " (the default for a slice regression test), or to [in-pool] only if it is"
                " genuinely part of the measured corpus."
            )
    eligible_set = set(eligible_rel)
    for p in in_pool:
        if p not in eligible_set and os.path.isfile(os.path.join(repo, p)):
            notes.append(f"{p}: listed [in-pool] but no longer passes the content filters")
    return errors, notes


# Trust (B8 step 1): the declaration-blocker taxonomy, mirrored from `DeclKind` in
# crates/trust-thir-lower/src/crate_module.rs. THE ORDER IS LOAD-BEARING — it is tractability,
# least tractable first, and `classify_note` attributes a body carrying several classes to the
# FIRST one present. That rule means no class is ever credited with a body that retiring it alone
# would not unblock, so every per-class count is a LOWER bound on what the class is worth.
#
# What this replaced: one anonymous `clean-skip-extern-callee` string covering 983 clean rows
# (919 MODELLED + 64 OPAQUE-COLLAPSE) across 577 files on postbuild-slice20-control — the corpus's
# largest single non-verdict class, 50.0% of the MODELLED->Agreed gap, and misnamed for four
# fifths of what it held. The five members are retired by unrelated work (see the Rust docs), so
# the merged class could not be ranked against at all.
SEAM_BLOCKER_KINDS = ["extern", "unknown", "havoc", "ambiguous", "local-unlowered"]

# Anything the producer named that this list does not know. Ordered FIRST in the dominance rule
# on purpose: a residue means the Python taxonomy has drifted from `DeclKind`, and a body carrying
# an unknown class must surface as such rather than be absorbed by a known co-blocker.
SEAM_BLOCKER_UNCLASSIFIED = "unclassified"

_SEAM_BLOCKERS_RE = re.compile(r"\[blockers: ([^\]]+)\]")


def parse_seam_blockers(note: str) -> dict:
    """`{kind: count}` from a step-2 declaration-gate skip note.

    Returns `{}` when the note carries no `[blockers: ...]` marker, which is how an artifact
    produced BEFORE this split is recognized: those rows keep the legacy merged class rather than
    being silently attributed to one member of a taxonomy their compiler never applied.
    """
    m = _SEAM_BLOCKERS_RE.search(note)
    if not m:
        return {}
    out = {}
    for part in m.group(1).split(","):
        kind, _, count = part.strip().partition("=")
        if kind:
            out[kind] = int(count) if count.isdigit() else 0
    return out


def seam_blocker_dominant(kinds: dict) -> str:
    """The single class a body is attributed to: the least tractable one present.

    `unclassified` wins outright, and so does any class the mirror does not know — a taxonomy
    drift must never hide behind a co-occurring known blocker.
    """
    if SEAM_BLOCKER_UNCLASSIFIED in kinds or set(kinds) - set(SEAM_BLOCKER_KINDS):
        return SEAM_BLOCKER_UNCLASSIFIED
    for kind in SEAM_BLOCKER_KINDS:
        if kind in kinds:
            return kind
    return SEAM_BLOCKER_UNCLASSIFIED


def seam_blocker_census(bodies) -> dict:
    """Trust (B8 step 1): the checked census behind the `clean-skip-seam-decl-*` split.

    Four views, because the merged class was ranked wrongly for want of exactly these:

    * `dominant` — the 5-way partition `classify_note` uses. Sums to `rows_split` BY
      CONSTRUCTION; `dominant_sums` records that as a checkable fact rather than a promise.
    * `sole_blocker` — bodies whose closure carries ONE class. This is the number that says what
      retiring that class ALONE recovers, and it is the one to rank against.
    * `participation` — bodies where the class appears at all. `sole` and `participation` bracket
      the truth, and this campaign has been burned in BOTH directions by quoting one alone
      (sole-counts inflated by first-fail masking; sole-counts under-counting a widening wave).
    * `combinations` — the exact co-occurrence sets, so a two-class campaign can be priced
      without another sweep.

    `dominant_modelled` restates the partition over MODELLED rows only, since that is the
    population the MODELLED->Agreed gap is measured over.
    """
    rows = [b for b in bodies if "extern/declaration-only callee" in (b.get("note") or "")]
    # Prefer the STRUCTURED field; fall back to the note only for artifacts written before it
    # existed. The note is truncated to 160 chars and the marker sits at offset ~112, so parsing
    # it is correct only by luck of name lengths — see the record-construction comment.
    parsed = [
        (b, b["seam_blockers"] if isinstance(b.get("seam_blockers"), dict)
            else parse_seam_blockers(b.get("note") or ""))
        for b in rows
    ]
    split = [(b, k) for b, k in parsed if k]
    out = {
        "rows_total": len(rows),
        "rows_split": len(split),
        # Non-zero only when reading an artifact built before the split shipped.
        "rows_legacy_unsplit": len(rows) - len(split),
    }
    if not split:
        return out
    dominant = collections.Counter()
    dominant_modelled = collections.Counter()
    sole = collections.Counter()
    participation = collections.Counter()
    combos = collections.Counter()
    for b, kinds in split:
        known = [k for k in SEAM_BLOCKER_KINDS if k in kinds]
        extra = sorted(set(kinds) - set(SEAM_BLOCKER_KINDS))
        for k in known + extra:
            participation[k] += 1
        combos["+".join(known + extra)] += 1
        d = seam_blocker_dominant(kinds)
        dominant[d] += 1
        if b.get("symbolic") is False and b.get("opaque_collapse") is False:
            dominant_modelled[d] += 1
        if len(kinds) == 1:
            sole[next(iter(kinds))] += 1
    out.update(
        dominant=dict(dominant),
        dominant_modelled=dict(dominant_modelled),
        sole_blocker=dict(sole),
        participation=dict(participation),
        combinations=dict(combos.most_common()),
        # The gate. If this ever disagrees the partition is not a partition.
        dominant_sums=sum(dominant.values()),
    )
    return out


# NB: no PEP 604 (`dict | None`) annotation here — this script runs under the macOS
# CommandLineTools python3.9, where that raises TypeError at import time.
def classify_note(mode: str, note: str, blockers=None) -> str:
    """Map a differential-event (mode, note) pair to a stable class name.

    `blockers` is the STRUCTURED seam-blocker census for this row, when the caller has it. Pass
    it. Parsing it back out of `note` works only while the note is intact, and the stored note is
    TRUNCATED to 160 chars — see `parse_seam_blockers` for why that is a trap rather than a
    detail.
    """
    if mode == "Agreed":
        return "agreed"
    if mode == "MirOracle":
        if note.startswith("signature divergence"):
            return "divergence-signature"
        return "divergence-interpretation"
    # mode == NotRun
    # Trust (B3/E6 authority audit): classify exact comparator markers before broad substring
    # rules below (`direct call`, `vararg`, ...). The diagnostic embeds function names, and a
    # coincidental name must not change the safety lane's scorecard class.
    if (
        "observable-effect comparison is not modeled" in note
        or "callable/frame identity comparison is not modeled" in note
    ):
        return "clean-skip-unmodeled-observation"
    if re.match(r"\d+ unsupported THIR shape", note):
        return "unsupported"
    if "direct call" in note:
        return "clean-skip-direct-call"
    # Trust (B9-A): crate-seam call-linking differential skip classes. `bundle construction failed`
    # is checked FIRST — its `{e:?}` detail could contain arbitrary substrings; none of these three
    # tokens appears in any pre-existing note, and the seam notes avoid every pre-existing trigger.
    # These bodies were the former `clean-skip-direct-call` population; at the seam they either turn
    # into real verdicts ("agreed" / a divergence) or redistribute into these fail-closed classes.
    if "oracle bundle construction failed" in note:
        return "clean-skip-oracle-bundle-failed"
    if "callee-set asymmetry" in note:
        return "clean-skip-callee-asymmetry"
    if "extern/declaration-only callee" in note:
        # Trust (B8 step 1): the split. `[blockers: ...]` is appended by
        # `run_seam_differentials` step 2 and names the DeclKind classes actually reachable from
        # this body. Its absence means the artifact predates the split — keep the merged class
        # rather than attributing a body to a taxonomy its compiler never applied.
        b = blockers if blockers is not None else parse_seam_blockers(note)
        if not b:
            return "clean-skip-extern-callee"
        return "clean-skip-seam-decl-" + seam_blocker_dominant(b)
    # Trust (B9-A): seam-only representation artifacts, reclassified from a false divergence to a
    # coverage-only skip. Neither is a semantic disagreement (see run_seam_differentials step 8).
    if "unit-call arity gap" in note:
        return "clean-skip-unit-call-arity"
    if "type-id interning differs" in note:
        return "clean-skip-seam-sig-interning"
    # Trust (B9-B1): a LIVE havoc (an Undef outside the proven-dead-seed shape) is its own
    # precise class; the dead-seed population now converts to real verdicts ("agreed").
    if "LIVE havoc" in note:
        return "clean-skip-oracle-havoc"
    # Trust (drop-glue lane): the held-back half of the old oracle-panic-model class. The
    # neutralisation is TOTAL and SYMMETRIC — it rewrites iff every const-false oracle assert in
    # the body is a fatal drop-glue marker (and there is at least one; that conjunct is the
    # anti-vacuity guard, since "every const-false assert here is drop glue" is trivially true of
    # a body with none). Anything else refuses and lands here, so this class measures the price of
    # the refusal instead of hiding it in the anonymous bucket.
    #
    # The token LEADS the note, so the 160-char store cap can never truncate it away — unlike the
    # seam-blocker marker, which ended at offset 160 of 160 with the closing bracket as the last
    # byte retained. Checked BEFORE the `oracle-panic-model` rule below because that rule's
    # substring would otherwise claim these rows.
    if note.startswith("oracle-drop-glue-mixed"):
        return "clean-skip-drop-glue-mixed"
    # Trust (drop-glue lane ride-along): `sig_tys_agree` returned Err — the two sides' SIGNATURES
    # are not comparable, so step (5) declines rather than judging. Measured on postbuild-dropglue:
    # neutralising the drop-glue markers pushed 40 bodies past the const-false guard and straight
    # into this refusal, and with no rule they all landed in the anonymous `clean-skip-other`.
    #
    # That is the exact failure this project has already paid for once — an anonymous catch-all hid
    # the second-largest bucket on the board and cost a whole unplannable wave. A wave that RETIRES
    # a named class by moving 40 rows into `clean-skip-other` has not retired them; it has hidden
    # them, and the histogram reads like progress.
    #
    # Three distinct spelling splits share this prefix and are all worth counting separately, so the
    # class keeps the parenthesised reason rather than collapsing them:
    #   nested spelling-split G0 quarantine (no enum provenance)
    #   array-vs-tuple  (producer spells [T; N>0] as Tuple, oracle as Array)  <- this is #202
    #   enum spelled first-class on one side only (mid-B3 residue)
    # Keyed on `startswith`, and that is load-bearing rather than stylistic: the STORED note is
    # truncated to 160 chars, so a rule keyed on a marker that can sit past that offset is
    # unreadable from the artifact afterwards. Measured while adding this rule —
    # `clean-skip-unmodeled-observation` rows store as exactly 160 chars ending
    # `"...; observable-effect comp"`, with their own marker cut mid-phrase. Their stored
    # `note_class` is RIGHT (classified from the full note at sweep time); it is OFFLINE
    # re-classification that is wrong for them.
    #
    # THE RULE THAT FOLLOWS FROM THAT: `note_class` in an artifact is authoritative. Do not
    # re-derive it from the stored `note` — you will silently mis-bucket every row whose marker
    # sits past 160. This is the third truncation defect in this file's neighbourhood tonight;
    # the first had ZERO characters of margin.
    if note.startswith("signature comparability failure"):
        return "clean-skip-sig-incomparable"
    # Trust: split `clean-skip-other`, which had grown to 397 rows / 15 distinct note prefixes —
    # the second-largest governance-clear population and completely unenumerated. An anonymous
    # catch-all has already cost this project one unplannable wave; leaving 397 rows in it while
    # ranking lanes off the histogram is ranking against a number that means nothing.
    #
    # Measured on postbuild-opaquerespell (rows / of which MODELLED):
    #   249/75  entry not spliced into the crate module   <- the UNDETERMINED bucket; its cause is
    #                                                        NOT recorded, and the one-line
    #                                                        diagnostic that would explain it sits
    #                                                        inside BYTE-IDENTICAL-frozen
    #                                                        crate_module.rs. Naming it does not
    #                                                        explain it — it makes the size of the
    #                                                        un-explainable part visible.
    #    61/35  call args carry a place-path value carrier
    #    32/30  call args carry a ZST closure value (Ty::Unit/PhantomData)
    #     9/9   producer-synthesized closure->fn-ptr shim
    #    32/22  both sides errored non-trappily (THIR out_of_fuel) — the interpreter fuel class
    #
    # 351 of the 397 are SEAM rows, i.e. `crate_module.rs` territory and governance-blocked. That
    # is the finding: the catch-all was mostly one frozen class wearing four names. Ordered
    # most-specific-first; every arm keys on a marker that leads its note or its seam prefix, so
    # none can be truncated away by the 160-char store.
    if note.startswith("seam-deferred body:"):
        if "entry not spliced" in note:
            return "clean-skip-seam-unspliced-entry"
        if "place-path value carrier" in note:
            return "clean-skip-seam-callarg-placepath"
        if "ZST closure value" in note:
            return "clean-skip-seam-callarg-zst-closure"
        if "closure→fn-p" in note or "closure->fn-p" in note:
            return "clean-skip-seam-closure-fnptr-shim"
    if note.startswith("both sides errored non-trappily") and "out_of_fuel" in note:
        return "clean-skip-interpreter-fuel"
    if "oracle-panic-model" in note:
        return "clean-skip-oracle-panic-model"
    if "Inst::Undef" in note or "CheckedBinaryOp" in note:
        return "clean-skip-oracle-undef"
    if note.startswith("param count") or note.startswith("scalar param count"):
        return "clean-skip-param-cap"
    if "non-scalar parameter" in note:
        return "clean-skip-nonscalar-param"
    # Trust (Q1, Slice B ceiling probe): a READ pointer param whose AGGREGATE referent was proven
    # to have an agreeing byte layout on both sides — materializable, but the aggregate referent
    # sampler is the follow-on lane, so it is still a coverage-only skip today. Checked BEFORE the
    # `param-read` rule below because that rule's substring would otherwise claim it, and this
    # class exists precisely to MEASURE the follow-on's yield on the corpus rather than estimate
    # it. Both notes say "is READ"; only this one says the referent is layout-agreeing.
    if "layout-agreeing AGGREGATE referent" in note:
        return "clean-skip-ptr-pointee-aggregate"
    # Trust (aggregate-param batch): a param the new aggregate lanes (ptr-leaf / fieldless /
    # tuple / wide) WOULD admit, withheld because `sig_tys_agree` returned Ok(false) — which at
    # step (5) publishes a DIVERGENCE. The batch admits bodies that previously died at the
    # non-scalar refusal, so admitting them opens a brand-new divergence-publication channel on
    # a RETURN-side spelling split, against a gate that says divergences 0. Conjunct (v) blocks
    # exactly that, and only for the newly-admitted lanes: a param that was already admissible
    # keeps today's behaviour and still publishes its divergence.
    #
    # It needs its own class rather than `clean-skip-other` for the reason that fallthrough keeps
    # earning: a held-back population in the anonymous bucket is a population nobody can rank, and
    # this one is the direct measure of how much the batch is leaving on the table.
    #
    # Keyed on the full phrase, NOT the bare word `aggregate` — that would be claimed by (and
    # would claim) the `layout-agreeing AGGREGATE referent` rule immediately above.
    if "aggregate param admissible but signature spelling split" in note:
        return "clean-skip-aggregate-sig-split"
    # Slice 3 (opaque-param widening) skip classes: a Ptr/Unit param that is actually READ
    # (opaque sampling refused, fail-closed), and an opacity-scan infrastructure failure.
    if "opaque sampling refused" in note:
        return "clean-skip-param-read"
    if "opacity scan failed" in note:
        return "clean-skip-opacity-scan"
    if "vararg" in note:
        return "clean-skip-vararg"
    # An RPIT/TAIT body: the MIR-side oracle's layout queries would cycle through this body's own
    # borrowck, so the differential declines BEFORE extraction. Distinct from every other skip in
    # kind — the others are things the oracle cannot MODEL, this one is a body it cannot be ASKED
    # about from inside `mir_built` at all. Left in `clean-skip-other` it would look like ordinary
    # oracle incapacity, and the population that has no verdict for a structural reason would stop
    # being countable.
    if "unrevealed opaque" in note:
        return "clean-skip-unrevealed-opaque"
    if "oracle lowering failed" in note:
        return "clean-skip-oracle-lowering-failed"
    # Trust (slice 20): the pending-const re-adjudication's own fail-close. A body deferred to
    # the seam because it carried const placeholders, whose `resolve_pending_consts` then FAILED
    # and marked it unsupported — so the seam refused to interpret a body still holding a
    # placeholder. Its own class rather than `clean-skip-other`: this is the population that
    # measures how often finalizer const evaluation does not deliver, which is the only number
    # that says whether the lane's ceiling is the gate or the evaluator.
    if "finalizer const resolution failed" in note:
        return "clean-skip-pending-const-unresolved"
    if "could not build sample argument" in note:
        return "clean-skip-sample-arg"
    # Wave-5 documented model split: producer-canonical first-class Ty::Enum vs the oracle's
    # flattened-struct enum spelling — a comparability failure (coverage-only), never a verdict.
    if "enum-typed comparison not modeled" in note:
        return "clean-skip-enum-model-split"
    return "clean-skip-other"


def body_kind(def_path: str) -> str:
    if "{closure" in def_path:
        return "closure"
    if "{constant#" in def_path:
        return "constant"
    return "named"  # fn / method / const-item body (indistinguishable in the log)


def parse_validation(stderr: str):
    """Trust (#181): the module-validation tripwire's per-class counts for one file.

    Returns `{"total": int, "classes": {name: count}}`, or None when the summary event is
    ABSENT — which means the binary predates the tripwire, NOT that the module was clean. That
    distinction is the whole point: a missing instrument and a passing one must never read the
    same, which is the failure mode a silent sweep produced twice before this existed.
    """
    m = VALSUM_RE.search(stderr)
    if not m:
        return None
    classes = {}
    for e in VALERR_RE.finditer(stderr):
        classes[e.group("class")] = classes.get(e.group("class"), 0) + int(e.group("n"))
    return {"total": int(m.group("total")), "classes": classes}


def parse_bodies(stderr: str):
    """Parse per-body events. Returns (bodies, anomalies)."""
    unsup = {}
    dup_unsup = 0
    for m in UNSUP_RE.finditer(stderr):
        p = m.group("path")
        if p in unsup:
            dup_unsup += 1
        unsup[p] = max(unsup.get(p, 0), int(m.group("count")))
    reasons = collections.defaultdict(list)
    # Trust (slice 20 ride-along a): the per-tag DETAIL, captured in lockstep with the tag.
    #
    # The compiler already computes this and the artifact threw it away. `SHAPE_RE` has always
    # captured group `at` — the span, plus `[masking: <leaf>]` for an aggregator tag whose real
    # cause is a subtree leaf (trust-thir-lower/src/lib.rs, `lower_call_args`) — and this loop
    # dropped it on the floor, so `grep -c "masking:" data.json` returned 0 and every lane
    # attribution in this campaign has been a guess reconstructed by hand from the source.
    #
    # BLIND SPOT, stated because it bounds what this can answer: `COLLECT_RE` carries no `at`
    # field, so the collect-all pass populates `collect_primary`/`collect_cascade` with tags
    # ONLY. This detail channel therefore covers `reasons` alone — the strict first-fail prefix
    # — and is blind to the non-sole bodies whose full leaf demand only the collect-all pass
    # sees. Widening it means adding `at` to the collect-all event, not reading it from here.
    reason_details = collections.defaultdict(list)
    for m in SHAPE_RE.finditer(stderr):
        reasons[m.group("path")].append(m.group("what"))
        at = m.group("at")
        # `None`, never `""`. An empty string is a real value the compiler can emit for a
        # span-less tag; conflating it with "no detail recorded" would make the absent case
        # invisible in exactly the artifact built to make it visible.
        reason_details[m.group("path")].append(at if at else None)
    symbolic = {}
    opaque = {}
    for m in CLASS_RE.finditer(stderr):
        symbolic[m.group("path")] = m.group("symbolic") == "true"
        opaque[m.group("path")] = m.group("opaque") == "true"
    # Trust (extern-750 attribution): row-1 probe outcomes, joined to bodies by DefIndex (see
    # DEFIDX_RE for why not by leaf name). An index that resolves to two different paths, or a
    # probe whose index no body claims, is DROPPED and counted rather than guessed at — an
    # attribution that quietly mis-joins is worse than one that reports a hole.
    _idx_to_path, _idx_ambiguous = {}, set()
    for m in DEFIDX_RE.finditer(stderr):
        i, p = m.group("index"), m.group("path")
        if _idx_to_path.setdefault(i, p) != p:
            _idx_ambiguous.add(i)
    _row1, _row1_unjoined = {}, 0
    for m in ROW1_PROBE_RE.finditer(stderr):
        i = m.group("def_index")
        p = _idx_to_path.get(i)
        if p is None or i in _idx_ambiguous:
            _row1_unjoined += 1
            continue
        _row1[p] = {
            "outcome": m.group("outcome"),
            "samples": int(m.group("samples")),
            "declarations": int(m.group("declarations")),
        }
    collect_primary = collections.defaultdict(list)
    collect_cascade = collections.defaultdict(list)
    for m in COLLECT_RE.finditer(stderr):
        dst = collect_primary if m.group("cls") == "primary" else collect_cascade
        dst[m.group("path")].append([m.group("what"), int(m.group("n"))])
    bodies = {}
    dup_diff = 0
    for m in DIFF_RE.finditer(stderr):
        p = m.group("path")
        if p in bodies:
            dup_diff += 1
            continue
        note = m.group("note")
        mode = m.group("mode")
        body_reasons = reasons.get(p, [])
        body_details = reason_details.get(p, [])
        # Dedup the duplicated event pairs (same pattern-inline-const anomaly as the
        # count event): a body's reason list longer than its count is trimmed to count.
        #
        # Trust (slice 20 ride-along a): the detail list is trimmed IN LOCKSTEP, by the same
        # slice, in the same branch. The two lists are positionally paired — `reason_details[i]`
        # is the detail for `reasons[i]` — so trimming one without the other silently desyncs
        # tag from detail and every attribution read off the artifact afterwards points at the
        # wrong span. That is worse than not shipping the detail at all, because it is wrong
        # rather than absent.
        cnt = unsup.get(p, 0)
        if len(body_reasons) > cnt:
            body_reasons = body_reasons[:cnt]
            body_details = body_details[:cnt]
        bodies[p] = {
            "def": p,
            "kind": body_kind(p),
            "unsupported": cnt,
            "reasons": body_reasons,
            # Positionally paired with `reasons`; see the lockstep trim above.
            "reason_details": body_details,
            "equal": m.group("equal") == "true",
            "samples": int(m.group("samples")),
            "mode": mode,
            # Absent (older log, or a lane that skipped the class event) is reported as
            # None, NOT as False — "not measured" must stay distinguishable from "modelled".
            "symbolic": symbolic.get(p),
            "opaque_collapse": opaque.get(p),
            # Trust (extern-750 attribution): the row-1 probe outcome for this body, when the
            # producer emitted one. Absent means the probe did not run for this body — which
            # must stay distinguishable from "ran and found nothing", because the ONLY reason
            # this bucket has been costed off n=104 is that nobody could tell those apart.
            **({"row1_probe": _row1.get(p)} if _row1.get(p) else {}),
            # Trust (B8 step 1): the seam-blocker census is a STRUCTURED FIELD, parsed from the
            # FULL note here and never re-parsed from the stored one.
            #
            # `note` below is truncated to 160 chars. Measured on postbuild-b8-treat, ALL 1021
            # step-2 rows already hit that cap, and the longest surviving marker
            # (`[blockers: extern=1, havoc=1, local-unlowered=2]`) ends at offset 160 of 160 —
            # its closing `]` is the LAST CHARACTER RETAINED. The margin is ZERO, not small.
            # (An earlier reading of this put it at nine characters; that measured the longest
            # TWO-kind marker and missed the three-kind rows, which are longer and survived by
            # exactly nothing. Re-measure `max(end of marker)`, not a marker you picked.)
            # One more character anywhere before the marker loses the closing `]`,
            # at which point `parse_seam_blockers` returns {} and the row degrades to the LEGACY
            # MERGED CLASS. That failure is invisible in the worst way: the histogram shows
            # "some rows did not split", which reads as a partial wave rather than a broken
            # parse. Raising the cap would buy margin and leave the same bug for whoever adds a
            # fifth blocker kind. The note is for humans; the field is for the classifier.
            **({"seam_blockers": _seam_blockers} if (_seam_blockers := parse_seam_blockers(note)) else {}),
            "note_class": classify_note(mode, note, _seam_blockers),
            "note": note[:160],
            "collect_primary": collect_primary.get(p, []),
            "collect_cascade": collect_cascade.get(p, []),
        }
    orphan_unsup = [p for p in unsup if p not in bodies]
    anomalies = {
        "duplicate_differential_events": dup_diff,
        "duplicate_unsupported_events": dup_unsup,
        "unsupported_event_without_differential_event": orphan_unsup,
    }
    return list(bodies.values()), anomalies


def run_one(trustc: str, src: str, edition: str, timeout: int, with_flag: bool, scratch: str):
    """Compile one file; returns (exit_code_or_None_on_timeout, stderr)."""
    tmpdir = tempfile.mkdtemp(dir=scratch)
    env = dict(os.environ)
    env["RUSTC_LOG"] = RUSTC_LOG_FILTER
    env["RUST_BACKTRACE"] = "0"
    env["RUSTC_ICE"] = "0"
    argv = [trustc]
    if with_flag:
        argv += ["-Z", "trust-ir-lower"]
    argv += [
        "-Z", "trust-verify=off",  # producer-only measurement; hook is independent
        "--edition", edition,
        "--crate-type", "lib",
        "--emit=metadata",
        "--out-dir", tmpdir,
        "--cap-lints", "allow",
        src,
    ]
    try:
        # Trust: memory-capped, session-group-reaped compile (see `guarded_compile`) so a
        # trait-solver-overflow torture body can neither OOM the host nor orphan a runaway trustc.
        code, stderr = guarded_compile(argv, tmpdir, env, timeout)
        if code is None:
            return None, ""
        return code, stderr.decode("utf-8", errors="replace")
    finally:
        shutil.rmtree(tmpdir, ignore_errors=True)


def measure_file(trustc: str, src: str, edition: str, timeout: int, scratch: str):
    """Full outcome for one source file (control-run on failure)."""
    code, stderr = run_one(trustc, src, edition, timeout, True, scratch)
    if code == 0:
        bodies, anomalies = parse_bodies(stderr)
        return {
            "file": src,
            "outcome": "ok",
            "bodies": bodies,
            "anomalies": anomalies,
            # Trust (#181): per-class counts from the producer's self-validation tripwire, and
            # the total. `None` (absent summary) means NOT MEASURED — a pre-tripwire binary —
            # and must stay distinguishable from a measured zero, exactly as the body-class
            # `symbolic` field does.
            "validation": parse_validation(stderr),
        }
    if code is None:
        return {"file": src, "outcome": "timeout", "bodies": []}
    ice = code == 101 or "internal compiler error" in stderr
    # Control: does it compile standalone WITHOUT the producer flag?
    ctl_code, _ = run_one(trustc, src, edition, timeout, False, scratch)
    if ctl_code == 0:
        partial, anomalies = parse_bodies(stderr)
        outcome = "flag_induced_ice" if ice else "flag_induced_fail"
        sig = ""
        m = re.search(r"internal compiler error: [^\n]*", stderr)
        if m:
            # Normalize away the per-def payload so signatures dedup by crash site.
            sig = re.sub(r"\s*for DefPath.*", "", m.group(0))[:200]
        else:
            # Plain panics without an ICE banner (e.g. the DiagCtxt-drop
            # `trimmed_def_paths` assertion) — dedup by panic site + first message line.
            m = re.search(r"panicked at ([^\n:]+(?::\d+)*):\n([^\n]*)", stderr)
            if m:
                sig = f"panicked at {m.group(1)}: {m.group(2)}"[:200]
        return {
            "file": src, "outcome": outcome, "ice_signature": sig,
            "partial_bodies": partial, "bodies": [], "anomalies": anomalies,
        }
    if ctl_code is None:
        return {"file": src, "outcome": "timeout_control", "bodies": []}
    return {"file": src, "outcome": "compile_fail", "bodies": []}


def _eligible_ui_files(repo: str):
    """Walk tests/ui and apply the content filters. Returns (all_files, eligible,
    filter_stats), all absolute and sorted.

    ONE implementation, shared by the sweep and by `--check-ui-pins`: the check is
    worthless if it audits a population the sweep does not actually sample."""
    ui_root = os.path.join(repo, "tests", "ui")
    all_files = []
    for dirpath, _dirnames, filenames in os.walk(ui_root):
        if os.sep + "auxiliary" in dirpath or dirpath.endswith(os.sep + "auxiliary"):
            continue
        for f in filenames:
            if f.endswith(".rs"):
                all_files.append(os.path.join(dirpath, f))
    all_files.sort()  # determinism
    eligible, filter_stats = [], collections.Counter()
    for p in all_files:
        try:
            with open(p, encoding="utf-8", errors="replace") as fh:
                content = fh.read()
        except OSError:
            filter_stats["unreadable"] += 1
            continue
        hit = None
        for name, rx in UI_CONTENT_FILTERS:
            if rx.search(content):
                hit = name
                break
        if hit:
            filter_stats[hit] += 1
        else:
            eligible.append(p)
    return all_files, eligible, filter_stats


def collect_locked_corpus(repo: str, lock_path: str):
    """The corpus as PINNED BY CONTENT, bypassing sampling entirely.

    `random.sample` is a function of the population LENGTH, so the seeded
    corpus was only ever stable while `len(eligible)` was --- and it was not.
    See scripts/trust_ir_corpus_lock.py for the measured drift and for why the
    campaign-pin manifest could not prevent it (it governs tests/ui/trust/ only,
    while the population is all of tests/ui).

    Under a lock the corpus is the list, so nothing landing anywhere in the tree
    can move it, and a sweep is directly comparable to the artifact the lock was
    generated from. The content filters are NOT applied here: they are a
    selection heuristic for choosing files that compile standalone, not a
    measurement requirement, and re-applying them would silently drop locked
    files that later gained a `//~` annotation --- which is one of the drifts
    this exists to stop.
    """
    rows, missing = [], []
    with open(lock_path) as fh:
        for line in fh:
            line = line.rstrip("\n")
            if not line or line.startswith("#"):
                continue
            parts = line.split(None, 1)
            if len(parts) != 2:
                raise ValueError(f"malformed corpus-lock row: {line!r}")
            digest, rel = parts[0].strip(), parts[1].strip()
            abs_path = os.path.join(repo, rel)
            if not os.path.isfile(abs_path):
                missing.append(rel)
                continue
            rows.append((abs_path, rel, digest))
    if missing:
        raise UiPinManifestError(
            f"corpus lock names {len(missing)} file(s) that do not exist; the corpus "
            f"cannot be measured as specified. Re-check with "
            f"`python3 scripts/trust_ir_corpus_lock.py --check`:\n  - "
            + "\n  - ".join(missing[:20])
            + (f"\n  - ... and {len(missing) - 20} more" if len(missing) > 20 else "")
        )
    if not rows:
        raise UiPinManifestError("corpus lock names no files; refusing a vacuous sweep")

    drift = [rel for abs_path, rel, digest in rows
             if hashlib.sha256(open(abs_path, "rb").read()).hexdigest() != digest]
    sample = sorted(abs_path for abs_path, _, _ in rows)
    return sample, {
        "ui_root": os.path.relpath(os.path.join(repo, "tests", "ui"), repo),
        "selection": "corpus-lock",
        "corpus_lock": os.path.relpath(lock_path, repo),
        "locked_files": len(rows),
        "content_drift": len(drift),
        "content_drift_files": sorted(drift)[:50],
        "eligible": len(rows),
        "sampled": len(sample),
        "seed": None,
        "note": "corpus pinned by content; sampling bypassed, content filters not "
                "re-applied (they are a selection heuristic, not a measurement "
                "requirement)",
    }


def collect_ui_sample(repo: str, seed: int, size: int):
    """size <= 0 means FULL POPULATION: every eligible file, no sampling.
    (size >= len(eligible) also degenerates to the full population — the
    seeded sample of the whole set, sorted, is the whole set.)"""
    ui_root = os.path.join(repo, "tests", "ui")
    all_files, eligible, filter_stats = _eligible_ui_files(repo)
    # Trust (UI-pin tax paydown): drop the campaign pins from the population BEFORE
    # sampling. This is applied to the CONTENT-FILTERED list and by exact path, so the
    # surviving list is element-for-element what it would be if the pins were not in
    # the tree at all — which is what makes the sample identical to the hand-move
    # procedure's rather than merely the same size. The audit runs first and fails
    # closed: measuring a silently-widened population is worse than not measuring.
    excluded_pins, in_pool_pins = load_ui_pin_manifest()
    eligible_rel = [os.path.relpath(p, repo) for p in eligible]
    errors, notes = audit_ui_pin_manifest(repo, eligible_rel, excluded_pins, in_pool_pins)
    if errors:
        raise UiPinManifestError(
            "campaign-pin manifest is out of sync with the tree"
            f" ({os.path.relpath(UI_PIN_MANIFEST, repo)}):\n  - "
            + "\n  - ".join(errors)
        )
    pin_set = set(excluded_pins)
    kept = [p for p, rel in zip(eligible, eligible_rel) if rel not in pin_set]
    pins_removed = len(eligible) - len(kept)
    eligible = kept

    if size <= 0:
        sample = list(eligible)  # full population (already sorted)
    else:
        rnd = random.Random(seed)
        sample = sorted(rnd.sample(eligible, min(size, len(eligible))))
    return sample, {
        "ui_root": os.path.relpath(ui_root, repo),
        "total_rs_files_excl_auxiliary_dirs": len(all_files),
        "excluded_by_content_filter": dict(filter_stats),
        "campaign_pins_manifest": os.path.relpath(UI_PIN_MANIFEST, repo),
        "campaign_pins_listed": len(excluded_pins),
        "campaign_pins_excluded_from_pool": pins_removed,
        "campaign_pins_in_pool_classified": len(in_pool_pins),
        "campaign_pin_notes": notes,
        "eligible": len(eligible),
        "sampled": len(sample),
        "seed": seed,
        "filters": [f"{n}: /{r.pattern}/" for n, r in UI_CONTENT_FILTERS],
    }


_DECL_KIND_SOURCE = os.path.join("crates", "trust-thir-lower", "src", "crate_module.rs")


def scan_decl_kind_prefixes(repo):
    """The `DeclKind::prefix()` strings, read out of the Rust source.

    Trust (B8 step 1) — THE DRIFT GATE. `SEAM_BLOCKER_KINDS` is a mirror of a Rust enum, and a
    mirror nobody checks is a comment. If someone adds a sixth `DeclKind` variant, every body
    reaching it lands in `unclassified` and the split silently stops partitioning the class it
    exists to partition. Scanning the arms is cheap and catches that at edit time rather than one
    forty-minute sweep later.

    Deliberately narrow: it reads only the `match self` arms of `fn prefix`, so unrelated string
    literals in the file cannot manufacture a phantom class.
    """
    path = os.path.join(repo, _DECL_KIND_SOURCE)
    with open(path, encoding="utf-8") as f:
        src = f.read()
    m = re.search(r"fn prefix\(self\) -> &'static str \{\s*match self \{(.*?)\n        \}", src, re.S)
    if not m:
        raise RuntimeError(
            f"{_DECL_KIND_SOURCE}: could not locate `DeclKind::prefix`'s match block. The drift "
            f"gate cannot verify SEAM_BLOCKER_KINDS; fix the scan rather than deleting it."
        )
    return re.findall(r'DeclKind::\w+\s*=>\s*"([^"]+)"', m.group(1))


def check_seam_blockers(repo):
    """`--check-seam-blockers`: the taxonomy gate. No compiler, no artifact, ~0s."""
    errors = []
    try:
        rust = scan_decl_kind_prefixes(repo)
    except (OSError, RuntimeError) as e:
        print(f"SEAM-BLOCKER TAXONOMY: FAIL\n  {e}", file=sys.stderr)
        return 1
    if sorted(rust) != sorted(SEAM_BLOCKER_KINDS):
        errors.append(
            f"SEAM_BLOCKER_KINDS {sorted(SEAM_BLOCKER_KINDS)} != DeclKind::prefix() "
            f"{sorted(rust)} — the Python mirror has drifted from the Rust taxonomy"
        )
    if SEAM_BLOCKER_UNCLASSIFIED in rust:
        errors.append(
            f"{SEAM_BLOCKER_UNCLASSIFIED!r} is a reserved residue label and must not be a "
            f"DeclKind prefix"
        )
    # The dominance rule is a total order over the known classes; a duplicate would make the
    # partition order-dependent.
    if len(set(SEAM_BLOCKER_KINDS)) != len(SEAM_BLOCKER_KINDS):
        errors.append("SEAM_BLOCKER_KINDS contains a duplicate")
    if errors:
        print("SEAM-BLOCKER TAXONOMY: FAIL", file=sys.stderr)
        for e in errors:
            print(f"  {e}", file=sys.stderr)
        return 1
    print(
        f"SEAM-BLOCKER TAXONOMY: OK — {len(SEAM_BLOCKER_KINDS)} classes mirrored from "
        f"DeclKind ({', '.join(SEAM_BLOCKER_KINDS)}), tractability order least-tractable-first"
    )
    return 0


def _seam_note(marker=None):
    """A step-2 skip note exactly as `run_seam_differentials` spells it."""
    blockers = f" [blockers: {marker}]" if marker is not None else ""
    return (
        "seam-deferred body: reachable callee closure includes an extern/declaration-only "
        f"callee (no local body to link){blockers}; crate-seam interpretation not asserted "
        "(coverage-only)"
    )


def selftest_seam_blockers(repo):
    """`--selftest-seam-blockers`: the mutation proof that the split actually splits.

    A gate nobody has watched fail is a gate nobody knows is wired up — the repo's established
    style. Seven properties, each with the mutation that must break it.
    """
    fails = []

    def check(name, got, want):
        if got != want:
            fails.append(f"{name}: got {got!r}, want {want!r}")

    modelled = {"symbolic": False, "opaque_collapse": False}

    # 1. Every class round-trips from a real note, and lands in its own class.
    for kind in SEAM_BLOCKER_KINDS:
        note = _seam_note(f"{kind}=1")
        check(f"parse[{kind}]", parse_seam_blockers(note), {kind: 1})
        check(f"classify[{kind}]", classify_note("NotRun", note), f"clean-skip-seam-decl-{kind}")

    # 2. A pre-split note keeps the legacy merged class. MUTATION: returning a split class here
    #    would silently re-label every historical artifact.
    check("legacy", classify_note("NotRun", _seam_note()), "clean-skip-extern-callee")
    check("legacy-parse", parse_seam_blockers(_seam_note()), {})

    # 3. Dominance is least-tractable-first, not first-seen and not alphabetical.
    check(
        "dominance",
        seam_blocker_dominant({"local-unlowered": 3, "extern": 1}),
        "extern",
    )
    check("dominance-order", seam_blocker_dominant({"ambiguous": 1, "havoc": 1}), "havoc")

    # 4. An unknown class wins outright — it may never hide behind a known co-blocker.
    check("stranger", seam_blocker_dominant({"extern": 1, "brand-new": 1}), "unclassified")
    check("stranger-alone", seam_blocker_dominant({"brand-new": 1}), "unclassified")
    check(
        "stranger-classify",
        classify_note("NotRun", _seam_note("extern=1, brand-new=1")),
        "clean-skip-seam-decl-unclassified",
    )

    # 5. The partition is a partition: dominant sums to rows_split, over a mixed population.
    bodies = (
        [dict(note=_seam_note("extern=2"), **modelled) for _ in range(5)]
        + [dict(note=_seam_note("local-unlowered=1"), **modelled) for _ in range(3)]
        + [dict(note=_seam_note("extern=1, havoc=1"), **modelled) for _ in range(2)]
        + [dict(note=_seam_note("havoc=1"), symbolic=False, opaque_collapse=True)]
        + [dict(note=_seam_note(), **modelled)]  # pre-split row
        + [dict(note="an unrelated skip", **modelled)]
    )
    c = seam_blocker_census(bodies)
    check("census.rows_total", c["rows_total"], 12)
    check("census.rows_split", c["rows_split"], 11)
    check("census.rows_legacy", c["rows_legacy_unsplit"], 1)
    check("census.sums", c["dominant_sums"], c["rows_split"])
    check("census.dominant", c["dominant"], {"extern": 7, "local-unlowered": 3, "havoc": 1})
    # `dominant` counts ALL clean rows at the gate; `dominant_modelled` drops the OPAQUE-COLLAPSE
    # one. This is the 983-vs-919 relationship in miniature, and getting it backwards is how the
    # gap would be quoted against the wrong denominator.
    check("census.modelled", c["dominant_modelled"], {"extern": 7, "local-unlowered": 3})
    # SOLE excludes the two co-blocked rows; participation includes them. The pair is the point.
    check("census.sole", c["sole_blocker"], {"extern": 5, "local-unlowered": 3, "havoc": 1})
    check(
        "census.participation",
        c["participation"],
        {"extern": 7, "local-unlowered": 3, "havoc": 3},
    )
    check(
        "census.combinations",
        c["combinations"],
        {"extern": 5, "local-unlowered": 3, "extern+havoc": 2, "havoc": 1},
    )

    # 6. Counts are parsed, not merely presence-detected.
    check("counts", parse_seam_blockers(_seam_note("extern=12, havoc=3")), {"extern": 12, "havoc": 3})

    # 7. The marker must not leak into a NEIGHBOURING classifier rule. `havoc` is a substring
    #    trigger for `clean-skip-oracle-havoc` further down the chain, and `extern=` sits inside a
    #    note the `direct call` rule also scans.
    check(
        "no-rule-bleed",
        classify_note("NotRun", _seam_note("havoc=1")),
        "clean-skip-seam-decl-havoc",
    )

    # 8. THE TRUNCATION TRAP, pinned as a property rather than left to luck.
    #    The stored note is `note[:160]`; measured on postbuild-b8-treat every one of the 1021
    #    step-2 rows already hits that cap, with the longest surviving marker ending at 151 — nine
    #    characters of headroom. These two assertions encode both halves: a truncated note DOES
    #    silently degrade to the legacy merged class, and the structured field is immune to it.
    full = _seam_note("extern=1, local-unlowered=1, ambiguous=1")
    truncated = full[:160]
    check("truncation-loses-marker", parse_seam_blockers(truncated), {})
    check(
        "truncation-degrades-to-legacy",
        classify_note("NotRun", truncated),
        "clean-skip-extern-callee",
    )
    # The field survives what the note cannot — this is the whole reason the field exists.
    field = parse_seam_blockers(full)
    check(
        "field-survives-truncation",
        classify_note("NotRun", truncated, field),
        "clean-skip-seam-decl-extern",
    )
    # And the census prefers the field over a mangled note.
    c2 = seam_blocker_census([dict(note=truncated, seam_blockers=field, **modelled)])
    check("census-prefers-field", c2["dominant"], {"extern": 1})
    check("census-field-not-legacy", c2["rows_legacy_unsplit"], 0)

    if fails:
        print("SEAM-BLOCKER SELFTEST: FAIL", file=sys.stderr)
        for f in fails:
            print(f"  {f}", file=sys.stderr)
        return 1
    print("SEAM-BLOCKER SELFTEST: OK — 8 properties, taxonomy mirrored, partition checked, "
          "truncation trap pinned")
    return check_seam_blockers(repo)


def check_ui_pins(repo):
    """Standalone audit of the campaign-pin manifest (`--check-ui-pins`).

    Runs the sampler's file-selection path only — no compilation, no built trustc,
    about a second. This is the gate a slice runs after adding its regression test,
    instead of discovering at the end of a 40-minute sweep that the sample moved."""
    try:
        excluded, in_pool = load_ui_pin_manifest()
    except UiPinManifestError as e:
        print(f"UI-PIN MANIFEST: FAIL\n  {e}", file=sys.stderr)
        return 1
    eligible_rel = [os.path.relpath(p, repo) for p in _eligible_ui_files(repo)[1]]
    eligible_rel.sort()
    errors, notes = audit_ui_pin_manifest(repo, eligible_rel, excluded, in_pool)
    pin_prefix = UI_PIN_DIR + os.sep
    in_dir = [p for p in eligible_rel if p.startswith(pin_prefix)]
    removed = sum(1 for p in eligible_rel if p in set(excluded))
    print(f"manifest:  {os.path.relpath(UI_PIN_MANIFEST, repo)}")
    print(f"eligible:  {len(eligible_rel)} total · {len(in_dir)} under {UI_PIN_DIR}")
    print(f"excluded:  {len(excluded)} listed · {removed} of them in the eligible population")
    print(f"in-pool:   {len(in_pool)} classified")
    print(f"sampling population after exclusion: {len(eligible_rel) - removed}")
    for note in notes:
        print(f"note: {note}")
    if errors:
        print("UI-PIN MANIFEST: FAIL", file=sys.stderr)
        for e in errors:
            print(f"  - {e}", file=sys.stderr)
        return 1
    print("UI-PIN MANIFEST: OK")
    return 0


def selftest_ui_pins(repo):
    """Mutation proof that the manifest audit is not decorative (`--selftest-ui-pins`).

    An audit that always returns no errors would pass every check above and silently
    reinstate the whole defect. Each case below breaks the manifest in one way and
    REQUIRES an error; a "simplification" that neuters the audit fails here instead of
    being discovered by a sweep whose numbers are quietly incomparable."""
    excluded, in_pool = load_ui_pin_manifest()
    eligible = sorted(os.path.relpath(p, repo) for p in _eligible_ui_files(repo)[1])
    if not excluded:
        print("SELFTEST: FAIL — [excluded] is empty, nothing to mutate", file=sys.stderr)
        return 1
    victim = excluded[-1]
    cases = [
        ("a pin dropped from [excluded]",
         [p for p in excluded if p != victim], in_pool),
        ("a stale entry naming a file that does not exist",
         excluded + [os.path.join(UI_PIN_DIR, "__selftest_absent__.rs")], in_pool),
        ("one file listed in both sections",
         excluded, in_pool + [excluded[0]]),
    ]
    # Each mutation must produce an error the UNMUTATED manifest does not already
    # produce. Comparing against the baseline rather than against "no errors at all"
    # keeps this proof independent of ambient tree state — an unrelated unclassified
    # file (another lane's new test) is `--check-ui-pins`' business, not the audit's
    # own correctness — while still refuting an audit that errors unconditionally.
    baseline, _ = audit_ui_pin_manifest(repo, eligible, excluded, in_pool)
    base_set = set(baseline)
    print(f"  baseline: the unmutated manifest reports {len(baseline)} error(s)"
          " (unrelated to this proof; run --check-ui-pins to act on them)")
    ok = True
    for label, exc, pool in cases:
        errors, _ = audit_ui_pin_manifest(repo, eligible, exc, pool)
        new = [e for e in errors if e not in base_set]
        if not new:
            ok = False
        print(f"  [{'ok ' if new else 'BAD'}] {label}: "
              + (f"audit raises a new error — {new[0].split(':')[0]}" if new
                 else "audit is SILENT about it"))
    print("UI-PIN SELFTEST: " + ("OK" if ok else "FAIL"), file=sys.stdout if ok else sys.stderr)
    return 0 if ok else 1


def aggregate(results):
    """Aggregate a list of per-file results into corpus-level stats."""
    files = collections.Counter(r["outcome"] for r in results)
    bodies = [b for r in results for b in r.get("bodies", [])]
    partial = [b for r in results for b in r.get("partial_bodies", [])]

    def body_stats(bs):
        clean = [b for b in bs if b["unsupported"] == 0]
        hist = collections.Counter(b["unsupported"] for b in bs)
        tag_hist = collections.Counter(t for b in bs for t in b.get("reasons", []))
        single = collections.Counter(
            b["reasons"][0] for b in bs
            if b["unsupported"] == 1 and len(b.get("reasons", [])) == 1)
        return {
            "reason_tag_histogram": dict(tag_hist.most_common()),
            "single_missing_shape_tag_histogram": dict(single.most_common()),
            "total": len(bs),
            "lowered_clean": len(clean),
            "lowered_clean_pct": round(100.0 * len(clean) / len(bs), 1) if bs else None,
            # Trust (measurement honesty): split the clean population. A SYMBOLIC clean body
            # lowered without a fail-closed tag but carries an opaque, value-less placeholder,
            # so it is refused by the executable SPLICE (`crate_module.rs`: `symbolic` gates
            # `splice_ok`; `opaque_collapse`, deliberately, does not) — it can never run.
            # Converting a tag into an opaque spelling therefore moves a body between these
            # lines without closing a gap; reporting only the sum would make that read as
            # progress.
            #
            # CORRECTED 2026-08-19 — this comment, and the SCORECARD.md line it fed, both said
            # a SYMBOLIC body "can never be `Agreed`". That is FALSE and was false before it
            # was written: measured on `postbuild-slice20-control`, 64 of 440 clean SYMBOLIC
            # bodies are `Agreed`. The differential is not categorically closed to them — where
            # it can ENUMERATE the placeholder (the vtable-slice-10 const-param/assoc-const
            # sample column: `usize`/`u32`/`u8`/`bool` sampled at N values) or PROVE it is never
            # read ("proven-never-read opaque param(s) as placeholders"), the row is sampled and
            # can Agree. What is true of SYMBOLIC is the splice refusal, not an Agreed refusal.
            # The companion asymmetry is real and worth stating: 0 of 370 OPAQUE-COLLAPSE bodies
            # are Agreed (0 of the 115 clean ones), because a COLLAPSED LIVE VALUE cannot be
            # enumerated the way an absent one can.
            #
            # So the renderer now prints the MEASURED per-class Agreed split instead of a prose
            # claim about what is possible. A wrong label is how this propagated into three
            # lanes' rankings; a measured number cannot go stale in the same way.
            #
            # Trust (#173): three-way, most-dishonest-wins. A body can be BOTH symbolic and
            # opaque-collapsed; it is counted once, under symbolic, so the three lines sum to
            # `lowered_clean`. MODELLED is now the residual: tag-free AND no opaque carrier AND
            # no collapsed live value.
            "lowered_clean_symbolic": sum(1 for b in clean if b.get("symbolic") is True),
            "lowered_clean_symbolic_agreed": sum(
                1 for b in clean if b.get("symbolic") is True and b["mode"] == "Agreed"
            ),
            "lowered_clean_opaque": sum(
                1 for b in clean
                if b.get("symbolic") is False and b.get("opaque_collapse") is True
            ),
            "lowered_clean_opaque_agreed": sum(
                1 for b in clean
                if b.get("symbolic") is False and b.get("opaque_collapse") is True
                and b["mode"] == "Agreed"
            ),
            "lowered_clean_modelled": sum(
                1 for b in clean
                if b.get("symbolic") is False and b.get("opaque_collapse") is False
            ),
            "lowered_clean_modelled_agreed": sum(
                1 for b in clean
                if b.get("symbolic") is False and b.get("opaque_collapse") is False
                and b["mode"] == "Agreed"
            ),
            # The whole-body opaque-collapse population, clean or not — the denominator the
            # "0 Agreed" asymmetry above is stated over. `lowered_clean_opaque` is its
            # clean-and-not-also-symbolic subset and answers a different question.
            "opaque_collapse_all": sum(1 for b in bs if b.get("opaque_collapse") is True),
            "opaque_collapse_all_agreed": sum(
                1 for b in bs if b.get("opaque_collapse") is True and b["mode"] == "Agreed"
            ),
            "lowered_clean_class_unmeasured": sum(1 for b in clean if b.get("symbolic") is None),
            "by_kind": dict(collections.Counter(b["kind"] for b in bs)),
            "clean_by_kind": dict(collections.Counter(b["kind"] for b in clean)),
            "note_class_histogram": dict(collections.Counter(b["note_class"] for b in bs)),
            # Trust (B8 step 1): the internal structure of what used to be the corpus's largest
            # anonymous class. Keyed off the note, so it re-derives from any artifact — including
            # pre-split ones, which report `rows_legacy_unsplit` and nothing else.
            "seam_declaration_blockers": seam_blocker_census(bs),
            "unsupported_count_per_body_histogram": {str(k): v for k, v in sorted(hist.items())},
            "agreed": sum(1 for b in bs if b["mode"] == "Agreed"),
            "divergences": sorted(b["def"] for b in bs if b["mode"] == "MirOracle"),
            "divergence_note_histogram": dict(collections.Counter(
                b["note"] for b in bs if b["mode"] == "MirOracle")),
        }

    # Trust (#181): MODULE-level validation, from the producer's self-validation tripwire. This is

    # a different denominator from every body-level number above — a MODULE is one compiled file,

    # a body is one fn. Never mix them: "31% of modules fail" and "132 error occurrences" describe

    # different things, and conflating them mis-scoped this work once already.

    # `measured` counts files whose binary actually emitted the tripwire; a file with no summary

    # event is NOT counted as passing.

    _val = [r.get("validation") for r in results if r.get("outcome") == "ok"]

    _val_measured = [v for v in _val if v is not None]

    validation = {

        "modules_measured": len(_val_measured),

        "modules_unmeasured": sum(1 for v in _val if v is None),

        "modules_invalid": sum(1 for v in _val_measured if v["total"] > 0),

        "error_occurrences": sum(v["total"] for v in _val_measured),

    }

    _cls = collections.Counter()

    for v in _val_measured:

        for k, c in v["classes"].items():

            _cls[k] += c

    validation["class_histogram"] = dict(_cls.most_common())

    ices = collections.Counter(
        r.get("ice_signature", "") for r in results
        if r["outcome"].startswith("flag_induced") and r.get("ice_signature"))
    combined = bodies + partial
    combined_clean = sum(1 for b in combined if b["unsupported"] == 0)
    anom = collections.Counter()
    for r in results:
        a = r.get("anomalies")
        if a:
            anom["duplicate_differential_events"] += a["duplicate_differential_events"]
            anom["duplicate_unsupported_events"] += a["duplicate_unsupported_events"]
            anom["unsupported_event_without_differential_event"] += len(
                a["unsupported_event_without_differential_event"])
    return {
        "file_outcomes": dict(files),
        # Trust (#181): MODULE-level well-formedness, from the producer's self-validation
        # tripwire. Sibling of, never merged into, the body-level stats below — a MODULE is one
        # compiled file, a BODY is one fn, and reporting an occurrence count against a module
        # denominator mis-scoped this work once already.
        "validation": validation,
        "bodies": body_stats(bodies),
        "partial_bodies_from_flag_induced_failures": body_stats(partial),
        "bodies_including_partial": {
            "total": len(combined),
            "lowered_clean": combined_clean,
            "lowered_clean_pct": round(100.0 * combined_clean / len(combined), 1)
            if combined else None,
        },
        "flag_induced_ice_signatures": dict(ices),
        "parse_anomalies": dict(anom),
    }


def provenance(trustc: str, repo: str, args):
    ver = subprocess.run([trustc, "--version", "--verbose"],
                         capture_output=True, text=True).stdout.strip()
    def git(*a):
        return subprocess.run(["git", "-C", repo, *a],
                              capture_output=True, text=True).stdout.strip()
    return {
        "trustc": trustc,
        "trustc_version_verbose": ver,
        "repo_head": git("rev-parse", "HEAD"),
        "repo_describe": git("describe", "--always", "--dirty"),
        "date_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
        "host": platform.platform(),
        "rustc_log_filter": RUSTC_LOG_FILTER,
        "compile_flags": [
            "-Z trust-ir-lower", "-Z trust-verify=off", f"--edition {args.edition}",
            "--crate-type lib", "--emit=metadata", "--cap-lints allow",
        ],
        "seed": args.seed,
        "sample_size_requested": args.sample_size,
        "timeout_per_file_s": args.timeout,
        "jobs": args.jobs,
    }


def render_markdown(data):
    """Generate SCORECARD.md content from the aggregated JSON."""
    out = []
    p = data["provenance"]
    out.append("# trust-ir producer scorecard\n")
    out.append(f"Generated {p['date_utc']} · trustc `{p['repo_describe']}` · seed {p['seed']}\n")
    for name, corpus in data["corpora"].items():
        agg = corpus["aggregate"]
        b = agg["bodies"]
        out.append(f"\n## corpus: {name}\n")
        meta = corpus.get("sample_meta") or {}
        if "campaign_pins_excluded_from_pool" in meta:
            # Self-describing: the sampling population is the whole basis of
            # cross-sweep comparability, so state it in the artifact itself.
            out.append(
                f"- sampling population: **{meta['eligible']}** eligible"
                f" (of {meta['total_rs_files_excl_auxiliary_dirs']} .rs files),"
                f" sampled **{meta['sampled']}** at seed {meta['seed']}"
            )
            out.append(
                f"- campaign UI pins held out of the population:"
                f" **{meta['campaign_pins_excluded_from_pool']}**"
                f" (of {meta['campaign_pins_listed']} listed in"
                f" `{meta['campaign_pins_manifest']}`;"
                f" the rest are already removed by the content filters)"
            )
        out.append(f"- file outcomes: `{agg['file_outcomes']}`")
        out.append(f"- bodies reached (in files that fully compiled under the flag): **{b['total']}**")
        out.append(f"- lowered clean (0 unsupported shapes): **{b['lowered_clean']}"
                   f" ({b['lowered_clean_pct']}%)**")
        if b.get("lowered_clean_symbolic") is not None:
            unm = b.get("lowered_clean_class_unmeasured", 0)
            unm_s = f" · class-unmeasured {unm}" if unm else ""

            # MEASURED, not asserted. The previous text claimed a SYMBOLIC body "can never be
            # Agreed"; 64 of 440 were, in the artifact that sentence was last printed over. A
            # per-class `n Agreed` is checkable against data.json and cannot rot into a rule.
            def _cls(name, n, agreed, gloss):
                r = f" ({agreed} Agreed, {round(100.0 * agreed / n, 1)}%)" if n else ""
                return f"{name} {n}{r} — {gloss}"

            out.append(
                "  - of which "
                + _cls("MODELLED", b["lowered_clean_modelled"],
                       b.get("lowered_clean_modelled_agreed", 0),
                       "no opaque carrier, no collapsed live value; the only class that is "
                       "both spliceable and freely sampleable")
                + "\n    · "
                + _cls("SYMBOLIC", b["lowered_clean_symbolic"],
                       b.get("lowered_clean_symbolic_agreed", 0),
                       "carries a value-less opaque placeholder. REFUSED BY THE SPLICE "
                       "(`symbolic` gates `splice_ok`) — it can never run. NOT refused by the "
                       "differential: where the placeholder can be enumerated (const-param / "
                       "assoc-const sample column) or proven never read, the row is sampled "
                       "and can Agree")
                + "\n    · "
                + _cls("OPAQUE-COLLAPSE", b.get("lowered_clean_opaque", 0),
                       b.get("lowered_clean_opaque_agreed", 0),
                       "a LIVE value typed as a placeholder; the differential refuses to "
                       "sample it, and a collapsed live value cannot be enumerated the way an "
                       "absent one can")
                + unm_s
            )
            oc_n = b.get("opaque_collapse_all")
            if oc_n is not None:
                out.append(
                    f"  - opaque-collapse population (clean or not): {oc_n},"
                    f" of which Agreed {b.get('opaque_collapse_all_agreed', 0)}"
                    f" — the asymmetry against SYMBOLIC above is the measurement, not a rule"
                )
        v = agg.get("validation")
        if v and (v["modules_measured"] or v["modules_unmeasured"]):
            unm = f", {v['modules_unmeasured']} UNMEASURED" if v["modules_unmeasured"] else ""
            out.append(
                f"- module well-formedness (`validate_module` on the assembled module):"
                f" **{v['modules_invalid']} of {v['modules_measured']} INVALID**"
                f" ({v['error_occurrences']} error occurrences){unm}"
            )
            if v["class_histogram"]:
                out.append(f"  - by class: {v['class_histogram']}")
        out.append(f"- by kind: {b['by_kind']} (clean: {b['clean_by_kind']})")
        out.append(f"- note-class histogram: {b['note_class_histogram']}")
        sdb = b.get("seam_declaration_blockers") or {}
        if sdb.get("rows_total"):
            out.append(
                f"- seam declaration-gate blockers: **{sdb['rows_total']} rows**"
                f" ({sdb['rows_split']} split, {sdb['rows_legacy_unsplit']} pre-split)"
            )
            if sdb.get("rows_split"):
                # The partition gate, rendered rather than asserted: a reader can check it.
                ok = "OK" if sdb["dominant_sums"] == sdb["rows_split"] else "**BROKEN**"
                out.append(
                    f"  - dominant (least-tractable present; sums to rows_split: {ok}):"
                    f" {sdb['dominant']}"
                )
                out.append(f"  - dominant, MODELLED rows only: {sdb['dominant_modelled']}")
                out.append(
                    f"  - SOLE blocker (rank against THIS — what retiring the class alone"
                    f" recovers): {sdb['sole_blocker']}"
                )
                out.append(f"  - participation (appears at all): {sdb['participation']}")
                out.append(f"  - co-occurrence sets: {sdb['combinations']}")
                unc = sdb["dominant"].get(SEAM_BLOCKER_UNCLASSIFIED, 0)
                if unc:
                    out.append(
                        f"  - **UNCLASSIFIED {unc}** — the producer named a declaration class"
                        f" this taxonomy does not know. `DeclKind` and `SEAM_BLOCKER_KINDS`"
                        f" have drifted; this is a finding, not a rounding error."
                    )
        tags = list(b["reason_tag_histogram"].items())
        if tags:
            out.append(f"- reason-tag histogram (top 20 of {len(tags)}): {dict(tags[:20])}")
            out.append(f"- single-missing-shape tag histogram (top 20): "
                       f"{dict(list(b['single_missing_shape_tag_histogram'].items())[:20])}")
        out.append(f"- unsupported-count-per-body: {b['unsupported_count_per_body_histogram']}")
        div = b["divergences"]
        div_shown = div[:10] + ([f"... +{len(div) - 10} more"] if len(div) > 10 else [])
        out.append(f"- differential Agreed: {b['agreed']}; divergences ({len(div)}): {div_shown}")
        if b["divergence_note_histogram"]:
            out.append(f"- divergence notes: {b['divergence_note_histogram']}")
        pb = agg["partial_bodies_from_flag_induced_failures"]
        if pb["total"]:
            out.append(f"- partial bodies observed before flag-induced aborts: {pb['total']}"
                       f" (clean {pb['lowered_clean']})")
            cp = agg["bodies_including_partial"]
            out.append(f"- bodies including partial: {cp['total']}, clean {cp['lowered_clean']}"
                       f" ({cp['lowered_clean_pct']}%)")
        if agg["flag_induced_ice_signatures"]:
            out.append(f"- flag-induced ICE signatures (normalized, by file count): "
                       f"{agg['flag_induced_ice_signatures']}")
        if any(agg["parse_anomalies"].values()):
            out.append(f"- PARSE ANOMALIES: {agg['parse_anomalies']}")
    out.append("\n(Per-body rows and full provenance: data.json.)\n")
    return "\n".join(out)


def rerender(out_dir: str, check_only: bool = False) -> int:
    """Recompute the aggregate + SCORECARD.md from an artifact's stored per-body rows.

    Every number on the scorecard is a pure function of `corpora[*].files`, which data.json
    already stores in full. So a reporting change — a corrected label, a new split, a fixed
    denominator — is verifiable on the artifacts already on disk, at zero compile cost. It
    does not re-run the producer and cannot change what was measured; it only changes how the
    measurement is stated.
    """
    path = out_dir if out_dir.endswith(".json") else os.path.join(out_dir, "data.json")
    with open(path) as fh:
        data = json.load(fh)
    diffs = []

    def walk(path, old, new):
        # Compare only keys the STORED artifact already has, recursively: a key this build
        # ADDS is a reporting improvement, not a disagreement about the measured rows.
        if isinstance(old, dict) and isinstance(new, dict):
            for k in sorted(old):
                if k not in new:
                    diffs.append(f"{path}.{k}: stored key DROPPED by this build")
                else:
                    walk(f"{path}.{k}", old[k], new[k])
        elif old != new:
            diffs.append(f"{path}: stored {old!r} != recomputed {new!r}")

    for name, corpus in data.get("corpora", {}).items():
        new = aggregate(corpus["files"])
        walk(name, corpus.get("aggregate", {}), new)
        corpus["aggregate"] = new
    if check_only:
        for d in diffs:
            print("MISMATCH " + d)
        print(f"rerender-check: {len(diffs)} disagreement(s) between stored and recomputed"
              f" aggregate keys")
        return 1 if diffs else 0
    if diffs:
        # A recomputation that CHANGES an existing key means the artifact and this script
        # disagree about the stored rows — say so loudly rather than overwrite in silence.
        for d in diffs:
            print("WARNING recomputed value differs: " + d)
    d = os.path.dirname(path) or "."
    with open(path, "w") as fh:
        json.dump(data, fh, indent=1)
    with open(os.path.join(d, "SCORECARD.md"), "w") as fh:
        fh.write(render_markdown(data))
    print(f"re-rendered {path} and {os.path.join(d, 'SCORECARD.md')} from stored rows")
    return 0


def main():
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--trustc", help="required unless --check-ui-pins")
    ap.add_argument("--repo", default=os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
    ap.add_argument("--out-dir", help="required unless --check-ui-pins")
    ap.add_argument("--seed", type=int, default=20260701)
    ap.add_argument("--sample-size", type=int, default=2000,
                    help="seeded ui-sample size; 0 = FULL population (all eligible)")
    ap.add_argument("--jobs", type=int, default=8)
    ap.add_argument("--timeout", type=int, default=60)
    ap.add_argument("--edition", default="2021")
    ap.add_argument("--no-ui-sample", action="store_true")
    ap.add_argument(
        "--corpus-lock", metavar="PATH", default=None,
        help="measure the corpus PINNED BY CONTENT in PATH (see "
             "scripts/trust_ir_corpus_lock.py) instead of re-deriving it with a "
             "seeded sample. The seeded sample is a function of the eligible "
             "population LENGTH and so was never stable; a lock makes a sweep "
             "directly comparable to the artifact the lock was generated from.")
    ap.add_argument("--corpus", action="append", default=[],
                    metavar="NAME=PATH", help="extra single-file corpus (repeatable)")
    ap.add_argument("--scratch", default=None,
                    help="scratch dir for per-run --out-dir temp dirs (default: mkdtemp)")
    ap.add_argument("--check-ui-pins", action="store_true",
                    help="audit the tests/ui/trust campaign-pin manifest against the tree and "
                         "exit; runs the sampler's file-selection path only (no compilation, "
                         "no --trustc needed, ~1s)")
    ap.add_argument("--selftest-ui-pins", action="store_true",
                    help="mutation proof that the manifest audit actually fails on a broken "
                         "manifest (does not modify anything on disk)")
    ap.add_argument("--check-seam-blockers", action="store_true",
                    help="verify SEAM_BLOCKER_KINDS still mirrors `DeclKind` in "
                         "crates/trust-thir-lower/src/crate_module.rs and exit (no compiler, "
                         "no artifact, ~0s)")
    ap.add_argument("--selftest-seam-blockers", action="store_true",
                    help="mutation proof that the declaration-blocker split actually splits "
                         "(also runs --check-seam-blockers)")
    ap.add_argument("--rerender", metavar="DIR",
                    help="recompute `aggregate` and rewrite SCORECARD.md from an EXISTING "
                         "postbuild dir's data.json per-body rows. No compiler, no corpus "
                         "sweep. This is how a reporting fix is verified: the wrong SYMBOLIC "
                         "label shipped in every artifact for weeks partly because correcting "
                         "it appeared to cost a full sweep.")
    ap.add_argument("--rerender-check", action="store_true",
                    help="with --rerender: do not write, only report whether the stored "
                         "aggregate differs from the recomputed one (exit 1 if it does, "
                         "ignoring keys this build newly adds)")
    args = ap.parse_args()

    # These are standalone gates: they must be runnable without a built compiler,
    # so --trustc is validated here rather than by argparse.
    if args.check_ui_pins:
        return check_ui_pins(os.path.abspath(args.repo))
    if args.selftest_ui_pins:
        return selftest_ui_pins(os.path.abspath(args.repo))
    if args.check_seam_blockers:
        return check_seam_blockers(os.path.abspath(args.repo))
    if args.selftest_seam_blockers:
        return selftest_seam_blockers(os.path.abspath(args.repo))
    if args.rerender:
        return rerender(args.rerender, check_only=args.rerender_check)
    if not args.trustc:
        ap.error("the following arguments are required: --trustc")
    if not args.out_dir:
        ap.error("the following arguments are required: --out-dir")

    trustc = os.path.abspath(args.trustc)
    repo = os.path.abspath(args.repo)
    os.makedirs(args.out_dir, exist_ok=True)
    scratch = args.scratch or tempfile.mkdtemp(prefix="trust-ir-scorecard-")
    os.makedirs(scratch, exist_ok=True)

    data = {
        "schema": "trust.trust-ir.producer-scorecard.v1",
        "provenance": provenance(trustc, repo, args),
        "corpora": {},
    }

    corpora = []
    for spec in args.corpus:
        name, _, path = spec.partition("=")
        corpora.append((name, [os.path.abspath(path)], None))
    if not args.no_ui_sample:
        if args.corpus_lock:
            sample, sample_meta = collect_locked_corpus(repo, args.corpus_lock)
        else:
            sample, sample_meta = collect_ui_sample(repo, args.seed, args.sample_size)
        # Self-describing run: a sweep that silently sampled a different population is
        # the failure mode this line exists to make visible in the log.
        if sample_meta.get("selection") == "corpus-lock":
            print(
                f"[ui_sample] CORPUS LOCK {sample_meta['corpus_lock']}"
                f" · {sample_meta['locked_files']} file(s) pinned by content"
                f" · content drift {sample_meta['content_drift']}"
                f" · sampling bypassed (comparable to the artifact the lock came from)",
                flush=True,
            )
            for rel in sample_meta.get("content_drift_files", [])[:10]:
                print(f"[ui_sample] drift: {rel}", flush=True)
        else:
            print(
                f"[ui_sample] eligible {sample_meta['eligible']}"
                f" · sampled {sample_meta['sampled']}"
                f" · campaign pins excluded from the pool"
                f" {sample_meta['campaign_pins_excluded_from_pool']}"
                f" of {sample_meta['campaign_pins_listed']} listed"
                f" ({sample_meta['campaign_pins_manifest']})",
                flush=True,
            )
        for note in sample_meta.get("campaign_pin_notes", []):
            print(f"[ui_sample] note: {note}", flush=True)
        corpora.append(("ui_sample", sample, sample_meta))

    for name, files, meta in corpora:
        print(f"[{name}] compiling {len(files)} file(s) with -P{args.jobs} ...", flush=True)
        results = []
        with concurrent.futures.ThreadPoolExecutor(max_workers=args.jobs) as ex:
            futs = {ex.submit(measure_file, trustc, f, args.edition, args.timeout, scratch): f
                    for f in files}
            for i, fut in enumerate(concurrent.futures.as_completed(futs)):
                results.append(fut.result())
                if (i + 1) % 200 == 0:
                    print(f"  {i + 1}/{len(files)}", flush=True)
        results.sort(key=lambda r: r["file"])
        for r in results:  # store repo-relative paths
            r["file"] = os.path.relpath(r["file"], repo)
        data["corpora"][name] = {
            "sample_meta": meta,
            "aggregate": aggregate(results),
            "files": results,
        }
        print(f"[{name}] {data['corpora'][name]['aggregate']['file_outcomes']}", flush=True)

    with open(os.path.join(args.out_dir, "data.json"), "w") as fh:
        json.dump(data, fh, indent=1)
    with open(os.path.join(args.out_dir, "SCORECARD.md"), "w") as fh:
        fh.write(render_markdown(data))
    shutil.rmtree(scratch, ignore_errors=True)
    print(f"wrote {args.out_dir}/data.json and {args.out_dir}/SCORECARD.md")


if __name__ == "__main__":
    sys.exit(main())
