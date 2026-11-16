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
  * Inputs and expected outcomes are fixed before compiling. Every file gets
    metadata and codegen control/subject pairs; a control failure cannot change
    the expected outcome or silently remove a file from the input census.
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
    file listed in NEITHER manifest section is held out exactly as an [excluded]
    entry is (2026-09-23): only [in-pool] admits a tests/ui/trust file, so a new
    regression test can never reshuffle the sample and needs no registration.
    Audit the manifest in ~1s without sweeping:

        python3 scripts/trust_ir_producer_scorecard.py --check-ui-pins
        python3 scripts/trust_ir_producer_scorecard.py --selftest-ui-pins

Usage (the flags of the 2026-07-01 baseline, which also ran a closure-free
variant of realcode.rs; that variant worked around a -Z trust-ir-lower ICE on
closure bodies and was retired once closure bodies lowered cleanly):
  python3 scripts/trust_ir_producer_scorecard.py \
      --trustc build/aarch64-apple-darwin/stage1/bin/trustc \
      --out-dir reports/trust-ir-producer-baseline-2026-07-01 \
      --seed 20260701 --sample-size 2000 --jobs 8 \
      --corpus realcode=scripts/realcode-coverage/corpus/realcode.rs

Check the conjunctive corpus-local instrumented-row zero-residue gate on an existing artifact:

  python3 scripts/trust_ir_producer_scorecard.py \
      --check-completion <sweep-dir>

Author: Andrew Yates | Copyright 2026 | License: Apache-2.0 OR MIT
"""

import argparse
import collections
import concurrent.futures
import datetime
import hashlib
import importlib.util
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

_mono_parser_spec = importlib.util.spec_from_file_location(
    "rust_instance_census", os.path.join(os.path.dirname(__file__), "rust_instance_census.py"))
if _mono_parser_spec is None or _mono_parser_spec.loader is None:
    raise ImportError("cannot load local rust_instance_census parser")
rust_instance_census = importlib.util.module_from_spec(_mono_parser_spec)
_mono_parser_spec.loader.exec_module(rust_instance_census)

# Trust: preserve only the maintained caller's advertised original descriptors.
# Native owners still authenticate them; this grants no scheduling/admission credit.
_resource_transport_spec = importlib.util.spec_from_file_location(
    "census_resource_transport", os.path.join(os.path.dirname(__file__), "lib/landing_targo.py"))
if _resource_transport_spec is None or _resource_transport_spec.loader is None:
    raise ImportError("cannot load local resource descriptor transport")
_resource_transport = importlib.util.module_from_spec(_resource_transport_spec)
_resource_transport_spec.loader.exec_module(_resource_transport)

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
    group on timeout. Returns (returncode_or_None, stderr_bytes); None also covers overflow."""
    proc = subprocess.Popen(
        argv, cwd=cwd, env=env,
        stdout=subprocess.DEVNULL, stderr=subprocess.PIPE,
        preexec_fn=_guard_preexec,
        # Keep the direct compiler as watchdog group leader. A native serial
        # owner, when used for sequential qualification, stays outside this group.
        pass_fds=_resource_transport.resource_fds(env),
    )
    cap_kb = GUARD_MEM_CAP_BYTES // 1024
    oom_killed = threading.Event()
    stderr_overflow = threading.Event()
    stderr_read_error = threading.Event()
    stop = threading.Event()
    chunks = []

    def _capture_stderr():
        size = 0
        try:
            while chunk := os.read(proc.stderr.fileno(), 64 * 1024):
                remaining = MAX_STDERR_BYTES - size
                if remaining > 0:
                    kept = chunk[:remaining]
                    chunks.append(kept)
                    size += len(kept)
                if len(chunk) > remaining and not stderr_overflow.is_set():
                    stderr_overflow.set()
                    try:
                        os.killpg(proc.pid, signal.SIGKILL)
                    except (ProcessLookupError, OSError):
                        pass
        except (OSError, ValueError):
            stderr_read_error.set()
            try:
                os.killpg(proc.pid, signal.SIGKILL)
            except (ProcessLookupError, OSError):
                pass

    reader = threading.Thread(target=_capture_stderr, daemon=True)
    reader.start()

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
        code = None
        try:
            code = proc.wait(timeout=timeout)
        except subprocess.TimeoutExpired:
            try:
                os.killpg(proc.pid, signal.SIGKILL)
            except (ProcessLookupError, OSError):
                proc.kill()
            try:
                proc.wait(timeout=10)
            except subprocess.TimeoutExpired:
                proc.kill()
                proc.wait()
        reader.join(timeout=10)
        if reader.is_alive():
            stderr_read_error.set()
            try:
                os.killpg(proc.pid, signal.SIGKILL)
            except (ProcessLookupError, OSError):
                pass
            proc.stderr.close()
            reader.join(timeout=1)
        stderr = b"".join(chunks)
        if stderr_overflow.is_set():
            stderr = stderr[:MAX_STDERR_BYTES - len(STDERR_OVERFLOW_MARKER)] + STDERR_OVERFLOW_MARKER
        if oom_killed.is_set() or stderr_overflow.is_set() or stderr_read_error.is_set():
            code = None
        return code, stderr
    finally:
        stop.set()
        proc.stderr.close()

# Exact-event filter: the two trust-ir-lower events live in module
# rustc_mir_build::builder (builder/mod.rs); the noisy sub-modules are forced off.
_RUSTC_LOG_FILTER_DEFAULT = (
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

# Trust (2026-08-31): `TRUST_SCORECARD_LOG_FILTER` overrides the filter for ONE run.
#
# WHY THIS EXISTS, and why it is an override rather than a change to the default:
# `crate_module=debug` is what ENABLES the self-validation walk at all — the call site
# guards it with `tracing::enabled!(DEBUG)` precisely so a normal compile never pays for
# it. On 2026-08-31 that walk (`trust_ir_build::validate_module`) was found to recurse
# UNBOUNDEDLY on some modules: 60 corpus files that compile without `-Ztrust-ir-lower`
# SIGSEGV with it, scoring `flag_induced_fail`, and the corpus lost 192 bodies
# (7,257 -> 7,065). See `reports/what-100-percent-costs-2026-08-31.md` Addendum 7 for the
# reproducer and the bisect.
#
# Dropping that one target restores the corpus, at the cost of leaving `modules_invalid`
# UNMEASURED. That is a real loss, so the override is per-run, never the default, and the
# effective filter is recorded verbatim in the artifact's `provenance.rustc_log_filter` —
# so an artifact measured this way SAYS SO, and a reader can tell a sweep that measured
# zero invalid modules from one that did not look. A filter that silently omits an
# instrument is the same failure as a gate that cannot fail (see the note above).
RUSTC_LOG_FILTER = os.environ.get("TRUST_SCORECARD_LOG_FILTER", _RUSTC_LOG_FILTER_DEFAULT)

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
# Trust (2026-10-01): the EFFECT-CONSERVATION verdict, one event per body the mainline lowering
# recorded (`rustc_mir_build::trust_ir_crate_finalize`, target `rustc_mir_build::builder`). The
# gate compares the body's trust-ir effects with rustc's built MIR and tags every value
# abstraction (D28); `classes` is `+`-joined `not-conserved(<effect>)` / `abstracted(<lane>)`,
# empty when conserved.
#   trust-ir-lower: effect conservation, def=DefId(0:N ~ path), conserved=<bool>, clean=<bool>,
#     spliced=<bool>, classes=<..>, equivalences={..}, detail=<n tag(s): ..>
EFFCONS_RE = re.compile(
    r"trust-ir-lower: effect conservation, "
    r"def=DefId\([^~]*~\s*(?P<path>.+?)\), conserved=(?P<conserved>true|false), "
    r"clean=(?P<clean>true|false), spliced=(?P<spliced>true|false), classes=(?P<classes>\S*), "
    r"equivalences=\{(?P<equivalences>[^}]*)\}(?:, detail=(?P<detail>.*?))?\s*$",
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
    # Trust (absent-callee Stage 0): the two priced unknowns, OPTIONAL so every
    # pre-instrument stderr still parses. `offender` = which Undef broke the
    # dead-seed proof (oracle-live-havoc rows); `why` = the differential's own
    # last note (not-run rows).
    r'(?:, offender="(?P<offender>[^"]*)")?'
    r'(?:, why="(?P<why>[^"]*)")?'
)
# Trust (absent-callee Stage 1.5): the two-sided UNINTERPRETED-CALLEE probe --
# instrument only; prices the conversion rate of the design's substitution.
ROW1_UC_RE = re.compile(
    r'trust-ir-lower: row1 UC probe, '
    r'def_index=(?P<def_index>\d+), '
    r'def_path="(?P<def_path>[^"]*)", '
    r'declarations=(?P<declarations>\d+), '
    r'outcome="(?P<outcome>[^"]*)", '
    r'samples=(?P<samples>\d+), '
    r'detail="(?P<detail>[^"]*)"'
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
# Trust (attribution gap, 2026-08-20): the per-ERROR detail event, on its own message so it can
# never be picked up as a class row by VALERR_RE above. The producer has emitted this since the
# #197 follow-up (`crate_module.rs`, `tracing::debug!(detail = ?e, ...)`) and the scorecard threw
# it away, so the artifact recorded that a module was ill-formed without recording WHICH struct,
# enum or constant the validator objected to — the one fact attribution actually needs.
#
#   trust-ir-lower: module validation detail, detail=<Variant> { .. }
#
# The payload is a Rust `Debug` rendering containing commas and braces, so it is captured to end
# of line rather than field-parsed. Absent (older binary) stays distinguishable from empty.
VALDETAIL_RE = re.compile(
    r"trust-ir-lower: module validation detail,\s*detail=(?P<detail>.+?)\s*$",
    re.MULTILINE,
)
DIFF_RE = re.compile(
    r"trust-ir-lower: differential, "
    r"def=DefId\([^~]*~\s*(?P<path>.+?)\), equal=(?P<equal>true|false), "
    r"samples=(?P<samples>\d+), mode=(?P<mode>\w+), note=\"(?P<note>.*)\"\s*$",
    re.MULTILINE,
)

# Trust (2026-09-02): the DERIVED-MIR channel, which this scorecard had never parsed at all
# (`grep -ci derived` returned 0 before this line). The compiler has been emitting it per body
# all along and `scripts/trust_ir_flip_frontier.py` already carried this exact regex; the
# scorecard's event list at the top of this file is channel-1 only, so every artifact it has
# ever produced records half the evidence.
#
# WHY THAT MATTERED, measured on the 2,000-file corpus lock with `build/snap-t24`: 2,819 clean
# bodies are `DerivedAgreed` and **16 are `DerivedMismatch`** — sixteen standing disagreements
# between the built MIR and the MIR re-derived from the producer's trust-ir, none of which any
# baseline artifact records and none of which the per-wave "divergences 0" line has ever
# covered, because that line is computed from `mode` alone.
#
# The 16 do NOT ship wrong code, and the distinction is worth stating precisely because the
# alarming reading is the natural one. `rustc_mir_build/src/builder/mod.rs:405` calls
# `flip_registry::record_green` ONLY under
# `derived_report.verdict == DerivedVerdict::DerivedAgreed`, so a `DerivedMismatch` body is
# never flipped and its real MIR is never replaced; under `-Ztrust-ir-lower=strict` the same
# site raises a hard `span_err`. Three of the 16 are additionally `mode=Agreed` on channel 1,
# which is the combination that WOULD flip if the derived verdict were green — so they are
# exactly the bodies where the two channels disagree about the same program, and exactly the
# ones no report could previously name.
#
# The instrument was working; the REPORTING was blind. This closes that.
DERIVED_RE = re.compile(
    r"trust-ir-lower: derived-MIR differential, "
    r"def=DefId\([^~]*~\s*(?P<path>.+?)\), verdict=(?P<verdict>\w+), "
    r'detail="(?P<detail>.*?)",\s*markers_exact',
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

    An eligible tests/ui/trust file in neither section is NOT an error: the sampler
    admits a file under that directory only when [in-pool] lists it, so an
    unclassified file is held out exactly like an [excluded] one and the seeded
    sample cannot move. (Until 2026-09-23 it was a hard error, which made every new
    regression test a manifest edit and left this audit red for weeks.)"""
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


def effect_conservation_census(clean):
    """The effect-conservation verdicts over lowered-clean bodies (see EFFCONS_RE)."""
    measured = [b for b in clean if b.get("effect_conservation") is not None]
    refused = [b for b in measured if not b["effect_conservation"]["conserved"]]
    classes = collections.Counter(
        c for b in refused for c in b["effect_conservation"]["classes"]
    )
    combos = collections.Counter(
        "+".join(b["effect_conservation"]["classes"]) for b in refused
    )
    return {
        "measured": len(measured),
        "unmeasured": len(clean) - len(measured),
        "conserved": len(measured) - len(refused),
        "refused": len(refused),
        "refused_spliced": sum(1 for b in refused if b["effect_conservation"]["spliced"]),
        "refused_not_conserved": sum(
            1 for b in refused
            if any(c.startswith("not-conserved(") for c in b["effect_conservation"]["classes"])
        ),
        "refused_abstracted_only": sum(
            1 for b in refused
            if all(c.startswith("abstracted(") for c in b["effect_conservation"]["classes"])
        ),
        "refused_agreed": sum(1 for b in refused if b["mode"] == "Agreed"),
        "refused_modelled": sum(
            1 for b in refused
            if b.get("symbolic") is False and b.get("opaque_collapse") is False
        ),
        "class_histogram": dict(classes.most_common()),
        "combination_histogram": dict(combos.most_common(20)),
        "not_conserved_defs": sorted(
            b["def"] for b in refused
            if any(c.startswith("not-conserved(") for c in b["effect_conservation"]["classes"])
        )[:200],
    }


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
    # Trust (absent-callee Stage 3): the fenced UC verdict class -- its own bucket, NEVER
    # folded into "agreed" (the mode string equality above already keeps every Agreed count
    # clean of it; this rule keeps the note-class histogram honest too).
    if mode == "AgreedUninterpretedCallee":
        return "agreed-uninterpreted-callee"
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
    # Trust (decision 2026-09-17(b)): the per-body refusal of a call edge to a Rust-ABI
    # declaration the producer cannot sign. Its OWN class, and deliberately not folded into
    # the pending-const row above: that row is "how often finalizer const evaluation does not
    # deliver", and this population has nothing to do with const evaluation. Leaving it in
    # `clean-skip-other` would make the coverage the owner traded for honest refusals
    # invisible in the one instrument that reports it.
    if "minting an unsignable Rust-ABI call edge" in note:
        return "clean-skip-unsignable-rust-abi-edge"
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
    out = {"total": int(m.group("total")), "classes": classes}
    # Trust (attribution gap): the per-error Debug renderings, which name the ids and types. Only
    # attached when the total is non-zero — a clean module would otherwise carry an empty list on
    # every one of ~1800 rows for no information. `[]` on an invalid row is itself a finding: it
    # means the binary emits the summary but not the detail event.
    if out["total"]:
        out["details"] = [d.group("detail") for d in VALDETAIL_RE.finditer(stderr)]
    return out


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
    effcons = {}
    for m in EFFCONS_RE.finditer(stderr):
        effcons.setdefault(m.group("path"), {
            "conserved": m.group("conserved") == "true",
            "clean": m.group("clean") == "true",
            "spliced": m.group("spliced") == "true",
            "classes": [c for c in m.group("classes").split("+") if c],
            # The rendered tags (sites), capped: the census reads the classes, a reader the sites.
            **({"detail": m.group("detail")[:400]} if m.group("detail") else {}),
        })
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
    _uc = {}
    for m in ROW1_UC_RE.finditer(stderr):
        i = m.group("def_index")
        p2 = _idx_to_path.get(i)
        if p2 is None or i in _idx_ambiguous:
            continue
        _uc[p2] = {
            "outcome": m.group("outcome"),
            "samples": int(m.group("samples")),
            **({"detail": m.group("detail")} if m.group("detail") else {}),
        }
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
            # Trust (absent-callee Stage 0): present only on instrumented rows.
            **({"offender": m.group("offender")} if m.group("offender") else {}),
            **({"why": m.group("why")} if m.group("why") else {}),
            # Trust (absent-callee Stage 1.5): the UC probe's row, when one ran.
            **({"uc": _uc.get(p)} if _uc.get(p) else {}),
        }
    collect_primary = collections.defaultdict(list)
    collect_cascade = collections.defaultdict(list)
    for m in COLLECT_RE.finditer(stderr):
        dst = collect_primary if m.group("cls") == "primary" else collect_cascade
        dst[m.group("path")].append([m.group("what"), int(m.group("n"))])
    # Trust (2026-09-02): the derived-MIR verdict per body. Keyed on the same def path as the
    # channel-1 event, so the two are joinable per body rather than only in aggregate. First
    # writer wins, matching `DIFF_RE`'s own dedup below.
    derived = {}
    for m in DERIVED_RE.finditer(stderr):
        derived.setdefault(m.group("path"), (m.group("verdict"), m.group("detail")))
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
            # Trust (2026-10-01): the effect-conservation verdict. None = no event (an older
            # compiler, or a body the mainline lowering did not record), never "conserved".
            "effect_conservation": effcons.get(p),
            # Trust (2026-09-02): the DERIVED-MIR channel. Absent (None) means the producer
            # emitted no derived event for this body and must stay distinguishable from
            # `DerivedUnsupported`, which means it emitted one and refused — the same
            # not-measured-vs-modelled discipline the fields above keep.
            "derived_verdict": (derived.get(p) or (None, None))[0],
            "derived_detail": (derived.get(p) or (None, None))[1],
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


CENSUS_SCHEMA = "trust.rust.hir-body-census.v1"
# Trust (2026-09-29): v2 adds compiler-independent identity to each body row
# (crate_name, def_path_no_crate, source); rustc_interface trust_body_census.rs.
# v1 stays accepted: retained artifacts were written by v1 compilers.
CENSUS_SCHEMA_V2 = "trust.rust.hir-body-census.v2"
CENSUS_SCHEMAS = (CENSUS_SCHEMA, CENSUS_SCHEMA_V2)
CENSUS_V1_BODY_KEYS = frozenset({"def", "kind", "def_kind", "def_index", "def_path_hash"})
CENSUS_V2_BODY_KEYS = CENSUS_V1_BODY_KEYS | {"crate_name", "def_path_no_crate", "source"}  # gitleaks:allow (field names, not a credential)


def census_v2_identity_error(body):
    """Why a v2 body row's identity fields are malformed, or None.

    `def` is `def_path_debug_str`: `<crate>[<4 hex>]<def_path_no_crate>`, so the
    two spellings must agree exactly.  `source` is all-null (disclosed as
    unmeasured: not one local SHA-256-checksummed file) or fully measured.
    """
    crate, path, source = body["crate_name"], body["def_path_no_crate"], body["source"]
    if not (isinstance(crate, str) and crate and "[" not in crate
            and isinstance(path, str) and path.startswith("::")):
        return "malformed v2 crate name or crate-free def path"
    if not re.fullmatch(re.escape(crate) + r"\[[0-9a-f]{4}\]" + re.escape(path), body["def"]):
        return "v2 def differs from crate name + crate-free def path"
    if not isinstance(source, dict) or set(source) != {"file", "sha256", "lo", "hi"}:
        return "malformed v2 source identity"
    if all(source[key] is None for key in source):
        return None
    def position(value):
        return (type(value) is list and len(value) == 2 and all(type(v) is int for v in value)
                and value[0] >= 1 and value[1] >= 0)
    if (not isinstance(source["file"], str) or not os.path.isabs(source["file"])
            or not isinstance(source["sha256"], str)
            or not re.fullmatch(r"[0-9a-f]{64}", source["sha256"])
            or not position(source["lo"]) or not position(source["hi"])
            or source["lo"] > source["hi"]):
        return "malformed or partially measured v2 source identity"
    return None
BODY_CENSUS_SOURCE = "independent-hir-and-typeck-generated-body-census/v1"
INPUT_MANIFEST_SCHEMA = "trust.rust.measurement-input-manifest.v1"


def file_sha256(path):
    digest = hashlib.sha256()
    with open(path, "rb") as source:
        for block in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


STAGE_CLOSURE_SCHEMA = "trust.rust.compiler-stage-closure.v1"
MAX_HIR_CENSUS_BYTES = 32 * 1024 * 1024
MAX_STDERR_BYTES = 16 * 1024 * 1024
STDERR_OVERFLOW_MARKER = b"\nscorecard: stderr capture exceeded limit\n"
LOADER_OVERRIDE_VARS = (
    "LD_LIBRARY_PATH", "LD_PRELOAD", "LD_AUDIT", "DYLD_LIBRARY_PATH",
    "DYLD_FALLBACK_LIBRARY_PATH", "DYLD_INSERT_LIBRARIES",
    "DYLD_FRAMEWORK_PATH", "DYLD_FALLBACK_FRAMEWORK_PATH",
)


def stage_closure_digest(closure):
    payload = {key: value for key, value in closure.items() if key != "sha256"}
    return hashlib.sha256(json.dumps(payload, sort_keys=True, separators=(",", ":")).encode()).hexdigest()


def compiler_stage_closure(trustc):
    """Hash the stage executable and full adjacent lib tree, not just the driver binary."""
    compiler = os.path.realpath(trustc)
    if os.path.basename(os.path.dirname(compiler)) != "bin" or os.path.basename(compiler) != "trustc":
        raise ValueError("compiler is not a stage bin/trustc")
    stage_root = os.path.dirname(os.path.dirname(compiler))
    lib_root = os.path.join(stage_root, "lib")
    if not os.path.isdir(lib_root) or os.path.islink(lib_root):
        raise ValueError("compiler stage lib directory is unavailable or symlinked")
    files = []
    for directory, subdirs, names in os.walk(lib_root, followlinks=False):
        subdirs.sort()
        if any(os.path.islink(os.path.join(directory, name)) for name in subdirs):
            raise ValueError("compiler stage contains a symlinked lib directory")
        for name in sorted(names):
            path = os.path.join(directory, name)
            resolved = os.path.realpath(path)
            if os.path.commonpath((lib_root, resolved)) != lib_root or not os.path.isfile(path):
                raise ValueError(f"compiler stage lib escapes closure: {path}")
            files.append({"path": os.path.relpath(path, stage_root),
                          "target": os.path.relpath(resolved, stage_root),
                          "sha256": file_sha256(path)})
    files.sort(key=lambda row: row["path"])
    drivers = [row for row in files if os.path.basename(row["path"]).startswith("librustc_driver")
               and row["path"].endswith((".dylib", ".so", ".dll"))]
    if len(drivers) != 1:
        raise ValueError("compiler stage needs exactly one identifiable rustc_driver library")
    closure = {"schema": STAGE_CLOSURE_SCHEMA, "stage_root": stage_root,
               "compiler": compiler, "compiler_sha256": file_sha256(compiler), "files": files}
    closure["sha256"] = stage_closure_digest(closure)
    return closure


def capture_stage_closure(trustc):
    try:
        return compiler_stage_closure(trustc), []
    except (OSError, ValueError) as error:
        return None, [f"compiler stage closure unmeasured: {error}"]


def validate_stage_closure(closure):
    if (not isinstance(closure, dict)
            or set(closure) != {"schema", "stage_root", "compiler", "compiler_sha256", "files", "sha256"}
            or closure["schema"] != STAGE_CLOSURE_SCHEMA
            or not isinstance(closure["stage_root"], str) or not os.path.isabs(closure["stage_root"])
            or os.path.normpath(closure["stage_root"]) != closure["stage_root"]
            or not isinstance(closure["compiler"], str)
            or closure["compiler"] != os.path.join(closure["stage_root"], "bin", "trustc")
            or not isinstance(closure["compiler_sha256"], str)
            or not re.fullmatch(r"[0-9a-f]{64}", closure["compiler_sha256"])
            or not isinstance(closure["files"], list) or not closure["files"]
            or not isinstance(closure["sha256"], str)
            or not re.fullmatch(r"[0-9a-f]{64}", closure["sha256"])):
        raise ValueError("missing or malformed compiler stage closure")
    paths = []
    for row in closure["files"]:
        if (not isinstance(row, dict) or set(row) != {"path", "target", "sha256"}
                or not all(isinstance(row[key], str) for key in row)
                or not re.fullmatch(r"[0-9a-f]{64}", row["sha256"])):
            raise ValueError("malformed compiler stage library row")
        for field in ("path", "target"):
            value = row[field]
            if (os.path.isabs(value) or os.path.normpath(value) != value
                    or not value.startswith("lib" + os.sep) or "\x00" in value):
                raise ValueError("compiler stage library path escapes lib tree")
        paths.append(row["path"])
    if paths != sorted(set(paths)):
        raise ValueError("duplicate or unordered compiler stage libraries")
    if any(row["target"] not in paths for row in closure["files"]):
        raise ValueError("compiler stage symlink target omitted from closure")
    drivers = [path for path in paths if os.path.basename(path).startswith("librustc_driver")
               and path.endswith((".dylib", ".so", ".dll"))]
    if len(drivers) != 1:
        raise ValueError("compiler stage closure needs exactly one rustc_driver")
    if closure["sha256"] != stage_closure_digest(closure):
        raise ValueError("compiler stage closure digest mismatch")
    return closure


def _unique_json_object(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise ValueError(f"duplicate JSON key {key!r}")
        result[key] = value
    return result


def _strict_json(raw):
    def reject_constant(value):
        raise ValueError(f"nonstandard JSON constant {value}")
    try:
        return json.loads(raw, object_pairs_hook=_unique_json_object,
                          parse_constant=reject_constant)
    except RecursionError as error:
        raise ValueError("JSON nesting exceeds parser capacity") from error


def parse_compiler_census(raw, *, input_path, lowering, exit_code,
                          expected_crate_types=("Rlib",)):
    """Validate actual compiler JSONL, retaining partial rows without crediting them.

    HIR completeness is not instance/runtime completeness. A complete footer
    attests analysis completion only; the separate process status must also pass.
    Crate types are caller-authored expectations, never inferred from this census.
    Existing rlib corpus callers keep their exact default contract.
    """
    result = {"status": "missing", "errors": [], "bodies": [], "sources": []}
    known_crate_types = {"Executable", "Dylib", "Rlib", "StaticLib", "Cdylib", "ProcMacro", "Sdylib"}
    if (type(expected_crate_types) not in (tuple, list) or not expected_crate_types
            or not all(type(kind) is str and kind in known_crate_types
                       for kind in expected_crate_types)
            or len(set(expected_crate_types)) != len(expected_crate_types)):
        result.update(status="malformed", errors=["expected crate types must be a nonempty unique list of compiler crate types"])
        return result
    if not (exit_code is None or type(exit_code) is int):
        result.update(status="malformed", errors=["compiler exit status must be integer or null"])
        return result
    if raw is None or raw == "":
        result["errors"].append("compiler census missing")
        return result
    if not isinstance(raw, str):
        result.update(status="malformed", errors=["compiler census must be UTF-8 JSONL text"])
        return result
    try:
        if len(raw) > MAX_HIR_CENSUS_BYTES or len(raw.encode("utf-8")) > MAX_HIR_CENSUS_BYTES:
            raise ValueError("compiler census exceeds bounded capture limit")
        if not raw.endswith("\n"):
            raise ValueError("census is truncated or has an unexpected record count")
        # JSONL separates on LF, not on every Unicode line separator that may
        # legitimately occur inside a source filename or JSON string.
        lines = [line + "\n" for line in raw[:-1].split("\n")]
        if not 1 <= len(lines) <= 3:
            raise ValueError("census is truncated or has an unexpected record count")
        records = [_strict_json(line) for line in lines]
        if (any(not isinstance(record, dict) or record.get("schema") not in CENSUS_SCHEMAS
                for record in records)
                or len({record["schema"] for record in records}) != 1):
            raise ValueError("malformed compiler census schema")
        schema = records[0]["schema"]
        result["schema"] = schema
        header = records[0]
        if (set(header) != {"schema", "event", "input", "compiler_version", "target", "edition", "crate_types",
                           "direct_lowering", "verification_enabled", "scope", "generated_scope", "reachable_instances"}
                or header["event"] != "begin" or header["input"] != input_path
                or header["direct_lowering"] is not lowering
                or header["verification_enabled"] is not False
                or header["scope"] != "local-hir-body-owners-after-typeck"
                or header["generated_scope"] != "local-typeck-synthetic-coroutine-bodies"
                or header["reachable_instances"] != "unmeasured"
                or header["edition"] not in {"2015", "2018", "2021", "2024"}
                or header["crate_types"] != list(expected_crate_types)
                or not all(isinstance(header[key], str) and header[key]
                           for key in ("compiler_version", "target"))):
            raise ValueError("census begin does not bind this input and compiler lane")
        result["header"] = header
        if len(records) >= 2:
            snapshot = records[1]
            if (set(snapshot) != {"schema", "event", "body_count", "bodies", "generated_body_count", "generated_bodies", "sources"}
                    or snapshot["event"] != "hir_snapshot"
                    or not isinstance(snapshot["bodies"], list)
                    or type(snapshot["body_count"]) is not int
                    or snapshot["body_count"] != len(snapshot["bodies"])
                    or not isinstance(snapshot["generated_bodies"], list)
                    or type(snapshot["generated_body_count"]) is not int
                    or snapshot["generated_body_count"] != len(snapshot["generated_bodies"])):
                raise ValueError("malformed HIR snapshot/count")
            identities, indices, paths = set(), set(), set()
            for body in snapshot["bodies"] + snapshot["generated_bodies"]:
                if (not isinstance(body, dict)
                        or set(body) != (CENSUS_V2_BODY_KEYS if schema == CENSUS_SCHEMA_V2
                                         else CENSUS_V1_BODY_KEYS)
                        or not all(isinstance(body.get(key), str) and body[key]
                                   for key in ("def", "kind", "def_kind", "def_path_hash"))
                        or type(body["def_index"]) is not int or body["def_index"] < 0
                        or body["kind"] != body_kind(body["def"])):
                    raise ValueError("malformed HIR body identity/class")
                if body["def_kind"].split(" ", 1)[0] not in {
                        "Fn", "AssocFn", "Closure", "Const", "AssocConst", "AnonConst",
                        "InlineConst", "Static", "SyntheticCoroutineBody"}:
                    raise ValueError(f"unknown HIR body class: {body['def_kind']}")
                if schema == CENSUS_SCHEMA_V2 and (error := census_v2_identity_error(body)):
                    raise ValueError(error)
                if (body["def_path_hash"] in identities or body["def_index"] in indices
                        or body["def"] in paths):
                    raise ValueError("duplicate HIR body identity")
                identities.add(body["def_path_hash"])
                indices.add(body["def_index"])
                paths.add(body["def"])
            if (any(body["def_kind"] != "SyntheticCoroutineBody" for body in snapshot["generated_bodies"])
                    or any(body["def_kind"] == "SyntheticCoroutineBody" for body in snapshot["bodies"])):
                raise ValueError("HIR and typeck-generated body classes are not correctly partitioned")
            result["bodies"] = snapshot["bodies"] + snapshot["generated_bodies"]
            result["generated_bodies"] = snapshot["generated_bodies"]
            result["snapshot_sources"] = snapshot["sources"]
            result["sources"] = snapshot["sources"]
        if len(records) != 3:
            result["status"] = "incomplete"
            result["errors"].append("compiler census missing complete footer")
            return result
        footer = records[2]
        if (set(footer) != {"schema", "event", "status", "body_count", "generated_body_count", "snapshot_sha256", "sources", "other_inputs"}
                or footer["event"] != "complete" or footer["status"] != "complete"
                or type(footer["body_count"]) is not int
                or footer["body_count"] != snapshot["body_count"]
                or type(footer["generated_body_count"]) is not int
                or footer["generated_body_count"] != snapshot["generated_body_count"]
                or footer["snapshot_sha256"] != hashlib.sha256(lines[1].encode("utf-8")).hexdigest()):
            raise ValueError("census complete footer/count/digest mismatch")
        for source_rows in (result["sources"], footer["sources"]):
            if not isinstance(source_rows, list):
                raise ValueError("malformed loaded-source list")
            source_paths = set()
            for source in source_rows:
                if (not isinstance(source, dict) or set(source) != {"file", "sha256"}
                        or not isinstance(source["file"], str) or not source["file"]
                        or not isinstance(source["sha256"], str)
                        or not re.fullmatch(r"[0-9a-f]{64}", source["sha256"])
                        or source["file"] in source_paths):
                    raise ValueError("malformed or duplicate loaded-source hash")
                source_paths.add(source["file"])
        later_sources = {source["file"]: source["sha256"] for source in footer["sources"]}
        if any(later_sources.get(source["file"]) != source["sha256"]
               for source in result["sources"]):
            raise ValueError("loaded sources changed between HIR snapshot and footer")
        if input_path not in later_sources:
            raise ValueError("compiler census omitted its root input hash")
        result["sources"] = footer["sources"]
        other = footer["other_inputs"]
        if (not isinstance(other, dict)
                or set(other) != {"tracked_files", "environment_variables", "proc_macro_io", "build_environment", "external_dependency_closure"}
                or any(other[key] != "unmeasured" for key in ("proc_macro_io", "build_environment", "external_dependency_closure"))
                or any(not isinstance(other[key], list)
                       or not all(isinstance(value, str) and value for value in other[key])
                       or len(other[key]) != len(set(other[key]))
                       for key in ("tracked_files", "environment_variables"))):
            raise ValueError("malformed non-source input disclosure")
        result["other_inputs"] = other
        result["status"] = "complete" if exit_code == 0 else "compiler_failed"
        if exit_code != 0:
            result["errors"].append("compiler did not exit successfully after census")
        if other["tracked_files"] or other["environment_variables"]:
            result["status"] = "input_closure_incomplete"
            result["errors"].append("consumption-time hashes are unmeasured for tracked files/environment: "
                                    + repr(other["tracked_files"] + other["environment_variables"]))
    except (ValueError, TypeError, KeyError, UnicodeError) as error:
        result["status"] = "malformed"
        result["errors"].append(str(error))
    return result


def run_one(trustc: str, src: str, edition: str, timeout: int, with_flag: bool, scratch: str,
            *, codegen: bool = False):
    """Compile one file, preserving diagnostics and any census bytes on failure."""
    trustc = os.path.realpath(trustc)
    tmpdir = tempfile.mkdtemp(dir=scratch)
    env = dict(os.environ)
    for name in LOADER_OVERRIDE_VARS:
        env.pop(name, None)
    env["RUSTC_LOG"] = RUSTC_LOG_FILTER
    env["RUST_BACKTRACE"] = "0"
    env["RUSTC_ICE"] = "0"
    census_path = os.path.join(tmpdir, "hir-census.jsonl")
    mono_path = os.path.join(tmpdir, "mono-census.jsonl")
    argv = [trustc, "-Z", "trust-ir-lower=" + ("on" if with_flag else "off")]
    argv += [
        "-Z", "trust-verify=off",  # producer-only measurement; hook is independent
        "-Z", "checksum-hash-algorithm=sha256",
        "-Z", "trust-body-census=" + census_path,
    ]
    if codegen:
        argv += ["-Z", "trust-instance-census=" + mono_path]
    argv += [
        "--edition", edition,
        "--crate-type", "lib",
        "--emit=link" if codegen else "--emit=metadata",
        "--out-dir", tmpdir,
        "--cap-lints", "allow",
        src,
    ]
    try:
        # Trust: memory-capped, session-group-reaped compile (see `guarded_compile`) so a
        # trait-solver-overflow torture body can neither OOM the host nor orphan a runaway trustc.
        error = None
        try:
            compiler_before = file_sha256(trustc)
        except OSError:
            compiler_before = None
        try:
            code, stderr = guarded_compile(argv, tmpdir, env, timeout)
        except OSError as exception:
            code, stderr, error = None, b"", str(exception)
        try:
            compiler_after = file_sha256(trustc)
        except OSError:
            compiler_after = None
        if len(stderr) > MAX_STDERR_BYTES:
            code = None
            stderr = stderr[:MAX_STDERR_BYTES - len(STDERR_OVERFLOW_MARKER)] + STDERR_OVERFLOW_MARKER
        if stderr.endswith(STDERR_OVERFLOW_MARKER):
            code = None
            error = "stderr capture exceeded bounded limit"
        try:
            with open(census_path, "rb") as census_file:
                census_bytes = census_file.read(MAX_HIR_CENSUS_BYTES + 1)
            if len(census_bytes) > MAX_HIR_CENSUS_BYTES:
                raise ValueError("HIR census exceeds bounded capture limit")
            census_raw = census_bytes.decode("utf-8")
        except FileNotFoundError:
            census_raw = None
        except (OSError, UnicodeError, ValueError) as exception:
            census_raw = None
            error = "; ".join(filter(None, (error, f"cannot read compiler census: {exception}")))
        result = {
            "exit_code": code,
            "stderr": stderr.decode("utf-8", errors="replace"),
            "error": error,
            "argv": argv,
            "input": src,
            "census_raw": census_raw,
            "compiler_sha256_before": compiler_before,
            "compiler_sha256_after": compiler_after,
        }
        if codegen:
            try:
                with open(mono_path, "rb") as census_file:
                    result["mono_raw"] = census_file.read(rust_instance_census.MAX_BYTES + 1).decode("utf-8")
            except FileNotFoundError:
                result["mono_raw"] = None
            except (OSError, UnicodeError) as exception:
                result["mono_raw"] = None
                result["error"] = "; ".join(filter(None, (result["error"],
                    f"cannot read mono census: {exception}")))
        return result
    finally:
        shutil.rmtree(tmpdir, ignore_errors=True)


def measure_file(trustc: str, src: str, edition: str, timeout: int, scratch: str):
    """Both compiler lanes and both flag modes for every predeclared input."""
    control = run_one(trustc, src, edition, timeout, False, scratch)
    subject = run_one(trustc, src, edition, timeout, True, scratch)
    codegen_control = run_one(trustc, src, edition, timeout, False, scratch, codegen=True)
    codegen_subject = run_one(trustc, src, edition, timeout, True, scratch, codegen=True)
    code, stderr, ctl_code = subject["exit_code"], subject["stderr"], control["exit_code"]
    measurement = {"control": control, "subject": subject,
                   "codegen_control": codegen_control, "codegen_subject": codegen_subject}
    if code == 0 and ctl_code == 0:
        bodies, anomalies = parse_bodies(stderr)
        cg_ctl, cg_sub = codegen_control["exit_code"], codegen_subject["exit_code"]
        if cg_ctl != 0 or cg_sub != 0:
            if cg_ctl == 0:
                cg_stderr = codegen_subject["stderr"]
                ice = cg_sub == 101 or "internal compiler error" in cg_stderr
                outcome = ("flag_induced_codegen_timeout" if cg_sub is None else
                           "flag_induced_codegen_ice" if ice else "flag_induced_codegen_fail")
                signature = re.search(r"internal compiler error: [^\n]*", cg_stderr)
                return {"file": src, "outcome": outcome, "bodies": [],
                        "partial_bodies": bodies, "anomalies": anomalies,
                        "ice_signature": signature.group(0)[:200] if signature else "",
                        "measurement": measurement}
            outcome = ("codegen_timeout" if cg_ctl is None or cg_sub is None else
                       "codegen_control_fail" if cg_sub == 0 else "codegen_compile_fail")
            return {"file": src, "outcome": outcome, "bodies": [],
                    "measurement": measurement}
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
            "measurement": measurement,
        }
    if code is None:
        return {"file": src, "outcome": "timeout", "bodies": [], "measurement": measurement}
    ice = code == 101 or "internal compiler error" in stderr
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
            "measurement": measurement,
        }
    if ctl_code is None:
        return {"file": src, "outcome": "timeout_control", "bodies": [], "measurement": measurement}
    return {"file": src, "outcome": "control_fail" if code == 0 else "compile_fail",
            "bodies": [], "measurement": measurement}


def prepare_input_manifest(corpora, repo, extra_sources=()):
    """Snapshot before ANY compiler run. Defaults admit every selected root as ok.

    Explicit expected compile failures must be supplied by an existing manifest;
    compilation results never edit this inventory. Extra sources are explicit
    because guessing imports from producer success would not be independent.
    """
    manifest = {"schema": INPUT_MANIFEST_SCHEMA, "corpora": {}}
    for name, files, _meta in corpora:
        if not name or name in manifest["corpora"]:
            raise ValueError(f"empty or duplicate corpus name: {name!r}")
        if not files or len(files) != len(set(files)):
            raise ValueError(f"corpus {name!r} has no inputs or duplicate inputs")
        source_paths = sorted(set(files) | {os.path.abspath(path) for path in extra_sources})
        sources = [{"file": os.path.relpath(path, repo), "sha256": file_sha256(path)}
                   for path in source_paths]
        hashes = {source["file"]: source["sha256"] for source in sources}
        manifest["corpora"][name] = {
            "files": [{"file": os.path.relpath(path, repo),
                       "sha256": hashes[os.path.relpath(path, repo)], "expected_outcome": "ok"}
                      for path in sorted(files)],
            "sources": sources,
        }
    return manifest


def validate_input_manifest(manifest):
    if (not isinstance(manifest, dict) or set(manifest) != {"schema", "corpora"}
            or manifest["schema"] != INPUT_MANIFEST_SCHEMA
            or not isinstance(manifest["corpora"], dict) or not manifest["corpora"]):
        raise ValueError("malformed precompile input manifest")
    for name, corpus in manifest["corpora"].items():
        if (not isinstance(name, str) or not name or not isinstance(corpus, dict)
                or set(corpus) != {"files", "sources"}
                or not isinstance(corpus["files"], list) or not corpus["files"]
                or not isinstance(corpus["sources"], list)):
            raise ValueError(f"malformed precompile corpus: {name!r}")
        for table in ("files", "sources"):
            seen = set()
            fields = {"file", "sha256", "expected_outcome"} if table == "files" else {"file", "sha256"}
            for row in corpus[table]:
                if (not isinstance(row, dict) or set(row) != fields
                        or not isinstance(row["file"], str) or not row["file"]
                        or os.path.isabs(row["file"]) or os.path.normpath(row["file"]) != row["file"]
                        or not isinstance(row["sha256"], str)
                        or not re.fullmatch(r"[0-9a-f]{64}", row["sha256"])
                        or row["file"] in seen
                        or (table == "files" and row["expected_outcome"] not in {"ok", "compile_fail"})):
                    raise ValueError(f"malformed or duplicate {name}.{table} row")
                seen.add(row["file"])
        hashes = {row["file"]: row["sha256"] for row in corpus["sources"]}
        if any(hashes.get(row["file"]) != row["sha256"] for row in corpus["files"]):
            raise ValueError(f"{name}: input roots must be in the source manifest with identical hashes")
    return manifest


def current_source_errors(sources, repo):
    errors = []
    for source in sources:
        try:
            digest = file_sha256(os.path.join(repo, source["file"]))
        except OSError as error:
            errors.append(f"input unavailable: {source['file']}: {error}")
        else:
            if digest != source["sha256"]:
                errors.append(f"precompile source hash mismatch: {source['file']}")
    return errors


def _census_argv_ok(argv, path, edition, lowering, codegen):
    if not isinstance(argv, list) or not all(isinstance(arg, str) for arg in argv):
        return False
    expected_len = 21 if codegen else 19
    if len(argv) != expected_len or not argv[0]:
        return False
    if argv[1:8] != ["-Z", "trust-ir-lower=" + ("on" if lowering else "off"),
                      "-Z", "trust-verify=off", "-Z", "checksum-hash-algorithm=sha256", "-Z"]:
        return False
    if not argv[8].startswith("trust-body-census=") or not argv[8].split("=", 1)[1]:
        return False
    offset = 2 if codegen else 0
    if codegen and (argv[9] != "-Z" or not argv[10].startswith("trust-instance-census=")
                    or not argv[10].split("=", 1)[1] or argv[8].split("=", 1)[1] == argv[10].split("=", 1)[1]):
        return False
    return (argv[9 + offset:15 + offset] ==
            ["--edition", edition, "--crate-type", "lib",
             "--emit=link" if codegen else "--emit=metadata", "--out-dir"]
            and bool(argv[15 + offset])
            and argv[16 + offset:] == ["--cap-lints", "allow", path])


def reconcile_compiler_censuses(corpus):
    """Recompute census status from retained compiler bytes, never authored totals."""
    errors, bodies, states = [], [], []
    mono_unrepresented = collections.Counter()
    mono_item_count = 0
    mono_matched_count = 0
    observed_codegen_files = 0
    residual = {"whole_program_complete": False, "g1_g3_status": "red",
                "unmeasured": list(rust_instance_census.UNMEASURED_V2),
                "reachable_instances": "unmeasured", "runtime_roots": "unmeasured",
                "external_dependency_closure": "unmeasured", "proc_macro_io": "unmeasured",
                "build_environment": "unmeasured"}
    evidence = corpus.get("census_evidence")
    if not isinstance(evidence, dict) or evidence.get("schema") != "trust.rust.producer-census-evidence.v2":
        return {"status": "unverified", "errors": ["missing compiler census evidence"],
                "bodies": [], "files": [], "mono_item_count": None,
                "mono_matched_count": None, "mono_unrepresented": {}, **residual}
    try:
        if set(evidence) != {"schema", "repo", "input_manifest", "target", "edition", "compiler_sha256_before",
                             "compiler_sha256_after", "stage_closure_before", "stage_closure_after",
                             "precompile_errors", "postcompile_errors"}:
            raise ValueError("malformed compiler census evidence fields")
        repo = evidence["repo"]
        if not isinstance(repo, str) or not os.path.isabs(repo):
            raise ValueError("census evidence requires an absolute repository identity")
        manifest = validate_input_manifest(evidence["input_manifest"])
        if set(manifest["corpora"]) != {"corpus"}:
            raise ValueError("per-corpus evidence must contain exactly its corpus manifest")
        inputs = manifest["corpora"]["corpus"]
        before, after = evidence["compiler_sha256_before"], evidence["compiler_sha256_after"]
        if (not isinstance(before, str) or not re.fullmatch(r"[0-9a-f]{64}", before)
                or before != after):
            raise ValueError("compiler executable identity missing or changed during measurement")
        stage_closure = None
        try:
            before_closure = validate_stage_closure(evidence["stage_closure_before"])
            after_closure = validate_stage_closure(evidence["stage_closure_after"])
            if before_closure != after_closure:
                errors.append("compiler stage driver/library closure changed during measurement")
            elif before_closure["compiler_sha256"] != before:
                errors.append("compiler executable differs from stage closure")
            else:
                stage_closure = before_closure
        except ValueError as error:
            errors.append(str(error))
        if (not isinstance(evidence["target"], str) or not evidence["target"]
                or evidence["edition"] not in {"2015", "2018", "2021", "2024"}):
            raise ValueError("missing compiler target or measurement edition")
        for field in ("precompile_errors", "postcompile_errors"):
            if not isinstance(evidence[field], list) or not all(isinstance(e, str) for e in evidence[field]):
                raise ValueError(f"malformed {field}")
            errors.extend(evidence[field])
        expected_input = {"schema": "trust.trust-ir.producer-input-census.v1",
                          "source": "precompile-content-manifest/v1", "files": inputs["files"]}
        if corpus.get("input_census") != expected_input:
            raise ValueError("input census differs from retained precompile manifest")
        files = corpus.get("files")
        if not isinstance(files, list):
            raise ValueError("missing measured input results")
        expected = {row["file"]: row["expected_outcome"] for row in inputs["files"]}
        if (not all(isinstance(row, dict) and isinstance(row.get("file"), str) for row in files)
                or sorted(row["file"] for row in files) != sorted(expected)):
            raise ValueError("measured file population differs from precompile manifest")
        source_hashes = {os.path.abspath(os.path.join(repo, row["file"])): row["sha256"]
                         for row in inputs["sources"]}
        for row in files:
            path = os.path.abspath(os.path.join(repo, row["file"]))
            measurement = row.get("measurement")
            if not isinstance(measurement, dict) or set(measurement) != {
                    "control", "subject", "codegen_control", "codegen_subject"}:
                errors.append(f"{row['file']}: missing metadata or codegen control/subject compiler run")
                continue
            completed_censuses = {}
            completed_mono = {}
            compiler_versions = {}
            for role, lowering, codegen in (("control", False, False), ("subject", True, False),
                                            ("codegen_control", False, True),
                                            ("codegen_subject", True, True)):
                run = measurement[role]
                fields = {"exit_code", "stderr", "error", "argv", "input", "census_raw",
                          "compiler_sha256_before", "compiler_sha256_after"}
                if codegen:
                    fields.add("mono_raw")
                if (not isinstance(run, dict) or set(run) != fields
                        or run["input"] != path
                        or not (run["exit_code"] is None or type(run["exit_code"]) is int)
                        or not isinstance(run["argv"], list)
                        or not all(isinstance(arg, str) for arg in run["argv"])
                        or not isinstance(run["stderr"], str)
                        or len(run["stderr"]) > MAX_STDERR_BYTES
                        or len(run["stderr"].encode("utf-8")) > MAX_STDERR_BYTES
                        or not (run["census_raw"] is None or isinstance(run["census_raw"], str))
                        or (codegen and not (run["mono_raw"] is None or isinstance(run["mono_raw"], str)))
                        or not (run["error"] is None or isinstance(run["error"], str))):
                    errors.append(f"{row['file']}: malformed {role} compiler run")
                    continue
                argv = run["argv"]
                if not _census_argv_ok(argv, path, evidence["edition"], lowering, codegen):
                    errors.append(f"{row['file']}: {role} argv does not describe its census lane")
                if stage_closure is None or not argv or argv[0] != stage_closure["compiler"]:
                    errors.append(f"{row['file']}: {role} compiler is not bound to the stage closure")
                if (run["compiler_sha256_before"] != before
                        or run["compiler_sha256_after"] != before):
                    errors.append(f"{row['file']}: {role} compiler executable changed or unmeasured around compiler run")
                if expected[row["file"]] == "compile_fail" and run["exit_code"] == 0:
                    errors.append(f"{row['file']}: predeclared compile-failure {role} run succeeded")
                census = parse_compiler_census(run["census_raw"], input_path=path,
                                               lowering=lowering, exit_code=run["exit_code"])
                if "header" in census:
                    compiler_versions[role] = census["header"]["compiler_version"]
                    for field in ("target", "edition"):
                        if census["header"][field] != evidence[field]:
                            errors.append(f"{row['file']}: {role} compiler {field} differs from the pinned measurement")
                state = {"file": row["file"], "role": role, "status": census["status"]}
                states.append(state)
                expected_failure = (expected[row["file"]] == "compile_fail"
                                    and type(run["exit_code"]) is int and run["exit_code"] == 1
                                    and census["status"] in {"incomplete", "compiler_failed"}
                                    and "header" in census and run["error"] is None)
                if expected_failure:
                    state["status"] = "expected_compile_failure"
                else:
                    errors.extend(f"{row['file']} {role}: {error}" for error in census["errors"])
                if run["error"]:
                    errors.append(f"{row['file']} {role}: {run['error']}")
                if census["status"] == "complete":
                    completed_censuses[role] = census
                    for source in census["sources"]:
                        if source_hashes.get(source["file"]) != source["sha256"]:
                            errors.append(f"{row['file']} {role}: loaded source absent or changed from "
                                          f"precompile manifest: {source['file']} (declare auxiliary inputs with --input-source)")
                    if role == "control" and expected[row["file"]] == "ok":
                        bodies.extend({"file": row["file"], "def": body["def"], "kind": body["kind"]}
                                      for body in census["bodies"])
                if codegen:
                    mono = rust_instance_census.parse_census(
                        run["mono_raw"].encode("utf-8") if run["mono_raw"] is not None else None,
                        input_path=path, exit_code=run["exit_code"], lowering=lowering)
                    states.append({"file": row["file"], "role": role + "_mono",
                                   "status": "expected_compile_failure" if expected_failure else mono["status"]})
                    if not expected_failure:
                        errors.extend(f"{row['file']} {role} mono: {error}" for error in mono["errors"])
                    if mono["status"] == "collector_observed":
                        completed_mono[role] = mono
                        header = mono["header"]
                        if (header["schema"] != rust_instance_census.SCHEMA_V3
                                or header["codegen_requested"] is not True
                                or header["incremental"] is not False
                                or header["collection_strategy"] != "lazy"):
                            errors.append(f"{row['file']} {role}: mono collector lane is not bounded codegen v3")
                        for field in ("target", "edition", "compiler_version"):
                            expected_value = (evidence[field] if field != "compiler_version"
                                              else census.get("header", {}).get(field))
                            if header[field] != expected_value:
                                errors.append(f"{row['file']} {role}: mono {field} differs from HIR/measurement")
                        for source, digest in mono["sources"].items():
                            if source_hashes.get(source) != digest.removeprefix("sha256="):
                                errors.append(f"{row['file']} {role}: mono loaded source absent or changed from "
                                              f"precompile manifest: {source}")
                        if census["status"] == "complete":
                            hir_sources = {source["file"]: source["sha256"] for source in census["sources"]}
                            mono_sources = {source: digest.removeprefix("sha256=")
                                            for source, digest in mono["sources"].items()}
                            if hir_sources != mono_sources:
                                errors.append(f"{row['file']} {role}: codegen HIR/mono loaded sources differ")
            if len(compiler_versions) != 4:
                errors.append(f"{row['file']}: compiler version missing from one or more runs")
            elif len(set(compiler_versions.values())) != 1:
                errors.append(f"{row['file']}: compiler versions differ across metadata/codegen runs")
            if all(role in completed_censuses for role in ("control", "subject")):
                control, subject = completed_censuses["control"], completed_censuses["subject"]
                if control["bodies"] != subject["bodies"]:
                    errors.append(f"{row['file']}: subject HIR census differs from lowering-disabled control")
                for field in ("compiler_version", "target"):
                    if control["header"][field] != subject["header"][field]:
                        errors.append(f"{row['file']}: control/subject {field} differs")
            available = [(role, completed_censuses[role]) for role in (
                "control", "subject", "codegen_control", "codegen_subject")
                if role in completed_censuses]
            for source_field in ("snapshot_sources", "sources"):
                if available:
                    first_role, first = available[0]
                    baseline = {source["file"]: source["sha256"] for source in first[source_field]}
                    for role, census in available[1:]:
                        observed_sources = {source["file"]: source["sha256"]
                                            for source in census[source_field]}
                        if observed_sources != baseline:
                            errors.append(f"{row['file']}: {role} HIR {source_field} differs from {first_role}")
            subject_run = measurement["subject"]
            if (isinstance(subject_run, dict) and isinstance(subject_run.get("stderr"), str)
                    and len(subject_run["stderr"]) <= MAX_STDERR_BYTES
                    and len(subject_run["stderr"].encode("utf-8")) <= MAX_STDERR_BYTES):
                parsed_bodies, parsed_anomalies = parse_bodies(subject_run["stderr"])
                if row.get("outcome") == "ok":
                    if row.get("bodies") != parsed_bodies:
                        errors.append(f"{row['file']}: producer body rows differ from saved subject stderr")
                    if row.get("anomalies") != parsed_anomalies:
                        errors.append(f"{row['file']}: producer anomalies differ from saved subject stderr")
                    if row.get("validation") != parse_validation(subject_run["stderr"]):
                        errors.append(f"{row['file']}: producer validation differs from saved subject stderr")
                elif isinstance(row.get("outcome"), str) and row["outcome"].startswith("flag_induced_"):
                    if row.get("partial_bodies") != parsed_bodies:
                        errors.append(f"{row['file']}: partial producer rows differ from saved subject stderr")
                    if row.get("anomalies") != parsed_anomalies:
                        errors.append(f"{row['file']}: producer anomalies differ from saved subject stderr")
            for role in ("control", "subject"):
                codegen_role = "codegen_" + role
                if role in completed_censuses and codegen_role in completed_censuses:
                    if completed_censuses[role]["bodies"] != completed_censuses[codegen_role]["bodies"]:
                        errors.append(f"{row['file']}: {codegen_role} HIR/generated roster differs from metadata {role}")
            if all(role in completed_censuses for role in ("codegen_control", "codegen_subject")):
                if completed_censuses["codegen_control"]["bodies"] != completed_censuses["codegen_subject"]["bodies"]:
                    errors.append(f"{row['file']}: codegen subject HIR roster differs from control")
            if all(role in completed_mono for role in ("codegen_control", "codegen_subject")):
                control, subject = completed_mono["codegen_control"], completed_mono["codegen_subject"]
                if expected[row["file"]] == "ok":
                    observed_codegen_files += 1
                for field in control["snapshot"]:
                    if control["snapshot"][field] != subject["snapshot"][field]:
                        errors.append(f"{row['file']}: codegen subject mono {field} differs from control")
                for field in control["header"]:
                    if field != "direct_lowering" and control["header"][field] != subject["header"][field]:
                        errors.append(f"{row['file']}: codegen subject mono {field} differs from control")
                if control["sources"] != subject["sources"]:
                    errors.append(f"{row['file']}: codegen subject mono sources differ from control")
                if expected[row["file"]] == "ok" and "codegen_control" in completed_censuses:
                    hir = {body["def_path_hash"]: body for body in completed_censuses["codegen_control"]["bodies"]}
                    producer = {(body["def"], body["kind"]) for body in row.get("bodies", [])
                                if isinstance(body, dict) and isinstance(body.get("def"), str)
                                and isinstance(body.get("kind"), str)}
                    for item in control["snapshot"]["items"]:
                        mono_item_count += 1
                        if not item["definition_is_local"]:
                            mono_unrepresented["external-" + item["kind"]] += 1
                            continue
                        if item["kind"] not in {"item", "static"}:
                            mono_unrepresented[item["kind"]] += 1
                            continue
                        owner = hir.get(item["def_path_hash"])
                        if (owner is None or owner["def"] != item["def"]
                                or owner["def_kind"] != item["def_kind"]):
                            mono_unrepresented["missing-local-hir"] += 1
                            errors.append(f"{row['file']}: local mono item {item['id']} absent from HIR/generated roster")
                        elif (owner["def"], owner["kind"]) not in producer:
                            mono_unrepresented["missing-producer-row"] += 1
                            errors.append(f"{row['file']}: local mono item {item['id']} absent from producer rows")
                        else:
                            mono_matched_count += 1
        observed = [(row["file"], body.get("def"), body.get("kind"))
                    for row in files for body in row.get("bodies", []) if isinstance(body, dict)]
        if sorted(observed, key=repr) != sorted((body["file"], body["def"], body["kind"]) for body in bodies):
            errors.append("producer body rows differ from independent HIR census")
        if observed_codegen_files == 0:
            errors.append("no admitted successful codegen collector observed")
        return {"status": "incomplete" if errors else "bounded_mono_reconciled",
                "errors": errors, "bodies": bodies, "files": states,
                "mono_item_count": mono_item_count, "mono_matched_count": mono_matched_count,
                "mono_unrepresented": dict(sorted(mono_unrepresented.items())), **residual}
    except (ValueError, TypeError, KeyError, UnicodeError) as error:
        errors.append(str(error))
        return {"status": "incomplete", "errors": errors, "bodies": bodies, "files": states,
                "mono_item_count": None,
                "mono_matched_count": None, "mono_unrepresented": dict(sorted(mono_unrepresented.items())),
                **residual}


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
    # Only [in-pool] admits a file under the pin directory; everything else there,
    # listed [excluded] or not listed at all, is held out.
    pin_prefix = UI_PIN_DIR + os.sep
    pool_set = set(in_pool_pins)
    kept = [
        p for p, rel in zip(eligible, eligible_rel)
        if not rel.startswith(pin_prefix) or rel in pool_set
    ]
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
    pool_set = set(in_pool)
    removed = sum(1 for p in in_dir if p not in pool_set)
    print(f"manifest:  {os.path.relpath(UI_PIN_MANIFEST, repo)}")
    print(f"eligible:  {len(eligible_rel)} total · {len(in_dir)} under {UI_PIN_DIR}")
    print(f"excluded:  {len(excluded)} listed · {removed} held out (listed or unclassified)")
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
    cases = [
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
            # Trust (fragment honesty, 2026-08-29): a coroutine BODY (the desugared async/gen
            # state machine itself, tagged `ClosureEnv(coroutine body)`) is OUT OF FRAGMENT by
            # architecture -- retiring the family means implementing the await/poll state
            # machine (roadmap B5), not adjusting a gate. The scouted census (2026-08-28)
            # measured this family owning 158/158 Match(generic/opaque scrutinee), 36/36
            # Yield, and 122/123 UpvarRef(non-Fn env) corpus-wide. These two rows separate
            # architectural refusal from coverage debt; the headline `lowered_clean_pct`
            # NEVER moves because of them -- the in-fragment rate is an ADDITIONAL line, and
            # replacing the headline with it would be metric-gaming.
            "bodies_out_of_fragment": sum(
                1 for x in bs if "ClosureEnv(coroutine body)" in x.get("reasons", [])),
            "lowered_clean_in_fragment_pct": (
                round(100.0 * len(clean) / (len(bs) - sum(
                    1 for x in bs if "ClosureEnv(coroutine body)" in x.get("reasons", []))), 1)
                if bs and len(bs) > sum(
                    1 for x in bs if "ClosureEnv(coroutine body)" in x.get("reasons", []))
                else None),
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
            # Trust (2026-10-01): the effect-conservation gate over the LOWERED-CLEAN bodies — the
            # bodies strict's tag arm passes and the splice may take. `refused` is the gate's
            # coverage cost: each is now a strict error and never codegen. `unmeasured` = no
            # event (a pre-gate compiler reports every clean body here).
            "effect_conservation": effect_conservation_census(clean),
            "by_kind": dict(collections.Counter(b["kind"] for b in bs)),
            "clean_by_kind": dict(collections.Counter(b["kind"] for b in clean)),
            "note_class_histogram": dict(collections.Counter(b["note_class"] for b in bs)),
            # Trust (B8 step 1): the internal structure of what used to be the corpus's largest
            # anonymous class. Keyed off the note, so it re-derives from any artifact — including
            # pre-split ones, which report `rows_legacy_unsplit` and nothing else.
            "seam_declaration_blockers": seam_blocker_census(bs),
            "unsupported_count_per_body_histogram": {str(k): v for k, v in sorted(hist.items())},
            "agreed": sum(1 for b in bs if b["mode"] == "Agreed"),
            # Trust (absent-callee Stage 3): its own column, beside -- never inside -- Agreed.
            "agreed_uninterpreted_callee": sum(
                1 for b in bs if b["mode"] == "AgreedUninterpretedCallee"
            ),
            "divergences": sorted(b["def"] for b in bs if b["mode"] == "MirOracle"),
            # Trust (2026-09-02): the DERIVED-MIR channel, previously unrecorded entirely.
            # `divergences` above is channel-1 only, so a per-wave "divergences 0" line has
            # never covered a derived-channel disagreement. These four keys make it checkable
            # from the artifact instead of re-measurable only off stderr.
            #
            # `derived_mismatches` is the one to read. A body in it is NOT shipping wrong code:
            # `rustc_mir_build/src/builder/mod.rs:405` calls `flip_registry::record_green` only
            # under `DerivedVerdict::DerivedAgreed`, so a mismatched body is never flipped, and
            # `-Ztrust-ir-lower=strict` turns the same verdict into a hard error. It is a
            # DETECTED disagreement, which is the instrument working — but one nothing counted.
            #
            # `derived_mismatch_flip_shaped` is the sharpest subset: bodies channel 1 calls
            # `Agreed` while the derived channel calls Mismatch. Those are the bodies where the
            # two independent checks disagree about the same program, and the ones that would
            # flip if the derived verdict ever turned green for the wrong reason.
            "derived_agreed": sum(1 for b in bs if b.get("derived_verdict") == "DerivedAgreed"),
            "derived_unsupported": sum(
                1 for b in bs if b.get("derived_verdict") == "DerivedUnsupported"
            ),
            "derived_unmeasured": sum(1 for b in bs if b.get("derived_verdict") is None),
            "derived_mismatches": sorted(
                b["def"] for b in bs if b.get("derived_verdict") == "DerivedMismatch"
            ),
            "derived_mismatch_flip_shaped": sorted(
                b["def"]
                for b in bs
                if b.get("derived_verdict") == "DerivedMismatch" and b["mode"] == "Agreed"
            ),
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

    # Trust (attribution gap, 2026-08-20): WHICH FILES were invalid, not just how many.
    #
    # The histogram above is an aggregate over an anonymous population, and a class name cannot
    # localize a defect. Measured cost of that omission: `INVALID` moved 0 -> 2 between two
    # control artifacts and NO ONE could name the two files from the artifacts — attribution
    # required re-running the producer over the corpus against a stage1 binary that a concurrent
    # build was rewriting. The per-file `validation` block was already stored on every row, so
    # the missing piece was never the measurement; it was that nothing surfaced it.
    #
    # Derived purely from `results`, exactly like every other aggregate key, so `--rerender`
    # backfills it onto EVERY artifact already on disk at zero compile cost. `details` is
    # forwarded when the row carries it (binaries emitting the `module validation detail` event);
    # an older row simply has no such key, which must stay distinguishable from an empty one.
    _invalid_files = []
    for r in results:
        if r.get("outcome") != "ok":
            continue
        v = r.get("validation")
        if v is None or not v["total"]:
            continue
        row = {"file": r["file"], "total": v["total"], "classes": v["classes"]}
        if v.get("details") is not None:
            row["details"] = v["details"]
        _invalid_files.append(row)
    validation["invalid_files"] = _invalid_files

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


def evaluate_producer_completion(aggregate):
    """Pure, fail-closed W0 zero-residue decision for one corpus aggregate.

    This deliberately consumes only the structured aggregate, not prose, percentages, or
    per-body rows. In particular, ``lowered_clean`` is not consulted: it means only that the
    producer emitted no unsupported-shape tag, and can still include symbolic placeholders,
    opaque live-value collapse, or bodies without an affirmative semantic adjudication.

    The returned dictionary is JSON-serializable. Missing, malformed, negative, or
    type-confused acceptance fields fail their checks instead of inheriting an optimistic
    default, so pre-instrumentation artifacts remain readable but cannot pass this gate.
    """
    missing = object()

    def field(path):
        value = aggregate
        for part in path.split("."):
            if not isinstance(value, dict) or part not in value:
                return missing
            value = value[part]
        return value

    def display(value):
        return None if value is missing else value

    def count(value):
        # bool is an int subclass, but accepting True as a count would make malformed JSON pass.
        return type(value) is int and value >= 0

    checks = []

    def add(check_id, fields, predicate, expected, actual, passed):
        missing_fields = [path for path in fields if field(path) is missing]
        check = {
            "id": check_id,
            "fields": fields,
            "predicate": predicate,
            "expected": expected,
            "actual": actual,
            "passed": bool(passed) and not missing_fields,
        }
        if missing_fields:
            check["missing_fields"] = missing_fields
        checks.append(check)

    total = field("bodies.total")
    add(
        "admitted_body_denominator_nonzero",
        ["bodies.total"],
        "greater_than",
        0,
        display(total),
        count(total) and total > 0,
    )

    modelled = field("bodies.lowered_clean_modelled")
    add(
        "modelled_equals_total",
        ["bodies.lowered_clean_modelled", "bodies.total"],
        "counts_equal",
        {"modelled": "bodies.total"},
        {"modelled": display(modelled), "total": display(total)},
        count(modelled) and count(total) and modelled == total,
    )

    def add_zero(check_id, path):
        value = field(path)
        add(check_id, [path], "equals", 0, display(value), count(value) and value == 0)

    add_zero("symbolic_zero", "bodies.lowered_clean_symbolic")
    add_zero("opaque_collapse_all_zero", "bodies.opaque_collapse_all")
    add_zero("opaque_collapse_clean_zero", "bodies.lowered_clean_opaque")
    add_zero("class_unmeasured_zero", "bodies.lowered_clean_class_unmeasured")

    ok_files = field("file_outcomes.ok")
    modules_measured = field("validation.modules_measured")
    add(
        "validation_measured_equals_ok_files",
        ["validation.modules_measured", "file_outcomes.ok"],
        "counts_equal",
        {"modules_measured": "file_outcomes.ok"},
        {"modules_measured": display(modules_measured), "ok_files": display(ok_files)},
        count(modules_measured) and count(ok_files) and modules_measured == ok_files,
    )
    add_zero("validation_unmeasured_zero", "validation.modules_unmeasured")
    add_zero("validation_invalid_zero", "validation.modules_invalid")
    add_zero("validation_errors_zero", "validation.error_occurrences")

    outcomes = field("file_outcomes")
    outcomes_well_formed = (
        isinstance(outcomes, dict)
        and all(isinstance(k, str) and count(v) for k, v in outcomes.items())
    )
    flag_induced = (
        {k: v for k, v in outcomes.items() if k.startswith("flag_induced_")}
        if outcomes_well_formed else None
    )
    add(
        "flag_induced_outcomes_zero",
        ["file_outcomes"],
        "all_matching_counts_equal_zero",
        {"key_prefix": "flag_induced_", "count": 0},
        flag_induced,
        outcomes_well_formed and all(v == 0 for v in flag_induced.values()),
    )

    ice_signatures = field("flag_induced_ice_signatures")
    ice_signatures_well_formed = (
        isinstance(ice_signatures, dict)
        and all(isinstance(k, str) and count(v) for k, v in ice_signatures.items())
    )
    add(
        "flag_induced_ice_signatures_zero",
        ["flag_induced_ice_signatures"],
        "all_counts_equal_zero",
        0,
        display(ice_signatures),
        ice_signatures_well_formed and all(v == 0 for v in ice_signatures.values()),
    )

    # A timeout or a future outcome spelling must not silently shrink the admitted denominator.
    # Standalone compile failures remain the scorecard's documented pre-admission exclusion.
    unresolved_outcomes = (
        {
            k: v for k, v in outcomes.items()
            if k not in {"ok", "compile_fail"} and not k.startswith("flag_induced_")
        }
        if outcomes_well_formed else None
    )
    add(
        "unresolved_file_outcomes_zero",
        ["file_outcomes"],
        "all_unrecognized_counts_equal_zero",
        {"accepted_keys": ["ok", "compile_fail"], "count": 0},
        unresolved_outcomes,
        outcomes_well_formed and all(v == 0 for v in unresolved_outcomes.values()),
    )

    add_zero(
        "agreed_uninterpreted_callee_zero",
        "bodies.agreed_uninterpreted_callee",
    )

    divergences = field("bodies.divergences")
    add(
        "divergences_zero",
        ["bodies.divergences"],
        "empty_list",
        [],
        display(divergences),
        isinstance(divergences, list) and not divergences,
    )

    anomalies = field("parse_anomalies")
    anomalies_well_formed = (
        isinstance(anomalies, dict)
        and all(isinstance(k, str) and count(v) for k, v in anomalies.items())
    )
    add(
        "parse_anomalies_zero",
        ["parse_anomalies"],
        "all_counts_equal_zero",
        0,
        display(anomalies),
        anomalies_well_formed and all(v == 0 for v in anomalies.values()),
    )

    add_zero(
        "partial_bodies_zero",
        "partial_bodies_from_flag_induced_failures.total",
    )

    complete = all(check["passed"] for check in checks)
    return {
        "schema": "trust.trust-ir.producer-row-gate.v2",
        "scope": "corpus-local instrumented-row zero-residue",
        "result": "pass" if complete else "incomplete",
        "complete": complete,
        "does_not_establish": [
            "G1",
            "an independently complete file/body denominator",
            "G4",
            "universal semantic equivalence",
            "product completion",
        ],
        "checks": checks,
        "non_acceptance_metrics": {
            "lowered_clean": {
                "field": "bodies.lowered_clean",
                "value": display(field("bodies.lowered_clean")),
                "acceptance_condition": False,
                "meaning": "diagnostic only: zero unsupported-shape tags",
            },
            "sampled_agreement": {
                "field": "bodies.lowered_clean_modelled_agreed",
                "value": display(field("bodies.lowered_clean_modelled_agreed")),
                "acceptance_condition": False,
                "meaning": (
                    "falsification health only; applicability must be owner-signed and "
                    "universal or exhaustive refinement evidence remains authoritative"
                ),
            },
        },
    }


def evaluate_scorecard_completion(data, *, recompute_from_files=False):
    """Conjoin corpus-local decisions, optionally rebuilding aggregates from raw rows.

    ``recompute_from_files`` is required for an evidence check: a stored aggregate is a cached
    rendering aid and must not be trusted over the artifact's raw per-file measurements.
    """
    corpora = data.get("corpora") if isinstance(data, dict) else None
    errors = []
    results = {}
    if not isinstance(data, dict) or data.get("schema") != "trust.trust-ir.producer-scorecard.v1":
        errors.append("missing or unsupported producer scorecard schema")
    provenance_value = data.get("provenance") if isinstance(data, dict) else None
    provenance_ok = (
        isinstance(provenance_value, dict)
        and isinstance(provenance_value.get("repo_head"), str)
        and re.fullmatch(r"[0-9a-f]{40}|[0-9a-f]{64}", provenance_value["repo_head"])
        and isinstance(provenance_value.get("trustc_version_verbose"), str)
        and bool(provenance_value["trustc_version_verbose"])
        and provenance_value.get("rustc_log_filter") == RUSTC_LOG_FILTER
        and isinstance(provenance_value.get("compile_flags"), list)
        and all(isinstance(flag, str) for flag in provenance_value["compile_flags"])
        and type(provenance_value.get("seed")) is int
    )
    if not provenance_ok:
        errors.append("missing or malformed scorecard provenance identity")
    if not isinstance(corpora, dict):
        errors.append("missing or malformed corpora mapping")
    elif not corpora:
        errors.append("no corpora to evaluate")
    else:
        for name, corpus in corpora.items():
            aggregate_value = corpus.get("aggregate") if isinstance(corpus, dict) else None
            if recompute_from_files:
                files = corpus.get("files") if isinstance(corpus, dict) else None
                raw_error = None
                if not isinstance(files, list):
                    raw_error = "missing or malformed files list"
                else:
                    retained_census = reconcile_compiler_censuses(corpus)
                    if retained_census["errors"]:
                        raw_error = "independent compiler census: " + "; ".join(retained_census["errors"])
                    input_census = corpus.get("input_census")
                    body_census = corpus.get("body_census")
                    census_rows = (
                        input_census.get("files") if isinstance(input_census, dict) else None
                    )
                    census_ok = (
                        isinstance(input_census, dict)
                        and set(input_census)
                        == {"schema", "source", "files"}
                        and input_census.get("schema")
                        == "trust.trust-ir.producer-input-census.v1"
                        and input_census.get("source") == "precompile-content-manifest/v1"
                        and isinstance(census_rows, list)
                    )
                    if not census_ok:
                        raw_error = "missing or malformed independent input census"
                    expected_files = []
                    if raw_error is None:
                        for census_index, census_row in enumerate(census_rows):
                            row_ok = (
                                isinstance(census_row, dict)
                                and set(census_row)
                                == {"file", "sha256", "expected_outcome"}
                                and isinstance(census_row.get("file"), str)
                                and bool(census_row["file"])
                                and isinstance(census_row.get("sha256"), str)
                                and re.fullmatch(r"[0-9a-f]{64}", census_row["sha256"])
                                and census_row.get("expected_outcome") in {"ok", "compile_fail"}
                            )
                            if not row_ok:
                                raw_error = (
                                    f"malformed input_census.files[{census_index}]"
                                )
                                break
                            expected_files.append(
                                (census_row["file"], census_row["expected_outcome"])
                            )
                        if raw_error is None and len(expected_files) != len(set(expected_files)):
                            raw_error = "duplicate rows in independent input census"

                    body_census_rows = (
                        body_census.get("bodies") if isinstance(body_census, dict) else None
                    )
                    body_census_ok = (
                        isinstance(body_census, dict)
                        and set(body_census) == {"schema", "source", "bodies"}
                        and body_census.get("schema")
                        == "trust.trust-ir.producer-body-census.v1"
                        and body_census.get("source")
                        == BODY_CENSUS_SOURCE
                        and isinstance(body_census_rows, list)
                    )
                    if raw_error is None and not body_census_ok:
                        raw_error = "missing or malformed independent reachable-body census"
                    if (raw_error is None and body_census_rows != retained_census["bodies"]):
                        raw_error = "body census rows do not equal retained independent compiler output"
                    expected_bodies = []
                    if raw_error is None:
                        for census_index, census_row in enumerate(body_census_rows):
                            row_ok = (
                                isinstance(census_row, dict)
                                and set(census_row) == {"file", "def", "kind"}
                                and all(
                                    isinstance(census_row.get(field), str)
                                    and bool(census_row[field])
                                    for field in ("file", "def", "kind")
                                )
                            )
                            if not row_ok:
                                raw_error = (
                                    f"malformed body_census.bodies[{census_index}]"
                                )
                                break
                            expected_bodies.append(
                                (census_row["file"], census_row["def"], census_row["kind"])
                            )
                        if raw_error is None and len(expected_bodies) != len(
                            set(expected_bodies)
                        ):
                            raw_error = "duplicate rows in independent reachable-body census"

                    observed_files = []
                    observed_bodies = []
                    for index, row in enumerate(files):
                        if (
                            not isinstance(row, dict)
                            or not isinstance(row.get("file"), str)
                            or not row.get("file")
                            or not isinstance(row.get("outcome"), str)
                        ):
                            raw_error = f"malformed files[{index}] result"
                            break
                        observed_files.append((row["file"], row["outcome"]))
                        if not isinstance(row.get("bodies"), list) or not all(
                            isinstance(body, dict) for body in row["bodies"]
                        ):
                            raw_error = f"malformed files[{index}].bodies"
                            break
                        # A failed compilation contributes no completed body and no module that
                        # validation examined.  Letting a non-`ok` row carry optimistic body rows
                        # permits a forged artifact to satisfy the body denominator while keeping
                        # `modules_measured == ok_files == 0` -- a validation bypass.
                        if row["outcome"] != "ok" and row["bodies"]:
                            raw_error = f"non-ok files[{index}] carries completed bodies"
                            break
                        if row["outcome"].startswith("flag_induced_") and (
                            not isinstance(row.get("partial_bodies"), list)
                            or not all(isinstance(body, dict) for body in row["partial_bodies"])
                        ):
                            raw_error = f"malformed files[{index}].partial_bodies"
                            break
                        if row["outcome"] in {"ok", "flag_induced_fail", "flag_induced_ice"} \
                                and not isinstance(row.get("anomalies"), dict):
                            raw_error = f"missing or malformed files[{index}].anomalies"
                            break
                        for body_kind in ("bodies", "partial_bodies"):
                            for body_index, body in enumerate(row.get(body_kind, [])):
                                body_types_ok = (
                                    isinstance(body.get("def"), str)
                                    and bool(body.get("def"))
                                    and type(body.get("unsupported")) is int
                                    and body["unsupported"] >= 0
                                    and isinstance(body.get("reasons"), list)
                                    and all(
                                        isinstance(reason, str) and bool(reason)
                                        for reason in body["reasons"]
                                    )
                                    and len(body["reasons"]) == len(set(body["reasons"]))
                                    and body["unsupported"] == len(body["reasons"])
                                    and isinstance(body.get("kind"), str)
                                    and bool(body.get("kind"))
                                    and isinstance(body.get("mode"), str)
                                    and body["mode"]
                                    in {
                                        "Agreed",
                                        "AgreedUninterpretedCallee",
                                        "MirOracle",
                                        "NotRun",
                                    }
                                    and type(body.get("equal")) is bool
                                    and type(body.get("samples")) is int
                                    and body["samples"] >= 0
                                    and body["equal"] == (body["mode"] == "Agreed")
                                    and (
                                        body["mode"] != "Agreed" or body["samples"] > 0
                                    )
                                    and type(body.get("symbolic")) in {bool, type(None)}
                                    and type(body.get("opaque_collapse")) is bool
                                    and isinstance(body.get("note_class"), str)
                                    and isinstance(body.get("note"), str)
                                )
                                if not body_types_ok:
                                    raw_error = (
                                        f"malformed files[{index}].{body_kind}[{body_index}]"
                                    )
                                    break
                                if body_kind == "bodies":
                                    observed_bodies.append(
                                        (row["file"], body["def"], body["kind"])
                                    )
                            if raw_error:
                                break
                        if raw_error:
                            break
                        if row["outcome"] == "ok":
                            validation = row.get("validation")
                            if not isinstance(validation, dict):
                                raw_error = f"missing or malformed files[{index}].validation"
                                break
                            total = validation.get("total")
                            classes = validation.get("classes")
                            classes_ok = (
                                isinstance(classes, dict)
                                and all(
                                    isinstance(name, str)
                                    and bool(name)
                                    and type(count) is int
                                    and count >= 0
                                    for name, count in classes.items()
                                )
                            )
                            if (
                                type(total) is not int
                                or total < 0
                                or not classes_ok
                                or total != sum(classes.values())
                            ):
                                raw_error = (
                                    f"inconsistent or malformed files[{index}].validation"
                                )
                                break
                    if raw_error is None and sorted(observed_files) != sorted(expected_files):
                        raw_error = "raw file rows do not equal the independent input census"
                    if raw_error is None and sorted(observed_bodies) != sorted(expected_bodies):
                        raw_error = (
                            "differential body rows do not equal the independent "
                            "reachable-body census"
                        )
                if raw_error:
                    errors.append(f"corpus {name!r}: {raw_error}")
                    aggregate_value = {}
                else:
                    try:
                        aggregate_value = aggregate(files)
                    except (AttributeError, KeyError, TypeError, ValueError) as exc:
                        errors.append(f"corpus {name!r}: malformed raw result: {exc}")
                        aggregate_value = {}
            elif not isinstance(aggregate_value, dict):
                errors.append(f"corpus {name!r} is missing a structured aggregate")
                aggregate_value = {}
            results[name] = evaluate_producer_completion(aggregate_value)
    complete = not errors and bool(results) and all(
        result["complete"] for result in results.values()
    )
    return {
        "schema": "trust.trust-ir.producer-scorecard-row-gate.v2",
        "scope": (
            "listed corpus-local instrumented-row zero-residue gates with explicit "
            "input/body census equality"
        ),
        "result": "pass" if complete else "incomplete",
        "complete": complete,
        "does_not_establish": [
            "G1",
            "G3",
            "independence of the supplied census",
            "G4",
            "universal semantic equivalence",
            "product completion",
        ],
        "aggregate_source": "recomputed_from_files" if recompute_from_files else "stored",
        "artifact_errors": errors,
        "corpora": results,
    }


def check_completion_artifact(out_dir):
    """Print the structured completion decision for an artifact; return a gate exit code."""
    path = out_dir if out_dir.endswith(".json") else os.path.join(out_dir, "data.json")
    try:
        with open(path) as fh:
            data = json.load(fh)
    except (OSError, json.JSONDecodeError) as exc:
        result = {
            "schema": "trust.trust-ir.producer-scorecard-row-gate.v2",
            "scope": (
                "listed corpus-local instrumented-row zero-residue gates with explicit "
                "input/body census equality"
            ),
            "result": "incomplete",
            "complete": False,
            "does_not_establish": [
                "G1",
                "G3",
                "independence of the supplied census",
                "G4",
                "universal semantic equivalence",
                "product completion",
            ],
            "aggregate_source": "recomputed_from_files",
            "artifact_errors": [f"cannot read {path}: {exc}"],
            "corpora": {},
        }
    else:
        result = evaluate_scorecard_completion(data, recompute_from_files=True)
    print(json.dumps(result, indent=2, sort_keys=True))
    return 0 if result["complete"] else 1


def provenance(trustc: str, repo: str, args):
    ver = subprocess.run([trustc, "--version", "--verbose"],
                         capture_output=True, text=True).stdout.strip()
    def git(*a):
        return subprocess.run(["git", "-C", repo, *a],
                              capture_output=True, text=True).stdout.strip()
    return {
        "trustc": trustc,
        "trustc_sha256": file_sha256(trustc),
        "trustc_version_verbose": ver,
        "target": next((line.removeprefix("host: ") for line in ver.splitlines()
                        if line.startswith("host: ")), None),
        "repo_head": git("rev-parse", "HEAD"),
        "repo_describe": git("describe", "--always", "--dirty"),
        "date_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
        "host": platform.platform(),
        "rustc_log_filter": RUSTC_LOG_FILTER,
        "compile_flags": [
            "-Z trust-ir-lower", "-Z trust-verify=off", f"--edition {args.edition}",
            "-Z checksum-hash-algorithm=sha256", "-Z trust-body-census=<new-per-run-path>",
            "-Z trust-instance-census=<new-codegen-run-path> (codegen pair)", "--crate-type lib",
            "--emit=metadata (producer/HIR pair)", "--emit=link (bounded mono pair)",
            "--cap-lints allow",
        ],
        "loader_override_policy": "remove listed loader path, preload, audit, and framework overrides",
        "seed": args.seed,
        "sample_size_requested": args.sample_size,
        "timeout_per_file_s": args.timeout,
        "jobs": args.jobs,
        "control_policy": "every input; explicit -Ztrust-ir-lower=off; expected outcomes fixed before compilation",
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
        census = reconcile_compiler_censuses(corpus)
        out.append(f"- independent HIR + bounded local-codegen mono census: **{census['status']}**; "
                   f"observed mono items {census['mono_item_count']}, matched local HIR/producer "
                   f"{census['mono_matched_count']}; G1/G3 **RED**")
        if census["mono_unrepresented"]:
            out.append(f"  - mono items without a local HIR/producer match: {census['mono_unrepresented']}")
        out.append(f"  - still unmeasured: {', '.join(census['unmeasured'])}; "
                   "reachable instances, runtime roots, proc-macro I/O, build environment, "
                   "and external dependency closure")
        for error in census["errors"][:10]:
            out.append(f"  - {error}")
        completion = evaluate_producer_completion(agg)
        failed_completion_checks = [
            check["id"] for check in completion["checks"] if not check["passed"]
        ]
        if completion["complete"]:
            out.append(
                "- corpus-local instrumented-row zero-residue gate: **PASS**"
                " (does not establish G1, G3, census independence, G4, universal semantic"
                " equivalence, or product completion)"
            )
        else:
            out.append(
                "- corpus-local instrumented-row zero-residue gate: **INCOMPLETE**"
                " (does not establish G1, G3, census independence, G4, universal semantic"
                " equivalence, or product completion);"
                " failed conjuncts: "
                + ", ".join(failed_completion_checks)
            )
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
        out.append(
            f"- lowered clean (diagnostic only; **NOT an acceptance metric**;"
            f" 0 unsupported shapes): **{b['lowered_clean']} ({b['lowered_clean_pct']}%)**"
        )
        if b.get("bodies_out_of_fragment"):
            out.append(
                f"- in-fragment rate (excluding {b['bodies_out_of_fragment']} coroutine bodies"
                f" -- out of fragment by architecture, roadmap B5):"
                f" **{b['lowered_clean_in_fragment_pct']}%** (secondary; the headline above"
                f" is the rate of record)")
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
            # Trust (attribution gap): NAME the invalid files. `.get` because artifacts predating
            # this key must keep re-rendering rather than KeyError.
            for row in (v.get("invalid_files") or [])[:20]:
                out.append(f"  - INVALID `{row['file']}`: {row['classes']}")
                for det in (row.get("details") or [])[:8]:
                    out.append(f"    - {det}")
            _extra = len(v.get("invalid_files") or []) - 20
            if _extra > 0:
                out.append(f"  - ... +{_extra} more invalid file(s); full list in data.json")
        out.append(f"- by kind: {b['by_kind']} (clean: {b['clean_by_kind']})")
        out.append(f"- note-class histogram: {b['note_class_histogram']}")
        # Trust (absent-callee Stage 2 disclosure): the UNINTERPRETED-CALLEE adjudication
        # column — probe rows whose two-leg UC comparison agreed under the pairing
        # conjuncts and fence. DISCLOSED, NEVER Agreed: these rows assert "the two
        # lowerings are the same program under the assumption the absent callee is a
        # pure function of nothing" (docs/TCB.md carries the row), and they are counted
        # here precisely so they can never be confused with the Agreed column above.
        uc_hist = {}
        for f2 in corpus.get("files", []):
            for b2 in f2.get("bodies", []):
                u2 = (b2.get("row1_probe") or {}).get("uc")
                if u2:
                    uc_hist[u2["outcome"]] = uc_hist.get(u2["outcome"], 0) + 1
        if uc_hist:
            out.append(
                f"- uninterpreted-callee adjudication (DISCLOSED, never Agreed): {uc_hist}"
            )
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
        ec = b.get("effect_conservation")
        if ec is not None:
            out.append(
                f"- effect conservation (gate verdicts on lowered-clean bodies): measured "
                f"{ec['measured']} (unmeasured {ec['unmeasured']}); conserved {ec['conserved']}; "
                f"REFUSED {ec['refused']} (spliced {ec['refused_spliced']}; with a lost effect "
                f"{ec['refused_not_conserved']}; abstraction only {ec['refused_abstracted_only']}; "
                f"of them sampled-Agreed {ec['refused_agreed']}, MODELLED {ec['refused_modelled']})"
            )
            if ec["class_histogram"]:
                out.append(f"  - refusal classes: {ec['class_histogram']}")
                out.append(f"  - refusal combinations (top 20): {ec['combination_histogram']}")
        div = b["divergences"]
        div_shown = div[:10] + ([f"... +{len(div) - 10} more"] if len(div) > 10 else [])
        out.append(
            f"- sampled differential Agreed (testing evidence, not a proof): {b['agreed']};"
            f" divergences ({len(div)}): {div_shown}"
        )
        if b.get("agreed_uninterpreted_callee"):
            out.append(
                f"- agreed-uninterpreted-callee (VERDICT CLASS, disclosed, never Agreed): "
                f"{b['agreed_uninterpreted_callee']}"
            )
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
    ap.add_argument("--input-manifest", metavar="PATH",
                    help="pre-authored trust.rust.measurement-input-manifest.v1 JSON; selects exact "
                         "corpora, source hashes and expected outcomes instead of sampling; never "
                         "generated from compiler failures")
    ap.add_argument("--input-source", action="append", default=[], metavar="PATH",
                    help="additional local module/include source to hash before compilation "
                         "(repeatable); undeclared loaded sources remain incomplete")
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
    ap.add_argument("--check-completion", metavar="DIR_OR_DATA_JSON",
                    help="recompute and evaluate each fail-closed corpus-local instrumented-row "
                         "zero-residue gate from an EXISTING artifact's raw file rows and "
                         "explicit input/body censuses, print structured JSON, and exit "
                         "nonzero unless every listed corpus passes; does not establish G1, "
                         "G3, census independence, G4, or product completion; no --trustc needed")
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
    if args.check_completion:
        return check_completion_artifact(args.check_completion)
    if args.rerender:
        return rerender(args.rerender, check_only=args.rerender_check)
    if not args.trustc:
        ap.error("the following arguments are required: --trustc")
    if not args.out_dir:
        ap.error("the following arguments are required: --out-dir")
    if args.jobs < 1 or args.timeout < 1:
        ap.error("--jobs and --timeout must be positive")
    if args.input_manifest and (args.corpus or args.corpus_lock or args.input_source):
        ap.error("--input-manifest selects exact inputs; do not combine it with --corpus, --corpus-lock or --input-source")

    trustc = os.path.realpath(os.path.abspath(args.trustc))
    repo = os.path.abspath(args.repo)
    if os.path.exists(args.out_dir) and (not os.path.isdir(args.out_dir) or os.listdir(args.out_dir)):
        ap.error("--out-dir must be new or empty; existing measurement artifacts are preserved")
    os.makedirs(args.out_dir, exist_ok=True)
    if args.scratch:
        os.makedirs(args.scratch, exist_ok=True)
    scratch = tempfile.mkdtemp(prefix="trust-ir-scorecard-", dir=args.scratch)

    data = {
        "schema": "trust.trust-ir.producer-scorecard.v1",
        "provenance": provenance(trustc, repo, args),
        "corpora": {},
    }

    corpora = []
    for spec in args.corpus:
        name, _, path = spec.partition("=")
        corpora.append((name, [os.path.abspath(path)], None))
    if not args.no_ui_sample and not args.input_manifest:
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

    try:
        if args.input_manifest:
            with open(args.input_manifest, encoding="utf-8") as source:
                manifest = validate_input_manifest(_strict_json(source.read()))
            corpora = [(name, [os.path.abspath(os.path.join(repo, row["file"]))
                               for row in corpus["files"]], {"selection": "precompile-input-manifest"})
                       for name, corpus in manifest["corpora"].items()]
        else:
            manifest = validate_input_manifest(prepare_input_manifest(corpora, repo, args.input_source))
    except (OSError, ValueError) as error:
        shutil.rmtree(scratch)
        ap.error(str(error))
    # Persist the denominator BEFORE any compiler run, independent of success.
    with open(os.path.join(args.out_dir, "input-manifest.json"), "x", encoding="utf-8") as source:
        json.dump(manifest, source, indent=2, sort_keys=True)
        source.write("\n")

    for name, files, meta in corpora:
        corpus_manifest = manifest["corpora"][name]
        compiler_before = file_sha256(trustc)
        stage_before, stage_before_errors = capture_stage_closure(trustc)
        precompile_errors = current_source_errors(corpus_manifest["sources"], repo) + stage_before_errors
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
        compiler_after = file_sha256(trustc)
        stage_after, stage_after_errors = capture_stage_closure(trustc)
        for r in results:  # store repo-relative paths
            r["file"] = os.path.relpath(r["file"], repo)
        data["corpora"][name] = {
            "sample_meta": meta,
            "aggregate": aggregate(results),
            "files": results,
            "input_census": {
                "schema": "trust.trust-ir.producer-input-census.v1",
                "source": "precompile-content-manifest/v1",
                "files": corpus_manifest["files"],
            },
            "census_evidence": {
                "schema": "trust.rust.producer-census-evidence.v2",
                "repo": repo,
                "target": data["provenance"]["target"],
                "edition": args.edition,
                "input_manifest": {"schema": INPUT_MANIFEST_SCHEMA,
                                   "corpora": {"corpus": corpus_manifest}},
                "compiler_sha256_before": compiler_before,
                "compiler_sha256_after": compiler_after,
                "stage_closure_before": stage_before,
                "stage_closure_after": stage_after,
                "precompile_errors": precompile_errors,
                "postcompile_errors": (current_source_errors(corpus_manifest["sources"], repo)
                                       + stage_after_errors),
            },
        }
        census = reconcile_compiler_censuses(data["corpora"][name])
        data["corpora"][name]["body_census"] = {
            "schema": "trust.trust-ir.producer-body-census.v1",
            "source": BODY_CENSUS_SOURCE,
            "bodies": census["bodies"],
        }
        data["corpora"][name]["census_status"] = census
        print(f"[{name}] bounded HIR/mono census {census['status']}; "
              f"mono items {census['mono_item_count']}; G1/G3 red", flush=True)
        for error in census["errors"][:10]:
            print(f"WARN: [{name}] {error}", flush=True)
        print(f"[{name}] {data['corpora'][name]['aggregate']['file_outcomes']}", flush=True)

    with open(os.path.join(args.out_dir, "data.json"), "w") as fh:
        json.dump(data, fh, indent=1)
    with open(os.path.join(args.out_dir, "SCORECARD.md"), "w") as fh:
        fh.write(render_markdown(data))
    shutil.rmtree(scratch, ignore_errors=True)
    print(f"wrote {args.out_dir}/data.json and {args.out_dir}/SCORECARD.md")


if __name__ == "__main__":
    sys.exit(main())
