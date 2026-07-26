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
    "rustc_mir_build::builder=debug"
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


def classify_note(mode: str, note: str) -> str:
    """Map a differential-event (mode, note) pair to a stable class name."""
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
        return "clean-skip-extern-callee"
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
    if "oracle-panic-model" in note:
        return "clean-skip-oracle-panic-model"
    if "Inst::Undef" in note or "CheckedBinaryOp" in note:
        return "clean-skip-oracle-undef"
    if note.startswith("param count") or note.startswith("scalar param count"):
        return "clean-skip-param-cap"
    if "non-scalar parameter" in note:
        return "clean-skip-nonscalar-param"
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
    for m in SHAPE_RE.finditer(stderr):
        reasons[m.group("path")].append(m.group("what"))
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
        # Dedup the duplicated event pairs (same pattern-inline-const anomaly as the
        # count event): a body's reason list longer than its count is trimmed to count.
        cnt = unsup.get(p, 0)
        if len(body_reasons) > cnt:
            body_reasons = body_reasons[:cnt]
        bodies[p] = {
            "def": p,
            "kind": body_kind(p),
            "unsupported": cnt,
            "reasons": body_reasons,
            "equal": m.group("equal") == "true",
            "samples": int(m.group("samples")),
            "mode": mode,
            "note_class": classify_note(mode, note),
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
        return {"file": src, "outcome": "ok", "bodies": bodies, "anomalies": anomalies}
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


def collect_ui_sample(repo: str, seed: int, size: int):
    """size <= 0 means FULL POPULATION: every eligible file, no sampling.
    (size >= len(eligible) also degenerates to the full population — the
    seeded sample of the whole set, sorted, is the whole set.)"""
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
    if size <= 0:
        sample = list(eligible)  # full population (already sorted)
    else:
        rnd = random.Random(seed)
        sample = sorted(rnd.sample(eligible, min(size, len(eligible))))
    return sample, {
        "ui_root": os.path.relpath(ui_root, repo),
        "total_rs_files_excl_auxiliary_dirs": len(all_files),
        "excluded_by_content_filter": dict(filter_stats),
        "eligible": len(eligible),
        "sampled": len(sample),
        "seed": seed,
        "filters": [f"{n}: /{r.pattern}/" for n, r in UI_CONTENT_FILTERS],
    }


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
            "by_kind": dict(collections.Counter(b["kind"] for b in bs)),
            "clean_by_kind": dict(collections.Counter(b["kind"] for b in clean)),
            "note_class_histogram": dict(collections.Counter(b["note_class"] for b in bs)),
            "unsupported_count_per_body_histogram": {str(k): v for k, v in sorted(hist.items())},
            "agreed": sum(1 for b in bs if b["mode"] == "Agreed"),
            "divergences": sorted(b["def"] for b in bs if b["mode"] == "MirOracle"),
            "divergence_note_histogram": dict(collections.Counter(
                b["note"] for b in bs if b["mode"] == "MirOracle")),
        }

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
        out.append(f"- file outcomes: `{agg['file_outcomes']}`")
        out.append(f"- bodies reached (in files that fully compiled under the flag): **{b['total']}**")
        out.append(f"- lowered clean (0 unsupported shapes): **{b['lowered_clean']}"
                   f" ({b['lowered_clean_pct']}%)**")
        out.append(f"- by kind: {b['by_kind']} (clean: {b['clean_by_kind']})")
        out.append(f"- note-class histogram: {b['note_class_histogram']}")
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


def main():
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--trustc", required=True)
    ap.add_argument("--repo", default=os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
    ap.add_argument("--out-dir", required=True)
    ap.add_argument("--seed", type=int, default=20260701)
    ap.add_argument("--sample-size", type=int, default=2000,
                    help="seeded ui-sample size; 0 = FULL population (all eligible)")
    ap.add_argument("--jobs", type=int, default=8)
    ap.add_argument("--timeout", type=int, default=60)
    ap.add_argument("--edition", default="2021")
    ap.add_argument("--no-ui-sample", action="store_true")
    ap.add_argument("--corpus", action="append", default=[],
                    metavar="NAME=PATH", help="extra single-file corpus (repeatable)")
    ap.add_argument("--scratch", default=None,
                    help="scratch dir for per-run --out-dir temp dirs (default: mkdtemp)")
    args = ap.parse_args()

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
        sample, sample_meta = collect_ui_sample(repo, args.seed, args.sample_size)
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
