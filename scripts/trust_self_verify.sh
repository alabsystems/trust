#!/usr/bin/env bash
# trust_self_verify.sh — dogfood Trust's verifier on Trust's OWN compiler logic.
#
# Author: Andrew Yates. Copyright 2026 Andrew Yates. License: Apache-2.0 OR MIT.
#
# ============================================================================
# WHAT THIS ACTUALLY VERIFIES (honesty header — read before trusting the score)
# ============================================================================
# Trust's verifier ("trustc") proves memory-safety / arithmetic / bounds /
# division obligations on the Rust code it compiles. The aspiration of
# self-verification is to run trustc over the *whole* Trust compiler source and
# certify that the compiler's own functions are panic-free. That aspiration is
# NOT fully reachable today:
#
#   * The compiler crates under `compiler/` are rustc-private (`#![feature(
#     rustc_private)]`) and only build against the in-tree bootstrap sysroot,
#     not the stable host toolchain that ships with this checkout. Compiling
#     them with the stage2 `trustc` as a standalone target requires the full
#     bootstrap plumbing (`./x.py`), which this lane does not run.
#   * Many of those functions take rich rustc/HIR/MIR types whose obligations
#     the verifier does not yet model, so a raw "% proved" over them would be
#     dominated by unmodeled-type UNKNOWNs and would *understate* the verifier's
#     real strength on the logic it does model.
#
# So this FIRST, HONEST version dogfoods the verifier on a *curated corpus of
# self-contained `.rs` samples that are faithful, extracted miniatures of the
# compiler's own logic*: the bounded-index / small-integer-arithmetic / guard /
# discriminant-match / divisor-guard shapes that recur throughout trust-vcgen,
# trust-router, and trust-types (e.g. interval clamping, VC-kind dispatch,
# obligation-id arithmetic, slice/window indexing). Each sample is compiled by
# the real stage2 `trustc` in DEFAULT mode (verification on) and its per-function
# verification JSON (`TRUST_JSON:` lines, via `-Z trust-verify-output=json`) is
# collected and tallied: proved / runtime_checked / unknown / failed, plus a
# per-obligation-kind breakdown.
#
# Each sample is also LABELED for soundness:
#   * label=safe   — has NO reachable panic/overflow path. Proving its
#                    load-bearing obligation is a *superiority win*; not proving
#                    it is a *completeness gap* (NOT a failure — exit stays 0).
#   * label=unsafe — has a genuine reachable panic/overflow/OOB path. Its
#                    load-bearing obligation MUST NOT be reported `proved`.
#                    If it is, that is a FALSE PROOF (proved-but-unsafe) and the
#                    script EXITS NON-ZERO. These `unsafe` samples are the
#                    soundness tripwire that makes the dogfood meaningful.
#
# EXIT CONTRACT (matches the task):
#   * exit 0   — no false proof. Incompleteness (unknown / runtime_checked on a
#                safe sample) is reported, never fatal.
#   * exit 1   — at least one FALSE PROOF (an `unsafe` sample's load-bearing
#                obligation came back `proved`). This is a soundness regression.
#   * exit 2   — harness/setup error (e.g. corpus failed to compile at all).
#   * exit 0 (skip) — no stage2 trustc present; prints a clear notice.
#
# DETERMINISTIC & RE-RUNNABLE: a fixed corpus, sorted output, no timestamps in
# the pass/fail logic. The scorecard records the trustc path + git rev for
# provenance but the verdict does not depend on the wall clock.
#
# FULL self-verification of the rustc-private crates is future work; see
# reports/local-target-crate-verification-gap.md and the roadmap.
# ============================================================================

set -u
set -o pipefail

REPO="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
TRUSTC="${TRUSTC:-$REPO/build/host/stage2/bin/trustc}"
SCORECARD="$REPO/reports/self-verification-scorecard.md"
WORKDIR="$(mktemp -d "${TMPDIR:-/tmp}/trust_self_verify.XXXXXX")"
trap 'rm -rf "$WORKDIR"' EXIT

# No z3 link/runtime paths: the stage2 `trustc` SMT backend is the pure-Rust
# `ay` solver — it links no libz3 and dlopens none at runtime (verified
# 2026-08-01: no z3-sys/links="z3" in any Cargo.lock; `otool -L trustc` is
# z3-clean). The old comment claiming trustc "needs" z3 for the SMT backend was
# stale. Re-adding these would resurrect a dead knob.

# ---------------------------------------------------------------------------
# Graceful skip when no built compiler is present.
# ---------------------------------------------------------------------------
if [ ! -x "$TRUSTC" ]; then
    # Try common host triples before giving up.
    for host in aarch64-apple-darwin x86_64-unknown-linux-gnu host; do
        cand="$REPO/build/$host/stage2/bin/trustc"
        if [ -x "$cand" ]; then TRUSTC="$cand"; break; fi
    done
fi
if [ ! -x "$TRUSTC" ]; then
    echo "NOTICE: no built stage2 trustc found (looked at \$TRUSTC and"
    echo "        build/<host>/stage2/bin/trustc). Skipping self-verification."
    echo "        Build with ./x.py build --stage 2, then re-run."
    # Still emit a scorecard stub so downstream consumers see a deterministic file.
    {
        echo "# Trust Self-Verification Scorecard"
        echo
        echo "**Status: SKIPPED** — no built stage2 \`trustc\` was found."
        echo
        echo "Build the compiler (\`./x.py build --stage 2\`) and re-run"
        echo "\`scripts/trust_self_verify.sh\` to populate this scorecard."
    } > "$SCORECARD"
    exit 0
fi

# ---------------------------------------------------------------------------
# Corpus: self-contained miniatures of the compiler's own logic.
#
# Each entry is written as one `<name>.rs` file. The harness records, per
# sample, a `label` (safe|unsafe) and the obligation `kind` that is
# load-bearing for that label (used ONLY for the unsafe-sample false-proof
# tripwire; the full per-kind tally is collected from the JSON regardless).
#
# The samples deliberately mirror real Trust compiler shapes:
#   - bounded slice/array indexing  (trust-vcgen bounds lane, interval clamp)
#   - small-integer obligation-id / count arithmetic (trust-router, trust-types)
#   - guard-narrowed arithmetic     (interval backend `if x < K { x + 1 }`)
#   - discriminant-style match dispatch (VcKind routing)
#   - divisor-guarded division      (trust-vcgen divzero lane)
# ---------------------------------------------------------------------------

SAMPLE_NAMES=()
declare -a SAMPLE_LABEL
declare -a SAMPLE_KEYKIND

emit_sample() {
    # emit_sample <name> <label safe|unsafe> <key-kind-substring> <<'RS' ... RS
    local name="$1" label="$2" keykind="$3"
    local f="$WORKDIR/$name.rs"
    cat > "$f"
    SAMPLE_NAMES+=("$name")
    SAMPLE_LABEL+=("$label")
    SAMPLE_KEYKIND+=("$keykind")
}

build_corpus() {
    # ---- SAFE samples (superiority targets; not proving = completeness gap) ----

    # interval clamp — the trust-vcgen interval lane shape: guard then index.
    emit_sample clamp_index_guarded safe bounds <<'RS'
#![crate_type = "lib"]
// Mirrors trust-vcgen's interval-clamped bounded index (`if i < len { buf[i] }`).
pub fn lookup(buf: &[u32; 16], i: usize) -> u32 {
    if i < 16 { buf[i] } else { 0 }
}
RS

    # bitmask-bounded index — the `arr[n & MASK]` idiom (router slot tables).
    emit_sample mask_index safe bounds <<'RS'
#![crate_type = "lib"]
// Router/cache slot selection via a power-of-two mask: always in bounds.
pub fn slot(table: &[u8; 8], n: usize) -> u8 {
    table[n & 7]
}
RS

    # guard-narrowed increment — interval backend `if x < K { x + 1 }`.
    emit_sample bump_id_guarded safe overflow <<'RS'
#![crate_type = "lib"]
// Obligation-id bump under an interval guard: no overflow possible.
pub fn next_id(cur: u32) -> u32 {
    if cur < 1_000_000 { cur + 1 } else { cur }
}
RS

    # widening accumulate over fixed array — bounded reduction (vcgen #50 shape).
    emit_sample sum_widen safe overflow <<'RS'
#![crate_type = "lib"]
// Sum of bytes into a wide accumulator: 16 * 255 fits in u32, no overflow.
pub fn checksum(a: &[u8; 16]) -> u32 {
    let mut t: u32 = 0;
    for &x in a { t += x as u32; }
    t
}
RS

    # divisor-guarded division — trust-vcgen divzero lane.
    emit_sample div_guarded safe divzero <<'RS'
#![crate_type = "lib"]
// Average with an explicit nonzero-divisor guard.
pub fn avg(total: u64, count: u64) -> u64 {
    if count != 0 { total / count } else { 0 }
}
RS

    # discriminant-style dispatch returning a bounded code (VcKind routing).
    emit_sample kind_code safe overflow <<'RS'
#![crate_type = "lib"]
// VcKind-style dispatch: every arm returns a small constant; no panic path.
pub fn priority(kind: u8) -> u8 {
    match kind {
        0 => 9,
        1 => 7,
        2 => 5,
        _ => 1,
    }
}
RS

    # ---- UNSAFE samples (soundness tripwire; MUST NOT be fully proved) ----

    # unguarded index — a reachable OOB. Must NOT prove the bounds obligation.
    emit_sample index_unguarded unsafe bounds <<'RS'
#![crate_type = "lib"]
// No guard on `i`: a caller can pass i >= len -> out of bounds.
pub fn at(buf: &[u32; 16], i: usize) -> u32 {
    buf[i]
}
RS

    # unguarded add on u8 — a reachable overflow. Must NOT prove overflow:add.
    emit_sample add_unguarded unsafe overflow <<'RS'
#![crate_type = "lib"]
// `a + b` on u8 with no bound: overflows for large a,b.
pub fn add(a: u8, b: u8) -> u8 {
    a + b
}
RS

    # unguarded division — a reachable div-by-zero. Must NOT prove divzero.
    emit_sample div_unguarded unsafe divzero <<'RS'
#![crate_type = "lib"]
// No nonzero guard on the divisor: panics when count == 0.
pub fn ratio(total: u64, count: u64) -> u64 {
    total / count
}
RS

    # off-by-one index — `buf[i + 1]` under an INSUFFICIENT guard (`i < len`,
    # not `i + 1 < len`). Reachable OOB at i == len-1. Data-dependent so rustc's
    # const `unconditional_panic` lint cannot fold it away; a real bounds
    # obligation is emitted and must NOT prove.
    emit_sample index_off_by_one unsafe bounds <<'RS'
#![crate_type = "lib"]
// Classic off-by-one: the guard bounds `i`, but the access is `buf[i + 1]`.
// At i == 15 this reads buf[16] -> out of bounds.
pub fn peek_next(buf: &[u32; 16], i: usize) -> u32 {
    if i < 16 { buf[i + 1] } else { 0 }
}
RS
}

# ---------------------------------------------------------------------------
# Run trustc over one sample, capture its TRUST_JSON lines.
# ---------------------------------------------------------------------------
run_sample() {
    local name="$1"
    local src="$WORKDIR/$name.rs"
    local out="$WORKDIR/$name.rlib"
    local log="$WORKDIR/$name.log"
    "$TRUSTC" --edition 2021 --crate-type lib \
        -Z trust-verify-output=json \
        "$src" -o "$out" > "$log" 2>&1
    local rc=$?
    # Keep only the structured transport lines for the analyzer.
    grep '^TRUST_JSON:' "$log" > "$WORKDIR/$name.json" 2>/dev/null || true
    return $rc
}

# ---------------------------------------------------------------------------
# Drive the corpus, analyze with a small embedded Python (deterministic JSON
# parse + tally + scorecard render + false-proof verdict).
# ---------------------------------------------------------------------------
build_corpus

# Compile-and-collect every sample (compile failures are recorded, not fatal —
# except a *total* corpus failure, which is a harness error -> exit 2).
compiled_any=0
for i in "${!SAMPLE_NAMES[@]}"; do
    name="${SAMPLE_NAMES[$i]}"
    if run_sample "$name"; then compiled_any=1; fi
    # Even a nonzero rc can still have emitted JSON (e.g. -full rejects); the
    # analyzer reads whatever JSON was produced. We only need *some* sample to
    # have compiled to consider the harness healthy.
    if [ -s "$WORKDIR/$name.json" ]; then compiled_any=1; fi
done

if [ "$compiled_any" -eq 0 ]; then
    echo "ERROR: no corpus sample produced any verification output."
    echo "       The stage2 trustc at $TRUSTC may be broken (its SMT backend is"
    echo "       the in-tree pure-Rust \`ay\` solver — no external z3/library path)."
    exit 2
fi

GIT_REV="$(git -C "$REPO" rev-parse --short HEAD 2>/dev/null || echo unknown)"

# Build a manifest the analyzer consumes (name<TAB>label<TAB>keykind<TAB>jsonpath).
MANIFEST="$WORKDIR/manifest.tsv"
: > "$MANIFEST"
for i in "${!SAMPLE_NAMES[@]}"; do
    printf '%s\t%s\t%s\t%s\n' \
        "${SAMPLE_NAMES[$i]}" "${SAMPLE_LABEL[$i]}" "${SAMPLE_KEYKIND[$i]}" \
        "$WORKDIR/${SAMPLE_NAMES[$i]}.json" >> "$MANIFEST"
done

TRUSTC="$TRUSTC" GIT_REV="$GIT_REV" SCORECARD="$SCORECARD" MANIFEST="$MANIFEST" \
python3 - <<'PY'
import json, os, sys

manifest = os.environ["MANIFEST"]
scorecard = os.environ["SCORECARD"]
trustc = os.environ["TRUSTC"]
git_rev = os.environ["GIT_REV"]

# Outcomes we tally. timeout/skipped fold into unknown for the headline, matching
# the compiler's own emit_transport_json aggregation.
OUTCOMES = ["proved", "runtime_checked", "unknown", "failed"]

def norm_outcome(o):
    o = (o or "").lower()
    if o in ("timeout", "timed_out", "skipped"):
        return "unknown"
    if o in OUTCOMES:
        return o
    return "unknown"

samples = []
with open(manifest) as fh:
    for line in fh:
        line = line.rstrip("\n")
        if not line:
            continue
        name, label, keykind, jsonpath = line.split("\t")
        samples.append((name, label, keykind, jsonpath))

# Aggregate tallies.
totals = {o: 0 for o in OUTCOMES}
by_kind = {}        # kind -> {outcome -> count}
per_sample = []     # (name, label, keykind, key_outcome, counts dict, total)
false_proofs = []   # soundness violations

for name, label, keykind, jsonpath in samples:
    counts = {o: 0 for o in OUTCOMES}
    key_outcomes = []   # outcomes of obligations whose kind matches keykind
    if os.path.exists(jsonpath):
        with open(jsonpath) as fh:
            for raw in fh:
                raw = raw.strip()
                idx = raw.find("TRUST_JSON:")
                if idx < 0:
                    continue
                try:
                    d = json.loads(raw[idx + len("TRUST_JSON:"):])
                except json.JSONDecodeError:
                    continue
                if d.get("type") != "function_result":
                    continue
                for r in d.get("results", []):
                    kind = (r.get("kind") or "unknown").lower()
                    oc = norm_outcome(r.get("outcome"))
                    counts[oc] += 1
                    totals[oc] += 1
                    by_kind.setdefault(kind, {o: 0 for o in OUTCOMES})
                    by_kind[kind][oc] += 1
                    if keykind in kind:
                        key_outcomes.append(oc)
    total = sum(counts.values())
    # Derive the load-bearing key outcome: for an `unsafe` sample, ANY proved
    # key obligation is a false proof. For a `safe` sample, "proved" is the win.
    if "proved" in key_outcomes:
        key_outcome = "proved"
    elif "failed" in key_outcomes:
        key_outcome = "failed"
    elif "runtime_checked" in key_outcomes:
        key_outcome = "runtime_checked"
    elif "unknown" in key_outcomes:
        key_outcome = "unknown"
    else:
        key_outcome = "none"   # no obligation of the key kind surfaced

    if label == "unsafe" and key_outcome == "proved":
        false_proofs.append(
            f"{name}: unsafe sample's `{keykind}` obligation was PROVED "
            f"(reachable panic/overflow proved safe)")

    per_sample.append((name, label, keykind, key_outcome, counts, total))

# ---- Render the scorecard (deterministic; sorted) ----
per_sample.sort(key=lambda t: t[0])
kinds_sorted = sorted(by_kind.keys())
grand_total = sum(totals.values())

def pct(n, d):
    return f"{(100.0 * n / d):.1f}%" if d else "n/a"

lines = []
A = lines.append
A("# Trust Self-Verification Scorecard")
A("")
A("_Dogfooding Trust's verifier on faithful miniatures of Trust's own compiler "
  "logic. Generated by `scripts/trust_self_verify.sh`._")
A("")
A("## Provenance")
A("")
A(f"- Compiler: `{trustc}`")
A(f"- Repo revision: `{git_rev}`")
A(f"- Corpus size: {len(samples)} samples, {grand_total} obligations")
A("")
A("## What this measures (and what it does not)")
A("")
A("This is the FIRST, honest version of compiler self-verification. It runs the "
  "real stage2 `trustc` (default mode, verification on) over a curated corpus of "
  "self-contained `.rs` samples that are faithful miniatures of the bounded-index "
  "/ small-integer-arithmetic / guard / discriminant-match / divisor-guard shapes "
  "that recur throughout `trust-vcgen`, `trust-router`, and `trust-types`. It "
  "does NOT yet compile the rustc-private compiler crates as standalone "
  "verification targets (that needs the full `./x.py` bootstrap sysroot and "
  "additional obligation modeling — future work; see "
  "`reports/local-target-crate-verification-gap.md`).")
A("")
A("Soundness verdict: the corpus includes `unsafe` samples with genuine, "
  "reachable panic/overflow/OOB paths. The harness EXITS NON-ZERO only if such a "
  "sample's load-bearing obligation is reported `proved` (a false proof). "
  "Incompleteness — `unknown` or `runtime_checked` on a `safe` sample — is "
  "reported but never fatal.")
A("")
A("## Headline tally")
A("")
A("| Outcome | Count | Share |")
A("|---|---:|---:|")
for o in OUTCOMES:
    A(f"| {o} | {totals[o]} | {pct(totals[o], grand_total)} |")
A(f"| **total** | **{grand_total}** | 100% |")
A("")
proved_safe = totals["proved"]
A(f"**Proved obligations: {totals['proved']} / {grand_total} "
  f"({pct(totals['proved'], grand_total)}).** "
  f"Runtime-checked (sound, dynamically guarded): {totals['runtime_checked']}. "
  f"Unknown (completeness frontier): {totals['unknown']}. "
  f"Failed (refuted, fail-closed): {totals['failed']}.")
A("")
A("## Per-obligation-kind breakdown")
A("")
A("| Kind | proved | runtime_checked | unknown | failed |")
A("|---|---:|---:|---:|---:|")
for k in kinds_sorted:
    c = by_kind[k]
    A(f"| `{k}` | {c['proved']} | {c['runtime_checked']} | {c['unknown']} | {c['failed']} |")
A("")
A("## Per-sample results")
A("")
A("`label=safe` → proving is a superiority win, not-proving is a completeness "
  "gap (non-fatal). `label=unsafe` → load-bearing obligation must NOT be "
  "`proved`; a `proved` here is a FALSE PROOF and fails the run.")
A("")
A("| Sample | label | key kind | key outcome | proved | rtc | unknown | failed |")
A("|---|---|---|---|---:|---:|---:|---:|")
for name, label, keykind, key_outcome, counts, total in per_sample:
    flag = ""
    if label == "unsafe" and key_outcome == "proved":
        flag = " ❌FALSE-PROOF"
    A(f"| `{name}` | {label} | `{keykind}` | {key_outcome}{flag} | "
      f"{counts['proved']} | {counts['runtime_checked']} | "
      f"{counts['unknown']} | {counts['failed']} |")
A("")

# Soundness section.
A("## Soundness verdict")
A("")
if false_proofs:
    A("**RESULT: FALSE PROOF DETECTED — soundness regression.** The verifier "
      "reported a reachable-panic obligation as proved:")
    A("")
    for fp in false_proofs:
        A(f"- ❌ {fp}")
    A("")
    A("This must be fixed before any release-evidence claim. The script exits "
      "non-zero.")
else:
    A("**RESULT: NO FALSE PROOF.** Every `unsafe` sample's reachable "
      "panic/overflow/OOB obligation was correctly NOT proved (failed, "
      "runtime-checked, or unknown — all sound). The verifier did not certify "
      "any unsafe self-code as safe.")
A("")

# Completeness note (informational).
unsafe_keys = [(n, k, ko) for (n, l, k, ko, c, t) in per_sample if l == "safe" and ko != "proved"]
if unsafe_keys:
    A("### Completeness frontier (safe samples not yet fully proved)")
    A("")
    A("These are NOT failures — they are proving-capability gaps to close:")
    A("")
    for n, k, ko in sorted(unsafe_keys):
        A(f"- `{n}` (`{k}`): key outcome `{ko}`")
    A("")

with open(scorecard, "w") as fh:
    fh.write("\n".join(lines) + "\n")

# Console summary.
print(f"self-verify: {len(samples)} samples, {grand_total} obligations | "
      f"proved={totals['proved']} rtc={totals['runtime_checked']} "
      f"unknown={totals['unknown']} failed={totals['failed']}")
print(f"scorecard -> {scorecard}")
if false_proofs:
    print("SOUNDNESS: FALSE PROOF DETECTED:")
    for fp in false_proofs:
        print("  -", fp)
    sys.exit(1)
print("SOUNDNESS: no false proof (all unsafe samples correctly not-proved).")
sys.exit(0)
PY
analyzer_rc=$?

echo "scorecard written: $SCORECARD"
exit $analyzer_rc
