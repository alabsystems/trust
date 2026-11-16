#!/usr/bin/env bash
# Trust clean-certification gate (advisory-lane kernel-Certified self-test).
#
# The superiority gate proves SAFE code is statically discharged (0 runtime
# checks). THIS gate proves the STRONGER property for the obligation classes the
# clean theorem prover can kernel-certify: clean's `Certified` tier actually
# FIRES on real compiled programs when advisory verification is requested.
#
# A `Certified` obligation was re-proved AND re-checked by the clean CIC kernel
# (`TypeChecker::check_type`, `infer_only = false`) with ZERO trust in the SMT
# solver — the de Bruijn criterion — so the solver is OUTSIDE the trusted base
# and codegen may soundly elide the runtime check.
#
# The judgment is PER OBLIGATION, read from the compiler's own
# `-Ztrust-verify-output=json` rows (`results[].proof_evidence.strength.assurance`).
# Every fixture below exists for its SLICE BOUNDS obligation (kind `slice`,
# `SliceBoundsCheck`, id `…:bounds_check:N`):
#
#   clean_certified/proved/*.rs  -> exit 0, at least one bounds row, and EVERY
#                                   bounds row proved with Certified assurance
#                                   (clean's kernel independently re-checked it).
#   clean_certified/mutant/*.rs  -> at least one bounds row is NOT proved (the bug
#                                   is visible), and NO bounds row carries
#                                   Certified assurance (clean never certifies the
#                                   buggy obligation).
#
# Per obligation, not per crate (2026-10-06, SUPERIORITY-GATE-DEAD): the old
# check failed a mutant on ANY "of which N kernel-certified" note, so it went red
# on mutants whose Certified rows are genuinely true — the `unreachable` arm of
# for_range/rev_range and the guarded `i += 1` of while_range (measured on w17) —
# while the mutated bounds rows were refuted and uncertified. And it read a
# compile that printed nothing as "0 certified = sound": with every compile dead
# it printed four `PASS  mutant` rows. No rows now means no PASS.
#
# This is the acceptance test for the clean engagement: it catches both a
# regression of the certification path (safe obligation no longer certified) and
# the cardinal soundness bug (a false `Certified` on an unsafe obligation).
#
# SOLVER: as in trust_superiority_gate.sh, trustc resolves its `ay` itself and
# this gate passes nothing. Since plan P4 / T4.1 (2026-10-10) trustc links its ay
# and spawns none, so the sibling check below is a toolchain-completeness
# preflight kept fail-closed, not a solver selection. It used to `export
# AY_PATH=…`, which trustc has refused since 80a35e2c7e (2026-07-14), so this
# release row measured nothing until 2026-10-06. Compiles run under `env -i`, and
# the gate exits 2 ("GATE CANNOT RUN") when no proved fixture produced a single
# verification row. Reuses the superiority fixtures (the proved/mutant pairs whose
# contradiction lives in clean's zero-trust linear-Int fragment: guard-bounded
# slice + range loops). Needs python3 to read the JSON rows.
#
# Exit status: 0 GREEN, 1 RED (a measured row failed), 2 GATE CANNOT RUN.
#
# Author: Andrew Yates. Copyright 2026 Andrew Yates.
set -uo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
TRUSTC="${TRUSTC:-$REPO_ROOT/build/host/stage2/bin/trustc}"
SUP="$REPO_ROOT/tests/trust-falsification/superiority"
CLEAN_PATH='/usr/bin:/bin:/usr/sbin:/sbin'
# No z3/LIBRARY_PATH export: the `ay` SMT solver is pure-Rust and stage2 `trustc`
# links no libz3 (verified 2026-08-01: no z3-sys/links="z3" in any Cargo.lock;
# `otool -L trustc` is z3-clean). Re-adding one would resurrect a dead knob.

# Fixtures whose proved obligation's contradiction lies in clean's ZERO-TRUST
# linear-Int Farkas fragment (so the clean kernel can independently re-check it).
# Guard-bounded slice indexing and range-loop bounds qualify; modulo/bitmask/
# clamp/2D do NOT (they need modular/clamp reasoning outside the Farkas fragment
# and prove via the interval backend → Trusted, not Certified).
CERTIFIABLE=(
  guarded_slice_bound
  for_range_index_bound
  while_range_index_bound
  rev_range_index_bound
)

cannot_run() {
  printf 'GATE CANNOT RUN: %s\n' "$*"
  printf 'CLEAN CERTIFICATION GATE: CANNOT RUN — no verdict was measured (exit 2)\n'
  exit 2
}

if [ ! -x "$TRUSTC" ]; then
  cannot_run "trustc not found at $TRUSTC (build it: ./x.py build --stage 2 compiler/rustc library/std)"
fi
AY_SIBLING="$(dirname "$TRUSTC")/ay"
if [ ! -x "$AY_SIBLING" ]; then
  cannot_run "no executable ay solver beside trustc at $AY_SIBLING; the toolchain under test is incomplete (this gate no longer builds one or passes a solver path)"
fi
PYTHON3="$(command -v python3 || true)"
if [ -z "$PYTHON3" ]; then
  cannot_run "python3 is required to read the compiler's JSON verification rows"
fi

TMPDIR_GATE="$(mktemp -d)" || cannot_run "could not create a temporary directory"
trap 'rm -rf "$TMPDIR_GATE"' EXIT
mkdir -p "$TMPDIR_GATE/home" "$TMPDIR_GATE/tmp" "$TMPDIR_GATE/work" \
  || cannot_run "could not populate $TMPDIR_GATE"

# compile_fixture <fixture.rs> <output-file>: advisory verify with JSON rows,
# stdout+stderr to the file; returns trustc's exit status. The environment is
# fixed, not inherited.
compile_fixture() {
  env -i PATH="$CLEAN_PATH" HOME="$TMPDIR_GATE/home" TMPDIR="$TMPDIR_GATE/tmp" \
    LC_ALL=C LANG=C TZ=UTC \
    "$TRUSTC" --edition 2021 --crate-type lib -Z trust-policy=advisory \
    -Z trust-verify-output=json "$1" \
    -o "$TMPDIR_GATE/work/$(basename "$1").rlib" >"$2" 2>&1
}

# judge_rows <proved|mutant> <output-file> <rc> -> "PASS <detail>" | "FAIL <detail>"
JUDGE_PY='
import json, sys

lane, path, rc = sys.argv[1], sys.argv[2], int(sys.argv[3])
BOUNDS_TYPED = {"SliceBoundsCheck", "IndexOutOfBounds"}
BOUNDS_KIND = {"slice", "index"}

def typed_name(row):
    t = row.get("typed_kind")
    if isinstance(t, str):
        return t
    if isinstance(t, dict) and len(t) == 1:
        return next(iter(t))
    return ""

def is_bounds(row):
    # Broad on purpose: every reading widens what the mutant lane forbids and
    # what the proved lane must certify.
    return (":bounds_check:" in str(row.get("obligation_id", ""))
            or typed_name(row) in BOUNDS_TYPED
            or row.get("kind") in BOUNDS_KIND)

def assurances(node):
    if isinstance(node, dict):
        for key, value in node.items():
            if key == "assurance":
                yield value
            else:
                yield from assurances(value)
    elif isinstance(node, list):
        for value in node:
            yield from assurances(value)

def certified(row):
    return "Certified" in set(assurances(row))

def label(row):
    return "%s(%s)" % (":".join(str(row.get("obligation_id", "?")).split(":")[-2:]), row.get("outcome"))

rows, functions = [], 0
with open(path, encoding="utf-8", errors="replace") as handle:
    for line in handle:
        if not line.startswith("TRUST_JSON:"):
            continue
        try:
            record = json.loads(line[len("TRUST_JSON:"):])
        except ValueError:
            print("FAIL unparseable TRUST_JSON record")
            sys.exit(0)
        if record.get("type") != "function_result":
            continue
        functions += 1
        results = record.get("results")
        if not isinstance(results, list):
            print("FAIL function_result without a results list")
            sys.exit(0)
        rows.extend(r for r in results if isinstance(r, dict))

if functions == 0:
    print("FAIL no verification summary (no function_result row; compile error?)")
    sys.exit(0)
bounds = [r for r in rows if is_bounds(r)]
cert_bounds = [r for r in bounds if certified(r)]
other_cert = sum(1 for r in rows if certified(r) and not is_bounds(r))
if not bounds:
    print("FAIL no slice bounds obligation among %d row(s): the obligation this fixture exists for is gone or renamed" % len(rows))
    sys.exit(0)
if lane == "proved":
    weak = [r for r in bounds if not (certified(r) and r.get("outcome") == "proved")]
    if rc != 0:
        print("FAIL compile exited %d" % rc)
    elif weak:
        print("FAIL NOT clean-certified: bounds row(s) %s lack Certified assurance"
              % ", ".join(label(r) for r in weak))
    else:
        print("PASS CLEAN-CERTIFIED: %d bounds obligation(s) kernel-re-checked (zero-trust)" % len(cert_bounds))
else:
    unproved = [r for r in bounds if r.get("outcome") != "proved"]
    if cert_bounds:
        print("FAIL FALSE CERTIFIED: clean certified the unsafe bounds obligation(s) %s"
              % ", ".join(label(r) for r in cert_bounds))
    elif not unproved:
        print("FAIL bounds obligation(s) %s proved without certification: the mutation is not visible"
              % ", ".join(label(r) for r in bounds))
    else:
        print("PASS sound: clean refused to certify the buggy bounds obligation(s) %s"
              " (%d other row(s) Certified)" % (", ".join(label(r) for r in unproved), other_cert))
'

judge() {
  local lane=$1 fixture=$2 out="$TMPDIR_GATE/compile.out" rc
  compile_fixture "$fixture" "$out"
  rc=$?
  "$PYTHON3" -I -c "$JUDGE_PY" "$lane" "$out" "$rc" 2>&1 || printf 'FAIL the JSON judge crashed\n'
}

# Warm ay + every certifiable fixture once (absorb debug-ay cold start, which can
# leave the first cold query runtime-checked / un-certified — see superiority
# gate). The warm-up is also the PREFLIGHT: if no proved fixture produced a
# single verification row, nothing below can be judged.
rows_seen=0
first_silent=''
for name in "${CERTIFIABLE[@]}"; do
  f="$SUP/proved/$name.rs"
  [ -e "$f" ] || continue
  compile_fixture "$f" "$TMPDIR_GATE/warm.out"
  if LC_ALL=C grep -aq '^TRUST_JSON:.*"type": *"function_result"' "$TMPDIR_GATE/warm.out"; then
    rows_seen=$((rows_seen + 1))
  elif [ -z "$first_silent" ]; then
    first_silent="$name: $(LC_ALL=C grep -a -m1 '^error' "$TMPDIR_GATE/warm.out" || true)"
  fi
done
if [ "$rows_seen" -eq 0 ]; then
  cannot_run "no proved fixture produced a verification row; first: ${first_silent:-<no proved fixture present>}"
fi

failed=0

for name in "${CERTIFIABLE[@]}"; do
  f="$SUP/proved/$name.rs"
  if [ ! -e "$f" ]; then
    echo "FAIL  proved   $name  — fixture missing"; failed=1; continue
  fi
  # Retry once: a real regression fails both attempts; a cold-start miss clears.
  verdict=''
  for _ in 1 2; do
    verdict="$(judge proved "$f")"
    case $verdict in PASS*) break ;; esac
  done
  case $verdict in
    PASS*) echo "PASS  proved   $name  — ${verdict#PASS }" ;;
    *) echo "FAIL  proved   $name  — ${verdict#FAIL }"; failed=1 ;;
  esac
done

for name in "${CERTIFIABLE[@]}"; do
  f="$SUP/mutant/$name.rs"
  if [ ! -e "$f" ]; then
    echo "FAIL  mutant   $name  — fixture missing"; failed=1; continue
  fi
  verdict="$(judge mutant "$f")"
  case $verdict in
    PASS*) echo "PASS  mutant   $name  — ${verdict#PASS }" ;;
    *) echo "FAIL  mutant   $name  — ${verdict#FAIL }"; failed=1 ;;
  esac
done

if [ "$failed" -eq 0 ]; then
  echo "CLEAN CERTIFICATION GATE: GREEN — clean kernel-certifies safe code, never certifies unsafe code"
  exit 0
else
  echo "CLEAN CERTIFICATION GATE: RED — certification regressed, or a false Certified was minted"
  exit 1
fi
