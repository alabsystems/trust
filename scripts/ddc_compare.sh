#!/usr/bin/env bash
# ddc_compare.sh — Diverse Double-Compilation (DDC) HARNESS SKELETON.
#
# ==========================================================================
#  WHAT THIS IS — AND WHAT IT IS NOT
# ==========================================================================
#  DDC (David A. Wheeler, "Fully Countering Trusting Trust through Diverse
#  Double-Compilation") defeats a Thompson trusting-trust backdoor by compiling
#  a compiler's SOURCE with TWO compilers of DISJOINT lineage and checking that
#  both, after a fixed-point re-compile, yield a BYTE-IDENTICAL stage-2 compiler.
#  A backdoor in one toolchain cannot survive into the other's output unless the
#  SAME backdoor independently exists in both — which disjoint lineages preclude.
#
#  This script wires up the MECHANISM: take two rustc paths A and B, build Trust
#  source with each, diff the stage2 outputs. It is a reusable harness.
#
#  IT IS *NOT* A THOMPSON RESULT ON THIS HOST.
#  A genuinely lineage-disjoint toolchain B does NOT exist on this single
#  arm64-apple-darwin machine: the only seed is the Homebrew rustc 1.96.0, and the
#  Trust toolchain was itself built from that same seed. Running A=Trust-stage0,
#  B=Homebrew is therefore a MECHANISM REHEARSAL ONLY — it proves the harness
#  works and surfaces nondeterminism; it does NOT close the Thompson loop because
#  B shares A's lineage. Closing the loop requires a disjoint toolchain B (e.g. an
#  upstream rust-lang nightly that never passed through Homebrew/Trust, or a
#  Mes -> tinycc -> rustc bootstrap chain) and ideally a second machine / CI.
#
#  This script REFUSES to print "Thompson defeated" under any circumstances. The
#  strongest claim it will emit is "mechanism rehearsal: A and B produced
#  byte-identical / differing stage2 trustc", annotated with the lineage caveat.
#
# ==========================================================================
#  USAGE
# ==========================================================================
#   scripts/ddc_compare.sh <rustc-A> <rustc-B> [--disjoint] [--dry-run]
#                          [--artifact PATH] [--log DIR]
#
#   <rustc-A>, <rustc-B>  paths to two rustc executables, or a token:
#                           "homebrew"      -> /opt/homebrew/bin/rustc
#                           "config-stage0" -> config.toml [build].rustc seed
#                           "trust-stage2"  -> build/host/stage2/bin/trustc
#                         (On this host config-stage0 == homebrew: same lineage.)
#   --disjoint            ASSERT (operator's responsibility) that A and B are
#                         lineage-disjoint. Without it, output is labeled
#                         "mechanism rehearsal (NOT lineage-disjoint)".
#   --dry-run             print the plan + the two build commands, build nothing.
#   --artifact PATH       which stage2 artifact to diff (default: the trustc
#                         driver binary). May be repeated.
#
# ==========================================================================
#  EXIT CODES
# ==========================================================================
#   0  the two stage2 outputs were byte-identical
#   1  they differed (expected unless source build is fully deterministic AND
#      the two toolchains agree)
#   2  setup / build failure
#
# ==========================================================================
#  DETERMINISM PREREQUISITE
# ==========================================================================
#  DDC requires the source build to be REPRODUCIBLE first — otherwise A-vs-A
#  already differs and the comparison is meaningless. Validate that separately
#  with scripts/repro_build_selfcompare.sh BEFORE trusting a DDC mismatch as
#  "lineage divergence" rather than "build nondeterminism". This script applies
#  the same neutralizers (SOURCE_DATE_EPOCH + --remap-path-prefix).

set -euo pipefail

REPO_ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$REPO_ROOT"

HOST_TRIPLE="${TRUST_HOST_TRIPLE:-$(uname -m | sed 's/arm64/aarch64/')-apple-darwin}"
EPOCH="${TRUST_REPRO_EPOCH:-1000000000}"
LOGDIR="${TRUST_DDC_LOGDIR:-reports/ddc-rehearsal}"
DRY_RUN=0
DISJOINT=0
declare -a ARTIFACTS

resolve_rustc() {
  case "$1" in
    homebrew)      echo "/opt/homebrew/bin/rustc" ;;
    # The configured stage0 (bring-your-own seed) — on this host that is the
    # Homebrew rustc, see config.toml [build].rustc. Read it live rather than
    # hard-coding so the token stays correct if the seed changes.
    config-stage0) grep -E '^[[:space:]]*rustc[[:space:]]*=' "${REPO_ROOT}/config.toml" \
                     | head -1 | sed -E 's/.*=[[:space:]]*"?([^"]*)"?.*/\1/' ;;
    # The Trust-built stage2 compiler (Trust lineage, but built FROM the seed —
    # still NOT lineage-disjoint from it).
    trust-stage2)  echo "${REPO_ROOT}/build/host/stage2/bin/trustc" ;;
    *)             echo "$1" ;;
  esac
}

if [ $# -lt 2 ]; then
  sed -n '2,70p' "$0"; exit 2
fi
RUSTC_A_RAW="$1"; RUSTC_B_RAW="$2"; shift 2
while [ $# -gt 0 ]; do
  case "$1" in
    --disjoint) DISJOINT=1; shift ;;
    --dry-run)  DRY_RUN=1; shift ;;
    --artifact) ARTIFACTS+=("$2"); shift 2 ;;
    --log)      LOGDIR="$2"; shift 2 ;;
    -h|--help)  sed -n '2,70p' "$0"; exit 0 ;;
    *) echo "unknown arg: $1" >&2; exit 2 ;;
  esac
done

RUSTC_A="$(resolve_rustc "$RUSTC_A_RAW")"
RUSTC_B="$(resolve_rustc "$RUSTC_B_RAW")"

if [ "${#ARTIFACTS[@]}" -eq 0 ]; then
  ARTIFACTS=("build/${HOST_TRIPLE}/stage2/bin/trustc")
fi

mkdir -p "$LOGDIR"
STAMP="$(date +%Y%m%d-%H%M%S)"
LOG="${LOGDIR}/ddc-${STAMP}.log"
log() { echo "$@" | tee -a "$LOG"; }

if [ "$DISJOINT" -eq 1 ]; then
  CLAIM_BANNER="DDC RUN (operator asserts A and B are lineage-DISJOINT)"
else
  CLAIM_BANNER="DDC MECHANISM REHEARSAL — NOT a Thompson result (A and B NOT asserted lineage-disjoint)"
fi

log "=================================================================="
log " ${CLAIM_BANNER}"
log "=================================================================="
log "rustc A : ${RUSTC_A_RAW} -> ${RUSTC_A}"
log "rustc B : ${RUSTC_B_RAW} -> ${RUSTC_B}"
log "host    : ${HOST_TRIPLE}"
log "epoch   : ${EPOCH}"
log "artifacts to diff:"; for a in "${ARTIFACTS[@]}"; do log "    ${a}"; done
log ""
if [ "$DISJOINT" -eq 0 ]; then
  log "NOTE: On this host the only rustc lineage is the Homebrew 1.96.0 seed and the"
  log "      Trust toolchain built from it. A and B therefore share lineage; a"
  log "      matching result here proves the HARNESS + build determinism, NOT that"
  log "      Thompson trusting-trust is defeated. Closing the loop needs a disjoint B"
  log "      (upstream rust-lang nightly, or Mes->tinycc->rustc) and ideally a 2nd host."
  log ""
fi

# Determinism neutralizers (same as repro_build_selfcompare.sh).
export SOURCE_DATE_EPOCH="$EPOCH"
export RUSTFLAGS="--remap-path-prefix=${REPO_ROOT}=/trust-source --remap-path-prefix=${HOME}=/home/trust"
export RUSTC_BOOTSTRAP=1
export LIBRARY_PATH="${LIBRARY_PATH:-/opt/homebrew/lib}"

build_with() {
  # $1 = rustc path, $2 = tag
  local rustc="$1" tag="$2"
  log "--- [${tag}] clean stage2 outputs, build Trust with rustc=${rustc} ---"
  local cmd=(python3 x.py build --stage 2)
  log "    RUSTC=${rustc} SOURCE_DATE_EPOCH=${EPOCH} \\"
  log "    RUSTFLAGS='${RUSTFLAGS}' \\"
  log "    ${cmd[*]}"
  if [ "$DRY_RUN" -eq 1 ]; then
    log "    [dry-run] not executed"
    return 0
  fi
  if [ ! -x "$rustc" ]; then
    log "    ERROR: rustc not executable: ${rustc}"; exit 2
  fi
  # Full stage2 rebuild from the given seed compiler.
  rm -rf "build/${HOST_TRIPLE}/stage2" "build/${HOST_TRIPLE}/stage2-rustc" \
         "build/${HOST_TRIPLE}/stage2-codegen"
  if ! RUSTC="$rustc" "${cmd[@]}" >>"${LOG}.build-${tag}" 2>&1; then
    log "    BUILD ${tag} FAILED — see ${LOG}.build-${tag}"; exit 2
  fi
}

snapshot() {
  # $1 = tag; copies the artifacts under LOGDIR with the tag.
  local tag="$1" a base
  for a in "${ARTIFACTS[@]}"; do
    base="$(basename "$a")"
    if [ -f "$a" ]; then
      cp "$a" "${LOGDIR}/${base}.${tag}.${STAMP}"
      log "    snapshot ${tag}: ${base} sha256=$(shasum -a 256 "$a" | awk '{print $1}')"
    else
      log "    snapshot ${tag}: MISSING ${a}"
    fi
  done
}

build_with "$RUSTC_A" A
[ "$DRY_RUN" -eq 0 ] && snapshot A
build_with "$RUSTC_B" B
[ "$DRY_RUN" -eq 0 ] && snapshot B

if [ "$DRY_RUN" -eq 1 ]; then
  log ""
  log "[dry-run] plan printed; no builds run, no comparison performed."
  exit 0
fi

log ""
log "=== STAGE2 OUTPUT COMPARISON ==="
RC=0
for a in "${ARTIFACTS[@]}"; do
  base="$(basename "$a")"
  fa="${LOGDIR}/${base}.A.${STAMP}"
  fb="${LOGDIR}/${base}.B.${STAMP}"
  if [ ! -f "$fa" ] || [ ! -f "$fb" ]; then
    log "  ${base}: MISSING snapshot(s) — cannot compare"; RC=2; continue
  fi
  if cmp -s "$fa" "$fb"; then
    log "  ${base}: BYTE-IDENTICAL"
  else
    log "  ${base}: DIFFER"
    log "    sha256(A)=$(shasum -a 256 "$fa" | awk '{print $1}')"
    log "    sha256(B)=$(shasum -a 256 "$fb" | awk '{print $1}')"
    log "    first diff: $(cmp -l "$fa" "$fb" 2>/dev/null | head -1)"
    log "    differing bytes (common length): $(cmp -l "$fa" "$fb" 2>/dev/null | wc -l | tr -d ' ')"
    [ "$RC" -eq 0 ] && RC=1
  fi
done

log ""
if [ "$DISJOINT" -eq 1 ]; then
  if [ "$RC" -eq 0 ]; then
    log "RESULT: stage2 outputs byte-identical across asserted-disjoint A and B."
    log "        (Validity depends on the operator's --disjoint assertion being TRUE.)"
  else
    log "RESULT: stage2 outputs DIFFER. Either build nondeterminism (run"
    log "        repro_build_selfcompare.sh) or genuine lineage divergence."
  fi
else
  log "RESULT (MECHANISM REHEARSAL — NOT a Thompson result): see per-artifact lines."
  log "        A and B are not asserted lineage-disjoint; this validates the harness"
  log "        and surfaces nondeterminism only."
fi
log "log: ${LOG}"
exit "$RC"
