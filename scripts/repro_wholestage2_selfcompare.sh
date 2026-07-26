#!/usr/bin/env bash
# repro_wholestage2_selfcompare.sh — WHOLE-STAGE2 reproducible-build SELF-COMPARE.
#
# PURPOSE
#   Extend scripts/repro_build_selfcompare.sh (which proved the trust_cg backend
#   dylib reproduces byte-identically) to the WHOLE determinism-relevant stage2
#   artifact set:
#     (a) bin/trustc                          — the user-facing driver shim/binary
#     (b) librustc_driver-*.dylib             — the LLVM-carrying compiler dylib
#     (c) libstd / libcore / libcompiler_builtins rlibs — the std/compiler rlibs
#     (d) librustc_codegen_trust_cg.dylib     — the verified backend (re-confirm)
#   Build the set TWICE, INDEPENDENTLY (forced recompile/relink + sysroot
#   reassembly, NOT a cached no-op), with the determinism neutralizers, then
#   byte-compare EACH artifact and HONESTLY characterize per-artifact MATCH/DIFFER.
#
#   This is the DDC PREREQUISITE widened from one artifact to whole-stage2. It is
#   NOT a Thompson result and NOT a DDC run (that needs a lineage-disjoint
#   toolchain B, absent on this host).
#
# INDEPENDENCE (load-bearing — a cached rebuild is meaningless)
#   Between builds A and B we delete, in stage2-rustc:
#     - the rustc_driver / rustc_driver_impl crate fingerprints + emitted dylibs
#     - the rustc_codegen_trust_cg fingerprint + dylib (re-confirm baseline)
#   and in the assembled stage2 sysroot:
#     - bin/trustc and the whole rustlib/<host>/lib tree
#   so bootstrap genuinely recompiles+relinks the driver and reassembles the
#   sysroot. Stage0/stage1 stay cached (keeps each build inside the time-box).
#   The build logs are grepped afterwards for "Compiling rustc_driver" /
#   "Assembling" evidence; if neither fires the run is flagged NON-INDEPENDENT.
#
# NEUTRALIZERS (env; bootstrap.py preserves a pre-set RUSTFLAGS)
#   - SOURCE_DATE_EPOCH      : fixed epoch — kill timestamp fields
#   - --remap-path-prefix    : repo root + $HOME -> stable logical paths
#     (load-bearing for the driver, which is built WITH debuginfo and so embeds
#      source paths — unlike the release backend dylib where it was a no-op.)
#
# HONESTY
#   Reports the REAL per-artifact result. The prior rung predicted the driver is
#   the LIKELY divergence site (LLVM codegen / debuginfo nondeterminism). If it
#   differs, this script characterizes WHERE (first offset, Mach-O section) and
#   WHY (debuginfo / symtab / embedded path / archive member order) — that
#   characterization IS the deliverable (the nondeterminism work-list), NOT a
#   failure. It does not retry, massage, or hide differences.
#
# USAGE
#   scripts/repro_wholestage2_selfcompare.sh [--keep] [--log DIR] [--full-clean]
#   Env overrides:
#     TRUST_REPRO_EPOCH    (default 1000000000)
#     TRUST_REPRO_LOGDIR   (default reports/repro-wholestage2)
#     TRUST_BUILD_TIMEOUT  (per-build wall-clock guard in seconds, default 1500 = 25m)
#
# EXIT CODES
#   0  every artifact byte-identical (whole-stage2 reproducible)
#   1  one or more artifacts differ (nondeterminism present — the honest work-list)
#   2  setup/build/independence failure

set -uo pipefail   # NOT -e: we want to characterize differs, not abort on cmp rc=1

REPO_ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$REPO_ROOT"

HOST_TRIPLE="${TRUST_HOST_TRIPLE:-$(uname -m | sed 's/arm64/aarch64/')-apple-darwin}"
EPOCH="${TRUST_REPRO_EPOCH:-1000000000}"
LOGDIR="${TRUST_REPRO_LOGDIR:-reports/repro-wholestage2}"
BUILD_TIMEOUT="${TRUST_BUILD_TIMEOUT:-1500}"
KEEP=0
FULL_CLEAN=0

while [ $# -gt 0 ]; do
  case "$1" in
    --log) LOGDIR="$2"; shift 2 ;;
    --keep) KEEP=1; shift ;;
    --full-clean) FULL_CLEAN=1; shift ;;
    -h|--help) sed -n '2,60p' "$0"; exit 0 ;;
    *) echo "unknown arg: $1" >&2; exit 2 ;;
  esac
done

S2RUST="build/${HOST_TRIPLE}/stage2-rustc/${HOST_TRIPLE}/release"
S2SYS="build/${HOST_TRIPLE}/stage2"
# Assembled sysroot layout (verified on this host):
#   ${S2SYS}/lib/librustc_driver-*.dylib            (the compiler dylib lives here)
#   ${S2SYS}/lib/rustlib/<host>/lib/lib{std,core,compiler_builtins}-*.rlib
SYSDRV="${S2SYS}/lib"
SYSLIB="${S2SYS}/lib/rustlib/${HOST_TRIPLE}/lib"
BACKEND="${S2RUST}/librustc_codegen_trust_cg.dylib"

mkdir -p "$LOGDIR"
STAMP="$(date +%Y%m%d-%H%M%S)"
MATCHLOG="${LOGDIR}/wholestage2-${STAMP}.log"

export SOURCE_DATE_EPOCH="$EPOCH"
export RUSTFLAGS="--remap-path-prefix=${REPO_ROOT}=/trust-source --remap-path-prefix=${HOME}=/home/trust"
export RUSTC_BOOTSTRAP=1
export LIBRARY_PATH="${LIBRARY_PATH:-/opt/homebrew/lib}"

log() { echo "$@" | tee -a "$MATCHLOG"; }

# Resolve a single hash-suffixed artifact by glob prefix; print path or empty.
resolve_one() {
  local pat="$1"
  local matches=( $pat )
  if [ -e "${matches[0]}" ]; then printf '%s\n' "${matches[0]}"; fi
}

log "=== repro_wholestage2_selfcompare ${STAMP} ==="
log "repo_root        : ${REPO_ROOT}"
log "host_triple      : ${HOST_TRIPLE}"
log "SOURCE_DATE_EPOCH: ${EPOCH}"
log "RUSTFLAGS        : ${RUSTFLAGS}"
log "per-build timeout: ${BUILD_TIMEOUT}s"
log "full-clean       : ${FULL_CLEAN}"
log ""

force_independence() {
  local tag="$1"
  log "--- ${tag}: forcing independence (drop driver+backend fingerprints, deps cached; wipe assembled sysroot) ---"
  # Driver crate(s): fingerprint + emitted dylib in stage2-rustc.
  rm -rf "${S2RUST}/.fingerprint/rustc_driver-"* 2>/dev/null || true
  rm -rf "${S2RUST}/.fingerprint/rustc_driver_impl-"* 2>/dev/null || true
  rm -f  "${S2RUST}/deps/librustc_driver-"*.dylib 2>/dev/null || true
  rm -f  "${S2RUST}/deps/librustc_driver_impl-"*.rlib 2>/dev/null || true
  # Backend (re-confirm baseline): fingerprint + dylib.
  rm -rf "${S2RUST}/.fingerprint/rustc_codegen_trust_cg-"* 2>/dev/null || true
  rm -f  "${S2RUST}/deps/librustc_codegen_trust_cg-"*.dylib 2>/dev/null || true
  rm -f  "${BACKEND}" "${S2RUST}/librustc_codegen_trust_cg.d" 2>/dev/null || true
  # Assembled stage2 sysroot: trustc shim + the compiler dylibs in lib/ + the
  # rustlib lib tree (forces a genuine reassembly, not a stale-copy reuse).
  rm -f  "${S2SYS}/bin/trustc" 2>/dev/null || true
  rm -f  "${SYSDRV}/librustc_driver-"*.dylib 2>/dev/null || true
  rm -f  "${SYSDRV}/librustc_codegen_trust_cg-"*.dylib 2>/dev/null || true
  rm -rf "${SYSLIB}" 2>/dev/null || true
  if [ "$FULL_CLEAN" -eq 1 ]; then
    log "    (full-clean) removing whole stage2-rustc + stage2 trees"
    rm -rf "build/${HOST_TRIPLE}/stage2-rustc" "build/${HOST_TRIPLE}/stage2" 2>/dev/null || true
  fi
}

build_once() {
  local tag="$1"
  force_independence "$tag"
  log "--- ${tag}: RUSTC_BOOTSTRAP=1 LIBRARY_PATH=${LIBRARY_PATH} python3 x.py build --stage 2 (timeout ${BUILD_TIMEOUT}s) ---"
  local blog="${MATCHLOG}.build-${tag}"
  local t0 t1 rc
  t0="$(date +%s)"
  # Portable timeout: gtimeout if present, else background+kill guard.
  if command -v timeout >/dev/null 2>&1; then
    timeout "${BUILD_TIMEOUT}" python3 x.py build --stage 2 >"$blog" 2>&1; rc=$?
  elif command -v gtimeout >/dev/null 2>&1; then
    gtimeout "${BUILD_TIMEOUT}" python3 x.py build --stage 2 >"$blog" 2>&1; rc=$?
  else
    # No timeout(1)/gtimeout: background the build + a sleeper that SIGTERMs it.
    python3 x.py build --stage 2 >"$blog" 2>&1 & local bpid=$!
    ( sleep "${BUILD_TIMEOUT}"; kill -TERM "$bpid" 2>/dev/null ) & local gpid=$!
    wait "$bpid"; rc=$?
    kill -TERM "$gpid" 2>/dev/null || true
    wait "$gpid" 2>/dev/null || true
  fi
  t1="$(date +%s)"
  local elapsed=$((t1 - t0))
  # Timed out: GNU timeout(1) uses rc=124; the background+kill path yields a
  # signal-terminated rc (>=128) at ~elapsed>=BUILD_TIMEOUT.
  if [ "$rc" = "124" ] || { [ "$rc" -ge 128 ] && [ "$elapsed" -ge "$((BUILD_TIMEOUT-5))" ]; }; then
    log "BUILD ${tag} TIMED OUT after ${elapsed}s (>= ${BUILD_TIMEOUT}s) — see ${blog}"
    return 2
  fi
  if [ "$rc" != "0" ]; then
    log "BUILD ${tag} FAILED rc=${rc} after ${elapsed}s — see ${blog}"
    return 2
  fi
  log "build ${tag} OK in ${elapsed}s"
  # Independence evidence: did the driver actually recompile?
  local comp asm
  comp="$(grep -cE "Compiling rustc_driver( |_impl )" "$blog" 2>/dev/null || echo 0)"
  asm="$(grep -cE "Assembling|Creating a sysroot|Copying|Install" "$blog" 2>/dev/null || echo 0)"
  log "    independence: 'Compiling rustc_driver*' lines=${comp}, assemble/copy lines=${asm}"
  if [ "$comp" -eq 0 ]; then
    log "    WARN: no 'Compiling rustc_driver' in ${tag} log — driver may be a CACHED no-op."
  fi
  return 0
}

# ---- artifact set (resolved AFTER a build, since names carry hashes) ----
declare -a ART_KEYS ART_DESC
ART_KEYS=( trustc rustc_driver_dylib libstd_rlib libcore_rlib libcompiler_builtins_rlib backend_dylib )
ART_DESC=(
  "bin/trustc (driver shim)"
  "librustc_driver-*.dylib (LLVM-carrying compiler dylib)"
  "libstd-*.rlib (standard library)"
  "libcore-*.rlib (core)"
  "libcompiler_builtins-*.rlib (compiler intrinsics)"
  "librustc_codegen_trust_cg.dylib (verified backend — re-confirm)"
)

resolve_artifact() {
  case "$1" in
    trustc)                   resolve_one "${S2SYS}/bin/trustc" ;;
    rustc_driver_dylib)       resolve_one "${SYSDRV}/librustc_driver-*.dylib" ;;
    libstd_rlib)              resolve_one "${SYSLIB}/libstd-*.rlib" ;;
    libcore_rlib)             resolve_one "${SYSLIB}/libcore-*.rlib" ;;
    libcompiler_builtins_rlib) resolve_one "${SYSLIB}/libcompiler_builtins-*.rlib" ;;
    backend_dylib)            resolve_one "$BACKEND" ;;
  esac
}

capture_set() {
  local tag="$1"
  local i key src dst
  for i in "${!ART_KEYS[@]}"; do
    key="${ART_KEYS[$i]}"
    src="$(resolve_artifact "$key")"
    dst="${LOGDIR}/${tag}-${key}-${STAMP}.bin"
    if [ -n "$src" ] && [ -e "$src" ]; then
      cp "$src" "$dst"
      eval "PATH_${key}=\"\$src\""
      eval "${tag}_SHA_${key}=\"\$(shasum -a 256 \"\$dst\" | awk '{print \$1}')\""
      eval "${tag}_SIZE_${key}=\"\$(stat -f%z \"\$dst\" 2>/dev/null || stat -c%s \"\$dst\")\""
    else
      log "    MISSING after ${tag}: ${key} (no match for its glob) — artifact not produced by this build"
      eval "${tag}_SHA_${key}=MISSING"
      eval "${tag}_SIZE_${key}=0"
    fi
  done
}

# ---------------- BUILD A ----------------
log ""
log "########## BUILD A ##########"
build_once A || { log "ABORT: build A did not complete (see log)"; exit 2; }
capture_set A

# ---------------- BUILD B ----------------
log ""
log "########## BUILD B ##########"
build_once B || { log "ABORT: build B did not complete (see log)"; exit 2; }
capture_set B

# ---------------- COMPARE + CHARACTERIZE ----------------
log ""
log "================= PER-ARTIFACT RESULT ================="
OVERALL_RC=0
for i in "${!ART_KEYS[@]}"; do
  key="${ART_KEYS[$i]}"
  desc="${ART_DESC[$i]}"
  eval "sa=\$A_SHA_${key}; sb=\$B_SHA_${key}; za=\$A_SIZE_${key}; zb=\$B_SIZE_${key}; pth=\${PATH_${key}:-?}"
  log ""
  log "### ${key} — ${desc}"
  log "    path   : ${pth}"
  if [ "$sa" = "MISSING" ] || [ "$sb" = "MISSING" ]; then
    log "    RESULT : UNMEASURED (artifact missing in A and/or B)"
    OVERALL_RC=2
    continue
  fi
  log "    sha256A: ${sa}  size=${za}"
  log "    sha256B: ${sb}  size=${zb}"
  abin="${LOGDIR}/A-${key}-${STAMP}.bin"
  bbin="${LOGDIR}/B-${key}-${STAMP}.bin"
  if [ "$sa" = "$sb" ]; then
    log "    RESULT : MATCH (byte-identical across two independent builds)"
  else
    log "    RESULT : DIFFER"
    OVERALL_RC=1
    if [ "$za" != "$zb" ]; then
      log "    size   : DIFFERS (${za} vs ${zb}) -> STRUCTURAL nondeterminism (CGU/symbol/member count)"
    else
      log "    size   : equal (${za}) -> BIT-LEVEL nondeterminism within identical layout"
    fi
    local_total="$(cmp -l "$abin" "$bbin" 2>/dev/null | wc -l | tr -d ' ')"
    first="$(cmp -l "$abin" "$bbin" 2>/dev/null | head -1)"
    log "    differing bytes (common prefix): ${local_total}"
    log "    first diff (offset_oct A_oct B_oct): ${first:-<none in common prefix>}"
    if [ -n "$first" ]; then
      offdec=$(( $(echo "$first" | awk '{print $1}') - 1 ))
      log "    first diff decimal offset: ${offdec}"
      # Mach-O section attribution for dylibs / binary.
      case "$key" in
        trustc|rustc_driver_dylib|backend_dylib)
          if command -v otool >/dev/null 2>&1; then
            sect="$(otool -l "$abin" 2>/dev/null | awk -v off="$offdec" '
              /sectname/ {sn=$2}
              /segname/  {seg=$2}
              /^[[:space:]]*offset/ {o=$2}
              /^[[:space:]]*size/   {sz=$2; if(o!="" && off>=o+0 && off<o+sz+0){print seg"."sn" (fileoff "o", size "sz")"; o=""}}')"
            log "    section @offset ${offdec}: ${sect:-<not in any mapped section — likely header/load-cmd/linkedit>}"
          fi
          # Embedded path survival check.
          ap="$(strings "$abin" 2>/dev/null | grep -c "${REPO_ROOT}" || true)"
          log "    embedded ${REPO_ROOT} occurrences (A): ${ap}"
          ;;
        *_rlib)
          # rlib = ar archive: compare member list + per-member to localize CGU/order vs content.
          ta="${REPO_ROOT}/${LOGDIR}/.ar-A-${key}"; tb="${REPO_ROOT}/${LOGDIR}/.ar-B-${key}"
          abs_a="${REPO_ROOT}/${abin}"; abs_b="${REPO_ROOT}/${bbin}"
          rm -rf "$ta" "$tb"; mkdir -p "$ta" "$tb"
          ( cd "$ta" && ar x "$abs_a" 2>/dev/null ) || true
          ( cd "$tb" && ar x "$abs_b" 2>/dev/null ) || true
          la="$(ar t "$abin" 2>/dev/null | sort)"
          lb="$(ar t "$bbin" 2>/dev/null | sort)"
          if [ "$la" != "$lb" ]; then
            log "    rlib MEMBER LIST differs -> CGU count/order or symtab differs:"
            diff <(echo "$la") <(echo "$lb") 2>/dev/null | head -10 | sed 's/^/      /' | tee -a "$MATCHLOG" >/dev/null
          else
            log "    rlib member list identical -> per-member content differs (debuginfo/symbol bytes):"
            ar t "$abin" 2>/dev/null | while read -r m; do
              [ -f "$ta/$m" ] && [ -f "$tb/$m" ] || continue
              if ! cmp -s "$ta/$m" "$tb/$m"; then
                msz_a="$(stat -f%z "$ta/$m" 2>/dev/null || echo ?)"; msz_b="$(stat -f%z "$tb/$m" 2>/dev/null || echo ?)"
                log "      member DIFFERS: $m (sizeA=$msz_a sizeB=$msz_b)"
              fi
            done
          fi
          rm -rf "$ta" "$tb"
          ;;
      esac
    fi
  fi
done

log ""
log "================= SUMMARY ================="
for i in "${!ART_KEYS[@]}"; do
  key="${ART_KEYS[$i]}"
  eval "sa=\$A_SHA_${key}; sb=\$B_SHA_${key}"
  if [ "$sa" = "MISSING" ] || [ "$sb" = "MISSING" ]; then r="UNMEASURED";
  elif [ "$sa" = "$sb" ]; then r="MATCH"; else r="DIFFER"; fi
  printf '  %-28s %s\n' "$key" "$r" | tee -a "$MATCHLOG"
done

if [ "$OVERALL_RC" -eq 0 ]; then
  log ""
  log "WHOLE-STAGE2: all measured artifacts byte-identical across two independent builds."
elif [ "$OVERALL_RC" -eq 1 ]; then
  log ""
  log "WHOLE-STAGE2: one or more artifacts DIFFER (see per-artifact characterization above)."
  log "This is the honest nondeterminism work-list, NOT a DDC failure. DDC still needs a disjoint toolchain B."
fi

if [ "$KEEP" -eq 0 ]; then
  rm -f "${LOGDIR}/"A-*-"${STAMP}.bin" "${LOGDIR}/"B-*-"${STAMP}.bin"
  log "(removed captured artifact copies; pass --keep to retain)"
fi
log ""
log "log written: ${MATCHLOG}"
exit "$OVERALL_RC"
