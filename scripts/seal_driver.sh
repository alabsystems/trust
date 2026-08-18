#!/usr/bin/env bash
# seal_driver.sh — THE sealing helper. One implementation, in scripts/, for
# every lane that needs a compiler CONTROL that stays a control.
#
# Consolidates three scratchpad copies that had drifted apart:
#   scratchpad/laneP/seal.sh          (the seal: unique dylib leaf + LC_ID_DYLIB)
#   scratchpad/wave-tr-ledger/tc      (the active dyld anti-contamination guard)
#   lane K's reseal.sh                (same seal, written independently)
# Those now call this file or point at it. Do not fork a fourth.
#
#   scripts/seal_driver.sh seal <tag> [--from DIR] [--out DIR]
#   scripts/seal_driver.sh guard <binary> [--dyld PATH] [--dyld-fallback PATH]
#                                         [--snapshot-root DIR] [--verbose]
#   scripts/seal_driver.sh classes <trustc>
#   scripts/seal_driver.sh selftest --control <tc> --subject <tc> [--class C]
#   scripts/seal_driver.sh verify <sealed-dir>
#   scripts/seal_driver.sh guardtest            (mutation-proves `guard` itself)
#
# ===========================================================================
# WHY A CONTROL STOPS BEING A CONTROL (the defect this exists to prevent)
# ===========================================================================
# macOS consults DYLD_LIBRARY_PATH for the LEAF NAME of every dylib load
# command, INCLUDING ABSOLUTE ONES. `rustc-main` names its driver as
#   build/<host>/stage1-rustc/release/deps/librustc_driver.dylib
# so a copied binary plus a DYLD_LIBRARY_PATH containing that shared deps dir
# loads whatever `librustc_driver.dylib` sits there NOW -- i.e. the newest
# build. A "control" sealed that way silently BECOMES the subject.
#
# And that is worse than it sounds. A control that equals the subject does not
# manufacture a false GAIN; every delta goes to zero. It manufactures a false
# ABSENCE OF REGRESSION -- "0 new mismatch, 0 lost agreed, 0 lost markers_exact"
# becomes a subject-vs-subject comparison that passes unconditionally. That is
# the half nobody re-checks.
#
# TWO MEASURED FACTS THIS FILE GOT WRONG UNTIL 2026-08-13, both since fixed:
#
#   1. @rpath IS NOT A DEFENCE. DYLD_LIBRARY_PATH's leaf-name lookup happens
#      BEFORE @rpath expansion, so it overrides an image's own LC_RPATH just as
#      it overrides an absolute load command. Measured on the real compiler:
#      `DYLD_LIBRARY_PATH=<dir with a same-leaf decoy> build/<host>/stage1/bin/trustc
#      --version` -> SIGSEGV, versus a clean `rustc 1.99.0-dev` with an empty
#      environment. The in-place install is contaminable and must be CHECKED,
#      not refused on sight and not waved through.
#
#   2. THIS SCRIPT CANNOT SEE THE CALLER'S DYLD_* BY DEFAULT. macOS strips every
#      DYLD_-prefixed variable when it execs a SIP-protected binary; /bin/sh and
#      /bin/bash are protected, and `#!/usr/bin/env bash` is /bin/bash here. So
#      `${DYLD_LIBRARY_PATH:-}` reads EMPTY inside this script while the
#      compiler -- not protected -- receives the caller's value in full.
#      Measured: with a decoy exported, the old `guard` returned PASS on
#      rustc-main while the compiler under that identical environment aborted on
#      the decoy. Callers must STATE the environment (`--dyld`); the guard now
#      refuses rather than certify from a blank it cannot read.
#      (The generated `tc` wrapper always stated it, which is why the wrapper
#      path was sound and the direct path was not.)
#
# ===========================================================================
# TWO GUARDS ARE NOT ENOUGH: A CONTROL MUST BE PROVED, NOT ASSUMED
# ===========================================================================
# `guard` is NEGATIVE evidence -- it refuses known contamination shapes. It
# cannot tell you that the binary in your hand is the OLD revision; a correctly
# sealed copy of the NEW driver passes every structural check.
#
# `selftest` is the POSITIVE evidence. It offers the control a perturbation
# class that ONLY THE SUBJECT REGISTERS. A genuine control must REFUSE it. If
# the control accepts, the control IS the subject and every delta measured
# against it is worthless -- and that is reported as a failure, loudly, before
# anything is measured.
#
# It fails CLOSED in the uninformative case too: if the two drivers register
# the SAME class set there is no discriminator, so the pair is reported
# UNPROVEN rather than passed. "I could not tell them apart" is not "they are
# different".
#
# MEASURED on this machine, 2026-08-13 (the discriminator is real, not
# hypothetical):
#   build/<host>/stage1-rustc/release/rustc-main  registers 10 classes
#       enum-reshape enum-case-value enum-ctor enum-disc-index switch-map
#       enum-payload marker-order marker-drop agg-field-order marker-arm
#   build/<host>/stage1/bin/trustc  and  build/<host>/stage2/bin/trustc
#       register 6 -- they do NOT know marker-order, marker-drop,
#       agg-field-order, marker-arm.
# So `marker-order` discriminates that pair today, and `selftest` finds such a
# class by itself rather than being told one.
#
# ===========================================================================
# IF THE SEALED DRIVER CANNOT FIND `std` (E0463), STOP -- IT IS NOT THE SEAL
# ===========================================================================
# The wrapper below hands the driver `--sysroot <repo>/build/<host>/stage1`, a
# FROZEN prebuilt std. `rustc_metadata` encodes preinterned symbols BY INDEX, so
# a driver whose `symbols!` list differs from the one that std was built with
# rejects it -- `error[E0463]: can't find crate for 'std'`, and, under
# `RUSTC_LOG=rustc_metadata=info`, `Rejecting via crate name`. Nothing about the
# seal, the guard or DYLD is involved. See docs/FROZEN_STD_SYMBOL_INDEX_ABI.md;
# the short version is that new symbols go in the `AppendOnly` section of
# compiler/rustc_span/src/symbol.rs, and a compile-time assertion there now
# catches the mistake before you spend a driver build on it.
#
# Also: `seal` stamps REV/TREE from $TRUST_REPO_ROOT, NOT from the worktree that
# produced the binary. If you built somewhere else, write your own PROVENANCE
# beside the seal and read that instead.
set -uo pipefail

HOST="${TRUST_HOST:-aarch64-apple-darwin}"
ROOT="${TRUST_REPO_ROOT:-$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd -P)}"
STAGE1_SYSROOT="$ROOT/build/$HOST/stage1"
DEFAULT_FROM="$ROOT/build/$HOST/stage1-rustc/release"

die()  { echo "seal_driver: $*" >&2; exit 1; }
note() { echo "seal_driver: $*" >&2; }

# ONE script-global scratch dir with ONE trap. Not a `local` + RETURN trap:
# bash traps are not function-scoped without `functrace`, so such a trap fires
# again when an outer caller returns -- with the local already gone, which under
# `set -u` aborts the script mid-measurement. Found by this file's own tests.
SEAL_TMP=""
cleanup() { [ -n "$SEAL_TMP" ] && rm -rf "$SEAL_TMP"; return 0; }
trap cleanup EXIT
scratch() {
  [ -n "$SEAL_TMP" ] || SEAL_TMP=$(mktemp -d) || die "mktemp failed"
  printf 'pub fn f(x:u32)->u32{x}\n' > "$SEAL_TMP/probe.rs"
  echo "$SEAL_TMP"
}

# Absolute, symlink-resolved path. The guard compares a dyld-resolved ABSOLUTE
# path against a caller-supplied snapshot root; comparing that to a RELATIVE
# root made `verify` refuse a correctly sealed directory. Found by this file's
# own tests.
abspath() {
  case "$1" in
    /*) ( cd "$(dirname "$1")" 2>/dev/null && printf '%s/%s\n' "$(pwd -P)" "$(basename "$1")" ) || printf '%s\n' "$1" ;;
    *)  ( cd "$(dirname "$1")" 2>/dev/null && printf '%s/%s\n' "$(pwd -P)" "$(basename "$1")" ) || printf '%s\n' "$1" ;;
  esac
}

# ---------------------------------------------------------------------------
# Fully symlink-resolved absolute path — FINAL COMPONENT INCLUDED.
#
# `abspath` resolves only the DIRECTORY (`cd; pwd -P`). A snapshot whose dylib
# is a SYMLINK to the live driver therefore satisfied a directory-only
# containment test while loading the live driver. Containment must be decided on
# the file dyld ends up at, not on the name it was reached by.
# ---------------------------------------------------------------------------
realpath_f() {
  local out
  if out=$(/bin/realpath "$1" 2>/dev/null) && [ -n "$out" ]; then printf '%s\n' "$out"; return 0; fi
  if out=$(/usr/bin/python3 -c 'import os,sys;print(os.path.realpath(sys.argv[1]))' "$1" 2>/dev/null) \
     && [ -n "$out" ]; then printf '%s\n' "$out"; return 0; fi
  abspath "$1"
}

# LC_RPATH entries of an image, in load-command order (dyld tries them in order).
lc_rpaths() {
  otool -l "$1" 2>/dev/null | awk '
    $1=="cmd" && $2=="LC_RPATH" { want=1; next }
    want==1 && $1=="path" {
      line=$0
      sub(/^[ \t]*path[ \t]+/, "", line)
      sub(/[ \t]+\(offset[ \t]+[0-9]+\)[ \t]*$/, "", line)
      print line
      want=0
    }'
}

# EVERY librustc_driver* load command of an image. Not `print $1; exit`: line 1
# of `otool -L` is the image's OWN name, `$1` truncates a path containing a
# space, and stopping at the first match ignores any second driver command.
driver_deps() {
  otool -L "$1" 2>/dev/null | awk '
    NR>1 {
      line=$0
      sub(/^[ \t]+/, "", line)
      sub(/[ \t]+\(compatibility version.*$/, "", line)
      if (line ~ /(^|\/)librustc_driver[^\/]*\.dylib$/) print line
    }'
}

# @loader_path / @executable_path. The driver is a DIRECT dependency of the
# binary, so the loading image and the main executable are both the binary.
expand_at() { # <path> <image-dir>
  case "$1" in
    @loader_path/*)     printf '%s/%s\n' "$2" "${1#@loader_path/}" ;;
    @executable_path/*) printf '%s/%s\n' "$2" "${1#@executable_path/}" ;;
    *) printf '%s\n' "$1" ;;
  esac
}

# HONEST resolution — the file the load command NAMES, with no DYLD_* override:
# an absolute path as written; @rpath through the image's own LC_RPATH entries,
# in order, first existing candidate winning, exactly as dyld does; and
# @loader_path/@executable_path expanded (including inside an LC_RPATH entry,
# which is how every in-place install is linked: `@loader_path/../lib`).
resolve_honest() { # <dep> <image>  -> path on stdout, non-zero if nothing exists
  local dep="$1" img="$2" imgdir tail r cand
  imgdir=$(dirname "$(abspath "$img")")
  case "$dep" in
    @rpath/*)
      tail=${dep#@rpath/}
      while IFS= read -r r; do
        [ -n "$r" ] || continue
        cand=$(expand_at "$r" "$imgdir")/$tail
        if [ -f "$cand" ]; then printf '%s\n' "$cand"; return 0; fi
      done <<RPATHS
$(lc_rpaths "$img")
RPATHS
      return 1 ;;
    @loader_path/*|@executable_path/*)
      cand=$(expand_at "$dep" "$imgdir")
      if [ -f "$cand" ]; then printf '%s\n' "$cand"; return 0; fi
      return 1 ;;
    *)
      if [ -f "$dep" ]; then printf '%s\n' "$dep"; return 0; fi
      return 1 ;;
  esac
}

# EFFECTIVE resolution — the file dyld WOULD LOAD under the DYLD_* variables
# actually in effect. MEASURED on this machine (macOS 15 / arm64), not assumed:
#   1. DYLD_LIBRARY_PATH, by LEAF NAME. It beats an absolute load command AND it
#      beats the image's own @rpath — both measured with a two-driver fixture
#      whose exit code names the dylib that actually loaded. So an @rpath binary
#      is contaminable exactly like an absolute one; "it uses @rpath" is not a
#      defence and must not be treated as one.
#   2. the honest path.
#   3. DYLD_FALLBACK_LIBRARY_PATH by leaf — used only when the honest path is
#      missing (also measured, both ways).
resolve_effective() { # <dep> <image> <dyld-path> <fallback-path>
  local dep="$1" img="$2" dyldp="$3" fbp="$4" leaf d hon saved_ifs
  leaf=${dep##*/}
  saved_ifs=$IFS; IFS=:
  for d in $dyldp; do
    if [ -n "$d" ] && [ -f "$d/$leaf" ]; then
      IFS=$saved_ifs; printf '%s\n' "$d/$leaf"; return 0
    fi
  done
  IFS=$saved_ifs
  if hon=$(resolve_honest "$dep" "$img"); then printf '%s\n' "$hon"; return 0; fi
  saved_ifs=$IFS; IFS=:
  for d in $fbp; do
    if [ -n "$d" ] && [ -f "$d/$leaf" ]; then
      IFS=$saved_ifs; printf '%s\n' "$d/$leaf"; return 0
    fi
  done
  IFS=$saved_ifs
  return 1
}

# Can this process SEE the caller's DYLD_* variables at all?
#
# MEASURED: macOS strips every DYLD_-prefixed variable from the environment when
# it execs a SIP-protected binary, and /bin/sh and /bin/bash are protected. On
# this machine `#!/usr/bin/env bash` IS /bin/bash (no unprotected bash on PATH),
# so this script reads an EMPTY DYLD_LIBRARY_PATH even when the caller exported
# one — while the compiler it is about to guard, not being protected, receives
# it in full. Defaulting to "$DYLD_LIBRARY_PATH" therefore did not observe the
# caller's environment; it observed a blank, and certified the exact
# substitution the guard exists to refuse. Probe with a real dyld variable
# (guaranteed to be in the scrub set) rather than trusting a prefix rule.
dyld_env_visible() {
  local probe
  probe=$(DYLD_FALLBACK_LIBRARY_PATH=__seal_probe__ "${BASH:-/bin/bash}" -c \
            'printf %s "${DYLD_FALLBACK_LIBRARY_PATH-}"' 2>/dev/null)
  [ "$probe" = "__seal_probe__" ]
}

# ---------------------------------------------------------------------------
# guard — the ACTIVE anti-contamination check. Three fail-closed halves.
#
#   A. SUBSTITUTION. Resolve the driver TWICE — honestly (what the load command
#      names) and effectively (what dyld would load under the DYLD_* in effect)
#      — and refuse unless they are the same file (device+inode). Resolving is
#      the whole job: the previous version compared an UNRESOLVED load-command
#      string against itself, which is not a comparison. It passed every @rpath
#      hijack unexamined and refused every legitimate @rpath install while
#      printing "These are different files" under two identical strings.
#
#   B. FOREIGN DRIVER. The driver that actually loads must live inside the
#      binary's own install root (--snapshot-root if given; else the binary's
#      directory, or its parent when the binary sits in a `bin/`, which is how
#      an in-place install is laid out). This is the naive `cp rustc-main` case:
#      the load command still honestly names the SHARED build, so no
#      substitution occurs and check A passes, yet the "snapshot" is the live
#      driver wearing a copied front-end. Decided on the realpath, so a symlink
#      into the live build cannot satisfy it either.
#
#   C. OBSERVABILITY. If the DYLD_* environment cannot be read (SIP scrub) and
#      the caller did not state it with --dyld, refuse. A guard that silently
#      reads a blank environment as "the caller set nothing" certifies nothing.
# ---------------------------------------------------------------------------
cmd_guard() {
  local bin="" dyld="" dyld_given=0 fbp="" fb_given=0 snaproot="" verbose=0
  bin="${1:-}"; shift || true
  while [ $# -gt 0 ]; do
    case "$1" in
      --dyld)          dyld="$2"; dyld_given=1; shift 2 ;;
      --dyld-fallback) fbp="$2";  fb_given=1;   shift 2 ;;
      --snapshot-root) snaproot="$2"; shift 2 ;;
      --verbose|-v)    verbose=1; shift ;;
      *) die "guard: unknown argument $1" ;;
    esac
  done
  [ -n "$bin" ] || die "usage: seal_driver.sh guard <binary> [--dyld PATH] [--dyld-fallback PATH] [--snapshot-root DIR] [--verbose]"

  if [ -n "${TC_ALLOW_UNSEALED_SNAPSHOT:-}" ]; then
    echo "seal_driver: WARNING: contamination guard disabled by TC_ALLOW_UNSEALED_SNAPSHOT." >&2
    echo "seal_driver: WARNING: any control measured through this run is UNVERIFIED." >&2
    return 0
  fi

  [ -x "$bin" ] || { echo "guard: REFUSING: no driver at $bin" >&2; return 97; }

  # --- C. observability ----------------------------------------------------
  local env_visible=0
  dyld_env_visible && env_visible=1
  if [ $dyld_given -eq 0 ]; then
    if [ $env_visible -eq 1 ]; then
      dyld="${DYLD_LIBRARY_PATH:-}"
    else
      cat >&2 <<EOF
guard: REFUSING TO RUN — THE DYLD ENVIRONMENT IS NOT OBSERVABLE.
guard:   binary            $bin
guard:   This script is running under a SIP-protected interpreter (${BASH:-sh}),
guard:   so macOS stripped every DYLD_* variable before it started. The caller's
guard:   DYLD_LIBRARY_PATH is invisible HERE but is delivered in full to the
guard:   compiler, which is not protected. Reading the blank as "nothing was
guard:   set" is how a leaf-name substitution gets certified as clean.
guard:   State it: --dyld "\$DYLD_LIBRARY_PATH"   (or --dyld '' to assert none)
EOF
      return 97
    fi
  fi
  if [ $fb_given -eq 0 ]; then
    # dyld's documented default when DYLD_FALLBACK_LIBRARY_PATH is unset. Kept
    # deliberately wide: a librustc_driver leaf in any of these is alarming.
    if [ $env_visible -eq 1 ] && [ -n "${DYLD_FALLBACK_LIBRARY_PATH:-}" ]; then
      fbp="$DYLD_FALLBACK_LIBRARY_PATH"
    else
      fbp="${HOME:-/nonexistent}/lib:/usr/local/lib:/usr/lib"
    fi
  fi
  if [ $env_visible -eq 1 ] && [ -n "${DYLD_ROOT_PATH:-}" ]; then
    echo "guard: REFUSING: DYLD_ROOT_PATH is set ($DYLD_ROOT_PATH); this guard does not model it." >&2
    return 97
  fi

  # --- install root, for check B ------------------------------------------
  local root bindir
  if [ -n "$snaproot" ]; then
    root=$(realpath_f "$snaproot")
  else
    bindir=$(dirname "$(abspath "$bin")")
    case "${bindir##*/}" in
      bin) root=$(realpath_f "$(dirname "$bindir")") ;;
      *)   root=$(realpath_f "$bindir") ;;
    esac
  fi
  root="${root%/}"

  local deps dep hon eff hon_id eff_id drv n=0
  deps=$(driver_deps "$bin")
  if [ -z "$deps" ]; then
    echo "guard: REFUSING: cannot read the driver load command of $bin" >&2
    return 97
  fi

  # A here-doc, NOT a pipe: a `while read` fed by a pipe runs in a subshell,
  # where `return 97` would be discarded and the guard would pass.
  while IFS= read -r dep; do
    [ -n "$dep" ] || continue
    n=$((n+1))
    hon=$(resolve_honest    "$dep" "$bin")                 || hon=""
    eff=$(resolve_effective "$dep" "$bin" "$dyld" "$fbp")  || eff=""
    [ -n "$hon" ] && hon=$(realpath_f "$hon")   # display/compare on the real file
    [ $verbose -eq 1 ] && {
      echo "guard: load command   $dep"
      echo "guard:   names        ${hon:-<UNRESOLVABLE>}"
      echo "guard:   dyld loads   ${eff:-<UNRESOLVABLE>}"
      echo "guard:   install root $root"
    } >&2

    if [ -z "$eff" ]; then
      cat >&2 <<EOF
guard: REFUSING TO RUN — THE DRIVER CANNOT BE RESOLVED.
guard:   binary            $bin
guard:   load command      $dep
guard:   Nothing on DYLD_LIBRARY_PATH, this image's LC_RPATHs, or the fallback
guard:   paths supplies it. This binary would not even launch.
EOF
      return 97
    fi
    if [ -z "$hon" ]; then
      cat >&2 <<EOF
guard: REFUSING TO RUN — DYLD SNAPSHOT CONTAMINATION (dangling load command).
guard:   binary            $bin
guard:   load command      $dep
guard:   names             <nothing — that file does not exist>
guard:   dyld would load   $eff
guard:   The file this binary was linked against is GONE, so what loads is
guard:   whatever the environment supplies. That is a substitution by default.
EOF
      return 97
    fi

    hon_id=$(stat -f '%d:%i' "$hon" 2>/dev/null)
    eff_id=$(stat -f '%d:%i' "$eff" 2>/dev/null)
    if [ -z "$hon_id" ] || [ -z "$eff_id" ] || [ "$hon_id" != "$eff_id" ]; then
      cat >&2 <<EOF
guard: REFUSING TO RUN — DYLD SNAPSHOT CONTAMINATION.
guard:   binary            $bin
guard:   load command      $dep
guard:   names             $hon
guard:   dyld would load   $eff
guard:   These are different files. The driver you would measure is NOT the one
guard:   this binary was linked against — a control run this way silently
guard:   becomes the subject and every delta collapses to zero.
guard:   Seal it: scripts/seal_driver.sh seal <tag>
EOF
      return 97
    fi

    # --- B. the driver must belong to this binary's own install -----------
    drv=$(realpath_f "$eff")
    case "$drv" in
      "$root"/*) : ;;
      *)
        cat >&2 <<EOF
guard: REFUSING TO RUN — SNAPSHOT WITH A FOREIGN DRIVER.
guard:   binary            $bin
guard:   dyld would load   $eff
guard:   which really is   $drv
guard:   install root      $root
guard:   The driver this binary loads lives outside its own install — so this is
guard:   the LIVE driver wearing a copied front-end, and a control run this way
guard:   IS the subject.
guard:   Seal it: scripts/seal_driver.sh seal <tag>
EOF
        return 97
        ;;
    esac
  done <<DEPS
$deps
DEPS

  [ $verbose -eq 1 ] && echo "guard: OK — $n driver load command(s) checked, all sealed to $root" >&2
  return 0
}

# ---------------------------------------------------------------------------
# seal — snapshot into a SELF-CONTAINED pair (binary + uniquely-named dylib).
#
# A leaf name that exists nowhere else cannot be substituted by leaf-name
# lookup. That, plus keeping the shared deps dir OFF the wrapper's
# DYLD_LIBRARY_PATH, closes the channel structurally rather than by convention.
# ---------------------------------------------------------------------------
cmd_seal() {
  local tag="" from="$DEFAULT_FROM" out=""
  tag="${1:-}"; shift || true
  while [ $# -gt 0 ]; do
    case "$1" in
      --from) from="$2"; shift 2 ;;
      --out)  out="$2";  shift 2 ;;
      *) die "seal: unknown argument $1" ;;
    esac
  done
  [ -n "$tag" ] || die "usage: seal_driver.sh seal <tag> [--from DIR] [--out DIR]"
  case "$tag" in
    *[!A-Za-z0-9_-]*) die "seal: tag must be [A-Za-z0-9_-]+ (it becomes a dylib leaf name)" ;;
  esac
  out="${out:-$ROOT/build/sealed/seal-$tag}"

  local src_bin="$from/rustc-main" src_dylib="$from/deps/librustc_driver.dylib"
  [ -x "$src_bin" ]  || die "seal: no rustc-main at $src_bin"
  [ -f "$src_dylib" ] || die "seal: no librustc_driver.dylib at $src_dylib"

  rm -rf "$out"; mkdir -p "$out" || die "seal: cannot create $out"
  cp "$src_bin"   "$out/rustc-main"
  cp "$src_dylib" "$out/librustc_driver_$tag.dylib"

  local new="$out/librustc_driver_$tag.dylib"
  install_name_tool -id "$new" "$new"            || die "seal: install_name_tool -id failed"
  install_name_tool -change "$src_dylib" "$new" "$out/rustc-main" \
      || die "seal: install_name_tool -change failed"
  codesign -f -s - "$new" 2>/dev/null || true
  codesign -f -s - "$out/rustc-main" 2>/dev/null || true

  # The wrapper. stage1/lib supplies libstd (@rpath) and is REVISION-INDEPENDENT
  # (the seed std, not rebuilt by buildtrustc.sh). The stage1-rustc deps dir is
  # DELIBERATELY ABSENT: nothing in the snapshot needs it, and its presence is
  # exactly the contamination channel. The guard runs anyway, before exec.
  cat > "$out/tc" <<EOF
#!/bin/sh
# Generated by scripts/seal_driver.sh — sealed driver wrapper for tag '$tag'.
# The shared stage1-rustc deps dir is deliberately NOT on DYLD_LIBRARY_PATH.
SEAL_DIR="$out"
DYLD_LIBRARY_PATH="$STAGE1_SYSROOT/lib\${DYLD_LIBRARY_PATH:+:\$DYLD_LIBRARY_PATH}"
export DYLD_LIBRARY_PATH
"$ROOT/scripts/seal_driver.sh" guard "\$SEAL_DIR/rustc-main" \\
    --dyld "\$DYLD_LIBRARY_PATH" --snapshot-root "\$SEAL_DIR" || exit 97
exec "\$SEAL_DIR/rustc-main" --sysroot "$STAGE1_SYSROOT" "\$@"
EOF
  chmod +x "$out/tc"

  # Provenance, so a snapshot can never be confused about what it is.
  ( cd "$ROOT" && git rev-parse HEAD ) > "$out/REV" 2>/dev/null || echo unknown > "$out/REV"
  ( cd "$ROOT" && git status --porcelain | head -1 | grep -q . && echo dirty || echo clean ) > "$out/TREE" 2>/dev/null || true
  shasum -a 256 "$new" "$out/rustc-main" > "$out/SHA256"
  cmd_classes "$out/tc" > "$out/PERTURB_CLASSES" 2>/dev/null || true

  echo "sealed $tag -> $out"
  echo "  rev            $(cat "$out/REV")"
  echo "  perturb classes $(tr '\n' ' ' < "$out/PERTURB_CLASSES")"
  otool -L "$out/rustc-main" | sed -n '2p'
}

# ---------------------------------------------------------------------------
# classes — the perturbation classes a driver REGISTERS.
#
# Read out of the compiler itself: an invalid `-Ztrust-sat-perturb` value makes
# it print its own accepted set. No table here to drift out of date.
# ---------------------------------------------------------------------------
cmd_classes() {
  local tc="${1:-}"
  [ -n "$tc" ] || die "usage: seal_driver.sh classes <trustc>"
  [ -x "$tc" ] || die "classes: not executable: $tc"
  local tmp; tmp=$(scratch)
  # The probe compile is EXPECTED to fail -- the diagnostic is the payload. Its
  # exit code must not propagate through `pipefail`.
  { "$tc" --edition 2021 --crate-type lib \
          -Ztrust-sat-perturb=__seal_driver_probe__ \
          -o "$tmp/out.rlib" "$tmp/probe.rs" 2>&1 || true; } \
    | sed -n 's/.*invalid -Ztrust-sat-perturb value: expected //p' \
    | head -1 \
    | sed 's/, or /, /; s/ or //' \
    | tr ',' '\n' \
    | sed 's/^ *//; s/ *$//' \
    | grep -v '^$'
}

# ---------------------------------------------------------------------------
# selftest — PROVE that a control is a control.
#
# Offer the control a perturbation class that only the subject registers. A
# genuine control must REFUSE it. Fail-closed in every uninformative case.
# ---------------------------------------------------------------------------
cmd_selftest() {
  local control="" subject="" want_class=""
  while [ $# -gt 0 ]; do
    case "$1" in
      --control) control="$2"; shift 2 ;;
      --subject) subject="$2"; shift 2 ;;
      --class)   want_class="$2"; shift 2 ;;
      *) die "selftest: unknown argument $1" ;;
    esac
  done
  [ -n "$control" ] && [ -n "$subject" ] \
    || die "usage: seal_driver.sh selftest --control <tc> --subject <tc> [--class C]"

  local c_set s_set
  c_set=$(cmd_classes "$control") || die "selftest: cannot read the control's class set"
  s_set=$(cmd_classes "$subject") || die "selftest: cannot read the subject's class set"
  [ -n "$c_set" ] || die "selftest: the control registered NO perturbation classes -- \
this discriminator does not apply to that binary; supply another."
  [ -n "$s_set" ] || die "selftest: the subject registered NO perturbation classes."

  echo "control classes: $(echo "$c_set" | tr '\n' ' ')"
  echo "subject classes: $(echo "$s_set" | tr '\n' ' ')"

  local only origin="derived from the class-set difference"
  only=$(comm -13 <(echo "$c_set" | sort) <(echo "$s_set" | sort))
  if [ -n "$want_class" ]; then
    echo "$s_set" | grep -qx "$want_class" \
      || die "selftest: --class $want_class is not registered by the SUBJECT; it cannot discriminate."
    only="$want_class"
    origin="supplied with --class (NOT derived; the control may well register it)"
  fi

  if [ -z "$only" ]; then
    cat >&2 <<EOF
selftest: UNPROVEN — no discriminating perturbation class.
selftest:   The control and the subject register the SAME class set, so this
selftest:   discriminator cannot tell them apart. That is NOT a pass: "I could
selftest:   not distinguish them" is not "they are different". Either these two
selftest:   binaries really are the same revision (in which case your control is
selftest:   the subject), or you need a different discriminator -- e.g. a
selftest:   -Z option present on only one side, or the lineage stamp:
selftest:     strings -a <driver>.dylib | grep trust_thir_lower.body_lineage
EOF
    return 3
  fi

  local class; class=$(echo "$only" | head -1)
  echo "discriminator: '$class' — $origin"

  # The subject must ACCEPT it (else the difference was an artifact of parsing).
  local tmp; tmp=$(scratch)

  local s_out c_out
  s_out=$("$subject" --edition 2021 --crate-type lib -Ztrust-verify=off -Ztrust-ir-lower \
            "-Ztrust-sat-perturb=$class" -o "$tmp/s.rlib" "$tmp/probe.rs" 2>&1)
  if echo "$s_out" | grep -q "invalid -Ztrust-sat-perturb value"; then
    die "selftest: the SUBJECT rejected '$class' that it advertised. Discriminator is unsound."
  fi

  c_out=$("$control" --edition 2021 --crate-type lib -Ztrust-verify=off -Ztrust-ir-lower \
            "-Ztrust-sat-perturb=$class" -o "$tmp/c.rlib" "$tmp/probe.rs" 2>&1)
  if echo "$c_out" | grep -q "invalid -Ztrust-sat-perturb value"; then
    echo "SELFTEST PASS: the control REFUSED '$class' — it is genuinely the older driver."
    echo "  control said: $(echo "$c_out" | head -1)"
    return 0
  fi

  cat >&2 <<EOF
SELFTEST FAIL — THE CONTROL IS NOT A CONTROL.
  control  $control
  subject  $subject
  The control ACCEPTED '$class', a perturbation class only the subject
  registers. The binary you are calling the control is the SUBJECT. Every
  delta measured against it is a subject-vs-subject comparison, which is why
  it will report "0 new mismatch, 0 lost agreed" no matter what changed.
  Re-seal:  scripts/seal_driver.sh seal <tag> --from <the control's build dir>
  control said: $(echo "$c_out" | head -1)
EOF
  return 1
}

# ---------------------------------------------------------------------------
# guardtest — PROVE `guard` still works, by mutation, in both directions.
#
# A guard is only evidence if its refusals come from its own logic. So this
# builds real Mach-O fixtures (clang, ~1s) in every shape that matters, asserts
# the verdicts, and then NEUTERS one mechanism at a time in a subshell and
# asserts the verdicts go RED. A mechanism whose removal changes nothing was
# never doing the work, and this reports that as a failure.
# ---------------------------------------------------------------------------
GT_PASS=0; GT_FAIL=0
gt_run() { # gt_run <expect PASS|REFUSE> <name> <override-or-empty> <guard args...>
  local expect="$1" name="$2" ov="$3"; shift 3
  local out rc got
  out=$( [ -n "$ov" ] && eval "$ov"; cmd_guard "$@" 2>&1 ); rc=$?
  got=PASS; [ $rc -ne 0 ] && got=REFUSE
  if [ "$got" = "$expect" ]; then
    GT_PASS=$((GT_PASS+1)); printf '  ok   %-52s %s\n' "$name" "$got"
  else
    GT_FAIL=$((GT_FAIL+1)); printf '  FAIL %-52s got %s want %s\n' "$name" "$got" "$expect"
    printf '%s\n' "$out" | sed 's/^/         | /'
  fi
}

cmd_guardtest() {
  command -v clang >/dev/null 2>&1 || die "guardtest: needs clang to build Mach-O fixtures"
  local T; T=$(scratch)/guardtest
  rm -rf "$T"; mkdir -p "$T/live/deps" "$T/inst/bin" "$T/inst/lib" "$T/decoy" "$T/cpsnap" || die "guardtest: mkdir"
  printf 'int drv(void){return 1;}\n' > "$T/a.c"
  printf 'int drv(void){return 2;}\n' > "$T/b.c"
  printf 'int drv(void);int main(void){return drv();}\n' > "$T/m.c"
  local HH=deadbeefcafe0001
  local LIVE="$T/live/deps/librustc_driver.dylib" INST="$T/inst/lib/librustc_driver-$HH.dylib"
  clang -dynamiclib -o "$LIVE" -install_name "$LIVE" "$T/a.c" || die "guardtest: clang"
  clang -o "$T/live/rustc-main" "$T/m.c" "$LIVE"              || die "guardtest: clang"
  clang -dynamiclib -o "$INST" -install_name "@rpath/librustc_driver-$HH.dylib" "$T/a.c" || die "guardtest: clang"
  clang -o "$T/inst/bin/trustc" "$T/m.c" "$INST" -Wl,-rpath,@loader_path/../lib          || die "guardtest: clang"
  # same LEAF names, different files -- the substitution material
  clang -dynamiclib -o "$T/decoy/librustc_driver.dylib"        -install_name "$LIVE" "$T/b.c" || die "guardtest: clang"
  clang -dynamiclib -o "$T/decoy/librustc_driver-$HH.dylib"    -install_name "@rpath/librustc_driver-$HH.dylib" "$T/b.c" || die "guardtest: clang"
  # a correctly sealed pair, and the two contaminated snapshot shapes
  mkdir -p "$T/sealed" "$T/linksnap"
  cp "$T/live/rustc-main" "$T/sealed/rustc-main"; cp "$LIVE" "$T/sealed/librustc_driver_gt.dylib"
  install_name_tool -id "$T/sealed/librustc_driver_gt.dylib" "$T/sealed/librustc_driver_gt.dylib" 2>/dev/null
  install_name_tool -change "$LIVE" "$T/sealed/librustc_driver_gt.dylib" "$T/sealed/rustc-main" 2>/dev/null
  clang -dynamiclib -o "$T/decoy/librustc_driver_gt.dylib" -install_name "$T/sealed/librustc_driver_gt.dylib" "$T/b.c" || die "guardtest: clang"
  cp "$T/live/rustc-main" "$T/cpsnap/rustc-main"
  cp "$T/live/rustc-main" "$T/linksnap/rustc-main"
  ln -s "$LIVE" "$T/linksnap/librustc_driver_link.dylib"
  install_name_tool -change "$LIVE" "$T/linksnap/librustc_driver_link.dylib" "$T/linksnap/rustc-main" 2>/dev/null
  for f in "$T/sealed/librustc_driver_gt.dylib" "$T/sealed/rustc-main" "$T/linksnap/rustc-main"; do
    codesign -f -s - "$f" 2>/dev/null || true
  done

  echo "guardtest: fixtures in $T"
  echo "== legitimate installs must PASS =="
  gt_run PASS   "sealed pair"                          "" "$T/sealed/rustc-main" --snapshot-root "$T/sealed" --dyld ""
  gt_run PASS   "sealed pair, no --snapshot-root"      "" "$T/sealed/rustc-main" --dyld ""
  gt_run PASS   "in-place @rpath install"              "" "$T/inst/bin/trustc"   --dyld ""
  gt_run PASS   "in-place @rpath install, own lib on DYLD" "" "$T/inst/bin/trustc" --dyld "$T/inst/lib"
  gt_run PASS   "live rustc-main (absolute load cmd)"  "" "$T/live/rustc-main"   --dyld ""

  echo "== contamination must be REFUSED =="
  gt_run REFUSE "same-leaf substitution, absolute"     "" "$T/live/rustc-main"   --dyld "$T/decoy"
  gt_run REFUSE "same-leaf substitution, @rpath"       "" "$T/inst/bin/trustc"   --dyld "$T/decoy"
  gt_run REFUSE "same-leaf substitution, sealed leaf"  "" "$T/sealed/rustc-main" --snapshot-root "$T/sealed" --dyld "$T/decoy"
  gt_run REFUSE "cp snapshot -> live driver"           "" "$T/cpsnap/rustc-main" --snapshot-root "$T/cpsnap" --dyld ""
  gt_run REFUSE "cp snapshot -> live driver, no --root" "" "$T/cpsnap/rustc-main" --dyld ""
  gt_run REFUSE "symlink snapshot -> live driver"      "" "$T/linksnap/rustc-main" --snapshot-root "$T/linksnap" --dyld ""

  echo "== mutation: each mechanism removed must turn refusals RED =="
  local N1='resolve_honest() { echo "$1"; return 0; }; resolve_effective() { echo "$1"; return 0; }'
  gt_run PASS   "N1 no resolution: substitution ADMITTED"    "$N1" "$T/live/rustc-main" --dyld "$T/decoy"
  gt_run PASS   "N1 no resolution: sealed hijack ADMITTED"   "$N1" "$T/sealed/rustc-main" --snapshot-root "$T/sealed" --dyld "$T/decoy"
  gt_run REFUSE "N1 no resolution: legit @rpath REFUSED"     "$N1" "$T/inst/bin/trustc" --dyld ""
  local N2='realpath_f() { abspath "$1"; }'
  gt_run PASS   "N2 no realpath: symlink snapshot ADMITTED"  "$N2" "$T/linksnap/rustc-main" --snapshot-root "$T/linksnap" --dyld ""

  # The observability half is only assertable where the environment really is
  # unreadable. Asserting a fixed verdict on both kinds of machine would make
  # this test pass by luck somewhere, so it states which world it is in.
  if dyld_env_visible; then
    echo "  --   DYLD_* IS visible to this shell (${BASH:-sh}); observability case not applicable here."
  else
    gt_run REFUSE "unstated env is refused, not assumed empty"  "" "$T/live/rustc-main"
    local N3='dyld_env_visible() { return 0; }'
    gt_run PASS   "N3 no env probe: unstated env ADMITTED"      "$N3" "$T/live/rustc-main"
  fi

  echo
  echo "guardtest: $GT_PASS ok, $GT_FAIL FAIL"
  [ $GT_FAIL -eq 0 ] || return 1
  echo "guardtest: OK — every refusal above is produced by the guard's own logic."
  return 0
}

# ---------------------------------------------------------------------------
# verify — re-check a sealed directory: hashes still match, guard still passes.
# ---------------------------------------------------------------------------
cmd_verify() {
  local dir="${1:-}"
  [ -n "$dir" ] || die "usage: seal_driver.sh verify <sealed-dir>"
  [ -f "$dir/SHA256" ] || die "verify: no SHA256 manifest in $dir — not a sealed directory"
  ( cd "$dir" && shasum -a 256 -c SHA256 ) || die "verify: the sealed pair no longer matches its manifest"
  cmd_guard "$dir/rustc-main" --dyld "$STAGE1_SYSROOT/lib" --snapshot-root "$dir" || return 97
  echo "verify OK: $dir (rev $(cat "$dir/REV" 2>/dev/null || echo unknown))"
}

case "${1:-}" in
  seal)     shift; cmd_seal     "$@" ;;
  guard)    shift; cmd_guard    "$@" ;;
  classes)  shift; cmd_classes  "$@" ;;
  selftest) shift; cmd_selftest "$@" ;;
  verify)   shift; cmd_verify   "$@" ;;
  guardtest) shift; cmd_guardtest "$@" ;;
  # The whole header block, however long it grows -- not a hard-coded line
  # range that silently truncates the moment someone documents a new fact.
  -h|--help|"") sed -n '2,/^set -uo pipefail/p' "$0" | sed '$d'; exit 0 ;;
  *) die "unknown subcommand: $1 (seal|guard|classes|selftest|verify|guardtest)" ;;
esac
