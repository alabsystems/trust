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
#   scripts/seal_driver.sh seal <tag> [--from DIR] [--out DIR] [--worktree DIR]
#                                     [--sysroot DIR]
#   scripts/seal_driver.sh guard <binary> [--dyld PATH] [--dyld-fallback PATH]
#                                         [--snapshot-root DIR] [--verbose]
#   scripts/seal_driver.sh classes <trustc>
#   scripts/seal_driver.sh selftest --control <tc> --subject <tc> [--class C]
#   scripts/seal_driver.sh verify <sealed-dir>
#   scripts/seal_driver.sh guardtest            (mutation-proves `guard` itself)
#   scripts/seal_driver.sh sysrootcheck [<sealed-dir>|<trustc>] [--sysroot DIR]
#   scripts/seal_driver.sh sysroots [<trustc>]  (the registry, with live versions)
#   scripts/seal_driver.sh sysroottest          (mutation-proves AUTO-SELECTION)
#   scripts/seal_driver.sh reverdict <sealed-dir>  (re-mint SYSROOT_COMPAT only)
#
# ===========================================================================
# WHY `sysrootcheck` EXISTS (the 2026-08-20 blocker, made cheap)
# ===========================================================================
# METADATA_VERSION was bumped 11 -> 12 by 631d86898a. The only std on this
# machine was built at v11, so EVERY driver built from a tree containing that
# commit dies with
#     error[E0514]: found crate `std` compiled by an incompatible version of
#                   rustc ... compiled by <unknown rustc version>
# The `<unknown rustc version>` is the tell: the reader could not even find a
# version string, because the metadata HEADER version differs -- it is not a
# stale-rebuild problem and `cargo clean` does nothing for it.
#
# A lane used to discover this by burning a 24 GB, ~22-minute driver build and
# then staring at a confusing E0514. `sysrootcheck` costs about a second: it
# reads the sysroot's own METADATA_VERSION out of libcore's .rmeta header,
# reads the DRIVER's out of a `#![no_core]` probe rlib (which needs no sysroot
# at all), and then actually resolves `std`. It states both numbers and the
# real reason. `seal` runs it and records the verdict in SYSROOT_COMPAT;
# `verify` runs it again; `guard` refuses -- for free -- on a recorded FAIL.
#
# ===========================================================================
# WHICH SYSROOT A SEAL COMPILES AGAINST -- AND WHY `seal` NOW CHOOSES IT
# (the 2026-08-24 promotion, and the trap it left behind)
# ===========================================================================
# On 2026-08-24 the SHARED stage1 was promoted to trust 9f07573349, taking it
# from METADATA_VERSION 11 to 13. `build/<host>/stage1-rustc/` -- the DEFAULT
# `--from` of this script, and the driver most measurement lanes seal as their
# CONTROL -- was deliberately NOT touched, because replacing a control turns it
# into a subject. Correct, and it left a trap:
#
#     seal from the default source  ->  driver=11 against sysroot=13
#                                   ->  SYSROOT_COMPAT = FAIL
#                                   ->  `guard` refuses every spawn (exit 96)
#
# and the refusal named neither the remedy nor the fact that a WORKING v11
# sysroot was sitting three directories away. A fail-closed gate whose remedy
# is undiscoverable is how a gate teaches people to work around it. Worse, a
# lane that read only the version-skew text was told "the sysroot must be
# rebuilt" -- a multi-hour answer to a problem whose real answer is a path.
#
# THE DECISION: `seal` AUTO-SELECTS the compile sysroot, from an ORDERED,
# HAND-WRITTEN REGISTRY, keyed by the DRIVER'S OWN METADATA_VERSION, and only
# after PROVING the pair with the same 4-fact check `sysrootcheck` runs. The
# argument, and the four properties that keep it from being a guess:
#
#   1. IT NEVER OVERRIDES STATED INTENT. `--sysroot DIR` and
#      TRUST_SEAL_COMPILE_SYSROOT are honoured verbatim, even when they fail.
#      Auto-selection is consulted ONLY when nobody said anything.
#   2. IT NEVER CHANGES A PAIRING THAT ALREADY WORKS. The default
#      build/<host>/stage1 is tried FIRST and kept whenever it passes, so a
#      lane sealing a current driver gets exactly what it got yesterday.
#      Auto-selection can only fire where the old behaviour was a guaranteed
#      FAIL -- it strictly replaces a failure, never a success.
#   3. THE ORDER IS A DECISION, NOT A SCAN. There is no globbing and no
#      filesystem search: `sysroot_registry` is a literal list with a stated
#      reason per entry, so "which of the four v11 sysroots" is answered by
#      something a human wrote and a reviewer can read. The v11 entry chosen
#      first is the promotion's own COW backup, which is byte-identical
#      (74/74, verified in reports/stage1-promotion-2026-08-24.md) to the
#      stage1 every pre-promotion seal was built against -- so auto-selecting
#      it REPRODUCES the pre-promotion pairing exactly rather than inventing a
#      new one. A registry that has gone stale therefore refuses loudly; it
#      does not fall back to guessing.
#   4. IT IS ALWAYS PRINTED AND ALWAYS RECORDED. Every seal now carries
#      SYSROOT (the path) and SYSROOT_SOURCE (stated / default / auto, with
#      the registry reason), on exactly the discipline REV/REV_SOURCE already
#      follow here: provenance that could be mistaken for a stated fact must
#      be labelled as what it is.
#
# AND IT REFUSES RATHER THAN GUESS, in three separate places:
#   * the driver's own METADATA_VERSION is UNKNOWN  -> no key, no selection;
#   * NO registered sysroot carries that version    -> named refusal listing
#     the whole registry with each entry's live version;
#   * a version-matching candidate FAILS facts 3/4  -> rejected and reported,
#     never used because the number matched.
# `sysroottest` mutation-proves each of those: neuter the version filter and
# the no-match refusal turns into a selection; neuter the 4-fact verification
# and a deliberately-broken same-version sysroot gets selected. A mechanism
# whose removal changes nothing was never doing the work.
#
# ESCAPES, for a lane that wants the old behaviour:
#   --sysroot DIR                   pin this seal's compile sysroot
#   TRUST_SEAL_COMPILE_SYSROOT=DIR  pin it for a whole lane
#   TRUST_SEAL_NO_AUTO_SYSROOT=1    never auto-select; use the default and let
#                                   SYSROOT_COMPAT/`guard` fail closed
#   scripts/seal_driver.sh sysroots [<trustc>]   what is registered, and at
#                                   which live METADATA_VERSION
#
# THE DYLD PATH IS DELIBERATELY NOT AUTO-SELECTED WITH IT. The wrapper's
# DYLD_LIBRARY_PATH still points at build/<host>/stage1/lib, which supplies the
# DRIVER BINARY's own libstd. That dylib survived the promotion byte-identical,
# and a compile sysroot may be rlib-only (the v12 collateral sysroot is), so
# moving both together is how every driver spawn dies in dyld.
#
# ===========================================================================
# WHY A SEAL MUST NOT TAKE ITS REV FROM $TRUST_REPO_ROOT
# ===========================================================================
# `seal` used to record `git -C $ROOT rev-parse HEAD`, where $ROOT is the
# SHARED repo -- not the worktree the driver was compiled from. Every lane
# builds in a detached worktree, so wave-W3b's seal read 4854cf3a9c while its
# sources were 36cbb1130d+W3+W3b, and two lanes independently hand-patched the
# REV file afterwards. A snapshot that misreports its own provenance is worse
# than one that admits it does not know.
#
# The identity of a seal is its DYLIB DIGEST (SHA256, always recorded). The rev
# is provenance ABOUT that identity and now comes only from the build tree:
# `--worktree DIR` if stated, else the cargo dep-file under `--from`, else the
# literal string `undetermined` -- never $ROOT's HEAD. What $ROOT's HEAD was is
# kept, clearly labelled, in SHARED_ROOT_REV, where it cannot be mistaken for
# the seal's own rev. REV_SOURCE records which of the three applied.
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
# Also: this paragraph used to say `seal` stamps REV/TREE from
# $TRUST_REPO_ROOT. IT NO LONGER DOES, and had not for some time — see the
# "WHY A SEAL MUST NOT TAKE ITS REV FROM $TRUST_REPO_ROOT" block above. REV
# comes from `--worktree`, else the cargo dep-file under `--from`, else the
# literal `undetermined`; $ROOT's HEAD is kept separately as SHARED_ROOT_REV
# where it cannot be mistaken for the seal's own rev. If you built elsewhere,
# pass `--worktree <that tree>` rather than writing provenance by hand.
set -uo pipefail

HOST="${TRUST_HOST:-aarch64-apple-darwin}"
ROOT="${TRUST_REPO_ROOT:-$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd -P)}"
STAGE1_SYSROOT="$ROOT/build/$HOST/stage1"
# The COMPILE sysroot a seal bakes into its wrapper is resolved per-seal by
# `resolve_compile_sysroot` — stated (--sysroot) > stated (env, below) >
# the default above when it PROVES OUT > auto-selected from `sysroot_registry`.
# Read the "WHICH SYSROOT A SEAL COMPILES AGAINST" block in the header before
# changing any of that. Only the DRIVER BINARY's own dylibs are pinned here:
# libstd for rustc-main itself lives under build/<host>/stage1/lib and a
# compile sysroot may be rlib-only, so DYLD_LIBRARY_PATH must keep pointing
# there — overriding both together makes every driver spawn die in dyld.
#   TRUST_SEAL_COMPILE_SYSROOT=DIR   pin the compile sysroot for a whole lane
#   TRUST_SEAL_NO_AUTO_SYSROOT=1     never auto-select; fail closed instead
#   TRUST_SEAL_SYSROOT_REGISTRY=A:B  replace the registry (tests; colon-separated)
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
# The recorded compat verdict as `guard` sees it: the file's first line, or
# the literal ABSENT when there is no readable verdict at all. Its own function
# so `guardtest`'s N4 mutation can restore the pre-2026-08-24 reading (absent
# == not-FAIL == fine) and watch the missing-verdict refusal go red.
sysroot_compat_verdict() { # <snapshot-root>
  local v; v=$(head -1 "$1/SYSROOT_COMPAT" 2>/dev/null || true)
  [ -n "$v" ] || v=ABSENT
  printf '%s\n' "$v"
}

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

  # Free fail-closed on the metadata-compatibility verdict. `seal` writes this
  # file; one file read per spawn, no compiler involved. A lane that ignores
  # `verify` still cannot measure through a driver that cannot read its sysroot.
  #
  # AN ABSENT VERDICT IS NOT AN OK VERDICT. This used to test only for the
  # literal string FAIL, so a snapshot with NO SYSROOT_COMPAT — one sealed
  # before the check existed, or one whose verdict was deleted — sailed
  # through. Measured 2026-08-24: build/sealed/seal-guardfix (v11 driver, v13
  # sysroot) PASSED this guard and then died inside the compiler with the exact
  # E0514 "compiled by <unknown rustc version>" that sysrootcheck exists to
  # pre-empt. Absence of evidence is the case this guard is FOR.
  if [ -n "$snaproot" ]; then
    local compat; compat=$(sysroot_compat_verdict "$snaproot")
    if [ "$compat" = ABSENT ]; then
      cat >&2 <<EOF
guard: REFUSING — this sealed driver has NO RECORDED sysroot-compat verdict.
guard:   snapshot   $snaproot
guard:   expected   $snaproot/SYSROOT_COMPAT   (missing or empty)
guard:   The seal predates the compat check, or its verdict was removed. An
guard:   ABSENT verdict is not an OK verdict — nothing here says this driver can
guard:   read the sysroot its wrapper names, and a driver that cannot dies with
guard:   a confusing E0514 several minutes into a build.
guard:   Mint and RECORD the verdict (about a second, no build; it touches
guard:   nothing but the verdict file, so a control stays the control it was):
guard:     scripts/seal_driver.sh reverdict $snaproot
guard:   If it refuses, that message names every sysroot this driver COULD use.
guard:   Then re-seal against one:
guard:     scripts/seal_driver.sh seal <tag> --from <build dir> --sysroot DIR
EOF
      return 96
    fi
    if [ "$compat" = FAIL ]; then
      cat >&2 <<EOF
guard: REFUSING — this sealed driver was recorded as UNABLE to read its sysroot.
guard:   snapshot   $snaproot
guard:   verdict    $snaproot/SYSROOT_COMPAT
EOF
      sed -n '2,8p' "$snaproot/SYSROOT_COMPAT" 2>/dev/null | sed 's/^/guard:   /' >&2
      echo "guard:   the full verdict, INCLUDING THE REMEDY, is in that file; re-check with:" >&2
      echo "guard:     scripts/seal_driver.sh sysrootcheck $snaproot" >&2
      echo "guard:   and see: scripts/seal_driver.sh sysroots $snaproot/rustc-main" >&2
      return 96
    fi
  fi

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
# sysrootcheck — is this driver's metadata format readable against that sysroot?
#
# Four independent facts, cheapest first, so a failure names its own cause:
#   1. the SYSROOT's METADATA_VERSION  — byte 8 of libcore's .rmeta header
#      (`rust\0\0\0<version>`); a pure file read, no compiler needed.
#   2. the DRIVER's METADATA_VERSION   — the same byte of a probe rlib built
#      from a `#![no_core]` source, which touches no sysroot crate at all, so
#      it still answers when std is unreadable.
#   3. whether `std` actually RESOLVES  — `--emit=metadata` on `fn main(){}`.
#   4. whether the sysroot's ENCODED MIR actually DECODES — codegen of one
#      monomorphized core generic (`Option::<u32>::map`), which forces the
#      driver to decode a real MIR body out of libcore's metadata.
# 3 and 4 together are the verdict; 1 and 2 turn "incompatible version of
# rustc" into two numbers and a remedy.
#
# WHY FACT 4 EXISTS (the 2026-08-21 blocker, made cheap): METADATA_VERSION
# equality is NECESSARY, NOT SUFFICIENT. trust f24fdb2fdb changed the MIR
# statement encoding (`Statement::trust_modular_arith`) without bumping the
# version byte, so a tip driver read "12=12 OK" from facts 1-3 against a
# pre-f24fdb2fdb sysroot — `fn main(){}` under `--emit=metadata` decodes crate
# ROOTS and tables but never a MIR BODY — and then ICEd 24 GB into a real build
# ("invalid enum variant tag while decoding `StmtDebugInfo`, expected 0..2,
# actual 15"). Fact 4 decodes a body in about a second and turns that class
# into a named refusal. The METADATA_VERSION bump for f24fdb2fdb landed with
# this probe; the probe is what catches the NEXT unversioned encoding change.
# ---------------------------------------------------------------------------
meta_version_of_file() {
  # First `rust\0\0\0<v>` in the file; prints the version byte, or nothing.
  python3 - "$1" <<'PY' 2>/dev/null
import sys, re
try:
    d = open(sys.argv[1], 'rb').read()
except OSError:
    raise SystemExit(1)
m = re.search(rb'rust\x00\x00\x00', d)
if m and m.end() < len(d):
    print(d[m.end()])
PY
}

sysroot_meta_version() {
  local sysroot="$1" f
  for f in "$sysroot/lib/rustlib/$HOST/lib"/libcore-*.rmeta \
           "$sysroot/lib/rustlib/$HOST/lib"/libstd-*.rmeta; do
    [ -f "$f" ] || continue
    meta_version_of_file "$f"
    return 0
  done
  return 1
}

driver_meta_version() {
  # A `#![no_core]` rlib: no sysroot crate is read, so this answers even when
  # every crate in the sysroot is unreadable. If the lang-item set this needs
  # ever drifts, the probe simply prints nothing and the caller says "unknown"
  # -- it must never be the reason a build is refused.
  local drv="$1" tmp; tmp=$(scratch)
  cat > "$tmp/mv.rs" <<'RS'
#![no_std]
#![no_core]
#![allow(internal_features)]
#![feature(no_core, lang_items)]
#[lang = "pointee_sized"] pub trait PointeeSized {}
#[lang = "meta_sized"] pub trait MetaSized: PointeeSized {}
#[lang = "sized"] pub trait Sized: MetaSized {}
#[lang = "copy"] pub trait Copy {}
#[lang = "legacy_receiver"] pub trait LegacyReceiver {}
pub struct Probe;
RS
  rm -f "$tmp/mv.rlib"
  "$drv" --edition 2021 -Zno-trust-verify --crate-type rlib \
         -o "$tmp/mv.rlib" "$tmp/mv.rs" >/dev/null 2>&1 || true
  [ -f "$tmp/mv.rlib" ] || return 1
  meta_version_of_file "$tmp/mv.rlib"
}

# ---------------------------------------------------------------------------
# FACTS 3 AND 4, QUIETLY, FOR ONE (driver, sysroot) PAIR.
#
# Extracted so that `sysrootcheck` (which prints) and the auto-selector (which
# must PROVE a candidate before choosing it) run the SAME probe. Returns
#   0  both pass          3  `std` does not resolve         4  MIR does not decode
# The driver's own output is left in S34_OUT / S34_DOUT for the caller.
#
# EVERY PATH HANDED TO THE DRIVER MUST BE ABSOLUTE. Fact 4 `cd`s into the
# scratch dir so a rustc-ice dump lands there and not in the caller's cwd; a
# RELATIVE driver or --sysroot therefore vanished, the probe "failed", and the
# gate printed `REFUSING — CANNOT DECODE THIS SYSROOT'S MIR` followed by an
# EMPTY error list. That is a fail-closed gate refusing for a reason that was
# not true, which is as corrosive as a false pass. Measured and fixed
# 2026-08-24: `sysrootcheck build/.../rustc-main` said REFUSE where
# `sysrootcheck /Users/.../rustc-main` said OK, on the same two files.
# Callers now abspath both; this function asserts nothing and trusts them.
# ---------------------------------------------------------------------------
S34_OUT=""; S34_DOUT=""
sysroot_facts_34() { # <drv-abs> <sysroot-abs-or-empty> <pass_sysroot 0|1>
  local drv="$1" sysroot="$2" pass="$3" tmp rc=0 drc=0
  tmp=$(scratch)
  S34_OUT=""; S34_DOUT=""
  printf 'fn main() {}\n' > "$tmp/hello.rs"
  rm -f "$tmp/hello.rmeta"
  if [ "$pass" = 1 ]; then
    S34_OUT=$("$drv" --sysroot "$sysroot" --edition 2021 -Zno-trust-verify \
                     --emit=metadata --crate-type bin \
                     -o "$tmp/hello.rmeta" "$tmp/hello.rs" 2>&1) || rc=$?
  else
    S34_OUT=$("$drv" --edition 2021 -Zno-trust-verify \
                     --emit=metadata --crate-type bin \
                     -o "$tmp/hello.rmeta" "$tmp/hello.rs" 2>&1) || rc=$?
  fi
  # NO SIZE CHECK HERE, and that is deliberate. `--crate-type bin
  # --emit=metadata` writes a ZERO-BYTE file at `-o` (a bin crate has no
  # metadata to emit), measured 2026-08-24 on this driver. The old line read
  # `[ -s "$tmp/hello.rmeta" ] || rc=${rc:-1}` — two bugs cancelling: it tested
  # a file that is always empty, and `${rc:-1}` expands to `0` when rc is
  # already 0, so it could never fire. Strengthening it to `rc=1` turned every
  # fact 3 into a failure. The exit status IS the signal for resolution
  # (E0514/E0463 are hard errors); fact 4 below carries the sufficiency check
  # and does verify its object file.
  [ "$rc" = 0 ] || return 3

  # fact 4: codegen of one monomorphized core generic forces a real MIR body
  # out of libcore's metadata, statement by statement.
  cat > "$tmp/mirprobe.rs" <<'RS'
fn main() {
    let v: Option<u32> = Some(core::hint::black_box(1u32));
    let w = v.map(|x| x.wrapping_add(1));
    core::hint::black_box(w);
}
RS
  rm -f "$tmp/mirprobe.o"
  if [ "$pass" = 1 ]; then
    S34_DOUT=$(cd "$tmp" && "$drv" --sysroot "$sysroot" --edition 2021 -Zno-trust-verify \
                     -Copt-level=0 --emit=obj --crate-type bin \
                     -o "$tmp/mirprobe.o" "$tmp/mirprobe.rs" 2>&1) || drc=$?
  else
    S34_DOUT=$(cd "$tmp" && "$drv" --edition 2021 -Zno-trust-verify \
                     -Copt-level=0 --emit=obj --crate-type bin \
                     -o "$tmp/mirprobe.o" "$tmp/mirprobe.rs" 2>&1) || drc=$?
  fi
  if [ "$drc" = 0 ] && [ ! -s "$tmp/mirprobe.o" ]; then drc=1; fi
  [ "$drc" = 0 ] || return 4
  return 0
}

# ---------------------------------------------------------------------------
# THE SYSROOT REGISTRY — AN ORDERED, HAND-WRITTEN LIST. NOT A FILESYSTEM SCAN.
#
# One `PATH<TAB>WHY` per line, most-canonical first. The ORDER is the tie-break
# and it is a DECISION: several sysroots on this machine share a
# METADATA_VERSION and differ in content, so "pick the first one found" would
# be a guess. A literal list is something a human wrote and a reviewer reads.
#
# WHEN A PROMOTION HAPPENS, EDIT THIS LIST. A stale registry makes the selector
# REFUSE LOUDLY (naming every entry and its live version) — it never falls back
# to guessing, so going stale costs a clear error message, not a wrong pairing.
# ---------------------------------------------------------------------------
sysroot_registry() {
  if [ -n "${TRUST_SEAL_SYSROOT_REGISTRY:-}" ]; then
    printf '%s\n' "$TRUST_SEAL_SYSROOT_REGISTRY" | tr ':' '\n' | grep -v '^$' \
      | sed 's/$/\tstated in TRUST_SEAL_SYSROOT_REGISTRY/'
    return 0
  fi
  printf '%s\t%s\n' \
    "$ROOT/build/$HOST/stage1" \
      'the shared stage1 — what a lane means by "the sysroot" unless it says otherwise' \
    "$ROOT/build/$HOST/stage1.backup-v11-20260824T023603Z" \
      'the 2026-08-24 promotion COW backup; byte-identical 74/74 to the stage1 that every pre-promotion seal was built against, so choosing it REPRODUCES the old pairing' \
    "$ROOT/build/$HOST/stage1.old-v11-20260824T023603Z" \
      'the same tree, original inodes, moved aside by the promotion swap' \
    "$ROOT/build/$HOST/stage2" \
      'the stage2 sysroot — a last v11 resort if both promotion trees are reaped'
}

# The registry with each entry's LIVE METADATA_VERSION. Pure reporting.
sysroot_registry_table() {
  local path why v
  sysroot_registry | while IFS=$'\t' read -r path why; do
    [ -n "$path" ] || continue
    if [ ! -d "$path" ]; then
      printf '  %-8s %s\n            %s\n' "ABSENT" "$path" "$why"
      continue
    fi
    v=$(sysroot_meta_version "$path" || true); [ -n "$v" ] || v="no-rmeta"
    printf '  %-8s %s\n            %s\n' "v$v" "$path" "$why"
  done
}

# THE PREDICATE THAT MAKES MISPAIRING IMPOSSIBLE. Its own function so that
# `sysroottest` can neuter exactly this and watch the refusals go red.
sysroot_version_matches() { # <driver-version> <sysroot-version>
  [ "$1" = "$2" ]
}

# A driver whose own METADATA_VERSION could not be read gives the selector NO
# KEY. Its own function for the same reason.
sysroot_key_usable() { # <driver-version>
  [ -n "$1" ] && [ "$1" != unknown ]
}

# Registry entries whose live version equals <want>, in registry order.
sysroot_candidates() { # <want-version>
  local want="$1" path why v
  sysroot_registry | while IFS=$'\t' read -r path why; do
    [ -n "$path" ] || continue
    [ -d "$path" ] || continue
    v=$(sysroot_meta_version "$path" || true)
    [ -n "$v" ] || continue
    sysroot_version_matches "$want" "$v" || continue
    printf '%s\t%s\n' "$path" "$why"
  done
}

# ---------------------------------------------------------------------------
# auto_select_sysroot — choose a compile sysroot for a driver, or REFUSE.
#
# Never a guess: keyed on the driver's own METADATA_VERSION, filtered by
# `sysroot_version_matches`, and every surviving candidate must PASS facts 3
# and 4 before it is chosen. Sets AUTO_SYSROOT / AUTO_SYSROOT_WHY on success.
# ---------------------------------------------------------------------------
AUTO_SYSROOT=""; AUTO_SYSROOT_WHY=""
auto_select_sysroot() { # <drv-abs> <driver-version>
  local drv="$1" dv="$2" path why cands rc tried=0
  AUTO_SYSROOT=""; AUTO_SYSROOT_WHY=""

  if ! sysroot_key_usable "$dv"; then
    cat >&2 <<EOF
auto-sysroot: REFUSING TO CHOOSE — THE DRIVER'S OWN METADATA_VERSION IS UNKNOWN.
auto-sysroot:   driver   $drv
auto-sysroot:   The \`#![no_core]\` probe produced no rlib for it, so there is no
auto-sysroot:   key to select on and any choice would be a guess. State one:
auto-sysroot:     scripts/seal_driver.sh seal <tag> --sysroot DIR
auto-sysroot:     TRUST_SEAL_COMPILE_SYSROOT=DIR scripts/seal_driver.sh seal <tag>
EOF
    return 1
  fi

  cands=$(sysroot_candidates "$dv")
  if [ -z "$cands" ]; then
    cat >&2 <<EOF
auto-sysroot: REFUSING TO CHOOSE — NO REGISTERED SYSROOT IS AT METADATA_VERSION $dv.
auto-sysroot:   driver   $drv  (METADATA_VERSION $dv)
auto-sysroot:   The registry is a hand-written list, and going stale makes it
auto-sysroot:   refuse rather than guess. What is registered right now:
EOF
    sysroot_registry_table >&2
    cat >&2 <<EOF
auto-sysroot:   Fix ONE of these, in order of preference:
auto-sysroot:     1. state the sysroot for this seal:  --sysroot DIR
auto-sysroot:     2. state it for the lane:            TRUST_SEAL_COMPILE_SYSROOT=DIR
auto-sysroot:     3. add the sysroot to \`sysroot_registry\` in this file, WITH a
auto-sysroot:        reason — that is the durable fix after a stage1 promotion.
EOF
    return 1
  fi

  while IFS=$'\t' read -r path why; do
    [ -n "$path" ] || continue
    tried=$((tried+1))
    rc=0; sysroot_facts_34 "$drv" "$path" 1 || rc=$?
    if [ "$rc" = 0 ]; then
      AUTO_SYSROOT="$path"; AUTO_SYSROOT_WHY="$why"
      note "auto-sysroot: SELECTED $path"
      note "auto-sysroot:   driver METADATA_VERSION $dv == sysroot $dv, std resolves, a core MIR body decodes."
      note "auto-sysroot:   registry reason: $why"
      note "auto-sysroot:   THIS WAS AUTO-SELECTED, NOT STATED. To pin it: --sysroot $path"
      return 0
    fi
    note "auto-sysroot: rejected $path — METADATA_VERSION $dv matches but fact $rc failed (3=std unresolved, 4=MIR undecodable)."
  done <<EOF
$cands
EOF

  cat >&2 <<EOF
auto-sysroot: REFUSING TO CHOOSE — $tried registered sysroot(s) carry METADATA_VERSION
auto-sysroot:   $dv, and NONE of them passed the 4-fact check against this driver.
auto-sysroot:   driver   $drv
auto-sysroot:   A matching version byte is NECESSARY, NOT SUFFICIENT; that is
auto-sysroot:   exactly what fact 4 exists to catch, and it is not overridden by
auto-sysroot:   the number matching. State a sysroot with --sysroot DIR, or see
auto-sysroot:   reports/metadata-v12-sysroot.md for building one without x.py.
EOF
  return 1
}

# ---------------------------------------------------------------------------
# resolve_compile_sysroot — the ONE place that decides what a seal compiles
# against. Sets RCS_PATH / RCS_SOURCE. Never fails: the last resort is the
# documented default, recorded as such, which then fails closed through
# SYSROOT_COMPAT and `guard` exactly as it does today. Falling back to a named
# default that demonstrably refuses is not a guess; silently pairing with some
# other sysroot would be.
# ---------------------------------------------------------------------------
RCS_PATH=""; RCS_SOURCE=""
resolve_compile_sysroot() { # <src-bin-abs> <stated-or-empty>
  local drv="$1" stated="$2" dv sv
  RCS_PATH=""; RCS_SOURCE=""

  if [ -n "$stated" ]; then
    RCS_PATH=$(abspath "$stated"); RCS_SOURCE="stated (--sysroot)"; return 0
  fi
  if [ -n "${TRUST_SEAL_COMPILE_SYSROOT:-}" ]; then
    RCS_PATH=$(abspath "$TRUST_SEAL_COMPILE_SYSROOT")
    RCS_SOURCE="stated (TRUST_SEAL_COMPILE_SYSROOT)"; return 0
  fi

  # The default FIRST, and kept whenever it proves out — so auto-selection can
  # only ever replace a failure, never a working pairing.
  if sysroot_facts_34 "$drv" "$STAGE1_SYSROOT" 1; then
    RCS_PATH="$STAGE1_SYSROOT"
    RCS_SOURCE="default (build/$HOST/stage1 — and it proves out: std resolves, MIR decodes)"
    return 0
  fi

  dv=$(driver_meta_version "$drv" || true); [ -n "$dv" ] || dv=unknown
  sv=$(sysroot_meta_version "$STAGE1_SYSROOT" || true); [ -n "$sv" ] || sv=unknown

  if [ -n "${TRUST_SEAL_NO_AUTO_SYSROOT:-}" ]; then
    note "seal: the default sysroot does not pair with this driver (driver=$dv sysroot=$sv)"
    note "seal: and auto-selection is OFF (TRUST_SEAL_NO_AUTO_SYSROOT). Using the default;"
    note "seal: SYSROOT_COMPAT will record FAIL and \`guard\` will refuse every spawn."
    RCS_PATH="$STAGE1_SYSROOT"
    RCS_SOURCE="default (build/$HOST/stage1) — auto-selection OFF (TRUST_SEAL_NO_AUTO_SYSROOT); driver=$dv sysroot=$sv"
    return 0
  fi

  note "seal: the default sysroot cannot be used by this driver (driver=$dv sysroot=$sv);"
  note "seal: consulting the sysroot registry."
  if auto_select_sysroot "$drv" "$dv"; then
    RCS_PATH="$AUTO_SYSROOT"
    RCS_SOURCE="auto (registry: $AUTO_SYSROOT_WHY)"
    return 0
  fi

  RCS_PATH="$STAGE1_SYSROOT"
  RCS_SOURCE="default (build/$HOST/stage1) — auto-selection REFUSED (see above); driver=$dv sysroot=$sv"
  note "seal: auto-selection REFUSED and will not guess. Sealing against the default,"
  note "seal: which records SYSROOT_COMPAT = FAIL so nothing can measure through it."
  return 0
}

# The --sysroot a generated wrapper hard-codes, but only when the literal names
# a directory that exists: these wrappers are shell, so the field may be `$VAR`,
# and reporting an unexpanded variable as "the sysroot" is worse than unknown.
wrapper_sysroot() {
  local f="$1" cand
  cand=$(sed -n 's/.*--sysroot "\([^"]*\)".*/\1/p' "$f" 2>/dev/null | head -1)
  [ -n "$cand" ] && [ -d "$cand" ] && printf '%s\n' "$cand"
  return 0
}

# Resolve a caller-supplied target into (driver binary, sysroot, dyld path).
# Accepts a sealed directory, a generated `tc` wrapper, or a bare rustc-main.
cmd_sysrootcheck() {
  local target="" sysroot="" dyld="" drv=""
  target="${1:-}"; shift || true
  while [ $# -gt 0 ]; do
    case "$1" in
      --sysroot) sysroot="$2"; shift 2 ;;
      --dyld)    dyld="$2";    shift 2 ;;
      *) die "sysrootcheck: unknown argument $1" ;;
    esac
  done
  [ -n "$target" ] || target="$DEFAULT_FROM/rustc-main"

  # A wrapper script supplies its OWN --sysroot; passing a second one makes
  # rustc refuse with "Option 'sysroot' given more than once". So: only add the
  # flag for a bare binary, or when the caller stated one explicitly.
  local sysroot_given=0 pass_sysroot=1
  [ -n "$sysroot" ] && sysroot_given=1
  if [ -d "$target" ]; then
    drv="$target/rustc-main"
    [ $sysroot_given -eq 1 ] || sysroot=$(wrapper_sysroot "$target/tc")
  elif [ -x "$target" ]; then
    drv="$target"
    if [ "$(head -c 2 "$target" 2>/dev/null)" = '#!' ]; then
      # A wrapper. It sets its own sysroot; do not add ours unless told to.
      [ $sysroot_given -eq 1 ] || { sysroot=$(wrapper_sysroot "$target"); pass_sysroot=0; }
    fi
  else
    die "sysrootcheck: no such driver or sealed directory: $target"
  fi
  [ -x "$drv" ] || die "sysrootcheck: not executable: $drv"
  # ABSOLUTE, always. Fact 4 `cd`s into the scratch dir, so a relative driver
  # or sysroot used to make it fail with an empty error list — a refusal for a
  # reason that was not true. See the note on `sysroot_facts_34`.
  drv=$(realpath_f "$drv")
  [ -n "$sysroot" ] && sysroot=$(abspath "$sysroot")
  # Only default to the stage1 sysroot when we are the one choosing it. For a
  # wrapper we are NOT: it has already chosen, and naming a different one here
  # would both duplicate the flag and attribute the wrong sysroot to the result.
  if [ -z "$sysroot" ] && [ $pass_sysroot -eq 1 ]; then sysroot="$STAGE1_SYSROOT"; fi
  [ -n "$dyld" ] || dyld="$STAGE1_SYSROOT/lib"
  export DYLD_LIBRARY_PATH="$dyld${DYLD_LIBRARY_PATH:+:$DYLD_LIBRARY_PATH}"

  local sv dv rc=0
  sv=$(sysroot_meta_version "$sysroot" || true); [ -n "$sv" ] || sv=unknown
  [ -n "$sysroot" ] || sysroot="(the wrapper's own — not a literal in $target)"
  dv=$(driver_meta_version "$drv" || true);      [ -n "$dv" ] || dv=unknown

  sysroot_facts_34 "$drv" "$sysroot" "$pass_sysroot" || rc=$?

  echo "sysrootcheck: driver   $drv"
  echo "sysrootcheck: sysroot  $sysroot"
  echo "sysrootcheck: METADATA_VERSION  driver=$dv  sysroot=$sv"
  if [ "$rc" = 0 ]; then
    echo "sysrootcheck: OK — std resolves AND a core MIR body decodes; this driver can compile against this sysroot."
    return 0
  fi

  if [ "$rc" = 4 ]; then
    # --- fact 4 failed: the version byte was NECESSARY, NOT SUFFICIENT ------
    cat >&2 <<EOF
sysrootcheck: REFUSING — THIS DRIVER CANNOT DECODE THIS SYSROOT'S MIR.
sysrootcheck:   driver            $drv
sysrootcheck:   sysroot           $sysroot
sysrootcheck:   METADATA_VERSION  driver=$dv  sysroot=$sv  (equal or not, it did not protect you)
sysrootcheck:   std RESOLVES (fact 3 passed) but decoding a real MIR body out of
sysrootcheck:   libcore's metadata failed (fact 4). That is the signature of an
sysrootcheck:   ENCODING change that landed without a METADATA_VERSION bump
sysrootcheck:   (measured instance: f24fdb2fdb's Statement.trust_modular_arith —
sysrootcheck:   "invalid enum variant tag while decoding StmtDebugInfo").
sysrootcheck:   The version byte is NECESSARY, NOT SUFFICIENT; this probe is the
sysrootcheck:   sufficiency check. The sysroot must be rebuilt by THIS driver —
sysrootcheck:   without x.py: see reports/metadata-v12-sysroot.md (dispatch route).
sysrootcheck:   first errors from the decode probe:
EOF
    echo "$S34_DOUT" | grep -E 'internal compiler error|invalid enum variant|error\[|^error' | head -6 | sed 's/^/sysrootcheck:     /' >&2
    sysrootcheck_remedy "$drv" "$dv" "$sysroot" >&2
    return 96
  fi

  cat >&2 <<EOF
sysrootcheck: REFUSING — THIS DRIVER CANNOT READ THIS SYSROOT.
sysrootcheck:   driver            $drv
sysrootcheck:   sysroot           $sysroot
sysrootcheck:   METADATA_VERSION  driver=$dv  sysroot=$sv
EOF
  if [ "$dv" != unknown ] && [ "$sv" != unknown ] && [ "$dv" != "$sv" ]; then
    cat >&2 <<EOF
sysrootcheck:   The metadata FORMAT versions differ, so every crate in the
sysrootcheck:   sysroot is unreadable to this driver. rustc reports this as
sysrootcheck:     error[E0514]: found crate \`std\` compiled by an incompatible
sysrootcheck:                   version of rustc ... by <unknown rustc version>
sysrootcheck:   which reads like a stale rebuild and is not one: \`cargo clean\`
sysrootcheck:   cannot help, and the version STRINGS may match exactly.
EOF
  else
    echo "sysrootcheck:   first errors from the resolution probe:" >&2
    echo "$S34_OUT" | grep -E '^(error|warning: unused)' | head -6 | sed 's/^/sysrootcheck:     /' >&2
  fi
  sysrootcheck_remedy "$drv" "$dv" "$sysroot" >&2
  return 96
}

# ---------------------------------------------------------------------------
# THE REMEDY BLOCK — why this exists.
#
# The 2026-08-24 stage1 promotion (11 -> 13) left every DEFAULT-source seal
# recording SYSROOT_COMPAT = FAIL, and the refusal above named no way out. The
# only advice on offer was "the sysroot must be rebuilt by a driver that writes
# version N" — a multi-hour answer, while a WORKING v11 sysroot sat three
# directories from the failing one. A fail-closed gate whose remedy is
# undiscoverable is how a gate teaches people to work around it.
#
# So the refusal now names: both versions (above), every registered sysroot AT
# THE DRIVER'S OWN VERSION with its path, the two ways to state one, and where
# to look when nothing matches. Nothing here is a suggestion to weaken a check.
# ---------------------------------------------------------------------------
sysrootcheck_remedy() { # <drv> <driver-version> <current-sysroot>
  local drv="$1" dv="$2" cur="$3" cands path why n=0
  echo "sysrootcheck:"
  echo "sysrootcheck:   ── HOW TO GET A WORKING PAIR ────────────────────────────────"
  if ! sysroot_key_usable "$dv"; then
    cat <<EOF
sysrootcheck:   This driver's OWN METADATA_VERSION could not be read (the
sysrootcheck:   \`#![no_core]\` probe produced no rlib), so nothing can be matched
sysrootcheck:   to it automatically. State the sysroot you mean:
sysrootcheck:     scripts/seal_driver.sh seal <tag> --sysroot DIR
sysrootcheck:     TRUST_SEAL_COMPILE_SYSROOT=DIR  (for a whole lane)
sysrootcheck:   Everything registered on this machine, with live versions:
EOF
    sysroot_registry_table
    return 0
  fi
  cands=$(sysroot_candidates "$dv")
  if [ -z "$cands" ]; then
    cat <<EOF
sysrootcheck:   NO registered sysroot on this machine is at METADATA_VERSION $dv.
sysrootcheck:   What IS registered (\`scripts/seal_driver.sh sysroots\`):
EOF
    sysroot_registry_table
    cat <<EOF
sysrootcheck:   Either point at one that is not registered —
sysrootcheck:     scripts/seal_driver.sh seal <tag> --sysroot DIR
sysrootcheck:     TRUST_SEAL_COMPILE_SYSROOT=DIR
sysrootcheck:   — and then ADD it to \`sysroot_registry\` in scripts/seal_driver.sh
sysrootcheck:   so the next lane does not repeat this, or build one without x.py:
sysrootcheck:   reports/metadata-v12-sysroot.md.
EOF
    return 0
  fi
  cat <<EOF
sysrootcheck:   This machine ALREADY HAS a sysroot at METADATA_VERSION $dv — you do
sysrootcheck:   not need to rebuild anything. Registered, in preference order:
EOF
  while IFS=$'\t' read -r path why; do
    [ -n "$path" ] || continue
    n=$((n+1))
    echo "sysrootcheck:     $path"
    echo "sysrootcheck:         ($why)"
  done <<EOF
$cands
EOF
  path=$(printf '%s\n' "$cands" | head -1 | cut -f1)
  cat <<EOF
sysrootcheck:   Use one, either for a single seal:
sysrootcheck:     scripts/seal_driver.sh seal <tag> --sysroot $path
sysrootcheck:   or for a whole lane:
sysrootcheck:     export TRUST_SEAL_COMPILE_SYSROOT=$path
sysrootcheck:   \`seal\` DOES THIS FOR YOU by default (auto-selection, header block
sysrootcheck:   "WHICH SYSROOT A SEAL COMPILES AGAINST"). You are seeing this
sysrootcheck:   message because the pair was NAMED — by you, by a sealed wrapper,
sysrootcheck:   or with auto-selection off — and a named pair is never overridden.
sysrootcheck:   Full registry:  scripts/seal_driver.sh sysroots $drv
EOF
}

# ---------------------------------------------------------------------------
# sysroots — what is registered, at which live METADATA_VERSION, and (given a
# driver) which entries could pair with it. One second, no build.
# ---------------------------------------------------------------------------
cmd_sysroots() {
  local drv="${1:-}" dv="" cands
  echo "sysroot registry (ordered; the order is the tie-break and it is a decision):"
  sysroot_registry_table
  [ -n "$drv" ] || {
    echo
    echo "Pass a driver to see which of these could pair with it:"
    echo "  scripts/seal_driver.sh sysroots $DEFAULT_FROM/rustc-main"
    return 0
  }
  drv=$(realpath_f "$drv")
  [ -x "$drv" ] || die "sysroots: not executable: $drv"
  export DYLD_LIBRARY_PATH="$STAGE1_SYSROOT/lib${DYLD_LIBRARY_PATH:+:$DYLD_LIBRARY_PATH}"
  dv=$(driver_meta_version "$drv" || true); [ -n "$dv" ] || dv=unknown
  echo
  echo "driver  $drv"
  echo "        METADATA_VERSION $dv"
  if ! sysroot_key_usable "$dv"; then
    echo "        -> UNKNOWN: no key, so auto-selection REFUSES. State --sysroot DIR."
    return 0
  fi
  cands=$(sysroot_candidates "$dv")
  if [ -z "$cands" ]; then
    echo "        -> no registered sysroot is at v$dv; auto-selection REFUSES (it does not guess)."
    return 0
  fi
  echo "        -> version-matching candidates, in the order the selector tries them:"
  printf '%s\n' "$cands" | cut -f1 | sed 's/^/             /'
  echo "        (each is still PROVED with facts 3+4 before it is chosen)"
}

# ---------------------------------------------------------------------------
# seal — snapshot into a SELF-CONTAINED pair (binary + uniquely-named dylib).
#
# A leaf name that exists nowhere else cannot be substituted by leaf-name
# lookup. That, plus keeping the shared deps dir OFF the wrapper's
# DYLD_LIBRARY_PATH, closes the channel structurally rather than by convention.
# ---------------------------------------------------------------------------
cmd_seal() {
  local tag="" from="$DEFAULT_FROM" out="" worktree="" sysroot_arg=""
  tag="${1:-}"; shift || true
  while [ $# -gt 0 ]; do
    case "$1" in
      --from)     from="$2"; shift 2 ;;
      --out)      out="$2";  shift 2 ;;
      --worktree) worktree="$2"; shift 2 ;;
      --sysroot)  sysroot_arg="$2"; shift 2 ;;
      *) die "seal: unknown argument $1" ;;
    esac
  done
  [ -n "$tag" ] || die "usage: seal_driver.sh seal <tag> [--from DIR] [--out DIR] [--worktree DIR] [--sysroot DIR]"
  case "$tag" in
    *[!A-Za-z0-9_-]*) die "seal: tag must be [A-Za-z0-9_-]+ (it becomes a dylib leaf name)" ;;
  esac
  out="${out:-$ROOT/build/sealed/seal-$tag}"

  local src_bin="$from/rustc-main" src_dylib="$from/deps/librustc_driver.dylib"
  [ -x "$src_bin" ]  || die "seal: no rustc-main at $src_bin"
  [ -f "$src_dylib" ] || die "seal: no librustc_driver.dylib at $src_dylib"

  # WHICH SYSROOT THIS SEAL COMPILES AGAINST. Decided BEFORE the copy, from the
  # SOURCE binary, so the answer does not depend on the seal existing yet. The
  # rule and its argument are in the header block "WHICH SYSROOT A SEAL
  # COMPILES AGAINST"; the short version is stated > default-that-proves-out >
  # auto-selected-and-proved > the default recorded as a refusal. This is the
  # only line that gets to make that choice.
  export DYLD_LIBRARY_PATH="$STAGE1_SYSROOT/lib${DYLD_LIBRARY_PATH:+:$DYLD_LIBRARY_PATH}"
  resolve_compile_sysroot "$(realpath_f "$src_bin")" "$sysroot_arg"
  local compile_sysroot="$RCS_PATH" sysroot_source="$RCS_SOURCE"

  rm -rf "$out"; mkdir -p "$out" || die "seal: cannot create $out"
  cp "$src_bin"   "$out/rustc-main"
  cp "$src_dylib" "$out/librustc_driver_$tag.dylib"

  local new="$out/librustc_driver_$tag.dylib"
  install_name_tool -id "$new" "$new"            || die "seal: install_name_tool -id failed"

  # REPOINT WHAT THE BINARY ACTUALLY NAMES, NOT WHAT WE GUESS IT NAMES.
  # `-change OLD NEW` matches the load command STRING EXACTLY and exits 0 when
  # nothing matches. Passing "$from/deps/librustc_driver.dylib" therefore
  # silently did nothing whenever $from reached the same file by a different
  # name — a symlinked TRUST_REPO_ROOT is enough — and produced a "sealed"
  # binary still pointing at the LIVE dylib. Measured 2026-08-24: the seal
  # completed, `otool -L` still named
  # build/<host>/stage1-rustc/release/deps/librustc_driver.dylib, `guard`
  # correctly refused it as a cp-snapshot, and PERTURB_CLASSES came out empty.
  # So: read the real load commands, change every librustc_driver entry, and
  # then ASSERT the result instead of trusting a zero exit.
  local dep
  while IFS= read -r dep; do
    [ -n "$dep" ] || continue
    install_name_tool -change "$dep" "$new" "$out/rustc-main" \
      || die "seal: install_name_tool -change '$dep' failed"
  done <<EOF
$(driver_deps "$out/rustc-main")
EOF
  codesign -f -s - "$new" 2>/dev/null || true
  codesign -f -s - "$out/rustc-main" 2>/dev/null || true

  # The assertion. A seal that still names any librustc_driver outside itself
  # is not a seal; refusing here is cheaper than a measurement taken through it.
  local remaining; remaining=$(driver_deps "$out/rustc-main" | grep -Fxv "$new" || true)
  [ -z "$remaining" ] || die "seal: THE RESEAL DID NOT TAKE — $out/rustc-main still names:
$(printf '%s\n' "$remaining" | sed 's/^/  /')
seal: expected only $new. This binary would load a driver outside its own
seal: snapshot, which is exactly the contamination this script exists to stop."
  driver_deps "$out/rustc-main" | grep -qx "$new" \
    || die "seal: $out/rustc-main does not name its own dylib $new after resealing."

  # The wrapper. stage1/lib supplies libstd (@rpath) and is REVISION-INDEPENDENT
  # (the seed std, not rebuilt by buildtrustc.sh). The stage1-rustc deps dir is
  # DELIBERATELY ABSENT: nothing in the snapshot needs it, and its presence is
  # exactly the contamination channel. The guard runs anyway, before exec.
  cat > "$out/tc" <<EOF
#!/bin/sh
# Generated by scripts/seal_driver.sh — sealed driver wrapper for tag '$tag'.
# The shared stage1-rustc deps dir is deliberately NOT on DYLD_LIBRARY_PATH.
# Compile sysroot: $sysroot_source
#   (DYLD_LIBRARY_PATH is NOT moved with it — it supplies this binary's own
#    libstd, and a compile sysroot may be rlib-only.)
SEAL_DIR="$out"
DYLD_LIBRARY_PATH="$STAGE1_SYSROOT/lib\${DYLD_LIBRARY_PATH:+:\$DYLD_LIBRARY_PATH}"
export DYLD_LIBRARY_PATH
"$ROOT/scripts/seal_driver.sh" guard "\$SEAL_DIR/rustc-main" \\
    --dyld "\$DYLD_LIBRARY_PATH" --snapshot-root "\$SEAL_DIR" || exit 97
exec "\$SEAL_DIR/rustc-main" --sysroot "$compile_sysroot" "\$@"
EOF
  chmod +x "$out/tc"

  # ---- provenance -------------------------------------------------------
  # IDENTITY is the dylib digest. REV is provenance about that identity and
  # may come ONLY from the tree these artifacts were compiled from: stated
  # (--worktree), inferred from the cargo dep-file beside them, or admitted
  # unknown. $ROOT's HEAD is a DIFFERENT repo state and is recorded separately.
  shasum -a 256 "$new" "$out/rustc-main" > "$out/SHA256"

  local src="" rev_source=""
  if [ -n "$worktree" ]; then
    src="$worktree"; rev_source="stated (--worktree)"
  else
    local depfile
    depfile=$(ls "$from"/rustc-main.d "$from"/deps/rustc_main*.d 2>/dev/null | head -1)
    if [ -n "$depfile" ]; then
      # First absolute source path in the dep-file, then its git worktree root.
      local srcfile
      srcfile=$(tr ' ' '\n' < "$depfile" | grep -m1 '^/.*\.rs$' || true)
      if [ -n "$srcfile" ] && [ -e "$srcfile" ]; then
        src=$(git -C "$(dirname "$srcfile")" rev-parse --show-toplevel 2>/dev/null || true)
        [ -n "$src" ] && rev_source="inferred (dep-file $depfile)"
      fi
    fi
  fi

  if [ -n "$src" ] && git -C "$src" rev-parse HEAD >/dev/null 2>&1; then
    git -C "$src" rev-parse HEAD > "$out/REV"
    git -C "$src" status --porcelain | head -1 | grep -q . && echo dirty > "$out/TREE" || echo clean > "$out/TREE"
    printf '%s\n' "$src" > "$out/SRC_ROOT"
  else
    echo undetermined > "$out/REV"
    echo undetermined > "$out/TREE"
    printf '%s\n' "${src:-none}" > "$out/SRC_ROOT"
    rev_source="undetermined"
    note "seal: REV is UNDETERMINED for $out."
    note "seal: the build tree could not be identified from --from $from, and"
    note "seal: \$TRUST_REPO_ROOT's HEAD is NOT this driver's rev. Pass"
    note "seal:     --worktree <the tree you compiled>"
    note "seal: to record it. The seal is still usable: its identity is its"
    note "seal: dylib digest, which SHA256 always carries."
  fi
  printf '%s\n' "$rev_source" > "$out/REV_SOURCE"
  # Same discipline as REV/REV_SOURCE: a sysroot that was CHOSEN for a lane must
  # never be mistakable for one the lane STATED.
  printf '%s\n' "$compile_sysroot" > "$out/SYSROOT"
  printf '%s\n' "$sysroot_source"  > "$out/SYSROOT_SOURCE"
  ( cd "$ROOT" && git rev-parse HEAD ) > "$out/SHARED_ROOT_REV" 2>/dev/null || echo unknown > "$out/SHARED_ROOT_REV"

  # The metadata-compatibility verdict, recorded WHERE THE BUILD ENDS — so a
  # 24 GB build that produced an unusable driver says so now, not 20 minutes
  # later inside a confusing E0514. `guard` reads this file for free.
  #
  # THIS MUST COME BEFORE PERTURB_CLASSES. `cmd_classes` runs the wrapper,
  # the wrapper runs `guard`, and `guard` now refuses a snapshot with no
  # recorded verdict — so minting the class list first produced an empty
  # PERTURB_CLASSES on every seal. Measured while landing the absent-verdict
  # arm, 2026-08-24.
  local compat_verdict=OK
  cmd_sysrootcheck "$out" > "$out/SYSROOT_COMPAT.detail" 2>&1 || compat_verdict=FAIL
  { echo "$compat_verdict"; cat "$out/SYSROOT_COMPAT.detail"; } > "$out/SYSROOT_COMPAT"
  rm -f "$out/SYSROOT_COMPAT.detail"
  [ "$compat_verdict" = FAIL ] && note "seal: SYSROOT_COMPAT = FAIL for $out — see $out/SYSROOT_COMPAT"

  cmd_classes "$out/tc" > "$out/PERTURB_CLASSES" 2>/dev/null || true
  # A seal whose driver CAN read its sysroot must register classes; an empty
  # list there means the wrapper did not run, and that is worth saying out loud
  # rather than leaving a blank line in the summary.
  if [ "$compat_verdict" = OK ] && [ ! -s "$out/PERTURB_CLASSES" ]; then
    note "seal: WARNING: PERTURB_CLASSES is EMPTY though SYSROOT_COMPAT is OK —"
    note "seal: the wrapper did not produce a class list. Run it by hand:"
    note "seal:   $ROOT/scripts/seal_driver.sh classes $out/tc"
  fi

  echo "sealed $tag -> $out"
  echo "  rev            $(cat "$out/REV")  [$(cat "$out/REV_SOURCE")]"
  echo "  shared-root rev $(cat "$out/SHARED_ROOT_REV")  (NOT this seal's rev)"
  echo "  sysroot        $(cat "$out/SYSROOT")"
  echo "                 [$(cat "$out/SYSROOT_SOURCE")]"
  echo "  sysroot compat $(head -1 "$out/SYSROOT_COMPAT")"
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
  # SYSROOT_COMPAT fixtures. `guard` reads only the first line, so these are
  # exact stand-ins for the real verdict files without needing a real sysroot.
  # EVERY --snapshot-root fixture except the two that test the compat leg gets
  # an OK verdict, so each arm still fails for ITS OWN reason. Without this the
  # cpsnap/linksnap refusals would come from the absent-verdict arm and those
  # tests would silently stop covering resolution and realpath.
  printf 'OK\nsysrootcheck: (guardtest fixture)\n' > "$T/sealed/SYSROOT_COMPAT"
  printf 'OK\nsysrootcheck: (guardtest fixture)\n' > "$T/cpsnap/SYSROOT_COMPAT"
  printf 'OK\nsysrootcheck: (guardtest fixture)\n' > "$T/linksnap/SYSROOT_COMPAT"
  mkdir -p "$T/noverdict"
  cp "$T/sealed/rustc-main" "$T/noverdict/rustc-main"
  cp "$T/sealed/librustc_driver_gt.dylib" "$T/noverdict/librustc_driver_gt.dylib"
  install_name_tool -id "$T/noverdict/librustc_driver_gt.dylib" "$T/noverdict/librustc_driver_gt.dylib" 2>/dev/null
  install_name_tool -change "$T/sealed/librustc_driver_gt.dylib" "$T/noverdict/librustc_driver_gt.dylib" "$T/noverdict/rustc-main" 2>/dev/null
  mkdir -p "$T/failverdict"
  cp "$T/noverdict/rustc-main" "$T/failverdict/rustc-main"
  cp "$T/noverdict/librustc_driver_gt.dylib" "$T/failverdict/librustc_driver_gt.dylib"
  install_name_tool -id "$T/failverdict/librustc_driver_gt.dylib" "$T/failverdict/librustc_driver_gt.dylib" 2>/dev/null
  install_name_tool -change "$T/noverdict/librustc_driver_gt.dylib" "$T/failverdict/librustc_driver_gt.dylib" "$T/failverdict/rustc-main" 2>/dev/null
  printf 'FAIL\nsysrootcheck: (guardtest fixture)\n' > "$T/failverdict/SYSROOT_COMPAT"
  for f in "$T/noverdict/librustc_driver_gt.dylib" "$T/noverdict/rustc-main" \
           "$T/failverdict/librustc_driver_gt.dylib" "$T/failverdict/rustc-main"; do
    codesign -f -s - "$f" 2>/dev/null || true
  done
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
  gt_run REFUSE "SYSROOT_COMPAT = FAIL"                "" "$T/failverdict/rustc-main" --snapshot-root "$T/failverdict" --dyld ""
  gt_run REFUSE "SYSROOT_COMPAT MISSING is not OK"     "" "$T/noverdict/rustc-main"   --snapshot-root "$T/noverdict"   --dyld ""

  echo "== mutation: each mechanism removed must turn refusals RED =="
  local N1='resolve_honest() { echo "$1"; return 0; }; resolve_effective() { echo "$1"; return 0; }'
  gt_run PASS   "N1 no resolution: substitution ADMITTED"    "$N1" "$T/live/rustc-main" --dyld "$T/decoy"
  gt_run PASS   "N1 no resolution: sealed hijack ADMITTED"   "$N1" "$T/sealed/rustc-main" --snapshot-root "$T/sealed" --dyld "$T/decoy"
  gt_run REFUSE "N1 no resolution: legit @rpath REFUSED"     "$N1" "$T/inst/bin/trustc" --dyld ""
  local N2='realpath_f() { abspath "$1"; }'
  gt_run PASS   "N2 no realpath: symlink snapshot ADMITTED"  "$N2" "$T/linksnap/rustc-main" --snapshot-root "$T/linksnap" --dyld ""
  # N4 restores the pre-2026-08-24 compat leg, which tested ONLY for the
  # literal FAIL and so read an absent verdict as a fine one. The
  # missing-verdict refusal must go from REFUSE back to PASS, or that new arm
  # is not the thing doing the refusing. The FAIL arm must stay REFUSE under
  # the same mutation — it was always covered and must not be credited twice.
  local N4='sysroot_compat_verdict() { local v; v=$(head -1 "$1/SYSROOT_COMPAT" 2>/dev/null || true); [ -n "$v" ] || v=OK; printf "%s\\n" "$v"; }'
  gt_run PASS   "N4 absent verdict read as OK: ADMITTED"     "$N4" "$T/noverdict/rustc-main"   --snapshot-root "$T/noverdict"   --dyld ""
  gt_run REFUSE "N4 does not weaken the FAIL arm"            "$N4" "$T/failverdict/rustc-main" --snapshot-root "$T/failverdict" --dyld ""

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
# reverdict — (re)mint SYSROOT_COMPAT for a seal that already exists.
#
# For the two situations the 2026-08-24 promotion created: a seal made BEFORE
# the compat check existed (no verdict at all — `guard` now refuses those, and
# rightly, but the refusal is undiagnosed), and a seal whose recorded verdict
# is STALE because the sysroot underneath it was replaced. Costs a second and
# touches nothing but the verdict file: the binary, the dylib, the wrapper and
# the recorded sysroot are left exactly as they were, so a control stays the
# control it was. If you want a DIFFERENT sysroot, re-seal — do not edit this.
# ---------------------------------------------------------------------------
cmd_reverdict() {
  local dir="${1:-}"
  [ -n "$dir" ] || die "usage: seal_driver.sh reverdict <sealed-dir>"
  [ -x "$dir/rustc-main" ] || die "reverdict: no rustc-main in $dir — not a sealed directory"
  local prev="(none)"
  [ -f "$dir/SYSROOT_COMPAT" ] && prev=$(head -1 "$dir/SYSROOT_COMPAT")
  local verdict=OK
  cmd_sysrootcheck "$dir" > "$dir/SYSROOT_COMPAT.detail" 2>&1 || verdict=FAIL
  { echo "$verdict"; cat "$dir/SYSROOT_COMPAT.detail"; } > "$dir/SYSROOT_COMPAT"
  rm -f "$dir/SYSROOT_COMPAT.detail"
  echo "reverdict: $dir"
  echo "reverdict:   was $prev  ->  now $verdict"
  echo "reverdict:   full verdict and remedy: $dir/SYSROOT_COMPAT"
  [ "$verdict" = OK ]
}

# ---------------------------------------------------------------------------
# sysroottest — PROVE that AUTO-SELECTION CANNOT SILENTLY MISPAIR.
#
# Auto-selection is the friendly half of this file and therefore the dangerous
# half: a chooser that guesses would hand a lane a driver paired with a sysroot
# nobody named, which is the class of confusion the 4-fact sysrootcheck was
# written to end. So the three refusals are asserted, and then the mechanism
# behind each is NEUTERED and the verdict must go red. A mechanism whose
# removal changes nothing was never doing the work — the same standard
# `guardtest` holds `guard` to.
#
# It runs against the REAL drivers and sysroots on this machine plus two
# synthetic fixtures, and it REFUSES to run rather than skip: a test that
# quietly finds no material and exits 0 is a false green.
# ---------------------------------------------------------------------------
ST_PASS=0; ST_FAIL=0
st_ok()   { ST_PASS=$((ST_PASS+1)); printf '  ok   %s\n' "$1"; }
st_bad()  { ST_FAIL=$((ST_FAIL+1)); printf '  FAIL %s\n' "$1"; [ -n "${2:-}" ] && printf '%s\n' "$2" | sed 's/^/         | /'; return 0; }
st_want() { # <name> <expect-substring-or-empty> <got>
  case "$3" in *"$2"*) st_ok "$1" ;; *) st_bad "$1" "want to contain: $2
got: $3" ;; esac
}

cmd_sysroottest() {
  local T; T=$(scratch)/sysroottest
  rm -rf "$T"; mkdir -p "$T" || die "sysroottest: mkdir"
  export DYLD_LIBRARY_PATH="$STAGE1_SYSROOT/lib${DYLD_LIBRARY_PATH:+:$DYLD_LIBRARY_PATH}"

  # ---- material, or refuse ------------------------------------------------
  local drv; drv="$DEFAULT_FROM/rustc-main"
  [ -x "$drv" ] || die "sysroottest: no driver at $drv — cannot prove anything here."
  drv=$(realpath_f "$drv")
  local dv; dv=$(driver_meta_version "$drv" || true); [ -n "$dv" ] || dv=unknown
  sysroot_key_usable "$dv" \
    || die "sysroottest: the default driver's METADATA_VERSION is UNKNOWN; this test needs a keyed driver."

  local real; real=$(sysroot_candidates "$dv" | head -1 | cut -f1)
  [ -n "$real" ] \
    || die "sysroottest: no registered sysroot at v$dv — add one to sysroot_registry, or this test has nothing to select."

  local other other_v
  other=$(sysroot_registry | cut -f1 | while read -r p; do
            [ -d "$p" ] || continue
            v=$(sysroot_meta_version "$p" || true)
            [ -n "$v" ] && [ "$v" != "$dv" ] && printf '%s\t%s\n' "$p" "$v" && break
          done)
  other_v=$(printf '%s' "$other" | cut -f2); other=$(printf '%s' "$other" | cut -f1)
  [ -n "$other" ] \
    || die "sysroottest: every registered sysroot is at v$dv; there is no wrong-version entry to prove the filter with."

  # A synthetic sysroot that ANSWERS the version question correctly and is
  # otherwise useless: one real libcore .rmeta, nothing else. Version-matching
  # is therefore satisfied and facts 3/4 cannot be.
  local fake="$T/fake-v$dv"
  mkdir -p "$fake/lib/rustlib/$HOST/lib"
  local realcore; realcore=$(ls "$real/lib/rustlib/$HOST/lib"/libcore-*.rmeta 2>/dev/null | head -1)
  [ -n "$realcore" ] || die "sysroottest: no libcore rmeta under $real"
  cp "$realcore" "$fake/lib/rustlib/$HOST/lib/"
  [ "$(sysroot_meta_version "$fake")" = "$dv" ] \
    || die "sysroottest: the synthetic sysroot did not read back as v$dv — fixture is wrong."

  echo "sysroottest: driver          $drv (v$dv)"
  echo "sysroottest: real v$dv sysroot $real"
  echo "sysroottest: wrong-version    $other (v$other_v)"
  echo "sysroottest: synthetic v$dv   $fake (version byte only — facts 3/4 must fail)"
  echo

  local out rc

  echo "== the version filter selects on the DRIVER's version, nothing else =="
  # Line-EXACT membership. Substring matching is wrong here and quietly so:
  # ".../stage1" is a prefix of ".../stage1.backup-v11-…", so a `case` glob
  # reports the v13 sysroot as present in the v11 candidate list.
  out=$(sysroot_candidates "$dv" | cut -f1)
  printf '%s\n' "$out" | grep -Fxq "$real" \
    && st_ok "candidates(v$dv) include the real v$dv sysroot" \
    || st_bad "candidates(v$dv) include the real v$dv sysroot" "$out"
  printf '%s\n' "$out" | grep -Fxq "$other" \
    && st_bad "candidates(v$dv) EXCLUDE the v$other_v sysroot" "$out" \
    || st_ok "candidates(v$dv) exclude the v$other_v sysroot"
  out=$(sysroot_candidates "$other_v" | cut -f1)
  printf '%s\n' "$out" | grep -Fxq "$real" \
    && st_bad "candidates(v$other_v) EXCLUDE the v$dv sysroot" "$out" \
    || st_ok "candidates(v$other_v) exclude the v$dv sysroot"

  echo
  echo "== a version NOTHING is registered at must REFUSE, not guess =="
  out=$(auto_select_sysroot "$drv" 99 2>&1); rc=$?
  [ $rc -ne 0 ] && st_ok "auto_select(v99) refuses (exit $rc)" || st_bad "auto_select(v99) refuses" "$out"
  [ -z "$AUTO_SYSROOT" ] && st_ok "auto_select(v99) chose NOTHING" || st_bad "auto_select(v99) chose NOTHING" "chose $AUTO_SYSROOT"
  st_want "the refusal names the version it could not match" "METADATA_VERSION 99" "$out"
  st_want "the refusal prints the whole registry"            "$real"              "$out"
  st_want "the refusal names --sysroot"                      "--sysroot"          "$out"
  st_want "the refusal names TRUST_SEAL_COMPILE_SYSROOT"     "TRUST_SEAL_COMPILE_SYSROOT" "$out"

  echo
  echo "== an UNKNOWN driver version must REFUSE, not guess =="
  out=$(auto_select_sysroot "$drv" unknown 2>&1); rc=$?
  [ $rc -ne 0 ] && st_ok "auto_select(unknown) refuses (exit $rc)" || st_bad "auto_select(unknown) refuses" "$out"
  [ -z "$AUTO_SYSROOT" ] && st_ok "auto_select(unknown) chose NOTHING" || st_bad "auto_select(unknown) chose NOTHING" "chose $AUTO_SYSROOT"
  st_want "the refusal says the KEY is unknown" "METADATA_VERSION IS UNKNOWN" "$out"

  echo
  echo "== a version-MATCHING but BROKEN sysroot must be rejected by facts 3/4 =="
  out=$(TRUST_SEAL_SYSROOT_REGISTRY="$fake:$real" auto_select_sysroot "$drv" "$dv" 2>&1); rc=$?
  # AUTO_SYSROOT is set in a subshell above, so re-run capturing only stderr.
  TRUST_SEAL_SYSROOT_REGISTRY="$fake:$real" auto_select_sysroot "$drv" "$dv" 2>/dev/null
  [ $rc -eq 0 ] && st_ok "auto_select skips the broken one and still succeeds" || st_bad "auto_select skips the broken one" "$out"
  [ "$AUTO_SYSROOT" = "$real" ] && st_ok "it chose the REAL sysroot, not the fixture" \
    || st_bad "it chose the REAL sysroot, not the fixture" "chose '$AUTO_SYSROOT'"
  st_want "and it SAID it rejected the fixture" "rejected $fake" "$out"

  echo
  echo "== mutation: each mechanism removed must turn a refusal into a mispair =="
  # M1 — neuter the version filter. The v99 refusal must become a SELECTION.
  out=$( sysroot_version_matches() { return 0; }
         auto_select_sysroot "$drv" 99 >/dev/null 2>&1 && echo "SELECTED:$AUTO_SYSROOT" || echo "REFUSED" )
  case "$out" in SELECTED:*) st_ok "M1 no version filter: v99 MISPAIRS (${out#SELECTED:})" ;;
                 *) st_bad "M1 no version filter: v99 MISPAIRS" "still $out — the filter is not what refuses" ;; esac
  # M2 — neuter the 4-fact verification. The broken fixture must be chosen.
  out=$( sysroot_facts_34() { return 0; }
         TRUST_SEAL_SYSROOT_REGISTRY="$fake:$real" auto_select_sysroot "$drv" "$dv" >/dev/null 2>&1 \
           && echo "SELECTED:$AUTO_SYSROOT" || echo "REFUSED" )
  [ "$out" = "SELECTED:$fake" ] && st_ok "M2 no 4-fact check: the BROKEN fixture is chosen" \
    || st_bad "M2 no 4-fact check: the BROKEN fixture is chosen" "got $out — facts 3/4 are not what rejects it"
  # M3 — neuter the unknown-key guard. Defence in depth: the candidate filter
  # refuses too, so this must STILL refuse; what changes is the DIAGNOSIS.
  out=$( sysroot_key_usable() { return 0; }
         auto_select_sysroot "$drv" unknown >/dev/null 2>&1 && echo "SELECTED:$AUTO_SYSROOT" || echo "REFUSED" )
  case "$out" in REFUSED) st_ok "M3 no key guard: STILL refuses (the candidate filter is the second line)" ;;
                 *) st_bad "M3 no key guard: STILL refuses" "$out — an unkeyed driver got paired" ;; esac

  echo
  echo "== stated intent is never overridden, and a working default is never moved =="
  RCS_PATH=""; RCS_SOURCE=""
  resolve_compile_sysroot "$drv" "$fake" >/dev/null 2>&1
  [ "$RCS_PATH" = "$(abspath "$fake")" ] && st_want "--sysroot wins even when it is broken" "stated (--sysroot)" "$RCS_SOURCE" \
    || st_bad "--sysroot wins even when it is broken" "got $RCS_PATH [$RCS_SOURCE]"
  RCS_PATH=""; RCS_SOURCE=""
  ( TRUST_SEAL_COMPILE_SYSROOT="$fake"; resolve_compile_sysroot "$drv" "" >/dev/null 2>&1
    [ "$RCS_PATH" = "$(abspath "$fake")" ] && case "$RCS_SOURCE" in *"TRUST_SEAL_COMPILE_SYSROOT"*) exit 0 ;; esac; exit 1 ) \
    && st_ok "TRUST_SEAL_COMPILE_SYSROOT wins over auto-selection" \
    || st_bad "TRUST_SEAL_COMPILE_SYSROOT wins over auto-selection"
  RCS_PATH=""; RCS_SOURCE=""
  resolve_compile_sysroot "$drv" "" >/dev/null 2>&1
  if [ "$(sysroot_meta_version "$STAGE1_SYSROOT" 2>/dev/null)" = "$dv" ]; then
    st_want "a WORKING default is kept, not auto-replaced" "default (" "$RCS_SOURCE"
  else
    st_want "a FAILING default falls to auto-selection"     "auto (registry:" "$RCS_SOURCE"
    [ "$RCS_PATH" = "$real" ] && st_ok "and it landed on the first registered v$dv sysroot" \
      || st_bad "and it landed on the first registered v$dv sysroot" "landed on $RCS_PATH"
  fi
  RCS_PATH=""; RCS_SOURCE=""
  ( TRUST_SEAL_NO_AUTO_SYSROOT=1; resolve_compile_sysroot "$drv" "" >/dev/null 2>&1
    [ "$RCS_PATH" = "$STAGE1_SYSROOT" ] && case "$RCS_SOURCE" in *"TRUST_SEAL_NO_AUTO_SYSROOT"*) exit 0 ;; esac
    case "$RCS_SOURCE" in "default ("*) exit 0 ;; esac; exit 1 ) \
    && st_ok "TRUST_SEAL_NO_AUTO_SYSROOT restores the fail-closed default" \
    || st_bad "TRUST_SEAL_NO_AUTO_SYSROOT restores the fail-closed default"

  echo
  echo "== the relative-path regression stays fixed =="
  out=$(cd "$ROOT" && cmd_sysrootcheck "${drv#$ROOT/}" --sysroot "${real#$ROOT/}" 2>&1); rc=$?
  [ $rc -eq 0 ] && st_ok "sysrootcheck accepts RELATIVE driver and sysroot paths" \
    || st_bad "sysrootcheck accepts RELATIVE driver and sysroot paths" "$out"

  echo
  echo "sysroottest: $ST_PASS ok, $ST_FAIL FAIL"
  [ $ST_FAIL -eq 0 ] || return 1
  echo "sysroottest: OK — auto-selection refuses on an unmatched version, on an"
  echo "sysroottest: unreadable key, and on a version-matching sysroot that does not"
  echo "sysroottest: prove out; and each of those refusals dies when its mechanism does."
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
  cmd_sysrootcheck "$dir" || return 96
  echo "verify OK: $dir (rev $(cat "$dir/REV" 2>/dev/null || echo unknown) [$(cat "$dir/REV_SOURCE" 2>/dev/null || echo pre-REV_SOURCE-seal)])"
  echo "verify   : sysroot $(cat "$dir/SYSROOT" 2>/dev/null || echo "(the wrapper's own — pre-SYSROOT-seal)") [$(cat "$dir/SYSROOT_SOURCE" 2>/dev/null || echo pre-SYSROOT_SOURCE-seal)]"
}

case "${1:-}" in
  seal)     shift; cmd_seal     "$@" ;;
  guard)    shift; cmd_guard    "$@" ;;
  classes)  shift; cmd_classes  "$@" ;;
  selftest) shift; cmd_selftest "$@" ;;
  verify)   shift; cmd_verify   "$@" ;;
  guardtest) shift; cmd_guardtest "$@" ;;
  sysrootcheck) shift; cmd_sysrootcheck "$@" ;;
  sysroots)     shift; cmd_sysroots     "$@" ;;
  sysroottest)  shift; cmd_sysroottest  "$@" ;;
  reverdict)    shift; cmd_reverdict    "$@" ;;
  # The whole header block, however long it grows -- not a hard-coded line
  # range that silently truncates the moment someone documents a new fact.
  -h|--help|"") sed -n '2,/^set -uo pipefail/p' "$0" | sed '$d'; exit 0 ;;
  *) die "unknown subcommand: $1 (seal|guard|classes|selftest|verify|guardtest|sysrootcheck|sysroots|sysroottest|reverdict)" ;;
esac
