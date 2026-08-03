#!/bin/sh
# verify-toolchain.sh — the OUTPUT CONTRACT for a Trust toolchain build.
#
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Copyright 2026 Andrew Yates | License: Apache 2.0
#
# WHY THIS EXISTS
# ---------------
# A `./x.py build --stage 2` completed in 1:00:02 and reported SUCCESS while
# shipping a stage2 bin/ that contained NO `ty`, NO `ay` and NO `clean` — the
# three verification backends. `bootstrap.toml`'s `[build] tools = [...]` had
# omitted them, and `l2_backend_enabled`
# (src/bootstrap/src/core/build_steps/tool.rs:900) treats that list as an
# ALLOWLIST: absent means all, PRESENT MEANS ONLY THESE. So the more specific
# the config got, the less the toolchain could do — silently. Nothing that
# merely COMPILES ever notices a missing prover. The build was green; the
# toolchain could not verify a single obligation.
#
# A build is not "successful" because it exited 0. It is successful when it
# produced the binaries it claims, and each of them RUNS. This script asserts
# exactly that, and is the last step of any build sequence.
#
# The required set below is DERIVED FROM THE REPO, not guessed. Every entry
# carries its own evidence pointer in the EVIDENCE column of the table. It is
# corroborated by an independent authority: bootstrap.py's
# STAGE0_REQUIRED_BINS (src/bootstrap/bootstrap.py:51) is exactly the TIER-2
# surface plus `trustc` — the delta (`trustd`, `ay`, `ty`, `clean`) is the
# stage2-only battery set that a stage0 seed does not carry.
#
# TWO TIERS, AND WHY THE DISTINCTION IS THE WHOLE POINT
# ----------------------------------------------------
#   TIER 1  VERIFICATION FLOOR. trustc + the three backends. These are
#           batteries of the compiler, not user tools. `tools = [...]` must
#           NEVER be able to drop one of these by silent omission. Dropping one
#           requires the separate, explicit `--allow-missing-backend=NAME`, and
#           even then this script prints a loud, greppable `TOOLCHAIN-CANNOT:`
#           line naming the capability that is gone. A narrow build stays
#           possible; a quiet narrow build does not.
#
#   TIER 2  TOOLCHAIN SURFACE. Formatter, linter, docs, analyzer, package
#           driver, compat aliases. Genuinely governed by `extended` + `tools`.
#           Missing is an error by default, waivable with `--allow-missing=NAME`.
#
# Existence is not enough: a zero-byte, truncated, wrong-arch or dylib-starved
# binary is exactly as useless as an absent one and is the failure mode a
# `[ -f ]` test cannot see. So every entry is EXECUTED with a bounded probe
# ladder (`--version`, `-V`, `--help`) and must exit 0 with output on at least
# one rung.
#
# Exit: 0 contract satisfied (possibly degraded-but-declared)
#       1 contract VIOLATED
#       2 usage / environment error (cannot run the check at all)

set -eu

SCRIPT_DIR=$(CDPATH='' cd -- "$(dirname -- "$0")" && pwd)
REPO_ROOT=$(CDPATH='' cd -- "$SCRIPT_DIR/.." && pwd)
SURFACE_LIB="$REPO_ROOT/scripts/lib/trust_toolchain_surface.sh"

PROBE_TIMEOUT=${TRUST_VERIFY_PROBE_TIMEOUT:-30}
ALLOW_MISSING=${TRUST_VERIFY_ALLOW_MISSING:-}
ALLOW_MISSING_BACKEND=${TRUST_VERIFY_ALLOW_MISSING_BACKEND:-}
CHECK_FORBIDDEN=1
CHECK_ALIASES=1
SYSROOT=

EXE=
case "${OS:-}$(uname -s 2>/dev/null || true)" in
    *Windows_NT*|*MINGW*|*MSYS*|*CYGWIN*) EXE=.exe ;;
esac

usage() {
    cat <<'EOF'
Usage: tools/verify-toolchain.sh [SYSROOT|BINDIR] [options]

Asserts that an installed toolchain contains the binaries the build claims to
have produced, and that each of them actually runs.

  SYSROOT|BINDIR            Toolchain root (containing bin/) or the bin/ dir
                            itself. Default: <repo>/build/host/stage2

Options:
  --allow-missing=A,B       Waive TIER-2 surface tools (formatter, linter, ...).
  --allow-missing-backend=A Waive a TIER-1 VERIFICATION FLOOR entry. Deliberately
                            a separate flag: dropping a prover is a different
                            decision from dropping a linter. Always prints a
                            TOOLCHAIN-CANNOT: line naming the lost capability.
  --no-forbidden-check      Skip the stock/retired-name check.
  --no-alias-check          Skip the rustc==trustc / cargo==targo byte-identity check.
  --probe-timeout=SECONDS   Per-binary probe budget (default 30).
  --list                    Print the derived required set with evidence, exit 0.
  -h, --help                This message.

Environment: TRUST_VERIFY_ALLOW_MISSING, TRUST_VERIFY_ALLOW_MISSING_BACKEND,
TRUST_VERIFY_PROBE_TIMEOUT mirror the flags.
EOF
}

# ---------------------------------------------------------------------------
# THE REQUIRED SET.
#
# tier|name|location|capability-if-absent|evidence|gate
#
# tier 1 = VERIFICATION FLOOR (never silently waivable)
# tier 2 = TOOLCHAIN SURFACE  (governed by extended + tools)
#
# `location` is bin or libexec. A libexec entry is existence-checked only —
# see probe_binary() for why.
#
# `gate` is WHICH mechanism decides whether this artifact gets installed, so
# an absence can be explained by its actual cause rather than a guess:
#   compiler  materialize_local_compiler_aliases — unconditional once rustc-main links
#   alias     upstream_compat_bin_for_tool_source — rides along with targo
#   source    presence of the in-tree manifest ONLY; `tools` cannot suppress it
#   l2        l2_backend_enabled(tools, ...) — THE ALLOWLIST TRAP behind failure 6
#   tools     the ordinary extended + `tools` user-tool path
# ---------------------------------------------------------------------------
required_set() {
    cat <<'EOF'
1|trustc|bin|compile anything at all — this is the compiler|compile.rs:2074 materialize_local_compiler_aliases copies rustc-main to bin/trustc unconditionally|compiler
1|ay|bin|discharge ANY native proof obligation; every one silently degrades to `unknown`|tool.rs:828 install_bin(ay); gate default_source_solver_enabled (tool.rs:651) is true whenever first-party/ay/crates/ay/Cargo.toml exists|source
1|ty|bin|discharge temporal / TLA+ obligations; aterm's L0 pre-push gate shells straight out to this binary|tool.rs:858 install_bin(ty); gate l2_backend_enabled(tools,"ty") && first-party/ty/crates/tla-cli/Cargo.toml|l2
1|clean|bin|re-check any CIC certificate or higher-order proof|tool.rs:885 install_bin(clean); gate l2_backend_enabled(tools,"clean") && first-party/clean/crates/clean/Cargo.toml|l2
2|rustc|bin|be selected by tools that spawn `rustc` by name|compile.rs:2070 bindir.join(exe("rustc")); byte-identical same-surface alias of trustc|compiler
2|cargo|bin|be registered by rustup at all — rustup refuses a toolchain with no `cargo` entrypoint|tool.rs:1035 upstream_compat_bin_for_tool_source: the single retained upstream alias|alias
2|targo|bin|drive any package build|tool.rs:785 install_bin(targo)|tools
2|targo-trust|bin|run `targo trust` — the verifier frontend|tool.rs:801 install_bin(targo-trust)|tools
2|trustd|bin|start the coordination daemon `targo trust` spawns on demand|tool.rs:807 install_bin(trustd), unconditional inside the targo-trust block, same-sysroot by design|alias
2|trustdoc|bin|build documentation|tool.rs:929 bins.push(("rustdoc_tool_binary","trustdoc")); gate tool_enabled_for_tool_settings(...,"trustdoc")|tools
2|trustfmt|bin|format sources|tool.rs:999 bins.push(("rustfmt","trustfmt"))|tools
2|targo-fmt|bin|run `targo fmt`|tool.rs:990 bins.push(("cargo-fmt","targo-fmt"))|tools
2|tippy|bin|lint|tool.rs:971 bins.push(("cargo-clippy","tippy"))|tools
2|targo-tippy|bin|run `targo tippy`|tool.rs:972 bins.push(("cargo-clippy","targo-tippy"))|tools
2|tippy-driver|bin|back either Tippy frontend|tool.rs:981 bins.push(("clippy-driver","tippy-driver"))|tools
2|trust-analyzer|bin|serve LSP|tool.rs:1002 bins.push(("rust-analyzer","trust-analyzer")); gate tool_enabled_for_tool_settings(...,"trust-analyzer")|tools
2|trust-analyzer-proc-macro-srv|libexec|expand proc macros for the analyzer|tool.rs:1291 libexec.join(exe("trust-analyzer-proc-macro-srv")); gate restore_rust_analyzer_proc_macro_srv_for_tool_settings (tool.rs:1357)|tools
EOF
}

# In-tree manifest whose presence is the `source`/`l2` availability gate
# (tool.rs:682-684). A missing manifest almost always means an uninitialised or
# drifted first-party/ submodule, not a deleted backend.
source_manifest_for() {
    case "$1" in
        ay)    printf 'first-party/ay/crates/ay/Cargo.toml\n' ;;
        ty)    printf 'first-party/ty/crates/tla-cli/Cargo.toml\n' ;;
        clean) printf 'first-party/clean/crates/clean/Cargo.toml\n' ;;
    esac
}

# Deliberately NOT required: trust-miri / targo-miri. They are the only entries
# built through extended_rustc_tool_is_default_step_for_tool_settings with
# stable=false (tool.rs:1004-1021), and bootstrap.toml's tools list does not
# name them. Absent by design, not by accident.

field() { printf '%s\n' "$1" | cut -d'|' -f"$2"; }

list_required() {
    printf 'DERIVED REQUIRED SET (authority: src/bootstrap/src/core/build_steps/tool.rs,\n'
    printf 'src/bootstrap/src/core/build_steps/compile.rs, bootstrap.toml)\n\n'
    required_set | while IFS= read -r row; do
        [ -n "$row" ] || continue
        printf 'TIER %s  %-30s (%s)\n' \
            "$(field "$row" 1)" "$(field "$row" 2)" "$(field "$row" 3)"
        printf '          evidence: %s\n' "$(field "$row" 5)"
    done
}

# ---------------------------------------------------------------------------
# Bounded execution. A probe that hangs is a failed probe, not a hung gate.
# macOS has no coreutils `timeout`; perl's alarm is the portable stand-in. If
# NEITHER exists we refuse to run rather than quietly probing unbounded —
# quietly-weakened checking is the exact disease this script treats.
# ---------------------------------------------------------------------------
TIMEOUT_KIND=
if command -v timeout >/dev/null 2>&1; then
    TIMEOUT_KIND=timeout
elif command -v gtimeout >/dev/null 2>&1; then
    TIMEOUT_KIND=gtimeout
elif command -v perl >/dev/null 2>&1; then
    TIMEOUT_KIND=perl
fi

run_bounded() {
    _secs=$1
    shift
    case "$TIMEOUT_KIND" in
        timeout)  timeout "$_secs" "$@" ;;
        gtimeout) gtimeout "$_secs" "$@" ;;
        perl)     perl -e 'alarm shift; exec @ARGV or exit 127' "$_secs" "$@" ;;
        *)        return 125 ;;
    esac
}

in_csv_list() {
    _needle=$1
    _hay=$2
    _old_ifs=$IFS
    IFS=', '
    for _item in $_hay; do
        if [ "$_item" = "$_needle" ]; then
            IFS=$_old_ifs
            return 0
        fi
    done
    IFS=$_old_ifs
    return 1
}

# ---------------------------------------------------------------------------
# Probe one installed artifact.
#   0 = present and demonstrably runnable
#   1 = present but broken (zero-byte, not executable, every probe failed)
#   2 = absent
# Prints its own diagnosis.
# ---------------------------------------------------------------------------
probe_binary() {
    _name=$1
    _loc=$2
    _path=$3

    if [ ! -e "$_path" ] && [ ! -L "$_path" ]; then
        printf '  MISSING   %-30s (no such path: %s)\n' "$_name" "$_path"
        return 2
    fi
    if [ -L "$_path" ]; then
        # Bootstrap installs regular files (copy_link hardlinks or copies). A
        # symlink here means something outside the build wrote this tree.
        if [ ! -e "$_path" ]; then
            printf '  BROKEN    %-30s (dangling symlink: %s)\n' "$_name" "$_path"
            return 1
        fi
        printf '  WARN      %-30s (symlink, not a regular installed file)\n' "$_name"
    elif [ ! -f "$_path" ]; then
        printf '  BROKEN    %-30s (not a regular file: %s)\n' "$_name" "$_path"
        return 1
    fi
    if [ ! -s "$_path" ]; then
        printf '  BROKEN    %-30s (ZERO BYTES: %s)\n' "$_name" "$_path"
        return 1
    fi
    if [ ! -x "$_path" ]; then
        printf '  BROKEN    %-30s (not executable: %s)\n' "$_name" "$_path"
        return 1
    fi

    # The proc-macro server speaks a stdio JSON protocol on stdin and has no
    # CLI surface to interrogate; probing it with `--version` would either hang
    # waiting for a message or teach us nothing. It is existence + shape only,
    # and this limit is stated rather than hidden.
    if [ "$_loc" = libexec ]; then
        printf '  OK(shape) %-30s (%s bytes; stdio-protocol server, not CLI-probed)\n' \
            "$_name" "$(wc -c <"$_path" | tr -d ' ')"
        return 0
    fi

    for _probe in --version -V --help; do
        _out=$(run_bounded "$PROBE_TIMEOUT" "$_path" "$_probe" 2>&1) && _rc=0 || _rc=$?
        if [ "$_rc" -eq 125 ]; then
            printf '  ERROR     %-30s (no timeout/gtimeout/perl available to bound the probe)\n' "$_name"
            return 1
        fi
        if [ "$_rc" -eq 0 ] && [ -n "$_out" ]; then
            printf '  OK        %-30s %s -> %s\n' \
                "$_name" "$_probe" "$(printf '%s' "$_out" | head -n 1 | cut -c1-72)"
            return 0
        fi
        _last_rc=$_rc
        _last_out=$_out
    done

    printf '  BROKEN    %-30s (RUNS BUT FAILS: last probe --help exited %s)\n' \
        "$_name" "${_last_rc:-?}"
    if [ -n "${_last_out:-}" ]; then
        printf '            %s\n' "$(printf '%s' "$_last_out" | head -n 2 | cut -c1-100)"
    fi
    return 1
}

# ---------------------------------------------------------------------------
# Diagnose WHY a required entry is absent, in terms of the config that caused
# it. This is the message that would have turned failure 6 from a mystery into
# a one-line fix.
# ---------------------------------------------------------------------------
explain_absence() {
    _name=$1
    _gate=$2
    _toml="$REPO_ROOT/bootstrap.toml"
    _manifest=$(source_manifest_for "$_name")

    case "$_gate" in
        compiler)
            printf '            Not governed by [build] tools. compile.rs materializes this\n'
            printf '            unconditionally once rustc-main links, so its absence means the\n'
            printf '            COMPILER ITSELF was never assembled into this sysroot — the\n'
            printf '            build stopped or was interrupted before Assemble.\n'
            return 0 ;;
        alias)
            printf '            Not independently configurable: it rides along with its\n'
            printf '            canonical tool. Absent here means the step that installs that\n'
            printf '            tool did not run to completion.\n'
            return 0 ;;
    esac

    # source/l2/tools entries: the manifest gate comes first, because a drifted
    # or uninitialised submodule is the likelier cause and reads nothing like a
    # config problem.
    if [ -n "$_manifest" ] && [ ! -f "$REPO_ROOT/$_manifest" ]; then
        printf '            In-tree source manifest is ABSENT: %s\n' "$_manifest"
        printf '            tool.rs:686 verifier_backend_source_present gates on exactly this\n'
        printf '            path, so the backend was never even attempted. This is normally a\n'
        printf '            drifted or uninitialised first-party/ submodule, not a config\n'
        printf '            choice. Check `git submodule status first-party/` before anything else.\n'
        return 0
    fi

    [ -f "$_toml" ] || return 0
    if ! grep -q '^[[:space:]]*tools[[:space:]]*=' "$_toml"; then
        printf '            bootstrap.toml has no [build] tools list, so nothing suppressed\n'
        printf '            this. The build claimed it and did not deliver it.\n'
        return 0
    fi
    if grep -q "\"$_name\"" "$_toml"; then
        printf '            bootstrap.toml DOES name "%s" in [build] tools — the build\n' "$_name"
        printf '            claimed it and did not deliver it. This is a build failure,\n'
        printf '            not a configuration choice.\n'
        return 0
    fi
    printf '            bootstrap.toml has a [build] tools list that does NOT name "%s".\n' "$_name"
    if [ "$_gate" = l2 ]; then
        printf '            THIS IS THE FAILURE-6 TRAP. tool.rs:900 l2_backend_enabled reads\n'
        printf '            that list as an ALLOWLIST (absent = ALL, PRESENT = ONLY THESE), so\n'
        printf '            naming any tool at all silently dropped this verification backend.\n'
        printf '            Add "%s" to [build] tools, or pass --allow-missing-backend=%s\n' "$_name" "$_name"
        printf '            to declare the capability loss out loud.\n'
    elif [ "$_gate" = source ]; then
        printf '            Its gate is source presence, not `tools` (tool.rs:651), so the\n'
        printf '            list did not suppress it — the install step failed.\n'
    fi
}

# ---------------------------------------------------------------------------
# Argument parsing
# ---------------------------------------------------------------------------
while [ $# -gt 0 ]; do
    case "$1" in
        -h|--help) usage; exit 0 ;;
        --list) list_required; exit 0 ;;
        --allow-missing=*) ALLOW_MISSING="${ALLOW_MISSING:+$ALLOW_MISSING,}${1#--allow-missing=}" ;;
        --allow-missing-backend=*)
            ALLOW_MISSING_BACKEND="${ALLOW_MISSING_BACKEND:+$ALLOW_MISSING_BACKEND,}${1#--allow-missing-backend=}" ;;
        --probe-timeout=*) PROBE_TIMEOUT="${1#--probe-timeout=}" ;;
        --no-forbidden-check) CHECK_FORBIDDEN=0 ;;
        --no-alias-check) CHECK_ALIASES=0 ;;
        --) shift; break ;;
        -*) printf 'verify-toolchain: unknown option: %s\n' "$1" >&2; usage >&2; exit 2 ;;
        *)
            if [ -n "$SYSROOT" ]; then
                printf 'verify-toolchain: unexpected extra argument: %s\n' "$1" >&2
                exit 2
            fi
            SYSROOT=$1 ;;
    esac
    shift
done

case "$PROBE_TIMEOUT" in
    ''|*[!0-9]*) printf 'verify-toolchain: --probe-timeout must be a whole number of seconds\n' >&2; exit 2 ;;
esac

[ -n "$SYSROOT" ] || SYSROOT="$REPO_ROOT/build/host/stage2"

# Accept either a sysroot or the bin/ dir itself.
if [ -d "$SYSROOT/bin" ]; then
    BIN_DIR="$SYSROOT/bin"
elif [ "$(basename -- "$SYSROOT")" = bin ] && [ -d "$SYSROOT" ]; then
    BIN_DIR="$SYSROOT"
    SYSROOT=$(dirname -- "$SYSROOT")
else
    printf 'verify-toolchain: not a toolchain root (no bin/ directory): %s\n' "$SYSROOT" >&2
    printf 'DETAIL: pass a sysroot such as <repo>/build/host/stage2, or its bin/ directly.\n' >&2
    exit 2
fi
LIBEXEC_DIR="$SYSROOT/libexec"

if [ -z "$TIMEOUT_KIND" ]; then
    printf 'verify-toolchain: no bounded-execution helper found (need timeout, gtimeout or perl).\n' >&2
    printf 'DETAIL: refusing to probe unbounded — a silently weakened check is the failure\n' >&2
    printf '        mode this gate exists to prevent.\n' >&2
    exit 2
fi

# ---------------------------------------------------------------------------
# Run the contract
# ---------------------------------------------------------------------------
printf 'verify-toolchain: %s\n' "$SYSROOT"
printf '  bin:     %s\n' "$BIN_DIR"
printf '  libexec: %s\n' "$LIBEXEC_DIR"
printf '  probes bounded by %s (%ss)\n\n' "$TIMEOUT_KIND" "$PROBE_TIMEOUT"

FAILURES=0
DEGRADED=0
WAIVED=0
CANNOT_FILE=$(mktemp "${TMPDIR:-/tmp}/verify-toolchain.cannot.XXXXXX")
FAIL_FILE=$(mktemp "${TMPDIR:-/tmp}/verify-toolchain.fail.XXXXXX")
trap 'rm -f "$CANNOT_FILE" "$FAIL_FILE"' EXIT INT TERM

for tier in 1 2; do
    if [ "$tier" = 1 ]; then
        printf 'TIER 1 — VERIFICATION FLOOR\n'
    else
        printf '\nTIER 2 — TOOLCHAIN SURFACE\n'
    fi
    required_set | while IFS= read -r row; do
        [ -n "$row" ] || continue
        rtier=$(field "$row" 1)
        [ "$rtier" = "$tier" ] || continue
        name=$(field "$row" 2)
        loc=$(field "$row" 3)
        cap=$(field "$row" 4)
        gate=$(field "$row" 6)

        if [ "$loc" = libexec ]; then
            path="$LIBEXEC_DIR/$name$EXE"
        else
            path="$BIN_DIR/$name$EXE"
        fi

        probe_binary "$name" "$loc" "$path" && status=0 || status=$?
        # Explicit `if`, not `[ ... ] && continue`: dash and bash disagree on
        # whether a failing test at the head of an AND-list trips `set -e`, and
        # a gate that silently stops enumerating after the first fault would be
        # a very on-brand bug for this script to have.
        if [ "$status" -eq 0 ]; then
            continue
        fi

        if [ "$rtier" = 1 ]; then
            waived=0
            if in_csv_list "$name" "$ALLOW_MISSING_BACKEND"; then
                waived=1
            fi
            if [ "$waived" = 1 ] && [ "$status" -eq 2 ]; then
                printf 'TOOLCHAIN-CANNOT: %s absent — this toolchain cannot %s\n' "$name" "$cap" \
                    >>"$CANNOT_FILE"
                printf '            WAIVED by --allow-missing-backend=%s (capability loss recorded)\n' "$name"
                continue
            fi
            if [ "$waived" = 1 ]; then
                printf '            --allow-missing-backend=%s waives ABSENCE, not BREAKAGE.\n' "$name"
                printf '            A backend that is present but does not run is a build defect.\n'
            fi
            if [ "$status" -eq 2 ]; then
                explain_absence "$name" "$gate"
            else
                printf '            Installed but not runnable. No config choice produces this;\n'
                printf '            it is a defective artifact (link failure, truncated copy,\n'
                printf '            wrong architecture, missing sibling dylib).\n'
            fi
            printf 'REQUIRED: %s (tier 1) — toolchain cannot %s\n' "$name" "$cap" >>"$FAIL_FILE"
            continue
        fi

        if in_csv_list "$name" "$ALLOW_MISSING" && [ "$status" -eq 2 ]; then
            printf '            WAIVED by --allow-missing=%s\n' "$name"
            printf 'WAIVED: %s\n' "$name" >>"$CANNOT_FILE"
            continue
        fi
        if [ "$status" -eq 2 ]; then
            explain_absence "$name" "$gate"
        else
            printf '            Installed but not runnable — a defective artifact, not a\n'
            printf '            configuration choice. --allow-missing waives ABSENCE only.\n'
        fi
        printf 'REQUIRED: %s (tier 2) — toolchain cannot %s\n' "$name" "$cap" >>"$FAIL_FILE"
    done
done

# The alias pairs are same-surface copies. A stale or divergent `rustc` is a
# real and silent failure: tooling that spawns `rustc` by name gets a different
# compiler than `trustc`.
if [ -f "$SURFACE_LIB" ]; then
    # Single source: the repo already owns this inventory and
    # scripts/check_toolchain_coherence.py enforces that it stays coherent with
    # bootstrap.py. Re-listing forbidden names here would create exactly the
    # duplicate-that-drifts this repo has been bitten by before.
    # shellcheck source=/dev/null
    . "$SURFACE_LIB"
else
    printf '\nNOTE: %s not found — alias and forbidden-name checks skipped.\n' "$SURFACE_LIB"
    CHECK_ALIASES=0
    CHECK_FORBIDDEN=0
fi

# The alias check canonicalizes paths through the shared library, which needs a
# Python 3. Say so rather than reporting a false BROKEN.
if [ "$CHECK_ALIASES" = 1 ] \
    && ! command -v "${TRUST_TOOLCHAIN_PYTHON3:-python3}" >/dev/null 2>&1; then
    printf '\nNOTE: no python3 — same-surface alias check skipped (existence/run checks stand).\n'
    CHECK_ALIASES=0
fi

if [ "$CHECK_ALIASES" = 1 ]; then
    printf '\nSAME-SURFACE ALIASES\n'
    for pair in 'trustc rustc' 'targo cargo'; do
        # shellcheck disable=SC2086
        set -- $pair
        if err=$(trust_toolchain_alias_pair_error "$BIN_DIR" "$1" "$2"); then
            printf '  BROKEN    %-30s %s\n' "$2" "$err"
            printf 'ALIAS: %s is not a same-surface copy of %s\n' "$2" "$1" >>"$FAIL_FILE"
        else
            printf '  OK        %-30s byte-identical to %s\n' "$2" "$1"
        fi
    done
fi

if [ "$CHECK_FORBIDDEN" = 1 ]; then
    printf '\nFORBIDDEN STOCK / RETIRED NAMES\n'
    if err=$(trust_toolchain_forbidden_entry_error "$BIN_DIR"); then
        printf '  PRESENT   %s\n' "$err"
        printf 'FORBIDDEN: %s\n' "$err" >>"$FAIL_FILE"
    else
        printf '  OK        no forbidden entrypoint present\n'
    fi
fi

# ---------------------------------------------------------------------------
# Verdict
# ---------------------------------------------------------------------------
# Count with wc, not `grep -c`: grep exits 1 on no-match, which under `set -e`
# either kills the script or (with a `|| printf 0` guard) concatenates grep's
# own "0" with the fallback "0" and yields the non-numeric string "00".
FAILURES=$(wc -l <"$FAIL_FILE" | tr -d ' ')
DEGRADED=$(sed -n '/^TOOLCHAIN-CANNOT:/p' "$CANNOT_FILE" | wc -l | tr -d ' ')
WAIVED=$(sed -n '/^WAIVED:/p' "$CANNOT_FILE" | wc -l | tr -d ' ')

printf '\n'
if [ "$DEGRADED" -gt 0 ]; then
    printf '================= DEGRADED TOOLCHAIN =================\n'
    grep '^TOOLCHAIN-CANNOT:' "$CANNOT_FILE"
    printf 'These losses were DECLARED. Nothing above is a surprise, and\n'
    printf 'nothing above is silent. Do not treat this sysroot as able to\n'
    printf 'discharge the obligations named.\n'
    printf '======================================================\n\n'
fi
if [ "$WAIVED" -gt 0 ]; then
    printf 'Waived tier-2 surface tools: %s\n\n' "$(sed -n 's/^WAIVED: //p' "$CANNOT_FILE" | tr '\n' ' ')"
fi

if [ "$FAILURES" -gt 0 ]; then
    printf 'OUTPUT CONTRACT VIOLATED — %s required artifact(s) missing or broken:\n' "$FAILURES"
    cat "$FAIL_FILE"
    printf '\nThe build did not produce what it claimed. Do not report success,\n'
    printf 'do not install this sysroot, and do not treat any gate run against\n'
    printf 'it as evidence.\n'
    exit 1
fi

printf 'OUTPUT CONTRACT SATISFIED — every required artifact is present and runs.\n'
exit 0
