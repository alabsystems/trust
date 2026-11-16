#!/usr/bin/env bash
# Exercise the real promotion path with synthetic tools in temporary roots.
# These fixtures test shell orchestration, not compiler or proof correctness.
set -euo pipefail

REPO="$(cd "$(dirname "$0")/../.." && pwd)"
# Keep the scoped lane's selected interpreter across the shell boundary. Direct
# callers use the same supported-version search; an explicit selection is never
# silently replaced. The production sealer's legacy-Python fixtures below keep
# their own isolated PATH and TRUST_TOOLCHAIN_PYTHON3 controls.
if [[ -n "${PYTHON_BIN:-}" ]]; then
    if ! "$PYTHON_BIN" -c 'import sys; sys.exit(0 if sys.version_info >= (3, 11) else 1)' 2>/dev/null; then
        printf 'FAIL: selected test Python requires Python >= 3.11: %s\n' "$PYTHON_BIN" >&2
        exit 1
    fi
else
    PYTHON_BIN=""
    for candidate in python3.14 python3.13 python3.12 python3.11 python3 python; do
        if command -v "$candidate" >/dev/null 2>&1 \
            && "$candidate" -c 'import sys; sys.exit(0 if sys.version_info >= (3, 11) else 1)' 2>/dev/null; then
            PYTHON_BIN="$candidate"
            break
        fi
    done
    if [[ -z "$PYTHON_BIN" ]]; then
        echo 'FAIL: promotion tests require Python >= 3.11' >&2
        exit 1
    fi
fi
# This helper's real Git/normalization controls belong to the same push lane.
"$PYTHON_BIN" -B "$REPO/scripts/tests/freeze_toolchain_sources_test.py"
WORK="$(mktemp -d "${TMPDIR:-/tmp}/promote-toolchain-test.XXXXXX")"
WORK="$(cd "$WORK" && pwd -P)"
trap 'rm -rf "$WORK"' EXIT
fail() { printf 'FAIL: %s\n' "$*" >&2; exit 1; }
# Every case runs fixture tools written for it a moment before, and on a busy
# Mac the first exec of a new file can wait 10-61 s (KNOWN_HAZARDS
# TRUST-KI-1014-3), past the 30 s bound tools/verify-toolchain.sh puts on each
# probe: a fixture trustc's `--version` then exits 142 and a case that is about
# something else fails (TRUST-KI-1014-6; tippy-fails-after-work on 2026-10-14).
# The fixtures answer at once once they run, so the probes here get a bound the
# machine's wait cannot reach. The product's own bound is not changed: the
# verifier's default stays 30 s, and promote-toolchain.sh runs as it is, handing
# the verifier the variable it already reads (TRUST_VERIFY_PROBE_TIMEOUT).
FIXTURE_PROBE_TIMEOUT=600

FIXTURE_REPO="$WORK/repo"
for rel in scripts/promote-toolchain.sh tools/verify-toolchain.sh \
    scripts/qualify_targo_resource.py scripts/build-slot scripts/lib/landing_targo.py \
    scripts/verify_sysroot_libraries.py \
    scripts/lib/trust_toolchain_surface.sh scripts/lib/trust_build_provenance.py \
    scripts/lib/seal_content_identity.py \
    scripts/lib/stage_receipt_provenance.py \
    scripts/prune_seal_symlinks.py \
    scripts/freeze_toolchain_sources.py \
    src/tools/trust-stage0-dist/prepare.py \
    src/tools/trust-stage0-dist/bootstrap_steps.py \
    tests/ui/trust/r1/flip_caller_covered.rs \
    tests/ui/trust/tool_attr_unknown_refused.rs \
    tests/ui/trust/tool_attr_vocabulary_accepted.rs \
    tests/ui/trust/verifier_budget_advisory_verdict.rs \
    tests/ui/trust/verifier_budget_termination.rs \
    tests/ui/trust/ice_trimmed_def_paths_clean_crate.rs \
    tests/ui/trust/instance_hypothesis/requires_dep_elision_cross_crate_run.rs \
    tests/ui/trust/instance_hypothesis/auxiliary/requires_dep_default_policy.rs; do
    mkdir -p "$FIXTURE_REPO/$(dirname "$rel")"
    cp "$REPO/$rel" "$FIXTURE_REPO/$rel"
done
mkdir -p "$FIXTURE_REPO/library" "$FIXTURE_REPO/compiler"
printf 'recorded standard-library source\n' > "$FIXTURE_REPO/library/fixture.rs"
printf 'recorded compiler source\n' > "$FIXTURE_REPO/compiler/fixture.rs"
mkdir -p "$FIXTURE_REPO/crates/trust-bignum/src" "$FIXTURE_REPO/crates/trust-memchr/src" \
    "$FIXTURE_REPO/src/llvm-project/libunwind/src"
cat > "$FIXTURE_REPO/Cargo.toml" <<'TOML'
[workspace.package]
version = "1.0.0"
edition = "2021"
license = "MIT"
authors = ["Source fixture"]
TOML
cat > "$FIXTURE_REPO/crates/trust-bignum/Cargo.toml" <<'TOML'
[package]
name = "trust-bignum"
version.workspace = true
edition.workspace = true
license.workspace = true
authors.workspace = true
[lints]
workspace = true
[dev-dependencies]
clean-kernel.workspace = true
TOML
printf '[package]\nname = "memchr"\nversion = "2.8.3"\nedition = "2021"\n' \
    > "$FIXTURE_REPO/crates/trust-memchr/Cargo.toml"
printf 'recorded bignum source\n' > "$FIXTURE_REPO/crates/trust-bignum/src/lib.rs"
printf 'recorded memchr source\n' > "$FIXTURE_REPO/crates/trust-memchr/src/lib.rs"
printf 'recorded unwind source\n' > "$FIXTURE_REPO/src/llvm-project/libunwind/src/fixture.c"
git -C "$FIXTURE_REPO" init -q
git -C "$FIXTURE_REPO" add .
git -C "$FIXTURE_REPO" -c core.hooksPath=/dev/null -c commit.gpgsign=false \
    -c user.name='Promotion fixture' -c user.email='fixture@example.invalid' \
    commit -qm 'Synthetic promotion fixture'
COMMIT="$(git -C "$FIXTURE_REPO" rev-parse HEAD)"

mkdir -p "$WORK/fake-bin" "$WORK/template/bin" "$WORK/template/libexec" \
    "$WORK/template/lib/rustlib/test-host/lib"
# Preserve the legacy bare Python in the isolated promotion PATH while making
# the suite's actual supported interpreter available under its versioned name.
SOURCE_PYTHON="$("$PYTHON_BIN" -c 'import os, sys; print(os.path.realpath(sys.executable))')"
SOURCE_PYTHON_MINOR="$("$PYTHON_BIN" -c 'import sys; print(sys.version_info.minor)')"
ln -s "$SOURCE_PYTHON" "$WORK/fake-bin/python3.$SOURCE_PYTHON_MINOR"
# Host process state must not affect this synthetic test's isolated roots.
printf '#!/bin/sh\nexit 1\n' > "$WORK/fake-bin/pgrep"
# Inject a fault only in the copied seal, to exercise the second contract gate.
cat > "$WORK/fake-bin/cp" <<'SH'
#!/usr/bin/env bash
set -euo pipefail
/bin/cp "$@"
dest="${!#}"
if [[ "$dest" == "$TEST_SEAL" ]]; then
    case "${TEST_COPY_FAULT:-}" in
        forbidden) ln "$dest/bin/targo-fmt" "$dest/bin/cargo-fmt" ;;
        missing) rm "$dest/libexec/trust-analyzer-proc-macro-srv" ;;
        broken) printf '#!/bin/sh\nexit 1\n' > "$dest/bin/tippy" ;;
        library) rm "$dest/lib/rustlib/test-host/lib/libproc_macro-fixture.rlib" ;;
        rustc-dev) rm "$dest"/lib/rustlib/test-host/lib/librustc_public-*.rmeta ;;
        rustc-dev-link) touch "$dest/rustc-dev-link-failure" ;;
        rustc-dev-run) touch "$dest/rustc-dev-run-failure" ;;
        tippy-start) /bin/cp "$(dirname "$0")/../tippy-driver.panic" "$dest/bin/tippy-driver" ;;
        # Still JSON, and no longer the bytes the candidate carried.
        receipt) printf ' \n' >> "$dest/tool-provenance.json" ;;
        lose-trust-miri) rm "$dest/bin/trust-miri" ;;
    esac
fi
SH
chmod +x "$WORK/fake-bin/pgrep" "$WORK/fake-bin/cp"

# THE SERIAL EXECUTOR. Since 083f70d694 (2026-11-07) every gate starts the
# compiler and the shipped tools through TRUST_TOOLCHAIN_SERIAL_COMMAND, and
# from that commit until 2026-11-12 this suite named none and stopped at its
# first case. This fixture is the executor as far as the sealing script reads
# it: `-- /absolute/program [arguments...]`, the program's own output and exit
# status, and a refusal that starts nothing, exits 75 and names itself in the
# real program's words (crates/trust-resource-controller/src/bin/
# trust-serial-command.rs). It carries no GNU transport and admits nothing; the
# real one is tested by scripts/tests/trust_serial_command_test.py. Its fault
# is a line baked into the file, as the tool fixtures' are, because the
# tool-start gate starts it in an empty environment.
write_serial_command() { # <path> <ok|unadmitted|after-the-noop|refuses-under|refuses-matching|cannot-launch|cannot-launch-then-unadmitted|vanishes-after-the-noop|unexecutable-after-the-noop> [<path prefix | glob over the command line>]
    printf '#!/usr/bin/env bash\nMODE=%s\nUNDER=%q\n' "$2" "${3:-}" > "$1"
    cat >> "$1" <<'SH'
refuse() { printf 'trust-serial-command: refused: %s\n' "$1" >&2; exit 75; }
unadmitted='command requires an already-admitted caller; this launcher grants no CPU/memory'
[[ "${1:-}" == -- && "${2:-}" == /* ]] || refuse 'use -- /absolute/program [arguments...]'
shift
case "$MODE" in
    # A caller that holds no build slot: nothing starts, the no-op included.
    unadmitted) refuse "$unadmitted" ;;
    # The slot is lost once the run is under way: only the no-op starts.
    after-the-noop) [[ "$(basename "$1")" == true ]] || refuse "$unadmitted" ;;
    # ...or later still: nothing under one directory starts.
    refuses-under) [[ "$1" != "$UNDER"/* ]] || refuse "$unadmitted" ;;
    # ...or one command only: a glob over the whole command line.
    refuses-matching) case "$*" in $UNDER) refuse "$unadmitted" ;; esac ;;
    # A program the OS will not start, as the real executor reports it; the no-op starts.
    cannot-launch) case "$*" in $UNDER) refuse 'command launch: No such file or directory (os error 2)' ;; esac ;;
    # The same, and only the first no-op (the question asked before any gate)
    # starts: when the gate asks again, the executor refuses that too.
    cannot-launch-then-unadmitted)
        case "$*" in $UNDER) refuse 'command launch: No such file or directory (os error 2)' ;; esac
        if [[ "$(basename "$1")" == true ]]; then
            [[ ! -e "$0.asked" ]] || refuse "$unadmitted"
            : > "$0.asked"
        fi ;;
    # The file the variable names is gone once the run is under way.
    vanishes-after-the-noop) [[ "$(basename "$1")" != true ]] || rm -f "$0" ;;
    # ...or is still a regular executable file that the OS will not execute:
    # rewritten in place as something that is not a program for this machine.
    unexecutable-after-the-noop)
        [[ "$(basename "$1")" != true ]] \
            || { printf '\177ELF\002\001\001\000\n)\n' > "$0.new"; chmod +x "$0.new"; mv "$0.new" "$0"; } ;;
esac
exec "$@"
SH
    chmod +x "$1"
}
write_serial_command "$WORK/serial-command" ok

cat > "$WORK/template/bin/trustc" <<'SH'
#!/usr/bin/env bash
set -euo pipefail
case "${1:-}" in
    --version|-V|--help)
        printf 'rustc 1.0.0 (%s 2026-09-15) (trustc 1.0.0)\n' "${TEST_COMMIT:0:9}"; exit 0 ;;
    -vV) printf 'commit-hash: %s\nhost: test-host\n' "$TEST_COMMIT"; exit 0 ;;
    # TEST_UI_FAULT=libdir-dies / zhelp-dies: the question fails for the
    # compiler's own reason (the second only once the copy is sealed).
    # TEST_UI_FAULT=zhelp-no-flag: the sealed copy prints its -Z help, exits 0,
    # and the flag is not in it.
    --print)
        [[ "${TEST_UI_FAULT:-}" != libdir-dies || "$*" != '--print target-libdir' ]] \
            || { echo 'fixture: no target libdir' >&2; exit 3; }
        printf '%s/../lib/rustlib/test-host/lib\n' "$(dirname "$0")"; exit 0 ;;
    -Z)
        [[ "${TEST_UI_FAULT:-}" != zhelp-dies || "$0" != */sealed/* ]] \
            || { echo 'fixture: -Z help died' >&2; exit 3; }
        [[ "${TEST_UI_FAULT:-}" != zhelp-no-flag || "$0" != */sealed/* ]] \
            || { printf '    -Z  verbose-internals=val -- fixture: a flag that is not the one asked for\n'; exit 0; }
        printf 'trust-verify\n'; exit 0 ;;
esac
AY_PROBE=0
for arg in "$@"; do
    case "$arg" in
        # TEST_UI_FAULT=ay-probe-dies: the compiler dies building the probe, with no line at all.
        */ay_probe.rs)
            [[ "${TEST_UI_FAULT:-}" != ay-probe-dies ]] || exit 3
            AY_PROBE=1 ;;
        # TEST_UI_FAULT=no-diagnostic: a compiler that dies without an `error`
        # line (killed, or with nothing at all), for the three shapes of row.
        */flip_caller_covered.rs)
            [[ "${TEST_UI_FAULT:-}" != no-diagnostic ]] || { echo 'Killed'; exit 137; }
            echo '1 proved, 0 failed'; exit 0 ;;
        */tool_attr_unknown_refused.rs)
            [[ "${TEST_UI_FAULT:-}" != no-diagnostic ]] || exit 1
            echo 'error: is not a Trust attribute'; exit 1 ;;
        */tool_attr_vocabulary_accepted.rs) echo 'carries #[trust::assume_total]'; exit 0 ;;
        */verifier_budget_advisory_verdict.rs)
            echo 'warning: Trust verification exceeded its per-function budget'; exit 0 ;;
        */verifier_budget_termination.rs)
            echo 'error: Trust verification exceeded its per-function budget'; exit 1 ;;
        */ice_trimmed_def_paths_clean_crate.rs) exit 0 ;;
        # B1's run-fail rows and their aux crate. The aux build leaves the rlib
        # the real compiler would; the test's build finds it on a -L path or
        # fails as rustc does, then leaves a binary that behaves as
        # TEST_B1_PROBE says: `panic` (main's behaviour), `elided` (store trust
        # 9192's: `0 0`, exit 0), `divide` (a panic the test does not assert),
        # `dies` (exit 3, one line on stderr, no stdout), `silent` (exit 3 only).
        */auxiliary/requires_dep_default_policy.rs)
            [[ "${TEST_UI_FAULT:-}" != no-diagnostic ]] || exit 1
            [[ "${TEST_B1_PROBE:-panic}" != aux-fails ]] \
                || { echo 'error: synthetic aux build failure'; exit 1; }
            out=''; previous=''
            for probe_arg in "$@"; do
                [[ "$previous" == --out-dir ]] && out="$probe_arg"
                previous="$probe_arg"
            done
            printf 'synthetic rlib\n' > "$out/librequires_dep_default_policy.rlib"
            exit 0 ;;
        */requires_dep_elision_cross_crate_run.rs)
            out=''; found=0; previous=''
            for probe_arg in "$@"; do
                [[ "$previous" == --out-dir ]] && out="$probe_arg"
                [[ "$previous" == -L && -f "$probe_arg/librequires_dep_default_policy.rlib" ]] && found=1
                previous="$probe_arg"
            done
            [[ "$found" -eq 1 ]] \
                || { echo "error[E0463]: can't find crate for \`requires_dep_default_policy\`"; exit 1; }
            case "${TEST_B1_PROBE:-panic}" in
                elided) printf '#!/bin/sh\necho "0 0"\n' ;;
                divide) printf '#!/bin/sh\necho "attempt to divide by zero" >&2\nexit 101\n' ;;
                dies) printf '#!/bin/sh\necho "fixture: died before main" >&2\nexit 3\n' ;;
                silent) printf '#!/bin/sh\nexit 3\n' ;;
                mute) printf '#!/bin/sh\nexit 101\n' ;;
                *) printf '#!/bin/sh\necho "attempt to add with overflow" >&2\nexit 101\n' ;;
            esac > "$out/requires_dep_elision_cross_crate_run"
            [[ "${TEST_B1_PROBE:-panic}" == not-executable ]] || chmod +x "$out/requires_dep_elision_cross_crate_run"
            exit 0 ;;
        # rustc-dev probe: reads the closure from the --sysroot it is given,
        # as the real compiler does, and records which sysroot that was so the
        # test can tell a probe of the seal from a probe of the build tree.
        */rustc_dev_probe.rs)
            sysroot="" out="" crate_type="" emit="" probe_rpath=0
            previous=""
            for probe_arg in "$@"; do
                [[ "$previous" == --sysroot ]] && sysroot="$probe_arg"
                [[ "$previous" == -o ]] && out="$probe_arg"
                [[ "$previous" == --crate-type ]] && crate_type="$probe_arg"
                [[ "$previous" == -C && "$probe_arg" == rpath=yes ]] && probe_rpath=1
                case "$probe_arg" in --emit=*) emit="${probe_arg#--emit=}" ;; esac
                previous="$probe_arg"
            done
            [[ -n "$sysroot" ]] || { echo 'error: rustc-dev probe ran without --sysroot' >&2; exit 1; }
            printf '%s\n' "$(cd "$sysroot" && pwd -P)" >> "${TEST_PROBE_LOG:-/dev/null}"
            available=0
            for rmeta in "$sysroot"/lib/rustlib/test-host/lib/librustc_public-*.rmeta; do
                [[ -e "$rmeta" ]] && available=1
            done
            [[ "$available" -eq 1 ]] \
                || { echo "error[E0463]: can't find crate for \`rustc_public\`" >&2; exit 1; }
            [[ "$crate_type" == bin && "$emit" == link && -n "$out" && "$probe_rpath" == 1 ]] \
                || { echo 'error: rustc-dev probe did not request an executable link' >&2; exit 1; }
            [[ -z "${LIBRARY_PATH:-}${LD_LIBRARY_PATH:-}${DYLD_LIBRARY_PATH:-}" ]] \
                || { echo 'error: native probe inherited a foreign library overlay' >&2; exit 1; }
            [[ ! -f "$sysroot/rustc-dev-link-failure" ]] \
                || { echo "ld: library 'Polly' not found" >&2; exit 1; }
            case "${TEST_RUSTC_DEV_LINK:-ok}" in
                fail) echo "ld: library 'Polly' not found" >&2; exit 1 ;;
                no-output) exit 0 ;;
            esac
            {
                printf '#!/usr/bin/env bash\nset -euo pipefail\n'
                printf 'printf "%%s\\n" %q >> "${TEST_PROBE_RUN_LOG:-/dev/null}"\n' "$sysroot"
                printf '[[ ! -f %q ]] || { echo "sealed native loader failure" >&2; exit 127; }\n' "$sysroot/rustc-dev-run-failure"
                printf '[[ -z "${LD_LIBRARY_PATH:-}${DYLD_LIBRARY_PATH:-}" ]] || { echo "foreign runtime overlay" >&2; exit 127; }\n'
                printf 'case "${TEST_RUSTC_DEV_RUN:-ok}" in\n'
                printf 'fail) echo "native fixture loader failure" >&2; exit 127 ;;\n'
                printf 'no-marker) exit 0 ;;\nesac\n'
                printf 'echo "trust-rustc-dev-native-link-probe: ok"\n'
            } > "$out"
            [[ "${TEST_RUSTC_DEV_LINK:-ok}" == not-executable ]] || chmod +x "$out"
            exit 0 ;;
    esac
done
while [[ $# -gt 0 ]]; do
    if [[ "$1" == -o ]]; then
        if [[ "$AY_PROBE" -eq 1 ]]; then
            # The AY-admission probe: answers as the sealed driver's rule would.
            cat > "$2" <<'PROBE'
#!/bin/sh
case "${TEST_AY_VERDICT:-admitted}" in
    admitted) printf 'ADMITTED %s\n' "$(shasum -a 256 "$1" | awk '{print $1}')" ;;
    dies) echo 'fixture: the probe could not load the sealed driver' >&2; exit 127 ;;
    *) printf 'REFUSED [TCG-AY-IDENTITY-MISMATCH] %s (fixture)\n' "$1" ;;
esac
PROBE
        elif [[ "${TEST_UI_FAULT:-}" == hello-dies && "$2" == */h ]]; then
            printf '#!/bin/sh\necho "fixture: hello died" >&2\nexit 9\n' > "$2"
        elif [[ "${TEST_UI_FAULT:-}" == hello-exits-3 && "$2" == */h ]]; then
            printf '#!/bin/sh\nprintf "ok\\n"\nexit 3\n' > "$2"
        elif [[ "${TEST_UI_FAULT:-}" == hello-does-not-compile && "$2" == */h ]]; then
            # The hello world does not compile, for the compiler's own reason.
            echo 'error: fixture: hello does not compile' >&2; exit 1
        else
            printf '#!/bin/sh\nprintf "ok\\n"\n' > "$2"
        fi
        chmod +x "$2"
        exit 0
    fi
    shift
done
exit 2
SH
chmod +x "$WORK/template/bin/trustc"
cp "$WORK/template/bin/trustc" "$WORK/template/bin/rustc"
for tool in ay ty clean cargo targo targo-trust trustd trustdoc rustdoc \
    trustfmt targo-fmt tippy targo-tippy tippy-driver trust-analyzer; do
    printf '#!/bin/sh\nprintf "synthetic tool fixture\\n"\n' > "$WORK/template/bin/$tool"
    chmod +x "$WORK/template/bin/$tool"
done
# Trust tools with a stock ancestor name themselves in --version, as the real
# ones do; the output contract refuses one that does not.
for brand in trustdoc:'rustc 1.0.0 (fixture) (trustdoc 1.0.0)' \
    rustdoc:'rustc 1.0.0 (fixture) (trustdoc 1.0.0)' \
    trustfmt:'trustfmt 1.0.0-fixture' targo-fmt:'trustfmt 1.0.0-fixture' \
    tippy:'tippy 1.0.0-fixture' targo-tippy:'tippy 1.0.0-fixture' \
    tippy-driver:'tippy 1.0.0-fixture' trust-analyzer:'trust-analyzer 1.0.0-fixture'; do
    printf '#!/bin/sh\nprintf "%s\\n"\n' "${brand#*:}" > "$WORK/template/bin/${brand%%:*}"
done
# The installed doctor is a separate, mandatory admission gate. Version/help
# probes still behave like ordinary tools; only the exact doctor command emits
# its machine-readable readiness result. Keep the cargo compatibility bytes.
cat > "$WORK/template/bin/targo" <<'SH'
#!/usr/bin/env bash
set -euo pipefail
if [[ "${1:-}" == --resource-capabilities ]]; then
    printf '{"version":3,"cpu_workers":false,"supports_invocation":false}\n'
elif [[ "$*" == 'trust doctor --format json' ]]; then
    case "${TEST_DOCTOR_STATE:-ready}" in
        ready) printf '{"ready":true}\n' ;;
        rejected) printf '{"ready":false,"status":"synthetic refusal"}\n' ;;
        malformed) printf 'not JSON\n' ;;
        failed) exit 1 ;;
        ready-but-fails) printf '{"ready":true}\n'; echo 'doctor: synthetic late failure' >&2; exit 3 ;;
    esac
else
    printf 'targo 1.0.0-fixture\n'
fi
SH
chmod +x "$WORK/template/bin/targo"
cp "$WORK/template/bin/targo" "$WORK/template/bin/cargo"

# The tool-start gate (promote steps 1f and 6, and --gate-only) makes every
# compiler-built tool do a piece of real work in an EMPTY environment, so these
# fixtures answer its rows the way the real tools do and take their fault from
# a line baked into the file, not from a TEST_* variable. Every other
# invocation still prints the banner the output contract reads.
write_tippy_driver() { # <path> <ok|panic|no-lint|no-work|fail-after-work>
    printf '#!/bin/sh\nMODE=%s\n' "$2" > "$1"
    cat >> "$1" <<'SH'
case "${1:-}" in --version|-V|--help|'') printf 'tippy 1.0.0-fixture\n'; exit 0 ;; esac
out=''; crate=''; src=''; previous=''
for arg in "$@"; do
    case "$previous" in --out-dir) out="$arg" ;; --crate-name) crate="$arg" ;; esac
    previous="$arg"; src="$arg"
done
[ -n "$out" ] && [ -n "$crate" ] && [ -f "$src" ] || { printf 'tippy 1.0.0-fixture\n'; exit 0; }
if [ "$MODE" = panic ]; then
    # The measured defect, verbatim: the banner above still answers.
    printf "\nthread 'rustc' (1) panicked at /rustc-dev/fixture/compiler/rustc_span/src/symbol.rs:3049:13:\n" >&2
    printf 'duplicate symbols in the rustc symbol list and the extra symbols added by the driver: [[66, 105, 110, 97, 114, 121, 72, 101, 97, 112], [86, 101, 99, 68, 101, 113, 117, 101]]\n' >&2
    exit 101
fi
if [ "$MODE" != no-lint ] && grep -q 'return 1;' "$src"; then
    printf 'error: unneeded `return` statement\n --> %s:2:5\n' "$src" >&2
    exit 1
fi
[ "$MODE" = no-work ] || printf 'synthetic metadata\n' > "$out/lib$crate.rmeta"
[ "$MODE" != fail-after-work ] || exit 3
exit 0
SH
    chmod +x "$1"
}
write_tippy_driver "$WORK/template/bin/tippy-driver" ok
write_tippy_driver "$WORK/tippy-driver.panic" panic
# The frontend runs its SIBLING driver on the package, as the real one does,
# and reports a driver failure the way Cargo does: exit 101, whatever the cause.
# `plain` is the frontend the lint row through the frontend exists for: it hands
# the package to a compiler that is not the linting driver, and the build finishes.
write_tippy_frontend() { # <path> <ok|plain>
    printf '#!/bin/sh\nMODE=%s\n' "$2" > "$1"
    cat >> "$1" <<'SH'
if [ "$*" = '--unverified --offline -- -D warnings' ] && [ -f Cargo.toml ]; then
    mkdir -p "$CARGO_TARGET_DIR"
    if [ "$MODE" = plain ]; then
        printf 'synthetic metadata\n' > "$CARGO_TARGET_DIR/libstart_probe.rmeta"
        printf '    Finished `dev` profile [unoptimized + debuginfo] target(s) in 0.00s\n' >&2
        exit 0
    fi
    if "$(dirname "$0")/tippy-driver" --edition 2021 --crate-type lib --crate-name start_probe \
        --emit=metadata -D warnings --out-dir "$CARGO_TARGET_DIR" src/lib.rs; then
        printf '    Finished `dev` profile [unoptimized + debuginfo] target(s) in 0.00s\n' >&2
        exit 0
    fi
    printf 'error: could not compile `start_probe` (lib)\n' >&2
    exit 101
fi
printf 'tippy 1.0.0-fixture\n'
SH
    chmod +x "$1"
}
write_tippy_frontend "$WORK/template/bin/tippy" ok
# A tool that answers EVERY invocation with its banner and exit 0. The output
# contract reads only that banner, so such a tool passes it; what refuses it is
# the witness of its tool-start row: a line only the work prints, or a file only
# the work leaves.
write_idle_tool() { # <path> <banner>
    printf '#!/bin/sh\nprintf "%%s\\n" "%s"\nexit 0\n' "$2" > "$1"
    chmod +x "$1"
}
cat > "$WORK/template/bin/trustdoc" <<'SH'
#!/bin/sh
out=''; crate=''; src=''; previous=''
for arg in "$@"; do
    case "$previous" in -o) out="$arg" ;; --crate-name) crate="$arg" ;; esac
    previous="$arg"; src="$arg"
done
if [ -n "$out" ] && [ -n "$crate" ] && [ -f "$src" ]; then
    mkdir -p "$out/$crate" && printf '<html>synthetic documentation</html>\n' > "$out/$crate/index.html"
    exit 0
fi
printf 'rustc 1.0.0 (fixture) (trustdoc 1.0.0)\n'
SH
cp "$WORK/template/bin/trustdoc" "$WORK/template/bin/rustdoc"
cat > "$WORK/template/bin/trustfmt" <<'SH'
#!/bin/sh
if [ "${3:-}" = --emit ] && [ "${4:-}" = stdout ] && [ -f "${5:-}" ]; then
    printf '%s:\n\npub fn add(a: u8, b: u8) -> u8 {\n    a.wrapping_add(b)\n}\n' "$5"
    exit 0
fi
printf 'trustfmt 1.0.0-fixture\n'
SH
write_trust_miri() { # <path> <ok|panic>: the one tool the output contract lets a toolchain omit
    printf '#!/bin/sh\nMODE=%s\n' "$2" > "$1"
    cat >> "$1" <<'SH'
case "${1:-}" in --version|-V|--help|'') printf 'trust-miri 1.0.0-fixture\n'; exit 0 ;; esac
# `MIRI_BE_RUSTC=host` is a plain compiler with no extra symbols; the gate must not use it.
[ "${MIRI_BE_RUSTC:-}" = target ] || { printf 'error: started without MIRI_BE_RUSTC=target\n' >&2; exit 1; }
[ "$MODE" = ok ] || { printf "\nthread 'rustc' (1) panicked at symbol.rs:3049:13:\nduplicate symbols in the rustc symbol list and the extra symbols added by the driver: [[115]]\n" >&2; exit 101; }
out=''; crate=''; previous=''
for arg in "$@"; do
    case "$previous" in --out-dir) out="$arg" ;; --crate-name) crate="$arg" ;; esac
    previous="$arg"
done
printf 'synthetic metadata\n' > "$out/lib$crate.rmeta"
SH
    chmod +x "$1"
}
cp "$WORK/template/bin/trust-analyzer" "$WORK/template/libexec/trust-analyzer-proc-macro-srv"
printf 'synthetic stdlib\n' > "$WORK/template/lib/rustlib/test-host/lib/libstd-fixture.rlib"
for crate in core alloc compiler_builtins test proc_macro trust_bignum; do
    printf 'synthetic library; no metadata semantics claimed\n' \
        > "$WORK/template/lib/rustlib/test-host/lib/lib$crate-fixture.rlib"
done
printf 'synthetic private driver\n' > "$WORK/template/lib/librustc_driver-fixture.dylib"
printf 'synthetic rustc-dev metadata\n' > "$WORK/template/lib/rustlib/test-host/lib/librustc_public-fixture.rmeta"

CASE_COUNT=0
CASES_NOT_RUN=0
new_case() {
    CASE_COUNT=$((CASE_COUNT + 1))
    CASE="$WORK/$1"
    SRC="$CASE/build/test-host/stage2"
    SEAL="$CASE/sealed/trust-${COMMIT:0:8}"
    PRIVATE="$CASE/build/test-host/rustc-private-sysroots/fixture-key"
    mkdir -p "$(dirname "$SRC")" "$PRIVATE/test-host" "$CASE/rustup/toolchains"
    cp -R "$WORK/template" "$SRC"
    cp "$SRC/lib/librustc_driver-fixture.dylib" "$PRIVATE/test-host/"
    printf '%s\n' "$COMMIT" > "$PRIVATE/.rustc-commit-hash"
    ln -s "$CASE/previous" "$CASE/rustup/toolchains/trust"
}

run_promotion() {
    local lock_command=()
    if [[ -n "${TEST_LOCK_PATH:-}" ]]; then
        lock_command=("$SOURCE_PYTHON" -c '
import fcntl, subprocess, sys
with open(sys.argv[1], "a") as lock:
    fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
    sys.exit(subprocess.call(sys.argv[2:]))
' "$TEST_LOCK_PATH")
    fi
    # TEST_SERIAL_UNSET=1: the variable is absent, not empty (the measured case).
    local serial=(TRUST_TOOLCHAIN_SERIAL_COMMAND="${TEST_SERIAL_COMMAND-$WORK/serial-command}")
    [[ "${TEST_SERIAL_UNSET:-0}" -eq 0 ]] || serial=()
    env -i HOME="$CASE/home" TMPDIR="${TEST_TMPDIR:-$WORK}" \
        PATH="$WORK/fake-bin:/usr/bin:/bin:/usr/sbin:/sbin" \
        TEST_COMMIT="$COMMIT" TEST_SEAL="$SEAL" TEST_COPY_FAULT="${1:-}" \
        TEST_DOCTOR_STATE="${TEST_DOCTOR_STATE:-ready}" \
        TEST_AY_VERDICT="${TEST_AY_VERDICT:-admitted}" \
        TEST_B1_PROBE="${TEST_B1_PROBE:-panic}" \
        TEST_RUSTC_DEV_LINK="${TEST_RUSTC_DEV_LINK:-ok}" \
        TEST_RUSTC_DEV_RUN="${TEST_RUSTC_DEV_RUN:-ok}" \
        TEST_PROBE_LOG="$CASE/probe-sysroots" \
        TEST_PROBE_RUN_LOG="$CASE/probe-run-sysroots" \
        LIBRARY_PATH="${LIBRARY_PATH:-}" LD_LIBRARY_PATH="${LD_LIBRARY_PATH:-}" \
        DYLD_LIBRARY_PATH="${DYLD_LIBRARY_PATH:-}" \
        TRUST_TOOLCHAIN_HOME="${TEST_TOOLCHAIN_HOME:-$CASE/sealed}" RUSTUP_HOME="$CASE/rustup" \
        ${serial[@]+"${serial[@]}"} \
        TEST_UI_FAULT="${TEST_UI_FAULT:-}" \
        TRUST_BUILD_PROVENANCE_DIR="$CASE/build" \
        TRUST_REQUIRE_BUILD_PROVENANCE="${TEST_REQUIRE_PROV:-0}" \
        TRUST_TOOLCHAIN_PYTHON3="${TEST_SURFACE_PYTHON:-python3}" \
        TRUST_VERIFY_ALLOW_MISSING='trustd,trustfmt,trust-analyzer-proc-macro-srv' \
        TRUST_VERIFY_ALLOW_MISSING_BACKEND=clean \
        TRUST_VERIFY_PROBE_TIMEOUT="$FIXTURE_PROBE_TIMEOUT" \
        ${lock_command[@]+"${lock_command[@]}"} bash "$FIXTURE_REPO/scripts/promote-toolchain.sh" \
        ${PROMOTE_OPTS+"${PROMOTE_OPTS[@]}"} "$SRC" ${PROMOTE_AFTER+"${PROMOTE_AFTER[@]}"} > "$CASE/output" 2>&1
}

assert_refusal() {
    local gate="$1" fault="${2:-}"
    if run_promotion "$fault"; then fail "$(basename "$CASE") was promoted"; fi
    grep -qF "$gate violates the complete Trust toolchain output contract" "$CASE/output" \
        || { cat "$CASE/output" >&2; fail "unexpected refusal for $(basename "$CASE")"; }
    [[ "$(readlink "$CASE/rustup/toolchains/trust")" == "$CASE/previous" ]] \
        || fail 'refusal moved the channel'
    [[ ! -e "$CASE/sealed/trust-current" && ! -L "$CASE/sealed/trust-current" ]] \
        || fail 'refusal created trust-current'
    if [[ "$gate" == stage2 ]]; then
        [[ ! -e "$CASE/sealed" ]] || fail 'invalid input was copied'
    fi
}

new_case complete
run_promotion || { cat "$CASE/output" >&2; fail 'complete canonical fixture was refused'; }
# A promotion that finishes keeps nothing: the scratch directory of step 6 is
# deleted and no line says one was kept. This is the suite's first run, so
# TMPDIR ($WORK) holds no directory that a refused run kept on purpose.
! grep -qF 'is kept in' "$CASE/output" \
    || { cat "$CASE/output" >&2; fail 'a promotion that finished said it kept its scratch directory'; }
[[ -z "$(find "$WORK" -maxdepth 1 -name 'tmp.*')" ]] \
    || { find "$WORK" -maxdepth 1 -name 'tmp.*' >&2; fail 'a promotion that finished left a scratch file or directory in TMPDIR'; }
# The fixtures' bound reached the verifier, and the verifier's own default is
# still the 30 s the product runs with.
grep -Eq "^  probes bounded by [a-z]+ \(${FIXTURE_PROBE_TIMEOUT}s\)$" "$CASE/output" \
    || { cat "$CASE/output" >&2; fail 'the fixture probe bound did not reach the verifier'; }
grep -qxF 'PROBE_TIMEOUT=${TRUST_VERIFY_PROBE_TIMEOUT:-30}' "$FIXTURE_REPO/tools/verify-toolchain.sh" \
    || fail "the verifier's default probe bound is no longer 30 s"
[[ "$(readlink "$CASE/rustup/toolchains/trust")" == "$SEAL" ]] || fail 'channel did not select seal'
[[ "$(readlink "$CASE/sealed/trust-current")" == "$SEAL" ]] || fail 'trust-current did not select seal'
for pair in trustc:rustc targo:cargo trustdoc:rustdoc; do
    cmp "$SEAL/bin/${pair%:*}" "$SEAL/bin/${pair#*:}" || fail "lost alias pair $pair"
done
for forbidden in cargo-fmt cargo-clippy; do
    [[ ! -e "$SEAL/bin/$forbidden" && ! -L "$SEAL/bin/$forbidden" ]] \
        || fail "promotion manufactured $forbidden"
done
cmp "$PRIVATE/test-host/librustc_driver-fixture.dylib" \
    "$CASE/sealed/rustc-private-sysroots/fixture-key/test-host/librustc_driver-fixture.dylib"
grep -q '^private_sysroot=fixture-key$' "$SEAL/PROVENANCE" || fail 'private sysroot was not recorded'
# The private sysroot is outside the seal, so it carries its own content identity.
"$PYTHON_BIN" -B "$REPO/scripts/lib/seal_content_identity.py" --prefix private_sysroot_content \
    "$CASE/sealed/rustc-private-sysroots/fixture-key" > "$CASE/private-identity"
grep -qx 'private_sysroot_content_scope=seal-content-v1' "$CASE/private-identity" \
    || fail 'the private sysroot identity names no scope'
while IFS= read -r line; do
    grep -qxF "$line" "$SEAL/PROVENANCE" || fail "PROVENANCE does not carry the private sysroot's $line"
done < "$CASE/private-identity"
# The rustc-dev probe asks the candidate before the copy, then the seal itself.
[[ "$(cat "$CASE/probe-sysroots")" == "$(cd "$SRC" && pwd -P)"$'\n'"$(cd "$SEAL" && pwd -P)" ]] \
    || { cat "$CASE/probe-sysroots" >&2; fail 'rustc-dev probe did not read the candidate and then the seal'; }
[[ "$(cat "$CASE/probe-run-sysroots")" == "$(cd "$SRC" && pwd -P)"$'\n'"$(cd "$SEAL" && pwd -P)" ]] \
    || { cat "$CASE/probe-run-sysroots" >&2; fail 'rustc-dev executable did not run from both candidate and seal'; }
[[ ! -e "$SEAL/SEED-MINT" ]] && ! grep -q '^seed_mint_sha256=' "$SEAL/PROVENANCE" \
    || fail 'a stage2 no pack cut minted was sealed with a pack-cut receipt'
# The tool-start gate asks the candidate before the copy, then the seal itself;
# a tool the output contract lets a toolchain omit is reported, never counted.
[[ "$(grep -F '==> tool-start gate: 7 starts through ' "$CASE/output")" == \
    "==> tool-start gate: 7 starts through $(cd "$SRC" && pwd -P)/bin"$'\n'"==> tool-start gate: 7 starts through $SEAL/bin" ]] \
    || { cat "$CASE/output" >&2; fail 'the tool-start gate did not start the candidate and then the seal'; }
[[ "$(grep -cxF '==> tool-start gate: 6/6 passed (1 not shipped, not started)' "$CASE/output")" -eq 2 ]] \
    || fail 'the tool-start gate did not report six starts and one tool not shipped, twice'
[[ "$(grep -cF '    n/a   trust-miri.session (this toolchain ships no bin/trust-miri; not started)' "$CASE/output")" -eq 2 ]] \
    || fail 'an absent trust-miri was not reported as not started'
for row in tippy-driver.clean:pass tippy-driver.lint:fail tippy.frontend:pass tippy.frontend-lint:fail \
    trustdoc.session:pass trustfmt.format:pass; do
    [[ "$(grep -cxF "    ok    ${row%:*} (${row#*:})" "$CASE/output")" -eq 2 ]] || fail "row ${row%:*} did not pass twice"
done
# The seal's identity is its whole content (T13a), read from the seal itself; the
# records promotion writes into it afterwards are outside it.
grep -qx "$("$PYTHON_BIN" -B "$REPO/scripts/lib/seal_content_identity.py" "$SEAL" | head -1)" "$SEAL/PROVENANCE" \
    || fail 'PROVENANCE does not carry the content identity of the sealed tree'
grep -qx 'artifact_content_scope=seal-content-v1' "$SEAL/PROVENANCE" || fail 'PROVENANCE does not name the identity scope'
grep -q '^artifact_bin_targo_sha256=' "$SEAL/PROVENANCE" || fail 'the per-file lines consumers read were dropped'

# A pack cut leaves its receipt beside the stage2's build tree; the seal carries it.
new_case pack-cut-receipt
printf 'schema=trust-seed-mint-v1\nsource_commit=%s\n' "$COMMIT" > "$CASE/build/trust-seed-mint"
run_promotion || { cat "$CASE/output" >&2; fail 'pack-cut fixture was refused'; }
cmp "$CASE/build/trust-seed-mint" "$SEAL/SEED-MINT" || fail 'the seal does not carry the pack-cut receipt'
grep -qx "seed_mint_sha256=$(shasum -a 256 "$CASE/build/trust-seed-mint" | awk '{print $1}')" "$SEAL/PROVENANCE" \
    || fail 'PROVENANCE does not bind the pack-cut receipt'

# A sealed compiler that links trust-cg-verify must admit the ay it ships
# (promote step 6a); a fixture private sysroot without trust_cg_verify is not
# asked, and the seal says so.
grep -qx 'ay_admission=not-checked: the sealed private sysroot carries no trust_cg_verify' \
    "$WORK/complete/sealed/trust-${COMMIT:0:8}/PROVENANCE" || fail 'an unasked ay admission was not recorded as such'

new_case ay-admitted
printf 'synthetic trust_cg_verify metadata\n' > "$PRIVATE/test-host/libtrust_cg_verify-fixture.rmeta"
run_promotion || { cat "$CASE/output" >&2; fail 'a compiler that admits its own ay was refused'; }
grep -q '^==> sealed compiler admits its own ay' "$CASE/output" || fail 'the ay admission was not asked'
grep -qx "ay_admission=admitted sha256=$(shasum -a 256 "$SEAL/bin/ay" | awk '{print $1}')" "$SEAL/PROVENANCE" \
    || fail 'PROVENANCE does not bind the admitted ay'

new_case ay-refused
printf 'synthetic trust_cg_verify metadata\n' > "$PRIVATE/test-host/libtrust_cg_verify-fixture.rmeta"
if TEST_AY_VERDICT=refused run_promotion; then fail 'a compiler that refuses its own ay was promoted'; fi
grep -qF 'the sealed compiler refuses the ay it ships: REFUSED [TCG-AY-IDENTITY-MISMATCH]' "$CASE/output" \
    || { cat "$CASE/output" >&2; fail 'unexpected refusal for ay-refused'; }
[[ "$(readlink "$CASE/rustup/toolchains/trust")" == "$CASE/previous" ]] || fail 'ay refusal moved the channel'
[[ ! -e "$SEAL/PROVENANCE" ]] || fail 'a refused seal was given a PROVENANCE'

# A probe that was built and then died says how: its exit status and its own
# words. ("failed to run" was the whole refusal.)
new_case ay-probe-dies-when-run
printf 'synthetic trust_cg_verify metadata\n' > "$PRIVATE/test-host/libtrust_cg_verify-fixture.rmeta"
if TEST_AY_VERDICT=dies run_promotion; then fail 'a seal was promoted with an AY-admission probe that died'; fi
grep -qxF "promote: the AY-admission probe did not run against the sealed driver: it exited 127 and printed ''; it said on stderr: fixture: the probe could not load the sealed driver" "$CASE/output" \
    || { cat "$CASE/output" >&2; fail 'an AY-admission probe that died was refused without its exit status and its words'; }
grep -qE '^promote: everything the checks of the sealed copy wrote is kept in ' "$CASE/output" \
    || fail 'a refusal that quotes the probe did not say where its files are kept'
[[ "$(readlink "$CASE/rustup/toolchains/trust")" == "$CASE/previous" ]] || fail 'a probe that died moved the channel'
[[ ! -e "$SEAL/PROVENANCE" ]] || fail 'a seal whose ay probe died was given a PROVENANCE'

write_completed_stamp() {
    "$PYTHON_BIN" -B - "$FIXTURE_REPO" "$CASE/build" "${1:-2}" <<'PY'
import importlib.util
from pathlib import Path
import sys
root, directory, version = Path(sys.argv[1]), Path(sys.argv[2]), sys.argv[3]
spec = importlib.util.spec_from_file_location("provenance", root / "scripts/lib/trust_build_provenance.py")
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)
owner = module.BuildStamp(root, directory, ["build", "--stage", "2"])
owner.start()
owner.finish("ok")
if version == "1":
    fields = module.validate_record(owner.path.read_text(), module._head(root))
    fields["record_version"] = "1"
    for key in module.RECURSIVE_IDENTITY[:3]:
        del fields[key]
    fields["tree_fingerprint"] = module.fingerprint(fields)
    fields["end_tree_fingerprint"] = fields["tree_fingerprint"]
    owner.path.write_text(module.render(fields))
PY
}

new_case required-recursive-provenance
write_completed_stamp
TEST_REQUIRE_PROV=1
run_promotion || { cat "$CASE/output" >&2; fail 'completed recursive stamp was refused'; }
grep -q '^provenance_class=BUILD-STAMPED-CLEAN$' "$SEAL/PROVENANCE" \
    || fail 'completed recursive source was not classified clean'
grep -q '^source_census_scope=recursive-worktrees/v1$' "$SEAL/PROVENANCE" \
    || fail 'seal omitted the observed recursive scope'

new_case required-legacy-provenance
write_completed_stamp 1
if run_promotion; then fail 'legacy top-level stamp satisfied recursive admission'; fi
grep -qF 'REFUSED (--require-provenance)' "$CASE/output" \
    || { cat "$CASE/output" >&2; fail 'legacy stamp had an unexpected refusal'; }
[[ "$(readlink "$CASE/rustup/toolchains/trust")" == "$CASE/previous" ]] \
    || fail 'legacy stamp refusal changed the channel'
[[ ! -e "$CASE/sealed" ]] || fail 'legacy stamp refusal copied a seal'
unset TEST_REQUIRE_PROV

# The same requirement spelled as the FLAG, which is how a seal asks for it
# (`promote-toolchain.sh --no-flip --require-provenance`). The two cases above
# ask through TRUST_REQUIRE_BUILD_PROVENANCE, and until 2026-10-12 no case
# spelled the flag: a sealer whose `--require-provenance` arm did nothing
# passed this whole file (measured that day by an independent review, on a
# scratch commit). Here the variable says 0 (TEST_REQUIRE_PROV is unset), so
# the refusal can only be the flag's.
new_case required-legacy-provenance-by-flag
write_completed_stamp 1
PROMOTE_OPTS=(--require-provenance)
if run_promotion; then fail '--require-provenance did not refuse a legacy top-level stamp'; fi
grep -qF 'REFUSED (--require-provenance)' "$CASE/output" \
    || { cat "$CASE/output" >&2; fail '--require-provenance gave an unexpected refusal'; }
[[ "$(readlink "$CASE/rustup/toolchains/trust")" == "$CASE/previous" ]] \
    || fail 'the --require-provenance refusal changed the channel'
[[ ! -e "$CASE/sealed" ]] || fail 'the --require-provenance refusal copied a seal'
unset PROMOTE_OPTS

# The candidate can live outside the checkout containing the promotion script.
# Exercise real kernel locks, including a stage reached through a symlink with
# spaces. A lock held by the script's unrelated build must not refuse it.
for shape in direct symlink; do
    new_case "locked external $shape"
    if [[ "$shape" == symlink ]]; then
        ln -s "$SRC" "$CASE/stage alias"
        SRC="$CASE/stage alias"
    fi
    TEST_LOCK_PATH="$CASE/build/lock"
    if run_promotion; then fail "locked $shape candidate was promoted"; fi
    grep -qF "an x.py/bootstrap build holds $CASE/build/lock" "$CASE/output" \
        || { cat "$CASE/output" >&2; fail "locked $shape candidate refused for the wrong reason"; }
    [[ ! -e "$CASE/sealed" ]] || fail 'locked candidate was copied'
    [[ "$(readlink "$CASE/rustup/toolchains/trust")" == "$CASE/previous" ]] \
        || fail 'locked candidate moved the channel'
    unset TEST_LOCK_PATH
done
# A lock nobody holds and this user cannot open is not "a build in flight":
# every failure of the probe used to be read as one.
if [[ "$(id -u)" -ne 0 ]]; then
    new_case lock-cannot-be-asked
    : > "$CASE/build/lock"; chmod 444 "$CASE/build/lock"
    if run_promotion; then fail 'a candidate whose build lock could not be asked was promoted'; fi
    grep -qF "promote: could not ask whether a build holds $CASE/build/lock (the probe exited 1): PermissionError" "$CASE/output" \
        && grep -qF 'It is not a build in flight' "$CASE/output" \
        || { cat "$CASE/output" >&2; fail 'an unreadable lock was not reported as one'; }
    ! grep -qF 'an x.py/bootstrap build holds' "$CASE/output" || fail 'an unreadable lock was reported as a build in flight'
    [[ ! -e "$CASE/sealed" ]] || fail 'a candidate whose lock could not be asked was copied'
else
    # root opens any file: the case cannot be staged. Said, and not counted as run.
    CASES_NOT_RUN=$((CASES_NOT_RUN + 1))
    echo 'NOT RUN: lock-cannot-be-asked (root opens any file, so a lock that cannot be opened cannot be staged)' >&2
fi
# A stage2 whose rustlib cannot be listed is refused before anything is spent on
# it, in find's own words. The listing's status was once discarded: the gates
# ran, `cp` died on the same directory, and the artifact directory it had begun
# was left behind with no PROVENANCE.
if [[ "$(id -u)" -ne 0 ]]; then
    new_case stdlib-listing-fails
    mkdir "$SRC/lib/rustlib/test-host/unreadable"; chmod 000 "$SRC/lib/rustlib/test-host/unreadable"
    promoted=1; run_promotion || promoted=0
    chmod 700 "$SRC/lib/rustlib/test-host/unreadable"
    [[ "$promoted" -eq 0 ]] || fail 'a stage2 whose rustlib could not be listed was promoted'
    grep -qF "promote: could not list the stdlib rlibs under $SRC/lib/rustlib: find exited 1, so nothing was copied. It said:" "$CASE/output" \
        && grep -qE '^        \| find: .*unreadable.*Permission denied' "$CASE/output" \
        || { cat "$CASE/output" >&2; fail 'a listing that failed was not refused in its own words'; }
    [[ ! -e "$CASE/sealed" ]] || fail 'a stage2 whose rustlib could not be listed was copied'
    [[ "$(readlink "$CASE/rustup/toolchains/trust")" == "$CASE/previous" ]] \
        || fail 'a stage2 whose rustlib could not be listed moved the channel'
else
    # root lists any directory: the case cannot be staged. Said, and not counted as run.
    CASES_NOT_RUN=$((CASES_NOT_RUN + 1))
    echo 'NOT RUN: stdlib-listing-fails (root lists any directory, so a listing that fails cannot be staged)' >&2
fi
new_case unrelated-helper-build
mkdir -p "$FIXTURE_REPO/build"
TEST_LOCK_PATH="$FIXTURE_REPO/build/lock"
run_promotion || { cat "$CASE/output" >&2; fail 'unrelated helper build blocked candidate'; }
[[ "$(readlink "$CASE/rustup/toolchains/trust")" == "$SEAL" ]] \
    || fail 'unlocked external candidate was not promoted'
unset TEST_LOCK_PATH

new_case frozen-sources-and-modes
mkdir -p "$SRC/lib/rustlib/src" "$SRC/lib/rustlib/rustc-src" "$CASE/outside"
ln -s "$FIXTURE_REPO" "$SRC/lib/rustlib/src/rust"
ln -s "$FIXTURE_REPO" "$SRC/lib/rustlib/rustc-src/rust"
ln -s "$CASE/outside" "$SRC/unrelated-escape"
# The copied sources must come from COMMIT, not these live worktree bytes.
printf 'changed live library source\n' > "$FIXTURE_REPO/library/fixture.rs"
printf 'changed live compiler source\n' > "$FIXTURE_REPO/compiler/fixture.rs"
chmod -R go+w "$SRC/bin" "$PRIVATE"
run_promotion || { cat "$CASE/output" >&2; fail 'source-sealing fixture was refused'; }
[[ ! -L "$SEAL/lib/rustlib/src/rust" ]] || fail 'rust-src still points at the live checkout'
[[ "$(cat "$SEAL/lib/rustlib/src/rust/library/fixture.rs")" == 'recorded standard-library source' ]] \
    || fail 'standard-library source did not come from compiler revision'
[[ "$(cat "$SEAL/lib/rustlib/rustc-src/rust/compiler/fixture.rs")" == 'recorded compiler source' ]] \
    || fail 'compiler source link was lost or not frozen'
[[ -f "$SEAL/lib/rustlib/src/rust/crates/trust-bignum/Cargo.toml" ]] \
    || fail 'frozen std sources omit their trust-bignum path dependency'
[[ -f "$SEAL/lib/rustlib/src/rust/crates/trust-memchr/Cargo.toml" ]] \
    || fail 'frozen std sources omit their memchr path patch'
[[ "$(cat "$SEAL/lib/rustlib/src/rust/src/llvm-project/libunwind/src/fixture.c")" == 'recorded unwind source' ]] \
    || fail 'frozen std sources omit libunwind'
"$PYTHON_BIN" - "$SEAL/lib/rustlib/src/rust/crates/trust-bignum/Cargo.toml" <<'PY' \
    || fail 'frozen std path dependency still needs its source workspace'
import pathlib, sys, tomllib
manifest = tomllib.loads(pathlib.Path(sys.argv[1]).read_text())
assert manifest["package"]["version"] == "1.0.0"
assert manifest["package"]["edition"] == "2021"
assert "lints" not in manifest and "dev-dependencies" not in manifest
PY
[[ ! -e "$SEAL/unrelated-escape" && ! -L "$SEAL/unrelated-escape" ]] \
    || fail 'source freezing weakened general escaping-link removal'
[[ -z "$(find "$SEAL" "$CASE/sealed/rustc-private-sysroots/fixture-key" ! -type l \( -perm -002 -o -perm -020 \))" ]] \
    || fail 'sealed toolchain or private sysroot remains writable by other users'

for doctor in rejected malformed failed ready-but-fails; do
    new_case "doctor-$doctor"
    TEST_DOCTOR_STATE="$doctor"
    if run_promotion; then fail "doctor $doctor was promoted"; fi
    grep -qF 'sealed toolchain fails its installed inventory validation' "$CASE/output" \
        || { cat "$CASE/output" >&2; fail "unexpected doctor $doctor refusal"; }
    # Each state has its own reason, never a traceback and never the sentence alone.
    case "$doctor" in
        rejected) DOCTOR_WHY='promote: installed toolchain is not ready: synthetic refusal' ;;
        malformed|failed) DOCTOR_WHY='promote: `targo trust doctor --format json` did not print a JSON report: ' ;;
        ready-but-fails) DOCTOR_WHY='reported ready and exited 3, and a doctor that fails is not a pass (its stderr began: doctor: synthetic late failure)' ;;
    esac
    grep -qF -- "$DOCTOR_WHY" "$CASE/output" || { cat "$CASE/output" >&2; fail "doctor $doctor gave no reason of its own"; }
    ! grep -qF 'Traceback' "$CASE/output" || { cat "$CASE/output" >&2; fail "doctor $doctor left a traceback for a reason"; }
    KEPT="$(sed -n 's/^promote: everything the checks of the sealed copy wrote is kept in //p' "$CASE/output")"
    [[ -n "$KEPT" && -f "$KEPT/doctor.json" && -f "$KEPT/doctor-stderr.txt" ]] \
        || { cat "$CASE/output" >&2; fail "doctor $doctor: what the doctor printed was not kept"; }
    [[ "$(readlink "$CASE/rustup/toolchains/trust")" == "$CASE/previous" ]] \
        || fail 'doctor refusal moved the channel'
    [[ ! -e "$CASE/sealed/trust-current" && ! -L "$CASE/sealed/trust-current" ]] \
        || fail 'doctor refusal created trust-current'
done
unset TEST_DOCTOR_STATE

for source_parent in src rustc-src; do
    new_case "escaping-parent-$source_parent"
    mkdir -p "$CASE/outside"
    printf 'external sentinel\n' > "$CASE/outside/sentinel"
    ln -s "$FIXTURE_REPO" "$CASE/outside/rust"
    ln -s "$CASE/outside" "$SRC/lib/rustlib/$source_parent"
    if run_promotion; then fail "escaping $source_parent parent was promoted"; fi
    grep -qF 'source snapshot parent is not a real directory' "$CASE/output" \
        || { cat "$CASE/output" >&2; fail "unexpected escaping $source_parent refusal"; }
    [[ "$(cat "$CASE/outside/sentinel")" == 'external sentinel' ]] \
        || fail 'source sealing changed an external file'
    [[ -L "$CASE/outside/rust" && "$(readlink "$CASE/outside/rust")" == "$FIXTURE_REPO" ]] \
        || fail 'source sealing replaced an external source link'
    [[ "$(readlink "$CASE/rustup/toolchains/trust")" == "$CASE/previous" ]] \
        || fail 'escaping source parent changed the channel'
    [[ ! -e "$CASE/sealed/trust-current" && ! -L "$CASE/sealed/trust-current" ]] \
        || fail 'escaping source parent created trust-current'
done

for forbidden in cargo-fmt cargo-clippy; do
    new_case "input-$forbidden"
    ln "$SRC/bin/targo-fmt" "$SRC/bin/$forbidden"
    assert_refusal stage2
done
for missing in bin/trustd bin/trustfmt bin/clean libexec/trust-analyzer-proc-macro-srv; do
    new_case "missing-${missing##*/}"
    rm "$SRC/$missing"
    assert_refusal stage2
done

assert_library_refusal() {
    local label="$1" fault="${2:-}"
    if run_promotion "$fault"; then fail "$(basename "$CASE") was promoted"; fi
    grep -qF "$label violates the complete Trust sysroot library contract" "$CASE/output" \
        || { cat "$CASE/output" >&2; fail 'unexpected library-contract refusal'; }
    [[ "$(readlink "$CASE/rustup/toolchains/trust")" == "$CASE/previous" ]] \
        || fail 'library refusal moved the channel'
    [[ ! -e "$CASE/sealed/trust-current" && ! -L "$CASE/sealed/trust-current" ]] \
        || fail 'library refusal created trust-current'
    if [[ "$label" == stage2 ]]; then
        [[ ! -e "$CASE/sealed" ]] || fail 'invalid library input was copied'
    fi
}
for crate in core alloc std compiler_builtins test proc_macro trust_bignum; do
    new_case "missing-host-library-$crate"
    rm "$SRC/lib/rustlib/test-host/lib/lib$crate-fixture.rlib"
    assert_library_refusal stage2
    grep -qF "missing $crate rlib" "$CASE/output" || fail 'missing host library had no diagnosis'
done
for crate in test proc_macro trust_bignum; do
    new_case "missing-cross-library-$crate"
    cross="$SRC/lib/rustlib/x86_64-apple-darwin/lib"
    mkdir -p "$cross"
    for member in core alloc std compiler_builtins test proc_macro trust_bignum; do
        printf 'synthetic cross library\n' > "$cross/lib$member-fixture.rlib"
    done
    rm "$cross/lib$crate-fixture.rlib"
    assert_library_refusal stage2
    grep -qF "x86_64-apple-darwin: missing $crate rlib" "$CASE/output" \
        || fail 'missing cross library had no target-specific diagnosis'
done
for crate in libc hashbrown; do
    new_case "ambiguous-public-library-$crate"
    for identity in stdlib compiler; do
        printf 'different synthetic dependency cohort\n' \
            > "$SRC/lib/rustlib/test-host/lib/lib$crate-$identity.rmeta"
    done
    assert_library_refusal stage2
    grep -qF "multiple public $crate artifact cohorts" "$CASE/output" \
        || fail 'public dependency collision had no diagnosis'
done
new_case sealed-missing-library
assert_library_refusal 'sealed toolchain' library

# A stock program under a Trust name runs and answers every probe; only its
# banner gives it away, and the output contract refuses it.
for stock in trustfmt:'rustfmt 1.9.0-stable (88d9e12ae1 2026-08-18)' \
    tippy-driver:'clippy 0.1.98 (88d9e12ae1 2026-08-18)'; do
    new_case "stock-${stock%%:*}"
    printf '#!/bin/sh\nprintf "%s\\n"\n' "${stock#*:}" > "$SRC/bin/${stock%%:*}"
    assert_refusal stage2
    grep -qF "IDENTITY: ${stock%%:*} (tier 2) is not the Trust build of ${stock%%:*}" "$CASE/output" \
        || { cat "$CASE/output" >&2; fail "stock ${stock%%:*} was refused for the wrong reason"; }
done
for alias in rustc cargo rustdoc; do
    new_case "mismatched-$alias"
    printf '#!/bin/sh\necho different-fixture\n' > "$SRC/bin/$alias"
    assert_refusal stage2
done
for fault in forbidden missing broken; do
    new_case "sealed-$fault"
    assert_refusal 'sealed toolchain' "$fault"
done

# A stage2 whose own sysroot lost the rustc-dev closure (a build-tree stage1,
# or a stage2 the Kind::Build top-up skipped) must not become the channel:
# trust-mc builds `extern crate rustc_public` against it with no overlay. It is
# refused before the copy, so no sealed artifact is left to block a re-run.
new_case missing-rustc-dev
rm "$SRC/lib/rustlib/test-host/lib/librustc_public-fixture.rmeta"
if run_promotion; then fail 'a seal without rustc-dev was promoted'; fi
grep -qF "stage2 at $SRC cannot build a rustc_private consumer from its own sysroot" "$CASE/output" \
    || { cat "$CASE/output" >&2; fail 'missing rustc-dev had an unexpected refusal'; }
grep -qF "E0463" "$CASE/output" || fail 'rustc-dev refusal did not carry the compiler diagnostic'
[[ ! -e "$SEAL" && ! -e "$CASE/sealed/rustc-private-sysroots" ]] \
    || fail 'missing rustc-dev left a sealed artifact behind'
[[ "$(readlink "$CASE/rustup/toolchains/trust")" == "$CASE/previous" ]] \
    || fail 'missing rustc-dev moved the channel'
[[ ! -e "$CASE/sealed/trust-current" && ! -L "$CASE/sealed/trust-current" ]] \
    || fail 'missing rustc-dev created trust-current'

for fault in fail no-output not-executable; do
    new_case "rustc-dev-link-$fault"
    if TEST_RUSTC_DEV_LINK="$fault" run_promotion; then fail "rustc-dev $fault link was promoted"; fi
    grep -qF 'cannot build a rustc_private consumer from its own sysroot' "$CASE/output" \
        || { cat "$CASE/output" >&2; fail 'native link failure had an unexpected refusal'; }
    # The step that failed is named, its output is quoted under that name, and
    # the directory with all of it is kept.
    case "$fault" in
        fail) grep -qxF '    FAIL  rustc-dev probe: the compiler exited 1 building a rustc_private consumer (rustc_dev_probe.log). It said:' "$CASE/output" \
                && grep -qxF "        | ld: library 'Polly' not found" "$CASE/output" ;;
        no-output) grep -qxF '    FAIL  rustc-dev probe: the compiler exited 0 without writing an executable' "$CASE/output" ;;
        # Written, and not something this run may execute: the row says which of
        # the two it is (no execute bit here; a noexec TMPDIR reads otherwise).
        # The mode is the caller's umask's, and an `ls` may mark an ACL or attribute after it.
        not-executable) grep -qxE '    FAIL  rustc-dev probe: the compiler exited 0 and wrote rustc_dev_probe as something that is not a file with an execute bit \(-rw-[-r][-w]-[-r][-w]-[.+@]?\)' "$CASE/output" ;;
    esac || { cat "$CASE/output" >&2; fail "rustc-dev $fault link: the probe did not say which step failed"; }
    KEPT="$(sed -n 's/^    \(\/.*\)$/\1/p' "$CASE/output" | tail -1)"
    grep -qF 'Its source and everything it printed are kept in' "$CASE/output" \
        && [[ -n "$KEPT" && -f "$KEPT/rustc_dev_probe.rs" && -f "$KEPT/rustc_dev_probe.log" ]] \
        || { cat "$CASE/output" >&2; fail "rustc-dev $fault link: the probe's files were not kept"; }
    [[ ! -e "$SEAL" && "$(readlink "$CASE/rustup/toolchains/trust")" == "$CASE/previous" ]] \
        || fail 'failed native link copied a seal or moved the channel'
done
for fault in fail no-marker; do
    new_case "rustc-dev-run-$fault"
    if TEST_RUSTC_DEV_RUN="$fault" run_promotion; then fail "rustc-dev $fault run was promoted"; fi
    grep -qF 'cannot build a rustc_private consumer from its own sysroot' "$CASE/output" \
        || { cat "$CASE/output" >&2; fail 'native execution failure had an unexpected refusal'; }
    case "$fault" in
        fail) grep -qxF '    FAIL  rustc-dev probe: the consumer it built exited 127 when run (rustc_dev_probe.run.log). It said:' "$CASE/output" \
                && grep -qxF '        | native fixture loader failure' "$CASE/output" ;;
        no-marker) grep -qxF '    FAIL  rustc-dev probe: the consumer it built exited 0 without completing its native driver call (rustc_dev_probe.run.log). It said:' "$CASE/output" \
                && grep -qxF '        | (it printed nothing)' "$CASE/output" ;;
    esac || { cat "$CASE/output" >&2; fail "rustc-dev $fault run: the probe did not say which step failed"; }
    [[ ! -e "$SEAL" && "$(readlink "$CASE/rustup/toolchains/trust")" == "$CASE/previous" ]] \
        || fail 'failed native run copied a seal or moved the channel'
done

new_case rustc-dev-ambient-overlay
mkdir "$CASE/decoy-overlay"
LIBRARY_PATH="$CASE/decoy-overlay" LD_LIBRARY_PATH="$CASE/decoy-overlay" \
    run_promotion || { cat "$CASE/output" >&2; fail 'private probe inherited an ambient overlay'; }

for fault in rustc-dev-link rustc-dev-run; do
    new_case "seal-lost-$fault"
    if run_promotion "$fault"; then fail "a seal with $fault failure was promoted"; fi
    grep -qF 'sealed toolchain cannot build a rustc_private consumer from its own sysroot' "$CASE/output" \
        || { cat "$CASE/output" >&2; fail 'sealed native failure had an unexpected refusal'; }
    [[ "$(readlink "$CASE/rustup/toolchains/trust")" == "$CASE/previous" ]] \
        || fail 'sealed native failure moved the channel'
done

# The candidate carries the closure but the sealed copy does not: the probe of
# the seal itself (step 6) still refuses before the channel moves.
new_case seal-lost-rustc-dev
if run_promotion rustc-dev; then fail 'a seal that lost rustc-dev in the copy was promoted'; fi
grep -qF 'sealed toolchain cannot build a rustc_private consumer from its own sysroot' "$CASE/output" \
    || { cat "$CASE/output" >&2; fail 'seal-lost rustc-dev had an unexpected refusal'; }
[[ "$(readlink "$CASE/rustup/toolchains/trust")" == "$CASE/previous" ]] \
    || fail 'seal-lost rustc-dev moved the channel'

assert_dependency_refusal() {
    if run_promotion; then fail 'missing surface dependency permitted promotion'; fi
    grep -qF 'toolchain surface validation requires' "$CASE/output" \
        || { cat "$CASE/output" >&2; fail 'unexpected dependency refusal'; }
    [[ ! -e "$CASE/sealed" ]] || fail 'missing dependency permitted copying'
    [[ "$(readlink "$CASE/rustup/toolchains/trust")" == "$CASE/previous" ]] \
        || fail 'missing dependency permitted channel change'
}

new_case missing-selected-python
printf '#!/bin/sh\necho mismatched-alias\n' > "$SRC/bin/cargo"
TEST_SURFACE_PYTHON="$CASE/absent-python"
assert_dependency_refusal

new_case broken-selected-python
TEST_SURFACE_PYTHON="$CASE/broken-python"
printf '#!/bin/sh\nexit 1\n' > "$TEST_SURFACE_PYTHON"
chmod +x "$TEST_SURFACE_PYTHON"
assert_dependency_refusal
unset TEST_SURFACE_PYTHON

new_case missing-surface-library
ln "$SRC/bin/targo-fmt" "$SRC/bin/cargo-fmt"
rm "$FIXTURE_REPO/scripts/lib/trust_toolchain_surface.sh"
assert_dependency_refusal

# The case above deleted the surface library from the fixture; put it back.
cp "$REPO/scripts/lib/trust_toolchain_surface.sh" "$FIXTURE_REPO/scripts/lib/"

# --no-flip seals and records everything but leaves the channel alone, so a
# seal can be admitted onto `trust` later by a separate, deliberate step.
new_case no-flip
PROMOTE_OPTS=(--no-flip)
run_promotion || { cat "$CASE/output" >&2; fail 'no-flip promotion was refused'; }
[[ -d "$SEAL" && -f "$SEAL/PROVENANCE" ]] || fail 'no-flip did not seal'
[[ "$(readlink "$CASE/rustup/toolchains/trust")" == "$CASE/previous" ]] || fail 'no-flip moved the channel'
[[ ! -e "$CASE/sealed/trust-current" && ! -L "$CASE/sealed/trust-current" ]] || fail 'no-flip created trust-current'
grep -qF 'sealed, NOT flipped (--no-flip)' "$CASE/output" || fail 'no-flip did not say so'
grep -q '^stage0_lineage=absent$' "$SEAL/PROVENANCE" || fail 'a seal without --lineage must say its lineage is absent'

write_lineage() {
    "$PYTHON_BIN" - "$1" "$SRC" "$COMMIT" "${2:-}" <<'PY'
import hashlib, json, sys
out, src, commit, variant = sys.argv[1:5]
sha = lambda p: hashlib.sha256(open(p, "rb").read()).hexdigest()
final = {"commit": commit, "trustc_sha256": sha(src + "/bin/trustc"),
         "driver_sha256": sha(src + "/lib/librustc_driver-fixture.dylib")}
if variant == "corrupt":
    final["trustc_sha256"] = "0" * 64
record = {"schema": "trust-seed-staircase-v1", "kind": "lineage",
          "root": {"commit": "629729f69eefb1cfe6ed766c6c01ee38aa7b0484"},
          "rungs": [{"label": "r0", "commit": commit}], "final": final}
if variant == "ddc-different":
    record["ddc"] = {"verdict": "different", "relation": "same-lineage"}
# A pinned root (a Linux extraction) and the host record that admitted it, as
# seed_staircase.py build_lineage writes root.pin_admission (docs/PLAN.md PKG-S6).
disclosed = {"root": "unpinned-host-chain", "predecessor_pin": "none", "double_compile_diverse": "false",
             "stock_built_ancestor": "inferred-no-receipt"}
if variant.startswith("pinned"):
    record["root"]["admission"] = {"commit": record["root"]["commit"], "pinned_seed": {"kind": "seed-sysroot"}}
pin_admission = {
    "pinned-fixed-point": {"kind": "fixed-point-unpinned-root", "root_disclosure": disclosed},
    "pinned-mint": {"kind": "mint", "root_disclosure": None},
    "pinned-fixed-point-undisclosed": {"kind": "fixed-point-unpinned-root", "root_disclosure": None},
    "pinned-disclosure-not-a-word": {"kind": "fixed-point-unpinned-root",
                                     "root_disclosure": {**disclosed, "root": "unpinned host chain"}},
    "pinned-kind-not-a-word": {"kind": "Mint!", "root_disclosure": None},
    "pinned-mint-disclosed": {"kind": "mint", "root_disclosure": disclosed},
    "pinned-fixed-point-not-its-words": {"kind": "fixed-point-unpinned-root",
                                         "root_disclosure": {**disclosed, "predecessor_pin": "abc"}},
    "pinned-disclosure-not-a-table": {"kind": "fixed-point-unpinned-root", "root_disclosure": "x"},
    "admission-without-pinned-root": {"kind": "mint", "root_disclosure": None},
}.get(variant)
if pin_admission is not None:
    record["root"]["pin_admission"] = pin_admission
json.dump(record, open(out, "w"))
PY
}

new_case lineage-sealed
write_lineage "$CASE/lineage.json"
PROMOTE_OPTS=(--no-flip --lineage "$CASE/lineage.json")
run_promotion || { cat "$CASE/output" >&2; fail 'matching lineage was refused'; }
cmp "$CASE/lineage.json" "$SEAL/STAGE0-LINEAGE" || fail 'lineage record was not sealed verbatim'
grep -q "^stage0_lineage_sha256=$(shasum -a 256 "$CASE/lineage.json" | cut -d' ' -f1)\$" "$SEAL/PROVENANCE" \
    || fail 'PROVENANCE does not bind the sealed lineage record'
grep -q '^stage0_lineage_summary=root=629729f69eefb1cfe6ed766c6c01ee38aa7b0484 rungs=1 .* ddc=none$' "$SEAL/PROVENANCE" \
    || fail 'PROVENANCE does not summarize the lineage'
[[ "$(readlink "$CASE/rustup/toolchains/trust")" == "$CASE/previous" ]] || fail 'lineage no-flip moved the channel'

new_case lineage-for-another-stage2
write_lineage "$CASE/lineage.json" corrupt
PROMOTE_OPTS=(--lineage "$CASE/lineage.json")
if run_promotion; then fail 'a lineage record naming another trustc was accepted'; fi
grep -qF 'does not describe this stage2: final.trustc_sha256' "$CASE/output" \
    || { cat "$CASE/output" >&2; fail 'foreign lineage refused for the wrong reason'; }
[[ ! -e "$CASE/sealed" ]] || fail 'foreign lineage was copied'
[[ "$(readlink "$CASE/rustup/toolchains/trust")" == "$CASE/previous" ]] || fail 'foreign lineage moved the channel'

new_case lineage-whose-double-compile-differs
write_lineage "$CASE/lineage.json" ddc-different
PROMOTE_OPTS=(--no-flip --lineage "$CASE/lineage.json")
if run_promotion; then fail 'a lineage whose double compile differs was sealed'; fi
grep -qF "its double compile says 'different'" "$CASE/output" \
    || { cat "$CASE/output" >&2; fail 'differing DDC refused for the wrong reason'; }
[[ ! -e "$CASE/sealed" ]] || fail 'a lineage with a differing DDC was copied'

# A lineage over a pinned root (root.admission.pinned_seed, a Linux extraction)
# says which host record admitted that seed; one that does not is refused. A
# root that is not pinned (the lineage-sealed case above) prints today's line.
grep -q 'pin_admission' "$WORK/lineage-sealed/sealed/trust-${COMMIT:0:8}/PROVENANCE" \
    && fail 'a lineage whose root is not pinned grew a pin_admission word'
new_case lineage-pinned-without-pin-admission
write_lineage "$CASE/lineage.json" pinned
PROMOTE_OPTS=(--no-flip --lineage "$CASE/lineage.json")
if run_promotion; then fail 'a pinned-root lineage without root.pin_admission was sealed'; fi
grep -qF 'its root is a pinned seed and it records no root.pin_admission' "$CASE/output" \
    || { cat "$CASE/output" >&2; fail 'a pinned root without pin_admission refused for the wrong reason'; }
[[ ! -e "$CASE/sealed" ]] || fail 'a pinned-root lineage without pin_admission was copied'

new_case lineage-pinned-fixed-point
write_lineage "$CASE/lineage.json" pinned-fixed-point
PROMOTE_OPTS=(--no-flip --lineage "$CASE/lineage.json")
run_promotion || { cat "$CASE/output" >&2; fail 'a fixed-point pinned-root lineage was refused'; }
grep -q '^stage0_lineage_summary=root=629729f69eefb1cfe6ed766c6c01ee38aa7b0484 rungs=1 .* ddc=none pin_admission=fixed-point-unpinned-root root=unpinned-host-chain predecessor_pin=none stock_built_ancestor=inferred-no-receipt$' "$SEAL/PROVENANCE" \
    || { grep stage0_lineage_summary "$SEAL/PROVENANCE" >&2; fail 'PROVENANCE does not say the fixed point that admitted the root'; }

new_case lineage-pinned-mint
write_lineage "$CASE/lineage.json" pinned-mint
PROMOTE_OPTS=(--no-flip --lineage "$CASE/lineage.json")
run_promotion || { cat "$CASE/output" >&2; fail 'a mint pinned-root lineage was refused'; }
grep -q '^stage0_lineage_summary=root=629729f69eefb1cfe6ed766c6c01ee38aa7b0484 rungs=1 .* ddc=none pin_admission=mint$' "$SEAL/PROVENANCE" \
    || { grep stage0_lineage_summary "$SEAL/PROVENANCE" >&2; fail 'PROVENANCE does not say the mint that admitted the root'; }

for refused in \
    'pinned-fixed-point-undisclosed|root.pin_admission is a fixed point and carries no root_disclosure' \
    "pinned-disclosure-not-a-word|root.pin_admission.root_disclosure.root is 'unpinned host chain', not a word" \
    "pinned-kind-not-a-word|root.pin_admission.kind is 'Mint!', not an admission kind" \
    'pinned-mint-disclosed|root.pin_admission is kind mint and carries a root_disclosure, which only a fixed point (fixed-point-unpinned-root) is admitted with' \
    "pinned-fixed-point-not-its-words|root.pin_admission.root_disclosure.predecessor_pin is 'abc'; a fixed point is admitted only with none" \
    'pinned-disclosure-not-a-table|root.pin_admission.root_disclosure is not a table' \
    'admission-without-pinned-root|it records root.pin_admission for a root that is not a pinned seed'; do
    variant="${refused%%|*}"
    new_case "lineage-$variant"
    write_lineage "$CASE/lineage.json" "$variant"
    PROMOTE_OPTS=(--no-flip --lineage "$CASE/lineage.json")
    if run_promotion; then fail "a lineage ($variant) was sealed"; fi
    grep -qF "${refused#*|}" "$CASE/output" \
        || { cat "$CASE/output" >&2; fail "a lineage ($variant) refused for the wrong reason"; }
    [[ ! -e "$CASE/sealed" ]] || fail "a lineage ($variant) was copied"
done
unset PROMOTE_OPTS

# THE STAGE RECEIPT. scripts/recreate_bootstrap.py leaves `tool-provenance.json`
# in the stage2 it builds. Until 2026-10-12 promotion never opened it: three
# seed-built seals of that day each carry a receipt saying mode seed,
# trust_from_trust, internal-release-ready, and each PROVENANCE says only
# `stage0_lineage=absent`. The fixture receipt has the fields of those three
# (read that day from ~/toolchains/trust-f22fc270), every hash being the fixture
# file's own, plus the `recreator_invocation` record the recreator writes since.
# `$2` names what to get wrong.
write_stage_receipt() { # <stage2> [variant]
    "$PYTHON_BIN" - "$1" "$COMMIT" "${2:-}" <<'PY'
import hashlib, json, os, sys
stage, commit, variant = sys.argv[1:4]
root = "build/test-host/stage2"
sha = lambda relative: hashlib.sha256(open(f"{stage}/{relative}", "rb").read()).hexdigest()
tools = []
for name in sorted(os.listdir(f"{stage}/bin")):
    if name in ("trustc", "rustc", "rustdoc"):
        continue  # the compiler and the two stock names have fields of their own
    tools.append({"name": name, "path": f"{root}/bin/{name}", "sha256": sha(f"bin/{name}"),
                  "producer_sha256": sha(f"bin/{name}"), "status": "bound"})
ty = next(row for row in tools if row["name"] == "ty")
receipt = {
    "schema": "trust.stage-tool-provenance.v2",
    "status": "internal-release-ready",
    "tool_binding_status": "ready",
    "source_tree_clean": True,
    "trust_from_trust": True,
    "stage": 2,
    "host": "test-host",
    "path_scope": "repository-root-relative",
    "stage_root": root,
    "tools": tools,
    "compiler": {"path": f"{root}/bin/trustc", "compiler_sha256": sha("bin/trustc"),
                 "compatibility_alias": f"{root}/bin/rustc",
                 "compatibility_alias_sha256": sha("bin/rustc"), "source_commit": commit},
    "rustdoc_alias": {"path": f"{root}/bin/rustdoc", "sha256": sha("bin/rustdoc")},
    "proc_macro_helper": {"path": f"{root}/libexec/trust-analyzer-proc-macro-srv",
                          "sha256": sha("libexec/trust-analyzer-proc-macro-srv")},
    "bootstrap_lineage": {
        "schema": "trust.bootstrap-lineage.v1", "mode": "seed", "status": "trust_from_trust",
        "trust_from_trust": True, "errors": [],
        "validated_seed": {"status": "validated",
                           "materialization_status": "fresh-from-validated-archives"},
    },
    "errors": [],
    "recreator_invocation": {
        "schema": "trust.recreator-invocation.v1", "scope": "self-reported",
        "argv": ["--stage", "2", "--require-seed", "--fresh-seed", "--no-register"],
    },
}
lineage, invocation = receipt["bootstrap_lineage"], receipt["recreator_invocation"]
if variant == "no-argv":                      # a receipt as written until 2026-10-12
    del receipt["recreator_invocation"]
elif variant == "genesis":                    # a stock-rust development build
    receipt.update(status="candidate-ready", trust_from_trust=False)
    lineage.update(mode="genesis", status="local_genesis", trust_from_trust=False, validated_seed=None)
    invocation["argv"] = ["--genesis", "--llvm-config", "/opt/llvm 22/bin/llvm-config"]
elif variant == "rejected":
    receipt.update(status="rejected", tool_binding_status="rejected",
                   errors=["public tool ty does not match its x.py producer: aa != bb"])
elif variant == "release-without-fresh-seed":
    lineage["validated_seed"]["materialization_status"] = "preexisting-unproven"
elif variant == "foreign-commit":
    receipt["compiler"]["source_commit"] = "0" * 40
elif variant == "path-outside-stage":
    ty["path"] = f"{root}/bin/../../stage1/bin/ty"
elif variant == "argv-injects-a-line":
    invocation["argv"] = ["--stage", "2\nprovenance_class=BUILD-STAMPED-CLEAN"]
elif variant == "atpkg":                      # built from the stage0 an installed pack ships
    receipt.update(status="candidate-ready")
    lineage.update(mode="atpkg", status="local_atpkg", validated_seed=None)
    invocation["argv"] = ["--stage", "2", "--no-register"]
elif variant == "release-ready":              # a publicly promoted seed, freshly materialized
    receipt.update(status="release-ready")
elif variant == "non-ascii-argument":
    # U+1FAE8 was assigned in Unicode 14: the python3 that runs the sealer here may
    # not know it (3.9.6 does not), the python3.14 that ran the recreator does.
    invocation["argv"] = ["--stage", "2", "--llvm-config",
                          "/opt/llvm-\U0001FAE8 22/it's/b\\in/llvm-config"]
elif variant == "long-arguments":
    invocation["argv"] = ["--stage", "2", "--llvm-config", "/opt/" + "x" * 4090 + "/bin/llvm-config"]
elif variant == "argument-not-recorded":      # one argument that is the reader's own word
    invocation["argv"] = ["not-recorded"]
elif variant == "format-characters":
    # What a printf FORMAT would interpret, outside the $'...' form and inside it.
    invocation["argv"] = ["--stage", "2", "--llvm-config",
                          "/opt/llvm-\U0001FAE8 22/it's/b\\in/llvm-config", "100%", "%s%n", "a\\tb", "\\"]
elif variant == "expanding-arguments":
    # 1100 characters in 2200 bytes: under 4096 as given, 8803 characters as written.
    invocation["argv"] = ["\u00e9" * 1100]
elif variant == "code-points-outside-the-refused-ranges":
    # The first code point outside each refused range (U+0020 and U+007E, U+00A0,
    # U+D7FF and U+E000), then what a wider rule would refuse: a zero-width space,
    # the bidi isolates, two noncharacters, two tag characters, the last code point.
    invocation["argv"] = [" ~", "\u00a0", "\ud7ff\ue000", "\u200b", "\u2066\u2069", "\ufdd0\ufdef",
                          "\U000e0000\U000e007f", "\U0010ffff"]
elif variant.startswith("argv-holds-U+"):     # one end of a range the reader refuses
    invocation["argv"] = ["--host", "a" + chr(int(variant[len("argv-holds-U+"):], 16)) + "b"]
elif variant.startswith("llvm-"):
    # THE LLVM THE STAGE CARRIES, as the recreator records it since 2026-10-13
    # (`llvm_identity`). The source identity is one sha256 over the git ids of the
    # LLVM inputs; a stated in-tree identity quotes the build record of the LLVM,
    # which names the config and native authority this receipt names.
    def identity_of(rows):
        return hashlib.sha256(json.dumps({"schema": "trust.llvm-source-identity.v1", "paths": rows},
                                         sort_keys=True, separators=(",", ":")).encode()).hexdigest()
    rows = [{"path": "src/bootstrap", "type": "tree", "oid": "2" * 40},
            {"path": "src/llvm-project", "type": "tree", "oid": "3" * 40},
            {"path": "src/version", "type": "blob", "oid": "4" * 40}]
    record = {"schema": "trust.llvm-build-record.v1", "built_at_commit": commit, "host": "test-host",
              "source_identity_sha256": identity_of(rows), "source_paths": rows,
              "bootstrap_config_sha256": "d" * 64, "native_authority_sha256": "8" * 64,
              "output_fingerprint_sha256": "6" * 64}
    llvm = {"schema": "trust.llvm-identity.v1", "mode": "in-tree", "provenance": "built-in-this-run",
            "identity_stated": True, "reasons": [], "source_identity_sha256": identity_of(rows),
            "source_paths": rows, "output_dirs": ["build/test-host/llvm"],
            "output_fingerprint_sha256": "6" * 64, "build_record": record}
    lineage["config_sha256"] = "d" * 64
    receipt["build_authority"] = {"authority_sha256": "8" * 64, "selected_llvm": None}
    receipt["llvm_identity"] = llvm
    not_stated = dict(provenance="reused", identity_stated=False, build_record=None,
                      reasons=["build/test-host/llvm was reused, and it holds no build record"])
    if variant == "llvm-reused":                # built at an earlier commit, in this build directory
        llvm["provenance"] = "reused"
        record["built_at_commit"] = "2" * 40
    elif variant == "llvm-not-stated":
        # Reused with nothing that says what it was built from: what every build
        # directory that existed before the record yields. The status word is
        # the lineage's, as it was before the record existed.
        llvm.update(not_stated)
    elif variant == "llvm-record-for-other-sources":  # a commit changed an LLVM source since
        other = [dict(row, oid="9" * 40) if row["path"] == "src/llvm-project" else row for row in rows]
        record.update(source_paths=other, source_identity_sha256=identity_of(other))
    elif variant == "llvm-not-an-object":
        receipt["llvm_identity"] = "in-tree"
    elif variant in ("llvm-external", "llvm-external-stated"):
        # --llvm-config. The recreator NEVER states such an LLVM: it did not watch it
        # being built, and binds the llvm-config executable, not what it points at.
        # The record holds no source identity either: the checkout's own
        # src/llvm-project is not what that LLVM was built from.
        llvm.update(mode="external", provenance="external", identity_stated=False,
                    reasons=["the stage links an external LLVM through --llvm-config"],
                    source_identity_sha256=None, source_paths=[], output_dirs=[],
                    output_fingerprint_sha256=None, build_record=None)
        receipt["build_authority"]["selected_llvm"] = {"name": "llvm-config", "status": "bound"}
        if variant == "llvm-external-stated":
            # What the first version of the record wrote for it (until the re-read
            # of 2026-10-13): stated, on the bound llvm-config, with the checkout's
            # LLVM source ids beside it. Not a record promotion writes down.
            llvm.update(identity_stated=True, reasons=[], source_identity_sha256=identity_of(rows),
                        source_paths=rows)
    elif variant in ("llvm-unknown", "llvm-unknown-with-ids"):
        # The config x.py obeys does not itself say which LLVM it links: here it
        # names an llvm-config the run was not given (the third reading's case,
        # 2026-10-13). Never stated, and no id of the checkout beside it.
        llvm.update(mode="unknown", provenance="unknown", identity_stated=False,
                    reasons=["bootstrap.toml links the external llvm-config '/opt/llvm/bin/llvm-config', "
                             "which is not the one this run binds (--llvm-config None)"],
                    source_identity_sha256=None, source_paths=[], output_dirs=[],
                    output_fingerprint_sha256=None, build_record=None)
        if variant == "llvm-unknown-with-ids":
            # What the recreator wrote for it from 381ac1ea0d until the follow-up
            # of that day: the same, with the checkout's LLVM source ids.
            llvm.update(source_identity_sha256=identity_of(rows), source_paths=rows)
    elif variant != "llvm-built":
        sys.exit(f"unknown receipt variant {variant}")
text = json.dumps(receipt, indent=2, sort_keys=True) + "\n"
if variant == "not-json":
    text = text[: len(text) // 2]
elif variant == "repeated-key":
    text = '{\n  "status": "candidate-ready",' + text[1:]
with open(f"{stage}/tool-provenance.json", "w") as out:
    out.write(text)
PY
}

# What PROVENANCE must say of a receipt, read from the receipt by this test and
# not by the code under test. `$2` is the recorded command line, shell-quoted.
stage_receipt_lines_of() { # <receipt> <argv words | not-recorded>
    "$PYTHON_BIN" - "$1" "$2" <<'PY'
import hashlib, json, sys
raw = open(sys.argv[1], "rb").read()
receipt = json.loads(raw)
lineage = receipt["bootstrap_lineage"]
seed = lineage["validated_seed"]
print("stage_receipt=tool-provenance.json")
print("stage_receipt_sha256=" + hashlib.sha256(raw).hexdigest())
print("stage_receipt_schema=" + receipt["schema"])
print("stage_receipt_status=" + receipt["status"])
print("stage_receipt_lineage_mode=" + lineage["mode"])
print("stage_receipt_trust_from_trust=" + ("true" if lineage["trust_from_trust"] else "false"))
print("stage_receipt_seed_materialization=" + (seed["materialization_status"] if seed else "not-applicable"))
# Every tool row, the compiler, its rustc name, the rustdoc name, the proc-macro helper.
print("stage_receipt_files_verified=%d" % (len(receipt["tools"]) + 4))
# The LLVM the stage carries: one line for a receipt without the record (every one
# written before 2026-10-13), seven for one with it, a value on every line.
# Of the source tree and the build directory, only an in-tree LLVM gets ids: an
# external one has none, and the ids a record of mode unknown may hold (the
# recreator of 381ac1ea0d wrote the checkout's) are not known to describe it.
llvm = receipt.get("llvm_identity")
if llvm is None:
    print("stage_receipt_llvm=not-recorded")
else:
    of_tree = llvm if llvm["mode"] == "in-tree" else {}
    built = of_tree.get("build_record")
    tree = [row["oid"] for row in of_tree.get("source_paths", []) if row["path"] == "src/llvm-project"]
    print("stage_receipt_llvm=" + llvm["mode"])
    print("stage_receipt_llvm_identity=" + ("stated" if llvm["identity_stated"] else "not-stated"))
    print("stage_receipt_llvm_provenance=" + llvm["provenance"])
    print("stage_receipt_llvm_source_sha256=" + (of_tree.get("source_identity_sha256") or "not-recorded"))
    print("stage_receipt_llvm_source_tree=" + (tree[0] if tree else "not-recorded"))
    print("stage_receipt_llvm_built_at_commit=" + (built["built_at_commit"] if built else "not-recorded"))
    print("stage_receipt_llvm_output_sha256=" + (of_tree.get("output_fingerprint_sha256") or "not-recorded"))
print("stage_receipt_recreator_argv=" + sys.argv[2])
PY
}

SEED_ARGV='--stage 2 --require-seed --fresh-seed --no-register'

# SECTION (f) OF A SEAL'S PROVENANCE, WORD FOR WORD. Every sentence of it tells
# a reader of the seal what promotion checked and what it did not, so a
# sentence reworded is a statement changed: the whole section is compared, down
# to the first line it records. (Until 2026-10-13 two of its lines were looked
# for and one phrase was forbidden; its last line, and the text for a stage2
# without a receipt, could say anything.) What the text says of the receipt's
# other hashes was measured that day on the receipt sealed in trust-f22fc270:
# 351 sha256 values, 21 compared by promotion, 154 of the rest the seed's
# stage0 tree, 62 of those under that tree's lib/. What it says x.py does with
# the in-tree LLVM is what bootstrap does since its fix of 2026-10-13
# (says_what_x_py_does_now, below); until 2026-10-14 it said that x.py does not
# rebuild the in-tree LLVM for a committed change to it.
section_f_of() { sed -n '/^# (f) THE STAGE RECEIPT/,/^stage_receipt=/p' "$1"; }
cat > "$WORK/section-f-with-a-receipt" <<'TEXT'
# (f) THE STAGE RECEIPT — the build record this stage2 carried, if it carried one.
#     This stage2 carried tool-provenance.json, the receipt
#     scripts/recreate_bootstrap.py writes into a stage2 it builds. It is sealed
#     here as content: artifact_content_sha256 covers it.
#     CHECKED by promotion, on the candidate and again on this sealed copy:
#     it names reported_commit, and the hashes it records for THIS STAGE2'S OWN
#     FILES are each the sha256 of that file here. Promotion takes those to be
#     the hash in each of its tool rows and the hashes of the compiler, of the
#     compiler's rustc name, of the rustdoc name and of the proc-macro helper:
#     stage_receipt_files_verified hashes. It compares no other with a file.
#     NOT CHECKED: who wrote the receipt; any other hash the receipt records;
#     any file of this stage2 the receipt records no such hash for.
#     The other hashes, measured 2026-10-13 on the receipt of trust-f22fc270 (a
#     seed build): it holds 351 sha256 values and 21 of them are the ones
#     compared; among the other 330 are the seed's stage0 tree with that
#     tree's own lib/, seed archives, native tools and source snapshots.
#     The files without one: the recreator writes these hashes for executables
#     only, so nothing under this stage2's lib/ (the compiler's driver library,
#     the standard library) has one, nor has an executable outside those named.
#     NOT RE-DERIVED by promotion: its status and its lineage, i.e. which
#     stage0 the build started from. Those are the receipt's own statements;
#     `recreate_bootstrap.py --verify-stage-provenance`, in the build tree, is
#     what recomputes them. stage_receipt_recreator_argv is what the build
#     said it was started with; nothing can re-derive a command line. It is
#     shell-quoted in ASCII; a value in parentheses is promotion's own word.
#     So is the bare word not-recorded when it is the whole value: the receipt
#     holds no record of the arguments (it was written before the recreator
#     recorded them, or not by the recreator), whereas the one argument
#     not-recorded is written quoted, as 'not-recorded'.
#     THE LLVM this stage2 carries, stage_receipt_llvm*, is the receipt's own
#     statement as well, and promotion compares it with no file: a seal holds
#     no build directory. x.py rebuilds the in-tree LLVM when
#     HEAD:src/llvm-project moves from the tree recorded beside it, but it
#     keeps an LLVM that cannot say what it was built from (one built
#     before that record, whose own build header names no commit this
#     checkout has), and a change to src/bootstrap, src/version, the
#     bootstrap config or the native tools rebuilds none, so a reused build
#     directory can carry an LLVM built from other sources or with another
#     recipe. _identity=stated: the build could say which sources its
#     LLVM was built from. Either it watched build/<host>/llvm being built from
#     nothing (_provenance=built-in-this-run), or it reused one whose directory
#     held the record of such a build for the same LLVM sources, bootstrap
#     config and native tools, its installed files unchanged since
#     (_provenance=reused; _built_at_commit is the commit of that build).
#     _source_sha256 is one sha256 over the git ids of the LLVM inputs in the
#     source tree, _source_tree the id of src/llvm-project among them; both
#     are written for stage_receipt_llvm=in-tree only.
#     stage_receipt_llvm=external: this stage2 links an LLVM through the
#     recreator's --llvm-config, and its identity is NEVER stated. The build
#     did not watch that LLVM being built and has no record of such a build;
#     what the receipt binds of it is the llvm-config executable (path, sha256,
#     version) and its dylib closure, not the libraries it points at. Its
#     other four lines say not-recorded: the src/llvm-project of the source
#     tree is not what that LLVM was built from.
#     stage_receipt_llvm=unknown: the build could not tell which LLVM x.py
#     links, and its identity is NEVER stated. The bootstrap config x.py
#     obeys did not itself say (it names an llvm-config other than the
#     build's --llvm-config, or none where the build was given one; it has
#     an include key; it does not set llvm.download-ci-llvm = false), or it
#     could not be read, or the LLVM could not be observed or recorded; the
#     receipt's llvm_identity.reasons say which. Its other four lines say
#     not-recorded: neither the src/llvm-project of the source tree nor
#     anything in the build directory is known to be what this stage2 links.
#     CHECKED by promotion: the form of that record, and that it contradicts
#     neither itself nor this receipt. stage_receipt_status does NOT depend on
#     it: a receipt is internal-release-ready on its source and seed lineage
#     whether or not _identity=stated, and a seal is cut either way unless
#     promotion was run with --require-llvm-identity, which refuses anything
#     but stated. stage_receipt_llvm=not-recorded: the receipt holds no such
#     record (it was written before 2026-10-13, or not by the recreator), and
#     nothing in this file says which LLVM this stage2 carries.
stage_receipt=tool-provenance.json
TEXT
cat > "$WORK/section-f-without-a-receipt" <<'TEXT'
# (f) THE STAGE RECEIPT — the build record this stage2 carried, if it carried one.
#     None: this stage2 carried no tool-provenance.json, the receipt
#     scripts/recreate_bootstrap.py writes when it completes a Stage2+ build.
stage_receipt=absent
TEXT
says_section_f() { # <PROVENANCE> <with-a-receipt | without-a-receipt>
    section_f_of "$1" | cmp -s - "$WORK/section-f-$2"
}

# WHAT x.py DOES WITH THE IN-TREE LLVM, as bootstrap does it since its fix of
# 2026-10-13 (docs/KNOWN_HAZARDS.md, LLVM-STAMP-COMMITTED-1), in the words of
# the recreator's refusal: section (f) of a seal, promotion's usage and its
# --require-llvm-identity refusal each say it, and none says any more that
# x.py does not rebuild the in-tree LLVM for a committed change to it (all
# three did until 2026-10-14; a seal cut before then keeps that sentence in
# its PROVENANCE, which is never rewritten). Read with the comment marks and
# the line breaks taken out, so that neither check depends on where a text
# wraps. <file> <what the file is>
says_what_x_py_does_now() {
    local flat
    flat="$(sed 's/^#//' "$1" | tr '\n' ' ' | tr -s ' ')"
    [[ "$flat" == *"x.py rebuilds the in-tree LLVM when HEAD:src/llvm-project moves from the tree recorded beside it, but it keeps an LLVM that cannot say what it was built from (one built before that record, whose own build header names no commit this checkout has), and a change to src/bootstrap, src/version, the bootstrap config or the native tools rebuilds none, so a "*"reused build directory can carry an LLVM built from other sources or with another recipe."* ]] \
        || { cat "$1" >&2; fail "$2 does not say what x.py does with the in-tree LLVM since 2026-10-13"; }
    [[ "$flat" != *"not rebuild the in-tree LLVM for a committed change"* && "$flat" != *"not rebuild LLVM for a committed change"* ]] \
        || { cat "$1" >&2; fail "$2 still says that x.py does not rebuild the in-tree LLVM for a committed change to it"; }
}

# The form the strictest reader of a seal's PROVENANCE requires of every line
# (first-party/trust-mc scripts/development_seal.py: `key=value` with a value, at
# most 8192 characters), and what this change promises of the lines it adds:
# printable ASCII, the value at most 4096 characters. Stdin: the lines. awk, not
# `grep -E '{1,4096}'`: POSIX promises a repetition count only up to 255
# (RE_DUP_MAX), and a grep that refused the pattern would read as a pass.
lines_are_bounded_ascii() {
    LC_ALL=C awk '
        { eq = index($0, "="); key = substr($0, 1, eq - 1); value = substr($0, eq + 1)
          if (eq < 2 || key !~ /^[a-z0-9_]+$/ || length(value) < 1 || length(value) > 4096 || value ~ /[^ -~]/) bad = 1 }
        END { exit (NR == 0 || bad) ? 1 : 0 }'
}
printf 'stage_receipt=absent\ntool_start_gate=7/7 passed\n' | lines_are_bounded_ascii \
    || fail 'the line-form check refuses two good lines'
for bad_line in 'stage_receipt_recreator_argv=' 'stage_receipt_recreator_argv' "stage_receipt_recreator_argv=$(printf 'caf\303\251')" \
    "stage_receipt_recreator_argv=$(printf 'a\tb')" "stage_receipt_recreator_argv=$(printf '%04097d' 0)"; do
    ! printf 'stage_receipt=absent\n%s\n' "$bad_line" | lines_are_bounded_ascii \
        || fail "the line-form check accepts a bad line (${bad_line:0:60})"
done

# A stage2 with the receipt of its own build: the seal names it, line for line.
external_receipt_case() {
    # Product and promoter are separate. Its old reader deliberately refuses:
    # selected receipt validation must use the current promoter engine reader.
    git -c core.hooksPath=/dev/null clone -q --no-hardlinks "$FIXTURE_REPO" "$CASE/source"
    mv "$CASE/build" "$CASE/source/build"
    SRC="$CASE/source/build/test-host/stage2"
    printf '#!/usr/bin/env python3\nraise SystemExit("old Product reader must not execute")\n' \
        > "$CASE/source/scripts/lib/stage_receipt_provenance.py"
    write_stage_receipt "$SRC" llvm-built
    cp "$SRC/tool-provenance.json" "$CASE/accepted.json"
    ACCEPTED_SHA="$(shasum -a 256 "$CASE/accepted.json" | awk '{print $1}')"
    write_stage_receipt "$SRC" rejected
    cp "$SRC/tool-provenance.json" "$CASE/original-rejected.json"
    PROMOTE_OPTS=(--no-flip --require-llvm-identity --source-root "$CASE/source"
        --stage-provenance-receipt "$CASE/accepted.json" --stage-provenance-sha256 "$ACCEPTED_SHA")
}
new_case external-stage-receipt
external_receipt_case
run_promotion || { cat "$CASE/output" >&2; fail 'external accepted receipt promotion refused'; }
cmp "$SRC/tool-provenance.json" "$CASE/original-rejected.json" || fail 'original rejected receipt changed'
cmp "$SEAL/tool-provenance.json" "$CASE/accepted.json" || fail 'accepted receipt was not carried into the new seal'
grep -qx "stage_receipt_sha256=$ACCEPTED_SHA" "$SEAL/PROVENANCE" || fail 'sealed receipt SHA is not selected audit'
grep -qx 'stage_receipt_llvm_identity=stated' "$SEAL/PROVENANCE" || fail 'selected LLVM requirement was not evaluated'

new_case external-stage-receipt-wrong-hash
external_receipt_case
PROMOTE_OPTS=(--no-flip --source-root "$CASE/source" --stage-provenance-receipt "$CASE/accepted.json"
    --stage-provenance-sha256 "$(printf '%064d' 0)")
if run_promotion; then fail 'wrong external receipt hash accepted'; fi
grep -qF 'explicitly selected receipt sha256 differs' "$CASE/output" || { cat "$CASE/output" >&2; fail 'wrong hash refused for another cause'; }
[[ ! -e "$CASE/sealed" ]] || fail 'wrong external receipt copied a seal'

new_case external-stage-receipt-stale-tool
external_receipt_case
printf '\n# changed tool bytes, preserved CLI behavior\n' >> "$SRC/bin/ty"
if run_promotion; then fail 'external audit licensed changed stage tool'; fi
grep -qF 'for tool ty' "$CASE/output" || { cat "$CASE/output" >&2; fail 'stale tool refused for another cause'; }
[[ ! -e "$CASE/sealed" ]] || fail 'stale externally audited stage copied a seal'

for mode in --gate-only --provenance; do
    new_case "external-receipt-unused-${mode#--}"
    write_stage_receipt "$SRC"
    PROMOTE_OPTS=("$mode" --stage-provenance-receipt "$SRC/tool-provenance.json"
        --stage-provenance-sha256 "$(shasum -a 256 "$SRC/tool-provenance.json" | awk '{print $1}')")
    if run_promotion; then fail "$mode ignored an unused external selector"; fi
    grep -qF -- "$mode does not use --stage-provenance-receipt" "$CASE/output" \
        || { cat "$CASE/output" >&2; fail 'unused selector refused for another cause'; }
done
unset PROMOTE_OPTS

new_case stage-receipt-recorded
write_trust_miri "$SRC/bin/trust-miri" ok
write_stage_receipt "$SRC"
PROMOTE_OPTS=(--no-flip)
run_promotion || { cat "$CASE/output" >&2; fail 'a stage2 carrying its own receipt was refused'; }
cmp "$SRC/tool-provenance.json" "$SEAL/tool-provenance.json" || fail 'the seal does not carry the stage receipt'
[[ "$(grep '^stage_receipt' "$SEAL/PROVENANCE")" == "$(stage_receipt_lines_of "$SEAL/tool-provenance.json" "$SEED_ARGV")" ]] \
    || { cat "$SEAL/PROVENANCE" >&2; fail 'PROVENANCE does not say what the sealed receipt says'; }
for line in 'stage_receipt_schema=trust.stage-tool-provenance.v2' 'stage_receipt_status=internal-release-ready' \
    'stage_receipt_lineage_mode=seed' 'stage_receipt_trust_from_trust=true' \
    'stage_receipt_seed_materialization=fresh-from-validated-archives' \
    "stage_receipt_sha256=$(shasum -a 256 "$SEAL/tool-provenance.json" | awk '{print $1}')" \
    "stage_receipt_recreator_argv=$SEED_ARGV"; do
    grep -qxF "$line" "$SEAL/PROVENANCE" || fail "PROVENANCE lacks $line"
done
grep -qF "==> stage receipt: tool-provenance.json names this stage2's commit and files (status internal-release-ready, lineage mode seed, " "$CASE/output" \
    || fail 'promotion did not say it checked the stage receipt'
# The seal says what that check reaches: the hashes the receipt records for this
# stage2's own files, which are executables. It says what it does not reach: the
# receipt's other hashes (the seed's own tree, lib/ and all, among them) and this
# stage2's lib/. It does not say who wrote the file. The whole section, word for
# word; the three lines after it are looked for by themselves so that a failure
# names the statement that went.
says_section_f "$SEAL/PROVENANCE" with-a-receipt \
    || { section_f_of "$SEAL/PROVENANCE" | diff "$WORK/section-f-with-a-receipt" - >&2 || true; fail 'section (f) of PROVENANCE is not, word for word, the text this test holds it to'; }
says_what_x_py_does_now "$SEAL/PROVENANCE" 'the PROVENANCE of a seal with a stage receipt'
grep -qxF '#     NOT CHECKED: who wrote the receipt; any other hash the receipt records;' "$SEAL/PROVENANCE" \
    && grep -qxF '#     any file of this stage2 the receipt records no such hash for.' "$SEAL/PROVENANCE" \
    && grep -qxF '#     only, so nothing under this stage2'"'"'s lib/ (the compiler'"'"'s driver library,' "$SEAL/PROVENANCE" \
    || fail 'PROVENANCE does not say what the receipt check does not reach'
! grep -qF 'scripts/recreate_bootstrap.py wrote' "$SEAL/PROVENANCE" \
    || fail 'PROVENANCE states as fact who wrote the stage receipt'
# Every line this change adds keeps the form the strictest reader of PROVENANCE
# requires of every line (first-party/trust-mc scripts/development_seal.py:
# `key=value` with a value, no key twice, at most 8192 characters), in ASCII.
new_lines="$(grep -E '^(stage_receipt|tool_start_gate)' "$SEAL/PROVENANCE")"
# The fixture receipt is one written before 2026-10-13 in this respect: it holds no
# `llvm_identity`, as the three sealed on 2026-10-12 do not, and the seal says so.
grep -qx 'stage_receipt_llvm=not-recorded' "$SEAL/PROVENANCE" || fail 'a seal whose receipt records no LLVM does not say stage_receipt_llvm=not-recorded'
[[ "$(grep -c '^stage_receipt_llvm' "$SEAL/PROVENANCE")" -eq 1 ]] || fail 'a seal whose receipt records no LLVM says more of it than not-recorded'
[[ "$(printf '%s\n' "$new_lines" | wc -l | tr -d ' ')" -eq 13 ]] || fail 'a seal with a receipt does not add thirteen lines'
[[ -z "$(printf '%s\n' "$new_lines" | cut -d= -f1 | sort | uniq -d)" ]] || fail 'a seal repeats one of the new keys'
printf '%s\n' "$new_lines" | lines_are_bounded_ascii \
    || fail 'a new PROVENANCE line is not key=value in printable ASCII with a bounded value'
# No staircase record was given, so stage0_lineage keeps its meaning and its
# value; only its explanation changes, and points at the receipt.
grep -qx 'stage0_lineage=absent' "$SEAL/PROVENANCE" || fail 'a stage receipt changed what stage0_lineage says'
grep -qF 'seal does say about its stage0 is the stage receipt, (f) below.' "$SEAL/PROVENANCE" \
    || fail 'the absent staircase record does not point at the stage receipt'
! grep -qF 'else on this path observes stage0' "$SEAL/PROVENANCE" \
    || fail 'PROVENANCE says nothing observes stage0 beside a receipt that does'
# The tool-start gate's result, as the run on the sealed copy printed it.
grep -qx 'tool_start_gate=7/7 passed' "$SEAL/PROVENANCE" || fail 'PROVENANCE does not record the tool-start gate'
grep -qx 'tool_start_gate_rows=tippy-driver.clean tippy-driver.lint tippy.frontend tippy.frontend-lint trust-miri.session trustdoc.session trustfmt.format' \
    "$SEAL/PROVENANCE" || fail 'PROVENANCE does not name the tool-start rows that passed'
grep -qx 'tool_start_gate_not_shipped=none' "$SEAL/PROVENANCE" || fail 'PROVENANCE does not say every tool-start row was started'
[[ "$(readlink "$CASE/rustup/toolchains/trust")" == "$CASE/previous" ]] || fail 'the stage-receipt no-flip moved the channel'
RECORDED_SEAL="$SEAL"
unset PROMOTE_OPTS

# A stage2 with no receipt (a plain x.py build) seals as before and says so:
# the staircase explanation keeps the words it had. The first case of this file
# sealed exactly such a stage2, so nothing is promoted again for this one.
new_case stage-receipt-absent
PLAIN_SEAL="$WORK/complete/sealed/trust-${COMMIT:0:8}"
[[ "$(grep '^stage_receipt' "$PLAIN_SEAL/PROVENANCE")" == 'stage_receipt=absent' ]] \
    || fail 'a seal without a stage receipt must say exactly stage_receipt=absent'
# What it says of the receipt it lacks is when the recreator writes one, and not
# that this stage2 was built some other way: nothing here observed its build.
says_section_f "$PLAIN_SEAL/PROVENANCE" without-a-receipt \
    || { section_f_of "$PLAIN_SEAL/PROVENANCE" | diff "$WORK/section-f-without-a-receipt" - >&2 || true; fail 'section (f) of a seal without a stage receipt is not, word for word, the text this test holds it to'; }
! grep -qF 'was not built by' "$PLAIN_SEAL/PROVENANCE" \
    || fail 'a seal without a stage receipt states as fact how its stage2 was built'
grep -qxF '#     Not recorded: promote was given no --lineage record, and nothing' "$PLAIN_SEAL/PROVENANCE" \
    && grep -qxF '#     else on this path observes stage0. Absence is not evidence either way.' "$PLAIN_SEAL/PROVENANCE" \
    && grep -qx 'stage0_lineage=absent' "$PLAIN_SEAL/PROVENANCE" \
    || fail 'a seal without a stage receipt lost the staircase explanation it had'
grep -qF '==> stage receipt: none in this stage2' "$WORK/complete/output" || fail 'promotion did not say the stage2 has no receipt'
[[ "$(grep '^tool_start_gate' "$PLAIN_SEAL/PROVENANCE")" == \
    'tool_start_gate=6/6 passed (1 not shipped, not started)'$'\n''tool_start_gate_rows=tippy-driver.clean tippy-driver.lint tippy.frontend tippy.frontend-lint trustdoc.session trustfmt.format'$'\n''tool_start_gate_not_shipped=trust-miri.session' ]] \
    || { cat "$PLAIN_SEAL/PROVENANCE" >&2; fail 'PROVENANCE does not record six starts and the row that was not shipped'; }

# A receipt that is present and cannot be recorded is a REFUSAL, before the
# first `cp`: the seal would otherwise quote another build's lineage as its own.
assert_receipt_refusal() { # <reason the refusal must carry>
    if run_promotion; then fail "$(basename "$CASE") was promoted"; fi
    grep -qF "REFUSED: $SRC/tool-provenance.json is a stage receipt that cannot be recorded" "$CASE/output" \
        || { cat "$CASE/output" >&2; fail "unexpected refusal for $(basename "$CASE")"; }
    grep -qF "$1" "$CASE/output" || { cat "$CASE/output" >&2; fail "$(basename "$CASE") was refused for the wrong reason"; }
    [[ ! -e "$CASE/sealed" ]] || fail "$(basename "$CASE"): a stage2 with an unusable receipt was copied"
    [[ "$(readlink "$CASE/rustup/toolchains/trust")" == "$CASE/previous" ]] || fail 'a receipt refusal moved the channel'
    [[ ! -e "$CASE/sealed/trust-current" && ! -L "$CASE/sealed/trust-current" ]] || fail 'a receipt refusal created trust-current'
}

new_case stage-receipt-not-json
write_stage_receipt "$SRC" not-json
assert_receipt_refusal 'is not a receipt to record: it is not JSON'

# The stale receipt: the stage2 changed after its receipt was written.
new_case stage-receipt-for-other-tools
write_stage_receipt "$SRC"
printf '# rebuilt after the receipt was written\n' >> "$SRC/bin/ty"
assert_receipt_refusal "for tool ty (build/test-host/stage2/bin/ty); the file in $SRC has $(shasum -a 256 "$SRC/bin/ty" | awk '{print $1}')"

# The candidate's receipt was this stage2's; the sealed copy's is another file.
new_case stage-receipt-changes-in-the-copy
write_stage_receipt "$SRC"
if run_promotion receipt; then fail 'a seal whose receipt changed in the copy was promoted'; fi
grep -qF 'the stage receipt changed while it was being sealed' "$CASE/output" \
    || { cat "$CASE/output" >&2; fail 'unexpected refusal for stage-receipt-changes-in-the-copy'; }
[[ ! -e "$SEAL/PROVENANCE" ]] || fail 'a seal whose receipt changed in the copy was given a PROVENANCE'
[[ "$(readlink "$CASE/rustup/toolchains/trust")" == "$CASE/previous" ]] || fail 'a receipt that changed in the copy moved the channel'
[[ ! -e "$CASE/sealed/trust-current" && ! -L "$CASE/sealed/trust-current" ]] || fail 'a receipt that changed in the copy created trust-current'

# The dry run (`--provenance` on a stage2 that is not sealed) asks the same
# question and writes nothing. Each row is one KIND of receipt that is not
# recordable: not strict JSON, one the recreator itself rejected (it writes a
# receipt for a stage it refuses too, and exits nonzero), fields that
# contradict each other, another build's commit, a path out of the stage, a
# file the seal could only point at, a recorded argument that would write a
# second line into PROVENANCE, and a recorded argument holding either end of
# each of the three code point ranges the reader refuses (U+0000-001F,
# U+007F-009F, U+D800-DFFF), under the python3 promotion itself runs. Every
# single check of the reader has its row in scripts/tests/recreate_bootstrap_test.py
# (test_promotion_refuses_a_receipt_it_must_not_record), on the receipt the
# recreator really writes.
PROMOTE_OPTS=(--provenance)
assert_dry_run_wrote_nothing() {
    [[ ! -e "$CASE/sealed" ]] || fail '--provenance sealed something'
    [[ "$(readlink "$CASE/rustup/toolchains/trust")" == "$CASE/previous" ]] || fail '--provenance moved the channel'
    [[ -z "$(find "$SRC" -newer "$CASE/before" 2>/dev/null)" ]] || fail '--provenance wrote into the stage2 it was asked about'
}
while IFS='|' read -r variant reason <&3; do
    new_case "stage-receipt-$variant"
    if [[ "$variant" == symlink ]]; then
        write_stage_receipt "$SRC"
        mv "$SRC/tool-provenance.json" "$CASE/receipt-elsewhere.json"
        ln -s "$CASE/receipt-elsewhere.json" "$SRC/tool-provenance.json"
    else
        write_stage_receipt "$SRC" "$variant"
    fi
    touch "$CASE/before"
    if run_promotion; then cat "$CASE/output" >&2; fail "the dry run accepted the receipt of $(basename "$CASE")"; fi
    grep -qF "$SRC carries a stage receipt promotion would REFUSE to seal" "$CASE/output" \
        || { cat "$CASE/output" >&2; fail "unexpected dry-run refusal for $(basename "$CASE")"; }
    grep -qF "$reason" "$CASE/output" || { cat "$CASE/output" >&2; fail "$(basename "$CASE") was refused for the wrong reason"; }
    # A key and `=`: the refusal itself is a line beginning `stage_receipt_provenance:`.
    ! grep -qE '^stage_receipt(_[a-z_]+)?=' "$CASE/output" || fail "$(basename "$CASE"): a refused receipt still printed a line to record"
    assert_dry_run_wrote_nothing
done 3<<'ROWS'
repeated-key|it repeats the key 'status'
rejected|its own writer rejected this stage (status rejected: public tool ty does not match its x.py producer
release-without-fresh-seed|status is internal-release-ready, which needs a freshly materialized Trust seed, while its lineage says mode seed, trust_from_trust true, seed materialization preexisting-unproven
foreign-commit|it names source commit '0000000000000000000000000000000000000000'; this tree's compiler reports
path-outside-stage|the path of tool ty is not a plain relative path: 'build/test-host/stage2/bin/../../stage1/bin/ty'
symlink|it is not a regular file
argv-injects-a-line|recreator_invocation.argv holds a control or unprintable character
argv-holds-U+0000|recreator_invocation.argv holds a control or unprintable character
argv-holds-U+001F|recreator_invocation.argv holds a control or unprintable character
argv-holds-U+007F|recreator_invocation.argv holds a control or unprintable character
argv-holds-U+009F|recreator_invocation.argv holds a control or unprintable character
argv-holds-U+D800|recreator_invocation.argv holds a control or unprintable character
argv-holds-U+DFFF|recreator_invocation.argv holds a control or unprintable character
llvm-not-an-object|llvm_identity is not an object
llvm-record-for-other-sources|llvm_identity's build record is for another source identity than this receipt's
llvm-external-stated|llvm_identity states the identity of an external LLVM: which sources an LLVM linked through --llvm-config was built from is never established; llvm_identity of an external LLVM carries a source identity: this checkout's LLVM sources do not describe an LLVM linked through --llvm-config
ROWS

# A receipt as the recreator wrote it until 2026-10-12, with no command line:
# the dry run prints the lines a seal would record, and says the argv is not there.
new_case stage-receipt-dry-run
write_stage_receipt "$SRC" no-argv
touch "$CASE/before"
run_promotion || { cat "$CASE/output" >&2; fail 'the dry run refused a stage2 carrying its own receipt'; }
[[ "$(grep '^stage_receipt' "$CASE/output")" == "$(stage_receipt_lines_of "$SRC/tool-provenance.json" not-recorded)" ]] \
    || { cat "$CASE/output" >&2; fail 'the dry run did not print the stage-receipt lines a seal would record'; }
grep -q '^artifact_content_sha256=' "$CASE/output" || fail 'the dry run lost the content identity'
assert_dry_run_wrote_nothing

# A development build from stock rust: not Trust-from-Trust, no seed, and an
# argument with a space in it is quoted so the line reads back as one command.
new_case stage-receipt-dry-run-genesis
write_stage_receipt "$SRC" genesis
touch "$CASE/before"
run_promotion || { cat "$CASE/output" >&2; fail 'the dry run refused a genesis receipt'; }
[[ "$(grep '^stage_receipt' "$CASE/output")" == \
    "$(stage_receipt_lines_of "$SRC/tool-provenance.json" "--genesis --llvm-config '/opt/llvm 22/bin/llvm-config'")" ]] \
    || { cat "$CASE/output" >&2; fail 'the dry run misread a genesis receipt'; }
for line in 'stage_receipt_status=candidate-ready' 'stage_receipt_lineage_mode=genesis' \
    'stage_receipt_trust_from_trust=false' 'stage_receipt_seed_materialization=not-applicable'; do
    grep -qxF "$line" "$CASE/output" || fail "the dry run of a genesis receipt lacks $line"
done
assert_dry_run_wrote_nothing

# The other receipts the recreator writes, and the command lines a line cannot
# hold as they are. `$argv` is what the line must say; the rest is read from the
# receipt by this test. A lineage that is Trust-from-Trust without being a seed
# (atpkg) is not printed as one; a public release is not printed as an internal
# one; an argument with a non-ASCII character is written in ASCII (its UTF-8
# bytes in the shell's $'...' form) whatever Unicode the python3 on PATH knows;
# arguments too long for a line are pointed at, not cut; and the reader's own
# word `not-recorded`, given as an argument, is quoted so it stays an argument.
# The length that counts is the WRITTEN one: 1100 e-acute are 2200 bytes as
# given and 8803 characters as written, so they are pointed at too. And the
# first code point outside each refused range is recorded, with code points a
# wider rule would refuse (U+200B, the bidi isolates, U+FDD0 and U+FDEF, two
# tag characters, U+10FFFF): promotion must not refuse what the recreator took.
argv_reads_back() { # <receipt> <recorded value>: this shell reads the line back as the receipt's arguments
    local -a words
    eval "words=($2)"
    "$PYTHON_BIN" - "$1" "${words[@]}" <<'PY'
import json, os, sys
recorded = json.load(open(sys.argv[1], encoding="utf-8"))["recreator_invocation"]["argv"]
sys.exit(0 if [os.fsencode(word) for word in sys.argv[2:]] == [word.encode("utf-8") for word in recorded] else 1)
PY
}
while IFS='|' read -r variant status mode materialization argv <&3; do
    new_case "stage-receipt-dry-run-$variant"
    write_stage_receipt "$SRC" "$variant"
    touch "$CASE/before"
    run_promotion || { cat "$CASE/output" >&2; fail "the dry run refused the receipt of $(basename "$CASE")"; }
    [[ "$(grep '^stage_receipt' "$CASE/output")" == "$(stage_receipt_lines_of "$SRC/tool-provenance.json" "$argv")" ]] \
        || { cat "$CASE/output" >&2; fail "the dry run misread the receipt of $(basename "$CASE")"; }
    for line in "stage_receipt_status=$status" "stage_receipt_lineage_mode=$mode" 'stage_receipt_trust_from_trust=true' \
        "stage_receipt_seed_materialization=$materialization" "stage_receipt_recreator_argv=$argv"; do
        grep -qxF -- "$line" "$CASE/output" || fail "the dry run of $(basename "$CASE") lacks $line"
    done
    grep '^stage_receipt' "$CASE/output" | lines_are_bounded_ascii \
        || fail "$(basename "$CASE"): a stage-receipt line is not printable ASCII with a bounded value"
    if [[ "$argv" != '('* ]]; then
        argv_reads_back "$SRC/tool-provenance.json" "$argv" \
            || fail "$(basename "$CASE"): the recorded command line does not read back as the receipt's arguments"
    fi
    assert_dry_run_wrote_nothing
done 3<<'ROWS'
atpkg|candidate-ready|atpkg|not-applicable|--stage 2 --no-register
release-ready|release-ready|seed|fresh-from-validated-archives|--stage 2 --require-seed --fresh-seed --no-register
non-ascii-argument|internal-release-ready|seed|fresh-from-validated-archives|--stage 2 --llvm-config $'/opt/llvm-\xf0\x9f\xab\xa8 22/it\'s/b\\in/llvm-config'
long-arguments|internal-release-ready|seed|fresh-from-validated-archives|(not quoted here: 4135 characters when quoted, more than 4096; read recreator_invocation.argv in tool-provenance.json)
argument-not-recorded|internal-release-ready|seed|fresh-from-validated-archives|'not-recorded'
expanding-arguments|internal-release-ready|seed|fresh-from-validated-archives|(not quoted here: 8803 characters when quoted, more than 4096; read recreator_invocation.argv in tool-provenance.json)
code-points-outside-the-refused-ranges|internal-release-ready|seed|fresh-from-validated-archives|' ~' $'\xc2\xa0' $'\xed\x9f\xbf\xee\x80\x80' $'\xe2\x80\x8b' $'\xe2\x81\xa6\xe2\x81\xa9' $'\xef\xb7\x90\xef\xb7\xaf' $'\xf3\xa0\x80\x80\xf3\xa0\x81\xbf' $'\xf4\x8f\xbf\xbf'
ROWS

# THE LLVM A STAGE CARRIES. Two of the three seals of 2026-10-12 carried an LLVM
# built at another commit, in a reused build directory (x.py did not then rebuild
# LLVM for a committed change to it), and nothing sealed said so. The recreator
# now records it and the seal names it: reused on the record of the build that
# made it (the commit that build ran at, not this stage2's); reused with nothing
# that says what it was built from, which is said as it is under the status word
# the receipt's lineage earned (the word does not depend on the LLVM, and such a
# stage2 is sealed unless promotion is asked to require the identity, below);
# and an external LLVM (the recreator's --llvm-config), which is NEVER stated:
# the build did not watch it being built and binds the llvm-config executable,
# not what it points at. It has no in-tree output to fingerprint, and the
# checkout's own src/llvm-project is not what it was built from, so no id of
# that tree stands beside it (until the re-read of 2026-10-13 this row said
# `stated`, with the tree id `3333...` on the line below it). And an LLVM of
# unknown mode (the config x.py obeys does not say which LLVM it links): never
# stated, and no id of the checkout beside it, also where the receipt holds
# them (the recreator wrote them from 381ac1ea0d until the follow-up of
# 2026-10-13; until then this row's seal said `3333...` too). `$tree`,
# `$built_at` and `$output` are what the lines must say; the rest is read
# from the receipt by this test.
while IFS='|' read -r variant status mode identity provenance tree built_at output <&3; do
    new_case "stage-receipt-dry-run-$variant"
    write_stage_receipt "$SRC" "$variant"
    touch "$CASE/before"
    run_promotion || { cat "$CASE/output" >&2; fail "the dry run refused the receipt of $(basename "$CASE")"; }
    [[ "$(grep '^stage_receipt' "$CASE/output")" == "$(stage_receipt_lines_of "$SRC/tool-provenance.json" "$SEED_ARGV")" ]] \
        || { cat "$CASE/output" >&2; fail "the dry run misread the receipt of $(basename "$CASE")"; }
    for line in "stage_receipt_status=$status" "stage_receipt_llvm=$mode" "stage_receipt_llvm_identity=$identity" \
        "stage_receipt_llvm_provenance=$provenance" "stage_receipt_llvm_source_tree=$tree" \
        "stage_receipt_llvm_built_at_commit=$built_at" "stage_receipt_llvm_output_sha256=$output"; do
        grep -qxF -- "$line" "$CASE/output" || { cat "$CASE/output" >&2; fail "the dry run of $(basename "$CASE") lacks $line"; }
    done
    [[ "$(grep -c '^stage_receipt_llvm' "$CASE/output")" -eq 7 ]] || fail "$(basename "$CASE"): a recorded LLVM is not seven lines"
    if [[ "$mode" != in-tree ]]; then
        grep -qxF 'stage_receipt_llvm_source_sha256=not-recorded' "$CASE/output" \
            || { cat "$CASE/output" >&2; fail "an LLVM of mode $mode is recorded with a source identity"; }
        ! grep -q '^stage_receipt_llvm.*=3333333333333333333333333333333333333333$' "$CASE/output" \
            || fail "the checkout's src/llvm-project id stands beside an LLVM of mode $mode"
    else
        grep -qE '^stage_receipt_llvm_source_sha256=[0-9a-f]{64}$' "$CASE/output" \
            || fail "$(basename "$CASE"): an in-tree LLVM is recorded without its source identity"
    fi
    grep '^stage_receipt' "$CASE/output" | lines_are_bounded_ascii \
        || fail "$(basename "$CASE"): a stage-receipt line is not printable ASCII with a bounded value"
    assert_dry_run_wrote_nothing
done 3<<'ROWS'
llvm-reused|internal-release-ready|in-tree|stated|reused|3333333333333333333333333333333333333333|2222222222222222222222222222222222222222|6666666666666666666666666666666666666666666666666666666666666666
llvm-not-stated|internal-release-ready|in-tree|not-stated|reused|3333333333333333333333333333333333333333|not-recorded|6666666666666666666666666666666666666666666666666666666666666666
llvm-external|internal-release-ready|external|not-stated|external|not-recorded|not-recorded|not-recorded
llvm-unknown|internal-release-ready|unknown|not-stated|unknown|not-recorded|not-recorded|not-recorded
llvm-unknown-with-ids|internal-release-ready|unknown|not-stated|unknown|not-recorded|not-recorded|not-recorded
ROWS
unset PROMOTE_OPTS

# A seal of a stage2 whose receipt says its LLVM was built in the run: the seven
# lines are in PROVENANCE as the sealed receipt has them, between the files that
# were compared and the command line, and section (f) explains them in the seal.
new_case stage-receipt-llvm-recorded
write_trust_miri "$SRC/bin/trust-miri" ok
write_stage_receipt "$SRC" llvm-built
PROMOTE_OPTS=(--no-flip)
run_promotion || { cat "$CASE/output" >&2; fail 'a stage2 whose receipt records its LLVM was refused'; }
cmp "$SRC/tool-provenance.json" "$SEAL/tool-provenance.json" || fail 'the seal does not carry the receipt that records its LLVM'
[[ "$(grep '^stage_receipt' "$SEAL/PROVENANCE")" == "$(stage_receipt_lines_of "$SEAL/tool-provenance.json" "$SEED_ARGV")" ]] \
    || { cat "$SEAL/PROVENANCE" >&2; fail 'PROVENANCE does not say of the LLVM what the sealed receipt says'; }
for line in 'stage_receipt_llvm=in-tree' 'stage_receipt_llvm_identity=stated' 'stage_receipt_llvm_provenance=built-in-this-run' \
    'stage_receipt_llvm_source_tree=3333333333333333333333333333333333333333' "stage_receipt_llvm_built_at_commit=$COMMIT" \
    'stage_receipt_llvm_output_sha256=6666666666666666666666666666666666666666666666666666666666666666'; do
    grep -qxF "$line" "$SEAL/PROVENANCE" || fail "PROVENANCE lacks $line"
done
grep -qE '^stage_receipt_llvm_source_sha256=[0-9a-f]{64}$' "$SEAL/PROVENANCE" || fail 'PROVENANCE lacks the LLVM source identity'
[[ "$(grep -A8 '^stage_receipt_files_verified=' "$SEAL/PROVENANCE" | cut -d= -f1 | tr '\n' ' ')" == \
    'stage_receipt_files_verified stage_receipt_llvm stage_receipt_llvm_identity stage_receipt_llvm_provenance stage_receipt_llvm_source_sha256 stage_receipt_llvm_source_tree stage_receipt_llvm_built_at_commit stage_receipt_llvm_output_sha256 stage_receipt_recreator_argv ' ]] \
    || fail 'the LLVM lines are not between the compared files and the command line'
llvm_seal_lines="$(grep -E '^(stage_receipt|tool_start_gate)' "$SEAL/PROVENANCE")"
[[ "$(printf '%s\n' "$llvm_seal_lines" | wc -l | tr -d ' ')" -eq 19 ]] || fail 'a seal whose receipt records its LLVM does not add nineteen lines'
[[ -z "$(printf '%s\n' "$llvm_seal_lines" | cut -d= -f1 | sort | uniq -d)" ]] || fail 'a seal that records its LLVM repeats a key'
printf '%s\n' "$llvm_seal_lines" | lines_are_bounded_ascii \
    || fail 'an LLVM line of PROVENANCE is not key=value in printable ASCII with a bounded value'
says_section_f "$SEAL/PROVENANCE" with-a-receipt \
    || fail 'section (f) of the seal that records its LLVM is not, word for word, the text this test holds it to'
grep -qxF '#     neither itself nor this receipt. stage_receipt_status does NOT depend on' "$SEAL/PROVENANCE" \
    && grep -qxF '#     promotion was run with --require-llvm-identity, which refuses anything' "$SEAL/PROVENANCE" \
    && grep -qxF '#     statement as well, and promotion compares it with no file: a seal holds' "$SEAL/PROVENANCE" \
    || fail 'PROVENANCE does not say what promotion checked of the LLVM record and what it did not'
[[ "$(readlink "$CASE/rustup/toolchains/trust")" == "$CASE/previous" ]] || fail 'the LLVM-record no-flip moved the channel'
LLVM_STATED_SEAL="$SEAL"
unset PROMOTE_OPTS

# REQUIRING THE IDENTITY IS A FLAG OF ITS OWN. By default a stage2 is sealed
# whatever its receipt says of its LLVM (other machines seal every day from
# build directories whose LLVM nobody recorded, and the seal says so). A seal
# that must not carry an LLVM of unstated origin is cut with
# --require-llvm-identity: it refuses, before the first `cp`, a stage2 with no
# receipt, a receipt with no LLVM record, and a record that does not state the
# identity, and says how to build one that does.
assert_llvm_identity_refusal() { # <reason the refusal must carry>
    if run_promotion; then fail "$(basename "$CASE") was promoted"; fi
    grep -qF 'REFUSED (--require-llvm-identity): this stage2 does not state which LLVM it carries (the reason is above)' "$CASE/output" \
        || { cat "$CASE/output" >&2; fail "unexpected refusal for $(basename "$CASE")"; }
    grep -qF "stage_receipt_provenance: $SRC does not state which LLVM it carries: $1" "$CASE/output" \
        || { cat "$CASE/output" >&2; fail "$(basename "$CASE") was refused for the wrong reason"; }
    grep -qF "cd $FIXTURE_REPO && python3 scripts/recreate_bootstrap.py --stage 2 --require-seed --fresh-seed --no-register --require-llvm-identity" "$CASE/output" \
        && grep -qF "scripts/promote-toolchain.sh --provenance --require-llvm-identity $SRC" "$CASE/output" \
        && grep -qF 'Seal it without the claim: drop --require-llvm-identity.' "$CASE/output" \
        || { cat "$CASE/output" >&2; fail "the refusal of $(basename "$CASE") does not carry its commands"; }
    says_what_x_py_does_now "$CASE/output" "the refusal of $(basename "$CASE")"
    [[ ! -e "$CASE/sealed" ]] || fail "$(basename "$CASE"): a stage2 that does not state its LLVM was copied"
    [[ "$(readlink "$CASE/rustup/toolchains/trust")" == "$CASE/previous" ]] || fail 'an LLVM-identity refusal moved the channel'
    [[ ! -e "$CASE/sealed/trust-current" && ! -L "$CASE/sealed/trust-current" ]] || fail 'an LLVM-identity refusal created trust-current'
}
PROMOTE_OPTS=(--no-flip --require-llvm-identity)
new_case require-llvm-identity-not-stated
write_stage_receipt "$SRC" llvm-not-stated
assert_llvm_identity_refusal 'its tool-provenance.json says the identity is not stated (mode in-tree, provenance reused): build/test-host/llvm was reused, and it holds no build record'
# The receipt of each of the three seals of 2026-10-12, in this respect.
new_case require-llvm-identity-not-recorded
write_stage_receipt "$SRC"
assert_llvm_identity_refusal 'its tool-provenance.json holds no llvm_identity record: it was written by a recreator from before 2026-10-13'
# A plain x.py build.
new_case require-llvm-identity-no-receipt
assert_llvm_identity_refusal 'it carries no tool-provenance.json: no build-time stage evidence was recorded, or the receipt was removed'
# A stage2 that links an LLVM through the recreator's --llvm-config. Until the
# re-read of 2026-10-13 its receipt said `stated` (on the hash of the
# llvm-config executable alone) and this flag sealed it; such an LLVM is never
# stated, and the refusal says what the claim needs.
new_case require-llvm-identity-external
write_stage_receipt "$SRC" llvm-external
assert_llvm_identity_refusal 'its tool-provenance.json says the identity is not stated (mode external, provenance external): the stage links an external LLVM through --llvm-config'
grep -qF 'never states an LLVM linked through --llvm-config (mode external): for' "$CASE/output" \
    && grep -qF 'that claim the stage must be built without --llvm-config.' "$CASE/output" \
    || { cat "$CASE/output" >&2; fail 'the refusal of an external LLVM does not say what the claim needs'; }
# A receipt that cannot be recorded at all stays that refusal.
new_case require-llvm-identity-unusable-receipt
write_stage_receipt "$SRC" llvm-not-an-object
assert_receipt_refusal 'llvm_identity is not an object'

# A stage2 that states it is sealed, and promotion says that it asked: built in
# the run, and reused on the record of the build that made it.
for variant in llvm-built llvm-reused; do
    new_case "require-llvm-identity-$variant"
    write_stage_receipt "$SRC" "$variant"
    run_promotion || { cat "$CASE/output" >&2; fail "--require-llvm-identity refused a stage2 whose receipt states its LLVM ($variant)"; }
    grep -qxF '==> LLVM identity: stated by the stage receipt (--require-llvm-identity)' "$CASE/output" \
        || { cat "$CASE/output" >&2; fail 'promotion did not say it required the LLVM identity'; }
    grep -qx 'stage_receipt_llvm_identity=stated' "$SEAL/PROVENANCE" || fail "the seal of $variant does not say stage_receipt_llvm_identity=stated"
    [[ "$(readlink "$CASE/rustup/toolchains/trust")" == "$CASE/previous" ]] || fail 'the --require-llvm-identity no-flip moved the channel'
done

# WITHOUT THE FLAG the stage2 the first case refused is sealed, as it was before
# the record existed, and says what its receipt says. --require-provenance, which
# seals are cut with today, does NOT imply the flag: it keeps its meaning.
new_case llvm-not-stated-is-sealed-unless-asked
write_stage_receipt "$SRC" llvm-not-stated
# --require-provenance needs the stamp of a build from a CLEAN checkout, and
# earlier cases left this fixture checkout edited (frozen-sources-and-modes
# changed two tracked sources, unrelated-helper-build left build/). It is put
# at its commit for this one promotion and then back as those cases left it.
mkdir "$CASE/checkout-as-it-was"
cp "$FIXTURE_REPO/library/fixture.rs" "$CASE/checkout-as-it-was/library-fixture.rs"
cp "$FIXTURE_REPO/compiler/fixture.rs" "$CASE/checkout-as-it-was/compiler-fixture.rs"
[[ ! -e "$FIXTURE_REPO/build" ]] || mv "$FIXTURE_REPO/build" "$CASE/checkout-as-it-was/build"
git -C "$FIXTURE_REPO" checkout -q -- library/fixture.rs compiler/fixture.rs
[[ -z "$(git -C "$FIXTURE_REPO" status --porcelain)" ]] || fail 'the fixture checkout is not at its commit for a completed stamp'
write_completed_stamp
PROMOTE_OPTS=(--no-flip --require-provenance)
if run_promotion; then sealed_unasked=1; else sealed_unasked=0; fi
cp "$CASE/checkout-as-it-was/library-fixture.rs" "$FIXTURE_REPO/library/fixture.rs"
cp "$CASE/checkout-as-it-was/compiler-fixture.rs" "$FIXTURE_REPO/compiler/fixture.rs"
[[ ! -e "$CASE/checkout-as-it-was/build" ]] || mv "$CASE/checkout-as-it-was/build" "$FIXTURE_REPO/build"
[[ "$sealed_unasked" -eq 1 ]] || { cat "$CASE/output" >&2; fail 'a stage2 whose LLVM identity is not stated was refused without --require-llvm-identity'; }
grep -q '^provenance_class=BUILD-STAMPED-CLEAN$' "$SEAL/PROVENANCE" \
    || { cat "$CASE/output" >&2; fail 'the --require-provenance seal of a stage2 whose LLVM is not stated is not a stamped clean one'; }
grep -qx 'stage_receipt_status=internal-release-ready' "$SEAL/PROVENANCE" \
    && grep -qx 'stage_receipt_llvm_identity=not-stated' "$SEAL/PROVENANCE" \
    && grep -qx 'stage_receipt_llvm_provenance=reused' "$SEAL/PROVENANCE" \
    && grep -qx 'stage_receipt_llvm_built_at_commit=not-recorded' "$SEAL/PROVENANCE" \
    || { cat "$SEAL/PROVENANCE" >&2; fail 'the seal of a stage2 whose LLVM is not stated does not say so under its own status word'; }
! grep -qF 'LLVM identity: stated' "$CASE/output" || fail 'promotion claims to have required an identity it was not asked to require'
LLVM_UNSTATED_SEAL="$SEAL"

# The same question without sealing anything: --provenance --require-llvm-identity.
PROMOTE_OPTS=(--provenance --require-llvm-identity)
new_case require-llvm-identity-dry-run-not-stated
write_stage_receipt "$SRC" llvm-not-stated
touch "$CASE/before"
if run_promotion; then fail 'the dry run with --require-llvm-identity passed a stage2 whose LLVM identity is not stated'; fi
grep -qF 'REFUSED (--require-llvm-identity): this stage2 does not state which LLVM it carries' "$CASE/output" \
    || { cat "$CASE/output" >&2; fail 'the dry run with --require-llvm-identity gave an unexpected refusal'; }
assert_dry_run_wrote_nothing
new_case require-llvm-identity-dry-run-stated
write_stage_receipt "$SRC" llvm-built
touch "$CASE/before"
run_promotion || { cat "$CASE/output" >&2; fail 'the dry run with --require-llvm-identity refused a stage2 that states its LLVM'; }
grep -qx 'stage_receipt_llvm_identity=stated' "$CASE/output" || fail 'the dry run with --require-llvm-identity lost the lines'
assert_dry_run_wrote_nothing
# Of a SEALED artifact it is asked of the record the seal carries, which is never
# rewritten: one that says stated, one that says not-stated, and one whose
# receipt records no LLVM (every seal cut before 2026-10-13).
new_case require-llvm-identity-of-a-seal
for sealed in "$LLVM_STATED_SEAL:pass" "$LLVM_UNSTATED_SEAL:stage_receipt_llvm_identity=not-stated" "$RECORDED_SEAL:stage_receipt_llvm=not-recorded"; do
    SRC="${sealed%%:*}"
    cp "$SRC/PROVENANCE" "$CASE/provenance-before"
    if [[ "${sealed#*:}" == pass ]]; then
        run_promotion || { cat "$CASE/output" >&2; fail '--provenance --require-llvm-identity refused a seal that says its LLVM identity is stated'; }
        cmp "$CASE/output" "$SRC/PROVENANCE" || fail '--provenance --require-llvm-identity did not print the seal record as it is'
    else
        if run_promotion; then fail "--provenance --require-llvm-identity passed a seal that says ${sealed#*:}"; fi
        grep -qF "REFUSED (--require-llvm-identity): the PROVENANCE of $SRC does not say stage_receipt_llvm_identity=stated." "$CASE/output" \
            && grep -qF "${sealed#*:}" "$CASE/output" \
            && grep -qF 'A seal is never rewritten' "$CASE/output" \
            || { cat "$CASE/output" >&2; fail "the refusal of a seal that says ${sealed#*:} does not say what the seal says"; }
    fi
    cmp "$SRC/PROVENANCE" "$CASE/provenance-before" || fail '--provenance --require-llvm-identity rewrote a seal record'
done
unset PROMOTE_OPTS

# A SEAL OF A STAGE2 WHOSE LLVM IS OF UNKNOWN MODE, from a receipt the recreator
# wrote from 381ac1ea0d until the follow-up of 2026-10-13 (the checkout's ids
# in the record): it is sealed, as it was, and the seal names no id of the
# checkout beside it (the third reading measured `3333...`-like ids there), and
# section (f) says what `unknown` means.
new_case stage-receipt-llvm-unknown-sealed
write_stage_receipt "$SRC" llvm-unknown-with-ids
PROMOTE_OPTS=(--no-flip)
run_promotion || { cat "$CASE/output" >&2; fail 'a stage2 whose LLVM is of unknown mode was refused without --require-llvm-identity'; }
[[ "$(grep '^stage_receipt' "$SEAL/PROVENANCE")" == "$(stage_receipt_lines_of "$SEAL/tool-provenance.json" "$SEED_ARGV")" ]] \
    || { cat "$SEAL/PROVENANCE" >&2; fail 'the seal does not say of an LLVM of unknown mode what this test reads from its receipt'; }
for line in 'stage_receipt_llvm=unknown' 'stage_receipt_llvm_identity=not-stated' 'stage_receipt_llvm_provenance=unknown' \
    'stage_receipt_llvm_source_sha256=not-recorded' 'stage_receipt_llvm_source_tree=not-recorded' \
    'stage_receipt_llvm_built_at_commit=not-recorded' 'stage_receipt_llvm_output_sha256=not-recorded'; do
    grep -qxF "$line" "$SEAL/PROVENANCE" || { cat "$SEAL/PROVENANCE" >&2; fail "the seal of an LLVM of unknown mode lacks $line"; }
done
! grep -q '=3333333333333333333333333333333333333333$' "$SEAL/PROVENANCE" \
    || fail "the checkout's src/llvm-project id stands beside an LLVM of unknown mode in a seal"
grep '^stage_receipt' "$SEAL/PROVENANCE" | lines_are_bounded_ascii \
    || fail 'a stage-receipt line of the seal of an LLVM of unknown mode is not printable ASCII with a bounded value'
says_section_f "$SEAL/PROVENANCE" with-a-receipt \
    || fail 'section (f) of the seal of an LLVM of unknown mode is not, word for word, the text this test holds it to'
[[ "$(readlink "$CASE/rustup/toolchains/trust")" == "$CASE/previous" ]] || fail 'the unknown-mode no-flip moved the channel'
unset PROMOTE_OPTS

# A WORD AFTER THE PATH IS REFUSED, as an unknown option before it is: the
# same words, exit 3, and nothing done. Until the follow-up of 2026-10-13
# promotion took the first word that is not an option as the path and looked
# at nothing after it, so `--no-flip <stage2> --require-llvm-identity` cut a
# seal WITHOUT the check it names (exit 0), `--provenance <seal>
# --require-llvm-identity` printed the record and exited 0, and an unknown
# option there was accepted (measured by the third reading of the
# LLVM-identity change). Every mode takes at most one path, so every mode is
# asked here. The --lineage operand is no place for an option either: there
# the flag was taken for the record's name, which --provenance never opens.
# (The helper holds every command-line refusal below to the same: exit 3, its
# own words, the usage, and nothing done.)
assert_command_line_refused() { # <the first line the refusal must be>
    local status=0
    run_promotion || status=$?
    [[ "$status" -eq 3 ]] || { cat "$CASE/output" >&2; fail "$(basename "$CASE"): exit $status, not the exit 3 of an option that is refused"; }
    [[ "$(head -1 "$CASE/output")" == "$1" ]] \
        || { cat "$CASE/output" >&2; fail "$(basename "$CASE") was refused with other words"; }
    grep -qxF 'Options go before the path; a word after it is refused, as an unknown option is.' "$CASE/output" \
        || { cat "$CASE/output" >&2; fail "$(basename "$CASE"): the refusal does not show the usage"; }
    ! grep -q '^==>' "$CASE/output" || { cat "$CASE/output" >&2; fail "$(basename "$CASE"): a step ran before the refusal"; }
    [[ ! -e "$CASE/sealed" ]] || fail "$(basename "$CASE"): a refused command line sealed something"
    [[ "$(readlink "$CASE/rustup/toolchains/trust")" == "$CASE/previous" ]] || fail "$(basename "$CASE"): a refused command line moved the channel"
}
after_the_path() { # <word> <path>
    printf 'promote: %s after the path %s (options are refused, never ignored; type every option before the path)' "$1" "$2"
}
new_case word-after-the-path-is-a-flag
write_stage_receipt "$SRC" llvm-not-stated
PROMOTE_OPTS=(--no-flip)
PROMOTE_AFTER=(--require-llvm-identity)
assert_command_line_refused "$(after_the_path --require-llvm-identity "$SRC")"
# The usage that refusal shows says what x.py does with the in-tree LLVM now.
says_what_x_py_does_now "$CASE/output" 'the usage'
new_case word-after-the-path-is-an-unknown-option
PROMOTE_AFTER=(--frobnicate)
assert_command_line_refused "$(after_the_path --frobnicate "$SRC")"
# ...and before the path that option is refused as it always was: the same exit.
unset PROMOTE_AFTER
PROMOTE_OPTS=(--no-flip --frobnicate)
assert_command_line_refused 'promote: unknown option --frobnicate (options are refused, never ignored)'
new_case word-after-the-path-is-a-second-path
PROMOTE_OPTS=(--no-flip)
PROMOTE_AFTER=("$CASE/elsewhere/stage2")
assert_command_line_refused "$(after_the_path "$CASE/elsewhere/stage2" "$SRC")"
# A dry run, and the record of a seal, which a seal never rewrites.
new_case word-after-the-provenance-operand
write_stage_receipt "$SRC" llvm-not-stated
PROMOTE_OPTS=(--provenance)
PROMOTE_AFTER=(--require-llvm-identity)
assert_command_line_refused "$(after_the_path --require-llvm-identity "$SRC")"
new_case word-after-the-provenance-operand-of-a-seal
SRC="$LLVM_UNSTATED_SEAL"
cp "$SRC/PROVENANCE" "$CASE/provenance-before"
assert_command_line_refused "$(after_the_path --require-llvm-identity "$SRC")"
! grep -q '^stage_receipt' "$CASE/output" || fail '--provenance printed a seal record over a word after its path'
cmp "$SRC/PROVENANCE" "$CASE/provenance-before" || fail 'a refused --provenance rewrote a seal record'
new_case word-after-the-gate-only-operand
PROMOTE_OPTS=(--gate-only)
PROMOTE_AFTER=(--require-llvm-identity)
assert_command_line_refused "$(after_the_path --require-llvm-identity "$SRC")"
unset PROMOTE_AFTER
new_case lineage-operand-is-an-option
write_stage_receipt "$SRC" llvm-not-stated
PROMOTE_OPTS=(--provenance --lineage --require-llvm-identity)
assert_command_line_refused 'promote: --lineage needs a file, not the option --require-llvm-identity (options are refused, never ignored)'
# A lone `-` has an option's shape too, and is no record's name (no case held
# this until the review of the follow-up, 2026-10-13).
new_case lineage-operand-is-a-dash
PROMOTE_OPTS=(--no-flip --lineage -)
assert_command_line_refused 'promote: --lineage needs a file, not the option - (options are refused, never ignored)'
# One record is checked and sealed: a second --lineage replaced the first,
# which was never opened (measured by the review of the follow-up, 2026-10-13).
new_case lineage-given-twice
PROMOTE_OPTS=(--no-flip --lineage "$CASE/first.json" --lineage "$CASE/second.json")
assert_command_line_refused "promote: --lineage $CASE/second.json after --lineage $CASE/first.json (one record is checked; options are refused, never ignored)"
# An empty word is no path: `promote-toolchain.sh --no-flip "$STAGE"` with an
# empty $STAGE took the checkout's default stage2 (found by the same review;
# here, before 2026-10-14: "no such stage2: <fixture>/build/host/stage2", exit 1).
new_case path-is-an-empty-word
PROMOTE_OPTS=(--no-flip)
SRC=""
assert_command_line_refused "promote: the path is an empty word (name the toolchain, or give no path for $FIXTURE_REPO/build/host/stage2; an empty word is refused, never read as no path)"

# A MODE REFUSES AN OPTION IT DOES NOT USE, with the same words and exit. Before
# 2026-10-14 each was dropped without a word (every case below exits 0 on the
# scripts before, measured): `--provenance --require-provenance` reported a
# stage2's class UNVERIFIED-PROVENANCE, or printed a seal's record, and exited
# 0; `--provenance --gate-only` ran the gates and printed no record; and
# `--gate-only` with a requirement passed on the gates alone. --gate-only
# starts tools and reads no record, so it takes no other option. --provenance
# asks one requirement of a record, --require-llvm-identity, and takes no
# other. Every option either mode does not use is asked, and the
# environment's spelling of --require-provenance as the flag is.
does_not_use() { # <mode> <option> <what the mode takes>
    printf 'promote: %s does not use %s (options are refused, never ignored; %s)' "$1" "$2" "$3"
}
for option in --provenance --allow-dirty-provenance --require-provenance --require-llvm-identity --no-flip --lineage; do
    new_case "gate-only-does-not-use$option"
    PROMOTE_OPTS=(--gate-only "$option")
    [[ "$option" != --lineage ]] || PROMOTE_OPTS+=("$CASE/lineage.json")
    assert_command_line_refused "$(does_not_use --gate-only "$option" 'it takes no other option')"
done
for option in --gate-only --allow-dirty-provenance --require-provenance --no-flip --lineage; do
    new_case "provenance-does-not-use$option"
    # A receipt that states its LLVM, so the one question --provenance asks
    # passes and nothing else stops the dry run.
    write_stage_receipt "$SRC" llvm-built
    # After the option it does use: the refusal is of the word, not of its place.
    PROMOTE_OPTS=(--provenance --require-llvm-identity "$option")
    [[ "$option" != --lineage ]] || PROMOTE_OPTS+=("$CASE/lineage.json")
    expected="$(does_not_use --provenance "$option" 'it takes --require-llvm-identity and paired explicit frontend authority')"
    [[ "$option" != --gate-only ]] || expected="$(does_not_use --gate-only --provenance 'it takes no other option')"
    assert_command_line_refused "$expected"
done
# Of a seal's record, which a seal never rewrites.
new_case provenance-of-a-seal-does-not-use-require-provenance
SRC="$LLVM_UNSTATED_SEAL"
cp "$SRC/PROVENANCE" "$CASE/provenance-before"
PROMOTE_OPTS=(--provenance --require-provenance)
assert_command_line_refused "$(does_not_use --provenance --require-provenance 'it takes --require-llvm-identity and paired explicit frontend authority')"
cmp "$SRC/PROVENANCE" "$CASE/provenance-before" || fail 'a refused --provenance rewrote a seal record'
TEST_REQUIRE_PROV=1
new_case provenance-does-not-use-the-environment-requirement
PROMOTE_OPTS=(--provenance)
assert_command_line_refused 'promote: --provenance does not use TRUST_REQUIRE_BUILD_PROVENANCE=1, the requirement of a seal (a requirement is refused, never ignored; it takes --require-llvm-identity and paired explicit frontend authority)'
new_case gate-only-does-not-use-the-environment-requirement
PROMOTE_OPTS=(--gate-only)
assert_command_line_refused 'promote: --gate-only does not use TRUST_REQUIRE_BUILD_PROVENANCE=1, the requirement of a seal (a requirement is refused, never ignored; it takes no other option)'
# The requirement is 1 and only 1, and a value that is not understood is
# refused in every mode: until 2026-10-14 `true` and `yes` turned it off
# without a word (measured: each case below sealed this stage2, whose class is
# UNVERIFIED-PROVENANCE, exit 0). 0 (and no value, which this test passes as
# 0) is every other case.
for value in true yes; do
    new_case "require-provenance-says-$value"
    TEST_REQUIRE_PROV="$value"
    PROMOTE_OPTS=(--no-flip)
    assert_command_line_refused "promote: TRUST_REQUIRE_BUILD_PROVENANCE=$value is neither 1 (require) nor 0 (do not require) (a value that is not understood is refused, never read as 0)"
done
unset TEST_REQUIRE_PROV
unset PROMOTE_OPTS

# A SEAL IS WHERE THE LINE IS WRITTEN. The dry runs above print what the reader
# gives; a seal passes those lines through the sealer's own `printf`, and the
# one sealing case before them records the plain seed command. Here the
# command line holds what a printf FORMAT would interpret (a percent sign,
# `%s%n`, a backslash before a letter, a lone backslash, and the `\xNN` bytes
# of the $'...' form): the seal records each character as it is, and this
# shell reads the sealed line back as the sealed receipt's arguments. (A sealer
# that wrote the lines as a format passed every case of this file until
# 2026-10-13; the second review of the change found that mutant alive.)
IFS= read -r FORMAT_ARGV <<'LINE'
--stage 2 --llvm-config $'/opt/llvm-\xf0\x9f\xab\xa8 22/it\'s/b\\in/llvm-config' 100% %s%n 'a\tb' '\'
LINE
new_case stage-receipt-recorded-format-characters
write_stage_receipt "$SRC" format-characters
PROMOTE_OPTS=(--no-flip)
run_promotion || { cat "$CASE/output" >&2; fail 'a stage2 whose receipt records a percent sign and backslashes was refused'; }
cmp "$SRC/tool-provenance.json" "$SEAL/tool-provenance.json" || fail 'the seal does not carry the receipt with the format characters'
[[ "$(grep '^stage_receipt' "$SEAL/PROVENANCE")" == "$(stage_receipt_lines_of "$SEAL/tool-provenance.json" "$FORMAT_ARGV")" ]] \
    || { cat "$SEAL/PROVENANCE" >&2; fail 'the seal does not record a command line holding format characters as it is'; }
grep -qxF -- "stage_receipt_recreator_argv=$FORMAT_ARGV" "$SEAL/PROVENANCE" \
    || fail 'PROVENANCE lacks the command line holding format characters'
grep '^stage_receipt' "$SEAL/PROVENANCE" | lines_are_bounded_ascii \
    || fail 'a sealed stage-receipt line holding format characters is not printable ASCII with a bounded value'
says_section_f "$SEAL/PROVENANCE" with-a-receipt \
    || fail 'section (f) of the seal that records format characters is not, word for word, the text this test holds it to'
[[ "$(readlink "$CASE/rustup/toolchains/trust")" == "$CASE/previous" ]] || fail 'the format-characters no-flip moved the channel'
argv_reads_back "$SEAL/tool-provenance.json" "$FORMAT_ARGV" \
    || fail 'the sealed command line holding format characters does not read back as the sealed receipt'"'"'s arguments'
unset PROMOTE_OPTS

# THE TOOL-START GATE. `trust-2615acef` was sealed on 2026-10-12 with a tippy
# that could not start: its `--version` answered, so the output contract passed.
assert_start_refusal() { # <row that must FAIL>...
    if run_promotion; then fail "$(basename "$CASE") was promoted"; fi
    grep -qF "stage2 at $SRC ships a tool that CANNOT START" "$CASE/output" \
        || { cat "$CASE/output" >&2; fail "unexpected refusal for $(basename "$CASE")"; }
    ! grep -qF 'violates the complete Trust toolchain output contract' "$CASE/output" \
        || fail "$(basename "$CASE") was refused by the output contract, which cannot see a start failure"
    local row
    for row in "$@"; do
        # The whole line: `tippy.frontend` is also how `tippy.frontend-lint` begins.
        grep -qxF "    FAIL  $row" "$CASE/output" || { cat "$CASE/output" >&2; fail "row $row did not fail"; }
    done
    [[ "$(grep -cF '    FAIL  ' "$CASE/output")" -eq $# ]] \
        || { cat "$CASE/output" >&2; fail "$(basename "$CASE"): expected exactly $# failing row(s)"; }
    [[ ! -e "$CASE/sealed" ]] || fail 'a toolchain that cannot start was copied'
    [[ "$(readlink "$CASE/rustup/toolchains/trust")" == "$CASE/previous" ]] || fail 'start refusal moved the channel'
    [[ ! -e "$CASE/sealed/trust-current" && ! -L "$CASE/sealed/trust-current" ]] || fail 'start refusal created trust-current'
}

# The measured case: every start of the driver panics. The lint row's exit is
# nonzero, which is the expected KIND; only its missing marker fails it.
new_case tippy-cannot-start
write_tippy_driver "$SRC/bin/tippy-driver" panic
"$SRC/bin/tippy-driver" --version | grep -qx 'tippy 1.0.0-fixture' || fail 'the panicking fixture must still answer --version'
assert_start_refusal tippy-driver.clean tippy-driver.lint tippy.frontend tippy.frontend-lint
[[ "$(grep -cF 'exit 101 is the expected kind, but the required marker never appeared' "$CASE/output")" -eq 2 ]] \
    || fail 'the two lint rows were not each failed on their marker'
grep -qF '| duplicate symbols in the rustc symbol list and the extra symbols added by the driver: [[66, 105' "$CASE/output" \
    || fail 'the refusal did not carry the panic message'
grep -qF 'python3 scripts/check_driver_extra_symbols.py' "$CASE/output" || fail 'the refusal does not name the source check'

# A driver that starts as a plain compiler and never lints.
new_case tippy-does-not-lint
write_tippy_driver "$SRC/bin/tippy-driver" no-lint
assert_start_refusal tippy-driver.lint tippy.frontend-lint
[[ "$(grep -cF 'it ran without linting' "$CASE/output")" -eq 2 ]] || fail 'a non-linting driver was refused for the wrong reason'

# The driver lints, and the frontend does not use it: it builds the package with
# a plain compiler and finishes. Both driver rows and the clean frontend row
# pass; only a lint that must fire THROUGH THE FRONTEND can see it.
new_case tippy-frontend-routes-to-a-plain-compiler
write_tippy_frontend "$SRC/bin/tippy" plain
assert_start_refusal tippy.frontend-lint
grep -qF 'it ran without linting' "$CASE/output" || fail 'a frontend that does not lint was refused for the wrong reason'
grep -qxF '    ok    tippy.frontend (pass)' "$CASE/output" || fail 'the plain-compiler frontend fixture did not finish its clean build'
grep -qxF '    ok    tippy-driver.lint (fail)' "$CASE/output" || fail 'the sibling driver of the plain-compiler frontend should still lint'

# A driver that exits 0 without compiling anything.
new_case tippy-returns-without-work
write_tippy_driver "$SRC/bin/tippy-driver" no-work
assert_start_refusal tippy-driver.clean
grep -qF 'it exited 0 without writing libstart_probe.rmeta' "$CASE/output" || fail 'an idle driver was refused for the wrong reason'

# A driver that writes what it was asked for and then exits nonzero: the file
# is there, so only the exit status can fail the row.
new_case tippy-fails-after-work
write_tippy_driver "$SRC/bin/tippy-driver" fail-after-work
assert_start_refusal tippy-driver.clean tippy.frontend
grep -qF 'expected it to start and finish its work, got exit 3' "$CASE/output" \
    || fail 'a driver that fails after its work was not refused on its exit status'

# Three tools that exit 0 without doing their work. Each still answers
# `--version`, so the output contract passes; each row's own witness refuses it.
# A frontend that never builds: no `Finished`, and no lint either.
new_case tippy-frontend-returns-without-work
write_idle_tool "$SRC/bin/tippy" 'tippy 1.0.0-fixture'
"$SRC/bin/tippy" --version | grep -qx 'tippy 1.0.0-fixture' || fail 'the idle frontend fixture must still answer --version'
assert_start_refusal tippy.frontend tippy.frontend-lint
grep -qF 'exit 0 is the expected kind, but the required marker never appeared' "$CASE/output" \
    && grep -qxF '          wanted marker: Finished' "$CASE/output" \
    || { cat "$CASE/output" >&2; fail 'an idle frontend was not refused on its missing Finished line'; }

# A trustfmt that formats nothing.
new_case trustfmt-returns-without-work
write_idle_tool "$SRC/bin/trustfmt" 'trustfmt 1.0.0-fixture'
assert_start_refusal trustfmt.format
grep -qF 'exit 0 is the expected kind, but the required marker never appeared' "$CASE/output" \
    && grep -qxF '          wanted marker:     a.wrapping_add(b)' "$CASE/output" \
    || { cat "$CASE/output" >&2; fail 'an idle trustfmt was not refused on its missing formatted line'; }

# A trustdoc that renders nothing (rustdoc is its alias: the same bytes).
new_case trustdoc-returns-without-work
write_idle_tool "$SRC/bin/trustdoc" 'rustc 1.0.0 (fixture) (trustdoc 1.0.0)'
cp "$SRC/bin/trustdoc" "$SRC/bin/rustdoc"
assert_start_refusal trustdoc.session
grep -qF 'it exited 0 without writing start_probe/index.html' "$CASE/output" \
    || { cat "$CASE/output" >&2; fail 'an idle trustdoc was not refused on its missing documentation'; }

# The candidate starts; the sealed copy does not. Step 6 refuses before the flip.
new_case sealed-tippy-cannot-start
if run_promotion tippy-start; then fail 'a seal whose tippy cannot start was promoted'; fi
grep -qF 'sealed toolchain ships a tool that cannot start from the seal' "$CASE/output" \
    || { cat "$CASE/output" >&2; fail 'unexpected refusal for sealed-tippy-cannot-start'; }
[[ "$(grep -cF '    FAIL  ' "$CASE/output")" -eq 4 ]] || fail 'the sealed copy should fail exactly the four tippy rows'
[[ "$(readlink "$CASE/rustup/toolchains/trust")" == "$CASE/previous" ]] || fail 'a seal that cannot start moved the channel'
[[ ! -e "$CASE/sealed/trust-current" && ! -L "$CASE/sealed/trust-current" ]] || fail 'a seal that cannot start created trust-current'
[[ ! -e "$SEAL/PROVENANCE" ]] || fail 'a seal that cannot start was given a PROVENANCE'

# trust-miri is started when the toolchain ships it, with its own extra symbols.
new_case trust-miri-shipped
write_trust_miri "$SRC/bin/trust-miri" ok
run_promotion || { cat "$CASE/output" >&2; fail 'a toolchain whose trust-miri starts was refused'; }
[[ "$(grep -cxF '    ok    trust-miri.session (pass)' "$CASE/output")" -eq 2 ]] || fail 'a shipped trust-miri was not started twice'
[[ "$(grep -cxF '==> tool-start gate: 7/7 passed' "$CASE/output")" -eq 2 ]] || fail 'the seven rows of a toolchain that ships trust-miri were not all started'
[[ "$(readlink "$CASE/rustup/toolchains/trust")" == "$SEAL" ]] || fail 'the trust-miri fixture was not promoted'

new_case trust-miri-cannot-start
write_trust_miri "$SRC/bin/trust-miri" panic
assert_start_refusal trust-miri.session

# What PROVENANCE keeps is the run on the SEALED copy, not the candidate's. Here
# the two differ and both pass: the candidate ships trust-miri and starts seven
# rows; the copy loses that one optional tool, and the seal starts six.
new_case tool-start-recorded-from-the-sealed-copy
write_trust_miri "$SRC/bin/trust-miri" ok
run_promotion lose-trust-miri || { cat "$CASE/output" >&2; fail 'a seal whose copy lost an optional tool was refused'; }
[[ "$(grep -E '^==> tool-start gate: [0-9]+/[0-9]+ passed' "$CASE/output")" == \
    '==> tool-start gate: 7/7 passed'$'\n''==> tool-start gate: 6/6 passed (1 not shipped, not started)' ]] \
    || { cat "$CASE/output" >&2; fail 'the candidate did not start seven rows and the sealed copy six'; }
[[ "$(grep '^tool_start_gate' "$SEAL/PROVENANCE")" == \
    'tool_start_gate=6/6 passed (1 not shipped, not started)'$'\n''tool_start_gate_rows=tippy-driver.clean tippy-driver.lint tippy.frontend tippy.frontend-lint trustdoc.session trustfmt.format'$'\n''tool_start_gate_not_shipped=trust-miri.session' ]] \
    || { cat "$SEAL/PROVENANCE" >&2; fail 'PROVENANCE records a tool-start run that is not the one on the sealed copy'; }

# --gate-only asks an existing toolchain both questions and changes nothing.
assert_gate_only_changed_nothing() {
    [[ ! -e "$CASE/sealed" ]] || fail '--gate-only sealed something'
    [[ "$(readlink "$CASE/rustup/toolchains/trust")" == "$CASE/previous" ]] || fail '--gate-only moved the channel'
    [[ -z "$(find "$SRC" -newer "$CASE/before" 2>/dev/null)" ]] || fail '--gate-only wrote into the toolchain it was asked about'
}
PROMOTE_OPTS=(--gate-only)
new_case gate-only-pass
touch "$CASE/before"
run_promotion || { cat "$CASE/output" >&2; fail '--gate-only refused a toolchain that starts'; }
grep -qF "gate-only: PASS — $SRC would clear the pre-promotion UI gate and the tool-start gate" "$CASE/output" \
    || { cat "$CASE/output" >&2; fail '--gate-only did not report both gates'; }
# The fixture's host is not Darwin, so no paired native tool was looked for,
# and the PASS line says that instead of naming the surface as cleared.
grep -qF 'and the native rustc-dev gate (the paired native-tool surface is a Darwin check; host test-host has none and nothing was checked)' "$CASE/output" \
    || { cat "$CASE/output" >&2; fail '--gate-only claimed a native-tool surface it did not check'; }
assert_gate_only_changed_nothing

# The read-only mode exercises the same native probe without sealing anything.
new_case gate-only-native-link-fails
touch "$CASE/before"
if TEST_RUSTC_DEV_LINK=fail run_promotion; then fail '--gate-only passed a missing native link closure'; fi
grep -qF 'native rustc-dev gate FAILED' "$CASE/output" \
    || { cat "$CASE/output" >&2; fail '--gate-only hid its private native link failure'; }
KEPT="$(sed -n 's/^    the rustc-dev probe: its source and everything it printed are kept in //p' "$CASE/output")"
[[ -n "$KEPT" && -f "$KEPT/rustc_dev_probe.log" ]] && grep -qxF "ld: library 'Polly' not found" "$KEPT/rustc_dev_probe.log" \
    || { cat "$CASE/output" >&2; fail '--gate-only did not keep what its failing probe printed'; }
! grep -qF 'the rustc-dev probe: its source' "$WORK/gate-only-pass/output" || fail 'a passing probe kept a scratch directory'
assert_gate_only_changed_nothing

new_case gate-only-native-run-fails
touch "$CASE/before"
if TEST_RUSTC_DEV_RUN=fail run_promotion; then fail '--gate-only passed a private runtime loader failure'; fi
grep -qF 'native rustc-dev gate FAILED' "$CASE/output" \
    || { cat "$CASE/output" >&2; fail '--gate-only hid its private native runtime failure'; }
assert_gate_only_changed_nothing

new_case gate-only-all-three-fail
write_tippy_driver "$SRC/bin/tippy-driver" panic
sed -i.bak 's/1 proved, 0 failed/0 proved, 1 failed/' "$SRC/bin/trustc" && rm "$SRC/bin/trustc.bak"
touch "$CASE/before"
if TEST_RUSTC_DEV_LINK=fail run_promotion; then fail '--gate-only passed three failed gates'; fi
grep -qF 'UI gate FAILED, tool-start gate FAILED, native rustc-dev gate FAILED' "$CASE/output" \
    || { cat "$CASE/output" >&2; fail '--gate-only failed to execute every gate'; }
assert_gate_only_changed_nothing

# The native Darwin SDK contract is checked directly by --gate-only, even
# though that mode deliberately does not run the full promotion surface scan.
# A Darwin SDK with neither tool is the recorded gap (DARWIN-NATIVE-TOOLS-PRODUCER-1,
# DECISION_QUEUE NATIVE-TOOLS-ABSENT-RECORDED): the other gates decide, and the
# verdict line says ABSENT, never "passed" and never silence.
new_case gate-only-native-tools-missing
sed -i.bak 's/host: test-host/host: aarch64-apple-darwin/' "$SRC/bin/trustc" && rm "$SRC/bin/trustc.bak"
touch "$CASE/before"
run_promotion || { cat "$CASE/output" >&2; fail '--gate-only refused a Darwin SDK only for the recorded native-tool gap'; }
grep -qF 'RECORDED  gate-only SDK publishes no paired bin/rust-lld and bin/dsymutil' "$CASE/output" \
    || { cat "$CASE/output" >&2; fail '--gate-only did not record the absent native linker tools'; }
grep -qF 'and the native rustc-dev gate (the paired native-tool surface is ABSENT and recorded: this SDK has no bin/rust-lld and no bin/dsymutil' "$CASE/output" \
    || { cat "$CASE/output" >&2; fail '--gate-only hid the absent native linker tools in its verdict'; }
if grep -qE 'gate-only: PASS .* and the paired native-tool surface$' "$CASE/output"; then
    cat "$CASE/output" >&2; fail '--gate-only claimed a native-tool surface it did not check'
fi
assert_gate_only_changed_nothing

# One tool without the other is a broken surface and still refuses.
new_case gate-only-native-tools-half
sed -i.bak 's/host: test-host/host: aarch64-apple-darwin/' "$SRC/bin/trustc" && rm "$SRC/bin/trustc.bak"
printf '#!/bin/sh\n# Inert orchestration fixture; not a native runtime qualification.\nexit 0\n' > "$SRC/bin/rust-lld"
chmod +x "$SRC/bin/rust-lld"
touch "$CASE/before"
if run_promotion; then fail '--gate-only passed a Darwin SDK with half a native-tool surface'; fi
grep -qF 'UI gate passed, tool-start gate passed, native rustc-dev gate passed, paired native-tool surface FAILED' "$CASE/output" \
    || { cat "$CASE/output" >&2; fail '--gate-only skipped other gates or hid a half native-tool surface'; }
assert_gate_only_changed_nothing

new_case gate-only-native-tools-present
sed -i.bak 's/host: test-host/host: aarch64-apple-darwin/' "$SRC/bin/trustc" && rm "$SRC/bin/trustc.bak"
for native_tool in rust-lld dsymutil; do
    printf '#!/bin/sh\n# Inert orchestration fixture; not a native runtime qualification.\nexit 0\n' > "$SRC/bin/$native_tool"
    chmod +x "$SRC/bin/$native_tool"
done
touch "$CASE/before"
run_promotion || { cat "$CASE/output" >&2; fail '--gate-only refused the complete inert Darwin surface'; }
grep -qE 'gate-only: PASS .* and the native rustc-dev gate and the paired native-tool surface$' "$CASE/output" \
    || { cat "$CASE/output" >&2; fail '--gate-only did not report the complete surface'; }
assert_gate_only_changed_nothing

# The toolchain may be named relative to the caller's directory; the frontend
# row starts its tool from inside a scratch package and must still find it.
new_case gate-only-relative-path
touch "$CASE/before"
ABSOLUTE_SRC="$SRC"
SRC=build/test-host/stage2
( cd "$CASE" && run_promotion ) || { cat "$CASE/output" >&2; fail '--gate-only refused a toolchain named by a relative path'; }
SRC="$ABSOLUTE_SRC"
[[ "$(grep -cxF '    ok    tippy.frontend (pass)' "$CASE/output")" -eq 1 ]] || fail 'the frontend row did not start through a relative path'
[[ "$(grep -cxF '    ok    tippy.frontend-lint (fail)' "$CASE/output")" -eq 1 ]] || fail 'the frontend lint row did not start through a relative path'
grep -qF 'gate-only: PASS — build/test-host/stage2 would clear' "$CASE/output" || fail '--gate-only did not pass the relative path'
assert_gate_only_changed_nothing

new_case gate-only-tippy-cannot-start
write_tippy_driver "$SRC/bin/tippy-driver" panic
touch "$CASE/before"
if run_promotion; then fail '--gate-only passed a toolchain whose tippy cannot start'; fi
grep -qF "gate-only: REFUSED — $SRC: UI gate passed, tool-start gate FAILED" "$CASE/output" \
    || { cat "$CASE/output" >&2; fail '--gate-only gave the wrong verdict for a tippy that cannot start'; }
assert_gate_only_changed_nothing

# One gate failing does not hide the other: both always run.
new_case gate-only-both-fail
write_tippy_driver "$SRC/bin/tippy-driver" panic
sed -i.bak 's/1 proved, 0 failed/0 proved, 1 failed/' "$SRC/bin/trustc" && rm "$SRC/bin/trustc.bak"
touch "$CASE/before"
if run_promotion; then fail '--gate-only passed a toolchain failing both gates'; fi
grep -qF "gate-only: REFUSED — $SRC: UI gate FAILED, tool-start gate FAILED" "$CASE/output" \
    || { cat "$CASE/output" >&2; fail '--gate-only did not report both failing gates'; }
grep -qF '    FAIL  tests/ui/trust/r1/flip_caller_covered.rs' "$CASE/output" || fail 'the UI gate row is missing'
grep -qF '    FAIL  tippy-driver.clean' "$CASE/output" || fail 'the tool-start gate did not run after a failing UI gate'
assert_gate_only_changed_nothing

# A required tool that is absent fails its row; it is never reported as n/a.
new_case gate-only-missing-trustdoc
rm "$SRC/bin/trustdoc"
touch "$CASE/before"
if run_promotion; then fail '--gate-only passed a toolchain without trustdoc'; fi
grep -qF '    FAIL  trustdoc.session' "$CASE/output" && grep -qF 'bin/trustdoc is not in this toolchain' "$CASE/output" \
    || { cat "$CASE/output" >&2; fail 'a missing required tool was not a failing row'; }
! grep -qF 'n/a   trustdoc.session' "$CASE/output" || fail 'a missing required tool was reported n/a'
assert_gate_only_changed_nothing

# B1's run-fail rows on a toolchain that elides the check, as store trust 9192
# does: both build, and both binaries print `0 0` and exit 0. The gate fails on
# exactly those two rows, by revision, and says what the run did.
B1_ROW=tests/ui/trust/instance_hypothesis/requires_dep_elision_cross_crate_run.rs
new_case gate-only-b1-check-elided
touch "$CASE/before"
if TEST_B1_PROBE=elided run_promotion; then fail '--gate-only passed a toolchain whose B1 probes do not panic'; fi
grep -qF "gate-only: REFUSED — $SRC: UI gate FAILED, tool-start gate passed" "$CASE/output" \
    || { cat "$CASE/output" >&2; fail '--gate-only gave the wrong verdict for an elided B1 check'; }
grep -qxF "    FAIL  $B1_ROW#advisory_pointer" "$CASE/output" && grep -qxF "    FAIL  $B1_ROW#off_direct" "$CASE/output" \
    || { cat "$CASE/output" >&2; fail 'the two B1 rows were not each named by revision'; }
[[ "$(grep -cF '    FAIL  ' "$CASE/output")" -eq 2 ]] || fail 'an elided B1 check should fail exactly the two B1 rows'
[[ "$(grep -cF 'expected the binary to panic (exit 101, //@ run-fail), got exit 0; its stdout began: 0 0' "$CASE/output")" -eq 2 ]] \
    || { cat "$CASE/output" >&2; fail 'a B1 row did not report the run it saw'; }
assert_gate_only_changed_nothing

# A panic, but not the one the test asserts: the run-fail marker is required.
new_case gate-only-b1-wrong-panic
touch "$CASE/before"
if TEST_B1_PROBE=divide run_promotion; then fail '--gate-only passed a B1 probe that panicked for another reason'; fi
[[ "$(grep -cF 'it panicked, but the required marker never appeared on its stderr' "$CASE/output")" -eq 2 ]] \
    && grep -qxF '          wanted marker: attempt to add with overflow' "$CASE/output" \
    && grep -qxF '          got instead:   attempt to divide by zero' "$CASE/output" \
    || { cat "$CASE/output" >&2; fail 'a B1 row passed on the wrong panic'; }
assert_gate_only_changed_nothing

# The aux crate does not build: the row fails on the aux build, naming it, and
# the test itself is never compiled against a dependency that is not there.
new_case gate-only-b1-aux-unbuilt
touch "$CASE/before"
if TEST_B1_PROBE=aux-fails run_promotion; then fail '--gate-only passed a B1 row whose aux crate did not build'; fi
[[ "$(grep -cF 'aux crate requires_dep_default_policy.rs did not build (exit 1): error: synthetic aux build failure' "$CASE/output")" -eq 2 ]] \
    || { cat "$CASE/output" >&2; fail 'a B1 row did not fail on its aux build'; }
! grep -qF "can't find crate for" "$CASE/output" || fail 'the B1 test was compiled after its aux crate failed'
assert_gate_only_changed_nothing

# The compiler exits 0 and the row's binary is there without an execute bit:
# the row says so. It used to say the compiler "left no executable", which is
# also what it said of a TMPDIR mounted noexec.
new_case gate-only-b1-binary-not-executable
touch "$CASE/before"
if TEST_B1_PROBE=not-executable run_promotion; then fail '--gate-only passed a B1 binary it could not run'; fi
[[ "$(grep -cE '^          the compiler exited 0 and wrote requires_dep_elision_cross_crate_run as something that is not a file with an execute bit \(-rw-[-r][-w]-[-r][-w]-[.+@]?\) \(the row.s binary, in /.*\)$' "$CASE/output")" -eq 2 ]] \
    || { cat "$CASE/output" >&2; fail 'a B1 binary without an execute bit was not said to be one on its two rows'; }
! grep -qF 'left no executable' "$CASE/output" || fail 'a binary that was written was said not to have been'
assert_gate_only_changed_nothing

# The binary dies without panicking and writes nothing to stdout: the row
# quotes its stderr, or says there was none. It used to end `its stdout began: `.
for death in dies silent; do
    new_case "gate-only-b1-binary-$death"
    touch "$CASE/before"
    if TEST_B1_PROBE="$death" run_promotion; then fail "--gate-only passed a B1 binary that $death"; fi
    case "$death" in
        dies) B1_SAID='fixture: died before main' ;;
        silent) B1_SAID='(it printed nothing)' ;;
    esac
    [[ "$(grep -cF "expected the binary to panic (exit 101, //@ run-fail), got exit 3; its stdout was empty and its stderr began: $B1_SAID" "$CASE/output")" -eq 2 ]] \
        || { cat "$CASE/output" >&2; fail "a B1 binary that $death was not quoted on its two rows"; }
    ! grep -nE '(: |got instead: +|began: *)$' "$CASE/output" \
        || { cat "$CASE/output" >&2; fail "a B1 binary that $death left a row ending at its colon"; }
    assert_gate_only_changed_nothing
done

# A ROW ALWAYS SAYS WHAT ITS COMMAND PRINTED. A row used to quote the first
# `error` line and nothing else, so a compiler that died without one left
# `got exit 1: ` with nothing after the colon. Here the compiler is killed on
# a row that must compile, prints nothing on a row that must be refused, and
# prints nothing for the aux crate; every row names what happened, and what
# each printed is kept and said to be.
no_row_ends_at_its_colon() {
    ! grep -nE '(: |got instead: +)$' "$CASE/output" \
        || { cat "$CASE/output" >&2; fail "$(basename "$CASE"): a row gives no reason after its colon"; }
}
new_case gate-only-compiler-dies-without-a-diagnostic
touch "$CASE/before"
if TEST_UI_FAULT=no-diagnostic run_promotion; then fail '--gate-only passed a compiler that dies on three rows'; fi
grep -qF 'got exit 137: Killed' "$CASE/output" \
    || { cat "$CASE/output" >&2; fail 'a killed compiler was not quoted on the row that must compile'; }
grep -qxF '          got instead:   (no error or warning line; exit 1) (it printed nothing)' "$CASE/output" \
    || { cat "$CASE/output" >&2; fail 'a silent compiler was not named on the row that must be refused'; }
[[ "$(grep -cF 'aux crate requires_dep_default_policy.rs did not build (exit 1): (it printed nothing)' "$CASE/output")" -eq 2 ]] \
    || { cat "$CASE/output" >&2; fail 'a silent aux build was not named on the two B1 rows'; }
no_row_ends_at_its_colon
grep -qF "gate-only: REFUSED — $SRC: UI gate FAILED, tool-start gate passed" "$CASE/output" \
    || { cat "$CASE/output" >&2; fail 'a compiler that dies is a FAILED gate, not another word'; }
KEPT="$(sed -n 's/^    everything each row printed is kept under \([^ ]*\) (output\.txt.*$/\1/p' "$CASE/output")"
[[ -n "$KEPT" && -f "$KEPT/flip_caller_covered/output.txt" ]] \
    && grep -qxF 'Killed' "$KEPT/flip_caller_covered/output.txt" \
    || { cat "$CASE/output" >&2; fail 'the UI gate did not keep what its failing rows printed'; }
assert_gate_only_changed_nothing
# The control: with nothing failing, the rows above pass and nothing is kept.
! grep -qF 'is kept under' "$WORK/gate-only-pass/output" || fail 'a passing gate kept a scratch directory'

# THE SERIAL EXECUTOR IS ASKED ONCE, BEFORE ANY GATE. Without one, or under a
# caller with no build slot, every row used to print FAIL with no reason and
# the refusal blamed the compiler (the GB10, 2026-11-10). Now the run stops
# before the first gate with one refusal that names the cause, the program,
# how to build it and what holds a slot.
assert_refused_before_any_gate() { # <the words the refusal must carry>...
    local words
    if run_promotion; then cat "$CASE/output" >&2; fail "$(basename "$CASE") ran without a usable serial executor"; fi
    for words in 'promote: REFUSED before any gate: ' "$@" 'trust-serial-command' \
        '--features serial-command --bin trust-serial-command' 'scripts/build-slot --cpus 1 -- bash' \
        'No gate ran. This says nothing about the toolchain.'; do
        grep -qF -- "$words" "$CASE/output" \
            || { cat "$CASE/output" >&2; fail "$(basename "$CASE"): the refusal does not say: $words"; }
    done
    ! grep -qE '^==> (UI gate|tool-start gate)|^    (FAIL|NOT RUN|ok) |^verify-toolchain:' "$CASE/output" \
        || { cat "$CASE/output" >&2; fail "$(basename "$CASE"): something ran before the refusal"; }
    ! grep -qF "FAILS this tree's named UI tests" "$CASE/output" || fail "$(basename "$CASE"): the compiler was blamed"
    [[ "$(grep -c '^promote: ' "$CASE/output")" -eq 1 ]] \
        || { cat "$CASE/output" >&2; fail "$(basename "$CASE"): the refusal was not said exactly once"; }
}
new_case gate-only-no-serial-executor
touch "$CASE/before"
TEST_SERIAL_COMMAND='' assert_refused_before_any_gate 'TRUST_TOOLCHAIN_SERIAL_COMMAND is not set.'
assert_gate_only_changed_nothing
# Absent, not empty: the case that was measured. A read with no default would
# pass the case above and stop here on bash's own "unbound variable".
new_case gate-only-serial-executor-unset
touch "$CASE/before"
TEST_SERIAL_UNSET=1 assert_refused_before_any_gate 'TRUST_TOOLCHAIN_SERIAL_COMMAND is not set.'
! grep -qF 'unbound variable' "$CASE/output" || fail 'an unset variable reached bash as an unbound one'
assert_gate_only_changed_nothing
# Each shape the variable may not have, in the one sentence that lists them.
for shape in missing relative directory symlink not-executable; do
    new_case "gate-only-serial-executor-$shape"
    touch "$CASE/before"
    case "$shape" in
        missing) NAMED="$CASE/absent/trust-serial-command" ;;
        relative) NAMED=serial-command ;;
        directory) NAMED="$CASE" ;;
        symlink) NAMED="$CASE/executor"; ln -s "$WORK/serial-command" "$NAMED" ;;
        not-executable) NAMED="$CASE/executor"; cp "$WORK/serial-command" "$NAMED"; chmod -x "$NAMED" ;;
    esac
    TEST_SERIAL_COMMAND="$NAMED" assert_refused_before_any_gate \
        "TRUST_TOOLCHAIN_SERIAL_COMMAND=$NAMED is not the absolute path of a regular executable file"
    assert_gate_only_changed_nothing
done
# A caller that holds no build slot: the executor's own words, once.
new_case gate-only-serial-executor-unadmitted
write_serial_command "$CASE/executor" unadmitted
touch "$CASE/before"
TEST_SERIAL_COMMAND="$CASE/executor" assert_refused_before_any_gate \
    'the serial executor would not start a no-op (exit 75).' \
    "    ran:  $CASE/executor -- " \
    '    said: trust-serial-command: refused: command requires an already-admitted caller; this launcher grants no CPU/memory'
assert_gate_only_changed_nothing

# A REFUSAL THAT BEGINS AFTER THE QUESTION is NOT RUN, never FAIL: the executor
# starts the no-op and then nothing. No row reads its exit status as the
# compiler's (the rows that expect a refusal would), and the verdict names the
# executor. The native probe says NOT RUN under its own name.
NOT_RUN='the serial executor refused to start'
new_case gate-only-serial-executor-refuses-after-the-question
write_serial_command "$CASE/executor" after-the-noop
touch "$CASE/before"
if TEST_SERIAL_COMMAND="$CASE/executor" run_promotion; then fail '--gate-only passed with no row run'; fi
[[ "$(grep -cE '^    NOT RUN  tests/ui/trust/' "$CASE/output")" -eq 8 ]] \
    || { cat "$CASE/output" >&2; fail 'the eight UI rows were not each NOT RUN'; }
[[ "$(grep -cE '^    NOT RUN  (tippy|trustdoc|trustfmt)' "$CASE/output")" -eq 6 ]] \
    || { cat "$CASE/output" >&2; fail 'the six shipped tool rows were not each NOT RUN'; }
[[ "$(grep -cF "$NOT_RUN the compiler, so this row says nothing about it: trust-serial-command: refused: command requires an already-admitted caller" "$CASE/output")" -eq 8 ]] \
    || { cat "$CASE/output" >&2; fail 'a UI row did not carry the executor refusal'; }
! grep -qE '^    (FAIL|ok)  ' "$CASE/output" || { cat "$CASE/output" >&2; fail 'a row that did not run was given a verdict'; }
grep -qF "gate-only: REFUSED — $SRC: UI gate NOT RUN (the serial executor refused), tool-start gate NOT RUN (the serial executor refused), native rustc-dev gate NOT RUN (the serial executor refused), paired native-tool surface not applicable (host test-host is not Darwin; nothing was checked)" "$CASE/output" \
    || { cat "$CASE/output" >&2; fail '--gate-only did not say which gates did not run'; }
grep -qxF "    NOT RUN  rustc-dev probe: $NOT_RUN the compiler, so this says nothing about it: trust-serial-command: refused: command requires an already-admitted caller; this launcher grants no CPU/memory" "$CASE/output" \
    || { cat "$CASE/output" >&2; fail 'the native probe did not say it was not run'; }
no_row_ends_at_its_colon
assert_gate_only_changed_nothing
unset PROMOTE_OPTS

# The same three, of a seal: refused before anything is verified or copied, and
# a refusal that begins later is the run's, in words that do not say "Fix the
# compiler".
assert_nothing_sealed() {
    [[ ! -e "$CASE/sealed" ]] || fail "$(basename "$CASE"): a refused run left an artifact directory"
    [[ "$(readlink "$CASE/rustup/toolchains/trust")" == "$CASE/previous" ]] || fail "$(basename "$CASE"): a refused run moved the channel"
}
new_case seal-no-serial-executor
TEST_SERIAL_COMMAND='' assert_refused_before_any_gate 'TRUST_TOOLCHAIN_SERIAL_COMMAND is not set.'
assert_nothing_sealed
new_case seal-serial-executor-refuses-after-the-question
write_serial_command "$CASE/executor" after-the-noop
if TEST_SERIAL_COMMAND="$CASE/executor" run_promotion; then fail 'a stage2 was sealed with no UI row run'; fi
grep -qF "promote: the UI gate on the stage2 at $SRC did not finish: $NOT_RUN a command for each row marked NOT RUN above — refusing to seal it; nothing was copied." "$CASE/output" \
    && grep -qF 'That is a refusal of this run, not a verdict on the toolchain' "$CASE/output" \
    && grep -qF 'scripts/build-slot --cpus 1 -- bash' "$CASE/output" \
    || { cat "$CASE/output" >&2; fail 'a UI gate that did not run was not refused as one'; }
! grep -qF "FAILS this tree's named UI tests" "$CASE/output" || fail 'the compiler was blamed for a gate that did not run'
assert_nothing_sealed
# Later still: the candidate's gates run, the copy is made, and nothing under
# the sealed root starts. The first question asked of the seal quotes the line.
new_case seal-serial-executor-refuses-the-sealed-copy
write_serial_command "$CASE/executor" refuses-under "$CASE/sealed"
if TEST_SERIAL_COMMAND="$CASE/executor" run_promotion; then fail 'a seal was promoted with its own compiler never started'; fi
grep -qF "promote: the hello world of the sealed copy at $SEAL was NOT RUN: $NOT_RUN it — the channel was not moved." "$CASE/output" \
    && grep -qxF '    said: trust-serial-command: refused: command requires an already-admitted caller; this launcher grants no CPU/memory' "$CASE/output" \
    || { cat "$CASE/output" >&2; fail 'a hello world that was never started was not said to be'; }
! grep -qF 'cannot compile a hello world' "$CASE/output" || fail 'the sealed compiler was blamed for a hello world that was never started'
[[ "$(readlink "$CASE/rustup/toolchains/trust")" == "$CASE/previous" ]] || fail 'a refused seal moved the channel'

# ONE COMMAND REFUSED, LATE. The executor starts everything but one command:
# the gate that reaches it says NOT RUN under its own name, on the candidate
# and on the sealed copy, and never in the words kept for a toolchain that
# failed. (The UI gate's own case is above.)
REFUSED_LINE='trust-serial-command: refused: command requires an already-admitted caller; this launcher grants no CPU/memory'
for late in stage2-rustc-dev stage2-tool-start sealed-rustc-dev sealed-tool-start; do
    new_case "seal-serial-executor-refuses-$late"
    case "$late" in
        stage2-rustc-dev) GLOB='*/rustc_dev_probe.rs'; GATE="the rustc-dev gate on the stage2 at $SRC"; DONE='refusing to seal it; nothing was copied' ;;
        stage2-tool-start) GLOB='*/bin/tippy-driver *'; GATE="the tool-start gate on the stage2 at $SRC"; DONE='refusing to seal it; nothing was copied' ;;
        sealed-rustc-dev) GLOB="$SEAL/bin/trustc *rustc_dev_probe.rs"; GATE="the rustc-dev gate on the sealed copy at $SEAL"; DONE='the channel was not moved' ;;
        sealed-tool-start) GLOB="$SEAL/bin/tippy-driver *"; GATE="the tool-start gate on the sealed copy at $SEAL"; DONE='the channel was not moved' ;;
    esac
    write_serial_command "$CASE/executor" refuses-matching "$GLOB"
    if TEST_SERIAL_COMMAND="$CASE/executor" run_promotion; then fail "$late: a seal was promoted with a gate not run"; fi
    grep -qF "promote: $GATE did not finish: $NOT_RUN a command for each row marked NOT RUN above — $DONE." "$CASE/output" \
        || { cat "$CASE/output" >&2; fail "$late: a gate that did not run was not refused as one"; }
    ! grep -qE 'cannot build a rustc_private consumer|CANNOT START|cannot start from the seal' "$CASE/output" \
        || { cat "$CASE/output" >&2; fail "$late: the toolchain was blamed for a gate that did not run"; }
    [[ "$(readlink "$CASE/rustup/toolchains/trust")" == "$CASE/previous" ]] || fail "$late: a refused run moved the channel"
    case "$late" in stage2-*) [[ ! -e "$CASE/sealed" ]] || fail "$late: a refused candidate was copied" ;; esac
    # The candidate's probe directory is kept and named: the refusal's reason is in it.
    if [[ "$late" == stage2-rustc-dev ]]; then
        KEPT="$(sed -n 's/^    the rustc-dev probe: its source and everything it printed are kept in //p' "$CASE/output")"
        [[ -n "$KEPT" && -f "$KEPT/rustc_dev_probe.rs" ]] && grep -qxF "$REFUSED_LINE" "$KEPT/rustc_dev_probe.log" \
            || { cat "$CASE/output" >&2; fail "$late: a probe that was not run did not say where its files are"; }
    fi
done
# The two commands of the seal that are not gate rows quote the executor too:
# a rustc that was never asked for its -Z help is not one without the flag,
# and a `--print target-libdir` that was never started does not end the run
# without a word.
new_case seal-z-help-was-not-asked
write_serial_command "$CASE/executor" refuses-matching "$SEAL/bin/rustc -Z help"
if TEST_SERIAL_COMMAND="$CASE/executor" run_promotion; then fail 'a seal was promoted with its -Z help never read'; fi
grep -qF "promote: \`rustc -Z help\` of the sealed copy at $SEAL was NOT RUN: $NOT_RUN it — the channel was not moved." "$CASE/output" \
    && grep -qxF "    said: $REFUSED_LINE" "$CASE/output" \
    && grep -qF 'scripts/build-slot --cpus 1 -- bash' "$CASE/output" \
    || { cat "$CASE/output" >&2; fail 'a -Z help that was never asked for was not said to be'; }
! grep -qE 'has no -Ztrust-verify flag|did not print its -Z help' "$CASE/output" \
    || fail 'a rustc that was never asked was blamed for its -Z help'
[[ "$(readlink "$CASE/rustup/toolchains/trust")" == "$CASE/previous" ]] || fail 'a refused seal moved the channel'
# ...and one that was asked and died says so, with its words, not "has no flag".
new_case seal-z-help-dies
if TEST_UI_FAULT=zhelp-dies run_promotion; then fail 'a seal was promoted with a rustc whose -Z help dies'; fi
grep -qF 'promote: the sealed rustc did not print its -Z help (exit 3): fixture: -Z help died' "$CASE/output" \
    || { cat "$CASE/output" >&2; fail 'a -Z help that died was not quoted'; }
! grep -qF 'has no -Ztrust-verify flag' "$CASE/output" || fail 'a rustc whose -Z help died was said to have no -Ztrust-verify flag'
[[ "$(readlink "$CASE/rustup/toolchains/trust")" == "$CASE/previous" ]] || fail 'a refused seal moved the channel'
# ...and one that was asked, answered, and has no such flag is refused in the
# words kept for it: the second of the two questions, the one that is about
# the toolchain.
new_case seal-z-help-has-no-trust-verify
if TEST_UI_FAULT=zhelp-no-flag run_promotion; then fail 'a seal was promoted with a rustc that has no -Ztrust-verify flag'; fi
grep -qxF 'promote: sealed toolchain has no -Ztrust-verify flag — it cannot verify, so it is not a Trust toolchain' "$CASE/output" \
    || { cat "$CASE/output" >&2; fail 'a rustc with no -Ztrust-verify flag was not refused as one'; }
! grep -qE 'was NOT RUN|did not print its -Z help' "$CASE/output" \
    || fail 'a rustc that printed its -Z help without the flag was said not to have been asked, or not to have answered'
[[ "$(readlink "$CASE/rustup/toolchains/trust")" == "$CASE/previous" ]] || fail 'a refused seal moved the channel'
[[ ! -e "$CASE/sealed/trust-current" && ! -L "$CASE/sealed/trust-current" ]] || fail 'a refused seal created trust-current'
# The fourth: the build of the AY-admission probe (step 6a), which only a
# private sysroot that carries trust_cg_verify reaches. A probe that was never
# built is not a sealed driver that cannot build it.
new_case seal-ay-probe-was-not-built
printf 'synthetic trust_cg_verify metadata\n' > "$PRIVATE/test-host/libtrust_cg_verify-fixture.rmeta"
write_serial_command "$CASE/executor" refuses-matching '*ay_probe.rs'
if TEST_SERIAL_COMMAND="$CASE/executor" run_promotion; then fail 'a seal was promoted with its ay admission never asked'; fi
grep -qF "promote: the build of the AY-admission probe against the sealed copy at $SEAL was NOT RUN: $NOT_RUN it — the channel was not moved." "$CASE/output" \
    && grep -qxF "    said: $REFUSED_LINE" "$CASE/output" \
    || { cat "$CASE/output" >&2; fail 'an AY-admission probe that was never built was not said to be'; }
! grep -qF 'could not build the AY-admission probe' "$CASE/output" \
    || fail 'the sealed driver was blamed for a probe that was never built'
[[ "$(readlink "$CASE/rustup/toolchains/trust")" == "$CASE/previous" ]] || fail 'a refused seal moved the channel'
[[ ! -e "$SEAL/PROVENANCE" ]] || fail 'a seal whose ay admission was never asked was given a PROVENANCE'
# ...and one the compiler died building says so, with its exit status and never
# an empty reason.
new_case seal-ay-probe-build-dies
printf 'synthetic trust_cg_verify metadata\n' > "$PRIVATE/test-host/libtrust_cg_verify-fixture.rmeta"
if TEST_UI_FAULT=ay-probe-dies run_promotion; then fail 'a seal was promoted with an AY-admission probe that was not built'; fi
grep -qxF 'promote: could not build the AY-admission probe against the sealed driver (exit 3; ay_probe.log). The compiler said:' "$CASE/output" \
    && grep -qxF '        | (it printed nothing)' "$CASE/output" \
    || { cat "$CASE/output" >&2; fail 'an AY-admission probe build that died was refused without its exit status and what it printed'; }
! grep -qF 'was NOT RUN' "$CASE/output" || fail 'a probe build that died was said not to have run'
[[ "$(readlink "$CASE/rustup/toolchains/trust")" == "$CASE/previous" ]] || fail 'a refused seal moved the channel'
[[ ! -e "$SEAL/PROVENANCE" ]] || fail 'a seal whose ay probe was not built was given a PROVENANCE'
new_case seal-target-libdir-was-not-asked
write_serial_command "$CASE/executor" refuses-matching '*/bin/trustc --print target-libdir'
if TEST_SERIAL_COMMAND="$CASE/executor" run_promotion; then fail 'a seal was promoted with its target libdir never read'; fi
grep -qF "promote: \`trustc --print target-libdir\` on the stage2 at $SRC was NOT RUN: $NOT_RUN it — nothing was copied." "$CASE/output" \
    && grep -qxF "    said: $REFUSED_LINE" "$CASE/output" \
    || { cat "$CASE/output" >&2; fail 'a target-libdir read that was never started ended the run without its reason'; }
assert_nothing_sealed
new_case seal-target-libdir-dies
if TEST_UI_FAULT=libdir-dies run_promotion; then fail 'a seal was promoted with its target libdir never read'; fi
grep -qF "promote: \`trustc --print target-libdir\` failed on the stage2 at $SRC (exit 3): fixture: no target libdir" "$CASE/output" \
    || { cat "$CASE/output" >&2; fail 'a target-libdir read that failed ended the run without its reason'; }
assert_nothing_sealed
# A UI row that FAILS refuses the seal, in words that send the reader to the
# rows before the source.
new_case seal-ui-gate-fails
if TEST_UI_FAULT=no-diagnostic run_promotion; then fail 'a stage2 that fails its UI rows was sealed'; fi
grep -qF "promote: stage2 at $SRC FAILS this tree's named UI tests (listed above) — refusing to seal it." "$CASE/output" \
    && grep -qF 'Each FAIL row says what the compiler printed.' "$CASE/output" \
    && grep -qF 'A row that quotes no compiler diagnostic (a compiler that was killed, or' "$CASE/output" \
    || { cat "$CASE/output" >&2; fail 'a failing UI gate did not refuse the seal in its own words'; }
assert_nothing_sealed
# ...and it is still the gate's verdict when the executor refused another row:
# a FAIL row was measured, so the refusal is the one for a compiler that
# failed, never "did not finish ... not a verdict on the toolchain".
new_case seal-ui-gate-fails-with-a-row-not-run
write_serial_command "$CASE/executor" refuses-matching '*/verifier_budget_termination.rs'
if TEST_UI_FAULT=no-diagnostic TEST_SERIAL_COMMAND="$CASE/executor" run_promotion; then fail 'a stage2 with FAIL and NOT RUN UI rows was sealed'; fi
grep -qxF '    FAIL  tests/ui/trust/r1/flip_caller_covered.rs' "$CASE/output" \
    && grep -qxF '    NOT RUN  tests/ui/trust/verifier_budget_termination.rs' "$CASE/output" \
    || { cat "$CASE/output" >&2; fail 'the fixture did not give a FAIL and a NOT RUN UI row'; }
grep -qF "promote: stage2 at $SRC FAILS this tree's named UI tests (listed above) — refusing to seal it." "$CASE/output" \
    || { cat "$CASE/output" >&2; fail 'a UI gate with a FAIL row was not refused as one that FAILS'; }
! grep -qF 'not a verdict on the toolchain' "$CASE/output" || { cat "$CASE/output" >&2; fail 'a measured FAIL row was called no verdict'; }
assert_nothing_sealed
# The identity reads of step 1b say what they were given.
new_case seal-version-names-no-rev
if COMMIT='' run_promotion; then fail 'a stage2 whose --version names no rev was sealed'; fi
grep -qF 'promote: could not read the rev out of trustc --version, which said: rustc 1.0.0 ( 2026-09-15) (trustc 1.0.0)' "$CASE/output" \
    || { cat "$CASE/output" >&2; fail 'a --version with no rev was not quoted'; }
assert_nothing_sealed
new_case seal-commit-is-not-in-the-repository
if COMMIT=0123456789abcdef0123456789abcdef01234567 run_promotion; then fail 'a stage2 of an unknown commit was sealed'; fi
grep -qF 'reports commit-hash 0123456789abcdef0123456789abcdef01234567, which is NOT a commit in' "$CASE/output" \
    && grep -qE '^    git said: fatal: ' "$CASE/output" \
    || { cat "$CASE/output" >&2; fail 'an unknown commit was refused without what git said'; }
assert_nothing_sealed

PROMOTE_OPTS=(--gate-only)
# The consumer is built and the executor will not run it: NOT RUN, by the
# probe's second step.
new_case gate-only-serial-executor-refuses-the-built-consumer
write_serial_command "$CASE/executor" refuses-matching '*/rustc_dev_probe'
touch "$CASE/before"
if TEST_SERIAL_COMMAND="$CASE/executor" run_promotion; then fail '--gate-only passed with its native consumer never run'; fi
grep -qxF "    NOT RUN  rustc-dev probe: $NOT_RUN the consumer it built, so this says nothing about it: $REFUSED_LINE" "$CASE/output" \
    && grep -qF "gate-only: REFUSED — $SRC: UI gate passed, tool-start gate passed, native rustc-dev gate NOT RUN (the serial executor refused)" "$CASE/output" \
    || { cat "$CASE/output" >&2; fail 'a consumer that was never run was not said to be'; }
assert_gate_only_changed_nothing
# The file the variable names is gone once the run is under way: the refusal
# is then this script's own (exit 1), and it is NOT RUN all the same.
new_case gate-only-serial-executor-vanishes-after-the-question
write_serial_command "$CASE/executor" vanishes-after-the-noop
touch "$CASE/before"
if TEST_SERIAL_COMMAND="$CASE/executor" run_promotion; then fail '--gate-only passed with no executor left to start a row'; fi
[[ "$(grep -cF "$NOT_RUN the compiler, so this row says nothing about it: promote: direct compiler gates require an explicit regular executable TRUST_TOOLCHAIN_SERIAL_COMMAND" "$CASE/output")" -eq 8 ]] \
    || { cat "$CASE/output" >&2; fail 'a row whose executor was gone was not NOT RUN'; }
! grep -qE '^    (FAIL|ok)  ' "$CASE/output" || { cat "$CASE/output" >&2; fail 'a row that did not run was given a verdict'; }
assert_gate_only_changed_nothing
# The file is still there, still executable by its mode, and no longer a
# program: bash answers 126 and env(1), which starts the tool rows, hands it to
# sh (any status). Every row is NOT RUN and quotes why; none is a FAIL.
new_case gate-only-serial-executor-cannot-be-executed-after-the-question
write_serial_command "$CASE/executor" unexecutable-after-the-noop
touch "$CASE/before"
if TEST_SERIAL_COMMAND="$CASE/executor" run_promotion; then fail '--gate-only passed with an executor the OS will not execute'; fi
[[ "$(grep -cF "$NOT_RUN the compiler, so this row says nothing about it: the serial executor itself can no longer be started (a no-op through it now exits " "$CASE/output")" -eq 8 ]] \
    || { cat "$CASE/output" >&2; fail 'a UI row whose executor cannot be executed was not NOT RUN'; }
[[ "$(grep -cE '^    NOT RUN  (tippy|trustdoc|trustfmt)' "$CASE/output")" -eq 6 ]] \
    || { cat "$CASE/output" >&2; fail 'a tool row whose executor cannot be executed was not NOT RUN'; }
# Each of the 15 rows (8 UI, 6 tool, the probe) carries the no-op's status and
# the end of what the shell said, which is the reason: the line opens with two
# long paths, so a clip from the left alone would cut it off.
[[ "$(grep -cE 'can no longer be started \(a no-op through it now exits [0-9]+\): .*(cannot execute|Exec format error)' "$CASE/output")" -eq 15 ]] \
    || { cat "$CASE/output" >&2; fail 'an executor that cannot be executed was not quoted with its status and the reason'; }
! grep -qF 'now exits 0)' "$CASE/output" || fail 'a no-op that was not started was said to have exited 0'
! grep -qE '^    (FAIL|ok)  ' "$CASE/output" || { cat "$CASE/output" >&2; fail 'a row that did not run was given a verdict'; }
grep -qF "gate-only: REFUSED — $SRC: UI gate NOT RUN (the serial executor refused), tool-start gate NOT RUN (the serial executor refused), native rustc-dev gate NOT RUN (the serial executor refused)" "$CASE/output" \
    || { cat "$CASE/output" >&2; fail 'an executor that cannot be executed was reported as the gates failing'; }
no_row_ends_at_its_colon
assert_gate_only_changed_nothing
# A PROGRAM THE OS WILL NOT START IS THE PROGRAM'S FAILURE. The real executor
# reports it in its refusal shape (exit 75, `refused: command launch: <OS
# error>`: measured on a driver with no interpreter, 2026-11-12) and still
# starts a no-op, so the rows FAIL and quote the error; they are not NOT RUN.
new_case gate-only-tool-cannot-be-launched
write_serial_command "$CASE/executor" cannot-launch '*/bin/tippy-driver *'
touch "$CASE/before"
if TEST_SERIAL_COMMAND="$CASE/executor" run_promotion; then fail '--gate-only passed a driver the OS will not start'; fi
grep -qxF '    FAIL  tippy-driver.clean' "$CASE/output" && grep -qxF '    FAIL  tippy-driver.lint' "$CASE/output" \
    && [[ "$(grep -cxF '          | trust-serial-command: refused: command launch: No such file or directory (os error 2)' "$CASE/output")" -eq 2 ]] \
    && grep -qF "gate-only: REFUSED — $SRC: UI gate passed, tool-start gate FAILED, native rustc-dev gate passed" "$CASE/output" \
    || { cat "$CASE/output" >&2; fail 'a driver that cannot be launched was not a FAILED tool-start gate'; }
! grep -qF 'NOT RUN' "$CASE/output" || { cat "$CASE/output" >&2; fail 'a driver that cannot be launched was reported as a refusal of the run'; }
assert_gate_only_changed_nothing
# ...and while the executor starts no no-op either, the same line is a refusal
# of the run: nothing tells the program's failure from the caller's, so the
# rows are NOT RUN and quote it.
new_case gate-only-tool-cannot-be-launched-and-no-noop-starts
write_serial_command "$CASE/executor" cannot-launch-then-unadmitted '*/bin/tippy-driver *'
touch "$CASE/before"
if TEST_SERIAL_COMMAND="$CASE/executor" run_promotion; then fail '--gate-only passed a driver that was never started'; fi
grep -qxF '    NOT RUN  tippy-driver.clean' "$CASE/output" && grep -qxF '    NOT RUN  tippy-driver.lint' "$CASE/output" \
    && [[ "$(grep -cxF "          $NOT_RUN bin/tippy-driver, so this row says nothing about it: trust-serial-command: refused: command launch: No such file or directory (os error 2)" "$CASE/output")" -eq 2 ]] \
    && grep -qF "gate-only: REFUSED — $SRC: UI gate passed, tool-start gate NOT RUN (the serial executor refused), native rustc-dev gate passed" "$CASE/output" \
    || { cat "$CASE/output" >&2; fail 'a launch failure the executor would not confirm was not NOT RUN'; }
! grep -qE '^    FAIL  ' "$CASE/output" || { cat "$CASE/output" >&2; fail 'a row that did not run was given a verdict'; }
assert_gate_only_changed_nothing
# The same for every command at once: an executor that says `command launch:`
# for everything and starts no no-op either is the executor that cannot launch.
# The UI rows and the probe are NOT RUN too, and none is a FAIL.
new_case gate-only-executor-launches-nothing
cat > "$CASE/executor" <<'SH'
#!/usr/bin/env bash
# The first no-op starts (the question before any gate); after it nothing does.
if [[ "$(basename "${2:-}")" == true && ! -e "$0.asked" ]]; then : > "$0.asked"; shift; exec "$@"; fi
printf 'trust-serial-command: refused: command launch: Resource temporarily unavailable (os error 11)\n' >&2
exit 75
SH
chmod +x "$CASE/executor"
touch "$CASE/before"
if TEST_SERIAL_COMMAND="$CASE/executor" run_promotion; then fail '--gate-only passed with an executor that launches nothing'; fi
[[ "$(grep -cE '^    NOT RUN  tests/ui/trust/' "$CASE/output")" -eq 8 ]] \
    && [[ "$(grep -cF "$NOT_RUN the compiler, so this row says nothing about it: trust-serial-command: refused: command launch: Resource temporarily unavailable (os error 11)" "$CASE/output")" -eq 8 ]] \
    && grep -qF "gate-only: REFUSED — $SRC: UI gate NOT RUN (the serial executor refused), tool-start gate NOT RUN (the serial executor refused), native rustc-dev gate NOT RUN (the serial executor refused)" "$CASE/output" \
    || { cat "$CASE/output" >&2; fail 'an executor that launches nothing was read as failures of the toolchain'; }
! grep -qE '^    (FAIL|ok)  ' "$CASE/output" || { cat "$CASE/output" >&2; fail 'a row the executor could launch nothing for was given a verdict'; }
assert_gate_only_changed_nothing
# A FAIL ROW IS THE GATE'S VERDICT, WHATEVER ELSE DID NOT RUN. A gate with rows
# that failed and one row the executor refused used to be summarised as NOT
# RUN (the first form of this change returned 2 whenever a row did not run),
# which a seal reads as "not a verdict on the toolchain". Each gate, with both
# kinds of row, is FAILED.
new_case gate-only-ui-rows-fail-and-one-is-not-run
write_serial_command "$CASE/executor" refuses-matching '*/verifier_budget_termination.rs'
touch "$CASE/before"
if TEST_UI_FAULT=no-diagnostic TEST_SERIAL_COMMAND="$CASE/executor" run_promotion; then fail '--gate-only passed a UI gate with FAIL and NOT RUN rows'; fi
grep -qxF '    FAIL  tests/ui/trust/r1/flip_caller_covered.rs' "$CASE/output" \
    && grep -qxF '    NOT RUN  tests/ui/trust/verifier_budget_termination.rs' "$CASE/output" \
    || { cat "$CASE/output" >&2; fail 'the fixture did not give the UI gate a FAIL row and a NOT RUN row'; }
grep -qF "gate-only: REFUSED — $SRC: UI gate FAILED, tool-start gate passed, native rustc-dev gate passed" "$CASE/output" \
    || { cat "$CASE/output" >&2; fail 'a UI gate with a FAIL row beside a NOT RUN row was not FAILED'; }
assert_gate_only_changed_nothing
new_case gate-only-tool-rows-fail-and-one-is-not-run
write_tippy_driver "$SRC/bin/tippy-driver" panic
write_serial_command "$CASE/executor" refuses-matching '*/bin/trustfmt *'
touch "$CASE/before"
if TEST_SERIAL_COMMAND="$CASE/executor" run_promotion; then fail '--gate-only passed a tool-start gate with FAIL and NOT RUN rows'; fi
grep -qxF '    FAIL  tippy-driver.clean' "$CASE/output" && grep -qxF '    NOT RUN  trustfmt.format' "$CASE/output" \
    || { cat "$CASE/output" >&2; fail 'the fixture did not give the tool-start gate a FAIL row and a NOT RUN row'; }
grep -qF "gate-only: REFUSED — $SRC: UI gate passed, tool-start gate FAILED, native rustc-dev gate passed" "$CASE/output" \
    || { cat "$CASE/output" >&2; fail 'a tool-start gate with a FAIL row beside a NOT RUN row was not FAILED'; }
assert_gate_only_changed_nothing
# A tool that dies without a word: its rows say so, and what every failing
# row printed is kept where the gate says.
new_case gate-only-tool-dies-without-a-word
printf '#!/bin/sh\ncase "${1:-}" in --version|-V|--help|"") printf "tippy 1.0.0-fixture\\n"; exit 0 ;; esac\nexit 3\n' > "$SRC/bin/tippy-driver"
touch "$CASE/before"
if run_promotion; then fail '--gate-only passed a driver that exits 3 on every start'; fi
[[ "$(grep -cxF '          | (it printed nothing)' "$CASE/output")" -eq 2 ]] \
    || { cat "$CASE/output" >&2; fail 'a silent driver was not said to have printed nothing on its two rows'; }
KEPT="$(sed -n 's/^    everything each row printed is kept under \([^ ]*\) (<row>\.txt)$/\1/p' "$CASE/output")"
[[ -n "$KEPT" && -f "$KEPT/tippy-driver.clean.txt" ]] && grep -qF 'could not compile' "$KEPT/tippy.frontend.txt" \
    || { cat "$CASE/output" >&2; fail 'the tool-start gate did not keep what its failing rows printed'; }
assert_gate_only_changed_nothing
# A B1 binary that exits 101 and writes nothing: the row says its stderr was empty.
new_case gate-only-b1-binary-panics-without-a-word
touch "$CASE/before"
if TEST_B1_PROBE=mute run_promotion; then fail '--gate-only passed a B1 binary that names no panic'; fi
[[ "$(grep -cxF '          got instead:   (its stderr was empty)' "$CASE/output")" -eq 2 ]] \
    || { cat "$CASE/output" >&2; fail 'a B1 binary with an empty stderr was not said to have one'; }
no_row_ends_at_its_colon
assert_gate_only_changed_nothing
unset PROMOTE_OPTS

PROMOTE_OPTS=(--provenance)
# A compiler that answers -vV and names no commit: the answer is quoted.
new_case provenance-compiler-names-no-commit
printf '#!/bin/sh\necho "host: test-host"\n' > "$SRC/bin/trustc"
if run_promotion; then fail '--provenance reported a compiler that names no commit'; fi
grep -qF 'promote: this trustc reports no commit-hash at all; its -vV said:' "$CASE/output" \
    && grep -qxF '        | host: test-host' "$CASE/output" \
    || { cat "$CASE/output" >&2; fail 'a -vV with no commit-hash was not quoted'; }
unset PROMOTE_OPTS

# A RELATIVE TRUST_TOOLCHAIN_HOME is the caller's directory plus that path. It
# used to reach the executor as a relative program at step 6: refused after
# the copy, in words that blamed the sealed compiler.
new_case seal-relative-toolchain-home
( cd "$CASE" && TEST_TOOLCHAIN_HOME=sealed run_promotion ) || { cat "$CASE/output" >&2; fail 'a relative TRUST_TOOLCHAIN_HOME was refused'; }
[[ -f "$SEAL/PROVENANCE" && "$(readlink "$CASE/rustup/toolchains/trust")" == "$SEAL" ]] \
    || { cat "$CASE/output" >&2; fail 'a relative TRUST_TOOLCHAIN_HOME did not seal and admit by its absolute path'; }

# A RELATIVE TMPDIR makes every scratch directory relative. The rustc-dev probe
# starts the consumer it built there through the executor, which starts an
# absolute program only: the row was NOT RUN, "run it again under a slot".
new_case relative-tmpdir
mkdir "$CASE/reltmp"
PROMOTE_OPTS=(--gate-only)
( cd "$CASE" && TEST_TMPDIR=reltmp run_promotion ) || { cat "$CASE/output" >&2; fail '--gate-only was refused under a relative TMPDIR'; }
grep -qF "gate-only: PASS — $SRC would clear" "$CASE/output" || { cat "$CASE/output" >&2; fail '--gate-only did not pass under a relative TMPDIR'; }
unset PROMOTE_OPTS
( cd "$CASE" && TEST_TMPDIR=reltmp run_promotion ) || { cat "$CASE/output" >&2; fail 'a seal was refused under a relative TMPDIR'; }
[[ -f "$SEAL/PROVENANCE" && "$(readlink "$CASE/rustup/toolchains/trust")" == "$SEAL" ]] \
    || { cat "$CASE/output" >&2; fail 'a relative TMPDIR did not seal and admit'; }
! grep -qF 'NOT RUN' "$CASE/output" || { cat "$CASE/output" >&2; fail 'a row was NOT RUN under a relative TMPDIR'; }
[[ "$(cat "$CASE/probe-run-sysroots")" == "$(cd "$SRC" && pwd -P)"$'\n'"$(cd "$SRC" && pwd -P)"$'\n'"$(cd "$SEAL" && pwd -P)" ]] \
    || { cat "$CASE/probe-run-sysroots" >&2; fail 'the rustc-dev consumer did not run three times under a relative TMPDIR'; }
[[ -z "$(ls -A "$CASE/reltmp")" ]] || fail 'a passing run left scratch under a relative TMPDIR'
# ...and a refused one names the directory it kept from the root, so that the
# line can be followed from any directory.
new_case relative-tmpdir-names-what-it-kept
mkdir "$CASE/reltmp"
if ( cd "$CASE" && TEST_UI_FAULT=hello-dies TEST_TMPDIR=reltmp run_promotion ); then fail 'a seal whose hello world dies was promoted'; fi
KEPT="$(sed -n 's/^promote: everything the checks of the sealed copy wrote is kept in //p' "$CASE/output")"
[[ "$KEPT" == "$CASE/reltmp/"* && -f "$KEPT/h.txt" ]] \
    || { cat "$CASE/output" >&2; fail 'a refusal under a relative TMPDIR did not name the kept directory from the root'; }

# THE REST OF THE SEAL'S REFUSALS SAY WHY TOO. Each of these used to end the
# run with one sentence that named no cause, or with nothing.
# The hello world builds and does not run.
new_case seal-hello-world-dies
if TEST_UI_FAULT=hello-dies run_promotion; then fail 'a seal whose hello world dies was promoted'; fi
grep -qF "promote: hello world did not run: the program the sealed compiler built exited 9 and printed '' (exit 0 and 'ok' were required); it said on stderr: fixture: hello died" "$CASE/output" \
    || { cat "$CASE/output" >&2; fail 'a hello world that died was not quoted'; }
KEPT="$(sed -n 's/^promote: everything the checks of the sealed copy wrote is kept in //p' "$CASE/output")"
[[ -n "$KEPT" && -f "$KEPT/h.rs" && -f "$KEPT/h.run-stderr.txt" ]] \
    || { cat "$CASE/output" >&2; fail 'what the hello world printed was not kept'; }
[[ "$(readlink "$CASE/rustup/toolchains/trust")" == "$CASE/previous" ]] || fail 'a hello world that died moved the channel'
# That refusal came after the copy step, so the copy is on disk without a
# PROVENANCE file. The re-run names it as that, not as an immutable artifact,
# and overwrites nothing; a finished seal is still refused in the old words.
[[ -d "$SEAL" && ! -e "$SEAL/PROVENANCE" ]] || fail 'the refused promotion left no unfinished copy to re-run against'
if run_promotion; then fail 'a promotion over an unfinished copy went ahead'; fi
grep -qF "promote: artifact $SEAL already exists and holds no PROVENANCE file." "$CASE/output" \
    && grep -qF 'It is not a seal this script wrote to the end.' "$CASE/output" \
    || { cat "$CASE/output" >&2; fail 'an unfinished copy was not named as one'; }
! grep -qF 'artifacts are IMMUTABLE' "$CASE/output" || fail 'an unfinished copy was called an immutable artifact'
[[ -d "$SEAL" && ! -e "$SEAL/PROVENANCE" ]] || fail 'the re-run changed the unfinished copy'
# The hello world prints `ok` and exits 3. Until 2026-11-12 only what it
# printed was read, and a program that died after printing was sealed.
new_case seal-hello-world-prints-ok-and-exits-nonzero
if TEST_UI_FAULT=hello-exits-3 run_promotion; then fail 'a seal whose hello world prints ok and exits 3 was promoted'; fi
grep -qF "promote: hello world did not run: the program the sealed compiler built exited 3 and printed 'ok' (exit 0 and 'ok' were required); it said on stderr: (it printed nothing)" "$CASE/output" \
    || { cat "$CASE/output" >&2; fail 'a hello world that printed ok and exited 3 was not refused for its exit status'; }
[[ "$(readlink "$CASE/rustup/toolchains/trust")" == "$CASE/previous" ]] || fail 'a hello world that exited 3 moved the channel'
[[ ! -e "$SEAL/PROVENANCE" && ! -e "$CASE/sealed/trust-current" && ! -L "$CASE/sealed/trust-current" ]] \
    || fail 'a hello world that exited 3 left a finished seal'
# The hello world does not compile: the compiler's own status and words, and
# what it printed is kept.
new_case seal-hello-world-does-not-compile
if TEST_UI_FAULT=hello-does-not-compile run_promotion; then fail 'a seal whose compiler cannot compile a hello world was promoted'; fi
grep -qF 'promote: sealed toolchain cannot compile a hello world (exit 1): error: fixture: hello does not compile' "$CASE/output" \
    || { cat "$CASE/output" >&2; fail 'a hello world that did not compile was not quoted'; }
KEPT="$(sed -n 's/^promote: everything the checks of the sealed copy wrote is kept in //p' "$CASE/output")"
[[ -n "$KEPT" && -f "$KEPT/h.rs" ]] && grep -qxF 'error: fixture: hello does not compile' "$KEPT/h.txt" \
    || { cat "$CASE/output" >&2; fail 'what the hello world compile printed was not kept'; }
[[ "$(readlink "$CASE/rustup/toolchains/trust")" == "$CASE/previous" ]] || fail 'a hello world that did not compile moved the channel'
new_case seal-exists-already
run_promotion || { cat "$CASE/output" >&2; fail 'the canonical fixture was refused'; }
[[ -f "$SEAL/PROVENANCE" ]] || fail 'a finished seal carries no PROVENANCE file'
if run_promotion; then fail 'a finished seal was promoted over'; fi
grep -qF "promote: artifact $SEAL already exists — artifacts are IMMUTABLE" "$CASE/output" \
    || { cat "$CASE/output" >&2; fail 'a finished seal was not refused as immutable'; }

# --provenance starts no compiler and asks for no executor.
PROMOTE_OPTS=(--provenance)
new_case provenance-needs-no-serial-executor
TEST_SERIAL_COMMAND='' run_promotion || { cat "$CASE/output" >&2; fail '--provenance asked for a serial executor'; }
grep -qE '^==> provenance: ' "$CASE/output" || { cat "$CASE/output" >&2; fail '--provenance did not report the class'; }
# A compiler the loader cannot start: this mode reads `trustc -vV` first, and
# the read was a pipeline under pipefail that ended the script with exit 127
# and not one word.
new_case provenance-compiler-cannot-load
cat > "$SRC/bin/trustc" <<'SH'
#!/bin/sh
echo "trustc: error while loading shared libraries: librustc_driver-fixture.so: cannot open shared object file: No such file or directory" >&2
exit 127
SH
if run_promotion; then fail '--provenance reported a compiler that cannot start'; fi
grep -qF "promote: $SRC/bin/trustc -vV exited 127, so the commit this compiler was built from is not known and there is nothing to report. It said:" "$CASE/output" \
    && grep -qxF '        | trustc: error while loading shared libraries: librustc_driver-fixture.so: cannot open shared object file: No such file or directory' "$CASE/output" \
    || { cat "$CASE/output" >&2; fail 'a compiler that cannot start ended --provenance without its reason'; }
unset PROMOTE_OPTS

# The usage names the variable and how to build what it names, and needs
# neither to print.
new_case help-names-the-serial-executor
env -i PATH=/usr/bin:/bin bash "$FIXTURE_REPO/scripts/promote-toolchain.sh" --help > "$CASE/output" 2>&1 \
    || { cat "$CASE/output" >&2; fail '--help needed something to print'; }
grep -qF 'TRUST_TOOLCHAIN_SERIAL_COMMAND' "$CASE/output" \
    && grep -qF -- '--features serial-command --bin trust-serial-command' "$CASE/output" \
    && grep -qF 'scripts/build-slot --cpus 1 -- bash' "$CASE/output" \
    || { cat "$CASE/output" >&2; fail 'the usage does not say what a gate needs'; }

# AN OLD SEAL. Every seal cut before 2026-10-12 has a PROVENANCE without the
# stage_receipt and tool_start_gate lines (and the three cut that day carry a
# receipt all the same). Nothing that reads a seal may come to need them:
# `--provenance` prints the record as it is, `--gate-only` answers by starting
# the tools again, and the output contract does not open the file.
old_format_provenance() { # <PROVENANCE>: the same record, as written before 2026-10-12
    "$PYTHON_BIN" - "$1" <<'PY'
import re, sys
text = open(sys.argv[1]).read()
for pattern, replacement in (
    (r"# THE TOOL-START GATE.*?\ntool_start_gate_not_shipped=[^\n]*\n", ""),
    (r"\n# \(f\) THE STAGE RECEIPT.*?\nstage_receipt_recreator_argv=[^\n]*\n", ""),
    (r"#     No seed-STAIRCASE record: promote was given no --lineage\. What this\n"
     r"#     seal does say about its stage0 is the stage receipt, \(f\) below\.\n",
     "#     Not recorded: promote was given no --lineage record, and nothing\n"
     "#     else on this path observes stage0. Absence is not evidence either way.\n"),
):
    text, count = re.subn(pattern, replacement, text, flags=re.S)
    if count != 1:
        sys.exit(f"expected one match of {pattern!r}, found {count}")
sys.stdout.write(text)
PY
}
new_case old-format-provenance
OLD_SEAL="$RECORDED_SEAL"
old_format_provenance "$OLD_SEAL/PROVENANCE" > "$CASE/old-format" \
    || fail 'the seal to age does not carry the lines a seal records since 2026-10-12'
! grep -qE '^(stage_receipt|tool_start_gate)' "$CASE/old-format" || fail 'the old-format fixture still carries a new line'
grep -q '^ay_admission=' "$CASE/old-format" && grep -qx 'stage0_lineage=absent' "$CASE/old-format" \
    && grep -q '^artifact_content_sha256=' "$CASE/old-format" || fail 'the old-format fixture lost a line every seal has'
cp "$CASE/old-format" "$OLD_SEAL/PROVENANCE"
SRC="$OLD_SEAL"
PROMOTE_OPTS=(--provenance)
run_promotion || { cat "$CASE/output" >&2; fail '--provenance refused a seal with an old-format PROVENANCE'; }
cmp "$CASE/output" "$CASE/old-format" || fail '--provenance did not print an old-format PROVENANCE as it is'
PROMOTE_OPTS=(--gate-only)
touch "$CASE/before"
run_promotion || { cat "$CASE/output" >&2; fail '--gate-only refused a seal with an old-format PROVENANCE'; }
grep -qF "gate-only: PASS — $OLD_SEAL would clear the pre-promotion UI gate and the tool-start gate" "$CASE/output" \
    || { cat "$CASE/output" >&2; fail '--gate-only did not pass a seal with an old-format PROVENANCE'; }
assert_gate_only_changed_nothing
unset PROMOTE_OPTS
env -i HOME="$CASE/home" TMPDIR="$WORK" PATH="$WORK/fake-bin:/usr/bin:/bin:/usr/sbin:/sbin" TEST_COMMIT="$COMMIT" \
    TRUST_VERIFY_PROBE_TIMEOUT="$FIXTURE_PROBE_TIMEOUT" \
    sh "$FIXTURE_REPO/tools/verify-toolchain.sh" "$OLD_SEAL" > "$CASE/surface" 2>&1 \
    || { cat "$CASE/surface" >&2; fail 'the output contract refused a seal with an old-format PROVENANCE'; }
cmp "$OLD_SEAL/PROVENANCE" "$CASE/old-format" || fail 'a read-only path rewrote the old-format PROVENANCE'

# A run that a signal ends in step 6 says ON ITS OWN STDERR where the files of
# its checks are. bash applies the redirections of a shell-function call to the
# shell itself, and a fatal signal runs the EXIT trap with them still in force:
# until 2026-11-12 the four redirected calls of step 6 (the hello world,
# `rustc -Z help`, each tool-start row, the ay probe) sent the trap's one line
# into the call's own output file, inside the directory the line names, and the
# terminal showed `Terminated` alone. The fixture tool of the sealed copy sends
# SIGTERM to the seal script from inside the call: to the outermost ancestor
# running it, because a subshell of the script has the same command line.
terminated_in_step_6() { # <case> <fixture tool> <glob over that tool's arguments>
    local hook status=0
    new_case "$1"
    cat > "$CASE/terminate-the-seal" <<SH
#!/bin/sh
p="\$1"; seal=''
while ps -o command= -p "\$p" 2>/dev/null | grep -qF '$FIXTURE_REPO/scripts/promote-toolchain.sh'; do
    seal="\$p"; p="\$(ps -o ppid= -p "\$p" | tr -d ' ')"
done
[ -n "\$seal" ] || { echo 'fixture: found no seal script to terminate' >&2; exit 0; }
kill -TERM "\$seal"
n=0; while kill -0 "\$seal" 2>/dev/null && [ "\$n" -lt 100 ]; do sleep 0.1; n=\$((n + 1)); done
SH
    chmod +x "$CASE/terminate-the-seal"
    hook="case \"\$0\" in */sealed/*) case \"\$*\" in $3) \"$CASE/terminate-the-seal\" \"\$PPID\" ;; esac ;; esac"
    awk -v hook="$hook" 'NR == 3 { print hook } { print }' "$SRC/bin/$2" > "$CASE/hooked"
    cat "$CASE/hooked" > "$SRC/bin/$2"
    [[ "$2" != trustc ]] || cp "$SRC/bin/trustc" "$SRC/bin/rustc"
    [[ "$1" != *-ay-probe ]] \
        || printf 'synthetic trust_cg_verify metadata\n' > "$PRIVATE/test-host/libtrust_cg_verify-fixture.rmeta"
    # The subshell takes the shell's own `Terminated` report of its child.
    ( run_promotion ) 2>/dev/null || status=$?
    [[ "$status" -eq 143 ]] || { cat "$CASE/output" >&2; fail "$1: the fixture did not end the run with SIGTERM (exit $status)"; }
    KEPT="$(sed -n 's/^promote: everything the checks of the sealed copy wrote is kept in //p' "$CASE/output")"
    [[ -n "$KEPT" && -f "$KEPT/h.rs" ]] \
        || { cat "$CASE/output" >&2; fail "$1: a run that a signal ended did not say where the files of its checks are"; }
    ! grep -rqF 'promote: everything the checks of the sealed copy wrote is kept in' "$KEPT" \
        || fail "$1: the line that names the kept directory was written into a file inside it"
    [[ "$(readlink "$CASE/rustup/toolchains/trust")" == "$CASE/previous" ]] || fail "$1: a terminated run moved the channel"
}
terminated_in_step_6 seal-terminated-in-the-hello-world trustc '*/h.rs'
terminated_in_step_6 seal-terminated-in-z-help trustc '"-Z help"'
terminated_in_step_6 seal-terminated-in-a-tool-start-row tippy-driver '*--out-dir*'
terminated_in_step_6 seal-terminated-in-the-ay-probe trustc '*/ay_probe.rs'

[[ "$((CASE_COUNT + CASES_NOT_RUN))" -eq 236 ]] || fail "expected 236 cases, ran $CASE_COUNT and did not run $CASES_NOT_RUN"
NOT_RUN_NOTE=""
[[ "$CASES_NOT_RUN" -eq 0 ]] || NOT_RUN_NOTE="; $CASES_NOT_RUN NOT RUN as root: lock-cannot-be-asked, stdlib-listing-fails"
echo "Promotion toolchain tests: $CASE_COUNT cases passed (synthetic tools; no installed channel changes$NOT_RUN_NOTE)"
