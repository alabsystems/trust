#!/bin/bash
# Smoke test: a built local tRust sysroot behaves like a practical standalone
# Trust toolchain. Current stage2 builds expose Trust-preferred tools plus only
# the same-sysroot rustc/cargo compatibility entrypoints.
#
# Exercises the standalone stage2 compatibility flow through sysroot-owned
# `targo`, `trustc`, `trustdoc`, and `targo-trust` tools in `stage2/bin`.
#
# This runs against a fresh temp crate while checking that the local stage2
# sysroot is self-contained. It intentionally does not require rustup linking:
# when linked, `bin/rustc` is the same-sysroot compatibility alias.
#
# It also verifies targo build/check/test/doc/fmt/clippy surfaces plus
# `targo trust check` with the default backend and trust-cg when available.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
TRUST_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
HOST_RUSTUP_BIN="$(command -v rustup 2>/dev/null || true)"
if [ -z "$HOST_RUSTUP_BIN" ] && [ -x "${CARGO_HOME:-$HOME/.cargo}/bin/rustup" ]; then
    HOST_RUSTUP_BIN="${CARGO_HOME:-$HOME/.cargo}/bin/rustup"
fi
echo "=== tRust Smoke Test: standalone trust toolchain ==="
echo

skip_test() {
    if [ "${TRUST_E2E_ALLOW_SKIP:-0}" = "1" ]; then
        printf 'SKIP: %s\n' "$1" >&2
        exit 0
    fi
    fail_test "$1 (set TRUST_E2E_ALLOW_SKIP=1 only for local diagnostics)"
}

fail_test() {
    printf 'FAIL: %s\n' "$1" >&2
    exit 1
}

canonicalize_dir() {
    (
        cd "$1"
        pwd -P
    )
}

canonicalize_file() {
    local path="$1"
    local dir
    local base

    dir="$(dirname "$path")"
    base="$(basename "$path")"
    printf '%s/%s\n' "$(canonicalize_dir "$dir")" "$base"
}

require_executable() {
    if [ ! -x "$1" ]; then
        fail_test "missing executable: $1"
    fi
}

require_directory() {
    if [ ! -d "$1" ]; then
        fail_test "missing directory: $1"
    fi
}

require_linked_tool() {
    local tool="$1"
    local path
    local expected
    local actual_path
    local expected_path

    if ! path="$("$HOST_RUSTUP_BIN" which --toolchain trust "$tool" 2>&1)"; then
        fail_test "linked trust toolchain is missing $tool"
    fi
    require_executable "$path"
    expected="$BIN_DIR/$tool"
    require_executable "$expected"

    actual_path="$(canonicalize_file "$path")"
    expected_path="$(canonicalize_file "$expected")"
    if [ "$actual_path" != "$expected_path" ]; then
        fail_test "linked trust tool $tool resolves outside exact stage2 bin surface: expected $expected_path, got $path"
    fi
}

require_alias_pair() {
    local compat="$1"
    local trust="$2"
    local compat_path="$BIN_DIR/$compat"
    local trust_path="$BIN_DIR/$trust"

    require_executable "$compat_path"
    require_executable "$trust_path"
    if ! cmp -s "$compat_path" "$trust_path"; then
        fail_test "alias pair $compat/$trust are not byte-identical same-surface artifacts"
    fi
}

current_trust_path() {
    "$HOST_RUSTUP_BIN" toolchain list -v | awk '$1 == "trust" { print $NF; exit }'
}

run_stage2_targo() {
    env -u RUSTC -u TRUSTC -u RUSTDOC -u RUSTFMT -u CLIPPY_DRIVER \
        -u CARGO_BUILD_RUSTC -u CARGO_BUILD_RUSTDOC -u RUSTUP_TOOLCHAIN \
        -u RUSTC_WRAPPER -u RUSTC_WORKSPACE_WRAPPER \
        -u CARGO_BUILD_RUSTC_WRAPPER -u CARGO_BUILD_RUSTC_WORKSPACE_WRAPPER \
        -u RUSTFLAGS -u RUSTDOCFLAGS -u CARGO_ENCODED_RUSTFLAGS \
        -u DYLD_LIBRARY_PATH -u LD_LIBRARY_PATH \
        PATH="$BIN_DIR:$PATH" \
        "$TARGO_BIN" "$@"
}

run_linked_targo() {
    if [ "${LINKED_TARGO_AVAILABLE:-0}" != "1" ]; then
        run_stage2_targo "$@"
        return
    fi

    env -u RUSTC -u TRUSTC -u RUSTDOC -u RUSTFMT -u CLIPPY_DRIVER \
        -u CARGO_BUILD_RUSTC -u CARGO_BUILD_RUSTDOC -u RUSTUP_TOOLCHAIN \
        -u RUSTC_WRAPPER -u RUSTC_WORKSPACE_WRAPPER \
        -u CARGO_BUILD_RUSTC_WRAPPER -u CARGO_BUILD_RUSTC_WORKSPACE_WRAPPER \
        -u RUSTFLAGS -u RUSTDOCFLAGS -u CARGO_ENCODED_RUSTFLAGS \
        -u DYLD_LIBRARY_PATH -u LD_LIBRARY_PATH \
        "$HOST_RUSTUP_BIN" run trust targo "$@"
}

run_linked_tool() {
    if [ "${LINKED_TARGO_AVAILABLE:-0}" != "1" ]; then
        env -u RUSTC -u TRUSTC -u RUSTDOC -u RUSTFMT -u CLIPPY_DRIVER \
            -u CARGO_BUILD_RUSTC -u CARGO_BUILD_RUSTDOC -u RUSTUP_TOOLCHAIN \
            -u RUSTC_WRAPPER -u RUSTC_WORKSPACE_WRAPPER \
            -u CARGO_BUILD_RUSTC_WRAPPER -u CARGO_BUILD_RUSTC_WORKSPACE_WRAPPER \
            -u RUSTFLAGS -u RUSTDOCFLAGS -u CARGO_ENCODED_RUSTFLAGS \
            -u DYLD_LIBRARY_PATH -u LD_LIBRARY_PATH \
            PATH="$BIN_DIR:$PATH" \
            "$@"
        return
    fi

    env -u RUSTC -u TRUSTC -u RUSTDOC -u RUSTFMT -u CLIPPY_DRIVER \
        -u CARGO_BUILD_RUSTC -u CARGO_BUILD_RUSTDOC -u RUSTUP_TOOLCHAIN \
        -u RUSTC_WRAPPER -u RUSTC_WORKSPACE_WRAPPER \
        -u CARGO_BUILD_RUSTC_WRAPPER -u CARGO_BUILD_RUSTC_WORKSPACE_WRAPPER \
        -u RUSTFLAGS -u RUSTDOCFLAGS -u CARGO_ENCODED_RUSTFLAGS \
        -u DYLD_LIBRARY_PATH -u LD_LIBRARY_PATH \
        "$HOST_RUSTUP_BIN" run trust "$@"
}

run_linked_cargo() {
    run_linked_tool cargo "$@"
}

run_alias_version_check() {
    local tool="$1"
    local output

    if ! output="$(run_linked_tool "$tool" --version 2>&1)"; then
        fail_test "Rust-compatible alias $tool --version failed
$output"
    fi
    if [ -z "$output" ]; then
        fail_test "Rust-compatible alias $tool --version produced no output"
    fi
    echo "$tool: $output"
}

# trust-cg is linked into trustc, not shipped as a loadable codegen plugin: a
# plugin would carry a second copy of rustc_span and its scoped TLS. Nothing
# ever lands in the sysroot's codegen-backends directory for it, so the only
# authority on whether *this* trustc owns the backend is trustc itself. The
# same question also yields the capability answer, since backend selection is
# fatal when the name cannot be resolved.
trust_cg_linked_crate_types() {
    "$TRUSTC_BIN" --print=supported-crate-types -Zunstable-options \
        -Zcodegen-backend=trust-cg 2>/dev/null
}

LOCAL_SYSROOT=""
CANDIDATES=(
    "$TRUST_ROOT/build/host/stage2"
    "$TRUST_ROOT/build/aarch64-unknown-linux-gnu/stage2"
    "$TRUST_ROOT/build/aarch64-apple-darwin/stage2"
    "$TRUST_ROOT/build/x86_64-unknown-linux-gnu/stage2"
    "$TRUST_ROOT/build/x86_64-apple-darwin/stage2"
)

for candidate in "${CANDIDATES[@]}"; do
    if [ -x "$candidate/bin/trustc" ]; then
        LOCAL_SYSROOT="$candidate"
        break
    fi
done

if [ -z "$LOCAL_SYSROOT" ]; then
    skip_test "local toolchain not found (build with ./x.py build --stage 2 compiler/rustc library/std)"
fi

LOCAL_SYSROOT="$(canonicalize_dir "$LOCAL_SYSROOT")"
BIN_DIR="$LOCAL_SYSROOT/bin"
TARGET_TRIPLE="$(basename "$(dirname "$LOCAL_SYSROOT")")"
STAGE_NAME="$(basename "$LOCAL_SYSROOT")"
BUILD_ROOT="$(dirname "$LOCAL_SYSROOT")"
TOOLS_BIN="$BIN_DIR"
TARGO_BIN="$TOOLS_BIN/targo"
TRUSTC_BIN="$BIN_DIR/trustc"
RUSTDOC_BIN="$TOOLS_BIN/trustdoc"
RUSTC_DEPS_DIR="$(dirname "$LOCAL_SYSROOT")/${STAGE_NAME}-rustc/$TARGET_TRIPLE/release/deps"
PREV_STAGE_NAME=""
case "$STAGE_NAME" in
    stage[1-9]*)
        PREV_STAGE_NAME="stage$(( ${STAGE_NAME#stage} - 1 ))"
        ;;
esac
PREV_RUSTC_DEPS_DIR=""
if [ -n "$PREV_STAGE_NAME" ]; then
    PREV_RUSTC_DEPS_DIR="$BUILD_ROOT/${PREV_STAGE_NAME}-rustc/$TARGET_TRIPLE/release/deps"
fi
export PATH="$TOOLS_BIN:$BIN_DIR:$PATH"
export RUSTC="$TRUSTC_BIN"
export TRUSTC="$TRUSTC_BIN"
export RUSTDOC="$RUSTDOC_BIN"
export RUSTFMT="$TOOLS_BIN/trustfmt"
require_executable "$TARGO_BIN"
require_executable "$TRUSTC_BIN"
require_executable "$RUSTDOC"

for trust_tool in \
    trustc \
    targo \
    targo-trust \
    trustd \
    trustdoc \
    trustfmt \
    targo-fmt \
    tippy \
    targo-tippy \
    tippy-driver \
    trust-analyzer
do
    require_executable "$BIN_DIR/$trust_tool"
done
for alias_pair in \
    rustc:trustc \
    cargo:targo
do
    require_alias_pair "${alias_pair%:*}" "${alias_pair#*:}"
done
for retired_debugger in rust-gdb rust-gdbgui rust-lldb rust-windbg.cmd
do
    if [ -e "$BIN_DIR/$retired_debugger" ]; then
        fail_test "forbidden Rust-named debugger entrypoint is installed: $BIN_DIR/$retired_debugger"
    fi
done
for trust_debugger in trust-gdb trust-gdbgui trust-lldb trust-windbg.cmd
do
    if [ -e "$BIN_DIR/$trust_debugger" ]; then
        require_executable "$BIN_DIR/$trust_debugger"
    fi
done
if [ -x "$BIN_DIR/trust-gdbgui" ]; then
    if ! "$BIN_DIR/trust-gdbgui" --help 2>&1 | grep -q '^trust-gdbgui$'; then
        fail_test "trust-gdbgui --help did not use Trust-prefixed invocation name"
    fi
fi
if [ -e "$BIN_DIR/trust-miri" ] \
    || [ -e "$BIN_DIR/targo-miri" ] \
    || [ -e "$BIN_DIR/miri" ] \
    || [ -e "$BIN_DIR/cargo-miri" ]; then
    require_executable "$BIN_DIR/trust-miri"
    require_executable "$BIN_DIR/targo-miri"
    if [ -e "$BIN_DIR/miri" ] || [ -e "$BIN_DIR/cargo-miri" ]; then
        fail_test "optional Miri surface contains forbidden Rust-named aliases"
    fi
fi

RUNTIME_LIB_PATHS=("$LOCAL_SYSROOT/lib")
if [ -d "$LOCAL_SYSROOT/lib/rustlib/$TARGET_TRIPLE/lib" ]; then
    RUNTIME_LIB_PATHS+=("$LOCAL_SYSROOT/lib/rustlib/$TARGET_TRIPLE/lib")
fi
if [ -d "$RUSTC_DEPS_DIR" ]; then
    RUNTIME_LIB_PATHS+=("$RUSTC_DEPS_DIR")
fi
if [ -d "$PREV_RUSTC_DEPS_DIR" ]; then
    RUNTIME_LIB_PATHS+=("$PREV_RUSTC_DEPS_DIR")
fi
if [ -n "$PREV_STAGE_NAME" ] && [ -d "$BUILD_ROOT/$PREV_STAGE_NAME/lib" ]; then
    RUNTIME_LIB_PATHS+=("$BUILD_ROOT/$PREV_STAGE_NAME/lib")
fi
RUNTIME_LIB_PATH="$(IFS=:; echo "${RUNTIME_LIB_PATHS[*]}")"
case "$(uname -s)" in
    Darwin)
        export DYLD_LIBRARY_PATH="$RUNTIME_LIB_PATH${DYLD_LIBRARY_PATH:+:$DYLD_LIBRARY_PATH}"
        ;;
    Linux)
        export LD_LIBRARY_PATH="$RUNTIME_LIB_PATH${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}"
        ;;
esac

RUSTUP_AVAILABLE=0
LINKED_TARGO_AVAILABLE=0
LINKED_TRUSTC=""
if [ -x "$HOST_RUSTUP_BIN" ]; then
    echo "rustup: present but intentionally not used for standalone Trust; same-sysroot bin/rustc is checked separately"

    CURRENT_TRUST_PATH="$(current_trust_path || true)"
    if [ -n "$CURRENT_TRUST_PATH" ] && [ -d "$CURRENT_TRUST_PATH" ]; then
        CURRENT_TRUST_PATH="$(canonicalize_dir "$CURRENT_TRUST_PATH")"
    else
        CURRENT_TRUST_PATH=""
    fi

    if [ -n "$CURRENT_TRUST_PATH" ] && [ "$CURRENT_TRUST_PATH" != "$LOCAL_SYSROOT" ]; then
        echo "rustup trust toolchain points at $CURRENT_TRUST_PATH; ignoring external selector"
    elif [ "$CURRENT_TRUST_PATH" = "$LOCAL_SYSROOT" ]; then
        RUSTUP_AVAILABLE=1
        if "$HOST_RUSTUP_BIN" which --toolchain trust targo >/dev/null 2>&1; then
            LINKED_TARGO_AVAILABLE=1
        fi
    fi
fi

echo "sysroot: $LOCAL_SYSROOT"
echo "tools: $TOOLS_BIN"
echo "trustc: $("$TRUSTC_BIN" --version)"
echo "trustdoc: $("$RUSTDOC_BIN" --version)"
echo "targo: $("$TARGO_BIN" --version)"
echo

if [ "$RUSTUP_AVAILABLE" = "1" ]; then
    if ! SYSROOT="$(run_linked_tool trustc --print sysroot 2>&1)"; then
        fail_test "rustup could not run trustc --print sysroot
$SYSROOT"
    fi
    if ! HOST_INFO="$(run_linked_tool trustc -vV 2>&1)"; then
        fail_test "rustup could not run trustc -vV
$HOST_INFO"
    fi
else
    if ! SYSROOT="$("$TRUSTC_BIN" --print sysroot 2>&1)"; then
        fail_test "stage2 trustc could not print sysroot
$SYSROOT"
    fi
    if ! HOST_INFO="$("$TRUSTC_BIN" -vV 2>&1)"; then
        fail_test "stage2 trustc -vV failed
$HOST_INFO"
    fi
fi
HOST_TRIPLE="$(printf '%s\n' "$HOST_INFO" | awk '/^host: / { print $2 }')"
if [ -z "$HOST_TRIPLE" ]; then
    fail_test "could not determine host triple from linked trustc -vV"
fi

if [ "$(canonicalize_dir "$SYSROOT")" != "$LOCAL_SYSROOT" ]; then
    fail_test "linked trust sysroot mismatch: expected $LOCAL_SYSROOT, got $SYSROOT"
fi

if [ "$RUSTUP_AVAILABLE" = "1" ]; then
    require_linked_tool trustc
    for tool in \
        targo \
        targo-trust \
        trustd \
        trustdoc \
        trustfmt \
        targo-fmt \
        tippy \
        targo-tippy \
        tippy-driver \
        trust-analyzer
    do
        require_linked_tool "$tool"
    done
fi

if [ "$LINKED_TARGO_AVAILABLE" = "1" ]; then
    if ! TARGO_VERSION="$(run_linked_tool targo --version 2>&1)"; then
        fail_test "linked trust targo --version failed
$TARGO_VERSION"
    fi
    case "$TARGO_VERSION" in
        targo\ *) ;;
        *) fail_test "linked trust targo --version did not start with \`targo \`: $TARGO_VERSION" ;;
    esac
fi

for version_tool in trustd trustdoc trustfmt tippy targo-tippy tippy-driver trust-analyzer; do
    if ! TOOL_VERSION="$(run_linked_tool "$version_tool" --version 2>&1)"; then
        fail_test "standalone Trust tool $version_tool --version failed
$TOOL_VERSION"
    fi
    echo "$version_tool: $TOOL_VERSION"
done

for alias_tool in \
    rustc \
    cargo
do
    run_alias_version_check "$alias_tool"
done

for forbidden_tool in \
    cargo-trust tcargo tcargo-trust tcargo-fmt rustdoc rustfmt cargo-fmt cargo-clippy clippy-driver \
    rust-analyzer miri cargo-miri targo-clippy trust-clippy trust-clippy-driver
do
    if [ -e "$BIN_DIR/$forbidden_tool" ]; then
        fail_test "forbidden stock or retired tool alias is present: $BIN_DIR/$forbidden_tool"
    fi
done

if [ -x "$SYSROOT/libexec/trust-analyzer-proc-macro-srv" ]; then
    require_executable "$SYSROOT/libexec/trust-analyzer-proc-macro-srv"
elif [ -x "$TOOLS_BIN/trust-analyzer-proc-macro-srv" ]; then
    require_executable "$TOOLS_BIN/trust-analyzer-proc-macro-srv"
else
    echo "trust-analyzer-proc-macro-srv: SKIP (not present in raw tool layout)"
fi
STOCK_PROC_MACRO_SRV="$SYSROOT/libexec/rust-analyzer-proc-macro-srv"
# `-e` observes ordinary entries; `-L` additionally catches a dangling
# symlink, which the public-surface readiness gate also rejects.
if [ -e "$STOCK_PROC_MACRO_SRV" ] || [ -L "$STOCK_PROC_MACRO_SRV" ]; then
    fail_test "forbidden stock analyzer proc-macro helper is present: $STOCK_PROC_MACRO_SRV"
fi
require_directory "$SYSROOT/lib/rustlib/src/rust"
require_directory "$SYSROOT/lib/rustlib/rustc-src/rust"

for llvm_tool in llvm-ar llvm-nm llvm-objdump llvm-profdata; do
    require_executable "$SYSROOT/lib/rustlib/$HOST_TRIPLE/bin/$llvm_tool"
done

TMP_DIR="$(mktemp -d /tmp/trust_toolchain_smoke_XXXXXX)"
trap 'rm -rf "$TMP_DIR"' EXIT

TOOL_WRAPPER_BIN="$TMP_DIR/tool-wrappers"
mkdir -p "$TOOL_WRAPPER_BIN"

write_tool_wrapper() {
    local name="$1"
    local real="$2"
    local extra="${3:-}"
    local wrapper="$TOOL_WRAPPER_BIN/$name"

    [ -x "$real" ] || return 0
    cat > "$wrapper" <<EOF
#!/bin/sh
export DYLD_LIBRARY_PATH="$RUNTIME_LIB_PATH\${DYLD_LIBRARY_PATH:+:\$DYLD_LIBRARY_PATH}"
export LD_LIBRARY_PATH="$RUNTIME_LIB_PATH\${LD_LIBRARY_PATH:+:\$LD_LIBRARY_PATH}"
exec "$real" $extra "\$@"
EOF
    chmod +x "$wrapper"
}

write_tool_wrapper trustfmt "$TOOLS_BIN/trustfmt"
if [ -x "$TOOL_WRAPPER_BIN/trustfmt" ]; then
    export RUSTFMT="$TOOL_WRAPPER_BIN/trustfmt"
fi

pushd "$TMP_DIR" >/dev/null

run_linked_targo new smoke --bin --quiet
cd smoke

run_targo_trust_check() {
    local label="$1"
    local runner="$2"
    shift
    shift

    local stdout_file="$TMP_DIR/targo-trust-${label}.stdout"
    local stderr_file="$TMP_DIR/targo-trust-${label}.stderr"
    local exit_code=0

    if "$runner" trust check --format json "$@" >"$stdout_file" 2>"$stderr_file"; then
        exit_code=0
    else
        exit_code=$?
    fi

    if [ "$exit_code" -gt 1 ]; then
        fail_test "targo trust check ($label) exited with $exit_code
$(cat "$stderr_file")"
    fi

    if [ ! -s "$stdout_file" ]; then
        fail_test "targo trust check ($label) produced no JSON output
$(cat "$stderr_file")"
    fi

    python3 - "$stdout_file" <<'PY'
import json
import pathlib
import sys

json.loads(pathlib.Path(sys.argv[1]).read_text(encoding="utf-8"))
PY
}

run_targo_trust_doctor() {
    local label="$1"
    local runner="$2"
    local stdout_file="$TMP_DIR/targo-trust-doctor-${label}.stdout"
    local stderr_file="$TMP_DIR/targo-trust-doctor-${label}.stderr"
    local exit_code=0

    if "$runner" trust doctor --format json >"$stdout_file" 2>"$stderr_file"; then
        exit_code=0
    else
        exit_code=$?
    fi

    if [ "$exit_code" -gt 1 ]; then
        fail_test "targo trust doctor --format json ($label) failed
$(cat "$stderr_file")"
    fi

    python3 - "$stdout_file" "$BIN_DIR" <<'PY'
import json
import pathlib
import sys

report = json.loads(pathlib.Path(sys.argv[1]).read_text(encoding="utf-8"))
bin_dir = pathlib.Path(sys.argv[2]).resolve()
compiler = report.get("compiler") or {}

def fail(message):
    raise SystemExit(message)

if compiler.get("check_report_mode") != "native_compiler":
    fail(f"targo trust doctor did not report native compiler mode: {compiler.get('check_report_mode')!r}")
if compiler.get("trust_verify") is not True:
    fail("targo trust doctor did not confirm default native verification output")
if compiler.get("json_transport") is not True:
    fail("targo trust doctor did not confirm JSON transport support")

path = compiler.get("path")
if not path:
    fail("targo trust doctor did not report a compiler path")
compiler_path = pathlib.Path(path).resolve()
if compiler_path != bin_dir / "trustc":
    fail(f"targo trust doctor compiler path is not an exact linked stage2 compiler: {compiler_path}")
if compiler.get("discovery_source") not in {"sibling_trustc", "rustup_toolchain_trust"}:
    fail(f"targo trust doctor used an unexpected discovery source: {compiler.get('discovery_source')!r}")

daily_driver = compiler.get("daily_driver") or {}
if daily_driver.get("ready") is not True:
    fail(f"targo trust doctor did not confirm linked daily-driver surfaces: {daily_driver!r}")

expected_tools = {
    "linked_targo_path": bin_dir / "targo",
    "linked_targo_trust_path": bin_dir / "targo-trust",
}
for field, expected in expected_tools.items():
    path = daily_driver.get(field)
    if not path:
        fail(f"targo trust doctor did not report {field}")
    if pathlib.Path(path).resolve() != expected:
        fail(f"targo trust doctor {field} is not an exact linked stage2 tool: {path}")

required_tools = daily_driver.get("required_tools")
if not isinstance(required_tools, list):
    fail(f"targo trust doctor did not expose required tool rows: {required_tools!r}")
trustd_rows = [
    row
    for row in required_tools
    if isinstance(row, dict) and row.get("name") == "trustd"
]
expected_trustd = bin_dir / "trustd"
if len(trustd_rows) != 1 or trustd_rows[0].get("status") != "present":
    fail(f"targo trust doctor did not require one present sibling trustd row: {trustd_rows!r}")
if pathlib.Path(trustd_rows[0].get("path", "")).resolve() != expected_trustd:
    fail(
        "targo trust doctor trustd path is not the exact linked stage2 daemon: "
        f"{trustd_rows[0].get('path')}"
    )

suite_by_name = {
    suite.get("name"): suite
    for suite in report.get("verifier_suites", [])
    if isinstance(suite, dict)
}
expected_suites = ["trust-mc", "trust-wp", "trust-vc"]
for name in expected_suites:
    suite = suite_by_name.get(name)
    if not suite:
        fail(f"targo trust doctor did not report verifier suite {name}")
    if suite.get("adapter_compiled") is not True:
        fail(f"{name} adapter is not compiled: {suite!r}")
    if suite.get("capability_available") is not True:
        fail(f"{name} capability is not available: {suite!r}")
PY
}

cat <<'RUST' > src/main.rs
fn midpoint(a: i32, b: i32) -> i32 {
    a + (b - a) / 2
}

fn main() {
    assert_eq!(midpoint(2, 6), 4);
    println!("{}", midpoint(10, 14));
}

#[cfg(test)]
mod tests {
    use super::midpoint;

    #[test]
    fn computes_midpoint() {
        assert_eq!(midpoint(-2, 2), 0);
    }
}
RUST

echo "--- targo check"
run_linked_targo --unverified check

echo "--- cargo alias check"
run_linked_cargo check

echo "--- targo build"
run_linked_targo --unverified build

echo "--- targo test"
run_linked_targo --unverified test

echo "--- targo doc --no-deps"
run_linked_targo --unverified doc --no-deps

echo "--- trustdoc"
mkdir -p "$TMP_DIR/rustdoc-alias"
run_linked_tool trustdoc src/main.rs -o "$TMP_DIR/rustdoc-alias"

echo "--- targo fmt --check"
run_linked_targo fmt --check

echo "--- tippy --no-deps -- -D warnings"
run_linked_tool tippy --no-deps -- -D warnings
echo "--- targo tippy --no-deps -- -D warnings"
run_linked_targo tippy --no-deps -- -D warnings

echo "--- targo trust check --format json"
echo "--- targo trust doctor --format json"
run_targo_trust_doctor linked run_linked_targo
run_targo_trust_check linked run_linked_targo src/main.rs
echo "--- cargo alias trust doctor --format json"
run_targo_trust_doctor cargo-alias run_linked_cargo
echo "--- cargo alias trust check --format json"
run_targo_trust_check cargo-alias run_linked_cargo src/main.rs

if ! RUSTC_ALIAS_SYSROOT="$(run_linked_tool rustc --print sysroot 2>&1)"; then
    fail_test "rustc alias --print sysroot failed
$RUSTC_ALIAS_SYSROOT"
fi
if [ "$(canonicalize_dir "$RUSTC_ALIAS_SYSROOT")" != "$LOCAL_SYSROOT" ]; then
    fail_test "rustc alias sysroot mismatch: expected $LOCAL_SYSROOT, got $RUSTC_ALIAS_SYSROOT"
fi

if TRUST_CG_LINK_TARGETS="$(trust_cg_linked_crate_types)"; then
    echo "--- trustc --print=supported-crate-types -Zcodegen-backend=trust-cg"
    printf '%s\n' "$TRUST_CG_LINK_TARGETS" | sed 's/^/    /'
    # `lib` is rustc's alias for `rlib`. A third entry would mean trust-cg
    # started advertising a linked artifact nobody has audited, and Cargo would
    # then treat that unavailable path as usable.
    if [ "$TRUST_CG_LINK_TARGETS" != "$(printf 'lib\nrlib')" ]; then
        fail_test "trust-cg advertises linked crate types other than rlib:
$TRUST_CG_LINK_TARGETS"
    fi

    # The smoke crate is a binary, which trust-cg cannot link, so give the
    # backend a target inside its audited lane instead of asserting a refusal
    # and calling that coverage: straight-line integer arithmetic in an
    # explicit rlib, which is the whole shape trust-cg claims today.
    TRUST_CG_FIXTURE="$TMP_DIR/trust_cg_rlib.rs"
    cat <<'RUST' > "$TRUST_CG_FIXTURE"
pub fn midpoint(a: i32, b: i32) -> i32 {
    a + (b - a) / 2
}
RUST

    echo "--- targo trust check --backend trust-cg --format json (rlib)"
    run_targo_trust_check trust-cg run_linked_targo \
        --backend trust-cg "$TRUST_CG_FIXTURE" --crate-type=rlib
else
    echo "--- trust-cg checks (SKIP: this trustc was built without the trust-cg backend)"
fi

popd >/dev/null

echo
echo "=== local trust toolchain smoke test: PASS ==="
