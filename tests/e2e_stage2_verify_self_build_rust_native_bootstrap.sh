#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
TMP_DIR="$(mktemp -d "${TMPDIR:-/tmp}/trust-stage2-verify-rust-native.XXXXXX")"
trap 'rm -rf "$TMP_DIR"' EXIT

fail() {
    echo "FAIL: $*" >&2
    exit 1
}

write_exe() {
    local path="$1"
    local body="$2"

    mkdir -p "$(dirname "$path")"
    printf '%s\n' "$body" >"$path"
    chmod +x "$path"
}

write_fake_sysroot() {
    local sysroot="$1"
    local tool

    mkdir -p "$sysroot/bin"
    # Trust: the produced stage2 sysroot exposes the targo/tippy bin surface that
    # stage2_verify_self_build.sh's REQUIRED_STAGE2_TOOLS preflight checks.
    for tool in \
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
        trust-analyzer \
        rustc \
        cargo
    do
        write_exe "$sysroot/bin/$tool" '#!/usr/bin/env sh
exit 0'
    done
}

PYTHON_BIN="${PYTHON3:-python3}"
command -v "$PYTHON_BIN" >/dev/null 2>&1 || fail "python3 is required"

FAKE_REPO="$TMP_DIR/repo"
REPORT_DIR="$FAKE_REPO/reports/stage2-verify"
mkdir -p \
    "$FAKE_REPO/src/bootstrap" \
    "$FAKE_REPO/targo-trust" \
    "$FAKE_REPO/custom-evidence"
printf '[package]\nname = "bootstrap"\nversion = "0.0.0"\nedition = "2021"\n' \
    >"$FAKE_REPO/src/bootstrap/Cargo.toml"
printf '[package]\nname = "targo-trust"\nversion = "0.0.0"\nedition = "2021"\n' \
    >"$FAKE_REPO/targo-trust/Cargo.toml"
printf '[package]\nname = "custom-evidence"\nversion = "0.0.0"\nedition = "2021"\n' \
    >"$FAKE_REPO/custom-evidence/Cargo.toml"
write_fake_sysroot "$FAKE_REPO/build/host/stage2"

echo "--- stage2 verify self-build rejects an evidence manifest outside the repository before report/bootstrap work"
mkdir -p "$TMP_DIR/outside"
printf '[package]\nname = "outside"\nversion = "0.0.0"\nedition = "2021"\n' \
    >"$TMP_DIR/outside/Cargo.toml"
ESCAPE_REPORT_DIR="$FAKE_REPO/reports/stage2-verify-escape"
set +e
PYTHON3="$PYTHON_BIN" \
    bash "$ROOT/scripts/stage2_verify_self_build.sh" \
    --repo-root "$FAKE_REPO" \
    --report-dir "$ESCAPE_REPORT_DIR" \
    --evidence-manifest "$TMP_DIR/outside/Cargo.toml" \
    --dry-run >"$TMP_DIR/escape.stdout" 2>"$TMP_DIR/escape.stderr"
escape_rc=$?
set -e
[[ "$escape_rc" -eq 2 ]] || fail "outside evidence manifest exited $escape_rc instead of 2"
grep -q 'escapes repository root' "$TMP_DIR/escape.stderr" \
    || fail "outside evidence manifest was not diagnosed"
[[ ! -e "$ESCAPE_REPORT_DIR" ]] \
    || fail "outside evidence manifest created report/bootstrap side effects"

echo "--- stage2 verify self-build dry-run separates bootstrap provenance from Cargo JSON evidence"
PYTHON3="$PYTHON_BIN" \
    bash "$ROOT/scripts/stage2_verify_self_build.sh" \
    --repo-root "$FAKE_REPO" \
    --report-dir "$REPORT_DIR" \
    --jobs 7 \
    --dry-run >/dev/null

FAKE_REPO_RESOLVED="$(cd "$FAKE_REPO" && pwd -P)"
REPORT_JSON="$REPORT_DIR/stage2-verify-self-build.report.json"
STAGE_ARGV="$REPORT_DIR/stage-command.argv"
BOOTSTRAP_ARGV="$REPORT_DIR/bootstrap-command.argv"

"$PYTHON_BIN" - "$REPORT_JSON" "$STAGE_ARGV" "$BOOTSTRAP_ARGV" "$FAKE_REPO_RESOLVED" <<'PY'
from __future__ import annotations

import json
import sys
from pathlib import Path

report_path = Path(sys.argv[1])
argv_path = Path(sys.argv[2])
repo_root = Path(sys.argv[4])
report = json.loads(report_path.read_text(encoding="utf-8"))
argv = argv_path.read_text(encoding="utf-8").splitlines()
bootstrap_argv = Path(sys.argv[3]).read_text(encoding="utf-8").splitlines()


def fail(message: str) -> None:
    raise SystemExit(f"FAIL: {message}")


def flag_value(args: list[str], flag: str) -> str | None:
    for index, arg in enumerate(args[:-1]):
        if arg == flag:
            return args[index + 1]
    return None


if report.get("status") != "planned":
    fail(f"expected dry-run status planned, got {report.get('status')!r}")

if bootstrap_argv[:4] != [
    "env",
    "-u",
    "CARGO_TARGET_DIR",
    str(repo_root / "build/host/stage2/bin/targo"),
]:
    fail(
        "bootstrap command should clear build-only escape hatches before Targo, "
        f"got {bootstrap_argv[:4]!r}"
    )

command_names = {Path(arg).name for arg in bootstrap_argv}
if "x.py" in command_names or any(name.startswith("python") for name in command_names):
    fail(f"bootstrap command must not route through python/x.py: {bootstrap_argv!r}")

if bootstrap_argv[4:6] != ["--unverified", "run"]:
    fail(
        "bootstrap command should explicitly authorize the unverified native "
        f"targo run transport, got {bootstrap_argv[4:6]!r}"
    )
if "--locked" not in bootstrap_argv or "--offline" not in bootstrap_argv:
    fail("bootstrap command should request locked offline cargo execution")
if flag_value(bootstrap_argv, "--target-dir") != str(repo_root / "build/full-verify/bootstrap-target"):
    fail("bootstrap command should use the default full-verify bootstrap target dir")
if flag_value(bootstrap_argv, "--manifest-path") != str(repo_root / "src/bootstrap/Cargo.toml"):
    fail("bootstrap command should run the repo-local bootstrap manifest")

try:
    separator = bootstrap_argv.index("--")
except ValueError:
    fail("bootstrap command should pass bootstrap args after --")
bootstrap_args = bootstrap_argv[separator + 1 :]
if flag_value(bootstrap_args, "--src") != str(repo_root):
    fail("bootstrap runner should receive --src for the fake repo")
if "build" not in bootstrap_args:
    fail("bootstrap runner should receive the build subcommand")
if flag_value(bootstrap_args, "--stage") != "2":
    fail("bootstrap runner should request stage 2")
for expected in (
    "llvm.ninja=false",
    "build.full-bootstrap=true",
    "build.extended=true",
    'build.tools=["targo","targo-trust","trustdoc","trustfmt","tippy","trust-analyzer"]',
    "compiler/rustc",
    "library/std",
):
    if expected not in bootstrap_args:
        fail(f"missing bootstrap arg {expected!r}")

semantics = report.get("stage2_bootstrap_semantics")
if not isinstance(semantics, dict):
    fail("report should include stage2_bootstrap_semantics")
if semantics.get("bootstrap_rebuild_planned") is not True:
    fail(f"Rust-native bootstrap runner should be planned separately: {semantics!r}")
if semantics.get("bootstrap_rebuild_completed") is not False:
    fail(f"dry run must not claim a completed rebuild: {semantics!r}")
if semantics.get("rebuild_claimed") is not False:
    fail(f"dry run must not claim a rebuild: {semantics!r}")
if semantics.get("full_bootstrap_requested") is not True:
    fail(f"full bootstrap should be detected: {semantics!r}")
if semantics.get("bootstrap_stdout_parsed_as_evidence") is not False:
    fail(f"bootstrap stdout must never be evidence: {semantics!r}")

expected_evidence = [
    str(repo_root / "build/host/stage2/bin/targo"),
    "build",
    "--message-format=json-render-diagnostics",
    "--manifest-path",
    str(repo_root / "targo-trust/Cargo.toml"),
    "-j",
    "7",
]
if argv != expected_evidence:
    fail(f"evidence command must be a direct manifest-scoped Targo build: {argv!r}")
if report.get("configuration", {}).get("target") != "stage2 full-bootstrap compiler/rustc library/std":
    fail("logical release target label was not preserved")
if report.get("configuration", {}).get("evidence_manifest_path") != str(repo_root / "targo-trust/Cargo.toml"):
    fail("explicit evidence manifest was not recorded")
if report.get("configuration", {}).get("include_dependencies") is not True:
    fail("dependency evidence scope should default to included")

expected_tools = [
    "trustc",
    "targo",
    "targo-trust",
    "trustd",
    "trustdoc",
    "trustfmt",
    "targo-fmt",
    "tippy",
    "targo-tippy",
    "tippy-driver",
    "trust-analyzer",
]
toolchain = report.get("toolchain", {})
if toolchain.get("required") != expected_tools:
    fail(f"report did not bind the complete canonical tool inventory: {toolchain!r}")
if toolchain.get("targo_fmt") != str(repo_root / "build/host/stage2/bin/targo-fmt"):
    fail(f"report did not bind canonical targo-fmt: {toolchain!r}")

command = report.get("command")
if not isinstance(command, dict) or command.get("uses_explicit_targo") is not True:
    fail(f"report should detect explicit targo use: {command!r}")
PY

echo "--- stage2 verify self-build preserves custom evidence command and normalized dependency scope"
CUSTOM_REPORT_DIR="$FAKE_REPO/reports/stage2-verify-custom-evidence"
CUSTOM_EVIDENCE=(
    "$FAKE_REPO_RESOLVED/build/host/stage2/bin/targo"
    build
    --message-format=json-render-diagnostics
    --manifest-path
    "$FAKE_REPO_RESOLVED/custom-evidence/Cargo.toml"
)
TRUST_STAGE2_VERIFY_INCLUDE_DEPENDENCIES=off \
    PYTHON3="$PYTHON_BIN" \
    bash "$ROOT/scripts/stage2_verify_self_build.sh" \
    --repo-root "$FAKE_REPO" \
    --report-dir "$CUSTOM_REPORT_DIR" \
    --target "custom logical release label" \
    --evidence-manifest "custom-evidence/Cargo.toml" \
    --dry-run \
    -- "${CUSTOM_EVIDENCE[@]}" >/dev/null

"$PYTHON_BIN" - "$CUSTOM_REPORT_DIR/stage2-verify-self-build.report.json" \
    "$CUSTOM_REPORT_DIR/stage-command.argv" \
    "$CUSTOM_REPORT_DIR/bootstrap-command.argv" \
    "${CUSTOM_EVIDENCE[@]}" <<'PY'
from __future__ import annotations

import json
import sys
from pathlib import Path

report = json.loads(Path(sys.argv[1]).read_text(encoding="utf-8"))
evidence_argv = Path(sys.argv[2]).read_text(encoding="utf-8").splitlines()
bootstrap_argv = Path(sys.argv[3]).read_text(encoding="utf-8").splitlines()
expected_argv = sys.argv[4:]

if evidence_argv != expected_argv:
    raise SystemExit(f"FAIL: custom evidence argv changed: {evidence_argv!r}")
if bootstrap_argv:
    raise SystemExit(f"FAIL: custom evidence path planned an implicit bootstrap: {bootstrap_argv!r}")
if report["configuration"]["target"] != "custom logical release label":
    raise SystemExit("FAIL: custom logical target label was not preserved")
if report["configuration"]["include_dependencies"] is not False:
    raise SystemExit("FAIL: dependency scope 'off' was not normalized to false")
semantics = report["stage2_bootstrap_semantics"]
if semantics["two_phase_claim"] is not False or semantics["rebuild_claimed"] is not False:
    raise SystemExit(f"FAIL: custom evidence command made a bootstrap claim: {semantics!r}")
if semantics["custom_evidence_command"] is not True:
    raise SystemExit(f"FAIL: custom evidence command was not identified: {semantics!r}")
PY

echo "--- stage2 verify self-build rejects a repo-shaped sysroot that resolves outward"
OUTSIDE_HOST="$TMP_DIR/outside-stage2-host"
mv "$FAKE_REPO/build/host" "$OUTSIDE_HOST"
ln -s "$OUTSIDE_HOST" "$FAKE_REPO/build/host"
OUTWARD_SYSROOT_REPORT="$FAKE_REPO/reports/stage2-verify-outward-sysroot"
PYTHON3="$PYTHON_BIN" \
    bash "$ROOT/scripts/stage2_verify_self_build.sh" \
    --repo-root "$FAKE_REPO" \
    --report-dir "$OUTWARD_SYSROOT_REPORT" \
    --dry-run >/dev/null
grep -q 'refusing non-repo stage2 sysroot for self-build evidence' \
    "$OUTWARD_SYSROOT_REPORT/logs/toolchain-preflight.log" \
    || fail "outward stage2 ancestor was not diagnosed by stage2 preflight"
[[ ! -s "$OUTWARD_SYSROOT_REPORT/stage-command.argv" ]] \
    || fail "stage2 command was planned from an outward stage2 ancestor"
rm "$FAKE_REPO/build/host"
mv "$OUTSIDE_HOST" "$FAKE_REPO/build/host"

echo "--- stage2 verify self-build rejects an outward compatibility alias"
AMBIENT_BIN="$FAKE_REPO/ambient/bin"
mkdir -p "$AMBIENT_BIN"
cp "$FAKE_REPO/build/host/stage2/bin/trustc" "$AMBIENT_BIN/rustc"
chmod +x "$AMBIENT_BIN/rustc"
rm "$FAKE_REPO/build/host/stage2/bin/rustc"
ln -s "$AMBIENT_BIN/rustc" "$FAKE_REPO/build/host/stage2/bin/rustc"
OUTWARD_REPORT_DIR="$FAKE_REPO/reports/stage2-verify-outward-alias"
PYTHON3="$PYTHON_BIN" \
    bash "$ROOT/scripts/stage2_verify_self_build.sh" \
    --repo-root "$FAKE_REPO" \
    --report-dir "$OUTWARD_REPORT_DIR" \
    --dry-run >/dev/null
grep -q 'invalid compatibility alias pair trustc:rustc: compatibility alias rustc resolves outside selected bin directory' \
    "$OUTWARD_REPORT_DIR/logs/toolchain-preflight.log" \
    || fail "outward rustc binding was not diagnosed by stage2 preflight"
[[ ! -s "$OUTWARD_REPORT_DIR/stage-command.argv" ]] \
    || fail "stage2 command was planned from an outward rustc alias"

echo "stage2 verify self-build Rust-native bootstrap dry-run regression passed"
