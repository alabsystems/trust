#!/bin/sh
# Regenerate or validate the 32 stdlib bit-method dumps and their twelve
# negative/positive controls using this checkout. Nothing under another
# worktree is consulted, and dumps plus forgeries are published transactionally
# only after all checks pass.
set -eu

HERE="$(cd "$(dirname "$0")" && pwd)"
REPO=$(cd "${REPO:-$HERE/../../../..}" && pwd)
TRUSTC=${TRUSTC:-$REPO/build/host/stage1/bin/trustc}
VALIDATE_ONLY=0
case "${1:-}" in
  --validate-only)
    VALIDATE_ONLY=1
    shift
    ;;
  "") ;;
  *)
    echo "usage: $0 [--validate-only]" >&2
    exit 2
    ;;
esac
test "$#" -eq 0 || {
  echo "usage: $0 [--validate-only]" >&2
  exit 2
}
test -f "$REPO/crates/Cargo.toml" && test -f "$REPO/library/core/src/lib.rs" || {
  echo "error: REPO is not a Trust checkout: $REPO" >&2
  exit 1
}

TMP=$(mktemp -d)
CANDIDATE_ROOT="$HERE/.regenerate-bitmethods.$$"
BACKUP_ROOT="$HERE/.corpus.previous.$$"
LOCK_DIR="$HERE/.regenerate-bitmethods.lock"
VALIDATION_TARGET_DIR=${TRUST_BITMETHODS_VALIDATION_TARGET_DIR:-$TMP/cargo-target}
PUBLISHING=0

rollback_publication() {
  test "$PUBLISHING" -eq 1 || return 0
  for directory in dumps forgeries; do
    if test -d "$BACKUP_ROOT/$directory"; then
      if test -d "$HERE/$directory"; then
        mv "$HERE/$directory" "$TMP/failed-$directory"
      fi
      mv "$BACKUP_ROOT/$directory" "$HERE/$directory"
    fi
  done
}

cleanup() {
  rollback_publication
  rm -rf "$TMP" "$CANDIDATE_ROOT" "$BACKUP_ROOT" "$LOCK_DIR"
}
test ! -e "$CANDIDATE_ROOT" && test ! -e "$BACKUP_ROOT" || {
  echo "error: stale process-specific bitmethods regeneration path" >&2
  rm -rf "$TMP"
  exit 1
}
if ! mkdir "$LOCK_DIR"; then
  echo "error: another bitmethods corpus validation/regeneration is already running" >&2
  rm -rf "$TMP"
  exit 1
fi
trap cleanup EXIT
trap 'exit 129' HUP
trap 'exit 130' INT
trap 'exit 143' TERM

hash_file() {
  if command -v sha256sum >/dev/null 2>&1; then
    sha256sum "$1" | awk '{print $1}'
  else
    shasum -a 256 "$1" | awk '{print $1}'
  fi
}

check_manifest() {
  base=$1
  manifest=$2
  if command -v sha256sum >/dev/null 2>&1; then
    (cd "$base" && sha256sum -c "$manifest")
  else
    (cd "$base" && shasum -a 256 -c "$manifest")
  fi
}

check_manifest "$REPO" "$HERE/SOURCE.sha256"

if test "$VALIDATE_ONLY" -eq 0; then
  test -x "$TRUSTC" || {
    echo "error: dump-capable stage1 trustc not found at $TRUSTC (set TRUSTC explicitly)" >&2
    exit 1
  }
  test ! -L "$TRUSTC" || {
    echo "error: TRUSTC must be a regular executable or hardlink, not a symlink" >&2
    exit 1
  }
  TRUSTC=$(cd "$(dirname "$TRUSTC")" && pwd -P)/$(basename "$TRUSTC")
  expected_version=$(sed -n 's/^trustc version: //p' "$HERE/TOOLCHAIN.sha256")
  expected_trustc_hash=$(sed -n 's/^trustc binary sha256: //p' "$HERE/TOOLCHAIN.sha256")
  expected_driver_name=$(sed -n 's/^rustc_driver dylib: //p' "$HERE/TOOLCHAIN.sha256")
  expected_driver_hash=$(sed -n 's/^rustc_driver sha256: //p' "$HERE/TOOLCHAIN.sha256")
  expected_host=$(sed -n 's/^host: //p' "$HERE/TOOLCHAIN.sha256")
  expected_dump_count=$(sed -n 's/^expected recursive core dump count: //p' "$HERE/TOOLCHAIN.sha256")
  test -n "$expected_version" && test -n "$expected_trustc_hash" && \
    test -n "$expected_driver_name" && test -n "$expected_driver_hash" && \
    test -n "$expected_host" && test -n "$expected_dump_count" || {
    echo "error: incomplete compiler identity in TOOLCHAIN.sha256" >&2
    exit 1
  }
  run_trustc() {
    env -u DYLD_LIBRARY_PATH -u DYLD_FALLBACK_LIBRARY_PATH \
      -u DYLD_VERSIONED_LIBRARY_PATH -u DYLD_INSERT_LIBRARIES \
      -u DYLD_IMAGE_SUFFIX -u DYLD_ROOT_PATH "$TRUSTC" "$@"
  }
  actual_version=$(run_trustc --version)
  actual_trustc_hash=$(hash_file "$TRUSTC")
  actual_host=$(run_trustc -vV | sed -n 's/^host: //p')
  test "$actual_version" = "$expected_version" || {
    echo "error: trustc version drift: $actual_version" >&2
    exit 1
  }
  test "$actual_trustc_hash" = "$expected_trustc_hash" || {
    echo "error: trustc binary hash drift: $actual_trustc_hash" >&2
    exit 1
  }
  test "$actual_host" = "$expected_host" || {
    echo "error: trustc host drift: $actual_host" >&2
    exit 1
  }

  # The small trustc launcher dynamically loads rustc_driver. Hashing only the
  # launcher leaves the extractor implementation unpinned, so verify the exact
  # linked dylib, its sole loader-relative search path, and the adjacent bytes
  # that the sanitized run_trustc environment will actually load.
  command -v otool >/dev/null 2>&1 || {
    echo "error: otool is required to authenticate the recorded Apple trustc" >&2
    exit 1
  }
  linked_driver_names=$(otool -L "$TRUSTC" | \
    sed -n 's|.*[/]\(librustc_driver-[^[:space:]]*\.dylib\).*|\1|p')
  test "$(printf '%s\n' "$linked_driver_names" | sed '/^$/d' | wc -l | tr -d ' ')" -eq 1 || {
    echo "error: trustc does not link exactly one rustc_driver dylib" >&2
    exit 1
  }
  test "$linked_driver_names" = "$expected_driver_name" || {
    echo "error: trustc links unexpected rustc_driver: $linked_driver_names" >&2
    exit 1
  }
  linked_rpaths=$(otool -l "$TRUSTC" | awk '
    $1 == "cmd" && $2 == "LC_RPATH" { in_rpath = 1; next }
    in_rpath && $1 == "path" { print $2; in_rpath = 0 }
  ')
  test "$linked_rpaths" = '@loader_path/../lib' || {
    echo "error: trustc LC_RPATH is not exactly @loader_path/../lib: $linked_rpaths" >&2
    exit 1
  }
  TRUSTC_DRIVER=$(cd "$(dirname "$TRUSTC")/../lib" && pwd -P)/$expected_driver_name
  test -f "$TRUSTC_DRIVER" || {
    echo "error: pinned adjacent rustc_driver not found at $TRUSTC_DRIVER" >&2
    exit 1
  }
  actual_driver_hash=$(hash_file "$TRUSTC_DRIVER")
  test "$actual_driver_hash" = "$expected_driver_hash" || {
    echo "error: rustc_driver hash drift: $actual_driver_hash" >&2
    exit 1
  }

  cp -R "$REPO/library/core" "$TMP/L-core"
  mkdir -p "$TMP/L"
  mv "$TMP/L-core" "$TMP/L/core"
  ln -s "$REPO/library/stdarch" "$TMP/L/stdarch"
  ln -s "$REPO/library/portable-simd" "$TMP/L/portable-simd"
  patch --forward -p0 -d "$TMP/L/core" < "$HERE/int_log10-workaround.diff"

  mkdir -p "$TMP/dump"
  TRUST_LIBRARY_PATH=${TRUST_LIBRARY_PATH:-}
  if test -z "$TRUST_LIBRARY_PATH"; then
    command -v brew >/dev/null 2>&1 || {
      echo "error: set TRUST_LIBRARY_PATH (or install Homebrew for automatic discovery)" >&2
      exit 1
    }
    TRUST_LIBRARY_PATH=$(brew --prefix)/lib
  fi
  test -d "$TRUST_LIBRARY_PATH" || {
    echo "error: recorded extraction LIBRARY_PATH is unavailable: $TRUST_LIBRARY_PATH" >&2
    exit 1
  }
  set +e
  # Run from the disposable directory as well as writing outputs there. The
  # recorded delayed compiler bug emits its diagnostic attachment in cwd;
  # keeping cwd under TMP prevents an accepted post-dump ICE note from leaving
  # an untracked file in the source checkout.
  (
    cd "$TMP"
    LIBRARY_PATH="$TRUST_LIBRARY_PATH" \
      run_trustc --edition 2024 --crate-type lib --crate-name core \
      -Z"trust-dump=mir:$TMP/dump" -Ztrust-policy=advisory \
      -o "$TMP/core.rlib" "$TMP/L/core/src/lib.rs"
  ) > "$TMP/trustc.stdout" 2> "$TMP/trustc.stderr"
  dump_status=$?
  set -e
  test "$(hash_file "$TRUSTC")" = "$expected_trustc_hash" && \
    test "$(hash_file "$TRUSTC_DRIVER")" = "$expected_driver_hash" || {
    echo "error: trustc or rustc_driver changed during extraction" >&2
    exit 1
  }
  total_dumps=$(find "$TMP/dump" -type f -name '*.json' | wc -l | tr -d ' ')
  echo "trustc exit=$dump_status; dumped $total_dumps bodies"
  test "$dump_status" -eq 101 || {
    echo "error: pinned core extraction exit drift: expected 101, got $dump_status" >&2
    exit 1
  }
  test ! -s "$TMP/trustc.stdout" && \
    test "$(grep -c '^error:' "$TMP/trustc.stderr")" -eq 1 && \
    test "$(grep -c '^error: internal compiler error: unexpected ambiguity:' "$TMP/trustc.stderr")" -eq 1 && \
    test "$(grep -c -F '::ptr::metadata::Pointee::Metadata' "$TMP/trustc.stderr")" -eq 1 && \
    test "$(grep -c -F 'num::nonzero::NonZero<T/#0>' "$TMP/trustc.stderr")" -eq 1 && \
    test "$(grep -c -F 'NormalizationResult' "$TMP/trustc.stderr")" -eq 1 && \
    test "$(grep -c -F 'note: no errors encountered even though delayed bugs were created' "$TMP/trustc.stderr")" -eq 1 && \
    test "$(grep -c -F 'note: those delayed bugs will now be shown as internal compiler errors' "$TMP/trustc.stderr")" -eq 1 && \
    test "$(grep -c -F 'warning: 27553 warnings emitted' "$TMP/trustc.stderr")" -eq 1 || {
    echo "error: core extraction did not fail with the one exact recorded delayed bug" >&2
    tail -n 100 "$TMP/trustc.stderr" >&2
    exit 1
  }
  echo "accepted exact recorded post-dump NonZero normalization failure" >&2
  test "$total_dumps" -eq "$expected_dump_count" || {
    echo "error: exact core dump inventory drift: expected $expected_dump_count, found $total_dumps" >&2
    exit 1
  }

  mkdir -p "$CANDIDATE_ROOT/dumps"
  python3 - "$TMP/dump" "$CANDIDATE_ROOT/dumps" "$total_dumps" <<'PY'
import glob
import json
import os
import sys

source, destination, expected_scan_count = sys.argv[1:]
expected_scan_count = int(expected_scan_count)
signed = ("i8", "i16", "i32", "i64")
unsigned = ("u8", "u16", "u32", "u64")
wanted = {
    f"num::<impl {ty}>::{method}"
    for ty in signed + unsigned
    for method in ("count_zeros", "leading_zeros", "swap_bytes", "reverse_bits")
}
raw_wanted = {f"core::{path}" for path in wanted}

# `safe_def_path_str` now emits the local crate qualifier. This extraction
# compiles exactly `--crate-name core`; keep the publication's established
# crate-relative identities by stripping exactly one leading `core::` from
# identity-bearing fields only. In particular, do not rewrite arbitrary string
# literals or source data. The compiler-authenticated intrinsic marker remains
# intact while its diagnostic payload becomes the same crate-relative path.
intrinsic_marker = "@trust-rustc-intrinsic::"
def canonical_core_identity(value):
    if value.startswith(intrinsic_marker + "core::"):
        return intrinsic_marker + value[len(intrinsic_marker + "core::"):]
    if value.startswith("core::"):
        return value[len("core::"):]
    return value

def canonicalize_identity_fields(value):
    if isinstance(value, list):
        return [canonicalize_identity_fields(item) for item in value]
    if not isinstance(value, dict):
        return value
    normalized = {}
    for key, item in value.items():
        if key in {"def_path", "func"} and isinstance(item, str):
            normalized[key] = canonical_core_identity(item)
        elif key == "name" and isinstance(item, str) and item.startswith("core::"):
            # Type/ADT identities use `name`; ordinary local/variant names do
            # not begin with a crate qualifier and are preserved byte-for-byte.
            normalized[key] = canonical_core_identity(item)
        else:
            normalized[key] = canonicalize_identity_fields(item)
    return normalized

found = {}
scanned = 0
for path in sorted(glob.glob(os.path.join(source, "**", "*.json"), recursive=True)):
    scanned += 1
    with open(path, encoding="utf-8") as stream:
        raw = json.load(stream)
    raw_def_path = raw.get("def_path", "")
    if raw_def_path not in raw_wanted:
        continue
    body = canonicalize_identity_fields(raw)
    def_path = body.get("def_path", "")
    if def_path in wanted:
        if def_path in found:
            raise SystemExit(f"duplicate target dump: {def_path}")
        found[def_path] = body
if scanned != expected_scan_count:
    raise SystemExit(
        f"dump scan count mismatch: recursive slicer saw {scanned}, extraction counted {expected_scan_count}"
    )
if set(found) != wanted:
    raise SystemExit(f"target inventory mismatch: missing={sorted(wanted-set(found))} extra={sorted(set(found)-wanted)}")
print(f"scanned {scanned} extracted MIR bodies; selected {len(found)} exact bitmethod targets")
for def_path, body in found.items():
    name = def_path.replace("::", "__") + ".json"
    with open(os.path.join(destination, name), "w", encoding="utf-8") as stream:
        json.dump(body, stream, indent=2)
        stream.write("\n")
PY
  python3 "$HERE/canonicalize_dump_paths.py" "$CANDIDATE_ROOT/dumps"
else
  mkdir -p "$CANDIDATE_ROOT"
  cp -R "$HERE/dumps" "$CANDIDATE_ROOT/dumps"
fi

python3 - \
  "$CANDIDATE_ROOT/dumps/num__<impl u32>__leading_zeros.json" \
  "$CANDIDATE_ROOT/dumps/num__<impl u8>__count_zeros.json" \
  "$CANDIDATE_ROOT/forgeries" <<'PY'
from copy import deepcopy
import json
import os
import sys

intrinsic_source, preop_source, destination = sys.argv[1:]
with open(intrinsic_source, encoding="utf-8") as stream:
    genuine = json.load(stream)
marker = "@trust-rustc-intrinsic::"
controls = (
    ("F1_fake_ctlz_defpath", "intrinsics::ctlz::<u32>", None),
    ("F2_nontotal_ctlz_nonzero", marker + "intrinsics::ctlz_nonzero::<u32>", None),
    ("F3_wrong_arity_ctlz", marker + "intrinsics::ctlz::<u32>", "arity"),
    ("F4_foreign_ctlz", marker + "intrinsics::ctlz::<u32>", "foreign"),
    ("F5_unmodeled_intrinsic_transmute", marker + "intrinsics::transmute::<u32, u32>", None),
    ("F6_valid_control_leading_zeros", marker + "intrinsics::ctlz::<u32>", None),
)
os.makedirs(destination)
for label, callee, mutation in controls:
    body = deepcopy(genuine)
    body["name"] = label
    body["def_path"] = "forgery::" + label
    calls = [
        block["terminator"]["Call"]
        for block in body["body"]["blocks"]
        if isinstance(block["terminator"], dict) and "Call" in block["terminator"]
    ]
    if len(calls) != 1:
        raise SystemExit(f"{label}: genuine base does not have exactly one Call")
    call = calls[0]
    call["func"] = callee
    if mutation == "arity":
        call["args"].append(deepcopy(call["args"][0]))
    elif mutation == "foreign":
        call["is_foreign"] = True
    path = os.path.join(destination, f"forgery__{label}.json")
    with open(path, "w", encoding="utf-8") as stream:
        json.dump(body, stream, indent=2)
        stream.write("\n")

with open(preop_source, encoding="utf-8") as stream:
    genuine_preop = json.load(stream)
preop_controls = (
    ("G1_wrong_callee_evil", "callee", "evil::count_ones::<u8>"),
    ("G2_wrong_method_trailing_zeros", "callee", "num::<impl u8>::trailing_zeros"),
    ("G3_sideeffect_preop_binaryop", "binary", None),
    ("G4_preop_unmodeled_value", "self_read", None),
    ("G5_multiwrite_preop_temp", "multiwrite", None),
    ("G6_valid_control_count_zeros", "valid", None),
)
for label, mutation, payload in preop_controls:
    body = deepcopy(genuine_preop)
    body["def_path"] = "forgery::" + label
    blocks = body["body"]["blocks"]
    calls = [
        block["terminator"]["Call"]
        for block in blocks
        if isinstance(block["terminator"], dict) and "Call" in block["terminator"]
    ]
    if len(calls) != 1:
        raise SystemExit(f"{label}: genuine pre-op base does not have exactly one Call")
    statements = blocks[0]["stmts"]
    if len(statements) != 1 or "Assign" not in statements[0]:
        raise SystemExit(f"{label}: genuine pre-op base does not have one assignment")
    assignment = statements[0]["Assign"]
    if mutation == "callee":
        calls[0]["func"] = payload
    elif mutation == "binary":
        source = deepcopy(assignment["rvalue"]["UnaryOp"][1])
        assignment["rvalue"] = {"BinaryOp": ["Add", source, deepcopy(source)]}
    elif mutation == "self_read":
        assignment["rvalue"]["UnaryOp"][1] = {
            "Copy": {"local": 2, "projections": []}
        }
    elif mutation == "multiwrite":
        return_blocks = [block for block in blocks if block["terminator"] == "Return"]
        if len(return_blocks) != 1:
            raise SystemExit(f"{label}: genuine pre-op base lacks a unique Return")
        return_blocks[0]["stmts"].append(deepcopy(statements[0]))
    elif mutation != "valid":
        raise SystemExit(f"{label}: unknown mutation {mutation}")
    path = os.path.join(destination, f"preop__{label}.json")
    with open(path, "w", encoding="utf-8") as stream:
        json.dump(body, stream, indent=2)
        stream.write("\n")
PY
cp "$HERE/results.tsv" "$CANDIDATE_ROOT/results.tsv"
cp "$HERE/forgeries.tsv" "$CANDIDATE_ROOT/forgeries.tsv"
python3 "$HERE/canonicalize_dump_paths.py" "$CANDIDATE_ROOT/dumps"
python3 "$HERE/canonicalize_dump_paths.py" "$CANDIDATE_ROOT/forgeries"

dump_count=$(find "$CANDIDATE_ROOT/dumps" -type f -name '*.json' | wc -l | tr -d ' ')
forgery_count=$(find "$CANDIDATE_ROOT/forgeries" -type f -name '*.json' | wc -l | tr -d ' ')
test "$dump_count" -eq 32 || {
  echo "error: expected exactly 32 bitmethod-family dumps, found $dump_count" >&2
  exit 1
}
test "$forgery_count" -eq 12 || {
  echo "error: expected exactly 12 bitmethod controls, found $forgery_count" >&2
  exit 1
}

tail -n +2 "$HERE/results.tsv" | cut -f1 | sort > "$TMP/expected-paths"
for file in "$CANDIDATE_ROOT"/dumps/*.json; do
  python3 -c "import json,sys; print(json.load(open(sys.argv[1]))['def_path'])" "$file"
done | sort > "$TMP/actual-paths"
test "$(wc -l < "$TMP/expected-paths" | tr -d ' ')" -eq 32
test "$(uniq "$TMP/expected-paths" | wc -l | tr -d ' ')" -eq 32
cmp "$TMP/expected-paths" "$TMP/actual-paths"

tail -n +2 "$HERE/forgeries.tsv" | cut -f1 | sort > "$TMP/expected-forgeries"
for file in "$CANDIDATE_ROOT"/forgeries/*.json; do
  python3 -c "import json,sys; print(json.load(open(sys.argv[1]))['def_path'])" "$file"
done | sort > "$TMP/actual-forgeries"
test "$(wc -l < "$TMP/expected-forgeries" | tr -d ' ')" -eq 12
test "$(uniq "$TMP/expected-forgeries" | wc -l | tr -d ' ')" -eq 12
cmp "$TMP/expected-forgeries" "$TMP/actual-forgeries"

# Pin the marker boundary independently of the verdict tools. Exactly the
# twelve unsigned direct-intrinsic leaves carry compiler-extracted authority.
# Ordinary method delegates and count_zeros remain unmarked. The detached
# control panel deliberately leaves F1 unmarked and retains the marker on
# F2-F6 so each mutation reaches its intended fail-closed gate.
python3 - "$CANDIDATE_ROOT/dumps" "$CANDIDATE_ROOT/forgeries" <<'PY'
import glob
import json
import os
import sys

dumps, controls = sys.argv[1:]
marker = "@trust-rustc-intrinsic::"
expected_marked = {
    f"num::<impl {ty}>::{method}": f"{marker}intrinsics::{intrinsic}::<{ty}>"
    for ty in ("u8", "u16", "u32", "u64")
    for method, intrinsic in (
        ("leading_zeros", "ctlz"),
        ("swap_bytes", "bswap"),
        ("reverse_bits", "bitreverse"),
    )
}
seen = {}
for path in sorted(glob.glob(os.path.join(dumps, "*.json"))):
    with open(path, encoding="utf-8") as stream:
        body = json.load(stream)
    calls = [
        block["terminator"]["Call"]
        for block in body["body"]["blocks"]
        if isinstance(block["terminator"], dict) and "Call" in block["terminator"]
    ]
    marked = [call["func"] for call in calls if call["func"].startswith(marker)]
    want = expected_marked.get(body["def_path"])
    if want is None and marked:
        raise SystemExit(f"unexpected intrinsic marker in {body['def_path']}: {marked}")
    if want is not None:
        if marked != [want]:
            raise SystemExit(f"marker mismatch in {body['def_path']}: expected {want}, got {marked}")
        seen[body["def_path"]] = want
if seen != expected_marked:
    raise SystemExit(f"marked dump inventory mismatch: {sorted(seen)}")

expected_controls = {
    "forgery::F1_fake_ctlz_defpath": ("intrinsics::ctlz::<u32>", 1, False),
    "forgery::F2_nontotal_ctlz_nonzero": (marker + "intrinsics::ctlz_nonzero::<u32>", 1, False),
    "forgery::F3_wrong_arity_ctlz": (marker + "intrinsics::ctlz::<u32>", 2, False),
    "forgery::F4_foreign_ctlz": (marker + "intrinsics::ctlz::<u32>", 1, True),
    "forgery::F5_unmodeled_intrinsic_transmute": (marker + "intrinsics::transmute::<u32, u32>", 1, False),
    "forgery::F6_valid_control_leading_zeros": (marker + "intrinsics::ctlz::<u32>", 1, False),
    "forgery::G1_wrong_callee_evil": ("evil::count_ones::<u8>", 1, False),
    "forgery::G2_wrong_method_trailing_zeros": ("num::<impl u8>::trailing_zeros", 1, False),
    "forgery::G3_sideeffect_preop_binaryop": ("num::<impl u8>::count_ones", 1, False),
    "forgery::G4_preop_unmodeled_value": ("num::<impl u8>::count_ones", 1, False),
    "forgery::G5_multiwrite_preop_temp": ("num::<impl u8>::count_ones", 1, False),
    "forgery::G6_valid_control_count_zeros": ("num::<impl u8>::count_ones", 1, False),
}
seen_controls = {}
for path in sorted(glob.glob(os.path.join(controls, "*.json"))):
    with open(path, encoding="utf-8") as stream:
        body = json.load(stream)
    calls = [
        block["terminator"]["Call"]
        for block in body["body"]["blocks"]
        if isinstance(block["terminator"], dict) and "Call" in block["terminator"]
    ]
    if len(calls) != 1:
        raise SystemExit(f"{body['def_path']}: expected exactly one Call")
    call = calls[0]
    seen_controls[body["def_path"]] = (call["func"], len(call["args"]), call["is_foreign"])
if seen_controls != expected_controls:
    raise SystemExit(f"control mutation inventory mismatch: {seen_controls}")
PY

# A checksum manifest is only an inventory guarantee when it names every
# published artifact exactly once. Check coverage before checking hashes so a
# newly added control cannot silently fall outside the manifest.
(
  cd "$CANDIDATE_ROOT"
  find dumps forgeries -type f -name '*.json' -print
  printf '%s\n' results.tsv forgeries.tsv
) | LC_ALL=C sort > "$TMP/expected-artifacts"
cut -c 67- "$HERE/ARTIFACTS.sha256" | LC_ALL=C sort > "$TMP/manifest-artifacts"
cmp "$TMP/expected-artifacts" "$TMP/manifest-artifacts" || {
  echo "error: ARTIFACTS.sha256 does not exactly cover the published corpus" >&2
  exit 1
}
check_manifest "$CANDIDATE_ROOT" "$HERE/ARTIFACTS.sha256"

CARGO_TARGET_DIR="$VALIDATION_TARGET_DIR" CARGO_NET_OFFLINE=${CARGO_NET_OFFLINE:-true} \
  RUSTC_BOOTSTRAP=1 \
  cargo build --release --locked -p trust-clean --manifest-path "$REPO/crates/Cargo.toml" \
  --bin ff-gate-diagnose-2026-07-10 --bin census-2026-07-06
TOOLS="$VALIDATION_TARGET_DIR/release"
"$TOOLS/ff-gate-diagnose-2026-07-10" "$CANDIDATE_ROOT/dumps" \
  > "$TMP/ff-gate.tsv" 2> "$TMP/ff-gate.stderr"
TRUST_CENSUS_BUDGET_SECS=${TRUST_CENSUS_BUDGET_SECS:-180} \
  "$TOOLS/census-2026-07-06" "$CANDIDATE_ROOT/dumps" \
  > "$TMP/census.tsv" 2> "$TMP/census.stderr"
"$TOOLS/ff-gate-diagnose-2026-07-10" "$CANDIDATE_ROOT/forgeries" \
  > "$TMP/forgery-ff.tsv" 2> "$TMP/forgery-ff.stderr"
TRUST_CENSUS_BUDGET_SECS=${TRUST_CENSUS_BUDGET_SECS:-180} \
  "$TOOLS/census-2026-07-06" "$CANDIDATE_ROOT/forgeries" \
  > "$TMP/forgery-census.tsv" 2> "$TMP/forgery-census.stderr"
if grep -F "# WARNING:" "$TMP/census.stderr" "$TMP/forgery-census.stderr" >/dev/null; then
  echo "error: census reported an incomplete or unreliable row" >&2
  grep -F "# WARNING:" "$TMP/census.stderr" "$TMP/forgery-census.stderr" >&2
  exit 1
fi

expected_ff_header='def_path	cluster_tag	via_ir_shape	via_ir_safety	via_mirsem_shape	via_mirsem_sl_safety_discharged	via_mirsem_call_requires	via_mirsem_loop_full	fully_faithful'
expected_census_header='def_path	total	inhabited	type_grounded_not_inhabited	not_grounded	kernel_rejected	safety_obligations	safety_discharged	fully_faithful	via_trustir	mirsem_fallback	declined	expr_fold_decline'
for table in "$TMP/ff-gate.tsv" "$TMP/forgery-ff.tsv"; do
  test "$(sed -n '1p' "$table")" = "$(printf '%b' "$expected_ff_header")" || {
    echo "error: FF-gate TSV schema drift in $table" >&2
    exit 1
  }
done
for table in "$TMP/census.tsv" "$TMP/forgery-census.tsv"; do
  test "$(sed -n '1p' "$table")" = "$(printf '%b' "$expected_census_header")" || {
    echo "error: census TSV schema drift in $table" >&2
    exit 1
  }
done

awk -F '\t' '
  NR == FNR { if (FNR > 1) expected[$1] = $2; next }
  FNR == 1 { next }
  {
    got = ($9 == "true" ? "FULLY_FAITHFUL" : $2)
    if (!($1 in expected) || got != expected[$1]) {
      print "FF-gate mismatch for " $1 ": expected " expected[$1] ", got " got > "/dev/stderr"
      bad = 1
    }
    if (++count[$1] != 1) { print "duplicate FF-gate row " $1 > "/dev/stderr"; bad = 1 }
    seen[$1] = 1
  }
  END {
    for (path in expected) if (!(path in seen)) { print "FF-gate missing " path > "/dev/stderr"; bad = 1 }
    exit bad
  }
' "$HERE/results.tsv" "$TMP/ff-gate.tsv"

awk -F '\t' '
  NR == FNR {
    if (FNR > 1) {
      verdict[$1] = $2; lane[$1] = $3; rejected[$1] = $4
      safety[$1] = $5; discharged[$1] = $6
    }
    next
  }
  FNR == 1 { next }
  {
    got_verdict = ($9 == 1 ? "FULLY_FAITHFUL" : "SHAPE_GAP")
    got_lane = ($10 == 1 ? "via_trustir" : ($11 == 1 ? "via_mirsem" : "-"))
    if (!($1 in verdict) || $2 != 1 || got_verdict != verdict[$1] || got_lane != lane[$1] ||
        $6 != rejected[$1] || $7 != safety[$1] || $8 != discharged[$1] || $12 != 0) {
      print "census mismatch for " $1 > "/dev/stderr"
      bad = 1
    }
    if (++count[$1] != 1) { print "duplicate census row " $1 > "/dev/stderr"; bad = 1 }
    seen[$1] = 1
  }
  END {
    for (path in verdict) if (!(path in seen)) { print "census missing " path > "/dev/stderr"; bad = 1 }
    exit bad
  }
' "$HERE/results.tsv" "$TMP/census.tsv"

awk -F '\t' '
  NR == FNR {
    if (FNR > 1) for (column = 2; column <= 9; column++) expected[$1, column] = $column
    next
  }
  FNR == 1 { next }
  {
    for (column = 2; column <= 9; column++) {
      if ($column != expected[$1, column]) {
        print "forgery FF mismatch for " $1 " column " column > "/dev/stderr"
        bad = 1
      }
    }
    if (++count[$1] != 1) { print "duplicate forgery FF row " $1 > "/dev/stderr"; bad = 1 }
    seen[$1] = 1
  }
  END {
    for (key in expected) { split(key, part, SUBSEP); paths[part[1]] = 1 }
    for (path in paths) if (!(path in seen)) { print "forgery FF missing " path > "/dev/stderr"; bad = 1 }
    exit bad
  }
' "$HERE/forgeries.tsv" "$TMP/forgery-ff.tsv"

awk -F '\t' '
  NR == FNR {
    if (FNR > 1) {
      rejected[$1] = $10; safety[$1] = $11; discharged[$1] = $12
      faithful[$1] = ($9 == "true" ? 1 : 0); via_ir[$1] = $13
      via_mirsem[$1] = $14; declined[$1] = $15
    }
    next
  }
  FNR == 1 { next }
  {
    if (!($1 in faithful) || $2 != 1 || $6 != rejected[$1] || $7 != safety[$1] ||
        $8 != discharged[$1] || $9 != faithful[$1] || $10 != via_ir[$1] ||
        $11 != via_mirsem[$1] || $12 != declined[$1]) {
      print "forgery census mismatch for " $1 > "/dev/stderr"
      bad = 1
    }
    if (++count[$1] != 1) { print "duplicate forgery census row " $1 > "/dev/stderr"; bad = 1 }
    seen[$1] = 1
  }
  END {
    for (path in faithful) if (!(path in seen)) { print "forgery census missing " path > "/dev/stderr"; bad = 1 }
    exit bad
  }
' "$HERE/forgeries.tsv" "$TMP/forgery-census.tsv"

if test "$VALIDATE_ONLY" -eq 0; then
  mkdir "$BACKUP_ROOT"
  PUBLISHING=1
  for directory in dumps forgeries; do
    mv "$HERE/$directory" "$BACKUP_ROOT/$directory"
  done
  for directory in dumps forgeries; do
    mv "$CANDIDATE_ROOT/$directory" "$HERE/$directory"
  done
  PUBLISHING=0
  rm -rf "$BACKUP_ROOT"
fi
echo "validated machine fields: 32/32 fully faithful, kernel_rejected=0; twelve controls exact"
