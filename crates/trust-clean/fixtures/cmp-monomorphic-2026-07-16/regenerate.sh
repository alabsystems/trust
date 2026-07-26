#!/bin/sh
# Rebuild and validate the foreign concrete core::cmp W16 observation corpus.
set -eu

HERE=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
REPO=${REPO:-$(git -C "$HERE" rev-parse --show-toplevel)}
TRUSTC=${TRUSTC:-"$REPO/build/host/stage2/bin/trustc"}
FF_GATE=${FF_GATE:-"$REPO/crates/target/release/ff-gate-diagnose-2026-07-10"}
CENSUS=${CENSUS:-"$REPO/crates/target/release/census-2026-07-06"}
SRC="$REPO/crates/trust-clean/fixtures/stdlib-leaf-cmp-2026-07-16/SOURCE/src/lib.rs"
CONTROL_SOURCE_DIR="$REPO/crates/trust-clean/fixtures/stdlib-leaf-cmp-2026-07-16/controls"
TRUST_VERIFY_RS="$REPO/compiler/rustc_mir_transform/src/trust_verify.rs"
TRUST_MIR_EXTRACT_LIB_RS="$REPO/crates/trust-mir-extract/src/lib.rs"
TRUST_MIR_EXTRACT_CONVERT_RS="$REPO/crates/trust-mir-extract/src/convert.rs"

for executable in "$TRUSTC" "$FF_GATE" "$CENSUS"; do
  [ -x "$executable" ] || {
    echo "missing executable: $executable" >&2
    exit 1
  }
done
[ -f "$SRC" ] || { echo "missing cmp source: $SRC" >&2; exit 1; }
[ -d "$CONTROL_SOURCE_DIR" ] || {
  echo "missing cmp control source directory: $CONTROL_SOURCE_DIR" >&2
  exit 1
}

if command -v sha256sum >/dev/null 2>&1; then
  SHA256_COMMAND=sha256sum
elif command -v shasum >/dev/null 2>&1; then
  SHA256_COMMAND=shasum
else
  echo "missing sha256sum/shasum" >&2
  exit 1
fi
sha256_file() {
  if [ "$SHA256_COMMAND" = sha256sum ]; then
    trust_sha_output=$(sha256sum "$1") || return 1
  else
    trust_sha_output=$(shasum -a 256 "$1") || return 1
  fi
  trust_sha_digest=${trust_sha_output%%[[:space:]]*}
  if [ "${#trust_sha_digest}" -ne 64 ]; then
    echo "invalid SHA-256 length for $1" >&2
    return 1
  fi
  case "$trust_sha_digest" in
    *[!0123456789abcdef]*)
      echo "invalid SHA-256 text for $1" >&2
      return 1
      ;;
  esac
  printf '%s\n' "$trust_sha_digest"
}

command -v jq >/dev/null 2>&1 || { echo "missing jq" >&2; exit 1; }
command -v python3 >/dev/null 2>&1 || { echo "missing python3" >&2; exit 1; }
command -v cmp >/dev/null 2>&1 || { echo "missing cmp" >&2; exit 1; }

# The fixture is a multi-file publication. Serialize regenerators with an
# atomic same-filesystem directory lock; a stale lock is preserved for manual
# recovery rather than guessed away.
LOCK="$HERE/.regenerate.lock"
if ! mkdir "$LOCK" 2>/dev/null; then
  echo "another regeneration is active, or recovery is required: $LOCK" >&2
  exit 1
fi
printf '%s\n' "$$" >"$LOCK/pid"

TMP=
publish=
backup=
installed=
backed_up=
publishing=0
rollback_failed=0
cleanup() {
  cleanup_status=$?
  trap - 0 HUP INT TERM
  set +e
  if [ "$publishing" -eq 1 ]; then
    for cleanup_target in $installed; do
      rm -rf "$HERE/$cleanup_target" || {
        echo "failed to remove $cleanup_target during publication rollback" >&2
        cleanup_status=1
        rollback_failed=1
      }
    done
    for cleanup_target in $backed_up; do
      if [ -e "$backup/$cleanup_target" ]; then
        mv "$backup/$cleanup_target" "$HERE/$cleanup_target" || {
          echo "failed to restore $cleanup_target during publication rollback" >&2
          cleanup_status=1
          rollback_failed=1
        }
      fi
    done
  fi
  [ -z "$TMP" ] || rm -rf "$TMP"
  if [ "$rollback_failed" -eq 0 ]; then
    rm -rf "$LOCK"
  else
    echo "publication recovery bytes preserved at $LOCK" >&2
    echo "backup=$backup staged=$publish" >&2
  fi
  exit "$cleanup_status"
}
trap cleanup 0
trap 'exit 1' HUP INT TERM

TMP=$(mktemp -d "$HERE/.regenerate.tmp.XXXXXX")
mkdir -p "$TMP/all" "$TMP/sliced" "$TMP/controls"

# Hash the launcher before any binary inspection or execution. The final
# unchanged check then binds every derived path/version to these same bytes.
trustc_sha256=$(sha256_file "$TRUSTC")
TRUSTC_DIR=$(CDPATH= cd -- "$(dirname -- "$TRUSTC")" && pwd)
case $(uname -s) in
  Darwin)
    command -v otool >/dev/null 2>&1 || { echo "missing otool" >&2; exit 1; }
    driver_ref=$(otool -L "$TRUSTC" | awk '$1 ~ /^@rpath\/librustc_driver-.*\.dylib$/ { print $1; exit }')
    [ -n "$driver_ref" ] || { echo "trustc has no @rpath rustc_driver" >&2; exit 1; }
    otool -l "$TRUSTC" | awk '
      $1 == "cmd" && $2 == "LC_RPATH" { in_rpath = 1; next }
      in_rpath && $1 == "path" { print $2; in_rpath = 0 }
    ' | grep -Fx '@loader_path/../lib' >/dev/null || {
      echo "trustc does not load rustc_driver from @loader_path/../lib" >&2
      exit 1
    }
    DRIVER="$TRUSTC_DIR/../lib/${driver_ref#@rpath/}"
    ;;
  Linux)
    command -v ldd >/dev/null 2>&1 || { echo "missing ldd" >&2; exit 1; }
    DRIVER=$(ldd "$TRUSTC" | awk '$1 ~ /^librustc_driver-.*\.so$/ { print $3; exit }')
    ;;
  *)
    echo "unsupported host for rustc_driver identity discovery: $(uname -s)" >&2
    exit 1
    ;;
esac
[ -f "$DRIVER" ] || { echo "missing loaded rustc_driver: $DRIVER" >&2; exit 1; }
rustc_driver_sha256=$(sha256_file "$DRIVER")

SYSROOT=$("$TRUSTC" --print sysroot)
TARGET_LIBDIR=$("$TRUSTC" --print target-libdir)
[ -d "$SYSROOT" ] || { echo "trustc sysroot is not a directory: $SYSROOT" >&2; exit 1; }
[ -d "$TARGET_LIBDIR" ] || {
  echo "trustc target libdir is not a directory: $TARGET_LIBDIR" >&2
  exit 1
}
case "$TARGET_LIBDIR" in
  "$SYSROOT"/*) ;;
  *)
    echo "trustc target libdir is outside its reported sysroot" >&2
    exit 1
    ;;
esac
case "$SYSROOT" in
  "$REPO"/*) sysroot_locator="REPO/${SYSROOT#"$REPO"/}" ;;
  *) sysroot_locator=TRUSTC_REPORTED_SYSROOT ;;
esac
target_libdir_locator="SYSROOT/${TARGET_LIBDIR#"$SYSROOT"/}"

set -- "$TARGET_LIBDIR"/libcore-*.rlib
[ "$#" -eq 1 ] && [ -f "$1" ] || {
  echo "expected exactly one libcore rlib in $TARGET_LIBDIR" >&2
  exit 1
}
CORE_RLIB=$1
set -- "$TARGET_LIBDIR"/libcore-*.rmeta
[ "$#" -eq 1 ] && [ -f "$1" ] || {
  echo "expected exactly one libcore rmeta in $TARGET_LIBDIR" >&2
  exit 1
}
CORE_RMETA=$1

write_directory_manifest() {
  manifest_directory=$1
  manifest_output=$2
  : >"$manifest_output.rows"
  manifest_count=0
  for manifest_input in \
    "$manifest_directory"/* \
    "$manifest_directory"/.[!.]* \
    "$manifest_directory"/..?*
  do
    [ -f "$manifest_input" ] || continue
    manifest_name=${manifest_input##*/}
    manifest_digest=$(sha256_file "$manifest_input")
    printf '%s\t%s\n' "$manifest_digest" "$manifest_name" >>"$manifest_output.rows"
    manifest_count=$((manifest_count + 1))
  done
  [ "$manifest_count" -gt 0 ] || {
    echo "no regular files to manifest in $manifest_directory" >&2
    return 1
  }
  LC_ALL=C sort "$manifest_output.rows" >"$manifest_output"
  rm -f "$manifest_output.rows"
  awk -F '\t' 'NF != 2 { exit 1 }' "$manifest_output" || {
    echo "directory manifest is not strict two-column TSV: $manifest_directory" >&2
    return 1
  }
}

write_directory_manifest "$TARGET_LIBDIR" "$TMP/SYSROOT_TARGET_MANIFEST.tsv"
write_directory_manifest "$CONTROL_SOURCE_DIR" "$TMP/CONTROL_SOURCE_MANIFEST.tsv"

trustc_version=$("$TRUSTC" -vV)
source_sha256=$(sha256_file "$SRC")
trust_verify_rs_sha256=$(sha256_file "$TRUST_VERIFY_RS")
trust_mir_extract_lib_rs_sha256=$(sha256_file "$TRUST_MIR_EXTRACT_LIB_RS")
trust_mir_extract_convert_rs_sha256=$(sha256_file "$TRUST_MIR_EXTRACT_CONVERT_RS")
regenerate_sh_sha256=$(sha256_file "$HERE/regenerate.sh")
ff_gate_sha256=$(sha256_file "$FF_GATE")
census_sha256=$(sha256_file "$CENSUS")
core_rlib_sha256=$(sha256_file "$CORE_RLIB")
core_rmeta_sha256=$(sha256_file "$CORE_RMETA")
sysroot_target_manifest_sha256=$(sha256_file "$TMP/SYSROOT_TARGET_MANIFEST.tsv")
sysroot_target_manifest_count=$(wc -l <"$TMP/SYSROOT_TARGET_MANIFEST.tsv" | tr -d ' ')
control_source_manifest_sha256=$(sha256_file "$TMP/CONTROL_SOURCE_MANIFEST.tsv")
control_source_manifest_count=$(wc -l <"$TMP/CONTROL_SOURCE_MANIFEST.tsv" | tr -d ' ')
census_budget_secs=${TRUST_CENSUS_BUDGET_SECS:-120}
case "$census_budget_secs" in
  ''|*[!0123456789]*)
    echo "TRUST_CENSUS_BUDGET_SECS must be a positive integer" >&2
    exit 1
    ;;
esac
[ "$census_budget_secs" -gt 0 ] || {
  echo "TRUST_CENSUS_BUDGET_SECS must be greater than zero" >&2
  exit 1
}
echo "trustc: $(printf '%s\n' "$trustc_version" | tr '\n' ' ')"
echo "trustc_sha256: $trustc_sha256"
echo "rustc_driver_sha256: $rustc_driver_sha256"

TRUST_DUMP_MONO=1 \
  "$TRUSTC" --edition 2024 --crate-type lib --crate-name stdlib_leaf_cmp_source \
  --sysroot "$SYSROOT" \
  -Ztrust-dump=mir-only:"$TMP/all" -Ztrust-policy=advisory \
  -o "$TMP/probe.rlib" "$SRC"

dumped=$(find "$TMP/all" -type f -name '*.json' | wc -l | tr -d ' ')
[ "$dumped" -gt 0 ] || { echo "trustc emitted no MIR dumps" >&2; exit 1; }
echo "dumped $dumped bodies total"

# Validate every compiler output, then select an exact, closed identity set.
python3 - "$TMP/all" "$TMP/sliced" <<'PY'
import json
import os
import shutil
import sys

source, destination = sys.argv[1:]
wanted = {
    "<i32 as core::cmp::Ord>::max": "i32_as_core_cmp_Ord_max.json",
    "<i32 as core::cmp::Ord>::min": "i32_as_core_cmp_Ord_min.json",
    "<u8 as core::cmp::Ord>::max": "u8_as_core_cmp_Ord_max.json",
    "<u8 as core::cmp::Ord>::min": "u8_as_core_cmp_Ord_min.json",
    "core::cmp::max::<i32>": "core_cmp_max_i32.json",
    "core::cmp::min::<i32>": "core_cmp_min_i32.json",
}
found = {}
files = sorted(name for name in os.listdir(source) if name.endswith(".json"))
for name in files:
    path = os.path.join(source, name)
    try:
        with open(path, encoding="utf-8") as stream:
            record = json.load(stream)
    except Exception as error:
        raise SystemExit(f"malformed compiler JSON {path}: {error}") from error
    if not isinstance(record, dict) or not isinstance(record.get("def_path"), str) or not record["def_path"]:
        raise SystemExit(f"compiler JSON lacks non-empty def_path: {path}")
    def_path = record["def_path"]
    if def_path not in wanted:
        continue
    if def_path in found:
        raise SystemExit(f"duplicate selected def_path {def_path}: {found[def_path]} and {path}")
    found[def_path] = path
    shutil.copyfile(path, os.path.join(destination, wanted[def_path]))

missing = sorted(set(wanted) - set(found))
extra = sorted(set(found) - set(wanted))
if missing or extra or len(found) != len(wanted):
    raise SystemExit(f"exact cmp identity mismatch: missing={missing}, extra={extra}, found={len(found)}")
for def_path in sorted(found):
    print("  sliced:", def_path)
print("sliced", len(found), "monomorphic cmp bodies")
PY

cp -R "$REPO/crates/trust-clean/fixtures/stdlib-leaf-cmp-2026-07-16/controls/." \
  "$TMP/controls/"

# Run the current analyzers before publishing any bytes. The six exact real
# min/max bodies must certify through the scalar sentinel-select/tail-call
# lanes; four simple controls are faithful while nested clamp stays fail-closed.
"$FF_GATE" "$TMP/sliced" >"$TMP/FF_GATE_REAL.txt"
awk -F '\t' '
  BEGIN {
    expected["<i32 as core::cmp::Ord>::max"] = "leaf"
    expected["<i32 as core::cmp::Ord>::min"] = "leaf"
    expected["<u8 as core::cmp::Ord>::max"] = "leaf"
    expected["<u8 as core::cmp::Ord>::min"] = "leaf"
    expected["core::cmp::max::<i32>"] = "forwarder"
    expected["core::cmp::min::<i32>"] = "forwarder"
  }
  NR == 1 {
    if (NF != 9 ||
        $1 != "def_path" ||
        $2 != "cluster_tag" ||
        $3 != "via_ir_shape" ||
        $4 != "via_ir_safety" ||
        $5 != "via_mirsem_shape" ||
        $6 != "via_mirsem_sl_safety_discharged" ||
        $7 != "via_mirsem_call_requires" ||
        $8 != "via_mirsem_loop_full" ||
        $9 != "fully_faithful") bad = 1
    next
  }
  {
    if (NF != 9) { bad = 1; next }
    rows++
    if (!($1 in expected) || seen[$1]++ || $2 != "FULLY_FAITHFUL" ||
        $3 != "true" || $4 != "true" || $8 != "false" || $9 != "true") {
      bad = 1
    } else if (expected[$1] == "leaf") {
      leaves++
      if ($5 != "false" || $6 != "false" || $7 != "false") bad = 1
    } else {
      forwarders++
      if ($5 != "true" || $6 != "true" || $7 != "true") bad = 1
    }
  }
  END {
    for (def_path in expected) if (seen[def_path] != 1) bad = 1
    exit !(rows == 6 && leaves == 4 && forwarders == 2 && !bad)
  }
' "$TMP/FF_GATE_REAL.txt" || { echo "unexpected real-body FF-gate result" >&2; exit 1; }

"$FF_GATE" "$TMP/controls" >"$TMP/FF_GATE_CONTROLS.txt"
awk -F '\t' '
  BEGIN {
    expected["ctl_clamp_i32"] = 1
    expected["ctl_max_i32"] = 1
    expected["ctl_max_u8"] = 1
    expected["ctl_min_i32"] = 1
    expected["ctl_min_u8"] = 1
  }
  NR == 1 {
    if (NF != 9 ||
        $1 != "def_path" ||
        $2 != "cluster_tag" ||
        $3 != "via_ir_shape" ||
        $4 != "via_ir_safety" ||
        $5 != "via_mirsem_shape" ||
        $6 != "via_mirsem_sl_safety_discharged" ||
        $7 != "via_mirsem_call_requires" ||
        $8 != "via_mirsem_loop_full" ||
        $9 != "fully_faithful") bad = 1
    next
  }
  {
    if (NF != 9) { bad = 1; next }
    rows++
    if (!($1 in expected) || seen[$1]++) {
      bad = 1
    } else if ($1 == "ctl_clamp_i32") {
      clamp++
      if ($2 != "SHAPE_GAP" || $3 != "false" || $4 != "false" ||
          $5 != "false" || $6 != "false" || $7 != "false" ||
          $8 != "false" || $9 != "false") bad = 1
    } else {
      faithful++
      if ($2 != "FULLY_FAITHFUL" || $3 != "true" || $4 != "true" ||
          $5 != "true" || $6 != "true" || $7 != "true" ||
          $8 != "false" || $9 != "true") bad = 1
    }
  }
  END {
    for (def_path in expected) if (seen[def_path] != 1) bad = 1
    exit !(rows == 5 && clamp == 1 && faithful == 4 && !bad)
  }
' "$TMP/FF_GATE_CONTROLS.txt" || { echo "unexpected control FF-gate result" >&2; exit 1; }

TRUST_CENSUS_BUDGET_SECS=$census_budget_secs \
  "$CENSUS" "$TMP/sliced" >"$TMP/CENSUS_REAL.tsv"
awk -F '\t' '
  BEGIN {
    expected["<i32 as core::cmp::Ord>::max"] = 1
    expected["<i32 as core::cmp::Ord>::min"] = 1
    expected["<u8 as core::cmp::Ord>::max"] = 1
    expected["<u8 as core::cmp::Ord>::min"] = 1
    expected["core::cmp::max::<i32>"] = 1
    expected["core::cmp::min::<i32>"] = 1
  }
  NR == 1 {
    if (NF != 13 ||
        $1 != "def_path" ||
        $2 != "total" ||
        $3 != "inhabited" ||
        $4 != "type_grounded_not_inhabited" ||
        $5 != "not_grounded" ||
        $6 != "kernel_rejected" ||
        $7 != "safety_obligations" ||
        $8 != "safety_discharged" ||
        $9 != "fully_faithful" ||
        $10 != "via_trustir" ||
        $11 != "mirsem_fallback" ||
        $12 != "declined" ||
        $13 != "expr_fold_decline") bad = 1
    next
  }
  {
    if (NF != 13) { bad = 1; next }
    rows++
    if (!($1 in expected) || seen[$1]++ ||
        $2 != "1" || $3 != "1" || $4 != "0" || $5 != "0" || $6 != "0" ||
        $7 != "0" || $8 != "0" || $9 != "1" || $10 != "1" ||
        $11 != "0" || $12 != "0" || $13 != "-") bad = 1
  }
  END {
    for (def_path in expected) if (seen[def_path] != 1) bad = 1
    exit !(rows == 6 && !bad)
  }
' "$TMP/CENSUS_REAL.tsv" || { echo "unexpected real-body census result" >&2; exit 1; }

# Bind every published JSON byte string to its structural identity.
printf 'kind\tsha256\tdef_path_json\tfile\n' >"$TMP/MANIFEST.tsv"
: >"$TMP/manifest.rows"
for kind in dumps controls; do
  case "$kind" in
    dumps) directory="$TMP/sliced" ;;
    controls) directory="$TMP/controls" ;;
  esac
  for record in "$directory"/*.json; do
    jq -e 'type == "object" and (.def_path | type == "string" and length > 0)' \
      "$record" >/dev/null
    digest=$(sha256_file "$record")
    def_path_json=$(jq -c '.def_path' "$record")
    printf '%s\t%s\t%s\t%s\n' "$kind" "$digest" "$def_path_json" "$(basename "$record")" \
      >>"$TMP/manifest.rows"
  done
done
[ "$(wc -l <"$TMP/manifest.rows" | tr -d ' ')" -eq 11 ] || {
  echo "expected 11 manifest records" >&2
  exit 1
}
[ "$(cut -f1,3 "$TMP/manifest.rows" | LC_ALL=C sort -u | wc -l | tr -d ' ')" -eq 11 ] || {
  echo "duplicate kind/def_path identity in manifest" >&2
  exit 1
}
LC_ALL=C sort "$TMP/manifest.rows" >>"$TMP/MANIFEST.tsv"
awk -F '\t' 'NF != 4 { exit 1 }' "$TMP/MANIFEST.tsv" || {
  echo "manifest is not strict four-column TSV" >&2
  exit 1
}

# Bind the executed compiler, sysroot, sources, controls, and analyzers only
# after every observation has completed. A concurrent replacement must make
# the harvest fail, never produce a receipt naming bytes other than those run.
assert_unchanged() {
  unchanged_label=$1
  unchanged_path=$2
  unchanged_expected=$3
  unchanged_actual=$(sha256_file "$unchanged_path")
  [ "$unchanged_actual" = "$unchanged_expected" ] || {
    echo "$unchanged_label changed during W16 harvest: $unchanged_path" >&2
    return 1
  }
}
assert_unchanged trustc "$TRUSTC" "$trustc_sha256"
assert_unchanged loaded-rustc-driver "$DRIVER" "$rustc_driver_sha256"
assert_unchanged source "$SRC" "$source_sha256"
assert_unchanged trust-verify-source "$TRUST_VERIFY_RS" "$trust_verify_rs_sha256"
assert_unchanged trust-mir-extract-lib-source \
  "$TRUST_MIR_EXTRACT_LIB_RS" "$trust_mir_extract_lib_rs_sha256"
assert_unchanged trust-mir-extract-convert-source \
  "$TRUST_MIR_EXTRACT_CONVERT_RS" "$trust_mir_extract_convert_rs_sha256"
assert_unchanged regeneration-script "$HERE/regenerate.sh" "$regenerate_sh_sha256"
assert_unchanged ff-gate "$FF_GATE" "$ff_gate_sha256"
assert_unchanged census "$CENSUS" "$census_sha256"
assert_unchanged libcore-rlib "$CORE_RLIB" "$core_rlib_sha256"
assert_unchanged libcore-rmeta "$CORE_RMETA" "$core_rmeta_sha256"

write_directory_manifest "$TARGET_LIBDIR" "$TMP/SYSROOT_TARGET_MANIFEST.tsv.after"
cmp -s "$TMP/SYSROOT_TARGET_MANIFEST.tsv" "$TMP/SYSROOT_TARGET_MANIFEST.tsv.after" || {
  echo "target libdir changed during W16 harvest" >&2
  exit 1
}
write_directory_manifest "$CONTROL_SOURCE_DIR" "$TMP/CONTROL_SOURCE_MANIFEST.tsv.after"
cmp -s "$TMP/CONTROL_SOURCE_MANIFEST.tsv" "$TMP/CONTROL_SOURCE_MANIFEST.tsv.after" || {
  echo "control source directory changed during W16 harvest" >&2
  exit 1
}

manifest_sha256=$(sha256_file "$TMP/MANIFEST.tsv")
ff_gate_real_sha256=$(sha256_file "$TMP/FF_GATE_REAL.txt")
ff_gate_controls_sha256=$(sha256_file "$TMP/FF_GATE_CONTROLS.txt")
census_real_sha256=$(sha256_file "$TMP/CENSUS_REAL.tsv")

{
  printf 'schema=trust-w16-generation-v2\n'
  printf 'corpus_date=2026-07-16\n'
  printf 'source=%s\n' "${SRC#"$REPO"/}"
  printf 'source_sha256=%s\n' "$source_sha256"
  printf 'control_source_manifest_sha256=%s\n' "$control_source_manifest_sha256"
  printf 'control_source_manifest_count=%s\n' "$control_source_manifest_count"
  printf 'trust_verify_rs_sha256=%s\n' "$trust_verify_rs_sha256"
  printf 'trust_mir_extract_lib_rs_sha256=%s\n' "$trust_mir_extract_lib_rs_sha256"
  printf 'trust_mir_extract_convert_rs_sha256=%s\n' "$trust_mir_extract_convert_rs_sha256"
  printf 'regenerate_sh_sha256=%s\n' "$regenerate_sh_sha256"
  printf 'trustc_sha256=%s\n' "$trustc_sha256"
  printf 'rustc_driver_file=%s\n' "$(basename "$DRIVER")"
  printf 'rustc_driver_sha256=%s\n' "$rustc_driver_sha256"
  printf 'sysroot_locator=%s\n' "$sysroot_locator"
  printf 'target_libdir_locator=%s\n' "$target_libdir_locator"
  printf 'sysroot_target_manifest_sha256=%s\n' "$sysroot_target_manifest_sha256"
  printf 'sysroot_target_manifest_count=%s\n' "$sysroot_target_manifest_count"
  printf 'core_rlib_file=%s\n' "$(basename "$CORE_RLIB")"
  printf 'core_rlib_sha256=%s\n' "$core_rlib_sha256"
  printf 'core_rmeta_file=%s\n' "$(basename "$CORE_RMETA")"
  printf 'core_rmeta_sha256=%s\n' "$core_rmeta_sha256"
  printf 'ff_gate_sha256=%s\n' "$ff_gate_sha256"
  printf 'census_sha256=%s\n' "$census_sha256"
  printf 'census_budget_secs=%s\n' "$census_budget_secs"
  printf 'manifest_sha256=%s\n' "$manifest_sha256"
  printf 'ff_gate_real_sha256=%s\n' "$ff_gate_real_sha256"
  printf 'ff_gate_controls_sha256=%s\n' "$ff_gate_controls_sha256"
  printf 'census_real_sha256=%s\n' "$census_real_sha256"
  printf 'all_dump_count=%s\n' "$dumped"
  printf 'selected_dump_count=6\n'
  printf 'trustc_version='; printf '%s\n' "$trustc_version" | tr '\n' ';'; printf '\n'
} >"$TMP/GENERATION.txt"

# All extraction, identity, analyzer, and manifest checks succeeded. Stage all
# nine published targets on the fixture filesystem, then swap them under the
# exclusive lock with rollback on every caught failure or signal.
publish="$LOCK/publish"
backup="$LOCK/backup"
mkdir -p "$publish" "$backup"
cp -R "$TMP/sliced" "$publish/dumps"
cp -R "$TMP/controls" "$publish/controls"
for artifact in MANIFEST.tsv GENERATION.txt FF_GATE_REAL.txt FF_GATE_CONTROLS.txt CENSUS_REAL.tsv SYSROOT_TARGET_MANIFEST.tsv CONTROL_SOURCE_MANIFEST.tsv; do
  cp "$TMP/$artifact" "$publish/$artifact"
done

installed=
backed_up=
publishing=1
for target in dumps controls MANIFEST.tsv GENERATION.txt FF_GATE_REAL.txt FF_GATE_CONTROLS.txt CENSUS_REAL.tsv SYSROOT_TARGET_MANIFEST.tsv CONTROL_SOURCE_MANIFEST.tsv; do
  if [ -e "$HERE/$target" ]; then
    backed_up="$backed_up $target"
    mv "$HERE/$target" "$backup/$target"
  fi
  installed="$installed $target"
  if ! mv "$publish/$target" "$HERE/$target"; then
    exit 1
  fi
done
publishing=0

echo "published six exact foreign cmp bodies, five controls, and validated manifests"
