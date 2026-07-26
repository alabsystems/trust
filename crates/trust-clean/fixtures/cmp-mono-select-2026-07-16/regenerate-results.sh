#!/bin/sh
# Rebuild the non-authoritative census manifest from the 22 committed MIR dumps.
set -eu

HERE=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
DUMPS="$HERE/dumps"
OUT="$HERE/results.tsv"
EXPECTED=22
JQ=${JQ:-jq}
REPO=${REPO:-$(git -C "$HERE" rev-parse --show-toplevel)}
FF_GATE=${FF_GATE:-"$REPO/crates/target/release/ff-gate-diagnose-2026-07-10"}

command -v "$JQ" >/dev/null 2>&1 || {
  echo "missing jq: set JQ to a compatible executable" >&2
  exit 1
}
[ -x "$FF_GATE" ] || {
  echo "missing executable: $FF_GATE" >&2
  exit 1
}
command -v cmp >/dev/null 2>&1 || { echo "missing cmp" >&2; exit 1; }
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

LOCK="$HERE/.regenerate-results.lock"
if ! mkdir "$LOCK" 2>/dev/null; then
  echo "another manifest regeneration is active, or recovery is required: $LOCK" >&2
  exit 1
fi
printf '%s\n' "$$" >"$LOCK/pid"
TMP=
cleanup() {
  cleanup_status=$?
  trap - 0 HUP INT TERM
  set +e
  [ -z "$TMP" ] || rm -rf "$TMP"
  rm -rf "$LOCK"
  exit "$cleanup_status"
}
trap cleanup 0
trap 'exit 1' HUP INT TERM
TMP=$(mktemp -d "$HERE/.regenerate-results.tmp.XXXXXX")
ff_gate_sha256=$(sha256_file "$FF_GATE")
"$FF_GATE" "$DUMPS" >"$TMP/ff-gate.tsv"
awk -F '\t' '
  BEGIN {
    expected["<i32 as std::cmp::Ord>::max"] = "FULLY_FAITHFUL"
    expected["<i32 as std::cmp::Ord>::min"] = "FULLY_FAITHFUL"
    expected["<i64 as std::cmp::Ord>::max"] = "FULLY_FAITHFUL"
    expected["<i64 as std::cmp::Ord>::min"] = "FULLY_FAITHFUL"
    expected["<u8 as std::cmp::Ord>::max"] = "FULLY_FAITHFUL"
    expected["<u8 as std::cmp::Ord>::min"] = "FULLY_FAITHFUL"
    expected["std::cmp::max::<i32>"] = "FULLY_FAITHFUL"
    expected["std::cmp::max::<u8>"] = "FULLY_FAITHFUL"
    expected["std::cmp::min::<i32>"] = "FULLY_FAITHFUL"
    expected["std::cmp::min::<u8>"] = "FULLY_FAITHFUL"
    expected["max_i32"] = "FULLY_FAITHFUL"
    expected["max_u8"] = "FULLY_FAITHFUL"
    expected["min_i32"] = "FULLY_FAITHFUL"
    expected["min_u8"] = "FULLY_FAITHFUL"
    expected["omax_i64"] = "FULLY_FAITHFUL"
    expected["omin_i64"] = "FULLY_FAITHFUL"
    expected["clamp_i32"] = "SHAPE_GAP"
    expected["core::fmt::num::<impl std::fmt::Debug for i32>::fmt"] = "SHAPE_GAP"
    expected["std::cmp::impls::<impl std::cmp::Ord for i32>::clamp"] = "SHAPE_GAP"
    expected["std::cmp::impls::<impl std::cmp::PartialOrd for i32>::lt"] = "SHAPE_GAP"
    expected["std::cmp::impls::<impl std::cmp::PartialOrd for i64>::lt"] = "SHAPE_GAP"
    expected["std::cmp::impls::<impl std::cmp::PartialOrd for u8>::lt"] = "SHAPE_GAP"
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
    rows++
    if (NF != 9 || !($1 in expected) || seen[$1]++ || $2 != expected[$1]) {
      bad = 1
    } else if ($2 == "FULLY_FAITHFUL") {
      faithful++
      if ($9 != "true") bad = 1
    } else {
      gaps++
      if ($3 != "false" || $4 != "false" || $5 != "false" ||
          $6 != "false" || $7 != "false" || $8 != "false" || $9 != "false") bad = 1
    }
  }
  END {
    for (def_path in expected) if (seen[def_path] != 1) bad = 1
    exit !(rows == 22 && faithful == 16 && gaps == 6 && !bad)
  }
' "$TMP/ff-gate.tsv" || {
  echo "unexpected historical FF-gate classification" >&2
  exit 1
}
: >"$TMP/rows"
count=0
for dump in "$DUMPS"/*.json; do
  "$JQ" -e 'type == "object" and (.def_path | type == "string" and length > 0 and (test("[\\t\\r\\n]") | not))' \
    "$dump" >/dev/null
  digest=$(sha256_file "$dump")
  def_path=$("$JQ" -r '.def_path' "$dump")
  def_path_json=$("$JQ" -c '.def_path' "$dump")
  cluster=$(awk -F '\t' -v key="$def_path" '
    NR > 1 && $1 == key { found++; value = $2 }
    END { if (found != 1) exit 1; print value }
  ' "$TMP/ff-gate.tsv") || {
    echo "missing or duplicate analyzer row for $def_path" >&2
    exit 1
  }
  digest_after=$(sha256_file "$dump")
  [ "$digest_after" = "$digest" ] || {
    echo "dump changed while its manifest row was assembled: $dump" >&2
    exit 1
  }
  printf '%s\t%s\t%s\n' "$digest" "$def_path_json" "$cluster" >>"$TMP/rows"
  count=$((count + 1))
done

if [ "$count" -ne "$EXPECTED" ]; then
  echo "expected $EXPECTED dump records, found $count" >&2
  exit 1
fi
if [ "$(cut -f1 "$TMP/rows" | LC_ALL=C sort -u | wc -l | tr -d ' ')" -ne "$EXPECTED" ]; then
  echo "duplicate dump SHA-256 in corpus" >&2
  exit 1
fi
if [ "$(cut -f2 "$TMP/rows" | LC_ALL=C sort -u | wc -l | tr -d ' ')" -ne "$EXPECTED" ]; then
  echo "duplicate def_path in corpus" >&2
  exit 1
fi
{
  printf 'dump_sha256\tdef_path_json\tcluster_tag\n'
  LC_ALL=C sort "$TMP/rows"
} >"$TMP/results.tsv"
awk -F '\t' 'NF != 3 { exit 1 }' "$TMP/results.tsv" || {
  echo "generated results.tsv is not a strict three-column TSV" >&2
  exit 1
}

# Re-read the complete corpus immediately before publication. Per-row checks
# alone allow a record processed early to change while later rows are built.
: >"$TMP/rows.after"
count_after=0
for dump in "$DUMPS"/*.json; do
  "$JQ" -e 'type == "object" and (.def_path | type == "string" and length > 0 and (test("[\\t\\r\\n]") | not))' \
    "$dump" >/dev/null
  digest=$(sha256_file "$dump")
  def_path=$("$JQ" -r '.def_path' "$dump")
  def_path_json=$("$JQ" -c '.def_path' "$dump")
  cluster=$(awk -F '\t' -v key="$def_path" '
    NR > 1 && $1 == key { found++; value = $2 }
    END { if (found != 1) exit 1; print value }
  ' "$TMP/ff-gate.tsv") || {
    echo "missing or duplicate analyzer row for $def_path during final validation" >&2
    exit 1
  }
  digest_after=$(sha256_file "$dump")
  [ "$digest_after" = "$digest" ] || {
    echo "dump changed during final corpus validation: $dump" >&2
    exit 1
  }
  printf '%s\t%s\t%s\n' "$digest" "$def_path_json" "$cluster" >>"$TMP/rows.after"
  count_after=$((count_after + 1))
done
[ "$count_after" -eq "$EXPECTED" ] || {
  echo "expected $EXPECTED records during final validation, found $count_after" >&2
  exit 1
}
cmp -s "$TMP/rows" "$TMP/rows.after" || {
  echo "historical corpus changed while results.tsv was assembled" >&2
  exit 1
}
[ "$(sha256_file "$FF_GATE")" = "$ff_gate_sha256" ] || {
  echo "FF-gate analyzer changed while results.tsv was assembled: $FF_GATE" >&2
  exit 1
}
mv "$TMP/results.tsv" "$OUT"
echo "wrote $OUT ($count records)"
