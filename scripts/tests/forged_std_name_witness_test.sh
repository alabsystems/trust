#!/usr/bin/env bash
# The failure-path proof for `scripts/forged_std_name_witness.sh`.
#
# Author: Andrew Yates. Copyright 2026 Andrew Yates. License: Apache-2.0 OR MIT.
#
# The witness's DIVERGED branch only runs when the compiler regresses, so a
# real trustc never exercises it — which is how a command substitution in its
# message went unnoticed: the explanation named `crate_is_authentic_std` inside
# double quotes, bash ran the predicate name as a COMMAND ("command not found")
# and printed the sentence with the name missing. The report a regression is
# supposed to produce was itself broken.
#
# A fake trustc drives each branch deterministically, with no build and no
# sysroot: it answers the instrument's positive control, builds nothing real,
# and reports a different number of masked sources for the two crate names.
set -euo pipefail

REPO_ROOT=$(cd -P "${BASH_SOURCE[0]%/*}/../.." && pwd -P)
WITNESS="$REPO_ROOT/scripts/forged_std_name_witness.sh"
TMP=$(mktemp -d)
trap 'rm -rf "$TMP"' EXIT

PASSED=0
fail() { printf 'forged_std_name_witness_test: %s\n' "$*" >&2; exit 1; }
ok()   { PASSED=$((PASSED + 1)); printf '  ok  %s\n' "$*"; }

[ -f "$WITNESS" ] || fail "witness is missing: $WITNESS"

# fake_trustc <std-masked-count>: the local control always fires once; the dep
# named `notstd` yields one masked source; the dep named `std` yields $1.
make_fake() {
  local path=$1 std_count=$2
  cat >"$path" <<EOF
#!/usr/bin/env bash
out=""
for a in "\$@"; do
  case "\$a" in
    -o) next_is_out=1; continue ;;
  esac
  if [ "\${next_is_out:-0}" = 1 ]; then out=\$a; next_is_out=0; fi
done
case " \$* " in
  *"--crate-type=rlib"*) : >"\$out"; exit 0 ;;
  *"/local.rs"*) echo "note: masked fail-closed source (control)"; exit 1 ;;
  *"libnotstd.rlib"*) echo "note: masked fail-closed source (dep drop)"; exit 1 ;;
  *"libstd.rlib"*)
    i=0; while [ "\$i" -lt $std_count ]; do
      echo "note: masked fail-closed source (dep drop)"; i=\$((i + 1)); done
    exit 1 ;;
esac
echo "fake trustc: unexpected invocation: \$*" >&2
exit 99
EOF
  chmod +x "$path"
}

# --- negative control: the two spellings DIVERGE -----------------------------
make_fake "$TMP/trustc-diverge" 0
set +e
bash "$WITNESS" "$TMP/trustc-diverge" >"$TMP/diverge.out" 2>"$TMP/diverge.err"
rc=$?
set -e
[ "$rc" -eq 1 ] || fail "a divergence must exit 1, got $rc; stdout: $(cat "$TMP/diverge.out")"
grep -q 'DIVERGED: the two spellings were treated DIFFERENTLY (1 vs 0)' "$TMP/diverge.out" \
  || fail "divergence headline missing; stdout: $(cat "$TMP/diverge.out")"
ok "divergent spellings exit 1 with the DIVERGED headline"

grep -qF 'The crate NAME is load-bearing again — `crate_is_authentic_std` is deciding' "$TMP/diverge.out" \
  || fail "the explanation lost the predicate name; stdout: $(cat "$TMP/diverge.out")"
ok "the explanation names \`crate_is_authentic_std\` literally"

if grep -q 'command not found' "$TMP/diverge.err"; then
  fail "the DIVERGED message executed a command substitution: $(cat "$TMP/diverge.err")"
fi
ok "the DIVERGED message executes nothing"

# --- accept control: identical treatment -------------------------------------
make_fake "$TMP/trustc-same" 1
set +e
bash "$WITNESS" "$TMP/trustc-same" >"$TMP/same.out" 2>"$TMP/same.err"
rc=$?
set -e
[ "$rc" -eq 0 ] || fail "identical treatment must exit 0, got $rc; stdout: $(cat "$TMP/same.out")"
grep -q 'forged-std witness: both spellings treated identically (1 each)' "$TMP/same.out" \
  || fail "accept line missing; stdout: $(cat "$TMP/same.out")"
ok "identical spellings exit 0"

printf 'forged_std_name_witness_test: %d checks passed\n' "$PASSED"
