#!/usr/bin/env bash
# Self-test for `scripts/seal_driver.sh sysrootcheck`: the gate that turns an
# equal-METADATA_VERSION encoding skew into a named refusal instead of an ICE.
#
# Why it exists. clean filed reports/ice/trustc-ice-2026-08-21T05_21_11-38057.txt:
#
#   thread 'rustc' panicked at compiler/rustc_metadata/src/rmeta/decoder.rs:515:18:
#   range end index 20 out of range for slice of length 8
#   ... <Statement as Decodable<MetadataDecodeContext>>::decode -> decode_span
#   #0 [optimized_mir] optimizing MIR for `core::str::<impl str>::len`
#
# That is a driver decoding libcore MIR written in a DIFFERENT statement
# encoding under the SAME metadata header: f24fdb2fdb added
# `Statement::trust_modular_arith` without bumping METADATA_VERSION, so the
# stream desynchronised and a garbage byte was read as an Indirect span tag of
# length 20. 47236131c9 owed-bumped 12 -> 13 and added sysrootcheck's fact 4
# (decode one real core MIR body) to catch the NEXT unversioned change.
#
# Fact 4 then silently stopped working for the drivers people run: the probes
# hard-coded `-Zno-trust-verify`, a spelling only `#[cfg(bootstrap)]` stage1
# drivers still accept, so every SHIPPING driver read `driver=unknown` and was
# REFUSED for a flag error. These cases pin the repair and the gate's verdicts
# with fake drivers, so they run anywhere in about a second:
#
#   1. shipping driver (new spelling only), matching sysroot  -> OK, v13=v13
#   2. seed/stage1-era driver (old spelling only)             -> OK
#   3. shipping driver whose core MIR decode ICEs as in the dump
#                                            -> refuse 96, and QUOTE the panic
#   4. a driver that accepts neither spelling                 -> refuse, never OK
#
# Opt-in live leg: SYSROOTCHECK_LIVE_DRIVER=/path/to/trustc runs the real gate
# on that driver against its own `--print sysroot`, which must say OK.
#
# Author: Andrew Yates. Copyright 2026 Andrew Yates. License: Apache-2.0 OR MIT.
set -uo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
GATE="$REPO_ROOT/scripts/seal_driver.sh"
[ -f "$GATE" ] || { echo "seal_driver sysrootcheck tests: no $GATE" >&2; exit 2; }

TMP="$(mktemp -d)" || exit 2
trap 'rm -rf "$TMP"' EXIT
HOST_T="aarch64-apple-darwin"

FAILED=0
pass() { echo "  ok   $1"; }
fail() { echo "  FAIL $1"; [ -n "${2:-}" ] && printf '%s\n' "$2" | sed 's/^/         /'; FAILED=1; }

# A sysroot that answers fact 1: one libcore .rmeta whose header says v13.
SYSROOT="$TMP/sysroot"
mkdir -p "$SYSROOT/lib/rustlib/$HOST_T/lib"
printf 'rust\000\000\000\015' > "$SYSROOT/lib/rustlib/$HOST_T/lib/libcore-0000.rmeta"

# fake_driver <path> <accepts: new|old|none> <decode: ok|skew>
fake_driver() {
  local path="$1" accepts="$2" decode="$3"
  cat > "$path" <<EOF
#!/usr/bin/env bash
accepts="$accepts"; decode="$decode"; sysroot="$SYSROOT"
EOF
  cat >> "$path" <<'EOF'
out=""; src=""; print=""
while [ $# -gt 0 ]; do
  case "$1" in
    -Ztrust-verify=off)
      [ "$accepts" = new ] || { echo 'error: unknown unstable option: `trust-verify`' >&2; exit 1; } ;;
    -Zno-trust-verify)
      [ "$accepts" = old ] || { echo 'error: unknown unstable option: `no-trust-verify`' >&2; exit 1; } ;;
    --print) print="$2"; shift ;;
    --sysroot) sysroot="$2"; shift ;;
    -o) out="$2"; shift ;;
    *.rs) src="$1" ;;
  esac
  shift
done
if [ "$print" = sysroot ]; then echo "$sysroot"; exit 0; fi
case "$(basename "$src")" in
  mv.rs)    printf 'rust\000\000\000\015fake-rlib' > "$out" ;;
  hello.rs) : > "$out" ;;
  mirprobe.rs)
    if [ "$decode" = skew ]; then
      cat >&2 <<'ICE'
thread 'rustc' panicked at compiler/rustc_metadata/src/rmeta/decoder.rs:515:18:
range end index 20 out of range for slice of length 8
error: the compiler unexpectedly panicked. This is a bug
ICE
      exit 101
    fi
    printf 'obj' > "$out" ;;
  *) echo "fake driver: unexpected source '$src'" >&2; exit 1 ;;
esac
exit 0
EOF
  chmod +x "$path"
}

run_gate() { # <driver> -> sets OUT, RC
  OUT=$(TRUST_REPO_ROOT="$TMP/repo" TRUST_HOST="$HOST_T" bash "$GATE" sysrootcheck "$1" \
          --sysroot "$SYSROOT" --dyld "$TMP" 2>&1); RC=$?
}
want() { # <label> <needle>
  case "$OUT" in *"$2"*) pass "$1" ;; *) fail "$1 (missing: $2)" "$OUT" ;; esac
}

echo "== 1. a SHIPPING driver (only -Ztrust-verify=off) is read, not refused =="
fake_driver "$TMP/shipping" new ok
run_gate "$TMP/shipping"
[ "$RC" = 0 ] && pass "rc 0" || fail "rc 0 (got $RC)" "$OUT"
want "fact 2 reads the driver's version" "driver=13  sysroot=13"
want "facts 3 and 4 pass" "OK — std resolves AND a core MIR body decodes"

echo "== 2. a stage1/seed-era driver (only -Zno-trust-verify) still works =="
fake_driver "$TMP/seed" old ok
run_gate "$TMP/seed"
[ "$RC" = 0 ] && pass "rc 0" || fail "rc 0 (got $RC)" "$OUT"
want "fact 2 reads the driver's version" "driver=13  sysroot=13"

echo "== 3. the 2026-08-21 decode_span skew is REFUSED and its cause QUOTED =="
fake_driver "$TMP/skew" new skew
run_gate "$TMP/skew"
[ "$RC" = 96 ] && pass "rc 96" || fail "rc 96 (got $RC)" "$OUT"
want "names fact 4" "CANNOT DECODE THIS SYSROOT'S MIR"
want "quotes the panic site" "decoder.rs:515:18"
want "quotes the panic message" "range end index 20 out of range for slice of length 8"
case "$OUT" in *"OK — std resolves"*) fail "never says OK on a skew" "$OUT" ;; *) pass "never says OK on a skew" ;; esac

echo "== 4. a driver that accepts NEITHER spelling fails closed =="
fake_driver "$TMP/neither" none ok
run_gate "$TMP/neither"
[ "$RC" != 0 ] && pass "refuses (rc $RC)" || fail "refuses" "$OUT"
case "$OUT" in *"OK — std resolves"*) fail "never says OK" "$OUT" ;; *) pass "never says OK" ;; esac

if [ -n "${SYSROOTCHECK_LIVE_DRIVER:-}" ]; then
  echo "== live: $SYSROOTCHECK_LIVE_DRIVER against its own sysroot =="
  live_sysroot=$("$SYSROOTCHECK_LIVE_DRIVER" --print sysroot) || { fail "live driver answers --print sysroot"; live_sysroot=""; }
  if [ -n "$live_sysroot" ]; then
    OUT=$(bash "$GATE" sysrootcheck "$SYSROOTCHECK_LIVE_DRIVER" --sysroot "$live_sysroot" \
            --dyld "$live_sysroot/lib" 2>&1); RC=$?
    [ "$RC" = 0 ] && pass "live rc 0" || fail "live rc 0 (got $RC)" "$OUT"
    want "live: a real core MIR body decodes" "OK — std resolves AND a core MIR body decodes"
  fi
fi

[ "$FAILED" = 0 ] && echo "seal_driver sysrootcheck tests: OK" || echo "seal_driver sysrootcheck tests: FAILED"
exit "$FAILED"
