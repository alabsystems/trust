#!/usr/bin/env bash
# Deterministic concurrency and stale-marker regression for trust-rustc-guard.
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
TMP="$(mktemp -d "${TMPDIR:-/tmp}/trust-rustc-guard-test.XXXXXX")"
trap 'rm -rf "$TMP"' EXIT

FAKE_RUSTC="$TMP/fake-rustc"
cat >"$FAKE_RUSTC" <<'EOF'
#!/usr/bin/env bash
printf '%s\n' "$*" >>"$TRUST_GUARD_TEST_CALLS"
EOF
chmod +x "$FAKE_RUSTC"

export TMPDIR="$TMP/tmp with spaces"
export TRUST_GUARD_TEST_CALLS="$TMP/calls"
mkdir -p "$TMPDIR"

uid="$(id -u 2>/dev/null || printf 'unknown')"
uid="${uid//[![:alnum:]]/_}"
marker_root="$TMPDIR/trust-rustc-guard-${uid:-unknown}"
mkdir -p "$marker_root/cargo.999999999.stale"

pids=()
for n in 1 2 3 4 5 6 7 8; do
	"$ROOT/scripts/trust-rustc-guard.sh" "$FAKE_RUSTC" --crate-name "crate$n" \
		2>"$TMP/stderr.$n" &
	pids+=("$!")
done
for pid in "${pids[@]}"; do
	wait "$pid"
done

[ ! -e "$marker_root/cargo.999999999.stale" ] \
	|| { echo "stale guard marker was not pruned" >&2; exit 1; }
notice_count="$(grep -h -c 'You are building with raw `cargo`' "$TMP"/stderr.* \
	| awk '{ total += $1 } END { print total + 0 }')"
[ "$notice_count" = 1 ] \
	|| { echo "parallel wrappers emitted $notice_count notices, expected exactly one" >&2; exit 1; }
[ "$(wc -l <"$TRUST_GUARD_TEST_CALLS" | tr -d ' ')" = 8 ] \
	|| { echo "not every concurrent wrapper reached rustc" >&2; exit 1; }
[ "$(find "$marker_root" -mindepth 1 -maxdepth 1 -type d | wc -l | tr -d ' ')" = 1 ] \
	|| { echo "guard retained more than the one live parent marker" >&2; exit 1; }

# An existing notice marker must not weaken strict mode for later siblings.
if TRUST_STRICT_CARGO=1 "$ROOT/scripts/trust-rustc-guard.sh" \
	"$FAKE_RUSTC" --crate-name strict-sibling 2>"$TMP/strict.stderr"; then
	echo "strict guard passed through after the notice marker already existed" >&2
	exit 1
fi
grep -q 'TRUST_STRICT_CARGO=1' "$TMP/strict.stderr" \
	|| { echo "strict guard did not explain its failure" >&2; exit 1; }

# A symlink at the predictable per-user marker path must never be followed.
symlink_tmp="$TMP/symlink-tmp"
symlink_target="$TMP/symlink-target"
mkdir -p "$symlink_tmp" "$symlink_target"
if ln -s "$symlink_target" "$symlink_tmp/trust-rustc-guard-${uid:-unknown}" 2>/dev/null; then
	TMPDIR="$symlink_tmp" "$ROOT/scripts/trust-rustc-guard.sh" \
		"$FAKE_RUSTC" --crate-name symlink-root 2>"$TMP/symlink.stderr"
	grep -q 'You are building with raw `cargo`' "$TMP/symlink.stderr" \
		|| { echo "unsafe marker root suppressed the guard notice" >&2; exit 1; }
	[ -z "$(find "$symlink_target" -mindepth 1 -maxdepth 1 -print -quit)" ] \
		|| { echo "guard followed an unsafe marker-root symlink" >&2; exit 1; }
fi

echo "trust rustc guard tests: PASS"
