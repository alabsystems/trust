#!/usr/bin/env bash
# Trust (assumption ledger, Stage 1) acceptance gate.
#
# The default lane verifies fail-closed, including classifier-unsupported bodies.
# The explicit lame/survey lane records those bodies as machine-readable
# assumption rows while still surfacing a non-proof verdict. Every step below
# must pass; the script is
# the acceptance evidence (the repo has no CI).
set -euo pipefail
cd "$(git rev-parse --show-toplevel)"
TRUSTC=build/host/stage2/bin/trustc
TMP=$(mktemp -d)
trap 'rm -rf "$TMP"' EXIT

echo "== 1. Unit tests (includes the previously-rotted trust_verify tests module)"
RUSTC_BOOTSTRAP=1 cargo test --manifest-path crates/Cargo.toml -p trust-types -p trust-report
RUSTC_BOOTSTRAP=1 cargo test --manifest-path targo-trust/Cargo.toml
python3 x.py test --stage 2 compiler/rustc_mir_transform

echo "== 2. Compiletest suites"
python3 x.py test --stage 2 tests/ui/trust tests/run-make/trust-assumption-rows

echo "== 3. Lame lane: async fn -> assumption row, build continues, label fail-closed"
cat > "$TMP/tick.rs" <<'EOF'
pub async fn tick(x: u32) -> u32 { x }
fn main() {}
EOF
OUT=$("$TRUSTC" --edition 2021 -Ztrust-policy=advisory -Ztrust-verify-output=json "$TMP/tick.rs" -o "$TMP/tick" 2>&1)
ROW=$(grep -F '"kind":"assumption:coroutine"' <<<"$OUT" | head -1)
grep -qF '"outcome":"skipped"' <<<"$ROW"
! grep -qF '"outcome":"proved"' <<<"$ROW"
! grep -qiE 'full.verifier|fullverification::|trust-verify-full' <<<"$ROW"   # is_full_verifier_text ban
test -x "$TMP/tick"                                                          # binary was produced

echo "== 4. Human surface (lame output mode)"
"$TRUSTC" --edition 2021 -Ztrust-policy=advisory "$TMP/tick.rs" -o "$TMP/tick2" 2>&1 | grep -qF 'Trust: ASSUMPTION [coroutine]'

echo "== 5. Batteries-on default is fail-closed; explicit vanilla is silent"
! "$TRUSTC" --edition 2021 --crate-type=lib "$TMP/tick.rs" 2>/dev/null
"$TRUSTC" --edition 2021 -Ztrust-verify=off -Ztrust-verify-output=json "$TMP/tick.rs" -o "$TMP/tick3" 2>&1 \
  | { ! grep -q 'TRUST_JSON'; }

echo "== 6. Refutations still abort the default-lane build"
cat > "$TMP/bad.rs" <<'EOF'
pub fn div(x: i32, y: i32) -> i32 { x / y }
fn main() {}
EOF
! "$TRUSTC" "$TMP/bad.rs" -o "$TMP/bad" 2>/dev/null

echo "== 7. targo strict aborts; allow-l0-gaps conditionally passes with a repeatable ledger"
cargo new --lib "$TMP/asyncrate" >/dev/null
printf 'pub async fn tick(x: u32) -> u32 { x }\n' > "$TMP/asyncrate/src/lib.rs"
(
  cd "$TMP/asyncrate"
  ! targo trust check --format json                             # compiler is strict by default
  targo trust check --allow-l0-gaps --format json               # conditional success, never proof
  R=target/trust/report.json
  jq -e '.assumptions | length > 0' "$R"
  jq -e '[.assumptions[] | select(.scope=="function" and .tag=="coroutine")] | length >= 1' "$R"
  jq -e '[.assumptions[] | select(.scope=="crate" and .tag=="dependency-scope")] | length >= 3' "$R"  # core/alloc/std
  jq -e '[.assumptions[] | select(.tag=="coroutine")] | all(.source=="trust-classifier")' "$R"
  targo trust check --allow-l0-gaps --format json 2> "$TMP/second.log" # warm repeat: same verdict class,
  ! grep -q 'cached proved row is non-evidentiary' "$TMP/second.log"  # no cache-replay unknowns (TRUST_NO_COMPILER_CACHE)
)

echo "== 8. e2e"
bash tests/e2e_compiler_verify.sh

echo "GATE: assumption-ledger stage 1 GREEN"
