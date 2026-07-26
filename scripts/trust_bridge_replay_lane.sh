#!/usr/bin/env bash
# trust_bridge_replay_lane.sh — the Lean<->Clean bridge REPLAY lane.
#
# Runs crates/trust-clean/tests/lean_clean_bridge.rs, which imports the vendored
# olean closure (185 modules) and kernel-checks that every bridged semIntBinOp /
# semIntUnOp / semCast arm still carries its agreement theorem, that no proven
# theorem has axiom residue, and that both deliberately-false forgery probes are
# REJECTED.
#
# WHY THIS IS ITS OWN LANE, AND NOT IN THE PRE-PUSH HOOK. It takes ~142s because
# it really does kernel-check the closure. A pre-push gate that slow is one
# everyone learns to skip with --no-verify, which is worse than not having it.
#
# WHY IT IS NOT COVERED BY fast.bridge-pin. That gate proves the vendored
# artifacts BELONG to the trust-ir pin. An artifact set can match its pin while a
# theorem inside it has stopped checking — on 2026-07-25 exactly that happened,
# and for the preceding days the bridge test could not even execute (it bailed at
# PinDrift in 2.88s), so nothing reported either problem. This lane is the one
# that would have.
#
# Requires no Lean toolchain: the artifacts are vendored, which is the point.
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."

echo "=== bridge.replay: kernel-checking the vendored Lean<->Clean closure ==="
RUSTC_BOOTSTRAP=1 CARGO_BUILD_JOBS="${CARGO_BUILD_JOBS:-4}" \
  cargo test --manifest-path crates/Cargo.toml -p trust-clean \
  --test lean_clean_bridge -- --test-threads=1
echo "bridge.replay: PASS"
