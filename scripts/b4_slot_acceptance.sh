#!/usr/bin/env bash
# b4_slot_acceptance.sh — the B4 memory-model ACCEPTANCE GATE, in the repo.
#
# docs/TRUST_IR_V2.md §B4 names this as B4's gate:
#
#     "the `tail`-vs-`letted` probe pair must yield distinguishable Modules
#      (named acceptance test)"
#
# The pair differs by exactly one thing — a `let` binding, which is a distinct
# STORAGE LOCATION in the source and in built MIR:
#
#     tail    fn probe(s: S) -> i32 { s.a }
#     letted  fn probe(s: S) -> i32 { let t = s; t.a }
#
# Today the producer has no slot table, so the binding evaporates and both
# lower to the same two instructions. B4 introduces `SlotId` + typed places,
# after which the two Modules must differ in their INSTRUCTIONS. This script is
# how that claim gets checked instead of asserted.
#
# WHY THE COMPARISON STRIPS DEBUG METADATA — do not remove this. A raw `cmp` of
# the two dumps reports "distinguishable" TODAY, on the strength of the source
# FILENAME, the `#loc` spans, and the `#scope` annotations alone. That is a gate
# that can never fail: it would go green on B4 doing nothing at all. The same
# trap as a ratchet that emits no rows. So the pair is compiled from files with
# the SAME basename in different directories, and every `; #loc:` / `; #scope:`
# suffix and `file N` line is stripped before the diff. What remains is the
# semantic content, which is the only thing B4 is claiming to change.
#
# Usage:  scripts/b4_slot_acceptance.sh [path/to/rustc]
# Exit:   0 = GREEN (Modules semantically distinguishable — B4's gate is met)
#         1 = RED   (semantically identical — B4 not landed / regressed)
#
# Author: Andrew Yates | Copyright 2026 | License: Apache-2.0 OR MIT
set -euo pipefail

RUSTC="${1:-build/aarch64-apple-darwin/stage1/bin/rustc}"
if [ ! -x "$RUSTC" ]; then
    echo "b4_slot_acceptance: no rustc at $RUSTC" >&2
    exit 2
fi

WORK="$(mktemp -d)"
trap 'rm -rf "$WORK"' EXIT

mkdir -p "$WORK/tail" "$WORK/letted"
cat > "$WORK/tail/probe.rs" <<'RS'
pub struct S { pub a: i32 }
pub fn probe(s: S) -> i32 { s.a }
RS
cat > "$WORK/letted/probe.rs" <<'RS'
pub struct S { pub a: i32 }
pub fn probe(s: S) -> i32 { let t = s; t.a }
RS

for variant in tail letted; do
    mkdir -p "$WORK/$variant.d"
    "$RUSTC" --edition 2021 --crate-name probe \
        -Ztrust-ir-lower -Ztrust-verify=off \
        -Ztrust-dump=ir:"$WORK/$variant.d" \
        --crate-type lib --emit=metadata -o "$WORK/$variant.rmeta" \
        "$WORK/$variant/probe.rs" >/dev/null
    # Strip every debug-metadata carrier: the `file N "..."` table (absolute
    # paths differ by construction) and any `; #loc:` / `; #scope:` suffix.
    sed -E 's/[[:space:]]*;[[:space:]]*#(loc|scope):.*$//; /^[[:space:]]*$/d; /^file [0-9]/d' \
        "$WORK/$variant.d/probe.trust-ir.txt" > "$WORK/$variant.semantic.txt"
done

if diff -q "$WORK/tail.semantic.txt" "$WORK/letted.semantic.txt" >/dev/null; then
    echo "B4 ACCEPTANCE: RED — \`tail\` and \`letted\` lower to SEMANTICALLY IDENTICAL Modules."
    echo "The \`let\` binding leaves no trace; there is no slot table yet. This is the"
    echo "expected pre-B4 state (docs/TRUST_IR_V2.md §B4). Shared body:"
    sed -n '/^fn @probe/,/^}/p' "$WORK/tail.semantic.txt" | sed 's/^/    /'
    exit 1
fi

echo "B4 ACCEPTANCE: GREEN — the Modules differ semantically:"
diff "$WORK/tail.semantic.txt" "$WORK/letted.semantic.txt" | sed 's/^/    /' || true
exit 0
