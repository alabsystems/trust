"""Which crates the crates lane tests as a crate of their own: the one rule.

scripts/check_crates_tests_scoped.py (the crates lane: the push profile's
scoped.crates-tests row, and scripts/land_gate.py's crates-tests leg) tests two
kinds of crate. One is the canonical workspace's developer default-members,
which Cargo's own inventory names (`targo metadata`; land_select reads the same
`default-members` from the root Cargo.toml). The other is the own-workspace
crate, run with its own `--manifest-path`. This module is the only definition of
the second kind. The lane reads it (own_workspace_roots) and so does the land
gate's selector (scripts/lib/land_select.py crates_members, crates_lane_sets),
which hands the lane the members a change reaches (`--also-members`) and caches
a PASS for each one.

The two must name the same crates. A directory the gate hands the lane that the
lane cannot attribute is run by nobody, yet its PASS was stored. That happened
before LAND-GATE-HOOKLESS-1 round 5 (D1): the gate counted every `[workspace]`
root under crates/ at any depth, and the lane counted only one level deep. Six
nested crates (four trust-disasm harnesses and two fixtures) then got cached
PASSes that nothing produced. The lane now also refuses (exit 2) an
`--also-members` directory it cannot attribute.

An own-workspace crate is `crates/<dir>`, exactly one level under crates/,
whose Cargo.toml has a line that is exactly `[workspace]` once stripped. A
`[workspace]` root nested deeper (crates/trust-disasm/harness/native-invariant,
crates/trust-clean/fixtures/.../extract-foldmemo) is not a crate this lane
tests. Its parent member's tests read it as data, and the parent's path
attribution covers it. The four disasm harnesses report no `#[test]` at all, so
the lane's zero-test rule could never pass them. The land gate names such a
crate NOT COVERED when a change touches or reaches it
(land_select.nested_workspace_crates). It never counts that crate as tested.

Author: Andrew Yates <andrewyates.name@gmail.com>
Copyright 2026 Andrew Yates | License: Apache-2.0 OR MIT
"""
from __future__ import annotations

from typing import Optional

WORKSPACE_LINE = "[workspace]"


def own_workspace_manifest(manifest: str) -> bool:
    """Whether the repo-relative path `manifest` is where an own-workspace
    crate's Cargo.toml sits: `crates/<dir>/Cargo.toml`, one level deep."""
    parts = manifest.split("/")
    return len(parts) == 3 and parts[0] == "crates" and bool(parts[1]) and parts[2] == "Cargo.toml"


def own_workspace_root(manifest: str, text: str) -> Optional[str]:
    """The `crates/<dir>` that the Cargo.toml at repo-relative `manifest`, whose
    content is `text`, makes an own-workspace crate of the crates lane, or None."""
    if not own_workspace_manifest(manifest):
        return None
    if not any(line.strip() == WORKSPACE_LINE for line in text.splitlines()):
        return None
    return manifest.rsplit("/", 1)[0]
