#!/usr/bin/env bash
# regenerate.sh: Re-dump `count_to.json` from the checked-in, byte-verified
# reconstruction `count_to.rs` (see PROVENANCE.md).
#
# SCOPE (honest): this script regenerates ONLY count_to.json. The other
# fixtures in this corpus were dumped from per-function scratch files
# (count_up.rs, NEWSHAPES.rs, ...) that were never checked in; their source
# text lives in the consolidated SOURCE.rs, which does NOT byte-reproduce
# their span metadata. count_to.rs is the one fixture with a verified
# byte-identical regeneration path.
#
# TWO DEFECTS THIS SCRIPT USED TO HAVE, both fixed here (2026-08-05):
#
#  1. IT LOOKED FOR A FILENAME TRUSTC DOES NOT EMIT. Since `2c9fdb1dd5`
#     (2026-07-10) every dump is content-addressed — `mir_dump_filename` writes
#     `trust-mir-<fingerprint>.json`, never `<fn>.json` — so `[[ -f
#     "$TMP/count_to.json" ]]` could only ever be false and the script died with
#         error: expected dump count_to.json was not produced
#     even though the dump had been produced perfectly. The publish step below
#     joins on the dump's own `def_path` — the IDENTITY, not a filename —
#     exactly as ../level-fold-corpus/ and ../expr-fold-corpus/ do.
#
#  2. IT RAN THE SOLVER. It passed `-Ztrust-dump=mir:` where PROVENANCE.md's
#     recipe (and the run that produced the checked-in bytes) says `mir-only:`.
#     `mir` publishes the extracted inputs AND dispatches proof; `mir-only`
#     publishes and stops. Both emit byte-identical dumps (measured), but `mir`
#     also runs a verification this script has no business gating on, and on the
#     current stage2 that verification FAILS on count_to:
#         2x [postcond] FAILED (trust-full-verifier);
#             counterexample: verified_counterexample = true
#     That failure is NOT why the dump was missing (defect 1 was) and it is NOT
#     being hidden here: it is a REAL, separately-reported regression in the
#     postcondition lane, not a fixture problem. It reproduces with no fixture in
#     sight on `fn f(n:i32)->i32 { let mut i=0; while i<n { i=i+1 } i }` with
#     `ensures(ret >= 0)` and no `requires` at all, and the 2026-07-16 stage2
#     under build/aarch64-apple-darwin/stage2-restored proves the same obligation
#     it now refutes. Dumping is the job here; solving is not.
#
# ONE-TIME MIGRATION, 2026-08-05. The dump this produces is no longer
# byte-identical to the bytes originally checked in at `98f116b930`. The five
# causes are enumerated and individually justified in PROVENANCE.md's drift
# ledger; each was checked to be a deliberate compiler change or a traceable
# edit to count_to.rs, none is a loss of information, and the corpus's tests
# were measured green on the new bytes (see the ledger). The regenerated dump
# was published as count_to.json, so the gate below is once again an EXACT
# byte comparison — anything that moves from here is a fresh, unexplained drift
# and must be diagnosed, not re-pinned.
#
# Requires: a built stage2 `trustc` (see the repo root CLAUDE.md) and python3.
#
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Copyright 2026 Andrew Yates | License: Apache-2.0 OR MIT
set -euo pipefail
export LC_ALL=C

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)"

# `--trustc <path>` beats TRUSTC beats the in-tree stage2 beats $PATH. There are
# four trustc paths on a typical dev box (build/{host,aarch64-apple-darwin}/
# stage2{,-restored}); name the one you mean rather than letting a stale restore
# win a `command -v` race.
TRUSTC="${TRUSTC:-}"
while [[ $# -gt 0 ]]; do
  case "$1" in
    --trustc) TRUSTC="${2:?--trustc needs a path}"; shift 2 ;;
    --trustc=*) TRUSTC="${1#--trustc=}"; shift ;;
    *) echo "usage: regenerate.sh [--trustc /path/to/trustc]" >&2; exit 2 ;;
  esac
done
if [[ -z "$TRUSTC" ]]; then
  for cand in \
    "$HERE/../../../../build/host/stage2/bin/trustc" \
    "$(command -v trustc || true)"; do
    if [[ -n "$cand" && -x "$cand" ]]; then TRUSTC="$cand"; break; fi
  done
fi
if [[ -z "$TRUSTC" || ! -x "$TRUSTC" ]]; then
  echo "error: trustc not found (pass --trustc /path/to/trustc)" >&2
  exit 1
fi
if ! command -v python3 >/dev/null 2>&1; then
  echo "error: regeneration requires python3 (it joins dumps on their own def_path)" >&2
  exit 1
fi

TMP="$(mktemp -d)"
trap 'rm -rf "$TMP"' EXIT

# The fixture's span.file is the RELATIVE path "count_to.rs", so compile with
# the file's directory as cwd and pass the bare filename. The crate name is
# therefore `count_to` too, which is what qualifies the def_path below.
cp "$HERE/count_to.rs" "$TMP/count_to.rs"
mkdir "$TMP/dump"
(cd "$TMP" && \
  LIBRARY_PATH="${LIBRARY_PATH:-/opt/homebrew/lib}" \
    "$TRUSTC" --crate-type lib -Z"trust-dump=mir-only:$TMP/dump" \
      -Ztrust-policy=advisory \
      count_to.rs -o "$TMP/count_to.rlib") || true

# Select the dump by IDENTITY. The corpus pins one owner; take the fresh dump
# whose own `def_path` is that owner, or — the one narrow, printed exception —
# the EXACT crate-qualified requalification of it.
#
# `safe_def_path_str` renders paths under `with_resolve_crate_name!` since
# `bd2d6ed1fc` (2026-07-13), whose stated requirement is that the string "must
# neither omit the local crate nor select a context-dependent visible re-export".
# A dump taken before that date is missing exactly one leading segment, the
# crate name, so the candidate `"$CRATE::<owner>"` is CONSTRUCTED and compared
# with `==` — never an `endswith`/`contains` search, which could drift onto a
# same-named item in another module. Ambiguity or a miss is fatal.
CRATE=count_to
CRATE="$CRATE" python3 - "$TMP/dump" "$HERE/count_to.json" "$TMP/fresh.json" <<'PY'
import json, os, shutil, sys

dump_dir, pinned_path, out_path = sys.argv[1], sys.argv[2], sys.argv[3]
crate = os.environ["CRATE"]

fresh = {}
for entry in sorted(os.listdir(dump_dir)):
    if not entry.endswith(".json"):
        continue
    full = os.path.join(dump_dir, entry)
    with open(full, "rb") as handle:
        fresh.setdefault(json.load(handle)["def_path"], []).append(full)

if not fresh:
    sys.exit(
        "no dumps were produced at all — trustc emitted nothing.\n"
        "Check that the stage2 you passed supports `-Ztrust-dump=mir-only:<dir>`\n"
        "(the flag was spelled `-Ztrust-dump-mir=<dir> -Ztrust-dump-only` before\n"
        "`d711cf76b1`) and that verification is not switched off for this unit."
    )

with open(pinned_path, "rb") as handle:
    owner = json.load(handle)["def_path"]

matches = fresh.get(owner, [])
if len(matches) != 1:
    candidate = f"{crate}::{owner}"          # exact, constructed — not a search
    if len(fresh.get(candidate, [])) == 1:
        print(
            f"REQUALIFIED owner under crate {crate!r} "
            f"(bd2d6ed1fc, `with_resolve_crate_name!`): {owner}  ->  {candidate}",
            file=sys.stderr,
        )
        matches = fresh[candidate]

if len(matches) != 1:
    sys.exit(
        f"cannot regenerate: pinned owner {owner!r} matched {len(matches)} of this\n"
        f"toolchain's dumps. Produced def_paths: {sorted(fresh)}\n"
        "This is an IDENTITY change, not a regeneration — update the corpus's\n"
        "owner set deliberately (and the tests that name it) rather than letting\n"
        "a fuzzy match pick a row."
    )

shutil.copyfile(matches[0], out_path)
PY

if cmp -s "$TMP/fresh.json" "$HERE/count_to.json"; then
  echo "count_to.json: re-dump is BYTE-IDENTICAL to the checked-in fixture"
else
  echo "warning: re-dump DIFFERS from the checked-in fixture (toolchain drift?)" >&2
  echo "         new dump left at $HERE/count_to.json.redump is NOT copied in;" >&2
  echo "         diagnose the difference before publishing it. PROVENANCE.md's" >&2
  echo "         drift ledger is the format: one enumerated, independently" >&2
  echo "         justified cause per difference, or it does not get published." >&2
  cp "$TMP/fresh.json" "$HERE/count_to.json.redump"
  exit 1
fi
