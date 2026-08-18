#!/usr/bin/env bash
# Regenerate the structural-fold-corpus dumps from SOURCE.rs with the prebuilt
# stage2 trustc — the SAME recipe as census-m6-cleankernel-2026-07-08 (dump-only,
# survey mode, no verification dispatch).
#
# NAMING. `trustc` writes every dump under a CONTENT-ADDRESSED filename
# (`mir_dump_filename` in rustc_mir_transform/src/trust_verify.rs:
# `trust-mir-<fingerprint>.json`, since 2026-07-10 `2c9fdb1dd5`), while this
# corpus is checked in under FRIENDLY names — `<VerifiableFunction.name>.json`,
# which is what `tests/structural_fold_corpus.rs::load` opens. So a rename step
# is mandatory, and it is done here. Copying the hash-named files straight in
# (what this script used to do) left the corpus unreadable by its own test AND
# doubled it, because `prove_dump_dir` enumerates the directory: the previous
# generation's friendly-named files stayed put beside the new hash-named ones and
# every member was counted twice.
#
# STALENESS. Publication REPLACES the corpus's `*.json` set rather than merging
# into it: the regenerated set is staged whole, checked against the checked-in
# inventory, and only then swapped in. A file that the current SOURCE.rs no
# longer produces is therefore removed rather than left to be re-read forever.
# A DIFFERENT inventory (a member added to or removed from SOURCE.rs) is a
# deliberate act, not a regeneration, so it fails closed unless the caller says
# so with ALLOW_INVENTORY_CHANGE=1.
#
# Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0 OR MIT
set -euo pipefail
export LC_ALL=C
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)"
REPO_ROOT="$(cd "$HERE/../../../.." && pwd -P)"
TRUSTC="${TRUSTC:-$REPO_ROOT/build/host/stage2/bin/trustc}"   # prebuilt stage2, do NOT rebuild
SCRATCH="$(mktemp -d)"
STAGE="$SCRATCH/stage"
trap 'rm -rf "$SCRATCH"' EXIT

if ! command -v python3 >/dev/null 2>&1; then
  echo "regeneration requires python3 (it reads each dump's own \`name\` field)" >&2
  exit 1
fi

# Homebrew installations may need this to locate the stage2 LLVM libraries.
# Leave a caller-supplied value alone, and do not inject a macOS-only path on
# other hosts.
if [[ -d /opt/homebrew/lib && -z "${LIBRARY_PATH:-}" ]]; then
  export LIBRARY_PATH=/opt/homebrew/lib
fi

"$TRUSTC" --edition 2021 --crate-type lib \
    \
    -Ztrust-dump=mir-only:"$SCRATCH/dump" \
    -Ztrust-policy=advisory \
    -o "$SCRATCH/out.rlib" "$HERE/SOURCE.rs"

# Stage the regenerated generation under its FRIENDLY names. The mapping is a
# function of the dump's own contents (`name`), never of directory order, and a
# collision is fatal — two functions that would land on one filename must not
# silently overwrite each other.
mkdir "$STAGE"
python3 - "$SCRATCH/dump" "$STAGE" <<'PY'
import json, os, shutil, sys

dump_dir, stage_dir = sys.argv[1], sys.argv[2]
seen = {}
for entry in sorted(os.listdir(dump_dir)):
    if not entry.endswith(".json"):
        continue
    path = os.path.join(dump_dir, entry)
    with open(path, "rb") as handle:
        name = json.load(handle)["name"]
    if not name or "/" in name or name in (".", ".."):
        sys.exit(f"dump {entry} carries an unusable name {name!r}")
    if name in seen:
        sys.exit(f"two dumps claim the name {name!r}: {seen[name]} and {entry}")
    seen[name] = entry
    shutil.copyfile(path, os.path.join(stage_dir, f"{name}.json"))
print(f"staged {len(seen)} dumps", file=sys.stderr)
PY

# The regenerated inventory must be exactly the checked-in one. Anything else is
# a corpus membership change, which is a deliberate edit and not a regeneration.
staged_list="$SCRATCH/staged.txt"
current_list="$SCRATCH/current.txt"
(cd "$STAGE" && find . -maxdepth 1 -name '*.json' -exec basename {} \; | sort) > "$staged_list"
(cd "$HERE" && find . -maxdepth 1 -name '*.json' -exec basename {} \; | sort) > "$current_list"
if ! diff -u "$current_list" "$staged_list" > "$SCRATCH/inventory.diff"; then
  if [[ "${ALLOW_INVENTORY_CHANGE:-0}" != "1" ]]; then
    echo "regenerated inventory differs from the checked-in corpus:" >&2
    cat "$SCRATCH/inventory.diff" >&2
    echo "re-run with ALLOW_INVENTORY_CHANGE=1 if SOURCE.rs really gained/lost a member" >&2
    exit 1
  fi
  echo "ALLOW_INVENTORY_CHANGE=1: publishing a changed inventory" >&2
fi

# Publish: drop the previous generation's dumps FIRST (so a member that is no
# longer produced cannot survive into a directory `prove_dump_dir` enumerates),
# then move the staged generation in.
while IFS= read -r stale; do
  rm -f "$HERE/$stale"
done < "$current_list"
while IFS= read -r fresh; do
  mv "$STAGE/$fresh" "$HERE/$fresh"
done < "$staged_list"

echo "regenerated $(wc -l < "$staged_list" | tr -d ' ') dumps into $HERE"
