#!/usr/bin/env bash
# Regenerate the level-fold-corpus dumps: build the census extract crate
# (census-m6-cleankernel-2026-07-08/extract-foldmemo — REAL, byte-for-byte
# clean-kernel `level/mod.rs`/`expr/*`/`name.rs` sources; see ITS provenance)
# with the prebuilt stage2 trustc in dump-only survey mode, then publish the
# Level-family rows this corpus pins.
#
# TWO DEFECTS THIS SCRIPT USED TO HAVE, both fixed here:
#
#  1. THE DUMP GATE NEVER TURNED ON. It set `RUSTFLAGS=-Ztrust-verify=off`
#     globally and re-enabled per target with `cargo rustc --lib --
#     -Ztrust-verify=on`. Cargo places RUSTFLAGS AFTER the `--` target flags and
#     `-Ztrust-verify` is last-value-wins, so the global `off` won and every run
#     died with
#         error: -Ztrust-dump=mir:<dir> and -Ztrust-dump=native-bundle:<dir>
#                require batteries-on Trust verification
#     The enabling flag has to be appended after everything Cargo assembles,
#     which only a RUSTC_WRAPPER can do — see `regenerate-rustc-wrapper.sh`
#     (the same mechanism `../expr-fold-corpus/` already uses). Verification
#     semantics are unchanged: target on, dependencies off, run still
#     `-Ztrust-policy=advisory` dump-only.
#
#  2. IT COPIED BY A FILENAME TRUSTC DOES NOT EMIT. `trustc` writes every dump
#     content-addressed (`mir_dump_filename`: `trust-mir-<fingerprint>.json`,
#     since 2026-07-10 `2c9fdb1dd5`), so `cp "$SCRATCH/dump/level__Level__
#     is_zero.json"` could only ever fail. The publish step below joins on the
#     dump's own `def_path` — the identity, not a filename — exactly as
#     `../expr-fold-corpus/regenerate.sh` does, and writes each row back under
#     the filename this corpus already uses.
#
# STALENESS. Publication REPLACES the corpus's `*.json` set: the fresh
# generation is staged whole and only then swapped in, so a row this corpus no
# longer pins cannot survive into a directory `prove_dump_dir` enumerates (it
# reads every `*.json` in the directory, so a leftover file is silently counted).
#
# ─────────────────────────────────────────────────────────────────────────────
# DO NOT REGENERATE THIS CORPUS YET — MEASURED 2026-08-04, TWO BLOCKERS
#
# This script now RUNS end to end (the dump gate and the def_path join are both
# fixed, and REQUALIFY_OWNER_CRATE=extract_foldmemo maps all 14 owners). It was
# run, the result was measured, and it was REVERTED: the corpus goes 9/1 -> 1/9.
# That is not a script defect and not fixture staleness — it is two real consumer
# gaps that the structural-fold corpus does not exercise. Recorded here so the
# next attempt starts from evidence instead of rediscovering them.
#
#  1. FIXED 2026-08-05 (`f0390d5e55`) — RE-MEASURED, no longer a blocker. For
#     THIS corpus the canonical cut lands on
#     `Arc<Level>`, NOT on `Level`: `canonical_cut_key`'s first component is the
#     erased def path's segment count, and `alloc::sync::Arc` and
#     `extract_foldmemo::level::Level` BOTH have 2, so the tie falls to the
#     instantiated path and `alloc::…` sorts before `extract_…`. The regenerated
#     table is therefore keyed
#     `{alloc::sync::Arc<extract_foldmemo::level::Level>, alloc::sync::Arc<…Name>}`
#     and `Level`'s own payload field is a bare marker. `arc_pointee_ty` /
#     `box_pointee_ty` take a `&Ty` with NO access to `datatype_defs`, so they
#     cannot destructure it, fail closed, and every row declines
#     `OpaquePayloadTouched("borrow of opaque field 0 of
#     extract_foldmemo::level::Level::variant#2")`.
#     Fixed exactly as diagnosed: the walks now take the body's `datatype_defs`
#     and resolve every node through it, with the turbofish-tolerant pin
#     (`is_instantiation_of`) because a cut marker's name carries its
#     instantiation. The structural corpus hides this because `Tree` (1 segment)
#     wins its tie outright, so there the cut is the ENUM and `Arc` stays a full
#     `Ty::Adt`.
#     RE-MEASURED 2026-08-05 against a stage2 carrying both halves: regenerating
#     no longer produces a single `OpaquePayloadTouched`. Every remaining failure
#     is cause (2) below, alone.
#
#  2. CALLEE IDENTITY NOW CARRIES INSTANTIATION (not R0; a separate axis). The
#     trampoline callee reads
#     `extract_foldmemo::expr::stack_safe::<bool, {closure@src/level/mod.rs:1285:20: 1285:22}>::<__trust_args@1a628c3d6ceed4e8a7778e3df75ee2cc>`
#     while `all_bodies()` keys siblings by the plain def_path, so the sibling
#     lookup misses and the wrapper declines
#     `StackSafeDrift("no sibling dump body for trampoline callee …")`. With (1)
#     fixed this is the SOLE remaining cause: a 2026-08-05 regeneration goes
#     9/1 -> 1/9 and every one of the 9 failures is this.
#
#     It is not a mechanical rename, and the callee spelling is CORRECT — see
#     `disambiguate_generic_call_path` in trust-mir-extract's convert.rs: the
#     `__trust_args@<fingerprint>` turbofish deliberately distinguishes
#     MONOMORPHISATIONS, because erasing generic args is a documented false-proof
#     vector (the `Vec::<[u8; 1<<40]>::with_capacity` hunt-11 case). The mismatch
#     is on the other side: `VerifiableFunction` carries only the args-FREE
#     `def_path`, and `all_bodies()` keys the sibling map by it, so an
#     instantiated callee can never join. Note `all_bodies()` also `insert`s
#     last-wins, so two monomorphisations of one generic would silently collide
#     there today.
#     The principled fix is for the dump to record the SAME disambiguated
#     identity its callers reference (an `Option<String>` beside `def_path`,
#     serde-defaulted so existing fixtures are untouched), making the lookup an
#     exact match rather than a lossy strip of the turbofish. That is a producer
#     + model + consumer change and needs a stage2 rebuild to verify, so it is
#     sequenced separately rather than guessed at here.
#
# Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0 OR MIT
set -euo pipefail
export LC_ALL=C
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)"
REPO_ROOT="$(cd "$HERE/../../../.." && pwd -P)"
EXTRACT="$HERE/../census-m6-cleankernel-2026-07-08/extract-foldmemo"
TRUSTC="${TRUSTC:-$REPO_ROOT/build/host/stage2/bin/trustc}"   # prebuilt stage2, do NOT rebuild
WRAPPER="$HERE/regenerate-rustc-wrapper.sh"
SCRATCH="$(mktemp -d)"
STAGE="$SCRATCH/stage"
trap 'rm -rf "$SCRATCH"' EXIT

if ! command -v python3 >/dev/null 2>&1; then
  echo "regeneration requires python3 (it joins dumps on their own def_path)" >&2
  exit 1
fi
if [[ ! -x "$TRUSTC" ]]; then
  echo "missing executable trustc: $TRUSTC (build stage2 first or set TRUSTC)" >&2
  exit 1
fi
if [[ ! -x "$WRAPPER" ]]; then
  echo "missing executable rustc wrapper: $WRAPPER" >&2
  exit 1
fi
TRUSTC="$(cd "$(dirname "$TRUSTC")" && pwd -P)/$(basename "$TRUSTC")"

# Homebrew installations may need this to locate the stage2 LLVM libraries.
# Leave a caller-supplied value alone, and do not inject a macOS-only path on
# other hosts.
if [[ -d /opt/homebrew/lib && -z "${LIBRARY_PATH:-}" ]]; then
  export LIBRARY_PATH=/opt/homebrew/lib
fi

cp -R "$EXTRACT" "$SCRATCH/extract"
(cd "$SCRATCH/extract" && \
  CARGO_TARGET_DIR="$SCRATCH/target" \
  RUSTC="$TRUSTC" \
  RUSTC_WRAPPER="$WRAPPER" \
  RUSTFLAGS="-Ztrust-verify=off" \
  cargo rustc --offline --lib -- \
    \
    -Ztrust-dump=mir-only:"$SCRATCH/dump" \
    -Ztrust-policy=advisory)

# Join the fresh dumps onto the corpus's OWN inventory by exact `def_path`, and
# stage the result. A missing or ambiguous owner is fatal — a half-regenerated
# corpus is worse than a stale one, and a def_path that no longer exists is a
# real identity change that a regeneration must not paper over.
#
# ONE NARROW EXCEPTION, off by default: CRATE REQUALIFICATION. `safe_def_path_str`
# renders paths under `with_resolve_crate_name!` since `bd2d6ed1fc` (2026-07-13),
# whose stated requirement is that the string "must neither omit the local crate
# nor select a context-dependent visible re-export". So every owner in a corpus
# dumped before that date is missing exactly one leading segment: the crate name.
# With REQUALIFY_OWNER_CRATE=<crate> the join additionally tries the EXACT string
# "<crate>::<owner>" — a constructed candidate compared with `==`, never a
# `endswith`/`contains` search, so it cannot drift onto a same-named item in
# another module. It is fatal unless EVERY unmatched owner requalifies under the
# SAME crate, and every mapping it uses is printed.
mkdir "$STAGE"
REQUALIFY_OWNER_CRATE="${REQUALIFY_OWNER_CRATE:-}" \
python3 - "$SCRATCH/dump" "$HERE" "$STAGE" <<'PY'
import json, os, shutil, sys

dump_dir, corpus_dir, stage_dir = sys.argv[1], sys.argv[2], sys.argv[3]

fresh = {}
for entry in sorted(os.listdir(dump_dir)):
    if not entry.endswith(".json"):
        continue
    with open(os.path.join(dump_dir, entry), "rb") as handle:
        def_path = json.load(handle)["def_path"]
    fresh.setdefault(def_path, []).append(entry)

requalify = os.environ.get("REQUALIFY_OWNER_CRATE", "").strip()

problems = []
requalified = []
for name in sorted(os.listdir(corpus_dir)):
    if not name.endswith(".json"):
        continue
    with open(os.path.join(corpus_dir, name), "rb") as handle:
        owner = json.load(handle)["def_path"]
    matches = fresh.get(owner, [])
    if len(matches) != 1 and requalify:
        # EXACT equality against a constructed candidate, not a suffix search.
        candidate = f"{requalify}::{owner}"
        if len(fresh.get(candidate, [])) == 1:
            requalified.append((owner, candidate))
            matches = fresh[candidate]
    if len(matches) != 1:
        near = sorted(p for p in fresh if p.endswith("::" + owner) or p.endswith(owner))
        problems.append(
            f"  {name}: def_path {owner!r} matched {len(matches)} fresh dumps"
            + (f"; did it become one of {near}?" if near else "")
        )
        continue
    shutil.copyfile(os.path.join(dump_dir, matches[0]), os.path.join(stage_dir, name))

if requalified:
    print(
        f"REQUALIFIED {len(requalified)} owners under crate {requalify!r} "
        "(bd2d6ed1fc, `with_resolve_crate_name!`):",
        file=sys.stderr,
    )
    for old, new in requalified:
        print(f"  {old}  ->  {new}", file=sys.stderr)

if problems:
    sys.exit(
        "cannot regenerate: the corpus's pinned owners do not join onto this\n"
        "toolchain's dumps by exact def_path.\n"
        + "\n".join(problems)
        + "\nThis is an IDENTITY change, not a regeneration — update the corpus's\n"
          "owner set deliberately (and the tests that name it) rather than letting\n"
          "a fuzzy match pick a row."
    )
print(f"staged {len(os.listdir(stage_dir))} dumps", file=sys.stderr)
PY

staged_list="$SCRATCH/staged.txt"
current_list="$SCRATCH/current.txt"
(cd "$STAGE" && find . -maxdepth 1 -name '*.json' -exec basename {} \; | sort) > "$staged_list"
(cd "$HERE" && find . -maxdepth 1 -name '*.json' -exec basename {} \; | sort) > "$current_list"
if ! diff -u "$current_list" "$staged_list" >/dev/null; then
  echo "staged inventory differs from the checked-in corpus (should be impossible)" >&2
  diff -u "$current_list" "$staged_list" >&2 || true
  exit 1
fi

while IFS= read -r stale; do
  rm -f "$HERE/$stale"
done < "$current_list"
while IFS= read -r fresh; do
  mv "$STAGE/$fresh" "$HERE/$fresh"
done < "$staged_list"

echo "regenerated $(wc -l < "$staged_list" | tr -d ' ') level-fold-corpus dumps"
