#!/usr/bin/env bash
# fetch_corpus.sh — idempotent fetch + fail-closed verify of the pinned
# Test262 corpus (tests/js262/corpus-pin.json, trust.js262.corpus-pin.v1).
#
# Fetches the pinned revision into build/js262/test262-<sha> (git init;
# remote add; fetch --depth 1; checkout FETCH_HEAD), verifies HEAD against
# the pin, then verifies the sha256 of every pinned harness payload and the
# manifest_hash. Exits nonzero on ANY revision or checksum drift. Safe to
# re-run: an already-correct checkout skips the network entirely.
#
# Author: Andrew Yates
# Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0

set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
PIN="$REPO_ROOT/tests/js262/corpus-pin.json"

if [ ! -f "$PIN" ]; then
    echo "fetch_corpus: missing pin file $PIN" >&2
    exit 1
fi

SHA="$(python3 -c 'import json,sys; print(json.load(open(sys.argv[1]))["git_commit_hash"])' "$PIN")"
REPO_URL="$(python3 -c 'import json,sys; print(json.load(open(sys.argv[1]))["upstream"]["repo"])' "$PIN")"
DEST="$REPO_ROOT/build/js262/test262-$SHA"

current_head() {
    git -C "$DEST" rev-parse HEAD 2>/dev/null || true
}

if [ "$(current_head)" != "$SHA" ]; then
    mkdir -p "$DEST"
    if [ ! -d "$DEST/.git" ]; then
        git -C "$DEST" init -q
    fi
    if git -C "$DEST" remote get-url origin >/dev/null 2>&1; then
        git -C "$DEST" remote set-url origin "$REPO_URL"
    else
        git -C "$DEST" remote add origin "$REPO_URL"
    fi
    git -C "$DEST" fetch --depth 1 origin "$SHA"
    git -C "$DEST" checkout -q FETCH_HEAD
fi

HEAD_NOW="$(current_head)"
if [ "$HEAD_NOW" != "$SHA" ]; then
    echo "fetch_corpus: revision drift: HEAD=$HEAD_NOW want=$SHA" >&2
    exit 1
fi

# Verify every pinned payload sha256 + the manifest_hash (fail-closed).
python3 - "$PIN" "$DEST" <<'PYEOF'
import hashlib, json, sys

pin_path, dest = sys.argv[1], sys.argv[2]
with open(pin_path, encoding="utf-8") as f:
    pin = json.load(f)

bad = 0
for p in pin["payloads"]:
    rel, want = p["relative_path"], p["sha256"]
    try:
        with open(f"{dest}/{rel}", "rb") as f:
            got = hashlib.sha256(f.read()).hexdigest()
    except OSError as e:
        print(f"fetch_corpus: missing payload {rel}: {e}", file=sys.stderr)
        bad += 1
        continue
    if got != want:
        print(f"fetch_corpus: payload drift {rel}: got {got} want {want}",
              file=sys.stderr)
        bad += 1

concat = "".join(p["relative_path"] + "\n" + p["sha256"] + "\n"
                 for p in pin["payloads"])
mh = hashlib.sha256(concat.encode("utf-8")).hexdigest()
if mh != pin["manifest_hash"]:
    print(f"fetch_corpus: manifest_hash drift: got {mh} "
          f"want {pin['manifest_hash']}", file=sys.stderr)
    bad += 1

if bad:
    sys.exit(1)
print(f"fetch_corpus: {len(pin['payloads'])} payloads verified")
PYEOF

echo "fetch_corpus: OK — $DEST at $SHA"
