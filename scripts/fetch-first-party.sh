#!/usr/bin/env bash
# Materialize the nine first-party/ sibling repos for a standalone (public)
# clone of this repository.
#
# The public snapshot cannot carry submodule gitlinks (the publication engine
# rejects mode-160000 entries, by design), so it ships first-party/PINS.txt
# instead: one line per sibling —
#
#     <name> <public-git-url> <40-hex-revision>
#
# written at export time by publish/transforms.sh (T5), where every revision
# is the sibling's newest ledger-attested public release, projected FORWARD
# from the private development pin (its source descends from, or is, that pin;
# a release behind the pin is refused, never shipped). This script clones each
# sibling at exactly that revision. (T5 writes it from the gitlinks of the commit
# the publication engine exported, named to it as CAPTURED_COMMIT.)
#
# In a DEVELOPMENT checkout there is no PINS.txt (first-party/ is populated by
# real submodules); use `git submodule update --init` there instead.
set -euo pipefail
cd "$(dirname "$0")/.."

PINS="first-party/PINS.txt"
if [ ! -f "$PINS" ]; then
  echo "fetch-first-party: $PINS not found." >&2
  echo "  Public snapshot: the file ships in the release — is this a full checkout?" >&2
  echo "  Development checkout: use \`git submodule update --init\` instead." >&2
  exit 1
fi

fail=0
while read -r name url rev; do
  case "$name" in ''|'#'*) continue ;; esac
  case "$rev" in
    *[!0-9a-f]*|'') echo "fetch-first-party: bad revision for $name: '$rev'" >&2; exit 1 ;;
  esac
  dest="first-party/$name"
  if [ -e "$dest/.git" ]; then
    have=$(git -C "$dest" rev-parse HEAD 2>/dev/null || echo none)
    if [ "$have" = "$rev" ]; then
      echo "fetch-first-party: $name already at ${rev:0:12}"
      continue
    fi
    echo "fetch-first-party: updating $name -> ${rev:0:12}"
    git -C "$dest" fetch --quiet origin "$rev" || git -C "$dest" fetch --quiet origin
    git -C "$dest" checkout --quiet --detach "$rev" || { echo "  checkout failed for $name" >&2; fail=1; }
  else
    echo "fetch-first-party: cloning $name at ${rev:0:12}"
    git clone --quiet "$url" "$dest" || { echo "  clone failed for $name" >&2; fail=1; continue; }
    git -C "$dest" checkout --quiet --detach "$rev" || { echo "  checkout failed for $name ($rev not reachable)" >&2; fail=1; }
  fi
done < "$PINS"

if [ "$fail" -ne 0 ]; then
  echo "fetch-first-party: FAILED — see messages above" >&2
  exit 1
fi
echo "fetch-first-party: all siblings materialized"
