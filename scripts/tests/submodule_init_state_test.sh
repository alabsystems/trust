#!/usr/bin/env bash
# Copyright 2026 Andrew Yates. License: Apache-2.0 OR MIT.
# A populated, pinned checkout can still lack its parent's init records.
set -euo pipefail
TASK_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
SYNC_SCRIPT="${1:-$TASK_ROOT/scripts/submodule_sync.sh}"
TASK_TEMP="$(mktemp -d)"
trap 'rm -rf "$TASK_TEMP"' EXIT
GIT=(git -c protocol.file.allow=always -c advice.detachedHead=false)
export GIT_AUTHOR_NAME=init-test GIT_AUTHOR_EMAIL=init-test@example.invalid
export GIT_COMMITTER_NAME=init-test GIT_COMMITTER_EMAIL=init-test@example.invalid
for repo in donor middle top; do
  "${GIT[@]}" init -q -b main "$TASK_TEMP/$repo"
done
printf 'committed source\n' > "$TASK_TEMP/donor/source.txt"
"${GIT[@]}" -C "$TASK_TEMP/donor" add source.txt
"${GIT[@]}" -C "$TASK_TEMP/donor" commit -qm source
"${GIT[@]}" -C "$TASK_TEMP/middle" submodule add -q --name named-solver "$TASK_TEMP/donor" third_party/solver
"${GIT[@]}" -C "$TASK_TEMP/middle" commit -qam solver
"${GIT[@]}" -C "$TASK_TEMP/top" submodule add -q "$TASK_TEMP/middle" first-party/tool
"${GIT[@]}" -C "$TASK_TEMP/top" commit -qam tool
"${GIT[@]}" -C "$TASK_TEMP/top" submodule update -q --init --recursive
PARENT="$TASK_TEMP/top/first-party/tool"
CHILD="$PARENT/third_party/solver"
"${GIT[@]}" -C "$PARENT" config --local --remove-section submodule.named-solver
printf 'uncommitted tracked edit\n' >> "$CHILD/source.txt"
printf 'untracked owner file\n' > "$CHILD/owner.txt"
cp "$CHILD/source.txt" "$TASK_TEMP/source.before"
cp "$CHILD/owner.txt" "$TASK_TEMP/owner.before"
PIN="$("${GIT[@]}" -C "$CHILD" rev-parse HEAD)"
TREE="$("${GIT[@]}" -C "$PARENT" write-tree)"
STATUS="$("${GIT[@]}" -C "$PARENT" submodule status -- third_party/solver)"
[ "${STATUS:0:1}" = '-' ] || { echo 'fixture is not unregistered' >&2; exit 1; }
set +e
bash "$SYNC_SCRIPT" --root "$TASK_TEMP/top" --offline --json > "$TASK_TEMP/report.json"
REPORT_RC=$?
set -e
[ "$REPORT_RC" -eq 1 ] || { echo "expected restorable initialization refusal; got $REPORT_RC" >&2; cat "$TASK_TEMP/report.json"; exit 1; }
# Keep the fixture portable without assuming any Python version or jq.
[ "$(tr ',' '\n' < "$TASK_TEMP/report.json" | sed -n 's/.*"state":"UNREGISTERED".*/yes/p' | wc -l | tr -d ' ')" = 1 ] || { echo 'missing exact UNREGISTERED row' >&2; exit 1; }
bash "$SYNC_SCRIPT" --root "$TASK_TEMP/top" --offline --restore > "$TASK_TEMP/restore.log"
bash "$SYNC_SCRIPT" --root "$TASK_TEMP/top" --offline --quiet
[ "$("${GIT[@]}" -C "$CHILD" rev-parse HEAD)" = "$PIN" ]
[ "$("${GIT[@]}" -C "$PARENT" write-tree)" = "$TREE" ]
cmp "$CHILD/source.txt" "$TASK_TEMP/source.before"
cmp "$CHILD/owner.txt" "$TASK_TEMP/owner.before"
STATUS="$("${GIT[@]}" -C "$PARENT" submodule status -- third_party/solver)"
[ "${STATUS:0:1}" = ' ' ]
echo 'submodule_init_state_test: PASS (init repaired; HEAD, index and owner edits preserved)'
