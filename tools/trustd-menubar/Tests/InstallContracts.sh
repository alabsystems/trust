#!/usr/bin/env bash
# Behavioral contracts for atomic publication and cooperative install locking.
set -euo pipefail

if [[ "$#" -ne 2 ]]; then
    printf 'usage: %s TOOL_ROOT TEST_DIRECTORY\n' "$0" >&2
    exit 64
fi

TOOL_ROOT="$1"
TEST_DIRECTORY="$2"
PUBLISH_TOOL="$TEST_DIRECTORY/atomic-publish"
if [[ "$TOOL_ROOT" != /* || "$TEST_DIRECTORY" != /* || -e "$TEST_DIRECTORY" ]]; then
    printf '%s\n' 'test paths must be absolute and the test directory must be absent' >&2
    exit 64
fi
/bin/mkdir -m 0700 "$TEST_DIRECTORY"

/usr/bin/xcrun --sdk macosx clang \
    -std=c11 \
    -Wall \
    -Wextra \
    -Werror \
    -mmacosx-version-min=13.0 \
    "$TOOL_ROOT/AtomicPublish.c" \
    -o "$PUBLISH_TOOL"

# First publication is exclusive and leaves no nested source directory.
/bin/mkdir "$TEST_DIRECTORY/first"
/bin/mkdir "$TEST_DIRECTORY/first/first-marker"
result="$("$PUBLISH_TOOL" "$TEST_DIRECTORY/first" "$TEST_DIRECTORY/live")"
test "$result" = created
test ! -e "$TEST_DIRECTORY/first"
test -d "$TEST_DIRECTORY/live/first-marker"

# Replacement is one atomic swap. The exact prior directory remains at the
# staging path, and applying the same operation in reverse restores it.
/bin/mkdir "$TEST_DIRECTORY/second"
/bin/mkdir "$TEST_DIRECTORY/second/second-marker"
result="$("$PUBLISH_TOOL" "$TEST_DIRECTORY/second" "$TEST_DIRECTORY/live")"
test "$result" = swapped
test -d "$TEST_DIRECTORY/live/second-marker"
test -d "$TEST_DIRECTORY/second/first-marker"
result="$("$PUBLISH_TOOL" "$TEST_DIRECTORY/second" "$TEST_DIRECTORY/live")"
test "$result" = swapped
test -d "$TEST_DIRECTORY/live/first-marker"
test -d "$TEST_DIRECTORY/second/second-marker"

# A non-directory or symlink destination is never consumed by publication.
/bin/mkdir "$TEST_DIRECTORY/non-directory-source"
/usr/bin/touch "$TEST_DIRECTORY/non-directory-destination"
if "$PUBLISH_TOOL" \
        "$TEST_DIRECTORY/non-directory-source" \
        "$TEST_DIRECTORY/non-directory-destination" >/dev/null 2>&1; then
    printf '%s\n' 'publisher accepted a non-directory destination' >&2
    exit 1
fi
test -d "$TEST_DIRECTORY/non-directory-source"

/bin/mkdir "$TEST_DIRECTORY/symlink-source"
/bin/ln -s "$TEST_DIRECTORY/live" "$TEST_DIRECTORY/symlink-destination"
if "$PUBLISH_TOOL" \
        "$TEST_DIRECTORY/symlink-source" \
        "$TEST_DIRECTORY/symlink-destination" >/dev/null 2>&1; then
    printf '%s\n' 'publisher accepted a symlink destination' >&2
    exit 1
fi
test -d "$TEST_DIRECTORY/symlink-source"

# Parent traversal is descriptor-relative and rejects an intermediate symlink.
/bin/mkdir "$TEST_DIRECTORY/parent-source"
/bin/ln -s "$TEST_DIRECTORY" "$TEST_DIRECTORY/linked-parent"
if "$PUBLISH_TOOL" \
        "$TEST_DIRECTORY/linked-parent/parent-source" \
        "$TEST_DIRECTORY/parent-destination" >/dev/null 2>&1; then
    printf '%s\n' 'publisher followed an intermediate parent symlink' >&2
    exit 1
fi
test -d "$TEST_DIRECTORY/parent-source"

# A held fd lock rejects a concurrent nonblocking acquisition and becomes
# immediately available when the holder closes its descriptor.
lock_path="$TEST_DIRECTORY/install.lock"
exec 7>>"$lock_path"
/usr/bin/lockf -s -t 0 7
if /usr/bin/lockf -s -t 0 "$lock_path" /usr/bin/true; then
    printf '%s\n' 'concurrent lock acquisition unexpectedly succeeded' >&2
    exit 1
fi
exec 7>&-
/usr/bin/lockf -s -t 0 "$lock_path" /usr/bin/true

# The product verifier rejects a symlink before inspecting any bundle data.
/bin/ln -s "$TEST_DIRECTORY/live" "$TEST_DIRECTORY/Fake.app"
if /bin/bash "$TOOL_ROOT/verify-app.sh" "$TEST_DIRECTORY/Fake.app" >/dev/null 2>&1; then
    printf '%s\n' 'bundle verifier accepted a symlink bundle' >&2
    exit 1
fi

printf '%s\n' 'TrustdMenubar atomic install contracts passed'
