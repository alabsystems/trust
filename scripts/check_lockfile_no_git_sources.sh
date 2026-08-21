#!/usr/bin/env bash
# Fail closed unless every Cargo package source is either local/path-owned or a
# checksummed registry source. Cargo emits canonical one-line source rows; a
# source row outside a package, a duplicate, or any non-canonical spelling is
# rejected instead of being treated as harmless text.

set -euo pipefail

if [[ "$#" -ne 1 ]]; then
    echo "usage: check_lockfile_no_git_sources.sh LOCKFILE" >&2
    exit 2
fi

lock_file="$1"
if [[ ! -f "$lock_file" || -L "$lock_file" ]]; then
    echo "error: Cargo lockfile is not one exact regular file: $lock_file" >&2
    exit 1
fi

summary="$(awk '
    function close_package() {
        if (in_package && source_rows > 1) {
            malformed_sources += source_rows - 1
        }
        source_rows = 0
    }

    /^\[\[package\]\]$/ {
        close_package()
        in_package = 1
        package_count++
        next
    }

    /^\[/ {
        close_package()
        in_package = 0
        next
    }

    {
        candidate = $0
        sub(/^[[:space:]]*/, "", candidate)
        first = substr(candidate, 1, 1)
        equals = index(candidate, "=")
        if (in_package && equals > 0 && \
            (first == "\"" || first == sprintf("%c", 39))) {
            key = substr(candidate, 1, equals - 1)
            sub(/[[:space:]]*$/, "", key)
            if (substr(key, length(key), 1) == first) {
                malformed_sources++
                next
            }
        }
    }

    /^[[:space:]]*source[[:space:]]*=/ {
        if (!in_package) {
            malformed_sources++
            next
        }
        source_rows++
        if ($0 ~ /^source = "git\+[^\"]+"$/) {
            git_sources++
        } else if ($0 ~ /^source = "registry\+[^\"]+"$/) {
            registry_sources++
        } else if ($0 ~ /^source = "[^\"]+"$/) {
            unsupported_sources++
        } else {
            malformed_sources++
        }
        next
    }

    END {
        close_package()
        printf "%d\t%d\t%d\t%d\n", \
            package_count, git_sources, unsupported_sources, malformed_sources
    }
' "$lock_file")" || {
    echo "error: could not parse Cargo package sources: $lock_file" >&2
    exit 1
}

IFS=$'\t' read -r package_count git_source_count unsupported_source_count malformed_source_count <<< "$summary"
for count in \
    "$package_count" \
    "$git_source_count" \
    "$unsupported_source_count" \
    "$malformed_source_count"
do
    if [[ ! "$count" =~ ^[0-9]+$ ]]; then
        echo "error: Cargo package-source parser produced a non-canonical count" >&2
        exit 1
    fi
done

if [[ "$package_count" -eq 0 ]]; then
    echo "error: Cargo lockfile contains no canonical package rows: $lock_file" >&2
    exit 1
fi
if [[ "$malformed_source_count" -gt 0 ]]; then
    echo "error: Cargo.lock contains $malformed_source_count malformed/non-canonical package source row(s)" >&2
    exit 1
fi
if [[ "$unsupported_source_count" -gt 0 ]]; then
    echo "error: Cargo.lock contains $unsupported_source_count unsupported non-registry package source row(s)" >&2
    exit 1
fi
if [[ "$git_source_count" -gt 0 ]]; then
    echo "error: Cargo.lock contains $git_source_count Git-sourced package(s), but certified-monitor E2E admits only checksummed registry archives" >&2
    exit 1
fi
