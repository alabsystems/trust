#!/usr/bin/env bash
# Run the real-Targo certified-monitor Cargo-test payload.
#
# These tests are intentionally ignored by ordinary crate test runs because
# they require a current repo-local stage2 Trust toolchain.  Libtest exits zero
# when an exact filter selects no tests, so this gate authenticates the compiled
# inventory and the one-test result for every invocation.  Unsupported hosts
# fail: they are not a successful platform skip.

set -euo pipefail
umask 077

# This payload is intentionally strict about its process environment. Source
# authority still belongs to the Rust-native parent, which validates the real
# checkout before and after this process. Direct shell output and retained logs
# are payload-only and must never be represented as release evidence.
export PATH=/usr/bin:/bin
export LC_ALL=C
export LANG=C
export TZ=UTC
export GIT_CONFIG_GLOBAL=/dev/null
export GIT_CONFIG_NOSYSTEM=1

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)"
TRUST_ROOT="$(cd "$SCRIPT_DIR/.." && pwd -P)"
MANIFEST="$TRUST_ROOT/targo-trust/Cargo.toml"
LOCK_FILE="$TRUST_ROOT/targo-trust/Cargo.lock"
REQUESTED_SYSROOT="${TRUST_STAGE2_SYSROOT:-}"
RUN_ID="${TRUST_CERTIFIED_MONITOR_E2E_RUN_ID:-stage2-certified-monitor-e2e-$(date -u '+%Y%m%dT%H%M%SZ')-$$}"
LOG_DIR="${TRUST_CERTIFIED_MONITOR_E2E_LOG_DIR:-$TRUST_ROOT/reports/build/$RUN_ID}"
TARGET_DIR="${TRUST_CERTIFIED_MONITOR_E2E_TARGET_DIR:-$TRUST_ROOT/build/stage2-certified-monitor-e2e-target/$RUN_ID}"
SOURCE_CARGO_HOME="${TRUST_CERTIFIED_MONITOR_E2E_CACHE_HOME:-${CARGO_HOME:-${HOME:+$HOME/.cargo}}}"
EXPECTED_HEAD="${TRUST_CERTIFIED_MONITOR_EXPECTED_HEAD:-}"

TESTS=(
    "tests::real_targo_test_instruments_library_used_by_integration_test"
    "tests::real_targo_test_executes_authorized_satisfying_integration_test"
    "tests::real_targo_test_rejects_unharnessed_test_target_before_execution"
)
RELEASE_TEST_PREFIX="tests::real_targo_test_"

usage() {
    cat <<'USAGE'
stage2_certified_monitor_e2e.sh -- certified-monitor test payload

USAGE:
  bash scripts/stage2_certified_monitor_e2e.sh [options]

OPTIONS:
  --stage2-sysroot PATH  Exact repo-local build/<host>/stage2 sysroot to require.
  --log-dir PATH         Fresh, non-existing payload-log directory.
  --target-dir PATH      Fresh, non-existing outer target directory.
  -h, --help             Show this help.

SUPPORTED HOSTS:
  Linux x86_64/aarch64 and macOS x86_64/arm64. Linux uses a sealed
  memfd/execveat image; macOS authenticates the code-signed live process while
  it is suspended and resumes it only after the exact CDHash matches.

The selected stage2 trustc, Targo, targo-trust, and trustd binaries must each
identify the current repository HEAD, and the committed checkout (including submodules
and untracked inputs) must remain clean. Cargo runs with private
HOME/TMPDIR/CARGO_HOME directories seeded only
from TRUST_CERTIFIED_MONITOR_E2E_CACHE_HOME's checksummed archives and a plain,
symlink-free registry-index snapshot. Git-sourced lock entries fail closed until
an authenticated Git-cache snapshot boundary exists. There is no allow-skip
mode: an absent or stale toolchain, reusable output directory, missing ignored
test, zero-test selection, or unsupported platform is a payload failure.

AUTHORITY:
  This shell can only produce payload-only/source-authority-unverified results.
  An authoritative PASS is printed by the Rust-native
  `targo trust release validate certified-monitors` parent only after its
  controlled-Git postcheck succeeds.
USAGE
}

while [[ "$#" -gt 0 ]]; do
    case "$1" in
        --stage2-sysroot)
            [[ "$#" -ge 2 ]] || { echo "error: --stage2-sysroot requires a value" >&2; exit 2; }
            REQUESTED_SYSROOT="$2"
            shift 2
            ;;
        --log-dir)
            [[ "$#" -ge 2 ]] || { echo "error: --log-dir requires a value" >&2; exit 2; }
            LOG_DIR="$2"
            shift 2
            ;;
        --target-dir)
            [[ "$#" -ge 2 ]] || { echo "error: --target-dir requires a value" >&2; exit 2; }
            TARGET_DIR="$2"
            shift 2
            ;;
        -h|--help)
            usage
            exit 0
            ;;
        *)
            echo "error: unknown argument: $1" >&2
            usage >&2
            exit 2
            ;;
    esac
done

# This shell is a bounded payload of the Rust-native release command, not its
# own source-authority root.  The native caller supplies HEAD only after a
# fixed-system-Git, fresh-index/object-database, recursive content check and
# repeats that check after this process exits.  Direct invocation may show
# `--help`, but no environment value is a capability and this shell never
# labels its own terminal result as an authoritative release PASS.
if [[ ! "$EXPECTED_HEAD" =~ ^[0-9a-f]{40}$ ]]; then
    echo "error: certified-monitor release E2E requires the Rust-native controlled-Git runner" >&2
    echo "  use: targo trust release validate certified-monitors" >&2
    exit 2
fi

if [[ ! "$RUN_ID" =~ ^[A-Za-z0-9][A-Za-z0-9._-]{0,127}$ || "$RUN_ID" == "." || "$RUN_ID" == ".." ]]; then
    echo "error: certified-monitor run id must be one bounded filesystem-safe token" >&2
    exit 2
fi

HOST_OS="$(uname -s)"
HOST_ARCH="$(uname -m)"
case "$HOST_OS:$HOST_ARCH" in
    Linux:x86_64|Linux:aarch64|Darwin:x86_64|Darwin:arm64)
        ;;
    *)
        echo "error: certified-monitor release E2E requires Linux x86_64/aarch64 or macOS x86_64/arm64; $HOST_OS $HOST_ARCH is unsupported and is not a successful skip" >&2
        exit 1
        ;;
esac

stable_file_identity() {
    local path="$1"
    if [[ "$HOST_OS" == "Darwin" ]]; then
        stat -f '%d:%i:%z:%m:%c:%p' -- "$path"
    else
        stat --format='%d:%i:%s:%Y:%Z:%f' -- "$path"
    fi
}

owner_mode() {
    local path="$1"
    if [[ "$HOST_OS" == "Darwin" ]]; then
        stat -f '%u:%Lp' -- "$path"
    else
        stat --format='%u:%a' -- "$path"
    fi
}

owner_group_mode() {
    local path="$1"
    if [[ "$HOST_OS" == "Darwin" ]]; then
        stat -f '%u:%g:%Lp' -- "$path"
    else
        stat --format='%u:%g:%a' -- "$path"
    fi
}

copy_registry_archive() {
    local source="$1"
    local destination="$2"
    if [[ "$HOST_OS" == "Linux" ]]; then
        cp --reflink=auto -- "$source" "$destination"
    else
        cp -- "$source" "$destination"
    fi
}

canonical_directory() {
    local path="$1"
    [[ -d "$path" ]] || return 1
    (cd "$path" && pwd -P)
}

trusted_git() {
    command git \
        -c core.fsmonitor=false \
        -c core.untrackedCache=false \
        "$@"
}

checkout_status() {
    trusted_git -C "$TRUST_ROOT" status \
        --porcelain=v1 \
        --untracked-files=all \
        --ignore-submodules=none
}

require_clean_checkout() {
    local phase="$1"
    local status
    if ! status="$(checkout_status)"; then
        echo "error: could not establish repository cleanliness $phase certified-monitor E2E" >&2
        return 1
    fi
    if [[ -n "$status" ]]; then
        echo "error: certified-monitor release E2E requires a clean committed checkout $phase execution" >&2
        printf '%s\n' "$status" >&2
        return 1
    fi
}

trust_repo_commit_from_version() {
    local version_output="$1"
    local label="$2"
    local matches
    local count

    matches="$(printf '%s\n' "$version_output" | sed -n 's/^trust-repo-commit-hash: //p')"
    count="$(printf '%s\n' "$matches" | wc -l | tr -d ' ')"
    if [[ "$count" -ne 1 || ! "$matches" =~ ^[0-9a-f]{40}$ ]]; then
        echo "error: $label did not report exactly one bootstrap-bound full Trust repo commit" >&2
        return 1
    fi
    printf '%s\n' "$matches"
}

create_fresh_private_directory() {
    local path="$1"
    local label="$2"
    local parent
    local canonical
    local metadata

    if [[ -z "$path" || "$path" == "/" || "$path" == */ || "${path##*/}" == "." || "${path##*/}" == ".." ]]; then
        echo "error: $label path is not one safe directory leaf: $path" >&2
        return 1
    fi
    if [[ -e "$path" || -L "$path" ]]; then
        echo "error: $label must not preexist or be reusable: $path" >&2
        return 1
    fi
    parent="$(dirname -- "$path")" || {
        echo "error: could not resolve parent for $label: $path" >&2
        return 1
    }
    mkdir -p -- "$parent" || {
        echo "error: could not create parent for $label: $parent" >&2
        return 1
    }
    mkdir -m 700 -- "$path" || {
        echo "error: could not atomically create fresh $label: $path" >&2
        return 1
    }
    if [[ ! -d "$path" || -L "$path" ]]; then
        echo "error: $label is not an exact private directory: $path" >&2
        return 1
    fi
    canonical="$(canonical_directory "$path")" || {
        echo "error: could not canonicalize fresh $label: $path" >&2
        return 1
    }
    metadata="$(owner_mode "$canonical")" || {
        echo "error: could not inspect fresh $label: $canonical" >&2
        return 1
    }
    if [[ "$metadata" != "$EUID:700" ]]; then
        echo "error: $label is not owned by this process with mode 0700: $canonical ($metadata)" >&2
        return 1
    fi
    printf '%s\n' "$canonical"
}

PRIVATE_TARGET_CREATED=""
cleanup_private_target() {
    local target="${PRIVATE_TARGET_CREATED:-}"
    [[ -n "$target" ]] || return 0
    if [[ ! -d "$target" || -L "$target" ]]; then
        echo "error: refusing to clean replaced certified-monitor target: $target" >&2
        return 1
    fi
    rm -rf -- "$target" || {
        echo "error: could not remove private certified-monitor target: $target" >&2
        return 1
    }
    if [[ -e "$target" || -L "$target" ]]; then
        echo "error: private certified-monitor target survived cleanup: $target" >&2
        return 1
    fi
    PRIVATE_TARGET_CREATED=""
}
trap 'cleanup_private_target || true' EXIT

hash_stable_regular_file() {
    local path="$1"
    local label="$2"
    local before
    local after
    local digest_line
    local digest

    if [[ ! -f "$path" || -L "$path" ]]; then
        echo "error: $label is not an exact regular file: $path" >&2
        return 1
    fi
    before="$(stable_file_identity "$path")" || {
        echo "error: could not inspect $label before hashing: $path" >&2
        return 1
    }
    digest_line="$(sha256sum -- "$path")" || {
        echo "error: could not hash $label: $path" >&2
        return 1
    }
    digest="${digest_line%% *}"
    if [[ ! "$digest" =~ ^[0-9a-f]{64}$ ]]; then
        echo "error: $label hash was not one canonical SHA-256 digest" >&2
        return 1
    fi
    after="$(stable_file_identity "$path")" || {
        echo "error: could not inspect $label after hashing: $path" >&2
        return 1
    }
    if [[ "$before" != "$after" ]]; then
        echo "error: $label changed while it was being hashed: $path" >&2
        return 1
    fi
    printf '%s\n' "$digest"
}

hash_stable_executable() {
    local path="$1"
    local label="$2"
    if [[ ! -x "$path" ]]; then
        echo "error: $label is not executable: $path" >&2
        return 1
    fi
    hash_stable_regular_file "$path" "$label"
}

# Bind every path, owner/group, and mode in the stage2 sysroot, not only the two
# launchers.  trustc consumes sysroot libraries and helper binaries while it
# compiles the test harness, so a commit string reported by an otherwise exact
# launcher is not enough authority.  Bootstrap's two rust-src links are the
# only admitted links and must resolve back to this exact clean checkout.
hash_stable_stage2_tree() {
    local root="$1"
    local digest_line
    local digest
    local entry
    local local_path
    local link_target
    local link_text
    local link_mode
    local file_mode
    local file_digest
    local directory_mode
    local root_mode

    [[ -d "$root" && ! -L "$root" ]] || {
        echo "error: stage2 sysroot is not one exact directory: $root" >&2
        return 1
    }
    digest_line="$(
        (
            cd "$root" || exit 1
            root_mode="$(owner_group_mode .)" || exit 1
            printf 'd\0.\0%s\0' "$root_mode"
            find . -mindepth 1 -print0 \
                | sort -z \
                | while IFS= read -r -d '' entry; do
                    local_path="$root/${entry#./}"
                    if [[ -L "$entry" ]]; then
                        case "$entry" in
                            ./lib/rustlib/rustc-src/rust|./lib/rustlib/src/rust)
                                ;;
                            *)
                                echo "error: stage2 sysroot contains an unreviewed symlink: $entry" >&2
                                exit 1
                                ;;
                        esac
                        link_target="$(canonical_directory "$entry")" || {
                            echo "error: stage2 rust-src link is dangling: $entry" >&2
                            exit 1
                        }
                        if [[ "$link_target" != "$TRUST_ROOT" ]]; then
                            echo "error: stage2 rust-src link escapes the exact checkout: $entry -> $link_target" >&2
                            exit 1
                        fi
                        link_text="$(readlink -- "$entry")" || exit 1
                        link_mode="$(owner_group_mode "$entry")" || exit 1
                        printf 'l\0%s\0%s\0%s\0' "$entry" "$link_mode" "$link_text"
                    elif [[ -f "$entry" ]]; then
                        file_mode="$(owner_group_mode "$entry")" || exit 1
                        file_digest="$(hash_stable_regular_file "$local_path" "stage2 sysroot file $entry")" || exit 1
                        printf 'f\0%s\0%s\0%s\0' "$entry" "$file_mode" "$file_digest"
                    elif [[ -d "$entry" ]]; then
                        directory_mode="$(owner_group_mode "$entry")" || exit 1
                        printf 'd\0%s\0%s\0' "$entry" "$directory_mode"
                    else
                        echo "error: stage2 sysroot contains a non-plain filesystem entry: $entry" >&2
                        exit 1
                    fi
                done
        ) | sha256sum
    )" || {
        echo "error: could not hash the complete stage2 sysroot: $root" >&2
        return 1
    }
    digest="${digest_line%% *}"
    if [[ ! "$digest" =~ ^[0-9a-f]{64}$ ]]; then
        echo "error: complete stage2 sysroot hash was not canonical SHA-256" >&2
        return 1
    fi
    printf '%s\n' "$digest"
}

require_plain_tree() {
    local root="$1"
    local label="$2"
    local unsupported

    [[ -d "$root" && ! -L "$root" ]] || {
        echo "error: $label root is not one exact directory: $root" >&2
        return 1
    }
    unsupported="$(find "$root" ! -type d ! -type f -print -quit)" || {
        echo "error: could not inspect $label for non-plain entries: $root" >&2
        return 1
    }
    if [[ -n "$unsupported" ]]; then
        echo "error: $label contains a symlink or non-plain filesystem entry: $unsupported" >&2
        return 1
    fi
}

seed_private_cargo_home() {
    local source_home="$1"
    local private_home="$2"
    local source_cache
    local source_index
    local registry_rows
    local git_source_count
    local name
    local version
    local expected_digest
    local archive
    local candidate
    local candidate_digest
    local registry_id
    local destination_dir
    local seeded_archives=0

    if [[ -z "$source_home" ]]; then
        echo "error: no Cargo cache seed was supplied; set TRUST_CERTIFIED_MONITOR_E2E_CACHE_HOME or CARGO_HOME" >&2
        return 1
    fi
    source_home="$(canonical_directory "$source_home")" || {
        echo "error: Cargo cache seed is not an existing directory: $source_home" >&2
        return 1
    }
    source_cache="$(canonical_directory "$source_home/registry/cache")" || {
        echo "error: Cargo cache seed has no registry archive cache: $source_home/registry/cache" >&2
        return 1
    }
    source_index="$(canonical_directory "$source_home/registry/index")" || {
        echo "error: Cargo cache seed has no registry index: $source_home/registry/index" >&2
        return 1
    }
    # `cp -a` would otherwise preserve a caller-controlled symlink into the
    # supposedly private Cargo home. Reject links, devices, sockets, and FIFOs
    # before copying, then recheck the isolated destination to close replacement
    # races that materialize as a non-plain copied entry.
    require_plain_tree "$source_index" "Cargo registry index seed" || return 1
    [[ -f "$LOCK_FILE" && ! -L "$LOCK_FILE" ]] || {
        echo "error: targo-trust Cargo.lock is not one exact regular file: $LOCK_FILE" >&2
        return 1
    }

    mkdir -m 700 -- \
        "$private_home" \
        "$private_home/registry" \
        "$private_home/registry/cache" \
        "$private_home/registry/index" || {
        echo "error: could not create private Cargo home: $private_home" >&2
        return 1
    }
    cp -a -- "$source_index/." "$private_home/registry/index/" || {
        echo "error: could not snapshot the Cargo registry index into private state" >&2
        return 1
    }
    require_plain_tree "$private_home/registry/index" "private Cargo registry index" || return 1

    registry_rows="$(awk '
        function emit() {
            if (registry && name != "" && version != "" && checksum != "") {
                print name "\t" version "\t" checksum
            } else if (registry) {
                malformed = 1
            }
        }
        /^\[\[package\]\]$/ { emit(); name = ""; version = ""; checksum = ""; registry = 0; next }
        /^name = "/ { name = $0; sub(/^name = "/, "", name); sub(/"$/, "", name); next }
        /^version = "/ { version = $0; sub(/^version = "/, "", version); sub(/"$/, "", version); next }
        /^source = "registry\+/ { registry = 1; next }
        /^checksum = "/ { checksum = $0; sub(/^checksum = "/, "", checksum); sub(/"$/, "", checksum); next }
        END { emit(); if (malformed) exit 3 }
    ' "$LOCK_FILE")" || {
        echo "error: registry package in Cargo.lock lacks exact name/version/checksum identity" >&2
        return 1
    }
    if [[ -z "$registry_rows" ]]; then
        echo "error: Cargo.lock contains no checksummed registry packages to seed" >&2
        return 1
    fi

    while IFS=$'\t' read -r name version expected_digest; do
        if [[ ! "$expected_digest" =~ ^[0-9a-f]{64}$ ]]; then
            echo "error: Cargo.lock has a non-canonical checksum for $name $version" >&2
            return 1
        fi
        archive="$name-$version.crate"
        shopt -s nullglob
        for candidate in "$source_cache"/*/"$archive"; do
            [[ -f "$candidate" && ! -L "$candidate" ]] || continue
            candidate_digest="$(hash_stable_regular_file "$candidate" "cached registry archive $archive")" || return 1
            [[ "$candidate_digest" == "$expected_digest" ]] || continue
            registry_id="$(basename -- "$(dirname -- "$candidate")")"
            [[ "$registry_id" =~ ^[A-Za-z0-9._-]+$ ]] || {
                echo "error: registry cache identity is not one safe path component: $registry_id" >&2
                return 1
            }
            destination_dir="$private_home/registry/cache/$registry_id"
            mkdir -m 700 -p -- "$destination_dir" || return 1
            if [[ ! -e "$destination_dir/$archive" && ! -L "$destination_dir/$archive" ]]; then
                copy_registry_archive "$candidate" "$destination_dir/$archive" || return 1
                chmod 400 "$destination_dir/$archive" || return 1
                candidate_digest="$(hash_stable_regular_file "$destination_dir/$archive" "private registry archive $archive")" || return 1
                if [[ "$candidate_digest" != "$expected_digest" ]]; then
                    rm -f -- "$destination_dir/$archive"
                    continue
                fi
            fi
            seeded_archives=$((seeded_archives + 1))
        done
        shopt -u nullglob
        # Cargo.lock can retain packages for inactive target cfgs. Missing
        # archives are therefore adjudicated by the later locked, offline
        # Host build: any actually-required absence is a hard Cargo failure.
    done <<< "$registry_rows"
    if [[ "$seeded_archives" -eq 0 ]]; then
        echo "error: Cargo cache seed contains none of Cargo.lock's checksummed registry archives" >&2
        return 1
    fi

    git_source_count="$(awk '/^source = "git\+/{count++} END {print count + 0}' "$LOCK_FILE")" || return 1
    if [[ "$git_source_count" -gt 0 ]]; then
        # A symlink to Cargo's caller-owned bare DB is not a snapshot: refs,
        # config, and objects can change while the gate runs. Copying the whole
        # DB without independently authenticating its config/objects is not an
        # evidence boundary either. Refuse Git sources until that format is
        # designed and regression-sealed.
        echo "error: Cargo.lock contains $git_source_count Git-sourced package(s), but certified-monitor E2E admits only checksummed registry archives" >&2
        return 1
    fi

    # Deliberately absent: user config, credentials, registry/src, git/checkouts,
    # Cargo bin shims, and any reusable compiled target artifacts.
    for forbidden in config config.toml credentials credentials.toml registry/src git/checkouts; do
        if [[ -e "$private_home/$forbidden" || -L "$private_home/$forbidden" ]]; then
            echo "error: private Cargo home unexpectedly contains reusable authority: $forbidden" >&2
            return 1
        fi
    done
}

stage2_candidates() {
    local candidate
    local seen=" "
    local candidates=("$TRUST_ROOT/build/host/stage2")

    shopt -s nullglob
    for candidate in "$TRUST_ROOT"/build/*/stage2; do
        candidates+=("$candidate")
    done
    shopt -u nullglob

    for candidate in "${candidates[@]}"; do
        [[ " $seen " == *" $candidate "* ]] && continue
        seen+="$candidate "
        printf '%s\n' "$candidate"
    done
}

# Mirror targo-trust's repo-local discovery boundary and reject ambiguous or
# incomplete stage2 trees instead of silently selecting around them.
discover_stage2_sysroot() {
    local candidate
    local canonical
    local seen=" "
    local discovered=()
    while IFS= read -r candidate; do
        [[ -f "$candidate/bin/trustc" && ! -L "$candidate/bin/trustc" && -x "$candidate/bin/trustc" ]] || continue
        if [[ ! -f "$candidate/bin/targo" || -L "$candidate/bin/targo" || ! -x "$candidate/bin/targo" ]]; then
            echo "error: discoverable stage2 trustc has no canonical executable sibling targo: $candidate" >&2
            return 1
        fi
        if [[ ! -f "$candidate/bin/targo-trust" || -L "$candidate/bin/targo-trust" || ! -x "$candidate/bin/targo-trust" ]]; then
            echo "error: discoverable stage2 trustc has no canonical executable sibling targo-trust: $candidate" >&2
            return 1
        fi
        if [[ ! -f "$candidate/bin/trustd" || -L "$candidate/bin/trustd" || ! -x "$candidate/bin/trustd" ]]; then
            echo "error: discoverable stage2 trustc has no canonical executable sibling trustd: $candidate" >&2
            return 1
        fi
        canonical="$(canonical_directory "$candidate")" || {
            echo "error: could not resolve stage2 sysroot: $candidate" >&2
            return 1
        }
        [[ " $seen " == *" $canonical "* ]] && continue
        seen+="$canonical "
        discovered+=("$canonical")
    done < <(stage2_candidates)

    case "${#discovered[@]}" in
        0)
            echo "error: no repo-local stage2 trustc/targo/targo-trust/trustd toolchain was found under $TRUST_ROOT/build/*/stage2" >&2
            return 1
            ;;
        1)
            printf '%s\n' "${discovered[0]}"
            ;;
        *)
            echo "error: multiple repo-local stage2 toolchains are discoverable; select one only after removing stale stage2 trees" >&2
            printf '  %s\n' "${discovered[@]}" >&2
            return 1
            ;;
    esac
}

STAGE2_SYSROOT="$(discover_stage2_sysroot)" || exit 1
case "$STAGE2_SYSROOT" in
    "$TRUST_ROOT"/build/*/stage2)
        ;;
    *)
        echo "error: discovered stage2 sysroot escapes the exact repo-local build/<host>/stage2 boundary: $STAGE2_SYSROOT" >&2
        exit 1
        ;;
esac

if [[ -n "$REQUESTED_SYSROOT" ]]; then
    REQUESTED_SYSROOT_INPUT="$REQUESTED_SYSROOT"
    REQUESTED_SYSROOT="$(canonical_directory "$REQUESTED_SYSROOT_INPUT")" || {
        echo "error: requested stage2 sysroot does not exist: $REQUESTED_SYSROOT_INPUT" >&2
        exit 1
    }
    if [[ "$REQUESTED_SYSROOT" != "$STAGE2_SYSROOT" ]]; then
        echo "error: requested stage2 sysroot is not the toolchain targo-trust will discover first" >&2
        echo "  requested: $REQUESTED_SYSROOT" >&2
        echo "  discovered: $STAGE2_SYSROOT" >&2
        exit 1
    fi
fi

TRUSTC="$STAGE2_SYSROOT/bin/trustc"
TARGO="$STAGE2_SYSROOT/bin/targo"
TARGO_TRUST="$STAGE2_SYSROOT/bin/targo-trust"
TRUSTD="$STAGE2_SYSROOT/bin/trustd"
require_clean_checkout "before" || exit 1

TRUSTC_VERSION="$("$TRUSTC" -Vv)" || {
    echo "error: stage2 trustc identity probe failed: $TRUSTC" >&2
    exit 1
}
if [[ "$(printf '%s\n' "$TRUSTC_VERSION" | grep -Fxc 'binary: trustc' || true)" -ne 1 ]]; then
    echo "error: stage2 compiler did not report exactly one canonical 'binary: trustc' identity" >&2
    exit 1
fi
TRUSTC_COMMIT="$(printf '%s\n' "$TRUSTC_VERSION" | sed -n 's/^commit-hash: //p')"
if [[ "$(printf '%s\n' "$TRUSTC_COMMIT" | wc -l | tr -d ' ')" -ne 1 || ! "$TRUSTC_COMMIT" =~ ^[0-9a-f]{40}$ ]]; then
    echo "error: stage2 trustc did not report exactly one full commit hash" >&2
    exit 1
fi
CURRENT_HEAD="$EXPECTED_HEAD"
if [[ "$TRUSTC_COMMIT" != "$CURRENT_HEAD" ]]; then
    echo "error: stale stage2 trustc reports $TRUSTC_COMMIT, but repository HEAD is $CURRENT_HEAD" >&2
    exit 1
fi
REPORTED_SYSROOT_RAW="$("$TRUSTC" --print sysroot)" || {
    echo "error: stage2 trustc sysroot probe failed" >&2
    exit 1
}
if [[ -z "$REPORTED_SYSROOT_RAW" || "$REPORTED_SYSROOT_RAW" == *$'\n'* ]]; then
    echo "error: stage2 trustc did not report exactly one sysroot line" >&2
    exit 1
fi
REPORTED_SYSROOT="$(canonical_directory "$REPORTED_SYSROOT_RAW")" || {
    echo "error: stage2 trustc reported a missing sysroot: $REPORTED_SYSROOT_RAW" >&2
    exit 1
}
if [[ "$REPORTED_SYSROOT" != "$STAGE2_SYSROOT" ]]; then
    echo "error: stage2 trustc reports a different sysroot: $REPORTED_SYSROOT" >&2
    exit 1
fi
TARGO_VERSION="$("$TARGO" -Vv)" || {
    echo "error: stage2 Targo identity probe failed: $TARGO" >&2
    exit 1
}
TARGO_FIRST_LINE="$(printf '%s\n' "$TARGO_VERSION" | sed -n '1p')"
if [[ -z "$TARGO_FIRST_LINE" || "$TARGO_FIRST_LINE" != targo\ * ]]; then
    echo "error: stage2 frontend did not report a canonical Targo identity: $TARGO_FIRST_LINE" >&2
    exit 1
fi
TARGO_COMMIT="$(trust_repo_commit_from_version "$TARGO_VERSION" "stage2 Targo")" || exit 1
if [[ "$TARGO_COMMIT" != "$CURRENT_HEAD" ]]; then
    echo "error: stale stage2 Targo reports Trust repo commit $TARGO_COMMIT, but repository HEAD is $CURRENT_HEAD" >&2
    exit 1
fi
TARGO_TRUST_VERSION="$("$TARGO_TRUST" --version)" || {
    echo "error: stage2 targo-trust identity probe failed: $TARGO_TRUST" >&2
    exit 1
}
TARGO_TRUST_FIRST_LINE="$(printf '%s\n' "$TARGO_TRUST_VERSION" | sed -n '1p')"
if [[ -z "$TARGO_TRUST_FIRST_LINE" || "$TARGO_TRUST_FIRST_LINE" != targo-trust\ * ]]; then
    echo "error: stage2 verifier frontend did not report a canonical targo-trust identity: $TARGO_TRUST_FIRST_LINE" >&2
    exit 1
fi
TARGO_TRUST_COMMIT="$(trust_repo_commit_from_version "$TARGO_TRUST_VERSION" "stage2 targo-trust")" || exit 1
if [[ "$TARGO_TRUST_COMMIT" != "$CURRENT_HEAD" ]]; then
    echo "error: stale stage2 targo-trust reports Trust repo commit $TARGO_TRUST_COMMIT, but repository HEAD is $CURRENT_HEAD" >&2
    exit 1
fi
TRUSTD_VERSION="$("$TRUSTD" --version)" || {
    echo "error: stage2 trustd identity probe failed: $TRUSTD" >&2
    exit 1
}
TRUSTD_FIRST_LINE="$(printf '%s\n' "$TRUSTD_VERSION" | sed -n '1p')"
if [[ -z "$TRUSTD_FIRST_LINE" || "$TRUSTD_FIRST_LINE" != trustd\ * ]]; then
    echo "error: stage2 daemon did not report a canonical trustd identity: $TRUSTD_FIRST_LINE" >&2
    exit 1
fi
TRUSTD_COMMIT="$(trust_repo_commit_from_version "$TRUSTD_VERSION" "stage2 trustd")" || exit 1
if [[ "$TRUSTD_COMMIT" != "$CURRENT_HEAD" ]]; then
    echo "error: stale stage2 trustd reports Trust repo commit $TRUSTD_COMMIT, but repository HEAD is $CURRENT_HEAD" >&2
    exit 1
fi
TRUSTC_SHA256="$(hash_stable_executable "$TRUSTC" "stage2 trustc")" || exit 1
TARGO_SHA256="$(hash_stable_executable "$TARGO" "stage2 Targo")" || exit 1
TARGO_TRUST_SHA256="$(hash_stable_executable "$TARGO_TRUST" "stage2 targo-trust")" || exit 1
TRUSTD_SHA256="$(hash_stable_executable "$TRUSTD" "stage2 trustd")" || exit 1
STAGE2_TREE_SHA256="$(hash_stable_stage2_tree "$STAGE2_SYSROOT")" || exit 1
MANIFEST_SHA256="$(hash_stable_regular_file "$MANIFEST" "targo-trust manifest")" || exit 1
LOCK_SHA256="$(hash_stable_regular_file "$LOCK_FILE" "targo-trust lock file")" || exit 1

if [[ "$LOG_DIR" != /* ]]; then
    LOG_DIR="$TRUST_ROOT/$LOG_DIR"
fi
if [[ "$TARGET_DIR" != /* ]]; then
    TARGET_DIR="$TRUST_ROOT/$TARGET_DIR"
fi
case "$LOG_DIR/" in
    "$TARGET_DIR/"*)
        echo "error: certified-monitor log directory must not be inside its ephemeral target" >&2
        exit 1
        ;;
esac
case "$TARGET_DIR/" in
    "$LOG_DIR/"*)
        echo "error: certified-monitor target directory must not be inside its retained log directory" >&2
        exit 1
        ;;
esac

TARGET_DIR="$(create_fresh_private_directory "$TARGET_DIR" "certified-monitor target directory")" || exit 1
PRIVATE_TARGET_CREATED="$TARGET_DIR"
LOG_DIR="$(create_fresh_private_directory "$LOG_DIR" "certified-monitor evidence directory")" || exit 1
case "$LOG_DIR/" in
    "$TARGET_DIR/"*)
        echo "error: canonical certified-monitor log directory overlaps its ephemeral target" >&2
        exit 1
        ;;
esac
case "$TARGET_DIR/" in
    "$LOG_DIR/"*)
        echo "error: canonical certified-monitor target directory overlaps its retained log directory" >&2
        exit 1
        ;;
esac

# Retain the exact inputs whose stability is rechecked below. The repository
# HEAD binds the committed source/submodule graph; explicit tool and Cargo-file
# hashes make the evidence directory independently inspectable without relying
# on a surrounding tier log.
IDENTITY_LOG="$LOG_DIR/gate-identity.txt"
EVIDENCE_FILES=()
{
    printf 'schema=trust.certified-monitor-e2e-payload-identity.v4\n'
    printf 'result_scope=payload-only\n'
    printf 'source_authority=unverified\n'
    printf 'head=%s\n' "$CURRENT_HEAD"
    printf 'host_os=%s\n' "$HOST_OS"
    printf 'host_arch=%s\n' "$HOST_ARCH"
    printf 'stage2_sysroot=%s\n' "$STAGE2_SYSROOT"
    printf 'trustc_sha256=%s\n' "$TRUSTC_SHA256"
    printf 'targo_sha256=%s\n' "$TARGO_SHA256"
    printf 'targo_trust_sha256=%s\n' "$TARGO_TRUST_SHA256"
    printf 'trustd_sha256=%s\n' "$TRUSTD_SHA256"
    printf 'stage2_tree_sha256=%s\n' "$STAGE2_TREE_SHA256"
    printf 'manifest_sha256=%s\n' "$MANIFEST_SHA256"
    printf 'lock_sha256=%s\n' "$LOCK_SHA256"
    printf 'targo_commit=%s\n' "$TARGO_COMMIT"
    printf 'targo_trust_commit=%s\n' "$TARGO_TRUST_COMMIT"
    printf 'trustd_commit=%s\n' "$TRUSTD_COMMIT"
    printf '%s\n' 'trustc_version_begin'
    printf '%s\n' "$TRUSTC_VERSION"
    printf '%s\n' 'trustc_version_end'
    printf '%s\n' 'targo_version_begin'
    printf '%s\n' "$TARGO_VERSION"
    printf '%s\n' 'targo_version_end'
    printf '%s\n' 'targo_trust_version_begin'
    printf '%s\n' "$TARGO_TRUST_VERSION"
    printf '%s\n' 'targo_trust_version_end'
    printf '%s\n' 'trustd_version_begin'
    printf '%s\n' "$TRUSTD_VERSION"
    printf '%s\n' 'trustd_version_end'
} >"$IDENTITY_LOG" || {
    echo "error: could not write certified-monitor gate identity: $IDENTITY_LOG" >&2
    exit 1
}
chmod 400 "$IDENTITY_LOG" || exit 1
EVIDENCE_FILES+=("$IDENTITY_LOG")

PRIVATE_HOME="$(create_fresh_private_directory "$TARGET_DIR/home" "certified-monitor HOME")" || exit 1
PRIVATE_TMPDIR="$(create_fresh_private_directory "$TARGET_DIR/tmp" "certified-monitor TMPDIR")" || exit 1
PRIVATE_CARGO_HOME="$TARGET_DIR/cargo-home"
seed_private_cargo_home "$SOURCE_CARGO_HOME" "$PRIVATE_CARGO_HOME" || exit 1
export HOME="$PRIVATE_HOME"
export TMPDIR="$PRIVATE_TMPDIR"
export CARGO_HOME="$PRIVATE_CARGO_HOME"

# Give the outer compilation only fresh private storage and the fixed system
# tool path. In particular, no compiler, wrapper, rustflags, loader, runner,
# user Cargo config, unpacked cache, or Trust-private environment channel
# reaches the compiled test harness and poisons its nested Targo invocations.
CLEAN_TARGO_ENV=(
    /usr/bin/env -i
    "PATH=$PATH"
    "HOME=$PRIVATE_HOME"
    "CARGO_HOME=$PRIVATE_CARGO_HOME"
    "TMPDIR=$PRIVATE_TMPDIR"
    "LC_ALL=$LC_ALL"
    "LANG=$LANG"
    "TZ=$TZ"
    GIT_CONFIG_GLOBAL=/dev/null
    GIT_CONFIG_NOSYSTEM=1
    CARGO_NET_OFFLINE=true
    CARGO_TERM_COLOR=never
    RUSTC_BOOTSTRAP=1
)

common_targo_test() {
    # Cargo searches `.cargo/config.toml` from its invocation directory toward
    # the filesystem root.  Invoke from `/`, with an absolute manifest and a
    # private CARGO_HOME, so neither a checkout-local ignored config nor a user
    # config in one of the checkout's parent directories can inject a runner,
    # wrapper, source replacement, or flags.
    (
        cd / || exit 1
        "${CLEAN_TARGO_ENV[@]}" \
            "$TARGO" --unverified test \
            --manifest-path "$MANIFEST" \
            --target-dir "$TARGET_DIR" \
            --bin targo-trust \
            --locked \
            --offline \
            "$@"
    )
}

LIST_LOG="$LOG_DIR/compiled-test-inventory.log"
if ! common_targo_test -- --list >"$LIST_LOG" 2>&1; then
    cat "$LIST_LOG" >&2
    echo "error: could not compile and list the targo-trust test inventory" >&2
    exit 1
fi
EVIDENCE_FILES+=("$LIST_LOG")

for test_name in "${TESTS[@]}"; do
    if [[ "$(grep -Fxc "$test_name: test" "$LIST_LOG" || true)" -ne 1 ]]; then
        echo "error: compiled inventory did not contain exactly one ignored E2E named '$test_name'" >&2
        echo "  inventory: $LIST_LOG" >&2
        exit 1
    fi
done

# The prefix is the reviewed release-boundary namespace. Require equality,
# not merely inclusion: otherwise a newly added real-Targo monitor regression
# could remain ignored forever while this gate continued to report 3/3.
mapfile -t INVENTORIED_RELEASE_TESTS < <(
    grep -E "^${RELEASE_TEST_PREFIX}.*: test$" "$LIST_LOG" \
        | sed 's/: test$//' \
        | sort
)
if [[ "${#INVENTORIED_RELEASE_TESTS[@]}" -ne "${#TESTS[@]}" ]]; then
    echo "error: compiled real-Targo release E2E inventory does not match the exact reviewed set" >&2
    printf '  inventoried: %s\n' "${INVENTORIED_RELEASE_TESTS[@]}" >&2
    printf '  reviewed: %s\n' "${TESTS[@]}" >&2
    exit 1
fi
for inventory_name in "${INVENTORIED_RELEASE_TESTS[@]}"; do
    reviewed=0
    for test_name in "${TESTS[@]}"; do
        if [[ "$inventory_name" == "$test_name" ]]; then
            reviewed=1
            break
        fi
    done
    if [[ "$reviewed" -ne 1 ]]; then
        echo "error: compiled real-Targo release E2E is not in the exact reviewed set: $inventory_name" >&2
        exit 1
    fi
done

for test_name in "${TESTS[@]}"; do
    short_name="${test_name#tests::}"
    test_log="$LOG_DIR/$short_name.log"
    echo "certified-monitor E2E: running $test_name"

    set +e
    common_targo_test "$test_name" -- --exact --ignored --test-threads=1 --nocapture \
        2>&1 | tee "$test_log"
    pipeline_status=("${PIPESTATUS[@]}")
    set -e
    test_rc="${pipeline_status[0]}"

    if [[ "$test_rc" -ne 0 ]]; then
        echo "error: certified-monitor E2E failed: $test_name (exit $test_rc)" >&2
        exit "$test_rc"
    fi
    if [[ "${pipeline_status[1]}" -ne 0 ]]; then
        echo "error: could not write certified-monitor E2E log for $test_name" >&2
        exit 1
    fi
    # The E2E may print nested Cargo/libtest summaries. The last test-result
    # line is the outer exact-filter harness and therefore the authoritative
    # selected-test count.
    outer_result="$(grep '^test result:' "$test_log" | tail -n 1 || true)"
    if [[ "$outer_result" != 'test result: ok. 1 passed; 0 failed; 0 ignored; 0 measured;'* ]]; then
        echo "error: $test_name exited zero without exactly one successful ignored-test execution" >&2
        exit 1
    fi
    EVIDENCE_FILES+=("$test_log")
done

FINAL_TRUSTC_SHA256="$(hash_stable_executable "$TRUSTC" "stage2 trustc recheck")" || exit 1
FINAL_TARGO_SHA256="$(hash_stable_executable "$TARGO" "stage2 Targo recheck")" || exit 1
FINAL_TARGO_TRUST_SHA256="$(hash_stable_executable "$TARGO_TRUST" "stage2 targo-trust recheck")" || exit 1
FINAL_TRUSTD_SHA256="$(hash_stable_executable "$TRUSTD" "stage2 trustd recheck")" || exit 1
FINAL_STAGE2_TREE_SHA256="$(hash_stable_stage2_tree "$STAGE2_SYSROOT")" || exit 1
FINAL_MANIFEST_SHA256="$(hash_stable_regular_file "$MANIFEST" "targo-trust manifest recheck")" || exit 1
FINAL_LOCK_SHA256="$(hash_stable_regular_file "$LOCK_FILE" "targo-trust lock-file recheck")" || exit 1
if [[ "$FINAL_TRUSTC_SHA256" != "$TRUSTC_SHA256" \
    || "$FINAL_TARGO_SHA256" != "$TARGO_SHA256" \
    || "$FINAL_TARGO_TRUST_SHA256" != "$TARGO_TRUST_SHA256" \
    || "$FINAL_TRUSTD_SHA256" != "$TRUSTD_SHA256" \
    || "$FINAL_STAGE2_TREE_SHA256" != "$STAGE2_TREE_SHA256" \
    || "$FINAL_MANIFEST_SHA256" != "$MANIFEST_SHA256" \
    || "$FINAL_LOCK_SHA256" != "$LOCK_SHA256" ]]; then
    echo "error: stage2 tools or Cargo inputs changed during certified-monitor E2E" >&2
    exit 1
fi

FINAL_TRUSTC_VERSION="$("$TRUSTC" -Vv)" || {
    echo "error: stage2 trustc identity recheck failed" >&2
    exit 1
}
FINAL_REPORTED_SYSROOT_RAW="$("$TRUSTC" --print sysroot)" || {
    echo "error: stage2 trustc sysroot recheck failed" >&2
    exit 1
}
FINAL_TARGO_VERSION="$("$TARGO" -Vv)" || {
    echo "error: stage2 Targo identity recheck failed" >&2
    exit 1
}
FINAL_TARGO_TRUST_VERSION="$("$TARGO_TRUST" --version)" || {
    echo "error: stage2 targo-trust identity recheck failed" >&2
    exit 1
}
FINAL_TRUSTD_VERSION="$("$TRUSTD" --version)" || {
    echo "error: stage2 trustd identity recheck failed" >&2
    exit 1
}
if [[ "$FINAL_TRUSTC_VERSION" != "$TRUSTC_VERSION" \
    || "$FINAL_REPORTED_SYSROOT_RAW" != "$REPORTED_SYSROOT_RAW" \
    || "$FINAL_TARGO_VERSION" != "$TARGO_VERSION" \
    || "$FINAL_TARGO_TRUST_VERSION" != "$TARGO_TRUST_VERSION" \
    || "$FINAL_TRUSTD_VERSION" != "$TRUSTD_VERSION" ]]; then
    echo "error: stage2 trustc/Targo/targo-trust/trustd identity changed during certified-monitor E2E" >&2
    exit 1
fi

TERMINAL_TRUSTC_SHA256="$(hash_stable_executable "$TRUSTC" "terminal stage2 trustc recheck")" || exit 1
TERMINAL_TARGO_SHA256="$(hash_stable_executable "$TARGO" "terminal stage2 Targo recheck")" || exit 1
TERMINAL_TARGO_TRUST_SHA256="$(hash_stable_executable "$TARGO_TRUST" "terminal stage2 targo-trust recheck")" || exit 1
TERMINAL_TRUSTD_SHA256="$(hash_stable_executable "$TRUSTD" "terminal stage2 trustd recheck")" || exit 1
TERMINAL_STAGE2_TREE_SHA256="$(hash_stable_stage2_tree "$STAGE2_SYSROOT")" || exit 1
if [[ "$TERMINAL_TRUSTC_SHA256" != "$TRUSTC_SHA256" \
    || "$TERMINAL_TARGO_SHA256" != "$TARGO_SHA256" \
    || "$TERMINAL_TARGO_TRUST_SHA256" != "$TARGO_TRUST_SHA256" \
    || "$TERMINAL_TRUSTD_SHA256" != "$TRUSTD_SHA256" \
    || "$TERMINAL_STAGE2_TREE_SHA256" != "$STAGE2_TREE_SHA256" ]]; then
    echo "error: stage2 trustc/Targo/targo-trust/trustd bytes changed during final identity probes" >&2
    exit 1
fi

# Reusable compiled artifacts are not retained as evidence. Remove the exact
# private target before the terminal source/HEAD checks so a custom in-tree
# location cannot turn its own generated files into a clean release result.
cleanup_private_target || exit 1

# The native parent repeats its controlled HEAD/content/submodule validation
# after this process exits.  Do not let this shell's repository-local Git config
# nominate a different terminal commit.
FINAL_HEAD="$EXPECTED_HEAD"
require_clean_checkout "after" || exit 1

# Seal the retained payload logs after the shell-local consistency checks.
# The manifest names every retained input/inventory/result log by a relative,
# fixed path and hashes stable regular-file bytes. It does not authenticate
# source authority; only the native parent's successful postcheck can do that.
EVIDENCE_MANIFEST="$LOG_DIR/evidence.sha256"
: >"$EVIDENCE_MANIFEST" || {
    echo "error: could not create certified-monitor evidence manifest: $EVIDENCE_MANIFEST" >&2
    exit 1
}
for evidence_file in "${EVIDENCE_FILES[@]}"; do
    evidence_digest="$(hash_stable_regular_file "$evidence_file" "certified-monitor retained evidence")" || exit 1
    evidence_name="${evidence_file#"$LOG_DIR"/}"
    if [[ "$evidence_name" == "$evidence_file" || "$evidence_name" == */* || -z "$evidence_name" ]]; then
        echo "error: retained evidence escaped the exact evidence-directory leaf boundary: $evidence_file" >&2
        exit 1
    fi
    printf '%s  %s\n' "$evidence_digest" "$evidence_name" >>"$EVIDENCE_MANIFEST" || exit 1
    chmod 400 "$evidence_file" || exit 1
done
chmod 400 "$EVIDENCE_MANIFEST" || exit 1
EVIDENCE_MANIFEST_SHA256="$(hash_stable_regular_file "$EVIDENCE_MANIFEST" "certified-monitor evidence manifest")" || exit 1
chmod 500 "$LOG_DIR" || exit 1

echo "certified-monitor payload: PASS ${#TESTS[@]}/${#TESTS[@]} (source authority unverified)"
echo "certified-monitor payload logs: $LOG_DIR"
echo "certified-monitor payload manifest sha256: $EVIDENCE_MANIFEST_SHA256"
echo "certified-monitor payload: native controlled-Git postcheck required for release PASS"
