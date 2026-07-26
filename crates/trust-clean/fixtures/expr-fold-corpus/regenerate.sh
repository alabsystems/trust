#!/usr/bin/env bash
# Regenerate the expr-fold-corpus dumps: build the census extract crate
# (census-m6-cleankernel-2026-07-08/extract-foldmemo — REAL, byte-for-byte
# clean-kernel sources; see ITS provenance) with the prebuilt stage1 trustc in
# dump-only survey mode, then copy the Expr-fold-SCC rows this corpus pins.
# Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0 OR MIT
set -euo pipefail
export LC_ALL=C
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)"
REPO_ROOT="$(cd "$HERE/../../../.." && pwd -P)"
EXTRACT="$HERE/../census-m6-cleankernel-2026-07-08/extract-foldmemo"
TRUSTC="${TRUSTC:-$REPO_ROOT/build/host/stage1/bin/trustc}"   # prebuilt stage1, do NOT rebuild
RUSTC_WRAPPER="$HERE/regenerate-rustc-wrapper.sh"
EXPECTED_INVENTORY=124
SCRATCH="$(mktemp -d)"
LOCK="$HERE/.regenerate.lock"
RUN_TOKEN="$$.$(date +%s).${RANDOM}${RANDOM}"
PUBLISH="$HERE/.regenerate-next.$RUN_TOKEN"
BACKUP="$HERE/.regenerate-backup.$RUN_TOKEN"
TRANSACTION="$HERE/.regenerate.transaction"
INVENTORY_FILES="$SCRATCH/inventory-files.txt"
INVENTORY_OWNERS="$SCRATCH/inventory-owners.tsv"
committed=0
lock_owned=0
LOCK_TARGET=""
CLAIM_TARGET=""
OWNER_INIT=""
mkdir -p "$SCRATCH/home" "$SCRATCH/cargo-home" "$SCRATCH/tmp"

sha256_file() {
  if command -v shasum >/dev/null 2>&1; then
    shasum -a 256 "$1" | awk '{ print $1 }'
  elif command -v sha256sum >/dev/null 2>&1; then
    sha256sum "$1" | awk '{ print $1 }'
  else
    echo "regeneration requires shasum or sha256sum" >&2
    return 1
  fi
}

resolve_command() {
  local command_name="$1"
  local resolved
  resolved="$(command -v "$command_name" 2>/dev/null || true)"
  if [[ -z "$resolved" || ! -x "$resolved" ]]; then
    echo "regeneration requires executable $command_name" >&2
    return 1
  fi
  local directory
  directory="$(cd "$(dirname "$resolved")" && pwd -P)"
  printf '%s/%s\n' "$directory" "$(basename "$resolved")"
}

PYTHON3_BIN="$(resolve_command python3)"
JQ_BIN="$(resolve_command jq)"
if command -v rustup >/dev/null 2>&1; then
  CARGO_BIN="$(env -u RUSTUP_TOOLCHAIN rustup which cargo 2>/dev/null || true)"
else
  CARGO_BIN=""
fi
if [[ -z "$CARGO_BIN" || ! -x "$CARGO_BIN" ]]; then
  CARGO_BIN="$(resolve_command cargo)"
fi
CARGO_BIN="$(cd "$(dirname "$CARGO_BIN")" && pwd -P)/$(basename "$CARGO_BIN")"
CONTROLLED_PATH="$(dirname "$CARGO_BIN"):/usr/bin:/bin:/usr/sbin:/sbin:/usr/local/bin:/opt/homebrew/bin"
SOURCE_CARGO_HOME="${CARGO_HOME:-${HOME:?HOME is required}/.cargo}"
for cache_component in registry git; do
  if [[ -e "$SOURCE_CARGO_HOME/$cache_component" ]]; then
    ln -s "$SOURCE_CARGO_HOME/$cache_component" "$SCRATCH/cargo-home/$cache_component"
  fi
done

# Python's os.fsync is used only as a portable syscall shim. Files are synced
# before their rename, and the containing directory is synced after every
# journal/commit-point rename so the SIGKILL recovery claim is durable rather
# than merely process-atomic.
fsync_paths() {
  "$PYTHON3_BIN" - "$@" <<'PY'
import os
import sys

for path in sys.argv[1:]:
    descriptor = os.open(path, os.O_RDONLY)
    try:
        os.fsync(descriptor)
    finally:
        os.close(descriptor)
PY
}

fsync_inventory_files() {
  local root="$1"
  local paths=()
  local file
  while IFS= read -r file; do
    paths+=("$root/$file")
  done < "$INVENTORY_FILES"
  fsync_paths "${paths[@]}"
}

# `ln -s target existing-directory` may succeed by creating a child link even
# with common no-dereference flags. Use the syscall directly so acquisition is
# an exact create-if-absent operation for the named link itself.
symlink_nofollow() {
  local target="$1"
  local link="$2"
  "$PYTHON3_BIN" - "$target" "$link" <<'PY'
import os
import sys

os.symlink(sys.argv[1], sys.argv[2])
PY
}

rename_exact() {
  local source="$1"
  local destination="$2"
  "$PYTHON3_BIN" - "$source" "$destination" <<'PY'
import os
import sys

os.rename(sys.argv[1], sys.argv[2])
PY
}

process_identity() {
  local pid="$1"
  ps -o lstart= -p "$pid" 2>/dev/null \
    | sed -e 's/^[[:space:]]*//' -e 's/[[:space:]][[:space:]]*/ /g'
}

write_owner() {
  local owner_dir="$1"
  local output="$owner_dir/owner.next.$RUN_TOKEN"
  local identity
  identity="$(process_identity "$$")"
  if [[ -z "$identity" ]]; then
    echo "cannot determine regeneration process start identity" >&2
    return 1
  fi
  printf '%s\t%s\t%s\n' "$$" "$RUN_TOKEN" "$identity" > "$output"
  chmod 0644 "$output"
  fsync_paths "$output"
  mv "$output" "$owner_dir/owner"
  fsync_paths "$owner_dir"
}

# Build owner metadata completely before publishing its reserved directory
# name. The temporary is on the corpus filesystem, so the final rename is
# atomic; a crash-only initializer artifact is reaped after a later process
# wins the public lock.
initialize_owner_directory() {
  local destination="$1"
  local kind="$2"
  OWNER_INIT="$HERE/.regenerate-owner-init.$RUN_TOKEN.$kind"
  mkdir "$OWNER_INIT"
  write_owner "$OWNER_INIT"
  rename_exact "$OWNER_INIT" "$destination"
  OWNER_INIT=""
  fsync_paths "$HERE"
}

owner_is_live() {
  local owner_dir="$1"
  local pid token recorded_identity extra
  IFS=$'\t' read -r pid token recorded_identity extra 2>/dev/null \
    < "$owner_dir/owner" || return 1
  [[ "$pid" =~ ^[0-9]+$ && -n "$token" && -n "$recorded_identity" && -z "${extra:-}" ]] || return 1
  local current_identity
  current_identity="$(process_identity "$pid")"
  [[ -n "$current_identity" && "$current_identity" == "$recorded_identity" ]]
}

owner_token_is_ours() {
  local owner_dir="$1"
  local pid token identity extra
  IFS=$'\t' read -r pid token identity extra 2>/dev/null \
    < "$owner_dir/owner" || return 1
  [[ "$pid" == "$$" && "$token" == "$RUN_TOKEN" && -n "$identity" && -z "${extra:-}" ]]
}

write_manifest() {
  local dir="$1"
  local output="$2"
  : > "$output"
  while IFS= read -r file; do
    printf '%s\t%s\n' "$(sha256_file "$dir/$file")" "$file" >> "$output"
  done < "$INVENTORY_FILES"
  chmod 0644 "$output"
}

read_manifest_inventory() {
  local manifest="$1"
  local listed="$2"
  local count=0
  local previous=""
  : > "$listed"
  while IFS=$'\t' read -r expected file extra; do
    if [[ ! "$expected" =~ ^[0-9a-f]{64}$ \
        || -z "$file" \
        || -n "${extra:-}" \
        || "$file" == */* \
        || "$file" != *.json ]]; then
      echo "malformed corpus manifest entry: $expected $file ${extra:-}" >&2
      return 1
    fi
    if [[ -n "$previous" && ( "$file" == "$previous" || "$file" < "$previous" ) ]]; then
      echo "corpus manifest filenames are duplicate or not bytewise sorted: $file" >&2
      return 1
    fi
    printf '%s\n' "$file" >> "$listed"
    previous="$file"
    count=$((count + 1))
  done < "$manifest"
  if [[ "$count" != "$EXPECTED_INVENTORY" ]]; then
    echo "corpus manifest has $count entries, want $EXPECTED_INVENTORY" >&2
    return 1
  fi
}

verify_manifest() {
  local dir="$1"
  local manifest="$2"
  local trusted_inventory="${3:-}"
  local listed="$SCRATCH/manifest-files.$$.txt"
  read_manifest_inventory "$manifest" "$listed"
  while IFS=$'\t' read -r expected file extra; do
    if [[ ! -f "$dir/$file" ]]; then
      echo "corpus manifest names missing file: $file" >&2
      return 1
    fi
    if [[ "$(sha256_file "$dir/$file")" != "$expected" ]]; then
      echo "corpus manifest hash mismatch: $file" >&2
      return 1
    fi
  done < "$manifest"
  if [[ -n "$trusted_inventory" ]] && ! cmp -s "$trusted_inventory" "$listed"; then
    echo "corpus manifest filename inventory drift" >&2
    return 1
  fi
}

journal_value() {
  local journal="$1"
  local key="$2"
  awk -F '\t' -v key="$key" '$1 == key && NF == 2 { print $2 }' "$journal"
}

write_transaction() {
  local root="$1"
  local publish="$2"
  local backup="$3"
  local old_manifest="$4"
  local new_manifest="$5"
  local old_toolchain="$6"
  local new_toolchain="$7"
  local phase="$8"
  local next="$root/.regenerate.transaction.next.$RUN_TOKEN"
  {
    printf 'version\t1\n'
    printf 'run_token\t%s\n' "$RUN_TOKEN"
    printf 'publish\t%s\n' "$(basename "$publish")"
    printf 'backup\t%s\n' "$(basename "$backup")"
    printf 'old_manifest\t%s\n' "$old_manifest"
    printf 'new_manifest\t%s\n' "$new_manifest"
    printf 'old_toolchain\t%s\n' "$old_toolchain"
    printf 'new_toolchain\t%s\n' "$new_toolchain"
    printf 'phase\t%s\n' "$phase"
  } > "$next"
  chmod 0644 "$next"
  fsync_paths "$next"
  mv "$next" "$root/.regenerate.transaction"
  fsync_paths "$root"
}

scan_transaction_orphans() {
  local root="$1"
  local orphan
  orphan="$(find "$root" -maxdepth 1 -type d \
    \( -name '.regenerate-next.*' -o -name '.regenerate-backup.*' \) \
    -print -quit)"
  if [[ -n "$orphan" ]]; then
    echo "orphaned regeneration directory without transaction journal: $orphan" >&2
    return 1
  fi
}

recover_transaction() {
  local root="${1:-$HERE}"
  local journal="$root/.regenerate.transaction"
  if [[ ! -f "$journal" ]]; then
    scan_transaction_orphans "$root"
    return
  fi
  local version journal_token publish_name backup_name old_manifest new_manifest
  local old_toolchain new_toolchain phase
  version="$(journal_value "$journal" version)"
  journal_token="$(journal_value "$journal" run_token)"
  publish_name="$(journal_value "$journal" publish)"
  backup_name="$(journal_value "$journal" backup)"
  old_manifest="$(journal_value "$journal" old_manifest)"
  new_manifest="$(journal_value "$journal" new_manifest)"
  old_toolchain="$(journal_value "$journal" old_toolchain)"
  new_toolchain="$(journal_value "$journal" new_toolchain)"
  phase="$(journal_value "$journal" phase)"
  if [[ "$version" != 1 ]] \
    || [[ ! "$journal_token" =~ ^[0-9]+\.[0-9]+\.[0-9]+$ ]] \
    || [[ "$publish_name" != ".regenerate-next.$journal_token" ]] \
    || [[ "$backup_name" != ".regenerate-backup.$journal_token" ]] \
    || [[ ! "$old_manifest" =~ ^[0-9a-f]{64}$ ]] \
    || [[ ! "$new_manifest" =~ ^[0-9a-f]{64}$ ]] \
    || [[ "$old_toolchain" != none && ! "$old_toolchain" =~ ^[0-9a-f]{64}$ ]] \
    || [[ ! "$new_toolchain" =~ ^[0-9a-f]{64}$ ]] \
    || [[ "$phase" != prepared && "$phase" != publishing ]]; then
    echo "malformed regeneration transaction journal: $journal" >&2
    return 1
  fi
  local publish="$root/$publish_name"
  local backup="$root/$backup_name"
  local current_manifest=""
  local current_toolchain=""
  if [[ -f "$root/MANIFEST.sha256" ]]; then
    current_manifest="$(sha256_file "$root/MANIFEST.sha256")"
  fi
  if [[ -f "$root/TOOLCHAIN.sha256" ]]; then
    current_toolchain="$(sha256_file "$root/TOOLCHAIN.sha256")"
  fi

  # The manifest is the commit point and TOOLCHAIN.sha256 is moved first. A
  # complete new generation survives; every pre-commit/mixed state rolls back.
  if [[ "$current_manifest" == "$new_manifest" \
      && "$current_toolchain" == "$new_toolchain" ]] \
    && verify_manifest "$root" "$root/MANIFEST.sha256" >/dev/null 2>&1; then
    rm -rf "$publish" "$backup"
    rm -f "$journal"
    fsync_paths "$root"
    echo "completed cleanup of committed interrupted regeneration" >&2
    scan_transaction_orphans "$root"
    return
  fi

  if [[ ! -d "$publish" || -L "$publish" \
      || ! -d "$backup" || -L "$backup" ]]; then
    echo "interrupted regeneration has unsafe/missing transaction directories" >&2
    return 1
  fi

  local authoritative="$SCRATCH/recovery-manifest.$RUN_TOKEN.sha256"
  if [[ -f "$backup/MANIFEST.sha256" \
      && "$(sha256_file "$backup/MANIFEST.sha256")" == "$old_manifest" ]]; then
    cp "$backup/MANIFEST.sha256" "$authoritative"
  elif [[ -f "$root/MANIFEST.sha256" \
      && "$(sha256_file "$root/MANIFEST.sha256")" == "$old_manifest" ]]; then
    cp "$root/MANIFEST.sha256" "$authoritative"
  else
    echo "interrupted regeneration has no authoritative old manifest" >&2
    return 1
  fi
  read_manifest_inventory "$authoritative" "$INVENTORY_FILES"
  while IFS= read -r file; do
    if [[ -f "$backup/$file" ]]; then
      rm -f "$root/$file"
      mv "$backup/$file" "$root/$file"
    fi
  done < "$INVENTORY_FILES"
  if [[ -f "$backup/MANIFEST.sha256" ]]; then
    rm -f "$root/MANIFEST.sha256"
    mv "$backup/MANIFEST.sha256" "$root/MANIFEST.sha256"
  fi
  if [[ "$old_toolchain" == none ]]; then
    rm -f "$root/TOOLCHAIN.sha256"
  elif [[ -f "$backup/TOOLCHAIN.sha256" ]]; then
    rm -f "$root/TOOLCHAIN.sha256"
    mv "$backup/TOOLCHAIN.sha256" "$root/TOOLCHAIN.sha256"
  fi
  if [[ "$(sha256_file "$root/MANIFEST.sha256")" != "$old_manifest" ]]; then
    echo "rollback did not restore the authoritative manifest" >&2
    return 1
  fi
  if [[ "$old_toolchain" != none \
      && ( ! -f "$root/TOOLCHAIN.sha256" \
        || "$(sha256_file "$root/TOOLCHAIN.sha256")" != "$old_toolchain" ) ]]; then
    echo "rollback did not restore toolchain provenance" >&2
    return 1
  fi
  verify_manifest "$root" "$root/MANIFEST.sha256"
  fsync_inventory_files "$root"
  fsync_paths "$root/MANIFEST.sha256"
  [[ ! -f "$root/TOOLCHAIN.sha256" ]] || fsync_paths "$root/TOOLCHAIN.sha256"
  fsync_paths "$root"
  rm -rf "$publish" "$backup"
  rm -f "$journal"
  fsync_paths "$root"
  echo "rolled back interrupted regeneration from transaction journal" >&2
  scan_transaction_orphans "$root"
}

run_clean_env() {
  local library_path=()
  if [[ -d /opt/homebrew/lib ]]; then
    library_path=(LIBRARY_PATH=/opt/homebrew/lib)
  fi
  env -i \
    HOME="$SCRATCH/home" \
    CARGO_HOME="$SCRATCH/cargo-home" \
    PATH="$CONTROLLED_PATH" \
    LC_ALL=C \
    LANG=C \
    TMPDIR="$SCRATCH/tmp" \
    "${library_path[@]}" \
    "$@"
}

write_toolchain_provenance() {
  local manifest="$1"
  local output="$2"
  local version version_output
  : > "$output"
  for spec in \
    "cargo:$CARGO_BIN" \
    "trustc:$TRUSTC" \
    "jq:$JQ_BIN" \
    "python3:$PYTHON3_BIN" \
    "rustc_wrapper:$RUSTC_WRAPPER" \
    "regeneration_script:$HERE/regenerate.sh"
  do
    local label="${spec%%:*}"
    local path="${spec#*:}"
    case "$label" in
      cargo|trustc|jq|python3)
        if ! version_output="$(run_clean_env "$path" --version 2>&1)"; then
          echo "cannot fingerprint $label executable: $path" >&2
          printf '%s\n' "$version_output" >&2
          return 1
        fi
        version="${version_output%%$'\n'*}"
        version="${version//$'\t'/ }"
        if [[ -z "$version" ]]; then
          echo "$label --version returned no fingerprint text: $path" >&2
          return 1
        fi
        ;;
      *) version=repository-script ;;
    esac
    printf '%s\t%s\t%s\n' "$(sha256_file "$path")" "$label" "$version" >> "$output"
  done
  printf '%s\tcorpus_manifest\tMANIFEST.sha256\n' "$(sha256_file "$manifest")" >> "$output"
  chmod 0644 "$output"
}

resolve_lock_target() {
  [[ -e "$LOCK" || -L "$LOCK" ]] || return 1
  local resolved parent name
  resolved="$(cd "$LOCK" 2>/dev/null && pwd -P)" || return 1
  parent="$(dirname "$resolved")"
  name="$(basename "$resolved")"
  if [[ "$parent" != "$HERE" ]] \
    || { [[ "$name" != .regenerate.lock ]] \
      && [[ ! "$name" =~ ^\.regenerate-lock-owner\.[0-9]+\.[0-9]+\.[0-9]+$ ]]; }; then
    return 1
  fi
  printf '%s\n' "$resolved"
}

claim_target_is_managed() {
  local target="$1"
  [[ -n "$target" \
    && "$(dirname "$target")" == "$HERE" \
    && "$(basename "$target")" =~ ^\.regenerate-claim-owner\.[0-9]+\.[0-9]+\.[0-9]+$ ]]
}

remove_stale_claim_target_if_managed() {
  local target="$1"
  if claim_target_is_managed "$target"; then
    rm -rf "$target"
  fi
}

reap_dead_owner_orphans() {
  local artifact name pid removed=0
  while IFS= read -r artifact; do
    if [[ "$artifact" == "$LOCK_TARGET" \
        || "$artifact" == "$CLAIM_TARGET" \
        || "$artifact" == "$OWNER_INIT" ]]; then
      continue
    fi
    name="$(basename "$artifact")"
    if [[ "$name" =~ ^\.regenerate-(lock|claim)-owner\.[0-9]+\.[0-9]+\.[0-9]+$ ]]; then
      if [[ -L "$artifact" ]]; then
        rm -f "$artifact"
        removed=1
      elif [[ -d "$artifact" ]]; then
        if owner_is_live "$artifact"; then
          continue
        fi
        rm -rf "$artifact"
        removed=1
      else
        echo "malformed reserved regeneration owner artifact: $artifact" >&2
        return 1
      fi
    elif [[ "$name" =~ ^\.regenerate-owner-init\.([0-9]+)\.[0-9]+\.[0-9]+\.(lock|claim)$ ]]; then
      pid="${BASH_REMATCH[1]}"
      if [[ -d "$artifact" && ! -L "$artifact" ]] \
        && { owner_is_live "$artifact" || kill -0 "$pid" 2>/dev/null; }; then
        continue
      fi
      if [[ -L "$artifact" ]]; then
        rm -f "$artifact"
        removed=1
      elif [[ -d "$artifact" ]]; then
        rm -rf "$artifact"
        removed=1
      else
        echo "malformed reserved regeneration initializer artifact: $artifact" >&2
        return 1
      fi
    else
      echo "malformed reserved regeneration owner name: $artifact" >&2
      return 1
    fi
  done < <(
    find "$HERE" -mindepth 1 -maxdepth 1 \
      \( -name '.regenerate-lock-owner.*' \
      -o -name '.regenerate-claim-owner.*' \
      -o -name '.regenerate-owner-init.*' \) -print
  )
  if [[ "$removed" == 1 ]]; then
    fsync_paths "$HERE"
  fi
}

legacy_owner_is_live() {
  local owner_dir="$1"
  local pid
  pid="$(cat "$owner_dir/pid" 2>/dev/null || true)"
  [[ "$pid" =~ ^[0-9]+$ ]] && kill -0 "$pid" 2>/dev/null
}

remove_our_recovery_claim() {
  local claim_target="$1"
  local current_claim
  current_claim="$(cd "$LOCK/recovery-claim" 2>/dev/null && pwd -P || true)"
  if [[ -n "$current_claim" && "$current_claim" == "$claim_target" ]]; then
    rm -f "$LOCK/recovery-claim"
    fsync_paths "$LOCK_TARGET"
  fi
  rm -rf "$claim_target"
  if [[ "$CLAIM_TARGET" == "$claim_target" ]]; then
    CLAIM_TARGET=""
  fi
}

acquire_regeneration_lock() {
  local candidate="$HERE/.regenerate-lock-owner.$RUN_TOKEN"
  initialize_owner_directory "$candidate" lock
  if symlink_nofollow "$(basename "$candidate")" "$LOCK" 2>/dev/null; then
    fsync_paths "$HERE"
    LOCK_TARGET="$candidate"
    lock_owned=1
    recover_transaction "$HERE"
    reap_dead_owner_orphans
    return
  fi
  rm -rf "$candidate"
  LOCK_TARGET="$(resolve_lock_target)" || {
    echo "regeneration lock changed during acquisition; retry" >&2
    return 1
  }
  if owner_is_live "$LOCK_TARGET" || legacy_owner_is_live "$LOCK_TARGET"; then
    echo "another live regeneration owns $LOCK" >&2
    return 1
  fi

  # Claim recovery *inside* the existing lock target. The public lock path is
  # never renamed or removed, so a fresh contender cannot enter between stale
  # ownership detection and journal recovery.
  local claim_target="$HERE/.regenerate-claim-owner.$RUN_TOKEN"
  CLAIM_TARGET="$claim_target"
  initialize_owner_directory "$claim_target" claim
  if ! symlink_nofollow \
    "../$(basename "$claim_target")" "$LOCK/recovery-claim" 2>/dev/null; then
    local stale_claim_target=""
    stale_claim_target="$(cd "$LOCK/recovery-claim" 2>/dev/null && pwd -P || true)"
    if [[ -n "$stale_claim_target" ]] \
      && claim_target_is_managed "$stale_claim_target" \
      && owner_is_live "$stale_claim_target"; then
      rm -rf "$claim_target"
      CLAIM_TARGET=""
      echo "another live process is recovering the regeneration lock" >&2
      return 1
    fi
    local displaced="$LOCK/recovery-claim.stale.$RUN_TOKEN"
    if ! mv "$LOCK/recovery-claim" "$displaced" 2>/dev/null; then
      rm -rf "$claim_target"
      CLAIM_TARGET=""
      echo "another process raced regeneration recovery; retry" >&2
      return 1
    fi
    if ! symlink_nofollow \
      "../$(basename "$claim_target")" "$LOCK/recovery-claim" 2>/dev/null; then
      rm -f "$displaced"
      rm -rf "$claim_target"
      CLAIM_TARGET=""
      echo "another process raced regeneration recovery; retry" >&2
      return 1
    fi
    rm -f "$displaced"
    remove_stale_claim_target_if_managed "$stale_claim_target"
  fi
  fsync_paths "$LOCK_TARGET"

  # A protocol-compliant owner file is installed before the lock symlink, but
  # recheck after the claim to also fail safely around legacy/partial owners.
  if owner_is_live "$LOCK_TARGET" || legacy_owner_is_live "$LOCK_TARGET"; then
    remove_our_recovery_claim "$claim_target"
    echo "regeneration owner became live while recovery was being claimed" >&2
    return 1
  fi
  recover_transaction "$HERE"
  write_owner "$LOCK_TARGET"
  lock_owned=1
  rm -f "$LOCK_TARGET/pid"
  remove_our_recovery_claim "$claim_target"
  reap_dead_owner_orphans
}

cleanup() {
  local status=$?
  trap - EXIT
  if [[ "$committed" == 0 && -f "$TRANSACTION" ]]; then
    if ! recover_transaction "$HERE"; then
      echo "automatic regeneration rollback failed; transaction journal retained" >&2
      status=1
    fi
  else
    rm -rf "$PUBLISH" "$BACKUP"
  fi
  if [[ -n "$CLAIM_TARGET" ]]; then
    remove_our_recovery_claim "$CLAIM_TARGET"
  fi
  if [[ -n "$OWNER_INIT" ]]; then
    rm -rf "$OWNER_INIT"
    OWNER_INIT=""
  fi
  if [[ "$lock_owned" == 1 && -n "$LOCK_TARGET" ]] \
    && owner_token_is_ours "$LOCK_TARGET"; then
    if ! reap_dead_owner_orphans; then
      status=1
    fi
    local current_target
    current_target="$(resolve_lock_target 2>/dev/null || true)"
    if [[ "$current_target" == "$LOCK_TARGET" ]]; then
      if [[ -L "$LOCK" ]]; then
        rm -f "$LOCK"
        fsync_paths "$HERE"
        rm -rf "$LOCK_TARGET"
      else
        rm -rf "$LOCK"
        fsync_paths "$HERE"
      fi
    fi
  fi
  rm -rf "$SCRATCH"
  exit "$status"
}
trap cleanup EXIT
trap 'exit 130' HUP INT TERM

if ! acquire_regeneration_lock; then
  exit 1
fi

if [[ ! -x "$RUSTC_WRAPPER" ]]; then
  echo "missing executable regeneration wrapper: $RUSTC_WRAPPER" >&2
  exit 1
fi

# The checked-in filename/owner inventory is itself evidence. Reject hidden
# duplicates instead of silently letting BTreeMap::entry or the join choose a
# winner.
find "$HERE" -maxdepth 1 -name '*.json' -exec basename {} \; | sort > "$INVENTORY_FILES"
inventory_count="$(wc -l < "$INVENTORY_FILES" | tr -d ' ')"
if [[ "$inventory_count" != "$EXPECTED_INVENTORY" ]]; then
  echo "corpus contains $inventory_count JSON files, want $EXPECTED_INVENTORY" >&2
  exit 1
fi
: > "$INVENTORY_OWNERS"
while IFS= read -r file; do
  printf '%s\t%s\n' "$("$JQ_BIN" -er '.def_path' "$HERE/$file")" "$file" >> "$INVENTORY_OWNERS"
done < "$INVENTORY_FILES"
duplicate_owners="$(cut -f1 "$INVENTORY_OWNERS" | sort | uniq -d)"
if [[ -n "$duplicate_owners" ]]; then
  echo "duplicate corpus def_path owner(s):" >&2
  printf '%s\n' "$duplicate_owners" >&2
  exit 1
fi
if [[ ! -f "$HERE/MANIFEST.sha256" ]]; then
  echo "missing corpus generation manifest: $HERE/MANIFEST.sha256" >&2
  exit 1
fi
verify_manifest "$HERE" "$HERE/MANIFEST.sha256" "$INVENTORY_FILES"

assert_self_test_artifact_cleanup() {
  local artifact resolved
  if [[ -n "$CLAIM_TARGET" ]]; then
    echo "workflow self-test retained this process's recovery-claim target" >&2
    return 1
  fi
  if find "$LOCK_TARGET" -mindepth 1 -maxdepth 1 -name 'recovery-claim*' -print -quit \
    | grep -q .; then
    echo "workflow self-test retained an in-lock recovery claim" >&2
    return 1
  fi
  while IFS= read -r artifact; do
    if [[ "$(basename "$artifact")" == .regenerate-lock-owner.* ]]; then
      resolved="$(cd "$artifact" 2>/dev/null && pwd -P || true)"
      if [[ -n "$resolved" && "$resolved" == "$LOCK_TARGET" ]]; then
        continue
      fi
    fi
    echo "workflow self-test retained regeneration artifact: $artifact" >&2
    return 1
  done < <(
    find "$HERE" -mindepth 1 -maxdepth 1 \
      \( -name '.regenerate-lock-owner.*' \
      -o -name '.regenerate-claim-owner.*' \
      -o -name '.regenerate-owner-init.*' \
      -o -name '.regenerate-next.*' \
      -o -name '.regenerate-backup.*' \
      -o -name '.regenerate.transaction' \
      -o -name '.regenerate.transaction.next.*' \) -print
  )
}

workflow_self_test() {
  local fake_rustc="$SCRATCH/fake-rustc.sh"
  local failing_tool="$SCRATCH/failing-tool.sh"
  local wrapper_args="$SCRATCH/wrapper-args.txt"
  local env_probe="$SCRATCH/env-probe.txt"
  local fingerprint_error="$SCRATCH/fingerprint-error.txt"
  local mixed="$SCRATCH/mixed-generation"
  local recovery="$SCRATCH/interrupted-generation"
  local committed_recovery="$SCRATCH/committed-generation"
  local unsafe_recovery="$SCRATCH/unsafe-transaction-generation"
  local owner_recovery="$SCRATCH/owner-artifact-recovery"
  local lock_race="$SCRATCH/lock-interleaving"
  local nested_log="$SCRATCH/nested-lock.log"

  if "$0" --check-workflow >"$nested_log" 2>&1; then
    echo "concurrent regeneration unexpectedly acquired the live lock" >&2
    return 1
  fi
  if [[ "$(resolve_lock_target)" != "$LOCK_TARGET" ]] \
    || ! owner_token_is_ours "$LOCK_TARGET"; then
    echo "failed concurrent acquisition removed or replaced the live lock" >&2
    return 1
  fi
  cat > "$fake_rustc" <<'EOF'
#!/usr/bin/env bash
set -euo pipefail
printf '%s\n' "$@" > "$TRUST_WRAPPER_TEST_OUT"
EOF
  chmod +x "$fake_rustc"

  cat > "$failing_tool" <<'EOF'
#!/usr/bin/env bash
echo "forced version failure" >&2
exit 23
EOF
  chmod +x "$failing_tool"
  local real_trustc="$TRUSTC"
  TRUSTC="$failing_tool"
  if write_toolchain_provenance "$HERE/MANIFEST.sha256" "$SCRATCH/should-not-exist" \
    >/dev/null 2>"$fingerprint_error"; then
    TRUSTC="$real_trustc"
    echo "toolchain provenance accepted a failing executable" >&2
    return 1
  fi
  TRUSTC="$real_trustc"
  if ! grep -q "cannot fingerprint trustc executable" "$fingerprint_error" \
    || ! grep -q "forced version failure" "$fingerprint_error"; then
    echo "toolchain provenance hid a version-command failure" >&2
    return 1
  fi

  TRUST_WRAPPER_TEST_OUT="$wrapper_args" "$RUSTC_WRAPPER" \
    "$fake_rustc" --crate-name dependency -Ztrust-verify=off
  if grep -qx -- '-Ztrust-verify=on' "$wrapper_args"; then
    echo "wrapper enabled Trust verification for a dependency" >&2
    return 1
  fi
  TRUST_WRAPPER_TEST_OUT="$wrapper_args" "$RUSTC_WRAPPER" \
    "$fake_rustc" --crate-name extract_foldmemo -Ztrust-verify=off
  if [[ "$(tail -n 1 "$wrapper_args")" != "-Ztrust-verify=on" ]]; then
    echo "wrapper did not append target-only verification enable" >&2
    return 1
  fi

  local poison_cargo_home="$SCRATCH/poison-cargo-home"
  mkdir "$poison_cargo_home"
  printf '[build]\nrustc = "/definitely/poison-rustc"\n' \
    > "$poison_cargo_home/config.toml"
  CARGO_HOME="$poison_cargo_home" \
  CARGO_ENCODED_RUSTFLAGS=poison \
  CARGO_BUILD_RUSTC=poison \
  CARGO_BUILD_RUSTC_WRAPPER=poison \
  CARGO_BUILD_RUSTFLAGS=poison \
  CARGO_INCREMENTAL=poison \
  CARGO_PROFILE_RELEASE_LTO=poison \
  CARGO_TARGET_AARCH64_APPLE_DARWIN_LINKER=poison \
  CARGO_TARGET_X86_64_UNKNOWN_LINUX_GNU_RUSTFLAGS=poison \
  RUSTFLAGS=poison \
  RUSTDOC=poison \
  RUSTDOCFLAGS=poison \
  RUSTUP_TOOLCHAIN=poison \
  RUSTC_WORKSPACE_WRAPPER=poison \
  RUSTC_CODEGEN_BACKEND=poison \
  RUSTC_SYSROOT=poison \
  RUSTC_BOOTSTRAP=poison \
  TRUST_UPDATE_EXTRACTED_FIXTURES=poison \
  TRUST_DUMP_V2_VC=poison \
  DYLD_LIBRARY_PATH=poison \
  LD_LIBRARY_PATH=poison \
    run_clean_env /usr/bin/env > "$env_probe"
  for poisoned in \
    CARGO_ENCODED_RUSTFLAGS CARGO_BUILD_RUSTC CARGO_BUILD_RUSTC_WRAPPER \
    CARGO_BUILD_RUSTFLAGS CARGO_INCREMENTAL CARGO_PROFILE_RELEASE_LTO \
    CARGO_TARGET_AARCH64_APPLE_DARWIN_LINKER \
    CARGO_TARGET_X86_64_UNKNOWN_LINUX_GNU_RUSTFLAGS RUSTFLAGS RUSTDOC \
    RUSTDOCFLAGS RUSTUP_TOOLCHAIN RUSTC_WORKSPACE_WRAPPER \
    RUSTC_CODEGEN_BACKEND RUSTC_SYSROOT RUSTC_BOOTSTRAP \
    TRUST_UPDATE_EXTRACTED_FIXTURES TRUST_DUMP_V2_VC DYLD_LIBRARY_PATH \
    LD_LIBRARY_PATH
  do
    if grep -q "^${poisoned}=" "$env_probe"; then
      echo "clean environment leaked $poisoned" >&2
      return 1
    fi
  done
  if ! grep -qx "CARGO_HOME=$SCRATCH/cargo-home" "$env_probe" \
    || ! grep -qx "HOME=$SCRATCH/home" "$env_probe" \
    || [[ -e "$SCRATCH/cargo-home/config.toml" \
      || -e "$SCRATCH/cargo-home/config" ]]; then
    echo "clean environment admitted caller Cargo home/config state" >&2
    return 1
  fi

  mkdir "$mixed"
  while IFS= read -r file; do
    ln -s "$HERE/$file" "$mixed/$file"
  done < "$INVENTORY_FILES"
  cp "$HERE/MANIFEST.sha256" "$mixed/MANIFEST.sha256"
  verify_manifest "$mixed" "$mixed/MANIFEST.sha256"
  local changed
  changed="$(head -n 1 "$INVENTORY_FILES")"
  rm "$mixed/$changed"
  cp "$HERE/$changed" "$mixed/$changed"
  printf ' ' >> "$mixed/$changed"
  if verify_manifest "$mixed" "$mixed/MANIFEST.sha256" >/dev/null 2>&1; then
    echo "old manifest accepted a mixed/interrupted generation" >&2
    return 1
  fi

  mkdir "$recovery"
  while IFS= read -r file; do
    ln -s "$HERE/$file" "$recovery/$file"
  done < "$INVENTORY_FILES"
  cp "$HERE/MANIFEST.sha256" "$recovery/MANIFEST.sha256"
  local recovery_backup="$recovery/.regenerate-backup.$RUN_TOKEN"
  local recovery_publish="$recovery/.regenerate-next.$RUN_TOKEN"
  mkdir "$recovery_backup" "$recovery_publish"
  rm "$recovery/$changed"
  cp "$HERE/$changed" "$recovery_backup/$changed"
  cp "$HERE/$changed" "$recovery/$changed"
  printf ' ' >> "$recovery/$changed"
  local old_manifest_hash
  old_manifest_hash="$(sha256_file "$recovery/MANIFEST.sha256")"
  write_transaction \
    "$recovery" "$recovery_publish" "$recovery_backup" \
    "$old_manifest_hash" \
    1111111111111111111111111111111111111111111111111111111111111111 \
    none \
    2222222222222222222222222222222222222222222222222222222222222222 \
    publishing
  recover_transaction "$recovery"
  verify_manifest "$recovery" "$recovery/MANIFEST.sha256"

  # A commit-point manifest plus the matching toolchain ledger must survive
  # recovery even though lock acquisition has not populated INVENTORY_FILES.
  mkdir "$committed_recovery"
  while IFS= read -r file; do
    ln -s "$HERE/$file" "$committed_recovery/$file"
  done < "$INVENTORY_FILES"
  cp "$HERE/MANIFEST.sha256" "$committed_recovery/MANIFEST.sha256"
  cp "$HERE/TOOLCHAIN.sha256" "$committed_recovery/TOOLCHAIN.sha256"
  local committed_publish="$committed_recovery/.regenerate-next.$RUN_TOKEN"
  local committed_backup="$committed_recovery/.regenerate-backup.$RUN_TOKEN"
  mkdir "$committed_publish" "$committed_backup"
  write_transaction \
    "$committed_recovery" "$committed_publish" "$committed_backup" \
    3333333333333333333333333333333333333333333333333333333333333333 \
    "$(sha256_file "$committed_recovery/MANIFEST.sha256")" \
    none \
    "$(sha256_file "$committed_recovery/TOOLCHAIN.sha256")" \
    publishing
  : > "$INVENTORY_FILES"
  recover_transaction "$committed_recovery"
  if [[ -e "$committed_recovery/.regenerate.transaction" \
      || -e "$committed_publish" \
      || -e "$committed_backup" ]]; then
    echo "committed transaction recovery did not retain and clean the new generation" >&2
    return 1
  fi
  find "$HERE" -maxdepth 1 -name '*.json' -exec basename {} \; \
    | sort > "$INVENTORY_FILES"

  # Journal-selected paths are never trusted as filesystem paths until both
  # manifest entries and transaction directories pass confinement checks.
  local unsafe_manifest="$SCRATCH/unsafe-manifest.sha256"
  local unsafe_listed="$SCRATCH/unsafe-manifest-files.txt"
  local first_hash first_file
  IFS=$'\t' read -r first_hash first_file < "$HERE/MANIFEST.sha256"
  {
    printf '%s\t../escape.json\n' "$first_hash"
    tail -n +2 "$HERE/MANIFEST.sha256"
  } > "$unsafe_manifest"
  if read_manifest_inventory "$unsafe_manifest" "$unsafe_listed" >/dev/null 2>&1; then
    echo "manifest inventory accepted a parent-directory traversal" >&2
    return 1
  fi

  mkdir "$unsafe_recovery"
  cp "$HERE/MANIFEST.sha256" "$unsafe_recovery/MANIFEST.sha256"
  local unsafe_publish="$unsafe_recovery/.regenerate-next.$RUN_TOKEN"
  local unsafe_backup="$unsafe_recovery/.regenerate-backup.$RUN_TOKEN"
  local external_backup="$SCRATCH/external-transaction-target"
  mkdir "$unsafe_publish" "$external_backup"
  printf 'must survive transaction recovery\n' > "$external_backup/sentinel"
  ln -s "$external_backup" "$unsafe_backup"
  write_transaction \
    "$unsafe_recovery" "$unsafe_publish" "$unsafe_backup" \
    "$(sha256_file "$unsafe_recovery/MANIFEST.sha256")" \
    4444444444444444444444444444444444444444444444444444444444444444 \
    none \
    5555555555555555555555555555555555555555555555555555555555555555 \
    publishing
  if recover_transaction "$unsafe_recovery" >/dev/null 2>&1; then
    echo "transaction recovery accepted a symlinked transaction directory" >&2
    return 1
  fi
  if [[ ! -f "$external_backup/sentinel" ]]; then
    echo "transaction recovery followed an external transaction directory" >&2
    return 1
  fi

  # Owner directories become visible only after initialization. Once a
  # process owns the public lock it may reap complete dead/unreferenced owners
  # and dead crash-only initializers, but never a live contender.
  mkdir "$owner_recovery"
  if ! (
    HERE="$owner_recovery"
    LOCK="$HERE/.regenerate.lock"
    LOCK_TARGET="$HERE/.regenerate-lock-owner.$RUN_TOKEN"
    CLAIM_TARGET=""
    OWNER_INIT=""
    initialize_owner_directory "$LOCK_TARGET" lock
    symlink_nofollow "$(basename "$LOCK_TARGET")" "$LOCK"
    dead_lock="$HERE/.regenerate-lock-owner.999999999.1.1"
    dead_claim="$HERE/.regenerate-claim-owner.999999999.1.2"
    dead_init="$HERE/.regenerate-owner-init.999999999.1.3.claim"
    live_contender="$HERE/.regenerate-lock-owner.999999998.1.1"
    mkdir "$dead_lock" "$dead_claim" "$dead_init" "$live_contender"
    printf '999999999\tdead\tdead process identity\n' > "$dead_lock/owner"
    printf '999999999\tdead\tdead process identity\n' > "$dead_claim/owner"
    write_owner "$live_contender"
    reap_dead_owner_orphans
    [[ -d "$LOCK_TARGET" \
      && -d "$live_contender" \
      && ! -e "$dead_lock" \
      && ! -e "$dead_claim" \
      && ! -e "$dead_init" ]]
  ); then
    echo "owner-artifact recovery removed a live owner or retained a dead orphan" >&2
    return 1
  fi

  mkdir "$recovery/.regenerate-next.orphan"
  if scan_transaction_orphans "$recovery" >/dev/null 2>&1; then
    echo "orphan scan accepted an owner-independent publish orphan" >&2
    return 1
  fi
  rm -rf "$recovery/.regenerate-next.orphan"

  # Forced stale-takeover interleaving: the recovery claim is installed while
  # the public lock remains continuously present. A preinitialized contender
  # cannot acquire it, and PID reuse is rejected by the recorded start identity.
  mkdir "$lock_race"
  local race_owner="$lock_race/.regenerate-lock-owner.stale"
  local race_claim="$lock_race/.regenerate-claim-owner.test"
  local race_contender="$lock_race/.regenerate-lock-owner.contender"
  local race_lock="$lock_race/.regenerate.lock"
  local unmanaged_claim="$SCRATCH/unmanaged-recovery-claim-target"
  local directory_lock="$lock_race/directory-lock"
  mkdir "$race_owner" "$race_claim" "$race_contender"
  mkdir "$directory_lock"
  if symlink_nofollow contender "$directory_lock" 2>/dev/null \
    || find "$directory_lock" -mindepth 1 -print -quit | grep -q .; then
    echo "exact symlink creation followed an existing directory" >&2
    return 1
  fi
  mkdir "$unmanaged_claim"
  printf 'must survive stale-claim cleanup\n' > "$unmanaged_claim/sentinel"
  remove_stale_claim_target_if_managed "$unmanaged_claim"
  if [[ ! -f "$unmanaged_claim/sentinel" ]]; then
    echo "stale-claim cleanup followed an unmanaged target" >&2
    return 1
  fi
  symlink_nofollow "$unmanaged_claim" "$lock_race/unmanaged.lock"
  if (LOCK="$lock_race/unmanaged.lock"; resolve_lock_target >/dev/null 2>&1); then
    echo "lock resolution accepted an unmanaged target" >&2
    return 1
  fi
  printf '%s\tstale-token\twrong process start identity\n' "$$" > "$race_owner/owner"
  if owner_is_live "$race_owner"; then
    echo "PID reuse/start-identity adversary was treated as a live owner" >&2
    return 1
  fi
  write_owner "$race_claim"
  write_owner "$race_contender"
  symlink_nofollow "$(basename "$race_owner")" "$race_lock"
  symlink_nofollow "../$(basename "$race_claim")" "$race_lock/recovery-claim"
  if symlink_nofollow "$(basename "$race_contender")" "$race_lock" 2>/dev/null; then
    echo "contender acquired the public lock during stale recovery" >&2
    return 1
  fi
  write_owner "$race_owner"
  if [[ "$(cd "$race_lock" && pwd -P)" != "$(cd "$race_owner" && pwd -P)" ]] \
    || ! owner_token_is_ours "$race_owner"; then
    echo "stale recovery replaced the public lock instead of its owner" >&2
    return 1
  fi
  rm -f "$race_lock/recovery-claim"

  reap_dead_owner_orphans
  assert_self_test_artifact_cleanup

  echo "regeneration workflow self-test passed (atomic lock, transaction recovery, allowlisted env, wrapper, manifest)"
}

if [[ "${1:-}" == "--check-workflow" ]]; then
  workflow_self_test
  exit 0
fi
if [[ "$#" != 0 ]]; then
  echo "usage: $0 [--check-workflow]" >&2
  exit 2
fi
if [[ ! -x "$TRUSTC" ]]; then
  echo "missing executable trustc: $TRUSTC (build stage1 first or set TRUSTC)" >&2
  exit 1
fi
TRUSTC="$(cd "$(dirname "$TRUSTC")" && pwd -P)/$(basename "$TRUSTC")"

# Snapshot every executable/script identity before extraction. Recompute after
# Cargo returns so replacing a tool through a symlink or in-place update cannot
# produce dumps whose recorded provenance names a different binary.
TOOLCHAIN_BEFORE="$SCRATCH/toolchain-before.sha256"
TOOLCHAIN_AFTER="$SCRATCH/toolchain-after.sha256"
write_toolchain_provenance "$HERE/MANIFEST.sha256" "$TOOLCHAIN_BEFORE"

cp -R "$EXTRACT" "$SCRATCH/extract"
(cd "$SCRATCH/extract" && \
  run_clean_env \
    CARGO_TARGET_DIR="$SCRATCH/target" \
    RUSTC="$TRUSTC" \
    RUSTC_WRAPPER="$RUSTC_WRAPPER" \
    RUSTFLAGS="-Ztrust-verify=off" \
  "$CARGO_BIN" rustc --locked --offline --lib -- \
    \
    -Ztrust-dump=mir-only:"$SCRATCH/dump" \
    -Ztrust-policy=advisory)
write_toolchain_provenance "$HERE/MANIFEST.sha256" "$TOOLCHAIN_AFTER"
if ! cmp -s "$TOOLCHAIN_BEFORE" "$TOOLCHAIN_AFTER"; then
  echo "regeneration tool identity changed while extraction was running" >&2
  diff -u "$TOOLCHAIN_BEFORE" "$TOOLCHAIN_AFTER" >&2 || true
  exit 1
fi

# Current trustc dumps use content-addressed filenames. Build one deterministic
# owner-to-file index, then join the corpus's existing inventory by exact
# `VerifiableFunction.def_path`. Require a UNIQUE owner match and stage every
# replacement before touching the checked-in corpus, so a partial/ambiguous
# extraction cannot leave a half-regenerated fixture directory.
MAP="$SCRATCH/dump-map.tsv"
"$JQ_BIN" -r '[.def_path, input_filename] | @tsv' "$SCRATCH"/dump/*.json > "$MAP"
mkdir "$PUBLISH"
while IFS=$'\t' read -r owner f; do
  matches="$(awk -F '\t' -v owner="$owner" '$1 == owner { print $2 }' "$MAP")"
  match_count="$(printf '%s\n' "$matches" | awk 'NF { n += 1 } END { print n + 0 }')"
  if [[ "$match_count" != 1 ]]; then
    echo "expected exactly one regenerated dump for $owner, found $match_count" >&2
    exit 1
  fi
  cp "$matches" "$PUBLISH/$f"
done < "$INVENTORY_OWNERS"

next_count="$(find "$PUBLISH" -maxdepth 1 -name '*.json' | wc -l | tr -d ' ')"
if [[ "$next_count" != "$inventory_count" ]]; then
  echo "staged corpus count $next_count differs from inventory $inventory_count" >&2
  exit 1
fi
write_manifest "$PUBLISH" "$PUBLISH/MANIFEST.sha256"
verify_manifest "$PUBLISH" "$PUBLISH/MANIFEST.sha256" "$INVENTORY_FILES"
write_toolchain_provenance "$PUBLISH/MANIFEST.sha256" "$PUBLISH/TOOLCHAIN.sha256"
fsync_inventory_files "$PUBLISH"
fsync_paths "$PUBLISH/MANIFEST.sha256" "$PUBLISH/TOOLCHAIN.sha256" "$PUBLISH"

# Publish each JSON by a same-filesystem atomic rename. Keep the OLD manifest
# authoritative throughout the file phase; any concurrent reader either sees
# and validates a complete old generation, or rejects a mixed/SIGKILL state.
# The final manifest rename is the commit point.
mkdir "$BACKUP"
old_manifest_hash="$(sha256_file "$HERE/MANIFEST.sha256")"
new_manifest_hash="$(sha256_file "$PUBLISH/MANIFEST.sha256")"
old_toolchain_hash=none
if [[ -f "$HERE/TOOLCHAIN.sha256" ]]; then
  old_toolchain_hash="$(sha256_file "$HERE/TOOLCHAIN.sha256")"
fi
new_toolchain_hash="$(sha256_file "$PUBLISH/TOOLCHAIN.sha256")"
write_transaction \
  "$HERE" "$PUBLISH" "$BACKUP" \
  "$old_manifest_hash" "$new_manifest_hash" \
  "$old_toolchain_hash" "$new_toolchain_hash" publishing
while IFS= read -r file; do
  mv "$HERE/$file" "$BACKUP/$file"
  mv "$PUBLISH/$file" "$HERE/$file"
done < "$INVENTORY_FILES"
if [[ -f "$HERE/TOOLCHAIN.sha256" ]]; then
  mv "$HERE/TOOLCHAIN.sha256" "$BACKUP/TOOLCHAIN.sha256"
fi
mv "$PUBLISH/TOOLCHAIN.sha256" "$HERE/TOOLCHAIN.sha256"
fsync_paths "$HERE/TOOLCHAIN.sha256" "$HERE" "$BACKUP" "$PUBLISH"
mv "$HERE/MANIFEST.sha256" "$BACKUP/MANIFEST.sha256"
mv "$PUBLISH/MANIFEST.sha256" "$HERE/MANIFEST.sha256"
fsync_paths "$HERE/MANIFEST.sha256" "$HERE" "$BACKUP"
verify_manifest "$HERE" "$HERE/MANIFEST.sha256" "$INVENTORY_FILES"
if [[ "$(sha256_file "$HERE/TOOLCHAIN.sha256")" != "$new_toolchain_hash" ]]; then
  echo "published toolchain provenance hash drift" >&2
  exit 1
fi
rm -rf "$PUBLISH" "$BACKUP"
rm -f "$TRANSACTION"
fsync_paths "$HERE"
committed=1
echo "regenerated $inventory_count expr-fold-corpus dumps"
