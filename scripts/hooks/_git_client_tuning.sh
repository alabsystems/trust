#!/usr/bin/env bash
# Git client tuning for a Trust clone: what makes `git status` fast on a
# 270,000-file superproject and its first-party submodules, and what stays off.
#
# Author: Andrew Yates. Copyright 2026 Andrew Yates. License: Apache-2.0 OR MIT.
#
# A library, not a command. Both hook installers (scripts/install-git-hooks.sh,
# scripts/install-pin-hook.sh) source it, because they are where a clone's local
# state is set. The record of the choice and its measurements is
# docs/DECISION_QUEUE.md GIT-CLIENT-TUNING-1 (Continuum EW-13).
#
# It also holds the installers' one registry step (trust_registry_prefetch; Continuum
# EW-2): not git tuning, but the same "prepare this clone" moment.
#
# WHAT IT SETS: what the clone declares, as data, in scripts/git-clone.gitconfig
# (read with `git config --file`, from the top argument of trust_git_tuning_apply
# and trust_git_tuning_status; that file says what each entry means). Missing or
# unreadable, nothing is tuned, and the apply and the report say so. Each key is
# set to true. The declaration as committed names:
#   core.untrackedCache  the untracked-file scan reuses a directory's earlier
#                        result while that directory's mtime is unchanged
#   feature.manyFiles    index format 4 (prefix-compressed paths), index.skipHash
#                        (no trailing checksum to compute on every write), and
#                        core.untrackedCache
# The superproject's keys go to the clone's own config (`git config --local`),
# which every linked worktree of the clone reads, so a `git worktree add`
# worktree's superproject needs no step. A submodule is a repository of its own
# whose git never reads the superproject's config. Each populated submodule of
# the current worktree gets the submodule keys (core.untrackedCache alone), in
# its own config: first-party/trust-cg's --attest gate (its
# scripts/host_boundary.py, LOCAL_DATA_KEYS) refuses any key of its
# repository's config that it does not list, and feature.manyFiles is not
# listed. An index keeps its format until something rewrites it in another: the
# current worktree's index is moved to the declared tuning.indexVersion (4)
# wherever feature.manyFiles is in effect, and an index git creates later under
# feature.manyFiles starts at 4.
#
# WHAT IT NEVER SETS: the declaration's tuning.never keys (core.fsmonitor), and
# core.hooksPath and core.sshCommand, which the installers set themselves and
# which are not tuning; a declaration naming one of these to be set is refused,
# entry by entry, and the rest applies. The built-in fsmonitor daemon was
# correct on macOS (submodules, the first-party/trust -> .. symlink and worktree
# removal were tested) and fastest. But the release completion gate
# (scripts/two_language_completion_gate.py), G2's checker
# (scripts/completion_gates/check_g2_lean_input.py) and
# scripts/recreate_bootstrap.py refuse a checkout whose own configuration names
# it, because a checker's read-only git would start a program (the daemon, or
# the hook the value names) whenever it reads the index. The gates already run
# their own git with core.fsmonitor=false; what they refuse is the checkout's
# setting. A repository-scope value of a tuning.never key is named in the
# report, so that refusal is not a surprise. recreate_bootstrap.py accepts only
# `false` or an empty value, so no, off and 0, which git reads as false, are
# named too.
#
# RULES
#   * A key already set in any scope (system, global, local, worktree or the
#     command line) is kept: it is somebody's choice, and is reported. A git
#     that cannot say which scope a key comes from (`git config --show-scope`,
#     git 2.26) could not keep that choice, so it tunes nothing.
#   * core.untrackedCache is only correct where a directory's mtime moves when
#     an entry in it changes. Git's own self-test (`git update-index
#     --test-untracked-cache`, about 6 s) runs once per filesystem per install,
#     wherever a key that turns the cache on (core.untrackedCache,
#     feature.manyFiles) is to be written or the cache is already in effect.
#     Where it fails, neither of those keys is written there (any other declared
#     key still is), and a cache already in effect there is warned about. The
#     keys are clone-wide, so a linked worktree on another filesystem (a network
#     or FUSE mount) is checked only when an install runs in it.
#   * An explicit index.version other than the declared one is kept, and that
#     index is not converted.
#   * An index another process holds (index.lock) is not converted. It keeps its
#     format, which is slower and never wrong; installing again converts it.
#   * Tuning is never a failure: nothing here makes an install exit nonzero. A
#     repository it cannot read, and a submodule list git cannot produce, are
#     named and skipped.
#   * The report writes nothing and takes no lock: it reads the index format
#     from the index file's header, not through `git update-index`.
#   * bash 3.2 (macOS /bin/bash) under `set -euo pipefail`: no arrays, every
#     command that may fail is tested.
#
# aterm converges every clone it manages to the same declaration on each sync
# pass, reading the default branch's copy as data and running nothing from the
# clone (its docs/DESIGN-init-github-2026-10-20.md); this library is what an
# install does in the checkout it runs in.
#
# Usage (from a caller that has already cd'd to the worktree top):
#   . scripts/hooks/_git_client_tuning.sh
#   trust_git_tuning_apply  "$PWD"   # write the keys, convert the index
#   trust_git_tuning_status "$PWD"   # report; writes nothing

TRUST_GIT_TUNING_SCOPE=""
TRUST_GIT_TUNING_VALUE=""

# _trust_git_tuning_key_ok KEY: whether KEY is a plain `section.name` key.
_trust_git_tuning_key_ok() {
  local re='^[A-Za-z][A-Za-z0-9-]*\.[A-Za-z][A-Za-z0-9-]*$'
  [[ "$1" =~ $re ]]
}

# _trust_git_tuning_lower WORDS: WORDS in lower case (git config key names are
# case-insensitive).
_trust_git_tuning_lower() {
  printf '%s' "$1" | tr '[:upper:]' '[:lower:]'
}

# _trust_git_tuning_declaration TOP PREFIX: read TOP's
# scripts/git-clone.gitconfig into the caller's locals decl_super, decl_sub,
# decl_index and decl_never (bash's dynamic scope; space-separated keys, or the
# index format), printing PREFIX and a line for each entry it refuses. Returns 1,
# having said why, when TOP has no declaration git can read: then nothing is
# tuned.
_trust_git_tuning_declaration() {
  local file="$1/scripts/git-clone.gitconfig" prefix="$2" out record name value lowered rc=0
  local never_lowered=" "
  decl_super=""
  decl_sub=""
  decl_index=""
  decl_never=""
  if [ ! -f "$file" ]; then
    echo "${prefix}git tuning: no scripts/git-clone.gitconfig in this checkout, which declares the"
    echo "${prefix}            tuning; nothing is tuned"
    return 1
  fi
  out="$(git config --file "$file" --no-includes --list 2>/dev/null)" || rc=$?
  if [ "$rc" -ne 0 ]; then
    echo "${prefix}git tuning: cannot read scripts/git-clone.gitconfig (git config exited $rc);"
    echo "${prefix}            nothing is tuned"
    return 1
  fi
  # The never keys first: one named there is refused wherever else it appears.
  while IFS= read -r record; do
    case "$record" in
      tuning.never=*)
        value="${record#tuning.never=}"
        if _trust_git_tuning_key_ok "$value"; then
          lowered="$(_trust_git_tuning_lower "$value")"
          case "$never_lowered" in
            *" $lowered "*) ;;
            *)
              never_lowered="$never_lowered$lowered "
              decl_never="${decl_never:+$decl_never }$value"
              ;;
          esac
        else
          echo "${prefix}git tuning: scripts/git-clone.gitconfig: tuning.never=$value is not a section.name key; ignored"
        fi
        ;;
    esac
  done <<<"$out"
  while IFS= read -r record; do
    [ -n "$record" ] || continue
    name="${record%%=*}"
    case "$record" in *=*) value="${record#*=}" ;; *) value="" ;; esac
    case "$name" in
      tuning.never) continue ;;
      tuning.superproject|tuning.submodule)
        lowered="$(_trust_git_tuning_lower "$value")"
        if ! _trust_git_tuning_key_ok "$value"; then
          echo "${prefix}git tuning: scripts/git-clone.gitconfig: $name=$value is not a section.name key; not set"
          continue
        fi
        case "$lowered" in
          core.hookspath|core.sshcommand)
            echo "${prefix}git tuning: scripts/git-clone.gitconfig: $name=$value is the installers' own, not"
            echo "${prefix}            tuning; not set"
            continue
            ;;
        esac
        case "$never_lowered" in
          *" $lowered "*)
            echo "${prefix}git tuning: scripts/git-clone.gitconfig: $name=$value is also declared never set; not set"
            continue
            ;;
        esac
        if [ "$name" = tuning.superproject ]; then
          case " $(_trust_git_tuning_lower "$decl_super") " in
            *" $lowered "*) ;;
            *) decl_super="${decl_super:+$decl_super }$value" ;;
          esac
        else
          case " $(_trust_git_tuning_lower "$decl_sub") " in
            *" $lowered "*) ;;
            *) decl_sub="${decl_sub:+$decl_sub }$value" ;;
          esac
        fi
        ;;
      tuning.indexversion)
        # git's own rule for a repeated key: the last one wins.
        case "$value" in
          2|3|4) decl_index="$value" ;;
          *)
            decl_index=""
            echo "${prefix}git tuning: scripts/git-clone.gitconfig: tuning.indexVersion=$value is not 2, 3 or 4;"
            echo "${prefix}            no index is converted"
            ;;
        esac
        ;;
      *)
        echo "${prefix}git tuning: scripts/git-clone.gitconfig: $name is not a tuning entry; ignored"
        ;;
    esac
  done <<<"$out"
  return 0
}

# _trust_git_tuning_repos TOP: TOP, then each populated submodule under it
# (nested ones too), one physical path per line. A last line `error: <why>`
# says git could not list them all. The tracked first-party/trust symlink is
# not a gitlink, so it is never visited.
_trust_git_tuning_repos() {
  local out line last="" rc=0
  printf '%s\n' "$1"
  out="$(git -C "$1" submodule foreach --quiet --recursive 'pwd -P' 2>&1)" || rc=$?
  while IFS= read -r line; do
    case "$line" in
      /*) printf '%s\n' "$line" ;;
      "") ;;
      *) last="$line" ;;
    esac
  done <<<"$out"
  if [ "$rc" -ne 0 ]; then
    printf 'error: %s\n' "${last:-git submodule foreach exited $rc}"
  fi
}

# _trust_git_tuning_label TOP REPO: REPO relative to TOP, or "superproject".
_trust_git_tuning_label() {
  if [ "$2" = "$1" ]; then printf 'superproject\n'; else printf '%s\n' "${2#"$1"/}"; fi
}

# _trust_git_tuning_keys TOP REPO: the declared keys REPO gets (the caller's
# decl_super for the superproject, decl_sub for a submodule).
_trust_git_tuning_keys() {
  if [ "$2" = "$1" ]; then
    printf '%s\n' "$decl_super"
  else
    printf '%s\n' "$decl_sub"
  fi
}

# _trust_git_tuning_cache_key KEY: whether KEY turns the untracked cache on.
_trust_git_tuning_cache_key() {
  case "$(_trust_git_tuning_lower "$1")" in
    core.untrackedcache|feature.manyfiles) return 0 ;;
    *) return 1 ;;
  esac
}

# _trust_git_tuning_device PATH: the filesystem PATH is on (GNU stat, then BSD).
_trust_git_tuning_device() {
  stat -c %d "$1" 2>/dev/null || stat -f %d "$1" 2>/dev/null || printf 'unknown:%s\n' "$1"
}

# _trust_git_tuning_scopes TOP: 0 when this git reports config scopes; else
# prints why not and returns 1.
_trust_git_tuning_scopes() {
  local rc=0
  git -C "$1" config --show-scope --list >/dev/null 2>&1 || rc=$?
  case "$rc" in
    0) return 0 ;;
    129)
      echo "git tuning: this git ($(git --version 2>/dev/null || echo 'version unknown')) cannot say which"
      echo "  config a setting comes from (git config --show-scope, git 2.26), so a choice made"
      echo "  in another scope could not be kept; nothing is tuned with it"
      ;;
    *) echo "git tuning: cannot read this clone's config (git config exited $rc); nothing is tuned" ;;
  esac
  return 1
}

# _trust_git_tuning_read REPO KEY: sets TRUST_GIT_TUNING_SCOPE and
# TRUST_GIT_TUNING_VALUE to the scope KEY comes from and its value. Returns 0
# when KEY is set, 1 when it is unset, 2 when REPO's config cannot be read.
_trust_git_tuning_read() {
  local out rc=0
  TRUST_GIT_TUNING_SCOPE=""
  TRUST_GIT_TUNING_VALUE=""
  out="$(git -C "$1" config --show-scope --get "$2" 2>/dev/null)" || rc=$?
  case "$rc" in
    0)
      TRUST_GIT_TUNING_SCOPE="${out%%$'\t'*}"
      TRUST_GIT_TUNING_VALUE="${out#*$'\t'}"
      return 0
      ;;
    1) return 1 ;;
    *) return 2 ;;
  esac
}

# _trust_git_tuning_cache_on REPO: whether REPO's git uses the untracked cache.
_trust_git_tuning_cache_on() {
  local value
  value="$(git -C "$1" config --get core.untrackedCache 2>/dev/null || true)"
  case "$(printf '%s' "$value" | tr '[:upper:]' '[:lower:]')" in
    true|yes|on|1) return 0 ;;
    "") ;;
    *) return 1 ;;
  esac
  [ "$(git -C "$1" config --type=bool --get feature.manyFiles 2>/dev/null || true)" = true ]
}

# _trust_git_tuning_index_version REPO: the format in the header of REPO's
# index, or nothing when it has no index file. Reading the file takes no lock
# and writes nothing; `git update-index --show-index-version` does both (it adds
# an untracked cache to an index that lacks one) and needs git 2.43.
_trust_git_tuning_index_version() {
  local path bytes
  path="$(git -C "$1" rev-parse --git-path index 2>/dev/null)" || return 0
  case "$path" in /*) ;; *) path="$1/$path" ;; esac
  [ -f "$path" ] || return 0
  bytes="$(od -An -tu1 -N8 "$path" 2>/dev/null | tr -s ' \n' '  ')" || return 0
  # shellcheck disable=SC2086 # eight decimal byte values, split on purpose
  set -- $bytes
  if [ "$#" -eq 8 ] && [ "$1 $2 $3 $4 $5 $6 $7" = "68 73 82 67 0 0 0" ]; then
    printf '%s\n' "$8"
  fi
}

# _trust_git_tuning_never_notes TOP: name each repository-scope value of a
# declared tuning.never key (core.fsmonitor) that a gate refuses: every value
# but `false` or an empty one (git reads a key with no value as true, and no,
# off and 0 as false, but recreate_bootstrap.py accepts only false or empty).
_trust_git_tuning_never_notes() {
  local top="$1" repo label record scope rest value lowered key pattern
  for key in $decl_never; do
    # --get-regexp matches the canonical, lower-case key name.
    pattern="^$(_trust_git_tuning_lower "$key" | sed 's/\./\\./g')\$"
    while IFS= read -r repo; do
      case "$repo" in /*) ;; *) continue ;; esac
      label="$(_trust_git_tuning_label "$top" "$repo")"
      while IFS= read -r record; do
        [ -n "$record" ] || continue
        scope="${record%%$'\t'*}"
        rest="${record#*$'\t'}"
        case "$scope" in local|worktree) ;; *) continue ;; esac
        case "$rest" in
          *" "*)
            value="${rest#* }"
            lowered="$(_trust_git_tuning_lower "$value")"
            ;;
          *)
            value="(no value, which git reads as true)"
            lowered=true
            ;;
        esac
        case "$lowered" in
          ""|false) continue ;;
          no|off|0)
            echo "  git tuning: $label: NOTE $key $value is set in $scope config; git reads"
            echo "              it as false, but recreate_bootstrap.py accepts only false and refuses"
            echo "              this checkout while it is (docs/DECISION_QUEUE.md GIT-CLIENT-TUNING-1)"
            ;;
          *)
            echo "  git tuning: $label: NOTE $key $value is set in $scope config;"
            echo "              the completion gate, G2's checker and recreate_bootstrap.py refuse"
            echo "              this checkout while it is (docs/DECISION_QUEUE.md GIT-CLIENT-TUNING-1)"
            ;;
        esac
      done < <(git -C "$repo" config --show-scope --get-regexp "$pattern" 2>/dev/null || true)
    done < <(_trust_git_tuning_repos "$top")
  done
}

# trust_git_tuning_apply TOP
trust_git_tuning_apply() {
  local top repo label keys key rc needed cache_needed rest unreadable device result
  local tested_ok="" tested_bad="" explicit version why
  local decl_super decl_sub decl_index decl_never
  top="$(cd -P "$1" 2>/dev/null && pwd -P)" || {
    echo "  git tuning: cannot enter $1; nothing tuned"
    return 0
  }
  _trust_git_tuning_declaration "$top" "  " || return 0
  if ! why="$(_trust_git_tuning_scopes "$top")"; then
    printf '%s\n' "$why" | sed 's/^/  /'
    return 0
  fi
  while IFS= read -r repo; do
    case "$repo" in
      /*) ;;
      error:*)
        echo "  git tuning: cannot list every submodule (${repo#error: });"
        echo "              a submodule not named here is not tuned"
        continue
        ;;
      *) continue ;;
    esac
    label="$(_trust_git_tuning_label "$top" "$repo")"
    if ! git -C "$repo" rev-parse --git-dir >/dev/null 2>&1; then
      echo "  git tuning: $label: not a readable repository; skipped"
      continue
    fi
    keys="$(_trust_git_tuning_keys "$top" "$repo")"

    needed=""
    unreadable=""
    for key in $keys; do
      rc=0
      _trust_git_tuning_read "$repo" "$key" || rc=$?
      case "$rc" in
        0)
          if [ "$TRUST_GIT_TUNING_SCOPE" = local ] && [ "$TRUST_GIT_TUNING_VALUE" = true ]; then
            echo "  git tuning: $label: $key already true"
          else
            echo "  git tuning: $label: $key=$TRUST_GIT_TUNING_VALUE is set in $TRUST_GIT_TUNING_SCOPE config; it is kept"
          fi
          ;;
        1) needed="$needed $key" ;;
        *) unreadable=1 ;;
      esac
    done
    if [ -n "$unreadable" ]; then
      echo "  git tuning: $label: cannot read its config; skipped"
      continue
    fi

    # The self-test, once per filesystem, wherever the cache is about to be or
    # already is in effect.
    cache_needed=""
    for key in $needed; do
      if _trust_git_tuning_cache_key "$key"; then cache_needed="$cache_needed $key"; fi
    done
    if [ -n "$cache_needed" ] || _trust_git_tuning_cache_on "$repo"; then
      device="$(_trust_git_tuning_device "$repo")"
      case " $tested_bad " in
        *" $device "*) result=bad ;;
        *)
          case " $tested_ok " in
            *" $device "*) result=ok ;;
            *)
              if (cd "$repo" && git update-index --test-untracked-cache) >/dev/null 2>&1; then
                tested_ok="$tested_ok $device"
                result=ok
              else
                tested_bad="$tested_bad $device"
                result=bad
              fi
              ;;
          esac
          ;;
      esac
      if [ "$result" = bad ]; then
        if [ -n "$cache_needed" ]; then
          echo "  git tuning: $label: git's untracked-cache mtime self-test FAILED on this"
          echo "              filesystem, so no key that turns the cache on is written here"
          rest=""
          for key in $needed; do
            _trust_git_tuning_cache_key "$key" || rest="$rest $key"
          done
          needed="$rest"
        fi
        if _trust_git_tuning_cache_on "$repo"; then
          echo "  git tuning: $label: WARNING the untracked cache is in effect here, but git's mtime"
          echo "              self-test fails on this filesystem, so git status here can miss an"
          echo "              untracked file: unset core.untrackedCache and feature.manyFiles where they"
          echo "              are set, or keep this checkout on a filesystem that passes (APFS and ext4 do)"
        fi
      fi
    fi
    for key in $needed; do
      if git -C "$repo" config --local "$key" true 2>/dev/null; then
        echo "  git tuning: $label: set $key = true"
      else
        echo "  git tuning: $label: could not write $key to its config; skipped"
      fi
    done

    # The index format follows feature.manyFiles, to the declared format, unless
    # index.version names another one.
    [ -n "$decl_index" ] || continue
    if [ "$(git -C "$repo" config --type=bool --get feature.manyFiles 2>/dev/null || true)" != true ]; then
      continue
    fi
    explicit="$(git -C "$repo" config --get index.version 2>/dev/null || true)"
    if [ -n "$explicit" ] && [ "$explicit" != "$decl_index" ]; then
      echo "  git tuning: $label: index.version=$explicit is set; its index is not converted"
      continue
    fi
    version="$(_trust_git_tuning_index_version "$repo")"
    if [ -z "$version" ]; then
      echo "  git tuning: $label: no index to convert yet; git writes the next one at format 4"
    elif [ "$version" = "$decl_index" ]; then
      echo "  git tuning: $label: index format $version"
    elif git -C "$repo" update-index --index-version "$decl_index" >/dev/null 2>&1; then
      echo "  git tuning: $label: index format $version -> $decl_index"
    else
      echo "  git tuning: $label: index format $version not converted (another process may"
      echo "              hold its index.lock); it stays correct, and installing again converts it"
    fi
  done < <(_trust_git_tuning_repos "$top")
  _trust_git_tuning_never_notes "$top"
  return 0
}

# trust_git_tuning_status TOP: one line per repository; writes nothing.
trust_git_tuning_status() {
  local top repo label keys key rc parts version untuned=""
  local decl_super decl_sub decl_index decl_never
  top="$(cd -P "$1" 2>/dev/null && pwd -P)" || {
    echo "git tuning: cannot enter $1"
    return 0
  }
  _trust_git_tuning_declaration "$top" "" || return 0
  _trust_git_tuning_scopes "$top" || return 0
  while IFS= read -r repo; do
    case "$repo" in
      /*) ;;
      error:*)
        echo "git tuning: cannot list every submodule (${repo#error: }); a submodule not named"
        echo "  here is not reported"
        continue
        ;;
      *) continue ;;
    esac
    label="$(_trust_git_tuning_label "$top" "$repo")"
    keys="$(_trust_git_tuning_keys "$top" "$repo")"
    parts=""
    for key in $keys; do
      rc=0
      _trust_git_tuning_read "$repo" "$key" || rc=$?
      case "$rc" in
        0) parts="$parts $key=$TRUST_GIT_TUNING_VALUE ($TRUST_GIT_TUNING_SCOPE)" ;;
        1)
          parts="$parts $key=<unset>"
          untuned=1
          ;;
        *) parts="$parts $key=<unreadable>" ;;
      esac
    done
    version="$(_trust_git_tuning_index_version "$repo")"
    echo "git tuning: $label:$parts, index format ${version:-unknown}"
  done < <(_trust_git_tuning_repos "$top")
  _trust_git_tuning_never_notes "$top"
  if [ -n "$untuned" ]; then
    echo "  a repository above is untuned (a submodule populated after the last install"
    echo "  is one); installing again tunes it where git's mtime self-test passes"
  fi
  return 0
}

# trust_registry_prefetch <top> [--check]: make the landing gate's build-graph
# check answer offline on this host (scripts/land_gate.py prefetch has why, and
# docs/LANDING_GATE.md). A host that cannot yet answer costs its gates every leg,
# and never the install: no registry and no targo are reported and pass.
trust_registry_prefetch() {
  local top="$1" check="${2:-}"
  [ -f "$top/scripts/land_gate.py" ] || return 0
  if ! command -v targo >/dev/null 2>&1; then
    echo "registry: no targo on PATH; run scripts/land_gate.py prefetch once it is there"
    return 0
  fi
  python3 "$top/scripts/land_gate.py" prefetch ${check:+"$check"} ||
    echo "  until scripts/land_gate.py prefetch succeeds, a gate here does what the registry lines above say"
  return 0
}
