#!/usr/bin/env bash
# measure_stamp.sh — NAME THE TREE YOU MEASURED.
#
# Author: Andrew Yates. Copyright 2026 Andrew Yates. License: Apache-2.0 OR MIT.
#
# ===========================================================================
# WHY THIS EXISTS
# ===========================================================================
# 2026-08-19, measured, not recalled. A lane committed wave-SG at `c8afeab02f`
# with `crates/trust-thir-lower/src/lib.rs` at blob `0a2fd94a8d`. Ninety-eight
# seconds later it EDITED that file and never `git add`ed the edit — blob
# `d08476acf3`. It then ran the crate suite and got **599 passed, 0 failed**,
# a real result of a real run. At 23:00 it amended the commit; the blob in the
# commit was still `0a2fd94a8d`. At 23:25 it pushed as `8e214e90d5`, whose body
# quotes that 599. `8e214e90d5` is RED at exactly one test.
#
# The number was not fabricated. The commit message simply described the
# WORKING TREE instead of the COMMIT, and nothing in the world could tell the
# difference — because the measurement never said which tree it was of. A
# confirmed-miscompile-class gate was reverted on the strength of that, and the
# class sat ungated for 2h10m. See reports/revert-silence-rca-2026-08-20.md.
#
# ===========================================================================
# WHAT IT DOES
# ===========================================================================
# One call, into the log the runner is already writing:
#
#     bash /path/to/trust/scripts/lib/measure_stamp.sh <path> [<path>...]
#
# or, sourced (works from bash AND zsh — several lane runners are zsh):
#
#     . /path/to/trust/scripts/lib/measure_stamp.sh
#     measure_stamp crates/trust-thir-lower/src/lib.rs
#
# It prints a block naming, for every measured path, the blob in the WORKING
# TREE and the blob at HEAD:
#
#     === MEASURE-STAMP v1
#     --- when     2026-08-20T18:22:03Z
#     --- head     68d8001117...
#     --- file     crates/trust-thir-lower/src/lib.rs worktree=d08476acf3... head=0a2fd94a8d... DIRTY
#
# A DIRECTORY argument is stamped as a git TREE, so one line names a whole crate:
#     measure_stamp crates/trust-thir-lower/src
# resolves to that directory's tree object on both sides. `git rev-parse
# <sha>:<dir>` reads a tree exactly as it reads a blob, so the checker treats
# the two identically and a runner never has to enumerate its own sources.
#     --- dirt     1
#     --- porcelain  M crates/trust-thir-lower/src/lib.rs
#     --- trailer  Measured-on: crates/trust-thir-lower/src/lib.rs@d08476acf3...
#     === END MEASURE-STAMP v1
#
# BOTH SIDES, because they are the two things that get confused. That is the
# same two-sided blob discipline scripts/check_frozen_files.sh already applies
# to the frozen oracle files — and this is the point the RCA makes: on the very
# commit that lost 2h10m, the FROZEN files were quoted by blob with total
# rigour. The discipline existed. It was simply never pointed at the file being
# CHANGED. This points it there.
#
# The `--- trailer` lines are the whole adoption story. They are pre-formatted
# for pasting into the commit body, and `scripts/check_measurement_provenance.sh`
# then verifies each one against the commit's own tree — so a stamp that names a
# tree the commit does not carry is a REFUSED PUSH, not a footnote.
#
# NO JUDGEMENT, BY CONSTRUCTION. This records; it does not decide. A stamp
# saying DIRTY is not an error here — measuring a dirty tree is a legitimate
# thing to do (that is what a mutation probe is). It becomes a refusal only when
# someone PUBLISHES it, which is where the checker lives. Keeping the recorder
# opinion-free is what makes it safe to drop into 80-odd in-flight runners.
#
# EXIT STATUS is 0 whenever the stamp was written, including for a dirty tree.
# It is 2 only when the stamp CANNOT be written (no git, not a worktree) — a
# missing stamp must never be mistaken for a clean one, so it is loud and the
# block that is printed says UNSTAMPABLE rather than nothing.

measure_stamp() {
    # POSIX only: this function is sourced by zsh runners as well as bash ones.
    ms_ts=$(date -u +%Y-%m-%dT%H:%M:%SZ 2>/dev/null || echo unknown)

    if ! command -v git >/dev/null 2>&1; then
        echo "=== MEASURE-STAMP v1 UNSTAMPABLE"
        echo "--- when     $ms_ts"
        echo "--- reason   git is not on PATH; this log names no tree"
        echo "=== END MEASURE-STAMP v1"
        return 2
    fi

    ms_root=$(git rev-parse --show-toplevel 2>/dev/null)
    if [ -z "$ms_root" ]; then
        echo "=== MEASURE-STAMP v1 UNSTAMPABLE"
        echo "--- when     $ms_ts"
        echo "--- reason   not inside a git worktree (cwd $(pwd)); this log names no tree"
        echo "=== END MEASURE-STAMP v1"
        return 2
    fi

    ms_head=$(git rev-parse HEAD 2>/dev/null || echo unknown)

    echo "=== MEASURE-STAMP v1"
    echo "--- when     $ms_ts"
    echo "--- repo     $ms_root"
    echo "--- head     $ms_head"

    ms_dirt=0
    ms_trailers=""
    for ms_p in "$@"; do
        # Accept absolute or repo-relative; report repo-relative, because that
        # is what a commit trailer has to say to be checkable.
        case "$ms_p" in
            "$ms_root"/*) ms_rel=${ms_p#"$ms_root"/} ;;
            /*)           ms_rel="$ms_p" ;;
            *)            ms_rel="$ms_p" ;;
        esac

        # A DIRECTORY is stamped as a git TREE, so one line can name a whole
        # crate. The worktree tree is written through a THROWAWAY index
        # (GIT_INDEX_FILE) — the real index is never touched, which matters
        # because these runners execute inside worktrees other lanes are using.
        # `git rev-parse <sha>:<dir>` resolves a tree exactly as it resolves a
        # blob, so the checker needs no special case for this.
        if [ -d "$ms_root/$ms_rel" ]; then
            ms_idx=$(mktemp -t measure_stamp_idx.XXXXXX 2>/dev/null) || ms_idx=""
            if [ -n "$ms_idx" ]; then
                rm -f "$ms_idx"
                ms_wt=$(cd "$ms_root" && GIT_INDEX_FILE="$ms_idx" git add -A -- "$ms_rel" >/dev/null 2>&1 &&
                        GIT_INDEX_FILE="$ms_idx" git write-tree --prefix="$ms_rel" 2>/dev/null) || ms_wt=""
                rm -f "$ms_idx"
            fi
            [ -n "$ms_wt" ] || ms_wt=unhashable
        elif [ -f "$ms_root/$ms_rel" ]; then
            ms_wt=$(git hash-object -- "$ms_root/$ms_rel" 2>/dev/null || echo unhashable)
        elif [ -f "$ms_p" ]; then
            ms_wt=$(git hash-object -- "$ms_p" 2>/dev/null || echo unhashable)
        else
            ms_wt=ABSENT
        fi

        ms_hd=$(git rev-parse --verify --quiet "HEAD:$ms_rel" 2>/dev/null || echo ABSENT)

        if [ "$ms_wt" = "$ms_hd" ]; then
            ms_state=clean
        else
            ms_state=DIRTY
            ms_dirt=$((ms_dirt + 1))
        fi
        echo "--- file     $ms_rel worktree=$ms_wt head=$ms_hd $ms_state"
        ms_trailers="$ms_trailers$ms_rel@$ms_wt
"
    done

    if [ "$#" -eq 0 ]; then
        # A stamp with no measured path is a stamp about nothing. Say so in the
        # block rather than emitting a block that reads clean.
        echo "--- file     NONE-DECLARED"
        echo "--- dirt     UNKNOWN"
        echo "--- porcelain $(git status --porcelain --untracked-files=no 2>/dev/null | tr '\n' ';')"
        echo "=== END MEASURE-STAMP v1"
        return 0
    fi

    echo "--- dirt     $ms_dirt"
    echo "--- porcelain [$(git status --porcelain --untracked-files=no 2>/dev/null | tr '\n' ';')]"
    printf '%s' "$ms_trailers" | while IFS= read -r ms_t; do
        [ -n "$ms_t" ] || continue
        echo "--- trailer  Measured-on: $ms_t"
    done
    echo "=== END MEASURE-STAMP v1"
    return 0
}

# Executable form. `return` fails outside a function in a non-sourced shell, so
# this is how the file tells whether it was run or sourced without relying on
# BASH_SOURCE (absent in zsh, where several lane runners live).
if (return 0 2>/dev/null); then
    :
else
    measure_stamp "$@"
    exit $?
fi
