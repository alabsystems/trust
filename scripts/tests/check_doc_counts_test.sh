#!/usr/bin/env bash
# The push-subject proof for `scripts/check_doc_counts.sh` (the G26 doc-truth gate).
#
# Author: Andrew Yates. Copyright 2026 Andrew Yates. License: Apache-2.0 OR MIT.
#
# Every case builds a real throwaway repository (with a bare `origin`, so
# refs/remotes/origin/main exists) holding a copy of the gate, and runs the
# gate INSIDE it the way scripts/hooks/pre-push does (cwd = repo,
# TRUST_PUSHED_REFS = git's pre-push lines), or with TRUST_PUSHED_REFS unset
# for the standing (working-tree) reading.
#
# What the gate promises under a push (its header, "WHICH TREE IS READ"): per
# pushed ref, SKIP when the pushed tree's in-scope entries equal what the
# destination has; JUDGE THE CHECKOUT when they equal HEAD's and this checkout
# provably holds HEAD there; otherwise REFUSE. So the verdict is either the
# unchanged reading of this checkout, which holds exactly the pushed content in
# scope, or a refusal — never a reading of something the push does not land.
#
# Outcomes: green (exit 0, judged), red (exit 1, judged), skip (exit 0 after
# `SKIPPED: `), refused (exit 1 with a `REFUSED —` line), malformed (exit 2).
# The third field of each case pins WHY, so a case cannot pass on an
# unrelated failure.
#
# DEFECT ARMS (ARM=1) are the shapes doc-counts-1 let through. For each, the
# test also proves the defect on the fixture itself: (a) the push reading
# refuses; (b) main's lane passes it — main never read TRUST_PUSHED_REFS, so
# its verdict on a push is the working-tree reading, which this gate keeps
# byte for byte and the test runs with TRUST_PUSHED_REFS unset; (c) that same
# reading on a REAL checkout of the pushed tree (git worktree add) is red.
# Point CHECKER at main's copy (`git show <rev>:scripts/check_doc_counts.sh >
# /tmp/x.sh; CHECKER=/tmp/x.sh …`) and every arm fails on (a).
#
# DOC-COUNTS-2 ARMS (ARM=2) are the shapes invariant (2)'s fail-open scan let
# through (`grep -rInE … docs 2>/dev/null || true`): a NUL-holding file, a line
# the locale cannot decode, an unreadable file. For each, (a) this gate is red
# for the stated reason, and (b) main's scan command, verbatim, reports no hit
# on the fixture while every other invariant reports ok, so main's lane passes.
# With CHECKER=main's copy every ARM=2 case fails on (a) too.
#
# ONLY=<name> runs one case. Sourced with DOC_COUNTS_TEST_LIB=1 it defines the
# fixtures and returns, so a differential harness can replay them.
set -euo pipefail

REPO_ROOT=$(cd -P "${BASH_SOURCE[0]%/*}/../.." && pwd -P)
CHECKER="${CHECKER:-$REPO_ROOT/scripts/check_doc_counts.sh}"
[ -f "$CHECKER" ] || { echo "check_doc_counts_test: no checker at $CHECKER" >&2; exit 1; }

# Hermetic git for the fixtures: no user/global hooks, signing, or rewrites.
export GIT_CONFIG_GLOBAL=/dev/null GIT_CONFIG_NOSYSTEM=1
export GIT_AUTHOR_NAME=t GIT_AUTHOR_EMAIL=t@example.invalid
export GIT_COMMITTER_NAME=t GIT_COMMITTER_EMAIL=t@example.invalid
unset GIT_DIR GIT_WORK_TREE GIT_INDEX_FILE TRUST_PUSH_REMOTE

TMP=$(mktemp -d "${TMPDIR:-/tmp}/doc-counts-test.XXXXXX")
TMP=$(cd -P "$TMP" && pwd -P)
CSTMP=""
cleanup() {
  chmod -R u+rwx "$TMP" 2>/dev/null || true; rm -rf "${TMP:?}"
  if [ -n "$CSTMP" ]; then chmod -R u+rwx "$CSTMP" 2>/dev/null || true; rm -rf "${CSTMP:?}"; fi
}
trap cleanup EXIT

FOLD=0; mkdir "$TMP/fold-probe" && [ -d "$TMP/FOLD-PROBE" ] && FOLD=1
# A case-SENSITIVE directory for the one case that needs one (hidden_lean). The
# fixture directory serves when it is case-sensitive; on a case-folding one
# (macOS's default) DOC_COUNTS_TEST_CS_DIR may name a directory on a
# case-sensitive volume (e.g. `hdiutil create -fs 'Case-sensitive APFS'`), and
# without one that case is reported n/a, never counted as passed.
if [ "$FOLD" = 0 ]; then CSTMP=""
elif [ -n "${DOC_COUNTS_TEST_CS_DIR:-}" ]; then
  CSTMP=$(mktemp -d "$DOC_COUNTS_TEST_CS_DIR/doc-counts-test-cs.XXXXXX"); CSTMP=$(cd -P "$CSTMP" && pwd -P)
  mkdir "$CSTMP/fold-probe"; if [ -d "$CSTMP/FOLD-PROBE" ]; then rm -rf "${CSTMP:?}"; CSTMP=""; echo "DOC_COUNTS_TEST_CS_DIR is case-folding; ignored" >&2; fi
fi
Z=0000000000000000000000000000000000000000
CLAIM='We have 82 wasm obligations proven unsat.'
HONEST='82 total obligations, of which 54 are genuine; nothing is claimed proven for them.'
RECIPE='[host]
rustflags = ["-Ztrust-verify=off"]'
U=(LANG=en_US.UTF-8 LC_ALL=en_US.UTF-8)
CL=(LANG=C LC_ALL=C)

# ---- fixture helpers -------------------------------------------------------

# mk <name>: a fresh repo whose committed main is consistent and GREEN, pushed
# to a bare origin. Sets R, BASE and ORIGIN.
mk() {
  R="$TMP/$1"
  ORIGIN="$TMP/$1.git"
  mkdir -p "$R/scripts" "$R/docs" "$R/proofs/trust-soundness"
  git init -q --bare "$ORIGIN"
  git -C "$R" init -q -b main
  git -C "$R" config commit.gpgsign false
  git -C "$R" config tag.gpgsign false
  cp "$CHECKER" "$R/scripts/check_doc_counts.sh"
  # Invariant (4) runs tools/gen_tcb_std_lists.py --check, whose inputs (the
  # compiler and bridge sources, docs/TCB.md) a fixture does not carry: a
  # stand-in answers "current" unless tools/STALE exists (standing_tcb_stale).
  mkdir -p "$R/tools"
  printf '%s\n' 'import os, sys' \
    'sys.exit(1 if os.path.exists(os.path.join(os.path.dirname(os.path.abspath(__file__)), "STALE")) else 0)' \
    >"$R/tools/gen_tcb_std_lists.py"
  : >"$R/proofs/trust-soundness/a.lean"
  : >"$R/proofs/trust-soundness/b.lean"
  echo "verified: 2/2" >"$R/proofs/trust-soundness/README.md"
  echo "$HONEST" >"$R/docs/wasm.md"
  git -C "$R" add -A
  git -C "$R" commit -qm base
  BASE=$(git -C "$R" rev-parse HEAD)
  git -C "$R" remote add origin "$ORIGIN"
  git -C "$R" push -q origin main
}
# commit_all <message>: commit the whole working tree; sets SHA.
commit_all() { git -C "$R" add -A; git -C "$R" commit -qm "$1"; SHA=$(git -C "$R" rev-parse HEAD); }
# stage <mode> <tree-path> <content>: one index entry, with plumbing.
stage() {
  local oid; oid=$(printf '%s' "$3" | git -C "$R" hash-object -w --stdin)
  printf '%s %s\t%s\0' "$1" "$oid" "$2" | git -C "$R" update-index -z --add --index-info
}
# land: commit the index and check it out as a puller's checkout would; sets SHA.
land() {
  git -C "$R" commit -qm "$1"; SHA=$(git -C "$R" rev-parse HEAD)
  rm -rf "$R/docs" "$R/proofs"; git -C "$R" reset -q --hard
}
# mk_carried <name>: origin/main carries an inflated claim, a [host] recipe and
# a stale README count (published before this gate could see them).
mk_carried() {
  mk "$1"
  echo "$CLAIM" >"$R/docs/wasm.md"
  printf '%s\n' "$RECIPE" >"$R/docs/recipe.md"
  : >"$R/proofs/trust-soundness/c.lean"
  commit_all carried
  git -C "$R" push -q origin main
  CARRIED=$SHA
}
upd() { REFS="refs/heads/main $SHA refs/heads/main $1"; }   # an update of main from <remote-sha>

# ---- the cases -------------------------------------------------------------
# Each sets REFS (git's pre-push lines, or UNSET for the standing reading),
# WANT, WHY and, for a defect arm, ARM=1.

CASES=()
def() { CASES+=("$1"); }

# == skip: nothing in scope changes against what the destination has
def skip_ledger; case_skip_ledger() { mk_carried skip_ledger; mkdir -p "$R/ledger"; echo row >"$R/ledger/goals.tsv"
  commit_all ledger; echo "$CLAIM" >"$R/docs/wip.md"   # local WIP is not what is pushed
  upd "$CARRIED"; WANT=skip; WHY='skipped (its in-scope entries'; }
# A claim-ledger goals publish:
# the goals branch forked from an OLD main (which carried what main has since
# fixed); the publish pushes a ledger-only child to the goals ref (an update)
# and to a mirror ref (a new ref), from a checkout that sits on main.
def goals_publish; case_goals_publish() { mk_carried goals_publish
  git -C "$R" checkout -qb goals "$CARRIED"; mkdir -p "$R/coordination"; echo r1 >"$R/coordination/ledger.json"
  commit_all ledger1; git -C "$R" push -q origin goals:goals/TRUST-TWO-LANGUAGE-100; local old=$SHA
  git -C "$R" checkout -q main; echo "$HONEST" >"$R/docs/wasm.md"; git -C "$R" rm -q docs/recipe.md
  echo "verified: 3/3" >"$R/proofs/trust-soundness/README.md"; commit_all fix; git -C "$R" push -q origin main
  local tree; tree=$(git -C "$R" rev-parse "$old^{tree}")
  local led; led=$(printf 'r2\n' | git -C "$R" hash-object -w --stdin)
  local ct; ct=$(printf '100644 blob %s\tledger.json\n' "$led" | git -C "$R" mktree)
  local t2; t2=$( { git -C "$R" ls-tree "$tree" | grep -v "$(printf '\t')coordination\$"; printf '040000 tree %s\tcoordination\n' "$ct"; } | git -C "$R" mktree)
  SHA=$(git -C "$R" commit-tree -p "$old" -m ledger2 "$t2")
  REFS="refs/heads/goals/TRUST-TWO-LANGUAGE-100 $SHA refs/heads/goals/TRUST-TWO-LANGUAGE-100 $old
refs/heads/goals/mirror/W0 $SHA refs/heads/goals/mirror/W0 $Z"
  WANT=skip; WHY='equal the fork point'; }
def newref_fork_skip; case_newref_fork_skip() { mk_carried newref_fork_skip
  git -C "$R" checkout -qb old "$CARRIED"
  git -C "$R" checkout -q main; echo "$HONEST" >"$R/docs/wasm.md"; commit_all fix; git -C "$R" push -q origin main
  git -C "$R" checkout -q old; mkdir -p "$R/ledger"; echo row >"$R/ledger/goals.tsv"; commit_all ledger
  REFS="refs/heads/old $SHA refs/heads/old $Z"; WANT=skip; WHY='fork point'; }
def newref_remote_url; case_newref_remote_url() { mk newref_remote_url   # TRUST_PUSH_REMOTE is git's URL
  git clone -q --bare "$ORIGIN" "$TMP/nru-up.git"; git -C "$R" remote add up "$TMP/nru-up.git"; git -C "$R" fetch -q up
  git -C "$R" checkout -qb topic; mkdir -p "$R/ledger"; echo row >"$R/ledger/goals.tsv"; commit_all ledger
  git -C "$R" update-ref -d refs/remotes/origin/main
  REFS="refs/heads/topic $SHA refs/heads/topic $Z"; ENVX=(TRUST_PUSH_REMOTE="$TMP/nru-up.git")
  WANT=skip; WHY='refs/remotes/up/main'; }
# git's pre-push $2 is the URL AFTER insteadOf rewriting ("short:x.git" with
# url.<dir>/.insteadOf=short: arrives as <dir>/x.git): the destination is still
# known, through `git remote get-url --push`.
def newref_insteadof; case_newref_insteadof() { mk newref_insteadof
  git clone -q --bare "$ORIGIN" "$TMP/nio-up.git"; git -C "$R" config url."$TMP/".insteadOf nioshort:
  git -C "$R" remote add up nioshort:nio-up.git; git -C "$R" fetch -q up
  git -C "$R" checkout -qb topic; mkdir -p "$R/ledger"; echo row >"$R/ledger/goals.tsv"; commit_all ledger
  git -C "$R" update-ref -d refs/remotes/origin/main
  REFS="refs/heads/topic $SHA refs/heads/topic $Z"; ENVX=(TRUST_PUSH_REMOTE="$TMP/nio-up.git")
  WANT=skip; WHY='refs/remotes/up/main'; }
def deletion_only; case_deletion_only() { mk deletion_only; echo "$CLAIM" >"$R/docs/wasm.md"
  REFS="(delete) $Z refs/heads/topic $BASE"; WANT=skip; WHY='deletion — lands no tree'; }

# == judged the checkout: the push is HEAD in scope, and the checkout holds HEAD
def main_push; case_main_push() { mk main_push; echo "a routine note" >"$R/docs/notes.md"; commit_all note
  upd "$BASE"; WANT=green; WHY='judged the checkout'; }
def main_push_ignored; case_main_push_ignored() { mk main_push_ignored   # ignored LaTeX by-products in docs/ do not refuse
  printf 'docs/*.aux\n' >"$R/.gitignore"; echo "a routine note" >"$R/docs/notes.md"; commit_all note
  printf 'relax\n' >"$R/docs/paper.aux"; upd "$BASE"; WANT=green; WHY='DOC COUNTS OK (the push'; }
def judged_claim; case_judged_claim() { mk judged_claim; echo "$CLAIM" >"$R/docs/wasm.md"; commit_all bad
  upd "$BASE"; WANT=red; WHY='inflated wasm proof count'; }
def judged_readme; case_judged_readme() { mk judged_readme; : >"$R/proofs/trust-soundness/c.lean"; commit_all stale
  upd "$BASE"; WANT=red; WHY='README.md does not state that count'; }
def judged_recipe; case_judged_recipe() { mk judged_recipe; printf '%s\n' "$RECIPE" >"$R/docs/recipe.md"; commit_all bad
  upd "$BASE"; WANT=red; WHY='sets a -Ztrust-* flag in [host]'; }
def judged_nodocs; case_judged_nodocs() { mk judged_nodocs; git -C "$R" rm -rq docs; commit_all nodocs
  upd "$BASE"; WANT=red; WHY='DOC-TRUTH GATE FAILED'; }
def judged_twice; case_judged_twice() { mk judged_twice; echo "$CLAIM" >"$R/docs/wasm.md"; commit_all bad; git -C "$R" tag v1
  REFS="refs/heads/main $SHA refs/heads/main $BASE
refs/tags/v1 $SHA refs/tags/v1 $Z"; WANT=red; WHY='the same checkout as above: red'; }
def unknown_remote_green; case_unknown_remote_green() { mk unknown_remote_green; echo note >"$R/docs/n.md"; commit_all note
  upd 2222222222222222222222222222222222222222; WANT=green; WHY='is not in this object store'; }
def unknown_remote_red; case_unknown_remote_red() { mk unknown_remote_red; echo "$CLAIM" >"$R/docs/n.md"; commit_all bad
  upd 2222222222222222222222222222222222222222; WANT=red; WHY='inflated wasm proof count'; }
def newref_fork_judged; case_newref_fork_judged() { mk newref_fork_judged; git -C "$R" checkout -qb topic
  echo "$CLAIM" >"$R/docs/claim.md"; commit_all bad
  REFS="refs/heads/topic $SHA refs/heads/topic $Z"; WANT=red; WHY='inflated wasm proof count'; }
def newref_nofork; case_newref_nofork() { mk newref_nofork; git -C "$R" remote remove origin; echo "$CLAIM" >"$R/docs/wasm.md"
  commit_all bad; REFS="refs/heads/next $SHA refs/heads/next $Z"; WANT=red; WHY='no fork point'; }
def newref_unknown_dest; case_newref_unknown_dest() { mk newref_unknown_dest; git init -q --bare "$TMP/nud-other.git"
  git -C "$R" checkout -qb feat; mkdir -p "$R/ledger"; echo n >"$R/ledger/n"; commit_all n
  REFS="refs/heads/feat $SHA refs/heads/feat $Z"; ENVX=(TRUST_PUSH_REMOTE="$TMP/nud-other.git")
  WANT=green; WHY='is not a remote here'; }

# == refused: the push lands content this checkout does not hold
def other_ref; case_other_ref() { mk other_ref; git -C "$R" checkout -qb bad
  echo "82 refinement obligations proved unsat" >"$R/docs/wasm.md"; commit_all bad; git -C "$R" checkout -q main
  REFS="refs/heads/bad $SHA refs/heads/main $BASE"; WANT=refused; WHY='to content this checkout does not hold'; ARM=1; }
def tag_other; case_tag_other() { mk tag_other; git -C "$R" checkout -qb t; echo "$CLAIM" >"$R/docs/wasm.md"; commit_all bad
  git -C "$R" checkout -q main; git -C "$R" tag -a -m v v1 "$SHA"
  REFS="refs/tags/v1 $(git -C "$R" rev-parse v1) refs/tags/v1 $Z"; WANT=refused; WHY='check out refs/tags/v1'; ARM=1; }
def dirty_scope; case_dirty_scope() { mk dirty_scope; echo "$CLAIM" >"$R/docs/wasm.md"; commit_all bad
  echo "$HONEST" >"$R/docs/wasm.md"; upd "$BASE"; WANT=refused; WHY='uncommitted edits'; ARM=1; }
def staged_scope; case_staged_scope() { mk staged_scope; echo "$CLAIM" >"$R/docs/wasm.md"; commit_all bad
  echo "$HONEST" >"$R/docs/wasm.md"; git -C "$R" add docs/wasm.md; upd "$BASE"; WANT=refused; WHY='staged changes'; ARM=1; }
def untracked_scope; case_untracked_scope() { mk untracked_scope; echo "verified: 3/3" >"$R/proofs/trust-soundness/README.md"
  commit_all stale; : >"$R/proofs/trust-soundness/wip.lean"
  upd "$BASE"; WANT=refused; WHY='untracked files there'; ARM=1; }
def ignored_lean; case_ignored_lean() { mk ignored_lean; echo "verified: 3/3" >"$R/proofs/trust-soundness/README.md"
  commit_all stale; echo 'wip.lean' >>"$R/.git/info/exclude"; : >"$R/proofs/trust-soundness/wip.lean"
  upd "$BASE"; WANT=refused; WHY='ignored ones and empty directories count'; ARM=1; }
def emptydir_lean; case_emptydir_lean() { mk emptydir_lean; echo "verified: 3/3" >"$R/proofs/trust-soundness/README.md"
  commit_all stale; mkdir "$R/proofs/trust-soundness/wip.lean"
  upd "$BASE"; WANT=refused; WHY='ignored ones and empty directories count'; ARM=1; }
def skip_worktree; case_skip_worktree() { mk skip_worktree; echo "$CLAIM" >"$R/docs/wasm.md"; commit_all bad
  git -C "$R" update-index --skip-worktree docs/wasm.md; echo "$HONEST" >"$R/docs/wasm.md"
  upd "$BASE"; WANT=refused; WHY="docs/wasm.md 'S'"; ARM=1; }
def assume_unchanged; case_assume_unchanged() { mk assume_unchanged; echo "$CLAIM" >"$R/docs/wasm.md"; commit_all bad
  git -C "$R" update-index --assume-unchanged docs/wasm.md; echo "$HONEST" >"$R/docs/wasm.md"
  upd "$BASE"; WANT=refused; WHY="docs/wasm.md 'h'"; ARM=1; }
# Same size, same mtime: only a byte comparison sees this edit.
def same_stat; case_same_stat() { mk same_stat; printf 'We have 82 wasm obligations proven unsat.\n' >"$R/docs/wasm.md"
  commit_all bad; local m; m=$(stat -f %m "$R/docs/wasm.md" 2>/dev/null || stat -c %Y "$R/docs/wasm.md")
  printf 'We have 82 wasm obligations PROVEN unsat.\n' >"$R/docs/wasm.md"
  touch -d "@$m" "$R/docs/wasm.md" 2>/dev/null || touch -t "$(date -r "$m" +%Y%m%d%H%M.%S)" "$R/docs/wasm.md"
  upd "$BASE"; WANT=refused; WHY='uncommitted edits'; ARM=1; }
# A smudge filter configured AFTER the file was checked out: `git diff` cleans
# the working copy and calls it unchanged, a fresh checkout smudges the claim in.
def filter_config; case_filter_config() { mk filter_config; git -C "$R" config filter.cl.smudge cat; git -C "$R" config filter.cl.clean cat
  printf 'docs/f.md filter=cl\n' >"$R/.gitattributes"; echo XX >"$R/docs/f.md"; commit_all filt
  git -C "$R" config filter.cl.smudge "sed s/XX/82-wasm-obligations-proven/"
  upd "$BASE"; WANT=refused; WHY='docs/f.md has filter=cl'; ARM=1; }
# A filter driver no in-scope path names converts nothing: judged, not refused
# (the owner's global filter.lfs; until 2026-10-24 a key alone refused by name).
def filter_unused; case_filter_unused() { mk filter_unused; git -C "$R" config filter.lfs.clean cat
  git -C "$R" config filter.lfs.smudge "sed s/note/82-wasm-obligations-proven/"; git -C "$R" config filter.lfs.required true
  echo note >"$R/docs/n.md"; commit_all note; upd "$BASE"; WANT=green; WHY='judged the checkout'; }
# The attribute that WOULD apply that driver, from the two places outside the
# tree check-attr also reads: still refused.
def filter_info_attributes; case_filter_info_attributes() { mk filter_info_attributes; git -C "$R" config filter.lfs.clean cat
  git -C "$R" config filter.lfs.smudge "sed s/note/82-wasm-obligations-proven/"
  echo note >"$R/docs/n.md"; commit_all note; mkdir -p "$R/.git/info"; printf 'docs/n.md filter=lfs\n' >"$R/.git/info/attributes"
  upd "$BASE"; WANT=refused; WHY='docs/n.md has filter=lfs'; }
def filter_attributes_file; case_filter_attributes_file() { mk filter_attributes_file; git -C "$R" config filter.lfs.clean cat
  git -C "$R" config filter.lfs.smudge "sed s/note/82-wasm-obligations-proven/"
  printf 'docs/*.md filter=lfs\n' >"$TMP/filter_attributes_file.attributes"
  git -C "$R" config core.attributesFile "$TMP/filter_attributes_file.attributes"
  echo note >"$R/docs/n.md"; commit_all note; upd "$BASE"; WANT=refused; WHY='docs/n.md has filter=lfs'; }
# An attribute committed after the file was checked out: the working copy is
# stale (UTF-8), a checkout writes UTF-16.
def attr_encoding; case_attr_encoding() { mk attr_encoding
  stage 100644 .gitattributes "proofs/trust-soundness/README.md working-tree-encoding=UTF-16
"; git -C "$R" commit -qm attr; SHA=$(git -C "$R" rev-parse HEAD); printf 'proofs/trust-soundness/README.md working-tree-encoding=UTF-16\n' >"$R/.gitattributes"
  upd "$BASE"; WANT=refused; WHY='working-tree-encoding=UTF-16'; ARM=1; }
def autocrlf; case_autocrlf() { mk autocrlf; git -C "$R" config core.autocrlf input; echo note >"$R/docs/n.md"; commit_all note
  upd "$BASE"; WANT=refused; WHY='core.autocrlf=input'; }
def symlink_readme; case_symlink_readme() { mk symlink_readme; mv "$R/proofs/trust-soundness/README.md" "$R/PROOFCOUNT.md"
  ln -s ../../PROOFCOUNT.md "$R/proofs/trust-soundness/README.md"; commit_all link; git -C "$R" push -q origin main; local l=$SHA
  echo "verified: 3/3" >"$R/PROOFCOUNT.md"; commit_all stale
  upd "$l"; WANT=refused; WHY='a symbolic link at proofs/trust-soundness/README.md'; }
def symlink_proofs; case_symlink_proofs() { mk symlink_proofs; git -C "$R" mv proofs pf; ln -s pf "$R/proofs"; commit_all l
  upd "$BASE"; WANT=refused; WHY='a symbolic link at proofs'; }
def gitlink_docs; case_gitlink_docs() { mk gitlink_docs; git -C "$R" update-index --add --cacheinfo "160000,$BASE,docs/sub"
  git -C "$R" commit -qm gl; SHA=$(git -C "$R" rev-parse HEAD); upd "$BASE"; WANT=refused; WHY='a gitlink at docs/sub'; }
def multi_ref; case_multi_ref() { mk multi_ref; git -C "$R" checkout -qb topic; echo fine >"$R/docs/fine.md"; commit_all fine
  local good=$SHA; git -C "$R" checkout -q main
  REFS="refs/heads/main $BASE refs/heads/main $BASE
refs/heads/topic $good refs/heads/topic $Z"; WANT=refused; WHY='check out refs/heads/topic'; }
# The checkout's proofs/ is named Proofs on disk (a case-folding filesystem):
# git's untracked scan follows the on-disk name, the reading the folded one.
def disk_case; case_disk_case() { mk disk_case; echo "verified: 3/3" >"$R/proofs/trust-soundness/README.md"; commit_all stale
  if [ "$FOLD" = 1 ]; then mv "$R/proofs" "$R/Proofs.tmp"; mv "$R/Proofs.tmp" "$R/Proofs"; : >"$R/Proofs/trust-soundness/wip.lean"
    WANT=refused; WHY='is not, on disk, a directory stored under exactly that name'; ARM=1
  else : >"$R/proofs/trust-soundness/wip.lean"; WANT=refused; WHY='untracked files there'; ARM=1; fi
  upd "$BASE"; }
# A tracked FILE stored on disk under a case-folded name (a manual rename on
# a case-folding filesystem, core.ignorecase=true): git's lstat folds case, so
# status, diff and the untracked scan call the checkout clean, while the
# reading's `find -name '*.md'` / `-name '*.lean'` match the STORED name and
# miss it; a real checkout writes the index spelling and the reading sees it.
_refold() { mv "$1" "$1.refold"; mv "$1.refold" "$2"; }
def disk_case_md; case_disk_case_md() { mk disk_case_md; printf '%s\n' "$RECIPE" >"$R/docs/recipe.md"; commit_all recipe
  _refold "$R/docs/recipe.md" "$R/docs/recipe.MD"; upd "$BASE"; WANT=refused; ARM=1
  if [ "$FOLD" = 1 ]; then WHY='docs/recipe.md is tracked, but no entry is stored on disk under exactly that name'; else WHY='uncommitted edits'; fi; }
def disk_case_lean; case_disk_case_lean() { mk disk_case_lean; : >"$R/proofs/trust-soundness/c.lean"; commit_all stale
  _refold "$R/proofs/trust-soundness/c.lean" "$R/proofs/trust-soundness/c.LEAN"; upd "$BASE"; WANT=refused; ARM=1
  if [ "$FOLD" = 1 ]; then WHY='proofs/trust-soundness/c.lean is tracked, but no entry is stored on disk'; else WHY='uncommitted edits'; fi; }
# a nested directory's case differs: the reading still finds the file (not an
# arm), but the stored-name rule refuses it all the same
def disk_case_subdir; case_disk_case_subdir() { mk disk_case_subdir; mkdir "$R/docs/sub"; printf '%s\n' "$RECIPE" >"$R/docs/sub/r.md"; commit_all recipe
  _refold "$R/docs/sub" "$R/docs/SUB"; upd "$BASE"; WANT=refused
  if [ "$FOLD" = 1 ]; then WHY='docs/sub/r.md is tracked, but no entry is stored'; else WHY='uncommitted edits'; fi; }
# the stored-name lists are compared line by line: an IGNORED directory named
# "zz<newline>docs" holding recipe.md walks as the line docs/recipe.md, and must
# not stand in for the tracked file
def disk_case_newline; case_disk_case_newline() { mk disk_case_newline; printf '%s\n' "$RECIPE" >"$R/docs/recipe.md"; commit_all recipe
  _refold "$R/docs/recipe.md" "$R/docs/recipe.MD"; echo 'zz*' >>"$R/.git/info/exclude"
  mkdir "$R/docs/zz
docs"; : >"$R/docs/zz
docs/recipe.md"; upd "$BASE"; WANT=refused; ARM=1
  if [ "$FOLD" = 1 ]; then WHY='holds a newline'; else WHY='uncommitted edits'; fi; }
# A case-SENSITIVE volume with core.ignorecase=true: an extra C.lean beside the
# tracked c.lean folds onto it, so git's untracked scan (ignored and --directory
# included) never lists it, while the reading counts it and turns a stale
# README green. proofs/trust-soundness's names must equal HEAD's both ways.
def hidden_lean; case_hidden_lean() {
  if [ "$FOLD" = 1 ] && [ -z "$CSTMP" ]; then
    mk hidden_lean; REFS=UNSET; WANT=na; WHY='no case-sensitive directory here (set DOC_COUNTS_TEST_CS_DIR)'; return 0
  fi
  local TMP="$TMP"; [ -z "$CSTMP" ] || TMP="$CSTMP"
  mk hidden_lean; : >"$R/proofs/trust-soundness/c.lean"; echo "verified: 4/4" >"$R/proofs/trust-soundness/README.md"; commit_all stale
  git -C "$R" config core.ignorecase true; : >"$R/proofs/trust-soundness/C.lean"
  upd "$BASE"; WANT=refused; WHY='the names stored in proofs/trust-soundness/ are not exactly HEAD'"'"'s there'; ARM=1; }
def carried_touch; case_carried_touch() { mk_carried carried_touch; echo "extra line" >>"$R/docs/wasm.md"; commit_all touch
  upd "$CARRIED"; WANT=red; WHY='inflated wasm proof count'; }   # touching docs re-reads what is carried

# == malformed input: exit 2
def malformed3; case_malformed3() { mk malformed3; REFS="refs/heads/main $BASE refs/heads/main"; WANT=malformed; WHY='malformed TRUST_PUSHED_REFS line'; }
def malformed5; case_malformed5() { mk malformed5; REFS="refs/heads/main $BASE refs/heads/main $BASE x"; WANT=malformed; WHY='malformed TRUST_PUSHED_REFS line'; }
def malformedhex; case_malformedhex() { mk malformedhex; REFS="refs/heads/main $BASE refs/heads/main XYZ"; WANT=malformed; WHY='malformed TRUST_PUSHED_REFS line'; }
def malformedlater; case_malformedlater() { mk malformedlater; REFS="refs/heads/main $BASE refs/heads/main $BASE
refs/heads/x ${BASE:0:39} refs/heads/x $Z"; WANT=malformed; WHY='malformed TRUST_PUSHED_REFS line'; }
def notree; case_notree() { mk notree; REFS="refs/heads/main 1111111111111111111111111111111111111111 refs/heads/main $BASE"
  WANT=malformed; WHY='does not name a tree'; }
def sha256_shape; case_sha256_shape() { mk sha256_shape; local h; h=$(printf '1%.0s' $(seq 1 64))
  REFS="refs/heads/main $h refs/heads/main $Z"; WANT=malformed; WHY='does not name a tree'; }   # 64 hex is well-formed

# == the standing reading (TRUST_PUSHED_REFS unset or blank): the working tree, main's reading
def standing_green; case_standing_green() { mk standing_green; REFS=UNSET; WANT=green; WHY='DOC COUNTS OK'; }
def standing_claim; case_standing_claim() { mk standing_claim; echo "$CLAIM" >"$R/docs/wasm.md"; REFS=UNSET; WANT=red; WHY='inflated wasm proof count'; }
def standing_blank; case_standing_blank() { mk standing_blank; echo "$CLAIM" >"$R/docs/wasm.md"; REFS="   "; WANT=red; WHY='inflated wasm proof count'; }
def standing_empty; case_standing_empty() { mk standing_empty; echo "$CLAIM" >"$R/docs/wasm.md"; REFS=""; WANT=red; WHY='inflated wasm proof count'; }
def standing_lean; case_standing_lean() { mk standing_lean; : >"$R/proofs/trust-soundness/wip.lean"; REFS=UNSET; WANT=red; WHY='README.md does not state that count'; }
def standing_noreadme; case_standing_noreadme() { mk standing_noreadme; rm "$R/proofs/trust-soundness/README.md"; REFS=UNSET; WANT=red; WHY='README.md is missing'; }
def standing_tcb_stale; case_standing_tcb_stale() { mk standing_tcb_stale; : >"$R/tools/STALE"; REFS=UNSET; WANT=red; WHY='generated std name lists in docs/TCB.md do not match'; }
def standing_recipe; case_standing_recipe() { mk standing_recipe; printf '%s\n' "$RECIPE" >"$R/docs/recipe.md"; REFS=UNSET; WANT=red; WHY='sets a -Ztrust-* flag in [host]'; }
# Character windows (main's semantics, kept): 24 em dashes are 26 characters
# but 74 bytes, inside {0,60} only when characters are counted.
MBGAP="82 $(printf '\342\200\224%.0s' $(seq 1 24)) obligations proven"
def standing_mb_window; case_standing_mb_window() { mk standing_mb_window; printf '%s\n' "$MBGAP" >"$R/docs/mb.md"
  REFS=UNSET; WANT=red; WHY='inflated wasm proof count'; }
# No exemption by name or magic: a PDF-looking file carrying the claim as text.
def standing_pdf_text; case_standing_pdf_text() { mk standing_pdf_text; printf '%%PDF-1.5\n%%\342\343\317\323\n%s\n' "$CLAIM" >"$R/docs/paper.pdf"
  REFS=UNSET; WANT=red; WHY='inflated wasm proof count'; }
# The honest framing stays green in a NUL-holding file, and in an unreadable-
# as-text line that lacks the claim's words.
def dc2_nul_honest; case_dc2_nul_honest() { mk dc2_nul_honest; printf 'x\000y\n%s\n' "$HONEST" >"$R/docs/nul.md"
  printf 'caf\351 au lait\n' >"$R/docs/latin1.tex"; REFS=UNSET; WANT=green; WHY="ok  wasm headline: no inflated"; }
# An unreadable-as-text line holding the claim's WORDS is refused even when its
# sentence is the honest one: its characters cannot be counted (a documented
# conservative cost of the fix; main passes it).
def dc2_invalid_honest; case_dc2_invalid_honest() { mk dc2_invalid_honest; printf 'caf\351: %s\n' "$HONEST" >"$R/docs/latin1.tex"
  REFS=UNSET; WANT=red; WHY='are not valid text in this locale'; }
# The same bytes under the C locale are text, and the honest sentence is green.
def dc2_invalid_honest_c; case_dc2_invalid_honest_c() { mk dc2_invalid_honest_c; printf 'caf\351: %s\n' "$HONEST" >"$R/docs/latin1.tex"
  LOC=CL; REFS=UNSET; WANT=green; WHY="ok  wasm headline: no inflated"; }

# == doc-counts-2 DEFECT ARMS (ARM=2): main's invariant (2) was
# `grep -rInE … docs 2>/dev/null || true`, which read grep's error exit as "no
# match" and, with -I, skipped every file holding a NUL; and BSD grep's regex
# matches nothing on a line that is not valid in the caller's locale. For each,
# the test proves on the fixture that main's scan command, verbatim, reports no
# hit (so main's lane, whose other invariants the candidate keeps and reports
# ok, is green), and that this gate refuses. With CHECKER=main's copy, every
# arm fails on the verdict.
def dc2_nul_claim; case_dc2_nul_claim() { mk dc2_nul_claim; printf 'x\000y. 82 refinement obligations proved unsat.\n' >"$R/docs/nul.md"
  REFS=UNSET; WANT=red; WHY='in a file holding a NUL byte'; ARM=2; }
def dc2_nul_mb_window; case_dc2_nul_mb_window() { mk dc2_nul_mb_window; printf 'x\000y\n%s\n' "$MBGAP" >"$R/docs/nul.tex"
  REFS=UNSET; WANT=red; WHY='in a file holding a NUL byte'; ARM=2; }
def dc2_invalid_tex; case_dc2_invalid_tex() { mk dc2_invalid_tex; printf 'caf\351. %s\n' "$CLAIM" >"$R/docs/latin1.tex"
  REFS=UNSET; WANT=red; WHY='docs/latin1.tex:1'; ARM=2; }
def dc2_invalid_ingap; case_dc2_invalid_ingap() { mk dc2_invalid_ingap; printf '82 wasm \351 obligations proved unsat.\n' >"$R/docs/latin1.tex"
  REFS=UNSET; WANT=red; WHY='docs/latin1.tex:1'; ARM=2; }
# _unreadable <path>: n/a when mode 000 does not stop this user reading it (root).
_unreadable() { if [ -r "$1" ] && { [ ! -d "$1" ] || ls "$1" >/dev/null 2>&1; }; then WANT=na; WHY='mode 000 does not stop reads here (root?)'; fi; }
def dc2_mode000_claim; case_dc2_mode000_claim() { mk dc2_mode000_claim; printf '%s\n' "$CLAIM" >"$R/docs/locked.tex"; chmod 000 "$R/docs/locked.tex"
  REFS=UNSET; WANT=red; WHY='docs/locked.tex: Permission denied'; ARM=2; _unreadable "$R/docs/locked.tex"; }
def dc2_mode000_noclaim; case_dc2_mode000_noclaim() { mk dc2_mode000_noclaim; echo note >"$R/docs/locked.tex"; chmod 000 "$R/docs/locked.tex"
  REFS=UNSET; WANT=red; WHY='could not read all of docs/'; ARM=2; _unreadable "$R/docs/locked.tex"; }
# An unreadable DIRECTORY: main refuses it too, by accident (invariant (3)'s
# `find docs` fails under set -e); this gate now names it in invariant (2).
def dc2_mode000_dir; case_dc2_mode000_dir() { mk dc2_mode000_dir; mkdir "$R/docs/locked"; printf '%s\n' "$CLAIM" >"$R/docs/locked/c.tex"
  chmod 000 "$R/docs/locked"; REFS=UNSET; WANT=red; WHY='docs/locked: Permission denied'; _unreadable "$R/docs/locked"; }
# The push reading judges the checkout with the same reading.
def dc2_push_nul; case_dc2_push_nul() { mk dc2_push_nul; printf 'x\000y. %s\n' "$CLAIM" >"$R/docs/nul.md"; commit_all nul
  upd "$BASE"; WANT=red; WHY='in a file holding a NUL byte'; ARM=2; }

# prepare <name>: reset the per-case variables and build the fixture.
prepare() {
  REFS=""; LOC=U; WANT=""; WHY=""; ENVX=(); ARM=0
  "case_$1"
}

# run_checker <script>: run <script> in $R the way the hook does; sets OUT, RC.
run_checker() {
  local script="$1" loc
  eval "loc=(\"\${${LOC}[@]}\")"
  RC=0
  if [ "$REFS" = UNSET ]; then
    OUT=$(cd "$R" && env -u TRUST_PUSHED_REFS "${loc[@]}" ${ENVX[@]+"${ENVX[@]}"} bash "$script" 2>&1) || RC=$?
  else
    OUT=$(cd "$R" && env TRUST_PUSHED_REFS="$REFS" "${loc[@]}" ${ENVX[@]+"${ENVX[@]}"} bash "$script" 2>&1) || RC=$?
  fi
}

# grade: the observed outcome of OUT/RC.
grade() {
  if [ "$RC" -eq 2 ]; then GOT=malformed
  elif [ "$RC" -ne 0 ] && grep -qE -- '^== .*: REFUSED — ' <<<"$OUT"; then GOT=refused
  elif [ "$RC" -ne 0 ]; then GOT=red
  elif grep -qE -- '^[[:space:]]*SKIPPED: ' <<<"$OUT"; then GOT=skip
  else GOT=green
  fi
}

# arm_proof: for a defect arm, main's lane (the standing reading here: it
# never read TRUST_PUSHED_REFS) passes, and the reading on a real checkout of
# the first pushed tree is red. Sets ARM_MSG on failure.
arm_proof() {
  local save_refs="$REFS" lsha w out rc=0
  REFS=UNSET; run_checker "$R/scripts/check_doc_counts.sh"; REFS="$save_refs"
  if [ "$RC" -ne 0 ]; then ARM_MSG="main's lane (the working-tree reading) already refuses this push (rc=$RC)"; return 1; fi
  lsha=$(awk '{print $2; exit}' <<<"$REFS")
  w="$TMP/arm-$(basename "$R")"
  git -C "$R" worktree add -q --detach "$w" "$lsha" >/dev/null 2>&1 || { ARM_MSG="cannot check out $lsha"; return 1; }
  out=$(cd "$w" && env -u TRUST_PUSHED_REFS "${U[@]}" bash "$w/scripts/check_doc_counts.sh" 2>&1) || rc=$?
  if [ "$rc" -eq 0 ]; then ARM_MSG="the reading on a checkout of $lsha is green: not a defect"; printf '%s\n' "$out" | sed 's/^/        | /'; return 1; fi
  return 0
}

# arm2_proof: for a doc-counts-2 arm, main's invariant-(2) scan command,
# verbatim, reports no hit on the fixture (in the case's locale), and every
# other invariant reports ok in this gate's output (they are main's verbatim),
# so main's lane passes it. Sets ARM_MSG on failure.
arm2_proof() {
  local loc out
  eval "loc=(\"\${${LOC}[@]}\")"
  out=$(cd "$R" && env "${loc[@]}" bash -c "grep -rInE '\\b82\\b[^.]{0,60}obligations?[^.]{0,30}\\b(proven|proved)\\b' \\
        docs 2>/dev/null || true" 2>&1)
  if [ -n "$out" ]; then ARM_MSG="main's scan command finds a hit here: not a doc-counts-2 case"; printf '%s\n' "$out" | sed 's/^/        | /'; return 1; fi
  if ! grep -qF 'ok  lean proof files' <<<"$OUT" || ! grep -qF 'ok  config recipes' <<<"$OUT"; then
    ARM_MSG="another invariant is not ok here, so main's lane would not pass on invariant (2) alone"; return 1
  fi
}

if [ "${DOC_COUNTS_TEST_LIB:-0}" = 1 ]; then
  return 0 2>/dev/null || exit 0
fi

PASSED=0
NA=()
FAILED=()
for name in "${CASES[@]}"; do
  [ -z "${ONLY:-}" ] || [ "$ONLY" = "$name" ] || continue
  prepare "$name" >/dev/null 2>&1 || { FAILED+=("$name (fixture)"); echo "  FAIL  $name: the fixture could not be built"; continue; }
  if [ "$WANT" = na ]; then NA+=("$name"); printf '  n/a   %-22s %s\n' "$name" "$WHY"; continue; fi
  run_checker "$R/scripts/check_doc_counts.sh"
  grade
  if [ "$GOT" = "$WANT" ] && { [ -z "$WHY" ] || grep -qF -- "$WHY" <<<"$OUT"; }; then
    if { [ "$ARM" = 1 ] && ! arm_proof; } || { [ "$ARM" = 2 ] && ! arm2_proof; }; then
      FAILED+=("$name (arm)"); printf '  FAIL  %-22s defect arm not proven: %s\n' "$name" "$ARM_MSG"
    else
      PASSED=$((PASSED + 1)); printf '  ok    %-22s %s%s\n' "$name" "$GOT" "$([ "$ARM" = 1 ] && echo '  (defect arm: main passes it, a checkout of it is red)'; [ "$ARM" = 2 ] && echo '  (doc-counts-2 arm: main'"'"'s scan reads no hit here)')"
    fi
  else
    FAILED+=("$name"); printf '  FAIL  %-22s want %s citing %s, got %s (rc=%s)\n' "$name" "$WANT" "'$WHY'" "$GOT" "$RC"
    printf '%s\n' "$OUT" | sed 's/^/        | /'
  fi
  chmod -R u+rwx "$R" 2>/dev/null || true
done

# A real `git push` through a minimal pre-push hook that exports git's lines
# and destination URL, as scripts/hooks/pre-push does.
if [ -z "${ONLY:-}" ] || [ "$ONLY" = HOOK ]; then
  mk HOOK
  cat >"$R/.git/hooks/pre-push" <<'EOF'
#!/usr/bin/env bash
TRUST_PUSHED_REFS="$(cat)"
export TRUST_PUSHED_REFS
export TRUST_PUSH_REMOTE="${2:-}"
exec bash scripts/check_doc_counts.sh
EOF
  chmod +x "$R/.git/hooks/pre-push"
  git -C "$R" config core.hooksPath "$R/.git/hooks"
  echo "clean" >"$R/docs/clean.md"; commit_all clean
  RC=0; OUT=$(cd "$R" && git push origin main 2>&1) || RC=$?
  if [ "$RC" -eq 0 ] && grep -qF 'judged the checkout' <<<"$OUT"; then
    PASSED=$((PASSED + 1)); echo "  ok    HOOK                   a real git push of a clean docs change is judged as the checkout and passes"
  else FAILED+=("HOOK clean"); echo "  FAIL  HOOK  clean push (rc=$RC)"; printf '%s\n' "$OUT" | sed 's/^/        | /'; fi
  git -C "$R" checkout -qb side; echo "$CLAIM" >"$R/docs/clean.md"; commit_all bad; git -C "$R" checkout -q main
  RC=0; OUT=$(cd "$R" && git push origin side:main 2>&1) || RC=$?
  if [ "$RC" -ne 0 ] && grep -qF 'REFUSED' <<<"$OUT" && [ "$(git -C "$ORIGIN" rev-parse main)" != "$SHA" ]; then
    PASSED=$((PASSED + 1)); echo "  ok    HOOK                   a real git push side:main of a claim is refused and origin does not move"
  else FAILED+=("HOOK side"); echo "  FAIL  HOOK  side push (rc=$RC)"; printf '%s\n' "$OUT" | sed 's/^/        | /'; fi
  git -C "$R" checkout -q side
  RC=0; OUT=$(cd "$R" && git push origin side:main 2>&1) || RC=$?
  if [ "$RC" -ne 0 ] && grep -qF 'inflated wasm proof count' <<<"$OUT" && [ "$(git -C "$ORIGIN" rev-parse main)" != "$SHA" ]; then
    PASSED=$((PASSED + 1)); echo "  ok    HOOK                   the same push from a checkout of it is judged red and origin does not move"
  else FAILED+=("HOOK bad"); echo "  FAIL  HOOK  bad push (rc=$RC)"; printf '%s\n' "$OUT" | sed 's/^/        | /'; fi
fi

echo
[ "${#NA[@]}" -eq 0 ] || echo "check_doc_counts_test: ${#NA[@]} case(s) NOT RUN (n/a here, not passed): ${NA[*]}"
if [ "${#FAILED[@]}" -eq 0 ]; then
  echo "check_doc_counts_test: all ${PASSED} cases passed"
  exit 0
fi
echo "check_doc_counts_test: ${#FAILED[@]} case(s) FAILED, ${PASSED} passed:"
printf '  %s\n' "${FAILED[@]}"
exit 1
