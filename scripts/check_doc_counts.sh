#!/usr/bin/env bash
# check_doc_counts.sh — Doc-truth gate (gap G26).
#
# Cross-checks human-readable count claims in docs/reports against the in-repo
# source of truth, so optimistic drift fails CI instead of relying on manual scrubs.
#
# Invariants checked:
#   (1) proofs/trust-soundness/README.md EXISTS, and the number of .lean files in
#       proofs/trust-soundness/ matches the "N/N" verified-count claim in it.
#       Absence is a FAILURE, not a skip: a `rm` or a rename during a proofs/
#       reorg would otherwise retire this invariant silently, and no other gate
#       in scripts/ or tests/ mentions that README.
#   (2) No doc presents the INFLATED wasm headline ("82 ... proven unsat"): the
#       honest genuine-obligation count is 54 (28 of the original 82 were
#       degenerate X==X self-equalities). Source of truth:
#       first-party/trust-cg/crates/trust-cg-verify/src/wasm_lowering_proofs.rs.
#       The scan is fail-CLOSED: it refuses when it cannot read part of docs/
#       and reads the lines `grep -rI` cannot (see "doc-counts-2" below).
#
#   (4) The generated std name lists in docs/TCB.md match their source
#       (`tools/gen_tcb_std_lists.py --check`). Nothing ran that check, so the block
#       drifted for weeks while the generator itself died on a broken anchor, and
#       nobody noticed until a doc sweep did (2026-09-28).
#
# Exit 0 iff all invariants hold.
#
# ===========================================================================
# WHICH TREE IS READ — the working-tree reading, and the push reading
# ===========================================================================
# The invariants are ONE function, `doc_counts_reading`, which reads the
# checkout it is run in. It is main's reading (moved into a function), edited
# only where invariant (2) was fail-open (doc-counts-2, below), and nothing
# below re-implements any part of it.
#
# STANDING READING — TRUST_PUSHED_REFS unset, empty or blank: the function runs
# on this checkout's working tree. No SUBJECT line is added, and the output and
# exit status are byte for byte what they were before the push reading existed,
# except where a doc-counts-2 finding (below) fires.
#
# PUSH READING — TRUST_PUSHED_REFS names at least one ref (scripts/hooks/pre-push
# exports git's pre-push lines, "<local-ref> <local-sha> <remote-ref>
# <remote-sha>", and TRUST_PUSH_REMOTE, git's destination URL). Before 2026-09-28
# the gate ignored the push and read the working tree, which can differ from
# every tree being published (docs/issues/2026-09-28-doc-counts-judges-the-
# worktree-not-the-push.md, doc-counts-1). Five rounds of fixes re-implemented
# what a checkout would hold in git terms (then with `git archive`), and each
# was found to read less than main in some corner. So the push reading does not
# lay anything out. It establishes, per pushed ref, that the verdict of the
# reading on a checkout of the pushed tree is ALREADY KNOWN, or it refuses:
#
#   SCOPE — the top-level entries the reading can reach, derived from the code
#   above (never from a list of what "usually" matters):
#     * `docs`                    invariants (2) and (3): `grep -r docs`,
#                                 `find docs -name '*.md'`;
#     * `proofs`                  invariant (1): `find proofs/trust-soundness`
#                                 and proofs/trust-soundness/README.md. The
#                                 WHOLE `proofs` entry, not the subdirectory, so
#                                 a sibling a case-folding filesystem opens as
#                                 trust-soundness is compared too;
#     * `.gitattributes`          the root attributes a checkout converts the
#                                 files above with (nested ones sit inside the
#                                 two subtrees and are compared with them);
#     * every other top-level entry a checkout could open as one of those: a
#       name that folds to one of them in ASCII case, a name holding any byte
#       outside printable ASCII (Unicode folding and normalisation: U+017F,
#       U+212A, NFC/NFD), or a name holding '/' (a tree git never writes, which
#       a checkout writes INTO docs/ or proofs/).
#   An entry is compared as its raw `git ls-tree` record (mode, object id,
#   name) with replace refs disabled, so gitlinks count and no ignore or
#   export setting hides anything. A symbolic link anywhere in SCOPE lets the
#   reading reach outside it (README.md -> ../../PROOFCOUNT.md; `docs` -> d2;
#   a link that climbs out of the checkout), so a tree whose SCOPE holds one is
#   never skipped and never judged as the checkout: it is refused.
#
#   For each pushed ref (a deletion lands no tree and judges nothing), with
#   T = <local-sha>^{tree} (it must resolve, else exit 2):
#   (1) SKIP when T's SCOPE records equal BASE's and hold no symbolic link.
#       BASE is <remote-sha>^{tree} when that object is in this store; for a new
#       ref, the tree of the merge-base of <local-sha> with
#       refs/remotes/<dest>/main, where <dest> is the remote TRUST_PUSH_REMOTE
#       names (a remote name, or a URL one of a remote's urls/pushurls equals,
#       raw or as `git remote get-url [--push] --all` rewrites it through
#       insteadOf/pushInsteadOf — git's pre-push $2 is the rewritten URL;
#       origin when TRUST_PUSH_REMOTE is unset or empty). A destination that is
#       not known here, a remote sha not in this store, or no fork point: no
#       BASE. The fork point is local state, like the tracking ref itself:
#       replace refs are off, but .git/info/grafts still shapes merge-base.
#       What the destination already carries is not re-judged — that is the
#       one way this reading passes a tree main's reading on its checkout would
#       fail (a claim published before this gate could see it).
#   (2) JUDGE THE CHECKOUT when T's SCOPE records equal HEAD's, SCOPE holds no
#       symbolic link or gitlink, and this checkout provably holds HEAD there:
#         - core.autocrlf unset or false;
#         - no in-scope file carries text/eol/crlf/filter/ident/working-tree-
#           encoding (git check-attr: the worktree, index, info/attributes and
#           core.attributesFile) — so a checkout writes every blob's bytes raw.
#           A `filter.<driver>.*` key in git config converts nothing on its
#           own: git runs a driver only for a path whose `filter` attribute
#           names it, and that attribute is what check-attr reads. Until
#           2026-10-24 any filter.* key refused by name, so the owner's global
#           `filter.lfs` (Trust sets no filter attribute) refused every push
#           that changed docs/, and pushes went out under a GIT_CONFIG_GLOBAL
#           copy with the key removed (docs/DECISION_QUEUE.md
#           PUSH-PATH-DOC-COUNTS-FILTER);
#         - the index holds no skip-worktree or assume-unchanged entry in SCOPE
#           and equals HEAD there (`git diff-index --cached`);
#         - the working tree's BYTES equal HEAD's in SCOPE: `git diff HEAD`
#           against a fresh temporary index of HEAD's SCOPE entries, with no stat
#           data, so every in-scope file is re-read (no stat cache, fsmonitor
#           or untracked cache is trusted, and the real index is not written);
#         - nothing untracked in SCOPE (`ls-files --others --exclude-standard`),
#           and nothing at all — ignored files and empty directories included —
#           under proofs/trust-soundness, whose NAMES invariant (1) counts.
#           Ignored files under docs/ are allowed: invariants (2) and (3) only
#           ever add a hit for an extra file, so an extra file can make this
#           reading refuse more than a checkout would, never less;
#         - docs/ and proofs/trust-soundness/ are, on disk, directories with
#           exactly those names (readdir's names, via `find -name`; getcwd is
#           not evidence): git's untracked scan follows the on-disk name, the
#           reading follows the kernel's folding. When HEAD holds no file under
#           one of them, nothing may exist at that path;
#         - every tracked path under them is stored on disk under exactly its
#           index name (readdir's bytes, not git's case-folded or precomposed
#           lstat), and proofs/trust-soundness/'s top-level names are exactly
#           HEAD's there: a docs/recipe.MD standing for docs/recipe.md reads
#           clean to git and is invisible to the reading's `find -name '*.md'`;
#         - no FIFO, socket or device under either directory.
#       Then the function runs once on this checkout and its verdict stands for
#       every ref that qualifies.
#   (3) Otherwise REFUSE (exit 1), naming the ref and why: the push changes
#       SCOPE to content this checkout does not hold. Check that ref out (and
#       leave it clean in SCOPE) and push again.
#   The verdict is red if any ref is red or refused. A malformed line (not four
#   fields, or a sha that is not 40 or 64 hex digits) is exit 2, like the
#   sibling push lanes.
#
# ===========================================================================
# doc-counts-2 — invariant (2) was fail-open (fixed 2026-09-28)
# ===========================================================================
# Main's scan was `grep -rInE '<pat>' docs 2>/dev/null || true`. Measured with
# macOS's BSD grep 2.6.0-FreeBSD, it passed a claim three ways:
#   * grep's error exit (2) read as "no match": a mode-000 file (or an
#     unreadable directory, or a missing docs/) made the scan green — and with a
#     non-.md name, the whole lane, since invariant (3) opens only *.md files;
#   * -I skips a file grep classes as binary: one NUL byte in its first buffer
#     (an invalid UTF-8 byte does NOT make a file binary here);
#   * in text mode, under a UTF-8 locale, grep's regex matches NOTHING on a
#     line holding an invalid byte (not even a literal word on that line), so
#     a claim on such a line was invisible. Only an undecodable *.md line was
#     caught, by accident: invariant (3)'s awk exits 2 on it under set -e.
# The fix keeps main's scan, in the caller's locale (the {0,60}/{0,30} windows
# count CHARACTERS: an earlier round's LC_ALL=C counted bytes and missed claims
# main catches), and adds, never replaces:
#   (a) pass 1's exit status is read: 1 = no hit; above 1 refuses, naming
#       grep's stderr (600 bytes at most, from a re-run: the verdict is the
#       first run's status);
#   (b) pass 2 (dc_scan_pass2) examines every file whose BYTES hold
#       82 ... obligation ... prove on one line (a C-locale `grep -ra`, which
#       every match of the pattern under any reading implies), and
#         - scans a binary-classed one with main's pattern in main's locale, as
#           TEXT with each NUL read as a space (grep -a on a binary-classed
#           file matches byte-wise even under a UTF-8 locale, measured);
#         - refuses, by file and line, a line the locale cannot decode that
#           holds those words: its characters cannot be counted. This refuses
#           the honest sentence too on such a line — a conservative cost.
#   Nothing is exempt by name, extension or magic (a %PDF file is scanned).
# Where none of these fires, the output is main's byte for byte.
set -euo pipefail
cd "$(git -C "$(dirname "$0")/.." rev-parse --show-toplevel)"

# dc_stream <file> <grep-args...>: grep, in the caller's locale and in TEXT
# mode, over <file> with each NUL byte read as a space. Exit 3 when the file
# cannot be read, else grep's status. Why the NUL rewrite: BSD grep 2.6.0
# matches a file it classes as binary (a NUL in its first buffer) BYTE-wise
# even with -a under a UTF-8 locale (measured: 26 em-dash characters, 74
# bytes, miss {0,60} there and hit in text mode). NUL -> space keeps every
# character count, word boundary and sentence boundary the pattern reads (both
# are one non-word character that is not '.'), and makes the stream text.
dc_stream() (
  set +e +o pipefail
  f="$1"; shift
  LC_ALL=C tr '\000' ' ' 2>/dev/null <"$f" | grep "$@" 2>/dev/null
  s=("${PIPESTATUS[@]}")
  [ "${s[0]}" -eq 0 ] || exit 3
  exit "${s[1]}"
)

# dc_scan_pass2: invariant (2)'s second pass (doc-counts-2). Reads dc_pat;
# sets dc_bin (hits in NUL-holding files, "file:line:text"), dc_undec
# ("file:line" of undecodable lines holding the claim's words) and appends to
# dc_err. Every line any reading of the pattern can match holds the BYTES 82,
# obligation and prove in that order, so a C-locale `82.*obligation.*prove` over
# every file (-a: binary ones too) names every file that can matter; only those
# are examined further, in the caller's locale except where stated.
dc_scan_pass2() {
  local f r u l n prc=missing NL=$'\n'
  dc_bin="" dc_undec=""
  while IFS= read -r -d '' f; do
    case "$f" in status:*) prc="${f#status:}"; continue ;; esac
    # (a) A file `grep -I` classes as binary: pass 1 skipped it whole. Scan it
    #     with main's pattern in main's locale, as text (dc_stream).
    r=0; grep -Iq -e '' -- "$f" 2>/dev/null || r=$?
    if [ "$r" -eq 1 ]; then
      r=0; u="$(dc_stream "$f" -nE "$dc_pat" | LC_ALL=C tr -c '\n\t\040-\176\200-\377' '?' | LC_ALL=C cut -b 1-300)" || r=$?
      if [ "$r" -eq 0 ]; then
        while IFS= read -r l; do dc_bin="${dc_bin:+$dc_bin$NL}$f:$l"; done <<<"$u"
      elif [ "$r" -ne 1 ]; then dc_err="${dc_err:+$dc_err$NL}the text scan of $f exited $r"; continue; fi
    elif [ "$r" -ne 0 ]; then dc_err="${dc_err:+$dc_err$NL}grep -I exited $r on $f"; continue
    fi
    # (b) A line that is not valid in the caller's locale (an invalid UTF-8
    #     byte under a UTF-8 locale): in text mode BSD grep's regex matches
    #     NOTHING on it (measured: not even a literal word on that line), and
    #     the file is not classed binary for it, so pass 1 cannot see a claim
    #     there. Its characters cannot be counted, so such a line holding the
    #     claim's words in order is refused by name. "Undecodable" = the
    #     locale's regex cannot match '^.*$' against it.
    r=0; u="$(dc_stream "$f" -nvE '^.*$' | LC_ALL=C cut -d: -f1)" || r=$?
    if [ "$r" -eq 1 ]; then continue
    elif [ "$r" -ne 0 ]; then dc_err="${dc_err:+$dc_err$NL}the decodability scan of $f exited $r"; continue; fi
    r=0; l="$(LC_ALL=C grep -anE '82.*obligation.*prove' -- "$f" 2>/dev/null | LC_ALL=C tr '\000' ' ' | LC_ALL=C cut -d: -f1)" || r=$?
    if [ "$r" -gt 1 ]; then dc_err="${dc_err:+$dc_err$NL}the byte scan of $f exited $r"; continue; fi
    for n in $l; do
      case $'\n'"$u"$'\n' in *$'\n'"$n"$'\n'*) dc_undec="${dc_undec:+$dc_undec$NL}$f:$n" ;; esac
    done
  done < <(r=0; LC_ALL=C grep -raEl --null '82.*obligation.*prove' docs 2>/dev/null || r=$?; printf 'status:%s\0' "$r")
  # 1 = no file can matter. Anything else but 0 (or no status at all) refuses;
  # pass 1 has usually named the unreadable path already.
  case "$prc" in 0 | 1) ;; *) dc_err="${dc_err:+$dc_err$NL}the byte-level prefilter over docs/ exited $prc" ;; esac
  return 0
}

# The reading: main's invariants. It reads the current directory. Invariants
# (1) and (3) are main's verbatim; (2) is main's scan with doc-counts-2 fixed.
doc_counts_reading() {
fail=0

# (1) Lean proof-file count vs README claim.
actual_lean="$(find proofs/trust-soundness -maxdepth 1 -name '*.lean' | wc -l | tr -d ' ')"
readme="proofs/trust-soundness/README.md"
if [ ! -f "$readme" ]; then
  echo "FAIL (G26): ${readme} is missing; the lean-count invariant cross-checks it."
  echo "            If the README moved, point this check at its new path — do not"
  echo "            let the ${actual_lean}-file count claim go ungated."
  fail=1
else
  # Accept the count if the README mentions it as "<actual>/<actual>" or "<actual> files".
  if ! grep -Eq "(\b${actual_lean}/${actual_lean}\b|\b${actual_lean} (proof )?files\b)" "$readme"; then
    echo "FAIL (G26): proofs/trust-soundness has ${actual_lean} .lean files, but README.md does not state that count (stale 31/31 or 30?)."
    grep -nE "verified:?\s*[0-9]+/[0-9]+|[0-9]+ (proof )?files|[0-9]+ declarations" "$readme" | head -5 || true
    fail=1
  else
    echo "ok  lean proof files: ${actual_lean} (README consistent)"
  fi
fi

# (2) No inflated wasm "82 ... proven" headline in the superproject's own docs/.
# (trust-cg's canonical wasm doc lives in the submodule and is that repo's concern.)
#
# The pattern is deliberately NOT a list of the two historical sentences: that
# was a regression lock over one phrasing, and "82 wasm obligations proven
# unsat" / "82 refinement obligations proved unsat" both walked straight past
# it. It now matches the count, then the noun `obligation(s)`, then the verb,
# all within one sentence (`[^.]` bounds each gap, so a match cannot span a
# sentence boundary). The `obligations?` anchor is load-bearing:
# without it a bare source position such as `frontier.rs:82:4) is UNKNOWN, not
# proved` matches and the gate reds on a healthy tree. The honest framing
# ("82 total obligations, of which 54 are genuine … nothing is claimed proven
# for them") is outside the 30-char gap and stays green.
#
# The scan is fail-CLOSED (doc-counts-2; see the header). Pass 1 is main's
# scan, same pattern, same caller's locale, with its exit status read: 0 =
# hits, 1 = none, anything else = grep could not read part of docs/ (a mode-000
# file, an unreadable directory, a missing docs/), so "no claim" would be
# unfounded and the gate refuses. Pass 2 (dc_scan_pass2) reads what pass 1
# cannot: binary-classed files, still counting characters in the caller's
# locale, and lines that locale cannot decode.
dc_pat='\b82\b[^.]{0,60}obligations?[^.]{0,30}\b(proven|proved)\b'
dc_rc=0
hits="$(grep -rInE "$dc_pat" docs 2>/dev/null)" || dc_rc=$?
dc_err=""
if [ "$dc_rc" -gt 1 ]; then
  # The verdict is the run above; this re-run only names what grep said.
  dc_err="grep -r over docs/ exited $dc_rc: $(grep -rInE "$dc_pat" docs 2>&1 >/dev/null | head -c 600 || true)"
fi
dc_scan_pass2
if [ -n "$hits" ] || [ -n "$dc_bin" ]; then
  echo "FAIL (G26): inflated wasm proof count (82) presented as proven; honest count is 54:"
  [ -z "$hits" ] || echo "$hits" | sed 's/^/  /'
  if [ -n "$dc_bin" ]; then
    echo "$dc_bin" | sed 's/^/  /'
    echo "  (the line(s) just above are in a file holding a NUL byte, which \`grep -I\` skips as binary; control bytes shown as ?, 300 bytes at most)"
  fi
  fail=1
fi
if [ -n "$dc_undec" ]; then
  echo "FAIL (G26): line(s) in docs/ are not valid text in this locale (${LC_ALL:-${LC_CTYPE:-${LANG:-C}}}), so the"
  echo "            headline scan cannot read them as characters, and each holds the claim's words"
  echo "            in order (82 ... obligation ... prove): the gate cannot rule the claim out. Fix the encoding:"
  echo "$dc_undec" | LC_ALL=C tr -c '\n\t\040-\176\200-\377' '?' | sed 's/^/  /'
  fail=1
fi
if [ -n "$dc_err" ]; then
  echo "FAIL (G26): the wasm-headline scan could not read all of docs/, so its \"no claim\" would be unfounded:"
  printf '%s\n' "$dc_err" | LC_ALL=C tr -c '\n\040-\176' '?' | sed 's/^/  /'
  fail=1
fi
if [ -z "$hits" ] && [ -z "$dc_bin" ] && [ -z "$dc_undec" ] && [ -z "$dc_err" ]; then
  echo "ok  wasm headline: no inflated '82 ... proven' claim"
fi

# (3) No published `.cargo/config.toml` recipe may set a `-Ztrust-*` flag in a
#     `[host]` stanza or under a `[profile.<p>.package.*]` table. `targo trust`
#     hard-errors on either one:
#       `[host] rustflags cannot set -Ztrust_verify during a verified Targo
#        invocation`   (…/build_context/target_info.rs,
#                       `reject_host_config_trust_policy`)
#       `profile rustflags cannot set rustc-equivalent -Ztrust_verify during a
#        verified Targo invocation`   (…/compiler/mod.rs, `reject_parallel_source`
#                       on `unit.profile.rustflags`)
#     so a recipe carrying either locks the authenticated lane out of every
#     checkout that pastes it. This invariant exists because the recipe
#     published in docs/TOOLCHAIN_POSTURE.md §4.2.1 carried BOTH from 2026-08-31
#     until 2026-09-20, was copied into two other docs, and was the first thing a
#     converting repo pasted. The profile half is the nastier of the two: it is
#     checked per unit, so a dependency-free probe crate never resolves a unit
#     that carries it and reports a clean PASS.
#     Both lanes belong on the measurement command line (`--config
#     'host.rustflags=[…]'`, `--config 'profile.dev.package."*".rustflags=[…]'`),
#     which reaches one invocation and no `targo trust` run.
#
#     Matches a `[host]` / `[host.<triple>]` / `[profile.*.package.*]` table
#     header followed, before the next table header, by a line mentioning
#     `-Ztrust`/`-Z trust`, and the dotted-key file spellings at the start of a
#     line. Everything is anchored at column 0, so prose that quotes the refusal
#     and the sanctioned `--config '…'` command lines — which are the fix, not
#     the defect — do not match. Per-file state is reset at FNR==1: without that,
#     one file's open stanza leaks into the next file scanned.
#     `/dev/null` is passed as awk's first file so awk never falls back to
#     reading stdin when the file list is empty, and awk's stderr is NOT
#     suppressed: a broken program here must fail the gate, not pass it quietly.
host_hits="$(
  find docs -name '*.md' -type f -print0 \
  | xargs -0 awk '
      FNR == 1 { instanza = 0; hdr = 0; what = "" }
      /^\[host(\.[^]]*)?\][ \t]*$/ {
          instanza = 1; hdr = FNR; what = "[host]"; next }
      /^\[profile\.[^]]*\.package\.[^]]*\][ \t]*$/ {
          instanza = 1; hdr = FNR; what = "profile package"; next }
      /^\[/ { instanza = 0 }
      instanza && /-Z ?trust/ {
          printf "%s:%d: %s stanza opened at line %d sets: %s\n", FILENAME, FNR, what, hdr, $0 }
      /^(host(\.[^ \t=]*)?|profile\.[^ \t=]*\.package\.[^ \t=]*)\.rustflags[ \t]*=/ && /-Z ?trust/ {
          printf "%s:%d: dotted key sets: %s\n", FILENAME, FNR, $0 }
    ' /dev/null
)"
if [ -n "$host_hits" ]; then
  echo "FAIL (G26): a published .cargo/config.toml recipe sets a -Ztrust-* flag in [host]"
  echo "            or under a profile package table; either hard-errors \`targo trust\`"
  echo "            in any checkout that pastes it. Those lanes go on the measurement"
  echo "            command line — see docs/TOOLCHAIN_POSTURE.md §4.2.1."
  echo "$host_hits" | sed 's/^/  /'
  fail=1
else
  echo "ok  config recipes: no [host]/profile-package stanza sets -Ztrust-* in docs/"
fi

# (4) The generated TCB std name lists are current.
if tcb_out="$(python3 tools/gen_tcb_std_lists.py --check 2>&1)"; then
  echo "ok  TCB std name lists: current with their source"
else
  echo "FAIL (G26): the generated std name lists in docs/TCB.md do not match their source."
  echo "            Run: python3 tools/gen_tcb_std_lists.py --write (an 'anchor drift'"
  echo "            line means the generator itself needs its anchor updated first)."
  echo "$tcb_out" | tail -3 | sed 's/^/  /'
  fail=1
fi

[ "$fail" -eq 0 ] && echo && echo "DOC COUNTS OK" || { echo; echo "DOC-TRUTH GATE FAILED"; exit 1; }
}

# ===========================================================================
# The push reading (see "WHICH TREE IS READ" above).
# ===========================================================================
PR_WORK=""
pr_cleanup() { if [ -n "$PR_WORK" ]; then rm -rf -- "${PR_WORK:?}"; fi; }

# pr_malformed <message>: exit 2 — this push's lines cannot be read.
pr_malformed() {
  echo "doc-counts: $1" >&2
  echo "doc-counts: cannot tell what this push lands, so nothing is judged — refusing (exit 2)" >&2
  exit 2
}

# pr_scope <tree> <out>: the raw `ls-tree -z` records of <tree>'s top-level
# entries in SCOPE, NUL-terminated, in the tree's own order. Byte tests run
# under C in this subshell only; the reading keeps the caller's locale.
pr_scope() (
  export LC_ALL=C
  git ls-tree -z "$1" >"$PR_WORK/ls" || exit 1
  : >"$2"
  while IFS= read -r -d '' rec; do
    name="${rec#*$'\t'}"
    case "$name" in
      [Dd][Oo][Cc][Ss] | [Pp][Rr][Oo][Oo][Ff][Ss] | .[Gg][Ii][Tt][Aa][Tt][Tt][Rr][Ii][Bb][Uu][Tt][Ee][Ss]) ;;
      */* | *[!\ -~]*) ;;
      *) continue ;;
    esac
    printf '%s\0' "$rec" >>"$2"
  done <"$PR_WORK/ls"
)

# pr_names <scope-file>: the entries' names, NUL-terminated.
pr_names() (
  export LC_ALL=C
  while IFS= read -r -d '' rec; do printf '%s\0' "${rec#*$'\t'}"; done <"$1"
)

# pr_differ <scope-a> <scope-b>: the names whose records differ, shell-quoted.
pr_differ() (
  export LC_ALL=C
  a=() b=() out=""
  while IFS= read -r -d '' rec; do a+=("$rec"); done <"$1"
  while IFS= read -r -d '' rec; do b+=("$rec"); done <"$2"
  for x in ${a[@]+"${a[@]}"}; do
    hit=0; for y in ${b[@]+"${b[@]}"}; do [ "$x" != "$y" ] || hit=1; done
    [ "$hit" = 1 ] || out="$out $(printf '%q' "${x#*$'\t'}")"
  done
  for y in ${b[@]+"${b[@]}"}; do
    hit=0; for x in ${a[@]+"${a[@]}"}; do [ "$x" != "$y" ] || hit=1; done
    case " $out " in *" $(printf '%q' "${y#*$'\t'}") "*) ;; *) [ "$hit" = 1 ] || out="$out $(printf '%q' "${y#*$'\t'}")" ;; esac
  done
  echo "${out# }"
)

# pr_link <scope-file> <gitlinks-too>: the first symbolic link (and, with
# <gitlinks-too> = 1, gitlink) in SCOPE, described; nothing if there is none.
# A tree that cannot be listed is reported as if it held one (refuse, not pass).
pr_link() (
  export LC_ALL=C
  set +o pipefail   # grep -m1 may close the pipe early; its own status decides
  while IFS= read -r -d '' rec; do
    meta="${rec%%$'\t'*}"; name="${rec#*$'\t'}"; mode="${meta%% *}"; oid="${meta##* }"
    case "$mode" in
      120000) printf 'a symbolic link at %q\n' "$name"; exit 0 ;;
      160000) if [ "$2" = 1 ]; then printf 'a gitlink at %q\n' "$name"; exit 0; fi ;;
      040000)
        git ls-tree -r -z "$oid" >"$PR_WORK/rec" || { printf 'an unreadable tree at %q\n' "$name"; exit 0; }
        pat='^120000 '; [ "$2" = 1 ] && pat='^(120000|160000) '
        rc=0; hit="$(tr '\0' '\n' <"$PR_WORK/rec" | grep -m1 -E "$pat")" || rc=$?
        if [ "$rc" -eq 0 ]; then
          case "$hit" in 120000*) k='a symbolic link' ;; *) k='a gitlink' ;; esac
          printf '%s at %q/%q\n' "$k" "$name" "${hit#*$'\t'}"; exit 0
        fi
        [ "$rc" -eq 1 ] || { printf 'an unlistable tree at %q\n' "$name"; exit 0; }
        ;;
    esac
  done <"$1"
)

# pr_first <nul-list>: the first three names of a NUL-separated list, quoted.
pr_first() (
  export LC_ALL=C
  k=0; out=""
  while IFS= read -r -d '' rec && [ "$k" -lt 3 ]; do out="$out $(printf '%q' "$rec")"; k=$((k + 1)); done <"$1"
  echo "${out# }"
)

# pr_dest_remote: the destination's remote name, or nothing when it is unknown.
# TRUST_PUSH_REMOTE is a remote name or git's destination URL; a URL matches a
# remote whose configured url/pushurl equals it, raw or rewritten (insteadOf /
# pushInsteadOf, as `git remote get-url` applies them). origin wins a tie.
pr_dest_remote() {
  local v="${TRUST_PUSH_REMOTE:-}" name url hit=""
  [ -n "$v" ] || { echo origin; return 0; }
  while IFS= read -r name; do
    [ "$name" != "$v" ] || { echo "$v"; return 0; }
  done < <(git remote 2>/dev/null || true)
  while IFS= read -r name; do
    [ -n "$name" ] || continue
    while IFS= read -r url; do
      [ "$url" = "$v" ] || continue
      if [ "$name" = origin ] || [ -z "$hit" ]; then hit="$name"; fi
    done < <(git config --get-all "remote.$name.url" 2>/dev/null || true
             git config --get-all "remote.$name.pushurl" 2>/dev/null || true
             git remote get-url --all "$name" 2>/dev/null || true
             git remote get-url --push --all "$name" 2>/dev/null || true)
  done < <(git remote 2>/dev/null || true)
  echo "$hit"
}

# pr_on_disk <a/b/...>: every component is a real directory (not a link)
# whose STORED name is exactly that component: readdir's names, matched by
# find -name. (getcwd is not evidence: macOS answers it from the name cache
# with the spelling last used to look a directory up.)
pr_on_disk() {
  local parent=. comp rest="$1" hit
  while [ -n "$rest" ]; do
    comp="${rest%%/*}"; [ "$comp" != "$rest" ] && rest="${rest#*/}" || rest=""
    hit="$(find "$parent" -mindepth 1 -maxdepth 1 -name "$comp" -type d -print 2>/dev/null)" || return 1
    [ "$hit" = "$parent/$comp" ] || return 1
    parent="$parent/$comp"
  done
}

# pr_checkout_holds_head <head-scope-file>: 0 when this checkout provably holds
# HEAD in SCOPE (so the reading here is the reading of a checkout of HEAD);
# otherwise 1 with the reason in PR_WHY.
pr_checkout_holds_head() {
  local head_scope="$1" rc out rec tag path attr val p kind
  local -a specs=(docs proofs .gitattributes)
  pr_names "$head_scope" >"$PR_WORK/names"
  while IFS= read -r -d '' rec; do specs+=("$rec"); done <"$PR_WORK/names"

  # A filter driver in config is judged where it can act: the `filter`
  # attribute check-attr reads below (the header, invariant (2)).
  rc=0; out="$(git config --list 2>&1 >/dev/null)" || rc=$?
  [ "$rc" -eq 0 ] || { PR_WHY="git config cannot be read: $out"; return 1; }
  out="$(git config --get core.autocrlf 2>/dev/null || true)"
  case "$out" in "" | false | no | off | 0) ;; *) PR_WHY="core.autocrlf=$out converts line endings on checkout"; return 1 ;; esac

  git --literal-pathspecs ls-files -v -z -- "${specs[@]}" >"$PR_WORK/tags" \
    || { PR_WHY="git ls-files -v failed"; return 1; }
  while IFS= read -r -d '' rec; do
    tag="${rec%% *}"; path="${rec#* }"
    [ "$tag" = H ] || { PR_WHY="the index marks $(printf '%q' "$path") '$tag' (skip-worktree, assume-unchanged or unmerged): git does not compare it with the working tree"; return 1; }
  done <"$PR_WORK/tags"
  rc=0; git --literal-pathspecs diff-index --cached --quiet HEAD -- "${specs[@]}" || rc=$?
  [ "$rc" -eq 0 ] || { PR_WHY="the index differs from HEAD there (staged changes, rc=$rc)"; return 1; }

  git --literal-pathspecs ls-files -z -- "${specs[@]}" >"$PR_WORK/files" \
    || { PR_WHY="git ls-files failed"; return 1; }
  git check-attr -z --stdin text eol crlf filter ident working-tree-encoding \
    <"$PR_WORK/files" >"$PR_WORK/attrs" || { PR_WHY="git check-attr failed"; return 1; }
  while IFS= read -r -d '' path && IFS= read -r -d '' attr && IFS= read -r -d '' val; do
    case "$val" in unspecified | unset) ;; *)
      PR_WHY="$(printf '%q' "$path") has $attr=$val, a checkout conversion"; return 1 ;;
    esac
  done <"$PR_WORK/attrs"

  # The temporary index holds HEAD's entries in SCOPE only: an index read from
  # all of HEAD has no stat data anywhere, and diff's auto-refresh then re-hashes
  # every tracked file in the repository (measured: 25 s of a 26 s push reading
  # on this repository); outside SCOPE the pathspecs below never look.
  rc=0; git --literal-pathspecs ls-tree -r -z HEAD -- "${specs[@]}" >"$PR_WORK/headls" 2>"$PR_WORK/err" || rc=$?
  [ "$rc" -eq 0 ] || { PR_WHY="HEAD cannot be listed there: $(head -c 300 "$PR_WORK/err")"; return 1; }
  rc=0; out="$(GIT_INDEX_FILE="$PR_WORK/index" git update-index -z --index-info <"$PR_WORK/headls" 2>&1)" || rc=$?
  [ "$rc" -eq 0 ] || { PR_WHY="HEAD cannot be read into an index there: $out"; return 1; }
  rc=0
  GIT_INDEX_FILE="$PR_WORK/index" git -c core.fsmonitor=false -c core.untrackedCache=false \
    -c core.sparseCheckout=false -c diff.autoRefreshIndex=true --literal-pathspecs \
    diff --quiet --no-ext-diff --no-textconv --ignore-submodules=none HEAD -- "${specs[@]}" || rc=$?
  [ "$rc" -eq 0 ] || { PR_WHY="the working tree differs from HEAD there (uncommitted edits, rc=$rc)"; return 1; }
  GIT_INDEX_FILE="$PR_WORK/index" git -c core.fsmonitor=false -c core.untrackedCache=false \
    --literal-pathspecs ls-files -z --others --exclude-standard -- "${specs[@]}" >"$PR_WORK/others" \
    || { PR_WHY="the untracked files there cannot be listed"; return 1; }
  [ ! -s "$PR_WORK/others" ] || { PR_WHY="untracked files there: $(pr_first "$PR_WORK/others")"; return 1; }

  for p in docs proofs/trust-soundness; do
    kind="$(git cat-file -t "HEAD:$p" 2>/dev/null || echo absent)"
    : >"$PR_WORK/sub"
    [ "$kind" != tree ] || git ls-tree -r "HEAD:$p" >"$PR_WORK/sub" || { PR_WHY="HEAD:$p cannot be listed"; return 1; }
    if [ "$kind" = tree ] && grep -qE '^100(644|755) ' "$PR_WORK/sub"; then
      pr_on_disk "$p" || { PR_WHY="$p is not, on disk, a directory stored under exactly that name (a case- or normalisation-folded name, or a link, stands there)"; return 1; }
    elif [ "$kind" != blob ]; then
      if [ -e "$p" ] || [ -L "$p" ]; then
        PR_WHY="HEAD holds no file under $p, but this checkout has something there"; return 1
      fi
    fi
  done
  if [ -d proofs/trust-soundness ]; then
    GIT_INDEX_FILE="$PR_WORK/index" git -c core.fsmonitor=false -c core.untrackedCache=false \
      --literal-pathspecs ls-files -z --others --directory -- proofs/trust-soundness >"$PR_WORK/others" \
      || { PR_WHY="the untracked entries under proofs/trust-soundness cannot be listed"; return 1; }
    [ ! -s "$PR_WORK/others" ] || { PR_WHY="proofs/trust-soundness holds entries HEAD does not (ignored ones and empty directories count: the reading counts names there): $(pr_first "$PR_WORK/others")"; return 1; }
  fi
  # STORED names of the files. git's lstat and untracked scan fold case under
  # core.ignorecase (and normalise under core.precomposeunicode), so a tracked
  # docs/recipe.md that sits on disk as docs/recipe.MD reads clean to every git
  # check above; main's `find -name '*.md'` / `-name '*.lean'` match the stored
  # name byte for byte and miss it, while a real checkout writes the index
  # spelling. So every tracked path under the two directories must be a name
  # readdir returns (find -print0 walks readdir; the start path is printed as
  # given, and pr_on_disk above vouches for it), and proofs/trust-soundness's
  # top level, whose names invariant (1) counts, must be EXACTLY the tracked
  # names there in both directions — an extra name git folds onto a tracked one
  # (a case-sensitive volume with core.ignorecase=true) is invisible to its
  # untracked scan. A name holding a newline refuses: the lists are compared
  # line by line.
  GIT_INDEX_FILE="$PR_WORK/index" git --literal-pathspecs ls-files -z -- docs proofs/trust-soundness >"$PR_WORK/tracked0" \
    || { PR_WHY="the tracked files under docs/ and proofs/trust-soundness/ cannot be listed"; return 1; }
  : >"$PR_WORK/disk0"
  for p in docs proofs/trust-soundness; do
    if [ -e "$p" ] || [ -L "$p" ]; then
      find "$p" -print0 >>"$PR_WORK/disk0" 2>"$PR_WORK/finderr" \
        || { PR_WHY="$p cannot be walked: $(head -c 300 "$PR_WORK/finderr")"; return 1; }
    fi
  done
  for p in tracked0 disk0; do
    [ "$(tr -cd '\n' <"$PR_WORK/$p" | wc -c | tr -d ' ')" = 0 ] \
      || { PR_WHY="a name under docs/ or proofs/trust-soundness/ holds a newline"; return 1; }
    # Called under `if`, so errexit is off here: every producer below states
    # its own failure, or a failed tool would leave an empty list that passes.
    tr '\0' '\n' <"$PR_WORK/$p" | LC_ALL=C sort -u >"$PR_WORK/${p%0}" \
      || { PR_WHY="the ${p%0} name list under docs/ and proofs/trust-soundness/ cannot be sorted"; return 1; }
  done
  LC_ALL=C comm -23 "$PR_WORK/tracked" "$PR_WORK/disk" >"$PR_WORK/misnamed" \
    || { PR_WHY="the tracked and stored names cannot be compared"; return 1; }
  [ ! -s "$PR_WORK/misnamed" ] || {
    PR_WHY="$(head -1 "$PR_WORK/misnamed" | LC_ALL=C sed 's/[^ -~]/?/g') is tracked, but no entry is stored on disk under exactly that name (a case- or normalisation-folded name stands for it, which main's find -name patterns read differently)"; return 1; }
  LC_ALL=C sed -n 's|^\(proofs/trust-soundness/[^/]*\).*$|\1|p' "$PR_WORK/tracked" | LC_ALL=C sort -u >"$PR_WORK/top.t" \
    || { PR_WHY="the tracked top-level names of proofs/trust-soundness/ cannot be listed"; return 1; }
  # grep exits 1 for "no stored names there", which is an answer; 2 is not.
  { LC_ALL=C grep -E '^proofs/trust-soundness/[^/]+$' "$PR_WORK/disk" >"$PR_WORK/top.d"; [ $? -le 1 ]; } \
    || { PR_WHY="the stored top-level names of proofs/trust-soundness/ cannot be listed"; return 1; }
  LC_ALL=C comm -3 "$PR_WORK/top.t" "$PR_WORK/top.d" >"$PR_WORK/top.x" \
    || { PR_WHY="the tracked and stored names of proofs/trust-soundness/ cannot be compared"; return 1; }
  [ ! -s "$PR_WORK/top.x" ] || {
    PR_WHY="the names stored in proofs/trust-soundness/ are not exactly HEAD's there (the reading counts them): $(head -1 "$PR_WORK/top.x" | tr -d '\t' | LC_ALL=C sed 's/[^ -~]/?/g')"; return 1; }

  for p in docs proofs/trust-soundness; do
    [ -d "$p" ] || continue
    find "$p" ! -type f ! -type d ! -type l -print >"$PR_WORK/special" 2>&1 \
      || { PR_WHY="$p cannot be walked: $(head -c 300 "$PR_WORK/special")"; return 1; }
    [ ! -s "$PR_WORK/special" ] || { PR_WHY="$p holds a FIFO, socket or device: $(head -c 300 "$PR_WORK/special")"; return 1; }
  done
  return 0
}

push_reading() {
  local line lref lsha rref rsha extra n=0 deletions=0 i T BASE bdesc mb remote=unset
  local label why red=0 judged=0 refused=0 skipped=0 head_tree="" checkout="" verdict=""
  local HEX='^([0-9a-f]{40}|[0-9a-f]{64})$' ZERO='^0+$'
  local -a LR LS RR RS TT
  export GIT_NO_REPLACE_OBJECTS=1

  while IFS= read -r line || [ -n "$line" ]; do
    case "$line" in *[![:space:]]*) ;; *) continue ;; esac
    lref="" lsha="" rref="" rsha="" extra=""
    read -r lref lsha rref rsha extra <<<"$line" || true
    if [ -z "$rsha" ] || [ -n "$extra" ] || ! [[ "$lsha" =~ $HEX ]] || ! [[ "$rsha" =~ $HEX ]]; then
      pr_malformed "malformed TRUST_PUSHED_REFS line '$line'; expected '<local-ref> <local-sha> <remote-ref> <remote-sha>' with 40- or 64-hex shas"
    fi
    if [[ "$lsha" =~ $ZERO ]]; then
      deletions=$((deletions + 1)); LR+=("$lref"); LS+=("$lsha"); RR+=("$rref"); RS+=("$rsha"); TT+=(-); continue
    fi
    T="$(git rev-parse --verify --quiet "${lsha}^{tree}" 2>/dev/null)" \
      || pr_malformed "pushed $lref ($lsha) does not name a tree in this repository"
    n=$((n + 1)); LR+=("$lref"); LS+=("$lsha"); RR+=("$rref"); RS+=("$rsha"); TT+=("$T")
  done <<<"$TRUST_PUSHED_REFS"

  echo "SUBJECT: the pushed refs (TRUST_PUSHED_REFS: $n update(s), $deletions deletion(s)); each is skipped (its in-scope entries equal what the destination has), judged as this checkout (which provably holds it in scope), or refused"
  if [ "${#LR[@]}" -eq 0 ]; then
    echo "SKIPPED: TRUST_PUSHED_REFS names no ref; there is no pushed tree to judge"; return 0
  fi
  PR_WORK="$(mktemp -d "${TMPDIR:-/tmp}/doc-counts.XXXXXX")"
  trap pr_cleanup EXIT

  for i in "${!LR[@]}"; do
    lref="${LR[$i]}" lsha="${LS[$i]}" rref="${RR[$i]}" rsha="${RS[$i]}" T="${TT[$i]}"
    label="$lref ${lsha:0:12} -> $rref"
    if [ "$T" = - ]; then echo "== $lref (deletion) -> $rref: deletion — lands no tree, judges nothing"; continue; fi
    pr_scope "$T" "$PR_WORK/t" || pr_malformed "the tree of $lref ($T) cannot be listed"

    # (1) skip: the destination already has exactly this SCOPE.
    BASE="" bdesc=""
    if ! [[ "$rsha" =~ $ZERO ]]; then
      if git cat-file -e "$rsha" 2>/dev/null && BASE="$(git rev-parse --verify --quiet "${rsha}^{tree}" 2>/dev/null)"; then
        bdesc="the destination tip ${rsha:0:12}"
      else BASE=""; bdesc="no base: the destination tip ${rsha:0:12} is not in this object store"; fi
    else
      [ "$remote" != unset ] || remote="$(pr_dest_remote)"
      if [ -z "$remote" ]; then
        bdesc="no base: the destination '${TRUST_PUSH_REMOTE:-}' is not a remote here"
      elif mb="$(git merge-base "$lsha" "refs/remotes/$remote/main" 2>/dev/null)" \
           && BASE="$(git rev-parse --verify --quiet "${mb}^{tree}" 2>/dev/null)"; then
        bdesc="the fork point ${mb:0:12} with refs/remotes/$remote/main"
      else BASE=""; bdesc="no base: a new ref with no fork point with refs/remotes/$remote/main"; fi
    fi
    why="$(pr_link "$PR_WORK/t" 0)"
    if [ -n "$BASE" ] && [ -z "$why" ]; then
      pr_scope "$BASE" "$PR_WORK/b" || pr_malformed "the base tree $BASE cannot be listed"
      if cmp -s "$PR_WORK/t" "$PR_WORK/b"; then
        echo "== $label: skipped (its in-scope entries — docs, proofs, .gitattributes — equal $bdesc)"
        skipped=$((skipped + 1)); continue
      fi
      bdesc="it changes $(pr_differ "$PR_WORK/b" "$PR_WORK/t") against $bdesc"
    fi

    # (2) judge the checkout: T is HEAD in SCOPE and the checkout holds HEAD there.
    [ -n "$why" ] || why="$(pr_link "$PR_WORK/t" 1)"
    if [ -n "$why" ]; then
      echo "== $label: REFUSED — its in-scope entries hold $why, through which the reading can reach content this gate does not compare"
      refused=$((refused + 1)); continue
    fi
    if [ -z "$head_tree" ]; then
      head_tree="$(git rev-parse --verify --quiet 'HEAD^{tree}' 2>/dev/null)" || head_tree=none
      [ "$head_tree" = none ] || pr_scope "$head_tree" "$PR_WORK/h" || head_tree=none
    fi
    if [ "$head_tree" = none ] || ! cmp -s "$PR_WORK/t" "$PR_WORK/h"; then
      if [ "$head_tree" = none ]; then why="this checkout has no HEAD"
      else why="the push changes $(pr_differ "$PR_WORK/h" "$PR_WORK/t") to content this checkout does not hold"; fi
      echo "== $label: REFUSED — $why ($bdesc); check out $lref and push again"
      refused=$((refused + 1)); continue
    fi
    if [ -z "$checkout" ]; then
      PR_WHY=""
      if pr_checkout_holds_head "$PR_WORK/h"; then checkout=holds; else checkout="$PR_WHY"; fi
    fi
    if [ "$checkout" != holds ]; then
      echo "== $label: REFUSED — it matches HEAD in scope, but this checkout does not hold HEAD there: $checkout; make the working tree clean in docs/ and proofs/ and push again"
      refused=$((refused + 1)); continue
    fi
    if [ -n "$verdict" ]; then
      echo "== $label: judged the checkout (the same checkout as above: $verdict)"
    else
      echo "== $label: judged the checkout (its in-scope entries equal HEAD ${head_tree:0:12}'s, and the working tree holds exactly HEAD there; $bdesc)"
      set +e
      ( set -e; doc_counts_reading )
      rc=$?
      set -e
      if [ "$rc" -eq 0 ]; then verdict=green; else verdict="red (rc=$rc)"; fi
    fi
    judged=$((judged + 1))
    [ "$verdict" = green ] || red=1
  done

  echo
  if [ "$red" -ne 0 ] || [ "$refused" -ne 0 ]; then
    echo "DOC-TRUTH GATE FAILED (the push: $refused ref(s) refused, checkout verdict: ${verdict:-not judged})"
    exit 1
  fi
  if [ "$n" -eq 0 ]; then
    echo "SKIPPED: deletion(s) only — no tree is pushed, nothing to judge"; return 0
  fi
  if [ "$judged" -eq 0 ]; then
    echo "SKIPPED: no pushed tree changes what this gate reads (docs/, proofs/, .gitattributes) against what its destination already has ($skipped skipped, $deletions deletion(s))"
    return 0
  fi
  echo "DOC COUNTS OK (the push: $judged ref(s) judged as this checkout, $skipped skipped)"
}

case "${TRUST_PUSHED_REFS:-}" in
  *[![:space:]]*) push_reading ;;
  *) doc_counts_reading ;;
esac
