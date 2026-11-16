#!/usr/bin/env python3
"""Trust: did a signature you changed leave a `#[cfg(test)]` construction site behind?

WHY THIS EXISTS, and why a BUILD-FREE lane is the right shape for it
--------------------------------------------------------------------
Measured twice in eighteen hours, same crate, same producer machine, same class:

  d26cb8c40e  wave-PC   added `PendingConst::promoted_global`, reached every
                        production construction site, missed the `#[cfg(test)]`
                        helper `str_const_finalize_tests::str_pending`.
                        E0063, repaired by cf89d447db.
  78a0bef5ff  wave-NSA  widened `propagate_union_lane_taint` 3 -> 4 params (and
                        `union_lane_ty_transitive` 2 -> 4, `param_lane_ty_transitive`
                        3 -> 4, and four siblings), updated all 2 production
                        callers and none of the ~45 `#[cfg(test)]` ones. E0061,
                        still red on origin/main at ad074447848d29974bec329d7e3587bb92dc4d38.

Both times the tree still BUILT: `x.py build` and `x.py test tests/ui` compile lib
targets, and a `#[cfg(test)]` body is not in a lib target. The producer's own
measurement loop therefore cannot see this class at all, however carefully it is run.

The only pre-push lane that CAN see it is `scoped.compiler-check`
(`x.py check --stage 1`, which passes `--tests` and `-p` for every workspace member
in rustc-main's dependency closure — `crates/trust-thir-lower` among them). It costs
9-11 minutes and takes the exclusive build-tree lock, so it lives only in the FULL
hook set. `scripts/hooks-pin/` — the narrow set this repo's own CLAUDE.md tells
shared machines to install, and the one `install-pin-hook.sh` installs — compiles
NOTHING. On a clone running the narrow set, or on any `git push --no-verify`, this
class is invisible at push time and the bill is paid by the next lane whose push IS
in scope, which is refused for a break it did not cause.

So the fix is not another slow lane. It is a lane cheap enough that BOTH hook sets
can afford it, which is why this file uses no cargo, no x.py, no build tree, no
network and no lock — only `git show` of the blobs in the range.

WHAT IT JUDGES, and what it deliberately does not
-------------------------------------------------
Definitions THIS PUSH CHANGED, and sites THIS PUSH ADDS, and only construction
sites among the files THIS PUSH CHANGED:

  * a free function whose parameter list changed  -> every unqualified call site
    IN THE SAME FILE must supply the declared number of arguments (E0061);
  * a struct whose named-field list changed       -> every `S { .. }` literal or
    pattern IN THE SAME CRATE (among the changed files) that does not use `..`
    must name exactly the declared fields (E0063 / E0027 / E0560);
  * a call or literal the push ADDS               -> the same two tests, against
    the declaration AT THE PUSHED TIP, whether or not the push changes it
    (see WHAT A PUSH ADDS below);
  * a `pub` field of a `pub struct` that THIS PUSH puts under a Cargo feature
    (`#[cfg(feature = ..)]`)                       -> refused at the declaration
    (2026-09-30): it makes the feature non-additive, and the literal it breaks
    lives in another crate, which this lane cannot resolve. See
    FEATURE-GATED PUBLIC FIELDS in analyse_blanked.

The two scopes differ on purpose. A struct literal names its type at the site, so
the changed-set match is exact and it is what catches `d26cb8c40e`, whose decl was
in `lib.rs` and whose stale `#[cfg(test)]` initializer was in `crate_module.rs` —
both in that one commit's diff. A free-function CALL names nothing: resolving it
across files means resolving `use`, and guessing at import resolution is how a
gate starts refusing correct pushes.

Restricting to changed definitions is what keeps it quiet: the population is a
handful of names per push, so a residual parsing quirk costs almost nothing, and a
file that was already skewed is not this push's business. Measured over the 300
single-commit ranges ending at `ad074447848d29974bec329d7e3587bb92dc4d38`, it
names `d26cb8c40e`, `78a0bef5ff` and `ed21a2887f` and nothing else. Judging
the sites a push ADDS keeps the same property — what a push adds is a handful
of sites, and a site that was already skewed is still not this push's — at
the price of skips of its own (WHAT A PUSH ADDS, below).

It SKIPS rather than guesses, and says how often:
  * a name declared more than once in the file (an inner `mod` may shadow it);
  * a method — any declaration with a `self` receiver, and any call site reached
    through `.` or `::` (`crate::f(..)` is a real free call and is skipped too:
    losing it costs a little coverage, guessing at it costs a false refusal);
  * a call site whose argument text contains `|`, `<` or `>` at top level, where
    a closure parameter list or a generic argument can hide a comma;
  * a changed free function whose name the file also binds as a VALUE
    (bound_as_value, the added-site pass's rule below): a parameter
    `name: impl FnOnce(..)`, a closure parameter, a `let name = |..| ..`. The
    value shadows the function where it is in scope, so `name(x)` there calls
    the value. Measured 2026-09-29: cb/track-b was refused on six such calls
    (`test_function_has_requires`, a parameter; `held`, a `#[cfg(test)]` let
    closure), none an error, and cf258abe3d7d judged alone on its six
    `local(..)` readings (below). The skip is per NAME and per file, so a
    real stale call elsewhere in a file that also binds the name as a value
    is not judged. Re-measured with it, 2026-09-29: the three regressions
    named above are named with identical findings, and over the last 300
    first-parent commits of main at c285a367afa that touch a .rs file under
    crates/ or compiler/, each judged as C^1..C, the one verdict that changed
    is cf258abe3d7d's, FAIL on its six closure calls to PASS;
  * a struct literal body that does not parse as field pairs (so an `if x == C {`
    block is never mistaken for a literal).

Comments and string literals are blanked (offsets preserved) before anything is
matched, so a doc comment that spells a call is not a call.

WHAT A PUSH ADDS (F1b in docs/issues/2026-09-28-cfg-test-caller-skew-push-subject.md)
-----------------------------------------------------------------------------------
Judging only changed definitions missed a union that breaks where no
declaration changes in base..head: branch A widens `struct Rec` and lands on
main; branch B, forked before A, adds a `#[cfg(test)]` `Rec { a: 1 }`; pushing
main merged with B, or B rebased onto main, changes no declaration and is
E0063. The lane passed every such shape: update, new ref, merge, rebase, with
and without a destination.

So every site the push ADDS is judged too (analyse_added_sites). A site is
added when its text (whitespace-collapsed, from its name to its closing
delimiter) is not at the base blob of the same path, counted as a multiset; a
site whose text the base already holds is the destination's own, as a carried
file is. A file the base lacks adds all of its sites, so a move is still an
add (F5 stays open by design). Each added site is read by the SAME readers
the changed-declaration passes use (_call_site, _literal_site) with the same
excusals, and is judged at the same scope:

  * a call, against a free function declared once in the SAME file;
  * a literal, against a struct declared once in its own file, or else
    declared exactly once in its crate at the pushed tip. That declaration may
    sit in a file the push never touched; it is found by one `git grep` of the
    pushed tree (struct_names_at), never by reading the crate.

With a destination, a (declaration, site) pair is set aside exactly as a
cross-file pair is: when ONE destination commit holds both files at their
pushed blobs (a same-file pair: when one holds the file).

The added-site pass SKIPS more than the changed-declaration passes do, never
less. Two of its skips are measured false findings on real history: the last
400 first-parent commits of main at 84a2e55537 that touch a .rs file under
crates/ or compiler/, each judged as a push of C^1..C to a destination whose
main is C^1. Every one of those trees landed through the gates.
  * A function name the file also binds as a VALUE (bound_as_value): `let
    leaf = || ..`, a parameter, a closure parameter. The value shadows the
    function where it is in scope. Measured: four commits and 25 sites, every
    one a closure beside a same-named `fn` elsewhere in the file. Since
    2026-09-29 the changed-signature pass asks it too (the SKIPS list above),
    and it reads a `use` by declaration, so a rustfmt-wrapped
    `use super::{\\n    f,\\n};` imports `f` rather than binding it.
  * A `Name {` directly inside an `enum` body (enum_variant_braces). That is a
    variant declaration, not a literal of the same-named struct. Measured: two
    commits (`CalleeOwner::TraitImpl`, `TrustDependencyKind::Allocation`).
  * Not measured, but the same rule the lane keeps elsewhere: a struct name
    the crate spells `struct Name` more than once, of any kind
    (declarations_named), and a name a non-local `use` imports, which the
    pass also applies to calls.
Four more skips are measured on the tree itself: every .rs file under crates/
and compiler/ at 84a2e55537 read as ADDED (155,658 sites), which the pass
without them refused at 91 sites. A review of 2026-09-28 reproduced the first
three shapes below as one-commit pushes from that tip which main's lane
passed; they account for 29 of the 91, including the only one under crates/.
With all four skips it refuses at 12, none under crates/.
  * A call inside an attribute (in_attribute): `#[derive(Debug)]` in a file
    that declares `pub fn derive(corpus, kind)`.
  * A call of a fn whose "parameters" are not all `pattern: Type`
    (rust_signature): `fn with_forced_trimmed_paths(ForceTrimmedGuard,
    FORCE_TRIMMED_PATH);` is input to a `define_helper!` invocation.
  * An import read by STATEMENT as well as by line
    (imports_foreign_statement): rustfmt wraps `use rustc_middle::thir::{`
    onto one line and `Ascription,` onto the next, and the line reading never
    sees `use ` beside the name.
  * A literal that is the value of a macro's `@key =` (in_macro_arm_input):
    `declare_lint!`'s `@future_incompatible = FutureIncompatibleInfo { .. }`,
    which the macro completes; 51 at that tip, and an upstream port adds more
    (cdbca2287b added four).
Each is asked only of a disagreeing added site, and only by this pass: the
changed-declaration passes read exactly as before, so the lane refuses
wherever it refused before them. The 12 left are in upstream compiler/ code,
in classes the changed-declaration passes share: an enum variant brought in
by a glob or a local `use`, a closure as a literal's field value, an
associated fn that calls the same-named free fn, and a block-local `use` of a
same-named fn.
With those skips, the replay refused three commits that main's lane passed:
3270bb7184, 888dd961ff and cd1e83d877. Each adds a `TrustIrGateSource { .. }`
in a `#[cfg(test)] mod tests;` file without the `abi_cross_check` field the
struct already had. These are real E0063s, and they stayed on main until
816d2bbbfa added `abi_cross_check: None` to all three.

It is NOT a type checker and does not claim to be: it cannot see a call site in a
file this push did not touch, a wrong argument TYPE, a trait-method skew, or
anything at all outside the two shapes above. `scoped.compiler-check` remains the
authority. This lane exists so that the authority is not the ONLY thing standing
between this class and `main` — a green here is not a green build, and a commit
body must not cite it as one.

WHAT A PUSH "CHANGED", when it has a destination
-------------------------------------------------
The unit this lane reads is the FILE: `git diff --name-only -z base..head`,
then the old and new blob of each file. `-z` because without it git C-quotes
a path holding a non-ASCII byte, `"`, `\\` or a control character
(`"crates/k/src/\\303\\251t\\303\\251.rs"`), the quoted name no longer starts
with `crates/`, and the file left the subject without a word. Every reader of
the subject — that diff and each blob read — runs `git --no-replace-objects`,
as the destination evidence below always did: the lane judges the objects
`git push` sends, never a local `refs/replace/*` stand-in for them.

For an UPDATE, base is the branch's old tip,
so a branch that merges main re-reads every file the merge brought in — files
the destination already holds byte for byte. Measured 2026-09-27: updating
`crystal/callee-sidecar` a573093063..d5e68f9812 read 792 files, 7,348
definitions in play, and refused the push on 12 sites in four files identical
to origin/main — six `local(..)` and four `observe(..)` calls that are really
calls to a same-named CLOSURE, and two enum VARIANT declarations
(`Shape::Fact { strict }`, `IrSafetyVcKind::Bounds { signed }`) read as
literals of a same-named private struct in a sibling file. None is a compile
error; none is the push's. Main's own pushes do not see them, because main
judges only the files its new commits touch — with one exception worth knowing:
the six `local(..)` readings are raised by main's own introducing commit
cf258abe3d7d judged alone, which reached main without this lane refusing it
(until 2026-09-29, when the changed-signature pass took the added-site pass's
bound_as_value skip: the `local` there is a closure, and that commit now
passes). It is the class c6eb148a34 closed for the revert-rationale lane, at
this lane's unit.

So with a destination (`--remote`, or `TRUST_PUSH_REMOTE` under
`--push-context`, which is what both hook sets pass), a file is INTRODUCED only
if its new blob differs from the blob at the same path in every commit the
destination already has: each ref it advertises and each destination-side
parent of the commits the push introduces (`rev-list --boundary`). The
advertisement is read by `scripts/lib/push_destination.sh`, the reader
check_revert_rationale.sh uses, so the two lanes exclude on the same evidence:
the destination's own `ls-remote`, never a local tracking ref. A same-file
finding is reported only when its file is introduced.

A cross-file (declaration, site) pair is set aside only when ONE of those
destination commits holds BOTH files, each blob at the path head gives it:
that exact pairing is already published. Carried "each by some commit" is not
enough. A merge of two published branches — one widening a struct and
updating the literals it knows, the other adding a `#[cfg(test)]` literal of
the struct's old shape — gives a head whose every file some destination
commit carries, while the pair exists in no destination commit and is E0063.
Judged file by file, that merge read 0 files and passed (F1 in
docs/issues/2026-09-28-cfg-test-caller-skew-push-subject.md). So a struct the
push widens still reports a stale literal in a file the destination carries,
a struct a merged-in main changed still reports a stale literal the push adds,
and a struct one merged-in branch changed reports a stale literal another
merged-in branch carries. Carried files are read as context from the same
diff the old reading used, in every crate where no one destination commit
carries all of the crate's changed files: each crate the push touches, and
each crate a merge assembles from more than one destination commit. An update
that only merges main (the measured shape above) reads no more than before:
the main commit it merged carries every file that merge brings — and, in each
crate the lane itself never touched, the whole crate. A crate whose changed
files one destination commit carries, but not WHOLE (some .rs file differs
between that commit and head, uncarried_crates), is read as context too: a
published branch B merged onto a main that widened `Rec` brings only B's file,
carried at B, whose added `Rec { a: 1 }` names a declaration B does not hold.

A NEW ref with a destination is judged against the destination's own
`refs/heads/main`, never the local `origin/main` a forged or stale tracking ref
could point at head. A destination that cannot be read, or a new ref whose
destination main is not in this object store, is exit 2: fail closed, as the
revert lane does. Without a destination, and for `--range`, the subject is the
whole range, as before.

Under `--push-context`, a non-blank TRUST_PUSHED_REFS is the push, and only the
push. Each non-blank line must be the four fields git hands a pre-push hook,
`<local ref> <local sha> <remote ref> <remote sha>`, or the lane exits 2: a
line it cannot read is never skipped, because the push may be sending what
that line names. A push of deletions alone sends no file, so there is nothing
to judge: the lane says `SKIPPED:` and exits 0, never falling through to
`origin/main..HEAD`, which is local work that push does not send (a clone with
unpushed skew on HEAD was refused `git push --delete` for it). Only an unset or
blank TRUST_PUSHED_REFS, no push in flight, reads the standing
`origin/main..HEAD`.

Usage:
    check_cfg_test_caller_skew.py                 # origin/main..HEAD
    check_cfg_test_caller_skew.py --push-context [--remote DEST]
                                                  # the refs git is pushing
    check_cfg_test_caller_skew.py --range A..B
    check_cfg_test_caller_skew.py --selftest      # mutation proof: in memory, plus
                                                  # throwaway git fixtures (no checkout)

Exit: 0 clean, nothing in range, or nothing pushed (SKIPPED), 1 skew found,
2 could not read the range, the push destination, or TRUST_PUSHED_REFS.

Author: Andrew Yates <andrewyates.name@gmail.com>
Copyright 2026 Andrew Yates | License: Apache-2.0 OR MIT
"""

from __future__ import annotations

import argparse
import bisect
import locale
import os
import re
import subprocess
import sys
from pathlib import Path

WATCHED_PREFIXES = ("crates/", "compiler/")
ZERO = "0" * 40
# The ONE reader of a push destination's advertised refs, shared with
# check_revert_rationale.sh and check_measurement_provenance.sh. Resolved beside
# this file so a copy of the checker finds the copy of its reader.
DESTINATION_HELPER = Path(__file__).resolve().parent / "lib" / "push_destination.sh"


class DestinationUnreadable(RuntimeError):
    """The push destination could not supply the evidence the subject needs."""


class PushedRefsUnreadable(RuntimeError):
    """TRUST_PUSHED_REFS holds a line that is not what git hands a pre-push hook."""


# --------------------------------------------------------------------------- git

# Every git child that reads the SUBJECT runs with this prefix. git push sends
# the real objects; a local `refs/replace/*` over a pushed commit or blob would
# otherwise make the lane judge the replacement while the destination receives
# the original. The destination evidence (introduced_commits, blob_ids and
# scripts/lib/push_destination.sh) already read that way, so now the subject
# and the evidence are read from the same objects.
GIT = ("git", "--no-replace-objects")


def git(*args: str, cwd: str | None = None) -> str:
    proc = subprocess.run([*GIT, *args], capture_output=True, cwd=cwd)
    if proc.returncode != 0:
        # stderr can echo a path of any bytes (`git show <rev>:<path>` on a
        # file that rev lacks, as blob_at asks for an added or deleted file),
        # so it is decoded leniently: a strict decode raised UnicodeDecodeError,
        # which is not a RuntimeError, and the run died in a traceback.
        err = proc.stderr.decode("utf-8", "replace").strip()
        raise RuntimeError(f"git {' '.join(map(display_path, args))} failed: {err}")
    # stdout is decoded exactly as text=True decoded it: strictly, in the
    # locale encoding, with universal newlines. The blob readings are unchanged.
    out = proc.stdout.decode(locale.getpreferredencoding(False))
    return out.replace("\r\n", "\n").replace("\r", "\n")


def changed_paths(
    base: str, head: str, cwd: str | None = None, within: list[str] | None = None
) -> list[str]:
    """Every path `base..head` changes, from `git diff --name-only -z`.

    Without `-z`, git C-quotes a path holding a non-ASCII byte, `"`, `\\` or a
    control character, and the quoted name does not start with `crates/`, so
    the file silently left the subject. Each NUL-terminated name is decoded
    with os.fsdecode, the inverse of how subprocess encodes an argument, so a
    path of any bytes goes back into `git show <rev>:<path>` unchanged.

    `within`, when given, limits the diff to those directories (literal
    pathspecs, so no name is read as a glob)."""
    spec = ["--", *(f":(literal){d}/" for d in within)] if within is not None else []
    proc = subprocess.run(
        [*GIT, "diff", "--name-only", "-z", base, head, *spec], capture_output=True, cwd=cwd
    )
    if proc.returncode != 0:
        err = proc.stderr.decode("utf-8", "replace").strip()
        raise RuntimeError(f"git diff --name-only -z {base} {head} failed: {err}")
    return [os.fsdecode(name) for name in proc.stdout.split(b"\0") if name]


def display_path(path: str) -> str:
    """A path as a report line can print it. A name that is not valid in the
    filesystem encoding holds surrogate escapes, which a UTF-8 stdout refuses
    to encode; print its undecodable bytes as U+FFFD instead of crashing."""
    return os.fsencode(path).decode("utf-8", "replace")


def blob_at(rev: str, path: str, cwd: str | None = None) -> str | None:
    try:
        return git("show", f"{rev}:{path}", cwd=cwd)
    except RuntimeError:
        return None


# ------------------------------------------------------------------- lexing aid


def blank_comments_and_strings(src: str) -> str:
    """Replace comment and string-literal CONTENT, preserving every offset and
    newline, so a doc comment that spells `f(a, b)` is not a call.

    A COMMENT becomes WHITESPACE and a STRING becomes `_`, and the difference is
    load-bearing rather than cosmetic. A comment is not a token: blanking
    `foo(\\n  a,\\n  // note\\n)` to non-space would turn the trailing comment into a
    second argument. A string IS a token: blanking `usize_decl(1, "bound")` to
    spaces leaves `usize_decl(1,      )`, whose last segment is empty, which reads
    as a trailing comma and reports one argument instead of two. Measured — that
    single choice produced 35 of the 36 false findings in the first run of this
    lane over `d26cb8c40e^..cf89d447db`, a range whose endpoint is a tree the
    repo recorded GREEN under `x.py check --stage 1`."""
    out = list(src)
    i, n = 0, len(src)

    def blank(a: int, b: int, filler: str = " ") -> None:
        for k in range(a, b):
            if out[k] != "\n":
                out[k] = filler

    while i < n:
        c = src[i]
        if c == "/" and i + 1 < n and src[i + 1] == "/":
            j = src.find("\n", i)
            j = n if j < 0 else j
            blank(i, j)
            i = j
        elif c == "/" and i + 1 < n and src[i + 1] == "*":
            depth, j = 1, i + 2
            while j < n and depth:
                if src.startswith("/*", j):
                    depth += 1
                    j += 2
                elif src.startswith("*/", j):
                    depth -= 1
                    j += 2
                else:
                    j += 1
            blank(i, j)
            i = j
        elif (
            c == "r"
            and i + 1 < n
            and src[i + 1] in '#"'
            # `r` must START a token, or `foo_r"` inside an identifier would be
            # read as a raw string. `b` is the one legal predecessor (`br"..."`).
            and (i == 0 or not re.match(r"[A-Za-z0-9_]", src[i - 1]) or src[i - 1] == "b")
        ):
            m = re.match(r'r(#*)"', src[i:])
            if not m:
                i += 1
                continue
            close = '"' + m.group(1)
            j = src.find(close, i + m.end())
            j = n if j < 0 else j + len(close)
            blank(i, j, "_")
            i = j
        elif c == '"':
            j = i + 1
            while j < n:
                if src[j] == "\\":
                    j += 2
                    continue
                if src[j] == '"':
                    j += 1
                    break
                j += 1
            blank(i, j, "_")
            i = j
        elif c == "'":
            # A char literal, never a lifetime: `'x'`, `'\n'`, `'\u{1}'`.
            m = re.match(r"'(?:\\(?:u\{[0-9a-fA-F]+\}|.)|[^\\'])'", src[i:])
            if m:
                blank(i, i + m.end(), "_")
                i += m.end()
            else:
                i += 1
        else:
            i += 1
    return "".join(out)


def per_source(fn):
    """Memoize a pure reading of one blanked source, keyed by the source text.
    The cross-file pass asks cfg_test_ranges and impl_body_braces of the same
    file once per (declaration, file) pair: measured 4,299 and 4,511 calls,
    about 15 s of a 47 s profile, on the 359-file range 69974d60f94c. Callers
    never mutate what these return."""
    cache: dict = {}

    def read(src: str):
        hit = cache.get(src)
        if hit is None:
            if len(cache) >= 64:
                cache.clear()
            hit = cache[src] = fn(src)
        return hit

    read.__doc__ = fn.__doc__
    return read


@per_source
def cfg_test_ranges(src: str) -> list[tuple[int, int]]:
    ranges = []
    for m in re.finditer(r"#\[cfg\(test\)\]", src):
        i = src.find("{", m.end())
        if i < 0:
            continue
        depth, j = 0, i
        while j < len(src):
            if src[j] == "{":
                depth += 1
            elif src[j] == "}":
                depth -= 1
                if depth == 0:
                    break
            j += 1
        ranges.append((m.start(), j))
    return ranges


def in_cfg_test(pos: int, ranges: list[tuple[int, int]]) -> bool:
    return any(a <= pos <= b for a, b in ranges)


_NEWLINES: dict[str, list[int]] = {}


def line_of(src: str, pos: int) -> int:
    """`src.count("\n", 0, pos) + 1`, from a table of newline offsets built
    once per source. The count scanned from the start of the file for every
    declaration and site, which is quadratic: measured 9.7 s of a 12.5 s run
    on a 21-file range (930af75ba07d) before the table, on main's lane."""
    offsets = _NEWLINES.get(src)
    if offsets is None:
        if len(_NEWLINES) >= 64:
            _NEWLINES.clear()
        offsets = [m.start() for m in re.finditer("\n", src)]
        _NEWLINES[src] = offsets
    return bisect.bisect_left(offsets, pos) + 1


def skip_balanced(src: str, i: int, opener: str, closer: str) -> int:
    """`i` indexes `opener`; returns the index just past its match, or -1."""
    depth = 0
    while i < len(src):
        if src[i] == opener:
            depth += 1
        elif src[i] == closer:
            depth -= 1
            if depth == 0:
                return i + 1
        i += 1
    return -1


def top_level_segments(src: str, open_paren: int, closer: str = ")") -> tuple[list[str], int] | None:
    """Split the delimited group starting at `open_paren` on top-level commas.
    Returns (segments, index_of_closer) or None when the group never closes."""
    opener = src[open_paren]
    depth, i = 0, open_paren
    seg_start = open_paren + 1
    segments: list[str] = []
    while i < len(src):
        c = src[i]
        if c in "([{":
            depth += 1
        elif c in ")]}":
            depth -= 1
            if depth == 0:
                segments.append(src[seg_start:i])
                return segments, i
        elif c == "," and depth == 1:
            segments.append(src[seg_start:i])
            seg_start = i + 1
        i += 1
    return None


def declared_segments(src: str, open_delim: int) -> tuple[list[str], int] | None:
    """Split a DECLARATION's parameter or field list on its real separators.

    `top_level_segments` counts every depth-1 comma, which is right for a call
    (`f(a, b)`) and WRONG for a declaration, where a generic argument hides one:
    `fn pair_enum_abi_supported<'tcx>(arg: &ArgAbi<'tcx, Ty<'tcx>>)` has ONE
    parameter and two depth-1 commas. Measured — that single confusion produced
    9 of the 11 findings in the first 80-commit sweep of this lane, every one of
    them on a tree that was green, and every one of them a generic parameter type.

    Angle-tracking is safe HERE and not in an expression: a declaration's `<`/`>`
    are generics, never a comparison. `->` is stepped over so an `impl Fn(A) -> B`
    bound does not close a bracket nothing opened."""
    depth, angle, i = 0, 0, open_delim
    seg_start = open_delim + 1
    segments: list[str] = []
    while i < len(src):
        c = src[i]
        if src.startswith("->", i) or src.startswith("=>", i):
            i += 2
            continue
        if c in "([{":
            depth += 1
        elif c in ")]}":
            depth -= 1
            if depth == 0:
                segments.append(src[seg_start:i])
                return segments, i
        elif c == "<" and depth == 1:
            angle += 1
        elif c == ">" and depth == 1 and angle:
            angle -= 1
        elif c == "," and depth == 1 and angle == 0:
            segments.append(src[seg_start:i])
            seg_start = i + 1
        i += 1
    return None


def arg_count(segments: list[str]) -> int:
    if len(segments) == 1 and not segments[0].strip():
        return 0
    if segments and not segments[-1].strip():  # trailing comma
        return len(segments) - 1
    return len(segments)


AMBIGUOUS = re.compile(r"[|<>]")


# ------------------------------------------------------------- fn declarations


def fn_decls(src: str) -> dict[str, list[dict]]:
    """name -> list of declarations (so a duplicated name can be skipped)."""
    found: dict[str, list[dict]] = {}
    for m in re.finditer(r"\bfn\s+([A-Za-z_][A-Za-z0-9_]*)", src):
        name = m.group(1)
        i = m.end()
        while i < len(src) and src[i].isspace():
            i += 1
        if i < len(src) and src[i] == "<":
            i = skip_balanced(src, i, "<", ">")
            if i < 0:
                continue
            while i < len(src) and src[i].isspace():
                i += 1
        if i >= len(src) or src[i] != "(":
            continue
        parsed = declared_segments(src, i)
        if parsed is None:
            continue
        segs, close = parsed
        params = [s.strip() for s in segs if s.strip()]
        has_self = bool(params) and re.match(r"^(&\s*('\w+\s*)?(mut\s+)?|mut\s+)?self\b", params[0])
        found.setdefault(name, []).append(
            {
                "pos": m.start(),
                "line": line_of(src, m.start()),
                "params": len(params),
                "has_self": bool(has_self),
                "sig": re.sub(r"\s+", " ", src[i : close + 1]).strip(),
            }
        )
    return found


def tail_before(src: str, pos: int, width: int = 16) -> str:
    """The last `width` characters of `src[:pos].rstrip()`, without copying the
    whole prefix. Every test the site readers make on that prefix (`endswith`
    of at most two characters, `\\bfn$`, `\\b(struct|...|where)$`) looks at no
    more than eight characters, so a 16-character tail answers each of them
    exactly as the full prefix did: where the prefix is longer than the tail,
    the character that decides a `\\b` is still inside it. It exists because
    the added-site reading (analyse_added_sites) asks it for every site of a
    file, where a full copy per site is quadratic."""
    j = pos
    while j > 0 and src[j - 1].isspace():
        j -= 1
    return src[max(0, j - width) : j]


# Every identifier directly followed by `(` or `{`. A per-name pattern
# `\bNAME\s*\(` matches at exactly the offsets where this matches with that
# name: an identifier followed by optional space and a delimiter cannot be the
# proper prefix of a longer one, and a match ends at the delimiter, so a scan
# for every name at once misses no site a scan for one name finds.
CALL_HEAD = re.compile(r"\b([A-Za-z_][A-Za-z0-9_]*)\s*\(")
LITERAL_HEAD = re.compile(r"\b([A-Za-z_][A-Za-z0-9_]*)\s*\{")


def _call_site(src: str, start: int, end: int, name: str) -> dict | None:
    """The call of `name` whose match spans src[start:end], or None when it is
    not one the lane judges. The ONE reading of a call site: fn_call_sites
    (a changed declaration) and call_sites_by_name (an added site) both use it."""
    before = tail_before(src, start)
    # a declaration, not a call
    if re.search(r"\bfn$", before):
        return None
    # a method or a path call — never judged (see the module docstring)
    if before.endswith(".") or before.endswith(":"):
        return None
    # a macro invocation
    if src[start + len(name) : end].lstrip().startswith("!"):
        return None
    open_paren = end - 1
    parsed = top_level_segments(src, open_paren)
    if parsed is None:
        return None
    segs, close = parsed
    ambiguous = any(AMBIGUOUS.search(s) for s in segs)
    return {"pos": start, "end": close, "args": arg_count(segs), "ambiguous": ambiguous}


def fn_call_sites(src: str, name: str) -> list[dict]:
    sites = []
    for m in re.finditer(r"\b" + re.escape(name) + r"\s*\(", src):
        site = _call_site(src, m.start(), m.end(), name)
        if site is None:
            continue
        site["line"] = line_of(src, m.start())
        sites.append(site)
    return sites


def call_sites_by_name(src: str, names: set[str]) -> dict[str, list[dict]]:
    """fn_call_sites for every name in `names`, in one scan (no `line`)."""
    out: dict[str, list[dict]] = {}
    for m in CALL_HEAD.finditer(src):
        name = m.group(1)
        if name not in names:
            continue
        site = _call_site(src, m.start(), m.end(), name)
        if site is not None:
            out.setdefault(name, []).append(site)
    return out


# --------------------------------------------------------- struct declarations


# The head of a macro invocation's INPUT: `name!(`, `name![`, `name! {`. Only an
# invocation of a macro the SAME source defines with `macro_rules!` counts (see
# `struct_decls`); `macro_rules!` itself is excluded by name.
MACRO_INPUT_HEAD = re.compile(r"\b([A-Za-z_][A-Za-z0-9_]*)\s*!\s*([({\[])")
MACRO_RULES_NAME = re.compile(r"\bmacro_rules\s*!\s*([A-Za-z_][A-Za-z0-9_]*)")
_MACRO_INPUT_CLOSER = {"(": ")", "[": "]", "{": "}"}


@per_source
def macro_input_ranges(src: str) -> tuple[list[int], list[int]]:
    """The OUTERMOST input groups of invocations of macros this blanked source
    itself defines with `macro_rules!`, as sorted parallel lists of open and
    close offsets (a nested group lies inside its outer one, so only outer
    groups are kept and one bisect answers `in_macro_input`)."""
    local_macros = set(MACRO_RULES_NAME.findall(src))
    groups = []
    for m in MACRO_INPUT_HEAD.finditer(src):
        if m.group(1) == "macro_rules" or m.group(1) not in local_macros:
            continue
        at = m.start(2)
        end = skip_balanced(src, at, src[at], _MACRO_INPUT_CLOSER[src[at]])
        if end >= 0:
            groups.append((at, end))
    starts: list[int] = []
    ends: list[int] = []
    for at, end in sorted(groups):
        if ends and at < ends[-1]:
            ends[-1] = max(ends[-1], end)
            continue
        starts.append(at)
        ends.append(end)
    return starts, ends


def in_macro_input(src: str, pos: int) -> bool:
    starts, ends = macro_input_ranges(src)
    k = bisect.bisect_right(starts, pos) - 1
    return k >= 0 and pos < ends[k]


def struct_decls(src: str) -> dict[str, list[dict]]:
    """Named-field struct declarations, by name.

    A `struct` spelled inside the input of a macro that the same file defines
    with `macro_rules!` is NOT a declaration this lane reads (2026-10-10): such a
    macro emits the real struct and may add fields the input never names.
    rustc_session's `top_level_options!( pub struct Options { .. } )` is the
    measured case: options.rs defines the macro, and it appends
    `target_modifiers` and `mitigation_coverage_map`, so a push that removed one
    `Options` field had both production `Options { .. }` literals in config.rs
    refused as naming "unknown" fields while `x.py check` compiled them. The
    skip is limited to file-local macros: a struct passed through an imported
    macro (`cfg_if!`, `bitflags!`) is still judged, as is one a `macro_rules!`
    body spells out. Like the lane's other macro-input skips, this judges less,
    never more."""
    found: dict[str, list[dict]] = {}
    for m in re.finditer(r"\bstruct\s+([A-Za-z_][A-Za-z0-9_]*)", src):
        if in_macro_input(src, m.start()):
            continue
        name = m.group(1)
        i = m.end()
        while i < len(src) and src[i].isspace():
            i += 1
        if i < len(src) and src[i] == "<":
            i = skip_balanced(src, i, "<", ">")
            if i < 0:
                continue
            while i < len(src) and src[i].isspace():
                i += 1
        # a where clause may sit between the generics and the body
        while i < len(src) and src[i] not in "{(;":
            i += 1
        if i >= len(src) or src[i] != "{":
            continue  # tuple or unit struct: no named fields to skew
        parsed = declared_segments(src, i)
        if parsed is None:
            continue
        segs, _ = parsed
        fields = []
        gated = []
        ok = True
        for seg in segs:
            body = re.sub(r"#\[[^\]]*\]", " ", seg).strip()
            if not body:
                continue
            fm = re.match(r"^(?:pub(?:\s*\([^)]*\))?\s+)?([A-Za-z_][A-Za-z0-9_]*)\s*:", body)
            if not fm:
                ok = False
                break
            fields.append(fm.group(1))
            # A bare-`pub` field that exists only under a Cargo feature: see
            # FEATURE-GATED PUBLIC FIELDS in analyse_file.
            if re.match(r"^pub\s", body) and FEATURE_CFG.search(seg):
                gated.append(fm.group(1))
        if not ok or not fields:
            continue
        public = re.search(r"(?:^|[^\w)])pub\s+$", src[max(0, m.start() - 16) : m.start()]) is not None
        found.setdefault(name, []).append(
            {
                "pos": m.start(),
                "line": line_of(src, m.start()),
                "fields": fields,
                "gated": gated if public else [],
            }
        )
    return found


# `#[cfg(feature = "x")]`, `#[cfg(all(feature = "x", ..))]`, `#[cfg(not(feature ..))]`:
# any `cfg` attribute whose predicate names a Cargo feature.
FEATURE_CFG = re.compile(r"#\[\s*cfg\s*\([^\]]*\bfeature\b")


@per_source
def impl_body_braces(src: str) -> set[int]:
    """Locate impl BODY braces, never every brace following a `for` token.

    Input is already comment/string-blanked. Headers can contain generics,
    higher-ranked bounds, function types and where clauses. Nested const
    expressions are skipped while finding the body brace, but their offsets
    are not excluded: a real struct literal inside one remains a judged site.
    This is a lexical aid, not a Rust parser; unrelated statement boundaries
    stop the scan rather than letting an impl token hide a later literal.
    """
    bodies: set[int] = set()
    for match in re.finditer(r"(?<![\w#])impl\b", src):
        i, angle = match.end(), 0
        while i < len(src):
            c = src[i]
            if src.startswith("->", i):
                i += 2
                continue
            if c in "([" or (c == "{" and angle):
                i = skip_balanced(src, i, c, {"(": ")", "[": "]", "{": "}"}[c])
                if i < 0:
                    break
                continue
            if c == "<":
                angle += 1
            elif c == ">" and angle:
                angle -= 1
            elif not angle and c == "{":
                bodies.add(i)
                break
            elif not angle and c in ";=}":
                break
            i += 1
    return bodies


def _literal_site(src: str, start: int, end: int, impl_bodies: set[int]) -> dict | None:
    """The struct literal or pattern whose `Name {` match spans src[start:end],
    or None when it is not one the lane judges. The ONE reading of a literal
    site: struct_literal_sites (a changed declaration) and
    literal_sites_by_name (an added site) both use it."""
    if end - 1 in impl_bodies:
        return None
    before = tail_before(src, start)
    if before.endswith(":") or before.endswith("."):
        return None
    # `fn f() -> ConcreteCalleeKey {` is a RETURN TYPE followed by the body
    # brace, not a literal. Measured: without this it was the last surviving
    # false finding in the 120-commit sweep (8932acd798, lineage.rs:723), and
    # it read the body's first path call `ConcreteCalleeKey::test_only(` as a
    # field named after the struct.
    if before.endswith("->") or before.endswith("as"):
        return None
    if re.search(r"\b(struct|enum|union|trait|impl|where)$", before):
        return None
    open_brace = end - 1
    parsed = top_level_segments(src, open_brace)
    if parsed is None:
        return None
    segs, close = parsed
    names: list[str] = []
    rest = False
    explicit = False
    for seg in segs:
        body = seg.strip()
        if not body:
            continue
        if body.startswith(".."):
            rest = True
            continue
        # a SINGLE colon: `Name::assoc(..)` is a path call opening a function
        # body, never a field, and `(?!:)` is what tells them apart.
        fm = re.match(r"^([A-Za-z_][A-Za-z0-9_]*)\s*(?::(?!:)|$)", body)
        if not fm:
            return None  # a block, a match arm body, anything that is not a literal
        explicit = explicit or ":" in body
        names.append(fm.group(1))
    if names and not explicit:
        # An all-shorthand body is indistinguishable from a plain block whose
        # last expression is an identifier (`if flag { x }`). Rust forbids a
        # struct literal in that position, but this lane does not parse Rust,
        # so it declines rather than guesses.
        return None
    return {"pos": start, "end": close, "fields": names, "rest": rest}


def struct_literal_sites(src: str, name: str) -> list[dict]:
    sites = []
    impl_bodies = impl_body_braces(src)
    for m in re.finditer(r"\b" + re.escape(name) + r"\s*\{", src):
        site = _literal_site(src, m.start(), m.end(), impl_bodies)
        if site is None:
            continue
        site["line"] = line_of(src, m.start())
        sites.append(site)
    return sites


def literal_sites_by_name(src: str, names: set[str]) -> dict[str, list[dict]]:
    """struct_literal_sites for every name in `names`, in one scan (no `line`)."""
    out: dict[str, list[dict]] = {}
    impl_bodies: set[int] | None = None
    for m in LITERAL_HEAD.finditer(src):
        name = m.group(1)
        if name not in names:
            continue
        if impl_bodies is None:
            impl_bodies = impl_body_braces(src)
        site = _literal_site(src, m.start(), m.end(), impl_bodies)
        if site is not None:
            out.setdefault(name, []).append(site)
    return out


# ------------------------------------------------------------------ the analysis


def analyse_file(base_src: str | None, head_src: str) -> tuple[list[dict], dict]:
    """Findings for one file, plus a tally of what was skipped."""
    return analyse_blanked(
        blank_comments_and_strings(base_src) if base_src is not None else None,
        blank_comments_and_strings(head_src),
    )


def analyse_blanked(base: str | None, head: str) -> tuple[list[dict], dict]:
    """The same judgement over sources whose comments and strings are already
    blanked, so a range-level run blanks each file exactly once."""
    stats = {
        "skipped_ambiguous": 0,
        "skipped_duplicate_name": 0,
        "skipped_foreign_import": 0,
        "skipped_bound_as_value": 0,
        "definitions_in_play": 0,
    }
    findings: list[dict] = []

    ranges = cfg_test_ranges(head)

    # ---- functions
    head_fns = fn_decls(head)
    base_fns = fn_decls(base) if base is not None else {}
    for name, decls in head_fns.items():
        if len(decls) != 1:
            stats["skipped_duplicate_name"] += 1
            continue
        decl = decls[0]
        if decl["has_self"]:
            continue
        prior = base_fns.get(name)
        prior_sig = prior[0]["sig"] if prior and len(prior) == 1 else None
        if prior_sig == decl["sig"]:
            continue  # this push did not touch the signature
        stats["definitions_in_play"] += 1
        wrong = []
        for site in fn_call_sites(head, name):
            if site["ambiguous"]:
                stats["skipped_ambiguous"] += 1
                continue
            if site["args"] == decl["params"]:
                continue
            # `#[derive(Clone, Debug)]` in a crate that declares `pub fn
            # derive(..)` is attribute input, not a call (in_attribute). The
            # added-site pass already read it so; this pass did not, and a
            # brand-new file puts every declaration in play here (measured
            # 2026-10-01: nine `#[derive(..)]` lines in the new
            # crates/trust-platform-derive/src/derive.rs read as calls).
            if in_attribute(head, site["pos"]):
                continue
            wrong.append(site)
        # The added-site pass's value rule, asked the same way: only of a name
        # with a disagreeing site. A closure parameter or a `let name = |..|`
        # SHADOWS the free function where it is in scope, so `name(x)` there is
        # a call of the value, not of the declaration whose arity changed
        # (measured: `test_function_has_requires` and `held` on cb/track-b,
        # and the six `local(..)` readings of cf258abe3d7d).
        if wrong and bound_as_value(head, name):
            stats["skipped_bound_as_value"] += 1
            continue
        for site in wrong:
            findings.append(
                {
                    "kind": "arity",
                    "name": name,
                    "decl_line": decl["line"],
                    "expected": decl["params"],
                    "line": site["line"],
                    "got": site["args"],
                    "cfg_test": in_cfg_test(site["pos"], ranges),
                }
            )

    # ---- structs
    head_structs = struct_decls(head)
    base_structs = struct_decls(base) if base is not None else {}
    for name, decls in head_structs.items():
        if len(decls) != 1:
            stats["skipped_duplicate_name"] += 1
            continue
        decl = decls[0]
        prior = base_structs.get(name)
        # FEATURE-GATED PUBLIC FIELDS (2026-09-30). A `pub` field of a `pub struct`
        # that exists only under `#[cfg(feature = ..)]` makes that feature
        # NON-ADDITIVE: a literal in another crate that compiles with the feature
        # off is E0063 the moment anything in the build graph turns it on, and
        # Cargo unifies features across the graph. Measured: trust-router's
        # `MirRouterConfig::enable_trust_cg_codegen` under `trust-cg-backend`, which
        # `rustc_mir_transform` turns on, left `trust-integration-tests`'
        # `verification_time_overhead` compiling in the `crates/` workspace and
        # failing in the compiler's graph, which no lane builds that target in.
        # The literal is in another crate, where this lane cannot see it; the
        # declaration is where it can, so a push that ADDS such a field is
        # refused here.
        prior_gated = prior[0]["gated"] if prior and len(prior) == 1 else []
        new_gated = sorted(set(decl["gated"]) - set(prior_gated))
        if new_gated:
            stats["definitions_in_play"] += 1
            findings.append(
                {
                    "kind": "feature-gated",
                    "name": name,
                    "decl_line": decl["line"],
                    "fields": new_gated,
                    "line": decl["line"],
                    "cfg_test": False,
                }
            )
        prior_fields = prior[0]["fields"] if prior and len(prior) == 1 else None
        if prior_fields == decl["fields"]:
            continue
        stats["definitions_in_play"] += 1
        want = set(decl["fields"])
        variant_bodies = enum_variant_braces(head)
        for site in struct_literal_sites(head, name):
            # `enum ActionKey { Event { role: Role, .. } }` declares a variant;
            # it is no literal of a same-named `struct Event` (in_variant_position).
            if in_variant_position(head, site["pos"], variant_bodies):
                continue
            got = set(site["fields"])
            missing = sorted(want - got)
            unknown = sorted(got - want)
            if site["rest"]:
                missing = []  # `..base` supplies the remainder
            if not missing and not unknown:
                continue
            findings.append(
                {
                    "kind": "fields",
                    "name": name,
                    "decl_line": decl["line"],
                    "missing": missing,
                    "unknown": unknown,
                    "line": site["line"],
                    "cfg_test": in_cfg_test(site["pos"], ranges),
                }
            )

    return findings, stats


def crate_root(path: str) -> str | None:
    parts = path.split("/")
    if len(parts) >= 2 and parts[0] in ("crates", "compiler"):
        return "/".join(parts[:2])
    return None


LOCAL_USE = re.compile(r"^\s*(pub\s+)?use\s+(crate|super|self)\b")


def imports_foreign(head_blank: str, name: str) -> bool:
    """Does this file `use` a NON-local path ending in `name`? If so the literal
    may denote another crate's type of the same name, and we must not judge it."""
    for line in head_blank.splitlines():
        if "use " not in line:
            continue
        if not re.search(r"\b" + re.escape(name) + r"\b", line):
            continue
        if not LOCAL_USE.match(line):
            return True
    return False


def analyse_cross_file_structs(
    sources: dict,
    stats: dict,
    carriers: dict[str, frozenset] | None = None,
    judged: set[str] | None = None,
) -> list[tuple[str, dict]]:
    """The measured miss that a same-file rule cannot see.

    `d26cb8c40e` added `PendingConst::promoted_global` in
    `crates/trust-thir-lower/src/lib.rs` and left the `#[cfg(test)]` initializer
    in `crates/trust-thir-lower/src/crate_module.rs` behind — E0063, red on main
    until `cf89d447db`. Both files are in that ONE commit's diff, so the decl and
    the stale site are both already in hand: widening from "the same file" to
    "the same crate, among the files this range changed" costs no extra I/O and
    catches it. It stays inside the changed set on purpose — reading a whole
    crate is 7-12 MiB (measured on `crates/trust-thir-lower` and
    `crates/trust-vcgen` at ad074447848d29974bec329d7e3587bb92dc4d38), which is
    not a price a push gate should pay.

    Functions deliberately do NOT get this widening: a cross-file free-function
    call resolves through `use`, and guessing at import resolution is how a gate
    starts refusing correct pushes.

    `carriers`, when given, maps each file to the destination commits that
    already hold its head blob at its path (carrier_sets). A (declaration,
    site) pair is set aside only when ONE destination commit holds BOTH files:
    that exact pairing is already published, so it is not this push's. Two
    files each carried by a DIFFERENT commit are not a published pair. A merge
    of two pushed branches builds exactly that — a widened struct from one, a
    stale `#[cfg(test)]` literal of its old shape from the other — and judged
    file by file (either file introduced) such a merge read 0 files and passed
    an E0063. An introduced file has no carrier, so a pair with one introduced
    end is judged, as before. Declarations are still COLLECTED from every file,
    so a name declared twice stays ambiguous exactly as it was before the
    narrowing.

    `judged`, when given, is the set of files analyse_blanked judged on their
    own (with no destination, every file). A declaration in any other file was
    not counted there, so it is counted here once a pair of it is judged."""
    findings: list[tuple[str, dict]] = []
    by_crate: dict[str, list[str]] = {}
    for path in sources:
        root = crate_root(path)
        if root:
            by_crate.setdefault(root, []).append(path)

    for _root, paths in by_crate.items():
        head_decls: dict[str, list[tuple[str, dict]]] = {}
        base_decls: dict[str, list[tuple[str, dict]]] = {}
        for path in paths:
            base_blank, head_blank = sources[path]
            for name, decls in struct_decls(head_blank).items():
                head_decls.setdefault(name, []).extend((path, d) for d in decls)
            if base_blank is not None:
                for name, decls in struct_decls(base_blank).items():
                    base_decls.setdefault(name, []).extend((path, d) for d in decls)

        for name, decls in head_decls.items():
            if len(decls) != 1:
                stats["skipped_duplicate_name"] += 1
                continue
            decl_path, decl = decls[0]
            prior = base_decls.get(name)
            prior_fields = prior[0][1]["fields"] if prior and len(prior) == 1 else None
            if prior_fields == decl["fields"]:
                continue
            # NOT counted again when analyse_blanked judged the declaring file:
            # it counted this definition there, and the summary line reports
            # DEFINITIONS, so counting one twice would misstate the subject.
            counted = judged is None or decl_path in judged
            want = set(decl["fields"])
            for path in paths:
                if path == decl_path:
                    continue  # analyse_file already judged the declaring file
                if carriers is not None and carriers[decl_path] & carriers[path]:
                    continue  # one destination commit already holds this very pair
                if not counted:
                    stats["definitions_in_play"] += 1
                    counted = True
                _base_blank, head_blank = sources[path]
                if imports_foreign(head_blank, name):
                    stats["skipped_foreign_import"] += 1
                    continue
                ranges = cfg_test_ranges(head_blank)
                variant_bodies = enum_variant_braces(head_blank)
                for site in struct_literal_sites(head_blank, name):
                    # A variant declaration in another file of the crate
                    # (`ActionKey::Event { .. }` in explore.rs beside `struct
                    # Event` in program.rs, measured 2026-10-01) is no literal.
                    if in_variant_position(head_blank, site["pos"], variant_bodies):
                        continue
                    got = set(site["fields"])
                    missing = [] if site["rest"] else sorted(want - got)
                    unknown = sorted(got - want)
                    if not missing and not unknown:
                        continue
                    findings.append(
                        (
                            path,
                            {
                                "kind": "fields",
                                "name": name,
                                "decl_line": decl["line"],
                                "missing": missing,
                                "unknown": unknown,
                                "line": site["line"],
                                "cfg_test": in_cfg_test(site["pos"], ranges),
                            },
                        )
                    )
    return findings


# ------------------------------------------------- sites the push ADDS (F1b)


def site_text(src: str, site: dict) -> str:
    """A site's text, whitespace-collapsed: `Rec { a: 1 }` from its name to its
    closing delimiter. Two sites with the same text are the same site."""
    return re.sub(r"\s+", " ", src[site["pos"] : site["end"] + 1])


def added_sites(head_src: str, head_sites: list[dict], base_src: str | None, base_sites: list[dict]) -> list[dict]:
    """The sites of `head_src` whose text is not at the base blob of the same
    path, counted as a multiset: a second copy of a text the base already has
    is added, and a file the base lacks (added, or moved here: F5) adds all of
    its sites."""
    pool: dict[str, int] = {}
    if base_src is not None:
        for site in base_sites:
            key = site_text(base_src, site)
            pool[key] = pool.get(key, 0) + 1
    out = []
    for site in head_sites:
        key = site_text(head_src, site)
        if pool.get(key):
            pool[key] -= 1
        else:
            out.append(site)
    return out


def struct_names_at(head: str, root: str, cwd: str | None) -> dict[str, list[str]]:
    """name -> the path of each line at `head`, in the crate at `root`, that
    spells `struct <name>` — one `git grep` over the pushed tree, so a
    declaration in a file the push never touched is found without reading the
    crate. A candidate list, not a verdict: comments and strings still match
    here, and analyse_added_sites confirms each on blanked text."""
    proc = subprocess.run(
        [
            *GIT, "-c", "grep.lineNumber=false", "-c", "grep.column=false",
            "grep", "--no-color", "--full-name", "-I", "-z", "-o", "-E",
            r"(^|[^A-Za-z0-9_])struct[[:space:]]+[A-Za-z_][A-Za-z0-9_]*",
            head, "--", f":(top,literal){root}/",
        ],
        capture_output=True,
        cwd=cwd,
    )
    if proc.returncode == 1:
        return {}  # no line matches
    if proc.returncode != 0:
        err = proc.stderr.decode("utf-8", "replace").strip()
        raise RuntimeError(f"git grep struct {head[:12]} -- {root}/ failed: {err}")
    prefix = os.fsencode(head) + b":"
    data = proc.stdout
    out: dict[str, list[str]] = {}
    i = 0
    while i < len(data):
        # `<rev>:<path>\0<match>\n`; a path may hold a newline, never a NUL.
        z = data.index(b"\0", i)
        nl = data.find(b"\n", z)
        nl = len(data) if nl < 0 else nl
        name_b = data[i:z]
        if not name_b.startswith(prefix):
            raise RuntimeError(f"git grep printed an unreadable line: {name_b[:80]!r}")
        m = re.search(rb"struct\s+([A-Za-z_][A-Za-z0-9_]*)", data[z + 1 : nl])
        if m:
            out.setdefault(m.group(1).decode("ascii"), []).append(os.fsdecode(name_b[len(prefix):]))
        i = nl + 1
    return out


CALLISH_AFTER = re.compile(r"\s*(?:\(|!|::)")
USE_LINE = re.compile(r"\s*(?:pub(?:\s*\([^)]*\))?\s+)?use\b")
# A `use` DECLARATION, from the keyword to its `;`, over as many lines as
# rustfmt wraps it onto. `use<..>` (a precise-capturing bound, `impl Tr + use<'a>`)
# is not a declaration and is never followed by its own `;` statement.
USE_DECLARATION = re.compile(r"\buse\b(?!\s*<)[^;]*;")


@per_source
def use_declaration_spans(blank: str) -> tuple[list[int], list[int]]:
    """(starts, ends) of every `use ..;` declaration in blanked source, sorted
    by start. They do not nest, so bisect finds the only one that can hold a
    position, as in_attribute does."""
    starts: list[int] = []
    ends: list[int] = []
    for m in USE_DECLARATION.finditer(blank):
        starts.append(m.start())
        ends.append(m.end())
    return starts, ends


def in_use_declaration(blank: str, pos: int) -> bool:
    starts, ends = use_declaration_spans(blank)
    k = bisect.bisect_right(starts, pos) - 1
    return k >= 0 and pos < ends[k]


def bound_as_value(blank: str, name: str) -> bool:
    """Does `name` appear in this blanked file anywhere but as a function's
    own declaration (`fn name`), a call or macro head (`name(`, `name!`), a
    path or method segment, or a `use` declaration? Such an occurrence is a
    value of that name — `let name = |..| ..`, a parameter `name: impl Fn(..)`,
    a closure parameter — which SHADOWS the free function wherever it is in
    scope, so a call of `name` may not be a call of the declaration at all.

    Measured on real history before this test: every added-call false finding
    in the 400-commit replay was such a closure (`let read_u32 = |at| ..`,
    `let leaf = || ..`, `let observe = |bytes| ..`, `let resolve = |..| ..`,
    `let bv = |n| ..` beside a same-named `fn` elsewhere in the file). The
    measured `local(..)` and `observe(..)` readings of 2026-09-27 are the same
    class. It is a SKIP: the name is then not judged at all, by the added-site
    pass or by the changed-signature pass (analyse_blanked).

    A `use` is read by DECLARATION, not by line. rustfmt wraps a test
    module's `use super::{\\n    a,\\n    f,\\n};` so that `f,` sits on a line
    of its own, and the line reading took that import of the free function for
    a value of its name: measured 2026-09-29, it would have skipped every
    name 78a0bef5ff is refused on (`propagate_union_lane_taint` and three
    siblings, 45 E0061 sites) and every name ed21a2887f is refused on (27
    sites), turning both to PASS, the moment the changed-signature pass asked
    this question — the regressions this lane exists to catch."""
    for m in re.finditer(r"\b" + re.escape(name) + r"\b", blank):
        if CALLISH_AFTER.match(blank, m.end()):
            continue
        before = tail_before(blank, m.start())
        if re.search(r"\bfn$", before) or before.endswith(".") or before.endswith(":"):
            continue
        line_start = blank.rfind("\n", 0, m.start()) + 1
        if USE_LINE.match(blank, line_start) or in_use_declaration(blank, m.start()):
            continue
        return True
    return False


def enum_variant_braces(blank: str) -> list[tuple[int, int]]:
    """(open, close) of every `enum` body in blanked source. A `Name {` directly
    inside one (at brace depth one) is a VARIANT DECLARATION —
    `enum CalleeOwner { TraitImpl { trait_name: &str, self_ty: SelfTyHead } }` —
    never a literal, whatever struct elsewhere in the crate shares its name."""
    bodies = []
    for m in re.finditer(r"\benum\s+[A-Za-z_][A-Za-z0-9_]*", blank):
        i, angle = m.end(), 0
        while i < len(blank):
            if blank.startswith("->", i):
                i += 2
                continue
            c = blank[i]
            if c == "<":
                angle += 1
            elif c == ">" and angle:
                angle -= 1
            elif not angle and c == "{":
                close = skip_balanced(blank, i, "{", "}")
                if close > 0:
                    bodies.append((i, close - 1))
                break
            elif not angle and c in ";=}(":
                break
            i += 1
    return bodies


def in_variant_position(blank: str, pos: int, bodies: list[tuple[int, int]]) -> bool:
    for open_, close in bodies:
        if open_ < pos < close:
            inner = blank[open_ + 1 : pos]
            if inner.count("{") == inner.count("}"):
                return True
    return False


def declarations_named(blank: str, name: str) -> int:
    """How many times blanked source declares a struct of this name, of ANY
    kind — named-field, tuple or unit. struct_decls reads only the first kind;
    a tuple struct of the same name elsewhere still makes the name ambiguous."""
    return len(re.findall(r"\bstruct\s+" + re.escape(name) + r"\b", blank))


USE_STATEMENT = re.compile(r"\buse\b([^;]*);")
LOCAL_USE_PATH = re.compile(r"\s*(?:::\s*)?(?:crate|super|self)\b")


def imports_foreign_statement(blank: str, name: str) -> bool:
    """imports_foreign read by STATEMENT as well as by line. rustfmt wraps a
    long import as `use rustc_middle::thir::{\\n    Ascription, ..\\n};`, and
    the line reading never sees `use ` and the name on one line, so it judged
    a foreign `Ascription { .. }` against the crate's own `Ascription`
    (compiler/rustc_mir_build/src/thir/pattern/mod.rs, measured 2026-09-28).
    A name spelled as a word anywhere in a `use ..;` statement whose path does
    not start with crate, super or self counts as foreign. It is the line
    reading OR the statement reading, so it skips wherever the line reading
    alone skipped."""
    if imports_foreign(blank, name):
        return True
    word = re.compile(r"\b" + re.escape(name) + r"\b")
    for m in USE_STATEMENT.finditer(blank):
        if word.search(m.group(1)) and not LOCAL_USE_PATH.match(m.group(1)):
            return True
    return False


@per_source
def attribute_spans(blank: str) -> tuple[list[int], list[int]]:
    """(starts, ends) of every `#[..]` and `#![..]` in blanked source, sorted by
    start. A `name(` inside one is attribute input, never a call:
    `#[derive(Debug)]` in a file that also declares `pub fn derive(corpus,
    kind)` (crates/trust-js-differential/src/slice.rs, measured 2026-09-28)."""
    starts: list[int] = []
    ends: list[int] = []
    for m in re.finditer(r"#!?\s*\[", blank):
        close = skip_balanced(blank, m.end() - 1, "[", "]")
        if close > 0:
            starts.append(m.start())
            ends.append(close)
    return starts, ends


def in_attribute(blank: str, pos: int) -> bool:
    starts, ends = attribute_spans(blank)
    # Attributes do not nest in the source this reads, so the one that starts
    # last before pos is the only one that can hold it.
    k = bisect.bisect_left(starts, pos) - 1
    return k >= 0 and pos < ends[k]


MACRO_ARM_KEY = re.compile(r"@\s*[A-Za-z_][A-Za-z0-9_]*\s*(?<![=!<>])=$")


def in_macro_arm_input(blank: str, pos: int) -> bool:
    """Is the site at pos the value of an `@key =` in a macro invocation? `@`
    before an identifier and `=` is never Rust expression or pattern syntax
    (a binding is `name @ Pat`); it is a macro's own input grammar, and the
    macro may supply the rest of the literal: `declare_lint!`'s
    `@future_incompatible = FutureIncompatibleInfo { reason: .., }` expands to
    `FutureIncompatibleInfo { $($field: $val,)* ..default_fields_for_macro() }`
    (compiler/rustc_lint_defs; 51 such literals at 84a2e55537, and an upstream
    port adds more — cdbca2287b added four)."""
    return bool(MACRO_ARM_KEY.search(tail_before(blank, pos, 64)))


SINGLE_COLON = re.compile(r"(?<!:):(?!:)")


def rust_signature(decl: dict) -> bool:
    """Is every parameter of this fn declaration `pattern: Type`? A Rust
    signature (edition 2018 on) has no other form, but macro input spelled like
    one does: `fn with_forced_trimmed_paths(ForceTrimmedGuard,
    FORCE_TRIMMED_PATH);` inside a `define_helper!` invocation
    (compiler/rustc_middle/src/ty/print/pretty.rs, measured 2026-09-28), whose
    two "parameters" say nothing about the generated function's arity. `::`
    alone is a path, not the `:` of a typed pattern; a parameter's attributes
    are stepped over."""
    parsed = declared_segments(decl["sig"], 0)
    if parsed is None:
        return False
    for seg in parsed[0]:
        body = seg
        while True:
            m = re.search(r"#\s*\[", body)
            if m is None:
                break
            close = skip_balanced(body, m.end() - 1, "[", "]")
            if close < 0:
                return False
            body = body[: m.start()] + " " + body[close:]
        body = body.strip()
        if body and not SINGLE_COLON.search(body):
            return False
    return True


def analyse_added_sites(
    sources: dict,
    head: str,
    carriers: dict[str, frozenset] | None,
    introduced: set[str],
    known: list[str] | None,
    cwd: str | None,
    counts: dict,
) -> list[tuple[str, dict]]:
    """F1b: a site the push ADDS, judged against the declaration at the pushed
    tip, whether or not the push changes that declaration.

    The other two passes judge only declarations whose shape base..head
    changes. A push that does not change the declaration but adds a site that
    disagrees with it was never judged: branch A widens `Rec` and lands; branch
    B, forked before A, adds a `#[cfg(test)]` `Rec { a: 1 }`; B merged into (or
    rebased onto) main changes no declaration, and its union is E0063.

    A site is ADDED when its text is not at the base blob of the same path
    (added_sites). A site whose text the base already holds is the
    destination's own, exactly as a carried file is. Each added site is read by
    the same readers (call_sites_by_name / literal_sites_by_name share
    _call_site / _literal_site with the changed-declaration passes) and
    excused exactly as they excuse (`..rest`, all-shorthand bodies, closures
    and generics in arguments, method and path calls, a foreign `use`), and it
    is judged at the same scope: a call against a free function declared once
    in the SAME file; a literal against a struct declared once in its own
    file, or else declared exactly once in its crate at the pushed tip. That
    declaration may sit in a file the push never touched, so it is found by
    one `git grep` of the pushed tree (struct_names_at), never by reading the
    crate. A (declaration, site) pair is set aside, as in
    analyse_cross_file_structs, when ONE destination commit holds both files
    at their pushed blobs; a same-file pair when a destination commit holds
    the file.

    Its own skips: a function name the file also binds as a value
    (bound_as_value) and a `Name {` that declares an enum variant
    (enum_variant_braces), both measured false findings on real history (the
    module docstring has the numbers), and a struct name spelled `struct Name`
    more than once in the crate (declarations_named), the lane's duplicate
    rule counted over the crate. Four read macro and attribute input for what
    it is, each measured on the tree at 84a2e55537: a call inside `#[..]`
    (in_attribute), a call of a fn whose parameters are not `pattern: Type`
    (rust_signature), a foreign import wrapped over several lines
    (imports_foreign_statement), and a literal after a macro's `@key =`
    (in_macro_arm_input). Every skip judges less, never more. Only
    bound_as_value also reaches a changed-declaration pass: analyse_blanked
    asks it of a changed free function with a disagreeing call, exactly as
    this pass does."""
    findings: list[tuple[str, dict]] = []
    extra_carriers: dict[str, frozenset] = {}

    def carried_by(path: str) -> frozenset:
        if carriers is None:
            return frozenset()
        if path in carriers:
            return carriers[path]
        if path not in extra_carriers:
            extra_carriers.update(carrier_sets(head, [path], known or [], cwd))
        return extra_carriers[path]

    # ---- calls: the same file, as for a changed signature
    for path, (base_blank, head_blank) in sources.items():
        if path not in introduced:
            continue  # a destination commit holds this file, so every same-file pair
        fns = fn_decls(head_blank)
        names = {n for n, ds in fns.items() if len(ds) == 1 and not ds[0]["has_self"]}
        if not names:
            continue
        head_sites = call_sites_by_name(head_blank, names)
        if not head_sites:
            continue
        base_sites = call_sites_by_name(base_blank, set(head_sites)) if base_blank is not None else {}
        ranges = None
        for name, sites in head_sites.items():
            decl = fns[name][0]
            new = [
                site
                for site in added_sites(head_blank, sites, base_blank, base_sites.get(name, []))
                if not site["ambiguous"]
            ]
            counts["added"] += len(new)
            wrong = [site for site in new if site["args"] != decl["params"]]
            if not wrong:
                continue
            # The skips are asked only of a name with a disagreeing site: they
            # can only remove a finding, and each scans the whole file.
            wrong = [site for site in wrong if not in_attribute(head_blank, site["pos"])]
            if not wrong:
                continue  # `#[derive(..)]` is attribute input, not a call of `fn derive`
            if not rust_signature(decl):
                continue  # macro input spelled like a fn, not a Rust signature
            if bound_as_value(head_blank, name) or imports_foreign_statement(head_blank, name):
                continue  # a local value or an import of this name may be what is called
            for site in wrong:
                if ranges is None:
                    ranges = cfg_test_ranges(head_blank)
                findings.append(
                    (
                        path,
                        {
                            "kind": "arity",
                            "name": name,
                            "decl_line": decl["line"],
                            "expected": decl["params"],
                            "line": line_of(head_blank, site["pos"]),
                            "got": site["args"],
                            "cfg_test": in_cfg_test(site["pos"], ranges),
                            "added": True,
                        },
                    )
                )

    # ---- literals: the same crate, as for a changed struct
    by_crate: dict[str, list[str]] = {}
    for path in sources:
        root = crate_root(path)
        if root:
            by_crate.setdefault(root, []).append(path)
    for root, paths in by_crate.items():
        spelled = {p: set(LITERAL_HEAD.findall(sources[p][1])) for p in paths}
        if not any(spelled.values()):
            continue
        declared = struct_names_at(head, root, cwd)
        blanks: dict[str, str | None] = {p: sources[p][1] for p in paths}

        def blank_of(path: str) -> str | None:
            if path not in blanks:
                try:
                    src = blob_at(head, path, cwd=cwd)
                except UnicodeDecodeError:
                    src = None  # unreadable as text: the name stays unresolved
                blanks[path] = blank_comments_and_strings(src) if src is not None else None
            return blanks[path]

        resolved: dict[str, tuple[str, dict] | None] = {}

        def crate_declaration(name: str) -> tuple[str, dict] | None:
            """The one declaration of `name` in the crate, or None when there is
            none the lane can read or more than one."""
            if name not in resolved:
                total, decls, readable = 0, [], True
                for p in dict.fromkeys(declared.get(name, [])):
                    blank = blank_of(p)
                    if blank is None:
                        readable = False
                        break
                    total += declarations_named(blank, name)
                    decls.extend((p, d) for d in struct_decls(blank).get(name, []))
                resolved[name] = decls[0] if readable and total == 1 and len(decls) == 1 else None
            return resolved[name]

        for path in paths:
            names = spelled[path] & set(declared)
            if not names:
                continue
            base_blank, head_blank = sources[path]
            head_sites = literal_sites_by_name(head_blank, names)
            if not head_sites:
                continue
            base_sites = (
                literal_sites_by_name(base_blank, set(head_sites)) if base_blank is not None else {}
            )
            ranges = None
            local = None
            variants = None
            for name, sites in head_sites.items():
                new = added_sites(head_blank, sites, base_blank, base_sites.get(name, []))
                if not new:
                    continue
                if declarations_named(head_blank, name):
                    # declared in this very file: the same-file reading
                    if local is None:
                        local = struct_decls(head_blank)
                    here = local.get(name, [])
                    if declarations_named(head_blank, name) != 1 or len(here) != 1:
                        continue
                    decl_path, decl = path, here[0]
                else:
                    found = crate_declaration(name)
                    if found is None:
                        continue
                    decl_path, decl = found
                counts["added"] += len(new)
                want = set(decl["fields"])
                wrong = []
                for site in new:
                    got = set(site["fields"])
                    missing = [] if site["rest"] else sorted(want - got)
                    unknown = sorted(got - want)
                    if missing or unknown:
                        wrong.append((site, missing, unknown))
                if not wrong:
                    continue
                # As for calls, the skips are asked only of a disagreeing site.
                if variants is None:
                    variants = enum_variant_braces(head_blank)
                wrong = [
                    w
                    for w in wrong
                    if not in_variant_position(head_blank, w[0]["pos"], variants)
                    and not in_macro_arm_input(head_blank, w[0]["pos"])
                ]
                if not wrong:
                    continue
                site_carriers = carried_by(path)
                if site_carriers and site_carriers & carried_by(decl_path):
                    continue  # one destination commit already holds this very pair
                if decl_path != path and imports_foreign_statement(head_blank, name):
                    continue
                for site, missing, unknown in wrong:
                    if ranges is None:
                        ranges = cfg_test_ranges(head_blank)
                    findings.append(
                        (
                            path,
                            {
                                "kind": "fields",
                                "name": name,
                                "decl_line": decl["line"],
                                "decl_path": decl_path,
                                "missing": missing,
                                "unknown": unknown,
                                "line": line_of(head_blank, site["pos"]),
                                "cfg_test": in_cfg_test(site["pos"], ranges),
                                "added": True,
                            },
                        )
                    )
    return findings


def uncarried_crates(
    head: str, shared: dict[str, frozenset], order: list[str], cwd: str | None, tries: int = 8
) -> set[str]:
    """Of the crates each of whose changed files one destination commit
    carries (`shared`: crate -> those commits), the ones no such commit carries
    WHOLE: some .rs file in the crate differs between it and `head`. Such a
    crate can still hold an added site whose declaration is in a file the
    range does not change (a published branch merged onto a main that widened
    the struct), so it is read. A crate one commit carries whole holds no pair
    that commit lacks. At most `tries` diffs; a crate left undecided is read,
    which costs time and never a verdict: every pair is still judged by
    carrier_sets."""
    left = dict(shared)
    for k in order:
        if not left or tries == 0:
            break
        roots = [r for r, ks in left.items() if k in ks]
        if not roots:
            continue
        tries -= 1
        differing = {
            crate_root(p) for p in changed_paths(k, head, cwd=cwd, within=roots) if p.endswith(".rs")
        }
        for r in roots:
            if r not in differing:
                del left[r]
    return set(left)


# ------------------------------------------------------------------ the driver


SHA = re.compile(r"[0-9a-f]{40}|[0-9a-f]{64}")


def pushed_ref_lines(value: str) -> tuple[list[tuple[str, str]], int]:
    """(local sha, remote sha) for each ref UPDATE git is pushing, and the
    number of deletions. A deletion sends nothing to read, so it is counted and
    dropped. Every non-blank line must be what git hands a pre-push hook —
    `<local ref> <local sha> <remote ref> <remote sha>` — or this raises: a
    line the lane cannot read is never skipped, because skipping it judges
    less than the push sends, and a value whose every line was skipped used to
    widen to origin/main..HEAD, which the push does not send at all."""
    out = []
    deletions = 0
    for line in value.splitlines():
        parts = line.split()
        if not parts:
            continue
        if len(parts) != 4 or not SHA.fullmatch(parts[1]) or not SHA.fullmatch(parts[3]):
            raise PushedRefsUnreadable(
                "not a pre-push ref line "
                f"(<local ref> <local sha> <remote ref> <remote sha>): {line!r}"
            )
        _local_ref, local_sha, _remote_ref, remote_sha = parts
        if local_sha.strip("0") == "":
            deletions += 1
            continue  # a deletion pushes nothing to read
        out.append((local_sha, remote_sha))
    return out, deletions


def destination_refs(remote: str, cwd: str | None) -> list[tuple[str, str]]:
    """(commit, advertised ref) for each ref the push destination ITSELF
    advertises whose object is a commit this store holds. The reading is
    scripts/lib/push_destination.sh's, the one check_revert_rationale.sh
    excludes on, so the two lanes cannot disagree about what is published."""
    if not DESTINATION_HELPER.is_file():
        raise DestinationUnreadable(
            f"{DESTINATION_HELPER} is missing; refusing to guess published history"
        )
    proc = subprocess.run(
        ["bash", str(DESTINATION_HELPER), remote], capture_output=True, text=True, cwd=cwd
    )
    if proc.returncode != 0:
        raise DestinationUnreadable(
            proc.stderr.strip() or f"{DESTINATION_HELPER.name} exited {proc.returncode}"
        )
    refs = []
    for line in proc.stdout.splitlines():
        m = re.fullmatch(r"([0-9a-f]{40}) (refs/\S+)", line)
        if not m:
            raise DestinationUnreadable(
                f"{DESTINATION_HELPER.name} printed an unreadable line: {line!r}"
            )
        refs.append((m.group(1), m.group(2)))
    return refs


def introduced_commits(head: str, known: list[str], cwd: str | None) -> tuple[list[str], list[str]]:
    """(the commits `head` brings that no destination ref reaches, the
    destination-side commits they sit on). One `rev-list --boundary`; the
    exclusions go on stdin so no destination can overflow an argument list."""
    proc = subprocess.run(
        ["git", "--no-replace-objects", "rev-list", "--boundary", "--stdin"],
        input="".join([f"{head}\n"] + [f"^{c}\n" for c in known]),
        capture_output=True,
        text=True,
        cwd=cwd,
    )
    if proc.returncode != 0:
        raise RuntimeError(
            f"git rev-list --boundary {head[:12]} --not <destination refs> failed: {proc.stderr.strip()}"
        )
    new: list[str] = []
    boundary: list[str] = []
    for line in proc.stdout.split():
        if line.startswith("-"):
            boundary.append(line[1:])
        else:
            new.append(line)
    return new, boundary


def blob_ids(specs: list[str], cwd: str | None) -> list[str | None]:
    """The blob each `<rev>:<path>` names, or None — one `cat-file --batch-check`.

    Names go in and come out as BYTES (os.fsencode, the encoding every other
    git argument gets), because changed_paths reads a path of any bytes. The
    batch protocol is one name per line, so a name holding a newline is asked
    on its own, with `cat-file -t` and `rev-parse` as argv."""
    if not specs:
        return []
    batched = [spec for spec in specs if "\n" not in spec]
    answers: dict[str, str | None] = {}
    if batched:
        proc = subprocess.run(
            ["git", "--no-replace-objects", "cat-file", "--batch-check=%(objectname) %(objecttype)"],
            input=b"".join(os.fsencode(spec) + b"\n" for spec in batched),
            capture_output=True,
            cwd=cwd,
        )
        if proc.returncode != 0:
            err = proc.stderr.decode("utf-8", "replace").strip()
            raise RuntimeError(f"git cat-file --batch-check failed: {err}")
        # Only a `<oid> blob` answer is read. Every other answer (`<name>
        # missing`, a tree) is one line, as the name that produced it has no
        # newline, so the count still pairs each answer with its question.
        lines = proc.stdout.split(b"\n")
        if lines and lines[-1] == b"":
            lines.pop()
        if len(lines) != len(batched):
            raise RuntimeError(
                f"git cat-file answered {len(lines)} line(s) for {len(batched)} object name(s)"
            )
        for spec, line in zip(batched, lines):
            m = re.fullmatch(rb"([0-9a-f]{40}) blob", line)
            answers[spec] = m.group(1).decode("ascii") if m else None
    for spec in specs:
        if spec in answers:
            continue
        kind = subprocess.run(
            ["git", "--no-replace-objects", "cat-file", "-t", spec], capture_output=True, cwd=cwd
        )
        oid = subprocess.run(
            ["git", "--no-replace-objects", "rev-parse", "--verify", "--quiet", spec],
            capture_output=True,
            cwd=cwd,
        )
        m = re.fullmatch(rb"([0-9a-f]{40})\n?", oid.stdout)
        is_blob = kind.returncode == 0 and kind.stdout.strip() == b"blob"
        answers[spec] = m.group(1).decode("ascii") if is_blob and oid.returncode == 0 and m else None
    return [answers[spec] for spec in specs]


def carrier_sets(head: str, paths: list[str], known: list[str], cwd: str | None) -> dict[str, frozenset]:
    """For each path, the `known` commits whose blob at that same path IS the
    blob at `head` — the destination commits that already carry the file byte
    for byte. Empty for a file no known commit carries, and for a file `head`
    deletes. A file with an empty set is INTRODUCED by the push, however
    `base..head` happens to reach it; that test is unchanged.

    A SET, not a yes/no, because a cross-file (declaration, site) pair is the
    destination's only when ONE commit carries BOTH files: two files each
    carried by a different commit (a merge of two published branches) form a
    pair no destination commit has (analyse_cross_file_structs)."""
    specs = []
    for path in paths:
        specs.append(f"{head}:{path}")
        specs.extend(f"{k}:{path}" for k in known)
    ids = blob_ids(specs, cwd)
    stride = 1 + len(known)
    out: dict[str, frozenset] = {}
    for i, path in enumerate(paths):
        row = ids[i * stride : (i + 1) * stride]
        if row[0] is None:
            out[path] = frozenset()
            continue
        out[path] = frozenset(k for k, blob in zip(known, row[1:]) if blob == row[0])
    return out


def introduced_subject(
    lines: list[tuple[str, str]], remote: str, cwd: str | None
) -> tuple[list[dict], str]:
    """The ranges a push with a known destination introduces. Every range keeps
    the base the lane always used for an update (the ref's old tip, which git
    read from the destination), so an introduced file is judged exactly as
    before; what changes is which files are introduced. A NEW ref is judged
    against the destination's advertised `refs/heads/main`, never the local
    `origin/main`, which a stale or forged tracking ref could aim at head."""
    dest = destination_refs(remote, cwd)
    dest_commits = list(dict.fromkeys(commit for commit, _ref in dest))
    dest_main = next((commit for commit, ref in dest if ref == "refs/heads/main"), None)
    ranges = []
    parts = []
    for local_sha, remote_sha in lines:
        new, boundary = introduced_commits(local_sha, dest_commits, cwd)
        if not new:
            parts.append(f"{local_sha[:12]} (already on the destination: nothing introduced)")
            continue
        if remote_sha.strip("0"):
            base = remote_sha
        elif dest_main is not None:
            base = dest_main
        else:
            raise DestinationUnreadable(
                f"new ref {local_sha[:12]}: {remote} advertises no refs/heads/main that this "
                "object store holds, so nothing destination-side can judge a new branch "
                "(git fetch, then retry)"
            )
        known = list(dict.fromkeys(dest_commits + boundary))
        # The commits a whole-crate test tries first: the destination-side
        # parents of what the push introduces, then destination main. A merge
        # of main is carried by the main commit it merged, which is a boundary.
        order = list(dict.fromkeys(boundary + ([dest_main] if dest_main else []) + dest_commits))
        ranges.append({"base": base, "head": local_sha, "known": known, "order": order})
        parts.append(f"{base[:12]}..{local_sha[:12]} ({len(new)} introduced commit(s))")
    return ranges, f"what this push introduces to {remote}: " + (", ".join(parts) or "no ref")


def resolve_subject(args, cwd: str | None) -> tuple[list[dict] | None, str]:
    """(ranges, a one-line account of the reading). `known` None judges every
    file in base..head; a list judges only files none of its commits carries.

    Ranges is None when there is NO subject: under --push-context, a non-blank
    TRUST_PUSHED_REFS whose every line is a deletion. That push sends no file,
    so it is SKIPPED, never widened to origin/main..HEAD, which it does not
    send. A line that is not a pre-push ref line raises PushedRefsUnreadable
    (exit 2), again never a widening. Only an unset or blank TRUST_PUSHED_REFS
    (no push in flight) reads the standing origin/main..HEAD."""
    if args.range:
        if ".." not in args.range:
            raise RuntimeError(f"--range must be A..B, got {args.range!r}")
        a, b = args.range.split("..", 1)
        rng = {"base": a or "origin/main", "head": b or "HEAD", "known": None}
        return [rng], f"{rng['base'][:12]}..{rng['head'][:12]}"

    if args.push_context:
        pushed = os.environ.get("TRUST_PUSHED_REFS", "")
        if pushed.strip():
            lines, deletions = pushed_ref_lines(pushed)
            if not lines:
                return None, (
                    f"nothing pushed to read ({deletions} ref deletion(s) and no update; "
                    "a deletion sends no file)"
                )
            remote = args.remote or os.environ.get("TRUST_PUSH_REMOTE", "")
            if remote:
                return introduced_subject(lines, remote, cwd)
            # No destination named: every pushed range in full, as before.
            ranges = [
                {"base": r if r.strip("0") else "origin/main", "head": l, "known": None}
                for l, r in lines
            ]
            return ranges, ", ".join(f"{g['base'][:12]}..{g['head'][:12]}" for g in ranges)
        # unset or blank TRUST_PUSHED_REFS: no push in flight, so widen to the
        # standing reading, and say so

    return [{"base": "origin/main", "head": "HEAD", "known": None}], "origin/main..HEAD"


def run(args) -> int:
    cwd = args.repo
    try:
        subject, reading = resolve_subject(args, cwd)
    except DestinationUnreadable as exc:
        print(f"cfg-test-skew: could NOT READ the push destination — {exc}", file=sys.stderr)
        print("               refusing to guess what it already carries.", file=sys.stderr)
        return 2
    except PushedRefsUnreadable as exc:
        print(f"cfg-test-skew: could NOT READ TRUST_PUSHED_REFS — {exc}", file=sys.stderr)
        print("               refusing to judge anything but what git says it is pushing.", file=sys.stderr)
        return 2
    print(f"SUBJECT: {reading}")
    if subject is None:
        print("SKIPPED: this push sends no file, so there is no construction site to judge.")
        return 0

    all_findings: list[tuple[str, dict]] = []
    total_stats = {
        "skipped_ambiguous": 0,
        "skipped_duplicate_name": 0,
        "skipped_foreign_import": 0,
        "skipped_bound_as_value": 0,
        "definitions_in_play": 0,
    }
    files_read = 0
    carried = 0
    context = 0
    narrowed = False
    added = {"added": 0}
    sources: dict = {}

    for rng in subject:
        base, head, known = rng["base"], rng["head"], rng["known"]
        try:
            names = changed_paths(base, head, cwd=cwd)
        except RuntimeError as exc:
            print(f"cfg-test-skew: could NOT READ the range {base}..{head} — {exc}", file=sys.stderr)
            print("               usually an unfetched remote sha: git fetch, rebase, retry.", file=sys.stderr)
            return 2
        paths = [p for p in names if p.endswith(".rs") and p.startswith(WATCHED_PREFIXES)]
        if known is None:
            carriers = None
            introduced = set(paths)
        else:
            narrowed = True
            carriers = carrier_sets(head, paths, known, cwd)
            introduced = {p for p in paths if not carriers[p]}
        # A file the destination already carries is never judged on its own,
        # but its crate is still read as context unless ONE destination commit
        # carries every changed file of that crate: only then is every
        # cross-file pair there one the destination already has
        # (analyse_cross_file_structs). A crate holding an introduced file has
        # no such commit, so every crate the push touches is still read.
        common: dict[str, frozenset] = {}
        for p in paths:
            root = crate_root(p)
            if root is None:
                continue
            here = carriers[p] if carriers is not None else frozenset()
            common[root] = common[root] & here if root in common else here
        live_crates = {root for root, shared in common.items() if not shared}
        # A crate whose changed files one destination commit carries is still
        # read unless such a commit carries the crate WHOLE: a site those
        # files add can name a declaration the range does not touch, in a
        # file that commit holds at another blob (analyse_added_sites).
        if carriers is not None:
            live_crates |= uncarried_crates(
                head,
                {root: shared for root, shared in common.items() if shared},
                rng.get("order") or known,
                cwd,
            )
        for path in paths:
            is_introduced = path in introduced
            if not is_introduced:
                carried += 1
                if crate_root(path) not in live_crates:
                    continue
            head_src = blob_at(head, path, cwd=cwd)
            if head_src is None:
                continue  # deleted by this push
            base_src = blob_at(base, path, cwd=cwd)
            files_read += 1
            head_blank = blank_comments_and_strings(head_src)
            base_blank = blank_comments_and_strings(base_src) if base_src is not None else None
            sources[path] = (base_blank, head_blank)
            if not is_introduced:
                context += 1
                continue
            findings, stats = analyse_blanked(base_blank, head_blank)
            for key in total_stats:
                total_stats[key] += stats[key]
            for f in findings:
                all_findings.append((path, f))
        all_findings.extend(
            analyse_cross_file_structs(sources, total_stats, carriers, introduced)
        )
        # F1b: every site the range ADDS, against the declaration at head,
        # changed or not. A site a pass above already reported is reported once.
        seen = {(p, f["kind"], f["name"], f["line"]) for p, f in all_findings}
        for path, f in analyse_added_sites(sources, head, carriers, introduced, known, cwd, added):
            key = (path, f["kind"], f["name"], f["line"])
            if key not in seen:
                seen.add(key)
                all_findings.append((path, f))
        sources = {}

    print(
        f"read {files_read} changed .rs file(s); "
        + (
            f"{carried} changed file(s) the destination already carries byte for byte are not "
            f"this push's on their own ({context} of them read only as cross-file context, "
            "where a pair no one destination commit holds is still judged); "
            if narrowed
            else ""
        )
        + f"{total_stats['definitions_in_play']} definition(s) whose shape this range changed; "
        f"skipped {total_stats['skipped_ambiguous']} ambiguous call site(s), "
        f"{total_stats['skipped_duplicate_name']} duplicated name(s), "
        f"{total_stats['skipped_foreign_import']} foreign-imported name(s), "
        f"{total_stats['skipped_bound_as_value']} changed fn name(s) the file also binds as a value; "
        f"{added['added']} added construction site(s) read against the declaration at the pushed tip"
    )

    if not all_findings:
        print(
            "PASS: every construction site of a shape this range changed still matches it, "
            "and every site it adds matches the declaration at the pushed tip."
        )
        return 0

    test_only = sum(1 for _, f in all_findings if f["cfg_test"])
    print()
    print(
        f"FAIL: {len(all_findings)} construction site(s) did not follow a shape this range changed, "
        "or were added against the declaration at the pushed tip"
    )
    print(f"      ({test_only} of them under #[cfg(test)], where no lib build can see them).")
    print()
    shown = 0
    for path, f in all_findings:
        if shown == 25:
            print(f"  ... and {len(all_findings) - shown} more")
            break
        tag = "cfg(test)" if f["cfg_test"] else "production"
        if f.get("added"):
            tag += ", added"
        where = f"line {f['decl_line']}"
        if f.get("decl_path") and f["decl_path"] != path:
            where = f"{display_path(f['decl_path'])}:{f['decl_line']}"
        if f["kind"] == "arity":
            print(
                f"  x {display_path(path)}:{f['line']}  [{tag}]  {f['name']}(..) takes "
                f"{f['expected']} argument(s) (declared {where}), {f['got']} supplied"
            )
        elif f["kind"] == "feature-gated":
            print(
                f"  x {display_path(path)}:{f['line']}  pub struct {f['name']}: pub field(s) "
                f"{', '.join(f['fields'])} exist only under a Cargo feature, which makes the "
                "feature non-additive (another crate's literal breaks when the graph turns it "
                "on). Declare the field in every feature set."
            )
        else:
            bits = []
            if f["missing"]:
                bits.append("missing " + ", ".join(f["missing"]))
            if f["unknown"]:
                bits.append("unknown " + ", ".join(f["unknown"]))
            print(
                f"  x {display_path(path)}:{f['line']}  [{tag}]  {f['name']} {{ .. }} "
                f"(declared {where}): " + "; ".join(bits)
            )
        shown += 1
    print()
    print("This lane compiles nothing — it reads the blobs in the range. A finding here")
    print("is a compile error `x.py build` and `x.py test tests/ui` CANNOT see, because a")
    print("#[cfg(test)] body is not in a lib target. Update the construction sites, or, if")
    print("this is a false reading, say so in the commit body and quarantine the row in")
    print("tests/trust-comprehensive/divergences.toml with an owner and an expiry.")
    return 1


# ------------------------------------------------------------------- selftest

SELFTEST_BEFORE = """
pub(crate) fn widen_me(taint: &mut Set, sid: Id) {
    let _ = (taint, sid);
}

pub(crate) struct Rec {
    pub a: u32,
    pub b: u32,
}

fn production() {
    widen_me(&mut s, id);
    let _ = Rec { a: 1, b: 2 };
}

#[cfg(test)]
mod tests {
    use super::*;
    fn helper() {
        widen_me(&mut s, id);
        let _ = Rec { a: 1, b: 2 };
    }
}
"""

SELFTEST_BROKEN = """
pub(crate) fn widen_me(taint: &mut Set, tys: &[Ty], sid: Id) {
    let _ = (taint, tys, sid);
}

pub(crate) struct Rec {
    pub a: u32,
    pub b: u32,
    pub c: u32,
}

fn production() {
    widen_me(&mut s, tys, id);
    let _ = Rec { a: 1, b: 2, c: 3 };
}

#[cfg(test)]
mod tests {
    use super::*;
    fn helper() {
        // the two sites the producer missed
        widen_me(&mut s, id);
        let _ = Rec { a: 1, b: 2 };
    }
}
"""

SELFTEST_REPAIRED = SELFTEST_BROKEN.replace(
    "        widen_me(&mut s, id);", "        widen_me(&mut s, tys, id);"
).replace("        let _ = Rec { a: 1, b: 2 };", "        let _ = Rec { a: 1, b: 2, c: 3 };")

SELFTEST_DOC_DECOY = """
pub(crate) fn widen_me(taint: &mut Set, tys: &[Ty], sid: Id) { let _ = (taint, tys, sid); }

/// The old spelling was `widen_me(&mut s, id)` and the string "widen_me(a)" is prose.
fn production() {
    widen_me(&mut s, tys, id);
}
"""

# Every decoy below is a shape that MADE this lane report a false finding during
# its own bring-up, on a tree the repo had recorded green. They are fixtures, not
# hypotheticals; deleting one re-opens a measured false refusal.
SELFTEST_RETURN_TYPE_DECOY = """
pub(crate) struct Rec { pub a: u32, pub b: u32, pub c: u32 }

/// `-> Rec {` is a return type in front of a body brace, and the body opens with
/// a PATH CALL whose `::` must not read as a field name. (8932acd798, lineage.rs:723)
fn make() -> Rec {
    Rec::assemble(1, 2, 3)
}
"""

SELFTEST_SHORTHAND_BLOCK_DECOY = """
pub(crate) struct Rec { pub a: u32, pub b: u32, pub c: u32 }

fn choose(flag: bool, x: u32, Rec: u32) -> u32 {
    if flag { x } else { Rec }
}
"""

SELFTEST_GENERIC_PARAM_DECOY = """
/// ONE parameter, two depth-1 commas. (30e0f71308, pair_enum_abi_supported)
fn pair_enum_abi_supported<'tcx>(arg: &ArgAbi<'tcx, Ty<'tcx>>) -> bool {
    let _ = arg;
    true
}

fn caller() {
    let _ = pair_enum_abi_supported(arg);
}
"""

SELFTEST_STRING_ARG_DECOY = """
fn usize_decl(index: usize, name: &str) -> LocalDecl {
    let _ = (index, name);
}

fn caller() {
    let _ = usize_decl(1, "bound");
    let _ = usize_decl(2, "counter");
}
"""

# A crate that declares `pub fn derive(..)` and also derives traits: every
# `#[derive(..)]` is attribute input, never a call of the function. Brand-new
# file, so the changed-declaration pass judges it (2026-10-01, trust-platform-derive).
SELFTEST_DERIVE_ATTRIBUTE_DECOY = """
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Limits { pub soft: u64 }

#[derive(Clone, Debug)]
pub enum Verdict { Refuted, Unknown }

pub fn derive(program: u32, limits: Limits, budget: usize) -> Verdict {
    let _ = (program, limits, budget);
    Verdict::Unknown
}

fn production() {
    let _ = derive(1, Limits { soft: 1 }, 10);
}
"""

# A variant that shares its name with a struct: the variant DECLARATION is not
# a literal of the struct. The struct's real literal must still be judged.
SELFTEST_VARIANT_NAME_DECOY = """
pub struct Event { pub symbol: u32, pub site: u32 }

pub enum ActionKey {
    Event { role: u8, at: u32 },
    Child { role: u8 },
}

fn production() -> Event {
    Event { symbol: 1, site: 2 }
}
"""

SELFTEST_CLOSURE_DECOY = """
pub(crate) fn taking(f: F, n: usize, m: usize) { let _ = (f, n, m); }

fn production() {
    taking(|a, b| a + b, 1, 2);
}
"""

# A VALUE of a changed free function's name shadows it where it is in scope, so
# a call there is a call of the value (bound_as_value). The two cb/track-b
# shapes the changed-signature pass refused on 2026-09-29, each a new or
# widened `fn` beside a same-named value, neither a compile error, plus a
# closure's own parameter list:
#   * PARAMETER (test_harness_exclusion.rs): `runner_closure_shape(..,
#     test_function_has_requires: impl FnOnce(DefId) -> bool)` calls its
#     parameter with one argument, while `fn test_function_has_requires(tcx,
#     test_function)` takes two;
#   * CLOSURE PARAMETER: `|has_requires: &dyn Fn(u32) -> bool| has_requires(7)`;
#   * LET (refutation_scope.rs): a `#[cfg(test)]` `let held = |func| ..` called
#     with one argument, beside `fn held(func, row)`.
# Each is (before, after: the fn widened, control: the value renamed and every
# call left as it is). In the control each call names the widened function
# itself, a real E0061 that must be flagged: the skip fires on the binding.
SELFTEST_FN_HAS_REQUIRES = "\nfn has_requires(def: u32) -> bool {\n    def > 0\n}\n"
SELFTEST_FN_HAS_REQUIRES_WIDE = "\nfn has_requires(tcx: u32, def: u32) -> bool {\n    def > tcx\n}\n"
SELFTEST_SHADOW_PARAM = (
    """
pub(super) fn runner_shape(shape: u32, has_requires: impl FnOnce(u32) -> bool) -> bool {
    has_requires(shape)
}
""",
    "has_requires: impl FnOnce",
    "pred: impl FnOnce",
)
SELFTEST_SHADOW_CLOSURE_PARAM = (
    """
fn apply() -> bool {
    let run = |has_requires: &dyn Fn(u32) -> bool| has_requires(7);
    run(&|d| d > 1)
}
""",
    "|has_requires: &dyn",
    "|pred: &dyn",
)
SELFTEST_SHADOW_LET_BEFORE = """
fn held(func: u32) -> bool {
    func > 0
}

#[cfg(test)]
mod tests {
    use super::*;
    fn screens() {
        let held = |func: u32| super::held(func);
        assert!(held(1));
        assert!(!held(0));
    }
}
"""
SELFTEST_SHADOW_LET_AFTER = SELFTEST_SHADOW_LET_BEFORE.replace(
    "fn held(func: u32) -> bool {", "fn held(func: u32, row: u32) -> bool {"
).replace("super::held(func)", "super::held(func, 0)")
SELFTEST_SHADOW_LET_CONTROL = SELFTEST_SHADOW_LET_AFTER.replace("let held = |func", "let probe = |func")


# The real call beside those shapes: the same widened `fn held`, whose stale
# `#[cfg(test)]` caller calls the FUNCTION, imported into the test module by a
# `use` rustfmt wrapped onto several lines. That import is not a value: read by
# line, `    held,` looked like one, and the skip swallowed every name
# 78a0bef5ff and ed21a2887f are refused on, the regressions this lane exists
# to catch.
SELFTEST_VALUE_REAL_BEFORE = """
pub(crate) fn held(func: u32) -> bool {
    func > 0
}

pub(crate) fn other(n: u32) -> u32 {
    n
}

fn production() -> bool {
    held(1)
}

#[cfg(test)]
mod tests {
    use super::{
        held,
        other,
    };
    fn screens() {
        assert!(held(1));
        let _ = other(2);
    }
}
"""
SELFTEST_VALUE_REAL_AFTER = SELFTEST_VALUE_REAL_BEFORE.replace(
    "pub(crate) fn held(func: u32) -> bool {", "pub(crate) fn held(func: u32, row: u32) -> bool {"
).replace("fn production() -> bool {\n    held(1)", "fn production() -> bool {\n    held(1, 2)")


def selftest_value_shadow(check, failures: list[str]) -> None:
    """The changed-signature pass skips a name the file binds as a value, as
    the added-site pass does, and still flags a real call of the function."""
    print("selftest: a VALUE named like a changed fn shadows it (bound_as_value, as the added-site pass reads it)")
    for label, (body, value, renamed) in (
        ("a fn PARAMETER", SELFTEST_SHADOW_PARAM),
        ("a CLOSURE PARAMETER", SELFTEST_SHADOW_CLOSURE_PARAM),
    ):
        before = body + SELFTEST_FN_HAS_REQUIRES
        after = body + SELFTEST_FN_HAS_REQUIRES_WIDE
        check(f"{label} named like a widened fn is what is called: not flagged", before, after, 0)
        check(
            f"control: {label} renamed, the same call now names the widened fn: CAUGHT",
            before, after.replace(value, renamed), 1, 0,
        )
    check(
        "a #[cfg(test)] `let held = |..|` beside a widened `fn held` is what is called: not flagged",
        SELFTEST_SHADOW_LET_BEFORE, SELFTEST_SHADOW_LET_AFTER, 0,
    )
    check(
        "control: the let renamed, the same #[cfg(test)] calls now name the widened fn: CAUGHT",
        SELFTEST_SHADOW_LET_BEFORE, SELFTEST_SHADOW_LET_CONTROL, 2, 2,
    )
    check(
        "a real stale call of the widened fn, imported by a rustfmt-wrapped `use super::{..}`, is CAUGHT",
        SELFTEST_VALUE_REAL_BEFORE, SELFTEST_VALUE_REAL_AFTER, 1, 1,
    )
    before = len(failures)
    for label, src, name, want in (
        ("a fn parameter", SELFTEST_SHADOW_PARAM[0], "has_requires", True),
        ("a closure parameter", SELFTEST_SHADOW_CLOSURE_PARAM[0], "has_requires", True),
        ("a let-bound closure", SELFTEST_SHADOW_LET_AFTER, "held", True),
        ("a wrapped `use super::{..}` import", SELFTEST_VALUE_REAL_AFTER, "held", False),
    ):
        if bound_as_value(blank_comments_and_strings(src), name) != want:
            failures.append(f"bound_as_value read {label} of `{name}` as {'an import' if want else 'a value'}")
    if len(failures) == before:
        print("  ok  bound_as_value: the three values read as values, the wrapped import as an import")


def selftest_impl_headers(failures: list[str]) -> None:
    # The actual push failure was an empty Error impl after a changed named
    # struct. Exact primary-site checks also prevent a broad `for` exemption.
    declaration = "struct Rec { a: u32, b: u32 }\n"
    cases = (
        ("qualified trait impl is not an empty literal", "impl std::error::Error for Rec {}", []),
        ("generic trait and function bound header", "impl<T: Fn(u32) -> u32> Trait<T> for Rec {}", []),
        ("unsafe impl header", "unsafe impl Trait for Rec {}", []),
        ("negative impl header", "impl !Trait for Rec {}", []),
        ("where-bound trait name is an impl body", "impl<T> Trait for Wrapper<T> where T: Rec {}", []),
        ("literal inside impl method still reports", "impl Trait for Rec { fn f() { let _ = Rec { a: 1 }; } }", ["Rec { a: 1 }"]),
        ("for iterator literal still reports", "fn f() { for _ in [Rec { a: 1 }] {} }", ["Rec { a: 1 }"]),
        ("for destructuring pattern still reports", "fn f() { for Rec { a: 1 } in xs {} }", ["Rec { a: 1 }"]),
        ("where-clause function body literal still reports", "fn f<T>() where T: Trait { let _ = Rec { a: 1 }; }", ["Rec { a: 1 }"]),
        ("const-generic header literal still reports", "impl Trait<{ let _ = Rec { a: 1 }; 0 }> for Rec {}", ["Rec { a: 1 }"]),
        ("complete literal after impl remains checked", "impl Trait for Rec {}\nfn f() { let _ = Rec { a: 1, b: 2 }; }", []),
    )
    for label, suffix, expected in cases:
        # Put each literal on its own line so exact line attribution cannot
        # confuse an impl header with the intended negative site.
        for token in expected:
            suffix = suffix.replace(token, "\n" + token + "\n")
        source = declaration + suffix
        findings, _stats = analyse_file(None, source)
        wanted = [{"kind": "fields", "name": "Rec", "missing": ["b"], "unknown": [],
                   "line": line_of(source, source.index(token))} for token in expected]
        got = [{key: row[key] for key in ("kind", "name", "missing", "unknown", "line")}
               for row in findings]
        if got != wanted:
            failures.append(f"{label}: expected exact sites {wanted!r}, got {got!r}")
        else:
            print(f"  ok  {label}: {len(got)} exact finding(s)")


class _Fixture:
    """A throwaway repository and a bare destination for the SUBJECT arms of
    --selftest. Which files a push is judged on is a property of `git diff`,
    replace refs and TRUST_PUSHED_REFS, so it is proved against real git
    objects, never a string the test invents. Every arm calls `run()` exactly
    as main() does, and maps a RuntimeError to exit 2 as main() does."""

    def __init__(self, root: str, name: str):
        self.repo = os.path.join(root, name)
        self.dest = os.path.join(root, name + "-dest.git")
        os.makedirs(self.repo)
        self.git("init", "-q")
        self.git("symbolic-ref", "HEAD", "refs/heads/main")
        subprocess.run(["git", "init", "-q", "--bare", self.dest], check=True, capture_output=True)

    def git(self, *args: str) -> str:
        proc = subprocess.run(["git", *args], cwd=self.repo, capture_output=True)
        if proc.returncode != 0:
            err = proc.stderr.decode("utf-8", "replace").strip()
            raise RuntimeError(f"selftest fixture: git {' '.join(args)}: {err}")
        return proc.stdout.decode("utf-8", "replace").strip()

    def write(self, path: str, text: str) -> None:
        full = os.path.join(self.repo, path)
        os.makedirs(os.path.dirname(full), exist_ok=True)
        with open(full, "w", encoding="utf-8") as fh:
            fh.write(text)

    def commit(self, message: str) -> str:
        self.git("add", "-A")
        self.git("commit", "-q", "--allow-empty", "-m", message)
        return self.git("rev-parse", "HEAD")

    def publish(self, sha: str, ref: str) -> None:
        # --no-verify: a fixture push must never run a hook of its own.
        self.git("push", "-q", "--no-verify", "-f", self.dest, f"{sha}:{ref}")

    def lane(self, pushed: str, remote: str | None) -> tuple[int, str]:
        import contextlib
        import io

        args = argparse.Namespace(range=None, push_context=True, remote=remote, repo=self.repo)
        os.environ["TRUST_PUSHED_REFS"] = pushed
        buf = io.StringIO()
        try:
            with contextlib.redirect_stdout(buf), contextlib.redirect_stderr(buf):
                try:
                    rc = run(args)
                except RuntimeError as exc:  # main()'s own mapping
                    print(f"cfg-test-skew: {exc}")
                    rc = 2
        finally:
            del os.environ["TRUST_PUSHED_REFS"]
        return rc, buf.getvalue()


SUBJECT_WIDEN_BEFORE = "pub fn widen_me(a: u32) {}\nfn p() { widen_me(1); }\n"
# Line 6 is the #[cfg(test)] caller the widening left behind.
SUBJECT_WIDEN_STALE_TEST = (
    "pub fn widen_me(a: u32, b: u32) {}\nfn p() { widen_me(1, 2); }\n"
    "#[cfg(test)]\nmod t {\n    use super::*;\n    fn h() { widen_me(1); }\n}\n"
)
SUBJECT_WIDEN_CLEAN = "pub fn widen_me(a: u32, b: u32) {}\nfn p() { widen_me(1, 2); }\n"


def selftest_push_subject(failures: list[str]) -> None:
    """Which files a push is judged on. Each arm is a confirmed defect of the
    subject reader (docs/issues/2026-09-28-cfg-test-caller-skew-push-subject.md,
    F2, F3, F4), with the exit the lane must give; the lane before this change
    gave a different one on every arm marked `was`."""
    import shutil
    import tempfile

    def expect(label: str, got: tuple[int, str], rc: int, *needles: str) -> None:
        code, out = got
        missing = [n for n in needles if n not in out]
        if code != rc or missing:
            failures.append(
                f"{label}: expected exit {rc} naming {list(needles)!r}, got exit {code}:\n"
                + "\n".join("      " + line for line in out.splitlines())
            )
        else:
            print(f"  ok  {label}: exit {code}")

    zero = "0" * 40
    saved = dict(os.environ)
    root = tempfile.mkdtemp(prefix="cfg-skew-selftest-")
    try:
        # Hermetic git: no inherited repository, hook, replace or identity
        # setting may decide an arm. HOME is the fixture root, so no global
        # config is read either.
        for key in list(os.environ):
            if key.startswith("GIT_") or key.startswith("TRUST_PUSH"):
                del os.environ[key]
        os.environ.update(
            {
                "HOME": root,
                "XDG_CONFIG_HOME": root,
                "GIT_CONFIG_NOSYSTEM": "1",
                "GIT_AUTHOR_NAME": "selftest",
                "GIT_AUTHOR_EMAIL": "selftest@example.invalid",
                "GIT_COMMITTER_NAME": "selftest",
                "GIT_COMMITTER_EMAIL": "selftest@example.invalid",
            }
        )
        print("selftest: the push subject, against throwaway git repositories")

        # F2, QUOTED PATHS. Without -z, `git diff --name-only` C-quotes these
        # names, a quoted name does not start with `crates/`, and the skew
        # passed (was: exit 0). The newline name also proves blob_ids asks a
        # name the line-based batch protocol cannot carry on its own.
        for tag, name in (
            ("non-ASCII", "crates/k/src/été.rs"),
            ("double-quote", 'crates/k/src/say"hi".rs'),
            ("newline", "crates/k/src/two\nlines.rs"),
        ):
            fx = _Fixture(root, "quoted-" + tag)
            fx.write(name, SUBJECT_WIDEN_BEFORE)
            base = fx.commit("base")
            fx.publish(base, "refs/heads/main")
            fx.write(name, SUBJECT_WIDEN_STALE_TEST)
            head = fx.commit("widen")
            for how, remote in (("with a destination", fx.dest), ("no destination", None)):
                expect(
                    f"F2: a skew in a crates/ file whose name git C-quotes ({tag}) is REFUSED ({how})",
                    fx.lane(f"refs/heads/main {head} refs/heads/main {base}", remote), 1,
                    ":6", "widen_me(..) takes 2",
                )

        # F2, A NAME THAT IS NOT UTF-8, made through index plumbing because
        # APFS cannot hold it (a Linux clone can). Adding or deleting it makes
        # blob_at ask `git show` for it at the rev that lacks it; git's error
        # echoes the raw bytes, and a strict decode of that stderr crashed the
        # run in a traceback (exit 1) where the lane before -z never read the
        # name (exit 0). Its content is clean, so the add and the delete pass;
        # a skew under the same name is still refused and still printed.
        fx = _Fixture(root, "non-utf8")
        odd = os.fsdecode(b"crates/k/src/\xff.rs")
        fx.write("crates/k/src/lib.rs", "pub fn keep() {}\n")
        base = fx.commit("base")

        def stage(text: str) -> str:
            proc = subprocess.run(
                ["git", "hash-object", "-w", "--stdin"], input=text.encode("utf-8"),
                cwd=fx.repo, capture_output=True, check=True,
            )
            fx.git("update-index", "--add", "--cacheinfo",
                   f"100644,{proc.stdout.decode('ascii').strip()},{odd}")
            fx.git("commit", "-q", "-m", "plumbing")
            return fx.git("rev-parse", "HEAD")

        added = stage(SUBJECT_WIDEN_BEFORE)
        skewed = stage(SUBJECT_WIDEN_STALE_TEST)
        fx.git("rm", "-q", "--cached", odd)
        fx.git("commit", "-q", "-m", "delete it")
        deleted = fx.git("rev-parse", "HEAD")
        for step, old, new, rc, needles in (
            ("added clean", base, added, 0, ("PASS",)),
            ("changed to a skew", added, skewed, 1, (":6", "widen_me(..) takes 2")),
            ("deleted", skewed, deleted, 0, ("PASS",)),
        ):
            fx.publish(old, "refs/heads/main")
            for how, remote in (("with a destination", fx.dest), ("no destination", None)):
                expect(
                    f"F2: a crates/ file whose name is not UTF-8, {step} ({how})",
                    fx.lane(f"refs/heads/main {new} refs/heads/main {old}", remote), rc, *needles,
                )

        # F4, REPLACE REFS. git push sends the real objects; a local
        # refs/replace over the pushed commit, or over the pushed blob, made
        # the lane judge a clean stand-in (was: exit 0). The commit arm needs
        # the diff reader to ignore it; the blob arm needs the blob reader to.
        fx = _Fixture(root, "replace")
        fx.write("crates/k/src/lib.rs", SUBJECT_WIDEN_BEFORE)
        base = fx.commit("base")
        fx.publish(base, "refs/heads/main")
        fx.write("crates/k/src/lib.rs", SUBJECT_WIDEN_CLEAN)
        clean = fx.commit("clean")
        clean_blob = fx.git("rev-parse", f"{clean}:crates/k/src/lib.rs")
        fx.git("reset", "-q", "--hard", base)
        fx.write("crates/k/src/lib.rs", SUBJECT_WIDEN_STALE_TEST)
        bad = fx.commit("skewed")
        bad_blob = fx.git("rev-parse", f"{bad}:crates/k/src/lib.rs")
        push = f"refs/heads/main {bad} refs/heads/main {base}"
        for kind, (old, new) in (("commit", (bad, clean)), ("blob", (bad_blob, clean_blob))):
            fx.git("replace", old, new)
            for how, remote in (("with a destination", fx.dest), ("no destination", None)):
                expect(
                    f"F4: a local replace ref over the pushed {kind} does not hide its skew ({how})",
                    fx.lane(push, remote), 1, "crates/k/src/lib.rs:6", "widen_me(..) takes 2",
                )
            fx.git("replace", "-d", old)

        # F3, DELETIONS. HEAD carries unpushed skew over origin/main; the push
        # deletes a branch and sends none of it (was: the fall-through to
        # origin/main..HEAD refused it, exit 1).
        fx = _Fixture(root, "deletion")
        fx.write("crates/k/src/lib.rs", SUBJECT_WIDEN_BEFORE)
        base = fx.commit("base")
        fx.publish(base, "refs/heads/main")
        fx.publish(base, "refs/heads/stale-topic")
        fx.git("update-ref", "refs/remotes/origin/main", base)
        fx.write("crates/k/src/lib.rs", SUBJECT_WIDEN_STALE_TEST)
        local = fx.commit("unpushed local work with a skew")
        deletion = f"(delete) {zero} refs/heads/stale-topic {base}"
        for how, remote in (("with a destination", fx.dest), ("no destination", None)):
            expect(
                f"F3: a deletion-only push has no subject and is SKIPPED, never judged on HEAD ({how})",
                fx.lane(deletion, remote), 0, "SKIPPED: ", "nothing pushed to read",
            )
            expect(
                f"F3: two deletions are still no subject ({how})",
                fx.lane(deletion + "\n" + deletion.replace("stale-topic", "other"), remote), 0,
                "SKIPPED: ",
            )
        # A line that is not what git hands a pre-push hook was skipped, and a
        # value whose every line was skipped widened to HEAD, so these arms were
        # judged on HEAD's skew (was: exit 1; the non-object-name line was
        # already exit 2, from the git child that could not read it).
        for label, pushed in (
            ("a three-field line", "refs/heads/x deadbeef refs/heads/x"),
            ("a four-field line whose shas are not object names", "not a ref line"),
            ("a five-field line", f"refs/heads/x {local} refs/heads/x {base} extra"),
            ("a malformed line beside a deletion", deletion + "\nrefs/heads/x deadbeef refs/heads/x"),
            ("a malformed line beside a real update",
             f"refs/heads/main {local} refs/heads/main {base}\nrefs/heads/x deadbeef refs/heads/x"),
        ):
            for how, remote in (("with a destination", fx.dest), ("no destination", None)):
                expect(
                    f"F3: {label} in TRUST_PUSHED_REFS refuses (exit 2), never widens ({how})",
                    fx.lane(pushed, remote), 2, "could NOT READ TRUST_PUSHED_REFS",
                )
        # Controls: the deletion beside a real update still judges the update,
        # and a BLANK value (no push in flight) still reads origin/main..HEAD.
        expect(
            "F3 control: a deletion beside an update still judges the update",
            fx.lane(deletion + f"\nrefs/heads/main {local} refs/heads/main {base}", fx.dest), 1,
            "crates/k/src/lib.rs:6",
        )
        expect(
            "F3 control: a blank TRUST_PUSHED_REFS is no push, and reads origin/main..HEAD",
            fx.lane(" \n", fx.dest), 1, "SUBJECT: origin/main..HEAD", "crates/k/src/lib.rs:6",
        )

        # F1, A PAIR NO DESTINATION COMMIT HOLDS. Branch A widens Rec and
        # updates the literal it knows; branch B, from the same base, adds a
        # #[cfg(test)] literal of the OLD Rec. Each compiles, both are
        # published, and main merges both: every file's head blob is on the
        # destination, each in a different commit, and the union is E0063 at
        # other.rs:7. Judged file by file it read 0 files (was: exit 0).
        fx = _Fixture(root, "union")
        fx.write("crates/k/src/lib.rs", "pub struct Rec {\n    pub a: u32,\n}\n")
        fx.write("crates/k/src/lits.rs", "fn p() { let _ = Rec { a: 1 }; }\n")
        fx.write("crates/k/src/other.rs", "fn q() {}\n")
        base = fx.commit("base")
        fx.publish(base, "refs/heads/main")
        fx.git("checkout", "-q", "-b", "A")
        fx.write("crates/k/src/lib.rs", "pub struct Rec {\n    pub a: u32,\n    pub b: u32,\n}\n")
        fx.write("crates/k/src/lits.rs", "fn p() { let _ = Rec { a: 1, b: 2 }; }\n")
        fx.publish(fx.commit("A: widen Rec"), "refs/heads/A")
        fx.git("checkout", "-q", "-b", "B", base)
        fx.write(
            "crates/k/src/other.rs",
            "fn q() {}\n\n#[cfg(test)]\nmod t {\n    use super::*;\n    fn h() {\n"
            "        let _ = Rec { a: 2 };\n    }\n}\n",
        )
        fx.publish(fx.commit("B: a test helper"), "refs/heads/B")
        fx.git("checkout", "-q", "main")
        fx.git("merge", "-q", "--no-edit", "A")
        fx.git("merge", "-q", "--no-edit", "B")
        merged = fx.git("rev-parse", "HEAD")
        update = f"refs/heads/main {merged} refs/heads/main {base}"
        fresh = f"refs/heads/union {merged} refs/heads/union {zero}"
        for how, push in (("an update of main", update), ("a NEW ref", fresh)):
            expect(
                f"F1: a merge of two published branches whose PAIR no destination commit holds is REFUSED ({how})",
                fx.lane(push, fx.dest), 1, "crates/k/src/other.rs:7", "Rec { .. }", "missing b",
            )
        expect(
            "F1 control: the same merge with no destination is refused, as it always was",
            fx.lane(update, None), 1, "crates/k/src/other.rs:7",
        )
        # Control: one destination commit already holds exactly that pairing
        # (a commit with the merged tree), so the pair is published, and main
        # would carry it byte for byte: set aside, as before.
        together = fx.git("commit-tree", f"{merged}^{{tree}}", "-p", base, "-m", "A and B")
        fx.publish(together, "refs/heads/AB")
        expect(
            "F1 control: the same pair published TOGETHER in one destination commit PASSES",
            fx.lane(update, fx.dest), 0, "PASS",
        )

        selftest_added_sites(root, expect)
    finally:
        os.environ.clear()
        os.environ.update(saved)
        shutil.rmtree(root, ignore_errors=True)


ADDED_LIB_BASE = (
    "pub struct Rec {\n    pub a: u32,\n}\n\npub fn f(a: u32) -> u32 {\n    a\n}\n\n"
    "fn p() {\n    let _ = Rec { a: 1 };\n    let _ = f(1);\n}\n"
    + "".join(f"fn filler_{i}() {{}}\n" for i in range(6))
)
ADDED_LIB_WIDE = (
    "pub struct Rec {\n    pub a: u32,\n    pub b: u32,\n}\n\npub fn f(a: u32, b: u32) -> u32 {\n    a + b\n}\n\n"
    "fn p() {\n    let _ = Rec { a: 1, b: 2 };\n    let _ = f(1, 2);\n}\n"
    + "".join(f"fn filler_{i}() {{}}\n" for i in range(6))
)


def added_test_mod(*sites: str) -> str:
    return "\n#[cfg(test)]\nmod t {\n    use super::*;\n    fn h() {\n" + "".join(
        f"        {s}\n" for s in sites
    ) + "    }\n}\n"


def selftest_added_sites(root: str, expect) -> None:
    """F1b: a push that changes NO declaration but ADDS a site that disagrees
    with the declaration at its tip. Branch A widens `Rec` and `f` and lands on
    main; branch B, forked before A, adds a `#[cfg(test)]` `Rec { a: 2 }` in
    another file and a `#[cfg(test)]` `f(2)` beside `f`. Each branch compiles;
    their union is E0063 and E0061. Every RED arm here was exit 0 on the lane
    before analyse_added_sites (the `was` of each arm), because base..head
    changes no declaration."""
    zero = "0" * 40
    other_site = "crates/k/src/other.rs:7"
    lib_site = f"crates/k/src/lib.rs:{(ADDED_LIB_WIDE + added_test_mod('')).count(chr(10)) - 2}"

    fx = _Fixture(root, "added")
    fx.write("crates/k/src/lib.rs", ADDED_LIB_BASE)
    fx.write("crates/k/src/other.rs", "fn q() {}\n")
    base = fx.commit("base")
    fx.git("checkout", "-q", "-b", "A")
    fx.write("crates/k/src/lib.rs", ADDED_LIB_WIDE)
    a = fx.commit("A: widen Rec and f, update every site it knows")
    fx.git("checkout", "-q", "-b", "B", base)
    fx.write("crates/k/src/other.rs", "fn q() {}\n" + added_test_mod("let _ = Rec { a: 2 };"))
    fx.write("crates/k/src/lib.rs", ADDED_LIB_BASE + added_test_mod("let _ = f(2);"))
    b = fx.commit("B: two test sites of the old shapes")
    fx.git("checkout", "-q", "main")
    fx.git("reset", "-q", "--hard", a)
    fx.git("merge", "-q", "--no-edit", "B")
    merged = fx.git("rev-parse", "HEAD")
    fx.git("checkout", "-q", "-b", "rebased", a)
    fx.write("crates/k/src/other.rs", "fn q() {}\n" + added_test_mod("let _ = Rec { a: 2 };"))
    fx.write("crates/k/src/lib.rs", ADDED_LIB_WIDE + added_test_mod("let _ = f(2);"))
    rebased = fx.commit("B rebased onto A")
    fx.publish(a, "refs/heads/main")
    needles = (other_site, "Rec { .. }", "missing b", lib_site, "f(..) takes 2", "added")
    for how, push, remote in (
        ("an update of main merging B", f"refs/heads/main {merged} refs/heads/main {a}", fx.dest),
        ("the same update, no destination", f"refs/heads/main {merged} refs/heads/main {a}", None),
        ("a NEW ref of the merge", f"refs/heads/topic {merged} refs/heads/topic {zero}", fx.dest),
        ("B rebased onto main", f"refs/heads/main {rebased} refs/heads/main {a}", fx.dest),
    ):
        expect(
            f"F1b: sites the push ADDS against declarations it does not change are REFUSED ({how}; was: exit 0)",
            fx.lane(push, remote), 1, *needles,
        )
    # B published on its own: the destination carries other.rs (at B) and
    # lib.rs's declaration (at main) byte for byte, but no ONE commit holds
    # the pair; B's lib.rs is not at B either, as the merge rewrote it.
    fx.publish(b, "refs/heads/B")
    expect(
        "F1b: the same merge with B published is REFUSED: no one destination commit holds the pair (was: exit 0)",
        fx.lane(f"refs/heads/main {merged} refs/heads/main {a}", fx.dest), 1, other_site, lib_site,
    )
    # Control: that exact merged tree already published in ONE commit.
    together = fx.git("commit-tree", f"{merged}^{{tree}}", "-p", a, "-m", "together")
    fx.publish(together, "refs/heads/together")
    expect(
        "F1b control: the merged tree published in ONE destination commit PASSES",
        fx.lane(f"refs/heads/main {merged} refs/heads/main {a}", fx.dest), 0, "PASS",
    )

    # The mirror: a lane branch widened Rec long ago (published at its old
    # tip); main adds an old-shape literal, which compiles on main; the lane
    # merges main. The declaring file is not in old..new at all.
    fx = _Fixture(root, "added-mirror")
    fx.write("crates/k/src/lib.rs", ADDED_LIB_BASE)
    fx.write("crates/k/src/other.rs", "fn q() {}\n")
    base = fx.commit("base")
    fx.git("checkout", "-q", "-b", "lane")
    fx.write("crates/k/src/lib.rs", ADDED_LIB_WIDE)
    old = fx.commit("lane: widen")
    fx.git("checkout", "-q", "main")
    fx.write("crates/k/src/other.rs", "fn q() {}\n" + added_test_mod("let _ = Rec { a: 2 };"))
    on_main = fx.commit("main: an old-shape literal")
    fx.git("checkout", "-q", "lane")
    fx.git("merge", "-q", "--no-edit", "main")
    new = fx.git("rev-parse", "HEAD")
    fx.publish(on_main, "refs/heads/main")
    fx.publish(old, "refs/heads/lane")
    expect(
        "F1b: a lane that widened Rec merges main's old-shape literal: REFUSED (was: exit 0)",
        fx.lane(f"refs/heads/lane {new} refs/heads/lane {old}", fx.dest), 1,
        other_site, "declared crates/k/src/lib.rs:1", "missing b",
    )

    # Controls on the widened tree: a site that MATCHES the tip passes, and a
    # stale site the destination already carries is not this push's, however
    # the push touches its file or the declaring file.
    fx = _Fixture(root, "added-controls")
    fx.write("crates/k/src/lib.rs", ADDED_LIB_WIDE + added_test_mod("let _ = f(2);"))
    fx.write("crates/k/src/other.rs", "fn q() {}\n" + added_test_mod("let _ = Rec { a: 2 };"))
    stale = fx.commit("main already carries two stale test sites")
    fx.publish(stale, "refs/heads/main")
    fx.write("crates/k/src/other.rs", "fn q0() {}\nfn q() {}\n" + added_test_mod("let _ = Rec { a: 2 };"))
    fx.write("crates/k/src/lib.rs", "fn z() {}\n" + ADDED_LIB_WIDE + added_test_mod("let _ = f(2);"))
    touched = fx.commit("edit both files away from the stale sites")
    for how, remote in (("with a destination", fx.dest), ("no destination", None)):
        expect(
            f"F1b control: a stale site the destination already carries is not the push's ({how})",
            fx.lane(f"refs/heads/main {touched} refs/heads/main {stale}", remote), 0, "PASS",
        )
    fx.write("crates/k/src/other.rs", "fn q0() {}\nfn q() {}\n"
             + added_test_mod("let _ = Rec { a: 2 };", "let _ = Rec { a: 3, b: 4 };"))
    fx.write("crates/k/src/lib.rs", "fn z() {}\n" + ADDED_LIB_WIDE
             + added_test_mod("let _ = f(2);", "let _ = f(3, 4);"))
    matching = fx.commit("add sites that match the tip")
    for how, remote in (("with a destination", fx.dest), ("no destination", None)):
        expect(
            f"F1b control: added sites that MATCH the declaration at the tip pass ({how})",
            fx.lane(f"refs/heads/main {matching} refs/heads/main {stale}", remote), 0, "PASS",
        )
    fx.write("crates/k/src/other.rs", "fn q0() {}\nfn q() {}\n"
             + added_test_mod("let _ = Rec { a: 2 };", "let _ = Rec { a: 2 };"))
    second = fx.commit("a SECOND copy of the stale literal")
    expect(
        "F1b: a second copy of a stale literal the destination carries is added, and REFUSED",
        fx.lane(f"refs/heads/main {second} refs/heads/main {stale}", fx.dest), 1,
        "crates/k/src/other.rs:9", "missing b",
    )

    # Decoys, each a false finding the added-site pass made on real history
    # before its skips (the module docstring): a closure that shadows a
    # same-named fn (69974d60f9: `let read_u32 = |at| ..` beside
    # `fn read_u32(bytes, offset)`), and an enum VARIANT declaration that
    # shares a struct's name (0c3e837149: `CalleeOwner::TraitImpl { .. }`).
    fx = _Fixture(root, "added-decoys")
    helper = "    fn read_u32(bytes: &[u8], offset: usize) -> u32 { u32::from(bytes[offset]) }\n"
    fx.write("crates/k/src/lib.rs", ADDED_LIB_WIDE)
    fx.write("crates/k/src/other.rs", "fn q() {}\n\n#[cfg(test)]\nmod t {\n    use super::*;\n" + helper + "}\n")
    start = fx.commit("the widened tree, with a test helper read_u32")
    fx.publish(start, "refs/heads/main")
    fx.write("crates/k/src/other.rs", (
        "fn q() {}\n\nfn scan(object: &[u8]) -> Option<u32> {\n"
        "    let read_u32 = |at: usize| object.get(at).map(|b| u32::from(*b));\n"
        "    read_u32(4)\n}\n\n#[cfg(test)]\nmod t {\n    use super::*;\n" + helper + "}\n"
        "\npub enum Owner {\n    Rec { trait_name: u32 },\n    Other,\n}\n"
    ))
    decoys = fx.commit("a shadowing closure and a same-named enum variant")
    for how, remote in (("with a destination", fx.dest), ("no destination", None)):
        expect(
            f"F1b decoys: a closure shadowing a same-named fn, and an enum variant named like a struct, PASS ({how})",
            fx.lane(f"refs/heads/main {decoys} refs/heads/main {start}", remote), 0, "PASS",
        )
    # ...and neither skip reaches a real added site beside them.
    fx.write("crates/k/src/other.rs", (
        "fn q() {}\n\n#[cfg(test)]\nmod t {\n    use super::*;\n" + helper
        + "    fn h() {\n        let _ = read_u32(&[1]);\n        let _ = Rec { a: 2 };\n    }\n}\n"
        "\npub enum Owner {\n    Rec { trait_name: u32 },\n    Other,\n}\n"
    ))
    real = fx.commit("a real stale call and a real stale literal beside the enum")
    expect(
        "F1b: beside the decoys' shapes, a real stale call and literal the push adds are REFUSED",
        fx.lane(f"refs/heads/main {real} refs/heads/main {start}", fx.dest), 1,
        "crates/k/src/other.rs:8", "read_u32(..) takes 2", "crates/k/src/other.rs:9", "missing b",
    )

    # Macro and attribute input, and a wrapped foreign import: four shapes
    # the added-site pass refused on pushes made from 84a2e55537 that main's
    # lane passed (review of 2026-09-28; each reproduced on the real tree):
    # `#[derive(Debug)]` in a file declaring `fn derive(corpus, kind)`
    # (crates/trust-js-differential/src/slice.rs), a call of a fn "declared"
    # as `fn with_x(Guard, CONST);` inside a macro invocation
    # (rustc_middle/src/ty/print/pretty.rs), a rustfmt-wrapped
    # `use ext::{\n    Rec,\n};` (rustc_mir_build/src/thir/pattern/mod.rs),
    # and `declare_lint!`'s `@future_incompatible = Info { .. }`, which the
    # macro completes (rustc_lint_defs/src/builtin.rs).
    fx = _Fixture(root, "added-macro-input")
    lib = ADDED_LIB_WIDE + (
        "\npub fn derive(corpus: u32, kind: u32) -> u32 {\n    corpus + kind\n}\n"
        "\nmacro_rules! define_helper {\n    ($(fn $name:ident($guard:ident, $flag:ident);)+) => {\n"
        "        $(pub fn $name() -> bool { true })+\n    };\n}\n"
        "\ndefine_helper!(\n    fn with_trimmed(TrimGuard, TRIM);\n);\n"
        "\nmacro_rules! declare_lint {\n    ($name:ident, @future_incompatible = Rec { $($f:ident: $v:expr),* $(,)? };) => {\n"
        "        pub static $name: Rec = Rec { $($f: $v,)* b: 0 };\n    };\n}\n"
    )
    fx.write("crates/k/src/lib.rs", lib)
    fx.write("crates/k/src/other.rs", "fn q() {}\n")
    fx.write("crates/k/src/lints.rs", "use crate::*;\n")
    start = fx.commit("the widened tree, with a helper-defining macro and a lint macro")
    fx.publish(start, "refs/heads/main")
    fx.write("crates/k/src/lib.rs", lib + (
        "\n#[derive(Debug)]\npub struct Probe {\n    pub n: u32,\n}\n"
        "\npub fn trimmed() -> bool {\n    with_trimmed()\n}\n"
    ))
    fx.write("crates/k/src/other.rs", (
        "use ext::{\n    Other,\n    Rec,\n};\n\nfn q() {}\n\n#[cfg(test)]\nmod t {\n    use super::*;\n"
        "    fn h() {\n        let _ = Rec { z: 1 };\n    }\n}\n"
    ))
    fx.write("crates/k/src/lints.rs", (
        "use crate::*;\n\ndeclare_lint! {\n    PROBE,\n    @future_incompatible = Rec {\n        a: 1,\n    };\n}\n"
    ))
    inputs = fx.commit("an attribute, a macro-declared fn, a wrapped foreign use, a lint arm")
    for how, remote in (("with a destination", fx.dest), ("no destination", None)):
        expect(
            "F1b: attribute input, macro input spelled as a fn, a rustfmt-wrapped foreign `use` "
            f"and a macro's `@key = Lit {{..}}` arm PASS ({how}; was: exit 1)",
            fx.lane(f"refs/heads/main {inputs} refs/heads/main {start}", remote), 0, "PASS",
        )
    # ...and none of those skips reaches a real added site beside them: a bare
    # `derive(1)` outside the attribute, a crate-local literal outside the lint
    # arm, in a file whose wrapped `use` imports only other names.
    fx.write("crates/k/src/lib.rs", lib + (
        "\n#[derive(Debug)]\npub struct Probe {\n    pub n: u32,\n}\n"
        "\n#[cfg(test)]\nfn probe() -> u32 {\n    derive(1)\n}\n"
    ))
    fx.write("crates/k/src/lints.rs", (
        "use crate::Rec;\nuse ext::{\n    Other,\n};\n\ndeclare_lint! {\n    PROBE,\n    @future_incompatible = Rec {\n        a: 1,\n    };\n}\n"
        "\n#[cfg(test)]\nfn probe() -> Rec {\n    Rec { a: 1 }\n}\n"
    ))
    fx.write("crates/k/src/other.rs", "fn q() {}\n")
    real = fx.commit("a real stale call and literal beside the attribute, the lint arm and a foreign use")
    lib_probe = (lib + "\n#[derive(Debug)]\npub struct Probe {\n    pub n: u32,\n}\n\n#[cfg(test)]\n").count("\n") + 2
    expect(
        "F1b: beside those shapes, a real stale call and literal the push adds are REFUSED",
        fx.lane(f"refs/heads/main {real} refs/heads/main {start}", fx.dest), 1,
        f"crates/k/src/lib.rs:{lib_probe}", "derive(..) takes 2", "crates/k/src/lints.rs:15", "missing b",
    )


def selftest_cross_file_variant(failures: list[str]) -> None:
    """The cross-file struct pass: a variant declared in one file of a crate is
    not a literal of a changed struct declared in another (2026-10-01:
    `ActionKey::Event { .. }` in explore.rs beside `struct Event` in program.rs).
    A stale literal in the second file must still be caught."""
    decl = "pub struct Event { pub symbol: u32, pub site: u32 }\n"
    variant = "pub enum ActionKey {\n    Event { role: u8, at: u32 },\n}\n"
    stale = "fn production() -> crate::program::Event {\n    Event { symbol: 1 }\n}\n"
    for label, other, want in (
        ("a variant in another file of the crate is not a literal", variant, 0),
        ("a stale literal in another file of the crate is still caught", stale, 1),
    ):
        sources = {
            "crates/demo/src/program.rs": (None, blank_comments_and_strings(decl)),
            "crates/demo/src/explore.rs": (None, blank_comments_and_strings(other)),
        }
        stats = {
            "skipped_ambiguous": 0,
            "skipped_duplicate_name": 0,
            "skipped_foreign_import": 0,
            "skipped_bound_as_value": 0,
            "definitions_in_play": 0,
        }
        got = len(analyse_cross_file_structs(sources, stats))
        if got != want:
            failures.append(f"{label}: expected {want} finding(s), got {got}")
        else:
            print(f"  ok  {label}: {got} finding(s)")


def selftest_macro_declared_struct(failures: list[str]) -> None:
    """A struct spelled inside the input of a macro the same file defines is not
    a declaration the lane reads (2026-10-10, rustc_session's
    `top_level_options!`): the macro may add fields, so a literal naming one is
    no finding. The same literal against a plain declaration, or against a
    struct passed through an imported macro, is still refused."""
    in_macro = (
        "macro_rules! opts {\n    (pub struct $n:ident { $($f:ident: $t:ty,)* }) => {\n"
        "        pub struct $n { $(pub $f: $t,)* pub extra: u32 }\n    };\n}\n"
        "opts! {\n    pub struct Opts {\n        a: u32,\n    }\n}\n"
    )
    plain = "pub struct Opts {\n    pub a: u32,\n}\n"
    imported = "cfg_if::cfg_if! {\n    if #[cfg(unix)] {\n        pub struct Opts {\n            pub a: u32,\n        }\n    }\n}\n"
    site = "fn build() -> crate::opts::Opts {\n    Opts { a: 1, extra: 2 }\n}\n"
    for label, decl, want in (
        ("a struct declared as a file-local macro's input is not judged", in_macro, 0),
        ("the same literal against a plain declaration is still refused", plain, 1),
        ("a struct passed through an imported macro is still judged", imported, 1),
    ):
        sources = {
            "crates/demo/src/opts.rs": (None, blank_comments_and_strings(decl)),
            "crates/demo/src/config.rs": (None, blank_comments_and_strings(site)),
        }
        stats = {
            "skipped_ambiguous": 0,
            "skipped_duplicate_name": 0,
            "skipped_foreign_import": 0,
            "skipped_bound_as_value": 0,
            "definitions_in_play": 0,
        }
        got = len(analyse_cross_file_structs(sources, stats))
        if got != want:
            failures.append(f"{label}: expected {want} finding(s), got {got}")
        else:
            print(f"  ok  {label}: {got} finding(s)")


SELFTEST_CONFIG_BEFORE = """
pub struct Config {
    pub depth: u32,
    pub(crate) internal: bool,
}
struct Private {
    pub a: u32,
}
"""

# The MirRouterConfig shape (2026-09-30): a public field that exists only under a
# Cargo feature, added to a public struct.
SELFTEST_CONFIG_GATED = SELFTEST_CONFIG_BEFORE.replace(
    "    pub(crate) internal: bool,\n}",
    "    pub(crate) internal: bool,\n    /// doc\n    #[cfg(feature = \"backend\")]\n    pub use_backend: bool,\n}",
)
# Not findings: a crate-private gated field, a gated field of a private struct, a
# gated field that was already gated before this push.
SELFTEST_CONFIG_DECOYS = SELFTEST_CONFIG_BEFORE.replace(
    "    pub(crate) internal: bool,\n}",
    "    pub(crate) internal: bool,\n    #[cfg(feature = \"backend\")]\n    pub(crate) hidden: bool,\n}",
).replace("    pub a: u32,\n}", "    pub a: u32,\n    #[cfg(feature = \"x\")]\n    pub b: u32,\n}")


def selftest_feature_gated(check) -> None:
    print("selftest: a public field gated on a Cargo feature (non-additive feature)")
    check("adding a feature-gated pub field to a pub struct is CAUGHT",
          SELFTEST_CONFIG_BEFORE, SELFTEST_CONFIG_GATED, 1, 0)
    check("declaring the field in every feature set clears it", SELFTEST_CONFIG_BEFORE,
          SELFTEST_CONFIG_GATED.replace('    #[cfg(feature = "backend")]\n', ""), 0)
    check("a crate-private field or a private struct is not judged",
          SELFTEST_CONFIG_BEFORE, SELFTEST_CONFIG_DECOYS, 0)
    check("a field already gated before this push is not this push's",
          SELFTEST_CONFIG_GATED, SELFTEST_CONFIG_GATED.replace("depth: u32", "depth: u64"), 0)


def selftest() -> int:
    failures = []

    def check(label, base, head, want_findings, want_cfg_test=None):
        findings, stats = analyse_file(base, head)
        got = len(findings)
        if got != want_findings:
            failures.append(
                f"{label}: expected {want_findings} finding(s), got {got}: "
                + "; ".join(f"{f['kind']} @{f['line']}" for f in findings)
            )
            return
        if want_cfg_test is not None:
            n = sum(1 for f in findings if f["cfg_test"])
            if n != want_cfg_test:
                failures.append(f"{label}: expected {want_cfg_test} under cfg(test), got {n}")
        print(f"  ok  {label}: {got} finding(s)")

    print("selftest: the mutation this lane exists to catch")
    # THE MUTATION. Identical to 78a0bef5ff (arity) and d26cb8c40e (fields) in shape:
    # production sites updated, the #[cfg(test)] ones left behind.
    check("planted cfg(test)-only skew is CAUGHT", SELFTEST_BEFORE, SELFTEST_BROKEN, 2, 2)
    check("repairing the two sites clears it", SELFTEST_BEFORE, SELFTEST_REPAIRED, 0)
    check("an unchanged file is not judged", SELFTEST_BEFORE, SELFTEST_BEFORE, 0)
    # A definition that appears for the FIRST time in this range is in play too.
    check("a brand-new file with a skew is CAUGHT", None, SELFTEST_BROKEN, 2, 2)
    print("selftest: the readings that must NOT be findings")
    check("a doc comment / string spelling a call is not a call", None, SELFTEST_DOC_DECOY, 0)
    check("a closure argument list is skipped, not miscounted", None, SELFTEST_CLOSURE_DECOY, 0)
    check("a return type in front of a body brace is not a literal", None, SELFTEST_RETURN_TYPE_DECOY, 0)
    check("an all-shorthand body could be a plain block, so it is declined", None, SELFTEST_SHORTHAND_BLOCK_DECOY, 0)
    check("a generic parameter type does not inflate the parameter count", None, SELFTEST_GENERIC_PARAM_DECOY, 0)
    check("a trailing string argument is an argument, not a trailing comma", None, SELFTEST_STRING_ARG_DECOY, 0)
    check("a #[derive(..)] attribute is not a call of a `fn derive`", None, SELFTEST_DERIVE_ATTRIBUTE_DECOY, 0)
    check("an enum variant declaration is not a literal of a same-named struct", None, SELFTEST_VARIANT_NAME_DECOY, 0)
    check(
        "a real literal beside a same-named variant is still judged",
        None,
        SELFTEST_VARIANT_NAME_DECOY.replace("Event { symbol: 1, site: 2 }", "Event { symbol: 1 }"),
        1,
    )
    selftest_cross_file_variant(failures)
    selftest_macro_declared_struct(failures)
    selftest_value_shadow(check, failures)
    selftest_feature_gated(check)

    selftest_impl_headers(failures)
    selftest_push_subject(failures)

    # The blanker must preserve every offset, or every reported line is wrong.
    for label, src in (
        ("before", SELFTEST_BEFORE),
        ("broken", SELFTEST_BROKEN),
        ("decoy", SELFTEST_DOC_DECOY),
    ):
        blanked = blank_comments_and_strings(src)
        if len(blanked) != len(src) or blanked.count("\n") != src.count("\n"):
            failures.append(f"blanker changed the shape of {label}")
    print("  ok  the comment/string blanker preserves offsets and line count")

    print()
    if failures:
        print("SELFTEST: RED")
        for f in failures:
            print(f"  x {f}")
        return 1
    print("SELFTEST: GREEN — the lane fails on the planted skew and passes once it is repaired.")
    return 0


def main() -> int:
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument("--push-context", action="store_true", help="judge the refs in TRUST_PUSHED_REFS")
    p.add_argument(
        "--remote",
        help="the push destination (URL or remote name); with --push-context, judge only what "
        "the push introduces to it (default: $TRUST_PUSH_REMOTE)",
    )
    p.add_argument("--range", help="A..B (default origin/main..HEAD)")
    p.add_argument("--repo", default=None, help="run against this worktree")
    p.add_argument("--selftest", action="store_true", help="mutation-prove the lane")
    args = p.parse_args()

    if args.remote and not args.push_context:
        p.error("--remote names a push destination and needs --push-context")
    if args.selftest:
        return selftest()
    try:
        return run(args)
    except RuntimeError as exc:
        print(f"cfg-test-skew: {exc}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    sys.exit(main())
