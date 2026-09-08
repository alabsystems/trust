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
Only definitions THIS PUSH CHANGED, and only construction sites among the files
THIS PUSH CHANGED:

  * a free function whose parameter list changed  -> every unqualified call site
    IN THE SAME FILE must supply the declared number of arguments (E0061);
  * a struct whose named-field list changed       -> every `S { .. }` literal or
    pattern IN THE SAME CRATE (among the changed files) that does not use `..`
    must name exactly the declared fields (E0063 / E0027 / E0560).

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
names `d26cb8c40e`, `78a0bef5ff` and `ed21a2887f` and nothing else.

It SKIPS rather than guesses, and says how often:
  * a name declared more than once in the file (an inner `mod` may shadow it);
  * a method — any declaration with a `self` receiver, and any call site reached
    through `.` or `::` (`crate::f(..)` is a real free call and is skipped too:
    losing it costs a little coverage, guessing at it costs a false refusal);
  * a call site whose argument text contains `|`, `<` or `>` at top level, where
    a closure parameter list or a generic argument can hide a comma;
  * a struct literal body that does not parse as field pairs (so an `if x == C {`
    block is never mistaken for a literal).

Comments and string literals are blanked (offsets preserved) before anything is
matched, so a doc comment that spells a call is not a call.

It is NOT a type checker and does not claim to be: it cannot see a call site in a
file this push did not touch, a wrong argument TYPE, a trait-method skew, or
anything at all outside the two shapes above. `scoped.compiler-check` remains the
authority. This lane exists so that the authority is not the ONLY thing standing
between this class and `main` — a green here is not a green build, and a commit
body must not cite it as one.

Usage:
    check_cfg_test_caller_skew.py                 # origin/main..HEAD
    check_cfg_test_caller_skew.py --push-context  # the refs git is pushing
    check_cfg_test_caller_skew.py --range A..B
    check_cfg_test_caller_skew.py --selftest      # mutation proof, no repo needed

Exit: 0 clean or nothing in range, 1 skew found, 2 could not read the range.

Author: Andrew Yates <andrewyates.name@gmail.com>
Copyright 2026 Andrew Yates | License: Apache-2.0 OR MIT
"""

from __future__ import annotations

import argparse
import os
import re
import subprocess
import sys

WATCHED_PREFIXES = ("crates/", "compiler/")
ZERO = "0" * 40


# --------------------------------------------------------------------------- git


def git(*args: str, cwd: str | None = None) -> str:
    proc = subprocess.run(
        ["git", *args], capture_output=True, text=True, cwd=cwd
    )
    if proc.returncode != 0:
        raise RuntimeError(f"git {' '.join(args)} failed: {proc.stderr.strip()}")
    return proc.stdout


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


def line_of(src: str, pos: int) -> int:
    return src.count("\n", 0, pos) + 1


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


def fn_call_sites(src: str, name: str) -> list[dict]:
    sites = []
    for m in re.finditer(r"\b" + re.escape(name) + r"\s*\(", src):
        before = src[:m.start()].rstrip()
        # a declaration, not a call
        if re.search(r"\bfn$", before):
            continue
        # a method or a path call — never judged (see the module docstring)
        if before.endswith(".") or before.endswith(":"):
            continue
        # a macro invocation
        if src[m.start() + len(name) : m.end()].lstrip().startswith("!"):
            continue
        open_paren = m.end() - 1
        parsed = top_level_segments(src, open_paren)
        if parsed is None:
            continue
        segs, close = parsed
        ambiguous = any(AMBIGUOUS.search(s) for s in segs)
        sites.append(
            {
                "pos": m.start(),
                "line": line_of(src, m.start()),
                "args": arg_count(segs),
                "ambiguous": ambiguous,
            }
        )
    return sites


# --------------------------------------------------------- struct declarations


def struct_decls(src: str) -> dict[str, list[dict]]:
    found: dict[str, list[dict]] = {}
    for m in re.finditer(r"\bstruct\s+([A-Za-z_][A-Za-z0-9_]*)", src):
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
        if not ok or not fields:
            continue
        found.setdefault(name, []).append(
            {"pos": m.start(), "line": line_of(src, m.start()), "fields": fields}
        )
    return found


def struct_literal_sites(src: str, name: str) -> list[dict]:
    sites = []
    for m in re.finditer(r"\b" + re.escape(name) + r"\s*\{", src):
        before = src[:m.start()].rstrip()
        if before.endswith(":") or before.endswith("."):
            continue
        # `fn f() -> ConcreteCalleeKey {` is a RETURN TYPE followed by the body
        # brace, not a literal. Measured: without this it was the last surviving
        # false finding in the 120-commit sweep (8932acd798, lineage.rs:723), and
        # it read the body's first path call `ConcreteCalleeKey::test_only(` as a
        # field named after the struct.
        if before.endswith("->") or before.endswith("as"):
            continue
        if re.search(r"\b(struct|enum|union|trait|impl|where)$", before):
            continue
        open_brace = m.end() - 1
        parsed = top_level_segments(src, open_brace)
        if parsed is None:
            continue
        segs, _ = parsed
        names: list[str] = []
        rest = False
        parses = True
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
                parses = False
                break
            explicit = explicit or ":" in body
            names.append(fm.group(1))
        if not parses:
            continue  # a block, a match arm body, anything that is not a literal
        if names and not explicit:
            # An all-shorthand body is indistinguishable from a plain block whose
            # last expression is an identifier (`if flag { x }`). Rust forbids a
            # struct literal in that position, but this lane does not parse Rust,
            # so it declines rather than guesses.
            continue
        sites.append(
            {
                "pos": m.start(),
                "line": line_of(src, m.start()),
                "fields": names,
                "rest": rest,
            }
        )
    return sites


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
        for site in fn_call_sites(head, name):
            if site["ambiguous"]:
                stats["skipped_ambiguous"] += 1
                continue
            if site["args"] == decl["params"]:
                continue
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
        prior_fields = prior[0]["fields"] if prior and len(prior) == 1 else None
        if prior_fields == decl["fields"]:
            continue
        stats["definitions_in_play"] += 1
        want = set(decl["fields"])
        for site in struct_literal_sites(head, name):
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


def analyse_cross_file_structs(sources: dict, stats: dict) -> list[tuple[str, dict]]:
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
    starts refusing correct pushes."""
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
            # NOT counted again: analyse_blanked already counted this definition
            # when it judged the declaring file. The summary line reports
            # DEFINITIONS, so counting one twice would misstate the subject.
            want = set(decl["fields"])
            for path in paths:
                if path == decl_path:
                    continue  # analyse_file already judged the declaring file
                _base_blank, head_blank = sources[path]
                if imports_foreign(head_blank, name):
                    stats["skipped_foreign_import"] += 1
                    continue
                ranges = cfg_test_ranges(head_blank)
                for site in struct_literal_sites(head_blank, name):
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


# ------------------------------------------------------------------ the driver


def resolve_ranges(args, cwd: str | None) -> list[tuple[str, str]]:
    if args.range:
        if ".." not in args.range:
            raise RuntimeError(f"--range must be A..B, got {args.range!r}")
        a, b = args.range.split("..", 1)
        return [(a or "origin/main", b or "HEAD")]

    if args.push_context:
        refs = os.environ.get("TRUST_PUSHED_REFS", "")
        out = []
        for line in refs.splitlines():
            parts = line.split()
            if len(parts) < 4:
                continue
            _local_ref, local_sha, _remote_ref, remote_sha = parts[:4]
            if local_sha.strip("0") == "":
                continue  # a deletion pushes nothing to read
            base = remote_sha if remote_sha.strip("0") else "origin/main"
            out.append((base, local_sha))
        if out:
            return out
        # unset TRUST_PUSHED_REFS: widen to the standing reading, and say so
        return [("origin/main", "HEAD")]

    return [("origin/main", "HEAD")]


def run(args) -> int:
    cwd = args.repo
    subject = resolve_ranges(args, cwd)
    print(f"SUBJECT: {', '.join(f'{a[:12]}..{b[:12]}' for a, b in subject)}")

    all_findings: list[tuple[str, dict]] = []
    total_stats = {
        "skipped_ambiguous": 0,
        "skipped_duplicate_name": 0,
        "skipped_foreign_import": 0,
        "definitions_in_play": 0,
    }
    files_read = 0
    sources: dict = {}

    for base, head in subject:
        try:
            names = git("diff", "--name-only", f"{base}", f"{head}", cwd=cwd).splitlines()
        except RuntimeError as exc:
            print(f"cfg-test-skew: could NOT READ the range {base}..{head} — {exc}", file=sys.stderr)
            print("               usually an unfetched remote sha: git fetch, rebase, retry.", file=sys.stderr)
            return 2
        for path in names:
            if not path.endswith(".rs") or not path.startswith(WATCHED_PREFIXES):
                continue
            head_src = blob_at(head, path, cwd=cwd)
            if head_src is None:
                continue  # deleted by this push
            base_src = blob_at(base, path, cwd=cwd)
            files_read += 1
            head_blank = blank_comments_and_strings(head_src)
            base_blank = blank_comments_and_strings(base_src) if base_src is not None else None
            sources[path] = (base_blank, head_blank)
            findings, stats = analyse_blanked(base_blank, head_blank)
            for key in total_stats:
                total_stats[key] += stats[key]
            for f in findings:
                all_findings.append((path, f))
        all_findings.extend(analyse_cross_file_structs(sources, total_stats))
        sources = {}

    print(
        f"read {files_read} changed .rs file(s); "
        f"{total_stats['definitions_in_play']} definition(s) whose shape this range changed; "
        f"skipped {total_stats['skipped_ambiguous']} ambiguous call site(s), "
        f"{total_stats['skipped_duplicate_name']} duplicated name(s), "
        f"{total_stats['skipped_foreign_import']} foreign-imported name(s)"
    )

    if not all_findings:
        print("PASS: every construction site of a shape this range changed still matches it.")
        return 0

    test_only = sum(1 for _, f in all_findings if f["cfg_test"])
    print()
    print(f"FAIL: {len(all_findings)} construction site(s) did not follow a shape this range changed")
    print(f"      ({test_only} of them under #[cfg(test)], where no lib build can see them).")
    print()
    shown = 0
    for path, f in all_findings:
        if shown == 25:
            print(f"  ... and {len(all_findings) - shown} more")
            break
        tag = "cfg(test)" if f["cfg_test"] else "production"
        if f["kind"] == "arity":
            print(
                f"  x {path}:{f['line']}  [{tag}]  {f['name']}(..) takes "
                f"{f['expected']} argument(s) (declared line {f['decl_line']}), {f['got']} supplied"
            )
        else:
            bits = []
            if f["missing"]:
                bits.append("missing " + ", ".join(f["missing"]))
            if f["unknown"]:
                bits.append("unknown " + ", ".join(f["unknown"]))
            print(
                f"  x {path}:{f['line']}  [{tag}]  {f['name']} {{ .. }} "
                f"(declared line {f['decl_line']}): " + "; ".join(bits)
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

SELFTEST_CLOSURE_DECOY = """
pub(crate) fn taking(f: F, n: usize, m: usize) { let _ = (f, n, m); }

fn production() {
    taking(|a, b| a + b, 1, 2);
}
"""


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
    p.add_argument("--range", help="A..B (default origin/main..HEAD)")
    p.add_argument("--repo", default=None, help="run against this worktree")
    p.add_argument("--selftest", action="store_true", help="mutation-prove the lane")
    args = p.parse_args()

    if args.selftest:
        return selftest()
    try:
        return run(args)
    except RuntimeError as exc:
        print(f"cfg-test-skew: {exc}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    sys.exit(main())
