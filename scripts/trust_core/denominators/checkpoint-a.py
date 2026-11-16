#!/usr/bin/env python3
"""E0.12 denominators `checkpoint-a`: the Checkpoint A straight-line population and the LLVM differential's programs.

Design of record: docs/design/2026-09-16-trust-core-architecture.md, §5.2 Stage 0.5 ("The Checkpoint A
straight-line function population (for E1.4.5 and K3)" and "The exact program count of the LLVM
differential that LEDGER calls "~129" (`LEDGER:42`) [S], for E1.7.3"; exit E0.12 "All published, each
with its predicate: 0 denominators without one"). LEDGER is docs/campaigns/2026-09-10-selfhost-trust-ir-cg.md
(the design's §1.4 table). Consumers: K3 and K6 (§5.1 items 5 and 6), E1.4.5 and E1.7.3.

Every number is recomputed from git objects (never a working tree, never the design):

  SUPERPROJECT  at `--rev` (default HEAD): the Checkpoint A log
                reports/2026-09-16-trust-core-architecture/checkpointA3.log.gz (SCR in the design), the
                census v2 report beside it (whose recorded digest the decompressed log must equal), the
                M-POS gate crates/trust-cg-bridge/src/verify_output.rs (whose SCOPE header is the design's
                definition of "straight-line"), and LEDGER.
  TRUST-CG      first-party/trust-cg read from the superproject's modules object store at three commits,
                each the gitlink the superproject names at a stated commit: at `--rev` (the pin every
                E1.7.3 row counts at); at the log's `build commit:` (the plugin that produced Checkpoint A,
                whose body-printing sites the log is searched for); and at the commit that introduced
                LEDGER's "~129 programs" sentence (the pin that sentence described).

The predicates (each row of docs/trust-core/denominators/checkpoint-a.toml repeats its own):

  straight-line.population            BLOCKED. Checkpoint A functions whose gate-input body lies in the
                                      M-POS SCOPE header. Measuring it needs every such function's body;
                                      the committed evidence carries none (the next row), so the row records
                                      what would unblock it instead of a number.
  straight-line.log-body-records      lines of the decompressed Checkpoint A log that carry a marker of a
                                      body-printing site of the Checkpoint A plugin: the leading token of the
                                      first string literal of every `eprintln!` in
                                      crates/rustc-codegen-trust-cg/src/*.rs (comments excluded) whose format
                                      string contains `:#?}`.
  straight-line.log-lowered-function-records
                                      lines of that log carrying the head of the plugin's only template that
                                      names a function it lowered (census v2's noop-precondition-check).
  llvm-differential.programs          distinct P with `include_str!("bridge_corpus/P")` in the code of
                                      crates/rustc-codegen-trust-cg/tests/bridge_differential_x86.rs (the P2
                                      harness); every one must be a `Case` of its `corpus()` (a finding
                                      otherwise, since the row's predicate says so).
  llvm-differential.corpus-cases      `Case { .. }` entries of `corpus()` (each: one `name`, one `src:
                                      include_str!` program; names unique).
  llvm-differential.standalone-only-programs
                                      harness programs included outside `corpus()` and by no Case.
  llvm-differential.program-runs      corpus-cases x the opt levels of `for opt in [..]` in
                                      `bridge_corpus_matches_llvm_across_opt_levels`, which must compile
                                      each case with `None` (LLVM, the oracle) and `Some(&dylib)` (trust-cg).
  llvm-differential.differential-harness-programs
                                      distinct bridge_corpus include_str! targets over every top-level test
                                      file whose name contains `differential`.
  bridge-corpus.files / .included-by-no-test
                                      blobs under tests/bridge_corpus/; those no top-level test file
                                      include_str!s.
  llvm-differential.suite-programs    BLOCKED, and E1.7.3's program set: every program any test of the
                                      crate compiles under both backends and compares (some are built at run
                                      time by format! templates). llvm-differential.programs and
                                      .differential-harness-programs are measured SUBSETS of it (lower
                                      bounds), never the set.
  ledger-pin.*                        the same harness count, and the count of top-level test files whose
                                      text contains `codegen-backend`, at the trust-cg gitlink of the commit
                                      that wrote LEDGER:42; test-files and test-files-naming-codegen-backend
                                      are the same file counts at --rev.

Usage (common.py needs Python 3.11+; macOS's /usr/bin/python3 is 3.9):
    python3.14 scripts/trust_core/denominators/checkpoint-a.py            # measure and print
    python3.14 scripts/trust_core/denominators/checkpoint-a.py --list     # also print every list
    python3.14 scripts/trust_core/denominators/checkpoint-a.py --write    # rewrite the TOML record
    python3.14 scripts/trust_core/denominators/checkpoint-a.py --check    # the TOML equals a re-measurement

Exit codes: 0 measured and (with --check) the record matches; 1 a finding or a mismatch;
2 an input cannot be read.

Author: Andrew Yates <andrewyates.name@gmail.com>
Copyright 2026 Andrew Yates | License: Apache-2.0 OR MIT
"""

import os as _floor_os
import shutil as _floor_shutil
import sys as _floor_sys

# Trust: python floor (scripts/tests/python_floor_test.py). This file needs tomllib (3.11+) and plain
# `python3` is 3.9 on macOS CommandLineTools, so an old interpreter re-execs here, before any import
# that needs 3.11 runs.
if __name__ == "__main__" and _floor_sys.version_info < (3, 11):
    for _floor_candidate in ("python3.14", "python3.13", "python3.12", "python3.11"):
        _floor_path = _floor_shutil.which(_floor_candidate)
        if _floor_path:
            _floor_argv = [_floor_path, _floor_os.path.abspath(__file__), *_floor_sys.argv[1:]]
            _floor_os.execv(_floor_path, _floor_argv)
    _floor_sys.exit("checkpoint-a.py requires Python 3.11+ (tomllib); none found on PATH")

import argparse
import gzip
import hashlib
import json
import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import common as C  # noqa: E402

import tomllib  # noqa: E402  (common.py has already refused an interpreter without it)

KEY = "checkpoint-a"
SCHEMA = "trust.core.denominator.v1"
RECORD_REL = f"docs/trust-core/denominators/{KEY}.toml"
SCRIPT_REL = f"scripts/trust_core/denominators/{KEY}.py"

SCR = "reports/2026-09-16-trust-core-architecture"
LOG_REL = f"{SCR}/checkpointA3.log.gz"
CENSUS_REL = f"{SCR}/census-v2.md"
GATE_REL = "crates/trust-cg-bridge/src/verify_output.rs"
LEDGER_REL = "docs/campaigns/2026-09-10-selfhost-trust-ir-cg.md"
LEDGER_CLAIM = "~129 programs"

PLUGIN = "crates/rustc-codegen-trust-cg"
PLUGIN_SRC = f"{PLUGIN}/src/"
TESTS = f"{PLUGIN}/tests/"
HARNESS = f"{TESTS}bridge_differential_x86.rs"
CORPUS = f"{TESTS}bridge_corpus/"
CORPUS_TEST = "bridge_corpus_matches_llvm_across_opt_levels"
RUNTIME_EXAMPLE = "m51_signed_narrow_x86.rs"  # the suite row's example of a run-time-built differential
DIGEST_RULE = "sha256 over the sorted lines `<path>\\t<blob id>\\n` of the row's programs (paths relative to tests/)"

SCOPE_START = "// SCOPE (honest):"
SCOPE_END = "Everything else is Unknown (fail-closed)."
BUILD_COMMIT = re.compile(r"build commit:\s*([0-9a-f]{40})\b")
CENSUS_DIGEST = re.compile(r"sha256 of the decompressed text `([0-9a-f]{64})`")
# The census v2 template (noop-precondition-check) by which the plugin names a function it lowered: the
# only positive function record among its templates. The census report must still carry it.
LOWERED = "rustc_codegen_trust_cg: lowered `"
LOWERED_TEMPLATE = "rustc_codegen_trust_cg: lowered `{name}` as a no-op"
INCLUDE = re.compile(r'include_str!\(\s*"bridge_corpus/([^"\\]+)"\s*\)')

# What the design says, found by these patterns in the design text at the same revision. A pattern
# that no longer matches is reported as "not found", never as agreement.
DESIGN_READINGS = (
    ("llvm-differential.programs", r'LLVM\s+differential\s+that\s+LEDGER\s+calls\s+"~(\d+)"'),
    ("llvm-differential.suite-programs", r"the\s+LLVM\s+differential\s+over\s+the\s+exact\s+program\s+set\s+counted\s+at\s+E0\.12"),
    ("straight-line.population", r"The\s+Checkpoint\s+A\s+straight-line\s+function\s+population"),
    ("straight-line.population", r"over\s+the\s+Checkpoint\s+A\s+straight-line\s+population"),
    ("straight-line.population", r"min\(1,000,\s+the\s+E0\.12\s+straight-line\s+population\)"),
    ("straight-line.population", r'single-block\s+scalar\s+functions",\s+"NEVER\s+Proven\s+on\s+Unknown"\s*\(`crates/trust-cg-bridge/src/verify_output\.rs:(\d+-\d+)`\)'),
    ("straight-line.population", r'integer-only,\s+straight-line,\s+single-block\s+scalar\s+functions"\s*\(`crates/trust-cg-bridge/src/verify_output\.rs:(\d+-\d+)`\)'),
)


class Fatal(Exception):
    """An input the measurement cannot proceed without (exit 2)."""


# --------------------------------------------------------------------------
# Rust source: comments and string literals, located without a parser
# --------------------------------------------------------------------------

CHAR_LITERAL = re.compile(r"'(?:\\u\{[0-9a-fA-F]{1,6}\}|\\x[0-9a-fA-F]{2}|\\.|[^\\'\n])'")
RAW_STRING = re.compile(r'b?r(#*)"')


def lex(src: str) -> tuple[str, str]:
    """(code, shape), both as long as `src`. `code` blanks every comment (nested block comments too);
    `shape` also blanks the contents of every string and char literal, keeping the quotes, so braces,
    brackets and keywords found in `shape` are the program's own, and a string literal found there is
    read back from `code` at the same offsets. Newlines are kept in both."""
    code, shape = list(src), list(src)
    n, i = len(src), 0

    def blank(a: int, b: int, *targets) -> None:
        for t in targets:
            for k in range(a, b):
                if t[k] != "\n":
                    t[k] = " "

    while i < n:
        if src.startswith("//", i):
            j = src.find("\n", i)
            j = n if j < 0 else j
            blank(i, j, code, shape)
            i = j
        elif src.startswith("/*", i):
            depth, j = 0, i
            while j < n:
                if src.startswith("/*", j):
                    depth, j = depth + 1, j + 2
                elif src.startswith("*/", j):
                    depth, j = depth - 1, j + 2
                    if depth == 0:
                        break
                else:
                    j += 1
            blank(i, j, code, shape)
            i = j
        elif (m := RAW_STRING.match(src, i)) and (i == 0 or not (src[i - 1].isalnum() or src[i - 1] == "_")):
            close = '"' + m.group(1)
            j = src.find(close, m.end())
            j = n if j < 0 else j
            blank(m.end(), j, shape)
            i = j + len(close)
        elif src[i] == '"':
            j = i + 1
            while j < n and src[j] != '"':
                j += 2 if src[j] == "\\" else 1
            blank(i + 1, min(j, n), shape)
            i = j + 1
        elif src[i] == "'" and (m := CHAR_LITERAL.match(src, i)):
            blank(i + 1, m.end() - 1, shape)
            i = m.end()
        else:
            i += 1
    return "".join(code), "".join(shape)


def match_close(shape: str, open_at: int) -> int:
    """The offset of the bracket closing the one at `open_at` (`{`, `[` or `(`), or -1."""
    pairs = {"{": "}", "[": "]", "(": ")"}
    opener = shape[open_at]
    closer, depth = pairs[opener], 0
    for k in range(open_at, len(shape)):
        if shape[k] == opener:
            depth += 1
        elif shape[k] == closer:
            depth -= 1
            if depth == 0:
                return k
    return -1


def string_at(code: str, shape: str, quote_at: int) -> str | None:
    """The literal text of the string literal whose opening quote is at `quote_at` (escapes kept)."""
    if shape[quote_at] != '"':
        return None
    end = shape.find('"', quote_at + 1)
    return None if end < 0 else code[quote_at + 1:end]


def fn_body(shape: str, name: str) -> tuple[int, int] | None:
    """(start, end) offsets of the braces of `fn <name>(..) .. { .. }`, or None."""
    m = re.search(rf"\bfn\s+{re.escape(name)}\s*\(", shape)
    if m is None:
        return None
    params_end = match_close(shape, m.end() - 1)
    brace = shape.find("{", params_end)
    if params_end < 0 or brace < 0:
        return None
    end = match_close(shape, brace)
    return None if end < 0 else (brace, end)


def includes(code: str, shape: str, lo: int = 0, hi: int | None = None) -> list[tuple[int, str]]:
    """(offset, P) for each `include_str!("bridge_corpus/P")` in code (not in a comment or a string)."""
    hi = len(code) if hi is None else hi
    return [(m.start(), m.group(1)) for m in INCLUDE.finditer(code, lo, hi) if shape[m.start()] == "i"]


# --------------------------------------------------------------------------
# git objects
# --------------------------------------------------------------------------


def blob_ids(store: str, rev: str, prefix: str) -> dict[str, str]:
    """path -> blob id for every blob at or below `prefix` at `rev` in a bare object store."""
    out = C.git(store, "ls-tree", "-r", "-z", "--full-tree", rev, "--", prefix, git_dir=True)
    if out is None:
        raise Fatal(f"{store}: cannot list {prefix} at {rev}")
    ids = {}
    for record in out.split("\0"):
        if record:
            meta, _, path = record.partition("\t")
            _, kind, oid = meta.split()
            if kind == "blob":
                ids[path] = oid
    return ids


def trust_cg_at(repo: Path, superproject_rev: str) -> tuple[C.GitTree, str]:
    tree = C.first_party_tree(repo, "trust-cg", superproject_rev)
    if tree is None:
        raise Fatal(f"first-party/trust-cg at superproject {superproject_rev}: no gitlink or no object store")
    if (C.git(tree.repo, "cat-file", "-t", tree.rev, git_dir=True) or "").strip() != "commit":
        raise Fatal(f"first-party/trust-cg {tree.rev} (gitlink at {superproject_rev}) is not in {tree.repo}")
    return tree, str(tree.repo)


def digest(pairs) -> str:
    return "sha256:" + hashlib.sha256("".join(f"{p}\t{o}\n" for p, o in sorted(pairs)).encode()).hexdigest()


# --------------------------------------------------------------------------
# measurements
# --------------------------------------------------------------------------


def measure_log(findings: C.Findings, repo: Path, rev: str) -> dict:
    raw = C.git(repo, "cat-file", "blob", f"{rev}:{LOG_REL}", binary=True)
    if raw is None:
        raise Fatal(f"{LOG_REL} is not in {rev}")
    try:
        text = gzip.decompress(raw).decode("utf-8")
    except (OSError, UnicodeDecodeError) as error:
        raise Fatal(f"{LOG_REL}: {error}") from error
    sha = hashlib.sha256(text.encode("utf-8")).hexdigest()
    census = C.git(repo, "show", f"{rev}:{CENSUS_REL}") or ""
    recorded = CENSUS_DIGEST.search(census)
    if recorded is None:
        findings.add("INPUT", f"{CENSUS_REL} records no decompressed-log digest")
    elif recorded.group(1) != sha:
        findings.add("INPUT", f"{LOG_REL} decompresses to sha256 {sha}, but {CENSUS_REL} records {recorded.group(1)}")
    if LOWERED_TEMPLATE not in census:
        findings.add("INPUT", f"{CENSUS_REL} no longer lists the template {LOWERED_TEMPLATE!r}")
    builds = {m.group(1) for m in BUILD_COMMIT.finditer(text)}
    if len(builds) != 1:
        raise Fatal(f"{LOG_REL}: expected one `build commit:`, found {sorted(builds)}")
    build = builds.pop()
    blob = (C.git(repo, "rev-parse", "--verify", f"{rev}:{LOG_REL}") or "").strip()
    return {"text": text, "lines": text.count("\n") + (0 if text.endswith("\n") else 1), "sha256": sha,
            "blob": blob, "build_commit": build}


def body_print_markers(findings: C.Findings, plugin: C.GitTree) -> list[dict]:
    """Every `eprintln!` of the plugin's src/ whose first string literal prints a value with `:#?}`."""
    markers = []
    for rel in plugin.files(PLUGIN_SRC, (".rs",)):
        src = plugin.text(rel)
        if src is None:
            findings.add("INPUT", f"trust-cg {plugin.rev}:{rel} is not UTF-8 text")
            continue
        code, shape = lex(src)
        for m in re.finditer(r"\beprintln!\s*\(", shape):
            quote = shape.find('"', m.end())
            close = match_close(shape, m.end() - 1)
            if quote < 0 or (0 <= close < quote):
                continue
            fmt = string_at(code, shape, quote)
            if fmt is None or ":#?}" not in fmt:
                continue
            line = src.count("\n", 0, m.start()) + 1
            token = re.match(r"[A-Z][A-Z0-9_]{2,}", fmt)
            if token is None:
                findings.add("BODY-SITE", f"trust-cg {plugin.rev[:12]}:{rel}:{line} prints a body with no leading "
                                          f"marker, so the log cannot be searched for it: {fmt[:80]!r}")
                continue
            markers.append({"marker": token.group(0), "site": f"{rel}:{line}"})
    return markers


def measure_scope(findings: C.Findings, repo: Path, rev: str) -> dict:
    text = C.git(repo, "show", f"{rev}:{GATE_REL}")
    if text is None:
        raise Fatal(f"{GATE_REL} is not in {rev}")
    lines = text.split("\n")
    start = next((k for k, ln in enumerate(lines) if ln.startswith(SCOPE_START)), None)
    end = None if start is None else next((k for k in range(start, len(lines)) if SCOPE_END in lines[k]), None)
    if start is None or end is None:
        raise Fatal(f"{GATE_REL}: the `{SCOPE_START}` header sentence is gone; the predicate has no source")
    quote = " ".join(ln.lstrip("/ ").strip() for ln in lines[start:end + 1])
    quote = quote[:quote.index(SCOPE_END) + len(SCOPE_END)]
    # Where the interpreter the gate runs (trust_ir_semantics through eval_rvalue) admits a shape the
    # header excludes: the first line of each, searched only inside that span.
    lo = next((k for k, ln in enumerate(lines) if ln.startswith("pub fn trust_ir_semantics(")), None)
    hi = next((k for k, ln in enumerate(lines) if ln.startswith("fn pick_width(")), None)
    wider = []
    if lo is None or hi is None or hi < lo:
        findings.add("GATE", f"{GATE_REL}: `pub fn trust_ir_semantics(` .. `fn pick_width(` span not found")
    else:
        for label, pattern in (("float locals", r"float_bit_width\(&d\.ty\)"),
                               ("Deref store", r"matches!\(place\.projections\[0\], Projection::Deref\)"),
                               ("Goto", r"Terminator::Goto\("),
                               ("Call to a proven local callee (bundle gate only; the single-function entry refuses it)",
                                r"Terminator::Call\s*\{"),
                               ("SwitchInt", r"Terminator::SwitchInt\s*\{")):
            hit = next((k + 1 for k in range(lo, hi) if re.search(pattern, lines[k])), None)
            if hit is not None:
                wider.append(f"{label} at {GATE_REL}:{hit}")
    blob = (C.git(repo, "rev-parse", "--verify", f"{rev}:{GATE_REL}") or "").strip()
    return {"lines": f"{start + 1}-{end + 1}", "quote": quote, "wider": wider, "blob": blob}


def measure_harness(findings: C.Findings, tree: C.GitTree, store: str, where: str) -> dict:
    src = tree.text(HARNESS)
    if src is None:
        raise Fatal(f"trust-cg {tree.rev}: {HARNESS} is missing")
    code, shape = lex(src)
    ids = blob_ids(store, tree.rev, TESTS)
    body = fn_body(shape, "corpus")
    if body is None:
        raise Fatal(f"trust-cg {tree.rev}: {HARNESS} has no `fn corpus()`")
    cases, names = [], set()
    for m in re.finditer(r"\bCase\s*\{", shape[body[0]:body[1]]):
        at = body[0] + m.start()
        close = match_close(shape, body[0] + m.end() - 1)
        name_at = [k.end() - 1 for k in re.finditer(r'\bname\s*:\s*"', shape[at:close])]
        progs = includes(code, shape, at, close)
        if len(name_at) != 1 or len(progs) != 1:
            findings.add("HARNESS", f"{where}: a Case at offset {at} has {len(name_at)} names and {len(progs)} programs")
            continue
        name = string_at(code, shape, at + name_at[0])
        if name in names:
            findings.add("HARNESS", f"{where}: two Cases are named {name!r}")
        names.add(name)
        cases.append({"case": name, "path": progs[0][1]})
    every = includes(code, shape)
    in_corpus = {p for off, p in every if body[0] <= off <= body[1]}
    programs = sorted({p for _, p in every})
    standalone_only = sorted(set(programs) - in_corpus)
    if standalone_only:
        findings.add("HARNESS", f"{where}: programs outside every Case ({', '.join(standalone_only)}); the "
                                "row's predicate says each program is a Case's, so restate it before publishing")
    case_paths = [c["path"] for c in cases]
    if len(set(case_paths)) != len(case_paths):
        findings.add("HARNESS", f"{where}: a corpus program is the src of more than one Case")
    for p in programs:
        if f"{CORPUS}{p}" not in ids:
            findings.add("HARNESS", f"{where}: include_str! names bridge_corpus/{p}, which is not in the tree")
    test = fn_body(shape, CORPUS_TEST)
    opts: list[str] = []
    if test is None:
        findings.add("HARNESS", f"{where}: `fn {CORPUS_TEST}` is gone; the corpus is no longer driven by it")
    else:
        body_code = re.sub(r"\s+", "", code[test[0]:test[1]])
        for need in ("forcaseincorpus()", "compile_link_run(case.name,case.src,opt,None)",
                     "compile_link_run(case.name,case.src,opt,Some(&dylib))"):
            if need not in body_code:
                findings.add("HARNESS", f"{where}: `{CORPUS_TEST}` no longer contains `{need}`")
        loop = re.search(r"\bfor\s+opt\s+in\s*\[", shape[test[0]:test[1]])
        if loop is None:
            findings.add("HARNESS", f"{where}: `{CORPUS_TEST}` has no `for opt in [..]`")
        else:
            lo = test[0] + loop.end() - 1
            hi = match_close(shape, lo)
            opts = [string_at(code, shape, k) for k in range(lo, hi) if shape[k] == '"'][0::2]
        x86_only = "if!host_is_x86_64()" in body_code
    return {
        "rev": tree.rev, "cases": cases, "programs": programs, "standalone_only": standalone_only,
        "opts": opts, "x86_only": test is not None and x86_only,
        "digest": digest((f"bridge_corpus/{p}", ids[f"{CORPUS}{p}"]) for p in programs if f"{CORPUS}{p}" in ids),
        "blobs": {p: ids.get(f"{CORPUS}{p}", "") for p in programs},
        "harness_blob": ids.get(HARNESS, ""),
    }


def measure_tests(tree: C.GitTree, store: str) -> dict:
    ids = blob_ids(store, tree.rev, TESTS)
    top = sorted(p for p in ids if p.endswith(".rs") and "/" not in p[len(TESTS):])
    tree.prefetch(top)
    naming = [p for p in top if "codegen-backend" in (tree.text(p) or "")]
    no_llvm = [p for p in naming if "llvm" not in (tree.text(p) or "").lower()]
    corpus_files = sorted(p[len(CORPUS):] for p in ids if p.startswith(CORPUS))
    included_by: dict[str, list[str]] = {}
    for p in top:
        code, shape = lex(tree.text(p) or "")
        for _, target in includes(code, shape):
            included_by.setdefault(target, [])
            if p[len(TESTS):] not in included_by[target]:
                included_by[target].append(p[len(TESTS):])
    differential = {t: hs for t, hs in included_by.items() if any("differential" in h for h in hs)}
    return {
        "rev": tree.rev, "top": [p[len(TESTS):] for p in top], "naming": [p[len(TESTS):] for p in naming],
        "no_llvm": [p[len(TESTS):] for p in no_llvm],
        "corpus_files": corpus_files,
        "not_included": sorted(set(corpus_files) - set(included_by)),
        "differential": dict(sorted(differential.items())),
        "differential_digest": digest((f"bridge_corpus/{t}", ids.get(f"{CORPUS}{t}", "")) for t in differential),
        "blobs": {t: ids.get(f"{CORPUS}{t}", "") for t in differential},
    }


def check_runtime_example(findings: C.Findings, tree: C.GitTree) -> None:
    """The blocked suite row names RUNTIME_EXAMPLE as a test that builds its programs at run time and compiles
    each under both backends; hold the record to that: its `fn differential_case` must build the source with
    `format!` and compile it with the LLVM oracle (`None`) and with trust-cg (`Some(..)`)."""
    text = tree.text(f"{TESTS}{RUNTIME_EXAMPLE}")
    if text is None:
        findings.add("SUITE", f"trust-cg {tree.rev[:12]}: {TESTS}{RUNTIME_EXAMPLE}, the suite row's example, is gone")
        return
    code, shape = lex(text)
    body = fn_body(shape, "differential_case")
    flat = re.sub(r"\s+", "", code[body[0]:body[1]]) if body else ""
    if not (body and "format!(" in flat and ",None)" in flat and ",Some(" in flat):
        findings.add("SUITE", f"trust-cg {tree.rev[:12]}: {RUNTIME_EXAMPLE}'s `differential_case` no longer builds its "
                              "source with format! and compiles it under both backends; restate the suite row's reason")


def ledger_facts(findings: C.Findings, repo: Path, rev: str) -> dict:
    text = C.git(repo, "show", f"{rev}:{LEDGER_REL}")
    if text is None:
        raise Fatal(f"{LEDGER_REL} is not in {rev}")
    hits = [k + 1 for k, ln in enumerate(text.split("\n")) if LEDGER_CLAIM in ln]
    if len(hits) != 1:
        findings.add("LEDGER", f"{LEDGER_REL} carries {LEDGER_CLAIM!r} on lines {hits}, not exactly once")
    log = C.git(repo, "log", "--reverse", "--format=%H", "-S", LEDGER_CLAIM, rev, "--", LEDGER_REL) or ""
    commits = [c for c in log.split() if C.HEX40.match(c)]
    if not commits:
        raise Fatal(f"no commit of {rev} introduced {LEDGER_CLAIM!r} into {LEDGER_REL}")
    return {"line": hits[0] if hits else None, "commit": commits[0],
            "blob": (C.git(repo, "rev-parse", "--verify", f"{rev}:{LEDGER_REL}") or "").strip()}


def design_readings(repo: Path, rev: str) -> dict[str, list[dict]]:
    text = C.git(repo, "show", f"{rev}:{C.DESIGN_REL}") or ""
    out: dict[str, list[dict]] = {}
    for row, pattern in DESIGN_READINGS:
        m = re.search(pattern, text)
        entry = {"pattern": pattern, "found": m is not None}
        if m is not None:
            entry["line"] = text.count("\n", 0, m.start()) + 1
            entry["value"] = m.group(1) if m.groups() else None
        out.setdefault(row, []).append(entry)
    return out


# --------------------------------------------------------------------------
# the record
# --------------------------------------------------------------------------


def q(value) -> str:
    """A TOML basic string (JSON's escapes are a subset of TOML's)."""
    return json.dumps(value, ensure_ascii=False)


def tk(name: str) -> str:
    return name if re.fullmatch(r"[A-Za-z0-9_-]+", name) else q(name)


def tv(value) -> str:
    if isinstance(value, bool):
        return "true" if value else "false"
    if isinstance(value, int):
        return str(value)
    if isinstance(value, str):
        return q(value)
    if isinstance(value, dict):
        return "{ " + ", ".join(f"{tk(k)} = {tv(v)}" for k, v in value.items()) + " }" if value else "{}"
    if isinstance(value, (list, tuple)):
        if not value:
            return "[]"
        if all(isinstance(v, str) and len(v) < 40 for v in value) and len(value) <= 6:
            return "[" + ", ".join(tv(v) for v in value) + "]"
        return "[\n" + "".join(f"  {tv(v)},\n" for v in value) + "]"
    raise TypeError(f"no TOML rendering for {type(value).__name__}")


def build_rows(m: dict) -> list[dict]:
    log, scope, markers = m["log"], m["scope"], m["markers"]
    head, head_tests, led, led_tests = m["harness"], m["tests"], m["ledger_harness"], m["ledger_tests"]
    ledger, cp_plugin = m["ledger"], m["checkpoint_plugin"]
    body_records = {k["marker"]: sum(1 for ln in log["text"].split("\n") if k["marker"] in ln) for k in markers}
    lowered = sum(1 for ln in log["text"].split("\n") if LOWERED in ln)
    readings = m["design"]

    def read(row: str, verdict) -> list[str]:
        notes = []
        for r in readings.get(row, []):
            if not r["found"]:
                notes.append(f"pattern {r['pattern']!r}: not found in the design")
            else:
                notes.append(f"design:{r['line']} " + verdict(r))
        return notes

    rows: list[dict] = []
    rows.append({
        "name": "straight-line.population", "status": "blocked",
        "predicate": (
            "Checkpoint A functions (distinct mangled symbols among the functions the Checkpoint A compile of "
            "library/std codegens; LEDGER's configuration: `x.py build --stage 1 library/std` with trust-ir-cg "
            "the default backend and certificates on) whose gate-input body - the trust-types VerifiableFunction "
            "the builtin adapter builds from the function's runtime MIR, which is what trust_ir_semantics reads - "
            f"lies in the M-POS gate's stated scope ({GATE_REL}:{scope['lines']}, quoted in `scope`): "
            "(1) exactly one basic block, the entry block, whose terminator is Return; "
            "(2) every local (return place, arguments, temporaries) has type Int or Bool (Bool as the result of "
            "a comparison, which `all ICmp` admits); "
            "(3) every statement is StorageLive, StorageDead, Nop, or an Assign to a local with no projection "
            "whose rvalue is Use (Copy or Move of a local, or an Int or Bool constant), BinaryOp with op in "
            "{Add, Sub, Mul, BitAnd, BitOr, BitXor, Shl, Shr, Div, Rem, Eq, Ne, Lt, Le, Gt, Ge}, UnaryOp Neg, or "
            "an Int-to-Int Cast (sign-extend, zero-extend or truncate). Any other terminator, second block, type, "
            "statement, projection or operand (Goto, SwitchInt, Call, Assert, Drop, a float, pointer, reference "
            "or aggregate local, Not, Cmp, a memory access) excludes the function."),
        "scope": scope["quote"],
        "scope_vs_implementation": (
            "the header's scope is the design's definition; trust_ir_semantics at this revision admits more ("
            + "; ".join(scope["wider"]) + "), which this predicate excludes"),
        "blocked": (
            "measuring the population needs the gate-input body of every function Checkpoint A codegens, and "
            f"the committed evidence has none: {LOG_REL} (sha256 of the decompressed text {log['sha256']}) holds "
            f"{sum(body_records.values())} body records (straight-line.log-body-records). The plugin that "
            f"produced it (trust-cg {cp_plugin[:12]}, the gitlink at the log's build commit "
            f"{log['build_commit'][:12]}) prints a body only through its knob-gated sites "
            f"({', '.join(k['marker'] + ' at ' + k['site'] for k in markers)}), and otherwise names a function "
            f"when it refuses, skips, stubs or drops it; its one template for a function it lowered "
            f"({LOWERED_TEMPLATE!r}, {CENSUS_REL}) matches {lowered} lines "
            "(straight-line.log-lowered-function-records). So the log does not even list the population, let "
            "alone its bodies. Object code, were any of the run's objects kept, is not the gate's input, and "
            "build/ is not a pinned input (observed 2026-09-26: build/aarch64-apple-darwin/stage1-std holds only "
            "a `dist` profile written 2026-09-25, after the 2026-09-16 run). The design gives no number for "
            "this population."),
        "unblock": (
            "commit, as gzip evidence under reports/, a per-function inventory of the Checkpoint A compile's "
            "gate-input bodies: a measurement build under native Targo build-tree ownership "
            "(`x.py build --stage 1 library/std`, LEDGER's Checkpoint A configuration, at the Checkpoint A "
            f"compiler {log['build_commit'][:12]} or a re-pinned one) with an always-on dump of each codegened "
            "function's VerifiableFunction (crates/trust-mir-extract's conversion of its runtime MIR) or of its "
            "per-instance runtime MIR; then add the classifier for this predicate over that inventory here and "
            "re-run --write. Until then E1.4.5's min(1,000, population) and K3's run set are undefined."),
        "design": read("straight-line.population",
                       lambda r: (f"cites {GATE_REL}:{r['value']} for the scope; the header sentence is at "
                                  f"{scope['lines']} here" if r.get("value") else "names this population "
                                  "(no number is given)")),
    })
    rows.append({
        "name": "straight-line.log-body-records", "value": sum(body_records.values()), "status": "measured",
        "predicate": (
            f"lines of the decompressed {LOG_REL} containing a body-print marker of the Checkpoint A plugin: the "
            "leading upper-case token of the first string literal of every `eprintln!` in "
            f"first-party/trust-cg {PLUGIN_SRC}*.rs (comments excluded) at the gitlink of the log's `build "
            "commit:` whose format string contains `:#?}`"),
        "markers": [f"{k['marker']} ({k['site']}): {body_records[k['marker']]} lines" for k in markers],
    })

    rows.append({
        "name": "straight-line.log-lowered-function-records", "value": lowered, "status": "measured",
        "predicate": (f"lines of the decompressed {LOG_REL} containing {LOWERED!r}, the fixed head of the "
                      f"plugin's only template that names a function it lowered ({LOWERED_TEMPLATE!r}, "
                      f"noop-precondition-check in {CENSUS_REL})"),
    })

    progs = [{"case": c["case"], "path": f"bridge_corpus/{c['path']}", "blob": head["blobs"].get(c["path"], "")}
             for c in head["cases"]]
    runs = len(head["cases"]) * len(head["opts"])
    rows.append({
        "name": "llvm-differential.programs", "value": len(head["programs"]), "status": "measured",
        "predicate": (
            f"distinct P such that `include_str!(\"bridge_corpus/P\")` occurs in the code (comments and string "
            f"contents excluded) of {HARNESS} at the trust-cg gitlink: the P2 bridge differential harness, whose "
            "header calls it \"the real two-compiler driver\". Each is the program of one `Case` of `corpus()`, "
            f"which `{CORPUS_TEST}` compiles with the LLVM backend (the oracle, `None`) and with the trust-cg "
            "backend (`Some(&dylib)`), runs and diffs at every opt level. The harness counts a trust-cg "
            "fail-closed as not a failure; E1.7.3's \"agrees on 100%\" is agreement on every program, so a "
            "refusal is not agreement."),
        "digest": head["digest"], "digest_rule": DIGEST_RULE,
        "opt_levels": head["opts"],
        "executes_only_on_x86_64_host": head["x86_only"],
        "subset_of": "llvm-differential.suite-programs",
        "e1_7_3": ("a measured SUBSET of E1.7.3's program set (llvm-differential.suite-programs, blocked): one "
                   "harness of the crate's differential suite, so a 100% agreement over this row is not E1.7.3's "
                   "pass"),
        "design": read("llvm-differential.programs",
                       lambda r: (f"says ~{r['value']} (from LEDGER:{ledger['line']}) [S]: not reproduced as a program "
                                  f"count - this harness has {len(head['programs'])} at the trust-cg pin and "
                                  f"{len(led['programs'])} at the pin LEDGER:{ledger['line']} was written against; "
                                  f"{len(led_tests['naming'])} is that pin's count of test FILES naming "
                                  "`codegen-backend` (ledger-pin rows)")),
        "files": progs,
    })
    rows.append({"name": "llvm-differential.corpus-cases", "value": len(head["cases"]), "status": "measured",
                 "predicate": "`Case { .. }` entries of `fn corpus()` in the harness, each with one `name` and one "
                              "`src: include_str!(..)`; names unique and no program shared by two Cases"})
    rows.append({"name": "llvm-differential.standalone-only-programs", "value": len(head["standalone_only"]),
                 "of": "llvm-differential.programs", "status": "measured",
                 "predicate": "harness programs included only outside `fn corpus()` (by the standalone "
                              "`*_is_supported_*` tests) and by no Case",
                 "files": [f"bridge_corpus/{p}" for p in head["standalone_only"]]})
    rows.append({"name": "llvm-differential.program-runs", "value": runs, "status": "measured",
                 "predicate": f"llvm-differential.corpus-cases x the opt levels of `for opt in [..]` in "
                              f"`{CORPUS_TEST}` ({', '.join(head['opts'])}); each run is one LLVM and one "
                              "trust-cg compile, link and execution"})
    rows.append({
        "name": "llvm-differential.differential-harness-programs", "value": len(head_tests["differential"]),
        "status": "measured",
        "predicate": (f"distinct P with `include_str!(\"bridge_corpus/P\")` in the code of any top-level "
                      f"{TESTS}*.rs whose file name contains `differential` (every harness that compiles a "
                      "bridge_corpus program with both backends and compares, each under its own contract: "
                      "fix_virtual_call_indirect_return_control.rs, for one, must make trust-cg refuse); a "
                      "superset of llvm-differential.programs"),
        "digest": head_tests["differential_digest"], "digest_rule": DIGEST_RULE,
        "subset_of": "llvm-differential.suite-programs",
        "files": [{"path": f"bridge_corpus/{t}", "blob": head_tests["blobs"][t], "harnesses": hs}
                  for t, hs in head_tests["differential"].items() if t not in set(head["programs"])],
        "files_note": "only the programs outside llvm-differential.programs are listed",
    })
    rows.append({"name": "bridge-corpus.files", "value": len(head_tests["corpus_files"]), "status": "measured",
                 "predicate": f"blobs under {CORPUS} at the trust-cg gitlink"})
    rows.append({"name": "bridge-corpus.included-by-no-test", "value": len(head_tests["not_included"]),
                 "of": "bridge-corpus.files", "status": "measured",
                 "predicate": f"bridge-corpus.files that no top-level {TESTS}*.rs include_str!s (comments "
                              "excluded): committed programs no harness runs",
                 "files": [f"bridge_corpus/{p}" for p in head_tests["not_included"]]})
    rows.append({
        "name": "llvm-differential.suite-programs", "status": "blocked",
        "predicate": (f"every distinct program source that any test of {PLUGIN} compiles with both the LLVM "
                      "backend (the oracle) and the trust-cg backend and compares, refusal controls included "
                      "(a test that requires trust-cg to refuse a program compiles it under both); E1.7.3's "
                      "\"exact program set counted at E0.12\" is this set"),
        "measured_lower_bounds": ["llvm-differential.differential-harness-programs",
                                  "llvm-differential.programs"],
        "drawn_from": "test-files-naming-codegen-backend",
        "blocked": (f"E1.7.3 consumes this row, and it cannot be enumerated statically. The crate's "
                    f"{len(head_tests['naming'])} backend-driving test files (test-files-naming-codegen-backend) "
                    "include LLVM differentials that build their program sources at run time (format! templates "
                    "around per-case bodies, e.g. tests/m51_signed_narrow_x86.rs `differential_case`), so no static "
                    "predicate enumerates the programs exactly; they must be captured while the tests run, and the "
                    "x86 differentials return before compiling on any host that is not x86_64. What IS measured "
                    "are lower bounds: every "
                    f"differential harness together names {len(head_tests['differential'])} bridge_corpus programs "
                    "(llvm-differential.differential-harness-programs), and the P2 harness's "
                    f"{len(head['programs'])} (llvm-differential.programs) are among them; the run-time programs of "
                    "tests such as tests/m51_signed_narrow_x86.rs are in neither. Until this row is measured, "
                    "E1.7.3's denominator is undefined: a 100% agreement over either lower bound is not E1.7.3's "
                    "pass"),
        "unblock": ("add a source-capture instrument to the crate's shared test support (record every source "
                    "compiled under both backends, with its opt level and whether the test requires trust-cg to "
                    "refuse it) and run the suite on an x86_64 host with the backend built; publish the capture "
                    "as gzip evidence and count it here"),
        "design": read("llvm-differential.suite-programs",
                       lambda r: "consumes this row as E1.7.3's exact program set"),
    })

    lp = ledger["commit"]
    rows.append({"name": "ledger-pin.llvm-differential.programs", "value": len(led["programs"]),
                 "status": "measured",
                 "predicate": (f"llvm-differential.programs' predicate at trust-cg {led['rev']}, the gitlink of "
                               f"superproject {lp}, the commit that introduced LEDGER's {LEDGER_CLAIM!r}"),
                 "digest": led["digest"], "digest_rule": DIGEST_RULE, "corpus_cases": len(led["cases"])})
    rows.append({"name": "ledger-pin.test-files", "value": len(led_tests["top"]), "status": "measured",
                 "predicate": f"`.rs` blobs directly in {TESTS} at trust-cg {led['rev']}"})
    rows.append({
        "name": "ledger-pin.test-files-naming-codegen-backend", "value": len(led_tests["naming"]),
        "of": "ledger-pin.test-files", "status": "measured",
        "predicate": (f"ledger-pin.test-files whose text contains `codegen-backend` anywhere: {len(led_tests['naming'])} "
                      f"equals LEDGER:{ledger['line']}'s \"~129\": the number is reproduced only under this different "
                      "predicate, test FILES that drive the backend rather than programs, and only by the "
                      "hypothesis that this is how LEDGER counted [H]; these files include tests that are not LLVM "
                      "differentials. naming_without_llvm lists the "
                      "files whose text never mentions `llvm` in any case: a lexical indication, not a proof, that "
                      "a file does not compare against LLVM (global_asm_refusal_x86.rs, for one, is a refusal "
                      "test: \"`global_asm!` FAILS CLOSED through the bridge\")"),
        "excluded": sorted(set(led_tests["top"]) - set(led_tests["naming"])),
        "naming_without_llvm": led_tests["no_llvm"],
    })
    rows.append({"name": "test-files", "value": len(head_tests["top"]), "status": "measured",
                 "predicate": f"`.rs` blobs directly in {TESTS} at the trust-cg gitlink"})
    rows.append({"name": "test-files-naming-codegen-backend", "value": len(head_tests["naming"]),
                 "of": "test-files", "status": "measured",
                 "predicate": "test-files whose text contains `codegen-backend` anywhere (the ledger-pin predicate "
                              "at the current pin)",
                 "excluded": sorted(set(head_tests["top"]) - set(head_tests["naming"])),
                 "naming_without_llvm": head_tests["no_llvm"]})
    return rows


def explain(m: dict, rows: list[dict]) -> list[str]:
    v = {r["name"]: r.get("value") for r in rows}
    head, led, ledger = m["harness"], m["ledger_harness"], m["ledger"]
    return [
        "How this measurement compares with the design:",
        "* straight-line.population is BLOCKED: the committed Checkpoint A evidence carries no function body",
        f"  (straight-line.log-body-records = {v['straight-line.log-body-records']}). The design gives no number for it.",
        f"  Its predicate is the M-POS SCOPE header ({GATE_REL}:{m['scope']['lines']}), which the design",
        "  cites as the definition; the implementation now admits more than the header states.",
        f"* LEDGER:{ledger['line']}'s \"~129 programs\" (design Stage 0.5) is NOT a program count. The harness has",
        f"  llvm-differential.programs = {v['llvm-differential.programs']} at trust-cg {head['rev'][:12]} and "
        f"{v['ledger-pin.llvm-differential.programs']} at trust-cg {led['rev'][:12]},",
        f"  the pin LEDGER:{ledger['line']} was written against (superproject {ledger['commit'][:12]}). At that pin",
        f"  {v['ledger-pin.test-files-naming-codegen-backend']} of {v['ledger-pin.test-files']} test files name "
        "`codegen-backend`: the \"~129\" is reproduced only under a different",
        "  predicate, as a count of test FILES, and only by the hypothesis [H] that LEDGER counted files.",
        "* E1.7.3's exact program set is llvm-differential.suite-programs: every program any test of the crate",
        "  compiles under both backends and compares. It is BLOCKED (some tests build their programs at run time;",
        "  the x86 differentials execute only on an x86_64 host), so E1.7.3's denominator is undefined until it is",
        "  measured. Measured SUBSETS (lower bounds, never the set): every differential harness together names",
        f"  {v['llvm-differential.differential-harness-programs']} corpus programs, and the P2 harness's "
        f"llvm-differential.programs = {v['llvm-differential.programs']}",
        f"  programs ({v['llvm-differential.program-runs']} program x opt-level runs) are among them.",
        f"  {v['bridge-corpus.included-by-no-test']} of {v['bridge-corpus.files']} corpus files run in no test.",
        "  The P2 harness targets x86_64-apple-darwin and executes only on an x86_64 host; Checkpoint A is AArch64.",
    ]


def render(m: dict, rows: list[dict], measured_at: str) -> str:
    log, ledger = m["log"], m["ledger"]
    out = [
        f"# E0.12 denominators `{KEY}`: the Checkpoint A straight-line population (E1.4.5, K3) and the exact",
        "# program set of the LLVM differential LEDGER:42 calls \"~129\" (E1.7.3).",
        "#",
        f"# GENERATED by {SCRIPT_REL} --write; do not edit. Its --check re-measures from git",
        "# objects and fails when any datum differs, except measured_at_commit and each row's `design` reading",
        "# (the design text is compared, not measured). A `blocked` row has no value, and says why and what unblocks it.",
        "# Design of record: docs/design/2026-09-16-trust-core-architecture.md §5.2 Stage 0.5 (exit E0.12).",
        "#",
        *[f"# {line}".rstrip() for line in explain(m, rows)],
        "",
        f"schema = {q(SCHEMA)}",
        f"key = {q(KEY)}",
        f"design = {q(C.DESIGN_REL)}",
        f"script = {q(SCRIPT_REL)}",
        f"exit = {q('E0.12')}",
        "consumers = " + tv([
            "E1.4.5: at least min(1,000, straight-line.population) Checkpoint A functions Certified by reflection",
            "K3 (§5.1 item 5, Stage 0.3): the reflection cost probe runs over straight-line.population",
            "K6 (§5.1 item 6): the M-POS checker on LLVM -O2 output for the same functions",
            "E1.7.3: the LLVM differential over llvm-differential.suite-programs (BLOCKED) agrees on 100%; "
            "llvm-differential.programs and llvm-differential.differential-harness-programs are measured subsets "
            "of that set (lower bounds), not the set",
        ]),
        "# The pin: the superproject commit this record was measured at. scripts/trust_core/denominators.py",
        "# re-measures every row at it (--rev); this script's own --check measures at --rev (default HEAD)",
        "# and ignores this line, so it also says whether HEAD still gives the record.",
        f"measured_at_commit = {q(measured_at)}",
        "",
        "[inputs.checkpoint_a_log]",
        f"path = {q(LOG_REL)}",
        f"blob = {q(log['blob'])}",
        f"decompressed_sha256 = {q('sha256:' + log['sha256'])}",
        f"decompressed_lines = {log['lines']}",
        f"digest_recorded_by = {q(CENSUS_REL)}",
        f"build_commit = {q(log['build_commit'])}",
        f"plugin = {q('first-party/trust-cg ' + m['checkpoint_plugin'] + ' (the gitlink at build_commit)')}",
        "",
        "[inputs.mpos_gate]",
        f"path = {q(GATE_REL)}",
        f"blob = {q(m['scope']['blob'])}",
        f"scope_lines = {q(m['scope']['lines'])}",
        "",
        "[inputs.trust_cg]",
        f"revision = {q(m['harness']['rev'])}",
        f"what = {q('first-party/trust-cg at the gitlink of the measured superproject revision, read from the modules object store')}",
        f"harness = {q(HARNESS)}",
        f"harness_blob = {q(m['harness']['harness_blob'])}",
        "",
        "[inputs.ledger]",
        f"path = {q(LEDGER_REL)}",
        f"blob = {q(ledger['blob'])}",
        f"claim = {q(LEDGER_CLAIM)}",
        f"claim_line = {ledger['line']}",
        f"introduced_by = {q(ledger['commit'])}",
        f"trust_cg_at_introduction = {q(m['ledger_harness']['rev'])}",
        "",
    ]
    for row in rows:
        out.append("[[row]]")
        for k, val in row.items():
            if k == "files" and not val:
                out.append("files = []")
                continue
            out.append(f"{tk(k)} = {tv(val)}")
        out.append("")
    return "\n".join(out)


def measured_content(text: str) -> dict:
    data = tomllib.loads(text)
    data.pop("measured_at_commit", None)
    for row in data.get("row", []):
        row.pop("design", None)
    return data


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n", 1)[0])
    parser.add_argument("--repo", type=Path, default=C.REPO_ROOT, help="the superproject (default: this checkout)")
    parser.add_argument("--rev", default="HEAD", help="the superproject revision to measure (default HEAD)")
    parser.add_argument("--record", type=Path, help=f"the record (default {RECORD_REL} in --repo)")
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--write", action="store_true", help="rewrite the record from this measurement")
    mode.add_argument("--check", action="store_true", help="fail unless the record equals this measurement")
    parser.add_argument("--list", action="store_true", help="print every row's list")
    args = parser.parse_args(argv)
    repo, rev = args.repo.resolve(), args.rev
    record = args.record or repo / RECORD_REL
    findings = C.Findings()
    try:
        commit = (C.git(repo, "rev-parse", "--verify", f"{rev}^{{commit}}") or "").strip()
        if not C.HEX40.match(commit):
            raise Fatal(f"{repo}: {rev} is not a commit")
        log = measure_log(findings, repo, commit)
        if (C.git(repo, "cat-file", "-t", log["build_commit"]) or "").strip() != "commit":
            raise Fatal(f"the log's build commit {log['build_commit']} is not in {repo}")
        plugin, _ = trust_cg_at(repo, log["build_commit"])
        markers = body_print_markers(findings, plugin)
        if not markers:
            findings.add("BODY-SITE", f"trust-cg {plugin.rev[:12]} has no body-printing eprintln; the log search is vacuous")
        head_tree, head_store = trust_cg_at(repo, commit)
        ledger = ledger_facts(findings, repo, commit)
        led_tree, led_store = trust_cg_at(repo, ledger["commit"])
        m = {
            "log": log, "markers": markers, "checkpoint_plugin": plugin.rev,
            "scope": measure_scope(findings, repo, commit),
            "harness": measure_harness(findings, head_tree, head_store, f"trust-cg {head_tree.rev[:12]}"),
            "tests": measure_tests(head_tree, head_store),
            "_runtime_example": check_runtime_example(findings, head_tree),
            "ledger": ledger,
            "ledger_harness": measure_harness(findings, led_tree, led_store, f"trust-cg {led_tree.rev[:12]}"),
            "ledger_tests": measure_tests(led_tree, led_store),
            "design": design_readings(repo, commit),
        }
    except Fatal as error:
        print(f"{KEY}: {error}", file=sys.stderr)
        return 2
    rows = build_rows(m)
    text = render(m, rows, commit)
    try:
        tomllib.loads(text)
    except tomllib.TOMLDecodeError as error:  # pragma: no cover - a renderer defect
        findings.add("RECORD", f"the rendered record is not TOML: {error}")

    print(f"{KEY}: superproject {commit}; trust-cg {m['harness']['rev'][:12]}; Checkpoint A plugin "
          f"{m['checkpoint_plugin'][:12]}; LEDGER pin trust-cg {m['ledger_harness']['rev'][:12]}")
    for row in rows:
        value = row.get("value", "-")
        of = f" of {row['of']}" if "of" in row else ""
        print(f"  {row['name']:<50} {str(value):>5}{of}  [{row['status']}]")
        for note in row.get("design", []):
            print(f"      {note}")
        if row["status"] == "blocked":
            print(f"      blocked: {row['blocked']}\n      unblock: {row['unblock']}")
        if args.list:
            for item in row.get("markers", []):
                print(f"      {item}")
            for item in row.get("excluded", []):
                print(f"      excluded {item}")
            for item in row.get("files", []):
                if isinstance(item, dict):
                    print("      " + "  ".join(f"{k}={v}" for k, v in item.items()))
                else:
                    print(f"      {item}")

    status = 0
    if args.write and not findings.violations:
        record.parent.mkdir(parents=True, exist_ok=True)
        record.write_text(text, encoding="utf-8")
        print(f"{KEY}: wrote {record}")
    elif args.check:
        try:
            committed = measured_content(record.read_text(encoding="utf-8"))
        except (OSError, tomllib.TOMLDecodeError) as error:
            findings.add("RECORD", f"{record}: {error}")
            committed = None
        if committed is not None and committed != measured_content(text):
            findings.add("RECORD", f"{record} differs from a re-measurement at {commit}; re-run with --write and review the diff")
        elif committed is not None:
            print(f"{KEY}: {record} matches the re-measurement")
    for violation in findings.violations:
        print(violation, file=sys.stderr)
        status = 1
    return status


if __name__ == "__main__":
    sys.exit(main())
