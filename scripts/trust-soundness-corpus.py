#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Licensed under the Apache License, Version 2.0
"""Run tests/trust-soundness-corpus against every verdict-issuing verifier.

SBC M0.5 (docs/plans/2026-10-08-soundness-by-construction.md, R8): each entry is
a program whose claimed property is FALSE (the reproducer), a native-execution
witness that shows it is false, and a correct twin. This runner asks every
verifier that can express an entry for a verdict on both, and reports

    proved / refused / error / skipped     per entry and verifier

plus totals. A reproducer PROVED is a false proof (FALSE-PROVED) unless the entry
lists it under `known_open` for that verifier (KNOWN-FALSE-PROVED: still a false
proof, shown apart and rejected by --strict). A verifier that cannot be found or built
is SKIPPED with the reason; a skip is never a pass.

FAIL-CLOSED. A verdict is REFUSED only when the verifier answered and said no: a
trustc row that carries the claim and is not proved, a Clean `verification: FAILED`
line, a trust-vc or trust-wp verdict parsed from its own output. A missing, crashing
or timed-out verifier, a compile with no rows, and an obligation anchor that matches
no row are ERROR, never a refusal. Under --strict the exit status is 1 when any
requested cell is FALSE-PROVED, KNOWN-FALSE-PROVED, XFIXED, SKIPPED, ERROR (other than a refusal the
entry whitelists with its exact text), TWIN-LOST (not known), or any witness is not
confirmed, and when no verifier judged any reproducer (every cell skipped or n/a):
a run that judged nothing is not a pass. `--self-test` runs the runner against fake
verifiers and checks that.

The corpus blocks no push or landing yet: its only --strict caller is the
required=false slow row `oracle.soundness-corpus` (tests/run_trust_comprehensive_harness.sh),
in no push profile and no pre-push lane. That is not on yet: a defect, not policy
(docs/STATUS.md "Not on yet"; docs/PLAN.md PKG-CORE3, whose exit is this runner's
--strict passing on a stage 1 of main). See the corpus README.

Verifiers (each one optional; configure by environment):
  trustc-default    TRUSTC (default: the atpkg store's current trustc, else PATH),
                    -Ztrust-verify=on
  trustc-advisory   the same with -Ztrust-policy=advisory (the lane that elides)
  trustc-certify    the same with -Ztrust-policy=certify (the release lane;
                    `targo trust check/certify` drive this compiler lane)
  trust-wp          TRUST_WP_DIR, a trust-wp checkout (its adversarial harness
                    builds trust-wp-driver); TRUST_WP_PYTHON (>= 3.11);
                    TRUST_WP_TOOLCHAIN_BIN, the Trust toolchain its harness builds
                    with (default: the directory of the selected trustc)
  trust-vc-syn      TRUST_VC_DIR, a trust-vc checkout (adapter crate built
                    against trust-vc-core's verify_function_from_file), or a built
                    adapter in TRUST_VC_SYN_ADAPTER
  trust-vc-mir      TRUST_VC_MIR_DRIVER, a built trust-vc-driver (needs rustc-driver)
  clean-external    CLEAN_BIN, a `clean` built with --features carcara-verify
Witnesses: Rust witnesses are compiled with TRUSTC -Ztrust-verify=off and run; an
SMT witness is AY_BIN (`ay`) answering sat with a model that an independent
evaluator in this file checks against every assertion (see `smt_model_check`).
"""

from __future__ import annotations

import argparse
import json
import math
import os
import re
import shutil
import signal
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
CORPUS = ROOT / "tests" / "trust-soundness-corpus"
ENTRIES = CORPUS / "entries"
SELFTEST = CORPUS / "selftest"
STORE_BIN = Path.home() / "Library/Application Support/aterm/pkg/store/trust/current/bin"

TRUSTC_LANES = {
    "trustc-default": [],
    "trustc-advisory": ["-Ztrust-policy=advisory"],
    "trustc-certify": ["-Ztrust-policy=certify"],
}
ALL_VERIFIERS = list(TRUSTC_LANES) + ["trust-wp", "trust-vc-syn", "trust-vc-mir", "clean-external"]
# Which verifiers can read which entry language at all. Anything else is
# not-applicable (n/a), which is neither a pass nor a skip. The trust-vc THIR lane
# (trust-vc-mir) verifies only functions that carry trust_vc contract markers, so a
# plain-Rust entry is never its target: it is statically n/a there, and never asked.
LANG_VERIFIERS = {
    "rust": list(TRUSTC_LANES) + ["trust-vc-syn"],
    "creusot": ["trust-wp"],
    "trust-vc": ["trust-vc-syn", "trust-vc-mir"],
    "smt": ["clean-external"],
}
SIDES = ("reproducer", "twin")

PROVED, REFUSED, ERROR, SKIPPED, NA = "proved", "refused", "error", "skipped", "n/a"
# Live compiler output uses exactly Outcome::as_str in
# crates/trust-types/src/outcome.rs. This is not a saved-report alias reader.
TRUSTC_ROW_OUTCOMES = frozenset({
    "proved", "failed", "unknown", "timeout", "runtime_checked", "skipped",
    "unsupported", "canceled", "rejected",
})
# The detail of an ERROR that is a verifier's own answer refusing a construct it does
# not support. Only such a detail can match an entry's `expected_refusal` (classify):
# a crash or a garbled answer whose output happens to contain the same text cannot.
CONSTRUCT_REFUSAL = "construct refusal: "
SHORT = {PROVED: "P", REFUSED: "R", ERROR: "E", SKIPPED: "S", NA: "-"}

# Cell classes. Known-open markers explain diagnostics; they cannot license a
# false proof. Recorded twin precision losses retain their separate policy.
STRICT_RED = {"FALSE-PROVED", "KNOWN-FALSE-PROVED", "XFIXED", "SKIPPED", "ERROR", "ERROR(known-open)", "TWIN-LOST"}
NOT_A_PASS = {"KNOWN-FALSE-PROVED", "TWIN-LOST(known)"}
PASSING = {"ok", "ok(refusal)", "ok(nif)", "ok(nif-refusal)", "n/a"}

# Every subprocess is capped by this when set (--timeout): a hanging verifier must
# end as an ERROR within a bounded time, never as a hang of the gate.
TIMEOUT_CAP: int | None = None


def log(msg: str) -> None:
    print(msg, file=sys.stderr, flush=True)


def run(argv, cwd=None, env=None, timeout=600, stdin=None):
    """(rc, stdout, stderr). rc is None when the program did not finish (timeout)
    or could not be started; the reason is appended to stderr."""
    if TIMEOUT_CAP:
        timeout = min(timeout, TIMEOUT_CAP)
    try:
        p = subprocess.Popen(
            argv, cwd=cwd, env=env, stdin=subprocess.PIPE if stdin is not None else subprocess.DEVNULL,
            stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, start_new_session=True,
        )
    except OSError as e:
        return None, "", f"[could not start {argv[0]}: {e}]"
    try:
        out, err = p.communicate(input=stdin, timeout=timeout)
        return p.returncode, out, err
    except subprocess.TimeoutExpired:
        # Kill the whole process group: a verifier that forks a solver must not
        # outlive its own timeout.
        try:
            os.killpg(p.pid, signal.SIGKILL)
        except OSError:
            pass
        out, err = p.communicate()
        return None, out or "", (err or "") + f"\n[timeout after {timeout}s]"


def clip(s: str, n: int = 200) -> str:
    s = " ".join(str(s).split())
    return s if len(s) <= n else s[: n - 3] + "..."


def is_executable(path) -> bool:
    return bool(path) and os.path.isfile(path) and os.access(path, os.X_OK)


# ---------------------------------------------------------------------------
# Entries
# ---------------------------------------------------------------------------


class AnchorError(Exception):
    pass


def load_entries(filter_re: str | None = None):
    entries = []
    for path in sorted(ENTRIES.glob("*/entry.json")):
        e = json.loads(path.read_text())
        e["_dir"] = path.parent
        if e.get("id") != path.parent.name:
            raise SystemExit(f"{path}: id {e.get('id')!r} != directory name")
        if filter_re and not re.search(filter_re, e["id"]):
            continue
        entries.append(e)
    return entries


def validate_entries(entries) -> list[str]:
    """Static checks an entry must pass before any verifier is asked. Each problem
    is returned as text; the runner refuses to run on any (they are never a pass)."""
    problems = []
    smt_twins = {}
    for e in entries:
        eid = e["id"]
        if e["lang"] not in LANG_VERIFIERS:
            problems.append(f"{eid}: unknown lang {e['lang']!r}")
            continue
        for key in ("known_open", "known_twin_lost", "expected_refusal", "expect"):
            for v in e.get(key, {}):
                if v not in ALL_VERIFIERS:
                    problems.append(f"{eid}: {key} names unknown verifier {v!r}")
        for v, sides in e.get("expected_refusal", {}).items():
            for side, text in sides.items():
                if side not in SIDES or not isinstance(text, str) or len(text) < 12:
                    problems.append(f"{eid}: expected_refusal[{v}][{side}] must be the exact refusal text")
                if side == "twin" and expectation(e, v, "twin") != "not-in-fragment":
                    problems.append(f"{eid}: a twin refusal is whitelisted for {v} but its twin is expected proved")
        if e["lang"] == "smt":
            for side in SIDES:
                if not (e["_dir"] / e[side]["cert"]).exists():
                    problems.append(f"{eid}: {side} certificate {e[side]['cert']} is missing")
            tw = (e["_dir"] / e["twin"]["cert"]).read_bytes() if (e["_dir"] / e["twin"]["cert"]).exists() else b""
            if tw in smt_twins:
                problems.append(f"{eid}: twin is byte-identical to {smt_twins[tw]}'s twin")
            smt_twins[tw] = eid
            construct = e.get("construct")
            if not construct:
                problems.append(f"{eid}: an SMT entry names its triggering `construct`")
            else:
                for side in SIDES:
                    problem = json.loads((e["_dir"] / e[side]["cert"]).read_text())["problem"]
                    if construct not in problem:
                        problems.append(f"{eid}: the {side} problem does not contain the construct {construct!r}")
        if e["lang"] in ("rust", "trust-vc") and any(
            v in TRUSTC_LANES for v in LANG_VERIFIERS[e["lang"]]
        ):
            for side in SIDES:
                spec = e[side]
                if spec.get("mode", "obligation") != "obligation":
                    continue
                ob = spec.get("obligation", {})
                if not ob.get("kind") or not (ob.get("at") or ob.get("message")):
                    problems.append(f"{eid}: {side} obligation needs `kind` and `at` or `message` (an anchor)")
                    continue
                try:
                    anchor_of(e, side)
                except AnchorError as err:
                    problems.append(str(err))
        w = e.get("witness")
        if not isinstance(w, dict):
            problems.append(f"{eid}: no witness")
        elif e["lang"] == "smt":
            if w.get("solver") != "ay" or w.get("expect") != "sat":
                problems.append(f"{eid}: an SMT witness is `solver: ay`, `expect: sat` (a model check)")
        elif not w.get("main") or not w.get("observed") or not isinstance(w.get("exit"), int):
            # An empty `observed` is in every output and a missing `exit` matches any
            # status, so such a witness would confirm whatever the binary did.
            problems.append(f"{eid}: a witness needs `main`, a non-empty `observed` and an integer `exit`")
        has_control = any(
            expectation(e, v, "twin") == "proved" for v in LANG_VERIFIERS[e["lang"]]
        )
        if not has_control and not e.get("no_control"):
            problems.append(f"{eid}: no verifier expects its twin proved; give it a control or a `no_control` reason")
    return problems


def expectation(entry, verifier, side):
    """`proved`, `not-proved` or `not-in-fragment` for one side of one entry."""
    lang_ok = verifier in LANG_VERIFIERS.get(entry["lang"], [])
    if not lang_ok:
        return NA
    exp = entry.get("expect", {}).get(verifier, {})
    if exp == "n/a" or exp.get("n/a"):
        return NA
    if side == "reproducer":
        return exp.get("reproducer", "not-proved")
    return exp.get("twin", entry.get("expect_default_twin", "proved"))


def na_reason(entry, verifier):
    exp = entry.get("expect", {}).get(verifier, {})
    return exp.get("n/a") if isinstance(exp, dict) else None


# ---------------------------------------------------------------------------
# Obligation anchors (shared with the self-test's fake compilers)
# ---------------------------------------------------------------------------


def side_source(entry, side):
    return entry[side].get("source", entry["source"])


def line_of(entry, spec, text):
    """The 1-based line of the first `text` at or after `fn <function>` in the source."""
    src = spec.get("source", entry["source"])
    lines = (entry["_dir"] / src).read_text().splitlines()
    start = next((i for i, l in enumerate(lines) if re.search(rf"\bfn {re.escape(spec['function'])}\b", l)), None)
    if start is None:
        raise AnchorError(f"{entry['id']}: fn {spec['function']} not found in {src}")
    for i in range(start, len(lines)):
        if text in lines[i]:
            return i + 1
    raise AnchorError(f"{entry['id']}: `{text}` not found after fn {spec['function']} in {src}")


def anchor_of(entry, side):
    """The resolved anchor of one side: kind, and line+file (from `at`) and/or message."""
    spec = entry[side]
    want = dict(spec.get("obligation", {}))
    if want.get("at"):
        want["line"] = line_of(entry, spec, want["at"])
        want["file"] = side_source(entry, side)
    return want


def row_kind_matches(row, kind):
    k = str(row.get("kind", ""))
    return not kind or k == kind or k.startswith(kind + ":")


def row_message(row):
    tk = row.get("typed_kind") or {}
    msg = (tk.get("Assertion") or {}).get("message") if isinstance(tk, dict) else None
    return f"{msg or ''} {row.get('description', '')}"


def row_matches(row, anchor):
    if not row_kind_matches(row, anchor.get("kind")):
        return False
    loc = row.get("location") or {}
    if anchor.get("line"):
        if loc.get("line_start") != anchor["line"]:
            return False
        if Path(str(loc.get("file", ""))).name != Path(anchor["file"]).name:
            return False
    if anchor.get("message") and anchor["message"] not in row_message(row):
        return False
    return True


# ---------------------------------------------------------------------------
# Witness
# ---------------------------------------------------------------------------


def run_witness(entry, trustc, work: Path, ay_bin):
    w = entry.get("witness")
    if not w:
        return {"status": "missing", "detail": "entry has no witness"}
    if entry["lang"] == "smt":
        return smt_witness(entry, ay_bin, work)
    if not trustc:
        return {"status": SKIPPED, "detail": "no trustc"}
    if w.get("target_arch") and os.uname().machine not in (w["target_arch"], "arm64"):
        return {"status": SKIPPED, "detail": f"witness needs {w['target_arch']}"}
    src = entry["_dir"] / w["main"]
    exe = work / f"{entry['id']}-witness"
    aux_flags = build_aux(entry, trustc, work, verify=False)
    if isinstance(aux_flags, str):
        return {"status": "error", "detail": aux_flags}
    rc, out, err = run(
        [trustc, "-Ztrust-verify=off", "--edition", entry.get("edition", "2021"),
         "-Coverflow-checks=on", "-Copt-level=0", *entry.get("witness_flags", []),
         *aux_flags, "-o", str(exe), str(src)],
        cwd=work, timeout=300,
    )
    if rc != 0 or not exe.exists():
        return {"status": "error", "detail": f"witness did not build (exit {rc}): {clip(err[-400:], 300)}"}
    rc, out, err = run([str(exe)], cwd=work, timeout=60)
    text = out + err
    want_rc = w.get("exit")
    observed = w.get("observed", "")
    ok = rc is not None and (want_rc is None or rc == want_rc) and observed in text
    return {
        "status": "ok" if ok else "MISMATCH",
        "detail": f"exit {rc}; " + (f"observed {observed!r}" if ok else f"output {clip(text[-300:], 300)!r}"),
    }


def build_aux(entry, trustc, work: Path, verify: bool):
    """Build an entry's auxiliary crates; return the `--extern`/-L flags or an error."""
    flags = []
    for aux in entry.get("aux", []):
        out = work / f"lib{aux['crate']}.rlib"
        rc, _o, err = run(
            [trustc, "--crate-type", "rlib", "--crate-name", aux["crate"], "--edition",
             entry.get("edition", "2021"), "-Ztrust-verify=off", "-Zalways-encode-mir",
             "-Coverflow-checks=on", "-o", str(out), str(entry["_dir"] / aux["file"])],
            cwd=work, timeout=300,
        )
        if rc != 0:
            return f"aux crate {aux['crate']} did not build (exit {rc}): {clip(err[-300:])}"
        flags += ["--extern", f"{aux['crate']}={out}", "-L", str(work)]
    return flags


# ---------------------------------------------------------------------------
# SMT witness: ay's model, checked by an independent evaluator
# ---------------------------------------------------------------------------
#
# ay answering `sat` is ay's word. The witness asks ay for a model after every
# check-sat and evaluates the assertions in scope there (plus the check's
# assumptions) under that model with the small evaluator below, which shares no
# code with ay. It covers what the corpus scripts use: Bool and Int, declare-fun /
# declare-const, define-fun with lexical scoping (a parameter never captures a free
# symbol of a body it calls), let, `!` annotations, push/pop, check-sat-assuming,
# `;` comments ending at LF or CR, and quoted symbols.
#
# Where ay is more permissive than SMT-LIB, the evaluator takes ay's reading, which
# is the reading under which the problem is satisfiable: a user declaration named
# like a Core symbol (`and`, `ite`, `|false|`) is a user function and takes
# precedence over the built-in of that name; a quoted symbol spelling a Core symbol
# (`|false|`) is a distinct user symbol; and a `:named` label that repeats a
# declared constant's name does not rebind it. A symbol the model does not define
# is an error, never a default.


class SmtError(Exception):
    pass


CORE = {"true", "false", "not", "and", "or", "xor", "=>", "=", "distinct", "ite",
        "+", "-", "*", "div", "mod", "abs", "<", "<=", ">", ">=", "let", "!"}


def smt_tokens(text: str):
    i, n = 0, len(text)
    while i < n:
        c = text[i]
        if c in " \t\r\n":
            i += 1
        elif c == ";":
            while i < n and text[i] not in "\r\n":
                i += 1
        elif c in "()":
            yield c
            i += 1
        elif c == "|":
            j = text.index("|", i + 1)
            name = text[i + 1: j]
            # |x| is x, except a quoted spelling of a Core symbol (ay's reading).
            yield ("|" + name + "|") if name in CORE else name
            i = j + 1
        elif c == '"':
            j = i + 1
            while j < n and not (text[j] == '"' and text[j + 1: j + 2] != '"'):
                j += 2 if text[j] == '"' else 1
            yield ("str", text[i + 1: j])
            i = j + 1
        else:
            j = i
            while j < n and text[j] not in " \t\r\n();|\"":
                j += 1
            yield text[i:j]
            i = j


def smt_parse(text: str):
    stack, out = [[]], None
    for t in smt_tokens(text):
        if t == "(":
            stack.append([])
        elif t == ")":
            if len(stack) == 1:
                raise SmtError("unbalanced )")
            top = stack.pop()
            stack[-1].append(top)
        else:
            stack[-1].append(t)
    if len(stack) != 1:
        raise SmtError("unbalanced (")
    out = stack[0]
    return out


class SmtFun:
    def __init__(self, params, body, scope, model_fun=False):
        self.params, self.body, self.scope, self.model_fun = params, body, scope, model_fun


def smt_eval(t, env, globals_, model):
    """Evaluate term t. env: local bindings (name -> value). globals_: the frozen
    global symbol table of the definition site (name -> ('decl', arity) | SmtFun)."""
    if isinstance(t, str):
        if t in env:
            return env[t]
        if t in globals_:
            g = globals_[t]
            if isinstance(g, SmtFun):
                return smt_apply(t, g, [], globals_, model)
            if t not in model:
                raise SmtError(f"the model has no value for {t}")
            return smt_apply(t, model[t], [], globals_, model)
        if t == "true":
            return True
        if t == "false":
            return False
        if re.fullmatch(r"\d+", t):
            return int(t)
        raise SmtError(f"unknown symbol {t}")
    if isinstance(t, tuple):
        raise SmtError("string literals are not supported")
    head, args = t[0], t[1:]
    if head == "let":
        new = dict(env)
        for name, val in args[0]:
            new[name] = smt_eval(val, env, globals_, model)
        return smt_eval(args[1], new, globals_, model)
    if head == "!":
        return smt_eval(args[0], env, globals_, model)
    if isinstance(head, list) and head and head[0] == "_":
        raise SmtError(f"indexed identifiers are not supported: {head}")
    if isinstance(head, str) and head not in env and head in globals_:
        g = globals_[head]
        vals = [smt_eval(a, env, globals_, model) for a in args]
        if isinstance(g, SmtFun):
            return smt_apply(head, g, vals, globals_, model)
        if head not in model:
            raise SmtError(f"the model has no value for {head}")
        return smt_apply(head, model[head], vals, globals_, model)
    if head == "ite":
        return smt_eval(args[1] if smt_eval(args[0], env, globals_, model) else args[2], env, globals_, model)
    vals = [smt_eval(a, env, globals_, model) for a in args]
    if head == "not":
        return not vals[0]
    if head == "and":
        return all(vals)
    if head == "or":
        return any(vals)
    if head == "xor":
        r = False
        for v in vals:
            r ^= bool(v)
        return r
    if head == "=>":
        r = vals[-1]
        for v in reversed(vals[:-1]):
            r = (not v) or r
        return r
    if head == "=":
        return all(a == vals[0] for a in vals[1:])
    if head == "distinct":
        return len(set(vals)) == len(vals)
    if head == "+":
        return sum(vals)
    if head == "-":
        return -vals[0] if len(vals) == 1 else vals[0] - sum(vals[1:])
    if head == "*":
        r = 1
        for v in vals:
            r *= v
        return r
    if head in ("div", "mod"):
        a, b = vals
        if b == 0:
            raise SmtError("division by zero is uninterpreted")
        q = a // b if b > 0 else -(a // -b)
        return q if head == "div" else a - b * q
    if head == "abs":
        return abs(vals[0])
    if head in ("<", "<=", ">", ">="):
        op = {"<": lambda a, b: a < b, "<=": lambda a, b: a <= b, ">": lambda a, b: a > b, ">=": lambda a, b: a >= b}[head]
        return all(op(vals[i], vals[i + 1]) for i in range(len(vals) - 1))
    raise SmtError(f"unsupported operator {head}")


def smt_apply(name, fun: SmtFun, vals, globals_, model):
    if len(vals) != len(fun.params):
        raise SmtError(f"{name} applied to {len(vals)} argument(s), takes {len(fun.params)}")
    env = dict(zip(fun.params, vals))
    # A model function's body is read over Core and its own parameters only; a
    # problem's define-fun over the symbols in scope where it was defined.
    scope = {} if fun.model_fun else fun.scope
    return smt_eval(fun.body, env, scope, model)


def smt_checks(problem: str):
    """[(assertions, assumptions, globals)] for each check-sat / check-sat-assuming."""
    scopes = [{"globals": {}, "asserts": []}]
    checks = []

    def globals_now():
        g = {}
        for s in scopes:
            g.update(s["globals"])
        return g

    for cmd in smt_parse(problem):
        if not isinstance(cmd, list) or not cmd:
            raise SmtError(f"not a command: {cmd}")
        op = cmd[0]
        if op in ("set-logic", "set-option", "set-info", "get-model", "get-info", "exit", "get-value"):
            continue
        if op == "declare-const":
            scopes[-1]["globals"][cmd[1]] = ("decl", 0)
        elif op == "declare-fun":
            scopes[-1]["globals"][cmd[1]] = ("decl", len(cmd[2]))
        elif op == "define-fun":
            params = [p[0] for p in cmd[2]]
            scopes[-1]["globals"][cmd[1]] = SmtFun(params, cmd[4], globals_now())
        elif op == "assert":
            term = cmd[1]
            g = globals_now()
            for name, sub in smt_named(term):
                if name not in g:  # a label repeating a declared name does not rebind it
                    scopes[-1]["globals"][name] = SmtFun([], sub, g)
            scopes[-1]["asserts"].append((term, g))
        elif op == "push":
            for _ in range(int(cmd[1]) if len(cmd) > 1 else 1):
                scopes.append({"globals": {}, "asserts": []})
        elif op == "pop":
            for _ in range(int(cmd[1]) if len(cmd) > 1 else 1):
                if len(scopes) == 1:
                    raise SmtError("pop below the base scope")
                scopes.pop()
        elif op == "check-sat":
            checks.append(([a for s in scopes for a in s["asserts"]], [], globals_now()))
        elif op == "check-sat-assuming":
            checks.append(([a for s in scopes for a in s["asserts"]], list(cmd[1]), globals_now()))
        else:
            raise SmtError(f"unsupported command {op}")
    return checks


def smt_named(term):
    if isinstance(term, list) and term:
        if term[0] == "!":
            attrs = term[2:]
            for i in range(0, len(attrs) - 1, 2):
                if attrs[i] == ":named":
                    yield attrs[i + 1], term[1]
        for sub in term:
            yield from smt_named(sub)


def smt_models(output: str):
    """The answers and models ay printed, in order: [(answer, {name: SmtFun})]."""
    text = "\n".join(l for l in output.splitlines() if not l.startswith("c "))
    items = smt_parse(text)
    res = []
    for it in items:
        if isinstance(it, str):
            res.append([it, None])
        elif isinstance(it, list):
            if it and it[0] == "error":
                raise SmtError(f"ay reported an error: {it}")
            defs = it[1:] if it and it[0] == "model" else it
            model = {}
            for d in defs:
                if not (isinstance(d, list) and d and d[0] == "define-fun"):
                    raise SmtError(f"unexpected model item {d}")
                model[d[1]] = SmtFun([p[0] for p in d[2]], d[4], {}, model_fun=True)
            if not res or res[-1][1] is not None:
                raise SmtError("a model with no answer before it")
            res[-1][1] = model
    return res


def smt_model_check(problem: str, output: str):
    """None when every check-sat was answered sat with a model satisfying every
    assertion (and assumption) in scope there; otherwise the reason."""
    checks = smt_checks(problem)
    answers = smt_models(output)
    if len(answers) != len(checks):
        return f"{len(checks)} check-sat command(s), {len(answers)} answer(s)"
    for k, ((asserts, assumptions, g), (answer, model)) in enumerate(zip(checks, answers)):
        if answer != "sat":
            return f"check {k + 1}: ay answered {answer!r}"
        if model is None:
            return f"check {k + 1}: ay printed no model"
        for term, tg in asserts:
            if smt_eval(term, {}, tg, model) is not True:
                return f"check {k + 1}: the model falsifies (assert {term})"
        for term in assumptions:
            if smt_eval(term, {}, g, model) is not True:
                return f"check {k + 1}: the model falsifies the assumption {term}"
    return None


def smt_witness(entry, ay_bin, work: Path):
    if not ay_bin:
        return {"status": SKIPPED, "detail": "no `ay` found (AY_BIN)"}
    problem = json.loads((entry["_dir"] / entry["reproducer"]["cert"]).read_text())["problem"]
    try:
        checks = smt_checks(problem)
    except (SmtError, ValueError, IndexError) as e:
        return {"status": "error", "detail": f"the evaluator cannot read the problem: {e}"}
    if not checks:
        return {"status": "error", "detail": "the problem has no check-sat"}
    # The same script with (get-model) after every check.
    script = "(set-option :produce-models true)\n" + re.sub(
        r"(\(check-sat(?:-assuming\s*\([^()]*(?:\([^()]*\)[^()]*)*\))?\s*\))", r"\1\n(get-model)", problem)
    f = work / f"{entry['id']}.smt2"
    f.write_text(script)
    rc, out, err = run([ay_bin, str(f)], cwd=work, timeout=60)
    if rc is None:
        return {"status": "error", "detail": f"ay did not finish: {clip(err[-200:])}"}
    try:
        why = smt_model_check(problem, out)
    except (SmtError, ValueError, IndexError, TypeError) as e:
        why = f"the model could not be evaluated: {e}"
    if why:
        return {"status": "MISMATCH", "detail": f"{why} (ay exit {rc})"}
    return {"status": "ok", "detail": f"ay answered sat {len(checks)}x; every model checked against every assertion"}


# ---------------------------------------------------------------------------
# trustc lanes
# ---------------------------------------------------------------------------


def decode_trustc_rows(text):
    """Keep observed rows and report unreadable or repeated function records.

    A valid claim must survive later bad output: a reproducer's emitted proof
    stays a false proof. But an unproved prefix cannot stand for a complete
    refusal, and incomplete output cannot establish a twin's proof.
    """
    funcs = {}
    problems = []
    seen = set()

    def unique_object(pairs):
        value = {}
        for key, item in pairs:
            if key in value:
                raise ValueError(f"duplicate JSON key {key!r}")
            value[key] = item
        return value

    def nonfinite_constant(raw):
        raise ValueError(f"nonfinite JSON constant {raw}")

    def finite_float(raw):
        value = float(raw)
        if not math.isfinite(value):
            raise ValueError(f"nonfinite JSON number {raw}")
        return value

    for number, line in enumerate(text.splitlines(), 1):
        i = line.find("TRUST_JSON:")
        if i < 0:
            continue
        try:
            j = json.loads(
                line[i + len("TRUST_JSON:"):], object_pairs_hook=unique_object,
                parse_constant=nonfinite_constant, parse_float=finite_float,
            )
        except ValueError as error:
            problems.append(f"TRUST_JSON line {number}: invalid JSON ({error})")
            continue
        if not isinstance(j, dict) or not isinstance(j.get("type"), str):
            problems.append(f"TRUST_JSON line {number}: record needs an object and type")
            continue
        # Other ordinary records, including summaries, share this framing.
        if j["type"] != "function_result":
            continue
        function = j.get("function")
        if not isinstance(function, str) or not function:
            problems.append(f"TRUST_JSON line {number}: function identity is missing")
            continue
        if function in seen:
            problems.append(f"TRUST_JSON line {number}: duplicate function {function}")
        seen.add(function)
        rows = j.get("results")
        if not isinstance(rows, list):
            problems.append(f"TRUST_JSON line {number}: {function} needs a results array")
            continue
        if "total" in j and (
            type(j["total"]) is not int or j["total"] != len(rows)
        ):
            problems.append(f"TRUST_JSON line {number}: {function} total differs from its rows")
        observed = funcs.setdefault(function, [])
        for index, row in enumerate(rows):
            if (
                not isinstance(row, dict)
                or not isinstance(row.get("kind"), str) or not row["kind"]
                or not isinstance(row.get("outcome"), str)
                or row["outcome"] not in TRUSTC_ROW_OUTCOMES
                or (row.get("location") is not None and not isinstance(row["location"], dict))
            ):
                problems.append(f"TRUST_JSON line {number}: {function} row {index} is malformed")
                continue
            observed.append(row)
    return funcs, problems


def trustc_rows(entry, trustc, lane_flags, opt, work: Path, source):
    """(rc, {function path: [rows]}, stderr, output problems) for one compile."""
    aux_flags = build_aux(entry, trustc, work, verify=True)
    if isinstance(aux_flags, str):
        return None, {}, aux_flags, []
    argv = [
        trustc, "-Ztrust-verify=on", "-Ztrust-verify-output=json", *lane_flags,
        "--edition", entry.get("edition", "2021"), "--crate-type", "lib",
        "--crate-name", "sbc", f"-Copt-level={opt}", "-Coverflow-checks=on",
        "--emit", "metadata", "-o", str(work / f"sbc-{entry['id']}-{opt}-{Path(source).stem}.rmeta"),
        *entry.get("rustc_flags", []), *aux_flags, str(entry["_dir"] / source),
    ]
    rc, out, err = run(argv, cwd=work, timeout=int(entry.get("timeout", 600)))
    funcs, problems = decode_trustc_rows(out + "\n" + err)
    return rc, funcs, err, problems


def compile_failure(rc):
    """None when trustc finished normally (0, or 1 for failed obligations)."""
    if rc is None:
        return "the compile did not finish"
    if rc in (0, 1):
        return None
    if rc < 0:
        return f"trustc died on signal {-rc}"
    return f"trustc exited {rc}" + (" (an internal compiler error)" if rc == 101 else "")


def trustc_level_verdict(entry, side, rc, funcs, err, output_problems=()):
    """One opt level's verdict for one side."""
    spec = entry[side]
    mode = spec.get("mode", "obligation")
    crash = compile_failure(rc)
    tail = clip(err[-300:], 200)
    if mode == "build-accepted":
        if crash:
            return ERROR, f"{crash}: {tail!r}"
        if rc == 0:
            return PROVED, "build accepted (exit 0)"
        # Exit 1 is a refusal only when trustc says why: `/usr/bin/false` exits 1 too.
        diag = re.search(r"^error(\[\w+\])?: .*", err, re.M)
        if not diag:
            return ERROR, f"exit {rc} with no error diagnostic: {tail!r}"
        return REFUSED, f"build refused (exit {rc}): {clip(diag.group(0), 160)}"
    # Build-accepted above judges the actual process outcome. Row-based modes
    # also need a readable population, while retaining observed false proofs.
    if output_problems:
        unreadable = "unreadable TRUST_JSON output: " + "; ".join(output_problems[:3])
        crash = f"{crash}; {unreadable}" if crash else unreadable
    fn = "sbc::" + spec["function"]
    rows = funcs.get(fn)
    if rows is None:
        return ERROR, f"no rows for {fn} ({crash or f'exit {rc}'}: {tail!r})"
    if not rows:
        # A function_result with no rows answers nothing about the claim.
        return ERROR, f"an empty result for {fn} ({crash or f'exit {rc}'}: {tail!r})"
    if mode == "assumption-kept":
        revoked = "does not cover its unsafe operations" in err
        kept = bool(rows) and all(str(r.get("kind", "")).startswith("assumption:") for r in rows)
        if kept and not revoked:
            # A claim the verifier emitted stands even if the compile crashed later
            # (fail-closed for the reproducer); a crashed twin is no proof.
            if crash and side == "twin":
                return ERROR, f"assumption kept, but {crash}"
            return PROVED, f"assumption kept ({rows[0].get('kind')}), no revocation" + (f"; then {crash}" if crash else "")
        if crash:
            return ERROR, f"{crash}; assumption not kept"
        return REFUSED, "assumption " + ("revoked" if revoked else "not kept") + f" ({sorted({str(r.get('kind')) for r in rows})})"
    anchor = anchor_of(entry, side)
    match = [r for r in rows if row_matches(r, anchor)]
    if not match:
        seen = sorted({f"{r.get('kind')}@{(r.get('location') or {}).get('line_start')}" for r in rows})
        return ERROR, f"anchor-miss: no row matches {_anchor_text(anchor)} (rows: {', '.join(seen)[:240]})"
    places = {(Path(str((r.get("location") or {}).get("file", ""))).name, (r.get("location") or {}).get("line_start")) for r in match}
    if len(places) > 1:
        return ERROR, f"ambiguous anchor: {_anchor_text(anchor)} matches rows at {sorted(places, key=str)}"
    pr = [r for r in match if r.get("outcome") == "proved"]
    cert = [r for r in pr if (r.get("proof_evidence") or {}).get("strength", {}).get("assurance") == "Certified"]
    text = (f"{len(pr)}/{len(match)} target row(s) proved" + (f", {len(cert)} kernel-certified" if cert else "")
            + f" [{', '.join(sorted({str(r.get('outcome', '?')) for r in match}))}]")
    if side == "reproducer":
        if pr:
            return PROVED, text + (f"; then {crash}" if crash else "")
        return (ERROR, f"{text}; {crash}") if crash else (REFUSED, text)
    if crash:
        return ERROR, f"{text}; {crash}"
    return (PROVED, text) if len(pr) == len(match) else (REFUSED, text)


def _anchor_text(a):
    parts = [f"kind {a['kind']}"] if a.get("kind") else []
    if a.get("line"):
        parts.append(f"line {a['line']} of {a['file']}")
    if a.get("message"):
        parts.append(f"message {a['message']!r}")
    return ", ".join(parts)


def fold_levels(side, levels):
    """A reproducer is proved if ANY opt level proves it; a twin only if EVERY level does."""
    statuses = [s for s, _ in levels.values()]
    detail = "; ".join(f"O{opt}: {d}" for opt, (_s, d) in levels.items())
    if side == "reproducer":
        if PROVED in statuses:
            return PROVED, detail
    elif statuses and all(s == PROVED for s in statuses):
        return PROVED, detail
    if ERROR in statuses:
        return ERROR, detail
    return REFUSED, detail


def run_trustc_lane(entry, verifier, trustc, trustc_reason, work):
    if trustc_reason:
        return {s: (SKIPPED, trustc_reason) for s in SIDES}
    compiles = {}
    for src in {side_source(entry, s) for s in SIDES}:
        compiles[src] = {
            opt: trustc_rows(entry, trustc, TRUSTC_LANES[verifier], opt, work, src)
            for opt in entry.get("opt_levels", ["0"])
        }
    out = {}
    for s in SIDES:
        levels = {opt: trustc_level_verdict(entry, s, *res) for opt, res in compiles[side_source(entry, s)].items()}
        out[s] = fold_levels(s, levels)
    return out


# ---------------------------------------------------------------------------
# trust-vc
# ---------------------------------------------------------------------------


class TrustVcSyn:
    def __init__(self, trust_vc_dir, toolchain_bin, work: Path):
        self.reason = None
        self.exe = None
        if os.environ.get("TRUST_VC_SYN_ADAPTER"):
            self.exe = os.environ["TRUST_VC_SYN_ADAPTER"]
            if not is_executable(self.exe):
                self.reason = f"TRUST_VC_SYN_ADAPTER={self.exe} is not an executable file"
            return
        if not trust_vc_dir:
            self.reason = "no trust-vc checkout (set TRUST_VC_DIR)"
            return
        core = Path(trust_vc_dir) / "crates" / "trust-vc-core"
        if not (core / "Cargo.toml").exists():
            self.reason = f"{core} has no Cargo.toml"
            return
        build = Path(os.environ.get("TRUST_VC_SYN_BUILD_DIR", work / "trust-vc-syn-adapter"))
        (build / "src").mkdir(parents=True, exist_ok=True)
        tmpl = (CORPUS / "adapters" / "trust-vc-syn" / "Cargo.toml.in").read_text()
        (build / "Cargo.toml").write_text(tmpl.replace("@TRUST_VC_CORE@", str(core)))
        shutil.copy(CORPUS / "adapters" / "trust-vc-syn" / "src" / "main.rs", build / "src" / "main.rs")
        for f in ("Cargo.lock", "rust-toolchain.toml"):
            if (Path(trust_vc_dir) / f).exists() and not (build / f).exists():
                shutil.copy(Path(trust_vc_dir) / f, build / f)
        # The targo beside the selected toolchain, not whatever PATH names.
        targo = str(toolchain_bin / "targo") if toolchain_bin and (toolchain_bin / "targo").exists() else shutil.which("targo")
        if not targo:
            self.reason = "no targo to build the adapter"
            return
        env = dict(os.environ, CARGO_INCREMENTAL="0")
        if toolchain_bin:
            env["PATH"] = f"{toolchain_bin}{os.pathsep}{env.get('PATH', '')}"
        log(f"building trust-vc syn adapter against {core} with {targo} ...")
        rc, _o, err = run([targo, "--unverified", "build", "--release"], cwd=build, env=env, timeout=3600)
        exe = build / "target" / "release" / "trust-vc-syn-adapter"
        if rc != 0 or not exe.exists():
            self.reason = f"adapter build failed: {clip(err[-300:])}"
            return
        self.exe = str(exe)

    def verdict(self, entry, side, work: Path):
        if self.reason:
            return SKIPPED, self.reason
        spec = entry[side]
        if spec.get("mode", "obligation") != "obligation":
            return NA, "trust-vc has no build-acceptance verdict"
        src = entry["_dir"] / spec.get("source", entry.get("trust_vc_source", entry["source"]))
        rc, out, err = run([self.exe, str(src), spec["function"]], cwd=work, timeout=int(entry.get("timeout", 600)))
        lines = out.strip().splitlines()
        try:
            j = json.loads(lines[-1])
            v = j["verdict"]
        except (ValueError, IndexError, KeyError, TypeError):
            return ERROR, f"no verdict (adapter exit {rc}): {clip((out + err)[-300:])}"
        if rc != 0:
            return ERROR, f"adapter exit {rc} after a verdict line: {clip((out + err)[-300:])}"
        raw = str(j.get("raw", ""))
        if v == "proved":
            return PROVED, "Verified"
        if v == "error":
            return ERROR, CONSTRUCT_REFUSAL + raw
        if v in ("refuted", "not-proved"):
            return REFUSED, f"{v}: {raw}"
        return ERROR, f"unknown verdict {v!r}: {raw}"


def decode_trust_vc_driver(text):
    """Read the driver's six-outcome TSV contract without losing observed claims.

    A broken record set cannot establish a refusal or twin proof. Retain its
    individually identifiable Verified rows for reproducer falsification only.
    """
    buckets = {"Verified": 0, "Refuted": 1, "Unknown": 2, "Error": 3,
               "UnsupportedType": 4, "UnsupportedContract": 4}
    counts, records, summaries, problems = [0] * 5, {}, [], []
    total = 0
    # The producer sanitizes LF, CR and TAB in details. Other Unicode line
    # separators are ordinary detail bytes, not additional protocol records.
    for line in text.split("\n"):
        parts = line.split("\t")
        if parts[0] == "TRUST_VC_DRIVER_RESULT":
            total += 1
            if summaries:
                problems.append("result after trailing summary")
            if len(parts) != 4 or not parts[1]:
                problems.append("malformed result record")
            if len(parts) < 3 or not parts[1]:
                continue
            function, verdict = parts[1:3]
            if function in records:
                problems.append(f"duplicate function {function!r}")
            records.setdefault(function, []).append((verdict, parts[3] if len(parts) > 3 else ""))
            if verdict not in buckets:
                problems.append(f"unknown verdict {verdict!r}")
            else:
                counts[buckets[verdict]] += 1
        elif parts[0] == "TRUST_VC_DRIVER_SUMMARY":
            summaries.append(parts[1:])
        elif line.startswith(("TRUST_VC_DRIVER_RESULT", "TRUST_VC_DRIVER_SUMMARY")):
            problems.append("malformed record tag")
    expected = [str(n) for n in (total, *counts)]
    if len(summaries) != 1:
        problems.append(f"expected one trailing summary, got {len(summaries)}")
    elif summaries[0] != expected:
        # Comparing canonical decimal spellings also rejects signs, padding,
        # non-integers and huge counts without parsing untrusted integers.
        problems.append(f"summary counters {clip(repr(summaries[0]))} disagree with records {expected}")
    return records, problems, int(any(counts[1:4]))


class TrustVcMir:
    """trust-vc's rustc-driver (THIR) lane: `trust-vc-driver <rustc args> <file>` prints
    `TRUST_VC_DRIVER_RESULT\t<function>\t<verdict>\t<detail>` per target."""

    def __init__(self, driver, trustc):
        self.reason = None
        self.driver = driver
        if not driver:
            self.reason = ("no trust-vc-driver (set TRUST_VC_MIR_DRIVER to one built with "
                           "`targo --unverified build -p trust-vc-driver --features rustc-driver`)")
        elif not is_executable(driver):
            self.reason = f"{driver} is not an executable file"
        self.sysroot = None
        if trustc and not self.reason:
            _rc, out, _e = run([trustc, "--print", "sysroot"], timeout=60)
            self.sysroot = out.strip() or None
        self.cache = {}

    def _results(self, entry, source, work: Path):
        key = (entry["id"], source)
        if key in self.cache:
            return self.cache[key]
        argv = [self.driver, "--edition", entry.get("edition", "2021"), "--crate-type", "lib",
                "--crate-name", "sbc", "--emit", "metadata", "-o", str(work / "trust-vc-mir.rmeta")]
        if self.sysroot:
            argv += ["--sysroot", self.sysroot]
        if os.environ.get("TRUST_VC_MACROS"):
            argv += ["--extern", f"trust_vc={os.environ['TRUST_VC_MACROS']}"]
        argv.append(str(entry["_dir"] / source))
        rc, out, err = run(argv, cwd=work, timeout=int(entry.get("timeout", 600)))
        res, problems, expected_exit = decode_trust_vc_driver(out)
        if rc in (0, 1) and rc != expected_exit:
            problems.append(f"driver exit {rc} disagrees with result population (expected {expected_exit})")
        self.cache[key] = (rc, res, err, problems)
        return self.cache[key]

    def verdict(self, entry, side, work: Path):
        if self.reason:
            return SKIPPED, self.reason
        spec = entry[side]
        if spec.get("mode", "obligation") != "obligation":
            return NA, "trust-vc has no build-acceptance verdict"
        src = spec.get("mir_source", entry.get("mir_source", spec.get("source", entry["source"])))
        rc, res, err, problems = self._results(entry, src, work)
        fn = spec["function"]
        hits = res.get(fn)
        if hits is None:
            matches = [rows for name, rows in res.items() if name.split("::")[-1] == fn]
            if len(matches) > 1:
                return ERROR, f"ambiguous TRUST_VC_DRIVER_RESULT for {fn}"
            hits = matches[0] if matches else None
        if hits is None:
            return ERROR, f"no TRUST_VC_DRIVER_RESULT for {fn} (exit {rc}: {clip(err[-300:])!r})"
        # The driver exits 0 (everything in-fragment verified) or 1 (something did not).
        crash = None if rc in (0, 1) else f"driver did not finish normally (exit {rc}): {clip(err[-200:])}"
        issues = [*problems, *([crash] if crash else [])]
        if any(verdict == "Verified" for verdict, _detail in hits):
            # An observed target claim stands for a reproducer even when a later
            # duplicate, damaged summary or crash makes the full output unusable.
            if issues and side == "twin":
                return ERROR, f"Verified, but {clip('; '.join(issues))}"
            return PROVED, "Verified" + (f"; {clip('; '.join(issues))}" if issues else "")
        if problems:
            return ERROR, "unusable driver record set: " + clip("; ".join(problems))
        verdict, detail = hits[0]
        if crash:
            return ERROR, f"{verdict}: {detail}; {crash}"
        if verdict == "Error":
            return ERROR, detail
        return REFUSED, f"{verdict}: {detail}"


# ---------------------------------------------------------------------------
# trust-wp
# ---------------------------------------------------------------------------

WP_ADAPTER = CORPUS / "adapters" / "trust_wp_adapter.py"


def wp_toolchain_env(toolchain_bin):
    """The environment trust-wp's harness builds and runs under. trust-wp-driver links
    rustc_private, so the compiler its harness selects must be an immutable toolchain
    that keeps its rustc-private sysroot beside it (trust-wp docs/DEVELOPING.md, "Channel
    pin"; scripts/trustc-private-wrapper.sh). An atpkg store toolchain is one; a `targo`
    on PATH may be a shim into some tree's dev sysroot, which is not. So the harness gets
    the selected toolchain's `targo` as CARGO and its bin directory first on PATH."""
    env = dict(os.environ)
    for k in ("RUSTC", "RUSTC_WRAPPER", "RUSTC_WORKSPACE_WRAPPER", "CARGO_BUILD_RUSTC", "CARGO"):
        env.pop(k, None)
    if toolchain_bin:
        env["PATH"] = f"{toolchain_bin}{os.pathsep}{env.get('PATH', '')}"
        # trust-wp's harness honours $CARGO and $RUSTC (tests/creusot_compat/
        # harness_targets.py build_tool/compiler_tool) and otherwise runs the bare
        # names, which on an atpkg machine are shims into a dev sysroot.
        if (Path(toolchain_bin) / "targo").exists():
            env["CARGO"] = str(Path(toolchain_bin) / "targo")
        if (Path(toolchain_bin) / "trustc").exists():
            env["RUSTC"] = str(Path(toolchain_bin) / "trustc")
    return env


class TrustWp:
    def __init__(self, wp_dir, toolchain_bin, work: Path, entries):
        self.reason = None
        self.results = {}
        adapter = os.environ.get("TRUST_WP_ADAPTER") or str(WP_ADAPTER)
        if not wp_dir:
            self.reason = "no trust-wp checkout (set TRUST_WP_DIR)"
            return
        if not os.environ.get("TRUST_WP_ADAPTER"):
            runner = Path(wp_dir) / "tests" / "adversarial" / "run_adversarial.py"
            if not runner.exists():
                self.reason = f"{runner} not found (submodule not checked out?)"
                return
        py = os.environ.get("TRUST_WP_PYTHON") or shutil.which("python3.11") or shutil.which("python3.12") or shutil.which("python3.13")
        if not py:
            self.reason = "trust-wp's harness needs python >= 3.11 (set TRUST_WP_PYTHON)"
            return
        wanted = [e for e in entries if e["lang"] == "creusot"]
        if not wanted:
            return
        cases = work / "trust-wp-cases"
        cases.mkdir(parents=True, exist_ok=True)
        for e in wanted:
            shutil.copy(e["_dir"] / e["source"], cases / (e["id"].replace("-", "_") + ".rs"))
        out_json = work / "trust-wp-results.json"
        log(f"running trust-wp ({wp_dir}) on {len(wanted)} case(s), toolchain {toolchain_bin} ...")
        rc, out, err = run(
            [py, adapter, "--trust-wp", str(wp_dir), "--cases", str(cases), "--json", str(out_json)],
            env=wp_toolchain_env(toolchain_bin),
            timeout=int(os.environ.get("TRUST_WP_TIMEOUT", "7200")),
        )
        if rc != 0 or not out_json.exists():
            self.reason = f"trust-wp adapter failed (exit {rc}): {clip((out + err)[-400:], 400)}"
            return
        try:
            self.results = json.loads(out_json.read_text())
        except ValueError as e:
            self.reason = f"trust-wp adapter wrote unreadable JSON: {e}"

    def verdict(self, entry, side, work: Path):
        if self.reason:
            # The harness ran nothing usable: no verdict exists for any case.
            return (SKIPPED if "not found" in self.reason or "no trust-wp" in self.reason
                    or "needs python" in self.reason else ERROR), self.reason
        r = self.results.get(entry["id"].replace("-", "_"))
        if r is None:
            return ERROR, "no result for this case"
        if r.get("error"):
            return ERROR, r["error"]
        fn = entry[side]["function"]
        credited = fn in r.get("verified_functions", [])
        asserted = [a for a in r.get("assertion_credits", []) if a.split("::")[-1] == fn]
        unproved = fn in r.get("unproved_assertion_functions", [])
        if side == "twin":
            if (credited or asserted) and not unproved:
                return PROVED, f"{fn}: " + ("verified" if credited else f"{len(asserted)} proof_assert verified")
            return REFUSED, f"{fn}: verdict {r.get('verdict')}; not credited"
        if credited or asserted:
            return PROVED, f"{fn}: " + ", ".join(
                (["function verified"] if credited else []) + ([f"{len(asserted)} proof_assert verified"] if asserted else [])
            )
        return REFUSED, f"{fn} not credited (case verdict {r.get('verdict')})"


# ---------------------------------------------------------------------------
# Clean
# ---------------------------------------------------------------------------


class CleanExternal:
    def __init__(self, clean_bin, work: Path):
        self.reason = None
        self.bin = clean_bin
        if not clean_bin:
            self.reason = "no `clean` with carcara-verify (set CLEAN_BIN)"
            return
        if not is_executable(clean_bin):
            self.reason = f"CLEAN_BIN={clean_bin} is not an executable file"
            return
        probe = work / "clean-probe.json"
        probe.write_text(json.dumps({
            "type": "alethe_certificate", "version": "1.0",
            "problem": "(set-logic QF_LIA)\n(declare-const x Int)\n(assert (> x 0))\n(assert (< x 0))\n(check-sat)\n",
            "proof": "(assume a0 (> x 0))\n(assume a1 (< x 0))\n"
                     "(step t1 (cl (not (> x 0)) (not (< x 0))) :rule la_generic :args (1 1))\n"
                     "(step t2 (cl) :rule resolution :premises (t1 a0 a1))\n",
        }))
        rc, out, err = run([clean_bin, "cert", "verify-external", str(probe)], cwd=work, timeout=120)
        if "carcara-verify feature required" in out + err:
            self.reason = f"{clean_bin} was built without --features carcara-verify"
        elif rc != 0 or "PASSED" not in out + err:
            self.reason = f"{clean_bin} does not accept the positive probe certificate (exit {rc}): {clip((out + err)[-200:])}"

    def verdict(self, entry, side, work: Path):
        if self.reason:
            return SKIPPED, self.reason
        cert = entry["_dir"] / entry[side]["cert"]
        rc, out, err = run([self.bin, "cert", "verify-external", "-v", str(cert)], cwd=work, timeout=300)
        text = (out + err).strip()
        if rc == 0 and "verification: PASSED" in text:
            return PROVED, "certificate accepted"
        if rc == 0:
            return ERROR, f"exit 0 without a PASSED line: {clip(text[-200:])}"
        m = re.search(r"Error: (.*)", text)
        # A refusal is Clean saying FAILED and why, with its ordinary failure status.
        if rc == 1 and "verification: FAILED" in text and m:
            return REFUSED, m.group(1).strip()
        return ERROR, f"no verdict (exit {rc}): {clip(text[-300:])}"


# ---------------------------------------------------------------------------
# Classification and report
# ---------------------------------------------------------------------------


def classify(entry, verifier, side, verdict):
    status, detail = verdict
    exp = expectation(entry, verifier, side)
    if exp == NA or status == NA:
        return "n/a"
    if status == SKIPPED:
        return "SKIPPED"
    known = entry.get("known_open", {}).get(verifier)
    whitelisted = entry.get("expected_refusal", {}).get(verifier, {}).get(side)
    refusal_ok = (status == ERROR and bool(whitelisted) and str(detail).startswith(CONSTRUCT_REFUSAL)
                  and whitelisted in str(detail))
    if side == "reproducer":
        if status == PROVED:
            return "KNOWN-FALSE-PROVED" if known else "FALSE-PROVED"
        if status == ERROR:
            # Only a clean REFUSED retires a known-open marker.
            if known:
                return "ERROR(known-open)"
            return "ok(refusal)" if refusal_ok else "ERROR"
        return "XFIXED" if known else "ok"
    # twin
    if status == PROVED:
        return "ok"
    if exp == "not-in-fragment":
        if status == REFUSED:
            return "ok(nif)"
        return "ok(nif-refusal)" if refusal_ok else "ERROR"
    if status == ERROR:
        return "ERROR"
    if known or entry.get("known_twin_lost", {}).get(verifier):
        return "TWIN-LOST(known)"
    return "TWIN-LOST"


def resolve_trustc():
    """(path or None, reason it is unusable or None)."""
    env = os.environ.get("TRUSTC")
    if env:
        return env, (None if is_executable(env) else f"TRUSTC={env} is not an executable file")
    if (STORE_BIN / "trustc").exists():
        return str(STORE_BIN / "trustc"), None
    w = shutil.which("trustc")
    return w, (None if w else "no trustc found (set TRUSTC)")


def corpus_run(args) -> int:
    global TIMEOUT_CAP
    if args.timeout:
        TIMEOUT_CAP = args.timeout
    entries = load_entries(args.filter)
    if not entries:
        log("no entries")
        return 2
    problems = validate_entries(load_entries())  # always the whole corpus: twins are compared across entries
    if problems:
        for p in problems:
            log(f"entry check: {p}")
        return 2
    verifiers = args.verifiers.split(",") if args.verifiers else ALL_VERIFIERS
    for v in verifiers:
        if v not in ALL_VERIFIERS:
            raise SystemExit(f"unknown verifier {v}")

    # The sealed store toolchain first: a PATH `trustc` may be a shim into some
    # tree's dev sysroot, which is not a reproducible verifier identity.
    trustc, trustc_reason = resolve_trustc()
    toolchain_bin = Path(os.environ["TRUST_WP_TOOLCHAIN_BIN"]) if os.environ.get("TRUST_WP_TOOLCHAIN_BIN") else (
        Path(os.path.realpath(trustc)).parent if trustc and not trustc_reason else None)
    ay_bin = os.environ.get("AY_BIN") or shutil.which("ay") or (
        str(STORE_BIN / "ay") if (STORE_BIN / "ay").exists() else None)
    work = Path(tempfile.mkdtemp(prefix="trust-soundness-corpus-"))

    def first_party(name, env):
        if os.environ.get(env):
            return os.environ[env]
        sub = ROOT / "first-party" / name
        return str(sub) if (sub / "Cargo.toml").exists() else None

    banner = [("trustc", os.path.realpath(trustc) if trustc else "none")]
    if trustc and not trustc_reason:
        _rc, out, _e = run([trustc, "-vV"], timeout=60)
        banner.append(("trustc -vV", " | ".join(out.strip().splitlines()[:2]) or "(no answer)"))
    elif trustc_reason:
        banner.append(("trustc unusable", trustc_reason))

    def git_head(d):
        if not d:
            return "none"
        rc, out, _e = run(["git", "-C", str(d), "rev-parse", "--short=10", "HEAD"], timeout=30)
        return f"{d} @ {out.strip()}" if rc == 0 else str(d)

    wp_dir = first_party("trust-wp", "TRUST_WP_DIR")
    banner.append(("trust-wp", git_head(wp_dir) + (f" (harness toolchain {toolchain_bin})" if toolchain_bin else "")))
    banner.append(("trust-vc", os.environ.get("TRUST_VC_SYN_ADAPTER") or git_head(first_party("trust-vc", "TRUST_VC_DIR"))))
    banner.append(("trust-vc-mir", os.environ.get("TRUST_VC_MIR_DRIVER") or "none"))
    cb = os.environ.get("CLEAN_BIN") or shutil.which("clean")
    if cb:
        # An atpkg shim execs the real binary; name that one.
        try:
            head = Path(cb).read_text(errors="ignore")[:400] if Path(cb).stat().st_size < 4096 else ""
        except OSError:
            head = ""
        m = re.search(r"exec '([^']+)'", head)
        banner.append(("clean", m.group(1) if m else os.path.realpath(cb)))
    banner.append(("ay (SMT witness)", os.path.realpath(ay_bin) if ay_bin else "none"))
    banner.append(("witnesses", "not run (--no-witness)" if args.no_witness else "run"))
    banner.append(("mode", "STRICT" if args.strict else "report only (non-blocking)"))

    wp = TrustWp(wp_dir, toolchain_bin, work, entries) if "trust-wp" in verifiers else None
    vcs = TrustVcSyn(first_party("trust-vc", "TRUST_VC_DIR"), toolchain_bin, work) if "trust-vc-syn" in verifiers else None
    clean_bin = os.environ.get("CLEAN_BIN") or shutil.which("clean")
    clean = CleanExternal(clean_bin, work) if "clean-external" in verifiers else None
    vcm = TrustVcMir(os.environ.get("TRUST_VC_MIR_DRIVER"), trustc if not trustc_reason else None) if "trust-vc-mir" in verifiers else None

    def process(e):
        ework = work / e["id"]
        ework.mkdir(parents=True, exist_ok=True)
        row = {"id": e["id"], "class": e.get("class", ""), "lang": e["lang"], "verifiers": {}}
        if not args.no_witness:
            row["witness"] = run_witness(e, None if trustc_reason else trustc, ework, ay_bin)
        for v in verifiers:
            if v not in LANG_VERIFIERS[e["lang"]]:
                continue
            if expectation(e, v, "reproducer") == NA:
                sides = {s: (NA, na_reason(e, v) or "not applicable") for s in SIDES}
            elif v in TRUSTC_LANES:
                sides = run_trustc_lane(e, v, trustc, trustc_reason, ework)
            else:
                lane = {"trust-wp": wp, "trust-vc-syn": vcs, "clean-external": clean, "trust-vc-mir": vcm}[v]
                sides = {s: lane.verdict(e, s, ework) for s in SIDES}
            row["verifiers"][v] = {
                s: {"verdict": sides[s][0], "detail": sides[s][1],
                    "expect": expectation(e, v, s), "class": classify(e, v, s, sides[s])}
                for s in sides
            }
        rep = " ".join(f"{v}={row['verifiers'][v]['reproducer']['class']}/{row['verifiers'][v]['twin']['class']}"
                       for v in row["verifiers"])
        log(f"{e['id']:<44} witness={row.get('witness', {}).get('status', '-'):<8} {rep}")
        return row

    import concurrent.futures
    with concurrent.futures.ThreadPoolExecutor(max_workers=max(1, args.jobs)) as pool:
        results = list(pool.map(process, entries))

    # ------------------------------------------------------------------ report
    print()
    print("trust-soundness-corpus — per entry: <reproducer verdict>:<class> / <twin verdict>:<class>")
    print("  P proved, R refused (not proved), E error, S skipped, - not applicable")
    for k, v in banner:
        print(f"  {k}: {v}")
    cols = list(verifiers)
    width = 34
    print(f"  {'entry':<44} {'witness':<9}" + "".join(f"{c:<{width}}" for c in cols))
    for r in results:
        cells = []
        for c in cols:
            cell = r["verifiers"].get(c)
            if not cell:
                cells.append(f"{'n/a':<{width}}")
                continue
            rep, tw = cell["reproducer"], cell["twin"]
            text = (f"{SHORT.get(rep['verdict'], rep['verdict'])}:{rep['class']} / "
                    f"{SHORT.get(tw['verdict'], tw['verdict'])}:{tw['class']}")
            cells.append(f"{text:<{width}}")
        print(f"  {r['id']:<44} {r.get('witness', {}).get('status', '-'):<9}" + "".join(cells))

    print()
    print("Totals per verifier (reproducers: proved / refused / error / skipped; twins: proved / not / skipped)")
    totals = {}
    for c in cols:
        t = {"rep": {}, "twin": {}, "false": 0, "known": 0, "classes": {}}
        for r in results:
            cell = r["verifiers"].get(c)
            if not cell:
                continue
            for side, key in (("reproducer", "rep"), ("twin", "twin")):
                v = cell[side]["verdict"]
                t["classes"][cell[side]["class"]] = t["classes"].get(cell[side]["class"], 0) + 1
                if v == NA:
                    continue
                t[key][v] = t[key].get(v, 0) + 1
            t["false"] += cell["reproducer"]["class"] == "FALSE-PROVED"
            t["known"] += cell["reproducer"]["class"] == "KNOWN-FALSE-PROVED"
        totals[c] = t
        rp = t["rep"]
        print(f"  {c:<16} reproducers {rp.get(PROVED, 0)} proved ({t['false']} FALSE-PROVED, "
              f"{t['known']} KNOWN-FALSE-PROVED) / {rp.get(REFUSED, 0)} refused / {rp.get(ERROR, 0)} error / "
              f"{rp.get(SKIPPED, 0)} skipped;  twins {t['twin'].get(PROVED, 0)} proved / "
              f"{sum(n for k, n in t['twin'].items() if k not in (PROVED, SKIPPED))} not / "
              f"{t['twin'].get(SKIPPED, 0)} skipped")
    skipped = {c: next((r["verifiers"][c]["reproducer"]["detail"] for r in results
                        if c in r["verifiers"] and r["verifiers"][c]["reproducer"]["verdict"] == SKIPPED), None)
               for c in cols}
    for c, why in skipped.items():
        if why:
            print(f"  SKIPPED {c}: {clip(why, 400)}")

    def cells_of(pred):
        return [(r["id"], c, s, cell[s]) for r in results for c, cell in r["verifiers"].items()
                for s in SIDES if pred(s, cell[s])]

    false_proved = cells_of(lambda s, x: x["class"] == "FALSE-PROVED")
    known = cells_of(lambda s, x: x["class"] == "KNOWN-FALSE-PROVED")
    xfixed = cells_of(lambda s, x: x["class"] == "XFIXED")
    lost = cells_of(lambda s, x: x["class"].startswith("TWIN-LOST"))
    errors = cells_of(lambda s, x: x["class"] in ("ERROR", "ERROR(known-open)"))
    bad_witness = [r for r in results if "witness" in r and r["witness"].get("status") != "ok"]
    print()
    print(f"FALSE-PROVED: {len(false_proved)}  " + ", ".join(f"{i}@{c}" for i, c, _s, _x in false_proved))
    print(f"KNOWN-FALSE-PROVED (open, not a pass): {len(known)}  " + ", ".join(f"{i}@{c}" for i, c, _s, _x in known))
    if xfixed:
        print("XFIXED (known-open, now cleanly refused; retire the marker): " + ", ".join(f"{i}@{c}" for i, c, _s, _x in xfixed))
    print(f"TWIN-LOST (precision, not soundness): {len(lost)}  " + ", ".join(f"{i}@{c}{'(known)' if x['class'] != 'TWIN-LOST' else ''}" for i, c, _s, x in lost))
    print(f"ERROR (no verdict): {len(errors)}")
    for i, c, s, x in errors:
        print(f"  {i}@{c} {s}: {clip(x['detail'], 300)}")
    if bad_witness:
        print("Witnesses not confirmed: " + ", ".join(f"{r['id']} ({r['witness']['status']}: {clip(r['witness']['detail'], 160)})" for r in bad_witness))

    strict_fail = [(i, c, s, x["class"]) for i, c, s, x in cells_of(lambda s, x: x["class"] in STRICT_RED)]
    strict_fail += [(r["id"], "witness", "-", r["witness"]["status"]) for r in bad_witness]
    # A run that judged nothing is not a pass: every requested cell skipped or n/a
    # (no verifier available, or a --filter/--verifiers pair that never meets).
    judged = cells_of(lambda s, x: s == "reproducer" and x["verdict"] not in (SKIPPED, NA))
    if not judged:
        print("VACUOUS: no verifier judged any reproducer (every cell skipped or n/a); not a pass")
        strict_fail.append(("-", "-", "-", "VACUOUS"))
    print()
    if args.strict:
        print(f"STRICT: {len(strict_fail)} failing cell(s)" + (": " if strict_fail else "") +
              ", ".join(f"{i}@{c}:{s}={k}" for i, c, s, k in strict_fail[:80]) + (" ..." if len(strict_fail) > 80 else ""))
    print("Gate: blocks no push or landing yet, a defect (docs/STATUS.md 'Not on yet'; docs/PLAN.md PKG-CORE3).")

    if args.json:
        Path(args.json).write_text(json.dumps(
            {"banner": dict(banner), "results": results, "totals": totals,
             "strict_failures": [list(f) for f in strict_fail]},
            indent=1, sort_keys=True, default=str) + "\n")
    if not args.keep_work:
        shutil.rmtree(work, ignore_errors=True)
    else:
        log(f"work dir kept: {work}")
    return 1 if (args.strict and strict_fail) else 0


# ---------------------------------------------------------------------------
# Self-test
# ---------------------------------------------------------------------------


def self_test(args) -> int:
    """Run the runner against fake verifiers and assert what --strict does.

    Every fake lives in tests/trust-soundness-corpus/selftest/. `fake_verifier.py`
    plays each verifier (trustc, the trust-vc syn adapter, trust-vc-driver, clean,
    the trust-wp adapter, ay) in one MODE: missing (a path that does not exist),
    false (/usr/bin/false), crash (SIGSEGV), late-crash (the oracle's answer, then
    SIGSEGV), hang (sleeps past --timeout), proved
    (everything proved), refused (everything refused) and oracle (exactly what the
    entries expect). With a real trustc it also runs the anchor-liveness check: a
    wrapper that rewrites ONLY each entry's anchored row, to proved for a reproducer
    and to failed for a twin, must turn every reproducer FALSE-PROVED and every
    twin TWIN-LOST.
    """
    fake = SELFTEST / "fake_verifier.py"
    py = sys.executable
    tmp = Path(tempfile.mkdtemp(prefix="sbc-selftest-"))
    failures = []
    entries = load_entries()
    probs = validate_entries(entries)
    if probs:
        print("FAIL entry checks:\n  " + "\n  ".join(probs))
        return 1
    print(f"entry checks: {len(entries)} entries pass")

    def tool(role, mode):
        if mode == "missing":
            return str(tmp / "does-not-exist" / role)
        if mode == "false":
            return "/usr/bin/false"
        if role == "trust-wp":
            # The runner hands the trust-wp adapter to python, so this fake is a script.
            p = tmp / f"{role}-{mode}.py"
            p.write_text(f"import os, sys\nos.environ.update(SBC_FAKE_ROLE={role!r}, SBC_FAKE_MODE={mode!r})\n"
                         f"os.execv({py!r}, [{py!r}, {str(fake)!r}, *sys.argv[1:]])\n")
            return str(p)
        p = tmp / f"{role}-{mode}"
        p.write_text(f"#!/bin/sh\nSBC_FAKE_ROLE={role} SBC_FAKE_MODE={mode} exec '{py}' '{fake}' \"$@\"\n")
        p.chmod(0o755)
        return str(p)

    families = {
        "trustc": (["trustc-default", "trustc-advisory", "trustc-certify"], "TRUSTC"),
        "trust-vc-syn": (["trust-vc-syn"], "TRUST_VC_SYN_ADAPTER"),
        "trust-vc-mir": (["trust-vc-mir"], "TRUST_VC_MIR_DRIVER"),
        "clean": (["clean-external"], "CLEAN_BIN"),
        "trust-wp": (["trust-wp"], "TRUST_WP_ADAPTER"),
    }

    def invoke(name, env_over, verifiers, extra=()):
        out_json = tmp / f"{name}.json"
        env = dict(os.environ)
        for k in ("TRUSTC", "TRUST_VC_SYN_ADAPTER", "TRUST_VC_MIR_DRIVER", "CLEAN_BIN", "TRUST_WP_ADAPTER", "AY_BIN"):
            env.pop(k, None)
        env.update(env_over)
        argv = [py, str(Path(__file__).resolve()), "--strict", "--json", str(out_json), "--timeout", "8",
                "--verifiers", ",".join(verifiers), *extra]
        rc, out, err = run(argv, env=env, timeout=3600)
        res = json.loads(out_json.read_text()) if out_json.exists() else None
        (tmp / f"{name}.log").write_text(out + "\n--- stderr\n" + err)
        return rc, res

    def check(name, cond, why):
        print(f"  {'ok  ' if cond else 'FAIL'} {name}: {why}")
        if not cond:
            failures.append(f"{name}: {why}")

    def cells(res, verifiers):
        for r in res["results"]:
            for v in verifiers:
                cell = r["verifiers"].get(v)
                if cell:
                    yield r["id"], v, cell

    # The verdict rules themselves, on synthetic entries: no corpus entry is known-open
    # or build-accepted today, so the fakes below cannot reach these paths.
    print("classification:")
    syn = {"id": "synthetic", "lang": "rust", "known_open": {"trustc-default": "a pointer"}}
    for verdict, want in (((PROVED, "x"), "KNOWN-FALSE-PROVED"), ((REFUSED, "x"), "XFIXED"),
                          ((ERROR, "trustc died on signal 11"), "ERROR(known-open)"),
                          ((SKIPPED, "no trustc"), "SKIPPED")):
        got = classify(syn, "trustc-default", "reproducer", verdict)
        check(f"known-open {verdict[0]}", got == want, f"classified {got} (want {want})")
    plain = {"id": "synthetic", "lang": "rust"}
    for verdict, side, want in (((ERROR, "anchor-miss: no row"), "reproducer", "ERROR"),
                                ((REFUSED, "x"), "reproducer", "ok"),
                                ((REFUSED, "x"), "twin", "TWIN-LOST"),
                                ((ERROR, "x"), "twin", "ERROR")):
        got = classify(plain, "trustc-default", side, verdict)
        check(f"plain {side} {verdict[0]}", got == want, f"classified {got} (want {want})")
    ba = {"id": "synthetic", "lang": "rust", "reproducer": {"function": "f", "mode": "build-accepted"}}
    for rc_, err_, want in ((1, "", ERROR), (1, "error[E0308]: mismatched types\n", REFUSED),
                            (0, "", PROVED), (101, "error: internal compiler error\n", ERROR),
                            (None, "[timeout after 8s]", ERROR)):
        got = trustc_level_verdict(ba, "reproducer", rc_, {}, err_)[0]
        check(f"build-accepted exit {rc_}", got == want, f"{got} (want {want})")
    ak = {"id": "synthetic", "lang": "rust", "reproducer": {"function": "f", "mode": "assumption-kept"}}
    got = trustc_level_verdict(ak, "reproducer", 0, {"sbc::f": []}, "")[0]
    check("assumption-kept, empty result", got == ERROR, f"{got} (want {ERROR})")

    by_id = {e["id"]: e for e in entries}
    for fam, (vs, envvar) in families.items():
        print(f"family {fam} ({', '.join(vs)}):")
        base = {"TRUST_WP_DIR": str(tmp)} if fam == "trust-wp" else {}
        if fam == "trust-wp":
            base["TRUST_WP_PYTHON"] = py
        modes = ["missing", "false", "crash", "late-crash", "hang", "proved", "refused", "oracle"]
        if fam == "trustc":
            modes.insert(5, "anchor-miss")
        for mode in modes:
            env = dict(base)
            env[envvar] = tool(fam, mode)
            if fam == "trust-vc-mir":
                env["TRUSTC"] = tool("trustc", "oracle")
            name = f"{fam}-{mode}"
            rc, res = invoke(name, env, vs, ["--no-witness"])
            if res is None:
                check(name, False, f"the runner wrote no JSON (exit {rc}; log {tmp / (name + '.log')})")
                continue
            got = list(cells(res, vs))
            applicable = [(i, v, c) for i, v, c in got if c["reproducer"]["class"] != "n/a"]
            check(name, bool(applicable), f"{len(applicable)} applicable cell(s)")
            if mode in ("missing", "false", "crash", "late-crash", "hang", "anchor-miss"):
                passing = [f"{i}@{v}" for i, v, c in applicable for s in SIDES if c[s]["class"] in PASSING - {"n/a"}]
                check(name, rc == 1, f"--strict exit {rc} (want 1)")
                check(name, not passing, f"no cell passes ({', '.join(passing[:6]) or 'none'})")
            elif mode == "proved":
                bad = [f"{i}@{v}" for i, v, c in applicable
                       if c["reproducer"]["class"] not in ("FALSE-PROVED", "KNOWN-FALSE-PROVED")]
                check(name, rc == 1, f"--strict exit {rc} (want 1)")
                check(name, not bad, f"every reproducer red ({', '.join(bad[:6]) or 'all'})")
            elif mode == "refused":
                bad = [f"{i}@{v}" for i, v, c in applicable
                       if c["twin"]["expect"] == "proved" and not c["twin"]["class"].startswith("TWIN-LOST")]
                check(name, rc == 1, f"--strict exit {rc} (want 1)")
                check(name, not bad, f"every twin expected proved is TWIN-LOST ({', '.join(bad[:6]) or 'all'})")
            elif mode == "oracle":
                bad = [f"{i}@{v}:{s}={c[s]['class']}" for i, v, c in applicable for s in SIDES
                       if c[s]["class"] not in PASSING | NOT_A_PASS]
                expected_rc = int(any(c[s]["class"] in STRICT_RED for _i, _v, c in applicable for s in SIDES))
                check(name, rc == expected_rc, f"--strict exit {rc} (want {expected_rc}: recorded false proofs still fail)")
                check(name, not bad, f"every cell matches its declared classification ({', '.join(bad[:6]) or 'all'})")

    # Under an always-refused verifier set, every entry with a control loses a twin.
    print("controls:")
    lost_by_entry = {}
    for fam, (vs, envvar) in families.items():
        p = tmp / f"{fam}-refused.json"
        if p.exists():
            for i, v, c in cells(json.loads(p.read_text()), vs):
                if c["twin"]["class"].startswith("TWIN-LOST"):
                    lost_by_entry.setdefault(i, []).append(v)
    for e in entries:
        if e.get("no_control"):
            print(f"  --   control {e['id']}: no-control ({clip(e['no_control'], 140)})")
        else:
            check(f"control {e['id']}", e["id"] in lost_by_entry, "an always-refused verifier loses its twin in "
                  + (", ".join(lost_by_entry.get(e["id"], [])) or "NO verifier"))

    # A run that judges nothing: a verifier that reads no entry the filter keeps.
    print("vacuous:")
    rc, res = invoke("vacuous", {"CLEAN_BIN": tool("clean", "oracle")}, ["clean-external"],
                     ["--no-witness", "--filter", "^al02-"])
    if res:
        vac = [f for f in res.get("strict_failures", []) if f[-1] == "VACUOUS"]
        check("vacuous", rc == 1 and bool(vac), f"--strict exit {rc} (want 1), VACUOUS reported: {bool(vac)}")
    else:
        check("vacuous", False, f"the runner wrote no JSON (exit {rc})")

    # Witnesses: a compiler whose witness binaries print the wrong thing, and an ay
    # that answers sat with a model that falsifies the problem, are both red.
    print("witnesses:")
    real_ay = os.environ.get("AY_BIN") or shutil.which("ay")
    rc, res = invoke("witness-wrong", {"TRUSTC": tool("trustc", "witness-wrong"),
                                       "AY_BIN": tool("ay", "badmodel" if real_ay else "unsat"),
                                       "SBC_REAL_AY": real_ay or ""},
                     ["trustc-default"])
    if res:
        bad = [r["id"] for r in res["results"] if r.get("witness", {}).get("status") == "ok"]
        check("witness-wrong", rc == 1, f"--strict exit {rc} (want 1)")
        check("witness-wrong", not bad, f"no witness confirmed ({', '.join(bad) or 'none'})")
    rc, res = invoke("ay-unsat", {"TRUSTC": tool("trustc", "oracle"), "AY_BIN": tool("ay", "unsat")},
                     ["clean-external"], ["--filter", "^(ay|clean)-"])
    if res:
        bad = [r["id"] for r in res["results"] if r.get("witness", {}).get("status") == "ok"]
        check("ay-unsat", not bad and rc == 1, f"exit {rc}; an ay answering unsat confirms nothing ({', '.join(bad) or 'none'})")

    # Anchor liveness against the real compiler.
    real, why = resolve_trustc()
    if why or not real or os.environ.get("SBC_SELFTEST_NO_LIVENESS"):
        print(f"anchor liveness: NOT RUN ({why or 'SBC_SELFTEST_NO_LIVENESS'})")
    else:
        print(f"anchor liveness against {os.path.realpath(real)}:")
        for mode, want_rep, want_twin in (("flip", "FALSE-PROVED", "TWIN-LOST"), ("anchor-only", "ok", "ok")):
            env = {"TRUSTC": tool("trustc", f"wrap-{mode}"), "SBC_REAL_TRUSTC": real}
            rc, res = invoke(f"liveness-{mode}", env, ["trustc-default"], ["--no-witness", "--timeout", "900"])
            if not res:
                check(f"liveness-{mode}", False, f"no JSON (exit {rc})")
                continue
            for i, v, c in cells(res, ["trustc-default"]):
                e = by_id[i]
                if e["reproducer"].get("mode", "obligation") != "obligation":
                    continue
                rc_ = c["reproducer"]["class"]
                tw = c["twin"]
                if mode == "flip":
                    ok_rep = rc_ in ("FALSE-PROVED", "KNOWN-FALSE-PROVED")
                    ok_tw = tw["expect"] != "proved" or tw["class"].startswith("TWIN-LOST")
                    check(f"liveness-flip {i}", ok_rep and ok_tw,
                          f"anchored rows flipped: reproducer {rc_}, twin {tw['class']}")
                else:
                    # Every row EXCEPT the anchored ones made proved, the anchored
                    # reproducer row made failed: the reproducer must not be proved,
                    # and the twin, anchored row made proved, must be.
                    ok_rep = rc_ in ("ok", "XFIXED")
                    ok_tw = tw["class"] == "ok"
                    check(f"liveness-anchor-only {i}", ok_rep and ok_tw,
                          f"only the anchored row decides: reproducer {rc_}, twin {tw['class']}")
    print()
    if failures:
        print(f"SELF-TEST FAILED: {len(failures)} check(s); logs in {tmp}")
        return 1
    print("SELF-TEST PASSED")
    if not args.keep_work:
        shutil.rmtree(tmp, ignore_errors=True)
    return 0


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--filter", help="regex over entry ids")
    ap.add_argument("--verifiers", help="comma-separated subset of " + ",".join(ALL_VERIFIERS))
    ap.add_argument("--json", help="write the full result table here")
    ap.add_argument("--no-witness", action="store_true", help="do not build and run witnesses")
    ap.add_argument("--strict", action="store_true",
                    help="exit 1 on any FALSE-PROVED (including known-open), XFIXED, SKIPPED, unwhitelisted ERROR, TWIN-LOST "
                         "(not known) or unconfirmed witness, or when nothing was judged "
                         "(the gate is non-blocking until it judges 0 proved reproducers)")
    ap.add_argument("--timeout", type=int, help="cap every verifier call at this many seconds")
    ap.add_argument("--self-test", action="store_true", help="run the runner against fake verifiers")
    ap.add_argument("--keep-work", action="store_true")
    ap.add_argument("--jobs", "-j", type=int, default=int(os.environ.get("TRUST_SOUNDNESS_CORPUS_JOBS", "4")),
                    help="entries run concurrently (default 4)")
    args = ap.parse_args()
    if args.self_test:
        return self_test(args)
    return corpus_run(args)


if __name__ == "__main__":
    sys.exit(main())
