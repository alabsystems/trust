#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Licensed under the Apache License, Version 2.0
"""Fake verifiers for `scripts/trust-soundness-corpus.py --self-test`.

One program plays every verifier the runner drives. SBC_FAKE_ROLE names which:
trustc, trust-vc-syn (the syn adapter), trust-vc-mir (trust-vc-driver), clean,
trust-wp (the trust-wp adapter) or ay. SBC_FAKE_MODE names how it behaves:

  crash        dies on SIGSEGV
  late-crash   answers as oracle, flushes the answer, then dies on SIGSEGV (a verdict
               printed by a verifier that then crashed is no verdict)
  hang         sleeps for an hour (the runner's --timeout must end it)
  proved       proves everything it is asked
  refused      refuses everything it is asked
  oracle       answers exactly what each entry expects (known-open bugs included)
  witness-wrong (trustc) as oracle, but every witness binary prints the wrong text
  anchor-miss  (trustc) emits rows for every function, none of them the anchored row
               (a decoy at another line, a reproducer's failed, a twin's proved), and
               an empty result for an assumption-kept side: no verdict exists
  wrap-flip    (trustc) runs SBC_REAL_TRUSTC and rewrites ONLY the anchored rows:
               a reproducer's to proved, a twin's to failed
  wrap-anchor-only (trustc) runs SBC_REAL_TRUSTC, makes every row proved except the
               anchored reproducer rows, which it makes failed
  unsat        (ay) answers unsat
  badmodel     (ay) runs SBC_REAL_AY and perturbs every value in its models

It knows the entries only through the runner's own entry and anchor code, so a fake
oracle and the runner cannot disagree about where a claim lives.
"""

from __future__ import annotations

import importlib.util
import json
import os
import re
import signal
import subprocess
import sys
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
RUNNER_PATH = HERE.parent.parent.parent / "scripts" / "trust-soundness-corpus.py"
_spec = importlib.util.spec_from_file_location("sbc_runner", RUNNER_PATH)
R = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(R)

ROLE = os.environ.get("SBC_FAKE_ROLE", "")
MODE = os.environ.get("SBC_FAKE_MODE", "")
LANE_OF_FLAG = {"-Ztrust-policy=advisory": "trustc-advisory", "-Ztrust-policy=certify": "trustc-certify"}


def entry_for(path: str):
    """The corpus entry a source/certificate path belongs to (by directory)."""
    d = Path(path).resolve().parent
    for e in R.load_entries():
        if e["_dir"].resolve() == d:
            return e
    return None


def die_or_hang():
    if MODE == "crash":
        os.kill(os.getpid(), signal.SIGSEGV)
    if MODE == "hang":
        time.sleep(3600)


def late_crash():
    """After the answer is out: the late-crash mode dies here."""
    if MODE == "late-crash":
        sys.stdout.flush()
        sys.stderr.flush()
        os.kill(os.getpid(), signal.SIGSEGV)


def oracle_proves(e, verifier, side):
    """What the oracle answers: the state the entry records as true today."""
    known = e.get("known_open", {}).get(verifier)
    if side == "reproducer":
        return bool(known)
    if known or e.get("known_twin_lost", {}).get(verifier):
        return False
    return R.expectation(e, verifier, "twin") == "proved"


def answer(e, verifier, side):
    if MODE == "proved":
        return True
    if MODE == "refused":
        return False
    return oracle_proves(e, verifier, side)


# ------------------------------------------------------------------ trustc


def fake_rows(e, side, proved):
    spec = e[side]
    mode = spec.get("mode", "obligation")
    if MODE == "anchor-miss":
        if mode != "obligation":
            return []
        # The decoy alone: failed for a reproducer (once read as a refusal), proved for a twin.
        return fake_rows_anchored(e, side, side == "reproducer")[1:]
    if mode == "assumption-kept":
        if proved:
            return [{"kind": "assumption:assumed-total", "outcome": "skipped", "location": {}}]
        return [{"kind": "overflow:add", "outcome": "failed", "location": {}}]
    return fake_rows_anchored(e, side, proved)


def fake_rows_anchored(e, side, proved):
    """[the anchored row, a decoy with the opposite outcome at another place]."""
    a = R.anchor_of(e, side)
    kind = a["kind"] if ":" in a["kind"] else a["kind"] + ":fake"
    loc = {"file": str(e["_dir"] / a["file"]), "line_start": a["line"]} if a.get("line") else {
        "file": "core/src/panic.rs", "line_start": 62}
    row = {"kind": kind, "outcome": "proved" if proved else "failed", "location": loc,
           "typed_kind": {"Assertion": {"message": a.get("message", "")}}, "description": ""}
    # A decoy with the opposite outcome: the runner must read the anchored row, not this.
    decoy = {"kind": kind, "outcome": "failed" if proved else "proved",
             "location": {"file": loc["file"], "line_start": (loc["line_start"] or 0) + 1000},
             "typed_kind": {"Assertion": {"message": "decoy"}}, "description": "decoy"}
    return [row, decoy]


def emit(fn, rows):
    print("TRUST_JSON:" + json.dumps({"type": "function_result", "function": fn, "results": rows}))


def trustc(argv):
    if "-vV" in argv:
        print(f"rustc 0.0.0-fake ({MODE})\nbinary: trustc")
        return 0
    if "--print" in argv:
        print(str(HERE))
        return 0
    if MODE.startswith("wrap-") and "-Ztrust-verify=on" not in argv:
        os.execv(os.environ["SBC_REAL_TRUSTC"], [os.environ["SBC_REAL_TRUSTC"], *argv])
    die_or_hang()
    out = argv[argv.index("-o") + 1] if "-o" in argv else None
    if "-Ztrust-verify=off" in argv:
        if "rlib" in argv:
            Path(out).write_bytes(b"")
            return 0
        # A witness binary that prints the wrong thing and exits 0.
        Path(out).write_text("#!/bin/sh\necho 'fake witness: nothing happened'\nexit 0\n")
        os.chmod(out, 0o755)
        return 0
    src = argv[-1]
    e = entry_for(src)
    lane = next((LANE_OF_FLAG[a] for a in argv if a in LANE_OF_FLAG), "trustc-default")
    if MODE.startswith("wrap-"):
        return wrap(argv, e)
    failed = False
    for side in R.SIDES:
        if e is None or Path(R.side_source(e, side)).name != Path(src).name:
            continue
        rows = fake_rows(e, side, answer(e, lane, side) if MODE != "witness-wrong" else oracle_proves(e, lane, side))
        failed |= any(r["outcome"] == "failed" for r in rows)
        emit("sbc::" + e[side]["function"], rows)
    late_crash()
    return 1 if failed else 0


def wrap(argv, e):
    real = os.environ["SBC_REAL_TRUSTC"]
    p = subprocess.run([real, *argv], capture_output=True, text=True)
    src = argv[-1]
    sides = {}
    for side in R.SIDES:
        if e and e[side].get("mode", "obligation") == "obligation" and Path(R.side_source(e, side)).name == Path(src).name:
            sides["sbc::" + e[side]["function"]] = (side, R.anchor_of(e, side))

    def rewrite(text):
        lines = []
        for line in text.splitlines():
            i = line.find("TRUST_JSON:")
            if i >= 0:
                try:
                    j = json.loads(line[i + len("TRUST_JSON:"):])
                except ValueError:
                    j = None
                if j and j.get("type") == "function_result" and j.get("function") in sides:
                    side, anchor = sides[j["function"]]
                    for r in j.get("results", []):
                        hit = R.row_matches(r, anchor)
                        if MODE == "wrap-flip":
                            if hit:
                                r["outcome"] = "proved" if side == "reproducer" else "failed"
                        else:  # wrap-anchor-only
                            if hit:
                                r["outcome"] = "failed" if side == "reproducer" else "proved"
                            else:
                                r["outcome"] = "proved"
                    line = line[:i] + "TRUST_JSON:" + json.dumps(j)
            lines.append(line)
        return "\n".join(lines) + ("\n" if lines else "")

    sys.stdout.write(rewrite(p.stdout))
    sys.stderr.write(rewrite(p.stderr))
    # The rewrite tests the anchors, not the compiler's exit: a crash after the rows
    # is the crash fakes' business.
    return 1 if p.returncode not in (0,) else 0


# ------------------------------------------------------------------ trust-vc


def trust_vc_syn(argv):
    die_or_hang()
    src, fn = argv[0], argv[1]
    e = entry_for(src)
    side = next(s for s in R.SIDES if e[s]["function"] == fn)
    white = e.get("expected_refusal", {}).get("trust-vc-syn", {}).get(side)
    if MODE in ("oracle", "late-crash") and white:
        print(json.dumps({"verdict": "error", "raw": white}))
    elif answer(e, "trust-vc-syn", side):
        print(json.dumps({"verdict": "proved", "raw": ""}))
    else:
        print(json.dumps({"verdict": "refuted" if side == "reproducer" else "not-proved", "raw": "fake"}))
    late_crash()
    return 0


def trust_vc_mir(argv):
    if "--print" in argv:
        print(str(HERE))
        return 0
    die_or_hang()
    src = argv[-1]
    e = entry_for(src)
    failed = 0
    for side in R.SIDES:
        fn = e[side]["function"]
        ok = answer(e, "trust-vc-mir", side)
        failed += not ok
        print(f"TRUST_VC_DRIVER_RESULT\t{fn}\t{'Verified' if ok else 'Refuted'}\tfake")
    print(f"TRUST_VC_DRIVER_SUMMARY\t{len(R.SIDES)}\t{len(R.SIDES) - failed}\t{failed}\t0\t0\t0")
    late_crash()
    return 1 if failed else 0


# ------------------------------------------------------------------ clean


def clean(argv):
    cert = argv[-1]
    if Path(cert).name == "clean-probe.json":
        print("External certificate verification: PASSED")
        return 0
    die_or_hang()
    e = entry_for(cert)
    side = next(s for s in R.SIDES if Path(e[s]["cert"]).name == Path(cert).name)
    if answer(e, "clean-external", side):
        print("External certificate verification: PASSED")
        late_crash()
        return 0
    print("External certificate verification: FAILED\n  Error: fake refusal")
    late_crash()
    return 1


# ------------------------------------------------------------------ trust-wp


def trust_wp(argv):
    die_or_hang()
    cases = Path(argv[argv.index("--cases") + 1])
    out = Path(argv[argv.index("--json") + 1])
    by_case = {e["id"].replace("-", "_"): e for e in R.load_entries() if e["lang"] == "creusot"}
    res = {}
    for f in sorted(cases.glob("*.rs")):
        e = by_case.get(f.stem)
        fns = re.findall(r"\bfn (\w+)", f.read_text())
        if MODE == "proved":
            credited = fns
        elif MODE == "refused" or e is None:
            credited = []
        else:
            credited = [e[s]["function"] for s in R.SIDES if oracle_proves(e, "trust-wp", s)]
        res[f.stem] = {"verdict": "fake", "verified_functions": credited, "assertion_credits": [],
                       "unproved_assertion_functions": [], "trust_wp_lines": [], "error": None}
    out.write_text(json.dumps(res))
    late_crash()
    return 0


# ------------------------------------------------------------------ ay


def ay(argv):
    die_or_hang()
    script = Path(argv[-1]).read_text()
    checks = len(re.findall(r"\(check-sat", script))
    if MODE == "unsat":
        print("unsat\n" * checks, end="")
        return 0
    p = subprocess.run([os.environ["SBC_REAL_AY"], *argv], capture_output=True, text=True)

    def perturb(m):
        v = m.group(2)
        if v == "true":
            nv = "false"
        elif v == "false":
            nv = "true"
        else:
            nv = "6" if v == "5" else "5"
        return m.group(1) + nv + m.group(3)

    # Every literal body of a model define-fun changes: true<->false, an Int to 5 (or 6).
    print(re.sub(r"(\(define-fun\s+\S+\s+\((?:\s*\([^()]*\))*\s*\)\s+\S+\s+)(true|false|\d+)(\s*\))", perturb, p.stdout))
    return 0


def main():
    argv = sys.argv[1:]
    fn = {"trustc": trustc, "trust-vc-syn": trust_vc_syn, "trust-vc-mir": trust_vc_mir,
          "clean": clean, "trust-wp": trust_wp, "ay": ay}[ROLE]
    return fn(argv)


if __name__ == "__main__":
    sys.exit(main())
