#!/usr/bin/env python3
"""Grade a `trustc -Ztrust-verify-output=json` wire for the two-language battery.

The battery's verification-ON rows are green only if the WIRE — the JSON
transport `targo trust` reads — says every obligation was PROVED. The first
grader counted only `proved` / `failed` / `unknown` and tested for
", 0 unknown, 0 failed", so a wire whose single obligation was
`runtime_checked` ("solver reported Proved without exact kernel/native proof
authority") printed `0 proved, 0 unknown, 0 failed` and was graded clean.
Measured 2026-09-15 on the sealed pack `43f8b339f`: battery row r08 read PASS
with functions_verified=0 / total_runtime_checked=1 — a vacuous green.

This grader closes that class rather than that instance:

  * every outcome the transport can carry is tallied — `proved`, `failed`,
    `unknown`, `timeout`, `runtime_checked`, `skipped`, `unsupported`,
    `canceled`, `rejected` (crates/trust-types/src/outcome.rs) — and any
    spelling it does NOT know is counted as `other`, never ignored;
  * clean means: at least one function result, at least one PROVED
    obligation (a wire that proved nothing verified nothing), and ZERO rows of
    every other outcome;
  * the `crate_summary` row must be present and must AGREE with the
    per-function tallies — an absent or disagreeing summary is not clean;
  * an empty wire is not clean. The caller decides whether a wire was expected
    at all (rows compiled with `-Ztrust-verify=off` never ask this grader).

Two tolerances exist, each explicit, narrow and named on the printed line:

  * `--tolerate-print-gap` accepts the std print backend's gap in the two
    shapes the compiler has emitted it: an `unknown` row whose kind is
    `native-verification-gap` (the bundled `ReentrantLock` member, older
    toolchains), and — measured 2026-09-17 on a HEAD stage1 — a
    `runtime_checked` row of kind `assert` that the COMPILER classes
    `"gap_class": "std-print-dispatch"`. That row is the function's
    whole-function panic-freedom AGGREGATE, named after its first marked
    panic site, and the class is trustc's attestation — made where the fold is
    visible — that EVERY panic site folded under it is std's `_print`/`_eprint`
    reached as an absent callee (whose only unproved obligation is std's own
    DEFINED write-failure panic, which no proof can discharge). A user
    `assert!`, another absent callee, drop glue, or a user `Display` folded
    under the same row leaves it unclassed. The grader never re-derives the
    class from the prose description, and an unclassed `runtime_checked` row,
    a `failed` row of that class, or a class it does not know stays
    non-clean;

A negative-control caller may add `--require-failed-in FUNCTION
--require-failed-obligation SUBSTRING` (both, FUNCTION verbatim from the wire's
`function` field; the substring may contain colons, as the compiler's kind tags
do); the line then ends with `required_failed=yes|no` (that function carries a
`failed` row whose obligation_id contains the substring). It never makes a wire
clean.
  * `--tolerate-requires-assumption` accepts `skipped` rows whose kind is
    `assumption:requires` — a function's OWN precondition, which its body
    assumes and its callers must prove. Measured 2026-09-16 on the pack: row
    r06's wire is 3 proved + 2 such rows while the human summary says
    "5 proved"; the first grader saw neither the skips nor the disagreement.

Both still require proved >= 1 and every other counter at zero, and neither
covers any other kind under the same outcome.

A wire cannot vouch for the process that wrote it. The rows are written while
the compiler runs; a panic at session TEARDOWN comes after every one of them.
Measured on stage2 `db07002ff` (2026-09-16) and again on stage2 `9b4c6b3ab`
(2026-09-17, the parent of the fix): a contract-only, island-free crate under
`-Ztrust-verify-output=json --error-format=human` wrote "3 proved, 0 unknown,
0 failed" plus an agreeing `crate_summary`, and THEN died with
`trimmed_def_paths called, diagnostics were expected but none were emitted`
(exit 101). The previous grader, fed that stream, printed `clean=yes` for an
ICE: its callers piped the compiler into it, so it never saw the status. So:

  * `--exit-code N` is REQUIRED to grade. N is the exit status of the compiler
    run whose stderr is on stdin. Absent, or non-zero, is `clean=no` — there is
    no tolerance for it and no default, because the only honest default for a
    status nobody measured is "unknown". Capture the run to a file, keep `$?`,
    then grade the file; `cmd 2>&1 | wire_grade.py` CANNOT supply it.
  * independently, a compiler-crash signature on a NON-transport line
    (`panicked at`, `internal compiler error`, `the compiler unexpectedly
    panicked`) is `clean=no` even with `--exit-code 0`, so a caller that
    reports the wrong process's status (a pipeline's last stage, a wrapper
    that swallows 101) is still caught. Text INSIDE a `TRUST_JSON` row is
    payload and is never read as a signature.

The compiler's `crate_summary` folds `timeout`, `skipped` and every
non-proved/failed/runtime_checked outcome into its `total_unknown` aggregate
(trust_verify.rs, emit_transport_json) — the agreement check here reproduces
that fold exactly rather than trusting either side alone.

`--selftest` proves the grader can fail: each synthetic wire below must grade
exactly as recorded, including the `runtime_checked` wire that the previous
grader accepted. Nothing here needs a toolchain.

stdin:  raw compiler stderr (TRUST_JSON lines are graded; every other line is
        scanned for a compiler-crash signature only)
stdout: one line —
  wire: F fns, P proved, U unknown, X failed, R runtime-checked, S skipped,
        T timed-out, O other | nonclean=<labels or -> | tolerated=<labels or ->
        | summary=<agree|absent|disagree(...)> | exit=<N|absent>
        | clean=<yes|no(reason)>
exit:   0 after grading (the caller reads `clean=`); --selftest exits 1 on any
        divergence.

Author: Andrew Yates <andrewyates.name@gmail.com>
Copyright 2026 Andrew Yates | License: Apache 2.0
"""
import json
import os
import sys

PREFIX = "TRUST_JSON"
KNOWN = ("proved", "failed", "unknown", "timeout", "runtime_checked", "skipped",
         "unsupported", "canceled", "rejected")
PRINT_GAP_KIND = "native-verification-gap"
# The compiler's own classification of the std print backend's absent-callee
# panic-freedom row (`TransportObligationResult::gap_class`, stamped from the
# same recognizer its policy-B decision consults). The row is `runtime_checked`
# with kind `assert`; std's write-failure panic is DEFINED behaviour, so no proof
# of that row can ever exist — the honest disposition is the disclosed tolerance.
PRINT_GAP_CLASS = "std-print-dispatch"
REQUIRES_KIND = "assumption:requires"
# What a dead compiler leaves on stderr. Matched on NON-transport lines only.
CRASH_SIGNATURES = ("panicked at", "internal compiler error",
                    "the compiler unexpectedly panicked")


def parse(lines):
    """Return (function_results, crate_summaries, crash) from raw stderr lines.

    `crash` is the first non-transport line carrying a compiler-crash
    signature (stripped), or None."""
    fns, summaries, crash = [], [], None
    for line in lines:
        i = line.find(PREFIX)
        if i < 0:
            if crash is None and any(sig in line for sig in CRASH_SIGNATURES):
                crash = line.strip()
            continue
        j = line.find("{", i)
        if j < 0:
            continue
        try:
            d = json.loads(line[j:])
        except Exception:
            continue
        t = d.get("type")
        if t == "function_result":
            fns.append(d)
        elif t == "crate_summary":
            summaries.append(d)
    return fns, summaries, crash


def grade(lines, tolerate_print_gap=False, tolerate_requires=False, exit_code=None,
          require_failed=None):
    """Grade one wire.

    `exit_code` is the compiler's exit status (int), or None when the caller did
    not supply one — which is never clean.

    `require_failed`: `(FUNCTION, OBLIGATION-SUBSTRING)` — a negative-control
    caller's demand that THAT function (the wire's `function` field, verbatim)
    carry a `failed` row whose obligation_id contains the substring (which may
    itself contain colons: the compiler's kind tags do); reported as
    `required_failed=yes|no` on the line, never as clean."""
    fns, summaries, crash = parse(lines)
    required_failed = None
    if require_failed:
        want_fn, want_sub = require_failed
        required_failed = any(
            f.get("function") == want_fn and r.get("outcome") == "failed"
            and want_sub in (r.get("obligation_id") or "")
            for f in fns for r in (f.get("results") or []))
    counts = {k: 0 for k in KNOWN}
    counts["other"] = 0
    nonclean, tolerated = set(), set()
    tolerated_unknown = tolerated_skipped = tolerated_runtime_checked = 0
    for f in fns:
        for r in f.get("results") or []:
            o = r.get("outcome")
            if o == "proved":
                counts["proved"] += 1
                continue
            kind = r.get("kind") or r.get("message") or r.get("description") or "?"
            label = "%s:%s" % (o, kind)
            if o in counts:
                counts[o] += 1
            else:
                counts["other"] += 1
            if tolerate_print_gap and o == "unknown" and kind == PRINT_GAP_KIND:
                tolerated_unknown += 1
                tolerated.add(label)
            elif (tolerate_print_gap and o == "runtime_checked" and kind == "assert"
                  and r.get("gap_class") == PRINT_GAP_CLASS):
                # Only the row the COMPILER classed as the std print backend, only as
                # a runtime-checked assertion. A `failed` row with the same class, a
                # class the grader does not know, or an unclassed runtime_checked row
                # is not covered — those are the vacuous-green class this grader exists
                # to refuse.
                tolerated_runtime_checked += 1
                tolerated.add("%s[%s]" % (label, PRINT_GAP_CLASS))
            elif tolerate_requires and o == "skipped" and kind == REQUIRES_KIND:
                tolerated_skipped += 1
                tolerated.add(label)
            else:
                nonclean.add(label)

    # The compiler's own aggregate: everything that is not proved / failed /
    # runtime_checked lands in `unknown`, and total = the four of them.
    aggregate_unknown = sum(v for k, v in counts.items()
                            if k not in ("proved", "failed", "runtime_checked"))
    total = counts["proved"] + counts["failed"] + counts["runtime_checked"] + aggregate_unknown

    if not summaries:
        summary = "absent"
    elif len(summaries) > 1:
        summary = "disagree(%d crate_summary rows)" % len(summaries)
    else:
        s = summaries[0]
        expect = {
            "functions_analyzed": len(fns),
            "total_proved": counts["proved"],
            "total_failed": counts["failed"],
            "total_unknown": aggregate_unknown,
            "total_timed_out": counts["timeout"],
            "total_skipped": counts["skipped"],
            "total_runtime_checked": counts["runtime_checked"],
            "total_obligations": total,
        }
        diffs = ["%s=%s!=%s" % (k, s.get(k), v) for k, v in expect.items() if s.get(k) != v]
        summary = "agree" if not diffs else "disagree(%s)" % ",".join(diffs)

    # The process verdict comes FIRST: rows written before a teardown panic are
    # complete, agreeing and all-proved, so every check below would pass them.
    reason = None
    if crash is not None:
        reason = "compiler crashed: %s" % crash[:120]
    elif exit_code is None:
        reason = ("compiler exit status not supplied: rows precede a teardown panic, so the "
                  "wire cannot vouch for the process; capture the run, keep $?, and pass "
                  "--exit-code <status>")
    elif exit_code != 0:
        reason = "compiler exited %d" % exit_code
    elif not fns:
        reason = "no function_result on the wire"
    elif counts["proved"] < 1:
        reason = "vacuous: nothing proved"
    elif summary != "agree":
        reason = "crate_summary %s" % summary
    else:
        hard = {k: v for k, v in counts.items()
                if k not in ("proved", "unknown", "skipped", "runtime_checked") and v}
        if counts["runtime_checked"] - tolerated_runtime_checked:
            hard["runtime_checked"] = counts["runtime_checked"] - tolerated_runtime_checked
        if hard:
            reason = "non-proved rows: " + ",".join("%s=%d" % kv for kv in sorted(hard.items()))
        elif counts["unknown"] - tolerated_unknown:
            reason = "unknown rows: %d" % (counts["unknown"] - tolerated_unknown)
        elif counts["skipped"] - tolerated_skipped:
            reason = "skipped rows: %d" % (counts["skipped"] - tolerated_skipped)

    other = counts["other"] + counts["unsupported"] + counts["canceled"] + counts["rejected"]
    line = ("wire: %d fns, %d proved, %d unknown, %d failed, %d runtime-checked, "
            "%d skipped, %d timed-out, %d other | nonclean=%s | tolerated=%s | summary=%s "
            "| exit=%s | clean=%s" % (
                len(fns), counts["proved"], counts["unknown"], counts["failed"],
                counts["runtime_checked"], counts["skipped"], counts["timeout"], other,
                ",".join(sorted(nonclean)) if nonclean else "-",
                ",".join(sorted(tolerated)) if tolerated else "-",
                summary,
                "absent" if exit_code is None else "%d" % exit_code,
                "yes" if reason is None else "no(%s)" % reason))
    if required_failed is not None:
        line += " | required_failed=%s" % ("yes" if required_failed else "no")
    return line, reason is None


# ---- self-test: the grader must be able to FAIL ----------------------------

def _fn(*results):
    return PREFIX + ":" + json.dumps({
        "type": "function_result", "function": "main::main",
        "results": [dict({"obligation_id": "vc:%d" % i, "kind": t[1], "outcome": t[0]},
                         **({"gap_class": t[2]} if len(t) > 2 else {}))
                    for i, t in enumerate(results)],
    })


def _summary(**kw):
    """A crate_summary row; `total_unknown` and `total_obligations` follow the
    compiler's fold unless a case overrides them to model a disagreement."""
    base = {"type": "crate_summary", "functions_analyzed": 1, "functions_verified": 0,
            "total_proved": 0, "total_failed": 0, "total_unknown": None, "total_timed_out": 0,
            "total_skipped": 0, "total_runtime_checked": 0, "total_obligations": None}
    base.update(kw)
    agg = kw.get("agg_unknown", base["total_timed_out"] + base["total_skipped"])
    base.pop("agg_unknown", None)
    if base["total_unknown"] is None:
        base["total_unknown"] = agg
    if base["total_obligations"] is None:
        base["total_obligations"] = (base["total_proved"] + base["total_failed"]
                                     + base["total_runtime_checked"] + base["total_unknown"])
    return PREFIX + ":" + json.dumps(base)


def selftest():
    G, R, C = PRINT_GAP_KIND, REQUIRES_KIND, PRINT_GAP_CLASS
    cases = [
        # name, lines, tolerate_print_gap, tolerate_requires, want_clean
        ("all proved", [_fn(("proved", "assert")), _summary(total_proved=1)], 0, 0, True),
        ("runtime_checked only (the r08 pack wire)",
         [_fn(("runtime_checked", "assert")), _summary(total_runtime_checked=1)], 0, 0, False),
        ("proved + runtime_checked",
         [_fn(("proved", "assert"), ("runtime_checked", "assert")),
          _summary(total_proved=1, total_runtime_checked=1)], 0, 0, False),
        ("skipped", [_fn(("skipped", "assert")), _summary(total_skipped=1)], 0, 0, False),
        ("timeout", [_fn(("timeout", "assert")), _summary(total_timed_out=1)], 0, 0, False),
        ("failed", [_fn(("proved", "a"), ("failed", "b")), _summary(total_proved=1, total_failed=1)], 0, 0, False),
        ("refuted spelling counts as other, not ignored",
         [_fn(("proved", "a"), ("refuted", "b")), _summary(total_proved=1, agg_unknown=1)], 0, 0, False),
        ("unsupported", [_fn(("proved", "a"), ("unsupported", "b")), _summary(total_proved=1, agg_unknown=1)], 0, 0, False),
        ("unknown spelling is not ignored",
         [_fn(("proved", "a"), ("verified", "b")), _summary(total_proved=1, agg_unknown=1)], 0, 0, False),
        ("zero obligations is vacuous", [_fn(), _summary()], 0, 0, False),
        ("empty wire", [], 0, 0, False),
        ("no crate_summary", [_fn(("proved", "assert"))], 0, 0, False),
        ("crate_summary disagrees on proved",
         [_fn(("proved", "assert")), _summary(total_proved=0, total_obligations=1)], 0, 0, False),
        ("crate_summary hides a skip",
         [_fn(("proved", "a"), ("skipped", R)), _summary(total_proved=1, total_skipped=0, agg_unknown=0)], 0, 1, False),
        ("two crate_summary rows",
         [_fn(("proved", "assert")), _summary(total_proved=1), _summary(total_proved=1)], 0, 0, False),
        ("print gap without tolerance",
         [_fn(("proved", "a"), ("unknown", G)), _summary(total_proved=1, agg_unknown=1)], 0, 0, False),
        ("print gap with tolerance",
         [_fn(("proved", "a"), ("unknown", G)), _summary(total_proved=1, agg_unknown=1)], 1, 0, True),
        ("print tolerance does not cover another unknown",
         [_fn(("proved", "a"), ("unknown", "solver-gap")), _summary(total_proved=1, agg_unknown=1)], 1, 0, False),
        ("print tolerance does not cover runtime_checked",
         [_fn(("proved", "a"), ("unknown", G), ("runtime_checked", "b")),
          _summary(total_proved=1, total_runtime_checked=1, agg_unknown=1)], 1, 0, False),
        ("print tolerance still needs a proof",
         [_fn(("unknown", G)), _summary(agg_unknown=1)], 1, 0, False),
        ("classed std print row with tolerance (the r09 HEAD wire, print half)",
         [_fn(("proved", "a"), ("runtime_checked", "assert", C)),
          _summary(total_proved=1, total_runtime_checked=1)], 1, 0, True),
        ("classed std print row without tolerance",
         [_fn(("proved", "a"), ("runtime_checked", "assert", C)),
          _summary(total_proved=1, total_runtime_checked=1)], 0, 0, False),
        ("print tolerance does not cover an unknown class",
         [_fn(("proved", "a"), ("runtime_checked", "assert", "solver-gap")),
          _summary(total_proved=1, total_runtime_checked=1)], 1, 0, False),
        ("print tolerance does not cover a classed FAILED row",
         [_fn(("proved", "a"), ("failed", "assert", C)),
          _summary(total_proved=1, total_failed=1)], 1, 0, False),
        ("print tolerance does not cover a classed non-assert kind",
         [_fn(("proved", "a"), ("runtime_checked", "overflow:add", C)),
          _summary(total_proved=1, total_runtime_checked=1)], 1, 0, False),
        ("print tolerance covers one classed row, not a second unclassed one",
         [_fn(("proved", "a"), ("runtime_checked", "assert", C), ("runtime_checked", "assert")),
          _summary(total_proved=1, total_runtime_checked=2)], 1, 0, False),
        ("classed print row still needs a proof",
         [_fn(("runtime_checked", "assert", C)), _summary(total_runtime_checked=1)], 1, 0, False),
        ("the r09 HEAD wire: 3 proved + 2 requires + 1 classed print row, both tolerances",
         [_fn(("proved", "a"), ("proved", "b"), ("proved", "c"), ("skipped", R), ("skipped", R),
              ("runtime_checked", "assert", C)),
          _summary(total_proved=3, total_skipped=2, total_runtime_checked=1)], 1, 1, True),
        ("the r09 HEAD wire with only the print tolerance",
         [_fn(("proved", "a"), ("proved", "b"), ("proved", "c"), ("skipped", R), ("skipped", R),
              ("runtime_checked", "assert", C)),
          _summary(total_proved=3, total_skipped=2, total_runtime_checked=1)], 1, 0, False),
        ("crate_summary hides the classed print row",
         [_fn(("proved", "a"), ("runtime_checked", "assert", C)),
          _summary(total_proved=1, total_runtime_checked=0)], 1, 0, False),
        ("requires assumption without tolerance (the r06 pack wire)",
         [_fn(("proved", "a"), ("proved", "b"), ("proved", "c"), ("skipped", R), ("skipped", R)),
          _summary(total_proved=3, total_skipped=2)], 0, 0, False),
        ("requires assumption with tolerance",
         [_fn(("proved", "a"), ("proved", "b"), ("proved", "c"), ("skipped", R), ("skipped", R)),
          _summary(total_proved=3, total_skipped=2)], 0, 1, True),
        ("requires tolerance does not cover another skipped kind",
         [_fn(("proved", "a"), ("skipped", "assumption:trusted-callee")), _summary(total_proved=1, total_skipped=1)], 0, 1, False),
        ("requires tolerance does not cover a print gap",
         [_fn(("proved", "a"), ("unknown", G)), _summary(total_proved=1, agg_unknown=1)], 0, 1, False),
        ("requires tolerance still needs a proof",
         [_fn(("skipped", R)), _summary(total_skipped=1)], 0, 1, False),
    ]
    # The process-verdict cases. `proved` is the measured json-ice wire shape:
    # complete, agreeing, all proved — everything the row checks accept. Only
    # the exit status / crash signature separates it from a real green.
    proved = [_fn(("proved", "postcond")), _summary(total_proved=1)]
    ice = [
        "",
        "thread 'rustc' (11562457) panicked at compiler/rustc_errors/src/lib.rs:478:17:",
        "`trimmed_def_paths` called, diagnostics were expected but none were emitted.",
        "error: the compiler unexpectedly panicked. This is a bug",
    ]
    payload_mentions_panic = [
        _fn(("proved", "the callee panicked at no reachable site: internal compiler error")),
        _summary(total_proved=1),
    ]
    # name, lines, exit_code (None = not supplied), want_clean
    exit_cases = [
        ("exit 0, all proved (control for the cases below)", proved, 0, True),
        ("rows then a teardown ICE, exit 101 (the json-ice wire)", proved + ice, 101, False),
        ("all proved, exit 101, no crash text on the stream", proved, 101, False),
        ("all proved, exit 1", proved, 1, False),
        ("all proved, exit status NOT supplied (the piped caller)", proved, None, False),
        ("crash text on the stream, caller claims exit 0", proved + ice, 0, False),
        ("crash text on the stream, exit status not supplied", proved + ice, None, False),
        ("crash words INSIDE a transport row are payload, not a crash",
         payload_mentions_panic, 0, True),
        ("tolerance does not cover a non-zero exit",
         [_fn(("proved", "a"), ("unknown", G)), _summary(total_proved=1, agg_unknown=1)], 101, False),
    ]
    # negative-control binding: (name, lines, require_failed, want_required_failed)
    failed_main = PREFIX + ":" + json.dumps({
        "type": "function_result", "function": "main::main",
        "results": [{"obligation_id": "vc:main__main:precondition:0", "kind": "precond", "outcome": "failed"},
                    {"obligation_id": "vc:main__main:assertion:panic-freedom:0", "kind": "assert",
                     "outcome": "runtime_checked", "gap_class": C}]})
    # (name, lines, require_failed, want_required_failed, want_clean)
    binding_cases = [
        ("required failed row present", [failed_main], ("main::main", "precondition"), True, False),
        ("required failed row: wrong function", [failed_main], ("main::double", "precondition"), False, False),
        ("required failed row: wrong obligation", [failed_main], ("main::main", "postcondition"), False, False),
        ("required failed row: the classed print row is not it", [failed_main], ("main::main", "assertion:panic-freedom"), False, False),
        ("required failed row: a colon-bearing obligation substring", [failed_main], ("main::main", "main__main:precondition"), True, False),
        ("required failed row: absent on a clean wire, which stays clean",
         [_fn(("proved", "a")), _summary(total_proved=1)], ("main::main", "precondition"), False, True),
    ]
    bad = 0
    for name, lines, req, want, want_clean in binding_cases:
        line, clean = grade(lines, True, True, exit_code=0, require_failed=req)
        got = line.endswith("required_failed=%s" % ("yes" if want else "no"))
        ok = got and clean == want_clean
        bad += 0 if ok else 1
        print("%s  %-56s want required_failed=%-3s  %s" % ("PASS" if ok else "FAIL", name, "yes" if want else "no", line))
    for name, lines, tol_gap, tol_req, want in cases:
        line, got = grade(lines, bool(tol_gap), bool(tol_req), exit_code=0)
        ok = got == want
        bad += 0 if ok else 1
        print("%s  %-56s want clean=%-3s  %s" % ("PASS" if ok else "FAIL", name, "yes" if want else "no", line))
    for name, lines, exit_code, want in exit_cases:
        line, got = grade(lines, tolerate_print_gap=True, exit_code=exit_code)
        ok = got == want
        bad += 0 if ok else 1
        print("%s  %-56s want clean=%-3s  %s" % ("PASS" if ok else "FAIL", name, "yes" if want else "no", line))
    # Argument parsing, which `grade()` alone does not reach. name, argv,
    # want (exit_code, flags) or want_error=True.
    arg_cases = [
        ("--exit-code N", ["--exit-code", "101"], (101, [])),
        ("--exit-code=N", ["--exit-code=0", "--tolerate-print-gap"], (0, ["--tolerate-print-gap"])),
        ("no --exit-code parses as absent", ["--tolerate-requires-assumption"],
         (None, ["--tolerate-requires-assumption"])),
        ("--exit-code with no value is refused", ["--exit-code"], True),
        ("--exit-code non-integer is refused", ["--exit-code", "x"], True),
        ("a second --exit-code is refused, not last-wins", ["--exit-code", "101", "--exit-code", "0"], True),
        ("an unknown flag is refused", ["--exit-code", "0", "--tolerate-everything"], True),
    ]
    for name, argv, want in arg_cases:
        exit_code, rest, error = parse_args(argv)
        got = True if error is not None else (exit_code, rest)
        ok = got == want
        bad += 0 if ok else 1
        print("%s  %-56s want %-24s got %s" % ("PASS" if ok else "FAIL", name, want, got))
    # The CALLER side of the same hole: a `cmd 2>&1 | wire_grade.py` pipe can
    # never supply the status. Every grading call in the battery script must
    # read a captured log and pass `--exit-code`.
    script = os.path.join(os.path.dirname(os.path.abspath(__file__)), os.pardir,
                          "e2e_two_language_programs.sh")
    try:
        with open(script) as f:
            calls = [l.strip() for l in f if '"$WIRE_GRADER"' in l and "--selftest" not in l
                     and not l.lstrip().startswith(("#", "WIRE_GRADER=", "if ", "echo "))]
        piped = [l for l in calls if '| python3 "$WIRE_GRADER"' in l or "--exit-code" not in l]
        ok, detail = (bool(calls) and not piped), ("%d call(s); offending: %s" % (len(calls), piped or "-"))
    except OSError as e:
        ok, detail = False, "cannot read %s: %s" % (script, e)
    bad += 0 if ok else 1
    print("%s  %-56s %s" % ("PASS" if ok else "FAIL", "battery script grades with --exit-code, never a pipe", detail))
    total = len(cases) + len(binding_cases) + len(exit_cases) + len(arg_cases) + 1
    print("selftest: %d cases, %d failed" % (total, bad))
    return 1 if bad else 0


KNOWN_FLAGS = ("--tolerate-print-gap", "--tolerate-requires-assumption")


def parse_args(argv):
    """Return (exit_code, flags, error). `error` is a usage message or None.

    `--exit-code N` / `--exit-code=N` is the graded compiler run's exit status.
    It may appear ONCE: a second one is refused rather than last-wins, since
    `--exit-code 101 --exit-code 0` would otherwise grade an ICE as exit 0.
    Whatever is left must be a known flag."""
    exit_code, rest, seen, i = None, [], False, 0
    argv = list(argv)
    while i < len(argv):
        a = argv[i]
        value = None
        if a == "--exit-code":
            i += 1
            value = argv[i] if i < len(argv) else ""
        elif a.startswith("--exit-code="):
            value = a[len("--exit-code="):]
        else:
            rest.append(a)
        if value is not None:
            if seen:
                return None, rest, "--exit-code given more than once; pass the one status of the graded run"
            seen = True
            try:
                exit_code = int(value)
            except ValueError:
                return None, rest, "--exit-code needs an integer exit status, got %r" % value
        i += 1
    unknown_flags = [a for a in rest if a not in KNOWN_FLAGS]
    if unknown_flags:
        return None, rest, "unknown argument(s): %s" % " ".join(unknown_flags)
    return exit_code, rest, None


def main(argv):
    if "--selftest" in argv:
        return selftest()
    want_fn = want_sub = None
    argv_rest = []
    it = iter(argv)
    for a in it:
        if a == "--require-failed-in":
            want_fn = next(it, None)
        elif a == "--require-failed-obligation":
            want_sub = next(it, None)
        else:
            argv_rest.append(a)
    if (want_fn is None) != (want_sub is None) or want_fn == "" or want_sub == "":
        sys.stderr.write("wire_grade.py: --require-failed-in FUNCTION and "
                         "--require-failed-obligation SUBSTRING must be given together\n")
        return 2
    require_failed = (want_fn, want_sub) if want_fn is not None else None
    exit_code, rest, error = parse_args(argv_rest)
    if error is not None:
        sys.stderr.write("wire_grade.py: %s\n" % error)
        return 2
    line, _ = grade(sys.stdin, "--tolerate-print-gap" in rest,
                    "--tolerate-requires-assumption" in rest, exit_code=exit_code,
                    require_failed=require_failed)
    print(line)
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
