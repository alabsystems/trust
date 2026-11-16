#!/usr/bin/env python3
"""Find ui/trust fixtures whose VERDICT depends on the per-VC solver budget.

A fixture whose exit status changes when only `-Ztrust-verify-timeout-ms` changes
is asserting a latency claim it does not mean to assert. It will pass alone and
red under a parallel suite run, and the failure will read like a verification
defect. That is the defect this finds -- and it is the defect whether the fixture
is expected to pass or to fail, so no expected-outcome parsing is needed.

Measured 2026-09-21 on 382 verification-bearing cases: exactly 2 were sensitive,
`contract_projection_named_params_verify` and
`native_loop_collection_semantics#slice_progress`, both since pinned at
`-Ztrust-verify-timeout-ms=120000` in their own headers. Serially those two need
between 3000ms and 5000ms, so the 5s daily-driver default carried under 1.7x
margin; at concurrency 16 on an 18-core box they were 0/16 at the default and
16/16 at the pin.

KNOWN BLIND SPOT, found 2026-09-21 the hard way. This compares EXIT CODES only,
so it cannot see a fixture whose verdict is stable but whose blessed STDERR is
load-dependent. `postcondition_composition_at_call_site` is the worked example:
it exits 0 either way, but under a heavier suite ay's proof checker logs
`ERROR ... proof validation cancelled by the caller` lines that are not in its
blessed stderr, and the test reds on the diff. Note that extending THIS sweep
would not have caught it -- measured, that noise is not budget-sensitive at all
(60 lines at 5000ms vs 58 at 120000ms, 16/16 runs at either), so it is a
different deadline than the per-VC budget. Catching that class needs a
load-sensitivity sweep over stderr, which is a separate instrument. The fixture
carries a `normalize-stderr` for the line instead.

SECOND BLIND SPOT, closed 2026-09-27: this sweep did not see what compiletest
sees. Its default pattern `tests/ui/trust/*.rs` was TOP-LEVEL ONLY (737 files at
8c39674bbb against 851 non-auxiliary fixtures, so every subdirectory fixture --
all of `memory_safe/` -- was never compiled); it ignored `//@ edition` (122
fixtures), `//@ rustc-env`, and the in-tree `//@ [rev] compile-flags` spelling;
and it keyed results by BASENAME. 737 is exactly the count a differential sweep
reported as "all 737 tests/ui/trust fixtures ... exit codes identical" while
`memory_safe/reject_diverging_call_gap.rs` regressed. Directives are now read the
way compiletest reads them (`parse_directive` / `resolve`, every `compile-flags`
line accumulating), discovery is recursive, every skip is counted and printed,
and a run in which NO pass-mode case exits 0 in the high arm (a set with no
pass-mode case included) exits 3 as INSTRUMENT BLIND instead of reporting
"zero sensitive". Pinned by
scripts/tests/ui_trust_budget_sensitivity_test.py.

POSITIVE CONTROL -- read this before believing a zero. A zero here is a fact
about the instrument until it has shown it can produce a non-zero. Both arms run
at the SAME parallelism so contention is held constant and the budget is the only
varying term; if a run reports nothing, lower --low until a known-sensitive
fixture appears, and if none ever does, the harness is not reaching the verifier.

  python3 scripts/ui_trust_budget_sensitivity.py                # 5000 vs 120000
  python3 scripts/ui_trust_budget_sensitivity.py --low 1000     # widen the net

The arms must BRACKET the current `-Ztrust-verify-timeout-ms` default, which is
the number a normal suite run actually uses. That default moved 5000 -> 20000 on
2026-09-21 (40220cd450, "the per-obligation budget was a race against machine
load, not a budget"), so the arms moved with it. If the default moves again,
move these too, or the sweep silently stops measuring the margin that matters.

Runs the PREBUILT stage1 compiler and never builds, so it is safe to run beside
a measurement -- but NOT beside `x.py build`, which deletes stage1/bin/rustc.
"""
import argparse, concurrent.futures as cf, glob, io, json, os, re, subprocess, sys, tempfile

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))


DEFAULT_TESTS = os.path.join(ROOT, "tests/ui/trust/**/*.rs")

# compiletest's pass/fail modes. A UI test with none of them is `check-fail`
# (`TestProps::from_file`), so only these three expect exit 0.
PASS_MODES = ("check-pass", "build-pass", "run-pass")
FAIL_MODES = ("check-fail", "build-fail", "run-fail", "run-crash")


def parse_directive(line):
    """One `//@` line, split EXACTLY as compiletest's `line_directive` does
    (src/tools/compiletest/src/directives/line.rs): leading whitespace is
    allowed, the revision bracket may be separated from `//@` by spaces
    (`//@ [rev] compile-flags: ...` is in-tree spelling), and the directive
    name ends at the first `:` or space. Returns (revision, name, value) --
    `value` is the text after `name:` or None -- or None for a non-directive.
    """
    rest = line.lstrip()
    if not rest.startswith("//@"):
        return None
    rest = rest[3:].lstrip()
    revision = None
    if rest.startswith("["):
        close = rest.find("]")
        if close < 0:
            return None  # compiletest panics on this; there is nothing to run
        revision = rest[1:close]
        rest = rest[close + 1:].lstrip()
    name = re.split(r"[: ]", rest, maxsplit=1)[0]
    value = rest[len(name) + 1:] if rest[len(name):len(name) + 1] == ":" else None
    return revision, name, value


def split_flags(value):
    """compiletest's `split_flags`: whitespace-separated, except that a
    single-quoted run is one flag (quotes removed)."""
    out = []
    for i, part in enumerate(value.strip().split("'")):
        out.extend([part] if i % 2 == 1 else part.split())
    return out


def edition_to_test(value):
    """`//@ edition: X` / `X..` / `X..Y`, resolved as compiletest does with no
    `--edition` override: the requested edition is 2015, so an exact edition
    is itself and a range resolves to its lower bound."""
    lower = value.split("..", 1)[0].strip()
    return lower or "2015"


def directives(path):
    """Everything this sweep reads from a fixture, per revision.

    Returns (revisions, lines, src): `lines` is every directive as
    (revision, name, value) in FILE ORDER, which is the order compiletest
    applies them in (`iter_directives`); `resolve` turns it into one case.
    """
    with io.open(path, encoding="utf-8", errors="replace") as fh:
        src = fh.read()
    lines = [d for d in map(parse_directive, src.splitlines()) if d is not None]
    revs = [r for rev, name, value in lines
            if name == "revisions" and value is not None for r in value.split()]
    return revs, lines, src


def resolve(lines, rev):
    """The (args, env, mode) compiletest would use for revision `rev` (None for
    an unrevisioned fixture): only lines unscoped or scoped to `rev` apply.

    EVERY `compile-flags` line accumulates, as compiletest's handler does
    (`props.compile_flags.extend`): a fixture that splits its flags over two
    lines is a normal fixture, and 62 of them under tests/ui/trust do
    (2026-09-27). Reading one of those lines is how a sweep compiles a fixture
    without the policy it exists to exercise. The LAST applicable `edition` and
    pass/fail-mode line wins, and the edition goes FIRST in the arguments, as
    compiletest inserts it (flags from `compile-flags` must come last). 122
    fixtures under tests/ui/trust declare an edition; compiled at the 2015
    default, an edition-2021 fixture can fail identically in both arms and
    measure nothing. A UI fixture with no mode line is `check-fail`.
    """
    flags, env, edition, mode = [], [], None, "check-fail"
    for line_rev, name, value in lines:
        if line_rev is not None and line_rev != rev:
            continue
        if name == "compile-flags" and value is not None:
            flags.extend(split_flags(value))
        elif name == "rustc-env" and value is not None and "=" in value:
            env.append(tuple(value.strip().split("=", 1)))
        elif name == "edition" and value is not None:
            edition = edition_to_test(value)
        elif name in PASS_MODES or name in FAIL_MODES:
            mode = name
    return ([f"--edition={edition}"] if edition else []) + flags, env, mode


def _in_ignored_dir(path):
    """compiletest skips any directory holding a `compiletest-ignore-dir` file."""
    d = os.path.dirname(os.path.abspath(path))
    while True:
        if os.path.exists(os.path.join(d, "compiletest-ignore-dir")):
            return True
        parent = os.path.dirname(d)
        if parent == d:
            return False
        d = parent


def discover(pattern):
    """The fixture files a pattern names, RECURSIVELY, never an `auxiliary/`
    crate (compiletest builds those as dependencies, not as tests) and never a
    directory compiletest is told to ignore.

    The default pattern used to be `tests/ui/trust/*.rs`, which is top-level
    only: 737 files at 8c39674bbb against 851 non-auxiliary fixtures, so the
    114 in subdirectories -- every `memory_safe/` fixture among them -- were
    never compiled. 737 is also exactly the count a differential sweep reported
    as "all 737 tests/ui/trust fixtures" while one of those subdirectory
    fixtures regressed (docs/KNOWN_HAZARDS.md, 2026-09-27).
    """
    paths = glob.glob(pattern, recursive=True)
    return sorted(p for p in paths
                  if os.path.isfile(p) and "auxiliary" not in p.split(os.sep)
                  and not _in_ignored_dir(p))


def cases(pattern, skip_pinned=True, skipped=None):
    """(path, revision, flags, env, expected_mode) for every verification-bearing
    case. `skipped`, when given, is a dict that counts each skip by reason, so
    a sweep can say what it did NOT reach instead of reading as complete."""
    def skip(reason):
        if skipped is not None:
            skipped[reason] = skipped.get(reason, 0) + 1

    for path in discover(pattern):
        revs, lines, _src = directives(path)
        # aux-build needs compiletest to build a sibling crate first; out of scope.
        if any(name in ("aux-build", "aux-crate", "proc-macro") for _, name, _ in lines):
            skip("aux-build")
            continue
        # compiletest never runs an `ignore-test` fixture. Conditional ignores
        # (`ignore-<target>`, `only-<target>`, `needs-*`) are NOT evaluated here;
        # a case they would exclude shows up in the reachability report instead.
        if any(rev is None and name == "ignore-test" for rev, name, _ in lines):
            skip("ignore-test")
            continue
        for rev in (revs or [None]):
            args, case_env, mode = resolve(lines, rev)
            case_flags = [a for a in args if not a.startswith("--edition=")]
            if not any("trust-verify=on" in flag for flag in case_flags):
                skip("no -Ztrust-verify=on")
                continue
            # A fixture that PINS its own budget has made the latency claim
            # explicit and deliberately; it is not an unnoticed margin flake.
            # Skipping them is what makes a zero here mean something.
            if skip_pinned and any("trust-verify-timeout-ms" in f for f in case_flags):
                skip("pins its own budget")
                continue
            # compiletest expands `{{build-base}}` and friends in compile-flags;
            # raw trustc does not, so a fixture carrying one would write a literal
            # `{{build-base}}` directory into the CWD. Measured: an earlier run of
            # this sweep did exactly that to the repo root. These need the harness.
            if any("{{" in flag for flag in case_flags):
                skip("needs compiletest variable expansion")
                continue
            yield (path, rev, args, case_env, mode)


def case_tag(case, root=ROOT):
    """A case's identity: the REPO-RELATIVE path, never the basename -- with a
    recursive walk two directories can hold the same file name, and results
    keyed by basename would silently overwrite one another."""
    path, rev = case[0], case[1]
    rel = os.path.relpath(path, root)
    return rel + (("#" + rev) if rev else "")


def run(tc, outdir, case, ms):
    path, rev, args, case_env, _mode = case
    args = [a for a in args if not a.startswith("-Ztrust-verify-timeout-ms")]
    tag = case_tag(case)
    cmd = [tc, *args, f"-Ztrust-verify-timeout-ms={ms}",
           "--crate-type", "lib", "--emit=metadata", "--out-dir", outdir, path]
    if rev:
        cmd[1:1] = ["--cfg", rev]
    child_env = dict(os.environ)
    child_env.update(case_env)
    try:
        p = subprocess.run(cmd, capture_output=True, text=True, timeout=300, env=child_env)
        return tag, p.returncode, p.stderr[-400:]
    except subprocess.TimeoutExpired:
        return tag, 124, "TIMEOUT"


def reachability(cs, results):
    """The second half of the 2026-09-27 hazard: identical exit codes over a
    set that contains pass-mode fixtures mean something only if some of those
    fixtures exited 0. Returns (pass_mode_cases, of_which_exited_zero,
    pass_mode_tags_that_did_not)."""
    expect_zero = [case_tag(c) for c in cs if c[4] in PASS_MODES]
    zero = [t for t in expect_zero if results.get(t, (None,))[0] == 0]
    return len(expect_zero), len(zero), sorted(set(expect_zero) - set(zero))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--low", type=int, default=5000)
    ap.add_argument("--high", type=int, default=120000)
    ap.add_argument("--jobs", type=int, default=4)
    ap.add_argument("--tests", default=DEFAULT_TESTS,
                    help="a glob, expanded RECURSIVELY (`**`); auxiliary/ crates are skipped")
    ap.add_argument("--trustc", default=os.path.join(
        ROOT, "build/aarch64-apple-darwin/stage1/bin/trustc"))
    ap.add_argument("--out", default="")
    ap.add_argument("--skip-pinned", default="yes", choices=["yes", "no"],
                    help="skip fixtures that pin their own -Ztrust-verify-timeout-ms "
                         "(default); pass 'no' to run the positive control on one")
    a = ap.parse_args()

    if not os.path.exists(a.trustc):
        sys.exit(f"no prebuilt compiler at {a.trustc} -- pass --trustc")

    # Deliberately NOT under build/: that tree is exclusive and an x.py run
    # would wipe it mid-sweep.
    outdir = tempfile.mkdtemp(prefix="budget-sensitivity-")
    skipped = {}
    cs = list(cases(a.tests, a.skip_pinned == "yes", skipped))
    print(f"cases: {len(cs)}  low={a.low}ms high={a.high}ms jobs={a.jobs}", flush=True)
    # What the sweep does NOT reach, stated up front: a count with no
    # denominator is how "all 737 fixtures" read as the whole suite.
    print(f"files: {len(discover(a.tests))}  skipped cases: "
          + (", ".join(f"{k}={v}" for k, v in sorted(skipped.items())) or "none"),
          flush=True)

    def arm(ms):
        with cf.ThreadPoolExecutor(max_workers=a.jobs) as ex:
            return {t: (rc, e) for t, rc, e in
                    ex.map(lambda c: run(a.trustc, outdir, c, ms), cs)}

    hi = arm(a.high); print("high arm done", flush=True)
    lo = arm(a.low);  print("low arm done", flush=True)

    diffs = []
    for tag in sorted(hi):
        rh, _ = hi[tag]
        rl, el = lo.get(tag, (None, ""))
        if rl is not None and rh != rl:
            diffs.append({"test": tag, "rc_high": rh, "rc_low": rl,
                          "low_err": (el.strip().splitlines() or [""])[-1]})

    expected, reached, unreached = reachability(cs, hi)
    print(f"\nreachability: {reached} of {expected} pass-mode case(s) exited 0 in the "
          f"high arm")
    if unreached:
        print(f"  {len(unreached)} pass-mode case(s) did NOT exit 0 at the high budget, so "
              "their budget verdict is unmeasured (the fixture fails today, or this harness "
              "does not reproduce compiletest for it):")
        for tag in unreached[:20]:
            print(f"    {tag}")
        if len(unreached) > 20:
            print(f"    ... and {len(unreached) - 20} more")

    print(f"\n=== BUDGET-SENSITIVE: {len(diffs)} of {len(cs)} ===")
    for d in diffs:
        print(json.dumps(d))
    # Blind unless some pass-mode case exited 0: that is the only witness that
    # this harness reached the verifier. A set with NO pass-mode case has no
    # witness either -- a narrowed `--tests` of fail-mode fixtures run on a
    # trustc that exits 1 every time agrees with itself perfectly.
    blind = not reached
    if blind:
        if expected:
            print("INSTRUMENT BLIND: not one pass-mode case compiled cleanly in the high arm, so")
        else:
            print("INSTRUMENT BLIND: the swept set holds no pass-mode case, so nothing can show")
            print("that this harness reached the verifier. Add a check-pass fixture to --tests;")
        print("identical exit codes between the arms say nothing about any verdict. A sweep")
        print("in which nothing compiles agrees with itself perfectly (docs/KNOWN_HAZARDS.md,")
        print("2026-09-27). Check --trustc and the flags this harness passes.")
    elif not diffs:
        print("NOTE: zero is a claim about the instrument until it has shown it can")
        print("produce a non-zero. The standing positive control is to point --tests")
        print("at tests/ui/trust/contract_projection_named_params_verify.rs and pass")
        print("--skip-pinned=no: that fixture's row needs 3000-5000ms, so a --low")
        print("below 3000 MUST report it. If it does not, the harness is not")
        print("reaching the verifier and this sweep proves nothing.")
    if a.out:
        with io.open(a.out, "w") as fh:
            fh.write(json.dumps(
                {"cases": len(cs), "low": a.low, "high": a.high, "diffs": diffs,
                 "skipped": skipped, "pass_mode_cases": expected,
                 "pass_mode_exited_zero": reached, "instrument_blind": blind}, indent=1))
    return 3 if blind else 0


if __name__ == "__main__":
    sys.exit(main())
