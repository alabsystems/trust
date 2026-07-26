#!/usr/bin/env python3
"""Program 3 Phase A.2 — the minimal-pair provability matrix.

Two functions differing in exactly ONE syntactic element, compiled together,
verdicts compared. Every Phase B item should cite a row of it.

CAVEAT EARNED THE HARD WAY: a minimal pair is evidence only if the pair is
SEMANTICALLY minimal, not merely syntactically minimal. Integer casts are exactly
where those come apart -- `n as u32` with `n: usize` can truncate 2^32 to 0, so
two programs that differ by "just a cast" may not mean the same thing. Verify the
programs are equivalent BEFORE attributing a verdict difference to the compiler.
A claimed defect was retracted for exactly this reason; see the report below.

  ./x.py build --stage 2
  python3 tests/trust-provability/minimal_pairs.py            # matrix + exit code
  python3 tests/trust-provability/minimal_pairs.py --update   # rewrite EXPECTED

Charter: docs/plans/2026-07-25-program-3-prove-rate.md
Findings: reports/audit-2026-07-25-cast-fact-propagation.md

HAZARD (§2 of the charter, learned the hard way): never infer a verdict from an
exit code. A renamed flag exits non-zero with `unknown unstable option`, and a
harness that reads that as "the verifier rejected it" certifies a live defect as
fixed. This script classifies on the per-obligation JSON transport, and treats a
missing/!=0-obligation row as a HARNESS error, never as a verdict.
"""
import argparse, json, os, re, subprocess, sys, tempfile

REPO = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", ".."))
TRUSTC = os.environ.get("TRUST_PROVABILITY_TRUSTC",
                        os.path.join(REPO, "build", "host", "stage2", "bin", "trustc"))

# (name, source, note). Each ADJACENT pair differs in exactly one element.
CASES = [
    # --- divisor guard, with and without an intervening cast -----------------
    ("div_guard_plain",
     "pub fn f(n: usize) -> usize { if n == 0 { 0 } else { 100 / n } }",
     "guard establishes n != 0; divisor used directly"),
    ("div_guard_cast_narrowing",
     "pub fn f(n: usize) -> u32 { if n == 0 { 0 } else { 100u32 / n as u32 } }",
     "NEGATIVE: usize->u32 CAN truncate (n=2^32 => 0), so refuting is CORRECT"),
    ("div_guard_cast_widening_u8",
     "pub fn f(n: u8) -> u32 { if n == 0 { 0 } else { 100u32 / n as u32 } }",
     "widening cannot truncate, so the guard carries: must PROVE"),
    ("div_guard_cast_widening_u16",
     "pub fn f(n: u16) -> u32 { if n == 0 { 0 } else { 100u32 / n as u32 } }",
     "same, wider source: must PROVE"),
    # NOTE: the real-world `v.len() as u32` divisor shape currently ICEs the
    # compiler (slice parameter), so it cannot be scored here. See the pre-flight
    # ICE guard below and reports/2026-07-25-flip-recovery-ICE.md.
    # Restore this row once that is fixed.

    # --- overflow: bound from a comparison guard vs from a cast --------------
    ("mul_guard",
     "pub fn f(x: u16) -> u16 { if x <= 255 { x * 2 } else { 0 } }",
     "bound from a comparison guard"),
    ("mul_cast",
     "pub fn f(v: u8) -> u16 { (v as u16) * 2 }",
     "SAME arithmetic; bound from a widening cast"),
    ("add_cast",
     "pub fn f(v: u8) -> u16 { v as u16 + 1 }",
     "control: cast-derived bound DOES reach the Add VC"),
    ("mul_cast_u32",
     "pub fn f(v: u8) -> u32 { (v as u32) * 2 }",
     "same as mul_cast at a wider target"),
    ("shl_cast",
     "pub fn f(v: u8) -> u16 { (v as u16) << 1 }",
     "shift form of the same widening"),
    ("mul_var_times_var_widening",
     "pub fn f(a: u8, b: u8) -> u16 { (a as u16) * (b as u16) }",
     "OPEN: 255*255=65025 fits u16, so SAFE and provable — but var*var stays on "
     "the BV path, which certify_vc cannot reconstruct. The remaining authority gap."),

    # --- the wall: a completeness gap presenting as a REFUTATION -------------
    ("loop_invariant_countdown",
     "pub fn f(mut n: u32) -> u32 { let mut s = 0u32; while n > 0 { n -= 1; s += 1; } s }",
     "WALL INSTANCE: s+n==n0 so s<=n0<=u32::MAX and `s += 1` cannot overflow, "
     "but it is REFUTED WITH A COUNTEREXAMPLE for want of the loop invariant"),
    ("loop_invariant_bounded_control",
     "pub fn f(mut n: u32) -> u32 { let mut s = 0u32; while n > 0 && s < 100 { n -= 1; s += 1; } s }",
     "control: same loop with an explicit bound — proves without the invariant"),

    # --- negatives: these MUST NOT prove ------------------------------------
    ("neg_nonlinear_mul",
     "pub fn f(a: u32, b: u32) -> u32 { a * b }",
     "NEGATIVE: genuinely nonlinear, must stay unproved"),
    ("neg_unguarded_div",
     "pub fn f(n: u32) -> u32 { 100 / n }",
     "NEGATIVE: real division by zero, must refute"),
    ("neg_unguarded_add",
     "pub fn f(a: u32, b: u32) -> u32 { a + b }",
     "NEGATIVE: real overflow, must refute"),
]

# Frozen at stage2 4c9a696c4 / aarch64-apple-darwin (build == HEAD).
# `outcome:kind` per obligation, sorted. See --update.
EXPECTED_PATH = os.path.join(os.path.dirname(__file__), "EXPECTED.json")


def compile_one(name, src, workdir):
    d = os.path.join(workdir, name)
    os.makedirs(d, exist_ok=True)
    p = os.path.join(d, f"{name}.rs")
    with open(p, "w") as fh:
        fh.write("#![crate_type=\"lib\"]\n" + src + "\n")
    env = dict(os.environ)
    env["TRUST_SEED_STAIRCASE"] = "1"
    cmd = [TRUSTC, "-Zthreads=1", "-Ztrust-verify=on",
           # advisory: we want every row, not an abort at the first unproved one
           "-Ztrust-policy=advisory", "-Ztrust-verify-output=json",
           "-Coverflow-checks=on", "--edition=2021",
           "--emit=metadata", "--out-dir", d, p]
    r = subprocess.run(cmd, capture_output=True, text=True, env=env)
    return r


def _json_rows(stderr):
    """Yield every decoded TRUST_JSON object on stderr."""
    for line in stderr.splitlines():
        i = line.find("TRUST_JSON:")
        if i < 0:
            continue
        try:
            yield json.loads(line[i + len("TRUST_JSON:"):].strip())
        except json.JSONDecodeError:
            continue


def parse_rows(stderr):
    """Extract per-obligation (outcome, kind, reason) from the JSON transport.

    The obligation array is `results` (verified against the live schema, and
    against `TransportObligationResult` in crates/trust-types/src/result.rs).
    """
    rows = []
    for obj in _json_rows(stderr):
        if obj.get("type") != "function_result":
            continue
        for o in obj.get("results") or []:
            rows.append({
                "outcome": str(o.get("outcome", "?")),
                "kind": str(o.get("kind", "?")),
                "reason": (o.get("reason") or ""),
                "counterexample": bool(o.get("counterexample") or o.get("counterexample_model")),
            })
    return rows


def parse_tally(stderr):
    """Crate-level tally. Under `-Ztrust-policy=advisory -Ztrust-verify-output=json`
    there is NO human `Trust verification: ...` summary line — the authoritative
    counts are the `crate_summary` transport row."""
    for obj in _json_rows(stderr):
        if obj.get("type") == "crate_summary":
            return {
                "proved": obj.get("total_proved", 0),
                "failed": obj.get("total_failed", 0),
                "unknown": obj.get("total_unknown", 0),
                "runtime_checked": obj.get("total_runtime_checked", 0),
                "total": obj.get("total_obligations", 0),
            }
    return None


HUMAN_RE = re.compile(
    r"\[(?P<kind>[a-z0-9_:.-]+)\]\s+(?P<outcome>FAILED|runtime-checked|UNKNOWN|skipped)",
    re.IGNORECASE)


def parse_rows_human(stderr):
    """Fallback for builds whose JSON transport omits the obligation array."""
    rows = []
    for m in HUMAN_RE.finditer(stderr):
        out = m.group("outcome").lower()
        out = {"failed": "Failed", "runtime-checked": "RuntimeChecked",
               "unknown": "Unknown", "skipped": "Skipped"}.get(out, out)
        seg = stderr[m.end():m.end() + 200]
        rows.append({"outcome": out, "kind": m.group("kind"),
                     "reason": seg.split("\n")[0].strip(),
                     "counterexample": "counterexample" in seg})
    return rows


SUMMARY_RE = re.compile(
    r"Trust verification: (\d+) proved, (\d+) failed, (\d+) unknown, "
    r"(\d+) timed out, (\d+) runtime-checked out of (\d+)")


def classify(r):
    """Return (signature, detail) or raise HarnessError."""
    if "unknown unstable option" in r.stderr or "Unrecognized option" in r.stderr:
        raise RuntimeError("HARNESS: a flag this script passes no longer exists — "
                           + (re.search(r"unknown unstable option: `[^`]*`", r.stderr)
                              or re.search(r"Unrecognized option: '[^']*'", r.stderr)
                              or ["?"])[0])
    tally = parse_tally(r.stderr)
    if tally is None:
        m = SUMMARY_RE.search(r.stderr)
        if not m:
            raise RuntimeError("HARNESS: no crate_summary transport row and no human "
                               "summary; the verifier did not run (or its output "
                               "changed shape)")
        proved, failed, unknown, _timed, rtchk, total = (int(x) for x in m.groups())
        tally = {"proved": proved, "failed": failed, "unknown": unknown,
                 "runtime_checked": rtchk, "total": total}
    if tally["total"] == 0:
        raise RuntimeError("HARNESS: zero obligations — the fixture emitted nothing to prove")

    rows = parse_rows(r.stderr) or parse_rows_human(r.stderr)
    if not rows:
        raise RuntimeError("HARNESS: a tally exists but no per-obligation rows parsed "
                           "— the transport schema moved")
    sig = dict(tally)
    sig["rows"] = sorted({f"{x['outcome']}:{x['kind']}" for x in rows})
    sig["counterexample"] = any(x["counterexample"] for x in rows)
    return sig


def verdict_label(sig):
    if sig["failed"]:
        return "REFUTED(+ce)" if sig["counterexample"] else "REFUTED"
    if sig["runtime_checked"]:
        return "runtime-checked"
    if sig["unknown"]:
        return "UNKNOWN"
    if sig["proved"] == sig["total"]:
        return "proved"
    return "mixed"


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--update", action="store_true",
                    help="rewrite EXPECTED.json from this run")
    ap.add_argument("--filter", default="")
    args = ap.parse_args()

    if not os.path.exists(TRUSTC):
        print(f"SKIP: no stage2 trustc at {TRUSTC} (run ./x.py build --stage 2)")
        return 0

    stamp = subprocess.run([TRUSTC, "-V"], capture_output=True, text=True).stdout.strip()
    print(f"trustc: {stamp}")
    print(f"host:   {subprocess.run([TRUSTC, '-vV'], capture_output=True, text=True).stdout.strip().splitlines()[-1] if True else ''}")
    print()

    work = tempfile.mkdtemp(prefix="provability_")

    # Pre-flight: an ICE is the limit case of "cannot prove". Scoring one as a
    # verdict would be the same lie as reading an exit code as a rejection, so
    # it is reported here, before the matrix, as a harness-level failure.
    ices = []
    for nm, src in [
        ("struct_field", "pub struct P { pub x: i32 } pub fn f(v: i32) -> i32 { P { x: v }.x }"),
        ("enum_match", "pub enum E { A, B(u32) } "
                       "pub fn f(e: &E) -> u32 { match e { E::A => 0, E::B(n) => *n } }"),
        ("option_return", "pub fn f(x: u32) -> Option<u32> { if x == 0 { None } else { Some(x) } }"),
        ("method_self", "pub struct P { pub x: i32 } impl P { pub fn g(&self) -> i32 { self.x } }"),
        ("slice_param_unused", "pub fn f(_v: &[u32]) -> u32 { 7 }"),
        ("array_param", "pub fn f(v: [u32; 4]) -> usize { v.len() }"),
        # controls — these must stay OK, or the ICE has widened again
        ("scalar_param_control", "pub fn f(x: u32) -> u32 { x }"),
        ("while_loop_control", "pub fn f(mut n: u32) -> u32 { let mut s = 0u32; "
                               "while n > 0 { n -= 1; s += 1; } s }"),
    ]:
        r = compile_one("ice_" + nm, src, work)
        if "unexpectedly panicked" in r.stderr:
            loc = re.search(r"panicked at ([^\s:]+:\d+)", r.stderr)
            ices.append(f"{nm}: ICE at {loc.group(1) if loc else '?'}")
    if ices:
        print("PRE-FLIGHT: the compiler CRASHES on these shapes —")
        for i in ices:
            print(f"  {i}")
        print("  see reports/2026-07-25-flip-recovery-ICE.md "
              "(owner: Program 1)\n")

    observed, harness_errors = {}, []
    for name, src, note in CASES:
        if args.filter and args.filter not in name:
            continue
        r = compile_one(name, src, work)
        try:
            sig = classify(r)
        except RuntimeError as e:
            harness_errors.append((name, str(e)))
            print(f"  {name:22} !! {e}")
            continue
        observed[name] = sig
        print(f"  {name:22} {verdict_label(sig):16} "
              f"proved={sig['proved']}/{sig['total']}  {note}")

    if harness_errors:
        print("\nHARNESS ERRORS — these are NOT verdicts. Fix the harness, do not "
              "read them as rejections.")
        return 2

    if args.update:
        with open(EXPECTED_PATH, "w") as fh:
            json.dump({"_stamp": stamp, "cases": observed}, fh, indent=2, sort_keys=True)
            fh.write("\n")
        print(f"\nwrote {EXPECTED_PATH}")
        return 0

    if not os.path.exists(EXPECTED_PATH):
        print("\nno EXPECTED.json — run with --update to freeze this run as the baseline")
        return 0

    with open(EXPECTED_PATH) as fh:
        expected = json.load(fh).get("cases", {})
    drift = []
    for name, sig in observed.items():
        exp = expected.get(name)
        if exp is None:
            drift.append(f"  {name}: new case, not in EXPECTED.json")
            continue
        if verdict_label(exp) != verdict_label(sig):
            drift.append(f"  {name}: {verdict_label(exp)} -> {verdict_label(sig)}")
    if drift:
        print("\nDRIFT vs EXPECTED.json:")
        print("\n".join(drift))
        print("\nA row moving toward `proved` is progress — rerun with --update and "
              "say so in the commit. A row moving away is a regression.")
        return 1
    print("\nmatrix matches EXPECTED.json")
    return 0


if __name__ == "__main__":
    sys.exit(main())
