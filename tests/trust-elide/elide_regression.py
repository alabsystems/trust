#!/usr/bin/env python3
"""Runtime ledger, increment 1: proven-overflow-check elision regression.

The verifier elides the overflow panic-branch of an arithmetic Add/Sub/Mul whose
no-overflow VC was KERNEL-certified (clean CIC re-check). There is no opt-in
switch: elision runs wherever verification runs. This pins:
  * PROVEN elides: a kernel-certified overflow op has its Assert(Overflow) replaced
    by a plain Goto under batteries-on verification + `-C overflow-checks=on`;
  * UNSAFE rejected: a genuinely-overflowing op fails verification (never codegen'd,
    never elided);
  * VANILLA baseline: under `-Ztrust-verify=off` no proof exists, so the Assert
    survives — which is also what pins that the fixture really emits one;
  * VALUE-PRESERVING: the arithmetic (the *WithOverflow rvalue) is ALWAYS retained.

Run after `x.py build --stage 2`:
    TRUST_SEED_STAIRCASE=1 python3 tests/trust-elide/elide_regression.py
"""
import subprocess, os, sys, re, tempfile

REPO = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", ".."))
TRUSTC = os.environ.get("TRUST_ELIDE_TRUSTC",
                        os.path.join(REPO, "build", "host", "stage2", "bin", "trustc"))
WORK = tempfile.mkdtemp(prefix="elide_reg_")

# Kernel-certified overflow families (each must ELIDE exactly its overflow check).
PROVEN = {
    "guarded_sub": "pub fn f(x: u32) -> u32 { if x > 10 { x - 10 } else { 0 } }",
    "diseq_sub":   "pub fn f(x: u32) -> u32 { if x != 0 { x - 1 } else { 0 } }",
    "widen_add":   "pub fn f(a: u8) -> u16 { a as u16 + 1 }",
    "guarded_add": "pub fn f(x: u32) -> u32 { if x < 1000 { x + 1 } else { 0 } }",
}
# Genuinely unsafe: verification must FAIL (never elided).
UNSAFE = {"unproven_add": "pub fn f(a: u32, b: u32) -> u32 { a + b }"}


_N = [0]

def compile(src, verify, emit="metadata"):
    # A fresh, isolated dir per invocation: the source lives outside the emit dir
    # and no stale .rmeta/.mir from another fixture can leak in.
    _N[0] += 1
    d = os.path.join(WORK, f"c{_N[0]}"); os.makedirs(d, exist_ok=True)
    p = os.path.join(WORK, f"s{_N[0]}.rs"); open(p, "w").write(src)
    env = dict(os.environ); env["TRUST_SEED_STAIRCASE"] = "1"; env["TRUST_ELIDE_DEBUG"] = "1"
    cmd = [TRUSTC, "-Zthreads=1", f"-Ztrust-verify={'on' if verify else 'off'}",
           "-Coverflow-checks=on",
           "--crate-type=lib", "--edition=2021", f"--emit={emit}", "--out-dir", d, p]
    r = subprocess.run(cmd, capture_output=True, text=True, env=env)
    r._dir = d
    return r


def elided_count(stderr):
    m = re.search(r"elided (\d+) kernel-certified overflow", stderr)
    return int(m.group(1)) if m else 0


def overflow_assert_count(mir_text):
    """Count MIR Assert terminators whose diagnostic is an overflow failure."""
    return sum(
        1
        for line in mir_text.splitlines()
        if "assert(" in line and "overflow" in line.lower()
    )


def mir(src, verify):
    import glob
    r = compile(src, verify, emit="mir")
    text = "".join(open(f).read() for f in glob.glob(os.path.join(r._dir, "*.mir")))
    return r, text


fails = []
for name, src in PROVEN.items():
    on = compile(src, verify=True)
    off = compile(src, verify=False)
    probs = []
    if on.returncode != 0:
        probs.append(f"verified compile failed ({on.returncode})")
    if off.returncode != 0:
        probs.append(f"vanilla compile failed ({off.returncode})")
    if elided_count(on.stderr) != 1:
        probs.append(
            "expected exactly one kernel-certified overflow elision "
            f"(reported {elided_count(on.stderr)})"
        )
    if elided_count(off.stderr) != 0:
        probs.append("elided a check with verification OFF (no proof exists there)")
    # MIR: the vanilla lane keeps the Assert(Overflow); the verified lane replaces it
    # with a goto; BOTH retain the *WithOverflow arithmetic (value-preserving).
    mir_off_result, m_off = mir(src, False)
    mir_on_result, m_on = mir(src, True)
    if mir_off_result.returncode != 0:
        probs.append(f"vanilla MIR compile failed ({mir_off_result.returncode})")
    if mir_on_result.returncode != 0:
        probs.append(f"verified MIR compile failed ({mir_on_result.returncode})")
    off_asserts = overflow_assert_count(m_off)
    on_asserts = overflow_assert_count(m_on)
    if off_asserts != 1:
        probs.append(
            "expected exactly one overflow assert in vanilla MIR "
            f"(found {off_asserts}; fixture or accounting drifted)"
        )
    if on_asserts != 0:
        probs.append(f"verified MIR retains {on_asserts} overflow assert(s)")
    if "WithOverflow" not in m_on:
        probs.append("verified MIR dropped the arithmetic rvalue (NOT value-preserving)")
    print(f"  {'PASS' if not probs else 'FAIL'}  {name}: elided_verified={elided_count(on.stderr)} elided_vanilla={elided_count(off.stderr)}"
          + ("" if not probs else "  <- " + "; ".join(probs)))
    if probs:
        fails.append(name)

for name, src in UNSAFE.items():
    on = compile(src, verify=True)
    probs = []
    if on.returncode == 0:
        probs.append("genuinely-unsafe op compiled clean (verification should FAIL)")
    if elided_count(on.stderr) != 0:
        probs.append("elided a check on an UNVERIFIED op (soundness hole!)")
    print(f"  {'PASS' if not probs else 'FAIL'}  {name}: exit={on.returncode} elided={elided_count(on.stderr)}"
          + ("" if not probs else "  <- " + "; ".join(probs)))
    if probs:
        fails.append(name)

print()
if fails:
    print(f"FAILED: {', '.join(fails)}"); sys.exit(1)
print("ALL proven-overflow-check elision regressions PASS "
      "(kernel-certified ops elide; unsafe rejected; vanilla baseline + value-preserving)")
