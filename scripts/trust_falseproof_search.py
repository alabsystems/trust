#!/usr/bin/env python3
# Trust differential FALSE-PROOF search ("adjacent program" soundness fuzzer).
#
# The load-bearing soundness question for a self-proving compiler: does Trust ever
# statically PROVE an obligation that a concrete execution VIOLATES? This tool searches
# the neighborhood of patterns Trust proves through its verifier — parametric "adjacent"
# variants (array size, element/accumulator type, operator, trip count, guards) — and
# cross-checks two independent oracles per variant:
#
#   STATIC      : batteries-on `trustc -Z trust-policy=advisory` (explicit advisory verification).
#                 fully_proved iff the report
#                 is "N proved, 0 failed, 0 unknown, 0 timed out, 0 runtime-checked out of N".
#   STATIC-FULL : the SAME function under batteries-on strict verification (D4). In strict mode a
#                 refutation is a BUILD ERROR and anything-not-proved routes to `failed`, so
#                 fully_proved = exit 0 AND the note shows every obligation proved. This is
#                 the independent oracle for the class where nearly every kernel-certified P0
#                 false proof has lived (the i128 abstract-interp TOP, range-contains &mut
#                 staleness, Option/Result payload-read aliasing, …).
#   RUNTIME     : the SAME function compiled WITHOUT the verifier, with overflow-checks +
#                 debug-assertions ON, driven on WORST-CASE inputs (T::MAX elements, full
#                 trip count) behind `black_box` so nothing const-folds. A panic (exit != 0)
#                 is a real overflow/bounds violation witness.
#
# Classification (advisory STATIC vs RUNTIME):
#   FALSE_PROOF      static fully-proved  AND runtime overflows  <-- SOUNDNESS BUG (loud)
#   SOUND_PROOF      static fully-proved  AND runtime safe       <-- superiority win
#   CORRECT_REJECT   static not-proved    AND runtime overflows  <-- sound + useful
#   COMPLETENESS_GAP static not-proved    AND runtime safe       <-- a proving frontier
# plus the strict pass adds, independently:
#   FALSE_PROOF_FULL strict fully-proved (exit 0) AND runtime overflows  <-- SOUNDNESS BUG
#
# Generator families cover the default arithmetic/bounds/alloc surface PLUS (E3): float
# value obligations (FpAdd/Sub/Mul/Div/FpNeg, exercised via a float result cast to an array
# index), and opaque-path stubs (dyn-dispatch / async / atomic) that must stay Unknown and
# never be vacuously proved.
#
# A FALSE_PROOF, a FALSE_PROOF_FULL, or an opaque-path over-claim are the only failures that
# matter; the tool exits non-zero if any is found. COMPLETENESS_GAPs are reported as the
# prioritized frontier for new proving capability.
#
# Env knobs (all additive; defaults preserve historical behavior):
#   TRUST_FP_LIMIT=N   run at most N variants total (a tiny smoke subset).
#   TRUST_FP_FULL=0    skip the strict static pass (D4); default runs it.
#
# Author: Andrew Yates. Copyright 2026 Andrew Yates.
import os
import subprocess
import sys
import tempfile
import itertools
import re

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
TRUSTC = os.environ.get("TRUSTC", os.path.join(REPO, "build/host/stage2/bin/trustc"))
ENV = dict(os.environ)
ENV["LIBRARY_PATH"] = "/tmp/trust_link_shims:/opt/homebrew/opt/z3/lib:" + ENV.get("LIBRARY_PATH", "")
ENV["LD_LIBRARY_PATH"] = "/opt/homebrew/opt/z3/lib:" + ENV.get("LD_LIBRARY_PATH", "")
ENV["DYLD_LIBRARY_PATH"] = "/opt/homebrew/opt/z3/lib:" + ENV.get("DYLD_LIBRARY_PATH", "")

VERDICT_RE = re.compile(
    r"Trust verification: (\d+) proved, (\d+) failed, (\d+) unknown, "
    r"(\d+) timed out, (\d+) runtime-checked out of (\d+) obligation"
)


def static_fully_proved(code, workdir):
    """Run explicit advisory verification; return (fully_proved, summary_str)."""
    src = os.path.join(workdir, "lib.rs")
    with open(src, "w") as f:
        f.write("#![crate_type = \"lib\"]\n" + code)
    out = os.path.join(workdir, "lib.rlib")
    r = subprocess.run(
        # Verification is batteries-on. This comparison lane explicitly removes
        # fail-closed enforcement while retaining every advisory proof row.
        [
            TRUSTC,
            "--edition",
            "2021",
            "--crate-type",
            "lib",
            "-Z",
            "trust-policy=advisory",
            src,
            "-o",
            out,
        ],
        env=ENV, capture_output=True, text=True, timeout=180,
    )
    text = r.stdout + r.stderr
    m = VERDICT_RE.search(text)
    if not m:
        return (False, "no-summary" + ("/" + "compile-error" if r.returncode != 0 else ""))
    proved, failed, unknown, timed, rtc, total = map(int, m.groups())
    fully = (failed == 0 and unknown == 0 and timed == 0 and rtc == 0 and total > 0 and proved == total)
    return (fully, f"{proved}p/{failed}f/{unknown}u/{rtc}rtc of {total}")


def static_fully_proved_full(code, workdir):
    """Run STRICT (default fail-closed) verification; return (fully_proved, summary).

    This is the D4 analogue of `static_fully_proved` for the strict verifier, where
    the load-bearing P0 false proofs have historically lived (kernel-certified strict
    proofs that runtime-violate: the i128 abstract-interp TOP, the range-contains
    &mut staleness, the Option/Result payload-read aliasing, …). Strict mode makes a
    Level-0 refutation a BUILD ERROR (exit != 0) and routes anything not fully proved
    to `failed`, so a strict build that EXITS 0 is the compiler's strongest assertion
    "every safety obligation is discharged". `fully_proved` is therefore exit-0 AND a
    verdict note of "N proved, 0 failed/unknown/timed/rtc out of N" — both signals must
    agree (a note saying all-proved while the build aborted, or vice versa, is treated
    as NOT fully proved, fail-closed). Pairing this with the worst-case runtime oracle
    is exactly the net that would catch a regression that weakens strict mode's
    fail-closed posture (the roadmap's rank-1 `unsupported_mir`→UNKNOWN item): a strict
    build that returns 0 while the program overflows is a strict FALSE_PROOF.
    """
    src = os.path.join(workdir, "lib_full.rs")
    with open(src, "w") as f:
        f.write("#![crate_type = \"lib\"]\n" + code)
    out = os.path.join(workdir, "lib_full.rlib")
    r = subprocess.run(
        [TRUSTC, "--edition", "2021", "--crate-type", "lib",
         src, "-o", out],
        env=ENV, capture_output=True, text=True, timeout=300,
    )
    text = r.stdout + r.stderr
    # A trustc TOOL error (a dropped/renamed `-Z` flag, bad args) is NOT a verdict —
    # reading it as "not proved" would silently neuter this whole pass on flag drift,
    # so surface it loudly (mirrors the falsification gate's 126 path).
    if re.search(r"unknown unstable option|unrecognized option|"
                 r"only accepted on the nightly|requires -Z ?unstable-options", text):
        return (False, "FULL-TOOL-ERROR(flag-drift?)")
    m = VERDICT_RE.search(text)
    if not m:
    # No verdict note. In strict mode a refutation aborts the build with an error; that
        # is the verifier fail-closing (not proved), which is sound.
        return (False, "full-no-summary" + ("/err" if r.returncode != 0 else ""))
    proved, failed, unknown, timed, rtc, total = map(int, m.groups())
    note_all_proved = (failed == 0 and unknown == 0 and timed == 0 and rtc == 0
                       and total > 0 and proved == total)
    # Belt-and-suspenders: only call it fully proved when BOTH the strict build
    # SUCCEEDED (exit 0) AND the note agrees every obligation is proved. Strict mode aborts
    # (exit != 0) on any failure, so a disagreement means fail-closed.
    fully = note_all_proved and r.returncode == 0
    return (fully, f"[full]{proved}p/{failed}f/{unknown}u/{rtc}rtc of {total}")


def runtime_overflows(code, driver_main, workdir):
    """Compile WITHOUT the verifier, overflow-checks ON, run the worst-case driver.
    Return (overflowed, detail)."""
    src = os.path.join(workdir, "bin.rs")
    with open(src, "w") as f:
        f.write(code + "\n" + driver_main + "\n")
    binp = os.path.join(workdir, "bin")
    # The runtime oracle is "compile WITHOUT the verifier, overflow-checks ON, run it":
    # it observes the REAL runtime behavior of an intentionally-buggy probe. Keep the
    # explicit `-Z trust-verify=off` isolation assertion so batteries-on verification
    # cannot turn this execution oracle into a proof build. The separate advisory and
    # strict static passes judge whether Trust proved it.
    c = subprocess.run(
        [TRUSTC, "--edition", "2021", "-Z", "trust-verify=off",
         "-C", "overflow-checks=on", "-C", "debug-assertions=on",
         "-O", src, "-o", binp],
        env=ENV, capture_output=True, text=True, timeout=180,
    )
    if c.returncode != 0:
        # A const-eval overflow is itself a real overflow witness; other compile errors
        # are inconclusive (skip).
        if "this arithmetic operation will overflow" in (c.stdout + c.stderr) or \
           "this operation will panic" in (c.stdout + c.stderr):
            return (True, "const-eval-overflow")
        return (None, "bin-compile-error")
    run = subprocess.run([binp], env=ENV, capture_output=True, text=True, timeout=60)
    if run.returncode != 0:
        return (True, "panic:" + (run.stderr.strip().splitlines() or ["?"])[-1][:80])
    return (False, "ran-ok:" + run.stdout.strip()[:40])


# ---- parametric "adjacent" variant families -------------------------------------------

def maxlit(ty):
    return f"{ty}::MAX"


def families():
    """Yield (name, lib_code, driver_main) for every adjacent variant."""
    elems = ["u8", "u16", "u32"]
    accs = ["u8", "u16", "u32", "u64"]
    sizes = [4, 16, 256, 1000, 4096]

    # Family A: for-each sum reduction `t += x as A` over [E; N].
    for E, A, N in itertools.product(elems, accs, sizes):
        name = f"sum_foreach[{E};{N}]->{A}"
        code = (f"pub fn f(a: &[{E}; {N}]) -> {A} {{ let mut t: {A} = 0; "
                f"for &x in a {{ t += x as {A}; }} t }}")
        drv = (f"fn main() {{ let a = std::hint::black_box([{maxlit(E)}; {N}]); "
               f"let r = std::hint::black_box(f(std::hint::black_box(&a))); "
               f"std::process::exit((r != 0) as i32 & 0); }}")
        yield (name, code, drv)

    # Family B: manual-index sum reduction `t += a[i] as A` for i in 0..N over [E; N].
    for E, A, N in itertools.product(elems, accs, sizes):
        name = f"sum_index[{E};{N}]->{A}"
        code = (f"pub fn f(a: &[{E}; {N}]) -> {A} {{ let mut t: {A} = 0; "
                f"for i in 0..{N} {{ t += a[i] as {A}; }} t }}")
        drv = (f"fn main() {{ let a = std::hint::black_box([{maxlit(E)}; {N}]); "
               f"let r = std::hint::black_box(f(std::hint::black_box(&a))); "
               f"std::process::exit((r != 0) as i32 & 0); }}")
        yield (name, code, drv)

    # Family C: dot-product / multiply-accumulate `t += (a[i] as A)*(b[i] as A)`.
    for E, A, N in itertools.product(elems, accs, sizes):
        name = f"dot[{E};{N}]->{A}"
        code = (f"pub fn f(a: &[{E}; {N}], b: &[{E}; {N}]) -> {A} {{ let mut t: {A} = 0; "
                f"for i in 0..{N} {{ t += (a[i] as {A}) * (b[i] as {A}); }} t }}")
        drv = (f"fn main() {{ let a = std::hint::black_box([{maxlit(E)}; {N}]); "
               f"let b = std::hint::black_box([{maxlit(E)}; {N}]); "
               f"let r = std::hint::black_box(f(std::hint::black_box(&a), std::hint::black_box(&b))); "
               f"std::process::exit((r != 0) as i32 & 0); }}")
        yield (name, code, drv)

    # Family L: piece #8 length-conflation. A PRIVATE `fill(arr:&mut[E], n)` indexed
    # loop `arr[i]` for i in 0..n, called from a `pub fn run` with a FIXED-size array
    # `[E; N_actual]` and a loop bound `N_bound`. R1 synthesizes P = `n <= arr__slice_len`
    # and the σ length-renderer produces the caller obligation `N_bound <= N_actual`:
    #   * N_bound == N_actual (exclusive loop) → tautology → flip → SOUND_PROOF (safe).
    #   * N_bound  > N_actual → obligation FALSE → no flip → CORRECT_REJECT (runtime OOB).
    #   * N_bound  < N_actual → tautology, indices 0..N_bound-1 in bounds → SOUND_PROOF.
    # The load-bearing property is FALSE_PROOF=0: a length-conflation regression that
    # renders the FORMAL's length (or a different actual's) instead of the real
    # N_actual would prove `N_bound <= N_actual` for N_bound > N_actual → FALSE_PROOF.
    for E in ["u8", "u32", "u64"]:
        for N_actual in [4, 16, 256, 1000]:
            for delta in [-1, 0, 1]:
                N_bound = N_actual + delta
                if N_bound < 0:
                    continue
                name = f"len_conflate[{E};act={N_actual};bound={N_bound}]"
                code = (
                    f"fn fill(arr: &mut [{E}], n: usize) {{ "
                    f"let mut i = 0; while i < n {{ arr[i] = 0; i += 1; }} }} "
                    f"pub fn run() {{ let mut buf = [0{E}; {N_actual}]; "
                    f"fill(&mut buf, {N_bound}); }}"
                )
                drv = (
                    "fn main() { std::hint::black_box(run()); "
                    "std::process::exit(0); }"
                )
                yield (name, code, drv)

    # Family L2: piece #8 TWO-slice conflation (T4 shape). `fill2(a:&mut[E], b:&mut[E], n)`
    # indexes ONLY `a[i]` (i in 0..n); the caller passes a LONG array for `a` and a SHORT
    # one for `b` with `n == len(a)`. P concerns `a__slice_len` and the σ renderer must
    # render a's length (long), NOT b's (short) — so the WIN holds. A regression that
    # leaked b's shorter length into a's obligation would make `n <= a__slice_len` render
    # `n <= short` and REJECT a safe call (a completeness loss), but rendering a's length
    # for b (or vice versa) on the OOB variant is the FALSE_PROOF tripwire. Here `a` is
    # exactly indexed to its own length, so this must stay SOUND_PROOF; the b-length is
    # never read by P (different formal). Demonstrates INV-2 different-slice impossibility.
    for E in ["u8", "u32"]:
        for N_a in [16, 256]:
            N_b = max(4, N_a // 2)
            name = f"len_two_slice[{E};a={N_a};b={N_b}]"
            code = (
                f"fn fill2(a: &mut [{E}], _b: &mut [{E}], n: usize) {{ "
                f"let mut i = 0; while i < n {{ a[i] = 0; i += 1; }} }} "
                f"pub fn run() {{ let mut a = [0{E}; {N_a}]; let mut b = [0{E}; {N_b}]; "
                f"fill2(&mut a, &mut b, {N_a}); }}"
            )
            drv = (
                "fn main() { std::hint::black_box(run()); std::process::exit(0); }"
            )
            yield (name, code, drv)

    # Family S: unguarded SCALAR arithmetic `a OP b` over every integer width and signedness
    # (worst case T::MAX both operands — overflows for +, *, so an UNGUARDED op must never be
    # fully proved). Catches the i128/u128 width-resolution false-proof class.
    int_tys = ["i8", "i16", "i32", "i64", "i128", "u8", "u16", "u32", "u64", "u128"]
    for T in int_tys:
        for opname, opsym in [("add", "+"), ("mul", "*")]:
            name = f"scalar_{opname}[{T}]"
            code = f"pub fn f(a: {T}, b: {T}) -> {T} {{ a {opsym} b }}"
            drv = (f"fn main() {{ let r = std::hint::black_box(f("
                   f"std::hint::black_box({maxlit(T)}), std::hint::black_box({maxlit(T)}))); "
                   f"std::process::exit((r != 0) as i32 & 0); }}")
            yield (name, code, drv)

    # Family V: DIVISION / remainder. Unguarded `a / b` must NOT prove (b can be 0); a
    # guard `if b != 0` should let it prove. Plus signed i32::MIN / -1 (overflow).
    widths = {"u8": 8, "u16": 16, "u32": 32, "u64": 64, "i8": 8, "i16": 16, "i32": 32, "i64": 64}
    for T in ["u32", "u64", "i32", "i64"]:
        yield (f"div_unguarded[{T}]",
               f"pub fn f(a: {T}, b: {T}) -> {T} {{ a / b }}",
               f"fn main() {{ let r = std::hint::black_box(f(std::hint::black_box({maxlit(T)}), "
               f"std::hint::black_box(0))); std::process::exit((r != 0) as i32 & 0); }}")
    # Guarded division: for UNSIGNED, `b != 0` is sufficient for safety (no signed-min/-1
    # overflow case), so it is genuinely safe and Trust should PROVE it. (A signed guarded
    # division also needs `!(a==MIN && b==-1)`, so it is omitted — Trust correctly refuses
    # the bare `b != 0` form there.)
    for T in ["u32", "u64"]:
        yield (f"div_guarded[{T}]",
               f"pub fn f(a: {T}, b: {T}) -> {T} {{ if b != 0 {{ a / b }} else {{ 0 }} }}",
               f"fn main() {{ let r = std::hint::black_box(f(std::hint::black_box({maxlit(T)}), "
               f"std::hint::black_box(0))); std::process::exit((r != 0) as i32 & 0); }}")
    yield ("div_signed_min_overflow[i32]",
           "pub fn f(a: i32, b: i32) -> i32 { a / b }",
           "fn main() { let r = std::hint::black_box(f(std::hint::black_box(i32::MIN), "
           "std::hint::black_box(-1))); std::process::exit((r != 0) as i32 & 0); }")

    # Family H: SHIFT. Unguarded `a << s` must NOT prove (s can be >= bit width).
    for T, w in [("u8", 8), ("u16", 16), ("u32", 32), ("u64", 64)]:
        yield (f"shl_unguarded[{T}]",
               f"pub fn f(a: {T}, s: u32) -> {T} {{ a << s }}",
               f"fn main() {{ let r = std::hint::black_box(f(std::hint::black_box(1), "
               f"std::hint::black_box({w}u32))); std::process::exit((r != 0) as i32 & 0); }}")

    # Family I: MODULO / mask index that is OUT OF BOUNDS — the divisor/mask exceeds the
    # array length, so the index can reach `len` (OOB). Must NOT prove.
    for N in [4, 16, 64]:
        yield (f"idx_mod_oob[u8;{N}]",
               f"pub fn f(a: &[u8; {N}], n: usize) -> u8 {{ a[n % {N + 1}] }}",
               f"fn main() {{ let a = std::hint::black_box([0u8; {N}]); "
               f"let r = std::hint::black_box(f(std::hint::black_box(&a), std::hint::black_box({N}))); "
               f"std::process::exit((r != 0) as i32 & 0); }}")
        yield (f"idx_mask_oob[u8;{N}]",
               f"pub fn f(a: &[u8; {N}], n: usize) -> u8 {{ a[n & {2 * N - 1}] }}",
               f"fn main() {{ let a = std::hint::black_box([0u8; {N}]); "
               f"let r = std::hint::black_box(f(std::hint::black_box(&a), std::hint::black_box({2 * N - 1}))); "
               f"std::process::exit((r != 0) as i32 & 0); }}")

    # Family D: element-wise widening square store `out[i] = (a[i] as A)*(a[i] as A)`.
    for E, A, N in itertools.product(elems, accs, [4, 16, 256]):
        name = f"sq_store[{E};{N}]->{A}"
        code = (f"pub fn f(a: &[{E}; {N}], out: &mut [{A}; {N}]) {{ "
                f"for i in 0..{N} {{ out[i] = (a[i] as {A}) * (a[i] as {A}); }} }}")
        drv = (f"fn main() {{ let a = std::hint::black_box([{maxlit(E)}; {N}]); "
               f"let mut out = std::hint::black_box([0 as {A}; {N}]); "
               f"f(std::hint::black_box(&a), std::hint::black_box(&mut out)); "
               f"std::process::exit(std::hint::black_box(out[0] != 1) as i32 & 0); }}")
        yield (name, code, drv)

    # Family SH: SHIFT-SCALED reduction `t += (x as A) << k` over [E; N] — the fixed-point /
    # byte-packing idiom. Exercises `addend_per_iteration_bound` case (c): per-iteration max
    # M = MAX(E) * 2^k. Worst case all-MAX: total is N * (MAX(E) << k), so the grid spans
    # SOUND_PROOF (fits A) and CORRECT_REJECT (overflows A — self-limiting). A FALSE_PROOF here
    # is the shift bound being wrong (e.g. forgetting the shift truncates / over-claiming M).
    for E, A, N, k in itertools.product(["u8", "u16"], accs, [4, 16, 256], [1, 2, 4, 8]):
        name = f"shift[{E};{N}]<<{k}->{A}"
        code = (f"pub fn f(a: &[{E}; {N}]) -> {A} {{ let mut t: {A} = 0; "
                f"for &x in a {{ t += (x as {A}) << {k}; }} t }}")
        drv = (f"fn main() {{ let a = std::hint::black_box([{maxlit(E)}; {N}]); "
               f"let r = std::hint::black_box(f(std::hint::black_box(&a))); "
               f"std::process::exit((r != 0) as i32 & 0); }}")
        yield (name, code, drv)

    # Family NM: NESTED 2D matrix sum `for i { for j { t += a[i][j] as A } }` over [[E;M];N].
    # Exercises the PRODUCT trip count K = N*M (`total_loop_iterations`) and the DFS loop
    # counting (`count_back_edges` must see exactly 2 headers). Worst case all-MAX: sum is
    # N*M*E::MAX, so the grid spans SOUND_PROOF (fits A) and CORRECT_REJECT (overflows A,
    # the self-limiting bound). A FALSE_PROOF here is the product trip count being wrong.
    for E, A, (N, M) in itertools.product(["u8", "u16"], accs, [(2, 2), (4, 4), (4, 8), (16, 16)]):
        name = f"nest2d[{E};{N}x{M}]->{A}"
        code = (f"pub fn f(a: &[[{E}; {M}]; {N}]) -> {A} {{ let mut t: {A} = 0; "
                f"for i in 0..{N} {{ for j in 0..{M} {{ t += a[i][j] as {A}; }} }} t }}")
        drv = (f"fn main() {{ let a = std::hint::black_box([[{maxlit(E)}; {M}]; {N}]); "
               f"let r = std::hint::black_box(f(std::hint::black_box(&a))); "
               f"std::process::exit((r != 0) as i32 & 0); }}")
        yield (name, code, drv)

    # Family NM3: NESTED 3D sum — TRIPLE product trip count K = N*M*P, 3-level DFS back-edge
    # counting (exactly 3 headers). All dims small enough that all-MAX u8 fits the A widths
    # used, so these are SOUND_PROOF — they confirm the deeper nest still proves (not a gap).
    for E, A, (N, M, P) in itertools.product(["u8"], ["u16", "u32", "u64"], [(2, 2, 2), (4, 4, 4)]):
        name = f"nest3d[{E};{N}x{M}x{P}]->{A}"
        code = (f"pub fn f(a: &[[[{E}; {P}]; {M}]; {N}]) -> {A} {{ let mut t: {A} = 0; "
                f"for i in 0..{N} {{ for j in 0..{M} {{ for k in 0..{P} {{ "
                f"t += a[i][j][k] as {A}; }} }} }} t }}")
        drv = (f"fn main() {{ let a = std::hint::black_box([[[{maxlit(E)}; {P}]; {M}]; {N}]); "
               f"let r = std::hint::black_box(f(std::hint::black_box(&a))); "
               f"std::process::exit((r != 0) as i32 & 0); }}")
        yield (name, code, drv)

    # Family NW: NESTED with an UNBOUNDED inner `while j < n` — the SOUNDNESS ADVERSARY for the
    # product trip count. There is ONE `Iterator::next` (the outer `for`) but TWO loops, so
    # `#next != #back-edge headers` and NO bound may be emitted; the self-add runs 4*n times and
    # genuinely overflows for the worst-case n. Trust must NOT prove (CORRECT_REJECT). A
    # FALSE_PROOF here is exactly the product trip count under-counting an unbounded loop.
    for A, nbig in [("u16", 1000), ("u32", 5_000_000)]:
        name = f"nest_while_unbounded->{A}"
        code = (f"pub fn f(a: &[u8; 4], n: usize) -> {A} {{ let mut t: {A} = 0; "
                f"for i in 0..4 {{ let _ = i; let mut j = 0usize; "
                f"while j < n {{ t += a[j % 4] as {A}; j += 1; }} }} t }}")
        drv = (f"fn main() {{ let a = std::hint::black_box([u8::MAX; 4]); "
               f"let r = std::hint::black_box(f(std::hint::black_box(&a), "
               f"std::hint::black_box({nbig}usize))); "
               f"std::process::exit((r != 0) as i32 & 0); }}")
        yield (name, code, drv)

    # Family SR: SOUNDNESS REGRESSION guards for hunt-5 false-proof classes (commit 579b8646a2).
    # Each UNSAFE witness must stay CORRECT_REJECT (Trust does NOT prove; runtime panics) — a
    # regression that reintroduces the stale-fact / unconditional-clamp bug flips it to FALSE_PROOF.
    # The SAFE counterparts must stay SOUND_PROOF — an over-aggressive fix shows COMPLETENESS_GAP.
    bb = "std::hint::black_box"
    # Class B: min/max result fact must NOT survive a `&mut` reassignment of the local.
    yield ("sr_min_mutborrow_oob",
           "pub fn f(a: usize, b: usize, arr: &[u8; 4]) -> u8 { "
           "let mut i = a.min(3); let p = &mut i; *p = b; arr[i] }",
           f"fn main() {{ let arr = {bb}([1u8,2,3,4]); "
           f"let r = {bb}(f({bb}(0usize), {bb}(6543usize), {bb}(&arr))); "
           f"std::process::exit((r != 0) as i32 & 0); }}")
    yield ("sr_max_mutborrow_underflow",
           "pub fn f(a: u32, b: u32) -> u32 { "
           "let mut m = a.max(10); let p = &mut m; *p = b; m - 10 }",
           f"fn main() {{ let r = {bb}(f({bb}(0u32), {bb}(0u32))); "
           f"std::process::exit((r != 0) as i32 & 0); }}")
    # Class A: clamp(x, lo, hi) with lo > hi PANICS — the `lo <= r <= hi` fact must be conditional.
    yield ("sr_clamp_lohi_index",
           "pub fn f(x: usize, arr: &[u8; 4]) -> u8 { arr[x.clamp(5, 2)] }",
           f"fn main() {{ let arr = {bb}([1u8,2,3,4]); "
           f"let r = {bb}(f({bb}(0usize), {bb}(&arr))); "
           f"std::process::exit((r != 0) as i32 & 0); }}")
    yield ("sr_clamp_lohi_overflow",
           "pub fn f(x: u8) -> u8 { x.clamp(200u8, 50u8).wrapping_add(0) + 100 }",
           f"fn main() {{ let r = {bb}(f({bb}(0u8))); "
           f"std::process::exit((r != 0) as i32 & 0); }}")
    # SAFE counterparts: must remain SOUND_PROOF (the legitimate clamped/min index idioms).
    yield ("sr_min_index_safe",
           "pub fn f(n: usize, arr: &[u8; 4]) -> u8 { arr[n.min(3)] }",
           f"fn main() {{ let arr = {bb}([1u8,2,3,4]); "
           f"let r = {bb}(f({bb}(usize::MAX), {bb}(&arr))); "
           f"std::process::exit((r != 0) as i32 & 0); }}")
    yield ("sr_clamp_index_safe",
           "pub fn f(n: usize, arr: &[u8; 4]) -> u8 { arr[n.clamp(0, 3)] }",
           f"fn main() {{ let arr = {bb}([1u8,2,3,4]); "
           f"let r = {bb}(f({bb}(usize::MAX), {bb}(&arr))); "
           f"std::process::exit((r != 0) as i32 & 0); }}")
    # hunt-7: a fact (min/cast) on an Option payload must NOT survive a mutation through
    # `o.as_mut()` (`let mut o=Some(a.min(3)); if let Some(r)=o.as_mut(){*r=b;} match o{Some(i)=>arr[i]}`).
    # Must stay CORRECT_REJECT — a regression reintroducing the stale construction payload fact flips
    # it to FALSE_PROOF. The SAFE construct-then-match (no mutation) must stay SOUND_PROOF.
    yield ("sr_option_aspmut_min_oob",
           "pub fn f(a: usize, b: usize, arr: &[u8; 4]) -> u8 { "
           "let mut o = Some(a.min(3)); if let Some(r) = o.as_mut() { *r = b; } "
           "match o { Some(i) => arr[i], None => 0 } }",
           f"fn main() {{ let arr = {bb}([1u8,2,3,4]); "
           f"let r = {bb}(f({bb}(0usize), {bb}(6543usize), {bb}(&arr))); "
           f"std::process::exit((r != 0) as i32 & 0); }}")
    yield ("sr_option_aspmut_cast_overflow",
           "pub fn f(a: u8, b: u32) -> u32 { let mut o = Some(a as u32); "
           "if let Some(r) = o.as_mut() { *r = b; } match o { Some(i) => i + 1, None => 0 } }",
           f"fn main() {{ let r = {bb}(f({bb}(0u8), {bb}(u32::MAX))); "
           f"std::process::exit((r != 0) as i32 & 0); }}")
    yield ("sr_option_construct_match_safe",
           "pub fn f(a: usize, arr: &[u8; 4]) -> u8 { let o = Some(a.min(3)); "
           "match o { Some(i) => arr[i], None => 0 } }",
           f"fn main() {{ let arr = {bb}([1u8,2,3,4]); "
           f"let r = {bb}(f({bb}(usize::MAX), {bb}(&arr))); "
           f"std::process::exit((r != 0) as i32 & 0); }}")
    # hunt-8: the `is_ascii() => x<=127` guard fact must NOT survive a reassignment of the guarded
    # value (`if x.is_ascii() { x = 200; arr[x as usize] }`). Must stay CORRECT_REJECT; the legit
    # non-reassigned `if x.is_ascii() { arr[x as usize] }` must stay SOUND_PROOF.
    yield ("sr_isascii_reassign_oob",
           "pub fn f(mut x: u8, arr: &[u32; 128]) -> u32 { "
           "if x.is_ascii() { x = 200; arr[x as usize] } else { 0 } }",
           f"fn main() {{ let arr = {bb}([7u32; 128]); "
           f"let r = {bb}(f({bb}(65u8), {bb}(&arr))); "
           f"std::process::exit((r != 0) as i32 & 0); }}")
    yield ("sr_isascii_mutborrow_oob",
           "pub fn f(mut x: u8, b: u8, arr: &[u32; 128]) -> u32 { "
           "if x.is_ascii() { let p = &mut x; *p = b; arr[x as usize] } else { 0 } }",
           f"fn main() {{ let arr = {bb}([7u32; 128]); "
           f"let r = {bb}(f({bb}(65u8), {bb}(200u8), {bb}(&arr))); "
           f"std::process::exit((r != 0) as i32 & 0); }}")
    yield ("sr_isascii_index_safe",
           "pub fn f(x: u8, arr: &[u32; 128]) -> u32 { "
           "if x.is_ascii() { arr[x as usize] } else { 0 } }",
           f"fn main() {{ let arr = {bb}([7u32; 128]); "
           f"let r = {bb}(f({bb}(200u8), {bb}(&arr))); "
           f"std::process::exit((r != 0) as i32 & 0); }}")
    # hunt-9: the is_ascii staleness gate must be PROJECTION-AWARE — a fact on a tuple/struct FIELD
    # (`t.0.is_ascii()`) must not survive a field store (`t.0 = 200`). Must stay CORRECT_REJECT.
    yield ("sr_isascii_field_reassign_oob",
           "pub fn f(a: u8, arr: &[u32; 128]) -> u32 { let mut t = (a, 0u8); "
           "if t.0.is_ascii() { t.0 = 200; arr[t.0 as usize] } else { 0 } }",
           f"fn main() {{ let arr = {bb}([7u32; 128]); "
           f"let r = {bb}(f({bb}(65u8), {bb}(&arr))); "
           f"std::process::exit((r != 0) as i32 & 0); }}")
    yield ("sr_isascii_field_safe",
           "pub fn f(a: u8, arr: &[u32; 128]) -> u32 { let t = (a, 0u8); "
           "if t.0.is_ascii() { arr[t.0 as usize] } else { 0 } }",
           f"fn main() {{ let arr = {bb}([7u32; 128]); "
           f"let r = {bb}(f({bb}(200u8), {bb}(&arr))); "
           f"std::process::exit((r != 0) as i32 & 0); }}")
    # hunt-10: the scaled-index dominance resolver (resolve_checked_result_through_dominating_
    # overflow_assert) + the dominating-guard threading (#49) must NOT let a guard `i<4` survive a
    # REASSIGNMENT of the guarded index between the guard and the index. The stale edge guard
    # `i<4` conjoined with the real violation `i>=8` would be UNSAT => vacuous bounds proof. The
    # value-stability protection drops the guard on reassignment; these lock that in across the
    # runtime-reassign / self-referential / field-projection vectors (CORRECT_REJECT), while the
    # legit non-reassigned scaled/field-guarded accesses must stay SOUND_PROOF.
    yield ("sr_scaledidx_reassign_oob",
           "pub fn f(mut i: usize, b: usize, a: &[i32; 8]) -> i32 { "
           "if i < 4 { i = b; a[i] } else { 0 } }",
           f"fn main() {{ let a = {bb}([7i32; 8]); "
           f"let r = {bb}(f({bb}(0usize), {bb}(100usize), {bb}(&a))); "
           f"std::process::exit((r != 0) as i32 & 0); }}")
    yield ("sr_scaledidx_selfadd_oob",
           "pub fn f(mut i: usize, a: &[i32; 8]) -> i32 { "
           "if i < 4 { i += 100; a[i] } else { 0 } }",
           f"fn main() {{ let a = {bb}([7i32; 8]); "
           f"let r = {bb}(f({bb}(0usize), {bb}(&a))); "
           f"std::process::exit((r != 0) as i32 & 0); }}")
    yield ("sr_scaledidx_field_oob",
           "pub fn f(mut t: (usize, u8), b: usize, a: &[i32; 8]) -> i32 { "
           "if t.0 < 4 { t.0 = b; a[t.0] } else { 0 } }",
           f"fn main() {{ let a = {bb}([7i32; 8]); "
           f"let r = {bb}(f({bb}((0usize, 0u8)), {bb}(100usize), {bb}(&a))); "
           f"std::process::exit((r != 0) as i32 & 0); }}")
    yield ("sr_scaledidx_scaled_safe",
           "pub fn f(i: usize, a: &[i32; 8]) -> i32 { if i < 4 { a[i * 2] } else { 0 } }",
           f"fn main() {{ let a = {bb}([7i32; 8]); "
           f"let r = {bb}(f({bb}(0usize), {bb}(&a))); "
           f"std::process::exit((r != 0) as i32 & 0); }}")
    yield ("sr_scaledidx_field_safe",
           "pub fn f(t: (usize, u8), a: &[i32; 8]) -> i32 { if t.0 < 4 { a[t.0] } else { 0 } }",
           f"fn main() {{ let a = {bb}([7i32; 8]); "
           f"let r = {bb}(f({bb}((0usize, 0u8)), {bb}(&a))); "
           f"std::process::exit((r != 0) as i32 & 0); }}")
    # hunt-11 Root A: the UnboundedAllocation obligation must be BYTE-aware. A multi-byte element
    # makes `count * size_of::<T>()` overflow isize::MAX (capacity-overflow panic) while `count`
    # stays below the element ceiling — so `Vec::<[u8;1<<40]>::with_capacity(n<2^27)` / `reserve`
    # proved (FP1 even kernel-CIC certified in -full) yet panics. Must stay CORRECT_REJECT. The u8
    # element (stride 1) guarded `with_capacity` must stay SOUND_PROOF (no regression).
    yield ("sr_wcap_byte_overflow",
           "pub fn f(n: usize) -> Vec<[u8; 1usize << 40]> { "
           "if n < (1usize << 27) { Vec::with_capacity(n) } else { Vec::new() } }",
           f"fn main() {{ let v = {bb}(f({bb}(1usize << 23))); "
           f"std::process::exit((v.capacity() != 0) as i32 & 0); }}")
    yield ("sr_reserve_byte_overflow",
           "pub fn f(v: &mut Vec<[u8; 1usize << 40]>, n: usize) { if n < (1usize << 27) { v.reserve(n); } }",
           f"fn main() {{ let mut v: Vec<[u8; 1usize << 40]> = Vec::new(); "
           f"f({bb}(&mut v), {bb}(1usize << 23)); "
           f"std::process::exit((v.capacity() != 0) as i32 & 0); }}")
    yield ("sr_wcap_u8_safe",
           "pub fn f(n: usize) -> Vec<u8> { if n < 1024 { Vec::with_capacity(n) } else { Vec::new() } }",
           f"fn main() {{ let v = {bb}(f({bb}(16usize))); "
           f"std::process::exit((v.capacity() == usize::MAX) as i32 & 0); }}")
    # hunt-11 Root B: a STRAY `it.next()` consumed OUTSIDE any loop must NOT balance a manual
    # while-loop's back-edge count and donate its range trip-count K as the while accumulator bound.
    # `let mut it=0..2; let _=it.next(); while m<100 {out[m]=1; m+=1;}` proved (default) yet writes
    # out[3..99] OOB. Must stay CORRECT_REJECT; a real for-each reduction must stay SOUND_PROOF.
    yield ("sr_stray_next_trip_oob",
           "pub fn f(out: &mut [u8; 3]) { let mut it = 0..2; let _f = it.next(); "
           "let mut m: usize = 0; while m < 100 { out[m] = 1; m += 1; } }",
           f"fn main() {{ let mut a = {bb}([0u8; 3]); f({bb}(&mut a)); "
           f"std::process::exit((a[0] != 0) as i32 & 0); }}")
    yield ("sr_foreach_sum_safe",
           "pub fn f(a: &[u8; 16]) -> u32 { let mut t: u32 = 0; for &x in a { t += x as u32; } t }",
           f"fn main() {{ let a = {bb}([255u8; 16]); "
           f"let r = {bb}(f({bb}(&a))); std::process::exit((r != 4080) as i32 & 0); }}")
    # hunt-11 Root A residual closure: the byte-aware alloc obligation must use the AUTHORITATIVE
    # element size (tcx.layout_of, carried via the __trust_elem_bytes_N token) so it sizes EVERY
    # concrete element — incl. a NAMED struct whose spelling hides its size — and the 256MiB
    # AVAILABILITY byte term must apply to with_capacity/reserve (not just from_elem), catching the
    # realistic multi-byte OOM that the count-only ceiling waved through. Must stay CORRECT_REJECT;
    # a TIGHTLY-bounded multi-byte with_capacity must stay SOUND_PROOF (no over-refusal).
    yield ("sr_wcap_named_struct_oob",
           "pub struct Big([u8; 1usize << 35]); "
           "pub fn f(n: usize) -> Vec<Big> { if n < (1usize << 28) { Vec::with_capacity(n) } else { Vec::new() } }",
           f"fn main() {{ let v = {bb}(f({bb}((1usize << 28) - 1))); "
           f"std::process::exit((v.capacity() != 0) as i32 & 0); }}")
    yield ("sr_wcap_megabyte_elem_oob",
           "pub fn f(n: usize) -> Vec<[u8; 1usize << 20]> { "
           "if n < (1usize << 28) { Vec::with_capacity(n) } else { Vec::new() } }",
           f"fn main() {{ let v = {bb}(f({bb}((1usize << 28) - 1))); "
           f"std::process::exit((v.capacity() != 0) as i32 & 0); }}")
    yield ("sr_wcap_multibyte_tight_safe",
           "pub fn f(n: usize) -> Vec<[u8; 4096]> { if n < 1000 { Vec::with_capacity(n) } else { Vec::new() } }",
           f"fn main() {{ let v = {bb}(f({bb}(16usize))); "
           f"std::process::exit((v.capacity() == usize::MAX) as i32 & 0); }}")
    # hunt-13: the range-validation guard `(L..=U).contains(&x)` must NOT carry its `x<=U` fact
    # across a `*p=b` reassignment via `p=&mut x` — that was a KERNEL-CERTIFIED OOB false proof (the
    # rewrite_range_contains_calls lane missed the &mut/AddressOf staleness vector). Must stay
    # CORRECT_REJECT; the legit non-mutated `(0..=4).contains(&x){arr[x]}` must stay SOUND_PROOF.
    yield ("sr_rangecontains_mut_oob",
           "pub fn f(mut x: usize, b: usize, arr: &[u8; 8]) -> u8 { "
           "if (0..=4).contains(&x) { let p = &mut x; *p = b; arr[x] } else { 0 } }",
           f"fn main() {{ let arr = {bb}([7u8; 8]); "
           f"let r = {bb}(f({bb}(0usize), {bb}(100usize), {bb}(&arr))); "
           f"std::process::exit((r != 0) as i32 & 0); }}")
    yield ("sr_rangecontains_safe",
           "pub fn f(x: usize, arr: &[u8; 8]) -> u8 { if (0..=4).contains(&x) { arr[x] } else { 0 } }",
           f"fn main() {{ let arr = {bb}([7u8; 8]); "
           f"let r = {bb}(f({bb}(0usize), {bb}(&arr))); "
           f"std::process::exit((r != 7) as i32 & 0); }}")
    # i128 add/sub overflow: the vcgen abstract_interp `try_eval_boolean` pre-discharge read
    # `interval_add`'s overflow-to-TOP ([i128::MIN,i128::MAX]) endpoints as PRECISE bounds, so
    # `a+b > i128::MAX` evaluated definitely-false and `fn f(a:i128,b:i128){a+b}` was kernel-headline
    # PROVED yet overflows at runtime — width-specific (only at 128-bit does the type MAX coincide
    # with the domain's TOP.hi). FIX = check_comparison_intervals returns None on a TOP operand.
    # Both must stay CORRECT_REJECT (unguarded 128-bit add/sub CAN overflow); a regression that
    # re-reads TOP as a bound flips them to FALSE_PROOF.
    yield ("sr_i128_add_overflow",
           "pub fn f(a: i128, b: i128) -> i128 { a + b }",
           f"fn main() {{ let r = {bb}(f({bb}(i128::MAX), {bb}(1i128))); "
           f"std::process::exit((r == 0) as i32 & 0); }}")
    yield ("sr_i128_sub_overflow",
           "pub fn f(a: i128, b: i128) -> i128 { a - b }",
           f"fn main() {{ let r = {bb}(f({bb}(i128::MIN), {bb}(1i128))); "
           f"std::process::exit((r == 0) as i32 & 0); }}")
    # task #77: signed-128 add/sub dominating-guard threading. A guarded-SAFE i128 add must
    # PROVE (SOUND_PROOF, completeness), while the &mut-stale guard must stay CORRECT_REJECT —
    # the guard map must EXCLUDE `a<10` once `a` is reassigned via `*p=b`, else the stale bound
    # would vacuously discharge the overflow (the i128 false-proof class). The bound (-1000,1000)
    # makes a+b in (-2000,2000), well inside i128.
    yield ("sr_i128_add_guarded_safe",
           "pub fn f(a: i128, b: i128) -> i128 { if a>-1000 && a<1000 && b>-1000 && b<1000 { a+b } else { 0 } }",
           f"fn main() {{ let r = {bb}(f({bb}(999i128), {bb}(999i128))); "
           f"std::process::exit((r != 1998) as i32 & 0); }}")
    yield ("sr_i128_add_mutstale",
           "pub fn f(mut a: i128, b: i128) -> i128 { if a<10 { let p=&mut a; *p=b; a+b } else { 0 } }",
           f"fn main() {{ let r = {bb}(f({bb}(5i128), {bb}(i128::MAX))); {bb}(r); }}")
    # hunt-revealed (2026-06-24): the CONST-ARITH i64-width FALSE-PROOF class. `ConstValue::Int`
    # carried no width, so an i128 const SUBEXPRESSION (`i128::MAX-1`, `i128::MIN+1`, `(MAX/2)*2`)
    # was typed i64; the i64-width in-range premise then emitted for its VALUE (`i64::MIN<=v<=
    # i64::MAX`) is CONSTANT-FALSE for a value outside i64, vacuously discharging the downstream
    # `x+b` overflow — a DEFAULT-mode false proof (`let x=i128::MAX-1; x+b` reported 2/2 proved yet
    # overflows). FIX = operand_ty widens a ConstValue::Int that does NOT fit i64 to width 128.
    # Must stay CORRECT_REJECT (x near the boundary + free b overflows); a regression re-narrowing
    # the const width flips them to FALSE_PROOF. The small-const sibling (value fits i64) is sound.
    yield ("sr_i128_constarith_add",
           "pub fn f(b: i128) -> i128 { let x: i128 = i128::MAX - 1; x + b }",
           f"fn main() {{ let r = {bb}(f({bb}(999i128))); {bb}(r); }}")
    yield ("sr_i128_constarith_sub",
           "pub fn f(b: i128) -> i128 { let x: i128 = i128::MIN + 1; x - b }",
           f"fn main() {{ let r = {bb}(f({bb}(999i128))); {bb}(r); }}")
    yield ("sr_i128_constarith_guarded",
           "pub fn f(b: i128) -> i128 { let x: i128; if b>0 && b<1000 { x = i128::MAX - 10; x + b } else { 0 } }",
           f"fn main() {{ let r = {bb}(f({bb}(999i128))); {bb}(r); }}")
    # frontier (2026-06-24): SIGNED reduction `s += x as ACC` over a fixed array of signed `iN`
    # elements. The accumulator infra was UNSIGNED-only (single upper bound `acc <= C + K*MAX`,
    # unsound for negative addends), so signed elements stayed runtime-checked. Fix emits the
    # SYMMETRIC pair `[C + K*MIN, C + K*MAX]` (`signed_addend_per_iteration_range`); ay discharges
    # both overflow directions. The safe cases must be SOUND_PROOF; the i8-accumulator and NESTED
    # (k = M*LEN via total_loop_iterations) cases GENUINELY overflow and must be CORRECT_REJECT —
    # the nested case pins that the bound multiplies by the WHOLE-NEST k, not the inner length.
    yield ("sr_signed_acc_i8_i32",
           "pub fn f(a: &[i8;8]) -> i32 { let mut s: i32 = 0; for &x in a { s += x as i32; } s }",
           f"fn main() {{ let a = {bb}([1i8,-2,3,-4,5,-6,7,-8]); {bb}(f({bb}(&a))); }}")
    yield ("sr_signed_acc_i16_i64",
           "pub fn f(a: &[i16;32]) -> i64 { let mut s: i64 = 0; for &x in a { s += x as i64; } s }",
           f"fn main() {{ let a = {bb}([100i16;32]); {bb}(f({bb}(&a))); }}")
    yield ("sr_signed_acc_i8_overflow",
           "pub fn f(a: &[i8;8]) -> i8 { let mut s: i8 = 0; for &x in a { s += x; } s }",
           f"fn main() {{ let a = {bb}([127i8;8]); {bb}(f({bb}(&a))); }}")
    yield ("sr_signed_acc_nested_overflow",
           "pub fn f(a: &[i8;8]) -> i32 { let mut s: i32 = 0; "
           "for _ in 0..3_000_000 { for &x in a { s += x as i32; } } s }",
           f"fn main() {{ let a = {bb}([127i8;8]); {bb}(f({bb}(&a))); }}")
    # frontier (2026-06-24): SIGNED i128 shift-reduction `t += (x as i128) << 4` over [u8;16]. The
    # i128 add overflow is BV-encoded; v2_signed_bv_accumulator_constraints renders the accumulator
    # bound in signed BV onto the fresh overflow operands so it discharges. Summing i128 ELEMENTS
    # directly (unbounded) overflows → CORRECT_REJECT (no bound rendered).
    yield ("sr_i128_shift_acc_safe",
           "pub fn f(a: &[u8;16]) -> i128 { let mut t: i128 = 0; for &x in a { t += (x as i128) << 4; } t }",
           f"fn main() {{ let a = {bb}([255u8;16]); {bb}(f({bb}(&a))); }}")
    yield ("sr_i128_elem_acc_overflow",
           "pub fn f(a: &[i128;4]) -> i128 { let mut t: i128 = 0; for &x in a { t += x; } t }",
           f"fn main() {{ let a = {bb}([i128::MAX;4]); {bb}(f({bb}(&a))); }}")
    # frontier (2026-06-24): non-square 2D grid flattened index `g[y*W+x]` over nested const-range
    # loops. The flattened-index global facts close [bounds]+[overflow:add]; the BV loop-var yield
    # render closes the BV-encoded [overflow:mul]. Safe (12=3*4) SOUND_PROOF; a len-11 array (idx
    # reaches 11) is OOB → CORRECT_REJECT (bound idx<=11 compatible with violation idx>=11).
    yield ("sr_grid_flattened_safe",
           "pub fn f(g: &[u8;12]) -> u8 { let mut s=0u8; for y in 0..3 { for x in 0..4 { s=s.wrapping_add(g[y*4+x]); } } s }",
           f"fn main() {{ let g = {bb}([7u8;12]); {bb}(f({bb}(&g))); }}")
    yield ("sr_grid_flattened_oob",
           "pub fn f(g: &[u8;11]) -> u8 { let mut s=0u8; for y in 0..3 { for x in 0..4 { s=s.wrapping_add(g[y*4+x]); } } s }",
           f"fn main() {{ let g = {bb}([7u8;11]); {bb}(f({bb}(&g))); }}")
    # frontier (2026-06-24): clamp-via-HELPER `arr[clamp_idx(i)]` where the local
    # `clamp_idx` returns `i.min(LEN-1)`. A whole-crate return-bound SUMMARY records
    # `clamp_idx <= 7`; the call site emits `dest <= 7` (SSA-gated + staleness-versioned),
    # discharging the len-8 index. SOUND: a helper returning `i.min(100)` gives `dest <= 100`,
    # which does NOT imply `dest < 8` → the OOB index stays runtime-checked → panics → CORRECT_REJECT.
    yield ("sr_clamp_via_helper_safe",
           "fn clamp_idx(i: usize) -> usize { i.min(7) } "
           "pub fn f(arr: &[u8;8], i: usize) -> u8 { arr[clamp_idx(i)] }",
           f"fn main() {{ let arr = {bb}([7u8;8]); {bb}(f({bb}(&arr), {bb}(50usize))); }}")
    yield ("sr_clamp_via_helper_oob",
           "fn clamp_idx(i: usize) -> usize { i.min(100) } "
           "pub fn f(arr: &[u8;8], i: usize) -> u8 { arr[clamp_idx(i)] }",
           f"fn main() {{ let arr = {bb}([7u8;8]); {bb}(f({bb}(&arr), {bb}(50usize))); }}")
    # frontier (2026-06-24): clamp-via-helper STALENESS twin — the call result is reassigned
    # through a `&mut` (`let p = &mut j; *p = 100`) AFTER the bounding call, so the `dest <= 7`
    # bound is STALE and MUST be withheld (the hunt-5/7/8 vector). The SSA gate (is_single_static_assignment
    # sees the mutable borrow) drops the fact → OOB stays runtime-checked → panics → CORRECT_REJECT.
    yield ("sr_clamp_via_helper_mutstale",
           "fn clamp_idx(i: usize) -> usize { i.min(7) } "
           "pub fn f(arr: &[u8;8], i: usize) -> u8 { let mut j = clamp_idx(i); let p = &mut j; *p = 100; arr[j] }",
           f"fn main() {{ let arr = {bb}([7u8;8]); {bb}(f({bb}(&arr), {bb}(50usize))); }}")
    # frontier (2026-06-24): clamp bound propagated THROUGH an `as usize` cast. `i.clamp(0,9)` gives
    # j∈[0,9] but `arr[j as usize]` indexes a SEPARATE local; `build_clamp_cast_facts` emits
    # `(j as usize)<=hi` (sound even under truncation; SSA-gated). Safe cases SOUND_PROOF. The hi=12
    # overrun (CORRECT_REJECT) and the &mut-reassignment STALENESS twin (CORRECT_REJECT) pin
    # soundness — the staleness one is the hunt-5/7/8 vector: the gate MUST withhold the stale bound.
    yield ("sr_clamp_cast_index_safe",
           "pub fn f(i: i32, arr: &[u8;10]) -> u8 { let j = i.clamp(0, 9); arr[j as usize] }",
           f"fn main() {{ let arr = {bb}([7u8;10]); {bb}(f({bb}(99i32), {bb}(&arr))); }}")
    yield ("sr_clamp_cast_index_u8_safe",
           "pub fn f(i: i32, arr: &[u8;6]) -> u8 { let j = i.clamp(0, 5); arr[j as usize] }",
           f"fn main() {{ let arr = {bb}([7u8;6]); {bb}(f({bb}(99i32), {bb}(&arr))); }}")
    # non-zero lower bound now proves in BOTH modes (the structural incompatible-const-bounds
    # discharge on index obligations — `(j as usize)<=7 ∧ >=8` is UNSAT — closed the former
    # advisory-lane lo>0 gap). lo=2 AND a negative-input clamp.
    yield ("sr_clamp_cast_index_start_safe",
           "pub fn f(i: i32, arr: &[u8;8]) -> u8 { let j = i.clamp(2, 7); arr[j as usize] }",
           f"fn main() {{ let arr = {bb}([7u8;8]); {bb}(f({bb}(-5i32), {bb}(&arr))); }}")
    yield ("sr_clamp_cast_index_oob",
           "pub fn f(i: i32, arr: &[u8;10]) -> u8 { let j = i.clamp(0, 12); arr[j as usize] }",
           f"fn main() {{ let arr = {bb}([7u8;10]); {bb}(f({bb}(99i32), {bb}(&arr))); }}")
    yield ("sr_clamp_cast_stale_oob",
           "pub fn f(i: i32, arr: &[u8;10]) -> u8 { let mut j = i.clamp(0, 9); "
           "let p = &mut j; *p = 100; arr[j as usize] }",
           f"fn main() {{ let arr = {bb}([7u8;10]); {bb}(f({bb}(5i32), {bb}(&arr))); }}")
    # frontier (2026-06-24): cast-bound propagation generalized from clamp to NON-NEGATIVE bounded
    # intrinsics — `n.rem_euclid(6)`∈[0,5] (any sign of n) and `n.trailing_zeros()`∈[0,32] cast `as
    # usize` then indexed. Safe cases SOUND_PROOF; `rem_euclid(7)` (∈[0,6]) on a len-6 array reaches
    # index 6 → OOB → CORRECT_REJECT (bound `<=6` is COMPATIBLE with violation `>=6`, self-limiting).
    yield ("sr_cast_rem_euclid_safe",
           "pub fn f(n: i32, arr: &[u8;6]) -> u8 { arr[n.rem_euclid(6) as usize] }",
           f"fn main() {{ let arr = {bb}([7u8;6]); {bb}(f({bb}(-13i32), {bb}(&arr))); }}")
    yield ("sr_cast_trailing_zeros_safe",
           "pub fn f(n: u32, arr: &[u8;33]) -> u8 { arr[n.trailing_zeros() as usize] }",
           f"fn main() {{ let arr = {bb}([7u8;33]); {bb}(f({bb}(0u32), {bb}(&arr))); }}")
    yield ("sr_cast_rem_euclid_oob",
           "pub fn f(n: i32, arr: &[u8;6]) -> u8 { arr[n.rem_euclid(7) as usize] }",
           f"fn main() {{ let arr = {bb}([7u8;6]); {bb}(f({bb}(6i32), {bb}(&arr))); }}")
    # frontier (2026-06-24): enum-discriminant index `arr[e as usize]` for a #[repr(u8)] fieldless
    # enum. The bounds VC already carries `disc∈{0..N-1}`, `idx==disc`, and the violation `idx>=len`;
    # the new equality-substitution discharge case-splits the validity disjunction and resolves
    # `idx=disc=k`, refuting `idx>=len` for k<len. Safe (variants==len) SOUND_PROOF; a 5th variant
    # on a len-4 array reaches index 4 → runtime OOB → CORRECT_REJECT (self-limiting: disc=4 does NOT
    # refute idx>=4). DEFAULT-mode (-full native-blocks the discriminant tag, like step_by).
    yield ("sr_enum_disc_index_safe",
           "#[repr(u8)] pub enum E { A, B, C, D } "
           "pub fn f(e: E, arr: &[u8;4]) -> u8 { arr[e as usize] }",
           f"fn main() {{ let arr = {bb}([7u8;4]); {bb}(f({bb}(E::D), {bb}(&arr))); }}")
    yield ("sr_enum_disc_index_oob",
           "#[repr(u8)] pub enum E { A, B, C, D, X } "
           "pub fn f(e: E, arr: &[u8;4]) -> u8 { arr[e as usize] }",
           f"fn main() {{ let arr = {bb}([7u8;4]); {bb}(f({bb}(E::X), {bb}(&arr))); }}")
    # P0 (2026-07-06): enum-disc-set across a NARROWING cast. The tag-set fact must be the
    # tags' IMAGE under the cast (mod 2^dest_width via truncate_nonneg_tag_as_int), never the
    # raw declared set — the raw set intersected with the dest type range is a VACUOUS premise
    # ({0,260,512} ∩ [0,255] = {0}) that FALSE-PROVED a guaranteed OOB (260 as u8 == 4 on
    # len-4). fits: tags fit u8 (fold is identity) → safe on len-6, prove-or-gap, NEVER
    # FALSE_PROOF. wrap_oob: E::B wraps to 4 → runtime OOB → must stay CORRECT_REJECT (a
    # regression re-carrying the raw set flips it to FALSE_PROOF — the loud signal). wrap_safe:
    # all tags ≡ 0 mod 256 → genuinely safe under the folded fact {0}. nonnarrow_oob: `as u16`
    # (no truncation) with tag 512 on len-512 → OOB → CORRECT_REJECT (pins that the identity
    # fold keeps the raw tag reachable).
    yield ("sr_enumdisc_castnarrow_fits",
           "#[repr(u16)] pub enum E { A = 0, B = 1, C = 5 } "
           "pub fn f(e: E, arr: &[u8;6]) -> u8 { arr[(e as u8) as usize] }",
           f"fn main() {{ let arr = {bb}([7u8;6]); {bb}(f({bb}(E::C), {bb}(&arr))); }}")
    yield ("sr_enumdisc_castnarrow_wrap_oob",
           "#[repr(u16)] pub enum E { A = 0, B = 260, C = 512 } "
           "pub fn f(e: E, arr: &[u8;4]) -> u8 { arr[(e as u8) as usize] }",
           f"fn main() {{ let arr = {bb}([7u8;4]); {bb}(f({bb}(E::B), {bb}(&arr))); }}")
    yield ("sr_enumdisc_castnarrow_wrap_safe",
           "#[repr(u16)] pub enum E { A = 0, B = 256, C = 512 } "
           "pub fn f(e: E, arr: &[u8;4]) -> u8 { arr[(e as u8) as usize] }",
           f"fn main() {{ let arr = {bb}([7u8;4]); {bb}(f({bb}(E::C), {bb}(&arr))); }}")
    yield ("sr_enumdisc_nonnarrow_oob",
           "#[repr(u16)] pub enum E { A = 0, B = 260, C = 512 } "
           "pub fn f(e: E, arr: &[u8;512]) -> u8 { arr[(e as u16) as usize] }",
           f"fn main() {{ let arr = {bb}([7u8;512]); {bb}(f({bb}(E::C), {bb}(&arr))); }}")
    # frontier (2026-06-24): `for i in (start..end).step_by(k) { arr[i] }`. StepBy<Range> yields a
    # SUBSET of [start,end); the trace now hops the 2-arg step_by call (like rev) to emit the yield
    # fact `i<end`, and the incompatible-const-bounds discharge closes `arr[i]` (`i<end ∧ i>=len`,
    # end<=len) — for BOTH start=0 AND start>0 (the former lo>0 default asymmetry is gone). A range
    # whose end overruns the array yields an OOB step value → CORRECT_REJECT. DEFAULT-mode (-full
    # native-blocks the step_by iterator call — a fresh-session iterator-yield modeling task).
    yield ("sr_stepby_index_safe",
           "pub fn f(arr: &mut [u8;10]) { for i in (0..10).step_by(3) { arr[i] = 1; } }",
           f"fn main() {{ let mut a = {bb}([0u8;10]); f({bb}(&mut a)); {bb}(&a); }}")
    yield ("sr_stepby_index_start_safe",
           "pub fn f(arr: &mut [u8;10]) { for i in (2..10).step_by(2) { arr[i] = 1; } }",
           f"fn main() {{ let mut a = {bb}([0u8;10]); f({bb}(&mut a)); {bb}(&a); }}")
    yield ("sr_stepby_index_oob",
           "pub fn f(arr: &mut [u8;10]) { for i in (0..15).step_by(3) { arr[i] = 1; } }",
           f"fn main() {{ let mut a = {bb}([0u8;10]); f({bb}(&mut a)); {bb}(&a); }}")
    # frontier (2026-06-24): `for c in a.chunks(n) { c[0] }`. A chunks() sub-slice has length in
    # [1, n], so c[0] is always in bounds — but the length-positive fact `c.len() >= 1` reaches the
    # bounds VC only via the equality `idx_len_var == c__slice_len`; the new equality-class index-len
    # discharge follows that to refute `idx(=0) >= c.len()`. c[0] SOUND_PROOF; c[1] on a non-multiple
    # length (last chunk len 1) is genuinely OOB → CORRECT_REJECT (len in [1,4] doesn't give >= 2).
    yield ("sr_chunks_index0_safe",
           "pub fn f(a: &[u8;12]) -> u8 { let mut s=0u8; for c in a.chunks(4) { s=s.wrapping_add(c[0]); } s }",
           f"fn main() {{ let a = {bb}([7u8;12]); {bb}(f({bb}(&a))); }}")
    yield ("sr_chunks_index1_oob",
           "pub fn f(a: &[u8;13]) -> u8 { let mut s=0u8; for c in a.chunks(4) { s=s.wrapping_add(c[1]); } s }",
           f"fn main() {{ let a = {bb}([7u8;13]); {bb}(f({bb}(&a))); }}")
    # hunt-15 Class D: a provable obligation (`arr[a&7]` bounds) ALONGSIDE an unmodeled panicking
    # `o.unwrap()` must NOT read as fully proved — the unwrap panics on None at runtime. The fix
    # surfaces unwrap/expect as an Unknown obligation so the headline is honest. The over-credit
    # witness must be CORRECT_REJECT (not fully proved + runtime panic); the modeled match/`if let`
    # equivalent (no unwrap) must stay SOUND_PROOF.
    yield ("sr_unwrap_overcredit",
           "pub fn f(a: u8, arr: &[u8;8]) -> u8 { let s = arr[(a & 7) as usize]; "
           "let o: Option<u8> = std::hint::black_box(None); s.wrapping_add(o.unwrap()) }",
           f"fn main() {{ let arr = {bb}([7u8;8]); {bb}(f({bb}(0u8), {bb}(&arr))); }}")
    yield ("sr_unwrap_match_safe",
           "pub fn f(a: u8, arr: &[u8;8], o: Option<u8>) -> u8 { let s = arr[(a & 7) as usize]; "
           "match o { Some(v) => s.wrapping_add(v), None => s } }",
           f"fn main() {{ let arr = {bb}([7u8;8]); "
           f"let r = {bb}(f({bb}(0u8), {bb}(&arr), {bb}(Some(1u8)))); "
           f"std::process::exit((r != 8) as i32 & 0); }}")
    # hunt-15 Class C: an Option/Result payload bound learned on a by-value match binding
    # `if let Some(v)=o {{ if v<K ... }}` must NOT survive a payload mutation via o.as_mut() /
    # o.insert(b) / o.get_or_insert_with(||b) — both `v` and the later `match o {{Some(i)=>arr[i]}}`
    # lower to `copy ((o as Some).0)` (one shared payload symbol), so the stale `v<K` vacuously
    # discharged `arr[i]` on the mutated `i==b` (kernel-certified OOB). FIX = guards.rs Use arm
    # drops the payload-projection-read equality when the enum local is mutably borrowed. The OOB
    # variants must stay CORRECT_REJECT; the NON-mutated safe form must stay SOUND_PROOF.
    yield ("sr_option_asmut_payload_oob",
           "pub fn f(a: u8, b: u8) -> u8 { let arr=[0u8;100]; let mut o=Some(a); "
           "if let Some(v)=o { if v<50 { if let Some(r)=o.as_mut(){*r=b;} "
           "return match o { Some(i)=>arr[i as usize], None=>0 }; } } 0 }",
           f"fn main() {{ {bb}(f({bb}(10u8), {bb}(200u8))); }}")
    yield ("sr_option_insert_payload_oob",
           "pub fn f(a: usize, b: usize) -> u8 { let arr=[0u8;8]; let mut o=Some(a); "
           "if let Some(v)=o { if v<5 { o.insert(b); "
           "return match o { Some(i)=>arr[i], None=>0 }; } } 0 }",
           f"fn main() {{ {bb}(f({bb}(2usize), {bb}(100usize))); }}")
    yield ("sr_result_asmut_payload_oob",
           "pub fn f(a: usize, b: usize) -> u8 { let arr=[0u8;8]; let mut r: Result<usize,()>=Ok(a); "
           "if let Ok(v)=r { if (0..=4).contains(&v) { if let Ok(p)=r.as_mut(){*p=b;} "
           "return match r { Ok(i)=>arr[i], Err(_)=>0 }; } } 0 }",
           f"fn main() {{ {bb}(f({bb}(2usize), {bb}(100usize))); }}")
    yield ("sr_option_payload_guard_safe",
           "pub fn f(a: u8) -> u8 { let arr=[0u8;100]; let o=Some(a); "
           "if let Some(v)=o { if v<50 { return match o { Some(i)=>arr[i as usize], None=>0 }; } } 0 }",
           f"fn main() {{ let r={bb}(f({bb}(10u8))); std::process::exit((r!=0) as i32 & 0); }}")
    # hunt-15 Class A: a `vec![x; n]` (std::vec::from_elem) / `(0..n).collect()` capacity-overflow
    # obligation was SILENTLY DROPPED from the default headline — `method_tail` stripped only ONE
    # of the TWO trailing turbofishes on the byte-token-rendered free-fn callee
    # (`from_elem::<u8>::<__trust_elem_bytes_1>`), so the alloc recognizer saw `<u8>` not `from_elem`
    # and emitted NOTHING. A function with a provable op (`a as u32+1`) then reported FULLY PROVED
    # while the unbounded alloc panicked "capacity overflow". FIX = method_tail strips ALL trailing
    # turbofishes. The OOB-alloc witnesses must stay CORRECT_REJECT; a bounded alloc must stay
    # SOUND_PROOF (guard proves the count ceiling).
    yield ("sr_vec_from_elem_capov",
           "pub fn f(a: u8, n: usize) -> (u32, Vec<u8>) { (a as u32 + 1, vec![0u8; n]) }",
           f"fn main() {{ let (x, v) = f({bb}(0u8), {bb}(usize::MAX)); "
           f"{bb}(&x); {bb}(&v); }}")
    yield ("sr_vec_from_elem_u64_byte_overflow",
           "pub fn f(a: u8, n: usize) -> (u32, Vec<u64>) { (a as u32 + 1, vec![0u64; n]) }",
           f"fn main() {{ let (x, v) = f({bb}(0u8), {bb}(usize::MAX / 4)); "
           f"{bb}(&x); {bb}(&v); }}")
    yield ("sr_collect_range_capov",
           "pub fn f(a: u8, n: usize) -> (u32, Vec<usize>) { let v: Vec<usize> = (0..n).collect(); (a as u32 + 1, v) }",
           f"fn main() {{ let (x, v) = f({bb}(0u8), {bb}(usize::MAX / 4)); "
           f"{bb}(&x); {bb}(&v); }}")
    yield ("sr_vec_from_elem_bounded_safe",
           "pub fn f(n: usize) -> Vec<u8> { if n < 8 { vec![0u8; n] } else { Vec::new() } }",
           f"fn main() {{ let v = {bb}(f({bb}(4usize))); std::process::exit((v.len()!=4) as i32 & 0); }}")

    # ---- E3: FLOAT-ARITHMETIC VALUE obligations -------------------------------------
    # The FpAdd/FpSub/FpMul/FpDiv/FpNeg value facts (guards.rs `fp_arith_value_def` /
    # `fp_neg_value_def`) are currently UN-FUZZED. Floats never panic on overflow/÷0 in
    # Rust (they yield ±inf/NaN), so the soundness witness is not an arithmetic trap but a
    # DOWNSTREAM obligation whose discharge depends on the modeled float VALUE: a float
    # result cast to a usize INDEX. An UNMASKED `arr[(a OP b) as usize]` is OOB-capable
    # (the saturating `f64 as usize` reaches usize::MAX), so it must NEVER be proved — if a
    # wrong/over-strong fp fact ever discharged that bounds obligation it would be a
    # FALSE_PROOF (the float analogue of the i128 abstract-interp TOP bug). The MASKED
    # `... & (N-1)` form is genuinely in-bounds for EVERY float input, so its bounds
    # obligation must prove (the fp-value obligation itself stays Unknown — fail-closed —
    # so the function is not "fully proved", but the BOUNDS half must stay sound).
    fp_widths = ["f32", "f64"]
    for FT in fp_widths:
        big = "1e30f32" if FT == "f32" else "1e300f64"
        for opname, opsym in [("add", "+"), ("sub", "-"), ("mul", "*"), ("div", "/")]:
            # Unmasked float-result index — OOB-capable, must CORRECT_REJECT.
            yield (f"fp_{opname}_index_oob[{FT}]",
                   f"pub fn f(a: {FT}, b: {FT}, arr: &[u8; 4]) -> u8 {{ arr[(a {opsym} b) as usize] }}",
                   f"fn main() {{ let arr = {bb}([1u8,2,3,4]); "
                   f"let r = {bb}(f({bb}({big}), {bb}(2.0{FT}), {bb}(&arr))); "
                   f"std::process::exit((r != 0) as i32 & 0); }}")
        # Masked float-result index — always in [0,4), the bounds obligation must prove.
        # Worst-case `big` saturates the cast to usize::MAX, but the mask folds it to <4,
        # so the runtime is SAFE; this is the SOUND_PROOF / COMPLETENESS_GAP boundary for
        # the masked-after-fp-cast lane (a FALSE_PROOF is impossible here — it is in
        # bounds — but a regression turning the bounds proof unsound elsewhere shows up as
        # an OOB sibling above).
        yield (f"fp_masked_index_safe[{FT}]",
               f"pub fn f(a: {FT}, b: {FT}, arr: &[u8; 4]) -> u8 {{ arr[((a + b) as usize) & 3] }}",
               f"fn main() {{ let arr = {bb}([1u8,2,3,4]); "
               f"let r = {bb}(f({bb}({big}), {bb}(2.0{FT}), {bb}(&arr))); "
               f"std::process::exit((r != 0) as i32 & 0); }}")
        # FpNeg into an unmasked index — negation is EXACT, but the magnitude is unbounded,
        # so the index is still OOB-capable: must CORRECT_REJECT (a wrong FpNeg fact that
        # claimed the result bounded would be a FALSE_PROOF).
        yield (f"fp_neg_index_oob[{FT}]",
               f"pub fn f(a: {FT}, arr: &[u8; 4]) -> u8 {{ let n = -a; arr[n as usize] }}",
               f"fn main() {{ let arr = {bb}([1u8,2,3,4]); "
               f"let r = {bb}(f({bb}(-{big}), {bb}(&arr))); "
               f"std::process::exit((r != 0) as i32 & 0); }}")

    # ---- E3: OPAQUE-PATH stubs — dyn-dispatch / async / atomic ----------------------
    # These paths must stay OPAQUE: Trust cannot see through a virtual call, an atomic
    # load, or a poll-driven async resumption, so a value coming OUT of one is unknown and
    # any overflow-capable use of it must FAIL CLOSED (stay Unknown / runtime-checked,
    # never proved). The witness: an opaque value `v` feeds `v + 1`; the worst-case driver
    # supplies an impl/atomic/future that yields T::MAX, so the runtime overflows. Correct
    # behavior is CORRECT_REJECT (not proved + overflow). A regression that VACUOUSLY
    # PROVES the opaque value (e.g. modeling a `&dyn T` method as total/bounded, or reading
    # an atomic load as a constant 0) flips it to FALSE_PROOF — these stubs are the
    # tripwire for exactly that "never vacuously proved" property.
    # dyn dispatch: a trait-object method result + 1.
    yield ("opaque_dyn_add[u8]",
           "pub trait T { fn g(&self, x: u8) -> u8; }\n"
           "pub fn f(t: &dyn T, x: u8) -> u8 { t.g(x) + 1 }",
           "struct Mx; impl T for Mx { fn g(&self, _x: u8) -> u8 { u8::MAX } }\n"
           f"fn main() {{ let m = Mx; let t: &dyn T = {bb}(&m); "
           f"let r = {bb}(f(t, {bb}(0u8))); std::process::exit((r != 0) as i32 & 0); }}")
    # atomic load: the loaded value is opaque (another thread can store anything) + 1.
    # The runtime driver uses fully-qualified paths (NOT a second `use`) so it does not
    # re-import the lib's `AtomicU8`/`Ordering` (a duplicate `use` is a compile error,
    # which would make the runtime oracle INCONCLUSIVE rather than a real witness).
    yield ("opaque_atomic_load_add[u8]",
           "use std::sync::atomic::{AtomicU8, Ordering};\n"
           "pub fn f(a: &AtomicU8) -> u8 { a.load(Ordering::SeqCst) + 1 }",
           f"fn main() {{ let a = std::sync::atomic::AtomicU8::new({bb}(u8::MAX)); "
           f"let r = {bb}(f({bb}(&a))); std::process::exit((r != 0) as i32 & 0); }}")
    yield ("opaque_atomic_fetch_add[u8]",
           "use std::sync::atomic::{AtomicU8, Ordering};\n"
           "pub fn f(a: &AtomicU8, d: u8) -> u8 { a.fetch_add(d, Ordering::SeqCst) + 1 }",
           f"fn main() {{ let a = std::sync::atomic::AtomicU8::new({bb}(u8::MAX)); "
           f"let r = {bb}(f({bb}(&a), {bb}(0u8))); "
           f"let _ = a.load(std::sync::atomic::Ordering::SeqCst); "
           f"std::process::exit((r != 0) as i32 & 0); }}")
    # async: the awaited result is opaque (resumption value) + 1; a minimal hand-rolled
    # block_on polls it to completion (no external executor dependency).
    block_on = (
        "fn block_on<F: std::future::Future>(mut fut: F) -> F::Output {\n"
        "    use std::task::{Context, Poll, RawWaker, RawWakerVTable, Waker};\n"
        "    fn nop(_: *const ()) {}\n"
        "    fn clone(_: *const ()) -> RawWaker { RawWaker::new(std::ptr::null(), &VT) }\n"
        "    static VT: RawWakerVTable = RawWakerVTable::new(clone, nop, nop, nop);\n"
        "    let w = unsafe { Waker::from_raw(RawWaker::new(std::ptr::null(), &VT)) };\n"
        "    let mut cx = Context::from_waker(&w);\n"
        "    let mut fut = unsafe { std::pin::Pin::new_unchecked(&mut fut) };\n"
        "    loop { if let Poll::Ready(v) = fut.as_mut().poll(&mut cx) { return v; } }\n"
        "}")
    yield ("opaque_async_add[u8]",
           "pub async fn f(x: u8) -> u8 { x + 1 }",
           block_on + "\n"
           f"fn main() {{ let r = {bb}(block_on(f({bb}(u8::MAX)))); "
           f"std::process::exit((r != 0) as i32 & 0); }}")

    # ---- Trust: piece #13 — SAFE-ASYNC data-safety families -------------------------
    # Piece #13 makes a coroutine RESUME body (post-StateTransform) reachable to the
    # verifier: the classifier no longer fast-rejects `async fn`, `ty_convert` models the
    # frame as an opaque `Ty::Coroutine`, and the aggregate/SetDiscriminant/frame-field
    # reads are obligation-free/havoc'd. The overriding property these families pin is
    # UNCHANGED: NO coroutine body may be VACUOUSLY PROVED. A zero-await body's parameter
    # arithmetic is now a REAL obligation (proved-or-refuted by ay), and every across-await
    # / resume-value read is HAVOC'D (opaque frame), so a value from a future / held across
    # a suspend must never discharge an overflow/index bound. A regression that concretized
    # a frame read (e.g. modeled a resume value as 0, or kept a stale pre-suspend guard)
    # flips one of these to FALSE_PROOF — the exact soundness tripwire.
    #
    # async_no_await_overflow: a ZERO-AWAIT overflowing body. The param `x` is read from
    # the frame as an unconstrained u8, so `x + 1` overflows at 255 → CORRECT_REJECT
    # (not proved + runtime panic). A regression proving it is a FALSE_PROOF.
    yield ("async_no_await_overflow[u8]",
           "pub async fn f(x: u8) -> u8 { x.wrapping_mul(1) + 1 }",
           block_on + "\n"
           f"fn main() {{ let r = {bb}(block_on(f({bb}(u8::MAX)))); "
           f"std::process::exit((r != 0) as i32 & 0); }}")
    # async_resume_value_add: the awaited resumption value is OPAQUE (an unmodeled
    # `Future::poll` result); `poll().await + 1` overflows for a future that resumes with
    # u8::MAX → CORRECT_REJECT. Modeling the resume value as bounded/constant would
    # FALSE_PROVE. (E3 opaque-path property extended to the async resume value.)
    yield ("async_resume_value_add[u8]",
           "async fn poll_val(v: u8) -> u8 { v }\n"
           "pub async fn f(v: u8) -> u8 { poll_val(v).await + 1 }",
           block_on + "\n"
           f"fn main() {{ let r = {bb}(block_on(f({bb}(u8::MAX)))); "
           f"std::process::exit((r != 0) as i32 & 0); }}")
    # async_across_await_index: a guard on `i` is established, then an `.await` intervenes
    # whose callee reseats `i` through a `&mut` handed across the suspend; the post-await
    # `a[i]` MUST fail closed — the frame field `i` is havoc'd across the suspend, so the
    # stale pre-suspend `i < 8` guard cannot discharge the bound. The driver reseats i to
    # 100 → runtime OOB panic → CORRECT_REJECT. A regression keeping the stale guard is a
    # FALSE_PROOF (the make-or-break across-await staleness trap).
    yield ("async_across_await_index[u8]",
           "async fn reseat(i: &mut usize) { *i = 100; }\n"
           "pub async fn f(a: &[u8; 8]) -> u8 {\n"
           "    let mut i = 0usize;\n"
           "    if i < 8 { reseat(&mut i).await; a[i] } else { 0 }\n"
           "}",
           block_on + "\n"
           f"fn main() {{ let arr = {bb}([1u8; 8]); "
           f"let r = {bb}(block_on(f({bb}(&arr)))); "
           f"std::process::exit((r != 0) as i32 & 0); }}")

    # Trust: piece #13 step-2 — a SAFE ZERO-AWAIT body now COMPILES GREEN (rc=0) and
    # its REAL arithmetic obligation is PROVED by ay. The native trust-ir-bridge lane
    # models the coroutine frame (opaque Undef), the state discriminant (havoc'd), and
    # the resume-state protocol asserts (executor-protocol Assume, a non-fatal
    # Termination coverage gap). `(x as u16) + 1` cannot overflow for any u8 x (max
    # 256 < 65536) → the body obligation proves (1p) and the program runs OK. NOTE the
    # fuzzer classifies this COMPLETENESS_GAP, NOT SOUND_PROOF, ONLY because its
    # `fully_proved` predicate requires 0 unknown and the two ResumedAfter* protocol
    # asserts stay `[termination] unknown` (the non-fatal gap that keeps the BUILD
    # rc=0). This is the honest, sound state — NOT a false proof (`1p/0f/2u`, never
    # `Np/0f/0u`). The load-bearing property is FALSE_PROOF=0 / FALSE_PROOF_FULL=0:
    # a regression that concretized the frame read or over-pruned would flip one of
    # the CORRECT_REJECT families above to FALSE_PROOF.
    yield ("async_no_await_safe_widen[u8]",
           "pub async fn f(x: u8) -> u16 { (x as u16) + 1 }",
           block_on + "\n"
           f"fn main() {{ let r = {bb}(block_on(f({bb}(u8::MAX)))); "
           f"std::process::exit((r != 256) as i32 & 0); }}")
    # A safe zero-await BOUNDED index: `a[x % 4]` over a `[u8; 4]` is always in
    # bounds → the index obligation proves (1p), runs OK, BUILD rc=0 (COMPLETENESS_GAP
    # in the fuzzer's 0-unknown sense, as above). A regression concretizing the frame
    # read `x` or the index would refute (completeness) or, worse, false-prove an OOB
    # sibling (caught by the unsafe CORRECT_REJECT families).
    yield ("async_no_await_safe_index[u8]",
           "pub async fn f(a: [u8; 4], x: u8) -> u8 { a[(x % 4) as usize] }",
           block_on + "\n"
           f"fn main() {{ let r = {bb}(block_on(f({bb}([7u8;4]), {bb}(u8::MAX)))); "
           f"std::process::exit((r != 7) as i32 & 0); }}")

    # ---- Trust: piece #7a/7b — CONST-GENERIC ARRAY index families ----------------
    # A `[u8; N]` with N a const-generic param gets a MODELED symbolic length. A
    # bound-checked index `if i < N { a[i] }` must PROVE (SOUND_PROOF); every
    # unguarded / off-by-one / wrong-param index must NOT prove (CORRECT_REJECT —
    # the runtime driver panics on an out-of-bounds `i`). The wrong-param family is
    # the fuzzed generalization of the M==N collision (INV-1): it must NEVER be a
    # FALSE_PROOF.
    cg_ns = [4, 16, 64]
    for N in cg_ns:
        # cg_guarded: SAFE — i<N guard discharges. SOUND_PROOF target.
        yield (f"cg_guarded[N={N}]",
               "pub fn f<const N: usize>(a: [u8; N], i: usize) -> u8 "
               "{ if i < N { a[i] } else { 0 } }",
               f"fn main() {{ let a = {bb}([1u8; {N}]); "
               f"let r = {bb}(f::<{N}>({bb}(a), {bb}({N} - 1))); "
               f"std::process::exit((r != 0) as i32 & 0); }}")
        # cg_repeat_guarded (7b): SAFE internally-built [x;N]. SOUND_PROOF target.
        yield (f"cg_repeat_guarded[N={N}]",
               "pub fn f<const N: usize>(i: usize) -> u8 "
               "{ let a = [0u8; N]; if i < N { a[i] } else { 0 } }",
               f"fn main() {{ let r = {bb}(f::<{N}>({bb}({N} - 1))); "
               f"std::process::exit((r != 0) as i32 & 0); }}")
        # cg_unguarded: UNSAFE — driver passes i==N (OOB). CORRECT_REJECT.
        yield (f"cg_unguarded[N={N}]",
               "pub fn f<const N: usize>(a: [u8; N], i: usize) -> u8 { a[i] }",
               f"fn main() {{ let a = {bb}([1u8; {N}]); "
               f"let r = {bb}(f::<{N}>({bb}(a), {bb}({N}))); "
               f"std::process::exit((r != 0) as i32 & 0); }}")
        # cg_off_by_one: UNSAFE — i<=N admits i==N (OOB). driver passes i==N.
        yield (f"cg_off_by_one[N={N}]",
               "pub fn f<const N: usize>(a: [u8; N], i: usize) -> u8 "
               "{ if i <= N { a[i] } else { 0 } }",
               f"fn main() {{ let a = {bb}([1u8; {N}]); "
               f"let r = {bb}(f::<{N}>({bb}(a), {bb}({N}))); "
               f"std::process::exit((r != 0) as i32 & 0); }}")
        # cg_repeat_unguarded (7b): UNSAFE — driver passes i==N (OOB).
        yield (f"cg_repeat_unguarded[N={N}]",
               "pub fn f<const N: usize>(i: usize) -> u8 "
               "{ let a = [0u8; N]; a[i] }",
               f"fn main() {{ let r = {bb}(f::<{N}>({bb}({N}))); "
               f"std::process::exit((r != 0) as i32 & 0); }}")

    # cg_wrong_param — the fuzzed M==N NON-conflation (INV-1). Index `[u8; M]`
    # under a bound on a DIFFERENT param N. With M < N and M <= i < N it is OOB.
    # The driver picks M<N and i in [M, N) so the runtime PANICS -> must be
    # CORRECT_REJECT (a FALSE_PROOF here is the exact collision the piece prevents).
    for M, N in [(4, 16), (8, 64), (2, 4)]:
        yield (f"cg_wrong_param[M={M},N={N}]",
               "pub fn f<const M: usize, const N: usize>(a: [u8; M], i: usize) -> u8 "
               "{ if i < N { a[i] } else { 0 } }",
               f"fn main() {{ let a = {bb}([1u8; {M}]); "
               f"let r = {bb}(f::<{M}, {N}>({bb}(a), {bb}({M}))); "
               f"std::process::exit((r != 0) as i32 & 0); }}")

    # ---- Trust: piece #7c — owned-Vec SCALAR index families (STALENESS) ----------
    # A `usize`-scalar index `v[i]` on a `Vec` now emits a `SliceBoundsCheck` VC
    # against the container's ABSTRACT length. This is the callarg-mut-staleness /
    # w0z family (Vec length CHANGES, unlike an array), so the LOAD-BEARING invariant
    # is FALSE_PROOF=0 AND FALSE_PROOF_FULL=0: a guarded `if i < v.len() { v[i] }`
    # must be SOUND_PROOF; every unguarded / stale-after-mutation index must NOT be
    # statically proved (the runtime driver drives the OOB, so it is CORRECT_REJECT).
    # A ghost length that survived a mutation channel (mem::swap / setter / &mut
    # escape) and still proved the OOB would be a FALSE_PROOF — the exact bug the
    # havoc discipline prevents.
    vec_lens = [4, 16, 64]
    for L in vec_lens:
        # vec_lenchecked: SAFE — `if i < v.len()` guard discharges. SOUND_PROOF.
        yield (f"vec_lenchecked[L={L}]",
               "pub fn f(v: &Vec<u8>, i: usize) -> u8 "
               "{ if i < v.len() { v[i] } else { 0 } }",
               f"fn main() {{ let v = {bb}(vec![1u8; {L}]); "
               f"let r = {bb}(f({bb}(&v), {bb}({L} - 1))); "
               f"std::process::exit((r != 0) as i32 & 0); }}")
        # vec_unguarded: UNSAFE — driver passes i==L (OOB). CORRECT_REJECT.
        yield (f"vec_unguarded[L={L}]",
               "pub fn f(v: &Vec<u8>, i: usize) -> u8 { v[i] }",
               f"fn main() {{ let v = {bb}(vec![1u8; {L}]); "
               f"let r = {bb}(f({bb}(&v), {bb}({L}))); "
               f"std::process::exit((r != 0) as i32 & 0); }}")
        # vec_off_by_one: UNSAFE — `i <= len` admits i==len (OOB). driver passes i==L.
        yield (f"vec_off_by_one[L={L}]",
               "pub fn f(v: &Vec<u8>, i: usize) -> u8 "
               "{ if i <= v.len() { v[i] } else { 0 } }",
               f"fn main() {{ let v = {bb}(vec![1u8; {L}]); "
               f"let r = {bb}(f({bb}(&v), {bb}({L}))); "
               f"std::process::exit((r != 0) as i32 & 0); }}")
        # vec_swap_stale: UNSAFE HAVOC — build a full `v`, then `mem::swap` it with an
        # EMPTY `w`; `v` is now empty, so ANY index panics. The `i` was "valid" for the
        # OLD length but the swap HAVOCed it. Must NOT statically prove (CORRECT_REJECT).
        # A FALSE_PROOF here is the callarg-mut-staleness bug.
        yield (f"vec_swap_stale[L={L}]",
               "pub fn f(i: usize) -> u8 "
               f"{{ let mut v = vec![1u8; {L}]; let mut w: Vec<u8> = Vec::new(); "
               "std::mem::swap(&mut v, &mut w); v[i] }",
               f"fn main() {{ let r = {bb}(f({bb}(0))); "
               f"std::process::exit((r != 0) as i32 & 0); }}")
        # vec_setter_stale: UNSAFE HAVOC — a non-whitelisted `&mut v` setter call
        # (`clear_all`) empties `v`; a later `v[i]` is stale. Must NOT prove.
        yield (f"vec_setter_stale[L={L}]",
               "fn clear_all(x: &mut Vec<u8>) { x.clear(); } "
               "pub fn f(i: usize) -> u8 "
               f"{{ let mut v = vec![1u8; {L}]; clear_all(&mut v); v[i] }}",
               f"fn main() {{ let r = {bb}(f({bb}(0))); "
               f"std::process::exit((r != 0) as i32 & 0); }}")

    # vec_escape_stale — an opaque `&mut v` escape (a fn-POINTER the callee may use to
    # empty `v`) HAVOCs the length; a later `v[i]` must NOT prove (CORRECT_REJECT).
    for L in [4, 16]:
        yield (f"vec_escape_stale[L={L}]",
               "pub fn f(shrink: fn(&mut Vec<u8>), i: usize) -> u8 "
               f"{{ let mut v = vec![1u8; {L}]; shrink(&mut v); v[i] }}",
               f"fn main() {{ fn s(x: &mut Vec<u8>) {{ x.clear(); }} "
               f"let r = {bb}(f({bb}(s as fn(&mut Vec<u8>)), {bb}(0))); "
               f"std::process::exit((r != 0) as i32 & 0); }}")

    # ---- Trust R2: corpus false-refutation families ---------------------------------
    # family 2 (get-Some index bound): `slice.get(idx) == Some` implies
    # `idx < len <= isize::MAX`, so the get-guarded `idx += 1` PROVES (bitflags
    # `IterNames::next`, semver `numeric_identifier`). The soundness tripwires: a
    # reseat of the index inside the Some arm, a cross-slice index, and the
    # off-by-one `flags[idx + 1]` must all stay NOT-proved (drivers panic →
    # CORRECT_REJECT). A FALSE_PROOF here is the get-contract fact surviving a
    # staleness channel.
    yield ("r2get_field_increment_safe",
           "pub struct It { flags: &'static [u32], idx: usize }\n"
           "impl It { pub fn new(f: &'static [u32]) -> It { It { flags: f, idx: 0 } } }\n"
           "impl Iterator for It { type Item = u32;\n"
           "  fn next(&mut self) -> Option<u32> {\n"
           "    while let Some(f) = self.flags.get(self.idx) {\n"
           "      self.idx += 1;\n"
           "      if *f != 0 { return Some(*f); }\n"
           "    }\n"
           "    None\n"
           "  }\n"
           "}",
           "static FLAGS: [u32; 3] = [1, 0, 2];\n"
           f"fn main() {{ let mut it = It::new({bb}(&FLAGS)); "
           f"let mut acc = 0u32; while let Some(v) = it.next() {{ acc = acc.wrapping_add({bb}(v)); }} "
           f"std::process::exit((acc == 0) as i32 & 0); }}")
    # NOTE: the full while-let scan LOOP over a plain local (`while let Some(&d) =
    # input.get(len) { len += 1 }`, the literal semver `numeric_identifier` shape)
    # trips a PRE-EXISTING ay grind (hangs on the pristine tip baseline too — the
    # F2-class budget escape), so the family pins the straight-line get-Some tie
    # on a plain local instead; the loop staleness channels are covered by
    # r2get_field_increment_safe / r2get_reseat_max_overflow.
    yield ("r2get_local_increment_safe",
           "pub fn scan_step(input: &[u8], len: usize) -> usize {\n"
           "  if let Some(_d) = input.get(len) { len + 1 } else { len }\n"
           "}",
           f"fn main() {{ let r = {bb}(scan_step({bb}(b\"12345\"), {bb}(0))); "
           f"std::process::exit((r != 1) as i32 & 0); }}")
    yield ("r2get_reseat_max_overflow",
           "pub struct It { flags: &'static [u32], idx: usize }\n"
           "impl It { pub fn new(f: &'static [u32]) -> It { It { flags: f, idx: 0 } }\n"
           "  pub fn poisoned(&mut self) -> usize {\n"
           "    while let Some(_f) = self.flags.get(self.idx) {\n"
           "      self.idx = usize::MAX;\n"
           "      let x = self.idx + 1;\n"
           "      return x;\n"
           "    }\n"
           "    0\n"
           "  }\n"
           "}",
           "static FLAGS: [u32; 3] = [1, 0, 2];\n"
           f"fn main() {{ let mut it = It::new({bb}(&FLAGS)); "
           f"let r = {bb}(it.poisoned()); "
           f"std::process::exit((r != 0) as i32 & 0); }}")
    yield ("r2get_cross_slice_oob",
           "pub fn f(a: &[u32], b: &[u32], i: usize) -> u32 {\n"
           "  if let Some(_) = a.get(i) { return b[i]; }\n"
           "  0\n"
           "}",
           f"fn main() {{ let a = {bb}([1u32, 2, 3]); let b: [u32; 0] = []; "
           f"let r = {bb}(f({bb}(&a), {bb}(&b), {bb}(0))); "
           f"std::process::exit((r != 0) as i32 & 0); }}")
    yield ("r2get_offbyone_index_oob",
           "pub fn f(a: &[u32], i: usize) -> u32 {\n"
           "  if let Some(_) = a.get(i) { return a[i + 1]; }\n"
           "  0\n"
           "}",
           f"fn main() {{ let a = {bb}([7u32]); "
           f"let r = {bb}(f({bb}(&a), {bb}(0))); "
           f"std::process::exit((r != 0) as i32 & 0); }}")
    # family 1 (CharIndices yields): `&s[i..]` / `&s[..i]` at a `char_indices()`-
    # yielded `i` is panic-free (bounds AND char boundary, by contract) — the heck
    # `capitalize` idiom PROVES. Tripwires: a DERIVED `i + 1` (may fall mid-char),
    # a cross-string slice, and a `mem::swap`-re-seated iterator must all stay
    # NOT-proved (drivers panic on non-boundary/OOB → CORRECT_REJECT). A
    # FALSE_PROOF here means the structural fold credited a non-yield index.
    yield ("r2ci_tail_safe",
           "pub fn tail(s: &str) -> &str {\n"
           "  let mut ci = s.char_indices();\n"
           "  if let Some((_, _c)) = ci.next() {\n"
           "    if let Some((i, _)) = ci.next() { return &s[i..]; }\n"
           "  }\n"
           "  \"\"\n"
           "}",
           f"fn main() {{ let r = {bb}(tail({bb}(\"h\\u{{e9}}llo\"))); "
           f"std::process::exit((r.len() == 0) as i32 & 0); }}")
    yield ("r2ci_head_safe",
           "pub fn head(s: &str) -> &str {\n"
           "  let mut ci = s.char_indices();\n"
           "  if let Some((_, _c)) = ci.next() {\n"
           "    if let Some((i, _)) = ci.next() { return &s[..i]; }\n"
           "  }\n"
           "  \"\"\n"
           "}",
           f"fn main() {{ let r = {bb}(head({bb}(\"\\u{{e9}}llo\"))); "
           f"std::process::exit((r.len() == 0) as i32 & 0); }}")
    yield ("r2ci_plus_one_boundary_panic",
           "pub fn f(s: &str) -> &str {\n"
           "  let mut ci = s.char_indices();\n"
           "  if let Some((_, _c)) = ci.next() {\n"
           "    if let Some((i, _)) = ci.next() { return &s[i + 1..]; }\n"
           "  }\n"
           "  \"\"\n"
           "}",
           f"fn main() {{ let r = {bb}(f({bb}(\"a\\u{{e9}}x\"))); "
           f"std::process::exit((r.len() == 0) as i32 & 0); }}")
    yield ("r2ci_cross_string_oob",
           "pub fn f<'a>(s: &str, t: &'a str) -> &'a str {\n"
           "  let mut ci = s.char_indices();\n"
           "  if let Some((_, _c)) = ci.next() {\n"
           "    if let Some((i, _)) = ci.next() { return &t[i..]; }\n"
           "  }\n"
           "  \"\"\n"
           "}",
           f"fn main() {{ let r = {bb}(f({bb}(\"hello\"), {bb}(\"\"))); "
           f"std::process::exit((r.len() == 0) as i32 & 0); }}")
    yield ("r2ci_swap_reseat_panic",
           "pub fn f<'a>(s: &'a str, t: &str) -> &'a str {\n"
           "  let mut ci = s.char_indices();\n"
           "  let mut cj = t.char_indices();\n"
           "  let _ = ci.next();\n"
           "  std::mem::swap(&mut ci, &mut cj);\n"
           "  let _ = ci.next();\n"
           "  if let Some((i, _)) = ci.next() { return &s[i..]; }\n"
           "  \"\"\n"
           "}",
           f"fn main() {{ let r = {bb}(f({bb}(\"\\u{{e9}}\"), {bb}(\"abc\"))); "
           f"std::process::exit((r.len() == 0) as i32 & 0); }}")

    # ---- Trust: UNMODELED-PANICKING-CALL family (absent-callee fail-closed) -------
    # A call to a std method the native bridge does NOT model as total (`u32::pow`,
    # `checked_add(...).unwrap()`, `u8::abs_diff`-then-index, …) whose panic-freedom
    # the native lane CANNOT establish. The bridge lowers it fail-soft: an
    # `Assert(false)+NoPanic` marker keeps the panic REACHABLE plus one honest
    # `PanicFreedom` obligation marked `ABSENT_CALLEE_ASSUMPTION_PREFIX`. That
    # obligation is Unknown by construction and MUST fail closed — an unproven panic
    # path is a build error (revert of d8a9bbc28e/d848dcad97 fail-open). The driver
    # supplies the panicking input so the program panics at runtime (rc=101), so
    # the ONLY correct outcome is CORRECT_REJECT (not proved + panics). A regression
    # that re-opens the fail-soft-to-non-fatal hole flips these to FALSE_PROOF /
    # FALSE_PROOF_FULL — the exact soundness bug this family guards.
    #
    # `mixed_pow`: the falsification-gate mutant shape — a PROVABLE `(a as u32)+1`
    # alongside the panicking `x.pow(20)`. The sibling arithmetic proves, but the
    # pow panic obligation must keep the whole function fail-closed.
    yield ("panic_call_mixed_pow[u8]",
           "pub fn f(a: u8) -> u32 { let x = (a as u32) + 1; x.pow(20) }",
           f"fn main() {{ let r = {bb}(f({bb}(255u8))); "
           f"std::process::exit((r != 0) as i32 & 0); }}")
    # `bare_pow`: the panicking call with no sibling obligation.
    yield ("panic_call_bare_pow[u32]",
           "pub fn f(a: u32) -> u32 { a.pow(20) }",
           f"fn main() {{ let r = {bb}(f({bb}(1000u32))); "
           f"std::process::exit((r != 0) as i32 & 0); }}")
    # `unwrap_none`: `Option::unwrap` on a `None` — an unmodeled panicking call that
    # ALWAYS panics; the honest absent-callee obligation must fail closed.
    yield ("panic_call_unwrap_none[u32]",
           "pub fn f(a: u32) -> u32 { let o: Option<u32> = if a > u32::MAX { Some(a) } else { None }; o.unwrap() }",
           f"fn main() {{ let r = {bb}(f({bb}(5u32))); "
           f"std::process::exit((r != 0) as i32 & 0); }}")
    # `expect_none`: the `expect` twin — same fail-closed obligation.
    yield ("panic_call_expect_none[u32]",
           "pub fn f(a: u32) -> u32 { let o: Option<u32> = if a > u32::MAX { Some(a) } else { None }; o.expect(\"none\") }",
           f"fn main() {{ let r = {bb}(f({bb}(7u32))); "
           f"std::process::exit((r != 0) as i32 & 0); }}")

    # ---- Trust: MASK-TO-TYPE-MAX family (unconditional masked-value bound) --------
    # `v & (2^k − 1)` lies in `[0, 2^k − 1]` for ANY `v` (the AND clears every bit
    # ≥ k). Two completeness wins the trust-certify `bv_mask_shift_rewrites` group
    # (e) unconditional bound closes:
    #   (a) a type-max CAST `(x & 0xFF) as u8` — the masked value provably fits the
    #       narrower type (SOUND_PROOF: safe, runs clean, must be fully proved);
    #   (b) a masked INDEX `arr[i & (LEN − 1)]` over a LEN-sized array where LEN is a
    #       power of two — the masked index is always `< LEN` (SOUND_PROOF).
    # BOTH forms are exercised with a LITERAL mask AND the `(1 << k) − 1` chained
    # mask so the value-resolver (`mask_const_value`) path is covered. The SOUNDNESS
    # twin — a mask window WIDER than the array (`i & 0xFF` over a len-100 array) —
    # is genuinely OOB and MUST stay CORRECT_REJECT (the bound `idx ≤ 255` is
    # SAT-compatible with `idx ≥ 100`, so no false proof). A regression that emits
    # the mask bound UNGATED (any mask, or a non-window mask) would flip the OOB
    # twin to FALSE_PROOF — the exact soundness risk this family guards.
    mask_windows = [(8, "0xFF", "u8", 256), (16, "0xFFFF", "u16", 65536)]
    for k, lit, target, span in mask_windows:
        # (a) type-max cast, literal mask — SAFE, must prove.
        yield (f"mask_cast_lit[{target}]",
               f"pub fn f(x: u32) -> {target} {{ (x & {lit}) as {target} }}",
               f"fn main() {{ let r = {bb}(f({bb}(u32::MAX))); "
               f"std::process::exit((r != 0) as i32 & 0); }}")
        # (a') type-max cast, CHAINED `(1u32<<k)-1` mask — SAFE, must prove.
        yield (f"mask_cast_chain[{target}]",
               f"pub fn f(x: u32) -> {target} {{ let m = (1u32 << {k}) - 1; (x & m) as {target} }}",
               f"fn main() {{ let r = {bb}(f({bb}(u32::MAX))); "
               f"std::process::exit((r != 0) as i32 & 0); }}")
    # (b) masked index over a power-of-two array, literal mask — SAFE, must prove.
    for k, lit, alen in [(4, "0xF", 16), (8, "0xFF", 256)]:
        yield (f"mask_index_safe[len={alen}]",
               f"pub fn f(a: &[i32; {alen}], i: usize) -> i32 {{ a[i & {lit}] }}",
               f"fn main() {{ let a = {bb}([0i32; {alen}]); "
               f"let r = {bb}(f({bb}(&a), {bb}(usize::MAX))); "
               f"std::process::exit((r != 0) as i32 & 0); }}")
        # (b') masked index, CHAINED mask — SAFE, must prove.
        yield (f"mask_index_chain[len={alen}]",
               f"pub fn f(a: &[i32; {alen}], i: usize) -> i32 {{ let m = (1usize << {k}) - 1; a[i & m] }}",
               f"fn main() {{ let a = {bb}([0i32; {alen}]); "
               f"let r = {bb}(f({bb}(&a), {bb}(usize::MAX))); "
               f"std::process::exit((r != 0) as i32 & 0); }}")
    # SOUNDNESS twin: mask WINDOW wider than the array — genuinely OOB, must NOT
    # prove and DOES panic at runtime (CORRECT_REJECT). Never a FALSE_PROOF.
    for k, lit, alen in [(8, "0xFF", 100), (9, "0x1FF", 300)]:
        yield (f"mask_index_oob[mask={lit},len={alen}]",
               f"pub fn f(a: &[i32; {alen}], i: usize) -> i32 {{ a[i & {lit}] }}",
               f"fn main() {{ let a = {bb}([0i32; {alen}]); "
               f"let r = {bb}(f({bb}(&a), {bb}(usize::MAX))); "
               f"std::process::exit((r != 0) as i32 & 0); }}")

    # Family R3 (sr_genalias_*): PRE-MONOMORPHIZATION ALIAS generics — the corpus's
    # serde-derive-shaped cluster (`I::Item` / `S::Item` / `T::Out` are param-bearing
    # projection aliases). R3 relaxes the alias DECLARATION stamp and lowers the
    # marker to an opaque zero-field struct so T-INDEPENDENT obligations get real
    # verdicts. These twins pin the soundness boundary: a T-dependent fact treated
    # as T-independent (havoc'd trait-call result, size_of::<T>, default-body
    # bundling) must NEVER prove, while the guarded T-independent twins are safe
    # at runtime.
    # (a) guarded generic index, DIRECT xs[i] — SAFE (the W1 shape; proves post-R3).
    yield ("sr_genalias_pick_direct_safe",
           "pub fn f<I: Iterator>(xs: &[I::Item], i: usize) -> Option<&I::Item> { "
           "if i < xs.len() { Some(&xs[i]) } else { None } }",
           f"fn main() {{ let v = {bb}(vec![1u8, 2, 3]); "
           f"let r = {bb}(f::<std::vec::IntoIter<u8>>({bb}(&v), {bb}(1usize)).is_some()); "
           f"std::process::exit((r as i32) & 0); }}")
    # (b) off-by-one OOB twin under the same guard — panics at i = len-1.
    yield ("sr_genalias_pick_oob",
           "pub fn f<I: Iterator>(xs: &[I::Item], i: usize) -> Option<&I::Item> { "
           "if i < xs.len() { Some(&xs[i + 1]) } else { None } }",
           f"fn main() {{ let v = {bb}(vec![1u8, 2, 3]); "
           f"let r = {bb}(f::<std::vec::IntoIter<u8>>({bb}(&v), {bb}(2usize)).is_some()); "
           f"std::process::exit((r as i32) & 0); }}")
    # (c) guarded arith beside an opaque alias payload — SAFE (the W2 shape).
    yield ("sr_genalias_shift_safe",
           "pub trait Src { type Item; } pub struct S8; impl Src for S8 { type Item = u8; } "
           "pub fn f<S: Src>(p: Option<S::Item>, k: u32) -> (Option<S::Item>, u32) { "
           "let b = if k < 1000 { k + 1 } else { 0 }; (p, b) }",
           f"fn main() {{ let r = {bb}(f::<S8>({bb}(Some(3u8)), {bb}(999u32))); "
           f"std::process::exit((r.1 != 1000) as i32 & 0); }}")
    # (d) UNGUARDED arith twin — overflows at u32::MAX for every S.
    yield ("sr_genalias_shift_overflow",
           "pub trait Src { type Item; } pub struct S8; impl Src for S8 { type Item = u8; } "
           "pub fn f<S: Src>(p: Option<S::Item>, k: u32) -> (Option<S::Item>, u32) { (p, k + 1) }",
           f"fn main() {{ let r = {bb}(f::<S8>({bb}(Some(3u8)), {bb}(u32::MAX))); "
           f"std::process::exit((r.1 != 0) as i32 & 0); }}")
    # (e) T-method result feeding an index — havoc'd; panics with Item=usize 100.
    yield ("sr_genalias_tfeed_oob",
           "pub trait Feed { type Item: Into<usize> + Copy; } "
           "pub struct FBig; impl Feed for FBig { type Item = usize; } "
           "pub fn f<S: Feed>(xs: &[u8; 4], it: S::Item) -> u8 { xs[it.into()] }",
           f"fn main() {{ let r = {bb}(f::<FBig>({bb}(&[9u8; 4]), {bb}(100usize))); "
           f"std::process::exit((r != 9) as i32 & 0); }}")
    # (f) size_of::<T>() feeding an index — layout-dependent; panics for T=[u64;16].
    yield ("sr_genalias_sizeof_oob",
           "pub fn f<T>(xs: &[u8; 64]) -> u8 { xs[core::mem::size_of::<T>()] }",
           f"fn main() {{ let r = {bb}(f::<[u64; 16]>({bb}(&[7u8; 64]))); "
           f"std::process::exit((r != 7) as i32 & 0); }}")
    # (g) where-clause-PINNED assoc arithmetic — overflows at u32::MAX (T4: refuted
    # if MIR spells u32, unknown if it spells the alias — NEVER proved).
    yield ("sr_genalias_pinned_overflow",
           "pub trait W { type Out; } pub struct W32; impl W for W32 { type Out = u32; } "
           "pub fn f<T: W<Out = u32>>(x: T::Out) -> u32 { x + 1 }",
           f"fn main() {{ let r = {bb}(f::<W32>({bb}(u32::MAX))); "
           f"std::process::exit((r != 0) as i32 & 0); }}")
    # (h) trait DEFAULT body + overriding PANICKING impl — the T5 bundling channel:
    # proving the generic caller against the default body is a FALSE_PROOF (the
    # runtime instantiation panics via the override).
    yield ("sr_genalias_default_override",
           "pub trait D { fn m(&self) -> u32 { 1 } } "
           "pub struct P; impl D for P { fn m(&self) -> u32 { panic!(\"override\") } } "
           "pub fn f<T: D>(t: &T) -> u32 { t.m() }",
           f"fn main() {{ let r = {bb}(f({bb}(&P))); "
           f"std::process::exit((r != 1) as i32 & 0); }}")

    # Trust (countdown-loop piece, 2026-07-07): the bounded-countdown-loop family
    # (itoa `Unsigned::fmt`). `build_countdown_trip_facts` emits the EXACTLY-TIGHT
    # trip bound `_t.0 >= LEN - c*T` (T from the type max + guard const + divisor —
    # a theorem, never lattice info). An off-by-one DOWN in T is a FALSE PROOF the
    # N-1 buffers pin (they genuinely underflow at TY::MAX); the exact-N buffers
    # are the completeness targets (SOUND_PROOF); N+1 stays safe. Dimensions:
    # width x divisor x stride x buffer-delta, plus the named gate traps (signed
    # companion, cursor &mut reseat, conditional division, companion re-inflation).
    def _cd_trips(m, d, c):
        t = 0
        while m > c:
            t += 1
            m //= d
        return t

    for TY, M in [("u16", (1 << 16) - 1), ("u32", (1 << 32) - 1),
                  ("u64", (1 << 64) - 1), ("u128", (1 << 128) - 1)]:
        for D, C in [(10_000, 999), (10, 0)]:
            for STRIDE in ([1, 4] if D == 10_000 else [1]):
                T = _cd_trips(M, D, C)
                n_exact = STRIDE * T
                for delta, tag in [(-1, "short"), (0, "exact"), (1, "roomy")]:
                    n = n_exact + delta
                    if n <= 0:
                        continue
                    name = f"sr_countdown[{TY};div{D};c{STRIDE};N={n};{tag}]"
                    code = (
                        f"pub fn f(n: {TY}, buf: &mut [u8; {n}]) -> usize {{ "
                        f"let mut offset = buf.len(); let mut remain = n; "
                        f"while remain > {C} {{ offset -= {STRIDE}; remain /= {D}; "
                        f"buf[offset] = (remain & 0xff) as u8; }} offset }}"
                    )
                    drv = (
                        f"fn main() {{ let mut b = {bb}([0u8; {n}]); "
                        f"let r = {bb}(f({bb}({TY}::MAX), &mut b)); "
                        f"std::process::exit((r > {n}) as i32 & 0); }}"
                    )
                    yield (name, code, drv)

    # The FULL fmt shape (loop + post-loop `-=2`/`-=1` sites + `/= 100` reseat +
    # `n == 0` zero-trip): the exact buffer proves; one smaller underflows.
    for TY, LEN in [("u32", 10), ("u64", 20)]:
        full = (
            f"pub fn f(n: {TY}, buf: &mut [u8; LENSUB]) -> usize {{ "
            f"let mut offset = buf.len(); let mut remain = n; "
            f"while remain > 999 {{ offset -= 4; let quad = remain % 10_000; "
            f"remain /= 10_000; buf[offset] = (quad / 1000) as u8; "
            f"buf[offset + 1] = ((quad / 100) % 10) as u8; "
            f"buf[offset + 2] = ((quad / 10) % 10) as u8; "
            f"buf[offset + 3] = (quad % 10) as u8; }} "
            f"if remain > 9 {{ offset -= 2; buf[offset] = ((remain / 10) % 10) as u8; "
            f"buf[offset + 1] = (remain % 10) as u8; remain /= 100; }} "
            f"if remain != 0 || n == 0 {{ offset -= 1; buf[offset] = remain as u8; }} "
            f"offset }}"
        )
        for ln, tag in [(LEN, "exact"), (LEN - 1, "short")]:
            drv = (
                f"fn main() {{ let mut b = {bb}([0u8; {ln}]); "
                f"let r = {bb}(f({bb}({TY}::MAX), &mut b)); "
                f"let mut b2 = {bb}([0u8; {ln}]); let r2 = {bb}(f({bb}(0{TY}), &mut b2)); "
                f"std::process::exit(((r > {ln}) | (r2 > {ln})) as i32 & 0); }}"
            )
            yield (f"sr_countdown_full[{TY};N={ln};{tag}]",
                   full.replace("LENSUB", str(ln)), drv)

    # SIGNED companion (GATE-UINT): the builder must not fire; the short variant
    # panics at i32::MAX (CORRECT_REJECT), the exact one is safe (at worst a
    # COMPLETENESS_GAP — never a FALSE_PROOF).
    for n, tag in [(8, "exact"), (7, "short")]:
        yield (f"sr_countdown_i32_signed[{tag}]",
               f"pub fn f(n: i32, buf: &mut [u8; {n}]) -> usize {{ "
               f"let mut offset = buf.len(); let mut remain = n; "
               f"while remain > 999 {{ offset -= 4; remain /= 10_000; "
               f"buf[offset] = (remain & 0xff) as u8; }} offset }}",
               f"fn main() {{ let mut b = {bb}([0u8; {n}]); "
               f"let r = {bb}(f({bb}(i32::MAX), &mut b)); "
               f"std::process::exit((r > {n}) as i32 & 0); }}")

    # Gate traps as runtime bugs: cursor &mut reseat, conditional division,
    # companion re-inflation — all genuinely panic; must stay CORRECT_REJECT.
    yield ("sr_countdown_cursor_reseat",
           "#[inline(never)] fn bump(p: &mut usize) { *p = (*p).wrapping_add(100); } "
           "pub fn f(n: u64, buf: &mut [u8; 20]) -> usize { "
           "let mut offset = buf.len(); let mut remain = n; "
           "while remain > 999 { offset -= 4; remain /= 10_000; bump(&mut offset); "
           "buf[offset] = (remain & 0xff) as u8; } offset }",
           f"fn main() {{ let mut b = {bb}([0u8; 20]); "
           f"let r = {bb}(f({bb}(u64::MAX), &mut b)); "
           f"std::process::exit((r > 200) as i32 & 0); }}")
    yield ("sr_countdown_conditional_div",
           "pub fn f(n: u64, flag: bool, buf: &mut [u8; 20]) -> usize { "
           "let mut offset = buf.len(); let mut remain = n; "
           "while remain > 999 { offset -= 4; if flag { remain /= 10_000; } "
           "buf[offset] = (remain & 0xff) as u8; } offset }",
           f"fn main() {{ let mut b = {bb}([0u8; 20]); "
           f"let r = {bb}(f({bb}(u64::MAX), {bb}(false), &mut b)); "
           f"std::process::exit((r > 200) as i32 & 0); }}")
    yield ("sr_countdown_companion_reinflate",
           "pub fn f(n: u64, buf: &mut [u8; 20]) -> usize { "
           "let mut offset = buf.len(); let mut remain = n; "
           "while remain > 999 { offset -= 4; remain /= 10_000; "
           "remain = remain.wrapping_add(1_000_000); "
           "buf[offset] = (remain & 0xff) as u8; } offset }",
           f"fn main() {{ let mut b = {bb}([0u8; 20]); "
           f"let r = {bb}(f({bb}(u64::MAX), &mut b)); "
           f"std::process::exit((r > 200) as i32 & 0); }}")


# The opaque-path stubs (E3) assert a value coming out of a dyn call / atomic load /
# async resumption stays UNKNOWN and is never vacuously proved. A name prefix is the
# cheapest reliable tag (the families generator yields plain tuples).
OPAQUE_STUB_PREFIX = "opaque_"


def main():
    only = sys.argv[1] if len(sys.argv) > 1 else None
    # E3/D4 knobs (additive; defaults preserve the historical advisory-lane behavior).
    #   TRUST_FP_LIMIT=N   run at most N variants total (a tiny smoke subset).
    #   TRUST_FP_FULL=0    skip the batteries-on strict static pass (D4).
    #   TRUST_FP_FULL=1    (default) also run the strict pass and classify FALSE_PROOF_FULL.
    try:
        limit = int(os.environ.get("TRUST_FP_LIMIT", "0"))
    except ValueError:
        limit = 0
    run_full = os.environ.get("TRUST_FP_FULL", "1") != "0"

    false_proofs = []       # advisory-lane false proofs (the historical class)
    false_proofs_full = []  # D4: strict false proofs (proved-exit0 + overflow)
    opaque_overclaims = []  # E3: an opaque-path stub that became (vacuously) proved
    gaps = []
    counts = {"FALSE_PROOF": 0, "FALSE_PROOF_FULL": 0, "SOUND_PROOF": 0,
              "CORRECT_REJECT": 0, "COMPLETENESS_GAP": 0, "INCONCLUSIVE": 0}
    n = 0
    for name, code, drv in families():
        if only and not name.startswith(only):
            continue
        if limit and n >= limit:
            break
        n += 1
        is_opaque_stub = name.startswith(OPAQUE_STUB_PREFIX)
        with tempfile.TemporaryDirectory() as wd:
            sp, ssum = static_fully_proved(code, wd)
            spf, sfsum = (static_fully_proved_full(code, wd) if run_full else (False, "[full]skipped"))
            ov, odet = runtime_overflows(code, drv, wd)

        # Default-mode classification (UNCHANGED — the historical pass is intact).
        if ov is None:
            cls = "INCONCLUSIVE"
        elif sp and ov:
            cls = "FALSE_PROOF"
            false_proofs.append((name, code, ssum, odet))
        elif sp and not ov:
            cls = "SOUND_PROOF"
        elif (not sp) and ov:
            cls = "CORRECT_REJECT"
        else:
            cls = "COMPLETENESS_GAP"
            gaps.append((name, ssum))

        # D4: batteries-on strict mode is an INDEPENDENT soundness oracle. A strict build
        # that fully proves yet runtime-overflows is a FALSE_PROOF — the class where
        # nearly every kernel-certified P0 has lived. This is additive: it never relaxes
        # the default verdict, only adds a (louder) failure if -full over-claims.
        full_fp = run_full and spf and (ov is True)
        if full_fp:
            counts["FALSE_PROOF_FULL"] += 1
            false_proofs_full.append((name, code, sfsum, odet))

        # E3: an opaque-path stub must stay Unknown/runtime-checked. If EITHER mode
        # fully proved it, the opacity invariant broke — record it. (When it also
        # overflows it is already a FALSE_PROOF[_FULL] above; the extra record makes the
        # specific "vacuously proved an opaque value" regression unmissable in triage.)
        opaque_overclaim = is_opaque_stub and (sp or spf)
        if opaque_overclaim:
            opaque_overclaims.append((name, ssum, sfsum, odet))

        counts[cls] += 1
        tags = []
        if cls == "FALSE_PROOF":
            tags.append("<<<<< SOUNDNESS BUG (default)")
        if full_fp:
            tags.append("<<<<< SOUNDNESS BUG (strict)")
        if opaque_overclaim:
            tags.append("<<<<< OPAQUE PATH VACUOUSLY PROVED")
        tag = ("  " + " ".join(tags)) if tags else ""
        print(f"[{cls:16}] {name:30} static={ssum:18} {sfsum:20} runtime={odet}{tag}")

    print(f"\n=== {n} variants: " + ", ".join(f"{k}={v}" for k, v in counts.items()) + " ===")
    if gaps:
        print("\nCOMPLETENESS FRONTIER (safe code Trust does not yet prove):")
        for name, ssum in gaps:
            print(f"  - {name:30} ({ssum})")

    failed = False
    if false_proofs:
        print("\n!!!! FALSE PROOFS — DEFAULT mode (Trust proved safe, runtime overflowed) !!!!")
        for name, code, ssum, odet in false_proofs:
            print(f"\n  {name}: static={ssum} runtime={odet}\n    {code}")
        failed = True
    if false_proofs_full:
        print("\n!!!! FALSE PROOFS — STRICT (default fail-closed) "
              "(fully proved + exit 0, runtime overflowed) !!!!")
        for name, code, sfsum, odet in false_proofs_full:
            print(f"\n  {name}: static={sfsum} runtime={odet}\n    {code}")
        failed = True
    if opaque_overclaims:
        # An opaque-path over-claim is a soundness regression even if (for these inputs)
        # the runtime did not trip — a value that cannot be seen through must never be
        # proved. Fail loudly so it cannot rot into a silent vacuous proof.
        print("\n!!!! OPAQUE PATH VACUOUSLY PROVED "
              "(dyn/async/atomic value must stay Unknown, never proved) !!!!")
        for name, ssum, sfsum, odet in opaque_overclaims:
            print(f"  {name}: default={ssum} full={sfsum} runtime={odet}")
        failed = True

    if failed:
        return 1
    print("\nNO FALSE PROOFS FOUND — every advisory-lane AND strict `-full` proof in this "
          "neighborhood is sound, and every opaque path stayed Unknown.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
