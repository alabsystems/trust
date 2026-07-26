#!/usr/bin/env python3
"""Differential soundness oracle for trustc over GENERIC programs (the real compiler).

The generics wall (`unsupported MIR TyKind::Param … needs monomorphization`) is Rung 3's #1
measured lever, and fixing it (per-mono / opaque-param lowering) is soundness-delicate — exactly
where a 6th false-proof could be manufactured. This is the net that must exist BEFORE that fix:
a corpus of generic functions whose panic status is fixed by T-INDEPENDENT arithmetic (so it is
knowable ground truth), run through the real trustc, asserting the verifier NEVER reports a
panicking generic function PROVED. If a future generics-lowering change makes one of the `panic`
cases PROVE, this fails — catching the unsoundness before it ships.

It doubles as a finding: on the current compiler, T-independent obligations in generic functions
DO prove/refute correctly (only T-dependent obligations are unknown), so the generics wall is
narrower than the raw unknown count implies.

Usage:  python3 scripts/trustc_generics_soundness_oracle.py [path-to-trustc]
Skips (exit 0) with a notice if no built trustc is found.
"""
import json
import os
import subprocess
import sys
import tempfile

# (fn_name, "total"|"panic"): panic status determined by knowable arithmetic. The function names
# are matched as substrings, so a function's CLOSURES (`fn::{closure#0}`) count toward its label.
CORPUS_LABELS = {
    "g_total_guarded": "total",       # if x>=1 { x-1 }  — guarded, T-independent
    "g_total_div_guarded": "total",   # if b==0 {0} else { a/b }
    "g_panic_sub": "panic",           # x-1            — underflows at x==0, any T
    "g_panic_div": "panic",           # a/b            — div-by-zero at b==0, any T
    # ADVERSARIAL — the patterns the coming generics / modular-spec fixes MUST NOT false-prove:
    "g_panic_t_value": "panic",       # x = t.into() unbounded; x-1 underflows at x==0 (T-VALUE-dependent)
    "g_total_t_value_guarded": "total",  # same but guarded — the recovery target (proved-or-unknown ok)
    "c_panic_closure_unbounded": "panic",  # `|v| -v` over an UNBOUNDED i64 — can hit i64::MIN (the
                                           # dangerous version of clean-kernel's context-safe closure)
    # R3 (pre-monomorphization ALIAS twins — `I::Item` / `S::Item` / `T::Out` are
    # param-bearing projection aliases, the corpus's serde-derive-shaped cluster):
    "r3_pick": "total",          # guarded T-independent bounds — the R3 recovery target
    "r3_shift": "total",         # guarded k+1 beside an opaque Option<S::Item> payload
    "r3_panic_shift": "panic",   # UNGUARDED k+1 beside the opaque payload — overflows at u32::MAX
    "r3_t_feed": "panic",        # T-method result feeding an index — havoc; must NOT prove
    "r3_t_oob": "panic",         # xs[10] on a symbolic-length generic slice — genuinely OOB
    "r3_t_sizeof": "panic",      # size_of::<T>() feeding an index — layout-dependent
    "r3_t_pinned": "panic",      # where-clause-PINNED T::Out=u32 arithmetic — overflows at MAX;
                                 # refuted (if MIR spells u32) or unknown (alias), NEVER proved
}

CORPUS_SRC = r"""
pub fn g_total_guarded<T>(_items: &[T], x: u32) -> u32 { if x >= 1 { x - 1 } else { 0 } }
pub fn g_total_div_guarded<T>(_t: &T, a: u64, b: u64) -> u64 { if b == 0 { 0 } else { a / b } }
pub fn g_panic_sub<T>(_items: &[T], x: u32) -> u32 { x - 1 }
pub fn g_panic_div<T>(_t: &T, a: u64, b: u64) -> u64 { a / b }
pub fn g_panic_t_value<T: Into<u32>>(t: T) -> u32 { let x: u32 = t.into(); x - 1 }
pub fn g_total_t_value_guarded<T: Into<u32>>(t: T) -> u32 { let x: u32 = t.into(); if x >= 1 { x - 1 } else { 0 } }
pub fn c_panic_closure_unbounded(opt: Option<i64>) -> Option<i64> { opt.map(|v| -v) }
pub fn r3_pick<I: Iterator>(xs: &[I::Item], i: usize) -> Option<&I::Item> {
    if i < xs.len() { Some(&xs[i]) } else { None }
}
pub trait Src { type Item; }
pub fn r3_shift<S: Src>(pending: Option<S::Item>, k: u32) -> (Option<S::Item>, u32) {
    let bumped = if k < 1000 { k + 1 } else { 0 };
    (pending, bumped)
}
pub fn r3_panic_shift<S: Src>(pending: Option<S::Item>, k: u32) -> (Option<S::Item>, u32) {
    (pending, k + 1)
}
pub trait Feed { type Item: Into<usize> + Copy; }
pub fn r3_t_feed<S: Feed>(xs: &[u8; 4], it: S::Item) -> u8 { xs[it.into()] }
pub fn r3_t_oob<I: Iterator>(xs: &[I::Item]) -> &I::Item { &xs[10] }
pub fn r3_t_sizeof<T>(xs: &[u8; 64]) -> u8 { xs[core::mem::size_of::<T>()] }
pub trait W { type Out; }
pub fn r3_t_pinned<T: W<Out = u32>>(x: T::Out) -> u32 { x + 1 }
struct SrcU8;
impl Src for SrcU8 { type Item = u8; }
struct FeedU8;
impl Feed for FeedU8 { type Item = u8; }
struct WU32;
impl W for WU32 { type Out = u32; }
fn main() {
    let v: Vec<u8> = vec![1, 2, 3];
    let _ = (g_total_guarded(&v, 5), g_total_div_guarded(&0u8, 10, 2),
             g_panic_sub(&v, 3), g_panic_div(&0u8, 10, 2),
             g_panic_t_value(7u8), g_total_t_value_guarded(7u8),
             c_panic_closure_unbounded(Some(5)));
    let long: Vec<u8> = vec![0; 16];
    let _ = (r3_pick::<std::vec::IntoIter<u8>>(&v, 1),
             r3_shift::<SrcU8>(Some(3u8), 5),
             r3_panic_shift::<SrcU8>(Some(3u8), 5),
             r3_t_feed::<FeedU8>(&[9u8; 4], 2u8),
             r3_t_oob::<std::vec::IntoIter<u8>>(&long),
             r3_t_sizeof::<u8>(&[7u8; 64]),
             r3_t_pinned::<WU32>(41));
}
"""

# Arithmetic/bounds obligation kinds (a panic surface with knowable ground truth). Substring
# match so `overflow:sub`, `overflow:neg`, `NegationOverflow`, `divzero`, etc. are all caught.
ARITH_KEYS = ("overflow", "neg", "divzero", "remzero", "shift", "bounds", "slice", "index")


def is_arith(kind):
    k = (kind or "").lower()
    return any(key in k for key in ARITH_KEYS)


def find_trustc(argv):
    if len(argv) > 1:
        return argv[1]
    root = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    for host in ("aarch64-apple-darwin", "x86_64-unknown-linux-gnu", "host"):
        p = os.path.join(root, "build", host, "stage2", "bin", "trustc")
        if os.path.exists(p):
            return p
    return None


def main():
    trustc = find_trustc(sys.argv)
    if not trustc:
        print("NOTICE: no built trustc found (build/<host>/stage2/bin/trustc) — skipping.")
        return 0

    with tempfile.TemporaryDirectory() as d:
        src = os.path.join(d, "generics_soundness.rs")
        with open(src, "w") as f:
            f.write(CORPUS_SRC)
        out = subprocess.run(
            [trustc, src, "-o", os.path.join(d, "out"),
             "-Z", "trust-policy=advisory", "-Z", "trust-verify-output=json"],
            capture_output=True, text=True,
        )
        # label -> list of arith outcomes, accumulated across the fn AND its closures
        # (a closure `fn::{closure#0}` counts toward `fn` via substring match).
        acc = {fn: [] for fn in CORPUS_LABELS}
        for line in (out.stdout + out.stderr).splitlines():
            i = line.find("TRUST_JSON:")
            if i < 0:
                continue
            try:
                d_ = json.loads(line[i + len("TRUST_JSON:"):])
            except json.JSONDecodeError:
                continue
            if d_.get("type") != "function_result":
                continue
            full = d_.get("function", "")
            for fn in CORPUS_LABELS:
                if fn in full:
                    for r in d_.get("results", []):
                        if is_arith(r.get("kind")):
                            acc[fn].append(r.get("outcome"))

    violations = []
    for fn, label in CORPUS_LABELS.items():
        outs = acc[fn]
        if not outs:
            # No arith obligation surfaced (e.g. T-dependent op left fully unknown): sound, not a
            # violation — there is simply nothing that could be a false PROVE.
            print(f"  {fn:26s} [{label:5s}] (no arith obligation surfaced)")
            continue
        if label == "panic" and any(o == "proved" for o in outs):
            # SOUNDNESS: a panicking case's arithmetic obligation must NEVER be PROVED.
            violations.append(
                f"FALSE PROVE: panicking `{fn}` had a PROVED arithmetic obligation {outs}")
        print(f"  {fn:26s} [{label:5s}] arith outcomes={outs}")

    if violations:
        print("\nSOUNDNESS VIOLATIONS (generics):")
        for v in violations:
            print("  -", v)
        return 1
    print("\ngenerics soundness oracle: no false PROVE on any panicking generic program "
          "(panicking arith obligations are failed/unknown, never proved). SOUND.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
