#!/usr/bin/env python3
"""trust_ir_scc_populations.py — the LOOP and RECURSION populations of a
published TrustIR module, by TARJAN SCC, with each body's differential verdict,
marker-channel verdict and flip outcome joined onto it.

Two populations, both defined by a strongly-connected component and NEVER by a
text-order back-edge heuristic (a text-order heuristic gave one lane two false
positives before this tool existed):

  LOOP      : a body whose intra-procedural BLOCK graph has a non-trivial SCC
              (|SCC| > 1, or a single block with a self-edge).
  RECURSION : a body whose node in the crate CALL graph lies in a non-trivial
              SCC (|SCC| > 1 = mutual recursion, or a self-edge = a direct
              self-call).

Input is the producer's own published evidence — `<crate>.trust-ir.txt` (the
canonical text TrustIR) and `<crate>.coverage.json` (verdicts + `func_id`) from
both opt levels, plus the two `RUSTC_LOG=rustc_mir_transform::trust_ir_flip=info`
stderr logs.

TWO JOINS, AND BOTH ARE LOAD-BEARING — a naive spelling of either silently
misreports the population:

  * coverage row -> TrustIR body is POSITIONAL (`func_id` is the 0-based index
    of the body's `rustcc fn` in the text module), not by name: 294 coverage
    rows share a `def_path` with another row (`cert::bundle::_` x6, serde's
    `__FieldVisitor::expecting` x23, ...). The correspondence is VERIFIED for
    every row that carries a `func_id` and the run ABORTS on one disagreement.
  * coverage row -> flip log is by `def_index`, not by name: the flip log
    renders rustc's DefId path (`level::{impl#18}::is_zero`) while coverage
    renders the pretty def path (`level::Level::is_zero`), so a name join
    reports EVERY impl method as "did not flip" and every FALLBACK as absent.

Usage:
  trust_ir_scc_populations.py <dump_O3_dir> <dump_O0_dir> \\
                              <O3.flip.txt> <O0.flip.txt> <crate-name>
"""
from __future__ import annotations

import json
import os
import re
import sys
from collections import defaultdict

# ---------------------------------------------------------------- trust-ir.txt

FN_RE = re.compile(r"^rustcc fn @(.+)\((functy\.\d+)\)\s*\{\s*$")
BLK_RE = re.compile(r"^bb(\d+)(?:\(([^)]*)\))?:\s*$")
CALL_RE = re.compile(r"\bcall @func\.(\d+)\b")
# every `bbN` mentioned in a terminator operand position
BBREF_RE = re.compile(r"\bbb(\d+)\b")

TERMS = ("br ", "condbr ", "switch ", "ret", "unreachable", "trap", "switchint ")


def strip_comment(line: str) -> str:
    # trust-ir text comments start at the first `;`
    i = line.find(";")
    return line if i < 0 else line[:i]


class Body:
    __slots__ = ("name", "functy", "blocks", "succs", "calls", "insts", "raw")

    def __init__(self, name, functy):
        self.name = name
        self.functy = functy
        self.blocks = []          # ordered block ids
        self.succs = {}           # bb -> [bb]
        self.calls = set()        # func ids called
        self.insts = 0
        self.raw = []


def parse_ir(path):
    bodies = []
    cur = None
    curbb = None
    with open(path, "r", errors="replace") as fh:
        for line in fh:
            line = line.rstrip("\n")
            if cur is None:
                m = FN_RE.match(line)
                if m:
                    cur = Body(m.group(1), m.group(2))
                    curbb = None
                continue
            if line == "}":
                bodies.append(cur)
                cur = None
                curbb = None
                continue
            cur.raw.append(line)
            code = strip_comment(line).strip()
            if not code:
                continue
            m = BLK_RE.match(code)
            if m:
                curbb = int(m.group(1))
                cur.blocks.append(curbb)
                cur.succs.setdefault(curbb, [])
                continue
            if curbb is None:
                continue
            cur.insts += 1
            for c in CALL_RE.finditer(code):
                cur.calls.add(int(c.group(1)))
            # terminator?
            head = code.split()[0] if code.split() else ""
            if head in ("br", "condbr", "switch", "switchint"):
                cur.succs[curbb].extend(int(b) for b in BBREF_RE.findall(code))
    return bodies


# ------------------------------------------------------------------- Tarjan

def tarjan(nodes, succ):
    """Iterative Tarjan. Returns list of SCCs (lists of nodes)."""
    index = {}
    low = {}
    onstack = {}
    stack = []
    out = []
    counter = [0]
    for root in nodes:
        if root in index:
            continue
        work = [(root, 0)]
        while work:
            v, pi = work[-1]
            if pi == 0:
                index[v] = low[v] = counter[0]
                counter[0] += 1
                stack.append(v)
                onstack[v] = True
            recurse = False
            succs = succ(v)
            for i in range(pi, len(succs)):
                w = succs[i]
                if w not in index:
                    work[-1] = (v, i + 1)
                    work.append((w, 0))
                    recurse = True
                    break
                elif onstack.get(w):
                    low[v] = min(low[v], index[w])
            if recurse:
                continue
            if low[v] == index[v]:
                comp = []
                while True:
                    w = stack.pop()
                    onstack[w] = False
                    comp.append(w)
                    if w == v:
                        break
                out.append(comp)
            work.pop()
            if work:
                u = work[-1][0]
                low[u] = min(low[u], low[v])
    return out


def has_cycle(nodes, succ):
    """True iff the graph has a non-trivial SCC or a self-edge."""
    for comp in tarjan(nodes, succ):
        if len(comp) > 1:
            return True, comp
        v = comp[0]
        if v in succ(v):
            return True, comp
    return False, None


def all_cycles(nodes, succ):
    res = []
    for comp in tarjan(nodes, succ):
        if len(comp) > 1 or comp[0] in succ(comp[0]):
            res.append(sorted(comp))
    return res


# --------------------------------------------------------------- flip logs

# THE FLIP LOG IS KEYED ON `def_index`, NOT ON A NAME.
# The log renders rustc's DefId path (`level::{impl#18}::is_zero`) while
# coverage.json renders the pretty def path (`level::Level::is_zero`); a
# name-keyed join silently reports every impl method as "did not flip". The
# numeric `DefId(0:NNNNN)` is exactly coverage.json's `def_index`.
FLIP_RE = re.compile(
    r"trust-ir-flip: (CTFE )?compiled from trust-ir, did=DefId\(0:(\d+) ~ "
)
FALLBACK_RE = re.compile(
    r"trust-ir-flip: FALLBACK to built MIR, did=DefId\(0:(\d+) ~ [^)]*\), "
    r"reason=\"(.*?)\", stage=\"(.*?)\""
)


def parse_flips(path):
    flips = {}
    fallbacks = {}
    with open(path, "r", errors="replace") as fh:
        for line in fh:
            if "trust_ir_flip" not in line:
                continue
            m = FLIP_RE.search(line)
            if m:
                flips[int(m.group(2))] = "ctfe" if m.group(1) else "codegen"
                continue
            m = FALLBACK_RE.search(line)
            if m:
                fallbacks.setdefault(int(m.group(1)), []).append((m.group(2), m.group(3)))
    return flips, fallbacks


# ------------------------------------------------------------------- main

def main():
    d3, d0, f3, f0, crate = sys.argv[1:6]
    ir3 = parse_ir(os.path.join(d3, f"{crate}.trust-ir.txt"))
    cov3 = json.load(open(os.path.join(d3, f"{crate}.coverage.json")))
    cov0 = json.load(open(os.path.join(d0, f"{crate}.coverage.json")))
    flips3, fb3 = parse_flips(f3)
    flips0, fb0 = parse_flips(f0)

    # ---- THE JOIN IS POSITIONAL, NOT BY NAME.
    # 294 coverage rows share a def_path with another row (`cert::bundle::_` x6,
    # serde `__FieldVisitor::expecting` x23, ...), so a name-keyed join silently
    # drops them. `func_id` is the 0-based index of the body's `rustcc fn` in the
    # published text module; that is VERIFIED below against every coverage row
    # that carries a func_id, and the run aborts if a single one disagrees.
    ir_by_fid = {i: b for i, b in enumerate(ir3)}
    cov3_by_fid, cov0_by_fid = {}, {}
    bad = 0
    for b in cov3["bodies"]:
        f = b.get("func_id")
        if f is None:
            continue
        cov3_by_fid[f] = b
        got = ir_by_fid.get(f)
        # The producer names a const/static INITIALIZER body `<item>::{const-init}`
        # while rustc's def path stops at the item — the same one suffix
        # `to_mir::names_this_body` steps over before comparing.
        gotname = got.name if got else None
        for suf in ("::{const-init}", "::{static-init}"):
            if gotname and gotname.endswith(suf):
                gotname = gotname[: -len(suf)]
                break
        if gotname != b["def_path"]:
            bad += 1
            if bad <= 5:
                print(f"  JOIN MISMATCH fid={f} cov={b['def_path']!r} ir={got.name if got else None!r}")
    for b in cov0["bodies"]:
        if b.get("func_id") is not None:
            cov0_by_fid[b["func_id"]] = b
    print(f"# bodies in coverage.json : {len(cov3['bodies'])}")
    print(f"# rustcc fn in trust-ir   : {len(ir3)}")
    print(f"# coverage rows w/ func_id: {len(cov3_by_fid)}")
    print(f"# POSITIONAL JOIN MISMATCH: {bad}")
    if bad:
        print("ABORT: positional func_id join is not sound on this dump")
        return 2

    by_path3 = {}
    by_path0 = {}
    for f, b in cov3_by_fid.items():
        by_path3[ir_by_fid[f].name] = b
    for f, b in cov0_by_fid.items():
        if f in ir_by_fid:
            by_path0[ir_by_fid[f].name] = b
    fid_of = {ir_by_fid[f].name: f for f in cov3_by_fid}
    name_of_fid = {f: ir_by_fid[f].name for f in ir_by_fid}

    # ---- LOOP population: intra-procedural block-graph SCC
    loop_bodies = []
    for b in ir3:
        if len(b.blocks) < 2:
            # a single block can still self-loop
            if b.blocks and b.blocks[0] in b.succs.get(b.blocks[0], []):
                loop_bodies.append((b, [[b.blocks[0]]]))
            continue
        cyc = all_cycles(b.blocks, lambda v, b=b: b.succs.get(v, []))
        if cyc:
            loop_bodies.append((b, cyc))

    # ---- RECURSION population: call-graph SCC over func ids
    #      nodes are func ids that HAVE a body in the trust-ir
    fid_body = dict(ir_by_fid)
    cg_nodes = sorted(fid_body)
    cg_succ = {f: sorted(c for c in fid_body[f].calls) for f in cg_nodes}
    rec_cycles = all_cycles(cg_nodes, lambda v: cg_succ.get(v, []))
    rec_fids = set()
    for comp in rec_cycles:
        rec_fids.update(comp)

    def row(b, cov, flips, fallbacks):
        c = cov.get(b.name)
        if c is None:
            return dict(verdict="(no coverage row)", markers=False, interp="?", samples=0,
                        flip=None, fb=None)
        di = c.get("def_index")
        dm = c["differentials"]["derived_mir"]
        it = c["differentials"]["interpreter"]
        return dict(
            verdict=dm["verdict"], detail=dm.get("detail", ""),
            markers=dm.get("markers_exact", False),
            mdetail=dm.get("markers_detail", ""),
            interp=it["verdict"], samples=it.get("samples", 0),
            flip=flips.get(di), fb=fallbacks.get(di),
        )

    print()
    print("=" * 78)
    print(f"LOOP POPULATION (block-graph SCC) : {len(loop_bodies)}")
    print("=" * 78)
    for b, cyc in sorted(loop_bodies, key=lambda x: x[0].name):
        r3 = row(b, by_path3, flips3, fb3)
        r0 = row(b, by_path0, flips0, fb0)
        print(f"\n{b.name}")
        print(f"    func_id={fid_of.get(b.name)}  blocks={len(b.blocks)}  insts={b.insts}  sccs={cyc}")
        print(f"    O3  derived_mir={r3['verdict']:12s} markers_exact={r3['markers']}  interp={r3['interp']}/{r3['samples']}  flip={r3['flip']}")
        print(f"        detail={r3.get('detail','')!r}")
        print(f"        markers_detail={r3.get('mdetail','')!r}")
        if r3["fb"]:
            print(f"        FALLBACK O3: {r3['fb']}")
        print(f"    O0  derived_mir={r0['verdict']:12s} markers_exact={r0['markers']}  interp={r0['interp']}/{r0['samples']}  flip={r0['flip']}")
        if r0["fb"]:
            print(f"        FALLBACK O0: {r0['fb']}")

    print()
    print("=" * 78)
    print(f"RECURSION POPULATION (call-graph SCC) : {len(rec_fids)}   cycles={len(rec_cycles)}")
    print("=" * 78)
    for comp in sorted(rec_cycles, key=lambda c: name_of_fid.get(c[0], "")):
        names = [name_of_fid.get(f, f"?fid{f}") for f in comp]
        kind = "SELF" if len(comp) == 1 else f"MUTUAL({len(comp)})"
        print(f"\n--- {kind} cycle: {names}")
        for f in comp:
            b = fid_body[f]
            r3 = row(b, by_path3, flips3, fb3)
            r0 = row(b, by_path0, flips0, fb0)
            selfcall = f in b.calls
            print(f"  {b.name}")
            print(f"    func_id={f}  blocks={len(b.blocks)}  insts={b.insts}  self_call={selfcall}  callees_in_scc={[name_of_fid.get(x,x) for x in sorted(set(b.calls)&set(comp))]}")
            print(f"    O3  derived_mir={r3['verdict']:12s} markers_exact={r3['markers']}  interp={r3['interp']}/{r3['samples']}  flip={r3['flip']}")
            print(f"        detail={r3.get('detail','')!r}")
            print(f"        markers_detail={r3.get('mdetail','')!r}")
            if r3["fb"]:
                print(f"        FALLBACK O3: {r3['fb']}")
            print(f"    O0  derived_mir={r0['verdict']:12s} markers_exact={r0['markers']}  interp={r0['interp']}/{r0['samples']}  flip={r0['flip']}")
            if r0["fb"]:
                print(f"        FALLBACK O0: {r0['fb']}")

    # ------- summary line in the brief's own vocabulary
    def summarize(tag, bodies):
        n = len(bodies)
        agreed = sum(1 for b in bodies if by_path3.get(b.name, {}).get("differentials", {}).get("derived_mir", {}).get("verdict") == "agreed")
        mx = sum(1 for b in bodies if by_path3.get(b.name, {}).get("differentials", {}).get("derived_mir", {}).get("markers_exact"))
        bodyful_closure = sum(1 for b in bodies if "{closure#" in b.name and b.insts > 0 and len(b.blocks) > 0)
        di = lambda b: by_path3.get(b.name, {}).get("def_index")
        f3n = sum(1 for b in bodies if di(b) in flips3)
        f0n = sum(1 for b in bodies if di(b) in flips0)
        print(f"\n{tag}: {n} carry one, {agreed} agreed, {mx} markers_exact, "
              f"{bodyful_closure} bodyful closure, {f3n} flip at -O3, {f0n} flip at -O0")

    print()
    print("=" * 78)
    print("SUMMARY (same vocabulary as the brief)")
    print("=" * 78)
    summarize("loop", [b for b, _ in loop_bodies])
    summarize("recursion", [fid_body[f] for f in sorted(rec_fids)])

    # ---- the -O0 module, measured independently. The two opt levels publish the
    # same producer module (the shim runs at `mir_built`, before optimization), so
    # a difference here is itself a finding rather than a nuisance.
    ir0 = parse_ir(os.path.join(d0, f"{crate}.trust-ir.txt"))
    l0 = set()
    for b in ir0:
        if b.blocks and (all_cycles(b.blocks, lambda v, b=b: b.succs.get(v, []))):
            l0.add(b.name)
    fid0 = {i: b for i, b in enumerate(ir0)}
    cg0 = {f: sorted(fid0[f].calls) for f in fid0}
    r0 = set()
    for comp in all_cycles(sorted(fid0), lambda v: cg0.get(v, [])):
        r0.update(fid0[f].name for f in comp)
    l3 = {b.name for b, _ in loop_bodies}
    r3 = {fid_body[f].name for f in rec_fids}
    print(f"\n-O0 module: {len(ir0)} bodies; loop={len(l0)} recursion={len(r0)}")
    print(f"   loop      symmetric difference O3 vs O0: {sorted(l3 ^ l0)}")
    print(f"   recursion symmetric difference O3 vs O0: {sorted(r3 ^ r0)}")


if __name__ == "__main__":
    main()
