#!/usr/bin/env python3
# W1 crate-ladder recensus 2026-07-11 — §3.1 evidence: the nine published-crate
# census corpora contain ZERO self-recursive rows and ZERO call-graph cycles,
# so the structural-fold lane (which requires self/SCC recursion) has no
# possible contact with them. Run from crates/trust-clean/fixtures/.
#
# Output (2026-07-11, corpora byte-identical to their committed state):
#   census-2026-07-06/arrayvec: self-recursive=0 cycles=0
#   census-2026-07-06/memchr: self-recursive=0 cycles=0
#   census-2026-07-06/either: self-recursive=0 cycles=0
#   census-2026-07-06/byteorder: self-recursive=0 cycles=0
#   census-2026-07-06/itoa: self-recursive=0 cycles=0
#   census-rung2-2026-07-07/ascii_utils: self-recursive=0 cycles=0
#   census-rung2-2026-07-07/bit_field: self-recursive=0 cycles=0
#   census-rung2-2026-07-07/cast: self-recursive=0 cycles=0
#   census-rung2-2026-07-07/nonmax: self-recursive=0 cycles=0
import json, pathlib, sys

sys.setrecursionlimit(10000)
DIRS = [
    "census-2026-07-06/arrayvec", "census-2026-07-06/memchr",
    "census-2026-07-06/either", "census-2026-07-06/byteorder",
    "census-2026-07-06/itoa", "census-rung2-2026-07-07/ascii_utils",
    "census-rung2-2026-07-07/bit_field", "census-rung2-2026-07-07/cast",
    "census-rung2-2026-07-07/nonmax",
]

for d in DIRS:
    funcs, names = {}, {}
    for p in sorted(pathlib.Path(d).glob("*.json")):
        try:
            f = json.loads(p.read_text())
        except Exception:
            continue
        funcs[f["def_path"]] = f
        names.setdefault(f.get("name", ""), f["def_path"])

    def resolve(callee):
        # mirror trust_vcgen::call_graph resolution: exact / name / ::suffix
        if callee in funcs:
            return callee
        if callee in names:
            return names[callee]
        for k in funcs:
            if k.endswith("::" + callee):
                return k
        return None

    edges, selfrec = {dp: set() for dp in funcs}, []
    for dp, f in funcs.items():
        for b in f.get("body", {}).get("blocks", []):
            t = b.get("terminator")
            if isinstance(t, dict) and "Call" in t:
                tgt = resolve(t["Call"].get("func", ""))
                if tgt == dp:
                    selfrec.append(dp)
                elif tgt:
                    edges[dp].add(tgt)

    WHITE, GRAY, BLACK = 0, 1, 2
    color = {n: WHITE for n in edges}
    cycles = []

    def dfs(n, stack):
        color[n] = GRAY
        stack.append(n)
        for m in edges[n]:
            if color[m] == GRAY:
                cycles.append(stack[stack.index(m):] + [m])
            elif color[m] == WHITE:
                dfs(m, stack)
        stack.pop()
        color[n] = BLACK

    for n in edges:
        if color[n] == WHITE:
            dfs(n, [])
    print(f"{d}: self-recursive={len(set(selfrec))} cycles={len(cycles)}")
