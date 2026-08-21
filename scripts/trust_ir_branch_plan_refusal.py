#!/usr/bin/env python3
"""trust_ir_branch_plan_refusal.py — which clause of `to_mir::plan_branch_markers`
refuses a body, read off the producer's own published TrustIR.

Evaluated against the PRODUCER'S OWN published trust-ir text, in the ADMITTING
direction: every clause this script cannot see (`func.scopes`, which is a
`#scope:` comment in the text and IS visible, so only the source-side
`source_form_admits` / `plan_field_write_markers` / `plan_interior_borrow_markers`
gates are unmodelled) is assumed to PASS. A body reported as ADMIT is therefore
an OVER-count; a body reported with a refusal really is refused, at that clause.

Clause order and line numbers are read off
`crates/trust-thir-lower/src/to_mir.rs` at the rev under measurement, so the
`file:line` in the output is checkable.

Usage:
  trust_ir_branch_plan_refusal.py <crate.trust-ir.txt>           # histogram
  trust_ir_branch_plan_refusal.py <crate.trust-ir.txt> <substr>  # per body
"""
from __future__ import annotations

import os
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from trust_ir_scc_populations import parse_ir, strip_comment, all_cycles  # noqa: E402

# to_mir.rs clause -> (line, text). Kept as data so a rev bump shows up as a diff.
CLAUSES = {
    "B1_scopes": ("to_mir.rs:4906", "func.scopes.is_some() -> None  (wave-MF firewall; a source `let`)"),
    "B2_blocks": ("to_mir.rs:4910", "func.blocks.len() < 2 -> None  (single-block class)"),
    "B3_term": ("to_mir.rs:4953", "terminator outside {Br, CondBr, Return} -> None"),
    "B4_operands": ("to_mir.rs:4964", "operands_of(inst) == None -> None  (instruction outside {Const,ExtractField,BinOp,ICmp,UnOp,Cast,Br,CondBr,Return})"),
    "B5_return": ("to_mir.rs:4978", "n_return != 1 -> None  (second Return = an early `return`)"),
    "B6_shift": ("to_mir.rs:4993", "any Shl/LShr/AShr -> None  (lost-flip hazard)"),
    "B7_uses": ("to_mir.rs:5002", "a result not used exactly once, in its own block -> None"),
    "B8_backedge": ("to_mir.rs:5031", "back edge (gray-node hit) -> None  ** A LOOP **"),
    "B9_unreach": ("to_mir.rs:5043", "postorder.len() != blocks.len() -> None  (unreachable block)"),
    "ADMIT": ("-", "no modelled clause refuses (over-count: source-side gates unmodelled)"),
}

# `operands_of`'s admitted instruction set, spelled as the trust-ir text opcodes.
# Const / ExtractField / BinOp / ICmp / UnOp / Cast, plus the three terminators.
OPC_OK = {
    "const", "extractfield",
    # BinOp
    "add", "sub", "mul", "udiv", "sdiv", "urem", "srem", "and", "or", "xor",
    "shl", "lshr", "ashr",
    # ICmp
    "icmp",
    # UnOp
    "not", "neg",
    # Cast
    "zext", "sext", "trunc", "bitcast", "inttoptr", "ptrtoint", "fptoui",
    "fptosi", "uitofp", "sitofp", "fpext", "fptrunc", "cast",
}
TERM_OK = {"br", "condbr", "ret"}
SHIFTS = {"shl", "lshr", "ashr"}


def blocks_of(body):
    """[(bb, [code lines...])] in text order."""
    out = []
    cur = None
    for line in body.raw:
        code = strip_comment(line).strip()
        if not code:
            continue
        m = re.match(r"^bb(\d+)(?:\(([^)]*)\))?:\s*$", code)
        if m:
            cur = (int(m.group(1)), [])
            out.append(cur)
            continue
        if cur is None:
            continue
        cur[1].append(code)
    return out


def opcode(code):
    """The instruction's opcode: `%3 = load enum.2, ptr %0` -> `load`."""
    if "=" in code.split(";")[0]:
        rhs = code.split("=", 1)[1].strip()
        return rhs.split()[0] if rhs.split() else ""
    return code.split()[0] if code.split() else ""


def first_refusal(body):
    has_scope = any(l.strip().startswith("; #scope:") for l in body.raw)
    if has_scope:
        return "B1_scopes", "carries `#scope:` (a source `let`)"
    blks = blocks_of(body)
    if len(blks) < 2:
        return "B2_blocks", f"{len(blks)} block(s)"
    n_return = 0
    for bb, codes in blks:
        if not codes:
            return "B3_term", f"bb{bb} empty"
        term = opcode(codes[-1])
        if term not in TERM_OK:
            return "B3_term", f"bb{bb} terminator `{term}`"
        if term == "ret":
            n_return += 1
        for c in codes[:-1]:
            op = opcode(c)
            if op not in OPC_OK:
                return "B4_operands", f"bb{bb} `{op}`"
    if n_return != 1:
        return "B5_return", f"{n_return} Return terminators"
    for bb, codes in blks:
        for c in codes[:-1]:
            if opcode(c) in SHIFTS:
                return "B6_shift", f"bb{bb} `{opcode(c)}`"
    # B7 (single use, own block) is not modelled: assume PASS (admitting direction).
    cyc = all_cycles(body.blocks, lambda v: body.succs.get(v, []))
    if cyc:
        return "B8_backedge", f"SCC {cyc}"
    # reachability
    seen, work = set(), [body.blocks[0]] if body.blocks else []
    while work:
        v = work.pop()
        if v in seen:
            continue
        seen.add(v)
        work.extend(body.succs.get(v, []))
    if len(seen) != len(body.blocks):
        return "B9_unreach", f"{len(body.blocks) - len(seen)} unreachable block(s)"
    return "ADMIT", ""


def all_refusals(body):
    """EVERY modelled clause that refuses, not just the first — a body with four
    independent walls needs four named, not one."""
    out = []
    if any(l.strip().startswith("; #scope:") for l in body.raw):
        out.append(("B1_scopes", "carries `#scope:` (a source `let`)"))
    blks = blocks_of(body)
    if len(blks) < 2:
        out.append(("B2_blocks", f"{len(blks)} block(s)"))
    bad_term, bad_op, shifts = [], [], []
    n_return = 0
    for bb, codes in blks:
        if not codes:
            bad_term.append(f"bb{bb} empty")
            continue
        term = opcode(codes[-1])
        if term not in TERM_OK:
            bad_term.append(f"bb{bb}:`{term}`")
        if term == "ret":
            n_return += 1
        for c in codes[:-1]:
            op = opcode(c)
            if op not in OPC_OK:
                bad_op.append(f"bb{bb}:`{op}`")
            if op in SHIFTS:
                shifts.append(f"bb{bb}:`{op}`")
    if bad_term:
        out.append(("B3_term", ", ".join(sorted(set(bad_term))[:8])))
    if bad_op:
        out.append(("B4_operands", ", ".join(sorted(set(bad_op))[:12])))
    if n_return != 1:
        out.append(("B5_return", f"{n_return} Return terminators"))
    if shifts:
        out.append(("B6_shift", ", ".join(sorted(set(shifts))[:6])))
    cyc = all_cycles(body.blocks, lambda v: body.succs.get(v, []))
    if cyc:
        out.append(("B8_backedge", f"SCC {cyc}"))
    seen, work = set(), ([body.blocks[0]] if body.blocks else [])
    while work:
        v = work.pop()
        if v in seen:
            continue
        seen.add(v)
        work.extend(body.succs.get(v, []))
    if body.blocks and len(seen) != len(body.blocks):
        out.append(("B9_unreach", f"{len(body.blocks) - len(seen)} unreachable"))
    return out


def main():
    path = sys.argv[1]
    wants = sys.argv[2:]
    ir = parse_ir(path)
    if wants:
        for b in ir:
            if any(w in b.name for w in wants):
                clause, why = first_refusal(b)
                loc, text = CLAUSES[clause]
                print(f"{b.name}")
                print(f"    blocks={len(b.blocks)} insts={b.insts} calls={sorted(b.calls)[:8]}")
                print(f"    FIRST refusal : {clause}  @ {loc}   [{why}]")
                print(f"                    {text}")
                for c, w in all_refusals(b):
                    print(f"    ALSO refuses  : {c:12s} @ {CLAUSES[c][0]:16s} {w}")
                print()
        return
    import collections
    hist = collections.Counter()
    for b in ir:
        hist[first_refusal(b)[0]] += 1
    print(f"first-refusing-clause histogram over {len(ir)} producer bodies "
          f"(ADMITTING direction; source-side gates assumed to pass)")
    for k, v in sorted(hist.items(), key=lambda x: -x[1]):
        print(f"  {k:14s} {v:6d}   {CLAUSES[k][0]}")
    print("\nADMIT list:")
    for b in ir:
        if first_refusal(b)[0] == "ADMIT":
            print("   ", b.name)


if __name__ == "__main__":
    main()
