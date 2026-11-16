#!/usr/bin/env python3
"""Honest type + loop coverage analysis over dumped VerifiableFunction JSONs.

Type coverage: a report-local syntactic Ty-constructor census. Every serialized
Adt is counted in the structural bucket, including stdlib adapter ADTs; this is
the deliberately naive constructor metric and is not a semantic grounding or
kernel-depth claim. Unsupported / Dynamic / Bv / Closure / Coroutine / FnDef /
FnPtr and malformed shapes are counted fail-closed.

Loop coverage: a report-local MIR-shape heuristic (back-edge detection + body
assignment shapes) estimates Counter / Accumulator / Iterator / Unknown.  It is
not an invocation of the verifier's classifier and must not be presented as an
exact verifier-recognition count.
"""
import json, os, sys, collections

DUMP = sys.argv[1] if len(sys.argv) > 1 else "dump"

# --- type classification --------------------------------------------------
# Secondary syntactic buckets only; kernel/grounding claims come from prove JSON.
STRUCTURAL_LEAF = {"Bool", "Unit", "Never"}

def reject_duplicate_pairs(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise ValueError(f"duplicate JSON key: {key!r}")
        result[key] = value
    return result

def reject_nonfinite(value):
    raise ValueError(f"non-finite JSON number: {value}")

# constructor key -> (is_structural, has_children_field)
def walk_ty(ty, counter, structural, failclosed):
    """ty is either a string (e.g. 'Bool') or a dict with one key."""
    if isinstance(ty, str):
        counter[ty] += 1
        if ty in ("Bool", "Unit", "Never"):
            structural[ty] += 1
        else:
            failclosed[ty] += 1
        return
    if not isinstance(ty, dict):
        counter["<unknown>"] += 1
        failclosed["<unknown>"] += 1
        return
    # A serialized Ty enum has exactly one constructor.  Empty or multi-key
    # objects are malformed and receive fail-closed credit, never omission from
    # the denominator or optimistic structural credit.
    if len(ty) != 1:
        counter["<malformed>"] += 1
        failclosed["<malformed>"] += 1
        return
    for k, v in ty.items():
        counter[k] += 1
        if k == "Int":
            structural["Int"] += 1
        elif k == "Float":
            structural["Float"] += 1
        elif k == "Tuple":
            structural["Tuple"] += 1
            for e in v:
                walk_ty(e, counter, structural, failclosed)
        elif k == "Array":
            structural["Array"] += 1
            walk_ty(v.get("elem"), counter, structural, failclosed)
        elif k == "Slice":
            structural["Slice"] += 1
            walk_ty(v.get("elem"), counter, structural, failclosed)
        elif k == "Ref":
            structural["Ref"] += 1
            walk_ty(v.get("inner"), counter, structural, failclosed)
        elif k == "RawPtr":
            structural["RawPtr"] += 1
            walk_ty(v.get("pointee"), counter, structural, failclosed)
        elif k == "Adt":
            # struct (variants empty) is structural in Phase1/4; enum structural in P4.
            structural["Adt"] += 1
            for (_, fty) in v.get("fields", []):
                walk_ty(fty, counter, structural, failclosed)
        elif k == "Datatype":
            structural["Datatype"] += 1
        elif k in ("Closure", "Coroutine"):
            failclosed[k] += 1
            for u in v.get("upvars", []):
                walk_ty(u, counter, structural, failclosed)
        elif k in ("FnDef", "FnPtr"):
            failclosed[k] += 1
        elif k == "Dynamic":
            failclosed["Dynamic"] += 1
        elif k == "Bv":
            failclosed["Bv"] += 1
        elif k == "Unsupported":
            failclosed["Unsupported"] += 1
        else:
            failclosed[k] += 1
        return

# --- loop detection from MIR ----------------------------------------------
def detect_loops(body):
    """Return list of loop-header block ids (a block that is a target of a later/equal block = back edge)."""
    blocks = body.get("blocks", [])
    succ = {}
    for b in blocks:
        bid = b["id"]
        t = b.get("terminator")
        targets = term_targets(t)
        succ[bid] = targets
    # back edge: edge u->v with v <= u (structured MIR: loop headers have lower ids)
    headers = set()
    for u, vs in succ.items():
        for v in vs:
            if v is not None and v <= u:
                headers.add(v)
    return headers, succ

def term_targets(t):
    if t is None:
        return []
    if isinstance(t, str):
        return []
    for k, v in t.items():
        if k == "Goto":
            return [v.get("target")] if isinstance(v, dict) else [v]
        if k == "SwitchInt":
            tgs = v.get("targets", [])
            out = []
            for entry in tgs:
                if isinstance(entry, list) and len(entry) == 2:
                    out.append(entry[1])
                elif isinstance(entry, int):
                    out.append(entry)
            ot = v.get("otherwise")
            if ot is not None:
                out.append(ot)
            return [x for x in out if isinstance(x, int)]
        if k == "Assert":
            return [v.get("target")]
        if k == "Call":
            tg = v.get("target")
            return [tg] if isinstance(tg, int) else []
        if k == "Drop":
            return [v.get("target")]
        if k == "Opaque":
            return v.get("targets", [])
    return []

def classify_loop(header_id, body):
    """Apply the report-local approximation over all body blocks.

    This intentionally does not claim execution-equivalence with
    trust_vcgen::classify_loop_pattern.
    """
    blocks = {b["id"]: b for b in body.get("blocks", [])}
    found_counter = found_accum = found_len = False
    for b in body.get("blocks", []):
        for stmt in b.get("stmts", []):
            if "Assign" not in stmt:
                continue
            a = stmt["Assign"]
            place = a.get("place")
            rv = a.get("rvalue")
            if not isinstance(rv, dict):
                continue
            for rk, rval in rv.items():
                if rk in ("BinaryOp", "CheckedBinaryOp") and isinstance(rval, list) and len(rval) == 3:
                    op, lhs, rhs = rval
                    if op in ("Add", "Sub") and same_place_operand(place, lhs):
                        if is_const(rhs):
                            found_counter = True
                        else:
                            found_accum = True
                if rk == "Len":
                    found_len = True
    if found_len and found_counter:
        return "Iterator"
    if found_counter:
        return "Counter"
    if found_accum:
        return "Accumulator"
    return "Unknown"

def same_place_operand(place, operand):
    if not isinstance(operand, dict):
        return False
    inner = operand.get("Copy") or operand.get("Move")
    if not isinstance(inner, dict) or not isinstance(place, dict):
        return False
    return inner.get("local") == place.get("local") and inner.get("projections") == place.get("projections")

def is_const(operand):
    return isinstance(operand, dict) and "Constant" in operand

# --- function-level: does it contain any fail-closed / unsupported node ----
def func_has_failclosed_ty(body):
    fc = collections.Counter(); st = collections.Counter(); ct = collections.Counter()
    for loc in body.get("locals", []):
        walk_ty(loc.get("ty"), ct, st, fc)
    return fc, st, ct

def func_has_unsupported_stmt(body):
    for b in body.get("blocks", []):
        for stmt in b.get("stmts", []):
            if "Unsupported" in stmt:
                return True
            # nested unsupported rvalue/operand
            s = json.dumps(stmt)
            if '"Unsupported"' in s:
                return True
        t = b.get("terminator")
        if t and isinstance(t, dict) and "Opaque" in t:
            return True
    return False

# --- main -----------------------------------------------------------------
ty_ctor = collections.Counter()
ty_structural = collections.Counter()
ty_failclosed = collections.Counter()
loop_kinds = collections.Counter()
func_count = 0
func_with_loop = 0
func_with_failclosed_ty = collections.Counter()
func_with_unsupported = 0
func_clean_types = 0
per_func = []

for fn in sorted(os.listdir(DUMP)):
    if not fn.endswith(".json"):
        continue
    with open(os.path.join(DUMP, fn), encoding="utf-8") as f:
        vf = json.load(
            f,
            object_pairs_hook=reject_duplicate_pairs,
            parse_constant=reject_nonfinite,
        )
    if not isinstance(vf, dict):
        raise ValueError(f"dump {fn} is not a JSON object")
    func_count += 1
    body = vf.get("body", {})
    if not isinstance(body, dict):
        raise ValueError(f"dump {fn} body is not a JSON object")
    fc, st, ct = func_has_failclosed_ty(body)
    for k, v in ct.items(): ty_ctor[k] += v
    for k, v in st.items(): ty_structural[k] += v
    for k, v in fc.items():
        ty_failclosed[k] += v
        func_with_failclosed_ty[k] += 1
    has_unsupported = func_has_unsupported_stmt(body)
    if has_unsupported:
        func_with_unsupported += 1
    if not fc and not has_unsupported:
        func_clean_types += 1
    headers, succ = detect_loops(body)
    fkinds = []
    if headers:
        func_with_loop += 1
        for h in headers:
            kind = classify_loop(h, body)
            loop_kinds[kind] += 1
            fkinds.append(kind)
    per_func.append({
        "name": vf.get("name"),
        "def_path": vf.get("def_path"),
        "loops": fkinds,
        "failclosed_ty": dict(fc),
        "has_unsupported_stmt": has_unsupported,
        "n_locals": len(body.get("locals", [])),
        "n_blocks": len(body.get("blocks", [])),
    })

total_ty_nodes = sum(ty_structural.values()) + sum(ty_failclosed.values())
struct_nodes = sum(ty_structural.values())
fc_nodes = sum(ty_failclosed.values())

out = {
    "n_functions": func_count,
    "type_coverage": {
        "method": "report-local-syntactic-ty-constructor-count.v1",
        "claim_boundary": "Secondary syntactic census; Adt includes stdlib adapters and is not kernel grounding/depth.",
        "total_ty_nodes": total_ty_nodes,
        "structural_nodes": struct_nodes,
        "failclosed_nodes": fc_nodes,
        "pct_structural": round(100*struct_nodes/total_ty_nodes, 1) if total_ty_nodes else 0,
        "structural_by_ctor": dict(ty_structural.most_common()),
        "failclosed_by_ctor": dict(ty_failclosed.most_common()),
    },
    "func_type_coverage": {
        "func_with_only_structural_types": func_clean_types,
        "pct_func_clean_types": round(100*func_clean_types/func_count, 1) if func_count else 0,
        "func_with_failclosed_ty_by_ctor": dict(func_with_failclosed_ty.most_common()),
        "func_with_unsupported_stmt": func_with_unsupported,
    },
    "loop_coverage": {
        "method": "report-local-mir-shape-heuristic.v1",
        "claim_boundary": "Approximation only; not an invocation of the verifier loop classifier.",
        "n_functions_with_loops": func_with_loop,
        "total_loop_headers": sum(loop_kinds.values()),
        "by_kind": dict(loop_kinds.most_common()),
        "pct_recognized": round(100*(sum(loop_kinds.values())-loop_kinds.get("Unknown",0))/sum(loop_kinds.values()),1) if sum(loop_kinds.values()) else None,
    },
    "per_func": per_func,
}
print(json.dumps(out, indent=2))
