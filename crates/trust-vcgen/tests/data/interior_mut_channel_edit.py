# Builds the G2 interior-mutability fixtures (tests/interior_mut_channel_realmir.rs)
# from stage-1 -O3 dumps of tests/data/interior_mut_channel_bases.rs: the hand edits
# of the verifier-gaps design, Appendix C. Usage: python3 interior_mut_channel_edit.py
# <dump-dir> <fixture-out-dir>. With `--guards <dump-dir> <fixture-out-dir>` it instead
# copies the -O0 dumps of tests/data/interior_mut_channel.rs (the design's Appendix A.6
# real-MIR guards) unedited, span files made crate-relative. With `--union <O0|O3>
# <dump-dir> <fixture-out-dir>` it copies the dumps of tests/data/interior_mut_channel_union.rs
# (tests/interior_mut_channel_union_realmir.rs) unedited; only a span in that file is made
# crate-relative, so a std span keeps the path `is_trusted_std_file` reads.
# Author: Andrew Yates. License: Apache-2.0 OR MIT.
import copy, glob, json, os, sys

if sys.argv[1] == "--union":
    opt, dump, outdir = sys.argv[2], sys.argv[3], sys.argv[4]
    UNION_SRC = "crates/trust-vcgen/tests/data/interior_mut_channel_union.rs"
    copied = 0
    for p in sorted(glob.glob(os.path.join(dump, "*.json"))):
        f = json.load(open(p))
        name = f["def_path"].rsplit("::", 1)[-1]
        if not name.startswith(("must_refute_", "control_")):
            continue
        def union_respan(x):
            if isinstance(x, dict):
                if "file" in x and "line_start" in x and x["file"].endswith("/" + UNION_SRC):
                    x["file"] = UNION_SRC
                for v in x.values():
                    union_respan(v)
            elif isinstance(x, list):
                for v in x:
                    union_respan(v)
        union_respan(f)
        with open(os.path.join(outdir, "interior_mut_channel_union_%s_%s_mir.json" % (opt, name)), "w") as h:
            json.dump(f, h, indent=2)
            h.write("\n")
        copied += 1
    print("copied %d" % copied)
    sys.exit(0)

if sys.argv[1] == "--guards":
    dump, outdir = sys.argv[2], sys.argv[3]
    GUARD_SRC = "crates/trust-vcgen/tests/data/interior_mut_channel.rs"
    for p in sorted(glob.glob(os.path.join(dump, "*.json"))):
        f = json.load(open(p))
        name = f["def_path"].rsplit("::", 1)[-1]
        if not name.startswith(("must_refute_", "control_")):
            continue
        def guard_respan(x):
            if isinstance(x, dict):
                if "file" in x and "line_start" in x:
                    x["file"] = GUARD_SRC
                for v in x.values():
                    guard_respan(v)
            elif isinstance(x, list):
                for v in x:
                    guard_respan(v)
        guard_respan(f)
        with open(os.path.join(outdir, "interior_mut_channel_guard_%s_mir.json" % name), "w") as h:
            json.dump(f, h, indent=2)
            h.write("\n")
    sys.exit(0)

dump, outdir = sys.argv[1], sys.argv[2]
SRC = "crates/trust-vcgen/tests/data/interior_mut_channel_bases.rs"

def load(def_path):
    for p in glob.glob(os.path.join(dump, "*.json")):
        f = json.load(open(p))
        if f["def_path"] == "interior_mut_channel_bases::" + def_path:
            return f
    raise SystemExit("no dump for " + def_path)

def respan(x):
    if isinstance(x, dict):
        if "file" in x and "line_start" in x:
            x["file"] = SRC
        for v in x.values():
            respan(v)
    elif isinstance(x, list):
        for v in x:
            respan(v)

def save(f, name):
    respan(f)
    with open(os.path.join(outdir, "interior_mut_channel_%s_mir.json" % name), "w") as h:
        json.dump(f, h, indent=2)
        h.write("\n")

def place(local, projs=None):
    return {"local": local, "projections": projs or []}

U64 = {"Int": {"width": 64, "signed": False}}

def adt(name, fields):
    return {"Adt": {"name": name, "fields": fields, "variants": [], "disc_index_safe": False,
                    "faithful_enum_repr": None, "layout": None, "enum_layout": None,
                    "adt_kind": "Struct"}}

# The extractor's own `Cell<usize>` (local 2 of the `local_cell_callee` dump).
base = load("local_cell_callee")
CELL = base["body"]["locals"][2]["ty"]
assert CELL["Adt"]["name"] == "core::cell::Cell", CELL

def assign(dst, rvalue, span):
    return {"Assign": {"place": dst, "rvalue": rvalue, "span": span}}

# ---- C.1: synthetic_cell_interior_callee (+ &mut twin, no-call control) ----
def cell_interior(variant):
    f = copy.deepcopy(base)
    c00 = place(2, [{"Field": 0}, {"Field": 0}])
    for b in f["body"]["blocks"]:
        t = b["terminator"]
        if isinstance(t, dict) and "Call" in t:
            call = t["Call"]
            span = call["span"]
            if call["func"] == "core::cell::Cell::<usize>::new":
                b["stmts"].append(assign(c00, {"Use": call["args"][0]}, span))
                b["terminator"] = {"Goto": call["target"]}
            elif call["func"] == "core::cell::Cell::<usize>::get":
                (arg,) = call["args"]
                tmp = arg["Move"]["local"]
                # Drop the `&c` temp the getter took: only the poke's borrow stays.
                b["stmts"] = [s for s in b["stmts"]
                              if not ("Assign" in s and s["Assign"]["place"] == place(tmp))]
                b["stmts"].append(assign(call["dest"], {"Use": {"Copy": c00}}, span))
                b["terminator"] = {"Goto": call["target"]}
            elif call["func"].endswith("::poke_cell"):
                if variant == "mut":
                    for s in b["stmts"]:
                        if "Assign" in s and s["Assign"]["place"] == place(8):
                            s["Assign"]["rvalue"]["Ref"]["mutable"] = True
                    f["body"]["locals"][8]["ty"] = {"Ref": {"mutable": True, "inner": CELL}}
                elif variant == "nocall":
                    b["terminator"] = {"Goto": call["target"]}
    f["name"] = f["def_path"] = "synthetic_cell_interior_callee" + ("" if variant == "shared" else "_" + variant)
    return f

save(cell_interior("shared"), "cell_interior_callee")
save(cell_interior("mut"), "cell_interior_callee_mut")
save(cell_interior("nocall"), "cell_interior_nocall")

# ---- C.2: synthetic_shared_slice_of_cells (+ the plain `&[usize]` body as dumped) ----
plain = load("cell_slice_interior")
save(copy.deepcopy(plain), "shared_slice_plain")
f = copy.deepcopy(plain)
f["body"]["locals"][1]["ty"] = {"Ref": {"mutable": False, "inner": {"Slice": {"elem": CELL}}}}
f["body"]["locals"][19]["ty"] = {"Ref": {"mutable": False, "inner": CELL}}
edited = 0
for b in f["body"]["blocks"]:
    for s in b["stmts"]:
        a = s.get("Assign")
        if not a:
            continue
        rv = a["rvalue"]
        if "Use" in rv and "Copy" in rv["Use"]:
            p = rv["Use"]["Copy"]
            if p["local"] == 1 and p["projections"] in (["Deref", {"Index": 14}], ["Deref", {"Index": 23}]):
                p["projections"] += [{"Field": 0}, {"Field": 0}]
                edited += 1
assert edited == 2, edited
f["name"] = f["def_path"] = "synthetic_shared_slice_of_cells"
save(f, "shared_slice_of_cells")

# ---- C.3: the two holder bodies ----
for which in ("mut", "shared"):
    f = load("pv_%s_holder" % which)
    w = f["body"]["locals"][1]["ty"]["Ref"]["inner"]["Adt"]
    assert w["fields"][0][0] == "r"
    w["fields"][0][1] = {"Ref": {"mutable": False, "inner": CELL}}
    for l in (10, 11):
        f["body"]["locals"][l]["ty"] = {"Ref": {"mutable": False, "inner": CELL}}
    edited = 0
    for b in f["body"]["blocks"]:
        for s in b["stmts"]:
            a = s.get("Assign")
            if a and "Use" in a["rvalue"] and "Copy" in a["rvalue"]["Use"]:
                p = a["rvalue"]["Use"]["Copy"]
                if p["local"] in (10, 11) and p["projections"] == ["Deref"]:
                    p["projections"] += [{"Field": 0}, {"Field": 0}]
                    edited += 1
    assert edited == 2, edited
    f["name"] = f["def_path"] = "synthetic_pv_%s_holder_cell" % which
    save(f, "pv_%s_holder_cell" % which)
print("ok")
