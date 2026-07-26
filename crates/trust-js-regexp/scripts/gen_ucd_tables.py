#!/usr/bin/env python3
# trust-js-regexp: UCD table generator.
#
# Generates the crate's src/generated/*.rs Unicode tables from pinned
# Unicode Character Database 16.0.0 source files (the Unicode version of the
# ES2025 reference engines we differentially test against: Node v24.5.0 ships
# ICU with Unicode 16.0 per process.versions.unicode).
#
# Provenance (all retrieved 2026-07-21 over HTTPS):
#   https://unicode.org/Public/16.0.0/ucd/UnicodeData.txt
#   https://unicode.org/Public/16.0.0/ucd/CaseFolding.txt
#   https://unicode.org/Public/16.0.0/ucd/SpecialCasing.txt
#   https://unicode.org/Public/16.0.0/ucd/DerivedCoreProperties.txt
#   https://unicode.org/Public/16.0.0/ucd/PropList.txt
#   https://unicode.org/Public/16.0.0/ucd/Scripts.txt
#   https://unicode.org/Public/16.0.0/ucd/ScriptExtensions.txt
#   https://unicode.org/Public/16.0.0/ucd/PropertyValueAliases.txt
#   https://unicode.org/Public/16.0.0/ucd/PropertyAliases.txt
#   https://unicode.org/Public/16.0.0/ucd/DerivedNormalizationProps.txt
#   https://unicode.org/Public/16.0.0/ucd/emoji/emoji-data.txt
#   https://unicode.org/Public/emoji/16.0/emoji-sequences.txt
#   https://unicode.org/Public/emoji/16.0/emoji-zwj-sequences.txt
# SHA-256 of the exact inputs used for the committed tables are recorded in
# src/generated/mod.rs.
#
# NOTE: trust-js-parse (same faithful-tier engine family) carries its own,
# independently generated ID_Start/ID_Continue tables; that crate is frozen
# and its tables are private, so this crate regenerates everything it needs.
# The duplication is known and flagged for a future consolidation pass.
#
# Usage: python3 gen_ucd_tables.py <ucd-dir> <out-dir>
#
# Author: Andrew Yates
# Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0

import hashlib
import os
import sys
from collections import defaultdict

UCD, OUT = sys.argv[1], sys.argv[2]
MAX_CP = 0x10FFFF


def lines(name):
    with open(os.path.join(UCD, name), encoding="utf-8") as f:
        for raw in f:
            line = raw.split("#", 1)[0].strip()
            if line:
                yield line


def sha256(name):
    with open(os.path.join(UCD, name), "rb") as f:
        return hashlib.sha256(f.read()).hexdigest()


def parse_cps(field):
    """'0041..005A' -> (0x41, 0x5A); '0041' -> (0x41, 0x41)."""
    if ".." in field:
        a, b = field.split("..")
        return int(a, 16), int(b, 16)
    v = int(field, 16)
    return v, v


def merge(ranges):
    out = []
    for a, b in sorted(ranges):
        if out and a <= out[-1][1] + 1:
            out[-1] = (out[-1][0], max(out[-1][1], b))
        else:
            out.append((a, b))
    return out


def complement(ranges, lo=0, hi=MAX_CP):
    out, cur = [], lo
    for a, b in merge(ranges):
        if a > cur:
            out.append((cur, a - 1))
        cur = max(cur, b + 1)
    if cur <= hi:
        out.append((cur, hi))
    return out


# --------------------------------------------------------------------------
# UnicodeData.txt: general category, Bidi_Mirrored, simple uppercase.
# --------------------------------------------------------------------------
gc_ranges = defaultdict(list)
bidi_mirrored = []
simple_upper = {}
assigned = []

pending_first = None
for line in lines("UnicodeData.txt"):
    f = line.split(";")
    cp = int(f[0], 16)
    name, gc = f[1], f[2]
    if name.endswith(", First>"):
        pending_first = (cp, gc)
        continue
    if name.endswith(", Last>"):
        a, g = pending_first
        assert g == gc
        gc_ranges[gc].append((a, cp))
        assigned.append((a, cp))
        pending_first = None
        continue
    gc_ranges[gc].append((cp, cp))
    assigned.append((cp, cp))
    if f[9] == "Y":
        bidi_mirrored.append((cp, cp))
    if f[12]:
        simple_upper[cp] = int(f[12], 16)

gc_ranges["Cn"] = complement(assigned)

GC_GROUPS = {
    "L": ["Lu", "Ll", "Lt", "Lm", "Lo"],
    "LC": ["Lu", "Ll", "Lt"],
    "M": ["Mn", "Mc", "Me"],
    "N": ["Nd", "Nl", "No"],
    "P": ["Pc", "Pd", "Ps", "Pe", "Pi", "Pf", "Po"],
    "S": ["Sm", "Sc", "Sk", "So"],
    "Z": ["Zs", "Zl", "Zp"],
    "C": ["Cc", "Cf", "Cn", "Co", "Cs"],
}
for grp, members in GC_GROUPS.items():
    gc_ranges[grp] = [r for m in members for r in gc_ranges[m]]

# --------------------------------------------------------------------------
# SpecialCasing.txt: unconditional entries (conditions field empty).
# Entry format: code; lower; title; upper; (conditions;)? # comment
# --------------------------------------------------------------------------
special_upper = {}
for line in lines("SpecialCasing.txt"):
    f = [x.strip() for x in line.split(";")]
    if len(f) >= 5 and f[4]:
        continue  # conditional (locale/context): Default Case Conversion of a
        # single-char string never satisfies these -> skip
    cp = int(f[0], 16)
    special_upper[cp] = [int(x, 16) for x in f[3].split()] if f[3] else [cp]

# Non-unicode-mode Canonicalize (ES2025 22.2.2.9.1 step 2): full Unicode
# Default Case Conversion toUppercase of the single code point; results that
# are not exactly one UTF-16 code unit are rejected (the char canonicalizes
# to itself). The final ASCII asymmetry rule (ch >= 128 && cu < 128 -> ch)
# is applied at runtime, NOT baked into this table.
canon_nonu = {}
for cp in range(0x10000):
    if cp in special_upper:
        up = special_upper[cp]
        u = up[0] if len(up) == 1 else cp
    else:
        u = simple_upper.get(cp, cp)
    if u > 0xFFFF:
        u = cp
    if u != cp:
        canon_nonu[cp] = u

# --------------------------------------------------------------------------
# CaseFolding.txt: simple case folding scf (status C and S).
# --------------------------------------------------------------------------
scf = {}
for line in lines("CaseFolding.txt"):
    f = [x.strip() for x in line.split(";")]
    if f[1] in ("C", "S"):
        cp, target = int(f[0], 16), int(f[2], 16)
        if target != cp:
            scf[cp] = target


def to_segments(mapping):
    """Compress {cp: target} into (start, end, delta, stride) runs."""
    items = sorted(mapping.items())
    segs = []
    i = 0
    while i < len(items):
        start, tgt = items[i]
        delta = tgt - start
        # try stride 2 first if the immediate successor is start+2 with same
        # delta and start+1 is not mapped with the same delta
        j = i + 1
        stride = 1
        if j < len(items) and items[j][0] == start + 2 and items[j][1] - items[j][0] == delta:
            if not (items[j - 1][0] + 1 in mapping and mapping[start + 1] - (start + 1) == delta):
                stride = 2
        end = start
        while j < len(items) and items[j][0] == end + stride and items[j][1] - items[j][0] == delta:
            end = items[j][0]
            j += 1
        segs.append((start, end, delta, stride))
        i = j
    return segs


# --------------------------------------------------------------------------
# Range-valued property files.
# --------------------------------------------------------------------------
def ranges_from(name, wanted):
    got = defaultdict(list)
    for line in lines(name):
        f = [x.strip() for x in line.split(";")]
        if len(f) < 2 or f[1] not in wanted:
            continue
        got[f[1]].append(parse_cps(f[0]))
    return got

CORE = ranges_from("DerivedCoreProperties.txt", {
    "Alphabetic", "Case_Ignorable", "Cased", "Changes_When_Casefolded",
    "Changes_When_Casemapped", "Changes_When_Lowercased",
    "Changes_When_Titlecased", "Changes_When_Uppercased",
    "Default_Ignorable_Code_Point", "Grapheme_Base", "Grapheme_Extend",
    "ID_Continue", "ID_Start", "Lowercase", "Math", "Uppercase",
    "XID_Continue", "XID_Start",
})
PLIST = ranges_from("PropList.txt", {
    "ASCII_Hex_Digit", "Bidi_Control", "Dash", "Deprecated", "Diacritic",
    "Extender", "Hex_Digit", "IDS_Binary_Operator", "IDS_Trinary_Operator",
    "Ideographic", "Join_Control", "Logical_Order_Exception",
    "Noncharacter_Code_Point", "Pattern_Syntax", "Pattern_White_Space",
    "Quotation_Mark", "Radical", "Regional_Indicator", "Sentence_Terminal",
    "Soft_Dotted", "Terminal_Punctuation", "Unified_Ideograph",
    "Variation_Selector", "White_Space",
})
NORM = ranges_from("DerivedNormalizationProps.txt", {"Changes_When_NFKC_Casefolded"})
EMOJI = ranges_from("emoji-data.txt", {
    "Emoji", "Emoji_Presentation", "Emoji_Modifier", "Emoji_Modifier_Base",
    "Emoji_Component", "Extended_Pictographic",
})

BINARY = {}
for src in (CORE, PLIST, NORM, EMOJI):
    for k, v in src.items():
        BINARY[k] = merge(v)
BINARY["Bidi_Mirrored"] = merge(bidi_mirrored)
BINARY["ASCII"] = [(0x00, 0x7F)]
BINARY["Any"] = [(0x0, MAX_CP)]
BINARY["Assigned"] = merge(assigned)

# ES2025 Table 69 canonical binary property names; aliases resolved from
# PropertyAliases.txt below (the ES table mirrors the UCD alias set).
ES_BINARY_PROPS = [
    "ASCII", "ASCII_Hex_Digit", "Alphabetic", "Any", "Assigned",
    "Bidi_Control", "Bidi_Mirrored", "Case_Ignorable", "Cased",
    "Changes_When_Casefolded", "Changes_When_Casemapped",
    "Changes_When_Lowercased", "Changes_When_NFKC_Casefolded",
    "Changes_When_Titlecased", "Changes_When_Uppercased", "Dash",
    "Default_Ignorable_Code_Point", "Deprecated", "Diacritic", "Emoji",
    "Emoji_Component", "Emoji_Modifier", "Emoji_Modifier_Base",
    "Emoji_Presentation", "Extended_Pictographic", "Extender",
    "Grapheme_Base", "Grapheme_Extend", "Hex_Digit", "IDS_Binary_Operator",
    "IDS_Trinary_Operator", "ID_Continue", "ID_Start", "Ideographic",
    "Join_Control", "Logical_Order_Exception", "Lowercase", "Math",
    "Noncharacter_Code_Point", "Pattern_Syntax", "Pattern_White_Space",
    "Quotation_Mark", "Radical", "Regional_Indicator", "Sentence_Terminal",
    "Soft_Dotted", "Terminal_Punctuation", "Unified_Ideograph", "Uppercase",
    "Variation_Selector", "White_Space", "XID_Continue", "XID_Start",
]

# PropertyAliases.txt: short ; long ; other...  Build canonical -> alias set.
prop_aliases = defaultdict(set)
for line in lines("PropertyAliases.txt"):
    f = [x.strip() for x in line.split(";")]
    names = set(f)
    for canon in ES_BINARY_PROPS:
        if canon in names:
            prop_aliases[canon] |= names
for canon in ES_BINARY_PROPS:
    prop_aliases[canon].add(canon)

# --------------------------------------------------------------------------
# PropertyValueAliases.txt: gc + sc value aliases.
# --------------------------------------------------------------------------
gc_aliases = defaultdict(set)   # canonical short (Lu) -> {Lu, Uppercase_Letter, ...}
sc_aliases = defaultdict(set)   # long name (Greek) -> {Grek, Greek, ...}
for line in lines("PropertyValueAliases.txt"):
    f = [x.strip() for x in line.split(";")]
    if f[0] == "gc":
        short = f[1]
        gc_aliases[short] |= set(f[1:])
    elif f[0] == "sc":
        # sc ; Grek ; Greek [; other]
        long = f[2]
        sc_aliases[long] |= set(f[1:])

# --------------------------------------------------------------------------
# Scripts.txt + ScriptExtensions.txt.
# --------------------------------------------------------------------------
script_ranges = defaultdict(list)   # long name -> ranges
for line in lines("Scripts.txt"):
    f = [x.strip() for x in line.split(";")]
    script_ranges[f[1]].append(parse_cps(f[0]))
script_ranges["Unknown"] = complement(
    [r for v in script_ranges.values() for r in v])

short_to_long = {}
for long, al in sc_aliases.items():
    for a in al:
        short_to_long[a] = long

# scx: default is {sc(cp)}; ScriptExtensions.txt overrides.
scx_override = {}  # cp -> set(long names)
for line in lines("ScriptExtensions.txt"):
    f = [x.strip() for x in line.split(";")]
    a, b = parse_cps(f[0])
    longs = {short_to_long[s] for s in f[1].split()}
    for cp in range(a, b + 1):
        scx_override[cp] = longs

scx_ranges = {}
override_cps = merge([(cp, cp) for cp in scx_override])
for name, ranges in script_ranges.items():
    # cps whose scx defaults to their sc
    base = []
    ov = sorted(scx_override)
    ovset = scx_override
    for (a, b) in merge(ranges):
        base.append((a, b))
    # subtract override cps, then re-add those whose override contains name
    keep = []
    for (a, b) in base:
        cur = a
        for cp in range(a, b + 1):
            if cp in ovset:
                if cur <= cp - 1:
                    keep.append((cur, cp - 1))
                cur = cp + 1
        if cur <= b:
            keep.append((cur, b))
    extra = [(cp, cp) for cp, longs in ovset.items() if name in longs]
    r = merge(keep + extra)
    if r != merge(ranges):
        scx_ranges[name] = r

# --------------------------------------------------------------------------
# Emoji sequence properties (properties of strings, v-mode only).
# --------------------------------------------------------------------------
seq_chars = defaultdict(list)     # prop -> ranges of single-cp members
seq_strings = defaultdict(set)    # prop -> set of tuples (len >= 2)

def add_seq(prop, field):
    if ".." in field:
        seq_chars[prop].append(parse_cps(field))
        return
    cps = [int(x, 16) for x in field.split()]
    if len(cps) == 1:
        seq_chars[prop].append((cps[0], cps[0]))
    else:
        seq_strings[prop].add(tuple(cps))

for line in lines("emoji-sequences.txt"):
    f = [x.strip() for x in line.split(";")]
    add_seq(f[1], f[0])
for line in lines("emoji-zwj-sequences.txt"):
    f = [x.strip() for x in line.split(";")]
    add_seq(f[1], f[0])

SEQ_PROPS = ["Basic_Emoji", "Emoji_Keycap_Sequence", "RGI_Emoji_Flag_Sequence",
             "RGI_Emoji_Modifier_Sequence", "RGI_Emoji_Tag_Sequence",
             "RGI_Emoji_ZWJ_Sequence"]
for p in SEQ_PROPS:
    assert p in seq_chars or p in seq_strings, p
seq_chars["RGI_Emoji"] = [r for p in SEQ_PROPS for r in seq_chars.get(p, [])]
seq_strings["RGI_Emoji"] = set().union(*(seq_strings.get(p, set()) for p in SEQ_PROPS))

# --------------------------------------------------------------------------
# Emission.
# --------------------------------------------------------------------------
HEADER = """\
// @generated by scripts/gen_ucd_tables.py from Unicode 16.0.0 UCD data.
// Do not edit by hand; see the script header for provenance.
//
// Author: Andrew Yates
// Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0
"""


def emit_ranges(f, name, ranges):
    r = merge(ranges)
    f.write(f"pub static {name}: &[(u32, u32)] = &[\n")
    for i in range(0, len(r), 6):
        f.write("    " + " ".join(f"({a:#x}, {b:#x})," for a, b in r[i:i + 6]) + "\n")
    f.write("];\n")


def emit_segments(f, name, mapping):
    segs = to_segments(mapping)
    f.write(f"pub static {name}: &[(u32, u32, i32, u8)] = &[\n")
    for i in range(0, len(segs), 4):
        f.write("    " + " ".join(
            f"({a:#x}, {b:#x}, {d}, {s})," for a, b, d, s in segs[i:i + 4]) + "\n")
    f.write("];\n")


def rust_ident(name):
    return name.upper().replace("-", "_")


with open(os.path.join(OUT, "case_tables.rs"), "w") as f:
    f.write(HEADER)
    f.write("\n// Simple case folding (CaseFolding.txt status C+S), as\n")
    f.write("// (start, end, delta, stride) segments over cps with scf(c) != c.\n")
    emit_segments(f, "SCF", scf)
    emit_ranges(f, "SCF_SOURCES", [(c, c) for c in scf])
    f.write("\n// Non-unicode-mode Canonicalize (uppercase-single-code-unit),\n")
    f.write("// EXCLUDING the runtime ASCII asymmetry rule. BMP only.\n")
    emit_segments(f, "CANON_NONU", canon_nonu)
    emit_ranges(f, "CANON_NONU_SOURCES", [(c, c) for c in canon_nonu])

with open(os.path.join(OUT, "property_tables.rs"), "w") as f:
    f.write(HEADER)
    for p in ES_BINARY_PROPS:
        emit_ranges(f, "P_" + rust_ident(p), BINARY[p])
    f.write("\n/// ES2025 Table 69 binary property lookup (canonical names + UCD aliases,\n")
    f.write("/// case-sensitive per UMatchProperty).\n")
    f.write("pub fn binary_property(name: &str) -> Option<&'static [(u32, u32)]> {\n")
    f.write("    Some(match name {\n")
    for p in ES_BINARY_PROPS:
        pats = " | ".join(f"\"{a}\"" for a in sorted(prop_aliases[p]))
        f.write(f"        {pats} => P_{rust_ident(p)},\n")
    f.write("        _ => return None,\n    })\n}\n")

GC_ORDER = ["Lu", "Ll", "Lt", "Lm", "Lo", "Mn", "Mc", "Me", "Nd", "Nl", "No",
            "Pc", "Pd", "Ps", "Pe", "Pi", "Pf", "Po", "Sm", "Sc", "Sk", "So",
            "Zs", "Zl", "Zp", "Cc", "Cf", "Cn", "Co", "Cs",
            "L", "LC", "M", "N", "P", "S", "Z", "C"]
with open(os.path.join(OUT, "gc_tables.rs"), "w") as f:
    f.write(HEADER)
    for g in GC_ORDER:
        emit_ranges(f, "GC_" + g.upper(), gc_ranges[g])
    f.write("\n/// General_Category value lookup (short + long + extra UCD aliases).\n")
    f.write("pub fn gc_ranges(name: &str) -> Option<&'static [(u32, u32)]> {\n")
    f.write("    Some(match name {\n")
    for g in GC_ORDER:
        al = sorted(gc_aliases.get(g, set()) | {g})
        pats = " | ".join(f"\"{a}\"" for a in al)
        f.write(f"        {pats} => GC_{g.upper()},\n")
    f.write("        _ => return None,\n    })\n}\n")

with open(os.path.join(OUT, "script_tables.rs"), "w") as f:
    f.write(HEADER)
    names = sorted(script_ranges)
    for n in names:
        emit_ranges(f, "SC_" + rust_ident(n), script_ranges[n])
    for n in sorted(scx_ranges):
        emit_ranges(f, "SCX_" + rust_ident(n), scx_ranges[n])
    f.write("\n/// Script value lookup (short + long aliases, case-sensitive).\n")
    f.write("pub fn script_ranges(name: &str) -> Option<&'static [(u32, u32)]> {\n")
    f.write("    Some(match name {\n")
    for n in names:
        al = sorted(sc_aliases.get(n, set()) | {n})
        pats = " | ".join(f"\"{a}\"" for a in al)
        f.write(f"        {pats} => SC_{rust_ident(n)},\n")
    f.write("        _ => return None,\n    })\n}\n")
    f.write("\n/// Script_Extensions value lookup.\n")
    f.write("pub fn script_ext_ranges(name: &str) -> Option<&'static [(u32, u32)]> {\n")
    f.write("    Some(match name {\n")
    for n in names:
        al = sorted(sc_aliases.get(n, set()) | {n})
        pats = " | ".join(f"\"{a}\"" for a in al)
        tbl = f"SCX_{rust_ident(n)}" if n in scx_ranges else f"SC_{rust_ident(n)}"
        f.write(f"        {pats} => {tbl},\n")
    f.write("        _ => return None,\n    })\n}\n")

with open(os.path.join(OUT, "emoji_strings.rs"), "w") as f:
    f.write(HEADER)
    f.write("// Properties of strings (ES2025 Table 70), UTS #51 RGI sets.\n")
    all_props = SEQ_PROPS + ["RGI_Emoji"]
    for p in all_props:
        emit_ranges(f, "PS_" + rust_ident(p) + "_CHARS", seq_chars.get(p, []))
        strs = sorted(seq_strings.get(p, set()), key=lambda t: (-len(t), t))
        f.write(f"pub static PS_{rust_ident(p)}_STRINGS: &[&[u32]] = &[\n")
        for i in range(0, len(strs), 4):
            f.write("    " + " ".join(
                "&[" + ", ".join(f"{c:#x}" for c in t) + "]," for t in strs[i:i + 4]) + "\n")
        f.write("];\n")
    f.write("\n/// Property-of-strings lookup (no aliases per ES2025 Table 70).\n")
    f.write("pub fn string_property(name: &str)\n")
    f.write("    -> Option<(&'static [(u32, u32)], &'static [&'static [u32]])> {\n")
    f.write("    Some(match name {\n")
    for p in all_props:
        f.write(f"        \"{p}\" => (PS_{rust_ident(p)}_CHARS, PS_{rust_ident(p)}_STRINGS),\n")
    f.write("        _ => return None,\n    })\n}\n")

with open(os.path.join(OUT, "mod.rs"), "w") as f:
    f.write(HEADER)
    f.write("//! Generated Unicode 16.0.0 tables. Input SHA-256:\n")
    for name in sorted(os.listdir(UCD)):
        if name.endswith(".txt") and name != "sha256.txt":
            f.write(f"//!   {sha256(name)}  {name}\n")
    f.write("pub mod case_tables;\npub mod emoji_strings;\npub mod gc_tables;\n")
    f.write("pub mod property_tables;\npub mod script_tables;\n")

print("generated tables into", OUT)
