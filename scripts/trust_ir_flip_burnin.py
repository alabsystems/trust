#!/usr/bin/env python3
"""trust_ir_flip_burnin.py — the trust-ir FLIP burn-in harness.

The evidence machine any default-on decision for the trust-ir flip must pass.

Under `-Z trust-ir-lower`, `inner_optimized_mir` flips DerivedAgreed bodies to MIR
re-derived from trust-ir (compiler/rustc_mir_transform/src/trust_ir_flip.rs). This
harness compiles every corpus file TWICE at O0 `--emit=obj`:

    flip ON :  -Z trust-ir-lower                         (the flip lane active)
    flip OFF:  -Z trust-ir-lower -Z trust-ir-flip=false  (only delta = tracked option)

and compares the emitted objects:

  (a) whole-object byte equality;
  (b) where bytes differ, per-symbol address-normalized disassembly
      (objdump -d, absolute addresses dropped, `<sym+off>` targets kept — offsets are
      symbol-relative so they survive global shifts), classifying every symbol
      identical / instruction-different (operand_only vs structural);
  (c) per-file flipped-body tally from the `compiled from trust-ir` log lines
      (RUSTC_LOG=rustc_mir_transform::trust_ir_flip=info), plus FALLBACK warns.

Corpus: the exact seeded tests/ui sample selection of trust_ir_producer_scorecard.py
(imported, not copied — same filters, same rng discipline) + any `--corpus NAME=PATH`
single-file corpora (default: the realcode corpora).

Compile shape (both sides identical): O0, no debuginfo, `--crate-type lib
-C link-dead-code=yes -C codegen-units=1 --emit=obj`. link-dead-code forces eager
mono-item collection so private bodies (ui files are mostly `fn main` programs)
actually reach `optimized_mir`/codegen — without it the flip never fires on a lib.

Honesty rules baked in:
  * flip-ON fails while flip-OFF succeeds  -> CRITICAL failure (loud, first-class).
  * flip-OFF fails while flip-ON succeeds  -> CRITICAL failure too (loud; weirder).
  * fails both ways                        -> excluded-with-count, out of denominator.
  * A comparison-tool error (objdump/nm) is NEVER counted as identical: the file is
    classified unexplained_difference with a "tool failure" problem.
  * bytes differ but no per-symbol text difference explains it -> unexplained.
  * Non-text sections / relocations / symbol tables are cross-checked; differences
    beyond the expected size-ripple set (__text, __compact_unwind, __eh_frame when
    instruction counts changed) -> unexplained.
  * flip_removed_dead_stores (verified benign class, wave-3): a differing symbol
    that maps to a flipped body is reclassified out of UNEXPLAINED only when the
    flip-on body PROVABLY equals flip-off minus dead stack traffic: flip-on's
    normalized instruction sequence embeds order-preservingly into flip-off's and
    every removed instruction is (a) balanced frame setup/teardown (`sub sp`/`add
    sp`), (b) a store to an sp-relative slot never loaded in EITHER body, or (c) an
    immediate mov feeding only such removed stores. The only ripple problem that
    proof may discharge is the __eh_frame relocation (type,value) sequence losing
    pairs that reference ltmp*/the verified symbols (a frameless fn drops its FDE).
    Anything failing the embedding proof stays UNEXPLAINED. This class is reported
    on its own row — never folded into byte_identical or equivalent counts.
    `--selftest` exercises the proof on hand-written fixtures with no toolchain.
  * Preflight (before any corpus work): verifies on this exact binary that (1) log
    capture does not perturb emitted bytes on either side, (2) the flip actually
    fires on a smoke file, (3) compilation is byte-deterministic across runs.

Output: <out-dir>/data.json + <out-dir>/BURNIN.md. Deterministic data body (sorted
files/histograms, no timestamps); provenance block carries trustc version + seed;
wall-clock timings live in a separate, explicitly nondeterministic `timing` block.

Usage (defaults reproduce the 2026-07-01 burn-in):
  python3 scripts/trust_ir_flip_burnin.py \
      --trustc build/aarch64-apple-darwin/stage1/bin/trustc \
      --out-dir reports/trust-ir-flip-burnin-2026-07-01 \
      --seed 20260701 --sample-size 300 --jobs 8 \
      --corpus realcode=reports/2026-06-29-honest-real-code-coverage/corpus/realcode.rs \
      --corpus realcode_no_closure_bodies=reports/trust-ir-producer-baseline-2026-07-01/corpus-variant/realcode_no_closure_bodies.rs

Self-test (no trustc/objdump needed; hand-written disasm fixtures):
  python3 scripts/trust_ir_flip_burnin.py --selftest

Author: Andrew Yates | Copyright 2026 | License: Apache-2.0 OR MIT
"""

import argparse
import collections
import concurrent.futures
import datetime
import json
import os
import platform
import re
import shutil
import subprocess
import sys
import tempfile
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from trust_ir_producer_scorecard import collect_ui_sample, guarded_compile  # same seeded corpus logic + OOM-guarded compile

# ----------------------------------------------------------------------------- constants

FLIP_LOG_FILTER = "rustc_mir_transform::trust_ir_flip=info"

# Both sides get these common flags; flip-OFF adds one tracked
# `-Z trust-ir-flip=false` option.
COMPILE_FLAGS = [
    "-Z", "trust-ir-lower",
    "-Z", "trust-verify=off",       # burn-in measures the flip, not the verifier
    "--edition", "2021",
    "--crate-type", "lib",
    "-C", "link-dead-code=yes",    # eager mono-item collection: private bodies reach codegen
    "-C", "codegen-units=1",       # one object, deterministic layout
    "-C", "opt-level=0",           # flip session gate: O0
    "-C", "debuginfo=0",           # flip session gate: no debuginfo
    "--cap-lints", "allow",
    "--emit=obj",
]

# Two seams emit a flip: `inner_optimized_mir` (runtime) and `inner_mir_for_ctfe`
# (const-eval), the latter spelled `CTFE compiled from trust-ir`. Both must parse.
# When only the runtime spelling did, every const-item flip was counted by the raw
# substring but dropped from the structured inventory, so `total_flipped_bodies`
# under-reported and a differing symbol produced by a CTFE flip could not be mapped
# back to the body that produced it.
FLIP_RE = re.compile(
    r"trust-ir-flip: (?P<seam>CTFE )?compiled from trust-ir, "
    r"did=DefId\([^~]*~\s*(?P<path>.+?)\), asserts=(?P<asserts>\d+), flipped_so_far=\d+"
)
# tracing renders the warn! as: `... FALLBACK to built MIR, did=DefId(0:4 ~ crate::f),
# reason="local type outside fragment: ()", stage="gate", fallbacks=1` — reason and
# stage are QUOTED (&str fields), did is not (Debug field).
FALLBACK_RE = re.compile(
    r"trust-ir-flip: FALLBACK to built MIR, "
    r"did=DefId\([^~]*~\s*(?P<path>.+?)\), reason=\"?(?P<reason>.*?)\"?, "
    r"stage=\"?(?P<stage>[\w-]+)\"?, fallbacks=\d+"
)

DIS_HEADER_RE = re.compile(r"^([0-9a-f]+) <(.+)>:\s*$")
DIS_SECTION_RE = re.compile(r"^Disassembly of section (.+):\s*$")
DIS_INSN_RE = re.compile(r"^\s*([0-9a-f]+):\s+(.*?)\s*$")
SEC_CONTENTS_RE = re.compile(r"^Contents of section (.+):\s*$")
RELOC_SECTION_RE = re.compile(r"^RELOCATION RECORDS FOR \[(.+)\]:\s*$")
RELOC_ROW_RE = re.compile(r"^([0-9a-f]+)\s+(\S+)\s+(\S+)\s*$")

# Sections whose raw contents legitimately ripple when instruction counts change
# (function sizes/addresses shift): text itself, unwind metadata (function addresses /
# sizes), and the LSDA (the except-table holds function-relative call-site offsets).
#
# Both object formats are named because objdump's output is otherwise identical
# enough to parse the same way, and a section vocabulary that only knows Mach-O
# does not decline on ELF — it silently routes every text change into
# `unexplained_difference`, which reads as a burn-in finding rather than as a
# harness that cannot see. ELF splits text per function
# (`.text.<mangled>` under the default function-sections), so text is matched by
# prefix rather than by equality.
SIZE_RIPPLE_SECTIONS = {
    # Mach-O
    "__TEXT,__text", "__LD,__compact_unwind", "__TEXT,__eh_frame",
    "__TEXT,__gcc_except_tab",
    # ELF
    ".text", ".eh_frame", ".eh_frame_hdr", ".gcc_except_table",
}


def is_text_section(sec):
    """Machine-code section in either object format (ELF splits it per function)."""
    return sec in ("__TEXT,__text", ".text") or sec.startswith(".text.")


def is_size_ripple_section(sec):
    return (is_text_section(sec)
            or sec in SIZE_RIPPLE_SECTIONS
            or sec.startswith(".gcc_except_table"))

# Branch mnemonics: their `<sym+off>` annotations are meaningful (branch targets are
# in __text; intra-symbol offsets are symbol-relative, so they survive global layout
# shifts). All OTHER pc-relative annotations (adrp/adr/ldr-literal data references)
# are junk under layout shifts — objdump prints "nearest preceding __text symbol +
# offset", which absorbs section-base shifts — so they are normalized to XREF; real
# target changes are still caught by the relocation (type,value) sequence and section
# content comparisons. Known resolution limit (documented): same-section addend-only
# retargeting inside one instruction is below this harness's resolution.
BRANCH_MNEMONICS = {"b", "bl", "cbz", "cbnz", "tbz", "tbnz"}

SMOKE_SRC = """\
pub fn burnin_add(a: i32, b: i32) -> i32 { a.wrapping_add(b) }
pub fn burnin_max3(a: i32, b: i32, c: i32) -> i32 {
    let m = if a > b { a } else { b };
    if m > c { m } else { c }
}
fn burnin_private(mut n: i32) -> i32 { let mut s = 0; while n > 0 { s += 1; n -= 1; } s }
// Mixed pointer-width anchors. Held here as a flip-coverage WITNESS, not as a
// fallback fixture: four successive fixtures were chosen for their gate rejection
// (a unit fn, a uniform-usize fn, then these mixed anchors when the shim still
// respelled pointer widths) and every one was absorbed by a later widening — the
// last by isize/usize becoming first-class end to end. A shape whose only job is
// to stay unsupported is a shape the producer is trying to support; the preflight
// no longer depends on one existing.
fn burnin_mixed(a: i64, b: isize) -> i64 { let _ = b; a + 1 }
fn main() { let _ = burnin_private(3); let _ = burnin_mixed(2, 3); }
"""

# ----------------------------------------------------------------------------- compile

def run_compile(trustc, src, out_obj, timeout, flip_on, capture_log=True, cwd=None):
    """One compile. Returns (exit_code_or_None_on_timeout, stderr_text, seconds)."""
    env = dict(os.environ)
    env["RUST_BACKTRACE"] = "0"
    env["RUSTC_ICE"] = "0"
    # Never let the retired ambient control become a second input when running
    # an older compiler during bisects.
    env.pop("TRUST_IR_FLIP", None)
    if capture_log:
        env["RUSTC_LOG"] = FLIP_LOG_FILTER
    else:
        env.pop("RUSTC_LOG", None)
    flip_args = [] if flip_on else ["-Z", "trust-ir-flip=false"]
    argv = [trustc, *COMPILE_FLAGS, *flip_args, "-o", out_obj, src]
    t0 = time.monotonic()
    # Trust: memory-capped, session-group-reaped compile (see `guarded_compile` in the scorecard
    # module) — ROOT-CAUSE fix for the OOM: a trait-solver-overflow torture body can no longer
    # balloon a trustc to tens of GB or orphan it on timeout.
    code, stderr = guarded_compile(argv, cwd or os.path.dirname(out_obj), env, timeout)
    if code is None:
        return None, "", time.monotonic() - t0
    return code, stderr.decode("utf-8", errors="replace"), time.monotonic() - t0


def parse_flip_log(stderr):
    """Returns (flips, fallbacks, parse_anomalies). The raw substring counts are
    cross-checked against the structured parses so a log-format drift can never
    silently zero these counts (that exact bug was caught during shakedown: the
    warn! fields are quoted, the first regex was not)."""
    flips = [{"def": m.group("path"), "asserts": int(m.group("asserts")),
              "seam": "ctfe" if m.group("seam") else "runtime"}
             for m in FLIP_RE.finditer(stderr)]
    fallbacks = [{"def": m.group("path"),
                  "reason": m.group("reason").strip().strip('"')[:200],
                  "stage": m.group("stage")}
                 for m in FALLBACK_RE.finditer(stderr)]
    anomalies = {}
    raw_flips = stderr.count("compiled from trust-ir")
    raw_fallbacks = stderr.count("FALLBACK to built MIR")
    if raw_flips != len(flips):
        anomalies["flip_lines_raw_vs_parsed"] = [raw_flips, len(flips)]
    if raw_fallbacks != len(fallbacks):
        anomalies["fallback_lines_raw_vs_parsed"] = [raw_fallbacks, len(fallbacks)]
    return flips, fallbacks, anomalies


def error_signature(code, stderr):
    if code is None:
        return "timeout"
    m = re.search(r"internal compiler error: [^\n]*", stderr)
    if m:
        return re.sub(r"\s*for DefPath.*", "", m.group(0))[:200]
    m = re.search(r"panicked at ([^\n:]+(?::\d+)*):\n([^\n]*)", stderr)
    if m:
        return f"panicked at {m.group(1)}: {m.group(2)}"[:200]
    m = re.search(r"^error(\[E\d+\])?: [^\n]*", stderr, re.MULTILINE)
    if m:
        return m.group(0)[:200]
    return f"exit={code} (no error line)"

# ----------------------------------------------------------------------------- object inspection

class ToolError(Exception):
    pass


def tool_out(argv):
    proc = subprocess.run(argv, capture_output=True, text=True, timeout=120)
    if proc.returncode != 0:
        raise ToolError(f"{' '.join(argv[:2])} exited {proc.returncode}: "
                        f"{proc.stderr.strip()[:200]}")
    return proc.stdout


def normalize_insn(text):
    """Drop absolute addresses; keep #imm operands. Branch targets keep their
    <sym+off> annotation (symbol-relative); non-branch pc-relative annotations
    (data refs) become XREF — see BRANCH_MNEMONICS comment."""
    text = re.sub(r"\s+", " ", text).strip()
    mnem = text.split(" ", 1)[0]
    if mnem in BRANCH_MNEMONICS or mnem.startswith("b."):
        text = re.sub(r"\b0x[0-9a-f]+\s+(<[^>]+>)", r"\1", text)  # "0x30 <s+0x28>" -> "<s+0x28>"
    else:
        text = re.sub(r"\b0x[0-9a-f]+\s+<[^>]+>", "XREF", text)
        text = re.sub(r"<[^>]+>", "XREF", text)
    text = re.sub(r"(?<=[\s,])0x[0-9a-f]+\b", "ADDR", text)       # bare targets ('#0x..' kept)
    return text


def parse_disassembly(obj):
    """objdump -d -> ordered {(section, start_addr): {label, lines, mnemonics}}."""
    out = tool_out(["objdump", "-d", "--no-show-raw-insn", obj])
    blocks = collections.OrderedDict()
    section, cur = None, None
    for line in out.splitlines():
        m = DIS_SECTION_RE.match(line)
        if m:
            section = m.group(1)
            cur = None
            continue
        m = DIS_HEADER_RE.match(line)
        if m and section is not None:
            start = int(m.group(1), 16)
            cur = {"label": m.group(2), "start": start, "lines": [], "mnemonics": []}
            blocks[(section, start)] = cur
            continue
        m = DIS_INSN_RE.match(line)
        if m and cur is not None:
            rel = int(m.group(1), 16) - cur["start"]
            text = normalize_insn(m.group(2))
            if not text:
                continue
            cur["lines"].append(f"+{rel:#x}: {text}")
            cur["mnemonics"].append(text.split(" ", 1)[0].split("\t", 1)[0])
    return blocks


def parse_nm(obj):
    """nm -P -> sorted [(name, type, addr_int)]."""
    out = tool_out(["nm", "-P", obj])
    syms = []
    for line in out.splitlines():
        parts = line.split()
        if len(parts) >= 3:
            try:
                addr = int(parts[2], 16)
            except ValueError:
                addr = -1
            syms.append((parts[0], parts[1], addr))
    return sorted(syms)


def parse_sections(obj):
    """objdump -s -> {section: concatenated hex content}. The printed offsets are
    flat VM addresses that shift when earlier sections change size, so only the
    byte content is compared (address column and ascii gutter stripped)."""
    out = tool_out(["objdump", "-s", obj])
    secs, cur = collections.OrderedDict(), None
    for line in out.splitlines():
        m = SEC_CONTENTS_RE.match(line)
        if m:
            cur = m.group(1)
            secs[cur] = []
        elif cur is not None and line.startswith(" "):
            hex_area = line.split("  ", 1)[0]      # ascii gutter starts after 2 spaces
            toks = hex_area.split()
            if toks and all(re.fullmatch(r"[0-9a-f]+", t) for t in toks):
                secs[cur].append("".join(toks[1:]))  # toks[0] = address column
    return {k: "".join(v) for k, v in secs.items()}


def parse_relocs(obj):
    """objdump -r -> {section: [(offset, type, value)]}."""
    out = tool_out(["objdump", "-r", obj])
    relocs, cur = collections.OrderedDict(), None
    for line in out.splitlines():
        m = RELOC_SECTION_RE.match(line)
        if m:
            cur = m.group(1)
            relocs[cur] = []
            continue
        if cur is None or line.startswith("OFFSET"):
            continue
        m = RELOC_ROW_RE.match(line.strip())
        if m:
            relocs[cur].append((m.group(1), m.group(2), m.group(3)))
    return relocs


def resolve_block_names(blocks, nm_syms):
    """Prefer real (non-ltmp) symbol-table names at a block's start address."""
    by_addr = collections.defaultdict(list)
    for name, typ, addr in nm_syms:
        by_addr[addr].append((0 if not name.startswith("ltmp") else 1, name))
    resolved = collections.OrderedDict()
    for (section, start), blk in blocks.items():
        candidates = sorted(by_addr.get(start, []))
        name = candidates[0][1] if candidates else blk["label"]
        key = (section, name)
        n = 2
        while key in resolved:  # duplicate names: disambiguate deterministically by order
            key = (section, f"{name}#{n}")
            n += 1
        resolved[key] = blk
    return resolved

# ----------------------------------------------------------------------------- flip <-> symbol mapping

def strip_synthetic_segments(def_path):
    segs = [s for s in def_path.split("::") if not s.startswith("{")]
    return segs


def def_matches_symbol(def_path, symbol):
    """Heuristic: mangled names (v0 and legacy) length-prefix identifiers, so the
    final real segment `foo` appears as e.g. `3foo`. Closures/consts match their parent."""
    segs = strip_synthetic_segments(def_path)
    if not segs:
        return False
    last = re.sub(r"\[[0-9a-f]+\]", "", segs[-1])  # crate[hash] -> crate
    return f"{len(last)}{last}" in symbol


def map_symbol_to_flip(symbol, flip_defs):
    return sorted(d["def"] for d in flip_defs if def_matches_symbol(d["def"], symbol))

# ----------------------------------------------------------------------------- dead-store-elimination proof
#
# Verified benign class `flip_removed_dead_stores` (burn-in wave-3 disposition (b) of
# reports/trust-ir-flip-burnin-2026-07-01/postwave2-full2000/UNEXPLAINED-TRIAGE.md):
# the producer's SSA lowering never materializes provably-dead stack stores, so the
# flipped body can be flip-off minus (frame setup + dead stores + the movs feeding
# them). That shape is accepted ONLY under the embedding proof below; every check is
# fail-closed — anything unparsed, unbalanced, escaped, or reachable stays UNEXPLAINED.

_LINE_PREFIX_RE = re.compile(r"^\+0x[0-9a-f]+: (?P<text>.*)$")
_FRAME_OP_RE = re.compile(r"^(?P<kind>sub|add) sp, sp, #(?P<imm>0x[0-9a-f]+|\d+)$")
_SP_STORE_RE = re.compile(
    r"^(?P<mnem>str|strb|strh|stur) (?P<reg>[wxsdbhq]\d+|wzr|xzr), "
    r"\[sp(?:, #(?P<off>-?(?:0x[0-9a-f]+|\d+)))?\]$")
_SP_STP_RE = re.compile(
    r"^stp (?P<reg1>[wxsdq]\d+|wzr|xzr), (?P<reg2>[wxsdq]\d+|wzr|xzr), "
    r"\[sp(?:, #(?P<off>-?(?:0x[0-9a-f]+|\d+)))?\]$")
_SP_LOAD_RE = re.compile(
    r"^(?P<mnem>ldr|ldrb|ldrh|ldrsb|ldrsh|ldrsw|ldur) (?P<reg>[wxsdbhq]\d+), "
    r"\[sp(?:, #(?P<off>-?(?:0x[0-9a-f]+|\d+)))?\]$")
_SP_LDP_RE = re.compile(
    r"^ldp (?P<reg1>[wxsdq]\d+), (?P<reg2>[wxsdq]\d+), "
    r"\[sp(?:, #(?P<off>-?(?:0x[0-9a-f]+|\d+)))?\]$")
# `mov w8, #0x5 ; =5` — objdump's immediate-value comment is part of the normalized text.
_IMM_MOV_RE = re.compile(
    r"^mov (?P<reg>[wx]\d+), #-?(?:0x[0-9a-f]+|\d+)(?: ; =-?\d+)?$")
_SP_MENTION_RE = re.compile(r"\b(?:sp|wsp)\b")
_GPR_RE = re.compile(r"\b[wx](\d+)\b")

_REG_BYTES = {"w": 4, "x": 8, "s": 4, "d": 8, "b": 1, "h": 2, "q": 16}


def _insn_texts(lines):
    """`+0x14: add sp, sp, #0x10` -> `add sp, sp, #0x10` (offsets shift on removal,
    so the embedding compares instruction text only; branch `<sym+off>` annotations
    stay in the text, so any branch retargeting still breaks the embedding)."""
    texts = []
    for line in lines:
        m = _LINE_PREFIX_RE.match(line)
        texts.append(m.group("text") if m else line)
    return texts


def _reg_width_bytes(reg):
    if reg in ("wzr", "xzr"):
        return 4 if reg[0] == "w" else 8
    return _REG_BYTES[reg[0]]


def _slot_range(off_str, nbytes):
    lo = int(off_str, 16) if off_str and "0x" in off_str else int(off_str or 0)
    return (lo, lo + nbytes)


def _parse_sp_store(text):
    """-> (data_regs, (lo, hi)) for a plain sp-relative store, else None.
    Writeback/post-index forms (`[sp, #-0x10]!`, `[sp], #0x10`) mutate sp and
    intentionally do NOT parse — they surface as unrecognized sp uses (fail)."""
    m = _SP_STORE_RE.match(text)
    if m:
        n = _reg_width_bytes(m.group("reg"))
        if m.group("mnem") == "strb":
            n = 1
        elif m.group("mnem") == "strh":
            n = 2
        return [m.group("reg")], _slot_range(m.group("off"), n)
    m = _SP_STP_RE.match(text)
    if m:
        n = _reg_width_bytes(m.group("reg1"))
        return [m.group("reg1"), m.group("reg2")], _slot_range(m.group("off"), 2 * n)
    return None


def _parse_sp_load(text):
    """-> (lo, hi) slot range for a plain sp-relative load, else None."""
    m = _SP_LOAD_RE.match(text)
    if m:
        n = _reg_width_bytes(m.group("reg"))
        mnem = m.group("mnem")
        if mnem in ("ldrb", "ldrsb"):
            n = 1
        elif mnem in ("ldrh", "ldrsh"):
            n = 2
        elif mnem == "ldrsw":
            n = 4
        return _slot_range(m.group("off"), n)
    m = _SP_LDP_RE.match(text)
    if m:
        n = _reg_width_bytes(m.group("reg1"))
        return _slot_range(m.group("off"), 2 * n)
    return None


def _gpr_ids(text):
    """Architectural GPR numbers mentioned (w8/x8 -> 8; zr/sp excluded)."""
    return {int(n) for n in _GPR_RE.findall(text)}


def prove_dead_store_elimination(on_lines, off_lines):
    """The embedding proof. Returns {"verified": bool, "reason": str|None,
    "removed": [insn texts]}. Sound direction only: True means flip-on ==
    flip-off minus dead stack traffic; every False is conservative."""
    on_insns = _insn_texts(on_lines)
    off_insns = _insn_texts(off_lines)

    def fail(reason):
        return {"verified": False, "reason": reason, "removed": []}

    if len(on_insns) >= len(off_insns):
        return fail("flip-on is not strictly smaller than flip-off (not a removal shape)")

    # Order-preserving embedding: greedy earliest-match is complete for the
    # subsequence test; unmatched flip-off positions are the removed set.
    i, removed_idx = 0, []
    for j, insn in enumerate(off_insns):
        if i < len(on_insns) and insn == on_insns[i]:
            i += 1
        else:
            removed_idx.append(j)
    if i != len(on_insns):
        return fail(f"flip-on does not embed into flip-off "
                    f"(first unmatched flip-on insn: {on_insns[i]!r})")

    # Classify every removed instruction; anything else is fatal.
    frame_sub, frame_add = 0, 0
    frame_removed = False
    removed_stores = {}   # off idx -> (data_regs, (lo, hi))
    removed_movs = {}     # off idx -> reg token
    for j in removed_idx:
        text = off_insns[j]
        m = _FRAME_OP_RE.match(text)
        if m:
            imm = int(m.group("imm"), 16) if "0x" in m.group("imm") else int(m.group("imm"))
            frame_removed = True
            if m.group("kind") == "sub":
                frame_sub += imm
            else:
                frame_add += imm
            continue
        st = _parse_sp_store(text)
        if st:
            removed_stores[j] = st
            continue
        if _IMM_MOV_RE.match(text):
            removed_movs[j] = _IMM_MOV_RE.match(text).group("reg")
            continue
        return fail(f"removed instruction outside the dead class: {text!r}")

    if frame_sub != frame_add:
        return fail(f"removed frame ops unbalanced: sub sp {frame_sub:#x} "
                    f"vs add sp {frame_add:#x}")

    # Every sp mention in EITHER body must be a recognized shape (frame op /
    # plain store / plain load) — otherwise a slot address may escape (e.g.
    # `add x8, sp, #0xc`) and "never loaded" cannot be proven.
    load_ranges = []
    for body, insns in (("flip-on", on_insns), ("flip-off", off_insns)):
        for text in insns:
            if not _SP_MENTION_RE.search(text):
                continue
            if _FRAME_OP_RE.match(text) or _parse_sp_store(text):
                continue
            ld = _parse_sp_load(text)
            if ld:
                load_ranges.append(ld)
                continue
            return fail(f"unrecognized sp use in {body}: {text!r} "
                        f"(cannot prove removed slots dead)")

    # Removing frame setup while flip-on still touches sp would silently
    # re-base every surviving sp-relative access.
    if frame_removed and any(_SP_MENTION_RE.search(t) for t in on_insns):
        return fail("frame setup removed but flip-on still references sp")

    # Removed-store slots must never be loaded in either body.
    for j, (_regs, (lo, hi)) in sorted(removed_stores.items()):
        for (llo, lhi) in load_ranges:
            if lo < lhi and llo < hi:
                return fail(f"removed store {off_insns[j]!r} slot [{lo:#x},{hi:#x}) "
                            f"is loaded (overlaps [{llo:#x},{lhi:#x}))")

    # A removed immediate mov's value may reach ONLY removed dead stores before
    # the register is redefined by another removed immediate mov. Any other
    # downstream mention (kept read, kept write, unknown) is fatal — this is
    # exactly the uninitialized-read / value-change hazard.
    for j, reg in sorted(removed_movs.items()):
        rid = int(reg[1:])
        for k in range(j + 1, len(off_insns)):
            if rid not in _gpr_ids(off_insns[k]):
                continue
            if k in removed_stores and any(
                    r not in ("wzr", "xzr") and r[0] in "wx" and int(r[1:]) == rid
                    for r in removed_stores[k][0]):
                continue  # the allowed use: feeding a removed dead store
            if k in removed_movs and int(removed_movs[k][1:]) == rid:
                break     # redefined by another removed immediate mov
            return fail(f"removed mov {off_insns[j]!r} value reaches "
                        f"non-dead instruction {off_insns[k]!r}")

    return {"verified": True, "reason": None,
            "removed": [off_insns[j] for j in removed_idx]}


EH_FRAME_TV_PROBLEM = "relocation (type,value) sequence mismatch in __eh_frame"


def dead_store_discharge(differing, problems, rel_on, rel_off):
    """Post-proof problem discharge. Only when EVERY differing symbol is
    dead-store-verified AND mapped to a flipped body may the __eh_frame
    (type,value) ripple be discharged — and then only if the flip-on sequence
    embeds into flip-off's and every removed pair references ltmp* or one of
    the verified symbols (a frameless fn legitimately drops its FDE). Returns
    (problems_remaining, discharged, dead_store_explained).

    Mach-O only, deliberately. The section VOCABULARY is format-aware because
    getting it wrong invents findings; this DISCHARGE is left narrow because
    getting it wrong hides them. An ELF `.eh_frame` FDE drop therefore stays
    UNEXPLAINED until the equivalent shape is validated on ELF objects — the
    conservative direction, and the one that keeps an unreviewed format from
    inheriting a proof written against another."""
    all_verified = bool(differing) and all(
        d.get("dead_store_proof", {}).get("verified") and d["mapped_flip_defs"]
        for d in differing)
    if not all_verified:
        return problems, [], False
    verified_syms = {d["symbol"] for d in differing}
    remaining, discharged = [], []
    for p in problems:
        if p == EH_FRAME_TV_PROBLEM:
            tv_on = [(t, v) for _, t, v in rel_on.get("__eh_frame", [])]
            tv_off = [(t, v) for _, t, v in rel_off.get("__eh_frame", [])]
            i, removed = 0, []
            for pair in tv_off:
                if i < len(tv_on) and pair == tv_on[i]:
                    i += 1
                else:
                    removed.append(pair)
            if (i == len(tv_on) and removed and all(
                    v.startswith("ltmp") or v in verified_syms for _, v in removed)):
                discharged.append({"problem": p,
                                   "removed_reloc_pairs": [list(r) for r in removed]})
                continue
        remaining.append(p)
    return remaining, discharged, not remaining


def classify_diff(diff):
    """File class from a deep_compare record. Fail-closed: any surviving
    problem is UNEXPLAINED; the verified dead-store class is its own row."""
    if diff["problems"]:
        return "unexplained_difference"
    if diff.get("dead_store_explained"):
        return "flip_removed_dead_stores"
    return "equivalent_instruction_different"

# ----------------------------------------------------------------------------- deep compare

def deep_compare(on_obj, off_obj, flips):
    """Both compiles succeeded, bytes differ. Returns the `diff` record."""
    problems = []
    try:
        dis_on = resolve_block_names(parse_disassembly(on_obj), parse_nm(on_obj))
        dis_off = resolve_block_names(parse_disassembly(off_obj), parse_nm(off_obj))
        nm_on = [(n, t) for n, t, _ in parse_nm(on_obj)]
        nm_off = [(n, t) for n, t, _ in parse_nm(off_obj)]
        sec_on, sec_off = parse_sections(on_obj), parse_sections(off_obj)
        rel_on, rel_off = parse_relocs(on_obj), parse_relocs(off_obj)
    except (ToolError, subprocess.TimeoutExpired, OSError) as e:
        return {"problems": [f"comparison tool failure: {e}"], "differing_symbols": [],
                "identical_symbols": 0, "sizes_changed": None, "section_diffs": [],
                "reloc_diff": None, "tool_failure": True,
                "dead_store_explained": False, "problems_discharged": []}

    if nm_on != nm_off:
        problems.append(
            f"symbol table (name,type) mismatch: only-on={sorted(set(nm_on) - set(nm_off))[:5]} "
            f"only-off={sorted(set(nm_off) - set(nm_on))[:5]}")

    keys_on, keys_off = set(dis_on), set(dis_off)
    if keys_on != keys_off:
        problems.append(
            f"disassembly block set mismatch: only-on={sorted(keys_on - keys_off)[:5]} "
            f"only-off={sorted(keys_off - keys_on)[:5]}")

    differing, identical = [], 0
    sizes_changed = keys_on != keys_off
    for key in dis_on:
        if key not in dis_off:
            continue
        a, b = dis_on[key], dis_off[key]
        if a["lines"] == b["lines"]:
            identical += 1
            continue
        if len(a["mnemonics"]) != len(b["mnemonics"]):
            sizes_changed = True
            kind = "structural"
        elif a["mnemonics"] == b["mnemonics"]:
            kind = "operand_only"
        else:
            kind = "structural"
        first_diff = []
        for la, lb in zip(a["lines"], b["lines"]):
            if la != lb:
                first_diff.append({"on": la, "off": lb})
                if len(first_diff) >= 4:
                    break
        section, symbol = key
        differing.append({
            "section": section,
            "symbol": symbol,
            "kind": kind,
            "insn_count_on": len(a["mnemonics"]),
            "insn_count_off": len(b["mnemonics"]),
            "mapped_flip_defs": map_symbol_to_flip(symbol, flips),
            "first_diff": first_diff,
            # the dead-store embedding proof runs on every differing symbol;
            # non-removal shapes fail it cheaply and keep their old class
            "dead_store_proof": prove_dead_store_elimination(a["lines"], b["lines"]),
        })
    differing.sort(key=lambda d: (d["section"], d["symbol"]))

    # Non-text sections: identical unless in the size-ripple set while sizes changed.
    section_diffs = []
    for sec in sorted(set(sec_on) | set(sec_off)):
        if sec_on.get(sec) != sec_off.get(sec):
            section_diffs.append(sec)
            if is_text_section(sec):
                continue  # covered by the disassembly comparison above
            if sizes_changed and is_size_ripple_section(sec):
                continue  # expected ripple: function sizes/addresses shifted
            problems.append(f"section {sec} contents differ"
                            + ("" if sizes_changed else " (no instruction-count change)"))

    # Relocations: (type, value) sequences must ALWAYS match; exact offsets too when
    # no instruction counts changed.
    reloc_diff = rel_on != rel_off
    for sec in sorted(set(rel_on) | set(rel_off)):
        tv_on = [(t, v) for _, t, v in rel_on.get(sec, [])]
        tv_off = [(t, v) for _, t, v in rel_off.get(sec, [])]
        if tv_on != tv_off:
            problems.append(f"relocation (type,value) sequence mismatch in {sec}")
        elif rel_on.get(sec) != rel_off.get(sec) and not sizes_changed:
            problems.append(f"relocation offsets shifted in {sec} without size change")

    if not differing and not problems:
        problems.append("object bytes differ but no text/section/reloc difference "
                        "was found — invisible delta (loud by policy)")

    problems, discharged, dead_store_explained = dead_store_discharge(
        differing, problems, rel_on, rel_off)

    return {"problems": problems, "differing_symbols": differing,
            "identical_symbols": identical, "sizes_changed": bool(sizes_changed),
            "section_diffs": section_diffs, "reloc_diff": reloc_diff,
            "tool_failure": False,
            "dead_store_explained": dead_store_explained,
            "problems_discharged": discharged}

# ----------------------------------------------------------------------------- per-file measurement

def measure_file(trustc, src, timeout, scratch):
    tmpdir = tempfile.mkdtemp(dir=scratch)
    on_obj = os.path.join(tmpdir, "on.o")
    off_obj = os.path.join(tmpdir, "off.o")
    try:
        on_code, on_log, on_secs = run_compile(trustc, src, on_obj, timeout, flip_on=True)
        off_code, off_log, off_secs = run_compile(trustc, src, off_obj, timeout, flip_on=False)
        flips, fallbacks, log_anomalies = parse_flip_log(on_log)
        off_flips, off_fallbacks, _ = parse_flip_log(off_log)

        rec = {
            "file": src,
            "flips": len(flips),
            "flip_defs": sorted(flips, key=lambda d: d["def"]),
            "fallbacks": sorted(fallbacks, key=lambda d: d["def"]),
            "on_exit": on_code, "off_exit": off_code,
            "on_secs": round(on_secs, 3), "off_secs": round(off_secs, 3),
            "off_side_flip_lines": len(off_flips) + len(off_fallbacks),  # must be 0
            "log_parse_anomalies": log_anomalies,                        # must be {}
        }

        on_ok = on_code == 0 and os.path.exists(on_obj)
        off_ok = off_code == 0 and os.path.exists(off_obj)
        if on_ok and off_ok:
            with open(on_obj, "rb") as fa, open(off_obj, "rb") as fb:
                bytes_on, bytes_off = fa.read(), fb.read()
            rec["obj_size_on"], rec["obj_size_off"] = len(bytes_on), len(bytes_off)
            if bytes_on == bytes_off:
                rec["class"] = "byte_identical"
            else:
                diff = deep_compare(on_obj, off_obj, flips)
                rec["diff"] = diff
                rec["class"] = classify_diff(diff)
        elif not on_ok and off_ok:
            rec["class"] = "critical_flip_on_failure"
            rec["error"] = error_signature(on_code, on_log)
        elif on_ok and not off_ok:
            rec["class"] = "critical_flip_off_failure"
            rec["error"] = error_signature(off_code, off_log)
        else:
            rec["class"] = ("excluded_timeout_both"
                            if on_code is None and off_code is None
                            else "excluded_compile_fail_both")
            rec["error"] = error_signature(on_code, on_log)
        return rec
    finally:
        shutil.rmtree(tmpdir, ignore_errors=True)

# ----------------------------------------------------------------------------- preflight

def preflight(trustc, scratch, timeout):
    """Prove, on THIS binary: log capture is byte-inert, the flip fires, determinism."""
    d = tempfile.mkdtemp(dir=scratch, prefix="preflight-")
    src = os.path.join(d, "burnin_smoke.rs")
    with open(src, "w") as fh:
        fh.write(SMOKE_SRC)
    objs, logs = {}, {}
    for tag, flip_on, cap in [("on_log", True, True), ("on_nolog", True, False),
                              ("on_log2", True, True),
                              ("off_log", False, True), ("off_nolog", False, False)]:
        obj = os.path.join(d, f"{tag}.o")
        code, log, _ = run_compile(trustc, src, obj, timeout, flip_on, capture_log=cap)
        if code != 0:
            raise SystemExit(f"PREFLIGHT FAILED: smoke compile {tag} exited {code}:\n{log[:500]}")
        with open(obj, "rb") as fh:
            objs[tag] = fh.read()
        logs[tag] = log
    flips, fallbacks, anomalies = parse_flip_log(logs["on_log"])
    checks = {
        "log_capture_inert_flip_on": objs["on_log"] == objs["on_nolog"],
        "log_capture_inert_flip_off": objs["off_log"] == objs["off_nolog"],
        "deterministic_across_runs": objs["on_log"] == objs["on_log2"],
        "flip_fires_on_smoke": len(flips) > 0,
        # OBSERVATION, not a gate. The check it replaces required the smoke file to
        # still contain a body the flip rejects, which made a producer improvement
        # look like a harness failure — and did, once the last such shape was
        # absorbed. What that check was really standing in for is log-format drift,
        # which `log_parse_agrees_with_raw_lines` detects without asking the
        # compiler to keep failing at something.
        "smoke_produced_a_fallback": len(fallbacks) > 0,
        # The drift detector: both regexes are cross-checked against a raw substring
        # count on every parse, so a quoting/field change that silently zeroes the
        # structured counts (the exact bug found during shakedown) fails here
        # whether or not this binary happens to emit either line kind.
        "log_parse_agrees_with_raw_lines": not anomalies,
        "log_parse_anomalies": anomalies,
        "smoke_flip_count": len(flips),
        "smoke_fallback_count": len(fallbacks),
        "flip_changes_smoke_bytes": objs["on_log"] != objs["off_log"],
    }
    shutil.rmtree(d, ignore_errors=True)
    hard = ["log_capture_inert_flip_on", "log_capture_inert_flip_off",
            "deterministic_across_runs", "flip_fires_on_smoke",
            "log_parse_agrees_with_raw_lines"]
    failed = [k for k in hard if not checks[k]]
    if failed:
        raise SystemExit(f"PREFLIGHT FAILED: {failed} — refusing to burn in. {checks}")
    return checks

# ----------------------------------------------------------------------------- aggregation

CLASS_ORDER = [
    "byte_identical", "equivalent_instruction_different", "flip_removed_dead_stores",
    "unexplained_difference",
    "critical_flip_on_failure", "critical_flip_off_failure",
    "excluded_compile_fail_both", "excluded_timeout_both",
]


def aggregate(results):
    classes = collections.Counter(r["class"] for r in results)
    compared = [r for r in results if r["class"] in
                ("byte_identical", "equivalent_instruction_different",
                 "flip_removed_dead_stores", "unexplained_difference")]
    diff_syms = [s for r in results for s in r.get("diff", {}).get("differing_symbols", [])]
    fallback_hist = collections.Counter(
        f"{f['stage']}: {f['reason']}" for r in results for f in r["fallbacks"])
    agg = {
        "files_total": len(results),
        "classes": {k: classes.get(k, 0) for k in CLASS_ORDER if classes.get(k, 0)},
        "files_compared": len(compared),
        "files_with_flips": sum(1 for r in results if r["flips"] > 0),
        "files_with_flips_and_byte_identical": sum(
            1 for r in results if r["flips"] > 0 and r["class"] == "byte_identical"),
        "total_flipped_bodies": sum(r["flips"] for r in results),
        "total_fallbacks": sum(len(r["fallbacks"]) for r in results),
        "fallback_histogram": dict(sorted(fallback_hist.items())),
        "off_side_flip_line_anomalies": sum(r["off_side_flip_lines"] for r in results),
        "log_parse_anomaly_files": sorted(
            r["file"] for r in results if r.get("log_parse_anomalies")),
        "differing_symbols_total": len(diff_syms),
        "differing_symbols_operand_only": sum(1 for s in diff_syms if s["kind"] == "operand_only"),
        "differing_symbols_structural": sum(1 for s in diff_syms if s["kind"] == "structural"),
        "differing_symbols_dead_store_verified": sum(
            1 for s in diff_syms if s.get("dead_store_proof", {}).get("verified")),
        "differing_symbols_unmapped_to_any_flip": sorted(
            s["symbol"] for s in diff_syms if not s["mapped_flip_defs"]),
        "dead_store_files": sorted(
            r["file"] for r in results if r["class"] == "flip_removed_dead_stores"),
        "unexplained_files": sorted(
            r["file"] for r in results if r["class"] == "unexplained_difference"),
        "critical_files": sorted(
            r["file"] for r in results if r["class"].startswith("critical")),
        "compile_secs_flip_on_sum": round(sum(r["on_secs"] for r in compared), 1),
        "compile_secs_flip_off_sum": round(sum(r["off_secs"] for r in compared), 1),
    }
    return agg

# ----------------------------------------------------------------------------- provenance / render

def provenance(trustc, repo, args, preflight_checks):
    ver = subprocess.run([trustc, "--version", "--verbose"],
                         capture_output=True, text=True).stdout.strip()
    objdump_ver = subprocess.run(["objdump", "--version"],
                                 capture_output=True, text=True).stdout.splitlines()
    def git(*a):
        return subprocess.run(["git", "-C", repo, *a],
                              capture_output=True, text=True).stdout.strip()
    return {
        "trustc": trustc,
        "trustc_version_verbose": ver,
        "repo_head": git("rev-parse", "HEAD"),
        "repo_describe": git("describe", "--always", "--dirty"),
        "date_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
        "host": platform.platform(),
        "objdump": objdump_ver[0] if objdump_ver else "unknown",
        "compile_flags_both_sides": " ".join(COMPILE_FLAGS),
        "flip_off_delta": "-Z trust-ir-flip=false (only difference between the two sides)",
        "rustc_log": FLIP_LOG_FILTER,
        "seed": args.seed,
        "sample_size_requested": args.sample_size,
        "timeout_per_compile_s": args.timeout,
        "jobs": args.jobs,
        "preflight": preflight_checks,
    }


def render_markdown(data):
    out = []
    p = data["provenance"]
    t = data["timing"]
    out.append("# trust-ir flip burn-in scorecard\n")
    out.append(f"trustc `{p['repo_describe']}` ({p['trustc_version_verbose'].splitlines()[0]}) "
               f"· seed {p['seed']} · sample {p['sample_size_requested']}\n")
    out.append("Both sides compile with identical flags "
               f"(`{p['compile_flags_both_sides']}`); flip-off side adds only "
               "`-Z trust-ir-flip=false`. Preflight on this binary: "
               f"`{p['preflight']}`.\n")
    total = data["overall"]
    out.append("## Headline\n")
    out.append("| metric | value |\n|---|---|")
    out.append(f"| files compared (both sides compiled) | {total['files_compared']} |")
    for k in CLASS_ORDER:
        v = total["classes"].get(k, 0)
        marker = " **<-- FAILURE CLASS**" if v and ("critical" in k or "unexplained" in k) else ""
        out.append(f"| {k} | {v}{marker} |")
    out.append(f"| total flipped bodies (flip-on side) | {total['total_flipped_bodies']} |")
    out.append(f"| files with >=1 flip | {total['files_with_flips']} "
               f"(byte-identical anyway: {total['files_with_flips_and_byte_identical']}) |")
    out.append(f"| fallback warns | {total['total_fallbacks']} |")
    out.append(f"| differing symbols | {total['differing_symbols_total']} "
               f"(operand-only {total['differing_symbols_operand_only']}, "
               f"structural {total['differing_symbols_structural']}) |")
    out.append(f"| differing symbols NOT mapped to a flipped body | "
               f"{len(total['differing_symbols_unmapped_to_any_flip'])} |")
    out.append(f"| off-side flip-line anomalies (must be 0) | "
               f"{total['off_side_flip_line_anomalies']} |")
    out.append(f"| log-parse anomaly files (must be 0) | "
               f"{len(total['log_parse_anomaly_files'])} |")
    out.append(f"| compile secs, flip on / off (sum) | "
               f"{total['compile_secs_flip_on_sum']} / {total['compile_secs_flip_off_sum']} |")
    out.append(f"| wall clock (whole run) | {t['wall_clock_secs']} s |")

    for name, corpus in data["corpora"].items():
        agg = corpus["aggregate"]
        out.append(f"\n## corpus: {name}\n")
        out.append(f"- files: {agg['files_total']}; classes: `{agg['classes']}`")
        out.append(f"- flipped bodies: {agg['total_flipped_bodies']} across "
                   f"{agg['files_with_flips']} files; fallbacks: {agg['total_fallbacks']}")
        if agg["fallback_histogram"]:
            out.append(f"- fallback histogram: {agg['fallback_histogram']}")
        out.append(f"- differing symbols: {agg['differing_symbols_total']} "
                   f"(operand-only {agg['differing_symbols_operand_only']}, "
                   f"structural {agg['differing_symbols_structural']})")
        if agg["differing_symbols_unmapped_to_any_flip"]:
            out.append(f"- **FINDING — differing symbols with no matching flipped body:** "
                       f"{agg['differing_symbols_unmapped_to_any_flip']}")
        if agg["dead_store_files"]:
            out.append(f"- verified dead-store eliminations (benign, embedding-proven; "
                       f"NOT byte-identical): {agg['dead_store_files']}")
        if agg["unexplained_files"]:
            out.append(f"- **UNEXPLAINED DIFFERENCES (burn-in failure):** "
                       f"{agg['unexplained_files']}")
        if agg["critical_files"]:
            out.append(f"- **CRITICAL (one side failed):** {agg['critical_files']}")
        # per-file rows for anything not byte-identical
        interesting = [r for r in corpus["files"]
                       if r["class"] not in ("byte_identical", "excluded_compile_fail_both",
                                             "excluded_timeout_both")]
        if interesting:
            out.append("\n| file | class | flips | differing symbols |")
            out.append("|---|---|---|---|")
            for r in interesting:
                syms = "; ".join(
                    f"{s['symbol']} ({s['kind']}, {s['insn_count_on']}/{s['insn_count_off']} insns"
                    + (", dead-store-verified"
                       if s.get("dead_store_proof", {}).get("verified") else "")
                    + (f", flip: {s['mapped_flip_defs'][0]}" if s["mapped_flip_defs"]
                       else ", UNMAPPED") + ")"
                    for s in r.get("diff", {}).get("differing_symbols", [])) or "-"
                out.append(f"| {r['file']} | {r['class']} | {r['flips']} | {syms} |")
    out.append("\n(Per-file rows, per-symbol diffs and full provenance: data.json.)\n")
    return "\n".join(out)

# ----------------------------------------------------------------------------- selftest
#
# Preflight-independent unit tests for the flip_removed_dead_stores proof: pure
# hand-written disasm fixtures, no trustc / objdump / corpus. The positive fixture
# is the REAL normalized shape of tests/ui/nll/borrow-use-issue-46875.rs `int`
# (the postwave2 UNEXPLAINED singleton), captured from this harness's own
# parse_disassembly on the reproduced objects (2026-07-02, stage1 @ 2b4962d0a0).

SELFTEST_INT_SYM = "__RNvCs8OW5DlcCxaQ_22borrow_use_issue_468753int"

SELFTEST_ON_LINES = ["+0x0: ret"]

SELFTEST_OFF_LINES = [
    "+0x0: sub sp, sp, #0x10",
    "+0x4: mov w8, #0x5 ; =5",
    "+0x8: str w8, [sp, #0xc]",
    "+0xc: mov w8, #0x7 ; =7",
    "+0x10: str w8, [sp, #0xc]",
    "+0x14: add sp, sp, #0x10",
    "+0x18: ret",
]

# __eh_frame reloc shape (trimmed from the real objects): flip-off carries the
# FDE pair for `int`; the frameless flip-on body drops exactly that pair.
SELFTEST_REL_OFF = {"__eh_frame": [
    ("0000001c", "ARM64_RELOC_SUBTRACTOR", "ltmp7"),
    ("0000001c", "ARM64_RELOC_UNSIGNED", "__RNvCs8OW5DlcCxaQ_22borrow_use_issue_468754main"),
    ("000000b0", "ARM64_RELOC_SUBTRACTOR", "ltmp7"),
    ("000000b0", "ARM64_RELOC_UNSIGNED", SELFTEST_INT_SYM),
    ("00000263", "ARM64_RELOC_POINTER_TO_GOT", "_rust_eh_personality"),
]}
SELFTEST_REL_ON = {"__eh_frame": [
    ("0000001c", "ARM64_RELOC_SUBTRACTOR", "ltmp7"),
    ("0000001c", "ARM64_RELOC_UNSIGNED", "__RNvCs8OW5DlcCxaQ_22borrow_use_issue_468754main"),
    ("00000243", "ARM64_RELOC_POINTER_TO_GOT", "_rust_eh_personality"),
]}


def _selftest_diff(on_lines, off_lines, problems, rel_on, rel_off,
                   symbol=SELFTEST_INT_SYM, mapped=("borrow_use_issue_46875[7e17]::int",)):
    """Assemble a deep_compare-shaped record from fixture lines, running the
    same proof + discharge + classification code paths as the harness."""
    differing = [{
        "section": "__TEXT,__text", "symbol": symbol, "kind": "structural",
        "insn_count_on": len(on_lines), "insn_count_off": len(off_lines),
        "mapped_flip_defs": list(mapped), "first_diff": [],
        "dead_store_proof": prove_dead_store_elimination(on_lines, off_lines),
    }]
    remaining, discharged, explained = dead_store_discharge(
        differing, list(problems), rel_on, rel_off)
    return {"problems": remaining, "differing_symbols": differing,
            "identical_symbols": 0, "sizes_changed": True, "section_diffs": [],
            "reloc_diff": True, "tool_failure": False,
            "dead_store_explained": explained, "problems_discharged": discharged}


def run_selftest():
    failures = []

    def check(name, cond, detail=""):
        status = "PASS" if cond else "FAIL"
        print(f"  [{status}] {name}" + (f" — {detail}" if detail and not cond else ""))
        if not cond:
            failures.append(name)

    print("selftest: flip_removed_dead_stores proof fixtures (no toolchain needed)")

    # --- positive: the real borrow-use-issue-46875 singleton shape ------------
    proof = prove_dead_store_elimination(SELFTEST_ON_LINES, SELFTEST_OFF_LINES)
    check("positive: real 7->1 dead-store collapse verifies", proof["verified"],
          str(proof["reason"]))
    check("positive: exactly the 6 dead insns removed",
          proof["removed"] == [_insn_texts(SELFTEST_OFF_LINES)[j] for j in range(6)],
          str(proof["removed"]))
    diff = _selftest_diff(SELFTEST_ON_LINES, SELFTEST_OFF_LINES,
                          [EH_FRAME_TV_PROBLEM], SELFTEST_REL_ON, SELFTEST_REL_OFF)
    check("positive: eh_frame FDE-drop problem discharged",
          not diff["problems"] and len(diff["problems_discharged"]) == 1,
          str(diff["problems"]))
    check("positive: classifies flip_removed_dead_stores (not byte_identical, "
          "not unexplained)", classify_diff(diff) == "flip_removed_dead_stores",
          classify_diff(diff))

    # --- negative: VALUE-CHANGING diff must stay UNEXPLAINED ------------------
    # flip-off stores 5 then loads it back; flip-on drops the store: the load
    # now reads junk. The slot IS loaded -> the "never loaded" leg must fail.
    neg_off = ["+0x0: sub sp, sp, #0x10", "+0x4: mov w8, #0x5 ; =5",
               "+0x8: str w8, [sp, #0xc]", "+0xc: ldr w0, [sp, #0xc]",
               "+0x10: add sp, sp, #0x10", "+0x14: ret"]
    neg_on = ["+0x0: sub sp, sp, #0x10", "+0x4: ldr w0, [sp, #0xc]",
              "+0x8: add sp, sp, #0x10", "+0xc: ret"]
    proof = prove_dead_store_elimination(neg_on, neg_off)
    check("negative(value-changing, slot loaded): proof fails", not proof["verified"])
    diff = _selftest_diff(neg_on, neg_off, [EH_FRAME_TV_PROBLEM],
                          SELFTEST_REL_ON, SELFTEST_REL_OFF)
    check("negative(value-changing, slot loaded): stays unexplained_difference",
          classify_diff(diff) == "unexplained_difference", classify_diff(diff))

    # value flows into a KEPT instruction (uninitialized-read hazard).
    neg_off = ["+0x0: sub sp, sp, #0x10", "+0x4: mov w8, #0x5 ; =5",
               "+0x8: str w8, [sp, #0xc]", "+0xc: mov w0, w8",
               "+0x10: add sp, sp, #0x10", "+0x14: ret"]
    neg_on = ["+0x0: sub sp, sp, #0x10", "+0x4: mov w0, w8",
              "+0x8: add sp, sp, #0x10", "+0xc: ret"]
    proof = prove_dead_store_elimination(neg_on, neg_off)
    check("negative(mov value reaches kept insn): proof fails", not proof["verified"])

    # changed immediate (5 -> 6): embedding must fail, class must stay unexplained.
    neg_on = ["+0x0: sub sp, sp, #0x10", "+0x4: mov w8, #0x6 ; =6",
              "+0x8: str w8, [sp, #0xc]", "+0xc: add sp, sp, #0x10", "+0x10: ret"]
    proof = prove_dead_store_elimination(neg_on, SELFTEST_OFF_LINES)
    check("negative(changed immediate): embedding fails", not proof["verified"])
    diff = _selftest_diff(neg_on, SELFTEST_OFF_LINES, [EH_FRAME_TV_PROBLEM],
                          SELFTEST_REL_ON, SELFTEST_REL_OFF)
    check("negative(changed immediate): stays unexplained_difference",
          classify_diff(diff) == "unexplained_difference", classify_diff(diff))

    # frame removed while flip-on still references sp: re-based accesses, fatal.
    neg_on = ["+0x0: str w8, [sp, #0xc]", "+0x4: ret"]
    proof = prove_dead_store_elimination(neg_on, SELFTEST_OFF_LINES)
    check("negative(frame removed, sp still used in flip-on): proof fails",
          not proof["verified"])

    # removed instruction outside the dead class (a call).
    neg_off = SELFTEST_OFF_LINES[:1] + ["+0x4: bl XREF"] + SELFTEST_OFF_LINES[1:]
    proof = prove_dead_store_elimination(SELFTEST_ON_LINES, neg_off)
    check("negative(removed call): proof fails", not proof["verified"])

    # unbalanced removed frame ops.
    neg_off = ["+0x0: sub sp, sp, #0x10", "+0x4: ret"]
    proof = prove_dead_store_elimination(["+0x0: ret"], neg_off)
    check("negative(unbalanced frame ops): proof fails", not proof["verified"])

    # sp-address escape (`add x8, sp, #0xc`) blocks the deadness proof.
    neg_off = ["+0x0: sub sp, sp, #0x10", "+0x4: mov w8, #0x5 ; =5",
               "+0x8: str w8, [sp, #0xc]", "+0xc: add x9, sp, #0xc",
               "+0x10: add sp, sp, #0x10", "+0x14: ret"]
    neg_on = ["+0x0: sub sp, sp, #0x10", "+0x4: add x9, sp, #0xc",
              "+0x8: add sp, sp, #0x10", "+0xc: ret"]
    proof = prove_dead_store_elimination(neg_on, neg_off)
    check("negative(sp address escape): proof fails", not proof["verified"])

    # --- discharge is narrow: only the __eh_frame FDE-drop for verified syms --
    rel_off_bad = {"__eh_frame": SELFTEST_REL_ON["__eh_frame"] + [
        ("000000d0", "ARM64_RELOC_SUBTRACTOR", "ltmp7"),
        ("000000d0", "ARM64_RELOC_UNSIGNED", "__some_unrelated_function"),
    ]}
    diff = _selftest_diff(SELFTEST_ON_LINES, SELFTEST_OFF_LINES,
                          [EH_FRAME_TV_PROBLEM], SELFTEST_REL_ON, rel_off_bad)
    check("negative(reloc drop names foreign symbol): stays unexplained_difference",
          classify_diff(diff) == "unexplained_difference", classify_diff(diff))

    diff = _selftest_diff(SELFTEST_ON_LINES, SELFTEST_OFF_LINES,
                          [EH_FRAME_TV_PROBLEM, "section __DATA,__data contents differ"],
                          SELFTEST_REL_ON, SELFTEST_REL_OFF)
    check("negative(non-eh_frame problem survives): stays unexplained_difference",
          classify_diff(diff) == "unexplained_difference", classify_diff(diff))

    diff = _selftest_diff(SELFTEST_ON_LINES, SELFTEST_OFF_LINES,
                          [EH_FRAME_TV_PROBLEM], SELFTEST_REL_ON, SELFTEST_REL_OFF,
                          mapped=())
    check("negative(symbol unmapped to any flipped body): stays unexplained_difference",
          classify_diff(diff) == "unexplained_difference", classify_diff(diff))

    # --- regression: the preexisting equivalent class is untouched ------------
    # realcode-like same-count operand swap (registers renumbered): not a removal
    # shape -> proof fails cheaply; problems empty -> class stays equivalent.
    eq_on = ["+0x0: ldur w9, [x29, #-0x8]", "+0x4: ldur w8, [x29, #-0x4]", "+0x8: ret"]
    eq_off = ["+0x0: ldur w8, [x29, #-0x4]", "+0x4: ldur w9, [x29, #-0x8]", "+0x8: ret"]
    proof = prove_dead_store_elimination(eq_on, eq_off)
    check("regression(operand-only swap): proof declines (not a removal shape)",
          not proof["verified"])
    diff = _selftest_diff(eq_on, eq_off, [], SELFTEST_REL_ON, SELFTEST_REL_ON)
    check("regression(operand-only swap, no problems): stays "
          "equivalent_instruction_different",
          classify_diff(diff) == "equivalent_instruction_different", classify_diff(diff))

    print(f"selftest: {'FAIL — ' + str(failures) if failures else 'all checks passed'}")
    return 1 if failures else 0

# ----------------------------------------------------------------------------- main

def main():
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--trustc", help="required unless --selftest")
    ap.add_argument("--repo", default=os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
    ap.add_argument("--out-dir", help="required unless --selftest")
    ap.add_argument("--seed", type=int, default=20260701)
    ap.add_argument("--sample-size", type=int, default=300,
                    help="seeded ui-sample size; 0 = FULL population (all eligible)")
    ap.add_argument("--jobs", type=int, default=8)
    ap.add_argument("--timeout", type=int, default=60)
    ap.add_argument("--no-ui-sample", action="store_true")
    ap.add_argument("--corpus", action="append", default=[],
                    metavar="NAME=PATH", help="extra single-file corpus (repeatable)")
    ap.add_argument("--scratch", default=None)
    ap.add_argument("--selftest", action="store_true",
                    help="run the built-in dead-store-proof fixture tests and exit "
                         "(no trustc / objdump / corpus needed)")
    args = ap.parse_args()

    if args.selftest:
        return run_selftest()
    if not args.trustc or not args.out_dir:
        ap.error("--trustc and --out-dir are required (unless --selftest)")

    trustc = os.path.abspath(args.trustc)
    repo = os.path.abspath(args.repo)
    os.makedirs(args.out_dir, exist_ok=True)
    scratch = args.scratch or tempfile.mkdtemp(prefix="trust-ir-flip-burnin-")
    os.makedirs(scratch, exist_ok=True)
    t_start = time.monotonic()

    print("preflight: log-capture inertness / flip liveness / determinism ...", flush=True)
    checks = preflight(trustc, scratch, args.timeout)
    print(f"preflight OK: {checks}", flush=True)

    corpora = []
    for spec in args.corpus:
        name, _, path = spec.partition("=")
        corpora.append((name, [os.path.abspath(path)], None))
    if not args.no_ui_sample:
        sample, sample_meta = collect_ui_sample(repo, args.seed, args.sample_size)
        corpora.append(("ui_sample", sample, sample_meta))

    data = {
        "schema": "trust.trust-ir.flip-burnin.v2",  # v2: + flip_removed_dead_stores class
        "provenance": provenance(trustc, repo, args, checks),
        "corpora": {},
    }
    all_results = []
    for name, files, meta in corpora:
        print(f"[{name}] burning in {len(files)} file(s), 2 compiles each, "
              f"jobs={args.jobs} ...", flush=True)
        results = []
        with concurrent.futures.ThreadPoolExecutor(max_workers=args.jobs) as ex:
            futs = [ex.submit(measure_file, trustc, f, args.timeout, scratch) for f in files]
            for i, fut in enumerate(concurrent.futures.as_completed(futs)):
                results.append(fut.result())
                if (i + 1) % 50 == 0:
                    print(f"  {i + 1}/{len(files)}", flush=True)
        results.sort(key=lambda r: r["file"])
        for r in results:
            r["file"] = os.path.relpath(r["file"], repo)
        data["corpora"][name] = {
            "sample_meta": meta,
            "aggregate": aggregate(results),
            "files": results,
        }
        all_results.extend(results)
        print(f"[{name}] {data['corpora'][name]['aggregate']['classes']}", flush=True)

    data["overall"] = aggregate(all_results)
    data["timing"] = {
        "_note": "nondeterministic block; excluded from reproducibility claims",
        "wall_clock_secs": round(time.monotonic() - t_start, 1),
        "compile_secs_flip_on_sum": data["overall"]["compile_secs_flip_on_sum"],
        "compile_secs_flip_off_sum": data["overall"]["compile_secs_flip_off_sum"],
    }

    with open(os.path.join(args.out_dir, "data.json"), "w") as fh:
        json.dump(data, fh, indent=1)
    with open(os.path.join(args.out_dir, "BURNIN.md"), "w") as fh:
        fh.write(render_markdown(data))
    shutil.rmtree(scratch, ignore_errors=True)

    o = data["overall"]
    print(f"\nBURN-IN: {o['files_compared']} compared | "
          f"{o['classes'].get('byte_identical', 0)} byte-identical | "
          f"{o['classes'].get('equivalent_instruction_different', 0)} equivalent | "
          f"{o['classes'].get('flip_removed_dead_stores', 0)} dead-store-verified | "
          f"{o['classes'].get('unexplained_difference', 0)} UNEXPLAINED | "
          f"{o['classes'].get('critical_flip_on_failure', 0) + o['classes'].get('critical_flip_off_failure', 0)} CRITICAL | "
          f"{o['total_flipped_bodies']} flipped bodies | "
          f"{o['total_fallbacks']} fallbacks")
    print(f"wrote {args.out_dir}/data.json and {args.out_dir}/BURNIN.md")
    failures = (o["classes"].get("unexplained_difference", 0)
                + o["classes"].get("critical_flip_on_failure", 0)
                + o["classes"].get("critical_flip_off_failure", 0))
    # A log-format drift zeroes the structured flip counts, which are what map a
    # differing symbol back to a flipped body. Reporting `0 flipped bodies, 0
    # unexplained` from a run whose parser went blind is the one way this harness
    # could publish a clean scorecard for a lane it never observed.
    if o["log_parse_anomaly_files"]:
        print(f"LOG PARSE DRIFT on {len(o['log_parse_anomaly_files'])} file(s): "
              f"{o['log_parse_anomaly_files'][:5]} — flip counts are not trustworthy")
        failures += len(o["log_parse_anomaly_files"])
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
