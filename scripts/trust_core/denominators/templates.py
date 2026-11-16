#!/usr/bin/env python3
"""E0.12 denominator `templates`: trust-cg's emitted A64/x86 templates, relocation and unwind record kinds.

Design of record: docs/design/2026-09-16-trust-core-architecture.md, §5.2 Stage 0.5 ("Emitted A64 and
x86 templates, starting from 294 and 232 opcode variants [M†]" and "Relocation and unwind record
kinds", exit E0.12 "All published, each with its predicate: 0 denominators without one"). D-8
states the same numbers ("294 `AArch64Opcode` and 232 `X86Opcode` variants in `trust-cg-ir`
[M†]"; "about 232 opcode variants in trust-cg's `X86Opcode` today [M†]"). The template count is
consumed by I-TEMPLATE-LEMMA and I-DERIVATION-OWED (D-8), E1.6.1 ("Every template E1.5.1's rules
emit has a definition in `aarch64_isa.lean` ... 0 templates without a record"), K2's extrapolated
one-time check of every emitted template, E1.8.4, E2.7.2 ("schema lemmas for 100% of emitted x86
templates"), E2.12.2 (50% of emitted AArch64 templates) and E3.1.3 (100%). The record kinds are
consumed by D-9 (`reloc : Kind -> ...`, the table semantics over `Obj`), E1.5.3, E2.6.1, E2.6.3
and E2.6.7.

Everything is read from git objects: first-party/trust-cg at the commit the superproject's gitlink
names at `--rev` (default HEAD), never a working tree. The design's own trust-cg pin (its status
block names it, "trust-cg `f61c934b`") is read the same way, only to test the [M†] numbers.

THE PREDICATES (each row of docs/trust-core/denominators/templates.toml repeats its own)

Source text is lexed first: comments and the contents of string and character literals are
blanked (offsets and lines kept), and every `#[cfg(test)]` / `#[cfg(all(test, ..))]` item (a
test module, function or impl) is excluded, so no test code contributes.

  opcode variants   the variants of `pub enum AArch64Opcode` (crates/trust-cg-ir/src/inst.rs) and of
                    `pub enum X86Opcode` (crates/trust-cg-ir/src/x86_64_ops.rs), one per top-level
                    comma-separated item of the enum body. This is the design's [M†] quantity.

  emitted template  (AArch64) a variant V of AArch64Opcode for which trust-cg's code emission
                    writes instruction bytes of V's own. Concretely:
                    (categories: encoded and fixup are emitted; skipped and refused are not)
                    (1) V's default flags (`AArch64Opcode::default_flags`) do not contain
                        IS_PSEUDO: every emitter walk skips an instruction whose flags carry it
                        (the object emitter `encode_function_with_fixups_and_blocks_impl_with_sites`
                        in crates/trust-cg-codegen/src/pipeline.rs does `if inst.is_pseudo() {
                        continue; }`, which the script checks is present); and
                    (2) either the unified encoder `encode_instruction` (crates/trust-cg-codegen/src/
                        aarch64/encode.rs), an exhaustive `match inst.opcode`, has an arm naming V
                        whose body is not a bare refusal (`Err(..)`, `return Err(..)`,
                        `unreachable!`, `panic!`, `todo!`, `unimplemented!`) and does not reach
                        one for V through a nested `match inst.opcode` or a same-file helper the
                        body passes `inst` to (followed transitively, arm by arm); or the encoder
                        refuses V with `UnsupportedOpcode` and the object emitter function above
                        names `AArch64Opcode::V` (its relocation-fixup interception writes a
                        placeholder word for V plus a relocation).
                    (x86-64) a variant V of X86Opcode for which `X86Encoder::encode_instruction`
                    (crates/trust-cg-codegen/src/x86_64/encode.rs), an exhaustive `match opcode`,
                    has an arm naming V whose body is neither a bare refusal nor a bare
                    `return Ok(0)` (zero bytes), followed through nested `match opcode` and
                    same-file helpers the body passes `opcode` to, as above. The x86 object
                    emitters call this encoder for every instruction (symbol fixups are recorded
                    after encoding), so there is no interception clause. (categories: encoded
                    is emitted; zero-bytes and refused are not)
                    An AArch64 variant that `AArch64Opcode::is_pseudo()` calls encoding-free but
                    whose default flags lack IS_PSEUDO reaches the encoder and gets a constant word
                    (BRK #1 or NOP at the measured pin): it is emitted bytes and is counted, and is
                    also listed in its own row with the real variant whose word it shares.
                    An opcode variant is a template FAMILY, not one encoding: D-8(d) splits a
                    template "wherever a field changes decoding"; that finer count is recorded as
                    blocked (see its row). `X86Sse2PackedOpcode` is a compatibility alias surface
                    that maps one-for-one into X86Opcode (`to_x86_opcode`); it adds no template,
                    and the script checks that every target is an emitted X86 template.

  relocation kinds  per object format and ISA, the relocation types trust-cg's object writer for
                    that pair can serialize: the variants of the writer's type (Mach-O AArch64
                    `macho::AArch64RelocKind` restricted to the Mach-O r_type range that
                    `is_elf_only` defines - the variants above it are ELF-only fixup carriers
                    Mach-O conversion refuses, and they are recorded, with the ELF type
                    `aarch64_elf_reloc_kind` maps each to, in their own row; Mach-O x86-64
                    `macho::x86_64_reloc::X86_64RelocKind`; ELF `elf::AArch64RelocType`,
                    `X86_64RelocType`, `RiscvRelocType`; COFF the `IMAGE_REL_AMD64_*` constants of
                    coff/writer.rs), each with its raw r_type value. The writer accepts any value
                    of its type, so this is the set a producer can put in an object: an upper
                    bound on what current code paths emit (which kinds a producer reaches is a
                    dataflow question this script does not answer). Beside it, the named rows of
                    trust-cg-verify's `ObjectRelocationKind` for the same pair (the certified-
                    output inventory; a kind outside it is represented there only by the pair's
                    `*Other(raw)` row), matched to writer kinds by name.

  unwind kinds      per object format and ISA and per table family:
                    compact unwind (Mach-O `__LD,__compact_unwind`) - the mode constants
                    (`UNWIND_ARM64_MODE_*` in frame.rs, `UNWIND_X86_64_MODE_*` in x86_64/
                    pipeline.rs) that the encoder names in non-test code (for AArch64, inside
                    `encode_compact_unwind`); the flag constants beside them are listed;
                    DWARF CFI (`__eh_frame` / `.eh_frame`) - the CIE shapes, one per `DwarfCie`
                    constructor named `<isa>_<darwin|elf>[_with_eh]` with its augmentation
                    string; the CFA instruction opcodes (`DW_CFA_*` constants of the one CFI
                    emitter, dwarf_cfi.rs, shared by both ISAs and both formats) and pointer
                    encodings (`DW_EH_PE_*` constants there);
                    LSDA (`__gcc_except_tab` / `.gcc_except_table`, exception_handling.rs, shared by
                    both ISAs) - the `DwEhPe` encodings and the record structs;
                    SEH (COFF `.pdata`/`.xdata`, x86-64 only) - the `UWOP_*` unwind codes of
                    x86_64/pipeline.rs.
                    The in-process JIT's tables (jit.rs, jit_unwind.rs) are not an object format
                    and are outside these rows.

Usage (the checkers need Python 3.11+, common.py's floor; macOS's /usr/bin/python3 is 3.9):
    python3.14 scripts/trust_core/denominators/templates.py            # measure and print
    python3.14 scripts/trust_core/denominators/templates.py --list     # also print every variant
    python3.14 scripts/trust_core/denominators/templates.py --write    # rewrite the TOML record
    python3.14 scripts/trust_core/denominators/templates.py --check    # the TOML equals a re-measurement
    python3.14 scripts/trust_core/denominators/templates.py --self-test  # also refute the classifier:
        five in-memory source mutations (a helper's nested match dropping a variant, a bare refusal,
        IS_PSEUDO, removing the fixup interception, an x86 helper's catch-all) must each flip exactly
        the one variant they target

Exit codes: 0 measured and (with --check) the record matches; 1 a finding or a mismatch;
2 the superproject or the trust-cg objects cannot be read.

Author: Andrew Yates <andrewyates.name@gmail.com>
Copyright 2026 Andrew Yates | License: Apache-2.0 OR MIT
"""

import os as _floor_os
import shutil as _floor_shutil
import sys as _floor_sys

# Trust: python floor (scripts/tests/python_floor_test.py). This file needs tomllib (3.11+) and plain
# `python3` is 3.9 on macOS CommandLineTools, so an old interpreter re-execs here, before any import
# that needs 3.11 runs.
if __name__ == "__main__" and _floor_sys.version_info < (3, 11):
    for _floor_candidate in ("python3.14", "python3.13", "python3.12", "python3.11"):
        _floor_path = _floor_shutil.which(_floor_candidate)
        if _floor_path:
            _floor_argv = [_floor_path, _floor_os.path.abspath(__file__), *_floor_sys.argv[1:]]
            _floor_os.execv(_floor_path, _floor_argv)
    _floor_sys.exit("templates.py requires Python 3.11+ (tomllib); none found on PATH")

import argparse
import hashlib
import json
import re
import sys
from dataclasses import dataclass, field
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import common as C  # noqa: E402

import tomllib  # noqa: E402  (common.py has already refused an interpreter without it)

KEY = "templates"
SCHEMA = "trust.core.denominator.v1"
RECORD_REL = f"docs/trust-core/denominators/{KEY}.toml"
SCRIPT_REL = f"scripts/trust_core/denominators/{KEY}.py"
SUBMODULE = "trust-cg"

IR = "crates/trust-cg-ir/src"
CG = "crates/trust-cg-codegen/src"
VERIFY = "crates/trust-cg-verify/src"
A64_OPS = f"{IR}/inst.rs"
X86_OPS = f"{IR}/x86_64_ops.rs"
A64_ENCODE = f"{CG}/aarch64/encode.rs"
X86_ENCODE = f"{CG}/x86_64/encode.rs"
PIPELINE = f"{CG}/pipeline.rs"
X86_PIPELINE = f"{CG}/x86_64/pipeline.rs"
MACHO_RELOC = f"{CG}/macho/reloc.rs"
MACHO_X86_RELOC = f"{CG}/macho/x86_64_reloc.rs"
MACHO_CONSTANTS = f"{CG}/macho/constants.rs"
ELF_RELOC = f"{CG}/elf/reloc.rs"
ELF_CONSTANTS = f"{CG}/elf/constants.rs"
COFF_WRITER = f"{CG}/coff/writer.rs"
INVENTORY = f"{VERIFY}/object_inventory.rs"
FRAME = f"{CG}/frame.rs"
DWARF_CFI = f"{CG}/dwarf_cfi.rs"
COMPACT_UNWIND = f"{CG}/unwind.rs"
EH = f"{CG}/exception_handling.rs"
A64_EMITTER_FN = "encode_function_with_fixups_and_blocks_impl_with_sites"

# The design's claims this record tests, found by pattern (never by line number, which moves).
DESIGN_CLAIMS = (
    ("a64.opcode-variants", r"starting from (\d+) and \d+ opcode variants \[M†\]"),
    ("x86.opcode-variants", r"starting from \d+ and (\d+) opcode variants \[M†\]"),
    ("a64.opcode-variants", r"The emitted-template denominators: (\d+) `AArch64Opcode`"),
    ("x86.opcode-variants", r"The emitted-template denominators: \d+ `AArch64Opcode` and (\d+) `X86Opcode`"),
    ("x86.opcode-variants", r"about (\d+) opcode variants in\s+trust-cg's `X86Opcode` today \[M†\]"),
)
# The design's status block: "with submodules at their gitlinks: clean `..`, trust-ir `..`, trust-cg `..`".
DESIGN_PIN = r"their gitlinks:[^\n]*?trust-cg `([0-9a-f]{7,40})`"


class Fatal(Exception):
    """The inputs cannot be read: exit 2."""


# --------------------------------------------------------------------------
# Rust source, lexed just enough
# --------------------------------------------------------------------------


def mask(text: str) -> str:
    """`text` with comments and the insides of string/char literals replaced by spaces (newlines
    kept), so braces, `=>` and identifiers can be counted. Offsets are unchanged."""
    out = list(text)
    n, i = len(text), 0

    def blank(a: int, b: int) -> None:
        for k in range(a, min(b, n)):
            if out[k] != "\n":
                out[k] = " "

    while i < n:
        c = text[i]
        if c == "/" and text.startswith("//", i):
            j = text.find("\n", i)
            j = n if j < 0 else j
            blank(i, j)
            i = j
        elif c == "/" and text.startswith("/*", i):
            depth, j = 1, i + 2
            while j < n and depth:
                if text.startswith("/*", j):
                    depth, j = depth + 1, j + 2
                elif text.startswith("*/", j):
                    depth, j = depth - 1, j + 2
                else:
                    j += 1
            blank(i, j)
            i = j
        elif c in "rb" and (i == 0 or not (text[i - 1].isalnum() or text[i - 1] == "_")):
            m = re.match(r'(?:br|r)(#*)"', text[i:i + 300])
            if m:  # a raw string: ends at `"` plus the same number of `#`
                end = text.find('"' + m.group(1), i + m.end())
                end = n if end < 0 else end + 1 + len(m.group(1))
                blank(i + m.end(), end - 1 - len(m.group(1)))
                i = end
            elif text.startswith('b"', i) or text.startswith("b'", i):
                i += 1  # the literal itself is handled at its quote
            else:
                i += 1
        elif c == '"':
            j = i + 1
            while j < n and text[j] != '"':
                j += 2 if text[j] == "\\" else 1
            blank(i + 1, j)
            i = j + 1
        elif c == "'":
            # a char literal ('x', '\n', '\u{..}', '{') or a lifetime/label ('a, 'static)
            if i + 1 < n and text[i + 1] == "\\":
                j = text.find("'", i + 3)  # past the escaped character, so '\'' closes at its own quote
                j = n if j < 0 else j
                blank(i + 1, j)
                i = j + 1
            elif i + 2 < n and text[i + 2] == "'":
                blank(i + 1, i + 2)
                i += 3
            else:
                i += 1
        else:
            i += 1
    return "".join(out)


OPEN, CLOSE = "([{", ")]}"


def matching(masked: str, pos: int) -> int:
    """The index of the bracket closing the one at `pos`."""
    depth = 0
    for k in range(pos, len(masked)):
        ch = masked[k]
        if ch in OPEN:
            depth += 1
        elif ch in CLOSE:
            depth -= 1
            if depth == 0:
                return k
    raise ValueError(f"unbalanced bracket at offset {pos}")


def split_top(masked: str, start: int, end: int, sep: str = ",") -> list[tuple[int, int]]:
    """Spans of `masked[start:end]` split at `sep` outside any bracket."""
    spans, depth, begin = [], 0, start
    for k in range(start, end):
        ch = masked[k]
        if ch in OPEN:
            depth += 1
        elif ch in CLOSE:
            depth -= 1
        elif ch == sep and depth == 0:
            spans.append((begin, k))
            begin = k + 1
    spans.append((begin, end))
    return [(a, b) for a, b in spans if masked[a:b].strip()]


@dataclass
class Fn:
    name: str
    params: list[str]  # parameter names in order (`self` first for a method)
    start: int  # offset of `fn`
    body: tuple[int, int]  # the body's span: its `{` to one past its `}`


@dataclass
class Source:
    """One Rust file at a pin: raw text, masked text, the excluded (test) spans, and its functions."""
    rel: str
    text: str
    masked: str = ""
    tests: list = field(default_factory=list)
    fns: list = field(default_factory=list)

    def __post_init__(self) -> None:
        self.masked = mask(self.text)
        self.tests = test_spans(self.masked)
        self.fns = [f for f in functions(self.masked) if not self.in_test(f.start)]

    def in_test(self, pos: int) -> bool:
        return any(a <= pos <= b for a, b in self.tests)

    def line(self, pos: int) -> int:
        return self.text.count("\n", 0, pos) + 1

    def fn(self, name: str, inside: tuple[int, int] | None = None) -> Fn:
        found = [f for f in self.fns if f.name == name and (inside is None or inside[0] <= f.start <= inside[1])]
        if len(found) != 1:
            raise Fatal(f"{self.rel}: {len(found)} non-test functions named `{name}`" + (" in the given impl" if inside else ""))
        return found[0]

    def impl(self, type_name: str) -> tuple[int, int]:
        """The body span of the (single, non-test) inherent `impl <type_name> {`."""
        spans = []
        for m in re.finditer(r"\bimpl\s+" + re.escape(type_name) + r"\s*\{", self.masked):
            if not self.in_test(m.start()):
                spans.append((m.end() - 1, matching(self.masked, m.end() - 1)))
        if len(spans) != 1:
            raise Fatal(f"{self.rel}: {len(spans)} inherent `impl {type_name}` blocks")
        return spans[0]


CFG_TEST = re.compile(r"#\[cfg\((?:all\(\s*)?test\b[^\]]*\]")


def test_spans(masked: str) -> list[tuple[int, int]]:
    """Spans of the items a `#[cfg(test)]`-style attribute gates: from the attribute to the end of
    the item's `{ .. }` body (or its `;`)."""
    spans = []
    for m in CFG_TEST.finditer(masked):
        k, depth = m.end(), 0
        while k < len(masked):
            ch = masked[k]
            if ch == "{" and depth == 0:
                spans.append((m.start(), matching(masked, k)))
                break
            if ch == ";" and depth == 0:
                spans.append((m.start(), k))
                break
            if ch in "([":
                depth += 1
            elif ch in ")]":
                depth -= 1
            k += 1
    return spans


def functions(masked: str) -> list[Fn]:
    found = []
    for m in re.finditer(r"\bfn\s+(\w+)", masked):
        k = m.end()
        if k < len(masked) and masked[k] == "<":  # generics
            depth = 0
            while k < len(masked):
                if masked[k] == "<":
                    depth += 1
                elif masked[k] == ">" and masked[k - 1] != "-":
                    depth -= 1
                    if depth == 0:
                        k += 1
                        break
                k += 1
        while k < len(masked) and masked[k].isspace():
            k += 1
        if k >= len(masked) or masked[k] != "(":
            continue
        close = matching(masked, k)
        params = []
        for a, b in split_top(masked, k + 1, close):
            p = masked[a:b].strip()
            pm = re.match(r"(?:&\s*(?:'\w+\s+)?)?(?:mut\s+)?(\w+)", p)
            params.append(pm.group(1) if pm else "")
        j, depth = close + 1, 0
        while j < len(masked):
            ch = masked[j]
            if ch == ";" and depth == 0:
                break  # a declaration without a body
            if ch == "{" and depth == 0:
                found.append(Fn(m.group(1), params, m.start(), (j, matching(masked, j) + 1)))
                break
            if ch in "([<":
                depth += 1
            elif ch in ")]>" and masked[j - 1] != "-":
                depth -= 1
            j += 1
    return found


@dataclass
class Variant:
    name: str
    line: int
    discriminant: str | None  # the text after `=`, when present
    shape: str  # "unit", "tuple" or "struct"


def enum_variants(src: Source, name: str) -> list[Variant]:
    hits = [m for m in re.finditer(r"\benum\s+" + re.escape(name) + r"\s*\{", src.masked) if not src.in_test(m.start())]
    if len(hits) != 1:
        raise Fatal(f"{src.rel}: {len(hits)} non-test definitions of enum {name}")
    open_ = hits[0].end() - 1
    close = matching(src.masked, open_)
    out = []
    for a, b in split_top(src.masked, open_ + 1, close):
        item = src.masked[a:b]
        body = re.sub(r"#\s*\[[^\]]*\]", lambda m: " " * len(m.group(0)), item)  # attributes
        m = re.match(r"\s*(\w+)\s*(\(|\{)?", body)
        if not m:
            raise Fatal(f"{src.rel}: cannot read a variant of {name} at line {src.line(a)}")
        disc = None
        if "=" in body and not m.group(2):
            disc = body.split("=", 1)[1].strip()
        shape = {"(": "tuple", "{": "struct"}.get(m.group(2) or "", "unit")
        out.append(Variant(m.group(1), src.line(a + m.start(1)), disc, shape))
    return out


# --------------------------------------------------------------------------
# match arms and the per-variant evaluation of a dispatch
# --------------------------------------------------------------------------


@dataclass
class Arm:
    pattern: str
    guarded: bool
    body: tuple[int, int]  # span of the body expression (a block includes its braces)
    line: int


def match_arms(src: Source, open_: int) -> list[Arm]:
    """The arms of the match whose `{` is at `open_`."""
    close = matching(src.masked, open_)
    arms, k, s = [], open_ + 1, src.masked
    while k < close:
        while k < close and (s[k].isspace() or s[k] == ","):
            k += 1
        if k >= close:
            break
        depth, j = 0, k
        while j < close:
            if s[j] in OPEN:
                depth += 1
            elif s[j] in CLOSE:
                depth -= 1
            elif depth == 0 and s.startswith("=>", j):
                break
            j += 1
        pattern = s[k:j]
        b = j + 2
        while b < close and s[b].isspace():
            b += 1
        depth, e = 0, b
        while e < close:
            if s[e] in OPEN:
                depth += 1
            elif s[e] in CLOSE:
                depth -= 1
                if depth == 0 and s[b] == "{" and e == matching(s, b):
                    # a block arm ends at its brace unless a method call or `?` continues it
                    nxt = e + 1
                    while nxt < close and s[nxt].isspace():
                        nxt += 1
                    if nxt >= close or s[nxt] not in ".?":
                        e += 1
                        break
            elif s[e] == "," and depth == 0:
                break
            e += 1
        guarded = re.search(r"\bif\b", pattern) is not None
        arms.append(Arm(pattern.strip(), guarded, (b, e), src.line(k)))
        k = e + 1
    return arms


def pattern_names(pattern: str, variants: set[str]) -> set[str]:
    head = re.split(r"\bif\b", pattern, maxsplit=1)[0]
    return {w for w in re.findall(r"\b(\w+)\b", head) if w in variants}


def is_catch_all(pattern: str) -> bool:
    head = re.split(r"\bif\b", pattern, maxsplit=1)[0].strip()
    return head == "_" or re.fullmatch(r"[a-z_][a-z0-9_]*", head) is not None


REFUSAL = re.compile(r"(?:return\s+)?(?:Err\s*\(|unreachable!\s*\(|panic!\s*\(|todo!\s*\(|unimplemented!\s*\()")


def body_core(src: Source, span: tuple[int, int]) -> str:
    """The arm body without its outer braces, surrounding whitespace and a trailing `;`."""
    t = src.masked[span[0]:span[1]].strip()
    while t.startswith("{") and matching(t, 0) == len(t) - 1:
        t = t[1:-1].strip()
    return t.rstrip(";").strip()


def bare(src: Source, span: tuple[int, int]) -> str | None:
    """"refusal", "zero-bytes" or "constant" when the body is exactly one such expression."""
    core = body_core(src, span)
    m = REFUSAL.match(core)
    if m:
        open_ = m.end() - 1
        if matching(core, open_) == len(core) - 1:
            return "refusal"
    if re.fullmatch(r"(?:return\s+)?Ok\s*\(\s*0\s*\)", core):
        return "zero-bytes"
    if re.fullmatch(r"(?:return\s+)?Ok\s*\(\s*(?:[A-Z][A-Z0-9_]*|0x[0-9A-Fa-f_]+)\s*\)", core):
        return "constant"
    return None


@dataclass
class Dispatch:
    """How one ISA's encoder is dispatched: the enum, the variable holding the opcode carrier, and
    how a match scrutinee on that carrier is spelled."""
    enum: str
    variants: set[str]
    scrutinee: str  # a format string over the carrier name, e.g. "{}.opcode" or "{}"


def evaluate(src: Source, disp: Dispatch, span: tuple[int, int], carrier: str, v: str,
             trail: list[str], seen: set) -> tuple[str, list[str]]:
    """("emits" | "refused", trail) for variant `v` flowing through the code in `span`, where the
    opcode is carried by the variable `carrier`."""
    kind = bare(src, span)
    here = f"{src.rel}:{src.line(span[0])}"
    if kind == "refusal":
        return "refused", trail + [f"bare refusal at {here}: {body_core(src, span)[:120]}"]
    if kind == "zero-bytes":
        return "zero-bytes", trail + [f"zero bytes at {here}"]
    s = src.masked
    scrut = re.escape(disp.scrutinee.format(carrier))
    inner_matches = []
    for m in re.finditer(r"\bmatch\s+" + scrut + r"\s*\{", s[span[0]:span[1]]):
        pos = span[0] + m.end() - 1
        if any(a < pos < b for a, b in inner_matches):
            continue
        inner_matches.append((pos, matching(s, pos)))
    for open_, close in inner_matches:
        arms = match_arms(src, open_)
        chosen = [a for a in arms if v in pattern_names(a.pattern, disp.variants) and not a.guarded]
        chosen = chosen or [a for a in arms if v in pattern_names(a.pattern, disp.variants)]
        chosen = chosen or [a for a in arms if is_catch_all(a.pattern) and not a.guarded]
        if not chosen:
            return "refused", trail + [f"no arm for {v} in the nested match at {src.rel}:{src.line(open_)}"]
        outcome, sub = evaluate(src, disp, chosen[0].body, carrier, v,
                                trail + [f"nested match {src.rel}:{src.line(open_)} arm line {chosen[0].line}"], seen)
        if outcome != "emits":
            return outcome, sub
    # same-file helpers the body hands the carrier to
    names = {f.name: f for f in src.fns}
    for m in re.finditer(r"\b(\w+)\s*\(", s[span[0]:span[1]]):
        callee = names.get(m.group(1))
        if callee is None:
            continue
        open_ = span[0] + m.end() - 1
        if any(a < open_ < b for a, b in inner_matches):
            continue  # handled inside the arm that was chosen
        args = [s[a:b].strip().lstrip("&").strip() for a, b in split_top(s, open_ + 1, matching(s, open_))]
        method = s[span[0] + m.start() - 1] == "." if span[0] + m.start() > 0 else False
        params = callee.params[1:] if method and callee.params[:1] == ["self"] else callee.params
        for index, arg in enumerate(args):
            if arg == carrier and index < len(params) and params[index]:
                key = (callee.name, v)
                if key in seen:
                    continue
                seen.add(key)
                outcome, sub = evaluate(src, disp, callee.body, params[index], v,
                                        trail + [f"helper {callee.name} ({src.rel}:{src.line(callee.start)})"], seen)
                if outcome != "emits":
                    return outcome, sub
    return "emits", trail


@dataclass
class Classified:
    name: str
    line: int  # the variant's line in the IR crate
    category: str
    arm_line: int | None
    why: str
    constant: bool = False
    opcode_pseudo: bool = False


    word: str = ""  # a constant arm's expression, e.g. `Ok(NOP)`


def classify_encoder(src: Source, fn: Fn, disp: Dispatch, carrier: str, variants: list[Variant],
                     findings: C.Findings) -> dict[str, tuple[str, int | None, str, bool, str]]:
    """Per variant: (outcome, encoder arm line, why, constant arm?, constant arm expression)."""
    s = src.masked
    scrut = re.escape(disp.scrutinee.format(carrier))
    m = re.search(r"\bmatch\s+" + scrut + r"\s*\{", s[fn.body[0]:fn.body[1]])
    if not m:
        raise Fatal(f"{src.rel}: `{fn.name}` has no `match {disp.scrutinee.format(carrier)}`")
    arms = match_arms(src, fn.body[0] + m.end() - 1)
    names = disp.variants
    # every qualified variant name the encoder file uses must be one the enum parse found
    stray = sorted({w for w in re.findall(r"\b" + disp.enum + r"::(\w+)", s) if w not in names})
    if stray:
        findings.add("PARSE", f"{src.rel} names {disp.enum} variants the enum parse did not find: {stray}")
    out = {}
    for var in variants:
        v = var.name
        explicit = [a for a in arms if v in pattern_names(a.pattern, names)]
        if len(explicit) > 1:
            findings.add("PARSE", f"{src.rel}: {v} is named by {len(explicit)} arms of `{fn.name}`")
        chosen = explicit or [a for a in arms if is_catch_all(a.pattern) and not a.guarded]
        if not chosen:
            findings.add("PARSE", f"{src.rel}: `{fn.name}` has no arm for {disp.enum}::{v} and no catch-all")
            out[v] = ("no-arm", None, "no arm", False, "")
            continue
        arm = chosen[0]
        outcome, trail = evaluate(src, disp, arm.body, carrier, v, [], set())
        const = bare(src, arm.body) == "constant"
        out[v] = (outcome, arm.line, "; ".join(trail) or "encoder arm", const,
                  " ".join(body_core(src, arm.body).split()) if const else "")
    return out


# --------------------------------------------------------------------------
# small readers of consts and names
# --------------------------------------------------------------------------


def consts(src: Source, pattern: str) -> list[tuple[str, int, int]]:
    """(name, value, line) of every non-test `const NAME: T = <int>;` whose NAME matches."""
    out = []
    for m in re.finditer(r"\bconst\s+(" + pattern + r")\s*:\s*\w+\s*=\s*(0x[0-9A-Fa-f_]+|\d[\d_]*)\s*;", src.masked):
        if src.in_test(m.start()):
            continue
        out.append((m.group(1), int(m.group(2).replace("_", ""), 0), src.line(m.start())))
    return out


def used_beyond_definition(src: Source, name: str) -> bool:
    """Whether `name` occurs in non-test code of `src` other than its own `const` definition."""
    hits = [m.start() for m in re.finditer(r"\b" + re.escape(name) + r"\b", src.masked) if not src.in_test(m.start())]
    defs = [m.start(1) for m in re.finditer(r"\bconst\s+(" + re.escape(name) + r")\b", src.masked)]
    return len([h for h in hits if h not in defs]) > 0


def named_in(src: Source, span: tuple[int, int], qualifier: str) -> set[str]:
    return set(re.findall(r"\b" + re.escape(qualifier) + r"::(\w+)", src.masked[span[0]:span[1]]))


def sha256_lines(items) -> str:
    return "sha256:" + hashlib.sha256("".join(f"{x}\n" for x in items).encode()).hexdigest()


def resolve(value: str, table: dict[str, int]) -> int:
    value = value.strip()
    if re.fullmatch(r"0x[0-9A-Fa-f_]+|\d[\d_]*", value):
        return int(value.replace("_", ""), 0)
    if value in table:
        return table[value]
    raise Fatal(f"cannot resolve discriminant {value!r}")


# --------------------------------------------------------------------------
# the measurement
# --------------------------------------------------------------------------


@dataclass
class Tree:
    """first-party/trust-cg at one commit, read from git objects."""
    commit: str
    tree: object
    cache: dict = field(default_factory=dict)

    def src(self, rel: str) -> Source:
        if rel not in self.cache:
            text = self.tree.text(rel)
            if text is None:
                raise Fatal(f"trust-cg {self.commit[:12]}: {rel} is not a readable blob")
            self.cache[rel] = Source(rel, text)
        return self.cache[rel]

    def blobs(self) -> list[dict]:
        """The path and blob id of every file this measurement read."""
        out = []
        for rel in sorted(self.cache):
            oid = (C.git(self.tree.repo, "rev-parse", f"{self.commit}:{rel}", git_dir=self.tree.git_dir) or "").strip()
            if not C.HEX40.match(oid):
                raise Fatal(f"trust-cg {self.commit[:12]}: no blob id for {rel}")
            out.append({"path": rel, "blob": oid})
        return out


def pseudo_sets(src: Source, enum: str, variants: set[str]) -> tuple[set[str], set[str]]:
    """(opcode-level `is_pseudo` members, variants whose `default_flags` arm carries IS_PSEUDO)."""
    impl = src.impl(enum)
    is_pseudo = src.fn("is_pseudo", impl)
    opcode_pseudo = set(re.findall(r"\bSelf::(\w+)", src.masked[is_pseudo.body[0]:is_pseudo.body[1]])) & variants
    flags = src.fn("default_flags", impl)
    m = re.search(r"\bmatch\s+self\s*\{", src.masked[flags.body[0]:flags.body[1]])
    if not m:
        raise Fatal(f"{src.rel}: {enum}::default_flags has no `match self`")
    flag_pseudo = set()
    for arm in match_arms(src, flags.body[0] + m.end() - 1):
        if re.search(r"\bIS_PSEUDO\b", src.masked[arm.body[0]:arm.body[1]]):
            if is_catch_all(arm.pattern):
                raise Fatal(f"{src.rel}: {enum}::default_flags gives IS_PSEUDO to a catch-all arm")
            flag_pseudo |= pattern_names(arm.pattern, variants)
    return opcode_pseudo, flag_pseudo


def measure_a64(t: Tree, findings: C.Findings) -> dict:
    ops = t.src(A64_OPS)
    variants = enum_variants(ops, "AArch64Opcode")
    names = {v.name for v in variants}
    opcode_pseudo, flag_pseudo = pseudo_sets(ops, "AArch64Opcode", names)
    enc = t.src(A64_ENCODE)
    disp = Dispatch("AArch64Opcode", names, "{}.opcode")
    fn = enc.fn("encode_instruction")
    encoded = classify_encoder(enc, fn, disp, fn.params[0], variants, findings)
    pipe = t.src(PIPELINE)
    emitter = pipe.fn(A64_EMITTER_FN)
    if not re.search(r"if\s+inst\.is_pseudo\(\)\s*\{\s*continue;\s*\}", pipe.masked[emitter.body[0]:emitter.body[1]]):
        findings.add("PREMISE", f"{PIPELINE}: `{A64_EMITTER_FN}` no longer skips `inst.is_pseudo()`; clause (1) of the predicate needs re-reading")
    intercepted = named_in(pipe, emitter.body, "AArch64Opcode") & names
    rows = []
    for var in variants:
        outcome, arm_line, why, const, word = encoded[var.name]
        if var.name in flag_pseudo:
            cat, why = "skipped", "default_flags gives it IS_PSEUDO, so every emitter walk skips it before the encoder"
        elif outcome == "emits":
            cat = "encoded"
        elif outcome == "refused" and var.name in intercepted and "UnsupportedOpcode" in why:
            cat, why = "fixup", f"{why}; `{A64_EMITTER_FN}` ({PIPELINE}) names it: the relocation-fixup interception writes its placeholder word and a relocation"
        else:
            cat = "refused"
        rows.append(Classified(var.name, var.line, cat, arm_line, why, const, var.name in opcode_pseudo, word))
    return {"variants": variants, "rows": rows, "opcode_pseudo": opcode_pseudo, "flag_pseudo": flag_pseudo,
            "encoder": f"{A64_ENCODE}:{enc.line(fn.start)}", "emitter": f"{PIPELINE}:{pipe.line(emitter.start)}"}


def measure_x86(t: Tree, findings: C.Findings) -> dict:
    ops = t.src(X86_OPS)
    variants = enum_variants(ops, "X86Opcode")
    names = {v.name for v in variants}
    opcode_pseudo, flag_pseudo = pseudo_sets(ops, "X86Opcode", names)
    enc = t.src(X86_ENCODE)
    disp = Dispatch("X86Opcode", names, "{}")
    fn = enc.fn("encode_instruction", enc.impl("X86Encoder"))
    carrier = fn.params[1] if fn.params[:1] == ["self"] else fn.params[0]
    encoded = classify_encoder(enc, fn, disp, carrier, variants, findings)
    rows = []
    for var in variants:
        outcome, arm_line, why, const, word = encoded[var.name]
        cat = {"emits": "encoded", "zero-bytes": "zero-bytes"}.get(outcome, "refused")
        rows.append(Classified(var.name, var.line, cat, arm_line, why, const, var.name in opcode_pseudo, word))
    # the SSE2 packed alias surface: every alias must land on an emitted X86Opcode template
    alias = enum_variants(ops, "X86Sse2PackedOpcode")
    to = ops.fn("to_x86_opcode", ops.impl("X86Sse2PackedOpcode"))
    m = re.search(r"\bmatch\s+self\s*\{", ops.masked[to.body[0]:to.body[1]])
    if not m:
        raise Fatal(f"{X86_OPS}: X86Sse2PackedOpcode::to_x86_opcode has no `match self`")
    mapping = {}
    for arm in match_arms(ops, to.body[0] + m.end() - 1):
        dst = re.findall(r"\bX86Opcode::(\w+)", ops.masked[arm.body[0]:arm.body[1]])
        for s_name in re.findall(r"\bSelf::(\w+)", arm.pattern):
            mapping[s_name] = dst[0] if len(dst) == 1 else None
    emitted = {r.name for r in rows if r.category == "encoded"}
    for a in alias:
        target = mapping.get(a.name)
        if target is None:
            findings.add("PREMISE", f"{X86_OPS}: X86Sse2PackedOpcode::{a.name} has no single X86Opcode target in to_x86_opcode")
        elif target not in emitted:
            findings.add("PREMISE", f"{X86_OPS}: X86Sse2PackedOpcode::{a.name} maps to X86Opcode::{target}, which is not an emitted template")
    return {"variants": variants, "rows": rows, "opcode_pseudo": opcode_pseudo, "flag_pseudo": flag_pseudo,
            "alias": [(a.name, mapping.get(a.name)) for a in alias], "encoder": f"{X86_ENCODE}:{enc.line(fn.start)}"}


def measure_relocs(t: Tree, findings: C.Findings) -> dict:
    out = {}
    mr = t.src(MACHO_RELOC)
    kinds = enum_variants(mr, "AArch64RelocKind")
    disc = {k.name: resolve(k.discriminant or "", {}) for k in kinds}
    elf_only = mr.fn("is_elf_only", mr.impl("AArch64RelocKind"))
    m = re.search(r">\s*\(\s*AArch64RelocKind::(\w+)\s+as\s+u8\s*\)", mr.masked[elf_only.body[0]:elf_only.body[1]])
    if not m:
        raise Fatal(f"{MACHO_RELOC}: is_elf_only is not `(self as u8) > (AArch64RelocKind::X as u8)`")
    last_macho = m.group(1)
    mc = t.src(MACHO_CONSTANTS)
    arm64_consts = {v: n for n, v, _ in consts(mc, r"ARM64_RELOC_\w+")}
    x86_consts = {v: n for n, v, _ in consts(mc, r"X86_64_RELOC_\w+")}
    macho_a64 = [(k.name, disc[k.name], arm64_consts.get(disc[k.name], "")) for k in kinds if disc[k.name] <= disc[last_macho]]
    carriers = [(k.name, disc[k.name]) for k in kinds if disc[k.name] > disc[last_macho]]
    if sorted(v for _, v, _ in macho_a64) != sorted(arm64_consts):
        findings.add("PREMISE", f"{MACHO_RELOC}: the Mach-O AArch64RelocKind values differ from the ARM64_RELOC_* constants of {MACHO_CONSTANTS}")
    xkinds = enum_variants(t.src(MACHO_X86_RELOC), "X86_64RelocKind")
    macho_x86 = []
    for k in xkinds:
        value = resolve(k.discriminant or "", {})
        macho_x86.append((k.name, value, x86_consts.get(value, "")))
    if sorted(v for _, v, _ in macho_x86) != sorted(x86_consts):
        findings.add("PREMISE", f"{MACHO_X86_RELOC}: X86_64RelocKind values differ from the X86_64_RELOC_* constants of {MACHO_CONSTANTS}")
    elf_consts = {n: v for n, v, _ in consts(t.src(ELF_CONSTANTS), r"R_\w+")}
    er = t.src(ELF_RELOC)
    elf = {}
    for enum, isa in (("AArch64RelocType", "aarch64"), ("X86_64RelocType", "x86_64"), ("RiscvRelocType", "riscv64")):
        elf[isa] = [(k.name, resolve(k.discriminant or "", elf_consts), (k.discriminant or "").strip())
                    for k in enum_variants(er, enum)]
    coff = [(n[len("IMAGE_REL_AMD64_"):], v, n) for n, v, _ in consts(t.src(COFF_WRITER), r"IMAGE_REL_AMD64_\w+")]
    # the ELF type `aarch64_elf_reloc_kind` maps each ELF-only carrier to (an arm returning Ok(..))
    pipe = t.src(PIPELINE)
    mapfn = pipe.fn("aarch64_elf_reloc_kind")
    carrier_map: dict[str, set] = {}
    for mm in re.finditer(r"\bmatch\s+[^{]*\{", pipe.masked[mapfn.body[0]:mapfn.body[1]]):
        for arm in match_arms(pipe, mapfn.body[0] + mm.end() - 1):
            body = pipe.masked[arm.body[0]:arm.body[1]]
            targets = re.findall(r"\bOk\(\s*crate::elf::AArch64RelocType::(\w+)\s*\)", body)
            if len(targets) != 1 or re.search(r"\bErr\s*\(", body):
                continue
            for kind in re.findall(r"\bAArch64RelocKind::(\w+)", arm.pattern):
                carrier_map.setdefault(kind, set()).add(targets[0])
    elf_a64_names = {n for n, _, _ in elf["aarch64"]}
    carrier_rows = []
    for name, value in carriers:
        targets = sorted(carrier_map.get(name, set()))
        if len(targets) != 1 or targets[0] not in elf_a64_names:
            findings.add("PREMISE", f"{PIPELINE}: aarch64_elf_reloc_kind maps the ELF-only carrier {name} to {targets or 'nothing'}")
        carrier_rows.append((name, value, targets))
    # the certified-output inventory's named rows
    inventory: dict[tuple, list] = {}
    for k in enum_variants(t.src(INVENTORY), "ObjectRelocationKind"):
        mm = re.match(r"(AArch64|X86_64)(Elf|MachO|Coff)(\w+)$", k.name)
        if not mm:
            findings.add("PARSE", f"{INVENTORY}: ObjectRelocationKind::{k.name} names no (ISA, format)")
            continue
        if k.shape != "unit":
            continue  # the `*Other(raw)` catch-alls
        pair = ({"Elf": "elf", "MachO": "macho", "Coff": "coff"}[mm.group(2)],
                {"AArch64": "aarch64", "X86_64": "x86_64"}[mm.group(1)])
        inventory.setdefault(pair, []).append(mm.group(3))
    writer = {
        ("macho", "aarch64"): macho_a64,
        ("macho", "x86_64"): macho_x86,
        ("elf", "aarch64"): elf["aarch64"],
        ("elf", "x86_64"): elf["x86_64"],
        ("coff", "x86_64"): coff,
        ("elf", "riscv64"): elf["riscv64"],
    }

    def norm(fmt: str, name: str) -> str:
        return name.replace("_", "").upper() if fmt == "coff" else name

    for (fmt, isa), rows in writer.items():
        by_norm = {norm(fmt, n): n for n, _, _ in rows}
        matched = []
        for r in inventory.get((fmt, isa), []):
            hit = by_norm.get(norm(fmt, r))
            if hit is None:
                findings.add("PREMISE", f"{INVENTORY}: inventory row {r} ({fmt}/{isa}) matches no writer kind by name")
            else:
                matched.append(hit)
        out[(fmt, isa)] = {"writer": rows, "inventory": matched}
    for pair in inventory:
        if pair not in writer:
            findings.add("PREMISE", f"{INVENTORY}: inventory rows for {pair} have no writer enumeration here")
    out["carriers"] = carrier_rows
    out["last_macho"] = last_macho
    return out


def measure_unwind(t: Tree, findings: C.Findings) -> dict:
    out = {}
    frame = t.src(FRAME)
    enc = frame.fn("encode_compact_unwind")
    used = set(re.findall(r"\b(UNWIND_ARM64_MODE_\w+)\b", frame.masked[enc.body[0]:enc.body[1]]))
    out["compact_a64"] = [(n, v, n in used) for n, v, _ in consts(frame, r"UNWIND_ARM64_MODE_\w+")]
    cu = t.src(COMPACT_UNWIND)
    out["compact_a64_flags"] = [
        (n, v, used_beyond_definition(frame, n)
         or any(not cu.in_test(mm.start()) for mm in re.finditer(r"\b" + n + r"\b", cu.masked)))
        for n, v, _ in consts(frame, r"UNWIND_HAS_LSDA|UNWIND_ARM64_FRAME_\w+")]
    xp = t.src(X86_PIPELINE)
    out["compact_x86"] = [(n, v, used_beyond_definition(xp, n)) for n, v, _ in consts(xp, r"UNWIND_X86_64_MODE_\w+")]
    cfi = t.src(DWARF_CFI)
    cie_impl = cfi.impl("DwarfCie")
    shapes = []
    for f in cfi.fns:
        if not (cie_impl[0] <= f.start <= cie_impl[1]):
            continue
        m = re.fullmatch(r"(aarch64|x86_64)_(darwin|elf)(_with_eh)?", f.name)
        if not m:
            continue
        aug = re.findall(r'augmentation:\s*b"([A-Za-z]+)\\0"', cfi.text[f.body[0]:f.body[1]])
        if len(aug) != 1:
            findings.add("PARSE", f"{DWARF_CFI}: DwarfCie::{f.name} has {len(aug)} augmentation literals")
        shapes.append({"isa": m.group(1), "format": {"darwin": "macho", "elf": "elf"}[m.group(2)],
                       "eh": bool(m.group(3)), "constructor": f"DwarfCie::{f.name}",
                       "augmentation": aug[0] if len(aug) == 1 else "?", "line": cfi.line(f.start)})
    out["cie"] = shapes
    out["cfa"] = [(n, v, used_beyond_definition(cfi, n)) for n, v, _ in consts(cfi, r"DW_CFA_\w+")]
    out["eh_pe"] = [(n, v, used_beyond_definition(cfi, n)) for n, v, _ in consts(cfi, r"DW_EH_PE_\w+")]
    eh = t.src(EH)
    out["dwehpe"] = [(k.name, resolve(k.discriminant or "", {})) for k in enum_variants(eh, "DwEhPe")]
    out["lsda_structs"] = [(mm.group(1), eh.line(mm.start())) for mm in re.finditer(r"\bpub\s+struct\s+(\w+)", eh.masked)
                           if not eh.in_test(mm.start())]
    out["seh"] = [(n, v, used_beyond_definition(xp, n)) for n, v, _ in consts(xp, r"UWOP_\w+")]
    cw = t.src(COFF_WRITER)
    out["seh_sections"] = sorted({f.name for f in cw.fns if f.name in ("add_exception_data_section", "add_unwind_data_section")})
    out["coff_machines"] = [n for n, _, _ in consts(cw, r"IMAGE_FILE_MACHINE_\w+")]
    return out


# --------------------------------------------------------------------------
# the design's claims
# --------------------------------------------------------------------------


def design_facts(repo: Path, rev: str) -> tuple[list[dict], str | None]:
    text = C.git(repo, "show", f"{rev}:{C.DESIGN_REL}") or ""
    claims = []
    for row, pattern in DESIGN_CLAIMS:
        m = re.search(pattern, text)
        if m is None:
            claims.append({"row": row, "found": False, "pattern": pattern})
            continue
        claims.append({"row": row, "found": True, "line": text.count("\n", 0, m.start(1)) + 1, "value": int(m.group(1))})
    pins = re.findall(DESIGN_PIN, text)
    return claims, (pins[0] if len(pins) == 1 else None)


# --------------------------------------------------------------------------
# rows
# --------------------------------------------------------------------------

P_SOURCE = ("Source is lexed (comments and string/char literal contents blanked) and every #[cfg(test)] "
            "item excluded; everything is read from git objects of first-party/trust-cg at the gitlink.")
P_VARIANTS = ("the variants of `pub enum {enum}` ({rel}): one per top-level comma-separated item of the enum body. "
              "This is the quantity the design's [M†] number counts.")
P_A64 = ("AArch64Opcode variants V for which trust-cg writes instruction bytes of V's own: (1) V's "
         "`AArch64Opcode::default_flags` arm does not carry IS_PSEUDO (every emitter walk skips such an "
         f"instruction; `{A64_EMITTER_FN}` in {PIPELINE} is checked to do `if inst.is_pseudo() {{ continue; }}`); and "
         f"(2) either the arm of the exhaustive `match inst.opcode` in `encode_instruction` ({A64_ENCODE}) that names V is "
         "not a bare refusal (`Err(..)`, `return Err(..)`, `unreachable!`, `panic!`, `todo!`, `unimplemented!`) and "
         "reaches none for V through a nested `match inst.opcode` or a same-file helper it passes `inst` to "
         "(followed transitively, choosing V's arm, else the unguarded catch-all), or the encoder refuses V with "
         f"UnsupportedOpcode and `{A64_EMITTER_FN}` names `AArch64Opcode::V` (its relocation-fixup interception "
         "writes V's placeholder word and a relocation). Categories: encoded, fixup (emitted); skipped, refused (not).")
P_X86 = ("X86Opcode variants V whose arm of the exhaustive `match opcode` in `X86Encoder::encode_instruction` "
         f"({X86_ENCODE}) is neither a bare refusal nor a bare `return Ok(0)` (zero bytes) and reaches neither for V "
         "through a nested `match opcode` or a same-file helper it passes `opcode` to (followed transitively, as for "
         "AArch64). The x86 object emitters call this encoder for every non-pseudo instruction and record symbol fixups "
         "after encoding, so no interception clause applies. Categories: encoded (emitted); zero-bytes, refused (not).")


def variant_rows(rows: list[Classified], emitted: bool, cats: tuple) -> list[dict]:
    out = []
    for r in rows:
        if r.category not in cats:
            continue
        item = {"name": r.name, "category": r.category, "ir_line": r.line, "encoder_arm_line": r.arm_line or 0}
        if r.constant:
            item["constant_arm"] = r.word
        if not emitted or r.category == "fixup":
            item["reason"] = r.why
        out.append(item)
    return out


def counts(rows, cats) -> dict:
    return {c: sum(1 for r in rows if r.category == c) for c in cats}


def build_rows(a64: dict, x86: dict, rel: dict, unw: dict, old: dict | None, old_pin: str | None,
               claims: list[dict]) -> list[dict]:
    rows = []
    a_names = [v.name for v in a64["variants"]]
    x_names = [v.name for v in x86["variants"]]

    def design_notes(row: str, measured: int, at_old: int | None) -> list[str]:
        notes = []
        for c in claims:
            if c["row"] != row:
                continue
            if not c["found"]:
                notes.append(f"the design no longer states this claim (pattern {c['pattern']!r} not found)")
                continue
            head = f"design:{c['line']} says {c['value']} [M†]"
            if at_old is None:
                notes.append(f"{head}: not tested (the design's trust-cg pin could not be read)")
            elif c["value"] == at_old == measured:
                notes.append(f"{head}: reproduced at the design's trust-cg pin {old_pin} and at the measured pin")
            elif c["value"] == at_old:
                notes.append(f"{head}: reproduced at the design's trust-cg pin {old_pin} ({at_old}); the measured pin has "
                             f"{measured}: the pin moved (a change of the enum, not of the predicate)")
            else:
                notes.append(f"{head}: NOT reproduced: {at_old} at the design's pin {old_pin}, {measured} at the measured pin")
        return notes

    old_a = [v.name for v in old["a64"]["variants"]] if old else None
    old_x = [v.name for v in old["x86"]["variants"]] if old else None
    for isa, names, olds, enum, relpath in (("a64", a_names, old_a, "AArch64Opcode", A64_OPS),
                                            ("x86", x_names, old_x, "X86Opcode", X86_OPS)):
        row = {"name": f"{isa}.opcode-variants", "value": len(names), "status": "measured",
               "predicate": P_VARIANTS.format(enum=enum, rel=relpath) + " " + P_SOURCE,
               "design": design_notes(f"{isa}.opcode-variants", len(names), len(olds) if olds is not None else None)}
        if olds is not None:
            row["added_since_design_pin"] = [n for n in names if n not in set(olds)]
            row["removed_since_design_pin"] = [n for n in olds if n not in set(names)]
        rows.append(row)

    a_rows = a64["rows"]
    a_emitted = [r for r in a_rows if r.category in ("encoded", "fixup")]
    rows.append({"name": "a64.emitted-templates", "value": len(a_emitted), "of": "a64.opcode-variants", "status": "measured",
                 "predicate": P_A64 + " " + P_SOURCE, "source": [a64["encoder"], a64["emitter"]],
                 "by_category": counts(a_rows, ("encoded", "fixup")),
                 "digest": sha256_lines(sorted(r.name for r in a_emitted)),
                 "variants": variant_rows(a_rows, True, ("encoded", "fixup"))})
    a_not = [r for r in a_rows if r.category not in ("encoded", "fixup")]
    rows.append({"name": "a64.not-emitted", "value": len(a_not), "of": "a64.opcode-variants", "status": "measured",
                 "predicate": "a64.opcode-variants minus a64.emitted-templates, each with the reason the predicate gives",
                 "by_category": counts(a_rows, ("skipped", "refused")),
                 "variants": variant_rows(a_rows, False, ("skipped", "refused"))})
    ps = [r for r in a_emitted if r.opcode_pseudo]
    real_words = {}
    for r in a_emitted:
        if r.constant and not r.opcode_pseudo:
            real_words.setdefault(r.word, []).append(r.name)
    rows.append({"name": "a64.emitted-templates.opcode-pseudo", "value": len(ps), "of": "a64.emitted-templates",
                 "status": "measured",
                 "predicate": ("emitted templates that `AArch64Opcode::is_pseudo()` lists (its doc: 'a pseudo-instruction "
                               "with no hardware encoding'): their default flags lack IS_PSEUDO, so they reach the encoder, "
                               "whose arm is a constant word; `same_word_as` lists the emitted variants outside is_pseudo() "
                               "whose arm is the same constant. They are emitted bytes, so they are in the denominator."),
                 "variants": [{"name": r.name, "encoder_arm_line": r.arm_line or 0, "constant_arm": r.word or "(not a constant arm)",
                               "same_word_as": real_words.get(r.word, [])} for r in ps]})
    x_rows = x86["rows"]
    x_emitted = [r for r in x_rows if r.category == "encoded"]
    rows.append({"name": "x86.emitted-templates", "value": len(x_emitted), "of": "x86.opcode-variants", "status": "measured",
                 "predicate": P_X86 + " " + P_SOURCE, "source": [x86["encoder"]],
                 "by_category": counts(x_rows, ("encoded",)),
                 "digest": sha256_lines(sorted(r.name for r in x_emitted)),
                 "variants": variant_rows(x_rows, True, ("encoded",))})
    x_not = [r for r in x_rows if r.category != "encoded"]
    rows.append({"name": "x86.not-emitted", "value": len(x_not), "of": "x86.opcode-variants", "status": "measured",
                 "predicate": "x86.opcode-variants minus x86.emitted-templates, each with the reason the predicate gives",
                 "by_category": counts(x_rows, ("zero-bytes", "refused")),
                 "variants": variant_rows(x_rows, False, ("zero-bytes", "refused"))})
    rows.append({"name": "x86.sse2-packed-alias", "value": len(x86["alias"]), "status": "measured",
                 "predicate": (f"the variants of `pub enum X86Sse2PackedOpcode` ({X86_OPS}), a compatibility surface each of "
                               "whose variants `to_x86_opcode` maps to exactly one X86Opcode variant; every target is checked "
                               "to be an emitted x86 template, so the alias adds 0 templates"),
                 "maps_to": [{"alias": a, "x86_opcode": b or "(none)"} for a, b in x86["alias"]]})
    if old:
        oa = [r for r in old["a64"]["rows"] if r.category in ("encoded", "fixup")]
        ox = [r for r in old["x86"]["rows"] if r.category == "encoded"]
        rows.append({"name": "a64.emitted-templates.at-design-pin", "value": len(oa), "status": "measured",
                     "predicate": f"a64.emitted-templates's predicate applied to trust-cg at the design's pin {old_pin} (informational: "
                                  "how far the design's 294 was from the emitted count when it was written)",
                     "by_category": counts(old["a64"]["rows"], ("encoded", "fixup", "skipped", "refused"))})
        rows.append({"name": "x86.emitted-templates.at-design-pin", "value": len(ox), "status": "measured",
                     "predicate": f"x86.emitted-templates's predicate applied to trust-cg at the design's pin {old_pin} (informational)",
                     "by_category": counts(old["x86"]["rows"], ("encoded", "zero-bytes", "refused"))})
    for isa, what, unblock in (
            ("a64", "the vendor decoder's encoding trees (D-8(a); E1.6.x): the generated A64 decoder",
             "the generated decoder of D-8(a) (or an owner-recorded split rule over the encoder's field choices); then count, per emitted opcode variant, the field splits the decoder distinguishes"),
            ("x86", "XED's datafiles (D-8(h); E2.7.1): the XED-generated decoder",
             "the XED-generated decoder of D-8(h)/E2.7.1; then count, per emitted opcode variant, the field splits it distinguishes")):
        rows.append({"name": f"{isa}.encoding-templates", "status": "blocked",
                     "predicate": ("D-8(d)'s template: an encoding with symbolic operand fields, split wherever a field changes "
                                   "decoding (e.g. Rd = 31 meaning SP or XZR); the count is >= the emitted opcode variants"),
                     "blocked": (f"which fields change decoding is decided by {what}, which does not exist at this pin; "
                                 "trust-cg's encoder arms pick fields procedurally (width from the operand's register class, FP "
                                 "size from the register, arrangement from operands), so a split read from them would be this "
                                 "script's guess, not a measurement"),
                     "unblock": unblock})

    # relocations
    total = 0
    labels = {"macho": "Mach-O", "elf": "ELF", "coff": "COFF"}
    writer_src = {("macho", "aarch64"): f"{MACHO_RELOC} enum AArch64RelocKind, discriminant <= {rel['last_macho']} (is_elf_only's bound)",
                  ("macho", "x86_64"): f"{MACHO_X86_RELOC} enum X86_64RelocKind",
                  ("elf", "aarch64"): f"{ELF_RELOC} enum AArch64RelocType (values from {ELF_CONSTANTS})",
                  ("elf", "x86_64"): f"{ELF_RELOC} enum X86_64RelocType (values from {ELF_CONSTANTS})",
                  ("coff", "x86_64"): f"{COFF_WRITER} `const IMAGE_REL_AMD64_*`",
                  ("elf", "riscv64"): f"{ELF_RELOC} enum RiscvRelocType (values from {ELF_CONSTANTS})"}
    for (fmt, isa), data in ((k, v) for k, v in rel.items() if isinstance(k, tuple)):
        writer, inv = data["writer"], set(data["inventory"])
        if isa != "riscv64":
            total += len(writer)
        rows.append({"name": f"reloc.{fmt}.{isa}", "value": len(writer), "status": "measured",
                     "predicate": (f"the {labels[fmt]} {isa} relocation types trust-cg's object writer can serialize: {writer_src[(fmt, isa)]}. "
                                   "The writer accepts any value of its type, so this bounds from above what current code paths "
                                   "emit; which kinds a producer reaches is not measured here."
                                   + (" Outside the A64/x86 scope of the design's denominators; recorded because the writer carries it." if isa == "riscv64" else "")),
                     "kinds": [{"name": n, "r_type": v, "abi_name": c, "in_inventory": n in inv} for n, v, c in writer]})
        rows.append({"name": f"reloc.{fmt}.{isa}.inventory", "value": len(inv), "of": f"reloc.{fmt}.{isa}", "status": "measured",
                     "predicate": (f"the named (non-catch-all) rows of trust-cg-verify's `ObjectRelocationKind` ({INVENTORY}) for "
                                   f"{labels[fmt]} {isa}, matched to writer kinds by name: the kinds the certified-output inventory "
                                   "names; a writer kind outside it is represented there only by the pair's `*Other(raw)` row"),
                     "not_in_inventory": [n for n, _, _ in writer if n not in inv]})
    rows.append({"name": "reloc.elf.aarch64.fixup-carriers", "value": len(rel["carriers"]), "status": "measured",
                 "predicate": (f"the AArch64RelocKind variants above is_elf_only's bound ({MACHO_RELOC}): ELF-only fixup carriers "
                               "Mach-O conversion refuses; each maps (aarch64_elf_reloc_kind, an arm returning Ok) to exactly one "
                               "reloc.elf.aarch64 kind, so they add no record kind"),
                 "maps_to": [{"carrier": n, "value": v, "elf_kind": (t[0] if len(t) == 1 else "(none)")} for n, v, t in rel["carriers"]]})
    rows.append({"name": "reloc.a64-x86.total", "value": total, "status": "measured",
                 "predicate": "the sum of reloc.<format>.<isa> over the A64/x86 pairs (Mach-O and ELF for aarch64 and x86_64, COFF for x86_64): (format, ISA, kind) triples"})

    # unwind
    def kinds_used(items):
        return [n for n, _, used in items if used], [n for n, _, used in items if not used]

    used, unused = kinds_used(unw["compact_a64"])
    rows.append({"name": "unwind.compact-unwind.macho.aarch64", "value": len(used), "status": "measured",
                 "predicate": (f"the `UNWIND_ARM64_MODE_*` constants of {FRAME} that `encode_compact_unwind` names: the mode "
                               "field values an AArch64 `__LD,__compact_unwind` entry can carry. The flag constants beside them "
                               f"(UNWIND_HAS_LSDA and the register-pair bits of FRAME mode) are listed, not counted; `used` is "
                               f"whether non-test code of frame.rs beyond the definition, or of {COMPACT_UNWIND}, names it"),
                 "kinds": [{"name": n, "value": f"{v:#010x}"} for n, v, u in unw["compact_a64"] if u],
                 "unused": unused,
                 "flags": [{"name": n, "value": f"{v:#010x}", "used": u} for n, v, u in unw["compact_a64_flags"]]})
    used, unused = kinds_used(unw["compact_x86"])
    rows.append({"name": "unwind.compact-unwind.macho.x86_64", "value": len(used), "status": "measured",
                 "predicate": (f"the `UNWIND_X86_64_MODE_*` constants of {X86_PIPELINE} named in non-test code beyond their "
                               "definition: the mode values an x86-64 `__LD,__compact_unwind` entry can carry"),
                 "kinds": [{"name": n, "value": f"{v:#010x}"} for n, v, u in unw["compact_x86"] if u], "unused": unused})
    for fmt in ("macho", "elf"):
        for isa in ("aarch64", "x86_64"):
            shapes = [s for s in unw["cie"] if s["format"] == fmt and s["isa"] == isa]
            rows.append({"name": f"unwind.dwarf-cfi.cie.{fmt}.{isa}", "value": len(shapes), "status": "measured",
                         "predicate": (f"the `DwarfCie` constructors of {DWARF_CFI} named `{isa}_{'darwin' if fmt == 'macho' else 'elf'}"
                                       "[_with_eh]`, each a CIE shape with its augmentation string (zR: pointer encoding "
                                       "only; zPLR: personality, LSDA and pointer encoding); FDEs reference them"),
                         "kinds": [{"constructor": s["constructor"], "augmentation": s["augmentation"], "eh": s["eh"], "line": s["line"]} for s in shapes]})
    used, unused = kinds_used(unw["cfa"])
    rows.append({"name": "unwind.dwarf-cfi.cfa-opcodes", "value": len(used), "status": "measured",
                 "predicate": (f"the `DW_CFA_*` constants of {DWARF_CFI} used in its non-test code: the CFA instructions the one "
                               "CFI emitter (shared by aarch64 and x86_64, Mach-O `__eh_frame` and ELF `.eh_frame`) writes"),
                 "kinds": [{"name": n, "value": f"{v:#04x}"} for n, v, u in unw["cfa"] if u], "unused": unused})
    used, unused = kinds_used(unw["eh_pe"])
    rows.append({"name": "unwind.dwarf-cfi.pointer-encodings", "value": len(used), "status": "measured",
                 "predicate": f"the `DW_EH_PE_*` constants of {DWARF_CFI} used in its non-test code (CIE/FDE pointer encodings, combined bitwise)",
                 "kinds": [{"name": n, "value": f"{v:#04x}"} for n, v, u in unw["eh_pe"] if u], "unused": unused})
    rows.append({"name": "unwind.lsda.pointer-encodings", "value": len(unw["dwehpe"]), "status": "measured",
                 "predicate": (f"the variants of `enum DwEhPe` ({EH}), the LSDA's value encodings; the LSDA emitter is shared by "
                               "aarch64 and x86_64 and serialized into Mach-O `__gcc_except_tab` and ELF `.gcc_except_table`"),
                 "kinds": [{"name": n, "value": f"{v:#04x}"} for n, v in unw["dwehpe"]]})
    rows.append({"name": "unwind.lsda.record-structs", "value": len(unw["lsda_structs"]), "status": "measured",
                 "predicate": f"the non-test `pub struct` items of {EH}: the LSDA (ExceptionTable, with its header) and its call-site, action and type-table records",
                 "kinds": [{"name": n, "line": ln} for n, ln in unw["lsda_structs"]]})
    used, unused = kinds_used(unw["seh"])
    rows.append({"name": "unwind.seh.coff.x86_64", "value": len(used), "status": "measured",
                 "predicate": (f"the `UWOP_*` unwind-code constants of {X86_PIPELINE} used in its non-test code: the UNWIND_CODE "
                               f"operations the COFF `.xdata` UNWIND_INFO records carry (with `.pdata` RUNTIME_FUNCTION entries; "
                               f"{COFF_WRITER} has {', '.join(unw['seh_sections'])}). The COFF writer's machine constants are "
                               f"{', '.join(unw['coff_machines'])}, so there is no AArch64 COFF row. "
                               "The JIT's own Windows tables (jit.rs) are not an object format and are not counted"),
                 "kinds": [{"name": n, "value": v} for n, v, u in unw["seh"] if u], "unused": unused})
    return rows


# --------------------------------------------------------------------------
# the record
# --------------------------------------------------------------------------


def q(value) -> str:
    return json.dumps(value, ensure_ascii=False)


def tv(value) -> str:
    if isinstance(value, bool):
        return "true" if value else "false"
    if isinstance(value, int):
        return str(value)
    if isinstance(value, str):
        return q(value)
    if isinstance(value, dict):
        return "{ " + ", ".join(f"{q(k)} = {tv(v)}" for k, v in value.items()) + " }" if value else "{}"
    if isinstance(value, (list, tuple)):
        if not value:
            return "[]"
        if all(isinstance(v, str) and len(v) < 40 for v in value) and len(value) <= 6:
            return "[" + ", ".join(tv(v) for v in value) + "]"
        return "[\n" + "".join(f"  {tv(v)},\n" for v in value) + "]"
    raise TypeError(f"no TOML rendering for {type(value).__name__}")


ROW_ORDER = ("name", "value", "of", "status", "predicate", "source", "blocked", "unblock", "digest", "by_category",
             "design", "added_since_design_pin", "removed_since_design_pin", "not_in_inventory", "unused", "flags",
             "kinds", "maps_to", "variants")


def explain(rows: list[dict], cg_commit: str, old_pin: str | None) -> list[str]:
    by = {r["name"]: r for r in rows}
    lines = [f"trust-cg at the superproject's gitlink {cg_commit}; the design's trust-cg pin {old_pin or '(unreadable)'} is read only to test [M†].", ""]
    lines.append("How this measurement compares with the design's \"294 and 232 opcode variants\" [M†]:")
    for key in ("a64.opcode-variants", "x86.opcode-variants"):
        r = by[key]
        lines.append(f"* {key} = {r['value']}.")
        lines += [f"  {note}" for note in r.get("design", [])]
        if r.get("added_since_design_pin") is not None:
            lines.append(f"  since the design's pin: {len(r['added_since_design_pin'])} variants added, {len(r['removed_since_design_pin'])} removed.")
    a, x = by["a64.emitted-templates"], by["x86.emitted-templates"]

    def cats(row: dict) -> str:
        return " + ".join(f"{v} {k}" for k, v in row["by_category"].items())

    lines += [
        "* The opcode-variant count is not the emitted-template count:",
        f"  a64.emitted-templates = {a['value']} ({cats(a)}); x86.emitted-templates = {x['value']} ({cats(x)}).",
        f"  Not emitted: a64 {by['a64.not-emitted']['value']} ({cats(by['a64.not-emitted'])}); "
        f"x86 {by['x86.not-emitted']['value']} ({cats(by['x86.not-emitted'])}).",
        f"  {by['a64.emitted-templates.opcode-pseudo']['value']} of the a64 emitted templates are variants that AArch64Opcode::is_pseudo() lists",
        "  as having no hardware encoding; their flags let them reach the encoder, which writes a constant word",
        "  (BRK #1 or NOP) for them (row a64.emitted-templates.opcode-pseudo).",
    ]
    if "a64.emitted-templates.at-design-pin" in by:
        lines.append(f"  At the design's pin the same predicate gives a64 {by['a64.emitted-templates.at-design-pin']['value']}, "
                     f"x86 {by['x86.emitted-templates.at-design-pin']['value']}.")
    lines.append(f"* Relocation kinds (writer surface) over the A64/x86 (format, ISA) pairs: {by['reloc.a64-x86.total']['value']}.")
    return lines


def render(rows: list[dict], inputs: dict, measured_at: str, cg_commit: str, old_pin: str | None) -> str:
    out = [
        f"# E0.12 denominator `{KEY}`: trust-cg's emitted A64/x86 templates, relocation and unwind record kinds.",
        "#",
        f"# GENERATED by {SCRIPT_REL} --write; checked by its --check, which re-measures from git objects and",
        "# fails on any difference (measured_at_commit and the design notes excepted). Do not edit.",
        "# Design of record: docs/design/2026-09-16-trust-core-architecture.md §5.2 Stage 0.5 (exit E0.12); D-8, D-9.",
        "#",
        *[f"# {line}".rstrip() for line in explain(rows, cg_commit, old_pin)],
        "",
        f"schema = {q(SCHEMA)}",
        f"key = {q(KEY)}",
        f"design = {q(C.DESIGN_REL)}",
        f"script = {q(SCRIPT_REL)}",
        f"exit = {q('E0.12')}",
        f"consumers = {tv(['D-8 I-TEMPLATE-LEMMA, I-DERIVATION-OWED', 'K2 extrapolated one-time template check', 'E1.6.1 interim template records', 'E1.8.4', 'E2.7.2 x86 schema lemmas', 'E2.12.2 and E3.1.3 A64 schema lemmas', 'D-9 reloc and table semantics; E1.5.3, E2.6.1, E2.6.3, E2.6.7'])}",
        "# The pin: the superproject commit this record was measured at. scripts/trust_core/denominators.py",
        "# re-measures every row at it (--rev); this script's own --check measures at --rev (default HEAD)",
        "# and ignores this line, so it also says whether HEAD still gives the record.",
        f"measured_at_commit = {q(measured_at)}",
    ]
    for name, data in inputs.items():
        out += ["", f"[inputs.{name}]"]
        for k, v in data.items():
            out.append(f"{k} = {tv(v)}")
    for row in rows:
        out += ["", "[[row]]"]
        for key in ROW_ORDER:
            if key in row:
                out.append(f"{key} = {tv(row[key])}")
        extra = [k for k in row if k not in ROW_ORDER]
        if extra:
            raise TypeError(f"row {row['name']} has unrendered keys {extra}")
    return "\n".join(out) + "\n"


def measured_content(text: str) -> dict:
    data = tomllib.loads(text)
    data.pop("measured_at_commit", None)
    for row in data.get("row", []):
        row.pop("design", None)
    return data


# --------------------------------------------------------------------------
# self-test: each classification rule refuses a mutation
# --------------------------------------------------------------------------

MUTATIONS = (
    ("a nested helper match that drops a variant refuses it", A64_ENCODE,
     "        LdpRI => (true, PairMemoryMode::Offset, false),\n", "", "a64", "LdpRI", "refused"),
    ("a top-level arm made a bare refusal refuses it", A64_ENCODE,
     "        AArch64Opcode::AlignNop => Ok(NOP),", "        AArch64Opcode::AlignNop => Err(EncodeError::PseudoInstruction(inst.opcode)),",
     "a64", "AlignNop", "refused"),
    ("IS_PSEUDO in default_flags skips it", A64_OPS,
     "            AlignNop => InstFlags::HAS_SIDE_EFFECTS,", "            AlignNop => InstFlags::IS_PSEUDO,", "a64", "AlignNop", "skipped"),
    ("without the emitter's interception a refused fixup form is refused", PIPELINE,
     "            } else if inst.opcode == AArch64Opcode::BlrTlsdesc {", "            } else if false {", "a64", "BlrTlsdesc", "refused"),
    ("an x86 helper's catch-all refusal refuses it", X86_ENCODE,
     "            X86Opcode::Pslld | X86Opcode::Psrld | X86Opcode::Psrad => 0x72,",
     "            X86Opcode::Psrld | X86Opcode::Psrad => 0x72,", "x86", "Pslld", "refused"),
)


def self_test(tree) -> list[str]:
    failures = []

    def classify(patch):
        t = Tree(tree.rev, tree)
        if patch:
            rel, old, new = patch
            text = tree.text(rel) or ""
            if text.count(old) != 1:
                return None
            t.cache[rel] = Source(rel, text.replace(old, new))
        f = C.Findings()
        cats = {("a64", r.name): r.category for r in measure_a64(t, f)["rows"]}
        cats.update({("x86", r.name): r.category for r in measure_x86(t, f)["rows"]})
        return cats

    base = classify(None)
    for what, rel, old, new, isa, name, want in MUTATIONS:
        got = classify((rel, old, new))
        if got is None:
            failures.append(f"SELFTEST: {what}: the mutation's anchor is not unique in {rel} at this pin")
            continue
        changed = sorted(k for k in base if base[k] != got.get(k))
        if got.get((isa, name)) != want or changed != [(isa, name)] or base[(isa, name)] == want:
            failures.append(f"SELFTEST: {what}: {isa} {name} is {got.get((isa, name))} (baseline {base[(isa, name)]}, want {want}); changed {changed}")
        else:
            print(f"  self-test ok: {what} ({isa} {name}: {base[(isa, name)]} -> {want})")
    return failures


# --------------------------------------------------------------------------
# main
# --------------------------------------------------------------------------


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n", 1)[0])
    parser.add_argument("--repo", type=Path, default=C.REPO_ROOT, help="the superproject (default: this checkout)")
    parser.add_argument("--rev", default="HEAD", help="the superproject revision whose trust-cg gitlink is measured (default HEAD)")
    parser.add_argument("--record", type=Path, help=f"the record (default {RECORD_REL} in --repo)")
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--write", action="store_true", help="rewrite the record from this measurement")
    mode.add_argument("--check", action="store_true", help="fail unless the record equals this measurement")
    parser.add_argument("--list", action="store_true", help="print every row's variants and kinds")
    parser.add_argument("--self-test", action="store_true", help="also run the classifier's mutation self-test")
    args = parser.parse_args(argv)
    repo = args.repo.resolve()
    record = args.record or repo / RECORD_REL
    findings = C.Findings()
    try:
        commit = (C.git(repo, "rev-parse", "--verify", f"{args.rev}^{{commit}}") or "").strip()
        if not C.HEX40.match(commit):
            raise Fatal(f"{repo}: {args.rev} is not a commit")
        tree = C.first_party_tree(repo, SUBMODULE, commit)
        if tree is None:
            raise Fatal(f"{repo}: first-party/{SUBMODULE} at {commit[:12]} has no gitlink or no object store")
        checkout = repo / "first-party" / SUBMODULE
        head = (C.git(checkout, "rev-parse", "HEAD") or "").strip() if (checkout / ".git").exists() else ""
        t = Tree(tree.rev, tree)
        a64 = measure_a64(t, findings)
        x86 = measure_x86(t, findings)
        rel = measure_relocs(t, findings)
        unw = measure_unwind(t, findings)
        claims, old_short = design_facts(repo, commit)
        old, old_pin, old_inputs = None, None, None
        if old_short:
            full = (C.git(tree.repo, "rev-parse", "--verify", f"{old_short}^{{commit}}", git_dir=tree.git_dir) or "").strip()
            if C.HEX40.match(full):
                old_pin = full
                ot = Tree(full, C.GitTree(tree.repo, full, git_dir=tree.git_dir))
                old_findings = C.Findings()
                old = {"a64": measure_a64(ot, old_findings), "x86": measure_x86(ot, old_findings)}
                for v in old_findings.violations:
                    findings.add("DESIGN-PIN", v)
                old_inputs = {"what": "trust-cg at the commit the design's status block names, read only to test the design's [M†] numbers",
                              "design_says": old_short, "commit": full, "files": ot.blobs()}
            else:
                findings.add("DESIGN-PIN", f"the design's trust-cg pin {old_short} is not in {tree.repo}")
        else:
            findings.add("DESIGN-PIN", "the design's status block names no single trust-cg pin")
    except Fatal as error:
        print(f"{KEY}: {error}", file=sys.stderr)
        return 2
    rows = build_rows(a64, x86, rel, unw, old, old_short, claims)
    inputs = {"trust-cg": {
        "submodule": f"first-party/{SUBMODULE}",
        "gitlink": tree.rev,
        "read": "git objects of the submodule's store at the gitlink (common.first_party_tree); never a working tree",
        "files": t.blobs(),
    }}
    if old_inputs:
        inputs["design-pin"] = old_inputs
    text = render(rows, inputs, commit, tree.rev, old_short)
    try:
        tomllib.loads(text)
    except tomllib.TOMLDecodeError as error:  # pragma: no cover - a renderer defect
        findings.add("RECORD", f"the rendered record is not TOML: {error}")

    print(f"{KEY}: superproject {commit}; first-party/{SUBMODULE} gitlink {tree.rev}"
          + (f" (checkout HEAD {head}{'' if head == tree.rev else ' DIFFERS; objects at the gitlink were read'})" if head else ""))
    for row in rows:
        value = row.get("value", "-")
        of = f" of {row['of']}" if "of" in row else ""
        print(f"  {row['name']:<44} {str(value):>5}{of}  [{row['status']}]")
        for note in row.get("design", []):
            print(f"      {note}")
        if row["status"] == "blocked":
            print(f"      blocked: {row['blocked']}\n      unblock: {row['unblock']}")
        if args.list:
            for item in row.get("variants", []) + row.get("kinds", []) + row.get("maps_to", []):
                print(f"      {json.dumps(item, ensure_ascii=False)}")
    if args.self_test:
        for failure in self_test(tree):
            findings.add("SELFTEST", failure)

    status = 0
    if args.write and not findings.violations:
        record.parent.mkdir(parents=True, exist_ok=True)
        record.write_text(text, encoding="utf-8")
        print(f"{KEY}: wrote {record}")
    elif args.check:
        try:
            committed = measured_content(record.read_text(encoding="utf-8"))
        except (OSError, tomllib.TOMLDecodeError) as error:
            findings.add("RECORD", f"{record}: {error}")
            committed = None
        if committed is not None and committed != measured_content(text):
            findings.add("RECORD", f"{record} differs from a re-measurement at {commit}; re-run with --write and review the diff")
        elif committed is not None:
            print(f"{KEY}: {record} matches the re-measurement")
    for violation in findings.violations:
        print(violation, file=sys.stderr)
        status = 1
    return status


if __name__ == "__main__":
    raise SystemExit(main())
