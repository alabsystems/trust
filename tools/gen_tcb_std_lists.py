#!/usr/bin/env python3
"""Generate the counted std name lists section of docs/TCB.md.

Plan of record: docs/design/2026-08-19-verified-sysroot-scoping.md, §5 step 2a —
"Publish it. `docs/TCB.md` enumerates 11 proof-authority classes but does not
count the std name lists. Add a generated section: the 180 `EXACT_TOTAL`
entries, the `total_std_iterator_ty` accepted type set, the four drop-glue
allowlists, the `is_total_rustc_intrinsic` names. A trusted fact that is
counted is manageable; one that is diffuse is not."

The lists extracted, and where they live:

  1. `EXACT_TOTAL`                — crates/trust-ir-bridge/src/lower.rs
  2. `is_total_rustc_intrinsic`   — crates/trust-ir-bridge/src/lower.rs
  3. `total_std_iterator_ty`      — compiler/rustc_mir_transform/src/trust_verify.rs
  4. the four drop-glue allowlists (is_total_drop_std_leaf,
     is_audited_panic_free_std_drop, is_never_drops_contents_wrapper,
     is_std_owning_or_scaffold)   — crates/trust-ir-bridge/src/lower.rs
  5. the `@trust-total-to-string::` stamp's admitted `Self` set
     (to_string_self_ty_is_foundational, TO_STRING_STR_MAX_REF_DEPTH)
                                  — crates/trust-mir-extract/src/convert.rs

Design rules this file obeys (same contract as tools/preflight.py):

  * The doc section is GENERATED, never hand-copied: hand-copied lists rot.
    Everything emitted is parsed out of the shipping source at run time.
  * Drift is LOUD: every extraction is anchored on an exact source pattern
    (the const declaration, the fn signature, the fail-closed `_ => false`
    arm, the crate-identity gate).  If an anchor stops matching — the list
    was renamed, restructured, or a matching form this parser does not
    understand was added — the script exits NONZERO instead of emitting a
    plausible-looking but wrong enumeration.  In particular, a string
    literal inside one of the drop-glue allowlist functions that cannot be
    classified (prefix gate / exact / suffix / substring / PARTS entry) is
    a hard failure, so a new matching idiom cannot silently drop entries
    from the published count.
  * Default mode only prints; `--write` splices between explicit BEGIN/END
    markers that must already exist in docs/TCB.md; `--check` fails (exit 1)
    when the on-disk section differs from a fresh generation, so the doc
    cannot silently go stale.  Output is a pure function of the source
    files — no timestamps — so `--check` is byte-stable.

Exit codes: 0 ok; 1 anchor drift, unclassifiable literal, empty list, or
--check mismatch; 2 usage / missing file / missing markers.
"""

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

LOWER_RS = "crates/trust-ir-bridge/src/lower.rs"
TRUST_VERIFY_RS = "compiler/rustc_mir_transform/src/trust_verify.rs"
CONVERT_RS = "crates/trust-mir-extract/src/convert.rs"
PANIC_FREE_INTRINSIC_RS = "crates/trust-types/src/panic_free_intrinsic.rs"

# Lang item -> the sysroot crate that DEFINES it. `crate_is_authentic_foundational`
# decides "foundational" by which crate OWNS one of these; a disjunct naming any
# other lang item (or any other shape) is anchor drift, because this table is
# what the published text says each crate is recognised by.
FOUNDATIONAL_LANG_ITEM_OWNER = {
    "sized_trait": "core",
    "owned_box": "alloc",
    "string": "alloc",
    "panic_impl": "std",
}

# The `TyKind` arms of `to_string_self_ty_is_foundational`, and what each one
# admits. A new arm is anchor drift until it is described here: the published
# set must say what the code accepts, not merely how many arms it has.
TO_STRING_SELF_ARMS = {
    "Bool": "bare `bool`",
    "Char": "bare `char`",
    "Int": "every bare signed integer (`i8` … `i128`, `isize`)",
    "Uint": "every bare unsigned integer (`u8` … `u128`, `usize`)",
    "Str": "`str`",
    "Ref": "a chain of 1 to {depth} SHARED references ending at `str` "
    "(`to_string_str_ref_chain_depth`); no other reference",
    "Adt": "bare `alloc::string::String`: the `String` lang item AND the "
    "compiler's own `alloc` by artifact residency (`is_real_alloc_crate`), "
    "no generic arguments",
}
TCB_MD = "docs/TCB.md"

BEGIN_MARKER = "<!-- BEGIN GENERATED tcb-std-name-lists"
END_MARKER = "<!-- END GENERATED tcb-std-name-lists -->"
BEGIN_LINE = (
    "<!-- BEGIN GENERATED tcb-std-name-lists -- regenerate with: "
    "python3 tools/gen_tcb_std_lists.py --write ; verify with: "
    "python3 tools/gen_tcb_std_lists.py --check. "
    "Everything between these markers is overwritten; do not edit by hand. -->"
)

# The four drop-glue allowlist functions, in the order the plan names them.
DROP_GLUE_FNS = (
    "is_total_drop_std_leaf",
    "is_audited_panic_free_std_drop",
    "is_never_drops_contents_wrapper",
    "is_std_owning_or_scaffold",
)


def die(msg: str, code: int = 1) -> "sys.NoReturn":
    sys.stderr.write(f"gen_tcb_std_lists: FAIL: {msg}\n")
    raise SystemExit(code)


def read(root: Path, rel: str) -> str:
    p = root / rel
    if not p.is_file():
        die(f"source file missing: {p}", 2)
    return p.read_text(encoding="utf-8")


def strip_line_comment(line: str) -> str:
    """Drop a trailing `// ...` comment, respecting string literals."""
    in_str = False
    i = 0
    while i < len(line):
        c = line[i]
        if in_str:
            if c == "\\":
                i += 2
                continue
            if c == '"':
                in_str = False
        elif c == '"':
            in_str = True
        elif c == "/" and line[i : i + 2] == "//":
            return line[:i]
        i += 1
    return line


def code_only(text: str) -> str:
    """The text with `// ...` comments removed, line structure preserved."""
    return "\n".join(strip_line_comment(l) for l in text.split("\n"))


def fn_body(source: str, fn_name: str, rel: str) -> str:
    """The exact body text of `fn fn_name(...)`, by brace counting.

    Comments are stripped first so braces in comments cannot skew the count;
    string literals are tracked so braces in strings cannot either.
    """
    stripped = code_only(source)
    # A definition line starts with (indented, optionally pub) `fn name`,
    # optionally generic (`fn name<'tcx>(`); call sites never match this shape.
    defs = [
        m.start(1)
        for m in re.finditer(
            r"(?:^|\n)\s*(?:pub(?:\([^)]*\))?\s+)?(fn "
            + re.escape(fn_name)
            + r")\s*(?:<[^>]*>)?\s*\(",
            stripped,
        )
    ]
    if len(defs) != 1:
        die(
            f"anchor drift: expected exactly 1 definition of `fn {fn_name}` in "
            f"{rel}, found {len(defs)}"
        )
    i = stripped.index("{", defs[0])
    depth = 0
    in_str = False
    j = i
    while j < len(stripped):
        c = stripped[j]
        if in_str:
            if c == "\\":
                j += 2
                continue
            if c == '"':
                in_str = False
        elif c == '"':
            in_str = True
        elif c == "{":
            depth += 1
        elif c == "}":
            depth -= 1
            if depth == 0:
                return stripped[i : j + 1]
        j += 1
    die(f"anchor drift: unbalanced braces walking `fn {fn_name}` in {rel}")


def const_str_array(text: str, decl: str, rel: str) -> list[str]:
    """Entries of `const NAME: &[&str] = &[ ... ];`, comments skipped."""
    lines = text.split("\n")
    starts = [i for i, l in enumerate(lines) if decl in l]
    if len(starts) != 1:
        die(f"anchor drift: expected exactly 1 `{decl}` in {rel}, found {len(starts)}")
    out: list[str] = []
    closed = False
    for l in lines[starts[0] + 1 :]:
        t = l.strip()
        if t.startswith("];"):
            closed = True
            break
        if t.startswith("//"):
            continue
        out += re.findall(r'"((?:[^"\\]|\\.)*)"', strip_line_comment(l))
    if not closed:
        die(f"anchor drift: `{decl}` in {rel} has no closing `];`")
    if not out:
        die(f"anchor drift: `{decl}` in {rel} parsed to zero entries")
    return out


def matches_bang_literals(body: str, fn_name: str) -> list[tuple[int, int, str]]:
    """(start, end, literal) for every string inside a `matches!(...)` span."""
    out: list[tuple[int, int, str]] = []
    for m in re.finditer(r"matches!\(", body):
        depth = 0
        j = m.end() - 1
        in_str = False
        while j < len(body):
            c = body[j]
            if in_str:
                if c == "\\":
                    j += 2
                    continue
                if c == '"':
                    in_str = False
            elif c == '"':
                in_str = True
            elif c == "(":
                depth += 1
            elif c == ")":
                depth -= 1
                if depth == 0:
                    break
            j += 1
        else:
            die(f"anchor drift: unbalanced `matches!(` in `{fn_name}`")
        span = body[m.start() : j + 1]
        for s in re.finditer(r'"((?:[^"\\]|\\.)*)"', span):
            out.append((m.start() + s.start(), m.start() + s.end(), s.group(1)))
    return out


# ---------------------------------------------------------------------------
# Extractors — one per published list.
# ---------------------------------------------------------------------------


def extract_exact_total(lower: str) -> list[str]:
    # The CONSUMER is anchored too, not just the declaration: if the membership
    # test stops being an exact `contains` on the normalized path (say, someone
    # widens it to a prefix or substring match), every published entry silently
    # covers MORE than its name says, and this section under-reports the
    # trusted surface while still counting 180. Found as a gap by the step-2/3
    # verification pass; the PARTS lists already had this treatment.
    if "EXACT_TOTAL.contains(&normalized.as_str())" not in lower:
        die(
            "anchor drift: EXACT_TOTAL is no longer consumed via an exact "
            "`contains` on the normalized path — the published list would no "
            "longer mean what this section claims"
        )
    entries = const_str_array(lower, "const EXACT_TOTAL: &[&str] = &[", LOWER_RS)
    # A repeated entry is inert for the membership test, but the published
    # "N entries" would count it twice and over-state the trusted surface (five
    # repeats were found and removed 2026-10-15: 240 listed, 235 distinct).
    # Refuse it, so the list stays a set and the count is the count of distinct
    # names.
    seen: set[str] = set()
    repeated = [e for e in entries if e in seen or seen.add(e)]
    if repeated:
        die(
            f"`EXACT_TOTAL` in {LOWER_RS} lists {len(set(repeated))} name(s) more than "
            f"once ({', '.join(sorted(set(repeated)))}); delete the later copies "
            "so the published count is the count of distinct names"
        )
    return entries


def extract_intrinsics(lower: str) -> list[str]:
    body = fn_body(lower, "is_total_rustc_intrinsic", LOWER_RS)
    if "TRUST_RUSTC_INTRINSIC_PATH_PREFIX" not in body:
        die(
            "anchor drift: `is_total_rustc_intrinsic` no longer gates on "
            "TRUST_RUSTC_INTRINSIC_PATH_PREFIX"
        )
    names = [lit for _, _, lit in matches_bang_literals(body, "is_total_rustc_intrinsic")]
    if not names:
        die("anchor drift: `is_total_rustc_intrinsic` matches! parsed to zero names")
    # Every string literal in the body must be one of the matched names, bar
    # the `rsplit("::")` path-segmentation plumbing — a new literal anywhere
    # else would be silently uncounted, so it fails instead.
    all_lits = re.findall(r'"((?:[^"\\]|\\.)*)"', body)
    extra = sorted(set(all_lits) - set(names) - {"::"})
    if extra:
        die(
            "anchor drift: `is_total_rustc_intrinsic` contains string literals "
            f"outside its matches! arm ({extra}); parser no longer covers the "
            "function"
        )
    return names


PANIC_FREE_ANCHOR = "pub const PANIC_FREE_RUSTC_INTRINSICS: &[PanicFreeIntrinsicEntry] = &["
PANIC_FREE_ENTRY = re.compile(
    r'^entry\("(\w+)", (16|32|64|128), (Unary|Binary|PowI), (true|false)\),$'
)


def extract_panic_free_intrinsics(src: str) -> list[tuple[str, str, str, str]]:
    """The std-call-summaries P2 panic-freedom-only intrinsic list, entry by entry.

    Anchored on the const declaration, its `];` terminator, and the classifier
    that consumes it; every non-comment line in between must be one `entry(...)`
    call, so an entry spelled another way is a hard failure, never uncounted.
    """
    start = src.find(PANIC_FREE_ANCHOR)
    if start < 0:
        die(f"anchor drift: `{PANIC_FREE_ANCHOR}` not found in {PANIC_FREE_INTRINSIC_RS}")
    end = src.find("\n];", start)
    if end < 0:
        die("anchor drift: PANIC_FREE_RUSTC_INTRINSICS has no `];` terminator")
    if "panic_free_intrinsic_entry(name)" not in src:
        die(
            "anchor drift: `classify_panic_free_intrinsic` no longer resolves names "
            "through `panic_free_intrinsic_entry` — the published list would no "
            "longer be the classifier's whole domain"
        )
    out = []
    for raw in src[start + len(PANIC_FREE_ANCHOR) : end].splitlines():
        line = strip_line_comment(raw).strip()
        if not line:
            continue
        m = PANIC_FREE_ENTRY.match(line)
        if not m:
            die(f"anchor drift: unparseable PANIC_FREE_RUSTC_INTRINSICS line: {raw!r}")
        out.append(m.groups())
    if not out:
        die("anchor drift: PANIC_FREE_RUSTC_INTRINSICS parsed to zero entries")
    return out


def extract_iterator_arms(verify: str) -> list[dict]:
    body = fn_body(verify, "total_std_iterator_ty", TRUST_VERIFY_RS)
    # Fail-closed anchors: the local-DefId rejection, the real-crate gate, and
    # the wildcard-false fallback. Losing any of these changes the semantics
    # this section documents, so each is a hard anchor.
    if "did.is_local()" not in body:
        die("anchor drift: `total_std_iterator_ty` lost its local-DefId rejection")
    crate_gate = re.search(
        r'crate_name\(did\.krate\)\.as_str\(\),\s*((?:"\w+"\s*\|\s*)*"\w+")', body
    )
    if crate_gate:
        gate = {"kind": "crate-name", "crates": re.findall(r'"(\w+)"', crate_gate.group(1))}
    elif "if !crate_is_authentic_foundational(tcx, did.krate) {" in body:
        # The gate is LANG-ITEM OWNERSHIP compared by `CrateNum`, not the
        # `--crate-name` string. Its disjuncts are PARSED, not assumed: a
        # widened body (`true || …`, a new lang item, a name test) fails here
        # instead of re-certifying the published sentence.
        gate = {"kind": "lang-item", "anchors": foundational_lang_item_anchors(verify)}
    else:
        die("anchor drift: `total_std_iterator_ty` crate-identity gate not found")
    if "_ => false" not in body:
        die("anchor drift: `total_std_iterator_ty` lost its `_ => false` fallback")
    mt = re.search(r"match tcx\.item_name\(did\)\.as_str\(\) \{", body)
    if not mt:
        die("anchor drift: `total_std_iterator_ty` item-name match not found")
    # Arm starts: lines whose stripped form begins with a string literal.
    lines = body[mt.end() :].split("\n")
    arm_line_idx = [i for i, l in enumerate(lines) if l.strip().startswith('"')]
    if not arm_line_idx:
        die("anchor drift: `total_std_iterator_ty` match parsed to zero arms")
    arms: list[dict] = []
    for k, i in enumerate(arm_line_idx):
        end = arm_line_idx[k + 1] if k + 1 < len(arm_line_idx) else len(lines)
        arm_text = "\n".join(lines[i:end])
        pat = arm_text.split("=>")[0]
        heads = re.findall(r'"(\w+)"', pat)
        if not heads:
            die("anchor drift: iterator match arm with no head-type literal")
        anchors = re.findall(r'def_path_has_module_segment\(tcx, did, "(\w+)"\)', arm_text)
        recursive = "total_std_iterator_ty(" in arm_text
        # DC-1 (2026-10-04): an arm that ALSO requires the inner iterator to
        # yield at most `usize::MAX` items (`Enumerate`, whose counter is
        # overflow-checked in the caller's profile).
        len_bounded = "total_std_iterator_len_fits_usize(" in arm_text
        int_only = "ty::Int(_)" in arm_text and "ty::Uint(_)" in arm_text
        pattern_gated = "str_pattern_ty_is_core(" in arm_text
        both_sides = bool(re.search(r"&&\s*\n?\s*total_std_iterator_ty\(", arm_text)) or (
            arm_text.count("total_std_iterator_ty(") >= 2
        )
        for h in heads:
            arms.append(
                {
                    "head": h,
                    "anchors": anchors,
                    "recursive": recursive,
                    "len_bounded": len_bounded and recursive,
                    "int_only": int_only,
                    "pattern_gated": pattern_gated,
                    "both_sides": both_sides and recursive,
                }
            )
    return [gate] + arms


LANG_ITEM_OWNERSHIP = re.compile(
    r"^tcx\.lang_items\(\)\.(\w+)\(\)\.is_some_and\(\|d\|d\.krate==krate\)$"
)

# The `owns` shorthand `crate_is_authentic_foundational` binds before its
# disjunction (whitespace removed). A disjunct may spell `owns(lang_items.X())`
# only when the body opens with exactly this prelude, so the shorthand cannot
# be rebound to something that is not an ownership test.
OWNS_PRELUDE = (
    "letlang_items=tcx.lang_items();"
    "letowns=|item:Option<DefId>|item.is_some_and(|d|d.krate==krate);"
)
OWNS_CALL = re.compile(r"^owns\(lang_items\.(\w+)\(\)\)$")

# ARTIFACT RESIDENCY (R2, 2026-09-28). Every predicate of the family must END
# with this conjunct, and its helper's body must be exactly the extractor's rule.
# Lang-item ownership is a source attribute that a `#![no_std]` graph leaves
# uncontested, so a body without the conjunct is anchor drift: the published
# text would describe an identity test the code no longer makes.
RESIDENCY_CONJUNCT = "&&crate_is_compiler_resident_sysroot(tcx,krate)"
RESIDENCY_FN = "crate_is_compiler_resident_sysroot"
RESIDENCY_BODY = "{trust_mir_extract::is_real_sysroot_crate(tcx,krate)}"

# The two single-anchor members of the family, and the ONE lang item each may
# test. Validated on every run, not only when the foundational body calls them.
AUTHENTIC_MEMBER_ANCHOR = {
    "crate_is_authentic_core": "sized_trait",
    "crate_is_authentic_std": "panic_impl",
}


def outer_parens_enclose_all(expr: str) -> bool:
    """True iff `expr` is `( … )` with the first `(` matching the last `)`."""
    if not (expr.startswith("(") and expr.endswith(")")):
        return False
    depth = 0
    for i, c in enumerate(expr):
        if c == "(":
            depth += 1
        elif c == ")":
            depth -= 1
            if depth == 0 and i != len(expr) - 1:
                return False
    return depth == 0


def residency_helper_is_the_sysroot_rule(verify: str) -> None:
    code = re.sub(r"\s+", "", fn_body(verify, RESIDENCY_FN, TRUST_VERIFY_RS))
    if code != RESIDENCY_BODY:
        die(
            f"anchor drift: `{RESIDENCY_FN}` is no longer exactly "
            f"`trust_mir_extract::is_real_sysroot_crate(tcx, krate)` (found `{code}`); "
            "the published residency text would be wrong"
        )


def lang_item_disjuncts(verify: str, fn_name: str) -> list[str]:
    """The lang items `fn_name`'s body tests ownership of, one per `||` disjunct.

    The body must be `OWNERSHIP && crate_is_compiler_resident_sysroot(tcx,
    krate)`, where OWNERSHIP is a single disjunct or a parenthesized `||` chain
    (optionally after the `owns` prelude). Every disjunct must be exactly
    `tcx.lang_items().<item>().is_some_and(|d| d.krate == krate)`,
    `owns(lang_items.<item>())` under the prelude, or a call to one of the two
    sibling helpers, which are parsed the same way. Anything else — a constant,
    a name comparison, a missing or moved residency conjunct — is anchor drift.
    """
    body = fn_body(verify, fn_name, TRUST_VERIFY_RS)
    code = re.sub(r"\s+", "", body)
    if not (code.startswith("{") and code.endswith("}")):
        die(f"anchor drift: `{fn_name}` body is not a single expression block")
    expr = code[1:-1]
    owns_bound = expr.startswith(OWNS_PRELUDE)
    if owns_bound:
        expr = expr[len(OWNS_PRELUDE) :]
    if not expr.endswith(RESIDENCY_CONJUNCT):
        die(
            f"anchor drift: `{fn_name}` does not end with the residency conjunct "
            f"`&& {RESIDENCY_FN}(tcx, krate)` (lang-item ownership alone is not "
            "sysroot identity; the published gate text would be wrong)"
        )
    ownership = expr[: -len(RESIDENCY_CONJUNCT)]
    if outer_parens_enclose_all(ownership):
        ownership = ownership[1:-1]
    elif "||" in ownership or "&&" in ownership:
        # `A || B && R` is `A || (B && R)`: the conjunct would not cover A.
        die(
            f"anchor drift: `{fn_name}`'s ownership test is not parenthesized, so "
            "the residency conjunct does not cover every disjunct"
        )
    items: list[str] = []
    for disjunct in ownership.split("||"):
        m = LANG_ITEM_OWNERSHIP.match(disjunct) or (owns_bound and OWNS_CALL.match(disjunct))
        if m:
            items.append(m.group(1))
        elif disjunct in ("crate_is_authentic_core(tcx,krate)", "crate_is_authentic_std(tcx,krate)"):
            if fn_name != "crate_is_authentic_foundational":
                die(f"anchor drift: `{fn_name}` recurses into `{disjunct}`")
            items.extend(lang_item_disjuncts(verify, disjunct.split("(")[0]))
        else:
            die(
                f"anchor drift: `{fn_name}` has a disjunct this generator does not "
                f"describe: `{disjunct}` (the published gate text would be wrong)"
            )
    if not items:
        die(f"anchor drift: `{fn_name}` parsed to zero lang-item anchors")
    return items


def foundational_lang_item_anchors(verify: str) -> list[tuple[str, str]]:
    """`(crate, lang item)` for every ownership test `crate_is_authentic_foundational` makes.

    Also validates, on every run, the residency helper and the two
    single-anchor members of the family, whose bodies the published text
    describes whether or not the foundational body calls them.
    """
    residency_helper_is_the_sysroot_rule(verify)
    for member, item in AUTHENTIC_MEMBER_ANCHOR.items():
        found = lang_item_disjuncts(verify, member)
        if found != [item]:
            die(f"anchor drift: `{member}` tests ownership of {found}, expected exactly [`{item}`]")
    anchors: list[tuple[str, str]] = []
    for item in lang_item_disjuncts(verify, "crate_is_authentic_foundational"):
        owner = FOUNDATIONAL_LANG_ITEM_OWNER.get(item)
        if owner is None:
            die(
                f"anchor drift: `crate_is_authentic_foundational` tests ownership of "
                f"lang item `{item}`, which FOUNDATIONAL_LANG_ITEM_OWNER does not map"
            )
        anchors.append((owner, item))
    if sorted({c for c, _ in anchors}) != ["alloc", "core", "std"]:
        die(f"anchor drift: `crate_is_authentic_foundational` anchors {anchors} do not cover core/alloc/std")
    return anchors


def extract_to_string_self(convert: str) -> dict:
    """The `@trust-total-to-string::` stamp's admitted `Self` arms, and their anchors."""
    body = fn_body(convert, "to_string_self_ty_is_foundational", CONVERT_RS)
    if "_ => false" not in body:
        die("anchor drift: `to_string_self_ty_is_foundational` lost its `_ => false` fallback")
    kinds: list[str] = []
    for k in re.findall(r"rustc_middle::ty::TyKind::(\w+)", body):
        if k not in kinds:
            kinds.append(k)
    unknown = [k for k in kinds if k not in TO_STRING_SELF_ARMS]
    if unknown:
        die(
            f"anchor drift: `to_string_self_ty_is_foundational` admits {unknown}, "
            "which TO_STRING_SELF_ARMS does not describe"
        )
    if not kinds:
        die("anchor drift: `to_string_self_ty_is_foundational` parsed to zero arms")
    required = {
        "Ref": "to_string_str_ref_chain_depth(ty).is_some()",
        "Adt": "tcx.lang_items().string() == Some(adt.did())",
    }
    for kind, anchor in required.items():
        if kind in kinds and anchor not in body:
            die(f"anchor drift: `to_string_self_ty_is_foundational`'s `{kind}` arm lost `{anchor}`")
    if "Adt" in kinds and not ("args.is_empty()" in body and "is_real_alloc_crate(tcx, adt.did().krate)" in body):
        die("anchor drift: the `String` arm lost its residency or no-generic-arguments test")
    depth = re.search(r"const TO_STRING_STR_MAX_REF_DEPTH: usize = (\d+);", convert)
    if not depth:
        die("anchor drift: `TO_STRING_STR_MAX_REF_DEPTH` not found")
    chain = fn_body(convert, "to_string_str_ref_chain_depth", CONVERT_RS)
    for anchor in ("TO_STRING_STR_MAX_REF_DEPTH", "Mutability::Not", "TyKind::Str"):
        if anchor not in chain:
            die(f"anchor drift: `to_string_str_ref_chain_depth` lost `{anchor}`")
    # The stamp mints only behind the authenticated admission, and never on a
    # second path of its own: its body must BE that one fallible call.
    stamp = fn_body(convert, "tcx_marked_total_to_string_path", CONVERT_RS)
    if "authenticated_total_to_string_self_ty(tcx, def_id, generic_args)?;" not in stamp:
        die("anchor drift: `tcx_marked_total_to_string_path` no longer mints only behind "
            "`authenticated_total_to_string_self_ty(..)?`")
    admit = fn_body(convert, "authenticated_total_to_string_self_ty", CONVERT_RS)
    for anchor in (
        "is_real_alloc_crate(tcx, to_string_method.krate)",
        "to_string_self_ty_is_foundational(tcx, self_ty)",
    ):
        if anchor not in admit:
            die(f"anchor drift: `authenticated_total_to_string_self_ty` lost `{anchor}`")
    selfty = fn_body(convert, "to_string_instantiated_self_ty", CONVERT_RS)
    for anchor in ("is_real_alloc_crate(tcx, alloc_krate)", "TyKind::Param(_)"):
        if anchor not in selfty:
            die(f"anchor drift: `to_string_instantiated_self_ty` lost `{anchor}`")
    alloc = fn_body(convert, "is_real_alloc_crate", CONVERT_RS)
    if 'as_str() == "alloc"' not in alloc or "is_real_sysroot_crate(tcx, krate)" not in alloc:
        die("anchor drift: `is_real_alloc_crate` is no longer name AND residency")
    return {"kinds": kinds, "depth": int(depth.group(1))}


def extract_drop_glue(lower: str) -> dict[str, dict[str, list[str]]]:
    """Per allowlist fn: literals classified by matching form.

    Classes: `prefix` (path gate via starts_with), `exact` (matches!),
    `suffix` (ends_with), `substring` (contains), `parts` (const PARTS
    entry, matched by contains).  Any literal in the body that fits none
    of these is a hard failure — see the module docstring.
    """
    out: dict[str, dict[str, list[str]]] = {}
    for fn in DROP_GLUE_FNS:
        body = fn_body(lower, fn, LOWER_RS)
        classes: dict[str, list[str]] = {
            "prefix": [],
            "exact": [],
            "suffix": [],
            "substring": [],
            "parts": [],
        }
        claimed: list[tuple[int, int]] = []

        def claim(m_start: int, m_end: int) -> None:
            claimed.append((m_start, m_end))

        for kind, pat in (
            ("prefix", r'\.starts_with\("((?:[^"\\]|\\.)*)"\)'),
            ("suffix", r'\.ends_with\("((?:[^"\\]|\\.)*)"\)'),
            ("substring", r'\.contains\("((?:[^"\\]|\\.)*)"\)'),
        ):
            for m in re.finditer(pat, body):
                classes[kind].append(m.group(1))
                claim(m.start(), m.end())
        for s, e, lit in matches_bang_literals(body, fn):
            classes["exact"].append(lit)
            claim(s, e)
        if "const PARTS: &[&str] = &[" in body:
            if "PARTS.iter().any(|p| name.contains(p))" not in body:
                die(f"anchor drift: `{fn}` PARTS no longer consumed via contains")
            classes["parts"] = const_str_array(
                body, "const PARTS: &[&str] = &[", f"{LOWER_RS}::{fn}"
            )
            ps = body.index("const PARTS: &[&str] = &[")
            pe = body.index("];", ps) + 2
            claim(ps, pe)
        # Loudness: every string literal must be inside a claimed span.
        for m in re.finditer(r'"((?:[^"\\]|\\.)*)"', body):
            if not any(s <= m.start() and m.end() <= e for s, e in claimed):
                die(
                    f"anchor drift: unclassifiable string literal "
                    f'"{m.group(1)}" in `{fn}` — a matching form this '
                    f"generator does not understand was added"
                )
        if not any(classes[k] for k in ("exact", "suffix", "substring", "parts")):
            die(f"anchor drift: `{fn}` parsed to zero accepted-name literals")
        out[fn] = classes
    return out


# ---------------------------------------------------------------------------
# Markdown emission.
# ---------------------------------------------------------------------------


def crate_split(entries: list[str]) -> str:
    counts: dict[str, int] = {}
    for e in entries:
        counts[e.split("::")[0]] = counts.get(e.split("::")[0], 0) + 1
    return ", ".join(f"{k} {v}" for k, v in sorted(counts.items(), key=lambda kv: -kv[1]))


def emit(root: Path) -> str:
    lower = read(root, LOWER_RS)
    verify = read(root, TRUST_VERIFY_RS)

    exact_total = extract_exact_total(lower)
    intrinsics = extract_intrinsics(lower)
    iter_info = extract_iterator_arms(verify)
    iter_gate, iter_arms = iter_info[0], iter_info[1:]
    to_string_self = extract_to_string_self(read(root, CONVERT_RS))
    drop_glue = extract_drop_glue(lower)
    panic_free = extract_panic_free_intrinsics(read(root, PANIC_FREE_INTRINSIC_RS))

    o: list[str] = []
    w = o.append
    w(BEGIN_LINE)
    w("")
    w("## The counted std name lists (generated)")
    w("")
    w("Every name below is a TRUSTED FACT: a std/core/alloc surface the verifier")
    w("accepts on audit rather than proof. This section exists so that surface is")
    w("*counted* — a trusted fact that is counted is manageable; one that is")
    w("diffuse is not (design doc 2026-08-19, §5 step 2a). It is generated from")
    w("the shipping source by `tools/gen_tcb_std_lists.py`; the generator exits")
    w("nonzero when any source anchor moves, and `--check` fails when this text")
    w("differs from a fresh generation.")
    w("")

    w(
        f"### `EXACT_TOTAL` — {len(exact_total)} entries ({crate_split(exact_total)})"
    )
    w("")
    w(f"`{LOWER_RS}`, `const EXACT_TOTAL`. Exact normalized-path totality names:")
    w("a call to one of these is accepted as panic-free with an UNCONSTRAINED")
    w("result, body unread. In source order:")
    w("")
    w("```text")
    for e in exact_total:
        w(e)
    w("```")
    w("")

    w(f"### `total_std_iterator_ty` — {len(iter_arms)} accepted head types")
    w("")
    w(f"`{TRUST_VERIFY_RS}`, `fn total_std_iterator_ty`. A typed-receiver gate:")
    if iter_gate["kind"] == "crate-name":
        w("the receiver's ADT must carry a real non-local `DefId` whose crate is one")
        w(f"of {{{', '.join('`' + c + '`' for c in iter_gate['crates'])}}} (rendered paths are")
        w("never consulted), and anything unmatched falls to `_ => false`.")
    else:
        owners = "; ".join(
            f"`{crate}` = owner of `{item}`" for crate, item in iter_gate["anchors"]
        )
        w("the receiver's ADT must carry a real non-local `DefId`, and its crate must")
        w("pass `crate_is_authentic_foundational`: LANG-ITEM OWNERSHIP, compared by")
        w(f"`CrateNum` ({owners}), AND ARTIFACT RESIDENCY")
        w(f"(`{RESIDENCY_FN}`, which is exactly")
        w("`trust_mir_extract::is_real_sysroot_crate`). Rendered paths and the")
        w("`--crate-name` string are never consulted as evidence, and anything")
        w("unmatched falls to `_ => false`. `crate_is_authentic_core`")
        w("(`sized_trait`) and `crate_is_authentic_std` (`panic_impl`) carry the")
        w("same residency conjunct.")
        w("")
        w("Ownership says WHICH sysroot crate a crate is; residency says that it IS")
        w("one. rustc rejects a second owner of a lang item (E0152) only when both")
        w("owners are loaded, so in a `#![no_std]` graph that never loads `alloc` or")
        w("`std`, a dependency may own `owned_box`/`string` (`#![feature(lang_items)]`)")
        w("or `panic_impl` (any `#[panic_handler]`). Ownership alone graded such a")
        w("dependency foundational until 2026-09-28; the residency conjunct refuses")
        w("it, because `is_real_sysroot_crate` admits only a crate named")
        w("`core`/`alloc`/`std`, and only when the loader opened it from this")
        w("compiler's own target library directory or the command line declares a")
        w("sysroot build (`-Zforce-unstable-if-unmarked`). Pins:")
        w("`tests/ui/trust/total_std_iterator_lang_item_foundational_impostor_refuted.rs`,")
        w("`tests/ui/trust/total_std_iterator_panic_handler_foundational_impostor_refuted.rs`.")
        w("")
        w("Residency is fail-closed OVER-DECLINE in three honest shapes, each read by")
        w("every consumer as mask/refuse: the genuine `core`/`alloc`/`std` loaded from")
        w("outside the target library directory without that declaration (the user")
        w("crate under `cargo -Zbuild-std`, an `--extern core=` sysroot), and a LOCAL")
        w("crate that owns an anchor (a `#![no_std]` crate's own `#[panic_handler]`).")
        w("A non-sysroot `panic_impl` owner (a panic-handler dependency) is likewise")
        w("no longer graded `std`; `core`'s own credits are unaffected. The extractor")
        w("discloses the same over-decline for its path stamp at")
        w("`invocation_is_building_the_sysroot` (`crates/trust-mir-extract/src/convert.rs`).")
    w("")
    w("| Head type | Def-path module anchor | Admission rule |")
    w("|---|---|---|")
    for a in iter_arms:
        anchor = ", ".join(f"`{x}`" for x in a["anchors"]) or "—"
        if a["both_sides"]:
            rule = "recurses; BOTH inner iterators must be total"
        elif a["len_bounded"]:
            rule = (
                "recurses; the inner iterator must also yield at most `usize::MAX` items "
                "(`total_std_iterator_len_fits_usize`)"
            )
        elif a["recursive"]:
            rule = "recurses into the inner iterator type"
        elif a["int_only"]:
            rule = "integer element types only"
        elif a.get("pattern_gated"):
            rule = "only when its pattern type is one of core's (`str_pattern_ty_is_core`)"
        else:
            rule = "accepted at the anchored module"
        w(f"| `{a['head']}` | {anchor} | {rule} |")
    w("")

    w("### The four drop-glue allowlists")
    w("")
    w(f"`{LOWER_RS}`. Literal kinds: *prefix* = path gate (`starts_with`, keeps a")
    w("same-named user type from matching); *exact* = full-path match; *suffix* /")
    w("*substring* = accepted name fragment (`ends_with` / `contains`).")
    w("")
    for fn in DROP_GLUE_FNS:
        c = drop_glue[fn]
        accepted = len(c["exact"]) + len(c["suffix"]) + len(c["substring"]) + len(c["parts"])
        w(f"#### `{fn}` — {accepted} accepted name literals")
        w("")
        if c["prefix"]:
            w("- prefix gates: " + ", ".join(f"`{x}`" for x in c["prefix"]))
        for kind, label in (
            ("exact", "exact"),
            ("suffix", "suffix"),
            ("substring", "substring"),
            ("parts", "substring (PARTS)"),
        ):
            for x in c[kind]:
                w(f"- {label}: `{x}`")
        w("")

    ts_kinds = to_string_self["kinds"]
    w(f"### `to_string_self_ty_is_foundational` — {len(ts_kinds)} admitted Self arms")
    w("")
    w(f"`{CONVERT_RS}`. The `@trust-total-to-string::` stamp")
    w("(`tcx_marked_total_to_string_path`) marks a `ToString::to_string` call panic-free")
    w("when the callee is the compiler's own `alloc` item by artifact residency, the")
    w("selected impl is alloc's blanket `impl<T: Display + ?Sized> ToString for T`,")
    w("and the INSTANTIATED `Self` (read from `TyCtxt`, never from path text) matches")
    w("one of these arms, each audited against its `SpecToString` specialization in")
    w("`library/alloc/src/string.rs`. Anything unmatched falls to `_ => false`. In")
    w("source order:")
    w("")
    for k in ts_kinds:
        w(f"- `TyKind::{k}`: " + TO_STRING_SELF_ARMS[k].format(depth=to_string_self["depth"]))
    w("")

    w(f"### `is_total_rustc_intrinsic` — {len(intrinsics)} intrinsic names")
    w("")
    w(f"`{LOWER_RS}`, `fn is_total_rustc_intrinsic`. Body-less rustc intrinsics")
    w("(`@trust-rustc-intrinsic::…` spellings) accepted as panic-free; they have")
    w("no MIR to lower, ever, so a model is the only possible discharge. In")
    w("source order:")
    w("")
    w("```text")
    for n in intrinsics:
        w(n)
    w("```")
    w("")

    w(
        f"### `PANIC_FREE_RUSTC_INTRINSICS` — {len(panic_free)} intrinsic names "
        "(panic-freedom only)"
    )
    w("")
    w(f"`{PANIC_FREE_INTRINSIC_RS}`, `const PANIC_FREE_RUSTC_INTRINSICS`. `core`")
    w("intrinsics stamped `@trust-rustc-panic-free-intrinsic::…` by")
    w("`tcx_marked_panic_free_intrinsic_path` (real `core`, `#[rustc_nounwind]`, safe,")
    w("fallback body pinned panic-free when it has one) and lowered with NO panic row")
    w("and an UNCONSTRAINED result. Panic-freedom only: the facet and determinism")
    w("gates never read this stamp, and no value fact is exported. Columns: name,")
    w("width, operand shape, fallback-bodied. In source order:")
    w("")
    w("```text")
    for name, width, shape, fallback in panic_free:
        w(f"{name} f{width} {shape} {'fallback' if fallback == 'true' else 'body-less'}")
    w("```")
    w("")
    w(END_MARKER)
    return "\n".join(o) + "\n"


def counts_summary(section: str) -> str:
    return "; ".join(
        f"{name}: {count}"
        for name, count in re.findall(r"#{3,4} `?([\w_]+)`? — (\d+ \w+(?: \w+)*)", section)
    )


# ---------------------------------------------------------------------------
# Selftest — the FALSIFYING check, kept runnable forever.
#
# Each perturbation below models a real drift class and must turn the
# generator RED in a scratch copy; a selftest where any of them stays green
# means the loudness this file promises is gone, and the selftest itself
# exits nonzero.
# ---------------------------------------------------------------------------


def selftest(repo: Path) -> int:
    import shutil
    import subprocess
    import tempfile

    me = str(Path(__file__).resolve())

    def run(scratch: Path, *extra: str) -> int:
        return subprocess.run(
            [sys.executable, me, "--repo", str(scratch), *extra],
            stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL,
        ).returncode

    failures: list[str] = []
    labels: list[str] = []
    with tempfile.TemporaryDirectory(prefix="gen_tcb_selftest.") as td:
        scratch = Path(td)
        for rel in (LOWER_RS, TRUST_VERIFY_RS, CONVERT_RS, PANIC_FREE_INTRINSIC_RS, TCB_MD):
            dst = scratch / rel
            dst.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(repo / rel, dst)

        lower = scratch / LOWER_RS
        verify = scratch / TRUST_VERIFY_RS
        convert = scratch / CONVERT_RS
        panic_free = scratch / PANIC_FREE_INTRINSIC_RS

        def perturbed(path: Path, old: str, new: str, label: str, *extra: str) -> None:
            labels.append(label)
            original = path.read_text(encoding="utf-8")
            if old not in original:
                failures.append(f"{label}: perturbation anchor `{old}` not found")
                return
            path.write_text(original.replace(old, new), encoding="utf-8")
            try:
                rc = run(scratch, *extra)
                if rc == 0:
                    failures.append(f"{label}: generator stayed GREEN (rc=0)")
                else:
                    sys.stderr.write(f"selftest ok: {label} -> rc={rc}\n")
            finally:
                path.write_text(original, encoding="utf-8")

        if run(scratch, "--check") != 0:
            failures.append("baseline --check on an unperturbed copy is not green")
        perturbed(
            lower,
            "const EXACT_TOTAL: &[&str] = &[",
            "const EXACT_TOTAL_RENAMED: &[&str] = &[",
            "renamed EXACT_TOTAL const anchor",
        )
        perturbed(
            verify,
            "_ => false",
            "_ => true",
            "iterator gate fail-closed fallback flipped open",
        )
        perturbed(
            lower,
            "fn is_never_drops_contents_wrapper(name: &str) -> bool {",
            'fn is_never_drops_contents_wrapper(name: &str) -> bool {\n'
            '    if name == "evil::SneakyWidening" {\n'
            "        return true;\n"
            "    }\n",
            "unrecognized matching form widens a drop-glue allowlist",
        )
        perturbed(
            lower,
            '"core::mem::size_of",',
            '"core::mem::size_of",\n        "core::mem::totally_new_entry",',
            "source list grew but the doc was not regenerated",
            "--check",
        )
        perturbed(
            lower,
            '"core::mem::size_of",',
            '"core::mem::size_of",\n        "core::mem::size_of",',
            "EXACT_TOTAL lists one name twice (count would over-state the surface)",
        )
        perturbed(
            verify,
            "    (owns(lang_items.sized_trait())\n",
            "    (true || owns(lang_items.sized_trait())\n",
            "iterator crate gate's ownership test widened to accept every crate",
        )
        foundational_body = (
            "    (owns(lang_items.sized_trait())\n"
            "        || owns(lang_items.owned_box())\n"
            "        || owns(lang_items.string())\n"
            "        || owns(lang_items.panic_impl()))\n"
            "        && crate_is_compiler_resident_sysroot(tcx, krate)\n"
        )
        perturbed(
            verify,
            foundational_body,
            foundational_body.replace("\n        && crate_is_compiler_resident_sysroot(tcx, krate)", ""),
            "iterator crate gate lost its residency conjunct (ownership alone again)",
        )
        perturbed(
            verify,
            foundational_body,
            foundational_body.replace("    (owns(lang_items.sized_trait())", "    owns(lang_items.sized_trait())")
            .replace("panic_impl()))\n", "panic_impl())\n"),
            "residency conjunct binds only the last ownership disjunct (precedence)",
        )
        perturbed(
            verify,
            "tcx.lang_items().sized_trait().is_some_and(|d| d.krate == krate)\n"
            "        && crate_is_compiler_resident_sysroot(tcx, krate)",
            "tcx.lang_items().sized_trait().is_some_and(|d| d.krate == krate)",
            "authentic-core lost its residency conjunct",
        )
        perturbed(
            verify,
            "-> bool {\n    trust_mir_extract::is_real_sysroot_crate(tcx, krate)\n}",
            "-> bool {\n    true || trust_mir_extract::is_real_sysroot_crate(tcx, krate)\n}",
            "residency helper widened to accept every crate",
        )
        perturbed(
            verify,
            "tcx.lang_items().panic_impl().is_some_and(|d| d.krate == krate)",
            "tcx.lang_items().panic_impl().is_some_and(|d| d.krate == krate)\n"
            '        || tcx.crate_name(krate).as_str() == "std"',
            "authentic-std regained a spoofable crate-name disjunct",
        )
        perturbed(
            convert,
            "rustc_middle::ty::TyKind::Ref(..) => to_string_str_ref_chain_depth(ty).is_some(),",
            "rustc_middle::ty::TyKind::Ref(..) => true,",
            "to_string stamp reference peel widened to any reference",
        )
        perturbed(
            convert,
            "rustc_middle::ty::TyKind::Str => true,",
            "rustc_middle::ty::TyKind::Str => true,\n"
            "        rustc_middle::ty::TyKind::Float(_) => true,",
            "to_string stamp admits a Self arm the generator does not describe",
        )
        perturbed(
            convert,
            "const TO_STRING_STR_MAX_REF_DEPTH: usize = 12;",
            "const TO_STRING_STR_MAX_REF_DEPTH: usize = 13;",
            "to_string str-chain depth grew but the doc was not regenerated",
            "--check",
        )
        perturbed(
            panic_free,
            '    entry("powif64", 64, PowI, false),\n',
            '    entry("powif64", 64, PowI, false),\n    entry("fmuladdf64", 64, Binary, false),\n',
            "panic-free intrinsic list grew but the doc was not regenerated",
            "--check",
        )
        perturbed(
            panic_free,
            '    entry("powif64", 64, PowI, false),\n',
            '    entry("powif64", 64, PowI, false),\n    ENTRY_MACRO!("fmuladdf64"),\n',
            "panic-free intrinsic list gained an entry the parser cannot read",
        )
        if run(scratch, "--check") != 0:
            failures.append("scratch copy did not restore to green after perturbations")

    for f in failures:
        sys.stderr.write(f"gen_tcb_std_lists: SELFTEST FAIL: {f}\n")
    if failures:
        return 1
    sys.stderr.write(f"gen_tcb_std_lists: selftest passed ({len(labels)} perturbations, all red)\n")
    return 0


# ---------------------------------------------------------------------------
# Modes.
# ---------------------------------------------------------------------------


def find_marked_span(doc: str) -> tuple[int, int]:
    b = doc.find(BEGIN_MARKER)
    e = doc.find(END_MARKER)
    if b < 0 or e < 0:
        die(
            f"{TCB_MD} is missing the generated-section markers "
            f"({BEGIN_MARKER} … {END_MARKER}); add them once by hand",
            2,
        )
    if doc.find(BEGIN_MARKER, b + 1) >= 0 or doc.find(END_MARKER, e + 1) >= 0:
        die(f"{TCB_MD} contains duplicate generated-section markers", 2)
    if e < b:
        die(f"{TCB_MD} markers are out of order", 2)
    return b, e + len(END_MARKER)


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n", 1)[0])
    ap.add_argument("--repo", type=Path, default=Path(__file__).resolve().parent.parent,
                    help="repo root (default: this script's parent's parent)")
    mode = ap.add_mutually_exclusive_group()
    mode.add_argument("--write", action="store_true",
                      help=f"splice the section between the markers in {TCB_MD}")
    mode.add_argument("--check", action="store_true",
                      help=f"exit 1 if the section in {TCB_MD} is stale")
    mode.add_argument("--selftest", action="store_true",
                      help="falsifying check: perturb anchors in a scratch copy "
                           "and require the generator to go red each time")
    args = ap.parse_args()

    if args.selftest:
        return selftest(args.repo)

    section = emit(args.repo)
    sys.stderr.write(f"gen_tcb_std_lists: {counts_summary(section)}\n")

    if not (args.write or args.check):
        sys.stdout.write(section)
        return 0

    tcb = args.repo / TCB_MD
    if not tcb.is_file():
        die(f"{tcb} not found", 2)
    doc = tcb.read_text(encoding="utf-8")
    b, e = find_marked_span(doc)

    if args.check:
        if doc[b:e] != section.rstrip("\n"):
            die(f"{TCB_MD} generated section is STALE; run: "
                f"python3 tools/gen_tcb_std_lists.py --write")
        sys.stderr.write("gen_tcb_std_lists: docs/TCB.md section is current\n")
        return 0

    tcb.write_text(doc[:b] + section.rstrip("\n") + doc[e:], encoding="utf-8")
    sys.stderr.write(f"gen_tcb_std_lists: wrote generated section into {tcb}\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
