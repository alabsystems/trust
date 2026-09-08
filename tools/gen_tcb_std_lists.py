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
    return const_str_array(lower, "const EXACT_TOTAL: &[&str] = &[", LOWER_RS)


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
    if not crate_gate:
        die("anchor drift: `total_std_iterator_ty` crate-identity gate not found")
    crates = re.findall(r'"(\w+)"', crate_gate.group(1))
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
        int_only = "ty::Int(_)" in arm_text and "ty::Uint(_)" in arm_text
        both_sides = bool(re.search(r"&&\s*\n?\s*total_std_iterator_ty\(", arm_text)) or (
            arm_text.count("total_std_iterator_ty(") >= 2
        )
        for h in heads:
            arms.append(
                {
                    "head": h,
                    "anchors": anchors,
                    "recursive": recursive,
                    "int_only": int_only,
                    "both_sides": both_sides and recursive,
                }
            )
    return [{"crates": crates}] + arms


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
    iter_crates, iter_arms = iter_info[0]["crates"], iter_info[1:]
    drop_glue = extract_drop_glue(lower)

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
    w("the receiver's ADT must carry a real non-local `DefId` whose crate is one")
    w(f"of {{{', '.join('`' + c + '`' for c in iter_crates)}}} (rendered paths are")
    w("never consulted), and anything unmatched falls to `_ => false`.")
    w("")
    w("| Head type | Def-path module anchor | Admission rule |")
    w("|---|---|---|")
    for a in iter_arms:
        anchor = ", ".join(f"`{x}`" for x in a["anchors"]) or "—"
        if a["both_sides"]:
            rule = "recurses; BOTH inner iterators must be total"
        elif a["recursive"]:
            rule = "recurses into the inner iterator type"
        elif a["int_only"]:
            rule = "integer element types only"
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
    with tempfile.TemporaryDirectory(prefix="gen_tcb_selftest.") as td:
        scratch = Path(td)
        for rel in (LOWER_RS, TRUST_VERIFY_RS, TCB_MD):
            dst = scratch / rel
            dst.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(repo / rel, dst)

        lower = scratch / LOWER_RS
        verify = scratch / TRUST_VERIFY_RS

        def perturbed(path: Path, old: str, new: str, label: str, *extra: str) -> None:
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
        if run(scratch, "--check") != 0:
            failures.append("scratch copy did not restore to green after perturbations")

    for f in failures:
        sys.stderr.write(f"gen_tcb_std_lists: SELFTEST FAIL: {f}\n")
    if failures:
        return 1
    sys.stderr.write("gen_tcb_std_lists: selftest passed (4 perturbations, all red)\n")
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
