#!/usr/bin/env python3
"""check_help_surfaces — every CLI help surface in this repo has been READ against
its handler, and any surface that appears or changes afterwards is refused until
it is read again.

WHY THIS EXISTS. Between 2026-08-31 and 2026-09-10, 138 help/usage claims across
the alab repos were found to contradict the code that implements them — rosters
hand-typed beside derived sets, exit codes that no longer happen, remedies naming
verbs that do not do the thing. Every one was found by reading a help surface
against its handler. That read is a dated fact about ONE version of the text, and
nothing made it durable: a new binary's usage text, or an edit to an existing one,
was unread until somebody thought to sweep again. This gate turns "all help
surfaces are read-verified" from a snapshot into an invariant of every green tip.

WHAT A HELP SURFACE IS. A source file that carries user-facing usage/help text:
discovered mechanically (a string literal with a line that starts a usage block —
`Usage:`, `OPTIONS:`, `COMMANDS:`, … — or code that exists only to print help:
`fn usage`/`print_usage`/`help_text`, a `USAGE`/`HELP`-named const, a clap
`#[command(`/`#[arg(`/`about =`/`long_about`). `#[arg(` earns its place: clap
derives a flag's `--help` line from the `///` doc on its field, so a file full
of flags and no `#[command(` is user-facing help with no marker — measured
2026-09-13, when it hid 27 of clean's `cli.rs`/`cmd_*.rs` files, one of which
had been edited by hand three days earlier with nothing watching it. The
manifest may add surfaces discovery
misses (`extra_surfaces`) and must classify the ones it over-finds (`not_help`,
each with a reason), so every discovered file is accounted for one way or the other.

WHAT IS HASHED. The file's PROSE: every string literal plus every doc comment
(`///`, `//!`, `/** */`), in source order, with plain comments, char literals and
code dropped. A code-only edit leaves a verified row alone; any change to text a
user can read invalidates it.

REFUSALS (each names its remedy):
  R1 UNROSTERED  a discovered surface is in neither `surfaces` nor `not_help`
  R2 CHANGED     a surface's prose differs from the hash recorded when it was read
  R3 GONE        a rostered path no longer exists
  R4 STALE       a row's `verified` date is missing, malformed, or older than
                 `max_age_days`
  R5 DEAD_ALLOW  a `not_help` entry names a file that is gone or is no longer
                 discovered (prune it)
  R6 DUPLICATE   a path appears in both lists, or twice in one
  R7 PROGRAM     a binary entry point (`src/main.rs`, `src/bin/*.rs`,
                 `src/bin/*/main.rs`, a `[[bin]] path`) under `program_roots` is
                 in neither list — every PROGRAM is accounted for, even one whose
                 help lives elsewhere (say where, in `not_help`) or that has none
  R8 EMBEDDED    a file a rostered surface pulls in with `include_str!` /
                 `include_bytes!` is in neither list. Such a file IS shipped help
                 text — it reaches the binary and the reader — but discovery walks
                 `*.rs`, and the only string the lexer sees at the macro is the
                 PATH, so its content is invisible without this rule
  R10 DESCRIBES  a row's `describes` entry names a path that is not in the tree
                 (a file or a directory both count), or names the row's own crate
                 (which every row gets for free), or its `drift_swept` names a
                 commit this repository does not have. `describes` is what `--drift` uses to reach a surface whose
                 subject is ANOTHER crate; a rotted edge does not fail loudly, it
                 just quietly stops naming the surface — the exact failure the
                 field exists to prevent

The remedy for R1/R2 is a READ, not a hash bump: `--dump` prints skeleton rows for
the offending files with today's date and the current hash; accepting a row is the
assertion that its help text was read against its handler on that date. R9 of the
gate registry: this scanner lexes (`prose_of_rust`), it never counts raw lines.

USAGE
  python3 scripts/check_help_surfaces.py            # the gate (exit 1 on refusal)
  python3 scripts/check_help_surfaces.py --dump     # skeleton rows for R1/R2 files
  python3 scripts/check_help_surfaces.py --selftest # mutation arms on a synthetic tree
"""
from __future__ import annotations

import argparse
import datetime as dt
import hashlib
import json
import re
import subprocess
import sys
import tempfile
from pathlib import Path

MANIFEST = "data/help_surfaces.json"

USAGE_STRING = re.compile(
    r"(?im)(?:^|\n)[ \t]*(usage|options|subcommands|commands|arguments|verbs|flags|exit codes?):"
)
HELP_CODE = re.compile(
    r"\bfn (usage|print_usage|help_text|usage_text|print_help|cmd_help|verb_help|usage_error)\b"
    r"|\b(?:const|static) (?:[A-Z0-9]+_)*(?:USAGE|HELP)(?:_[A-Z0-9]+)*\b"
    r"|#\[command\(|#\[clap\(|#\[arg\(|\babout\s*=\s*\"|\blong_about\b"
)
# A cheap superset of the two discovery markers over RAW text, so the 5,000-file
# walk lexes only files that can match. (An anchored case-insensitive regex here
# cost 18 s over clean and `HELP_CODE` over raw text 9 s; substring tests cost
# under a second, and the usage keywords are found by substring and checked in
# place.)
USAGE_NEEDLES = (
    "usage:", "options:", "subcommands:", "commands:", "arguments:", "verbs:", "flags:",
    "exit code:", "exit codes:",
)


CODE_NEEDLES = (
    "fn usage", "fn print_usage", "fn help_text", "fn usage_text", "fn print_help",
    "fn cmd_help", "fn verb_help", "fn usage_error", "USAGE", "HELP", "#[command(",
    "#[clap(", "#[arg(", "about =", "about=", "long_about",
)


def raw_hint(src: str) -> bool:
    """True when the lexed markers COULD match: a code needle anywhere in the raw
    text (a superset of `HELP_CODE` over the code half), or a usage keyword that sits
    where a string literal's line can start — after a quote, a real newline, an
    escaped `\\n`, or at the top of the file."""
    if any(n in src for n in CODE_NEEDLES):
        return True
    low = src.lower()
    for needle in USAGE_NEEDLES:
        pos = low.find(needle)
        while pos >= 0:
            k = pos
            while k > 0 and src[k - 1] in " \t":
                k -= 1
            if k == 0 or src[k - 1] in '"\n' or src[k - 2 : k] == "\\n":
                return True
            pos = low.find(needle, pos + 1)
    return False


EXCLUDED_PATH = re.compile(r"/(examples|benches|tests|target)/|(_tests?|/tests)\.rs$|/kani_proofs\.rs$")


# ----------------------------------------------------------------- extraction
# One tokenizer for both halves of a Rust file. `re` does the scanning at C speed;
# Python touches one token at a time, which is what keeps a 6,000-file walk inside
# a hook budget (the char-by-char loop this replaced took 119 s over clean).
TOKEN = re.compile(
    r"(?P<line>//[^\n]*)"
    r"|(?P<block>/\*(?:[^*]|\*(?!/))*\*/)"
    r"|(?P<raw>(?<![A-Za-z0-9_])(?:b|c)?r(?P<hashes>#*)\")"
    r"|(?P<str>(?<![A-Za-z0-9_])(?:b|c)?\"(?:[^\"\\]|\\[\s\S])*\")"
    r"|(?P<char>'(?:[^'\\\n]|\\(?:[^\n]|u\{[0-9a-fA-F]+\}))')"
    r"|(?P<life>'[A-Za-z_][A-Za-z0-9_]*)"
)
CONTINUATION = re.compile(r"\\\n[ \t\r\n]*")


def _block_end(src: str, start: int) -> int:
    """End (exclusive) of the block comment opening at `start`, nesting honoured."""
    depth, j, n = 1, start + 2, len(src)
    while j < n and depth:
        if src.startswith("/*", j):
            depth += 1
            j += 2
        elif src.startswith("*/", j):
            depth -= 1
            j += 2
        else:
            j += 1
    return j


def _tokens(src: str):
    """Yield (kind, start, end, body) over `src`: kind in line/block/raw/str/char/life."""
    pos, n = 0, len(src)
    while pos < n:
        m = TOKEN.search(src, pos)
        if not m:
            return
        kind = m.lastgroup
        if kind == "block":
            end = _block_end(src, m.start()) if "/*" in src[m.start() + 2 : m.end() - 2] else m.end()
            yield kind, m.start(), end, src[m.start() : end]
            pos = end
        elif kind == "raw":
            hashes = m.group("hashes")
            body_start = m.end()
            close = src.find('"' + hashes, body_start)
            close = n if close < 0 else close
            end = min(n, close + 1 + len(hashes))
            yield kind, m.start(), end, src[body_start:close]
            pos = end
        elif kind == "str":
            body = m.group("str")
            body = body[body.index('"') + 1 : -1]
            yield kind, m.start(), m.end(), body
            pos = m.end()
        else:
            yield kind, m.start(), m.end(), m.group(0)
            pos = m.end()


def split_rust(src: str) -> tuple[list[str], list[str], str]:
    """One pass: (string literals, doc comments, the CODE half with every comment
    and literal body blanked to spaces, line geometry preserved). A `\\`-newline
    continuation inside a literal is removed with the indentation that follows
    it; every other escape is kept verbatim."""
    strings: list[str] = []
    docs: list[str] = []
    code: list[str] = []
    pos = 0
    for kind, s, e, body in _tokens(src):
        code.append(src[pos:s])
        if kind == "line":
            if body.startswith("///") or body.startswith("//!"):
                docs.append(body[3:].strip())
            code.append(re.sub(r"[^\n]", " ", src[s:e]))
        elif kind == "block":
            if body.startswith("/**") or body.startswith("/*!"):
                docs.append(body[3:-2].strip())
            code.append(re.sub(r"[^\n]", " ", src[s:e]))
        elif kind in ("raw", "str"):
            strings.append(body if kind == "raw" else CONTINUATION.sub("", body))
            q = src.index('"', s) + 1
            close = q + len(body) if kind == "raw" else e - 1
            code.append(src[s:q] + re.sub(r"[^\n]", " ", src[q:close]) + src[close:e])
        else:
            code.append(src[s:e])
        pos = e
    code.append(src[pos:])
    return strings, docs, "".join(code)


def prose_of_rust(src: str) -> tuple[list[str], list[str]]:
    """(string literals, doc comments) in source order; everything else dropped."""
    strings, docs, _ = split_rust(src)
    return strings, docs


def strip_comments_keep_strings(src: str) -> str:
    """Comments blanked, string literals INTACT. `strip_noncode` blanks literal
    bodies too, which would erase the very path an `include_str!` names."""
    out: list[str] = []
    pos = 0
    for kind, s, e, _body in _tokens(src):
        out.append(src[pos:s])
        out.append(re.sub(r"[^\n]", " ", src[s:e]) if kind in ("line", "block") else src[s:e])
        pos = e
    out.append(src[pos:])
    return "".join(out)


def strip_noncode(src: str) -> str:
    """The CODE half of a Rust file (see `split_rust`). `HELP_CODE` runs over this,
    so a doc comment that merely mentions `fn usage(` cannot discover a file —
    only a definition can."""
    return split_rust(src)[2]


def prose_digest(path: Path) -> str:
    text = path.read_text(encoding="utf-8", errors="replace")
    if path.suffix == ".rs":
        strings, docs = prose_of_rust(text)
        body = "\n\x00".join(strings) + "\n\x01" + "\n\x00".join(docs)
    else:
        body = text
    return hashlib.sha256(body.encode("utf-8")).hexdigest()


def discovery_reasons(path: Path) -> list[str]:
    src = path.read_text(encoding="utf-8", errors="replace")
    strings, _docs, code = split_rust(src)
    reasons = []
    if USAGE_STRING.search("\n".join(strings)):
        reasons.append("usage-string")
    m = HELP_CODE.search(code)
    if m:
        reasons.append("help-code:" + m.group(0).strip())
    return reasons


def discover(root: Path, scan_roots: list[str]) -> dict[str, list[str]]:
    found: dict[str, list[str]] = {}
    for sr in scan_roots:
        p = root / sr
        if not p.exists():
            continue
        files = [p] if p.is_file() else sorted(p.rglob("*.rs"))
        for f in files:
            rel = f.relative_to(root).as_posix()
            if EXCLUDED_PATH.search("/" + rel):
                continue
            src = f.read_text(encoding="utf-8", errors="replace")
            if not raw_hint(src):
                continue
            reasons = discovery_reasons(f)
            if reasons:
                found[rel] = reasons
    return found


INCLUDE_RE = re.compile(r'include_(?:str|bytes)!\s*\(\s*"([^"]+)"\s*\)')


def embedded_files(root: Path, surfaces: list[str]) -> dict[str, str]:
    """Files a rostered surface compiles in, as {path: the surface that includes it}.

    `include_str!("../assets/x.md")` puts a whole file in the binary, and in this
    repo that is how shipped documentation travels. The lexer sees only the PATH
    string at the macro, so the CONTENT never reaches `prose_digest` of the
    including file: editing the asset moves no hash. Measured 2026-09-13 on
    aterm's four primer skill assets — 1,281 lines of agent-facing CLI
    documentation, `include_str!`-ed into a rostered surface, invisible to every
    gate. Resolved relative to the including file, as the macro resolves it.

    SCOPE, measured rather than assumed: only ROSTERED surfaces are scanned. An
    asset embedded by a file that is not itself a help surface is out of scope,
    because widening it drowns the signal — trust's tree carries thousands of
    upstream rustdoc `.md` includes (`intrinsic_is_convergent.md`, `docs/add.md`
    …) that are library documentation, not CLI help. Checked across all three
    repos on 2026-09-13: every non-`.rs`, non-vendored, non-test embed outside a
    rostered surface is data (`policy.toml`, `trusted_keys.toml`, a font, a
    trail pack) or third-party (vendored winit's changelog), so the narrower
    scan loses nothing today. Re-measure before assuming it still does.
    """
    out: dict[str, str] = {}
    for rel in surfaces:
        path = root / rel
        if path.suffix != ".rs" or not path.is_file():
            continue
        code = strip_comments_keep_strings(path.read_text(encoding="utf-8", errors="replace"))
        for m in INCLUDE_RE.finditer(code):
            target = (path.parent / m.group(1)).resolve()
            try:
                inc = target.relative_to(root.resolve()).as_posix()
            except ValueError:
                continue
            # A `.rs` target needs no rule of its own: the `*.rs` walk already
            # reaches it, and whether it carries help is R1's question. Including
            # it here would be a second, wrong answer to a question another rule
            # owns — measured 2026-09-13, when nine of R8's first sixteen hits
            # were `.rs` files a TEST include_str!s to scan its own source. Test
            # and fixture trees are excluded for the same reason they are
            # everywhere else: a golden is derived text, not a claim.
            if target.suffix == ".rs" or EXCLUDED_PATH.search("/" + inc):
                continue
            if target.is_file():
                out.setdefault(inc, rel)
    return out


def program_entry_points(root: Path, program_roots: list[str]) -> list[str]:
    """Every binary entry point under `program_roots`: the conventional
    `src/main.rs`, `src/bin/*.rs`, `src/bin/*/main.rs` of each Cargo package, plus
    any explicit `[[bin]] path = "…"`. Test, example, bench and target trees are
    skipped as everywhere else."""
    out: set[str] = set()
    bin_path = re.compile(r'\[\[bin\]\][^\[]*?path\s*=\s*"([^"]+)"', re.S)
    for pr in program_roots:
        base = root / pr
        if not base.is_dir():
            continue
        for toml in sorted(base.rglob("Cargo.toml")):
            rel_dir = toml.parent.relative_to(root).as_posix()
            if EXCLUDED_PATH.search("/" + rel_dir + "/") or "/vendor/" in "/" + rel_dir + "/":
                continue
            d = toml.parent
            candidates = [d / "src/main.rs"]
            candidates += sorted((d / "src/bin").glob("*.rs"))
            candidates += sorted((d / "src/bin").glob("*/main.rs"))
            for m in bin_path.finditer(toml.read_text(encoding="utf-8", errors="replace")):
                candidates.append(d / m.group(1))
            for c in candidates:
                if c.is_file():
                    rel = c.relative_to(root).as_posix()
                    if not EXCLUDED_PATH.search("/" + rel):
                        out.add(rel)
    return sorted(out)


# ----------------------------------------------------------------------- gate
def check(root: Path, manifest: dict, today: dt.date) -> tuple[list[str], list[dict]]:
    """(refusal lines, skeleton rows for --dump)."""
    refusals: list[str] = []
    skeleton: list[dict] = []
    max_age = int(manifest.get("max_age_days", 180))
    surfaces = manifest.get("surfaces", [])
    not_help = manifest.get("not_help", [])
    rostered = {r["path"]: r for r in surfaces}
    allowed = {r["path"]: r for r in not_help}

    seen: dict[str, int] = {}
    for r in surfaces + not_help:
        seen[r["path"]] = seen.get(r["path"], 0) + 1
    for p, k in sorted(seen.items()):
        if k > 1:
            refusals.append(f"R6 DUPLICATE  {p} appears {k} times across surfaces/not_help — keep one row")

    discovered = discover(root, manifest.get("scan_roots", []))
    for extra in manifest.get("extra_surfaces", []):
        discovered.setdefault(extra, ["explicit"])

    for rel in sorted(discovered):
        if rel in rostered or rel in allowed:
            continue
        refusals.append(
            f"R1 UNROSTERED {rel} carries help text ({', '.join(discovered[rel])}) and no row says it was read — "
            f"read it against its handler, then add the `--dump` row"
        )
        skeleton.append(
            {
                "path": rel,
                "prose_sha256": prose_digest(root / rel),
                "verified": today.isoformat(),
                "method": "TODO: who read it against what",
            }
        )

    for rel, row in sorted(rostered.items()):
        p = root / rel
        if not p.is_file():
            refusals.append(f"R3 GONE       {rel} is rostered but not on disk — drop the row or fix the path")
            continue
        current = prose_digest(p)
        if row.get("prose_sha256") != current:
            refusals.append(
                f"R2 CHANGED    {rel}: help/doc text changed since it was read on {row.get('verified', '?')} — "
                f"re-read it against its handler, then replace the row with the `--dump` one"
            )
            skeleton.append(
                {
                    "path": rel,
                    "prose_sha256": current,
                    "verified": today.isoformat(),
                    "method": row.get("method", "TODO"),
                }
            )
        try:
            verified = dt.date.fromisoformat(str(row.get("verified")))
        except (TypeError, ValueError):
            refusals.append(f"R4 STALE      {rel}: `verified` is missing or not YYYY-MM-DD")
            continue
        age = (today - verified).days
        if age > max_age:
            refusals.append(
                f"R4 STALE      {rel}: read {age} days ago (limit {max_age}) — re-read it and re-date the row"
            )
        swept = row.get("drift_swept")
        if swept is not None and (
            not isinstance(swept, str)
            or not swept
            or subprocess.run(
                ["git", "-C", str(root), "rev-parse", "--verify", f"{swept}^{{commit}}"],
                capture_output=True,
            ).returncode != 0
        ):
            refusals.append(
                f"R10 DESCRIBES {rel}: `drift_swept` is {swept!r}, which this repository has no "
                f"commit for — a sweep bound that resolves to nothing is silently ignored by "
                f"`--drift`, so the surface would look swept and never be named; fix it or drop it"
            )
        own = own_crate(root, rel)
        for subj in row.get("describes") or []:
            if not (root / subj).exists():
                refusals.append(
                    f"R10 DESCRIBES {rel}: `describes` names {subj}, which is not a path in the tree "
                    f"— a cross-crate edge that resolves to nothing stops naming this surface in "
                    f"`--drift` without ever saying so; fix the path or drop the entry"
                )
            elif subj == own:
                refusals.append(
                    f"R10 DESCRIBES {rel}: `describes` names {subj}, which is its OWN crate — every row "
                    f"gets that subject for free, so the entry adds nothing; drop it"
                )

    programs = set(program_entry_points(root, manifest.get("program_roots", [])))
    embedded = embedded_files(root, [r["path"] for r in surfaces])
    for rel in sorted(allowed):
        if not (root / rel).is_file():
            refusals.append(f"R5 DEAD_ALLOW {rel} is in not_help but not on disk — prune it")
        elif rel not in discovered and rel not in programs and rel not in embedded:
            refusals.append(f"R5 DEAD_ALLOW {rel} is in not_help but discovery no longer finds it — prune it")

    for rel in sorted(embedded):
        if rel in rostered or rel in allowed:
            continue
        refusals.append(
            f"R8 EMBEDDED   {rel} is compiled into {embedded[rel]} by include_str!/include_bytes! and is in "
            f"neither list — it is shipped text a reader sees; read it against the code it describes and add "
            f"the `--dump` row, or record in not_help why it is not help"
        )
        skeleton.append(
            {
                "path": rel,
                "prose_sha256": prose_digest(root / rel),
                "verified": today.isoformat(),
                "method": f"TODO: who read it against what (embedded in {embedded[rel]})",
            }
        )

    for rel in sorted(programs):
        if rel in rostered or rel in allowed:
            continue
        refusals.append(
            f"R7 PROGRAM    {rel} is a binary entry point in neither list — read its help against its "
            f"parser and add the `--dump` row, or record in not_help where its help lives (or that it takes no arguments)"
        )
        skeleton.append(
            {
                "path": rel,
                "prose_sha256": prose_digest(root / rel),
                "verified": today.isoformat(),
                "method": "TODO: who read it against what (or move to not_help with where its help lives)",
            }
        )

    return refusals, skeleton


def own_crate(root: Path, rel: str) -> str:
    """The subject every surface has for free: the package it lives in — the
    nearest ancestor holding a `Cargo.toml`, so this works for `crates/<x>`,
    a repo-root package like `targo-trust`, and a tool under `src/tools` alike.
    Falls back to the file itself when no manifest is above it (a script)."""
    here = (root / rel).parent
    while True:
        if (here / "Cargo.toml").is_file():
            try:
                return here.relative_to(root).as_posix()
            except ValueError:
                break
        if here == root or here.parent == here:
            break
        here = here.parent
    return rel


def row_commit(root: Path, rel: str) -> str | None:
    """The commit that last touched `rel`'s row in the manifest — when the read
    was RECORDED, which is the bound the drift question actually wants.

    Of the commits `git blame` gives the row's object (its `"path"` line back to
    the opening brace and forward to the closing one), the newest by committer
    time. `None` when no line of the row is committed yet.
    """
    text = (root / MANIFEST).read_text(encoding="utf-8")
    lines = text.splitlines()
    needle = f'"path": "{rel}",'
    try:
        at = next(i for i, l in enumerate(lines) if l.strip() == needle)
    except StopIteration:
        return None
    first = at
    while first > 0 and lines[first].strip() != "{":
        first -= 1
    last = at
    while last < len(lines) - 1 and not lines[last].strip().startswith("}"):
        last += 1
    out = subprocess.run(
        ["git", "-C", str(root), "blame", "--porcelain", "-L",
         f"{first + 1},{last + 1}", "--", MANIFEST],
        capture_output=True, text=True,
    ).stdout
    current, newest = None, None
    for line in out.splitlines():
        if line.startswith("\t"):
            continue
        head = line.split(" ", 1)[0]
        if len(head) in (40, 64) and all(c in "0123456789abcdef" for c in head) and " " in line:
            current = head
        elif line.startswith("committer-time ") and current and set(current) != {"0"}:
            try:
                when = int(line[len("committer-time "):].strip())
            except ValueError:
                continue
            if newest is None or when > newest[0]:
                newest = (when, current)
    return newest[1] if newest else None


def read_anchor(root: Path, rel: str, recorded: str) -> tuple[str | None, bool]:
    """The commit a row's read is anchored to.

    FIRST the commit that last touched the row in the manifest ([`row_commit`]):
    a row is a dated assertion, and the commit that recorded it is when the read
    happened. Failing that, the newest commit whose version of `rel` hashes to
    the row's `prose_sha256` — the text that was read, though possibly committed
    long before the reading.

    Why not the row's DATE, which is what this reported against until
    2026-09-13. A row carries a day, not a time, so a date bound either DROPS
    same-day drift (`--since=YYYY-MM-DD` as a bare date excludes commits made on
    that day — measured here: `--since=2026-09-13 -- cmd_fold.rs` found 0 while
    `--since=2026-09-13T00:00:00` found the commit made that evening) or, spelled
    with the midnight, names the very commit that MINTED the row as motion under
    it. That put 89 of 93 surfaces on the worklist, which is not a worklist.

    `(None, False)` when neither anchor resolves, and the caller falls back to
    the date.
    """
    recorded_at = row_commit(root, rel)
    if recorded_at:
        return recorded_at, True
    log = subprocess.run(
        ["git", "-C", str(root), "log", "--format=%H", "--", rel],
        capture_output=True, text=True,
    ).stdout.split()
    for sha in log:
        blob = subprocess.run(
            ["git", "-C", str(root), "show", f"{sha}:{rel}"],
            capture_output=True, text=True,
        )
        if blob.returncode != 0:
            continue
        body = blob.stdout
        if rel.endswith(".rs"):
            strings, docs = prose_of_rust(body)
            body = "\n\x00".join(strings) + "\n\x01" + "\n\x00".join(docs)
        if hashlib.sha256(body.encode("utf-8")).hexdigest() == recorded:
            return sha, True
    return None, False


def drift_report(root: Path, manifest: dict) -> int:
    """The next sweep's worklist: which read-verified surfaces describe code that
    has MOVED since they were read.

    A row's date is a fact about a reading, and a reading is only as good as the
    tree it was read against — but the tree a help surface is ABOUT is not always
    its own file. `aterm help atpkg` describes crates/atpkg; a drift check that
    groups moved code by crate and re-reads that crate's own help never reaches
    it. Measured 2026-09-13: three false fabric claims sat in aterm's manual for
    days for exactly that reason, because they describe another crate's code.

    Every row has one subject for free — its own crate — which is what the
    per-crate sweep already covers. `describes` ADDS the edges that sweep cannot
    see: the other paths a surface makes claims about. This prints, per surface,
    which of its subjects have commits after its `verified` date.

    Deliberately a REPORT and not a refusal: these repos move every day, so a
    rule that refused here would be permanently red and would teach `--no-verify`
    within a week. What it replaces is a human remembering to compute the same
    list, which is the step that was missed.
    """
    surfaces = manifest.get("surfaces", [])
    stale: list[tuple[str, str, list[str]]] = []
    cross = 0
    for row in surfaces:
        subjects = [own_crate(root, row["path"])] + list(row.get("describes") or [])
        if row.get("describes"):
            cross += 1
        anchor, exact = read_anchor(root, row["path"], row.get("prose_sha256", ""))
        # A sweep that READ this surface and found the moved code does not reach
        # any of its claims answered the drift question without earning a new
        # `verified` date (that date means the whole surface was read against its
        # handler; a drift pass is narrower). `drift_swept` records the commit it
        # asked up to, so the worklist CONVERGES instead of re-deriving the same
        # negative every sweep. It never substitutes for `verified` — R4 staleness
        # still counts from that — and it is ignored when it names a commit this
        # repository does not have.
        swept = row.get("drift_swept")
        if swept and subprocess.run(
            ["git", "-C", str(root), "merge-base", "--is-ancestor", swept, "HEAD"],
            capture_output=True,
        ).returncode == 0:
            if not anchor or subprocess.run(
                ["git", "-C", str(root), "merge-base", "--is-ancestor", anchor, swept],
                capture_output=True,
            ).returncode == 0:
                anchor, exact = swept, True
        moved = []
        for subj in subjects:
            if anchor:
                args = ["log", "--oneline", f"{anchor}..HEAD", "--", subj]
            else:
                # No committed version of the file hashes to the row (it was
                # recorded from a dirty tree), so fall back to the date. Spell
                # the midnight: `--since=YYYY-MM-DD` as a bare date EXCLUDES
                # commits made ON that day. Measured 2026-09-13 on this repo —
                # `--since=2026-09-13 -- cmd_fold.rs` found 0 commits while
                # `--since=2026-09-13T00:00:00` found the one made that evening.
                # The bare form silently dropped same-day drift, the likeliest
                # window of all.
                args = ["log", "--oneline", f"--since={row['verified']}T00:00:00", "--", subj]
            out = subprocess.run(
                ["git", "-C", str(root), *args], capture_output=True, text=True
            ).stdout.strip()
            if out:
                moved.append(f"{subj} ({len(out.splitlines())} commit(s))")
        if moved:
            if not exact:
                how = f"read {row['verified']}, DATE bound"
            elif row.get("drift_swept") == anchor:
                how = f"read {row['verified']}, swept @ {anchor[:12]}"
            else:
                how = f"read {row['verified']} @ {anchor[:12]}"
            stale.append((row["path"], how, moved))

    for path, how, moved in sorted(stale):
        print(f"drift: {path} ({how}) — subject moved: {', '.join(moved)}")
    print(
        f"drift: {len(stale)} of {len(surfaces)} surface(s) describe code that moved since they "
        f"were read ({cross} row(s) declare a cross-crate subject beyond their own)"
    )
    return 0


def run_gate(root: Path, dump: bool) -> int:
    mpath = root / MANIFEST
    if not mpath.is_file():
        print(f"check_help_surfaces: FAIL — {MANIFEST} is missing")
        return 1
    manifest = json.loads(mpath.read_text(encoding="utf-8"))
    refusals, skeleton = check(root, manifest, dt.date.today())
    if dump:
        print(json.dumps(skeleton, indent=2, ensure_ascii=False))
        return 0
    n_surf = len(manifest.get("surfaces", []))
    if refusals:
        for line in refusals:
            print(f"check_help_surfaces: {line}")
        print(
            f"check_help_surfaces: FAIL — {len(refusals)} refusal(s) over {n_surf} rostered surface(s); "
            f"`python3 scripts/check_help_surfaces.py --dump` prints the rows a fresh read would mint"
        )
        return 1
    print(
        f"check_help_surfaces: ok — {n_surf} help surface(s) read-verified, "
        f"{len(manifest.get('not_help', []))} classified not-help, max age {manifest.get('max_age_days', 180)} days"
    )
    return 0


# ------------------------------------------------------------------- selftest
def selftest() -> int:
    """Mutation arms on a synthetic tree: each must go red for its named rule, and
    the unmutated tree must be green."""
    today = dt.date(2026, 9, 10)
    src = (
        '//! A tool.\n'
        'const USAGE: &str = "Usage: tool <file> [--fast]\\n\\nOptions:\\n  --fast  skip checks";\n'
        'fn main() { let _c = \'"\'; // not a "string"\n'
        '    /* plain comment "not prose" */ println!("{USAGE}"); }\n'
    )
    other = 'fn helper() -> u8 { 7 } // no help here\n'
    failures = 0

    def build(tmp: Path, with_row=True, sha=None, verified=today.isoformat(), allow_other=False):
        (tmp / "crates/t/src").mkdir(parents=True)
        (tmp / "crates/t/Cargo.toml").write_text('[package]\nname = "t"\n')
        (tmp / "crates/t/src/main.rs").write_text(src)
        (tmp / "crates/t/src/helper.rs").write_text(other)
        rows = []
        if with_row:
            rows.append(
                {
                    "path": "crates/t/src/main.rs",
                    "prose_sha256": sha or prose_digest(tmp / "crates/t/src/main.rs"),
                    "verified": verified,
                    "method": "selftest",
                }
            )
        man = {
            "max_age_days": 180,
            "scan_roots": ["crates"],
            "program_roots": ["crates"],
            "surfaces": rows,
            "not_help": [],
        }
        if allow_other:
            man["not_help"].append({"path": "crates/t/src/helper.rs", "reason": "planted"})
        return man

    def arm(name: str, expect: str | None, mutate=None, **kw):
        nonlocal failures
        with tempfile.TemporaryDirectory() as d:
            tmp = Path(d)
            man = build(tmp, **kw)
            if mutate:
                mutate(tmp, man)
            refusals, _ = check(tmp, man, today)
            tags = " ".join(r.split()[0] for r in refusals)
            ok = (expect is None and not refusals) or (expect is not None and expect in tags)
            print(f"  {'ok ' if ok else 'RED'} {name}: {tags or 'green'}")
            if not ok:
                failures += 1

    print("check_help_surfaces --selftest")
    arm("control: read row, unchanged text", None)
    arm("R1: a new usage string with no row", "R1", with_row=False)
    arm(
        "R2: a help literal edited after the read",
        "R2",
        mutate=lambda t, m: (t / "crates/t/src/main.rs").write_text(src.replace("skip checks", "skip nothing")),
    )
    arm(
        "R2 does NOT fire on a code-only edit",
        None,
        mutate=lambda t, m: (t / "crates/t/src/main.rs").write_text(src.replace("let _c", "let _d")),
    )
    arm("R4: a row older than max_age_days", "R4", verified="2025-01-01")
    arm("R4: a malformed date", "R4", verified="yesterday")
    arm("R3: a rostered file removed", "R3", mutate=lambda t, m: (t / "crates/t/src/main.rs").unlink())
    arm("R5: not_help names a file discovery does not find", "R5", allow_other=True)

    def describes_ghost(_t, m):
        m["surfaces"][0]["describes"] = ["crates/gone"]

    def describes_own(_t, m):
        m["surfaces"][0]["describes"] = ["crates/t"]

    def describes_real(t, m):
        (t / "crates/u/src").mkdir(parents=True)
        (t / "crates/u/Cargo.toml").write_text('[package]\nname = "u"\n')
        m["surfaces"][0]["describes"] = ["crates/u"]

    def swept_ghost(_t, m):
        m["surfaces"][0]["drift_swept"] = "deadbeefdeadbeefdeadbeefdeadbeefdeadbeef"

    arm("R10: a describes edge naming a path that is not in the tree", "R10", mutate=describes_ghost)
    arm("R10: a drift_swept naming a commit this repo does not have", "R10", mutate=swept_ghost)
    arm("R10: a describes edge naming the row's own crate", "R10", mutate=describes_own)
    arm("R10 does NOT fire on a real sibling crate", None, mutate=describes_real)

    def plant_embedded(t, m):
        (t / "crates/t/assets").mkdir()
        (t / "crates/t/assets/guide.md").write_text("Usage: tool <file>\n")
        (t / "crates/t/assets/scan.rs").write_text("fn scanned() {}\n")
        (t / "crates/t/src/main.rs").write_text(
            src.replace(
                "fn main()",
                'const G: &str = include_str!("../assets/guide.md");\n'
                'const S: &str = include_str!("../assets/scan.rs");\n'
                "fn main()",
            )
        )

    arm("R8: a file include_str!-ed into a surface, unrostered", "R8", mutate=plant_embedded)

    def plant_embedded_classified(t, m):
        plant_embedded(t, m)
        m["surfaces"][0]["prose_sha256"] = prose_digest(t / "crates/t/src/main.rs")
        m["not_help"].append({"path": "crates/t/assets/guide.md", "reason": "planted"})

    arm("R8 cleared by a not_help row, which R5 must not then refuse", None, mutate=plant_embedded_classified)

    def plant_rs_include(t, m):
        (t / "crates/t/assets").mkdir()
        (t / "crates/t/assets/scan.rs").write_text("fn scanned() {}\n")
        (t / "crates/t/src/main.rs").write_text(
            src.replace("fn main()", 'const S: &str = include_str!("../assets/scan.rs");\nfn main()')
        )
        m["surfaces"][0]["prose_sha256"] = prose_digest(t / "crates/t/src/main.rs")

    arm("R8 does NOT fire on a .rs include (R1 owns that question)", None, mutate=plant_rs_include)

    def plant_program(t, m):
        (t / "crates/t/src/bin").mkdir()
        (t / "crates/t/src/bin/quiet.rs").write_text("fn main() { let _ = std::env::args(); }\n")

    arm("R7: a binary entry point with no help and no row", "R7", mutate=plant_program)

    def plant_and_classify(t, m):
        plant_program(t, m)
        m["not_help"].append({"path": "crates/t/src/bin/quiet.rs", "reason": "takes no arguments"})

    arm("R7 cleared by a not_help row, which R5 must not then refuse", None, mutate=plant_and_classify)
    arm(
        "R6: the same path rostered twice",
        "R6",
        mutate=lambda t, m: m["surfaces"].append(dict(m["surfaces"][0])),
    )
    # a doc comment that only MENTIONS help code discovers nothing
    with tempfile.TemporaryDirectory() as d:
        tmp = Path(d)
        (tmp / "crates/t/src").mkdir(parents=True)
        (tmp / "crates/t/src/lib.rs").write_text("/// see `fn usage(` and `const USAGE` elsewhere\nfn x() {}\n")
        found = discover(tmp, ["crates"])
        if found:
            print(f"  RED discovery: a doc comment mentioning help code discovered {sorted(found)}")
            failures += 1
        else:
            print("  ok  discovery: help-code markers are matched in code, not in comments")
    # extraction pins: the char literal '"' and the plain comment never reach the prose
    strings, docs = prose_of_rust(src)
    if any("not prose" in s or "not a" in s for s in strings) or docs != ["A tool."]:
        print("  RED extraction: a comment or char literal leaked into the prose")
        failures += 1
    else:
        print("  ok  extraction: comments and char literals are not prose; the module doc is")
    print(f"check_help_surfaces --selftest: {'ok' if not failures else f'{failures} arm(s) RED'}")
    return 1 if failures else 0


def main(argv: list[str]) -> int:
    ap = argparse.ArgumentParser(add_help=True)
    ap.add_argument("--repo-root", default=None)
    ap.add_argument("--dump", action="store_true", help="print skeleton rows for R1/R2 files")
    ap.add_argument("--selftest", action="store_true", help="run the mutation arms")
    ap.add_argument(
        "--drift",
        action="store_true",
        help="report which surfaces describe code that moved since they were read",
    )
    a = ap.parse_args(argv)
    if a.selftest:
        return selftest()
    root = Path(a.repo_root) if a.repo_root else Path(__file__).resolve().parents[1]
    if a.drift:
        mpath = root / MANIFEST
        if not mpath.is_file():
            print(f"check_help_surfaces: FAIL — {MANIFEST} is missing")
            return 1
        return drift_report(root, json.loads(mpath.read_text(encoding="utf-8")))
    return run_gate(root, a.dump)


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
