#!/usr/bin/env python3
"""Re-anchor the trust-core citations that are provably pure line moves, and register them.

The trust-core ledgers cite source by LINE (`worktree:P:L`, `rustc:P:L`, `trust-test:P:L`,
`first-party:<repo>/<path>:L`, or a range `P:L-M`, each with a quote), and their checkers read
those files at git HEAD (a first-party file at the commit the superproject's gitlink pins). So a
commit that inserts a line above a cited one turns the ledger red without changing a word it says.

This tool does ONLY the provable part, and refuses everything else:

  * it runs the checker and reads its `<KIND>: ...: <src>:<P>:<L>[-<M>] does not contain '<quote>'`
    findings;
  * for each, it reads the cited lines at the base (the ledger table's last commit, or --base) and
    requires them to contain the quote there;
  * it looks for those WHOLE LINES, byte-identical and contiguous, at HEAD. Exactly one match is a
    pure move; none (the text changed) or several (ambiguous) is SUBSTANTIVE and left untouched.

With --write it finishes the job in one command:

  1. every `<src>:<P>:<L>[-<M>]` of a move in the ledger's table and document is rewritten through one
     simultaneous mapping, so a chain of moves cannot rewrite a line twice;
  2. the checker runs again and regenerates the document's generated blocks;
  3. each judgment the rewrite changed (a `REVIEW: judgment X: its content changed` finding after it,
     none about X before it) takes its new digest, reviewed by ONE generated producer record whose
     evidence lists each move. A judgment that was already unreviewed before the rewrite, or any other
     new REVIEW finding, is reported for a person and never registered;
  4. the checker runs a last time and its verdict is the tool's.

    python3 scripts/trust_core/reanchor_citations.py semantics_retirement            # report
    python3 scripts/trust_core/reanchor_citations.py semantics_retirement --write    # rewrite and register

After a REBASE, the ledger's last commit is the rebased one, whose tree already holds the upstream
edit that moved the lines, so every citation would read as "already stale". Name the pre-rebase
commit, where the checker was green:

    python3 scripts/trust_core/reanchor_citations.py semantics_retirement --base ORIG_HEAD --write

`--base auto` tries the ledger table's last 20 commits (newest first) and takes the one proving
the most moves, printing each candidate's count. The default base is often already post-drift —
an alignment or pin move can stale citations in a commit that also last touched the table — while
an older ledger commit still proves them (measured: semantics_retirement 0 provable at its last
commit, 30 at the pre-alignment commit, 6 more at an older one still). A move's proof does not
depend on which green base exhibits it.

Exit status: without --write, 0 when nothing substantive remains and 1 otherwise; with --write, 0 when
the checker is green afterwards and 1 when something needs a person; 2 on a usage or environment error.
"""

from __future__ import annotations

import argparse
import ast
import datetime
import json
import re
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import common as C  # noqa: E402  (guards the Python floor before tomllib is used)

tomllib = C.tomllib

REPO = C.REPO_ROOT
TRUST_CORE = REPO / "docs" / "trust-core"

# checker module -> (ledger table, prose document, the checker's flag that regenerates the document's
# blocks). The table decides "the ledger's last commit"; the registry is reviews/<checker>.toml.
LEDGERS = {
    "semantics_retirement": ("semantics-retirement.toml", "SEMANTICS_RETIREMENT.md", "--write-counts"),
    "mir_constructor_table": ("mir-constructor-table.toml", "MIR_CONSTRUCTOR_TABLE.md", "--write-counts"),
    "core_vocabulary": ("core-vocabulary.toml", "CORE_VOCABULARY.md", "--write-counts"),
    "language_decisions": ("language-decisions.toml", "LANGUAGE_DECISIONS.md", "--write-blocks"),
    "minirust_baseline": ("minirust-baseline.toml", "MINIRUST_BASELINE.md", "--write-blocks"),
    "static_semantics_source_map": ("static-semantics-source-map.toml", "STATIC_SEMANTICS_SOURCE_MAP.md", "--write-blocks"),
    "ub_coverage_matrix": ("ub-coverage-matrix.toml", "UB_COVERAGE_MATRIX.md", "--write-blocks"),
}

EXTERNAL = {"minirust": ("minirust", "minirust"), "reference": ("rust-reference", "reference"),
            "fls": ("fls", "fls"), "a-mir-formality": ("a-mir-formality", "a-mir-formality"),
            "rfcs": ("rfcs", "rfcs")}
SOURCES = "worktree|rustc|trust-test|first-party|std|" + "|".join(EXTERNAL)
# Every checker reports a stale line citation in this shape, under its own finding kind, with the quote
# printed as a Python literal (repr), so a backslash in it is doubled.
_CITE = re.compile(
    rf"^\s*[A-Z][A-Z-]*: .*?: ({SOURCES}):(\S+?):(\d+)(?:-(\d+))? does not contain (?:the word )?"
    r"(?P<quote>'.*'|\".*\")\s*$"
)
REF = re.compile(rf"(?<![\w-])({SOURCES}):([^\s\"'»«,)]+?):(\d+)(?:-(\d+))?(?![\w-])")
_CHANGED = re.compile(r"^\s*REVIEW: judgment (?P<jid>.+?): its content changed since it was registered "
                      r"\(content (?P<new>sha256:[0-9a-f]{64}), registered (?P<old>sha256:[0-9a-f]{64})\)")
_REVIEW = re.compile(r"^\s*REVIEW(?:-HISTORY)?: ")

Cite = tuple[str, str, int, int]  # (source, path, first line, last line)


def parse_finding(line: str) -> tuple[str, str, int, int, str] | None:
    """(source, path, first, last, quote) of a stale-citation finding, or None."""
    found = _CITE.match(line)
    try:
        quote = ast.literal_eval(found.group("quote")) if found else None
    except (SyntaxError, ValueError):
        quote = None
    if not isinstance(quote, str):
        return None
    first = int(found.group(3))
    return found.group(1), found.group(2), first, int(found.group(4) or first), quote


_BEYOND = re.compile(rf"^\s*[A-Z][A-Z-]*: .*?: ({SOURCES}):(\S+?):(\d+)(?:-(\d+))?: the file has \d+ lines")


def beyond_end_findings(lines, ledger_texts) -> list[tuple[str, str, int, int, str]]:
    """A citation past a shrunken file's end carries no quote in the finding; take the quote(s) the
    ledger cites at that ref, from the table (`ref = "..", quote = ".."`) and the prose (`ref «..»`)."""
    out = []
    for line in lines:
        found = _BEYOND.match(line)
        if not found:
            continue
        ref = f"{found.group(1)}:{found.group(2)}:{found.group(3)}" + (f"-{found.group(4)}" if found.group(4) else "")
        first = int(found.group(3))
        last = int(found.group(4) or first)
        for text in ledger_texts:
            for q in re.finditer(r'ref = "' + re.escape(ref) + r'", quote = ("(?:[^"\\]|\\.)*")', text):
                out.append((found.group(1), found.group(2), first, last, tomllib.loads("q = " + q.group(1))["q"]))
            for q in re.finditer(re.escape(ref) + r" «([^»]*)»", text):
                out.append((found.group(1), found.group(2), first, last, q.group(1)))
    return out


def _holds(quote: str, cited: list[str]) -> bool:
    """The quote is on the cited lines, as the resolver reads them (with or without a comment marker)."""
    for lines in (cited, [C.strip_marker(line) for line in cited]):
        if (quote in lines[0]) if len(lines) == 1 else C.collapse(quote) in C.collapse("\n".join(lines)):
            return True
    return False


def classify(findings, lines_at_base, lines_at_head, base_label: str = "base"):
    """Split stale-citation findings into provable moves and everything else.

    `findings` are (source, path, first, last, quote); `lines_at_base(source, path)` and
    `lines_at_head(source, path)` return a file's lines or None. A citation is a MOVE only when the
    cited lines at base contain EVERY quote cited there and those WHOLE lines occur, contiguous,
    exactly once at base AND exactly once at HEAD. Pure, so it is tested without git.
    """
    moves: dict[Cite, tuple[int, int]] = {}
    substantive: list[str] = []
    quotes: dict[Cite, list[str]] = {}
    for source, path, first, last, quote in findings:
        quotes.setdefault((source, path, first, last), [])
        if quote not in quotes[(source, path, first, last)]:
            quotes[(source, path, first, last)].append(quote)
    for key, cited_quotes in quotes.items():
        source, path, first, last = key
        at = f"{source}:{path}:{first}" + (f"-{last}" if last != first else "")
        old, new = lines_at_base(source, path), lines_at_head(source, path)
        if old is None or new is None or not (1 <= first <= last <= len(old)):
            substantive.append(f"{at}: the file or line is absent at {base_label} or HEAD")
            continue
        cited = old[first - 1:last]
        wrong = [q for q in cited_quotes if not _holds(q, cited)]
        if wrong:
            substantive.append(f"{at}: already did not contain the quote at {base_label} — quote «{wrong[0][:70]}»")
            continue
        quote = cited_quotes[0]
        span = last - first + 1
        twins = sum(old[i:i + span] == cited for i in range(len(old) - span + 1))
        matches = [i + 1 for i in range(len(new) - span + 1) if new[i:i + span] == cited]
        if twins > 1:
            # A twin at base could be the copy that survived: not provably this one.
            substantive.append(f"{at}: the cited text occurs {twins} times at {base_label} — ambiguous")
        elif len(matches) == 1:
            moves[key] = (matches[0], matches[0] + span - 1)
        elif not matches:
            substantive.append(f"{at}: the cited text changed (no identical line at HEAD) — quote «{quote[:70]}»")
        else:
            substantive.append(f"{at}: the cited text occurs {len(matches)} times at HEAD ({matches[:6]}) — ambiguous")
    return moves, substantive


def rewrite(text: str, moves: dict) -> str:
    """Apply every move at once, so a chain (a->b, b->c) never rewrites a line twice. A range moves
    only as a whole, and a single-line move never touches a range that starts on its line."""

    def replace(match: re.Match) -> str:
        first = int(match.group(3))
        key = (match.group(1), match.group(2), first, int(match.group(4) or first))
        if key not in moves:
            return match.group(0)
        a, b = moves[key]
        return f"{key[0]}:{key[1]}:{a}" + (f"-{b}" if match.group(4) else "")

    return REF.sub(replace, text)


def move_label(key: Cite, new: tuple[int, int]) -> str:
    source, path, first, last = key
    if first == last:
        return f"{source}:{path}:{first} -> {new[0]}: pure move: whole line byte-identical and unique at HEAD"
    return f"{source}:{path}:{first}-{last} -> {new[0]}-{new[1]}: pure move: whole lines byte-identical and unique at HEAD"


def choose_base(results: list[tuple[str, int]]) -> str | None:
    """The base with the most provable moves from (revision, move count) pairs, NEWEST first, so a
    tie keeps the newer base. Scan order is the ledger table's own commit history: every candidate
    is a revision someone committed the citations green at, and a move is no less proven for being
    found from an older one — the cited line must still be byte-identical and unique at BOTH trees."""
    best: tuple[str, int] | None = None
    for rev, count in results:
        if best is None or count > best[1]:
            best = (rev, count)
    return best[0] if best else None


def moved_judgments(before: list[str], after: list[str]) -> tuple[dict[str, tuple[str, str]], list[str]]:
    """({judgment: (registered digest, new digest)} a rewrite alone changed, the new REVIEW findings a
    person must settle), from the checker's output before and after the rewrite. A judgment qualifies
    only when no REVIEW finding named it before: then the rewrite is the only change to its content."""
    named_before = [line.strip() for line in before if _REVIEW.match(line)]
    moved: dict[str, tuple[str, str]] = {}
    other: list[str] = []
    for line in after:
        if not _REVIEW.match(line) or line.strip() in named_before:
            continue
        changed = _CHANGED.match(line)
        jid = changed.group("jid") if changed else None
        if jid is not None and not any(f"judgment {jid}:" in b or f"judgment {jid} " in b for b in named_before):
            moved[jid] = (changed.group("old"), changed.group("new"))
        else:
            other.append(line.strip())
    return moved, other


def _entry_line(key: str, entry: dict) -> str:
    reviews = ", ".join(f"[{json.dumps(r, ensure_ascii=False)}, {json.dumps(d)}]" for r, d in entry["reviews"])
    return f'{key} = {{ digest = {json.dumps(entry["digest"])}, reviews = [{reviews}] }}'


def register(registry: str, record_id: str, record: dict, moved: dict[str, tuple[str, str]]) -> str:
    """The registry text with `record` appended and each moved judgment's digest reviewed by it. Refuses
    (ValueError) a record id already present, or an entry whose registered digest is not `old`."""
    data = tomllib.loads(registry)
    if record_id in data.get("record", {}):
        raise ValueError(f"record {record_id} already exists")
    lines = registry.split("\n")
    for jid, (old, new) in sorted(moved.items()):
        key = json.dumps(jid, ensure_ascii=False)
        at = [i for i, line in enumerate(lines) if line.startswith(f"{key} = {{")]
        entry = data.get("judgment", {}).get(jid)
        if len(at) != 1 or not isinstance(entry, dict) or tomllib.loads(lines[at[0]]).get(jid) != entry:
            raise ValueError(f"judgment {jid} is not one line of the registry")
        if entry.get("digest") != old or "retired" in entry:
            raise ValueError(f"judgment {jid} is registered at {entry.get('digest')}, not {old}")
        lines[at[0]] = _entry_line(key, {"digest": new, "reviews": [*entry["reviews"], [record_id, new]]})
    text = "\n".join(lines).rstrip("\n") + "\n"
    evidence = "".join(f"  {json.dumps(e, ensure_ascii=False)},\n" for e in record["evidence"])
    text += (f"\n[record.{record_id}]\nround = {json.dumps(record['round'], ensure_ascii=False)}\n"
             f"date = {json.dumps(record['date'])}\nevidence = [\n{evidence}]\n"
             f"reason = {json.dumps(record['reason'], ensure_ascii=False)}\n")
    parsed = tomllib.loads(text)
    if parsed["record"].get(record_id) != record or any(parsed["judgment"][j]["digest"] != n for j, (_, n) in moved.items()):
        raise ValueError("the registry does not read back as written")
    return text


def git(*args: str) -> str:
    return subprocess.run(["git", "-C", str(REPO), *args], capture_output=True, text=True, check=True).stdout


def lines_at(rev: str, source: str, path: str) -> list[str] | None:
    """A cited file's lines at superproject revision `rev`, or None. `first-party:<repo>/<rest>` is
    read from that submodule at the commit the gitlink at `rev` names. External sources use the
    immutable EXTERNAL_PINS blob at that revision, never a clone's checkout or today's pin. Missing
    historical pins/objects refuse a move; reads never fetch. Standard-library citations use the
    upstream Rust alignment object, matching the static-semantics checker's separate std tree."""
    if source == "first-party":
        repo, _, rest = path.partition("/")
        tree = C.first_party_tree(REPO, repo, rev) if rest else None
        return tree.lines(rest) if tree is not None else None
    if source in EXTERNAL or source == "std":
        text = C.GitTree(REPO, rev).text(C.PINS_REL)
        try:
            pins = tomllib.loads(text) if text is not None else {}
            if pins.get("schema") != "trust.core.external-pins.v1":
                return None
            if source == "std":
                revision, directory = pins["alignment"]["rust_revision"], "rust"
            else:
                name, directory = EXTERNAL[source]
                revision = pins["sources"][name]["revision"]
            if not isinstance(revision, str) or re.fullmatch(r"[0-9a-f]{40}", revision) is None:
                return None
        except (KeyError, TypeError, tomllib.TOMLDecodeError):
            return None
        return C.GitTree(C.sources_root() / directory, revision).lines(path)
    if source not in ("rustc", "worktree", "trust-test"):
        return None
    return C.GitTree(REPO, rev).lines(path)


def run_checker(python: str, checker: str, *flags: str) -> tuple[int, list[str]]:
    run = subprocess.run([python, str(REPO / "scripts" / "trust_core" / f"{checker}.py"), *flags],
                         cwd=REPO, capture_output=True, text=True)
    return run.returncode, run.stdout.splitlines() + run.stderr.splitlines()


def unique_record_id(registry: str, stem: str) -> str:
    records = tomllib.loads(registry).get("record", {})
    suffix = 1
    while (f"{stem}-{suffix}" if suffix > 1 else stem) in records:
        suffix += 1
    return f"{stem}-{suffix}" if suffix > 1 else stem


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("checker", choices=sorted(LEDGERS))
    parser.add_argument("--write", action="store_true", help="rewrite the provable moves and register them")
    parser.add_argument("--base", help="a revision where the citations were green, or `auto` to try the "
                        "table's last 20 commits and take the one proving the most moves "
                        "(default: the ledger table's last commit; after a rebase, the pre-rebase commit)")
    parser.add_argument("--python", default=sys.executable, help="interpreter for the checker (needs 3.11+)")
    args = parser.parse_args()

    table_name, doc_name, write_flag = LEDGERS[args.checker]
    table, doc = TRUST_CORE / table_name, TRUST_CORE / doc_name
    registry = TRUST_CORE / "reviews" / f"{args.checker}.toml"
    files = [p for p in (table, doc) if p.exists()]
    if git("status", "--porcelain", "--", *(str(p) for p in files + [registry])).strip():
        print(f"refusing: {', '.join(p.name for p in files + [registry])} has uncommitted changes; the ledger's "
              "last commit must be the state these citations were green in", file=sys.stderr)
        return 2
    auto = args.base == "auto"
    if args.base and not auto:
        resolved = subprocess.run(["git", "-C", str(REPO), "rev-parse", "--verify", "--quiet",
                                   f"{args.base}^{{commit}}"], capture_output=True, text=True)
        base = resolved.stdout.strip()
        if resolved.returncode != 0 or not base:
            print(f"refusing: --base {args.base} is not a commit", file=sys.stderr)
            return 2
        candidates = [base]
    else:
        candidates = git("log", "-20", "--format=%H", "--", str(table)).split()
        base = candidates[0] if candidates else ""
    if not base:
        print(f"refusing: {table} has no commit to re-anchor from", file=sys.stderr)
        return 2
    head = git("rev-parse", "HEAD").strip()

    before_status, before = run_checker(args.python, args.checker)
    findings = [found for line in before if (found := parse_finding(line))]
    findings += beyond_end_findings(before, [p.read_text(encoding="utf-8") for p in files])

    caches: dict[tuple[str, str, str], list[str] | None] = {}

    def reader(rev):
        def read(source: str, path: str):
            if (rev, source, path) not in caches:
                caches[(rev, source, path)] = lines_at(rev, source, path)
            return caches[(rev, source, path)]
        return read

    if auto:
        scored: list[tuple[str, tuple[dict, list]]] = []
        for candidate in candidates:
            result = classify(findings, reader(candidate), reader(head), candidate[:10])
            scored.append((candidate, result))
            print(f"  AUTO-BASE {candidate[:10]} provable={len(result[0])} substantive={len(result[1])}")
        chosen = choose_base([(rev, len(result[0])) for rev, result in scored])
        base = chosen if chosen is not None else base
        moves, substantive = next(result for rev, result in scored if rev == base)
        print(f"  AUTO-BASE chose {base[:10]} ({len(moves)} provable move(s))")
    else:
        moves, substantive = classify(findings, reader(base), reader(head), base[:10])
    print(f"{args.checker}: {len(findings)} stale-citation finding(s); {len(moves)} provable move(s); "
          f"{len(substantive)} substantive; base {base[:10]}")
    for key, new in sorted(moves.items()):
        print(f"  MOVE {move_label(key, new).split(': pure move')[0]}")
    for item in substantive:
        print(f"  SUBSTANTIVE {item}")
    if not args.write:
        return 1 if substantive else 0
    if not moves:
        # No eligible repair does not establish that the checker passed. Keep
        # its diagnostics and its violation/environment-error distinction.
        for line in before:
            print(line)
        return before_status or (1 if substantive else 0)

    for path in files:
        text = path.read_text(encoding="utf-8")
        rewritten = rewrite(text, moves)
        if rewritten != text:
            path.write_text(rewritten, encoding="utf-8")
            print(f"  rewrote {path.relative_to(REPO)}")

    _, after = run_checker(args.python, args.checker, write_flag)
    moved, other = moved_judgments(before, after)
    if git("rev-parse", "HEAD").strip() != head:
        print("refusing to register: HEAD moved while the checker ran", file=sys.stderr)
        return 2
    if moved:
        text = registry.read_text(encoding="utf-8")
        record_id = unique_record_id(text, f"pure-moves-{base[:10]}-to-{head[:10]}")
        base_note = (f"--base auto chose {base[:10]} (most provable of the table's last {len(candidates)} commits)"
                     if auto else f"--base {base[:10]}" if args.base else f"base {base[:10]}, the table's last commit")
        record = {
            "round": f"cited lines moved between {base[:10]} and {head[:10]}, each a whole cited line byte-identical and unique at both commits "
                     "(generated by scripts/trust_core/reanchor_citations.py; producer record; independent verification pending)",
            "date": datetime.date.today().isoformat(),
            "evidence": [
                f"{args.checker}.py at {head[:10]}: {len(findings)} stale-citation finding(s); "
                f"scripts/trust_core/reanchor_citations.py {args.checker} --write ({base_note}): "
                f"{len(moves)} pure move(s), {len(substantive)} substantive",
                *(move_label(key, new) for key, new in sorted(moves.items())),
                f"{args.checker}.py after the rewrite: {len(moved)} judgment(s) changed by these moves alone "
                "(no REVIEW finding named them before it); each new digest is read from its REVIEW finding",
            ],
            "reason": "Only cited line numbers move; every quote and every other word of each judgment is unchanged. "
                      "The judgments take their new digests from the checker's output.",
        }
        registry.write_text(register(text, record_id, record, moved), encoding="utf-8")
        print(f"  registered {len(moved)} judgment(s) under record {record_id} in {registry.relative_to(REPO)}")
    for line in other:
        print(f"  NEEDS A PERSON {line}")

    code, final = run_checker(args.python, args.checker)
    remaining = [line.strip() for line in final if re.match(r"^\s+[A-Z][A-Z-]*: ", line)]
    print(f"{args.checker} after the re-anchor: " + ("OK" if code == 0 else f"{len(remaining)} violation(s) remain"))
    for line in remaining:
        print(f"  {line}")
    return 0 if code == 0 else 1


if __name__ == "__main__":
    raise SystemExit(main())
