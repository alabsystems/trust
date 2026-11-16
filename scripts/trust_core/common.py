#!/usr/bin/env python3
"""The machinery every Trust core Phase 0 checker shares, implemented once.

Design of record: docs/design/2026-09-16-trust-core-architecture.md, §5.0 (rules 3
and 10: fail-closed, an exit is a pass line that can fail) and §5.2 Stage 0.2.
The bounded acceptance standard for the Phase 0 tables has a MECHANICAL layer that
fails on any violation and a JUDGMENT layer in which every non-mechanical decision is
content with a digest and an append-only review record. This module is both layers'
shared implementation; a deliverable's checker keeps only its own rules.

  PINS       docs/trust-core/EXTERNAL_PINS.toml is the one record of the external
             revisions (load_pins). verify_clone refuses a clone that is not a plain
             copy of its pin: another HEAD, a dirty worktree, an index entry flagged
             skip-worktree or assume-unchanged, replace refs, a grafts file, or a
             commit date other than the recorded one or after the alignment
             timestamp. locate_clones raises MissingClone with every clone command.
             A source recorded with `read = "objects"` is read only from git objects
             at its pin (GitTree), so its HEAD, worktree and index are not what a
             check reads: verify_clone then requires the pinned commit, not a clean
             checkout of it. A source recorded with a `branch` has its pin re-derived
             on every run as the first-parent commit of that branch at or before the
             alignment timestamp, from a history that is not shallow.
  TREES      cited bytes come from git objects (GitTree): a clone at its pin, this
             repository at HEAD, a first-party submodule at the commit its gitlink
             names. A modified working tree cannot supply a quote. DirTree reads a
             directory and exists for mutation tests that pass it explicitly. No read
             fetches: a missing object of a partial clone is absent, not fetched into
             the clone (only a test asks for `lazy_fetch`). RootedTree shows a tree only
             under declared path roots, so a corpus bounded by a stated rule reads
             nothing outside it, whichever objects the clone happens to hold.
  CITATIONS  Resolver.check resolves `design:L`, `minirust:P:L`, `reference:P:L`,
             `fls:P:L`, `a-mir-formality:P:L`, `rfcs:P:L`, `rustc:P:L` (compiler/,
             library/, src/, tests/), `worktree:P:L`, `first-party:NAME/P:L`, each
             with an optional `-L2` range, plus the Reference rule id `reference:r[ID]`
             and the FLS paragraph id `fls:fls_ID`, against an exact quote (a whole
             word when `word`; with `strip`, also against the lines with one leading
             comment or blockquote marker removed, as `strip_marker` does).
             check_prose resolves every `REF «quote»` of a document and refuses a line
             citation that is not in that checked form. A checker may declare further
             clone kinds (Resolver `kinds`, read from trees[kind]) and kinds whose
             citations are always compared with `strip` (`comment_kinds`).
  UPSTREAM   a citation (rustc: or worktree:) of a file under compiler/, library/,
             src/ or tests/ that carries a `Trust:` marker anywhere fails PIN unless
             the cited lines lie inside a region the checker parses and verified free
             of one (Resolver.upstream_region: an enum whose variants it enumerates,
             registered before any citation into its file is resolved);
             Resolver.resolve reports it as PIN whichever predicate cites. A parsed
             region that carries a marker fails PIN itself.
  UNIQUENESS unique_rows refuses two rows with one key; repeated_elements refuses a
             list that repeats an element, at any depth.
  BLOCKS     check_block compares a generated block between `<!-- NAME:begin` and
             `<!-- NAME:end -->` with its rendering; replace_block rewrites it.
  REVIEWS    a judgment is content under an id `KIND:KEY`: a table row selected by
             key, a table's comments, each with the lines that place it uniquely
             (toml_comments), document prose between `<!-- reviewed:prose:ID -->` and
             `<!-- /reviewed:prose:ID -->`, or a document's outline: its headings,
             block markers and section opening markers in order (document_judgments,
             which refuses any other line outside a section). merge_judgments refuses
             one id from two sources. docs/trust-core/reviews/<deliverable>.toml
             (data only, no comments) registers each id with its digest and review
             records. check_reviews fails on an unregistered judgment, content whose
             digest differs from the registered one, a registered digest no appended
             review reviewed, a registry entry whose judgment is gone (unless
             retired), and against every committed version of the registry: an edited
             or removed record, judgment or review, reviews out of their committed
             order, and a committed record credited with a review it did not make
             when committed. Two lines of history merged keep each line's reviews in
             its order (check_registry_history). The history is refused when it
             cannot be read whole: a shallow repository, a failed `git log`, or a
             registry outside the repository.
  IMMUTABLE  check_immutable refuses a file (a web snapshot) that differs from its
             first committed version or from its sha256 pin.

Author: Andrew Yates <andrewyates.name@gmail.com>
Copyright 2026 Andrew Yates | License: Apache-2.0 OR MIT
"""

import bisect
import hashlib
import json
import os
import posixpath
import re
import subprocess
import sys
from dataclasses import dataclass
from datetime import datetime
from pathlib import Path

try:
    import tomllib
except ModuleNotFoundError:  # pragma: no cover - interpreter guard
    tomllib = None

# Every checker imports this module before it defines anything, so an interpreter too old for
# tomllib and the `X | Y` annotations stops here with its version named, not later with a
# TypeError or an AttributeError on `None`. `#!/usr/bin/env python3` runs whichever python3 is
# first on PATH (macOS ships 3.9 as /usr/bin/python3); scripts/check_script_tests.sh tries
# python3.14 first.
if sys.version_info < (3, 11) or tomllib is None:  # pragma: no cover - interpreter guard
    raise SystemExit(f"{Path(sys.argv[0] or 'trust_core').name}: the Trust core checkers need Python 3.11 or later "
                     f"(tomllib, `X | Y` annotations); {sys.executable} is {sys.version.split()[0]}")

REPO_ROOT = Path(__file__).resolve().parents[2]
PINS_REL = "docs/trust-core/EXTERNAL_PINS.toml"
DESIGN_REL = "docs/design/2026-09-16-trust-core-architecture.md"
# The superproject commit the design's header says the document was "Written read-only against".
DESIGN_HEADER_PIN = re.compile(r"\*\*Written\s+read-only\s+against\*\*\s+superproject\s+`([0-9a-f]{7,40})`")
REVIEWS_DIR = "docs/trust-core/reviews"
TRUST_VERSION_REL = "release/trust-version.toml"
# The durable source cache scripts/trust_core/fetch_sources.py fills: outside the repository
# (build/ belongs to x.py) and outside /tmp (macOS empties it, which lost the Phase 0 clones
# once). $TRUST_CORE_SOURCES wins; then $XDG_CACHE_HOME/trust/trust-core-sources.
DEFAULT_SOURCES = str(Path(os.environ.get("XDG_CACHE_HOME") or Path.home() / ".cache") / "trust" / "trust-core-sources")
FETCH_COMMAND = "python3 scripts/trust_core/fetch_sources.py"
REVIEWS_SCHEMA = "trust.core.reviews.v1"
HEX40 = re.compile(r"^[0-9a-f]{40}$")
DIGEST = re.compile(r"^sha256:[0-9a-f]{64}$")
DATE = re.compile(r"^\d{4}-\d{2}-\d{2}$")
UPSTREAM_PREFIXES = ("compiler/", "library/", "src/", "tests/")
# CLAUDE.md: every modification to an upstream rustc file is marked `// Trust:`. The tree also
# spells it with a tag: `// Trust (W6):`, `/// Trust #54:`, `// Trust #7 (R3):` (every such
# spelling in compiler/, library/, src/ and tests/ at 2026-09-17 matches TRUST_TAGGED).
TRUST_EDIT = "Trust:"
TRUST_TAGGED = re.compile(r"(?://[/!]?|/\*+!?)\s*Trust(?:\s*#\d+)?(?:\s*\([^)\n]*\))?\s*:")


def is_trust_marker(line: str) -> bool:
    """True for a line carrying a Trust edit marker in any of its spellings."""
    return TRUST_EDIT in line or TRUST_TAGGED.search(line) is not None
# A line citation inside free text (a note, a reason) that no predicate checks.
FREE_TEXT_CITATION = re.compile(r"\blines?\s+[0-9]+|:[0-9]+\b")


class Findings:
    """Violations as `KIND: message` lines; a checker exits non-zero when any exist."""

    def __init__(self) -> None:
        self.violations: list[str] = []

    def add(self, kind: str, message: str) -> None:
        self.violations.append(f"{kind}: {message}")


# --------------------------------------------------------------------------
# git
# --------------------------------------------------------------------------


def git_environment() -> dict[str, str]:
    """No inherited GIT_* variable: GIT_DIR, GIT_INDEX_FILE, GIT_REPLACE_REF_BASE,
    GIT_GRAFT_FILE and the rest could point a pinned read elsewhere."""
    return {k: v for k, v in os.environ.items() if not k.startswith("GIT_")}


def git(repo: Path | str, *args: str, binary: bool = False, stdin: bytes | None = None, git_dir: bool = False,
        lazy_fetch: bool = False, ok_codes: tuple = (0,)):
    """stdout of git (str, or bytes when `binary`), or None when git fails.

    Replace objects are disabled, so `git replace <pin> <other>` cannot make a read of
    the pin return another commit's tree. `git_dir` addresses a bare object store. A partial
    clone never fetches a missing object (`--no-lazy-fetch`) unless `lazy_fetch` asks, so a
    read cannot modify the clone or depend on the network. `ok_codes` are the exit
    codes that are not a failure: `git grep` exits 1 when nothing matches, which is an
    empty result, not an unreadable tree."""
    where = ["--git-dir", str(repo)] if git_dir else ["-C", str(repo)]
    fetch = [] if lazy_fetch else ["--no-lazy-fetch"]
    try:
        run = subprocess.run(["git", "--no-replace-objects", *fetch, *where, *args], input=stdin,
                             capture_output=True, env=git_environment())
    except OSError:
        return None
    if run.returncode not in ok_codes or (run.returncode != 0 and run.stderr.strip()):
        return None
    return run.stdout if binary else run.stdout.decode("utf-8", "replace")


def design_header_pin(repo: Path | str, design_text: str) -> tuple[list[str], str | None]:
    """Every commit the design header names as the one the document was written against, and the
    full commit of `repo` it resolves to when the header names exactly one that names exactly one
    commit (else None: no pin, several, absent from this clone, or an ambiguous abbreviation)."""
    named = DESIGN_HEADER_PIN.findall(design_text)
    if len(named) != 1:
        return named, None
    commit = (git(repo, "rev-parse", "--verify", "--quiet", f"{named[0]}^{{commit}}") or "").strip()
    return named, commit if HEX40.match(commit) else None


# --------------------------------------------------------------------------
# pins
# --------------------------------------------------------------------------


class PinsError(ValueError):
    pass


class MissingClone(Exception):
    """A source clone a checker reads is absent; the message carries each clone command."""


@dataclass(frozen=True)
class Source:
    name: str
    url: str
    revision: str
    committer_date: str
    read: str = "checkout"  # "objects": read only from git objects at the pin (verify_clone)
    branch: str | None = None  # the branch whose first-parent history names the pin (verify_clone)

    @property
    def directory(self) -> str:
        return self.url.rstrip("/").rsplit("/", 1)[-1]


@dataclass(frozen=True)
class Pins:
    alignment: str
    alignment_date: str
    sources: dict


def parse_date(stamp: str) -> datetime | None:
    try:
        return datetime.fromisoformat(stamp.replace("Z", "+00:00"))
    except (AttributeError, ValueError):
        return None


def load_pins(path: Path | None = None) -> Pins:
    """The alignment and every cloned source of EXTERNAL_PINS.toml; in-tree sources
    (Miri) have no clone. A source may record how it is read (`read`: checkout or objects)
    and the branch its pin is derived from (`branch`). A malformed record raises PinsError."""
    path = path or REPO_ROOT / PINS_REL
    try:
        data = tomllib.loads(Path(path).read_text(encoding="utf-8"))
    except (OSError, tomllib.TOMLDecodeError) as error:
        raise PinsError(f"{path}: {error}") from error
    if data.get("schema") != "trust.core.external-pins.v1":
        raise PinsError(f"{path}: schema is not trust.core.external-pins.v1")
    alignment = data.get("alignment", {})
    revision, date = alignment.get("rust_revision"), alignment.get("rust_committer_date")
    if not isinstance(revision, str) or not HEX40.match(revision) or parse_date(date) is None:
        raise PinsError(f"{path}: [alignment] needs a 40-hex rust_revision and an ISO rust_committer_date")
    sources = {}
    for name, row in sorted(data.get("sources", {}).items()):
        if str(row.get("repo", "")).startswith("in-tree"):
            continue
        rev, stamp, url = row.get("revision"), row.get("committer_date"), row.get("repo")
        if not isinstance(rev, str) or not HEX40.match(rev):
            raise PinsError(f"{path}: [sources.{name}] revision {rev!r} is not 40-hex")
        if not isinstance(url, str) or not url.startswith("https://"):
            raise PinsError(f"{path}: [sources.{name}] repo {url!r} is not an https URL")
        when = parse_date(stamp)
        if when is None or when > parse_date(date):
            raise PinsError(f"{path}: [sources.{name}] committer_date {stamp!r} is not at or before the alignment")
        read, branch = row.get("read", "checkout"), row.get("branch")
        if read not in ("checkout", "objects"):
            raise PinsError(f"{path}: [sources.{name}] read {read!r} is not checkout or objects")
        if branch is not None and (not isinstance(branch, str) or not branch.strip()):
            raise PinsError(f"{path}: [sources.{name}] branch {branch!r} is not a branch name")
        sources[name] = Source(name, url, rev, stamp, read, branch)
    return Pins(revision, date, sources)


def sources_root() -> Path:
    return Path(os.environ.get("TRUST_CORE_SOURCES") or DEFAULT_SOURCES)


def clone_command(source: Source, path: Path) -> str:
    return f"git clone {source.url} {path} && git -C {path} checkout {source.revision}"


def locate_clones(pins: Pins, names, overrides: dict | None = None) -> dict[str, Path]:
    """name -> clone directory ($TRUST_CORE_SOURCES/<repo name> unless overridden)."""
    found, missing = {}, []
    for name in names:
        if name not in pins.sources:
            raise PinsError(f"{PINS_REL} records no source {name!r}")
        source = pins.sources[name]
        path = Path((overrides or {}).get(name) or sources_root() / source.directory)
        if not (path / ".git").exists():
            missing.append(f"the {name} clone is missing at {path}; clone it:\n  {clone_command(source, path)}")
        found[name] = path
    if missing:
        raise MissingClone("\n".join(missing) + f"\n(fetch every pinned source at once: {FETCH_COMMAND}; or point TRUST_CORE_SOURCES at a directory holding these clones)")
    return found


def verify_objects(findings: Findings, what: str, repo: Path) -> None:
    """Refuse replace refs and a grafts file: either substitutes history for the pin."""
    replaced = git(repo, "for-each-ref", "--format=%(refname)", "refs/replace/")
    if replaced is None or replaced.strip():
        findings.add("PIN", f"{what} carries replace refs, or they cannot be listed: {(replaced or '').split()[:3]}")
    grafts = git(repo, "rev-parse", "--git-path", "info/grafts")
    if grafts is None or (Path(repo) / grafts.strip()).exists():
        findings.add("PIN", f"{what} carries a grafts file, or it cannot be located")


def verify_clone(findings: Findings, path: Path, source: Source, pins: Pins) -> None:
    """The clone holds its pin as recorded. A checkout-read clone is a plain checkout of the pin:
    HEAD, a clean worktree, only plain index entries. An objects-read clone holds the pinned
    commit, and its HEAD, worktree and index are not read. Either refuses replace refs, a grafts
    file and a commit date other than the recorded one. With a `branch`, the history is not
    shallow and the first-parent commit of the branch at or before the alignment timestamp is
    the pin. No read here fetches a missing object."""
    what = f"{source.name} clone {path}"
    if source.read == "objects":
        if git(path, "cat-file", "-e", f"{source.revision}^{{commit}}") is None:
            findings.add("PIN", f"{what} does not hold the pinned commit {source.revision}")
    else:
        head = (git(path, "rev-parse", "HEAD") or "").strip()
        if head != source.revision:
            findings.add("PIN", f"{what} is at {head or 'no commit'}, not the pinned {source.revision}")
        status = git(path, "status", "--porcelain", "--untracked-files=all")
        if status is None or status.strip():
            findings.add("PIN", f"{what} is not a clean checkout: {(status or 'git status failed').splitlines()[:3]}")
        flags = git(path, "ls-files", "-v", "-z")
        flagged = sorted(e[2:] for e in (flags or "").split("\0") if e and not e.startswith("H "))
        if flags is None or flagged:
            findings.add("PIN", f"{what} has index entries that are not plain tracked files (skip-worktree, assume-unchanged or unmerged hide edits from git status): {flagged[:3]}")
    verify_objects(findings, what, path)
    if source.branch is not None:
        if (git(path, "rev-parse", "--is-shallow-repository") or "").strip() != "false":
            findings.add("PIN", f"{what} is shallow (or not a repository), so its pin cannot be derived from its history")
        derived = (git(path, "-c", "core.commitGraph=false", "rev-list", "--first-parent", "-1",
                       f"--before={pins.alignment_date}", source.branch, "--") or "").strip()
        if derived != source.revision:
            findings.add("PIN", f"{what}: the first-parent commit of {source.branch} at or before {pins.alignment_date} is "
                                f"{derived or 'none'}, not the pinned {source.revision}")
    stamp = (git(path, "log", "-1", "--format=%cI", source.revision, "--") or "").strip()
    when = parse_date(stamp)
    if when is None or when != parse_date(source.committer_date) or when > parse_date(pins.alignment_date):
        findings.add("PIN", f"{what}: the pin was committed {stamp or 'unknown'}, not the recorded {source.committer_date} at or before the alignment {pins.alignment_date}")


def verify_alignment(findings: Findings, tree, pins: Pins) -> None:
    """release/trust-version.toml (read from `tree`) names the alignment EXTERNAL_PINS records."""
    text = tree.text(TRUST_VERSION_REL)
    try:
        revision = tomllib.loads(text or "")["rust_alignment"]["revision"]
    except (KeyError, TypeError, tomllib.TOMLDecodeError):
        revision = None
    if revision != f"rust-lang/rust:{pins.alignment}":
        findings.add("PIN", f"{TRUST_VERSION_REL} [rust_alignment].revision is {revision!r}, not rust-lang/rust:{pins.alignment}")


# --------------------------------------------------------------------------
# trees
# --------------------------------------------------------------------------


class GitTree:
    """The files of one commit, read from git objects in batches (`cat-file --batch`)."""

    def __init__(self, repo: Path | str, rev: str, git_dir: bool = False, lazy_fetch: bool = False) -> None:
        self.repo, self.rev, self.git_dir, self.lazy_fetch = Path(repo), rev, git_dir, lazy_fetch
        self._text: dict[str, str | None] = {}
        self._listed: dict[str, list[str]] = {}

    def files(self, prefix: str = "", suffixes: tuple = ()) -> list[str]:
        if prefix not in self._listed:
            args = ["ls-tree", "-r", "--name-only", "-z", self.rev] + (["--", prefix] if prefix else [])
            self._listed[prefix] = [r for r in (git(self.repo, *args, git_dir=self.git_dir, lazy_fetch=self.lazy_fetch) or "").split("\0") if r]
        return sorted(r for r in self._listed[prefix] if r.startswith(prefix) and (not suffixes or r.endswith(suffixes)))

    def prefetch(self, rels) -> None:
        want = [r for r in dict.fromkeys(rels) if r not in self._text]
        if not want:
            return
        out = git(self.repo, "cat-file", "--batch", binary=True, git_dir=self.git_dir, lazy_fetch=self.lazy_fetch,
                  stdin="".join(f"{self.rev}:{r}\n" for r in want).encode()) or b""
        pos = 0
        for rel in want:
            end = out.find(b"\n", pos)
            header = out[pos:end].split() if end >= 0 else []
            self._text[rel] = None
            if len(header) != 3 or header[1] != b"blob":
                pos = end + 1 if end >= 0 else len(out)
                if len(header) == 3:  # a tree or commit: skip its body
                    pos += int(header[2]) + 1
                continue
            size = int(header[2])
            try:
                self._text[rel] = out[end + 1:end + 1 + size].decode("utf-8")
            except UnicodeDecodeError:
                pass
            pos = end + 1 + size + 1

    def text(self, rel: str) -> str | None:
        self.prefetch([rel])
        return self._text[rel]

    def lines(self, rel: str) -> list[str] | None:
        text = self.text(rel)
        return None if text is None else text.split("\n")


class DirTree:
    """A directory with GitTree's interface. Only a mutation test passes one explicitly."""

    def __init__(self, root: Path | str, files: dict[str, str] | None = None) -> None:
        self.root, self.overlay = Path(root), dict(files or {})

    def files(self, prefix: str = "", suffixes: tuple = ()) -> list[str]:
        found = {p.relative_to(self.root).as_posix() for p in self.root.rglob("*") if p.is_file() and ".git" not in p.parts}
        found |= set(self.overlay)
        return sorted(r for r in found if r.startswith(prefix) and (not suffixes or r.endswith(suffixes)))

    def prefetch(self, rels) -> None:
        pass

    def text(self, rel: str) -> str | None:
        if rel in self.overlay:
            return self.overlay[rel]
        try:
            return (self.root / rel).read_text(encoding="utf-8")
        except (OSError, UnicodeDecodeError):
            return None

    def lines(self, rel: str) -> list[str] | None:
        text = self.text(rel)
        return None if text is None else text.split("\n")


class RootedTree:
    """`tree` seen only under `roots` (path prefixes such as "library/core/src/"): a file
    outside them, or a path that is not written canonically, is absent from files, text and
    lines. A citation, a search or an enumeration of a corpus a rule bounds reads nothing past
    the bound, whichever objects a partial clone holds; no roots is an empty tree."""

    def __init__(self, tree, roots) -> None:
        self.tree, self.roots = tree, tuple(roots)

    def inside(self, rel: object) -> bool:
        return isinstance(rel, str) and bool(self.roots) and rel == posixpath.normpath(rel) and rel.startswith(self.roots)

    def files(self, prefix: str = "", suffixes: tuple = ()) -> list[str]:
        return [r for r in self.tree.files(prefix, suffixes) if self.inside(r)]

    def prefetch(self, rels) -> None:
        self.tree.prefetch([r for r in rels if self.inside(r)])

    def text(self, rel: str) -> str | None:
        return self.tree.text(rel) if self.inside(rel) else None

    def lines(self, rel: str) -> list[str] | None:
        text = self.text(rel)
        return None if text is None else text.split("\n")


def first_party_tree(repo: Path, name: str, rev: str = "HEAD") -> GitTree | None:
    """first-party/<name> at the commit the superproject's gitlink names at `rev`, read from
    its own checkout when that is a repository of its own, else from the superproject's
    modules store (an empty submodule directory would silently read the superproject)."""
    listing = (git(repo, "ls-tree", rev, f"first-party/{name}") or "").split()
    if len(listing) < 3 or listing[1] != "commit":
        return None
    checkout = Path(repo) / "first-party" / name
    top = (git(checkout, "rev-parse", "--show-toplevel") or "").strip() if (checkout / ".git").exists() else ""
    if top and os.path.realpath(top) == os.path.realpath(checkout):
        store = (git(checkout, "rev-parse", "--absolute-git-dir") or "").strip()
    else:
        common = (git(repo, "rev-parse", "--path-format=absolute", "--git-common-dir") or "").strip()
        store = os.path.join(common, "modules", "first-party", name)
    return GitTree(store, listing[2], git_dir=True) if store and os.path.isdir(store) else None


# --------------------------------------------------------------------------
# citations
# --------------------------------------------------------------------------

SOURCE_KINDS = ("design", "minirust", "reference", "fls", "a-mir-formality", "rustc", "worktree", "first-party", "rfcs")


def ref_pattern(kinds: tuple) -> re.Pattern:
    return re.compile(
        r"^(?P<source>" + "|".join(re.escape(s) for s in kinds) + r"):"
        r"(?:r\[(?P<rule>[A-Za-z0-9_.-]+)\]|(?P<fls>fls_[A-Za-z0-9]+)|(?:(?P<path>[^\s:«]+):)?(?P<start>[1-9][0-9]*)(?:-(?P<end>[1-9][0-9]*))?)$"
    )


def prose_citation_pattern(kinds: tuple) -> re.Pattern:
    return re.compile(r"\b(?:" + "|".join(re.escape(s) for s in kinds) + r"):[^\s«]+ «[^»]*»")


REF = ref_pattern(SOURCE_KINDS)
PROSE_CITATION = prose_citation_pattern(SOURCE_KINDS)
UNCHECKED_CITATION = re.compile(
    r"(?:\b(?:design|minirust|reference|fls|rustc|worktree):[0-9]+\b|[\w./-]+\.(?:md|rs|toml|py|sh|lean|rst):[0-9]+\b|\blines?\s+[0-9]+\b)"
)
FLS_PARAGRAPH = re.compile(r":dp:`(fls_[A-Za-z0-9]+)`")
REFERENCE_RULE = re.compile(r"^r\[([^\]\s]+)\]\s*$")
# One leading marker a quote may omit under `strip`: a Rust comment (`//`, `///`, `//!`), a
# markdown blockquote (`>`, repeated), or an FLS paragraph id token.
LINE_MARKER = re.compile(r"^\s*(?://[/!]?|>(?:\s*>)*|:dp:`[^`]*`)[ \t]?")


def strip_marker(line: str) -> str:
    return LINE_MARKER.sub("", line, count=1)


def whole_word(token: str, text: str) -> bool:
    return re.search(r"(?<![A-Za-z0-9_])" + re.escape(token) + r"(?![A-Za-z0-9_])", text) is not None


def collapse(text: str) -> str:
    return " ".join(text.split())


def parse_ref(ref: object, kinds: tuple = SOURCE_KINDS) -> dict | None:
    """The parts of a citation reference, or None when it is not one. `kinds` extends the
    source kinds only as a Resolver declares them (every declared kind is a path kind)."""
    pattern = REF if kinds == SOURCE_KINDS else ref_pattern(kinds)
    match = pattern.match(ref) if isinstance(ref, str) else None
    if match is None:
        return None
    parts = match.groupdict()
    if parts["start"] is not None:
        if (parts["source"] == "design") != (parts["path"] is None):
            return None
        parts["start"] = int(parts["start"])
        parts["end"] = int(parts["end"]) if parts["end"] else parts["start"]
        if parts["end"] < parts["start"]:
            return None
    elif (parts["rule"] and parts["source"] != "reference") or (parts["fls"] and parts["source"] != "fls"):
        return None
    return parts


class PinProblem(str):
    """A citation problem that is a PIN violation whichever predicate resolved the citation: the
    cited text is not verified upstream text."""

    kind = "PIN"


class Resolver:
    """Resolves citations against pinned trees. `trees` maps a clone source to its tree at the
    pin and "worktree" to this repository at HEAD; "design" may override the design file.
    `kinds` declares further path citation kinds, each read from trees[kind] (a checker's own
    pinned clone); `comment_kinds` are kinds whose citations are always checked with `strip`,
    so a quote may span the lines of one doc comment without their `///`, `//!` or `//`."""

    def __init__(self, repo: Path, trees: dict, kinds: tuple = (), comment_kinds: tuple = ()) -> None:
        self.repo, self.trees = Path(repo), dict(trees)
        self.kinds = SOURCE_KINDS + tuple(k for k in kinds if k not in SOURCE_KINDS)
        self.comment_kinds = tuple(comment_kinds)
        self._rules: dict[str, dict] = {}
        self.read: set[tuple[str, str]] = set()
        # upstream file -> the (first, last) line spans the checker parsed and verified marker-free
        self.verified: dict[str, list[tuple[int, int]]] = {}
        self._markers: dict[str, int | None] = {}  # upstream file -> its first `Trust:` line, if any

    def tree_of(self, source: str, path: str | None):
        if source == "first-party":
            name, _, rest = (path or "").partition("/")
            key = f"first-party/{name}"
            if key not in self.trees:
                self.trees[key] = first_party_tree(self.repo, name)
            return self.trees[key], rest
        if source == "design":
            return self.trees.get("design") or self.trees.get("worktree"), DESIGN_REL
        if source in ("rustc", "worktree"):
            return self.trees.get("worktree"), path
        return self.trees.get(source), path

    def spans(self, source: str) -> dict:
        """rule id -> (file, first line, text) for Reference rules; paragraph id likewise for FLS."""
        if source not in self._rules:
            tree, spans = self.trees.get(source), {}
            if tree is not None:
                suffix = ".md" if source == "reference" else ".rst"
                files = tree.files("src/", (suffix,))
                tree.prefetch(files)
                for rel in files:
                    lines = tree.lines(rel) or []
                    for i, line in enumerate(lines):
                        found = REFERENCE_RULE.match(line) if source == "reference" else FLS_PARAGRAPH.search(line)
                        if not found:
                            continue
                        j = i + 1
                        while j < len(lines) and not (REFERENCE_RULE.match(lines[j]) if source == "reference" else (FLS_PARAGRAPH.search(lines[j]) or not lines[j].strip())):
                            j += 1
                        body = lines[i + 1:j] if source == "reference" else lines[i:j]
                        spans.setdefault(found.group(1), []).append((rel, i + 1, collapse("\n".join(body))))
            self._rules[source] = spans
        return self._rules[source]

    def upstream_region(self, findings: Findings, rel: str, first: int, last: int, what: str) -> bool:
        """Lines first..last of the upstream file `rel` at HEAD are a region the checker parses
        (an enum whose variants it enumerates, from the end of the item before it). A region
        that carries a `Trust:` marker is refused (PIN), so no marked Trust edit changes what the
        checker reads there; a region free of one is recorded as verified, and a citation inside
        it is exempt from the whole-file guard in `check`. A checker registers its regions
        before it resolves a citation into their files; a citation checked first fails closed."""
        tree = self.trees.get("worktree")
        lines = tree.lines(rel) if tree is not None else None
        if lines is None or not 1 <= first <= last <= len(lines):
            findings.add("PIN", f"{rel}: the parsed region of {what} is not a span of the file at HEAD")
            return False
        marked = [first + i for i, line in enumerate(lines[first - 1:last]) if is_trust_marker(line)]
        if marked:
            findings.add("PIN", f"{rel}: the parsed region of {what} carries a `Trust:` edit (line {marked[0]}), so it is not the pinned upstream text")
            return False
        self.verified.setdefault(rel, []).append((first, last))
        return True

    def check(self, ref: str, quote: object, word: bool = False, strip: bool = False) -> str | None:
        """None when `quote` is at `ref` at the pin; otherwise the reason it is not. With `strip`
        (always for a declared comment kind), a line citation also holds against its lines with
        one leading marker removed."""
        parts = parse_ref(ref, self.kinds)
        if parts is None:
            return f"{ref!r} is not a citation (design:L, <source>:<path>:L[-L], reference:r[ID], fls:fls_ID)"
        if not isinstance(quote, str) or not quote.strip():
            return f"{ref}: the quote is empty"
        source = parts["source"]
        if parts["rule"] or parts["fls"]:
            ident = parts["rule"] or parts["fls"]
            found = self.spans(source).get(ident, [])
            if len(found) != 1:
                return f"{ref}: the {'rule' if parts['rule'] else 'paragraph'} id {ident} is defined {len(found)} times at the pin"
            rel, line, text = found[0]
            self.read.add((source, rel))
            return None if collapse(quote) in text else f"{ref} ({rel}:{line}) does not contain {quote!r}"
        path = parts["path"]
        if path is not None and (path != posixpath.normpath(path) or path.startswith(("/", "./"))
                                 or ".." in path.split("/")):
            return f"{ref}: the path is not written canonically (no ./, .., // or leading /), so one file has one spelling and every guard sees it"
        if source == "rustc" and not parts["path"].startswith(UPSTREAM_PREFIXES):
            return f"{ref}: a rustc citation names a file under {', '.join(UPSTREAM_PREFIXES)}"
        tree, rel = self.tree_of(source, parts["path"])
        lines = tree.lines(rel) if tree is not None and rel else None
        if lines is None:
            return f"{ref}: {rel or parts['path']} does not exist in the {source} tree"
        if parts["end"] > len(lines):
            return f"{ref}: the file has {len(lines)} lines"
        self.read.add((source, rel))
        cited = lines[parts["start"] - 1:parts["end"]]
        if source in ("rustc", "worktree") and rel.startswith(UPSTREAM_PREFIXES):
            if rel not in self._markers:
                self._markers[rel] = next((i for i, line in enumerate(lines, 1) if is_trust_marker(line)), None)
            marker = self._markers[rel]
            inside = any(a <= parts["start"] and parts["end"] <= b for a, b in self.verified.get(rel, ()))
            if marker is not None and not inside:
                return PinProblem(f"{ref}: {rel} carries a `Trust:` edit (line {marker}), and the cited lines lie in no "
                                  f"region the checker parses and verified free of one, so they are not verified upstream text")
        held, strip = False, strip or source in self.comment_kinds
        for lines_ in [cited] + ([[strip_marker(line) for line in cited]] if strip else []):
            if parts["start"] == parts["end"]:
                held = held or (whole_word(quote, lines_[0]) if word else quote in lines_[0])
            else:
                held = held or collapse(quote) in collapse("\n".join(lines_))
        return None if held else f"{ref} does not contain {'the word ' if word else ''}{quote!r}"

    def resolve(self, findings: Findings, kind: str, where: str, ref: str, quote: object, word: bool = False,
                strip: bool = False) -> bool:
        """`check`, with its problem added to `findings` as `kind`, or as PIN for a PinProblem."""
        problem = self.check(ref, quote, word, strip)
        if problem:
            findings.add(getattr(problem, "kind", kind), f"{where}: {problem}")
        return problem is None


def check_prose(findings: Findings, kind: str, where: str, text: str, resolver: Resolver) -> int:
    """Every `REF «quote»` in `text` resolves, and no line citation stands outside that form.
    Returns the number of citations resolved."""
    stripped, count = text, 0
    kinds = getattr(resolver, "kinds", SOURCE_KINDS)
    pattern = PROSE_CITATION if kinds == SOURCE_KINDS else prose_citation_pattern(kinds)
    for match in pattern.finditer(text):
        ref, _, rest = match.group(0).partition(" «")
        resolver.resolve(findings, kind, where, ref, rest[:-1])
        count += 1
        stripped = stripped.replace(match.group(0), " ", 1)
    for match in UNCHECKED_CITATION.finditer(stripped):
        findings.add(kind, f"{where}: line citation {match.group(0)!r} is not in the checked `REF «quote»` form")
    return count


# --------------------------------------------------------------------------
# uniqueness
# --------------------------------------------------------------------------


def canonical(value: object) -> str:
    return json.dumps(value, sort_keys=True, ensure_ascii=False, separators=(",", ":"), default=str)


def repeated_elements(findings: Findings, kind: str, where: str, value: object, path: str = "") -> None:
    """No list, at any depth, repeats an element."""
    if isinstance(value, list):
        seen = set()
        for element in value:
            key = canonical(element)
            if key in seen:
                findings.add(kind, f"{where}: {path or 'a list'} repeats {element!r}")
            seen.add(key)
            repeated_elements(findings, kind, where, element, path)
    elif isinstance(value, dict):
        for name, element in value.items():
            repeated_elements(findings, kind, where, element, f"{path}.{name}" if path else name)


def unique_rows(findings: Findings, kind: str, what: str, rows, key) -> dict:
    """key -> row for the rows of one table; a second row with a key already seen is refused."""
    out = {}
    for index, row in enumerate(rows):
        k = key(row)
        if k in out:
            findings.add(kind, f"{what}[{index}]: duplicate row {k!r}")
        else:
            out[k] = row
    return out


# --------------------------------------------------------------------------
# generated blocks
# --------------------------------------------------------------------------


def block_span(text: str, name: str) -> tuple[int, int] | None:
    """(offset after the begin marker line, offset of the end marker) of block `name`."""
    begin = re.search(r"^<!-- " + re.escape(name) + r":begin\b[^\n]*-->\n", text, re.M)
    end = re.search(r"^<!-- " + re.escape(name) + r":end -->$", text, re.M)
    if begin is None or end is None or end.start() < begin.end():
        return None
    return begin.end(), end.start()


def replace_block(text: str, name: str, body: str) -> str:
    span = block_span(text, name)
    if span is None:
        raise ValueError(f"the {name} markers are missing")
    return text[:span[0]] + body.rstrip("\n") + "\n" + text[span[1]:]


def check_block(findings: Findings, kind: str, text: str, name: str, body: str) -> None:
    span = block_span(text, name)
    if span is None:
        findings.add(kind, f"the `{name}` block markers are missing")
    elif text[span[0]:span[1]].strip() != body.strip():
        findings.add(kind, f"the published `{name}` block differs from its computed rendering (regenerate it)")


# --------------------------------------------------------------------------
# reviewed judgments
# --------------------------------------------------------------------------

SECTION_OPEN = re.compile(r"^<!-- reviewed:([a-z][a-z0-9-]*):([A-Za-z0-9_.:-]+) -->$")
SECTION_CLOSE = re.compile(r"^<!-- /reviewed:([a-z][a-z0-9-]*):([A-Za-z0-9_.:-]+) -->$")
HEADING = re.compile(r"^#{1,6}(?:\s|$)")


def digest(judgment_id: str, content: object) -> str:
    return "sha256:" + hashlib.sha256(canonical({"id": judgment_id, "content": content}).encode("utf-8")).hexdigest()


def document_judgments(findings: Findings, kind: str, text: str, generated: tuple = (),
                       section_kind: str = "prose", outline_id: str = "outline:document") -> dict:
    """The judgments of a document. `SECTION_KIND:ID` is the text between
    `<!-- reviewed:SECTION_KIND:ID -->` and `<!-- /reviewed:SECTION_KIND:ID -->`; `outline_id`
    is the list, in document order, of every heading, every generated-block marker line and
    every section's opening marker outside the sections. A section's content is keyed by its
    id, so the outline is what makes where a section stands a judgment: a section moved under
    another heading (an owner question under Limitations), or two sections exchanged, changes
    it. A section takes only the section kind, so it cannot stand in for another judgment;
    sections do not nest; the body of a generated block is its checker's (check_block); and
    any other line that is not blank and lies in no section is refused, so no text escapes
    review."""
    spans = [s for s in (block_span(text, name) for name in generated) if s]
    out: dict[str, object] = {}
    current, start, offset, outline = None, 0, 0, []
    for number, line in enumerate(text.split("\n"), 1):
        begin, offset = offset, offset + len(line) + 1
        marker = SECTION_OPEN.match(line) or SECTION_CLOSE.match(line)
        jid = f"{marker.group(1)}:{marker.group(2)}" if marker else None
        if marker and marker.group(1) != section_kind:
            findings.add(kind, f"line {number}: section {jid} is not a `{section_kind}:` section, and only those are reviewed prose")
        if marker and marker.re is SECTION_OPEN:
            if current is not None:
                findings.add(kind, f"line {number}: section {jid} opens inside {current}")
            elif jid in out:
                findings.add(kind, f"line {number}: section {jid} appears twice")
            if current is None:
                outline.append(line)
            current, start = jid, offset
        elif marker:
            if jid != current:
                findings.add(kind, f"line {number}: section close {jid} does not match the open section {current}")
            else:
                out[current] = text[start:begin]
            current = None
        elif current is not None or not line.strip() or any(a <= begin < b for a, b in spans):
            continue
        elif HEADING.match(line) or any(offset == a or begin == b for a, b in spans):
            outline.append(line)
        else:
            findings.add(kind, f"line {number} lies in no reviewed section: {line.strip()[:60]!r}")
    if current is not None:
        findings.add(kind, f"section {current} is never closed")
    out[outline_id] = outline
    return out


def toml_comments(text: str) -> list:
    """The comments of a TOML document in order, each [its text after `#`, where it stands, the
    lines that place it]. Basic, literal and multi-line strings are skipped, so a `#` inside a
    string is no comment. A comment after a value stands `after` its line; a comment alone on
    its line `heads` the next line that holds content (a line not blank once its comment is
    removed). The placing lines are the shortest run of content lines from that line on (each
    without its comment, stripped) that occurs exactly once in the document, where a run that
    reaches the end of the document occurs once. Rows that begin with the same line are told
    apart by the lines after it, so a comment moved to head another row or table, or to stand
    after another line, changes the list; a comment that heads nothing places with no lines."""
    spans, i, n = [], 0, len(text)
    while i < n:
        if text.startswith(('"""', "'''"), i):
            quote, j = text[i:i + 3], i + 3
            while j < n and not text.startswith(quote, j):
                j += 2 if quote == '"""' and text[j] == "\\" else 1
            i = j + 3
            for _ in range(2):  # a multi-line string may end with one or two of its quotes
                i += i < n and text[i] == quote[0]
        elif text[i] in "\"'":
            j = i + 1
            while j < n and text[j] not in (text[i], "\n"):
                j += 2 if text[i] == '"' and text[j] == "\\" else 1
            i = j + 1
        elif text[i] == "#":
            j = text.find("\n", i)
            j = n if j < 0 else j
            spans.append((i, j))
            i = j
        else:
            i += 1
    lines = text.split("\n")
    starts = [0]
    for line in lines[:-1]:
        starts.append(starts[-1] + len(line) + 1)
    comment_at = {}  # line index -> column where its comment begins
    for begin, _ in spans:
        index = bisect.bisect_right(starts, begin) - 1
        comment_at[index] = begin - starts[index]
    content, position = [], {}  # the content lines, and line index -> its place among them
    for index, line in enumerate(lines):
        body = line[:comment_at[index]] if index in comment_at else line
        if body.strip():
            position[index] = len(content)
            content.append(body.strip())
    occurrences: dict[str, list[int]] = {}
    for place, body in enumerate(content):
        occurrences.setdefault(body, []).append(place)

    def placing(place: int) -> list[str]:
        if place >= len(content):
            return []
        length, rivals = 1, [q for q in occurrences[content[place]] if q != place]
        while rivals and place + length < len(content):
            rivals = [q for q in rivals if q + length < len(content) and content[q + length] == content[place + length]]
            length += 1
        return content[place:place + length]

    out = []
    for begin, end in spans:
        index = bisect.bisect_right(starts, begin) - 1
        if index in position:
            out.append([text[begin + 1:end], "after", "\n".join(placing(position[index]))])
        else:
            following = next((position[k] for k in range(index + 1, len(lines)) if k in position), len(content))
            out.append([text[begin + 1:end], "heads", "\n".join(placing(following))])
    return out


def merge_judgments(findings: Findings, pairs) -> dict:
    """id -> content for (id, content) pairs. An id produced twice is refused, so no judgment
    (a row, a section) can replace another's content under the other's id."""
    out: dict = {}
    for jid, content in pairs:
        if jid in out:
            findings.add("REVIEW", f"judgment id {jid} is produced twice (two rows with one key, or two sources); each judgment has its own id")
        else:
            out[jid] = content
    return out


def read_registry(text: str) -> dict:
    return tomllib.loads(text)


def check_reviews(findings: Findings, registry_path: Path, deliverable: str, judgments: dict,
                  kinds: set[str], repo: Path | None = None, committed_rel: str | None = None) -> dict:
    """The judgment layer. `judgments` maps every current judgment id to its content; `kinds`
    are the judgment kinds the deliverable declares. With `repo`, the registry is compared
    with every committed version of `committed_rel` (default: the registry's own path in
    `repo`). Returns counts."""
    counts = {"judgments": len(judgments), "records": 0, "reviews": 0, "retired": 0, "history": 0}
    try:
        text = Path(registry_path).read_text(encoding="utf-8")
        data = read_registry(text)
    except (OSError, tomllib.TOMLDecodeError) as error:
        findings.add("REVIEW", f"{registry_path}: {error}")
        return counts
    if toml_comments(text):
        findings.add("REVIEW", f"{registry_path}: carries comments, which no review covers; the registry is data only (its format is common.py's)")
    if set(data) != {"schema", "deliverable", "record", "judgment"} or data.get("schema") != REVIEWS_SCHEMA or data.get("deliverable") != deliverable:
        findings.add("REVIEW", f"{registry_path}: must hold exactly schema = {REVIEWS_SCHEMA!r}, deliverable = {deliverable!r}, [record.*] and [judgment]")
        return counts
    records, entries = data["record"], data["judgment"]
    counts["records"] = len(records)
    for rid, record in records.items():
        where = f"review record {rid}"
        if not isinstance(record, dict) or set(record) != {"round", "date", "evidence", "reason"}:
            findings.add("REVIEW", f"{where}: keys must be exactly round, date, evidence, reason")
            continue
        if not all(isinstance(record[k], str) and record[k].strip() for k in ("round", "reason")) or not DATE.match(str(record["date"])):
            findings.add("REVIEW", f"{where}: needs a non-empty round and reason and a YYYY-MM-DD date")
        elif FREE_TEXT_CITATION.search(record["reason"]):
            findings.add("REVIEW", f"{where}: its reason carries a line citation no predicate checks; cite it in evidence")
        evidence = record["evidence"]
        if not isinstance(evidence, list) or not evidence or not all(isinstance(e, str) and e.strip() for e in evidence):
            findings.add("REVIEW", f"{where}: evidence must list what was read")
        repeated_elements(findings, "REVIEW", where, evidence, "evidence")
    used: set[str] = set()
    for jid, entry in entries.items():
        where = f"judgment {jid}"
        kind = jid.split(":", 1)[0]
        if ":" not in jid or kind not in kinds:
            findings.add("REVIEW", f"{where}: {kind!r} is not a judgment kind this deliverable declares ({sorted(kinds)})")
        if not isinstance(entry, dict) or not set(entry) <= {"digest", "reviews", "retired"} or not {"digest", "reviews"} <= set(entry):
            findings.add("REVIEW", f"{where}: an entry is {{digest, reviews[, retired]}}")
            continue
        reviews = entry["reviews"]
        if not DIGEST.match(str(entry["digest"])) or not isinstance(reviews, list) or not reviews or not all(
                isinstance(r, list) and len(r) == 2 and r[0] in records and DIGEST.match(str(r[1])) for r in reviews):
            findings.add("REVIEW", f"{where}: needs a sha256 digest and reviews [[record, sha256 digest], ..] naming known records")
            continue
        repeated_elements(findings, "REVIEW", where, reviews, "reviews")
        used.update(r[0] for r in reviews)
        counts["reviews"] += len(reviews)
        if "retired" in entry:
            counts["retired"] += 1
            used.add(entry["retired"])
            if entry["retired"] not in records:
                findings.add("REVIEW", f"{where}: retired by unknown record {entry['retired']!r}")
            if jid in judgments:
                findings.add("REVIEW", f"{where}: is retired, but the judgment exists")
            continue
        if jid not in judgments:
            findings.add("REVIEW", f"{where}: is registered, but no such judgment exists (stale); retire it with a review record")
            continue
        actual = digest(jid, judgments[jid])
        if entry["digest"] != actual:
            findings.add("REVIEW", f"{where}: its content changed since it was registered (content {actual}, registered {entry['digest']}); a changed judgment takes its new digest and a review by a new record")
        elif reviews[-1][1] != actual:
            findings.add("REVIEW", f"{where}: its last review record ({reviews[-1][0]}) reviewed {reviews[-1][1]}, not the content {actual}; append a review of the current content by a new record")
    for jid in sorted(set(judgments) - set(entries)):
        findings.add("REVIEW", f"judgment {jid} is not registered in {Path(registry_path).name}; register it with a review record")
    for rid in sorted(set(records) - used):
        findings.add("REVIEW", f"review record {rid} reviews no judgment (stale)")
    if repo is not None:
        counts["history"] = check_registry_history(findings, Path(registry_path), Path(repo), records, entries, committed_rel)
    return counts


def merge_heads(repo: Path) -> list[str]:
    """The commits an unfinished merge is bringing in (each line of MERGE_HEAD), else none."""
    path = (git(repo, "rev-parse", "--path-format=absolute", "--git-path", "MERGE_HEAD") or "").strip()
    try:
        text = Path(path).read_text(encoding="ascii") if path else ""
    except OSError:
        return []
    return [line.strip() for line in text.split("\n") if re.fullmatch(r"[0-9a-f]{40,64}", line.strip())]


def reviews_by_record(entries: dict) -> dict[str, set]:
    """record -> the (judgment, digest) pairs it reviews and the (judgment, "retired") it retires."""
    out: dict[str, set] = {}
    for jid, entry in entries.items():
        if not isinstance(entry, dict):
            continue
        for review in entry.get("reviews") or []:
            if isinstance(review, list) and len(review) == 2:
                out.setdefault(str(review[0]), set()).add((jid, str(review[1])))
        if "retired" in entry:
            out.setdefault(str(entry["retired"]), set()).add((jid, "retired"))
    return out


def check_registry_history(findings: Findings, registry_path: Path, repo: Path, records: dict, entries: dict,
                           committed_rel: str | None = None) -> int:
    """Append-only against every committed version of the registry (the first included): no
    record, judgment entry or review is edited or removed, a retirement is never undone, and a
    record reviews exactly what it reviewed when first committed, so a later change can only
    be reviewed by a new record.

    The order is append-only too, over a history that may merge. Against each committed
    version, a judgment's current reviews by that version's records begin with that version's
    reviews, in order; and a review by a record no version has committed stands after every
    review by a committed record. On one line of history this is exactly "the committed
    reviews are a prefix": a review by a later committed record is ordered against the version
    that committed it. Where two lines each appended a review to one judgment, the merge holds
    both, each line's in its order, which no single prefix can. A record may review only the
    (judgment, digest) pairs the commit that introduced it credits to it: a commit that holds the
    record while no earlier committed version of the registry (no ancestor) does. A later commit,
    HEAD included, never widens that set, so a change credited to a committed record is refused
    before and after it is committed, while a review a committed merge dropped can be restored.
    A record two lines each introduced reviews only what every introducing commit credits.

    During a merge (MERGE_HEAD present) the versions on every merged head are read with HEAD's,
    so a resolution that drops the incoming branch's review is refused before it is committed,
    not only after. The history must be readable whole: a shallow repository
    (`git clone --depth`) hides every commit behind its boundary, as a grafts file or a replace
    ref would substitute one, so it is refused, as are a failed `git log` and a registry that
    is not in the repository."""
    top = (git(repo, "rev-parse", "--show-toplevel") or "").strip()
    if not top:
        findings.add("REVIEW-HISTORY", f"{repo} is not a git repository, so the committed review history cannot be read")
        return 0
    shallow = (git(top, "rev-parse", "--is-shallow-repository") or "").strip()
    common = (git(top, "rev-parse", "--path-format=absolute", "--git-common-dir") or "").strip()
    if shallow != "false" or not common or (Path(common) / "shallow").exists():
        findings.add("REVIEW-HISTORY", f"{top} is a shallow repository (or its shallow state cannot be read): every commit behind its boundary is hidden, so an edited or re-credited committed review record would pass; read the review history from a full clone")
    rel = committed_rel
    if rel is None:
        try:
            rel = registry_path.resolve().relative_to(Path(top).resolve()).as_posix()
        except ValueError:
            findings.add("REVIEW-HISTORY", f"{registry_path} is not in the repository {top}, so its committed versions cannot be read")
            return 0
    now_by_record = reviews_by_record(entries)
    committed_records: set[str] = set()
    # record -> {commit holding it: the (judgment, digest) pairs that version credits to it}
    holders: dict[str, dict[str, set]] = {}
    # A commit-graph file is a cache git trusts for parents; a forged one hides history the way a
    # grafts file does, so history is read from the commit objects themselves.
    log = git(top, "-c", "core.commitGraph=false", "log", "--full-history", "--format=%H", "HEAD", *merge_heads(top), "--", rel)
    if log is None:
        findings.add("REVIEW-HISTORY", f"the committed versions of {rel} cannot be listed (git log failed)")
        return 0
    versions = 0
    for sha in log.split():
        blob = git(top, "show", f"{sha}:{rel}")
        if blob is None:
            # `git log -- rel` listed this commit as touching rel. If rel is absent there it was
            # deleted; if the tree cannot be read (a partial clone offline) the version is hidden.
            if git(top, "-c", "core.commitGraph=false", "cat-file", "-e", f"{sha}^{{tree}}") is None or \
                    (git(top, "ls-tree", sha, "--", rel) or "").strip():
                findings.add("REVIEW-HISTORY", f"{rel} at {sha[:10]} cannot be read (a partial or damaged clone), so its committed review records cannot be compared")
            continue
        try:
            old = read_registry(blob)
        except tomllib.TOMLDecodeError:
            findings.add("REVIEW-HISTORY", f"{rel} at {sha[:10]} does not parse")
            continue
        versions += 1
        old_entries = old.get("judgment") or {}
        old_by_record = reviews_by_record(old_entries)
        old_records = old.get("record") or {}
        committed_records.update(old_records)
        for rid, record in old_records.items():
            if records.get(rid) != record:
                findings.add("REVIEW-HISTORY", f"review record {rid} was committed in {sha[:10]} and is now edited or removed; records are append-only")
            holders.setdefault(rid, {})[sha] = old_by_record.get(rid, set())
        for jid, entry in old_entries.items():
            now = entries.get(jid)
            if not isinstance(now, dict) or not isinstance(entry, dict):
                findings.add("REVIEW-HISTORY", f"judgment {jid} was registered in {sha[:10]} and is now removed; retire it instead")
                continue
            before = entry.get("reviews") or []
            kept = [r for r in now.get("reviews") or [] if isinstance(r, list) and r and isinstance(r[0], str) and r[0] in old_records]
            if kept[:len(before)] != before:
                findings.add("REVIEW-HISTORY", f"judgment {jid}: its review records committed in {sha[:10]} are edited, removed or reordered; reviews are append-only")
            if "retired" in entry and now.get("retired") != entry["retired"]:
                findings.add("REVIEW-HISTORY", f"judgment {jid}: its retirement committed in {sha[:10]} is undone or edited")
    # Each committed version's ancestors that touch the registry: a version introduces a record
    # when none of them holds it. Every ancestor that touches the registry is itself in `log`
    # (an ancestor of HEAD or of a merged head), so `holders` sees every version that could.
    ancestors: dict[str, set] = {}

    def ancestor_versions(sha: str) -> set | None:
        if sha not in ancestors:
            # The parents are named explicitly: `git log` given no revision reads HEAD, so a root
            # commit's empty `sha^@` would silently list HEAD's history instead of nothing.
            line = git(top, "-c", "core.commitGraph=false", "rev-list", "--parents", "-n", "1", sha)
            parents = None if line is None else line.split()[1:]
            listed = "" if parents == [] else None if parents is None else \
                git(top, "-c", "core.commitGraph=false", "log", "--full-history", "--format=%H", *parents, "--", rel)
            ancestors[sha] = None if listed is None else set(listed.split())
        return ancestors[sha]

    for rid in sorted(holders):
        held = holders[rid]
        introducing = []
        for sha in held:
            before = ancestor_versions(sha)
            if before is None:
                findings.add("REVIEW-HISTORY", f"the committed versions of {rel} before {sha[:10]} cannot be listed (git log failed), so the commit that introduced review record {rid} cannot be found")
                continue
            if not before & held.keys():
                introducing.append(sha)
        if not introducing:
            continue
        introducing.sort()
        # A record two lines each introduced reviews only what both credit it with.
        credited = set.intersection(*(held[sha] for sha in introducing))
        added = sorted(now_by_record.get(rid, set()) - credited)
        if added:
            findings.add("REVIEW-HISTORY", f"review record {rid} was committed in {introducing[0][:10]} and now also reviews {[j for j, _ in added][:4]}; a change is reviewed by a new record, never credited to a committed one")
    for jid, entry in entries.items():
        reviews = [r for r in (entry.get("reviews") or []) if isinstance(r, list) and r and isinstance(r[0], str)] if isinstance(entry, dict) else []
        # The index of the last review by a committed record; with none, no review stands before one.
        last_committed = max((i for i, r in enumerate(reviews) if r[0] in committed_records), default=0)
        early = sorted({str(r[0]) for r in reviews[:last_committed] if r[0] not in committed_records})
        if early:
            findings.add("REVIEW-HISTORY", f"judgment {jid}: the review by {early} stands before a committed review, but no version committed its record; a new review is appended after every committed one")
    return versions


# --------------------------------------------------------------------------
# immutable files
# --------------------------------------------------------------------------


def check_immutable(findings: Findings, kind: str, repo: Path, rels, sha256: dict | None = None) -> int:
    """Each file equals its first committed version and, when pinned, its sha256. Returns the
    number of files compared with a committed version."""
    compared = 0
    for rel in rels:
        path = Path(repo) / rel
        try:
            data = path.read_bytes()
        except OSError:
            findings.add(kind, f"{rel} does not exist")
            continue
        pin = (sha256 or {}).get(rel)
        if pin is not None and hashlib.sha256(data).hexdigest() != pin:
            findings.add(kind, f"{rel} does not match its sha256 pin {pin}")
        for sha in (git(repo, "log", "--full-history", "--reverse", "--format=%H", "--", rel) or "").split():
            first = git(repo, "show", f"{sha}:{rel}", binary=True)
            if first is None:
                continue
            compared += 1
            if first != data:
                findings.add(kind, f"{rel} differs from its first committed version ({sha[:10]}); a snapshot is never edited, a new retrieval is a new file")
            break
    return compared
