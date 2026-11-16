#!/usr/bin/env python3
"""check_audited_trust_spec_sources.py — the TCB ALLOWLIST DRIFT GATE.

`AUDITED_TRUST_SPEC_SOURCES` in
`src/tools/targo/crates/targo-core/src/compiler/mod.rs` is the allowlist of contract
proc-macro providers that verified Targo will admit. Those crates are compiled
into the verified compiler's address space, so the allowlist does not name them
by crate name -- a name is not authority -- it pins the exact BYTES of each
provider's manifest and library source by sha256. Before a verified build
compiles such a provider, Targo re-hashes both files and refuses the build when
either digest disagrees with the pin.

That refusal is the right behaviour and it is also a TRIPWIRE WITH NOBODY
WATCHING IT: nothing in the tree compared the allowlist to the tree, so the only
way to learn that a pin had gone stale was to run a verified build and read

    Trust spec provider `trust-spec@0.1.1` does not match its audited source
    identity (manifest_sha256=..., lib_sha256=...)

MEASURED 2026-09-11: `crates/trust-spec/src/lib.rs` was pinned at
892427b1... (the digest of its initial commit) while the file had hashed
853603e0... since 2026-08-26/27, when `42afd77700` added `decreases` and
`08877adcb0` made `invariant` refuse instead of erase. Every verified build that
compiled `trust-spec` -- fleet-wide, on main, on seal/15 and on seal/16 -- had
been refused for two weeks, and no lane said so. The stale pin was found by
hand, which is exactly the failure mode this gate removes.

WHAT THIS CHECKS
    For every entry of `AUDITED_TRUST_SPEC_SOURCES`, this gate finds the
    provider in THIS checkout by package name, re-computes sha256 over the exact
    bytes of its manifest and its library source, and requires both to equal the
    pin. When the entry pins a literal `version`, the provider's manifest must
    declare that version literally -- an entry keyed on a version the manifest
    inherits (`version.workspace = true`) can never be reached by the lookup and
    is dead pin, not protection.

WHAT THIS DELIBERATELY DOES NOT DO
    It does not judge whether a moved digest is SAFE to admit. That is an audit:
    a human reads the diff and states, in the allowlist comment beside the pin,
    what capability the new bytes gain or lose. A gate that could decide it
    would be a gate that decides what enters the TCB. This one only guarantees
    that the question gets ASKED -- loudly, in seconds, before a two-hour seal
    build discovers it.

    It also does not fail when a provider is not present in this checkout AND
    the provider's HOME is an uninitialized submodule: a provider that is not
    here cannot have drifted here, and a fresh worktree must not read as a TCB
    violation. That case is reported as UNRESOLVED with the reason.

    THE EXCUSE IS KEYED TO THE PROVIDER'S HOME. It was not, and that was a hole
    (found in review, 2026-09-11, before this lane ever ran in anger): ANY
    uninitialized submodule anywhere excused ANY provider that could not be
    found -- including one whose home is the superproject itself. Measured on a
    fresh worktree with `crates/trust-spec` moved away: `0 provider(s) at their
    audited bytes, 2 unresolved`, printed GREEN, rc=0. A gate that checked
    nothing reported a pass. Two rules now stand between that and a green:

      * a provider whose manifest the SUPERPROJECT tracks (asked of git, so the
        answer survives the file being absent) is never excused by a submodule;
        it is MISSING, and MISSING is red.
      * a run that resolved ZERO providers exits 2, not 0. It compared no bytes,
        so it has established nothing -- the same rule as a zero-entry
        allowlist, one step later.

    `--require-all` raises the bar the rest of the way: every UNRESOLVED becomes
    a failure. That is the RELEASE bar (`release.audited-trust-spec-sources-
    complete`), where every submodule is populated anyway; the `fast`/`push` rows
    stay advisory about a submodule a working tree has not furnished, and are
    fail-closed about everything else.

    scripts/check_audited_trust_spec_sources.py               # the gate
    scripts/check_audited_trust_spec_sources.py --print       # + pinned vs in-tree
    scripts/check_audited_trust_spec_sources.py --require-all # every pin, or red
    scripts/check_audited_trust_spec_sources.py --selftest    # mutation-proof it

    `--print` is the gate plus the digests: it returns the SAME verdict code the
    default mode would, because a mode that returned 0 on a drifted tree would
    be a second, softer answer to the only question this script asks.

Exit 0 = every entry matches the tree. 1 = drift, a pin guarding nothing, or a
provider missing from its home. 2 = the gate could not ask its question
(allowlist unreadable, it parsed to zero entries, or it resolved zero providers
-- an empty extraction is a BROKEN GATE, never a pass).

Author: Andrew Yates | Copyright 2026 Andrew Yates | License: Apache-2.0 OR MIT
"""

from __future__ import annotations

import argparse
import hashlib
import os
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

ALLOWLIST_REL = "src/tools/targo/crates/targo-core/src/compiler/mod.rs"
CONST_NAME = "AUDITED_TRUST_SPEC_SOURCES"

# Where a provider may live. `vendor/` is excluded on purpose: a vendored copy is
# not what a path/submodule provider resolves to, and walking it costs seconds.
SEARCH_ROOTS = (
    "crates",
    "first-party",
    "src/tools",
    "compiler",
    "library",
    "targo-trust",
    "tools",
)
SKIP_DIRS = {".git", "target", "build", "vendor", "node_modules"}


class GateError(Exception):
    """The gate cannot ask its question. Exit 2, never a pass."""


# ---------------------------------------------------------------------------
# Parsing the allowlist
# ---------------------------------------------------------------------------
OPENER_RE = re.compile(r"AuditedTrustSpecSource\s*\{")
FIELD_STR_RE = r'{name}\s*:\s*"(?P<val>[^"]*)"'


def _balanced_body(text: str, open_brace: int) -> str:
    """The body between `text[open_brace]` == `{` and its MATCHING `}`."""
    depth = 0
    for index in range(open_brace, len(text)):
        char = text[index]
        if char == "{":
            depth += 1
        elif char == "}":
            depth -= 1
            if depth == 0:
                return text[open_brace + 1 : index]
    raise GateError(
        f"an `{CONST_NAME}` entry is not brace-balanced -- the gate cannot read "
        "where it ends, and a gate that reads half an entry is not a gate that "
        "passed."
    )


def entry_bodies(block: str) -> list[str]:
    """Each `AuditedTrustSpecSource { .. }` body, BRACE-BALANCED.

    Not a non-greedy regex stopping at the first close brace: that ends the
    body at the FIRST `}` it meets, and these bodies are audit prose that keeps
    growing. The day an audit comment quotes a
    `HashMap<K, V> { .. }`, a `#[cfg(..)] fn f() { .. }` or a diagnostic holding
    a brace, a non-greedy scan truncates the entry -- dropping the very fields
    (`package`, `manifest_sha256`, `lib_sha256`) that the pin IS. Balance
    instead, exactly the way `parse_allowlist` balances the outer `&[ .. ]`.
    """
    return [_balanced_body(block, opener.end() - 1) for opener in OPENER_RE.finditer(block)]


def _field(body: str, name: str) -> str | None:
    match = re.search(FIELD_STR_RE.format(name=name), body)
    return match.group("val") if match else None


def parse_allowlist(source: str) -> list[dict[str, str | None]]:
    """Extract the allowlist entries, or raise. An empty result is an error."""
    anchor = re.search(
        rf"const\s+{CONST_NAME}\s*:\s*&\[AuditedTrustSpecSource\]\s*=\s*&\[",
        source,
    )
    if anchor is None:
        raise GateError(
            f"`{CONST_NAME}` is not declared in {ALLOWLIST_REL} in the shape this "
            "gate reads. It was renamed, reshaped, or removed -- and a gate that "
            "cannot find the allowlist is not a gate that passed."
        )
    # Balance brackets from the opening `&[` so a later `];` in the file cannot
    # truncate or extend the block.
    start = anchor.end() - 1
    depth = 0
    end = None
    for index in range(start, len(source)):
        char = source[index]
        if char == "[":
            depth += 1
        elif char == "]":
            depth -= 1
            if depth == 0:
                end = index
                break
    if end is None:
        raise GateError(f"`{CONST_NAME}` in {ALLOWLIST_REL} is not bracket-balanced")
    block = source[start : end + 1]

    # ASSERT THE EXTRACTION. A regex that silently matches fewer entries than the
    # block contains reports GREEN about pins it never read.
    declared = len(OPENER_RE.findall(block))
    entries: list[dict[str, str | None]] = []
    for body in entry_bodies(block):
        package = _field(body, "package")
        manifest_sha256 = _field(body, "manifest_sha256")
        lib_sha256 = _field(body, "lib_sha256")
        version_match = re.search(r'version\s*:\s*(None|Some\(\s*"([^"]*)"\s*\))', body)
        if package is None or manifest_sha256 is None or lib_sha256 is None:
            raise GateError(
                f"an `{CONST_NAME}` entry is missing package/manifest_sha256/"
                f"lib_sha256: {body.strip()[:200]}"
            )
        if version_match is None:
            raise GateError(
                f"the `{CONST_NAME}` entry for `{package}` has no readable "
                "`version` field (expected `None` or `Some(\"x.y.z\")`)"
            )
        entries.append(
            {
                "package": package,
                "version": version_match.group(2),
                "manifest_sha256": manifest_sha256,
                "lib_sha256": lib_sha256,
            }
        )
    if len(entries) != declared:
        raise GateError(
            f"read {len(entries)} of {declared} `{CONST_NAME}` entries -- the "
            "allowlist changed shape and this gate would have judged a subset"
        )
    if not entries:
        raise GateError(
            f"`{CONST_NAME}` parsed to ZERO entries. An empty failure-list "
            "extraction is a broken gate, not a pass."
        )
    return entries


# ---------------------------------------------------------------------------
# Finding the provider in this checkout
# ---------------------------------------------------------------------------
PKG_NAME_RE = re.compile(r'^\s*name\s*=\s*"([^"]+)"', re.MULTILINE)


def manifest_package_name(text: str) -> str | None:
    """The `[package] name`, read without a TOML parser (manifests are simple)."""
    section = None
    for line in text.splitlines():
        stripped = line.strip()
        if stripped.startswith("[") and stripped.endswith("]"):
            section = stripped[1:-1].strip()
            continue
        if section == "package":
            match = PKG_NAME_RE.match(line)
            if match:
                return match.group(1)
    return None


def manifest_literal_version(text: str) -> str | None:
    """The `[package] version = "x"` when declared literally, else None."""
    section = None
    for line in text.splitlines():
        stripped = line.strip()
        if stripped.startswith("[") and stripped.endswith("]"):
            section = stripped[1:-1].strip()
            continue
        if section == "package":
            match = re.match(r'^\s*version\s*=\s*"([^"]+)"', line)
            if match:
                return match.group(1)
    return None


def manifest_lib_path(text: str) -> str:
    """`[lib] path`, defaulting to the cargo default."""
    section = None
    for line in text.splitlines():
        stripped = line.strip()
        if stripped.startswith("[") and stripped.endswith("]"):
            section = stripped[1:-1].strip()
            continue
        if section == "lib":
            match = re.match(r'^\s*path\s*=\s*"([^"]+)"', line)
            if match:
                return match.group(1)
    return "src/lib.rs"


def find_manifest_index(root: Path) -> dict[str, list[Path]]:
    """Index every named provider in one traversal of the same SEARCH_ROOTS."""
    found: dict[str, list[Path]] = {}
    for rel in SEARCH_ROOTS:
        base = root / rel
        if not base.is_dir():
            continue
        for dirpath, dirnames, filenames in os.walk(base):
            # Prune rather than filter: a build directory is thousands of files.
            dirnames[:] = [d for d in dirnames if d not in SKIP_DIRS]
            if "Cargo.toml" not in filenames:
                continue
            manifest = Path(dirpath) / "Cargo.toml"
            try:
                text = manifest.read_text(encoding="utf-8", errors="replace")
            except OSError:
                continue
            package = manifest_package_name(text)
            if package is not None:
                found.setdefault(package, []).append(manifest)
    return {package: sorted(manifests) for package, manifests in found.items()}


def uninitialized_submodules(root: Path) -> list[str]:
    """Submodule paths declared by .gitmodules that are absent or empty here."""
    gitmodules = root / ".gitmodules"
    if not gitmodules.is_file():
        return []
    absent: list[str] = []
    for match in re.finditer(
        r"^\s*path\s*=\s*(.+?)\s*$",
        gitmodules.read_text(encoding="utf-8", errors="replace"),
        re.MULTILINE,
    ):
        rel = match.group(1)
        path = root / rel
        if not path.is_dir() or not any(path.iterdir()):
            absent.append(rel)
    return absent


def _git(root: Path, *args: str) -> str | None:
    """`git -C root ...` stdout, or None when git cannot answer."""
    try:
        result = subprocess.run(
            ["git", "-C", str(root), *args],
            capture_output=True,
            text=True,
            timeout=120,
        )
    except (OSError, subprocess.SubprocessError):
        return None
    if result.returncode != 0:
        return None
    return result.stdout


def superproject_manifest_homes(root: Path) -> dict[str, list[str]] | None:
    """package name -> the SUPERPROJECT-tracked Cargo.toml paths declaring it.

    GIT is asked, not the filesystem, because the question this answers is
    "where does this provider LIVE", and that must stay answerable when the
    provider's files are not on disk. A submodule contributes only its gitlink
    PATH to `git ls-files`, never its contents, so a package in this table has
    its home in the superproject itself and no uninitialized submodule can
    account for its absence.

    `None` means git could not answer at all (not a repository, no git binary);
    the caller then falls back to the unkeyed excuse and SAYS SO in its output.
    """
    listing = _git(root, "ls-files", "-z", "--", "*Cargo.toml", "Cargo.toml")
    if listing is None:
        return None
    homes: dict[str, list[str]] = {}
    for rel in listing.split("\0"):
        if not rel or any(part in SKIP_DIRS for part in Path(rel).parts):
            continue
        path = root / rel
        if path.is_file():
            text = path.read_text(encoding="utf-8", errors="replace")
        else:
            # Tracked but not on disk -- exactly the case that matters.
            text = _git(root, "show", f":{rel}") or _git(root, "show", f"HEAD:{rel}")
        if text is None:
            continue
        name = manifest_package_name(text)
        if name:
            homes.setdefault(name, []).append(rel)
    return homes


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1 << 20), b""):
            digest.update(chunk)
    return digest.hexdigest()


# ---------------------------------------------------------------------------
# The gate
# ---------------------------------------------------------------------------
def run_check(root: Path, printing: bool = False, require_all: bool = False) -> int:
    allowlist = root / ALLOWLIST_REL
    if not allowlist.is_file():
        raise GateError(f"no allowlist at {allowlist}")
    entries = parse_allowlist(allowlist.read_text(encoding="utf-8", errors="replace"))
    manifests_by_package = find_manifest_index(root)

    failed = 0
    unresolved = 0
    pinned = 0
    absent_submodules = uninitialized_submodules(root)
    # Computed on the FIRST provider that is not on disk, and only then: it costs
    # a `git ls-files` plus one read per tracked manifest, and the overwhelmingly
    # common run resolves every provider.
    homes: dict[str, list[str]] | None = None
    homes_asked = False

    print(f"=== audited trust-spec sources ({ALLOWLIST_REL}) ===")
    for entry in entries:
        package = entry["package"]
        manifests = manifests_by_package.get(package, [])
        if not manifests:
            if not homes_asked:
                homes = superproject_manifest_homes(root)
                homes_asked = True
            # THE EXCUSE IS KEYED TO THE PROVIDER'S HOME, not to the mere
            # existence of an uninitialized submodule anywhere in the tree. A
            # provider whose manifest the SUPERPROJECT tracks lives here; its
            # absence is this tree's problem and no submodule accounts for it.
            home_in_superproject = None if homes is None else (package in homes)
            if home_in_superproject:
                print(f"  MISSING     {package}")
                for rel in homes[package][:4]:
                    print(f"              the superproject tracks {rel}, and it is not on disk here.")
                print(
                    "              This provider's home is the superproject "
                    "itself, so an uninitialized"
                )
                print(
                    "              submodule does not excuse it. Restore the "
                    "provider, or remove the entry."
                )
                failed = 1
                continue
            if absent_submodules:
                print(f"  UNRESOLVED  {package}")
                print(
                    "              not in this checkout, and "
                    f"{len(absent_submodules)} submodule(s) are uninitialized "
                    f"({', '.join(absent_submodules[:4])}). A provider that is not"
                )
                print(
                    "              here cannot have drifted here. Populate the "
                    "submodule to have this pin checked."
                )
                if home_in_superproject is None:
                    print(
                        "              (git could not say where this provider "
                        "lives, so this excuse is NOT keyed to a path.)"
                    )
                if require_all:
                    print(
                        "              --require-all: an unresolved pin is a "
                        "pin this run did not check."
                    )
                    failed = 1
                unresolved += 1
                continue
            print(f"  MISSING     {package}")
            print(
                "              every submodule is populated and no manifest in "
                "this tree declares this package."
            )
            print(
                "              This pin guards nothing: remove the entry, or "
                "restore the provider."
            )
            failed = 1
            continue
        if len(manifests) > 1:
            print(f"  AMBIGUOUS   {package}")
            for manifest in manifests:
                print(f"              {manifest.relative_to(root)}")
            print(
                "              two crates in one tree claim this package name, so "
                "one pin cannot say which bytes are admitted."
            )
            failed = 1
            continue

        manifest = manifests[0]
        text = manifest.read_text(encoding="utf-8", errors="replace")
        lib = manifest.parent / manifest_lib_path(text)
        rel_manifest = manifest.relative_to(root)
        if not lib.is_file():
            print(f"  MISSING     {package}: no library source at {lib.relative_to(root)}")
            failed = 1
            continue
        rel_lib = lib.relative_to(root)

        actual_manifest = sha256_file(manifest)
        actual_lib = sha256_file(lib)

        if printing:
            print(f"  {package}")
            print(f"    manifest {rel_manifest}")
            print(f"      pinned  {entry['manifest_sha256']}")
            print(f"      in-tree {actual_manifest}")
            print(f"    lib      {rel_lib}")
            print(f"      pinned  {entry['lib_sha256']}")
            print(f"      in-tree {actual_lib}")
            # NO `continue`: `--print` still COMPARES and still reaches the
            # verdict below. It used to return 0 unconditionally, so a human who
            # ran it as a quick check on a drifted tree got a green-looking
            # listing and rc=0 -- on exactly the tree state this gate exists to
            # catch. `--print` adds the digests to the report; it does not
            # subtract the judgement.

        drifted = []
        if actual_manifest != entry["manifest_sha256"]:
            drifted.append(("manifest_sha256", rel_manifest, entry["manifest_sha256"], actual_manifest))
        if actual_lib != entry["lib_sha256"]:
            drifted.append(("lib_sha256", rel_lib, entry["lib_sha256"], actual_lib))

        version_problem = None
        if entry["version"] is not None:
            literal = manifest_literal_version(text)
            if literal is None:
                version_problem = (
                    f"the entry keys on version {entry['version']!r}, but "
                    f"{rel_manifest} does not declare a literal version (it "
                    "inherits one), so the lookup can never match it"
                )
            elif literal != entry["version"]:
                version_problem = (
                    f"the entry keys on version {entry['version']!r}, but "
                    f"{rel_manifest} declares {literal!r}"
                )

        if not drifted and version_problem is None:
            print(f"  PINNED      {package}  {rel_manifest}")
            pinned += 1
            continue

        failed = 1
        print(f"  DRIFTED     {package}  {rel_manifest}")
        for field, rel, expected, actual in drifted:
            print(f"              {field}  ({rel})")
            print(f"                pinned   {expected}")
            print(f"                in-tree  {actual}")
        if version_problem is not None:
            print(f"              version   {version_problem}")
        print(
            "              These bytes are compiled INTO the verified compiler's "
            "address space. Do not"
        )
        print(
            "              move a pin to make this green: read the diff first and "
            "say, in the comment"
        )
        print(
            "              beside the entry, what capability the new bytes gain "
            "or lose."
        )
        for field, rel, _expected, actual in drifted:
            print(f"              Fix (after auditing {rel}), in {ALLOWLIST_REL}:")
            print(f'                  {field}: "{actual}",')
        if version_problem is not None:
            print(f"              Fix: reconcile `version` in {ALLOWLIST_REL} with {rel_manifest}.")

    print()
    if failed:
        print(
            "AUDITED TRUST-SPEC SOURCES: RED -- the allowlist and the tree "
            "disagree, so every verified"
        )
        print(
            "build that compiles this provider is refused until an audit moves "
            "the pin."
        )
        return 1
    if pinned == 0:
        # The same rule `parse_allowlist` applies to a zero-entry allowlist, one
        # step later: a run that compared NO bytes has not established anything,
        # so it must not read as a pass. This is the rule that makes the excuse
        # above safe to have at all.
        raise GateError(
            f"the gate resolved NO providers ({len(entries)} entr(ies) pinned, "
            f"{unresolved} unresolved): it compared zero bytes, so there is "
            "nothing for it to report green about. An empty extraction is a "
            "BROKEN GATE, never a pass -- populate the submodules that hold "
            "these providers, or fix the allowlist."
        )
    print(
        f"AUDITED TRUST-SPEC SOURCES: GREEN -- {pinned} provider(s) at their "
        f"audited bytes, {unresolved} unresolved."
    )
    return 0


# ---------------------------------------------------------------------------
# --selftest: the mutation proof
# ---------------------------------------------------------------------------
SCRATCH_ALLOWLIST_HEAD = """\
struct AuditedTrustSpecSource {
    package: &'static str,
    version: Option<&'static str>,
    manifest_sha256: &'static str,
    lib_sha256: &'static str,
}

const AUDITED_TRUST_SPEC_SOURCES: &[AuditedTrustSpecSource] = &[
"""

SCRATCH_ENTRY = """\
    AuditedTrustSpecSource {{
        package: "{package}",
        // a bracket in a comment [ ] must not confuse the block scan
{comment}\
        version: {version},
        manifest_sha256: "{manifest}",
        lib_sha256: "{lib}",
    }},
"""

SCRATCH_ALLOWLIST_TAIL = "];\n"

# An audit comment that BALANCES a brace. A non-greedy `.*?` body scan ends the
# entry here and never reads `manifest_sha256`/`lib_sha256`.
BRACE_COMMENT = """\
        // Audit note: the macro expands to `impl Trait for T { fn f() {} }`,
        // and a `HashMap<K, V> { .. }` in a quoted diagnostic must not end this
        // entry. Everything below this line is still part of the pin.
"""

# Digests for a provider that is NOT in this checkout at all. They are never
# compared -- the point of the fixture is WHETHER the gate lets that pass.
ABSENT_DIGEST = "0" * 64

SCRATCH_MANIFEST = """\
[package]
name = "{package}"
version = "0.1.1"
edition = "2021"

[lib]
name = "trust"
proc-macro = true
"""

SCRATCH_LIB = """\
#![forbid(unsafe_code)]

use proc_macro::TokenStream;

#[proc_macro_attribute]
pub fn requires(_attr: TokenStream, item: TokenStream) -> TokenStream {
    item
}
"""


def _write(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")


def _git_track(root: Path) -> bool:
    """Make `root` a git repo and stage everything in it.

    The gate asks GIT where a provider lives, so the fixtures that exercise that
    question must be tracked. Only `init` + `add` are run (no commit, no config
    writes): `superproject_manifest_homes` reads the INDEX first.
    """
    if shutil.which("git") is None:
        return False
    for args in (["init", "-q"], ["add", "-A"]):
        result = subprocess.run(
            ["git", "-C", str(root), *args], capture_output=True, text=True
        )
        if result.returncode != 0:
            return False
    return True


def _seed_scratch(
    root: Path,
    *,
    version: str = "0.1.1",
    local_provider: bool = True,
    submodule_provider: bool = False,
    brace_in_comment: bool = False,
) -> bool:
    """Seed a scratch superproject and return whether git could track it.

    `local_provider` -- `crates/scratch-spec`, whose HOME is the superproject.
    `submodule_provider` -- an entry for `sub-spec`, whose home is the declared
    submodule `first-party/sub`, which is left present-but-EMPTY (uninitialized).
    Its files are never written, so it is unresolvable by construction.
    """
    entries = ""
    if local_provider:
        manifest = root / "crates/scratch-spec/Cargo.toml"
        lib = root / "crates/scratch-spec/src/lib.rs"
        _write(manifest, SCRATCH_MANIFEST.format(package="scratch-spec"))
        _write(lib, SCRATCH_LIB)
        entries += SCRATCH_ENTRY.format(
            package="scratch-spec",
            comment=BRACE_COMMENT if brace_in_comment else "",
            version=f'Some("{version}")',
            manifest=sha256_file(manifest),
            lib=sha256_file(lib),
        )
    if submodule_provider:
        entries += SCRATCH_ENTRY.format(
            package="sub-spec",
            comment="",
            version="None",
            manifest=ABSENT_DIGEST,
            lib=ABSENT_DIGEST,
        )
        _write(
            root / ".gitmodules",
            '[submodule "first-party/sub"]\n'
            "\tpath = first-party/sub\n"
            "\turl = https://example.invalid/sub.git\n",
        )
        (root / "first-party/sub").mkdir(parents=True, exist_ok=True)
    _write(root / ALLOWLIST_REL, SCRATCH_ALLOWLIST_HEAD + entries + SCRATCH_ALLOWLIST_TAIL)
    return _git_track(root)


def selftest() -> int:
    me = Path(__file__).resolve()
    tmp = Path(tempfile.mkdtemp(prefix="audited-spec-selftest-"))
    passed = failed = 0
    print("=== audited-trust-spec-sources selftest ===")

    def expect(want: int, label: str, root: Path, *extra: str, wanted: str | None = None):
        """Run the gate on `root` and assert its exit code (and, optionally,
        that a given string is in its output -- a code alone cannot tell a
        verdict from a verdict reached for the wrong reason)."""
        nonlocal passed, failed
        result = subprocess.run(
            [sys.executable, str(me), "--selftest-run", str(root), *extra],
            capture_output=True,
            text=True,
        )
        out = result.stdout + result.stderr
        ok = result.returncode == want and (wanted is None or wanted in out)
        if ok:
            passed += 1
            print(f"  PASS  {label} (rc={result.returncode})")
        else:
            failed += 1
            print(f"  FAIL  {label} (want rc={want}, got rc={result.returncode})")
            if wanted is not None and wanted not in out:
                print(f"        output does not contain {wanted!r}")
            for line in out.strip().splitlines():
                print(f"        {line}")
        return result

    try:
        root = tmp / "pristine"
        _seed_scratch(root)
        expect(0, "pristine tree is GREEN", root)

        # One discovery must retain every package and every duplicate across
        # search roots, even when an earlier allowlist entry already matches.
        root = tmp / "indexed-providers"
        _seed_scratch(root)
        manifest = root / "tools/second-spec/Cargo.toml"
        lib = manifest.parent / "src/lib.rs"
        _write(manifest, SCRATCH_MANIFEST.format(package="second-spec"))
        _write(lib, SCRATCH_LIB)
        entry = SCRATCH_ENTRY.format(
            package="second-spec", comment="", version='Some("0.1.1")',
            manifest=sha256_file(manifest), lib=sha256_file(lib),
        )
        allowlist = root / ALLOWLIST_REL
        allowlist.write_text(
            allowlist.read_text(encoding="utf-8").replace(
                SCRATCH_ALLOWLIST_TAIL, entry + SCRATCH_ALLOWLIST_TAIL
            ), encoding="utf-8",
        )
        expect(0, "both indexed providers are compared", root, wanted="2 provider(s)")
        duplicate = root / "first-party/shadow/second-spec"
        _write(duplicate / "Cargo.toml", manifest.read_text(encoding="utf-8"))
        _write(duplicate / "src/lib.rs", SCRATCH_LIB)
        expect(1, "a later indexed provider's duplicate stays RED", root, wanted="AMBIGUOUS")

        # 1. the defect this gate was written for: the library source moved.
        root = tmp / "lib-moved"
        _seed_scratch(root)
        lib = root / "crates/scratch-spec/src/lib.rs"
        lib.write_text(SCRATCH_LIB + "\n// one more line\n", encoding="utf-8")
        result = subprocess.run(
            [sys.executable, str(me), "--selftest-run", str(root)],
            capture_output=True,
            text=True,
        )
        out = result.stdout + result.stderr
        want_actual = sha256_file(lib)
        if (
            result.returncode == 1
            and "DRIFTED" in out
            and want_actual in out
            and 'lib_sha256: "' in out
        ):
            passed += 1
            print("  PASS  moved lib.rs -> RED, and the output names both digests and the fix")
        else:
            failed += 1
            print(f"  FAIL  moved lib.rs (rc={result.returncode})")
            for line in out.strip().splitlines():
                print(f"        {line}")

        # 2. the manifest moved.
        root = tmp / "manifest-moved"
        _seed_scratch(root)
        manifest = root / "crates/scratch-spec/Cargo.toml"
        manifest.write_text(
            SCRATCH_MANIFEST.format(package="scratch-spec") + '\n[dependencies]\nsyn = "2"\n',
            encoding="utf-8",
        )
        expect(1, "moved Cargo.toml -> RED", root)

        # 3. a pinned literal version the manifest does not declare.
        root = tmp / "version-skew"
        _seed_scratch(root, version="0.9.9")
        expect(1, "entry keys on a version the manifest does not declare -> RED", root)

        # 4. an entry whose package is nowhere, with every submodule populated.
        root = tmp / "provider-gone"
        _seed_scratch(root)
        shutil.rmtree(root / "crates/scratch-spec")
        expect(1, "pin guarding a provider that is not in the tree -> RED", root)

        # 5. THE EXCUSE IS KEYED TO THE PROVIDER'S HOME. An uninitialized
        #    submodule excuses a provider that lives IN a submodule -- it does
        #    not excuse one whose home is the superproject. Before the review fix
        #    this case was asserted GREEN, which is how `0 provider(s) at their
        #    audited bytes` could print a pass.
        root = tmp / "local-provider-gone-submodule-absent"
        tracked = _seed_scratch(root, submodule_provider=True)
        shutil.rmtree(root / "crates/scratch-spec")
        if tracked:
            expect(
                1,
                "superproject-homed provider gone is NOT excused by an absent submodule",
                root,
                wanted="MISSING     scratch-spec",
            )
        else:
            print("  SKIP  superproject-homed provider (git could not track the fixture)")

        # 6. ... and the excuse it IS for: a provider whose home is a submodule
        #    nobody has populated, ALONGSIDE one that resolves. A fresh worktree
        #    must not read as a TCB violation.
        root = tmp / "submodule-provider-unresolved"
        _seed_scratch(root, submodule_provider=True)
        expect(
            0,
            "submodule-homed provider + uninitialized submodule -> GREEN (UNRESOLVED)",
            root,
            wanted="UNRESOLVED  sub-spec",
        )

        # 7. --require-all is the release bar: an unresolved pin is a pin this
        #    run did not check.
        expect(1, "the same tree under --require-all -> RED", root, "--require-all")

        # 8. ZERO COVERAGE IS A BROKEN GATE. Every entry unresolved means the
        #    run compared no bytes at all; it must not report green.
        root = tmp / "zero-coverage"
        _seed_scratch(root, local_provider=False, submodule_provider=True)
        expect(
            2,
            "a run that resolved NO providers -> rc=2 (it compared zero bytes)",
            root,
            wanted="resolved NO providers",
        )

        # 9. `--print` reaches the same verdict as the default mode. It used to
        #    return 0 unconditionally, so a drifted tree printed green digests.
        root = tmp / "print-on-a-drifted-tree"
        _seed_scratch(root)
        lib = root / "crates/scratch-spec/src/lib.rs"
        lib.write_text(SCRATCH_LIB + "\n// drift\n", encoding="utf-8")
        expect(1, "--print on a drifted tree -> RED, not a green listing", root, "--print")

        # 10. an audit comment containing BALANCED braces must not truncate the
        #     entry. The proof that the entry is still READ, not merely
        #     tolerated: drift inside it is still caught.
        root = tmp / "brace-in-audit-comment"
        _seed_scratch(root, brace_in_comment=True)
        expect(0, "an audit comment with braces still parses -> GREEN", root)
        lib = root / "crates/scratch-spec/src/lib.rs"
        lib.write_text(SCRATCH_LIB + "\n// drift\n", encoding="utf-8")
        expect(
            1,
            "... and the pin in that same entry is still compared",
            root,
            wanted="DRIFTED",
        )

        # 6. a broken gate must not read as a pass.
        root = tmp / "allowlist-renamed"
        _seed_scratch(root)
        allowlist = root / ALLOWLIST_REL
        allowlist.write_text(
            allowlist.read_text(encoding="utf-8").replace(
                "AUDITED_TRUST_SPEC_SOURCES", "AUDITED_SOMETHING_ELSE"
            ),
            encoding="utf-8",
        )
        expect(2, "allowlist renamed away -> rc=2 (the gate cannot ask)", root)

        # 7. an empty allowlist is an empty extraction, never a pass.
        root = tmp / "allowlist-empty"
        _seed_scratch(root)
        allowlist = root / ALLOWLIST_REL
        text = allowlist.read_text(encoding="utf-8")
        head = text.split("const AUDITED_TRUST_SPEC_SOURCES")[0]
        allowlist.write_text(
            head + "const AUDITED_TRUST_SPEC_SOURCES: &[AuditedTrustSpecSource] = &[\n];\n",
            encoding="utf-8",
        )
        expect(2, "allowlist parsed to zero entries -> rc=2 (broken gate)", root)

        # 8. an entry the regex cannot read must not be skipped silently.
        root = tmp / "allowlist-unreadable-entry"
        _seed_scratch(root)
        allowlist = root / ALLOWLIST_REL
        text = allowlist.read_text(encoding="utf-8")
        allowlist.write_text(
            text.replace("];\n", "    AuditedTrustSpecSource { package: PKG },\n];\n"),
            encoding="utf-8",
        )
        expect(2, "an entry this gate cannot read -> rc=2, not a skipped pin", root)
    finally:
        shutil.rmtree(tmp, ignore_errors=True)

    print()
    print(f"selftest: {passed} ok, {failed} bad")
    return 0 if failed == 0 else 1


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="the gate (default)")
    parser.add_argument("--print", dest="printing", action="store_true")
    parser.add_argument(
        "--require-all",
        action="store_true",
        help="an UNRESOLVED pin is a failure (the release bar: every provider present)",
    )
    parser.add_argument("--selftest", action="store_true")
    parser.add_argument("--selftest-run", metavar="ROOT", help=argparse.SUPPRESS)
    args = parser.parse_args()

    if args.selftest:
        return selftest()
    try:
        root = Path(args.selftest_run) if args.selftest_run else Path(__file__).resolve().parents[1]
        return run_check(root, printing=args.printing, require_all=args.require_all)
    except GateError as error:
        print(f"audited-trust-spec-sources: CANNOT CHECK -- {error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    sys.exit(main())
