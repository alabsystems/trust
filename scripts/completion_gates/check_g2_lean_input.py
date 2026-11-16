#!/usr/bin/env python3
"""G2 — Lean input completeness: the schema-owned gate checker.

Named by ``scripts/two_language_completion_gate.py`` (``CHECKER_PATHS["G2"]``)
and executed under its fixed protocol (read-only snapshot, ``python -I``,
``PATH=/usr/bin:/bin``, ``cwd=--root``, one JSON verdict on stdout carrying
the receipt-bound digests).  Self-contained: standard library only, and it
runs under the 3.9 CommandLineTools ``python3`` this box has — which has no
``tomllib``, so the three upstream-Lean ledgers it reads are parsed by a
stated line-anchored subset reader that refuses anything outside the subset.

This checker is the JUDGE of evidence for the nine G2 conjuncts fixed by
``REQUIRED_CHECKS["G2"]``.  It runs no compiler, samples nothing, and never
reads a ``passed`` flag out of the evidence: every conjunct is COMPUTED from
the bound artifact against a structural rule, and every file of the source
tree a conjunct consults is PIN-BOUND before it is read (see ``Context``):
``first-party/clean`` must be an initialized submodule whose HEAD is the
gitlink the accepted revision records, with a clean worktree, and every
consulted file's on-disk blob must be the blob at that pin; files outside
the submodule bind the same way against the accepted revision's HEAD tree.
A symlink anywhere on a consulted path is refused.  An uninitialized
directory holding files, an edited worktree, a symlinked ledger, or a copy
under ``evidence/`` is therefore never the pin — the guarantee the first
landing of this file claimed and did not have (adversarial review,
2026-09-16: hand-authored evidence read 8/9 against the pristine tree and
9/9 against two on-disk edits).

THE REAL GUARANTEE, conjunct by conjunct:

* ``pinned_upstream_lean_revision`` — binds the TRACKED baseline
  ``first-party/clean/tests/upstream-lean/baseline.toml`` at its own path,
  cross-checks the corpus MANIFEST it names AND hashes every corpus file on
  disk against it, and cross-checks the toolchain pin ``first-party/clean/
  lean-toolchain`` (what ``clean-olean/lean_toolchain.rs`` resolves).  Every
  independent defect is reported, not only the first.  Measured 2026-09-16:
  RED — the baseline records ``selection_is_representative = false`` and the
  toolchain pins ``v4.30.0-rc2`` against the baseline's ``v4.27.0``.  Even
  coherent local pins remain red without an independent complete upstream
  ``tests/lean`` tree denominator.
* ``vanilla_lean_build`` — judges a ``trust.lean.ir-library/v1`` envelope by
  the shape ``targo-trust/src/lean_build.rs`` actually writes and its own
  importer (``decode_and_revalidate``) accepts: ``native_codegen`` the string
  ``"unavailable"``, a non-empty ``limitations`` list ending with the
  instrument's own disclosure that serialized bindings are not G1-G8
  completion evidence.  That disclosure IS the refusal: a real envelope reads
  red for the reason the instrument states, and a hand-authored one cannot
  pass because it cannot both carry the v1 disclosure and omit it.  This
  conjunct is STRUCTURALLY RED under v1; it needs a v2 envelope with a
  producer binding.  Sources are pin-bound to the tree.
* ``external_olean_and_dependency_graphs`` — NO instrument produces the
  admitting import graph this contract fixes (``targo trust check`` records
  ``external_olean_imports: "unsupported"``; ``trust_clean::olean_census`` is
  ``diagnostic-only-no-import-admission``).  The shape rules are the
  documented contract; after them the conjunct refuses UNCONDITIONALLY by
  name until the instrument exists and its producer is bound.
* ``all_lean_computational_declarations_inventoried`` — judges a
  ``trust.lean.check-kernel-roster/v1`` census, refusing the ``authority``
  the instrument always writes (``diagnostic-only``) by name, binding
  ``tool_source_revision`` to the accepted revision and every requested and
  checked source to the tree, and requiring the verified denominator and
  measured runtime classification the instrument discloses it lacks.
  A structurally favorable inventory still reads red: no producer binds its
  authority or denominator to the owner-admitted Lean population.
* ``zero_upstream_lean_semantic_regressions`` — judges
  ``run_upstream_lean.py --json`` against the TRACKED ``corpus.toml``:
  seededness is computed from the corpus, results must biject the pinned
  probes on (id, file, decl, expected), the summary is cross-checked, a
  stdout capture beginning with the UNSEEDED banner is refused with the
  seeding fix.  A structurally favorable run still reads red: its JSON has no
  producer or owner-policy binding for non-applicable classifications.
* ``non_applicable_lean_harness_rows_only`` — binds the TRACKED
  ``exceptions.toml`` at its own path; every row must be a non-applicable
  classification, and active rows must name a tracked probe and expire after
  the checker's system UTC date.
* ``owner_pinned_lean_surface_and_accept_reject_parity``,
  ``lean_elaborator_constructor_totality``,
  ``lean_macro_io_unsafe_ffi_surface`` — NO instrument produces these; as
  for the import graph, the shape rules are the contract and the conjunct
  then refuses unconditionally by name.

Every tree file a conjunct consulted is recorded in that check's
``artifacts`` beside the bound artifact, so the verdict can be re-verified
against exactly what was read.

Every Git call runs as ``git --no-replace-objects --no-optional-locks -c
core.fsmonitor=false -c core.attributesFile=/dev/null`` with every caller
``GIT_*`` variable stripped and the runner's own neutralizers set in their
place: no system or global configuration tier, no XDG configuration, no
system attributes, and no lazy fetch (on a Git that honors
``GIT_NO_LAZY_FETCH``: 2.45, and the 2.41.1/2.42.2/2.43.4/2.44.1 security
releases).  The checker runs directly as well as under the runner, so it
protects itself: before any tree is read, the superproject and the clean
submodule are each refused by name when they carry a ``refs/replace/*`` ref
(a replacement object lets ``ls-tree`` and ``status`` answer for a forged
tree while ``rev-parse HEAD`` still names the pin), a non-empty
``info/attributes``, or repository configuration that starts a program from a
read-only command -- an fsmonitor hook, a promisor remote, or any
``filter.*`` driver (``status`` runs a clean filter to compare content).
Consulted files are bound by their RAW bytes (``hash-object --no-filters``),
which are what the conjuncts read.

EVIDENCE BUNDLE (``--verify-evidence``), schema ``trust.two-language.gate-evidence/v1``::

    {"schema": "trust.two-language.gate-evidence/v1", "gate": "G2",
     "checker": "trust.two-language.g2.lean-input/v2",
     "artifacts": {"<check id>": {"path": "<relative>", "sha256": "<64 hex>"}, ...}}

Every artifact path is root-relative, must not escape ``--root``, must exist,
and must hash to the recorded digest.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import stat
import subprocess
import sys
from datetime import date, datetime, timezone
from pathlib import Path
from typing import Any, Callable

# Trust (2026-09-27): an EXPLICIT nesting bound, because the `RecursionError`
# caught at the parse sites below is NOT one. Python's recursion limit is not a
# property this gate controls. MEASURED 2026-09-27: `b"[" * 1100 + b"0" + b"]" * 1100`
# raises `RecursionError` on CPython 3.9 (so the reader refused it) and parses
# CLEANLY on CPython 3.14 (so it did not). `_isolated_python` runs every checker
# under `sys.executable` and NOTHING here pins an interpreter version, so on a
# newer Python the refusal of adversarially nested evidence silently disappeared.
# `scripts/tests/completion_gate_malformed_input_test.py` is the control and does
# fail on 3.14 — but no harness lane runs it, so nothing said so.
#
# 64 is chosen from measurement, not taste: the deepest legitimate JSON in the
# tree is depth 4. Refuse-only — this can reject input a reader previously
# accepted, never accept input it previously rejected.
TRUST_MAX_JSON_DEPTH = 64


def _trust_json_nesting_depth(text: str) -> int:
    """Maximum `[`/`{` nesting of `text`, ignoring brackets inside strings."""
    depth = 0
    deepest = 0
    in_string = False
    escaped = False
    for ch in text:
        if in_string:
            if escaped:
                escaped = False
            elif ch == "\\":
                escaped = True
            elif ch == '"':
                in_string = False
            continue
        if ch == '"':
            in_string = True
        elif ch == "[" or ch == "{":
            depth += 1
            deepest = max(deepest, depth)
        elif ch == "]" or ch == "}":
            depth -= 1
    return deepest


SCHEMA = "trust.two-language.gate-checker-verdict/v2"
EVIDENCE_SCHEMA = "trust.two-language.gate-evidence/v1"
GOAL = "TRUST-TWO-LANGUAGE-100"
GATE = "G2"
CHECKER = "trust.two-language.g2.lean-input/v2"
REPOSITORY_ID = "https://github.com/alabsystems/trust"
HEX_DIGEST = re.compile(r"^[0-9a-f]{64}$")
GIT_OID = re.compile(r"^[0-9a-f]{40}$")
PREFIXED_DIGEST = re.compile(r"^(sha256:)?[0-9a-f]{64}$")

# Exactly REQUIRED_CHECKS["G2"] in scripts/two_language_completion_gate.py.
REQUIRED = (
    "pinned_upstream_lean_revision",
    "vanilla_lean_build",
    "external_olean_and_dependency_graphs",
    "all_lean_computational_declarations_inventoried",
    "zero_upstream_lean_semantic_regressions",
    "non_applicable_lean_harness_rows_only",
    "owner_pinned_lean_surface_and_accept_reject_parity",
    "lean_elaborator_constructor_totality",
    "lean_macro_io_unsafe_ffi_surface",
)

# Tree files the conjuncts are judged against.  ``clean-olean/lean_toolchain.rs``
# anchors the pinned Lean toolchain at ``<clean workspace root>/lean-toolchain``;
# the upstream-Lean instrument (``run_upstream_lean.py``) lives beside its
# three ledgers under ``tests/upstream-lean/`` of that same workspace.
CLEAN_ROOT = "first-party/clean"
LEAN_TOOLCHAIN_PIN = f"{CLEAN_ROOT}/lean-toolchain"
UPSTREAM_BASELINE = f"{CLEAN_ROOT}/tests/upstream-lean/baseline.toml"
UPSTREAM_EXCEPTIONS = f"{CLEAN_ROOT}/tests/upstream-lean/exceptions.toml"
UPSTREAM_CORPUS = f"{CLEAN_ROOT}/tests/upstream-lean/corpus.toml"
SEED_COMMAND = "tests/upstream-lean/run_upstream_lean.py --seed-from-corpus-dir"
UNSEEDED_BANNER = "UPSTREAM-LEAN CORPUS IS UNSEEDED"

# Artifact schemas.  The first four are what the real instruments write today
# (targo-trust/src/lean_build.rs, targo-trust/src/lean_cli/census.rs,
# crates/trust-certify/src/clean_census.rs, crates/trust-clean/src/olean_census.rs);
# the rest are fixed here.  A conjunct passes only against its exact schema.
IR_LIBRARY_SCHEMA = "trust.lean.ir-library/v1"
IR_LIBRARY_AUTHORITY = "recheck-sources-and-re-earn-gate-on-import"
# The last line of every *_LIMITATIONS constant in lean_build.rs — the
# instrument's own statement that its envelope is not completion evidence.
IR_LIBRARY_COMPLETION_DISCLOSURE = (
    "Serialized gate bindings are not transferable proof authority or G1-G8 completion evidence."
)
KERNEL_ROSTER_SCHEMA = "trust.lean.check-kernel-roster/v1"
KERNEL_ROSTER_INNER_SCHEMA = "trust.lean.kernel-roster/v1"
KERNEL_CLASSIFICATION_SCHEMA = "trust.lean.kernel-classification/v1"
SOURCE_GRAPH_SCHEMA = "trust.lean.source-check-observation/v1"
# What census.rs / clean_census.rs always write, and the admitting value no
# instrument writes yet.
CENSUS_DIAGNOSTIC_AUTHORITY = "diagnostic-only"
CENSUS_INVENTORY_AUTHORITY = "post-lowering-inventory"
OLEAN_DIAGNOSTIC_SCHEMA = "trust.lean.olean-closure-observation/v1"
OLEAN_IMPORT_GRAPH_SCHEMA = "trust.two-language.lean-olean-import-graph/v1"
OLEAN_IMPORT_GRAPH_AUTHORITY = "admitted-external-imports"
SURFACE_PARITY_SCHEMA = "trust.two-language.lean-surface-parity/v1"
CONSTRUCTOR_TOTALITY_SCHEMA = "trust.two-language.lean-elaborator-constructor-totality/v1"
MACRO_IO_SURFACE_SCHEMA = "trust.two-language.lean-macro-io-unsafe-ffi-surface/v1"
SEMANTICS_CONTRACT_SCHEMA = "trust.two-language.semantics-contract/v1"
ADMISSION_CONTRACT_SCHEMA = "trust.two-language.admission-contract/v1"
CORPUS_MANIFEST_SCHEMA = "trust.two-language.corpus-manifest/v1"
ADMISSION_CONTRACT_ID = "trust.two-language.contract.admission"

UPSTREAM_REVISION = re.compile(r"^leanprover/lean4:([0-9a-f]{40})$")
# lean_toolchain.rs accepts any single non-whitespace token as the pin; the
# release tag is extracted when the token carries one, so a nightly pin reads
# as a DISAGREEMENT with the baseline, never as a malformed pin.
RELEASE_TAG = re.compile(r"^leanprover/lean4:(v\d+\.\d+\.\d+(?:-rc\d+)?)$")
LEAN_VERSION = re.compile(r"^v\d+\.\d+\.\d+(?:-rc\d+)?$")
MANIFEST_CHECKSUM = re.compile(r"^sha256:[0-9a-f]{64}$")
ISO_DATE = re.compile(r"^\d{4}-\d{2}-\d{2}$")

# Vocabulary of the upstream-Lean instrument (run_upstream_lean.py / corpus.toml / exceptions.toml).
PROBE_OUTCOMES = ("lowers", "rejected", "empty", "timeout", "crashed")
PINNABLE_OUTCOMES = ("lowers", "rejected", "empty")
WAIVABLE_OUTCOMES = ("rejected", "empty", "timeout")
LEDGER_FIELDS = ("id", "probe_id", "observed", "kind", "status", "owner", "reason", "issue", "reviewed_on", "expires_on")
LEDGER_STATUSES = ("active", "resolved", "superseded")
# G2: a ledger row may classify a harness row NON-APPLICABLE.  It may not
# waive a valid admitted Lean program (expected_fail) or change its expected
# semantics (intentional_divergence).
NON_APPLICABLE_KINDS = ("expected_skip", "environmental_skip")
WAIVING_KINDS = ("expected_fail", "intentional_divergence")
BASELINE_SURFACES = {
    "lean.parse": "parser",
    "lean.elab": "elaborator",
    "lean.trust-ir": "trust_ir",
}

# Kernel classification (trust.lean.kernel-classification/v1) -> the runtime
# classification an inventoried row must carry.
KERNEL_KINDS = {
    "proof-only": "kernel-only",
    "type-family": "kernel-only",
    "computational-candidate": "trust-ir-body",
    "primitive-candidate": "trust-ir-body",
}

# Lean 4 kernel/elaborator data families and their constructors, fixed by
# upstream Lean 4 (src/Lean/Expr.lean, Level.lean, Declaration.lean, Syntax.lean).
CONSTRUCTOR_FAMILIES = {
    "Expr": ("bvar", "fvar", "mvar", "sort", "const", "app", "lam", "forallE", "letE", "lit", "mdata", "proj"),
    "Level": ("zero", "succ", "max", "imax", "param", "mvar"),
    "Literal": ("natVal", "strVal"),
    "ConstantInfo": ("axiomInfo", "defnInfo", "thmInfo", "opaqueInfo", "quotInfo", "inductInfo", "ctorInfo", "recInfo"),
    "Syntax": ("missing", "node", "atom", "ident"),
}

# The macro / IO / unsafe / FFI surface of Lean 4 a complete frontend must carry.
MACRO_IO_UNSAFE_FFI_FEATURES = (
    "macro_rules",
    "syntax_and_macro_commands",
    "elab_commands",
    "notation",
    "do_notation",
    "io_actions",
    "partial_def",
    "unsafe_def",
    "implemented_by",
    "extern_ffi",
    "opaque_definitions",
    "initialize_commands",
)
FEATURE_LOWERINGS = ("trust-ir-body", "kernel-only")
VERDICTS = ("accept", "reject")
TRACKED_BLOB_MODES = ("100644", "100755")

# The runner's GIT_GLOBAL_OPTIONS, plus the repository-local attributes-file
# override (the global tier that would name one is neutralized in _git_env):
# no replacement objects, no optional index locks, no fsmonitor hook.
GIT_GLOBAL_OPTIONS = (
    "--no-replace-objects", "--no-optional-locks",
    "-c", "core.fsmonitor=false",
    "-c", f"core.attributesFile={os.devnull}",
)
# Repository settings with which a read-only Git command starts a program (the
# runner's PROGRAM_CONFIG), plus every filter driver: `git status` runs a
# driver's clean command to compare a stat-dirty file.  Refused by name in the
# superproject and the clean submodule before either tree is read.
PROGRAM_CONFIG = (
    r"^(core\.fsmonitor|extensions\.partialclone"
    r"|remote\.(.*\.)?(promisor|partialclonefilter)|filter\..*)$"
)
# Git reads an empty value, and false, no, off or 0 in any case, as false; a
# key with no value at all is true.
FALSE_SPELLINGS = (b"", b"false", b"no", b"off", b"0")
# TOML ends a line only at LF or CRLF.  Every other character Python's
# str.splitlines breaks on -- a lone CR, VT, FF, FS/GS/RS, and U+0085/U+2028/
# U+2029, which TOML admits inside a comment -- would make the subset reader
# see a key or table header that a real TOML parser (run_upstream_lean.py's
# tomllib) reads as comment text.  The remaining C0 controls and DEL are
# invalid in TOML anyway.  The tracked ledgers contain none of them, so each
# is refused wherever it appears.
TOML_FORBIDDEN = re.compile("[\x00-\x08\x0a-\x1f\x7f\x85\u2028\u2029]")
# TOML's decimal integer (no sign-plus, underscore, or leading-zero forms, and
# ASCII digits only -- ``\d`` would also admit Arabic-Indic and other Unicode
# digits, which int() reads but TOML refuses), bounded before int() so no
# interpreter's digit limit can raise.  The same form as G1's reader.
TOML_INTEGER = re.compile(r"-?(?:0|[1-9][0-9]{0,18})\Z")
# The tracked ledgers nest arrays at most one level deep; the bound refuses
# deeper values before recursion can exhaust the interpreter stack.
TOML_MAX_ARRAY_DEPTH = 8


def sha256_of(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1 << 20), b""):
            digest.update(chunk)
    return digest.hexdigest()


class Refusal(Exception):
    """A conjunct refusal.  The message names the fix (v7/D3)."""


def load_json_object(path: Path) -> dict[str, Any]:
    try:
        _trust_text = path.read_text(encoding="utf-8")
        if _trust_json_nesting_depth(_trust_text) > TRUST_MAX_JSON_DEPTH:
            raise ValueError(f"JSON nests deeper than {TRUST_MAX_JSON_DEPTH}")
        value = json.loads(_trust_text)
    except (OSError, UnicodeError, ValueError, RecursionError) as exc:
        raise Refusal(f"artifact is not a JSON document: {exc}") from exc
    if not isinstance(value, dict):
        raise Refusal("artifact must be a JSON object")
    return value


def require_schema(doc: dict[str, Any], schema: str) -> None:
    if doc.get("schema") != schema:
        raise Refusal(f"artifact schema must be {schema!r}, got {doc.get('schema')!r}")


def nonempty_list(doc: dict[str, Any], key: str) -> list[Any]:
    value = doc.get(key)
    if not isinstance(value, list) or not value:
        raise Refusal(f"`{key}` must be a non-empty list")
    return value


def require_hex(value: Any, what: str) -> str:
    if not isinstance(value, str) or not HEX_DIGEST.fullmatch(value):
        raise Refusal(f"{what} must be a lowercase 64-hex digest")
    return value


def require_str(value: Any, what: str) -> str:
    if not isinstance(value, str) or not value:
        raise Refusal(f"{what} must be a non-empty string")
    return value


def canonical(value: Any) -> str:
    """One spelling per JSON value, so kernel ``Name`` values compare as
    identities whether they serialize as strings or structured components."""
    return json.dumps(value, sort_keys=True, separators=(",", ":"))


def plain_relative(relative: str, what: str) -> tuple[str, ...]:
    parts = Path(relative).parts
    if not relative or Path(relative).is_absolute() or not parts or any(part in ("..", ".") for part in parts):
        raise Refusal(f"{what} must be a plain root-relative path, got {relative!r}")
    return parts


def lstat_or_none(path: Path, label: str) -> os.stat_result | None:
    """``os.lstat(path)``, or None when the entry is absent (ENOENT, or a
    non-directory on the way: ENOTDIR).  Any other error -- a component
    longer than NAME_MAX, a directory that cannot be searched -- is a named
    refusal, never an exception escaping the verdict (Python 3.9's
    ``Path.is_symlink``/``exists``/``is_file`` swallow only a few errnos)."""
    try:
        return os.lstat(path)
    except (FileNotFoundError, NotADirectoryError):
        return None
    except OSError as exc:
        raise Refusal(f"{label}: cannot inspect it: {exc.strerror or exc}") from None
    except ValueError as exc:
        raise Refusal(f"{label}: cannot inspect it: {exc}") from None


def _git_env() -> dict[str, str]:
    # The runner's _git_env, repeated because this checker also runs
    # directly: every caller GIT_* variable is dropped, then the system,
    # global and XDG configuration tiers and the system attributes file are
    # replaced by empty ones, and lazy fetching is off (a promisor remote's
    # transport would otherwise start a program on any missing-object read).
    env = {key: value for key, value in os.environ.items() if not key.startswith("GIT_")}
    env.update(
        GIT_CONFIG_NOSYSTEM="1",
        GIT_CONFIG_GLOBAL=os.devnull,
        GIT_ATTR_NOSYSTEM="1",
        GIT_NO_LAZY_FETCH="1",
        XDG_CONFIG_HOME=os.devnull,
    )
    return env


# ── the accepted source tree, PIN-BOUND ─────────────────────────────────────


class Context:
    """Receipt-bound inputs a conjunct may be judged against: the accepted
    tree under ``--root``, the accepted source revision, and the owner-signed
    authority policy.

    Every tree read goes through ``tree_file``, which binds the file to a
    commit before reading it: under ``first-party/clean`` to the gitlink the
    accepted HEAD records (submodule initialized, HEAD == gitlink, worktree
    clean, on-disk raw bytes == blob at the pin); elsewhere to the accepted
    HEAD tree of the superproject.  No symlink component is followed.  Git
    runs with ``GIT_GLOBAL_OPTIONS`` under ``_git_env``, so the tree being
    judged is never written to and no replacement object, fsmonitor hook or
    caller ``GIT_*`` override is honored; each repository is refused by name
    (``refuse_repository_overrides``) before its tree is read when it
    carries a replacement ref, repository-local attributes, or configuration
    that starts a program."""

    def __init__(
        self,
        root: Path,
        policy_path: Path,
        policy_sha256: str,
        corpus_path: Path,
        corpus_sha256: str,
        acceptance_run_id: str,
        source_revision: str,
    ) -> None:
        self.root = root
        self.policy_path = policy_path
        self.policy_sha256 = policy_sha256
        self.corpus_path = corpus_path
        self.corpus_sha256 = corpus_sha256
        self.acceptance_run_id = acceptance_run_id
        self.source_revision = source_revision
        self._pin: str | None = None
        self._super_head: str | None = None
        self._blobs: dict[str, dict[str, str]] = {}
        self.consulted: dict[str, dict[str, str]] = {}

    # -- git ---------------------------------------------------------------

    def git_process(self, args: list[str], cwd: Path | None = None, stdin: bytes | None = None) -> subprocess.CompletedProcess:
        """Run hardened Git; bytes in and out, and a Git that cannot run refuses."""
        try:
            return subprocess.run(
                ["git", *GIT_GLOBAL_OPTIONS, *args],
                cwd=str(cwd or self.root), env=_git_env(), input=stdin,
                capture_output=True, check=False, timeout=300,
            )
        except (OSError, subprocess.TimeoutExpired) as exc:
            raise Refusal(f"git is required to bind the tree to its pin and could not run: {exc}") from exc

    def git_bytes(self, args: list[str], cwd: Path | None = None) -> bytes:
        process = self.git_process(args, cwd)
        if process.returncode != 0:
            detail = process.stderr.decode("utf-8", errors="replace").strip().splitlines()
            raise Refusal(f"git {' '.join(args[:2])} failed: {detail[0] if detail else 'no diagnostic'}")
        return process.stdout

    def git(self, args: list[str], cwd: Path | None = None) -> str:
        output = self.git_bytes(args, cwd)
        try:
            return output.decode("utf-8")
        except UnicodeDecodeError:
            raise Refusal(f"git {' '.join(args[:2])} answered with bytes that are not UTF-8") from None

    def refuse_repository_overrides(self, repo: Path, label: str) -> None:
        """Refuse, by name, a repository whose own state would make a Git
        reader answer for something other than its committed tree, or run a
        program: a ``refs/replace/*`` ref (``--no-replace-objects`` already
        bypasses it; a repository carrying one is refused outright, as the
        runner does), a non-empty ``info/attributes`` (repository-local
        content conversion), and the ``PROGRAM_CONFIG`` settings -- an
        fsmonitor hook that is not a false spelling, a promisor remote, or
        any filter driver.  Called before the repository's HEAD or tree is
        read."""
        replace_refs = self.git_bytes(["for-each-ref", "--format=%(refname)", "refs/replace/"], cwd=repo).split()
        if replace_refs:
            names = ", ".join(ref.decode("utf-8", errors="replace") for ref in replace_refs[:3])
            raise Refusal(
                f"{label} carries refs/replace/* object substitutions ({names}): a replacement object makes "
                f"ls-tree and status answer for a forged tree while HEAD still names the pin"
            )
        attributes = self.git(["rev-parse", "--git-path", "info/attributes"], cwd=repo).strip()
        attributes_path = Path(attributes) if Path(attributes).is_absolute() else repo / attributes
        info = lstat_or_none(attributes_path, f"{label} info/attributes")
        if info is not None and (not stat.S_ISREG(info.st_mode) or info.st_size):
            raise Refusal(f"{label} carries a repository-local info/attributes, which changes content conversion")
        process = self.git_process(["config", "--null", "--get-regexp", PROGRAM_CONFIG], cwd=repo)
        if process.returncode == 1 and not process.stdout:
            return
        if process.returncode != 0:
            raise Refusal(f"{label}: cannot read the repository configuration")
        offending: list[str] = []
        for record in process.stdout.split(b"\0"):
            if not record:
                continue
            key, has_value, value = record.partition(b"\n")
            if key == b"core.fsmonitor" and has_value and value.lower() in FALSE_SPELLINGS:
                continue
            offending.append(key.decode("utf-8", errors="replace"))
        if offending:
            raise Refusal(
                f"{label} configuration starts a program from a read-only Git command "
                f"(fsmonitor hook, promisor remote or filter driver): {', '.join(offending[:3])}"
            )

    def refuse_symlinks(self, relative: str) -> None:
        current = self.root
        for part in plain_relative(relative, "tree path"):
            current = current / part
            shown = current.relative_to(self.root).as_posix()
            info = lstat_or_none(current, f"{relative}: `{shown}`")
            if info is None:
                return
            if stat.S_ISLNK(info.st_mode):
                raise Refusal(f"{relative}: `{shown}` is a symlink; a tree read follows no symlink")

    def super_head(self) -> str:
        if self._super_head is None:
            try:
                top = self.git(["rev-parse", "--show-toplevel"]).strip()
            except Refusal as exc:
                raise Refusal(f"--root is not the top level of a git worktree ({exc}): an ungoverned directory has no pin") from None
            if not top or Path(top).resolve() != self.root:
                raise Refusal(f"--root is not the top level of a git worktree (git answers {top!r})")
            self.refuse_repository_overrides(self.root, "the superproject")
            head = self.git(["rev-parse", "HEAD"]).strip()
            if not GIT_OID.fullmatch(head):
                raise Refusal("the superproject has no HEAD commit")
            self._super_head = head
        return self._super_head

    def clean_pin(self) -> str:
        """The clean submodule's gitlink at the accepted HEAD, established
        only once the submodule is initialized AT that gitlink with a clean
        worktree.  ``git rev-parse`` inside an uninitialized submodule
        directory silently answers for the SUPERPROJECT, so the checks here
        start from the superproject's tree entry and require ``.git``."""
        if self._pin is not None:
            return self._pin
        self.super_head()
        self.refuse_symlinks(CLEAN_ROOT)
        entry = self.git(["ls-tree", "HEAD", "--", CLEAN_ROOT]).strip()
        if not entry:
            raise Refusal(f"{CLEAN_ROOT} is not in the superproject tree at HEAD")
        mode, kind, oid = entry.split()[:3]
        if mode != "160000" or kind != "commit" or not GIT_OID.fullmatch(oid):
            raise Refusal(f"{CLEAN_ROOT} at HEAD is not a submodule gitlink (mode {mode}): files committed in its place are not the clean pin")
        sub = self.root / CLEAN_ROOT
        if lstat_or_none(sub / ".git", f"{CLEAN_ROOT}/.git") is None:
            raise Refusal(
                f"{CLEAN_ROOT} has no .git: the clean submodule is not initialized at its pin {oid[:12]} — "
                f"materialize the clean submodule (scripts/submodule_sync.sh --restore); "
                f"an uninitialized directory holding files is not the pin"
            )
        top = self.git(["rev-parse", "--show-toplevel"], cwd=sub).strip()
        if not top or Path(top).resolve() != sub.resolve():
            raise Refusal(f"git inside {CLEAN_ROOT} answers for {top!r}, not the submodule: not initialized at its pin")
        self.refuse_repository_overrides(sub, CLEAN_ROOT)
        head = self.git(["rev-parse", "HEAD"], cwd=sub).strip()
        if head != oid:
            raise Refusal(f"{CLEAN_ROOT} is checked out at {head[:12]} but the accepted revision pins {oid[:12]}: only the pin is the pin")
        porcelain = self.git(["status", "--porcelain", "--untracked-files=all"], cwd=sub).strip()
        if porcelain:
            first = porcelain.splitlines()[0]
            raise Refusal(
                f"{CLEAN_ROOT} worktree differs from the pin {oid[:12]} (git status: {first!r}): "
                f"an on-disk file that is not the blob at the pin cannot be judged"
            )
        self._pin = oid
        return oid

    def _blob_map(self, repo: Path, commit: str) -> dict[str, str]:
        """``{path: blob oid}`` of the regular files at ``commit``.  A path
        that is not UTF-8 is left out: every consulted path is text that must
        name its entry exactly, and no surrogate spelling may stand in for
        raw bytes."""
        key = f"{repo}@{commit}"
        if key not in self._blobs:
            blobs: dict[str, str] = {}
            for entry in self.git_bytes(["ls-tree", "-r", "-z", commit], cwd=repo).split(b"\0"):
                if not entry:
                    continue
                meta, _, raw_path = entry.partition(b"\t")
                try:
                    mode, kind, oid = meta.decode("ascii").split()[:3]
                    path = raw_path.decode("utf-8")
                except (UnicodeDecodeError, ValueError):
                    continue
                if kind == "blob" and mode in TRACKED_BLOB_MODES:
                    blobs[path] = oid
            self._blobs[key] = blobs
        return self._blobs[key]

    def _binding(self, relative: str) -> tuple[Path, str, dict[str, str], str]:
        """``(repo, path inside repo, blob map, label)`` for one tree path."""
        parts = plain_relative(relative, "tree path")
        if parts[:2] == tuple(Path(CLEAN_ROOT).parts):
            pin = self.clean_pin()
            inner = "/".join(parts[2:])
            return self.root / CLEAN_ROOT, inner, self._blob_map(self.root / CLEAN_ROOT, pin), f"the clean pin {pin[:12]}"
        head = self.super_head()
        return self.root, "/".join(parts), self._blob_map(self.root, head), f"the accepted revision {head[:12]}"

    def tree_files(self, relatives: list[str]) -> list[Path]:
        """Pin-bind several tree files at once (one ``hash-object`` call over
        their RAW bytes: ``--no-filters``, because raw bytes are what the
        conjuncts read, whatever conversion or filter an attribute names)."""
        if not relatives:
            return []
        paths: list[Path] = []
        expected: list[str] = []
        repos: set[Path] = set()
        for relative in relatives:
            # --stdin-paths reads one path per line and strips a trailing CR,
            # so a path holding a line break or other control character would
            # hash a DIFFERENT file than the one read here.
            if re.search("[\x00-\x1f\x7f]", relative):
                raise Refusal(f"tree path {relative!r} holds a control character: it cannot be bound one path per line")
            self.refuse_symlinks(relative)
            repo, inner, blobs, label = self._binding(relative)
            repos.add(repo)
            path = self.root / relative
            blob = blobs.get(inner)
            info = lstat_or_none(path, relative)
            if blob is None:
                raise Refusal(f"{relative} is not a tracked regular file at {label}" + ("" if info is not None else " and is absent on disk"))
            if info is None or not stat.S_ISREG(info.st_mode):
                raise Refusal(f"{relative} is tracked at {label} but absent on disk: materialize the tree at its pin")
            paths.append(path)
            expected.append(blob)
        process = self.git_process(
            ["hash-object", "--no-filters", "--stdin-paths"],
            stdin=b"".join(os.fsencode(str(p)) + b"\n" for p in paths),
        )
        actual = process.stdout.decode("ascii", errors="replace").split()
        if process.returncode != 0 or len(actual) != len(paths):
            raise Refusal("git hash-object failed over the consulted tree files")
        for relative, path, want, got in zip(relatives, paths, expected, actual):
            if want != got:
                _, _, _, label = self._binding(relative)
                raise Refusal(f"{relative} on disk (blob {got[:12]}) is not the blob at {label} ({want[:12]}): only the committed pin is judged")
            try:
                digest = sha256_of(path)
            except OSError as exc:
                raise Refusal(f"{relative} cannot be read: {exc.strerror or exc}") from None
            self.consulted.setdefault(relative, {"path": relative, "sha256": digest})
        return paths

    def tree_file(self, relative: str) -> Path:
        return self.tree_files([relative])[0]

    def tree_text(self, relative: str) -> str:
        try:
            return self.tree_file(relative).read_text(encoding="utf-8")
        except UnicodeError as exc:
            raise Refusal(f"{relative} is not UTF-8: {exc}") from exc
        except OSError as exc:
            raise Refusal(f"{relative} cannot be read: {exc.strerror or exc}") from exc

    def require_tree_artifact(self, path: Path, relative: str) -> None:
        """A conjunct whose evidence IS a tracked ledger must be bound to that
        ledger's own path: a copy under evidence/ is not the pin."""
        lexical = self.root / relative
        if path != lexical:
            # Bound elsewhere: either a copy, or the tracked path is a symlink that resolves elsewhere.
            try:
                self.refuse_symlinks(relative)
            except Refusal as exc:
                raise Refusal(f"{exc}: a symlinked ledger is not the pin") from None
            raise Refusal(f"artifact must be the tracked file {relative} itself, bound by its own path — a copy is not the pin")
        self.refuse_symlinks(relative)

    def lean_toolchain_pin(self) -> tuple[str, str | None]:
        """``(pin token, release tag or None)`` from the pinned toolchain file."""
        text = self.tree_text(LEAN_TOOLCHAIN_PIN).strip()
        if not text or any(char.isspace() for char in text):
            raise Refusal(f"{LEAN_TOOLCHAIN_PIN} must pin exactly one toolchain token, got {text!r}")
        match = RELEASE_TAG.fullmatch(text)
        return text, (match.group(1) if match else None)

    def bound_json(self, path: Path, digest: str, label: str) -> dict[str, Any]:
        require_hex(digest, f"{label} sha256")
        try:
            actual = sha256_of(path)
        except OSError as exc:
            raise Refusal(f"{label} cannot be read: {exc}") from exc
        if actual != digest:
            raise Refusal(f"{label} hash mismatch: recorded {digest}, actual {actual}")
        return load_json_object(path)

    def owner_lean_revision(self) -> str:
        """Join the Clean baseline to the top-level owner admission and corpus pins."""
        policy = self.bound_json(self.policy_path, self.policy_sha256, "authority policy")
        contracts = policy.get("contracts")
        admission_ref = contracts.get("admission") if isinstance(contracts, dict) else None
        if (
            not isinstance(admission_ref, dict)
            or set(admission_ref) != {"id", "path", "sha256"}
            or admission_ref.get("id") != ADMISSION_CONTRACT_ID
        ):
            raise Refusal("authority policy lacks the schema-owned owner admission contract reference")
        contract_path, error = resolve_ref(
            self.root,
            {"path": admission_ref["path"], "sha256": admission_ref["sha256"]},
        )
        if error is not None or contract_path is None:
            raise Refusal(f"owner admission contract: {error}")
        contract = load_json_object(contract_path)
        require_schema(contract, ADMISSION_CONTRACT_SCHEMA)
        if contract.get("goal_id") != GOAL or contract.get("repository_id") != REPOSITORY_ID:
            raise Refusal("owner admission contract has the wrong goal or repository identity")
        lanes = contract.get("lanes")
        lean = lanes.get("lean") if isinstance(lanes, dict) else None
        if (
            not isinstance(lean, dict)
            or not isinstance(lean.get("upstream_revision"), str)
            or not GIT_OID.fullmatch(lean["upstream_revision"])
        ):
            raise Refusal("owner admission contract has no pinned Lean upstream revision")
        revision = lean["upstream_revision"]
        entries = lean.get("entries")
        if not isinstance(entries, list) or not entries:
            raise Refusal("owner admission contract has no Lean entries")
        corpus = self.bound_json(self.corpus_path, self.corpus_sha256, "receipt corpus manifest")
        require_schema(corpus, CORPUS_MANIFEST_SCHEMA)
        for field, expected in (
            ("goal_id", GOAL),
            ("repository_id", REPOSITORY_ID),
            ("acceptance_run_id", self.acceptance_run_id),
            ("source_revision", self.source_revision),
        ):
            if corpus.get(field) != expected:
                raise Refusal(f"receipt corpus manifest {field} does not match the acceptance run")
        corpus_lean = corpus.get("lean")
        if not isinstance(corpus_lean, dict) or corpus_lean.get("upstream_revision") != revision:
            raise Refusal("receipt corpus Lean revision disagrees with the owner admission contract")
        if corpus_lean.get("admission_policy_sha256") != admission_ref["sha256"] or corpus_lean.get("entries") != entries:
            raise Refusal("receipt corpus Lean population disagrees with the owner admission contract")
        return revision


# ── a stated TOML subset ────────────────────────────────────────────────────
#
# The three ledgers are one scalar (or one single-line array) per line under
# ``[table]`` / ``[[array-of-tables]]`` headers with ``#`` comments.  That is
# the whole subset; a line outside it refuses with its number instead of
# being guessed at.  Lines are TOML's lines (LF or CRLF), never Python's
# str.splitlines lines (see TOML_FORBIDDEN); integers are TOML's 64-bit
# decimal form (TOML_INTEGER); arrays nest at most TOML_MAX_ARRAY_DEPTH.


def _strip_comment(line: str) -> str:
    in_string = False
    escaped = False
    for index, char in enumerate(line):
        if in_string:
            if escaped:
                escaped = False
            elif char == "\\":
                escaped = True
            elif char == '"':
                in_string = False
        elif char == '"':
            in_string = True
        elif char == "#":
            return line[:index]
    return line


def _split_array(body: str, what: str, number: int) -> list[str]:
    """Top-level elements of a TOML array body, refused as G1's reader refuses
    them: an empty element (``[1,,2]``, ``[,]``) and an unterminated string are
    not TOML, so they are refused rather than read around.  One trailing comma
    is TOML and reads as nothing."""
    items: list[str] = []
    current: list[str] = []
    in_string = False
    escaped = False
    for char in body:
        if in_string:
            current.append(char)
            if escaped:
                escaped = False
            elif char == "\\":
                escaped = True
            elif char == '"':
                in_string = False
        elif char == '"':
            in_string = True
            current.append(char)
        elif char == ",":
            items.append("".join(current))
            current = []
        else:
            current.append(char)
    if in_string:
        raise Refusal(f"{what} line {number}: unterminated TOML array string")
    tail = "".join(current)
    if tail.strip():
        items.append(tail)
    items = [item.strip() for item in items]
    if any(not item for item in items):
        raise Refusal(f"{what} line {number}: empty TOML array element")
    return items


def _toml_value(raw: str, what: str, number: int, depth: int = 0) -> Any:
    if raw.startswith('"') and raw.endswith('"') and len(raw) >= 2:
        # A TOML basic string's escapes (\" \\ \n \t \uXXXX) are JSON's.
        try:
            return json.loads(raw)
        except json.JSONDecodeError:
            raise Refusal(f"{what} line {number}: unsupported string escape") from None
    if raw in ("true", "false"):
        return raw == "true"
    if TOML_INTEGER.fullmatch(raw):
        value = int(raw)
        if not -(2 ** 63) <= value < 2 ** 63:
            raise Refusal(f"{what} line {number}: TOML integer outside the 64-bit range")
        return value
    if raw.startswith("[") and raw.endswith("]"):
        if depth >= TOML_MAX_ARRAY_DEPTH:
            raise Refusal(f"{what} line {number}: TOML array nesting exceeds {TOML_MAX_ARRAY_DEPTH}")
        return [_toml_value(item, what, number, depth + 1) for item in _split_array(raw[1:-1], what, number)]
    raise Refusal(f"{what} line {number}: value outside the ledger TOML subset: {raw[:40]!r}")


def read_toml_subset(text: str, what: str) -> dict[str, Any]:
    """Lines end only where TOML ends them, at LF or CRLF; a line that still
    holds a ``TOML_FORBIDDEN`` character is refused with its number, so the
    subset never sees a line, key or header that TOML reads as comment text."""
    segments = text.split("\n")
    lines: list[str] = []
    for number, segment in enumerate(segments, 1):
        if number < len(segments) and segment.endswith("\r"):
            segment = segment[:-1]
        forbidden = TOML_FORBIDDEN.search(segment)
        if forbidden:
            raise Refusal(
                f"{what} line {number}: control character or non-TOML line break "
                f"U+{ord(forbidden.group()):04X} (TOML ends lines only at LF or CRLF)"
            )
        lines.append(segment)
    doc: dict[str, Any] = {}
    target: dict[str, Any] = doc
    array_tables: set[str] = set()
    for number, raw in enumerate(lines, 1):
        line = _strip_comment(raw).strip()
        if not line:
            continue
        if line.startswith("[["):
            if not line.endswith("]]"):
                raise Refusal(f"{what} line {number}: malformed array-of-tables header")
            name = line[2:-2].strip()
            if not re.fullmatch(r"[A-Za-z0-9_-]+", name):
                raise Refusal(f"{what} line {number}: unsupported array-of-tables name {name!r}")
            if name in doc and name not in array_tables:
                raise Refusal(f"{what} line {number}: `{name}` is already defined")
            rows = doc.setdefault(name, [])
            array_tables.add(name)
            table: dict[str, Any] = {}
            rows.append(table)
            target = table
            continue
        if line.startswith("["):
            if not line.endswith("]"):
                raise Refusal(f"{what} line {number}: malformed table header")
            name = line[1:-1].strip()
            if not re.fullmatch(r"[A-Za-z0-9_-]+(?:\.[A-Za-z0-9_-]+)?", name):
                raise Refusal(f"{what} line {number}: unsupported table name {name!r}")
            parent, dot, child = name.partition(".")
            if dot:
                holder = doc.get(parent)
                base = holder[-1] if isinstance(holder, list) and holder else holder
                if not isinstance(base, dict):
                    raise Refusal(f"{what} line {number}: sub-table `{name}` has no parent table")
                if child in base:
                    raise Refusal(f"{what} line {number}: duplicate table `{name}`")
                table = base[child] = {}
            else:
                if name in doc:
                    raise Refusal(f"{what} line {number}: duplicate table `{name}`")
                table = doc[name] = {}
            target = table
            continue
        key, sep, value = line.partition("=")
        key = key.strip()
        if not sep or not key or not re.fullmatch(r"[A-Za-z0-9_-]+", key):
            raise Refusal(f"{what} line {number}: line outside the ledger TOML subset")
        if key in target:
            raise Refusal(f"{what} line {number}: duplicate key `{key}`")
        target[key] = _toml_value(value.strip(), what, number)
    return doc


def read_tree_toml(cx: Context, relative: str) -> dict[str, Any]:
    return read_toml_subset(cx.tree_text(relative), relative)


# ── shared readers over the upstream-Lean instrument ────────────────────────


def upstream_pin(cx: Context) -> tuple[dict[str, Any], str, str, dict[str, Any]]:
    """``(baseline, commit sha, version, manifest)`` — the baseline's
    ``[upstream]`` pin and the corpus MANIFEST it names, both pin-bound."""
    baseline = read_tree_toml(cx, UPSTREAM_BASELINE)
    upstream = baseline.get("upstream")
    if not isinstance(upstream, dict):
        raise Refusal("baseline.toml has no [upstream] table")
    if upstream.get("channel") != "lean4":
        raise Refusal(f"baseline [upstream] channel must be \"lean4\", got {upstream.get('channel')!r}")
    revision = require_str(upstream.get("revision"), "baseline [upstream] revision")
    match = UPSTREAM_REVISION.fullmatch(revision)
    if match is None:
        raise Refusal(f"baseline [upstream] revision must be `leanprover/lean4:<40 hex commit>`, got {revision!r}")
    version = require_str(upstream.get("version"), "baseline [upstream] version")
    if not LEAN_VERSION.fullmatch(version):
        raise Refusal(f"baseline [upstream] version must be `vX.Y.Z[-rcN]`, got {version!r}")
    manifest_path = require_str(upstream.get("manifest_path"), "baseline [upstream] manifest_path")
    plain_relative(manifest_path, "baseline [upstream] manifest_path")
    manifest = load_json_object(cx.tree_file(f"{CLEAN_ROOT}/{manifest_path}"))
    return baseline, match.group(1), version, manifest


def manifest_files(manifest: dict[str, Any]) -> dict[str, str]:
    checksums = manifest.get("checksums")
    if not isinstance(checksums, dict) or not checksums:
        raise Refusal("corpus MANIFEST has no per-file `checksums`")
    for name, checksum in checksums.items():
        if not isinstance(name, str) or not name.endswith(".lean") or len(Path(name).parts) != 1:
            raise Refusal(f"corpus MANIFEST entry {name!r} is not a plain .lean file name")
        if not isinstance(checksum, str) or not MANIFEST_CHECKSUM.fullmatch(checksum):
            raise Refusal(f"corpus MANIFEST checksum for {name!r} is not `sha256:<64 hex>`")
    return checksums


def ledger_rows(cx: Context) -> list[dict[str, Any]]:
    ledger = read_tree_toml(cx, UPSTREAM_EXCEPTIONS)
    unknown = sorted(set(ledger) - {"schema_version", "exceptions"})
    if unknown:
        raise Refusal(f"exceptions.toml carries unknown top-level keys or tables {unknown[:3]}: a ledger is schema_version and exceptions only")
    require_str(ledger.get("schema_version"), "exceptions.toml schema_version")
    rows = ledger.get("exceptions", [])
    if not isinstance(rows, list):
        raise Refusal("exceptions.toml `exceptions` must be an array of tables")
    for index, row in enumerate(rows):
        if not isinstance(row, dict):
            raise Refusal(f"exceptions.toml row {index} is not a table")
        missing = [field for field in LEDGER_FIELDS if not isinstance(row.get(field), str) or not row[field].strip()]
        if missing:
            raise Refusal(f"exceptions.toml row {row.get('id', index)!r} lacks {missing}")
    return rows


def active_ledger_rows(cx: Context) -> dict[str, dict[str, Any]]:
    """Active ledger rows keyed by probe id, however they are classified —
    the caller decides what a row may cover."""
    active: dict[str, dict[str, Any]] = {}
    for row in ledger_rows(cx):
        if row["status"] == "active":
            active.setdefault(row["probe_id"], row)
    return active


def corpus_probes(cx: Context) -> dict[str, dict[str, Any]]:
    """The probes ``corpus.toml`` pins, keyed by id, each with file / decl /
    expected — the population a suite run must biject."""
    corpus = read_tree_toml(cx, UPSTREAM_CORPUS)
    unknown = sorted(set(corpus) - {"schema_version", "probes"})
    if unknown:
        raise Refusal(f"corpus.toml carries unknown top-level keys or tables {unknown[:3]}: a corpus is schema_version and probes only")
    require_str(corpus.get("schema_version"), "corpus.toml schema_version")
    probes = corpus.get("probes", [])
    if not isinstance(probes, list):
        raise Refusal("corpus.toml `probes` must be an array of tables")
    pinned: dict[str, dict[str, Any]] = {}
    for index, probe in enumerate(probes):
        if not isinstance(probe, dict):
            raise Refusal(f"corpus.toml probe {index} is not a table")
        for field in ("id", "file", "decl", "expected"):
            require_str(probe.get(field), f"corpus.toml probe {probe.get('id', index)!r} {field}")
        if probe["expected"] not in PINNABLE_OUTCOMES:
            raise Refusal(f"corpus.toml probe {probe['id']!r} pins expected {probe['expected']!r}, which is not pinnable")
        if probe["id"] in pinned:
            raise Refusal(f"corpus.toml pins probe {probe['id']!r} twice")
        pinned[probe["id"]] = probe
    return pinned


# ── conjunct verifiers ──────────────────────────────────────────────────────
#
# Each takes the resolved artifact path and the context and either returns
# None (conjunct holds against this artifact) or raises Refusal.


def verify_pinned_upstream_lean_revision(path: Path, cx: Context) -> None:
    """Artifact: the tracked upstream-Lean baseline itself,
    ``first-party/clean/tests/upstream-lean/baseline.toml`` — what
    ``run_upstream_lean.py`` reads — bound by its own path AND pin.  Checks
    that ``[upstream]`` pins ``leanprover/lean4:<40 hex>`` with a ``vX.Y.Z``
    version; the corpus MANIFEST it names pins the SAME commit and version
    with one ``sha256:`` checksum per ``.lean`` file and a matching
    ``file_count``; the corpus directory on disk holds exactly those files,
    each pin-bound and hashing to its checksum; the baseline's own
    ``[corpus] selection_is_representative`` is true; and the Clean
    toolchain pin ``first-party/clean/lean-toolchain`` names that same
    version, the owner admission revision and the receipt corpus revision;
    baseline surface statuses must all be compatible.  Two pins that can
    disagree are not a pin.  Even agreement is structural only: a complete
    upstream tests/lean tree enumeration is not independently available.
    Independent defects are ACCUMULATED so every live one is named.
    Measured 2026-09-16: ``selection_is_representative = false`` and
    ``v4.30.0-rc2`` against ``v4.27.0``."""
    cx.require_tree_artifact(path, UPSTREAM_BASELINE)
    baseline, commit, version, manifest = upstream_pin(cx)
    upstream = baseline["upstream"]
    file_count = upstream.get("file_count")
    if type(file_count) is not int or file_count < 1:
        raise Refusal("baseline [upstream] file_count must be a positive integer")
    corpus_path = require_str(upstream.get("corpus_path"), "baseline [upstream] corpus_path")
    plain_relative(corpus_path, "baseline [upstream] corpus_path")
    files = manifest_files(manifest)
    problems: list[str] = []
    if manifest.get("lean4_commit") != commit:
        problems.append(
            f"corpus MANIFEST pins lean4_commit {manifest.get('lean4_commit')!r} but the baseline pins {commit!r}; "
            f"two pins that can disagree are not a pin"
        )
    if manifest.get("lean4_version") != version:
        problems.append(f"corpus MANIFEST lean4_version {manifest.get('lean4_version')!r} disagrees with the baseline {version!r}")
    if manifest.get("tests_path") != "tests/lean":
        problems.append(f"corpus MANIFEST tests_path is {manifest.get('tests_path')!r}, not the upstream tests/lean suite")
    if type(manifest.get("file_count")) is not int:
        problems.append(f"corpus MANIFEST file_count must be an integer, got {manifest.get('file_count')!r}")
    elif manifest["file_count"] != len(files) or file_count != len(files):
        problems.append(f"file_count disagrees: baseline {file_count}, MANIFEST {manifest.get('file_count')}, checksums {len(files)}")
    # The corpus on disk: exactly the pinned files, each pin-bound, each hashing to its checksum.
    corpus_rel = f"{CLEAN_ROOT}/{corpus_path}"
    cx.refuse_symlinks(corpus_rel)
    corpus_dir = cx.root / corpus_rel
    corpus_info = lstat_or_none(corpus_dir, corpus_rel)
    listing: list[str] | None = None
    if corpus_info is None or not stat.S_ISDIR(corpus_info.st_mode):
        problems.append(f"corpus directory {corpus_rel} is absent: the pinned suite is not on disk")
    else:
        try:
            listing = sorted(entry.name for entry in corpus_dir.iterdir())
        except OSError as exc:
            problems.append(f"corpus directory {corpus_rel} cannot be listed: {exc.strerror or exc}")
    if listing is not None:
        on_disk = [name for name in listing if name.endswith(".lean")]
        missing = sorted(set(files) - set(on_disk))
        extra = sorted(set(on_disk) - set(files))
        if missing or extra:
            problems.append(
                f"corpus directory holds {len(on_disk)} .lean files but the MANIFEST pins {len(files)}"
                + (f"; missing {missing[:3]}" if missing else "") + (f"; unpinned {extra[:3]}" if extra else "")
            )
        try:
            present = [name for name in sorted(files) if name in set(on_disk)]
            paths = cx.tree_files([f"{corpus_rel}/{name}" for name in present])
            mismatched = [name for name, file in zip(present, paths) if "sha256:" + sha256_of(file) != files[name]]
            if mismatched:
                problems.append(
                    f"{len(mismatched)} corpus file(s) do not hash to their MANIFEST checksum (first: {mismatched[:3]}): "
                    f"the pin does not describe the corpus on disk"
                )
        except Refusal as exc:
            problems.append(str(exc))
    corpus = baseline.get("corpus")
    if not isinstance(corpus, dict) or corpus.get("selection_is_representative") is not True:
        defect = corpus.get("selection_defect") if isinstance(corpus, dict) else None
        problems.append(
            "baseline [corpus] selection_is_representative is not true: the pinned corpus is not the full upstream suite"
            + (f" — {defect}" if isinstance(defect, str) and defect else "")
        )
    entries = baseline.get("entries")
    if not isinstance(entries, list) or len(entries) != len(BASELINE_SURFACES):
        problems.append("baseline must enumerate exactly the parser, elaborator and trust_ir surfaces")
    else:
        observed: dict[str, Any] = {}
        for entry in entries:
            if not isinstance(entry, dict) or not isinstance(entry.get("id"), str) or entry["id"] in observed:
                problems.append("baseline has a malformed or duplicate Lean surface entry")
                break
            observed[entry["id"]] = entry
        if set(observed) != set(BASELINE_SURFACES) or any(
            observed[entry_id].get("surface") != surface
            for entry_id, surface in BASELINE_SURFACES.items()
            if entry_id in observed
        ):
            problems.append("baseline Lean surface identities are incomplete or unknown")
        for entry_id, entry in observed.items():
            if entry.get("status") != "compatible":
                problems.append(f"baseline {entry_id} status {entry.get('status')!r} is not compatible")
    try:
        owner_revision = cx.owner_lean_revision()
        if commit != owner_revision:
            problems.append(
                f"baseline upstream Lean revision {commit} disagrees with the owner admission and receipt corpus revision {owner_revision}"
            )
    except Refusal as exc:
        problems.append(str(exc))
    try:
        toolchain, tag = cx.lean_toolchain_pin()
        if tag != version:
            problems.append(
                f"{LEAN_TOOLCHAIN_PIN} pins {toolchain!r} but the upstream baseline pins {version!r}; "
                f"align the two pins (bump the baseline + MANIFEST, or the toolchain) — two pins that can disagree are not a pin"
            )
    except Refusal as exc:
        problems.append(str(exc))
    if problems:
        raise Refusal("; ".join(problems))
    raise Refusal(
        "the baseline, MANIFEST, toolchain and owner revision agree locally, but no independent enumeration "
        "of the complete upstream Lean tests/lean tree binds this denominator; selection_is_representative "
        "alone is not G2 completeness evidence"
    )


def verify_vanilla_lean_build(path: Path, cx: Context) -> None:
    """Artifact: a ``trust.lean.ir-library/v1`` envelope — what
    ``targo trust build FILE.lean --emit=trust-ir --out lib.json`` writes
    (``targo-trust/src/lean_build.rs``), the only ``.lean`` BUILD path as
    opposed to ``targo trust check``.  Judged by the shape the instrument
    actually writes and its own importer ``decode_and_revalidate`` accepts:
    ``native_codegen`` is the STRING ``"unavailable"`` (anything else is not
    a v1 envelope), every source is a ``.lean`` file PIN-BOUND under the tree
    whose bytes hash to the recorded ``sha256`` (which is also the digest of
    the recorded text), ``module_sha256`` IS the digest of the decoded
    ``module_binary_hex``, the owned declarations are exactly the kernel-only
    ones plus one digest-bound body binding per computational declaration,
    and ``limitations`` is the non-empty list every real envelope carries,
    ending with the instrument's own disclosure that serialized bindings are
    not G1-G8 completion evidence.  That disclosure is the instrument's
    refusal: the conjunct is STRUCTURALLY RED under v1 — a real envelope
    reads red for the reason the instrument states, and a hand-authored one
    cannot pass because it cannot both carry the v1 disclosure and omit it.
    G2 needs a v2 envelope with a producer binding
    ``{tool_source_revision, artifact_sha256 ∈ the toolchain manifest}`` and
    an empty limitations list."""
    doc = load_json_object(path)
    require_schema(doc, IR_LIBRARY_SCHEMA)
    if doc.get("authority") != IR_LIBRARY_AUTHORITY:
        raise Refusal(f"envelope authority must be {IR_LIBRARY_AUTHORITY!r}, got {doc.get('authority')!r}")
    codegen = doc.get("native_codegen")
    if codegen != "unavailable":
        raise Refusal(
            f"native_codegen is {codegen!r}: not a {IR_LIBRARY_SCHEMA} envelope — lean_build.rs writes native_codegen as the "
            f"string \"unavailable\" and its importer refuses anything else; a hand-authored executable record is not the instrument's"
        )
    for source in nonempty_list(doc, "sources"):
        if not isinstance(source, dict):
            raise Refusal("sources must be objects")
        source_path = require_str(source.get("path"), "source path")
        if not source_path.endswith(".lean"):
            raise Refusal(f"source {source_path!r} is not a .lean file: vanilla Lean must enter as Lean, not as a Rust token tree")
        text = source.get("source")
        if not isinstance(text, str):
            raise Refusal(f"source {source_path!r} records no source text")
        recorded = require_hex(source.get("sha256"), f"source {source_path!r} sha256")
        try:
            encoded = text.encode("utf-8")
        except UnicodeEncodeError:
            raise Refusal(f"source {source_path!r} text is not encodable UTF-8 (a lone surrogate): no file holds it") from None
        actual = hashlib.sha256(encoded).hexdigest()
        if recorded != actual:
            raise Refusal(f"source {source_path!r} sha256 {recorded[:12]}… is not the digest of its recorded text {actual[:12]}…")
        on_disk = sha256_of(cx.tree_file(source_path))
        if on_disk != recorded:
            raise Refusal(f"source {source_path!r} in the tree hashes {on_disk[:12]}…, not the envelope's {recorded[:12]}…: the envelope was not built from this tree")
    require_hex(doc.get("source_closure_sha256"), "source_closure_sha256")
    require_hex(doc.get("owned_declarations_sha256"), "owned_declarations_sha256")
    require_str(doc.get("module_stable_digest"), "module_stable_digest")
    binary_hex = doc.get("module_binary_hex")
    if not isinstance(binary_hex, str) or not binary_hex or len(binary_hex) % 2 or not re.fullmatch(r"[0-9a-f]+", binary_hex):
        raise Refusal("module_binary_hex must be non-empty lowercase hex of even length")
    module_sha256 = require_hex(doc.get("module_sha256"), "module_sha256")
    actual_module = hashlib.sha256(bytes.fromhex(binary_hex)).hexdigest()
    if module_sha256 != actual_module:
        raise Refusal(f"module_sha256 {module_sha256[:12]}… is not the digest of module_binary_hex {actual_module[:12]}…")
    owned = {canonical(name) for name in nonempty_list(doc, "owned_declarations")}
    kernel_only_raw = doc.get("kernel_only_declarations")
    if not isinstance(kernel_only_raw, list):
        raise Refusal("`kernel_only_declarations` must be a list")
    kernel_only = {canonical(name) for name in kernel_only_raw}
    body_declarations: set[str] = set()
    function_ids: set[int] = set()
    for body in nonempty_list(doc, "bodies"):
        if not isinstance(body, dict):
            raise Refusal("bodies must be objects")
        declaration = canonical(body.get("declaration"))
        if declaration in body_declarations:
            raise Refusal(f"declaration {declaration} carries two body bindings")
        body_declarations.add(declaration)
        function_id = body.get("function_id")
        if type(function_id) is not int or function_id < 0 or function_id in function_ids:
            raise Refusal(f"body {declaration} function_id must be a unique non-negative integer")
        function_ids.add(function_id)
        require_hex(body.get("kernel_payload_sha256"), f"body {declaration} kernel_payload_sha256")
        require_str(body.get("subject_digest"), f"body {declaration} subject_digest")
        require_str(body.get("carrier"), f"body {declaration} carrier")
        require_str(body.get("method"), f"body {declaration} method")
    if not kernel_only <= owned or not body_declarations <= owned:
        raise Refusal("kernel-only declarations and body bindings must name owned declarations")
    if kernel_only & body_declarations:
        raise Refusal(f"declarations both kernel-only and body-bound: {sorted(kernel_only & body_declarations)[:4]}")
    unbound = owned - kernel_only - body_declarations
    if unbound:
        raise Refusal(f"computational declarations without a Trust-IR body: {sorted(unbound)[:4]}")
    limitations = doc.get("limitations")
    if not isinstance(limitations, list) or not all(isinstance(line, str) for line in limitations):
        raise Refusal("`limitations` must be a list of strings")
    if not limitations or limitations[-1] != IR_LIBRARY_COMPLETION_DISCLOSURE:
        raise Refusal(
            f"limitations {'is empty' if not limitations else 'do not end with the instrument disclosure'}: not a {IR_LIBRARY_SCHEMA} "
            f"envelope — lean_build.rs's revalidator requires the recomputed limitations constant, which every real envelope carries "
            f"and which ends {IR_LIBRARY_COMPLETION_DISCLOSURE!r}"
        )
    raise Refusal(
        f"native_codegen is \"unavailable\" and the envelope discloses {len(limitations)} limitations, the last being the instrument's "
        f"own refusal: {limitations[-1]!r} (first: {limitations[0][:120]!r}); the .lean build path is a library lane — G2 needs a v2 "
        f"envelope with a producer binding {{tool_source_revision, artifact_sha256 in the toolchain manifest}} and an empty limitations list"
    )


def verify_external_olean_and_dependency_graphs(path: Path, cx: Context) -> None:
    """Artifact schema ``trust.two-language.lean-olean-import-graph/v1``: what
    an ADMITTING ``.olean`` loader would write — one row per module of the
    import closure with the module's on-disk ``.olean`` digest and its import
    edges, every import loaded into the kernel environment, against the
    pinned toolchain.  The shape rules (the contract): every module
    ``admission: "loaded"`` with a unique name; every ``olean``-origin module
    a 64-hex ``olean_sha256`` and a ``.olean`` path; every import edge inside
    the graph (closed) and the graph acyclic (computed here); at least one
    external module importing another external module; ``toolchain`` equal
    to the tree's pin.  The diagnostic ``trust.lean.olean-closure-observation/v1``
    (authority diagnostic-only-no-import-admission) is refused by name.
    NO INSTRUMENT PRODUCES THIS SCHEMA: ``targo trust check`` records
    ``external_olean_imports: "unsupported"`` and the census admits nothing,
    so after the shape rules the conjunct refuses UNCONDITIONALLY until an
    admitting loader exists and this checker binds its producer."""
    doc = load_json_object(path)
    if doc.get("schema") == OLEAN_DIAGNOSTIC_SCHEMA:
        raise Refusal(
            f"artifact is the diagnostic {OLEAN_DIAGNOSTIC_SCHEMA} (authority diagnostic-only-no-import-admission); "
            f"G2 needs an admitting loader's {OLEAN_IMPORT_GRAPH_SCHEMA}"
        )
    require_schema(doc, OLEAN_IMPORT_GRAPH_SCHEMA)
    if doc.get("authority") != OLEAN_IMPORT_GRAPH_AUTHORITY:
        raise Refusal(f"authority must be {OLEAN_IMPORT_GRAPH_AUTHORITY!r}, got {doc.get('authority')!r}")
    toolchain, _ = cx.lean_toolchain_pin()
    if doc.get("toolchain") != toolchain:
        raise Refusal(f"graph toolchain {doc.get('toolchain')!r} is not the pinned {toolchain!r}")
    modules: dict[str, dict[str, Any]] = {}
    for module in nonempty_list(doc, "modules"):
        if not isinstance(module, dict):
            raise Refusal("modules must be objects")
        name = require_str(module.get("name"), "module name")
        if name in modules:
            raise Refusal(f"module {name!r} appears twice")
        if module.get("origin") not in ("source", "olean"):
            raise Refusal(f"module {name!r} origin must be \"source\" or \"olean\"")
        if module.get("admission") != "loaded":
            raise Refusal(f"module {name!r} admission is {module.get('admission')!r}, not \"loaded\": observed is not admitted")
        if not isinstance(module.get("imports"), list) or not all(isinstance(i, str) for i in module["imports"]):
            raise Refusal(f"module {name!r} imports must be a list of module names")
        if module["origin"] == "olean":
            require_hex(module.get("olean_sha256"), f"module {name!r} olean_sha256")
            if not require_str(module.get("path"), f"module {name!r} path").endswith(".olean"):
                raise Refusal(f"module {name!r} path is not an .olean file")
        modules[name] = module
    for name, module in modules.items():
        for target in module["imports"]:
            if target not in modules:
                raise Refusal(f"module {name!r} imports {target!r}, which is not in the graph: the closure is open")
    state: dict[str, int] = {}
    for name in modules:
        if state.get(name) == 2:
            continue
        state[name] = 1
        path = [name]
        active = {name: 0}
        stack = [(name, iter(modules[name]["imports"]))]
        while stack:
            owner, imports = stack[-1]
            target = next(imports, None)
            if target is None:
                state[owner] = 2
                stack.pop()
                path.pop()
                active.pop(owner)
            elif state.get(target) == 1:
                cycle = path[active[target]:] + [target]
                raise Refusal(f"import cycle: {' -> '.join(cycle)}")
            elif state.get(target) != 2:
                state[target] = 1
                active[target] = len(path)
                path.append(target)
                stack.append((target, iter(modules[target]["imports"])))
    external = [m for m in modules.values() if m["origin"] == "olean"]
    if not external:
        raise Refusal("the graph has no external .olean module: no external import was exercised")
    if not any(modules[t]["origin"] == "olean" for m in external for t in m["imports"]):
        raise Refusal("no external module imports another external module: a single leaf import is not a Mathlib-style dependency graph")
    raise Refusal(
        f"no instrument produces {OLEAN_IMPORT_GRAPH_SCHEMA}: targo trust check records external_olean_imports \"unsupported\" and "
        f"trust_clean::olean_census is diagnostic-only-no-import-admission; this conjunct reads red until an admitting .olean loader "
        f"exists and this checker binds its producer (tool_source_revision + artifact_sha256 in the toolchain manifest)"
    )


def verify_all_lean_computational_declarations_inventoried(path: Path, cx: Context) -> None:
    """Artifact: a ``trust.lean.check-kernel-roster/v1`` census — what
    ``targo trust check|build FILE.lean --census roster.json`` writes
    (``targo-trust/src/lean_cli/census.rs`` around ``trust-certify``'s
    ``trust.lean.kernel-roster/v1``).  The instrument classifies every owned
    kernel identity and then DISCLOSES that it is diagnostic (``authority:
    "diagnostic-only"`` on both the wrapper and the roster), that its
    denominator is unverified and its runtime body universe unmeasured.
    Holds iff both ``authority`` fields carry the admitting value
    ``post-lowering-inventory`` (refused by name otherwise — the instrument's
    own diagnostic row is not inventory authority); ``tool_source_revision``
    is the accepted source revision; every ``requested_files`` entry and
    every ``source_graph.sources[]`` path is PIN-BOUND under the tree and
    hashes to its recorded ``sha256``; the closure was accepted with no
    unresolved import and no rejected check; every declaration is classified,
    attributed, digest-bound and free of unresolved dependencies;
    ``denominator_status`` is ``denominator_verified`` and
    ``runtime_body_universe`` is ``measured`` in roster AND source graph; and
    every row's ``runtime_classification`` is ``kernel-only`` (proof-only /
    type-family) or a ``{"trust_ir_body": {function_id, subject_digest}}``
    record (computational / primitive candidates).  These are structural
    diagnostics only: no instrument writes the admitting authority or binds
    the denominator to the owner-admitted Lean population, so even a shaped
    report refuses at the end."""
    doc = load_json_object(path)
    require_schema(doc, KERNEL_ROSTER_SCHEMA)
    authority = doc.get("authority")
    if authority != CENSUS_INVENTORY_AUTHORITY:
        raise Refusal(
            f"census authority is {authority!r}: the instrument's own row says it is diagnostic (census.rs writes "
            f"{CENSUS_DIAGNOSTIC_AUTHORITY!r}); G2 needs an inventory whose authority is {CENSUS_INVENTORY_AUTHORITY!r}, which no instrument writes yet"
        )
    roster = doc.get("kernel_roster")
    if not isinstance(roster, dict):
        raise Refusal("`kernel_roster` must be an object")
    if roster.get("status") == "not-collected":
        raise Refusal("kernel_roster.status is \"not-collected\": the check refused before a roster could be taken")
    require_schema(roster, KERNEL_ROSTER_INNER_SCHEMA)
    if roster.get("authority") != CENSUS_INVENTORY_AUTHORITY:
        raise Refusal(
            f"kernel_roster.authority is {roster.get('authority')!r} (clean_census.rs writes {CENSUS_DIAGNOSTIC_AUTHORITY!r}); "
            f"G2 needs {CENSUS_INVENTORY_AUTHORITY!r}, which no instrument writes yet"
        )
    revision = doc.get("tool_source_revision")
    if revision != cx.source_revision:
        raise Refusal(f"tool_source_revision {revision!r} is not the accepted source revision {cx.source_revision!r}")
    for requested in nonempty_list(doc, "requested_files"):
        cx.tree_file(require_str(requested, "requested file"))
    if roster.get("check_rejected") is not False:
        raise Refusal("kernel_roster.check_rejected is not false: a rejected check inventories nothing")
    if roster.get("kernel_classification_schema") != KERNEL_CLASSIFICATION_SCHEMA:
        raise Refusal(f"kernel_classification_schema must be {KERNEL_CLASSIFICATION_SCHEMA!r}")
    for row in nonempty_list(roster, "declarations"):
        if not isinstance(row, dict):
            raise Refusal("declarations must be objects")
        name = require_str(row.get("name"), "declaration name")
        require_hex(row.get("kernel_payload_sha256"), f"declaration {name!r} kernel_payload_sha256")
        if row.get("ownership") not in ("elaborator-introduces", "kernel-inductive-owner"):
            raise Refusal(f"declaration {name!r} ownership is {row.get('ownership')!r}: an unattributed identity is not inventoried")
        if row.get("unresolved_dependencies") != []:
            raise Refusal(f"declaration {name!r} has unresolved dependencies: {row.get('unresolved_dependencies')}")
        classification = row.get("kernel_classification")
        kind = classification.get("kind") if isinstance(classification, dict) else None
        if not isinstance(kind, str) or kind not in KERNEL_KINDS:
            reason = classification.get("reason") if isinstance(classification, dict) else None
            raise Refusal(f"declaration {name!r} kernel classification is {kind!r} ({reason!r}): every declaration must be classified")
        runtime = row.get("runtime_classification")
        expected = KERNEL_KINDS[kind]
        if runtime == "unmeasured":
            raise Refusal(
                f"declaration {name!r} ({kind}) runtime_classification is \"unmeasured\": the roster is written before lowering; "
                f"G2 needs a post-lowering inventory that records {expected!r} per row"
            )
        if expected == "kernel-only":
            if runtime != "kernel-only":
                raise Refusal(f"declaration {name!r} ({kind}) must stay kernel-only, got {runtime!r}")
            continue
        body = runtime.get("trust_ir_body") if isinstance(runtime, dict) else None
        if not isinstance(body, dict):
            raise Refusal(f"declaration {name!r} ({kind}) carries no trust_ir_body record")
        if type(body.get("function_id")) is not int or body["function_id"] < 0:
            raise Refusal(f"declaration {name!r} trust_ir_body.function_id must be a non-negative integer")
        digest = body.get("subject_digest")
        if not isinstance(digest, str) or not PREFIXED_DIGEST.fullmatch(digest):
            raise Refusal(f"declaration {name!r} trust_ir_body.subject_digest must be a 64-hex digest")
    if roster.get("unattributed_declarations") != 0:
        raise Refusal(f"unattributed_declarations is {roster.get('unattributed_declarations')!r}, not 0")
    graph = doc.get("source_graph")
    if not isinstance(graph, dict):
        raise Refusal("`source_graph` must be an object")
    require_schema(graph, SOURCE_GRAPH_SCHEMA)
    if graph.get("source_closure_accepted") is not True:
        raise Refusal("source_graph.source_closure_accepted is not true")
    for source in nonempty_list(graph, "sources"):
        if not isinstance(source, dict):
            raise Refusal("source_graph.sources must be objects")
        source_path = require_str(source.get("path"), "checked source path")
        if source.get("read_status") != "read-utf8":
            raise Refusal(f"checked source {source_path!r} read_status is {source.get('read_status')!r}")
        recorded = require_hex(source.get("sha256"), f"checked source {source_path!r} sha256")
        on_disk = sha256_of(cx.tree_file(source_path))
        if on_disk != recorded:
            raise Refusal(f"checked source {source_path!r} in the tree hashes {on_disk[:12]}…, not the census's {recorded[:12]}…")
    if graph.get("unresolved_imports") != []:
        raise Refusal(f"source_graph.unresolved_imports is not empty: {graph.get('unresolved_imports')}")
    if graph.get("tool_path_bytes_stable") is not True:
        raise Refusal("source_graph.tool_path_bytes_stable is not true: the tool image changed during the census")
    for holder, label in ((roster, "kernel_roster"), (graph, "source_graph")):
        if holder.get("denominator_status") != "denominator_verified":
            raise Refusal(
                f"{label}.denominator_status is {holder.get('denominator_status')!r}: the instrument discloses its denominator "
                f"is unverified — G2 needs \"denominator_verified\""
            )
        if holder.get("runtime_body_universe") != "measured":
            raise Refusal(f"{label}.runtime_body_universe is {holder.get('runtime_body_universe')!r}, not \"measured\"")
    raise Refusal(
        "structurally favorable census is not G2 inventory authority: no independent producer binds "
        "post-lowering bodies and the complete denominator to the owner-admitted Lean population"
    )


def verify_zero_upstream_lean_semantic_regressions(path: Path, cx: Context) -> None:
    """Artifact: the JSON a run of the pinned upstream-Lean suite writes —
    ``first-party/clean/tests/upstream-lean/run_upstream_lean.py --json``
    (``{summary, results, findings}``, one result per pinned probe carrying
    the outcome ``classify_run`` observed) — judged against the TRACKED
    ``corpus.toml``.  Seededness is COMPUTED from the corpus (a run over an
    unseeded corpus measures nothing, whatever its summary says); a stdout
    capture that begins with the runner's UNSEEDED banner is refused with
    the seeding fix.  Holds iff the results biject the pinned probes on
    (id, file, decl, expected), ``summary.probes``/``executed``/``matched_pin``
    equal the counts computed here, the run raised no finding, every probe
    is pinned ``expected: "lowers"`` (pinning ``rejected``/``empty`` records a
    regression as normal), every observed outcome is ``lowers`` unless an
    ACTIVE row of the tracked exceptions ledger names that probe with that
    observation under a non-applicable kind (``crashed`` is never covered),
    at least one probe lowered, and every ``.lean`` file of the pinned
    MANIFEST is covered — the pinned suite.  These are structural diagnostics
    only: the run JSON carries no producer record or owner-policy binding for
    waived rows, so even a shaped run refuses at the end."""
    try:
        text = path.read_text(encoding="utf-8")
    except (OSError, UnicodeError) as exc:
        raise Refusal(f"artifact is unreadable: {exc}") from exc
    if not text.lstrip().startswith("{") and UNSEEDED_BANNER in text:
        raise Refusal(
            f"artifact is a stdout capture of run_upstream_lean.py that begins with its UNSEEDED banner: the corpus measured nothing; "
            f"seed it ({SEED_COMMAND}, review every proposed row, commit corpus.toml), rerun, and bind the pure JSON"
        )
    doc = load_json_object(path)
    if set(doc) != {"summary", "results", "findings"}:
        raise Refusal("artifact must be exactly the runner's {summary, results, findings} JSON")
    summary, results = doc["summary"], doc["results"]
    if not isinstance(summary, dict) or not {"probes", "executed", "matched_pin", "unseeded", "findings"} <= set(summary):
        raise Refusal("summary must carry probes, executed, matched_pin, unseeded, findings")
    if not isinstance(results, list):
        raise Refusal("`results` must be a list")
    probes = corpus_probes(cx)
    if not probes:
        raise Refusal(
            f"corpus.toml pins 0 probes but the run carries {len(results)}: the corpus is UNSEEDED — nothing was executed, so nothing "
            f"may pass; seed it ({SEED_COMMAND}), review every proposed row, commit corpus.toml"
        )
    if summary.get("unseeded") is not False:
        raise Refusal(f"summary.unseeded is {summary.get('unseeded')!r} but corpus.toml pins {len(probes)} probes")
    if type(summary.get("findings")) is not int:
        raise Refusal(f"summary.findings must be an integer count, got {summary.get('findings')!r}")
    if doc["findings"] != [] or summary.get("findings") != 0:
        raise Refusal(f"the run raised findings: {doc['findings'][:2] if isinstance(doc['findings'], list) else doc['findings']!r}")
    _, _, _, manifest = upstream_pin(cx)
    files = manifest_files(manifest)
    active = active_ledger_rows(cx)
    covered: set[str] = set()
    lowered = 0
    matched = 0
    seen_ids: set[str] = set()
    for result in results:
        if not isinstance(result, dict) or not {"probe_id", "file", "decl", "expected", "observed"} <= set(result):
            raise Refusal("every result must carry probe_id, file, decl, expected, observed")
        probe_id = require_str(result["probe_id"], "result probe_id")
        if probe_id in seen_ids:
            raise Refusal(f"probe {probe_id!r} appears twice")
        seen_ids.add(probe_id)
        probe = probes.get(probe_id)
        if probe is None:
            raise Refusal(f"probe {probe_id!r} is not pinned in corpus.toml: a run must biject the pinned probes")
        for field in ("file", "decl", "expected"):
            if result[field] != probe[field]:
                raise Refusal(f"probe {probe_id!r} {field} {result[field]!r} is not the pinned {probe[field]!r}")
        file = probe["file"]
        if file not in files:
            raise Refusal(f"probe {probe_id!r} names {file!r}, which the pinned MANIFEST does not carry")
        if probe["expected"] != "lowers":
            raise Refusal(f"probe {probe_id!r} is pinned expected={probe['expected']!r}: recording a non-lowering as normal changes the expected semantics")
        observed = result["observed"]
        if observed not in PROBE_OUTCOMES:
            raise Refusal(f"probe {probe_id!r} observed {observed!r} is not an outcome of classify_run")
        if observed == probe["expected"]:
            matched += 1
        if observed == "lowers":
            lowered += 1
        else:
            if observed == "crashed":
                raise Refusal(f"probe {probe_id!r} CRASHED: a compiler death on valid upstream Lean is a regression no row can cover")
            row = active.get(probe_id)
            if row is None:
                raise Refusal(f"probe {probe_id!r} observed {observed!r} and no active ledger row classifies it: a semantic regression")
            if row["observed"] != observed or row["kind"] not in NON_APPLICABLE_KINDS:
                raise Refusal(
                    f"probe {probe_id!r} observed {observed!r} is covered by row {row['id']!r} ({row['kind']}, waives {row['observed']!r}): "
                    f"only a non-applicable row over exactly this observation may cover it"
                )
        covered.add(file)
    unexecuted = sorted(set(probes) - seen_ids)
    if unexecuted:
        raise Refusal(f"{len(unexecuted)} pinned probe(s) have no result (first: {unexecuted[:3]}): the run did not execute the corpus")
    for field, want in (("probes", len(probes)), ("executed", len(results)), ("matched_pin", matched)):
        if type(summary.get(field)) is not int:
            raise Refusal(f"summary.{field} must be an integer count, got {summary.get(field)!r}")
        if summary.get(field) != want:
            raise Refusal(f"summary.{field} is {summary.get(field)!r} but the results compute {want}")
    if lowered == 0:
        raise Refusal("no probe lowered: a run in which every row is non-applicable is vacuous")
    uncovered = sorted(set(files) - covered)
    if uncovered:
        raise Refusal(f"{len(uncovered)} of {len(files)} pinned suite files have no probe (first: {uncovered[:3]}): the FULL suite must run")
    raise Refusal(
        "structurally favorable suite JSON is not G2 regression evidence: no independent runner/compiler "
        "identity or owner-bound non-applicable classification proves these results"
    )


def verify_non_applicable_lean_harness_rows_only(path: Path, cx: Context) -> None:
    """Artifact: the tracked exceptions ledger itself,
    ``first-party/clean/tests/upstream-lean/exceptions.toml``, bound by its
    own path and pin.  Holds iff every row carries the ledger's required
    fields, a waivable observation (``crashed`` is never waivable), a
    lifecycle status, real calendar dates with ``expires_on`` after
    ``reviewed_on``, and a NON-APPLICABLE kind — ``expected_skip`` or
    ``environmental_skip``.
    ``expected_fail`` waives a valid admitted Lean program and
    ``intentional_divergence`` changes its expected semantics; both are
    refused by name.  Every active row must name a probe the tracked
    ``corpus.toml`` pins (a live waiver over a retired probe is a ghost row).
    An empty ledger holds: it classifies nothing at all.  Every active row
    must satisfy reviewed_on <= as-of < expires_on against one captured system
    UTC date.  Host-clock integrity is an explicit TCB assumption; an
    evidence-authored as-of date cannot renew a lapsed waiver."""
    cx.require_tree_artifact(path, UPSTREAM_EXCEPTIONS)
    rows = ledger_rows(cx)
    probe_ids = set(corpus_probes(cx))
    try:
        as_of = datetime.now(timezone.utc).date()
    except (OSError, OverflowError, ValueError):
        as_of = None
    seen: set[str] = set()
    for row in rows:
        row_id = row["id"]
        if row_id in seen:
            raise Refusal(f"duplicate ledger row id {row_id!r}")
        seen.add(row_id)
        if row["kind"] in WAIVING_KINDS:
            raise Refusal(
                f"ledger row {row_id!r} is kind {row['kind']!r}: a ledger may classify a harness row non-applicable "
                f"({', '.join(NON_APPLICABLE_KINDS)}); it may not waive a valid admitted Lean program or change its expected semantics"
            )
        if row["kind"] not in NON_APPLICABLE_KINDS:
            raise Refusal(f"ledger row {row_id!r} kind {row['kind']!r} is not a non-applicable classification")
        if row["observed"] not in WAIVABLE_OUTCOMES:
            raise Refusal(f"ledger row {row_id!r} classifies observed {row['observed']!r}, which no row may cover")
        if row["status"] not in LEDGER_STATUSES:
            raise Refusal(f"ledger row {row_id!r} status {row['status']!r} is not one of {LEDGER_STATUSES}")
        dates: dict[str, date] = {}
        for field in ("reviewed_on", "expires_on"):
            if not ISO_DATE.fullmatch(row[field]):
                raise Refusal(f"ledger row {row_id!r} {field} is not YYYY-MM-DD")
            try:
                dates[field] = date.fromisoformat(row[field])
            except ValueError:
                raise Refusal(f"ledger row {row_id!r} {field} {row[field]!r} is not a real calendar date") from None
        if dates["expires_on"] <= dates["reviewed_on"]:
            raise Refusal(f"ledger row {row_id!r} expires_on {row['expires_on']} is not after reviewed_on {row['reviewed_on']}")
        if row["status"] == "active":
            if row["probe_id"] not in probe_ids:
                raise Refusal(f"active ledger row {row_id!r} names probe {row['probe_id']!r}, which corpus.toml does not pin: a ghost waiver")
            if as_of is None:
                raise Refusal(f"active ledger row {row_id!r} cannot be accepted without a system UTC date")
            if dates["reviewed_on"] > as_of:
                raise Refusal(
                    f"active ledger row {row_id!r} reviewed_on {row['reviewed_on']} is after "
                    f"system UTC date {as_of.isoformat()}: a future review cannot authorize a skip"
                )
            if dates["expires_on"] <= as_of:
                raise Refusal(
                    f"active ledger row {row_id!r} expires_on {row['expires_on']} has lapsed "
                    f"(system UTC date {as_of.isoformat()}): re-review, then renew or retire"
                )


def load_semantics_contract(cx: Context) -> dict[str, Any]:
    """Read the owner-signed semantics contract through the authority policy
    the runner hands over — inline under ``contracts.semantics`` /
    ``authority_contracts.semantics`` or as a ``{path, sha256}`` reference
    resolved and digest-checked here."""
    policy = cx.bound_json(cx.policy_path, cx.policy_sha256, "authority policy")
    contracts = policy.get("contracts")
    if not isinstance(contracts, dict) or "semantics" not in contracts:
        contracts = policy.get("authority_contracts")
    if not isinstance(contracts, dict) or "semantics" not in contracts:
        raise Refusal("authority policy has no semantics contract")
    contract = contracts["semantics"]
    if isinstance(contract, dict) and {"path", "sha256"} <= set(contract) <= {"id", "path", "sha256"}:
        raw = contract.get("path")
        if not isinstance(raw, str) or not raw or Path(raw).is_absolute():
            raise Refusal("semantics contract path must be a non-empty relative path")
        try:
            candidate = (cx.root / raw).resolve()
        except (OSError, RuntimeError, ValueError) as exc:
            # Python 3.9 raises RuntimeError for a symlink loop.
            raise Refusal(f"semantics contract path cannot be resolved: {exc}") from None
        try:
            candidate.relative_to(cx.root)
        except ValueError:
            raise Refusal("semantics contract path escapes --root") from None
        try:
            if not candidate.is_file():
                raise Refusal(f"semantics contract file does not exist: {raw}")
            actual = sha256_of(candidate)
        except OSError as exc:
            raise Refusal(f"semantics contract cannot be read: {exc.strerror or exc}") from None
        if actual != require_hex(contract.get("sha256"), "semantics contract sha256"):
            raise Refusal("semantics contract digest mismatch")
        contract = load_json_object(candidate)
    if not isinstance(contract, dict):
        raise Refusal("semantics contract must be an object")
    require_schema(contract, SEMANTICS_CONTRACT_SCHEMA)
    return contract


def verify_owner_pinned_lean_surface_and_accept_reject_parity(path: Path, cx: Context) -> None:
    """Artifact schema ``trust.two-language.lean-surface-parity/v1``: an
    accept/reject parity run over the owner-pinned Lean language surface.
    The shape rules (the contract): ``lean_language_definition`` equal — id
    AND sha256 — to the ``definitions.lean_language`` reference of the
    owner-signed semantics contract inside the authority policy,
    ``upstream_revision`` a pinned ``leanprover/lean4:<commit>``, every
    program a digest-bound source with ``upstream_verdict == trust_verdict``
    in {accept, reject}, BOTH classes exercised.  NO INSTRUMENT PRODUCES
    THIS SCHEMA (``tests/upstream-lean`` measures lowering, not acceptance
    parity), so after the shape rules the conjunct refuses UNCONDITIONALLY
    until a parity instrument exists and this checker binds its producer."""
    doc = load_json_object(path)
    require_schema(doc, SURFACE_PARITY_SCHEMA)
    contract = load_semantics_contract(cx)
    definitions = contract.get("definitions")
    pinned = definitions.get("lean_language") if isinstance(definitions, dict) else None
    if not isinstance(pinned, dict):
        raise Refusal("the semantics contract pins no lean_language definition")
    pinned_id = require_str(pinned.get("id"), "pinned lean_language id")
    pinned_digest = require_hex(pinned.get("sha256"), "pinned lean_language sha256")
    claimed = doc.get("lean_language_definition")
    if not isinstance(claimed, dict) or claimed.get("id") != pinned_id or claimed.get("sha256") != pinned_digest:
        raise Refusal(
            f"lean_language_definition {claimed!r} is not the owner-pinned surface {{id: {pinned_id!r}, sha256: {pinned_digest[:12]}…}}"
        )
    if not UPSTREAM_REVISION.fullmatch(require_str(doc.get("upstream_revision"), "upstream_revision")):
        raise Refusal("upstream_revision must be `leanprover/lean4:<40 hex commit>`")
    seen: set[str] = set()
    for program in nonempty_list(doc, "programs"):
        if not isinstance(program, dict):
            raise Refusal("programs must be objects")
        program_id = require_str(program.get("id"), "program id")
        require_hex(program.get("source_sha256"), f"program {program_id!r} source_sha256")
        upstream, trust = program.get("upstream_verdict"), program.get("trust_verdict")
        if upstream not in VERDICTS or trust not in VERDICTS:
            raise Refusal(f"program {program_id!r} verdicts must be accept or reject")
        if upstream != trust:
            raise Refusal(f"program {program_id!r}: upstream Lean {upstream}s but Trust {trust}s — accept/reject parity is broken")
        seen.add(upstream)
    missing = [v for v in VERDICTS if v not in seen]
    if missing:
        raise Refusal(f"parity run exercised no {missing} program: both classes must be exercised")
    raise Refusal(
        f"no instrument produces {SURFACE_PARITY_SCHEMA}: no accept/reject parity run over the owner-pinned Lean surface exists "
        f"(tests/upstream-lean measures lowering, not acceptance parity); this conjunct reads red until that instrument exists and "
        f"this checker binds its producer"
    )


def verify_lean_elaborator_constructor_totality(path: Path, cx: Context) -> None:
    """Artifact schema ``trust.two-language.lean-elaborator-constructor-totality/v1``:
    per constructor of the Lean 4 kernel/elaborator data families FIXED here
    (``Expr``, ``Level``, ``Literal``, ``ConstantInfo``, ``Syntax``), a
    ``handled`` verdict with digest-bound evidence.  The shape rules (the
    contract): every family lists exactly the constructors upstream Lean 4
    defines, each ``handled`` with a 64-hex ``evidence_sha256``; a missing or
    unknown constructor, or any other status, refuses by name.  NO
    INSTRUMENT PRODUCES THIS SCHEMA (no elaborator-constructor census
    exists), so after the shape rules the conjunct refuses UNCONDITIONALLY
    until one exists and this checker binds its producer."""
    doc = load_json_object(path)
    require_schema(doc, CONSTRUCTOR_TOTALITY_SCHEMA)
    families = doc.get("families")
    if not isinstance(families, dict):
        raise Refusal("`families` must be an object keyed by family name")
    unknown_families = sorted(set(families) - set(CONSTRUCTOR_FAMILIES))
    if unknown_families:
        raise Refusal(f"unknown constructor families: {unknown_families}")
    for family, constructors in CONSTRUCTOR_FAMILIES.items():
        rows = families.get(family)
        if not isinstance(rows, dict):
            raise Refusal(f"family {family!r} is absent")
        extra = sorted(set(rows) - set(constructors))
        if extra:
            raise Refusal(f"family {family!r} lists constructors Lean 4 does not define: {extra}")
        for constructor in constructors:
            row = rows.get(constructor)
            if not isinstance(row, dict):
                raise Refusal(f"constructor {family}.{constructor} is not inventoried")
            if row.get("status") != "handled":
                raise Refusal(f"constructor {family}.{constructor} is {row.get('status')!r}, not handled")
            require_hex(row.get("evidence_sha256"), f"constructor {family}.{constructor} evidence_sha256")
    raise Refusal(
        f"no instrument produces {CONSTRUCTOR_TOTALITY_SCHEMA}: no census of the Lean 4 elaborator's constructor coverage exists; "
        f"this conjunct reads red until one exists and this checker binds its producer"
    )


def verify_lean_macro_io_unsafe_ffi_surface(path: Path, cx: Context) -> None:
    """Artifact schema ``trust.two-language.lean-macro-io-unsafe-ffi-surface/v1``:
    one row per feature of the FIXED macro / IO / unsafe / FFI surface
    (``macro_rules``, ``syntax_and_macro_commands``, ``elab_commands``,
    ``notation``, ``do_notation``, ``io_actions``, ``partial_def``,
    ``unsafe_def``, ``implemented_by``, ``extern_ffi``,
    ``opaque_definitions``, ``initialize_commands``).  The shape rules (the
    contract): each ``supported`` with a lowering in {trust-ir-body,
    kernel-only} and digest-bound evidence; a missing feature or any other
    status refuses by name.  NO INSTRUMENT PRODUCES THIS SCHEMA — the
    ``.lean`` build path admits a scalar fragment and no macro, IO, unsafe or
    ``@[extern]`` declaration — so after the shape rules the conjunct refuses
    UNCONDITIONALLY until a surface census exists and this checker binds its
    producer."""
    doc = load_json_object(path)
    require_schema(doc, MACRO_IO_SURFACE_SCHEMA)
    features = doc.get("features")
    if not isinstance(features, dict):
        raise Refusal("`features` must be an object keyed by feature")
    unknown = sorted(set(features) - set(MACRO_IO_UNSAFE_FFI_FEATURES))
    if unknown:
        raise Refusal(f"unknown surface features: {unknown}")
    for feature in MACRO_IO_UNSAFE_FFI_FEATURES:
        row = features.get(feature)
        if not isinstance(row, dict):
            raise Refusal(f"feature {feature!r} is not inventoried")
        if row.get("status") != "supported":
            raise Refusal(f"feature {feature!r} is {row.get('status')!r}, not supported")
        if row.get("lowering") not in FEATURE_LOWERINGS:
            raise Refusal(f"feature {feature!r} lowering {row.get('lowering')!r} is not one of {FEATURE_LOWERINGS}")
        require_hex(row.get("evidence_sha256"), f"feature {feature!r} evidence_sha256")
    raise Refusal(
        f"no instrument produces {MACRO_IO_SURFACE_SCHEMA}: the .lean build path admits a scalar fragment and no macro, IO, unsafe "
        f"or @[extern] declaration; this conjunct reads red until a surface census exists and this checker binds its producer"
    )


VERIFIERS: dict[str, Callable[[Path, Context], None]] = {
    "pinned_upstream_lean_revision": verify_pinned_upstream_lean_revision,
    "vanilla_lean_build": verify_vanilla_lean_build,
    "external_olean_and_dependency_graphs": verify_external_olean_and_dependency_graphs,
    "all_lean_computational_declarations_inventoried": verify_all_lean_computational_declarations_inventoried,
    "zero_upstream_lean_semantic_regressions": verify_zero_upstream_lean_semantic_regressions,
    "non_applicable_lean_harness_rows_only": verify_non_applicable_lean_harness_rows_only,
    "owner_pinned_lean_surface_and_accept_reject_parity": verify_owner_pinned_lean_surface_and_accept_reject_parity,
    "lean_elaborator_constructor_totality": verify_lean_elaborator_constructor_totality,
    "lean_macro_io_unsafe_ffi_surface": verify_lean_macro_io_unsafe_ffi_surface,
}
assert tuple(VERIFIERS) == REQUIRED


# ── driver (identical protocol to the G5/G7 checkers) ───────────────────────


def resolve_ref(root: Path, ref: Any) -> tuple[Path | None, str | None]:
    """Resolve one ``{"path","sha256"}`` reference fail-closed.  Returns the
    path and, on refusal, the reason."""
    if not isinstance(ref, dict) or set(ref) != {"path", "sha256"}:
        return None, "artifact reference must be exactly {path, sha256}"
    raw, digest = ref.get("path"), ref.get("sha256")
    if not isinstance(raw, str) or not raw or "\0" in raw or Path(raw).is_absolute():
        return None, "artifact path must be a non-empty relative path"
    try:
        candidate = (root / raw).resolve()
    except (OSError, RuntimeError, ValueError) as exc:
        # Python 3.9 raises RuntimeError for a symlink loop.
        return None, f"artifact path cannot be resolved: {exc}"
    try:
        candidate.relative_to(root)
    except ValueError:
        return None, "artifact path escapes --root"
    if not isinstance(digest, str) or not HEX_DIGEST.fullmatch(digest):
        return candidate, "artifact sha256 must be a lowercase 64-hex digest"
    try:
        if not candidate.is_file():
            return candidate, f"artifact file does not exist: {raw}"
        actual = sha256_of(candidate)
    except OSError as exc:
        return candidate, f"artifact cannot be read: {exc.strerror or exc}"
    if actual != digest:
        return candidate, f"artifact hash mismatch: recorded {digest}, actual {actual}"
    return candidate, None


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--verify-evidence", required=True)
    ap.add_argument("--root", required=True)
    ap.add_argument("--receipt")
    for flag in (
        "--toolchain-manifest", "--corpus-manifest", "--subject-graph", "--linked-module",
        "--release-artifact", "--authority-policy", "--policy-authorization",
        "--acceptance-run-id", "--source-revision", "--checker-sha256", "--evidence-sha256",
        "--toolchain-sha256", "--corpus-manifest-sha256", "--subject-graph-sha256",
        "--linked-module-sha256", "--release-artifact-sha256", "--authority-policy-sha256",
        "--policy-authorization-sha256",
    ):
        ap.add_argument(flag, required=True)
    ap.add_argument("--prior-gates-root")
    args = ap.parse_args()

    root = Path(args.root).resolve()
    diagnostics: list[str] = []
    passed = True
    # G1-G7 are pre-seal facts: the receipt and the prior-gates root belong to
    # G8 only.  Their presence here is a protocol violation, refused.
    if args.receipt is not None or args.prior_gates_root is not None:
        passed = False
        diagnostics.append("G2 must not receive --receipt or --prior-gates-root (G8-only protocol inputs)")
    cx = Context(
        root,
        Path(args.authority_policy),
        args.authority_policy_sha256,
        Path(args.corpus_manifest),
        args.corpus_manifest_sha256,
        args.acceptance_run_id,
        args.source_revision,
    )

    bundle: dict[str, Any] = {}
    try:
        loaded = json.loads(Path(args.verify_evidence).read_text(encoding="utf-8"))
        if isinstance(loaded, dict):
            bundle = loaded
        else:
            diagnostics.append("evidence bundle must be a JSON object")
            passed = False
    except (OSError, UnicodeError, ValueError, RecursionError) as exc:
        diagnostics.append(f"evidence bundle unreadable: {exc}")
        passed = False
    if bundle and (
        set(bundle) != {"schema", "gate", "checker", "artifacts"}
        or bundle.get("schema") != EVIDENCE_SCHEMA
        or bundle.get("gate") != GATE
        or bundle.get("checker") != CHECKER
        or not isinstance(bundle.get("artifacts"), dict)
    ):
        diagnostics.append(f"evidence bundle header must be exactly {{schema={EVIDENCE_SCHEMA!r}, gate={GATE!r}, checker={CHECKER!r}, artifacts}}")
        passed = False
    artifacts = bundle.get("artifacts") if isinstance(bundle.get("artifacts"), dict) else {}
    unknown = sorted(set(artifacts) - set(REQUIRED))
    if unknown:
        diagnostics.append(f"evidence binds unknown check ids: {unknown}")
        passed = False

    bound: dict[Path, str] = {}
    checks: list[dict[str, Any]] = []
    for check_id in REQUIRED:
        ref = artifacts.get(check_id)
        row_ok = False
        row_artifacts: list[Any] = []
        cx.consulted = {}
        if ref is None:
            diagnostics.append(f"{check_id}: no artifact bound")
        else:
            path, refusal = resolve_ref(root, ref)
            if refusal is None and path is not None:
                if bound.get(path, ref["sha256"]) != ref["sha256"]:
                    refusal = "the same path is bound to conflicting digests"
                bound[path] = ref["sha256"]
            if refusal is not None:
                diagnostics.append(f"{check_id}: {refusal}")
            else:
                try:
                    VERIFIERS[check_id](path, cx)  # type: ignore[arg-type]
                    row_ok = True
                except Refusal as exc:
                    diagnostics.append(f"{check_id}: {exc}")
                # The bound artifact plus every tree file the conjunct consulted,
                # so the verdict can be re-verified against exactly what was read.
                row_artifacts = [ref] + [consulted for relative, consulted in cx.consulted.items() if relative != ref["path"]]
        passed = passed and row_ok
        checks.append({"id": check_id, "passed": row_ok, "artifacts": row_artifacts})

    verdict = {
        "schema": SCHEMA,
        "goal_id": GOAL,
        "gate": GATE,
        "checker": CHECKER,
        "repository_id": REPOSITORY_ID,
        "acceptance_run_id": args.acceptance_run_id,
        "checker_sha256": args.checker_sha256,
        "evidence_sha256": args.evidence_sha256,
        "source_revision": args.source_revision,
        "toolchain_sha256": args.toolchain_sha256,
        "corpus_manifest_sha256": args.corpus_manifest_sha256,
        "subject_graph_sha256": args.subject_graph_sha256,
        "linked_module_sha256": args.linked_module_sha256,
        "release_artifact_sha256": args.release_artifact_sha256,
        "authority_policy_sha256": args.authority_policy_sha256,
        "policy_authorization_sha256": args.policy_authorization_sha256,
        "prior_gates_root": args.prior_gates_root,
        "passed": passed,
        "checks": checks,
    }
    print(json.dumps(verdict))
    for line in diagnostics:
        print(f"{GATE}: {line}", file=sys.stderr)
    return 0 if passed else 1


if __name__ == "__main__":
    sys.exit(main())
