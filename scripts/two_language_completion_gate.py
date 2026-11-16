#!/usr/bin/env python3
"""Structural release-receipt gate for TRUST-TWO-LANGUAGE-100.

This is the top-level conjunction for the goal recorded in
``docs/TWO_LANGUAGE_100_PERCENT_GOAL.md``.  It does not reinterpret a producer
percentage and it does not claim to prove the semantic facts recorded by a
specialized checker.  It verifies that:

* one source revision, toolchain identity, and corpus manifest are bound, and
  the checkout (submodules included) is byte-for-byte that revision's checkout,
  apart from untracked files its ignore rules exclude, before and after the
  checkers run, and configures no program a checker's Git would start (see
  ``worktree_refusals``);
* exactly G1 through G8 have distinct, content-hashed checker evidence;
* every gate's schema-owned, source-controlled checker is content-bound and
  re-executed against that evidence, in an interpreter that reads no bytecode
  from the tree (``_isolated_python``);
* every required conjunct reported by the fresh checker run is affirmative;
* every conjunct binds at least one existing, content-hashed evidence artifact;
* no author-provided ``complete`` or ``vision_complete`` bit can mint success.

The evidence-producing checkers remain responsible for the semantics of their
artifacts.  This script is the fail-closed, checker-executing structural
conjunction over them.  An authored JSON ``passed`` bit is never sufficient.

Usage:
    python3 -I -B scripts/two_language_completion_gate.py \
        --receipt build/two-language-completion/receipt.json --root . \
        --trusted-owner-key /external/trust-owner.pub

Without -I, Python puts the script's directory first on sys.path; for a copy
inside the candidate that is its scripts/, where an ignored sourceless
``json.pyc`` would be imported in place of the standard library.  So a run
without -I and -B re-executes itself once with them before its first import
that searches sys.path (see the guard below).  A release runs an externally
pinned copy with ``--candidate-verifier`` instead.

Exit 0 means the structural receipt is complete.  Exit 1 means incomplete or
malformed evidence.  A structurally green receipt is necessary, not sufficient,
for believing a checker whose own implementation has not been reviewed.
"""

# No import may precede this guard, ``from __future__`` included: that is an
# ordinary import searched on sys.path.  sys and posix are built in, loaded
# before any script runs, and found by the built-in importer ahead of
# sys.path; os is not safe here, since under -S it is not loaded yet and, on
# Python 3.9, not frozen either.
import sys

_ISOLATED_MARKER = b"TRUST_COMPLETION_GATE_ISOLATED"

if __name__ == "__main__" and not (sys.flags.isolated and sys.flags.dont_write_bytecode):
    import posix

    if _ISOLATED_MARKER in posix.environ or not sys.executable:
        # The re-executed interpreter did not honor -I -B, or there is no
        # interpreter to re-execute: refuse rather than loop or run exposed.
        sys.exit("two_language_completion_gate: cannot start an isolated (-I -B) interpreter")
    _script = __file__ if __file__.startswith("/") else f"{posix.getcwd()}/{__file__}"
    posix.execve(
        sys.executable,
        [sys.executable, "-I", "-B", _script, *sys.argv[1:]],
        {**posix.environ, _ISOLATED_MARKER: b"1"},
    )

import argparse
import errno
import hashlib
import json
import os
import re
import stat
import subprocess
import tempfile
import zlib
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
from typing import Any, Callable, NamedTuple, Optional, Union

# The marker only ever guards the one re-execution; checkers never see it.
os.environ.pop(os.fsdecode(_ISOLATED_MARKER), None)

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



SCHEMA = "trust.two-language.completion/v2"
CHECKER_VERDICT_SCHEMA = "trust.two-language.gate-checker-verdict/v2"
VERDICT_SCHEMA = "trust.two-language.completion-verdict/v2"
GOAL_ID = "TRUST-TWO-LANGUAGE-100"
GATES = tuple(f"G{i}" for i in range(1, 9))
CHECKER_IDS = {
    "G1": "trust.two-language.g1.rust-input/v2",
    "G2": "trust.two-language.g2.lean-input/v2",
    "G3": "trust.two-language.g3.producer-totality/v2",
    "G4": "trust.two-language.g4.semantic-faithfulness/v2",
    "G5": "trust.two-language.g5.mixed-linking/v2",
    "G6": "trust.two-language.g6.proof-authority/v2",
    "G7": "trust.two-language.g7.codegen-authority/v3",
    "G8": "trust.two-language.g8.release-reproducibility/v3",
}

REPOSITORY_ID = "https://github.com/alabsystems/trust"
TOOLCHAIN_SCHEMA = "trust.two-language.toolchain-manifest/v1"
CORPUS_SCHEMA = "trust.two-language.corpus-manifest/v1"
SUBJECT_GRAPH_SCHEMA = "trust.two-language.subject-index/v3"
POLICY_SCHEMA = "trust.two-language.authority-policy/v2"
POLICY_AUTH_SCHEMA = "trust.two-language.policy-authorization/v1"
POLICY_SIGNATURE_NAMESPACE = "trust-two-language-policy"
SSH_KEYGEN = Path("/usr/bin/ssh-keygen")
# ssh-keygen reads a candidate-supplied signature file; a FIFO swapped in for
# it must not hold the gate forever.
SSH_KEYGEN_TIMEOUT = 60

AUTHORITY_CONTRACTS = {
    "admission": (
        "trust.two-language.contract.admission",
        "trust.two-language.admission-contract/v1",
    ),
    "semantics": (
        "trust.two-language.contract.semantics",
        "trust.two-language.semantics-contract/v1",
    ),
    "obligations": (
        "trust.two-language.contract.obligations",
        "trust.two-language.obligation-contract/v1",
    ),
    "proof_authority": (
        "trust.two-language.contract.proof-authority",
        "trust.two-language.proof-authority-contract/v1",
    ),
    "compatibility_surfaces": (
        "trust.two-language.contract.compatibility-surfaces",
        "trust.two-language.compatibility-surfaces-contract/v2",
    ),
    "codegen_surface": (
        "trust.two-language.contract.codegen-surface",
        "trust.two-language.codegen-surface-contract/v2",
    ),
    "acceptance_environment": (
        "trust.two-language.contract.acceptance-environment",
        "trust.two-language.acceptance-environment-contract/v1",
    ),
}
SEMANTICS_DEFINITIONS = {
    "rust_language",
    "lean_language",
    "trust_ir",
    "rust_to_trust_ir_refinement",
    "lean_to_trust_ir_refinement",
    "observation_model",
    "undefined_behavior",
    "abi_memory_model",
}
OBLIGATION_CLASSES = {
    "safety",
    "functional",
    "termination",
    "ownership",
    "unsafe_memory",
    "temporal",
}
COMPATIBILITY_CAPABILITIES = {
    "kani": {"nondeterminism", "assume", "harnesses"},
    "verus": {"ghost", "tracked", "triggers", "fuel", "broadcast", "calculations"},
    "creusot": {"prophecy", "mutable_borrows", "machine_integers", "contracts"},
    "tla_plus": {"fairness", "stuttering", "infinite_behaviors", "temporal_operators"},
}
COMPATIBILITY_IMAGE_DESTINATIONS = {
    "kani": {
        "computational": [
            "rust:nondeterministic-program",
            "trust-ir:nondeterministic-program",
        ],
        "proposition": ["lean:canonical-obligation"],
    },
    "verus": {
        "computational": ["rust:canonical-clause"],
        "proposition": ["lean:canonical-term"],
    },
    "creusot": {
        "computational": ["rust:canonical-clause"],
        "proposition": ["lean:canonical-term"],
    },
    "tla_plus": {
        "computational": [],
        "proposition": ["lean:canonical-temporal-term"],
    },
}
ACCEPTANCE_RUN_MODES = {
    "cold_build",
    "warm_build",
    "cross_crate",
    "mixed_language",
    "tests",
    "release",
}
TOOLCHAIN_ROLES = {
    "trustc",
    "rust_frontend",
    "lean_frontend",
    "clean_kernel",
    "trust_ir_producer",
    "trust_ir_linker",
    "trust_codegen",
    "trust_router",
    "proof_reconstructor",
    "runtime",
    "linker",
    "top_verifier",
    "python",
    "ssh_keygen",
}

CODEGEN_CELL_FIELDS = (
    "target_id",
    "abi_id",
    "crate_type",
    "runtime_id",
    "startup_id",
    "linker_id",
    "unwind_mode",
    "debug_mode",
    "opt_level",
    "profile_id",
)
CODEGEN_TARGET_AXIS_BY_CELL_FIELD = {
    "abi_id": "abis",
    "crate_type": "crate_types",
    "runtime_id": "runtimes",
    "startup_id": "startups",
    "linker_id": "linkers",
    "unwind_mode": "unwind_modes",
    "debug_mode": "debug_modes",
    "opt_level": "opt_levels",
    "profile_id": "profiles",
}

# The receipt cannot choose the program that decides a gate.  Each checker is
# fixed by this schema and must be tracked at the exact source revision being
# accepted.  These checkers are intentionally absent until their corresponding
# gates are implemented; therefore the current product cannot manufacture a
# green top-level receipt from hand-authored JSON.
CHECKER_PATHS = {
    "G1": "scripts/completion_gates/check_g1_rust_input.py",
    "G2": "scripts/completion_gates/check_g2_lean_input.py",
    "G3": "scripts/completion_gates/check_g3_producer_totality.py",
    "G4": "scripts/completion_gates/check_g4_semantic_faithfulness.py",
    "G5": "scripts/completion_gates/check_g5_mixed_linking.py",
    "G6": "scripts/completion_gates/check_g6_proof_authority.py",
    "G7": "scripts/completion_gates/check_g7_codegen_authority.py",
    "G8": "scripts/completion_gates/check_g8_release_reproducibility.py",
}

# These are deliberately exact sets.  Adding a new meaning to a gate requires
# a schema revision rather than silently accepting a receipt produced under a
# different definition of "100%".
REQUIRED_CHECKS: dict[str, tuple[str, ...]] = {
    "G1": (
        "pinned_upstream_rust_revision",
        "full_upstream_rust_surface",
        "all_reachable_rust_bodies_inventoried",
        "zero_upstream_rust_semantic_regressions",
        "non_applicable_rust_harness_rows_only",
        "owner_pinned_rust_surface_and_accept_reject_parity",
        "rust_frontend_constructor_totality",
        "rust_macro_build_asm_ffi_dynamic_runtime_surface",
    ),
    "G2": (
        "pinned_upstream_lean_revision",
        "vanilla_lean_build",
        "external_olean_and_dependency_graphs",
        "all_lean_computational_declarations_inventoried",
        "zero_upstream_lean_semantic_regressions",
        "non_applicable_lean_harness_rows_only",
        "owner_pinned_lean_surface_and_accept_reject_parity",
        "lean_elaborator_constructor_totality",
        "lean_macro_io_unsafe_ffi_surface",
    ),
    "G3": (
        "admitted_file_manifest_exact",
        "reachable_body_census_exact",
        "rust_zero_producer_residue",
        "lean_zero_producer_residue",
        "all_joined_modules_valid",
        "no_denominator_exclusions",
        "subject_index_roots_match",
    ),
    "G4": (
        "every_body_universally_refined",
        "finite_domain_exhaustiveness_certificates_checked",
        "sampled_agreement_not_used_as_proof",
        "refinement_certificates_biject_reachable_bodies",
        "all_lean_rows_carrier_faithful_gate",
        "no_weak_or_uninterpreted_verdict_classes",
        "owner_pinned_semantics_relation_observation_model",
        "certificates_bind_authorized_relation",
        "whole_program_contextual_refinement",
        "assumption_closure_checked",
    ),
    "G5": (
        "rust_to_lean_typed_link",
        "lean_to_rust_typed_link",
        "cross_crate_digest_rechecked_link",
        "proof_call_firewall",
        "typed_bidirectional_call_graph",
        "cross_language_value_category_matrix",
        "shared_abi_and_memory_model",
        "cross_crate_import_assumption_closure",
    ),
    "G6": (
        "source_policy_obligation_bijection",
        "zero_vacuous_weakened_or_tautological_obligations",
        "every_obligation_owned_and_typed",
        "trust_ir_native_verdict_authority",
        "every_favorable_verdict_kernel_rechecked",
        "proof_evidence_exact_digest_binding",
        "zero_open_dropped_or_unowned_obligations",
        "rust_contracts_typed_ssa_epoch_effect_identity_bound",
        "zero_design_only_contracts",
        "external_olean_transitive_trust_attested",
        "proof_dependency_closure_policy_clean",
        "obligation_certificate_bijection_matches_subject_index",
        "kani_parse_and_reject_surface",
        "kani_computational_image_exposed",
        "kani_canonical_proposition_image_exposed",
        "kani_computational_translation_validated_zero_authority",
        "kani_proposition_translation_validated_zero_authority",
        "verus_parse_and_reject_surface",
        "verus_computational_image_exposed",
        "verus_canonical_proposition_image_exposed",
        "verus_computational_translation_validated_zero_authority",
        "verus_proposition_translation_validated_zero_authority",
        "creusot_parse_and_reject_surface",
        "creusot_computational_image_exposed",
        "creusot_canonical_proposition_image_exposed",
        "creusot_computational_translation_validated_zero_authority",
        "creusot_proposition_translation_validated_zero_authority",
        "tla_parse_and_reject_surface",
        "tla_canonical_proposition_image_exposed",
        "tla_proposition_translation_validated_zero_authority",
        "required_policy_instances_biject_obligations",
        "formula_to_canonical_proposition_bridge_checked",
        "proof_grade_kernel_axiom_policy_exact",
        "compatibility_feature_manifests_exact",
        "compatibility_translations_universally_or_exhaustively_validated",
    ),
    "G7": (
        "exact_linked_module_is_codegen_input",
        "full_admitted_codegen_surface",
        "zero_unproved_fallbacks",
        "machine_equivalence_evidence",
        "objects_biject_admitted_modules",
        "authorized_codegen_matrix_complete",
        "typed_module_object_executable_lineage",
        "linked_executable_composition_validated",
        "runtime_startup_syslib_closure_bound",
    ),
    "G8": (
        "g1_through_g7_same_source_revision",
        "g1_through_g7_same_run_and_subject_graph",
        "detached_release_seal_binds_prior_root_and_artifact",
        "owner_authorized_policy_and_repository_identity",
        "pinned_reproducible_environment",
        "cold_warm_cross_crate_release_reproducible",
        "release_artifact_binds_all_evidence",
        "authorized_toolchain_roster_exact",
        "acceptance_run_matrix_exact",
        "externally_pinned_top_verifier",
    ),
}

HEX_DIGEST = re.compile(r"^[0-9a-f]{64}$")
GIT_REVISION = re.compile(r"^(?:[0-9a-f]{40}|[0-9a-f]{64})$")
CHECKER_ID = re.compile(r"^[a-z0-9][a-z0-9._/-]*$")


def _sha256(path: Path) -> str:
    """sha256 of the regular file at ``path``; OSError for anything else.

    Read through ``_open_regular``: a FIFO or device put in place of a bound
    file can neither hang the gate nor feed it bytes without end.
    """
    opened = _open_regular(path)
    if opened is None:
        raise OSError(errno.EINVAL, "not a regular file", str(path))
    fd, _info = opened
    digest = hashlib.sha256()
    try:
        while True:
            chunk = os.read(fd, 1024 * 1024)
            if not chunk:
                break
            digest.update(chunk)
    finally:
        os.close(fd)
    return digest.hexdigest()


def _read_file(path: Path) -> bytes:
    """The bytes of the regular file at ``path``; OSError for anything else."""
    data = _read_regular(path)
    if data is None:
        raise OSError(errno.EINVAL, "not a regular file", str(path))
    return data


def _canonical_json_sha256(value: Any) -> str:
    encoded = json.dumps(value, sort_keys=True, separators=(",", ":")).encode("utf-8")
    return hashlib.sha256(encoded).hexdigest()


# Every Git call disables replacement objects (a refs/replace/* ref otherwise
# substitutes the content of any object the gate reads), never takes the
# optional locks with which `git status` rewrites the candidate's index, and
# never starts a file-system-monitor hook named by the candidate's config.
# (_git_env also turns off lazy fetching; see PROGRAM_CONFIG.)
GIT_GLOBAL_OPTIONS = ("--no-replace-objects", "--no-optional-locks", "-c", "core.fsmonitor=false")
# Repository settings with which a read-only Git command starts a program.  A
# checker runs Git with the candidate's own configuration, so
# worktree_refusals refuses each by name, in every repository it inspects:
# * core.fsmonitor: every index read -- G2's `git status` in
#   first-party/clean -- runs the hook it names, or starts the built-in
#   daemon when it is true;
# * a promisor remote: every command that needs an object the store lacks --
#   G1's `git show <rev>:<path>` or `cat-file` -- starts a lazy `git fetch`,
#   whose transport runs what the remote's uploadpack, ext:: URL or ssh
#   settings name.  The raw-bytes comparison reads no blob, so a store
#   without one still passes it.  Git names a promisor remote by
#   extensions.partialClone, whatever its value, by a true
#   remote.<name>.promisor, and by any remote.<name>.partialCloneFilter,
#   whose remote it registers before reading the value (promisor-remote.c,
#   the same in every release from 2.41 to 2.56-rc2).  <name> may be empty
#   or missing: remote.promisor names the remote "", which a
#   url.<base>.insteadOf rewrite of "" gives a URL.  So every key of the
#   remote section whose last part is promisor or partialclonefilter is
#   matched.
# Nothing else the checkers run reaches a program: no checker runs a diff
# (textconv and external diff drivers) or shows a commit (gpg.program), Git's
# output is never a terminal (the pager), and no command they run writes a
# ref -- nor, under --no-optional-locks, the index -- so no hook fires.  The
# filter drivers that status and hash-object run are refused on their own.
PROGRAM_CONFIG = (
    r"^(core\.fsmonitor|extensions\.partialclone"
    r"|remote\.(.*\.)?(promisor|partialclonefilter))$"
)
# Git reads an empty value, and false, no, off or 0 in any case, as false; a
# key with no value at all is true.
FALSE_SPELLINGS = (b"", b"false", b"no", b"off", b"0")
# `--attr-source` arrived in Git 2.41; without it no checkout conversion can be
# recomputed from the pinned tree, so a genuine checkout that converts a file
# (this repository's six `eol=crlf` LLVM files) would read as tampered.
# GIT_CONFIG_GLOBAL arrived in 2.32, and an older Git silently ignores it and
# reads the operator's global configuration.  Every other option used here
# makes a Git that lacks it fail, which refuses.
MIN_GIT_VERSION = (2, 41)
# `git status` settings the candidate's configuration may not relax.  They are
# not the clean-tree predicate on their own: an index whose cached stat data
# was recorded from a rewritten file (e.g. by one `git -c core.autocrlf=true
# add`) still reads clean under them, which is why raw bytes are compared too.
HARDENED_STATUS_OPTIONS = (
    "-c", "core.untrackedCache=false",
    "-c", "diff.ignoreSubmodules=none",
    "-c", "core.checkStat=default",
    "-c", "core.trustctime=true",
    # On a case-sensitive volume, ignoreCase=true hides an untracked file whose
    # name differs from a tracked one only in case; false can only add entries.
    "-c", "core.ignoreCase=false",
    # Reported paths are matched against raw directory entries
    # (account_for_untracked), so status reports them as the file system
    # stores them rather than precomposed.
    "-c", "core.precomposeUnicode=false",
)
# Checkout conversion, recomputed in a sandbox repository from the pinned
# tree's own .gitattributes and nothing else (``_checkout_conversions``), for
# the exact tree path bytes.
CHECKOUT_CONVERSION_OPTIONS = (
    "-c", "core.autocrlf=false",
    "-c", "core.eol=lf",
    "-c", f"core.attributesFile={os.devnull}",
    "-c", "core.precomposeUnicode=false",
)
# Upper bounds, in seconds, on one Git command: GIT_TIMEOUT for the ones whose
# work grows with the checkout (status, ls-files, cat-file) -- `git status` on
# this repository's 254,550 tracked files takes well under a minute -- and
# GIT_QUICK_TIMEOUT for the ones that read only configuration and refs.  A
# command that runs out of time is refused like any failing Git command.
GIT_TIMEOUT = 900
GIT_QUICK_TIMEOUT = 60
# How many offending paths one refusal names.
NAMED_PATHS = 3
# Worktree files are hashed on a few threads in fixed-size batches.  Measured
# on this repository's 254,550 tracked regular files (2.86 GiB, warm cache):
# 14.1 s on one thread and 4.6 s on four under Python 3.9 (8.3 s and 4.3 s
# under 3.14), slower again on six or more (GIL contention).
HASH_WORKERS = 4
HASH_BATCH = 512
# Files whose raw bytes differ from their blob are checked for a checkout
# conversion this many at a time, each batch in one sandbox; once a batch has
# decided the refusal the remaining files are not examined.
CONVERSION_BATCH = 64


def _git_env() -> dict[str, str]:
    # Candidate identity and cleanliness must not be redirected by the caller:
    # every caller-supplied GIT_* variable is dropped, and the system and
    # global configuration tiers -- including the XDG ignore and attributes
    # files Git reads even without a global config file -- are replaced by
    # empty ones.  What remains is the candidate's own repository
    # configuration, which worktree_refusals inspects instead of trusting.
    # Git honors safe.directory only from those neutralized tiers, so a
    # checkout owned by another user than the one running the gate is refused
    # as of "dubious ownership".  Lazy fetching is off as well: Git 2.45, and
    # the May 2024 security releases 2.41.1, 2.42.2, 2.43.4 and 2.44.1, honor
    # GIT_NO_LAZY_FETCH, but earlier releases ignore it, which is why the gate
    # reads no object of a repository whose configuration names a promisor
    # remote (PROGRAM_CONFIG).
    env = {key: value for key, value in os.environ.items() if not key.startswith("GIT_")}
    env.update(
        GIT_CONFIG_NOSYSTEM="1",
        GIT_CONFIG_GLOBAL=os.devnull,
        GIT_ATTR_NOSYSTEM="1",
        GIT_NO_LAZY_FETCH="1",
        XDG_CONFIG_HOME=os.devnull,
    )
    return env


def _bounded_run(
    command: list[str], timeout: float, **kwargs: Any
) -> subprocess.CompletedProcess:
    """``subprocess.run`` with bytes captured; a missing program or a timeout refuses.

    Either becomes a nonzero exit (127, or 124 with the command that timed
    out), which every caller already refuses.  On a timeout the child is
    killed, not left blocked behind the gate.
    """
    try:
        return subprocess.run(
            command, check=False, capture_output=True, timeout=timeout, **kwargs
        )
    except subprocess.TimeoutExpired:
        detail = f"timed out after {timeout:g} s: {' '.join(command)}"
        return subprocess.CompletedProcess(command, 124, b"", detail.encode())
    except OSError as exc:
        return subprocess.CompletedProcess(command, 127, b"", str(exc).encode())


def _ssh_keygen(*args: str, stdin: Optional[bytes] = None) -> subprocess.CompletedProcess:
    """Run SSH_KEYGEN, bounded by SSH_KEYGEN_TIMEOUT, in a fixed environment."""
    return _bounded_run(
        [str(SSH_KEYGEN), *args],
        SSH_KEYGEN_TIMEOUT,
        input=stdin,
        env={"LANG": "C", "LC_ALL": "C", "PATH": "/usr/bin:/bin"},
    )


def _git_run(
    root: Path, *args: str, stdin: Optional[bytes] = None, timeout: Optional[float] = None
) -> subprocess.CompletedProcess:
    """Run hardened Git against ``root``; bytes out, and a missing Git refuses.

    Git opens files the candidate controls (included configuration,
    info/exclude, core.excludesFile, every .gitignore it walks) with a
    blocking open, so a FIFO at any of them would stall it forever: each
    call is bounded, by GIT_TIMEOUT unless the caller passes a shorter bound.
    """
    command = ["git", *GIT_GLOBAL_OPTIONS, "-C", str(root), *args]
    return _bounded_run(
        command, GIT_TIMEOUT if timeout is None else timeout, input=stdin, env=_git_env()
    )


def _diagnostic(process: subprocess.CompletedProcess) -> str:
    detail = process.stderr.decode("utf-8", errors="replace").strip()
    return f"git exited {process.returncode}: {detail[:300] or 'no diagnostic'}"


def _display(path: Union[bytes, str]) -> str:
    # Surrogate-free, so a hostile path name cannot break the JSON or --text
    # verdict it is reported in.
    if isinstance(path, str):
        path = os.fsencode(path)
    return path.decode("utf-8", errors="backslashreplace")


def _named(paths: list[bytes]) -> str:
    shown = ", ".join(_display(path) for path in paths[:NAMED_PATHS])
    extra = len(paths) - NAMED_PATHS
    return f"{shown} (+{extra} more)" if extra > 0 else shown


def _identity(path: Union[str, bytes, Path]) -> tuple[int, int]:
    info = os.stat(path)
    return info.st_dev, info.st_ino


def _identity_or_none(path: Union[str, bytes, Path]) -> Optional[tuple[int, int]]:
    """``_identity``, or None when ``path`` cannot be stat'ed."""
    try:
        return _identity(path)
    except (OSError, ValueError):
        return None


def _file_mode(
    path: Union[str, bytes, Path], *, follow_symlinks: bool = True
) -> tuple[Optional[int], Optional[str]]:
    """``path``'s st_mode (None when nothing is there), and why it cannot be stat'ed.

    Python 3.9's pathlib is_file() and is_symlink() raise every OSError but
    ENOENT, ENOTDIR, EBADF and ELOOP: a candidate-chosen name longer than
    NAME_MAX, or one under a directory without search permission, would
    crash the gate instead of refusing.  So candidate-derived paths are
    stat'ed only through this.
    """
    try:
        info = os.stat(path, follow_symlinks=follow_symlinks)
    except (FileNotFoundError, NotADirectoryError):
        return None, None
    except (OSError, ValueError) as exc:
        return None, str(exc)
    return info.st_mode, None


def _file_size(path: Union[str, bytes, Path]) -> Optional[int]:
    """``path``'s size, or None when it cannot be stat'ed."""
    try:
        return os.stat(path).st_size
    except (OSError, ValueError):
        return None


def _is_regular_file(path: Union[str, bytes, Path]) -> bool:
    """Whether ``path`` leads to a regular file; False when it cannot be stat'ed."""
    mode, _problem = _file_mode(path)
    return mode is not None and stat.S_ISREG(mode)


def _resolved(path: Path) -> tuple[Path, Optional[str]]:
    """``path.resolve()``, or its absolute spelling plus why it did not resolve.

    Python 3.9's pathlib raises RuntimeError on a symlink loop (3.13+ returns
    the partially resolved path instead), and ValueError on an embedded NUL;
    getcwd() can raise OSError.  None of these may crash the gate.
    """
    try:
        return path.resolve(), None
    except (OSError, RuntimeError, ValueError) as exc:
        problem = str(exc)
    try:
        return Path(os.path.abspath(path)), problem
    except OSError:
        # A relative path under a deleted working directory: abspath calls
        # getcwd() again and fails the same way.
        return path, problem


def _inside_root_by_identity(path: Path, root: Path) -> Optional[str]:
    """Why ``path`` counts as inside ``root``; None when it provably is not.

    Lexical containment is not identity: on a case-insensitive volume
    ``/work/TRUST/owner.pub`` lies inside ``--root /work/trust`` although
    ``relative_to`` says it does not, and a bind mount aliases a directory the
    same way.  ``path`` is inside when it or any ancestor has ``root``'s
    (st_dev, st_ino); when the path or an ancestor cannot be stat'ed nothing
    is proved, so that also counts as inside.
    """
    try:
        root_identity = _identity(root)
    except (OSError, ValueError) as exc:
        return f"--root cannot be stat'ed: {exc}"
    for candidate in (path, *path.parents):
        try:
            identity = _identity(candidate)
        except (OSError, ValueError) as exc:
            return f"cannot stat {candidate}: {exc}"
        if identity == root_identity:
            return f"{candidate} is --root"
    return None


def _git_version_refusal() -> Optional[str]:
    process = _bounded_run(["git", "--version"], GIT_QUICK_TIMEOUT, env=_git_env())
    match = re.match(rb"git version (\d+)\.(\d+)", process.stdout)
    if process.returncode != 0 or match is None:
        return f"cannot determine the git version: {_diagnostic(process)}"
    version = (int(match.group(1)), int(match.group(2)))
    if version < MIN_GIT_VERSION:
        wanted = ".".join(map(str, MIN_GIT_VERSION))
        return (
            f"git {version[0]}.{version[1]} is too old for this gate: GIT_CONFIG_GLOBAL "
            "(2.32) neutralizes the operator's configuration and --attr-source (2.41) "
            f"recomputes checkout conversions from the pinned tree; {wanted}+ is required"
        )
    return None


def _git_path(worktree: Path, *args: str) -> tuple[Optional[str], str]:
    """The one absolute path ``git rev-parse <args>`` prints, or None and why not.

    One path per call: a path may itself hold a newline, so several paths in
    one output cannot be told apart.
    """
    process = _git_run(
        worktree, "rev-parse", "--path-format=absolute", *args, timeout=GIT_QUICK_TIMEOUT
    )
    if process.returncode != 0:
        return None, _diagnostic(process)
    if not process.stdout.endswith(b"\n"):
        return None, "unparseable rev-parse output"
    return os.fsdecode(process.stdout[:-1]), ""


def _safe_tree_path(path: bytes) -> bool:
    return bool(path) and all(
        part not in (b"", b".", b"..") and part.lower() != b".git"
        for part in path.split(b"/")
    )


def _open_regular(path: Union[str, bytes, Path]) -> Optional[tuple[int, os.stat_result]]:
    """An fd on ``path`` if it is itself a regular file, else None.

    O_NOFOLLOW refuses a symlink in the final component and O_NONBLOCK keeps a
    FIFO planted at a tracked path from hanging the gate; the type is then
    decided by fstat on the descriptor actually read.
    """
    fd = os.open(
        path,
        os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK | getattr(os, "O_CLOEXEC", 0),
    )
    try:
        info = os.fstat(fd)
    except OSError:
        os.close(fd)
        raise
    if not stat.S_ISREG(info.st_mode):
        os.close(fd)
        return None
    return fd, info


def _blob_digest(path: bytes, algorithm: Any) -> tuple[Optional[str], int]:
    """Git blob id of the raw bytes at ``path`` (no filters) and its st_mode.

    The id is None when ``path`` is not a regular file or changed size while
    being read.
    """
    opened = _open_regular(path)
    if opened is None:
        return None, 0
    fd, info = opened
    try:
        digest = algorithm(b"blob %d\0" % info.st_size)
        size = 0
        while True:
            chunk = os.read(fd, 1024 * 1024)
            if not chunk:
                break
            size += len(chunk)
            digest.update(chunk)
    finally:
        os.close(fd)
    if size != info.st_size:
        return None, info.st_mode
    return digest.hexdigest(), info.st_mode


def _verified_objects(
    worktree: Path, oids: list[str], kind: bytes
) -> tuple[list[bytes], Optional[str]]:
    """The contents of ``oids``, each re-hashed against its own id.

    Git does not re-hash every object it reads: measured with Git 2.50, a pack
    whose index maps a pinned blob or subtree id onto other content is served
    by ``cat-file``, ``show``, ``ls-tree -r`` and ``status`` without complaint.
    So nothing the gate compares against may come from an unhashed read.
    """
    algorithm = hashlib.sha1 if len(oids[0]) == 40 else hashlib.sha256
    requests = "".join(f"{oid}\n" for oid in oids).encode()
    process = _git_run(worktree, "cat-file", "--batch", stdin=requests)
    if process.returncode != 0:
        return [], f"cannot read objects: {_diagnostic(process)}"
    output = process.stdout
    contents: list[bytes] = []
    position = 0
    for oid in oids:
        end = output.find(b"\n", position)
        header = output[position:end].split(b" ") if end >= 0 else []
        if len(header) != 3 or header[0] != oid.encode() or not header[2].isdigit():
            return [], f"object {oid} is missing or unreadable"
        start = end + 1
        stop = start + int(header[2])
        content = output[start:stop]
        if output[stop:stop + 1] != b"\n" or len(content) != int(header[2]):
            return [], f"object {oid} is truncated"
        position = stop + 1
        if header[1] != kind:
            return [], f"object {oid} is a {_display(header[1])}, not a {_display(kind)}"
        if algorithm(b"%s %d\0" % (kind, len(content)) + content).hexdigest() != oid:
            return [], f"object {oid} does not hash to its id (a substituted object)"
        contents.append(content)
    return contents, None


def _tree_entries(body: bytes, raw_size: int) -> Optional[list[tuple[bytes, bytes, str]]]:
    """A tree object's (mode, name, oid) entries, or None when it is malformed."""
    entries: list[tuple[bytes, bytes, str]] = []
    position = 0
    while position < len(body):
        # Each entry is "<octal mode> <name>\0<raw oid>".
        nul = body.find(b"\0", position)
        space = body.find(b" ", position, nul) if nul >= 0 else -1
        if space < 0 or nul + 1 + raw_size > len(body) or b"/" in body[space + 1:nul]:
            return None
        entries.append(
            (body[position:space], body[space + 1:nul], body[nul + 1:nul + 1 + raw_size].hex())
        )
        position = nul + 1 + raw_size
    return entries


def _verified_head_tree(
    worktree: Path, head: str
) -> tuple[list[tuple[bytes, str, bytes]], dict[bytes, tuple[str, bytes]], Optional[str]]:
    """Every non-tree entry of ``head`` as (mode, oid, path), from re-hashed trees.

    Also returns every tree object, keyed by its directory prefix (b"" for the
    root, else b"dir/sub/"), as (oid, body): the checkout conversion needs the
    trees along a path.
    """
    raw_size = len(head) // 2
    commits, problem = _verified_objects(worktree, [head], b"commit")
    if problem is not None:
        return [], {}, problem
    first_line = commits[0].split(b"\n", 1)[0].split(b" ")
    root_tree = first_line[1].decode("ascii", errors="replace") if len(first_line) == 2 else ""
    if first_line[0] != b"tree" or not GIT_REVISION.fullmatch(root_tree):
        return [], {}, f"commit {head} names no tree"
    entries: list[tuple[bytes, str, bytes]] = []
    trees: dict[bytes, tuple[str, bytes]] = {}
    level = [(root_tree, b"")]
    while level:
        bodies, problem = _verified_objects(worktree, [oid for oid, _prefix in level], b"tree")
        if problem is not None:
            return [], {}, problem
        next_level: list[tuple[str, bytes]] = []
        for (oid, prefix), body in zip(level, bodies):
            parsed = _tree_entries(body, raw_size)
            if parsed is None:
                return [], {}, f"tree {oid} is malformed"
            trees[prefix] = (oid, body)
            for mode, name, child in parsed:
                if mode in (b"40000", b"040000"):
                    next_level.append((child, prefix + name + b"/"))
                else:
                    entries.append((mode, child, prefix + name))
        level = next_level
    return entries, trees, None


def _write_loose_object(git_dir: Path, kind: bytes, oid: str, content: bytes) -> None:
    directory = git_dir / "objects" / oid[:2]
    directory.mkdir(exist_ok=True)
    (directory / oid[2:]).write_bytes(
        zlib.compress(b"%s %d\0" % (kind, len(content)) + content)
    )


def _checkout_conversions(
    worktree: Path,
    head: str,
    trees: dict[bytes, tuple[str, bytes]],
    requests: list[tuple[bytes, str]],
) -> tuple[dict[bytes, Optional[bytes]], dict[bytes, str]]:
    """Each (path, blob) of ``requests`` as a checkout of ``head`` writes it.

    Returns (converted, failures).  ``converted[path]`` is None when the bytes
    depend on core.ignoreCase: whether .gitattributes patterns match
    case-insensitively is the candidate's own setting, so a conversion that
    depends on it is not the pinned checkout.  ``failures[path]`` says why no
    conversion could be computed.

    Git computes each conversion in a throwaway bare repository into which
    the gate writes only objects it re-hashed itself: the pinned trees along
    the path, the .gitattributes blobs on the way, and the blob.  The
    candidate's own object store cannot serve the conversion even after its
    objects were re-hashed.  When two packs claim one id with different
    content, which one a Git process reads depends on the lookups it made
    before (packs are searched most recently used first).  Measured with Git
    2.50: a process that reads only the .gitattributes id gets the genuine
    blob, while a process that converts a file reads that file's blob first,
    from the other pack, and then gets forged attributes from it.  The
    sandbox also has none of the candidate's configuration, filter drivers,
    hooks or info/attributes.
    """
    raw_size = len(head) // 2
    failures: dict[bytes, str] = {}

    def fail_all(problem: str) -> tuple[dict[bytes, Optional[bytes]], dict[bytes, str]]:
        return {}, {path: problem for path, _oid in requests}

    # Git reads the .gitattributes of every directory on the path, from the
    # attribute-source tree; nothing else in the tree.
    prefixes: set[bytes] = set()
    attribute_oids: set[str] = set()
    for path, _oid in requests:
        parts = path.split(b"/")[:-1]
        for depth in range(len(parts) + 1):
            prefix = b"/".join(parts[:depth]) + (b"/" if depth else b"")
            if prefix in prefixes:
                continue
            if prefix not in trees:
                return fail_all(f"HEAD has no tree at {_display(prefix)}")
            prefixes.add(prefix)
            for mode, name, child in _tree_entries(trees[prefix][1], raw_size) or ():
                if name == b".gitattributes" and mode in (b"100644", b"100755", b"120000"):
                    attribute_oids.add(child)
    blob_oids = sorted(attribute_oids | {oid for _path, oid in requests})
    contents, problem = _verified_objects(worktree, blob_oids, b"blob")
    if problem is not None:
        return fail_all(problem)
    object_format = "sha1" if len(head) == 40 else "sha256"
    try:
        with tempfile.TemporaryDirectory(prefix="trust-gate-checkout-") as sandbox_name:
            sandbox = Path(sandbox_name)
            init = _git_run(
                sandbox, "init", "-q", "--bare", "--template=",
                f"--object-format={object_format}", ".",
            )
            if init.returncode != 0:
                return fail_all(f"cannot create the conversion sandbox: {_diagnostic(init)}")
            for prefix in prefixes:
                _write_loose_object(sandbox, b"tree", *trees[prefix])
            for oid, content in zip(blob_oids, contents):
                _write_loose_object(sandbox, b"blob", oid, content)
            root_tree = trees[b""][0]

            def convert(request: tuple[bytes, str]) -> tuple[Optional[bytes], Optional[str]]:
                path, oid = request
                outputs = []
                for ignore_case in ("false", "true"):
                    process = _git_run(
                        sandbox, "--git-dir=.", f"--attr-source={root_tree}",
                        *CHECKOUT_CONVERSION_OPTIONS, "-c", f"core.ignoreCase={ignore_case}",
                        "cat-file", "--filters", f"--path={os.fsdecode(path)}", oid,
                    )
                    if process.returncode != 0:
                        return None, _diagnostic(process)
                    outputs.append(process.stdout)
                return (outputs[0] if outputs[0] == outputs[1] else None), None

            with ThreadPoolExecutor(max_workers=HASH_WORKERS) as pool:
                results = list(pool.map(convert, requests))
    except OSError as exc:
        return fail_all(f"cannot use the conversion sandbox: {exc}")
    converted: dict[bytes, Optional[bytes]] = {}
    for (path, _oid), (output, problem) in zip(requests, results):
        if problem is not None:
            failures[path] = problem
        else:
            converted[path] = output
    return converted, failures


def _read_regular(path: Union[str, bytes, Path]) -> Optional[bytes]:
    opened = _open_regular(path)
    if opened is None:
        return None
    fd, _info = opened
    chunks = []
    try:
        while True:
            chunk = os.read(fd, 1024 * 1024)
            if not chunk:
                break
            chunks.append(chunk)
    finally:
        os.close(fd)
    return b"".join(chunks)


def _status_entries(output: bytes) -> tuple[list[bytes], list[bytes], list[bytes]]:
    """Split ``git status --porcelain -z --ignored`` output.

    Returns (changes, changed paths, ignored paths): changes are the records
    as reported, and a directory's path keeps its trailing slash.  A rename
    or copy record is followed by its source path, part of the same change.
    """
    changes: list[bytes] = []
    changed: list[bytes] = []
    ignored: list[bytes] = []
    records = iter(output.split(b"\0"))
    for record in records:
        if not record:
            continue
        code, path = record[:2], record[3:]
        if code == b"!!":
            ignored.append(path)
            continue
        changes.append(record)
        changed.append(path)
        if b"R" in code or b"C" in code:
            changed.append(next(records, b""))
    return changes, changed, ignored


class _CheckoutInspection:
    """One clean-tree inspection of a checkout and, recursively, its submodules."""

    def __init__(self) -> None:
        self.refusals: list[str] = []
        self.visited: set[tuple[int, int]] = set()

    def inspect(self, worktree: Path, prefix: str, pinned: Optional[str]) -> bool:
        """Inspect the checkout at ``worktree``, whose HEAD must be ``pinned``.

        Returns whether running ``git status`` there is safe: status executes
        the clean filter of any configured driver, in this repository or in a
        submodule it recurses into, and reads objects, so it only runs once
        every repository at or below this one has been inspected and
        configures neither a filter driver nor a promisor remote.
        """
        label = f"submodule {prefix.rstrip('/')}: " if prefix else ""

        def refuse(detail: str) -> None:
            self.refusals.append(f"{label}{detail}")

        toplevel, problem = _git_path(worktree, "--show-toplevel")
        if toplevel is None:
            refuse(f"cannot inspect the repository layout: {problem}")
            return False
        # The directory Git inspects must be the directory the checkers read,
        # by identity: core.worktree or a .git file can point status elsewhere.
        try:
            identity = _identity(worktree)
            redirected = _identity(toplevel) != identity
        except (OSError, ValueError) as exc:
            refuse(f"cannot compare Git's worktree with {_display(str(worktree))}: {exc}")
            return False
        if redirected:
            refuse(
                f"Git inspects {_display(toplevel)}, not {_display(str(worktree))} "
                "(core.worktree or a .git file redirects it)"
            )
            return False
        self.visited.add(identity)
        # Before the first object read: with a promisor remote configured,
        # reading an object the store lacks runs a program (PROGRAM_CONFIG).
        if not self.refuse_program_config(worktree, refuse):
            return False

        head_process = _git_run(
            worktree, "rev-parse", "--verify", "--quiet", "HEAD^{commit}",
            timeout=GIT_QUICK_TIMEOUT,
        )
        head = head_process.stdout.decode("ascii", errors="replace").strip()
        if head_process.returncode != 0 or not GIT_REVISION.fullmatch(head):
            refuse("HEAD is not a readable commit")
            return False
        if pinned is not None and head != pinned:
            refuse(f"HEAD {head} is not the pinned commit {pinned}")
            return False

        replace_refs = _git_run(
            worktree, "for-each-ref", "--format=%(refname)", "refs/replace/",
            timeout=GIT_QUICK_TIMEOUT,
        )
        if replace_refs.returncode != 0:
            refuse(f"cannot list replacement refs: {_diagnostic(replace_refs)}")
        elif replace_refs.stdout.strip():
            refuse(
                "replacement refs substitute object content for every other Git "
                f"reader: {_named(replace_refs.stdout.split())}"
            )
        for name, effect in (
            ("info/grafts", "rewrites commit ancestry (a graft file)"),
            ("info/attributes", "adds repository-local attributes that change content conversion"),
        ):
            path, problem = _git_path(worktree, "--git-path", name)
            if path is None:
                refuse(f"cannot locate {name}: {problem}")
                continue
            try:
                info = os.lstat(path)
            except FileNotFoundError:
                continue
            except OSError as exc:
                refuse(f"cannot inspect {_display(path)}: {exc}")
                continue
            if not stat.S_ISREG(info.st_mode) or info.st_size:
                refuse(f"{_display(path)} {effect}")

        filters = _git_run(
            worktree, "config", "--null", "--get-regexp", r"^filter\.", timeout=GIT_QUICK_TIMEOUT
        )
        filter_free = False
        if filters.returncode == 0:
            keys = [entry.split(b"\n", 1)[0] for entry in filters.stdout.split(b"\0") if entry]
            refuse(
                "filter drivers in the repository configuration rewrite content "
                f"between the index and the worktree: {_named(keys)}"
            )
        elif filters.returncode == 1 and not filters.stdout:
            filter_free = True
        else:
            refuse(f"cannot read the repository configuration: {_diagnostic(filters)}")

        # Each record is "<tag> <mode> <oid> <stage>\t<path>"; the tag says
        # skip-worktree (S) or, in lower case, assume-unchanged.
        index = _git_run(worktree, "ls-files", "--stage", "-v", "-z")
        indexed: Optional[dict[bytes, tuple[bytes, str]]] = {}
        if index.returncode != 0:
            refuse(f"cannot read the index: {_diagnostic(index)}")
            indexed = None
        else:
            skipped: list[bytes] = []
            assumed: list[bytes] = []
            unmerged: list[bytes] = []
            for record in index.stdout.split(b"\0"):
                if not record:
                    continue
                meta, tab, path = record.partition(b"\t")
                fields = meta.split(b" ")
                if len(fields) != 4 or not tab:
                    refuse("cannot read the index: unparseable ls-files output")
                    indexed = None
                    break
                tag, mode, oid, stage = fields
                if tag in (b"S", b"s"):
                    skipped.append(path)
                if tag.islower():
                    assumed.append(path)
                if stage != b"0" or path in indexed:
                    unmerged.append(path)
                indexed[path] = (mode, oid.decode("ascii", errors="replace"))
            for flagged, flag in ((skipped, "skip-worktree"), (assumed, "assume-unchanged")):
                if flagged:
                    refuse(f"{flag} index entries hide their worktree files: {_named(flagged)}")
            if unmerged:
                refuse(f"the index holds unmerged or duplicate entries: {_named(unmerged)}")

        entries, trees, problem = _verified_head_tree(worktree, head)
        if problem is not None:
            refuse(f"cannot verify HEAD's tree: {problem}")
            return False
        if indexed is not None:
            # git status decides what is untracked by the index, and compares
            # the index with HEAD through the index's own cache-tree extension,
            # which can claim a directory equals HEAD's tree while listing an
            # extra file under it; so the index must list exactly HEAD's
            # entries (an extra one reads as tracked and unchanged).
            pinned_entries = {path: (mode, oid) for mode, oid, path in entries}
            stray_entries = sorted(
                path
                for path in pinned_entries.keys() | indexed.keys()
                if pinned_entries.get(path) != indexed.get(path)
            )
            if stray_entries:
                refuse(f"index entries differ from HEAD's tree: {_named(stray_entries)}")
        submodules = self.compare_tree(worktree, refuse, entries, head, trees)

        status_safe = filter_free
        for path, oid in submodules:
            nested = Path(os.fsdecode(os.fsencode(worktree) + b"/" + path))
            try:
                identity = _identity(nested)
            except (OSError, ValueError) as exc:
                refuse(f"cannot inspect submodule {_display(path)}: {exc}")
                status_safe = False
                continue
            if identity in self.visited:
                refuse(f"submodule {_display(path)} revisits a checkout already inspected")
                status_safe = False
                continue
            nested_safe = self.inspect(nested, f"{prefix}{_display(path)}/", oid)
            status_safe = status_safe and nested_safe

        if status_safe:
            # --ignored=matching lists each ignored path the walk met, an
            # ignored directory as one entry that is not descended into.
            status = _git_run(
                worktree, *HARDENED_STATUS_OPTIONS, "status", "--porcelain", "-z",
                "--untracked-files=all", "--ignore-submodules=none", "--ignored=matching",
            )
            if status.returncode != 0:
                refuse(f"cannot inspect worktree state: {_diagnostic(status)}")
            else:
                changes, changed, ignored = _status_entries(status.stdout)
                if changes:
                    refuse(f"git status reports changes: {_named(changes)}")
                # Git reads a .gitignore in every directory it walks, tracked
                # or not, and an untracked one can ignore itself and anything
                # beside it.  Of the .gitignore files, only the committed ones,
                # which the raw comparison pins, may decide what is ignored.
                planted = [
                    path for path in ignored
                    if path.rstrip(b"/").rpartition(b"/")[2].lower() == b".gitignore"
                ]
                if planted:
                    refuse(
                        "untracked .gitignore files hide untracked content from git "
                        f"status: {_named(planted)}"
                    )
                listed = {path.rstrip(b"/") for path in (*changed, *ignored)}
                self.account_for_untracked(worktree, refuse, entries, listed)
        return status_safe

    @staticmethod
    def refuse_program_config(worktree: Path, refuse: Callable[[str], None]) -> bool:
        """Refuse the PROGRAM_CONFIG settings at ``worktree`` by name.

        They are read from the tiers the candidate controls, which a checker's
        Git reads too: the repository's own configuration, its includes and
        its worktree scope (``_git_env`` neutralizes the system and global
        tiers).  The listing also holds the gate's own command-line
        ``core.fsmonitor=false`` (GIT_GLOBAL_OPTIONS), which passes as a false
        spelling; it masks none of the candidate's values, which are listed
        beside it.  Returns whether objects of this repository may be read at
        all: not when it names a promisor remote, nor when its configuration
        cannot be read, since reading an object the store lacks then runs a
        program even in the gate's own Git wherever GIT_NO_LAZY_FETCH is
        ignored.
        """
        config = _git_run(
            worktree, "config", "--null", "--get-regexp", PROGRAM_CONFIG,
            timeout=GIT_QUICK_TIMEOUT,
        )
        if config.returncode == 1 and not config.stdout:
            return True
        if config.returncode != 0:
            refuse(f"cannot read the repository configuration: {_diagnostic(config)}")
            return False
        monitors: list[bytes] = []
        promisors: list[bytes] = []
        for record in config.stdout.split(b"\0"):
            if not record:
                continue
            # "<key>\n<value>", or just "<key>" for a key without a value.
            key, has_value, value = record.partition(b"\n")
            setting = key + b"=" + value if has_value else key
            if key == b"extensions.partialclone" or key.endswith(b".partialclonefilter"):
                # Either names a promisor remote whatever its value spells: the
                # extension's value is the remote's name, and Git registers a
                # filter's remote before it reads the filter.
                promisors.append(setting)
            elif has_value and value.lower() in FALSE_SPELLINGS:
                continue
            elif key == b"core.fsmonitor":
                monitors.append(setting)
            else:
                promisors.append(setting)
        if monitors:
            refuse(
                "core.fsmonitor starts a program whenever a checker's Git reads the "
                f"index: {_named(monitors)}"
            )
        if promisors:
            refuse(
                "a promisor remote makes a checker's Git fetch any object the store "
                f"lacks, running the programs its transport settings name: {_named(promisors)}"
            )
        return not promisors

    def compare_tree(
        self,
        worktree: Path,
        refuse: Callable[[str], None],
        entries: list[tuple[bytes, str, bytes]],
        head: str,
        trees: dict[bytes, tuple[str, bytes]],
    ) -> list[tuple[bytes, str]]:
        """Compare HEAD's (mode, oid, path) entries with the raw worktree.

        Returns the gitlinks that hold a checkout.  Regular files must hash (as
        Git blobs, with no conversion) to HEAD's blob with HEAD's executable
        bit, symlinks must be symlinks whose target is HEAD's blob, and nothing
        may be reached through a symlinked or missing directory.  A regular
        file whose raw bytes differ is still HEAD's checkout when they equal
        the blob as the pinned commit's own .gitattributes convert it (the
        vendored LLVM tree checks six files out with ``eol=crlf``), computed
        from re-hashed objects only (``_checkout_conversions``).  Differing
        files are converted CONVERSION_BATCH at a time; once more than
        NAMED_PATHS of them are confirmed or cannot be converted the refusal
        is decided, and later batches are reported as not examined.
        """
        base = os.fsencode(worktree)
        algorithm = hashlib.sha1 if len(head) == 40 else hashlib.sha256
        directories: dict[bytes, Optional[str]] = {b"": None}

        def directory_state(relative: bytes) -> Optional[str]:
            # None for a real directory reached without a symlink, else why not.
            # Iterative, from the nearest known ancestor down: HEAD's tree is
            # the candidate's, and no path depth may exhaust the recursion limit.
            unknown: list[bytes] = []
            while relative not in directories:
                unknown.append(relative)
                relative = relative.rpartition(b"/")[0]
            state = directories[relative]
            for relative in reversed(unknown):
                if state is None:
                    try:
                        info = os.lstat(base + b"/" + relative)
                    except FileNotFoundError:
                        state = "missing"
                    except OSError as exc:
                        state = f"unreadable ({exc.strerror})"
                    else:
                        if stat.S_ISLNK(info.st_mode):
                            state = "symlink"
                        elif not stat.S_ISDIR(info.st_mode):
                            state = "not a directory"
                directories[relative] = state
            return state

        missing: list[bytes] = []
        wrong_type: list[bytes] = []
        wrong_mode: list[bytes] = []
        unreadable: list[bytes] = []
        differing: list[tuple[bytes, str]] = []
        wrong_target: list[bytes] = []
        stray: list[bytes] = []
        unsupported: list[bytes] = []
        submodules: list[tuple[bytes, str]] = []
        regular: list[tuple[bytes, bytes, str]] = []
        for mode, oid, path in entries:
            if not _safe_tree_path(path):
                unsupported.append(path)
                continue
            full = base + b"/" + path
            state = directory_state(path.rpartition(b"/")[0])
            if mode == b"160000":
                # A gitlink with nothing checked out is nothing a checker can
                # read; one holding files must be a checkout of its pin.
                if state == "missing":
                    continue
                if state is not None:
                    wrong_type.append(path)
                    continue
                try:
                    info = os.lstat(full)
                except FileNotFoundError:
                    continue
                except OSError:
                    unreadable.append(path)
                    continue
                if not stat.S_ISDIR(info.st_mode):
                    wrong_type.append(path)
                    continue
                try:
                    names = os.listdir(full)
                except OSError:
                    unreadable.append(path)
                    continue
                if not names:
                    continue
                if b".git" not in names:
                    stray.append(path)
                    continue
                submodules.append((path, oid))
                continue
            if mode not in (b"100644", b"100755", b"120000"):
                unsupported.append(path)
                continue
            if state is not None:
                (missing if state == "missing" else wrong_type).append(path)
                continue
            if mode == b"120000":
                try:
                    target = os.readlink(full)
                except FileNotFoundError:
                    missing.append(path)
                    continue
                except OSError as exc:
                    (wrong_type if exc.errno == errno.EINVAL else unreadable).append(path)
                    continue
                if algorithm(b"blob %d\0" % len(target) + target).hexdigest() != oid:
                    wrong_target.append(path)
                continue
            regular.append((path, mode, oid))

        def digests_of(
            batch: list[tuple[bytes, bytes, str]],
        ) -> list[tuple[Optional[str], int, Optional[OSError]]]:
            results: list[tuple[Optional[str], int, Optional[OSError]]] = []
            for path, _mode, _oid in batch:
                try:
                    results.append((*_blob_digest(base + b"/" + path, algorithm), None))
                except OSError as exc:
                    results.append((None, 0, exc))
            return results

        # Hashing is bound by per-file system calls, which release the GIL.
        batches = [
            regular[start:start + HASH_BATCH] for start in range(0, len(regular), HASH_BATCH)
        ]
        with ThreadPoolExecutor(max_workers=HASH_WORKERS) as pool:
            for batch, results in zip(batches, pool.map(digests_of, batches)):
                for (path, mode, oid), (digest, file_mode, failure) in zip(batch, results):
                    if isinstance(failure, (FileNotFoundError, NotADirectoryError)):
                        missing.append(path)
                    elif failure is not None:
                        (wrong_type if failure.errno == errno.ELOOP else unreadable).append(path)
                    elif digest is None:
                        # No st_mode: not a regular file; else it changed size mid-read.
                        (unreadable if file_mode else wrong_type).append(path)
                    else:
                        if bool(file_mode & stat.S_IXUSR) != (mode == b"100755"):
                            wrong_mode.append(path)
                        if digest != oid:
                            differing.append((path, oid))

        confirmed: list[bytes] = []
        unconverted: list[bytes] = []
        unconverted_reason = ""
        examined = 0
        while examined < len(differing) and len(confirmed) + len(unconverted) <= NAMED_PATHS:
            batch = differing[examined:examined + CONVERSION_BATCH]
            examined += len(batch)
            converted, failures = _checkout_conversions(worktree, head, trees, batch)
            for path, _oid in batch:
                if path in failures:
                    unconverted.append(path)
                    unconverted_reason = unconverted_reason or failures[path]
                    continue
                try:
                    raw = _read_regular(base + b"/" + path)
                except OSError:
                    raw = None
                expected = converted.get(path)
                if expected is None or raw != expected:
                    confirmed.append(path)
        for paths, what in (
            (missing, "HEAD entries are missing from the worktree"),
            (wrong_type, "worktree entries do not have HEAD's file type"),
            (wrong_mode, "worktree executable bits differ from HEAD"),
            (unreadable, "worktree entries cannot be read, or changed while being read"),
            (confirmed, "raw worktree bytes differ from HEAD's checkout"),
            (wrong_target, "symlink targets differ from HEAD"),
            (stray, "gitlink directory holds content outside its pin (no .git)"),
            (unsupported, "HEAD's tree has entries this gate cannot verify"),
        ):
            if paths:
                refuse(f"{what}: {_named(paths)}")
        if unconverted:
            refuse(
                f"cannot compute HEAD's checkout conversion for {_named(unconverted)}: "
                f"{unconverted_reason}"
            )
        unexamined = [path for path, _oid in differing[examined:]]
        if unexamined:
            refuse(
                "raw worktree bytes differ from HEAD's blob (not examined for a checkout "
                f"conversion once the refusal was decided): {_named(unexamined)}"
            )
        return submodules

    def account_for_untracked(
        self,
        worktree: Path,
        refuse: Callable[[str], None],
        entries: list[tuple[bytes, str, bytes]],
        listed: set[bytes],
    ) -> None:
        """Refuse every worktree entry that is neither HEAD's nor listed by status.

        Git's untracked-file walk never reports an entry named .git in any
        directory, a FIFO, socket or device, or what lies in a directory it
        cannot open, and an untracked directory holding only such entries is
        not reported either.  So every entry below ``worktree`` must be a HEAD
        entry (a gitlink's content is its own inspection's), a directory on
        the way to one, the repository's own .git, or a path ``git status``
        listed; an untracked directory it did not list is walked the same way.
        """
        tracked = {path for _mode, _oid, path in entries}
        directories: set[bytes] = set()
        for path in tracked:
            parent = path.rpartition(b"/")[0]
            while parent and parent not in directories:
                directories.add(parent)
                parent = parent.rpartition(b"/")[0]
        base = os.fsencode(worktree)
        unreported: list[bytes] = []
        pending = [b""]
        while pending:
            relative = pending.pop()
            try:
                with os.scandir(base + b"/" + relative if relative else base) as listing:
                    children = [
                        (entry.name, entry.is_dir(follow_symlinks=False)) for entry in listing
                    ]
            except OSError:
                unreported.append(relative or b".")
                continue
            for name, is_directory in children:
                path = relative + b"/" + name if relative else name
                if path in tracked or path in listed or (not relative and name == b".git"):
                    continue
                if path in directories:
                    # A symlink or file standing in for a HEAD directory is
                    # compare_tree's refusal; only a real one is walked.
                    if is_directory:
                        pending.append(path)
                    continue
                if is_directory and name != b".git":
                    pending.append(path)
                else:
                    unreported.append(path)
        if unreported:
            refuse(
                "worktree entries neither in HEAD nor reported by git status: "
                f"{_named(sorted(unreported))}"
            )


def worktree_refusals(root: Path, expected_head: Optional[str] = None) -> list[str]:
    """Every reason the checkout at ``root`` is not exactly its HEAD commit.

    An empty list is the clean-tree predicate that ``validate`` requires before
    the checkers run and ``post_run_integrity_check`` requires after them.
    ``git status`` alone cannot be that predicate: it compares through cached
    stat data, content conversions, filter drivers, index flags, the index's
    cache-tree, replacement objects and submodule settings the candidate's
    own configuration controls, while the checkers read raw bytes, and its
    untracked-file walk skips some entries entirely.  So, for ``root`` and
    recursively for every initialized submodule, this requires that:

    * Git inspects exactly that directory (``--show-toplevel`` by identity);
    * its configuration sets no core.fsmonitor and names no promisor remote
      (extensions.partialClone, a true remote.<name>.promisor, or any
      remote.<name>.partialCloneFilter, <name> empty or missing included),
      with which a checker's read-only Git would start a program
      (``PROGRAM_CONFIG``); no object of a repository naming one is read;
    * HEAD is ``expected_head`` (for a submodule: its gitlink) when given;
    * no refs/replace/* ref, graft file, repository-local info/attributes,
      filter driver, or skip-worktree/assume-unchanged index entry exists,
      and the index lists exactly HEAD's entries;
    * every regular file's raw bytes and executable bit, and every symlink's
      target, equal HEAD's checkout of that entry (``compare_tree``);
    * every gitlink is an empty directory or a checkout of its pin that
      satisfies this same predicate (an absent one fails the status below);
    * a hardened ``git status`` reports nothing but ignored paths, and no
      untracked .gitignore is among them;
    * every other worktree entry is one of those ignored paths
      (``account_for_untracked``).

    Untracked files the repository's own ignore rules exclude (``build/``) stay
    permitted, as before: the committed .gitignore files and the
    repository-local info/exclude and core.excludesFile.  The operator's
    global and XDG exclude files no longer count toward them.
    """
    refusal = _git_version_refusal()
    if refusal is not None:
        return [refusal]
    inspection = _CheckoutInspection()
    inspection.inspect(root, "", expected_head)
    return inspection.refusals


def _isolated_python(bytecode_prefix: Path) -> list[str]:
    """The interpreter command every checker runs under.

    -I keeps the candidate's directories off sys.path, but a module imported
    by file path -- the G3 scorecard replay loads rust_instance_census that
    way -- is still loaded from the __pycache__ beside its source, and an
    unchecked-hash .pyc there runs without being compared to that source.
    The clean-tree predicate permits __pycache__ (the repository ignores it).
    So bytecode is read only below ``bytecode_prefix``, which must be a fresh
    empty directory outside the candidate, and -B writes none there or in the
    tree.  A checker that starts Python itself must pass the same flags: -X
    options are not inherited.
    """
    return [sys.executable, "-I", "-B", "-X", f"pycache_prefix={bytecode_prefix}"]


def _strict_json(text: str) -> Any:
    """Use one unambiguous, finite JSON protocol for files and checker output."""
    if _trust_json_nesting_depth(text) > TRUST_MAX_JSON_DEPTH:
        raise ValueError(f"JSON nests deeper than {TRUST_MAX_JSON_DEPTH}")

    def unique_object(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
        result: dict[str, Any] = {}
        for key, value in pairs:
            if key in result:
                raise ValueError(f"duplicate JSON key {key!r}")
            result[key] = value
        return result

    def reject_constant(token: str) -> Any:
        raise ValueError(f"non-finite JSON number {token}")

    value = json.loads(text, object_pairs_hook=unique_object, parse_constant=reject_constant)
    # parse_constant rejects the nonstandard spellings, but not a standard
    # numeric token such as 1e999 that overflows Python's float to infinity.
    json.dumps(value, allow_nan=False)
    return value


METADATA_REFUSAL = "must bind underlying evidence, not receipt metadata"


class _Metadata(NamedTuple):
    """The receipt metadata files, by path, by file identity and by content."""

    paths: frozenset
    identities: frozenset
    digests: frozenset


class ReceiptValidator:
    def __init__(
        self,
        root: Path,
        receipt_path: Path,
        trusted_owner_key: Optional[Path],
        external_verifier: Optional[Path] = None,
        external_verifier_sha256: Optional[str] = None,
    ):
        self.errors: list[str] = []
        self.root = self.resolved(root, "repository", "--root")
        self.receipt_path = self.resolved(receipt_path, "receipt", "receipt path")
        self.trusted_owner_key = (
            self.resolved(trusted_owner_key, "policy_authorization", "trusted owner key")
            if trusted_owner_key is not None
            else None
        )
        self.external_verifier = (
            self.resolved(external_verifier, "external_verifier", "external verifier")
            if external_verifier is not None
            else None
        )
        self.external_verifier_sha256 = external_verifier_sha256
        self.trusted_owner_fingerprint: Optional[str] = None
        self.bound_files: dict[Path, str] = {}
        self.prior_gates_root: Optional[str] = None
        self.head_before_run: Optional[str] = None
        self.worktree_clean_before_run = False
        # Set once worktree_refusals refused the checkout: from then on the
        # gate reads no object of it (see resolve_checker) and runs no
        # checker (see validate_gate in validate).
        self.checkout_refused = False

    def error(self, location: str, detail: str) -> None:
        self.errors.append(f"{location}: {detail}")

    def resolved(self, path: Path, location: str, what: str) -> Path:
        resolved, problem = _resolved(path)
        if problem is not None:
            self.error(location, f"{what} cannot be resolved: {problem}")
        return resolved

    def exact_keys(self, value: Any, expected: set[str], location: str) -> bool:
        if not isinstance(value, dict):
            self.error(location, "must be an object")
            return False
        actual = set(value)
        missing = sorted(expected - actual)
        unknown = sorted(actual - expected)
        if missing:
            self.error(location, f"missing keys {missing}")
        if unknown:
            self.error(location, f"unknown keys {unknown}")
        return not missing and not unknown

    def validate_codegen_cell_binding(
        self,
        row: dict[str, Any],
        location: str,
        cells: dict[str, dict[str, str]],
    ) -> Optional[dict[str, str]]:
        """Join one observed codegen row to the exact owner-signed matrix cell."""
        cell_id = row.get("codegen_cell_id")
        if not isinstance(cell_id, str) or not cell_id:
            self.error(f"{location}.codegen_cell_id", "must be a non-empty string")
            return None
        cell = cells.get(cell_id)
        if cell is None:
            self.error(
                f"{location}.codegen_cell_id",
                "must name an owner-signed codegen matrix cell",
            )
            return None
        for field in CODEGEN_CELL_FIELDS:
            if row.get(field) != cell.get(field):
                self.error(
                    f"{location}.{field}",
                    "must exactly equal the owner-signed codegen cell value",
                )
        return cell

    def load_json(self, path: Path, location: str) -> Optional[dict[str, Any]]:
        return self.load_json_bytes(path, location)[0]

    def load_json_bytes(
        self, path: Path, location: str
    ) -> tuple[Optional[dict[str, Any]], Optional[bytes]]:
        """The JSON object in the regular file at ``path``, and the bytes parsed.

        Read through ``_read_file``, which refuses a FIFO or device (a FIFO put
        in place of the receipt would otherwise block the read forever), and
        read once, so a digest bound from these bytes describes what was parsed.
        """
        try:
            data = _read_file(path)
        except (OSError, ValueError) as exc:
            # ValueError: an embedded NUL in a caller-supplied path.
            self.error(location, f"cannot read JSON: {exc}")
            return None, None
        try:
            value = _strict_json(data.decode("utf-8"))
        except (UnicodeError, ValueError, RecursionError) as exc:
            self.error(location, f"cannot read JSON: {exc}")
            return None, data
        if not isinstance(value, dict):
            self.error(location, "must contain a JSON object")
            return None, data
        return value, data

    def metadata(self, paths: set[Path]) -> _Metadata:
        """``paths`` with the (st_dev, st_ino) of each file and its content digests.

        A file's content counts both as the receipt records it (bound_files)
        and as read now.  A file that cannot be stat'ed or read has no identity
        or content another path could share, and it has been refused already.
        """
        identities: set[tuple[int, int]] = set()
        digests: set[str] = set()
        for path in paths:
            identity = _identity_or_none(path)
            if identity is not None:
                identities.add(identity)
            bound = self.bound_files.get(path)
            if bound is not None:
                digests.add(bound)
            try:
                digests.add(_sha256(path))
            except (OSError, ValueError):
                pass
        return _Metadata(frozenset(paths), frozenset(identities), frozenset(digests))

    def resolve_ref(
        self,
        value: Any,
        location: str,
        *,
        forbidden: Optional["_Metadata"] = None,
    ) -> Optional[Path]:
        """Resolve a {path, sha256} reference inside --root and bind its digest.

        With ``forbidden``, the file must not be receipt metadata: not one of
        its paths, not the same file (a case alias on a case-insensitive
        volume, a hard link), and not the same bytes (a copy).
        """
        if not self.exact_keys(value, {"path", "sha256"}, location):
            return None
        raw_path = value.get("path")
        digest = value.get("sha256")
        if not isinstance(raw_path, str) or not raw_path or "\0" in raw_path:
            self.error(f"{location}.path", "must be a non-empty relative path")
            return None
        if Path(raw_path).is_absolute():
            self.error(f"{location}.path", "absolute paths are forbidden")
            return None
        try:
            candidate = (self.root / raw_path).resolve()
        except (OSError, RuntimeError, ValueError) as exc:
            # RuntimeError: Python 3.9's pathlib on a symlink loop.
            self.error(f"{location}.path", f"cannot resolve path: {exc}")
            return None
        try:
            candidate.relative_to(self.root)
        except ValueError:
            self.error(f"{location}.path", "escapes --root")
            return None
        if forbidden is not None and candidate in forbidden.paths:
            self.error(f"{location}.path", METADATA_REFUSAL)
            forbidden = None  # refused once is enough
        if not isinstance(digest, str) or not HEX_DIGEST.fullmatch(digest):
            self.error(f"{location}.sha256", "must be a lowercase 64-hex digest")
            return candidate
        try:
            info = os.stat(candidate)
        except (FileNotFoundError, NotADirectoryError):
            info = None
        except (OSError, ValueError) as exc:
            self.error(f"{location}.path", f"cannot stat {raw_path}: {exc}")
            return candidate
        if info is None or not stat.S_ISREG(info.st_mode):
            self.error(f"{location}.path", f"file does not exist: {raw_path}")
            return candidate
        try:
            actual = _sha256(candidate)
        except OSError as exc:
            self.error(f"{location}.path", f"cannot read file: {exc}")
            return candidate
        if forbidden is not None and (
            (info.st_dev, info.st_ino) in forbidden.identities
            or digest in forbidden.digests
            or actual in forbidden.digests
        ):
            self.error(f"{location}.path", METADATA_REFUSAL)
        if actual != digest:
            self.error(f"{location}.sha256", f"hash mismatch: recorded {digest}, actual {actual}")
        previous = self.bound_files.get(candidate)
        if previous is not None and previous != digest:
            self.error(location, "the same path is bound to conflicting digests")
        elif isinstance(digest, str) and HEX_DIGEST.fullmatch(digest):
            self.bound_files[candidate] = digest
        return candidate

    def resolve_named_ref(
        self,
        value: Any,
        location: str,
        *,
        expected_id: Optional[str] = None,
        forbidden: Optional["_Metadata"] = None,
    ) -> tuple[Optional[str], Optional[Path], Optional[str]]:
        """Resolve a content reference whose semantic identity is also explicit."""
        if not self.exact_keys(value, {"id", "path", "sha256"}, location):
            return None, None, None
        ref_id = value.get("id")
        if not isinstance(ref_id, str) or not CHECKER_ID.fullmatch(ref_id):
            self.error(f"{location}.id", "must be a non-empty typed identifier")
            ref_id = None
        elif expected_id is not None and ref_id != expected_id:
            self.error(f"{location}.id", f"must equal {expected_id!r}")
        path = self.resolve_ref(
            {"path": value.get("path"), "sha256": value.get("sha256")},
            location,
            forbidden=forbidden,
        )
        digest = value.get("sha256")
        if not isinstance(digest, str) or not HEX_DIGEST.fullmatch(digest):
            digest = None
        return ref_id, path, digest

    def resolve_checker(
        self,
        gate: str,
        source_revision: Any,
        recorded_digest: Any,
        location: str,
    ) -> Optional[tuple[Path, str, bytes]]:
        """Resolve the schema-owned checker and bind it to the accepted commit.

        Once the checkout has been refused the checker is not bound to the
        source revision: the receipt is refused already and no checker runs
        (validate_gate checks ``checkout_refused`` before run_checker), and
        the gate reads no more objects of that checkout.
        """
        relative = CHECKER_PATHS[gate]
        checker_path = self.root / relative
        mode, problem = _file_mode(checker_path, follow_symlinks=False)
        if problem is not None:
            self.error(location, f"schema-owned checker cannot be stat'ed: {problem}")
            return None
        if mode is not None and stat.S_ISLNK(mode):
            self.error(location, "checker must be a regular tracked file, not a symlink")
            return None
        try:
            candidate = checker_path.resolve()
        except (OSError, RuntimeError, ValueError) as exc:
            self.error(location, f"schema-owned checker path cannot be resolved: {exc}")
            return None
        try:
            candidate.relative_to(self.root)
        except ValueError:
            self.error(location, "schema-owned checker path escapes --root")
            return None
        if not _is_regular_file(candidate):
            self.error(location, f"schema-owned checker is not implemented: {relative}")
            return None
        try:
            working_bytes = _read_file(candidate)
        except OSError as exc:
            self.error(location, f"schema-owned checker cannot be read: {exc}")
            return None
        actual_digest = hashlib.sha256(working_bytes).hexdigest()
        if not isinstance(recorded_digest, str) or not HEX_DIGEST.fullmatch(recorded_digest):
            self.error(location, "must be a lowercase 64-hex digest")
        elif recorded_digest != actual_digest:
            self.error(
                location,
                f"checker hash mismatch: recorded {recorded_digest}, actual {actual_digest}",
            )
        if not isinstance(source_revision, str) or not GIT_REVISION.fullmatch(source_revision):
            self.error(location, "cannot bind checker to an invalid source revision")
            return candidate, actual_digest, working_bytes
        if self.checkout_refused:
            # Reading a refused checkout's objects again could run a program:
            # with a promisor remote configured, a Git that ignores
            # GIT_NO_LAZY_FETCH fetches any object the store lacks
            # (PROGRAM_CONFIG).
            checker_bytes = working_bytes
        else:
            tracked = _git_run(
                self.root, "show", f"{source_revision}:{relative}", timeout=GIT_QUICK_TIMEOUT
            )
            if tracked.returncode != 0:
                self.error(location, f"checker is not tracked at source revision: {relative}")
                checker_bytes = working_bytes
            else:
                checker_bytes = tracked.stdout
                tracked_digest = hashlib.sha256(tracked.stdout).hexdigest()
                if tracked_digest != actual_digest:
                    self.error(
                        location,
                        "working checker bytes differ from the source-revision checker bytes",
                    )
        previous = self.bound_files.get(candidate)
        if previous is not None and previous != actual_digest:
            self.error(location, "checker path is already bound to a conflicting digest")
        self.bound_files[candidate] = actual_digest
        return candidate, actual_digest, checker_bytes

    def run_checker(
        self,
        gate: str,
        checker_bytes: bytes,
        evidence_path: Path,
        toolchain_path: Path,
        corpus_path: Path,
        subject_graph_path: Path,
        linked_module_path: Path,
        release_artifact_path: Path,
        policy_path: Path,
        policy_authorization_path: Path,
        acceptance_run_id: Any,
        subject_graph_digest: Any,
        linked_module_digest: Any,
        release_artifact_digest: Any,
        policy_digest: Any,
        policy_authorization_digest: Any,
        source_revision: Any,
        checker_digest: str,
        evidence_digest: Any,
        toolchain_digest: Any,
        corpus_digest: Any,
        prior_gates_root: Optional[str],
    ) -> Optional[dict[str, Any]]:
        """Re-run one schema-owned checker using the fixed verification protocol."""
        location = f"{gate}.checker_run"
        with tempfile.TemporaryDirectory(prefix=f"trust-{gate.lower()}-checker-") as tmp:
            checker_snapshot = Path(tmp) / "checker.py"
            checker_snapshot.write_bytes(checker_bytes)
            checker_snapshot.chmod(0o444)
            bytecode_prefix = Path(tmp) / "bytecode"
            bytecode_prefix.mkdir()
            command = [
                *_isolated_python(bytecode_prefix),
                str(checker_snapshot),
                "--verify-evidence",
                str(evidence_path),
                "--root",
                str(self.root),
                "--toolchain-manifest",
                str(toolchain_path),
                "--corpus-manifest",
                str(corpus_path),
                "--subject-graph",
                str(subject_graph_path),
                "--linked-module",
                str(linked_module_path),
                "--release-artifact",
                str(release_artifact_path),
                "--authority-policy",
                str(policy_path),
                "--policy-authorization",
                str(policy_authorization_path),
                "--acceptance-run-id",
                str(acceptance_run_id),
                "--source-revision",
                str(source_revision),
                "--checker-sha256",
                checker_digest,
                "--evidence-sha256",
                str(evidence_digest),
                "--toolchain-sha256",
                str(toolchain_digest),
                "--corpus-manifest-sha256",
                str(corpus_digest),
                "--subject-graph-sha256",
                str(subject_graph_digest),
                "--linked-module-sha256",
                str(linked_module_digest),
                "--release-artifact-sha256",
                str(release_artifact_digest),
                "--authority-policy-sha256",
                str(policy_digest),
                "--policy-authorization-sha256",
                str(policy_authorization_digest),
            ]
            # G1-G7 are the pre-seal facts.  They must not depend on the final
            # receipt (which includes the G8 seal), or the seal becomes a hash
            # fixed-point.  Only G8 inspects the final receipt after receiving
            # the already-computed G1-G7 root.
            if gate == "G8":
                command.extend(["--receipt", str(self.receipt_path)])
                if self.trusted_owner_key is not None:
                    command.extend(["--trusted-owner-key", str(self.trusted_owner_key)])
                if self.external_verifier is not None:
                    command.extend(["--external-verifier", str(self.external_verifier)])
                if self.external_verifier_sha256 is not None:
                    command.extend(["--external-verifier-sha256", self.external_verifier_sha256])
            if prior_gates_root is not None:
                command.extend(["--prior-gates-root", prior_gates_root])
            checker_env = {
                "HOME": tmp,
                "LANG": "C.UTF-8",
                "LC_ALL": "C.UTF-8",
                "PATH": "/usr/bin:/bin",
                "PYTHONHASHSEED": "0",
                "TZ": "UTC",
            }
            try:
                process = subprocess.run(
                    command,
                    cwd=self.root,
                    env=checker_env,
                    check=False,
                    capture_output=True,
                    text=True,
                    timeout=1800,
                )
            except (OSError, subprocess.TimeoutExpired) as exc:
                self.error(location, f"could not execute checker: {exc}")
                return None
        if process.returncode != 0:
            detail = process.stderr.strip() or process.stdout.strip() or "no diagnostic"
            self.error(location, f"checker exited {process.returncode}: {detail[:1000]}")
        try:
            verdict = _strict_json(process.stdout)
        except (ValueError, RecursionError) as exc:
            self.error(location, f"checker stdout is not one JSON verdict: {exc}")
            return None
        if not isinstance(verdict, dict):
            self.error(location, "checker verdict must be a JSON object")
            return None
        return verdict

    def validate_manifest_header(
        self,
        value: Optional[dict[str, Any]],
        *,
        schema: str,
        location: str,
        acceptance_run_id: Any,
        source_revision: Any,
    ) -> bool:
        if value is None:
            return False
        expected = {
            "schema": schema,
            "goal_id": GOAL_ID,
            "acceptance_run_id": acceptance_run_id,
            "source_revision": source_revision,
        }
        ok = True
        for key, wanted in expected.items():
            if value.get(key) != wanted:
                self.error(f"{location}.{key}", f"must equal {wanted!r}")
                ok = False
        return ok

    def validate_contract_header(
        self,
        value: Optional[dict[str, Any]],
        *,
        schema: str,
        location: str,
    ) -> bool:
        if value is None:
            return False
        expected = {
            "schema": schema,
            "goal_id": GOAL_ID,
            "repository_id": REPOSITORY_ID,
        }
        ok = True
        for key, wanted in expected.items():
            if value.get(key) != wanted:
                self.error(f"{location}.{key}", f"must equal {wanted!r}")
                ok = False
        return ok

    def validate_admission_contract(
        self,
        value: Optional[dict[str, Any]],
    ) -> dict[str, dict[str, Any]]:
        location = "authority_contracts.admission"
        result: dict[str, dict[str, Any]] = {}
        if value is None:
            return result
        self.exact_keys(value, {"schema", "goal_id", "repository_id", "lanes"}, location)
        self.validate_contract_header(
            value,
            schema=AUTHORITY_CONTRACTS["admission"][1],
            location=location,
        )
        lanes = value.get("lanes")
        if not self.exact_keys(lanes, {"rust", "lean", "mixed"}, f"{location}.lanes"):
            return result
        for lane in ("rust", "lean", "mixed"):
            lane_value = lanes.get(lane)
            lane_location = f"{location}.lanes.{lane}"
            if not self.exact_keys(
                lane_value,
                {
                    "upstream_repository",
                    "upstream_revision",
                    "upstream_tree_sha256",
                    "feature_manifest",
                    "suite_manifest",
                    "exception_ledger",
                    "entries",
                },
                lane_location,
            ):
                continue
            repository = lane_value.get("upstream_repository")
            revision = lane_value.get("upstream_revision")
            tree_digest = lane_value.get("upstream_tree_sha256")
            if not isinstance(repository, str) or not repository:
                self.error(f"{lane_location}.upstream_repository", "must be non-empty")
            if not isinstance(revision, str) or not GIT_REVISION.fullmatch(revision):
                self.error(f"{lane_location}.upstream_revision", "must be a Git revision")
            if not isinstance(tree_digest, str) or not HEX_DIGEST.fullmatch(tree_digest):
                self.error(f"{lane_location}.upstream_tree_sha256", "must be 64-hex")

            support_docs: dict[str, Optional[dict[str, Any]]] = {}
            for field in ("feature_manifest", "suite_manifest", "exception_ledger"):
                path = self.resolve_ref(lane_value.get(field), f"{lane_location}.{field}")
                support_docs[field] = (
                    self.load_json(path, f"{lane_location}.{field}")
                    if path is not None and _is_regular_file(path)
                    else None
                )

            entries = lane_value.get("entries")
            if not isinstance(entries, list) or not entries:
                self.error(f"{lane_location}.entries", "must be a non-empty list")
                continue
            entry_ids: set[str] = set()
            admitted_ids: set[str] = set()
            normalized_entries: list[dict[str, Any]] = []
            for index, entry in enumerate(entries):
                entry_location = f"{lane_location}.entries[{index}]"
                if not self.exact_keys(
                    entry,
                    {"id", "kind", "admitted", "source", "expected_outcome"},
                    entry_location,
                ):
                    continue
                entry_id = entry.get("id")
                if not isinstance(entry_id, str) or not entry_id or entry_id in entry_ids:
                    self.error(f"{entry_location}.id", "must be unique and non-empty")
                    continue
                entry_ids.add(entry_id)
                if type(entry.get("admitted")) is not bool:
                    self.error(f"{entry_location}.admitted", "must be a boolean")
                elif entry["admitted"]:
                    admitted_ids.add(entry_id)
                if not isinstance(entry.get("kind"), str) or not entry.get("kind"):
                    self.error(f"{entry_location}.kind", "must be non-empty")
                if not isinstance(entry.get("expected_outcome"), str) or not entry.get(
                    "expected_outcome"
                ):
                    self.error(f"{entry_location}.expected_outcome", "must be non-empty")
                self.resolve_ref(entry.get("source"), f"{entry_location}.source")
                normalized_entries.append(entry)
            if not admitted_ids:
                self.error(lane_location, "must owner-authorize at least one admitted entry")

            feature_manifest = support_docs["feature_manifest"]
            feature_location = f"{lane_location}.feature_manifest"
            if feature_manifest is not None:
                self.exact_keys(feature_manifest, {"schema", "lane", "features"}, feature_location)
                if feature_manifest.get("schema") != "trust.two-language.language-feature-manifest/v1":
                    self.error(f"{feature_location}.schema", "has the wrong schema")
                if feature_manifest.get("lane") != lane:
                    self.error(f"{feature_location}.lane", f"must equal {lane!r}")
                features = feature_manifest.get("features")
                if (
                    not isinstance(features, list)
                    or not features
                    or not all(isinstance(item, str) and item for item in features)
                    or len(features) != len(set(features))
                ):
                    self.error(f"{feature_location}.features", "must be non-empty and unique")

            suite_manifest = support_docs["suite_manifest"]
            suite_location = f"{lane_location}.suite_manifest"
            if suite_manifest is not None:
                self.exact_keys(suite_manifest, {"schema", "lane", "cases"}, suite_location)
                if suite_manifest.get("schema") != "trust.two-language.suite-manifest/v1":
                    self.error(f"{suite_location}.schema", "has the wrong schema")
                if suite_manifest.get("lane") != lane:
                    self.error(f"{suite_location}.lane", f"must equal {lane!r}")
                cases = suite_manifest.get("cases")
                if (
                    not isinstance(cases, list)
                    or not all(isinstance(case, str) for case in cases)
                    or sorted(cases) != sorted(entry_ids)
                ):
                    self.error(
                        f"{suite_location}.cases",
                        "must enumerate exactly the owner-authorized entry IDs",
                    )

            ledger = support_docs["exception_ledger"]
            ledger_location = f"{lane_location}.exception_ledger"
            if ledger is not None:
                self.exact_keys(ledger, {"schema", "lane", "rows"}, ledger_location)
                if ledger.get("schema") != "trust.two-language.exception-ledger/v1":
                    self.error(f"{ledger_location}.schema", "has the wrong schema")
                if ledger.get("lane") != lane:
                    self.error(f"{ledger_location}.lane", f"must equal {lane!r}")
                rows = ledger.get("rows")
                if not isinstance(rows, list):
                    self.error(f"{ledger_location}.rows", "must be a list")
                else:
                    ledger_ids: set[str] = set()
                    for index, row in enumerate(rows):
                        row_location = f"{ledger_location}.rows[{index}]"
                        if not self.exact_keys(
                            row,
                            {"entry_id", "classification", "reason"},
                            row_location,
                        ):
                            continue
                        entry_id = row.get("entry_id")
                        if (
                            not isinstance(entry_id, str)
                            or entry_id not in entry_ids
                            or entry_id in ledger_ids
                        ):
                            self.error(
                                f"{row_location}.entry_id",
                                "must uniquely name an owner-authorized entry",
                            )
                        else:
                            ledger_ids.add(entry_id)
                        if isinstance(entry_id, str) and entry_id in admitted_ids:
                            self.error(
                                f"{row_location}.entry_id",
                                "an admitted program cannot be waived by the exception ledger",
                            )
                        if row.get("classification") != "non-applicable-harness":
                            self.error(
                                f"{row_location}.classification",
                                "only non-applicable-harness is authorized",
                            )
                        if not isinstance(row.get("reason"), str) or not row.get("reason"):
                            self.error(f"{row_location}.reason", "must be non-empty")
            result[lane] = {
                "upstream_revision": revision,
                "entries": normalized_entries,
            }
        return result

    def validate_semantics_contract(
        self,
        value: Optional[dict[str, Any]],
    ) -> dict[str, dict[str, str]]:
        location = "authority_contracts.semantics"
        result: dict[str, dict[str, str]] = {}
        if value is None:
            return result
        self.exact_keys(
            value,
            {"schema", "goal_id", "repository_id", "definitions"},
            location,
        )
        self.validate_contract_header(
            value,
            schema=AUTHORITY_CONTRACTS["semantics"][1],
            location=location,
        )
        definitions = value.get("definitions")
        if not self.exact_keys(definitions, SEMANTICS_DEFINITIONS, f"{location}.definitions"):
            return result
        ids: set[str] = set()
        paths: set[Path] = set()
        identities: set[tuple[int, int]] = set()
        for role in sorted(SEMANTICS_DEFINITIONS):
            ref_id, path, digest = self.resolve_named_ref(
                definitions.get(role),
                f"{location}.definitions.{role}",
            )
            if ref_id is not None and ref_id in ids:
                self.error(f"{location}.definitions.{role}.id", "semantic IDs must be distinct")
            elif ref_id is not None:
                ids.add(ref_id)
            # Distinct files, not only distinct spellings: a case alias on a
            # case-insensitive volume or a hard link names one file twice, and
            # resolve() canonicalizes neither.  A path that cannot be stat'ed
            # is already refused by resolve_ref.
            identity = _identity_or_none(path) if path is not None else None
            if path is not None and (path in paths or identity in identities):
                self.error(f"{location}.definitions.{role}.path", "semantic paths must be distinct")
            elif path is not None:
                paths.add(path)
                if identity is not None:
                    identities.add(identity)
            if ref_id is not None and digest is not None:
                result[role] = {"id": ref_id, "sha256": digest}
        return result

    def validate_obligation_contract(
        self,
        value: Optional[dict[str, Any]],
    ) -> dict[str, Any]:
        location = "authority_contracts.obligations"
        result: dict[str, Any] = {"rules": {}, "formula_encoder": {}}
        if value is None:
            return result
        self.exact_keys(
            value,
            {"schema", "goal_id", "repository_id", "rules", "formula_encoder"},
            location,
        )
        self.validate_contract_header(
            value,
            schema=AUTHORITY_CONTRACTS["obligations"][1],
            location=location,
        )
        encoder_id, _encoder_path, encoder_digest = self.resolve_named_ref(
            value.get("formula_encoder"),
            f"{location}.formula_encoder",
        )
        if encoder_id is not None and encoder_digest is not None:
            result["formula_encoder"] = {"id": encoder_id, "sha256": encoder_digest}
        rules = value.get("rules")
        if not isinstance(rules, list) or not rules:
            self.error(f"{location}.rules", "must be a non-empty list")
            return result
        classes: set[str] = set()
        for index, rule in enumerate(rules):
            row_location = f"{location}.rules[{index}]"
            if not self.exact_keys(
                rule,
                {"id", "class", "applicability", "formula_schema"},
                row_location,
            ):
                continue
            rule_id = rule.get("id")
            rule_class = rule.get("class")
            if (
                not isinstance(rule_id, str)
                or not CHECKER_ID.fullmatch(rule_id)
                or rule_id in result["rules"]
            ):
                self.error(f"{row_location}.id", "must be a unique typed rule ID")
                continue
            if not isinstance(rule_class, str) or rule_class not in OBLIGATION_CLASSES:
                self.error(f"{row_location}.class", "is not a required obligation class")
            else:
                classes.add(rule_class)
            self.resolve_named_ref(rule.get("applicability"), f"{row_location}.applicability")
            self.resolve_named_ref(rule.get("formula_schema"), f"{row_location}.formula_schema")
            result["rules"][rule_id] = rule
        if classes != OBLIGATION_CLASSES:
            self.error(
                f"{location}.rules",
                f"must cover exactly the required obligation classes {sorted(OBLIGATION_CLASSES)}",
            )
        return result

    def validate_proof_authority_contract(
        self,
        value: Optional[dict[str, Any]],
    ) -> dict[str, Any]:
        location = "authority_contracts.proof_authority"
        result: dict[str, Any] = {"kernels": {}, "canonical_proposition_encoder": {}}
        if value is None:
            return result
        self.exact_keys(
            value,
            {
                "schema",
                "goal_id",
                "repository_id",
                "canonical_proposition_encoder",
                "kernels",
                "axiom_policy",
                "external_olean_policy",
                "denied_axioms",
            },
            location,
        )
        self.validate_contract_header(
            value,
            schema=AUTHORITY_CONTRACTS["proof_authority"][1],
            location=location,
        )
        encoder_id, _encoder_path, encoder_digest = self.resolve_named_ref(
            value.get("canonical_proposition_encoder"),
            f"{location}.canonical_proposition_encoder",
        )
        if encoder_id is not None and encoder_digest is not None:
            result["canonical_proposition_encoder"] = {
                "id": encoder_id,
                "sha256": encoder_digest,
            }
        self.resolve_named_ref(value.get("axiom_policy"), f"{location}.axiom_policy")
        self.resolve_named_ref(
            value.get("external_olean_policy"),
            f"{location}.external_olean_policy",
        )
        if value.get("denied_axioms") != ["sorryAx"]:
            self.error(f"{location}.denied_axioms", "must be exactly ['sorryAx']")
        kernels = value.get("kernels")
        if not isinstance(kernels, list) or not kernels:
            self.error(f"{location}.kernels", "must be a non-empty list")
            return result
        for index, kernel in enumerate(kernels):
            row_location = f"{location}.kernels[{index}]"
            if not self.exact_keys(
                kernel,
                {
                    "id",
                    "environment_sha256",
                    "artifact",
                    "proof_grades",
                    "axiom_allowlist_root_sha256",
                },
                row_location,
            ):
                continue
            kernel_id = kernel.get("id")
            if (
                not isinstance(kernel_id, str)
                or not CHECKER_ID.fullmatch(kernel_id)
                or kernel_id in result["kernels"]
            ):
                self.error(f"{row_location}.id", "must be a unique typed kernel ID")
                continue
            for field in ("environment_sha256", "axiom_allowlist_root_sha256"):
                digest = kernel.get(field)
                if not isinstance(digest, str) or not HEX_DIGEST.fullmatch(digest):
                    self.error(f"{row_location}.{field}", "must be 64-hex")
            self.resolve_named_ref(kernel.get("artifact"), f"{row_location}.artifact")
            grades = kernel.get("proof_grades")
            if (
                not isinstance(grades, list)
                or not grades
                or not all(isinstance(item, str) and item for item in grades)
                or len(grades) != len(set(grades))
            ):
                self.error(f"{row_location}.proof_grades", "must be non-empty and unique")
            result["kernels"][kernel_id] = kernel
        return result

    def validate_compatibility_contract(self, value: Optional[dict[str, Any]]) -> None:
        location = "authority_contracts.compatibility_surfaces"
        if value is None:
            return
        self.exact_keys(
            value,
            {"schema", "goal_id", "repository_id", "surfaces"},
            location,
        )
        self.validate_contract_header(
            value,
            schema=AUTHORITY_CONTRACTS["compatibility_surfaces"][1],
            location=location,
        )
        surfaces = value.get("surfaces")
        if not self.exact_keys(surfaces, set(COMPATIBILITY_CAPABILITIES), f"{location}.surfaces"):
            return
        for surface, required_capabilities in COMPATIBILITY_CAPABILITIES.items():
            row = surfaces.get(surface)
            row_location = f"{location}.surfaces.{surface}"
            if not self.exact_keys(
                row,
                {
                    "required",
                    "upstream_repository",
                    "upstream_version",
                    "feature_manifest",
                    "corpus_root_sha256",
                    "elaborator",
                    "ingestion_authority",
                    "computational_destinations",
                    "computational_image",
                    "proposition_destinations",
                    "proposition_image",
                    "semantic_capabilities",
                },
                row_location,
            ):
                continue
            if row.get("required") is not True:
                self.error(f"{row_location}.required", "must be the boolean true")
            for field in ("upstream_repository", "upstream_version"):
                if not isinstance(row.get(field), str) or not row.get(field):
                    self.error(f"{row_location}.{field}", "must be non-empty")
            corpus_root = row.get("corpus_root_sha256")
            if not isinstance(corpus_root, str) or not HEX_DIGEST.fullmatch(corpus_root):
                self.error(f"{row_location}.corpus_root_sha256", "must be 64-hex")
            if row.get("ingestion_authority") != "zero-authority":
                self.error(
                    f"{row_location}.ingestion_authority",
                    "must equal 'zero-authority'",
                )
            destinations = COMPATIBILITY_IMAGE_DESTINATIONS[surface]
            computational_destinations = row.get("computational_destinations")
            proposition_destinations = row.get("proposition_destinations")
            if computational_destinations != destinations["computational"]:
                self.error(
                    f"{row_location}.computational_destinations",
                    f"must equal {destinations['computational']!r}",
                )
            if proposition_destinations != destinations["proposition"]:
                self.error(
                    f"{row_location}.proposition_destinations",
                    f"must equal {destinations['proposition']!r}",
                )
            computational_ref: tuple[Optional[str], Optional[Path], Optional[str]]
            if destinations["computational"]:
                computational_ref = self.resolve_named_ref(
                    row.get("computational_image"),
                    f"{row_location}.computational_image",
                )
            else:
                computational_ref = (None, None, None)
                if row.get("computational_image") is not None:
                    self.error(
                        f"{row_location}.computational_image",
                        "must be null because this surface has no computational image",
                    )
            proposition_ref = self.resolve_named_ref(
                row.get("proposition_image"),
                f"{row_location}.proposition_image",
            )
            if destinations["computational"]:
                for index, label in enumerate(("id", "path", "sha256")):
                    computational_value = computational_ref[index]
                    proposition_value = proposition_ref[index]
                    if (
                        computational_value is not None
                        and proposition_value is not None
                        and computational_value == proposition_value
                    ):
                        self.error(
                            f"{row_location}.computational_image.{label}",
                            "must not alias the distinct canonical proposition image",
                        )
            capabilities = row.get("semantic_capabilities")
            if (
                not isinstance(capabilities, list)
                or not all(isinstance(item, str) for item in capabilities)
                or set(capabilities) != required_capabilities
            ):
                self.error(
                    f"{row_location}.semantic_capabilities",
                    f"must equal {sorted(required_capabilities)}",
                )
            feature_path = self.resolve_ref(
                row.get("feature_manifest"),
                f"{row_location}.feature_manifest",
            )
            self.resolve_named_ref(row.get("elaborator"), f"{row_location}.elaborator")
            if feature_path is not None and _is_regular_file(feature_path):
                manifest = self.load_json(feature_path, f"{row_location}.feature_manifest")
                if manifest is not None:
                    self.exact_keys(
                        manifest,
                        {"schema", "surface", "features"},
                        f"{row_location}.feature_manifest",
                    )
                    if manifest.get("schema") != "trust.two-language.compatibility-feature-manifest/v1":
                        self.error(f"{row_location}.feature_manifest.schema", "has the wrong schema")
                    if manifest.get("surface") != surface:
                        self.error(f"{row_location}.feature_manifest.surface", "has the wrong surface")
                    features = manifest.get("features")
                    if not isinstance(features, list) or not features:
                        self.error(f"{row_location}.feature_manifest.features", "must be non-empty")

    def validate_codegen_contract(
        self,
        value: Optional[dict[str, Any]],
    ) -> dict[str, Any]:
        location = "authority_contracts.codegen_surface"
        result: dict[str, Any] = {
            "targets": {},
            "translation_relation": {},
            "cells": {},
            "matrix_root": None,
        }
        if value is None:
            return result
        self.exact_keys(
            value,
            {
                "schema",
                "goal_id",
                "repository_id",
                "translation_relation",
                "targets",
                "matrix_cells",
            },
            location,
        )
        self.validate_contract_header(
            value,
            schema=AUTHORITY_CONTRACTS["codegen_surface"][1],
            location=location,
        )
        relation_id, _relation_path, relation_digest = self.resolve_named_ref(
            value.get("translation_relation"),
            f"{location}.translation_relation",
        )
        if relation_id is not None and relation_digest is not None:
            result["translation_relation"] = {
                "id": relation_id,
                "sha256": relation_digest,
            }
        targets = value.get("targets")
        if not isinstance(targets, list) or not targets:
            self.error(f"{location}.targets", "must be a non-empty list")
            return result
        for index, target in enumerate(targets):
            row_location = f"{location}.targets[{index}]"
            if not self.exact_keys(
                target,
                {
                    "id",
                    "triple",
                    "abis",
                    "crate_types",
                    "runtimes",
                    "startups",
                    "linkers",
                    "unwind_modes",
                    "debug_modes",
                    "opt_levels",
                    "profiles",
                },
                row_location,
            ):
                continue
            target_id = target.get("id")
            if (
                not isinstance(target_id, str)
                or not CHECKER_ID.fullmatch(target_id)
                or target_id in result["targets"]
            ):
                self.error(f"{row_location}.id", "must be a unique typed target ID")
                continue
            target_valid = True
            if not isinstance(target.get("triple"), str) or not target.get("triple"):
                self.error(f"{row_location}.triple", "must be non-empty")
                target_valid = False
            for field in (
                "abis",
                "crate_types",
                "runtimes",
                "startups",
                "linkers",
                "unwind_modes",
                "debug_modes",
                "opt_levels",
                "profiles",
            ):
                items = target.get(field)
                if (
                    not isinstance(items, list)
                    or not items
                    or not all(isinstance(item, str) and item for item in items)
                    or len(items) != len(set(items))
                ):
                    self.error(f"{row_location}.{field}", "must be non-empty and unique")
                    target_valid = False
            if target_valid:
                result["targets"][target_id] = target

        matrix_cells = value.get("matrix_cells")
        if not isinstance(matrix_cells, list) or not matrix_cells:
            self.error(f"{location}.matrix_cells", "must be a non-empty list")
            return result
        seen_cell_ids: set[str] = set()
        seen_configurations: set[tuple[str, ...]] = set()
        projections: dict[str, dict[str, set[str]]] = {
            target_id: {
                axis: set() for axis in CODEGEN_TARGET_AXIS_BY_CELL_FIELD.values()
            }
            for target_id in result["targets"]
        }
        for index, cell in enumerate(matrix_cells):
            row_location = f"{location}.matrix_cells[{index}]"
            if not self.exact_keys(
                cell,
                {"id", *CODEGEN_CELL_FIELDS},
                row_location,
            ):
                continue
            cell_id = cell.get("id")
            if (
                not isinstance(cell_id, str)
                or not CHECKER_ID.fullmatch(cell_id)
                or cell_id in seen_cell_ids
            ):
                self.error(f"{row_location}.id", "must be a unique typed matrix-cell ID")
                continue
            seen_cell_ids.add(cell_id)
            cell_valid = True
            for field in CODEGEN_CELL_FIELDS:
                if not isinstance(cell.get(field), str) or not cell.get(field):
                    self.error(f"{row_location}.{field}", "must be a non-empty string")
                    cell_valid = False
            target_id = cell.get("target_id")
            target = (
                result["targets"].get(target_id)
                if isinstance(target_id, str)
                else None
            )
            if target is None:
                self.error(
                    f"{row_location}.target_id",
                    "must name an owner-authorized codegen target",
                )
                cell_valid = False
            else:
                for field, axis in CODEGEN_TARGET_AXIS_BY_CELL_FIELD.items():
                    if cell.get(field) not in target[axis]:
                        self.error(
                            f"{row_location}.{field}",
                            f"must select a value from target.{axis}",
                        )
                        cell_valid = False
            if not cell_valid:
                continue
            configuration = tuple(cell[field] for field in CODEGEN_CELL_FIELDS)
            if configuration in seen_configurations:
                self.error(
                    row_location,
                    "must not duplicate an authorized configuration under another cell ID",
                )
                continue
            seen_configurations.add(configuration)
            normalized_cell = {
                "id": cell_id,
                **{field: cell[field] for field in CODEGEN_CELL_FIELDS},
            }
            result["cells"][cell_id] = normalized_cell
            for field, axis in CODEGEN_TARGET_AXIS_BY_CELL_FIELD.items():
                projections[target_id][axis].add(cell[field])

        for target_id, target in result["targets"].items():
            for axis in CODEGEN_TARGET_AXIS_BY_CELL_FIELD.values():
                observed = projections[target_id][axis]
                expected = set(target[axis])
                if observed != expected:
                    self.error(
                        f"{location}.matrix_cells.{target_id}.{axis}",
                        "signed cells must cover every declared target-axis value exactly",
                    )
        if result["cells"]:
            result["matrix_root"] = _canonical_json_sha256(
                sorted(result["cells"].values(), key=lambda row: row["id"])
            )
        return result

    def validate_acceptance_environment_contract(
        self,
        value: Optional[dict[str, Any]],
    ) -> dict[str, Any]:
        location = "authority_contracts.acceptance_environment"
        result: dict[str, Any] = {"component_roster": []}
        if value is None:
            return result
        self.exact_keys(
            value,
            {"schema", "goal_id", "repository_id", "component_roster", "run_modes"},
            location,
        )
        self.validate_contract_header(
            value,
            schema=AUTHORITY_CONTRACTS["acceptance_environment"][1],
            location=location,
        )
        roster = value.get("component_roster")
        if not isinstance(roster, list) or not roster:
            self.error(f"{location}.component_roster", "must be a non-empty list")
        else:
            roles: set[str] = set()
            names: set[str] = set()
            for index, component in enumerate(roster):
                row_location = f"{location}.component_roster[{index}]"
                if not self.exact_keys(
                    component,
                    {"role", "name", "version", "artifact_sha256"},
                    row_location,
                ):
                    continue
                role = component.get("role")
                name = component.get("name")
                if not isinstance(role, str) or role not in TOOLCHAIN_ROLES or role in roles:
                    self.error(f"{row_location}.role", "must uniquely name a required role")
                else:
                    roles.add(role)
                if not isinstance(name, str) or not name or name in names:
                    self.error(f"{row_location}.name", "must be unique and non-empty")
                else:
                    names.add(name)
                if not isinstance(component.get("version"), str) or not component.get("version"):
                    self.error(f"{row_location}.version", "must be non-empty")
                digest = component.get("artifact_sha256")
                if not isinstance(digest, str) or not HEX_DIGEST.fullmatch(digest):
                    self.error(f"{row_location}.artifact_sha256", "must be 64-hex")
            if roles != TOOLCHAIN_ROLES:
                self.error(
                    f"{location}.component_roster",
                    f"must cover exactly the required roles {sorted(TOOLCHAIN_ROLES)}",
                )
            result["component_roster"] = roster
        run_modes = value.get("run_modes")
        if (
            not isinstance(run_modes, list)
            or not all(isinstance(item, str) for item in run_modes)
            or set(run_modes) != ACCEPTANCE_RUN_MODES
        ):
            self.error(
                f"{location}.run_modes",
                f"must equal {sorted(ACCEPTANCE_RUN_MODES)}",
            )
        return result

    def validate_authority_contracts(
        self,
        policy: Optional[dict[str, Any]],
    ) -> dict[str, Any]:
        result: dict[str, Any] = {}
        if policy is None:
            return result
        contracts = policy.get("contracts")
        location = "authority_policy.contracts"
        if not self.exact_keys(contracts, set(AUTHORITY_CONTRACTS), location):
            return result
        paths: set[Path] = set()
        digests: set[str] = set()
        loaded: dict[str, Optional[dict[str, Any]]] = {}
        for role, (contract_id, _schema) in AUTHORITY_CONTRACTS.items():
            _ref_id, path, digest = self.resolve_named_ref(
                contracts.get(role),
                f"{location}.{role}",
                expected_id=contract_id,
            )
            if path is not None and path in paths:
                self.error(f"{location}.{role}.path", "contract paths must be distinct")
            elif path is not None:
                paths.add(path)
            if digest is not None and digest in digests:
                self.error(f"{location}.{role}.sha256", "contract digests must be distinct")
            elif digest is not None:
                digests.add(digest)
            loaded[role] = (
                self.load_json(path, f"authority_contracts.{role}")
                if path is not None and _is_regular_file(path)
                else None
            )
            result[f"{role}_sha256"] = digest
        result["admission"] = self.validate_admission_contract(loaded.get("admission"))
        result["semantics"] = self.validate_semantics_contract(loaded.get("semantics"))
        result["obligations"] = self.validate_obligation_contract(loaded.get("obligations"))
        result["proof_authority"] = self.validate_proof_authority_contract(
            loaded.get("proof_authority")
        )
        self.validate_compatibility_contract(loaded.get("compatibility_surfaces"))
        result["codegen_surface"] = self.validate_codegen_contract(
            loaded.get("codegen_surface")
        )
        result["acceptance_environment"] = self.validate_acceptance_environment_contract(
            loaded.get("acceptance_environment")
        )
        return result

    def validate_toolchain_manifest(
        self,
        value: Optional[dict[str, Any]],
        acceptance_run_id: Any,
        source_revision: Any,
        authority_contracts: dict[str, Any],
    ) -> None:
        location = "toolchain_manifest"
        if value is None:
            return
        self.exact_keys(
            value,
            {"schema", "goal_id", "acceptance_run_id", "source_revision", "components"},
            location,
        )
        self.validate_manifest_header(
            value,
            schema=TOOLCHAIN_SCHEMA,
            location=location,
            acceptance_run_id=acceptance_run_id,
            source_revision=source_revision,
        )
        components = value.get("components")
        if not isinstance(components, list) or not components:
            self.error(f"{location}.components", "must be a non-empty list")
            return
        names: set[str] = set()
        roles: set[str] = set()
        normalized: list[dict[str, Any]] = []
        for index, component in enumerate(components):
            row_location = f"{location}.components[{index}]"
            if not self.exact_keys(
                component,
                {"role", "name", "version", "artifact"},
                row_location,
            ):
                continue
            role = component.get("role")
            name = component.get("name")
            version = component.get("version")
            if not isinstance(role, str) or role not in TOOLCHAIN_ROLES or role in roles:
                self.error(f"{row_location}.role", "must uniquely name a required role")
            else:
                roles.add(role)
            if not isinstance(name, str) or not name:
                self.error(f"{row_location}.name", "must be a non-empty string")
            elif name in names:
                self.error(f"{row_location}.name", f"duplicate component {name!r}")
            else:
                names.add(name)
            if not isinstance(version, str) or not version:
                self.error(f"{row_location}.version", "must be a non-empty string")
            self.resolve_ref(component.get("artifact"), f"{row_location}.artifact")
            artifact = component.get("artifact")
            normalized.append(
                {
                    "role": role,
                    "name": name,
                    "version": version,
                    "artifact_sha256": (
                        artifact.get("sha256") if isinstance(artifact, dict) else None
                    ),
                }
            )
        if roles != TOOLCHAIN_ROLES:
            self.error(
                f"{location}.components",
                f"must cover exactly the required roles {sorted(TOOLCHAIN_ROLES)}",
            )
        expected_roster = authority_contracts.get("acceptance_environment", {}).get(
            "component_roster",
            [],
        )
        if sorted(normalized, key=lambda row: str(row.get("role"))) != sorted(
            expected_roster,
            key=lambda row: str(row.get("role")) if isinstance(row, dict) else "",
        ):
            self.error(
                f"{location}.components",
                "must equal the owner-authorized component roster exactly",
            )

    def validate_corpus_manifest(
        self,
        value: Optional[dict[str, Any]],
        acceptance_run_id: Any,
        source_revision: Any,
        authority_contracts: dict[str, Any],
    ) -> set[str]:
        location = "corpus_manifest"
        admitted_ids: set[str] = set()
        if value is None:
            return admitted_ids
        self.exact_keys(
            value,
            {
                "schema",
                "goal_id",
                "acceptance_run_id",
                "source_revision",
                "repository_id",
                "rust",
                "lean",
                "mixed",
            },
            location,
        )
        self.validate_manifest_header(
            value,
            schema=CORPUS_SCHEMA,
            location=location,
            acceptance_run_id=acceptance_run_id,
            source_revision=source_revision,
        )
        if value.get("repository_id") != REPOSITORY_ID:
            self.error(f"{location}.repository_id", f"must equal {REPOSITORY_ID!r}")
        ids: set[str] = set()
        authorized_lanes = authority_contracts.get("admission", {})
        admission_digest = authority_contracts.get("admission_sha256")
        for lane in ("rust", "lean", "mixed"):
            lane_value = value.get(lane)
            lane_location = f"{location}.{lane}"
            if not self.exact_keys(
                lane_value,
                {"upstream_revision", "admission_policy_sha256", "entries"},
                lane_location,
            ):
                continue
            upstream_revision = lane_value.get("upstream_revision")
            policy_digest = lane_value.get("admission_policy_sha256")
            if not isinstance(upstream_revision, str) or not upstream_revision:
                self.error(f"{lane_location}.upstream_revision", "must be a non-empty string")
            if not isinstance(policy_digest, str) or not HEX_DIGEST.fullmatch(policy_digest):
                self.error(
                    f"{lane_location}.admission_policy_sha256",
                    "must be a lowercase 64-hex digest",
                )
            elif policy_digest != admission_digest:
                self.error(
                    f"{lane_location}.admission_policy_sha256",
                    "must equal the owner-signed admission contract digest",
                )
            authorized_lane = authorized_lanes.get(lane, {})
            if upstream_revision != authorized_lane.get("upstream_revision"):
                self.error(
                    f"{lane_location}.upstream_revision",
                    "must equal the owner-authorized upstream revision",
                )
            entries = lane_value.get("entries")
            if not isinstance(entries, list) or not entries:
                self.error(f"{lane_location}.entries", "must be a non-empty list")
                continue
            lane_admitted = 0
            normalized_entries: list[dict[str, Any]] = []
            for index, entry in enumerate(entries):
                entry_location = f"{lane_location}.entries[{index}]"
                if not self.exact_keys(
                    entry,
                    {"id", "kind", "admitted", "source", "expected_outcome"},
                    entry_location,
                ):
                    continue
                entry_id = entry.get("id")
                kind = entry.get("kind")
                if not isinstance(entry_id, str) or not entry_id:
                    self.error(f"{entry_location}.id", "must be a non-empty string")
                elif entry_id in ids:
                    self.error(f"{entry_location}.id", f"duplicate corpus id {entry_id!r}")
                else:
                    ids.add(entry_id)
                    if entry.get("admitted") is True:
                        admitted_ids.add(entry_id)
                        lane_admitted += 1
                if not isinstance(kind, str) or not kind:
                    self.error(f"{entry_location}.kind", "must be a non-empty string")
                if type(entry.get("admitted")) is not bool:
                    self.error(f"{entry_location}.admitted", "must be a boolean")
                if not isinstance(entry.get("expected_outcome"), str) or not entry.get(
                    "expected_outcome"
                ):
                    self.error(f"{entry_location}.expected_outcome", "must be non-empty")
                self.resolve_ref(entry.get("source"), f"{entry_location}.source")
                normalized_entries.append(entry)
            if lane_admitted == 0:
                self.error(lane_location, "must contain at least one admitted program")
            if normalized_entries != authorized_lane.get("entries"):
                self.error(
                    f"{lane_location}.entries",
                    "must exactly equal the owner-signed admission population",
                )
        if not admitted_ids:
            self.error(location, "must contain at least one admitted program")
        return admitted_ids

    def validate_subject_graph(
        self,
        value: Optional[dict[str, Any]],
        acceptance_run_id: Any,
        source_revision: Any,
        admitted_corpus_ids: set[str],
        linked_module_digest: Any,
        release_artifact_digest: Any,
        authority_contracts: dict[str, Any],
    ) -> dict[str, set[str]]:
        location = "subject_graph"
        artifact_digests: dict[str, set[str]] = {
            "modules": set(),
            "objects": set(),
            "executables": set(),
            "translation_evidence": set(),
        }
        if value is None:
            return artifact_digests
        self.exact_keys(
            value,
            {
                "schema",
                "goal_id",
                "acceptance_run_id",
                "source_revision",
                "programs",
                "roots",
                "release_executable",
            },
            location,
        )
        self.validate_manifest_header(
            value,
            schema=SUBJECT_GRAPH_SCHEMA,
            location=location,
            acceptance_run_id=acceptance_run_id,
            source_revision=source_revision,
        )
        programs = value.get("programs")
        roots = value.get("roots")
        root_names = {
            "admitted_files",
            "reachable_bodies",
            "refinement_certificates",
            "obligations",
            "proof_certificates",
            "modules",
            "codegen_matrix_cells",
            "objects",
            "translation_evidence",
            "call_edges",
            "executables",
        }
        if not self.exact_keys(roots, root_names, f"{location}.roots"):
            roots = {}
        else:
            for root_name, root_digest in roots.items():
                if not isinstance(root_digest, str) or not HEX_DIGEST.fullmatch(root_digest):
                    self.error(
                        f"{location}.roots.{root_name}",
                        "must be a lowercase 64-hex canonical root",
                    )
        if not isinstance(programs, list) or not programs:
            self.error(f"{location}.programs", "must be a non-empty list")
            return artifact_digests
        release_locator = value.get("release_executable")
        release_locator_valid = self.exact_keys(
            release_locator,
            {"program_id", "executable_id"},
            f"{location}.release_executable",
        )

        program_ids: set[str] = set()
        observed_admitted_files: set[str] = set()
        observed_languages: set[str] = set()
        observed_cross_language_directions: set[str] = set()
        observed_cross_language_value_categories: set[str] = set()
        observed_cross_language_matrix: set[tuple[str, str]] = set()
        observed_obligation_classes: set[str] = set()
        executable_records: dict[tuple[str, str], dict[str, Any]] = {}
        object_records_by_program: dict[str, dict[str, dict[str, Any]]] = {}
        root_rows: dict[str, list[dict[str, Any]]] = {name: [] for name in root_names}
        for program_index, program in enumerate(programs):
            program_location = f"{location}.programs[{program_index}]"
            program_keys = {
                "id",
                "entrypoints",
                "admitted_file_ids",
                "bodies",
                "refinement_certificates",
                "obligations",
                "proof_certificates",
                "modules",
                "objects",
                "translation_evidence",
                "executables",
                "call_edges",
                "contextual_refinement",
            }
            if not self.exact_keys(program, program_keys, program_location):
                continue
            program_id = program.get("id")
            if not isinstance(program_id, str) or not program_id:
                self.error(f"{program_location}.id", "must be a non-empty string")
                program_id = f"<invalid-{program_index}>"
            elif program_id in program_ids:
                self.error(f"{program_location}.id", f"duplicate program id {program_id!r}")
            else:
                program_ids.add(program_id)

            codegen = authority_contracts.get("codegen_surface", {})
            signed_cells = codegen.get("cells", {}) if isinstance(codegen, dict) else {}
            if not isinstance(signed_cells, dict) or not signed_cells:
                self.error(
                    f"{program_location}.objects",
                    "cannot realize an empty or invalid owner-signed codegen matrix",
                )
                signed_cells = {}
            for cell in sorted(signed_cells.values(), key=lambda row: row["id"]):
                root_rows["codegen_matrix_cells"].append(
                    {"program_id": program_id, **cell}
                )

            admitted_file_ids = program.get("admitted_file_ids")
            if (
                not isinstance(admitted_file_ids, list)
                or not admitted_file_ids
                or not all(isinstance(item, str) and item for item in admitted_file_ids)
                or len(admitted_file_ids) != len(set(admitted_file_ids))
            ):
                self.error(
                    f"{program_location}.admitted_file_ids",
                    "must be a non-empty duplicate-free string list",
                )
                admitted_file_ids = []
            for file_id in admitted_file_ids:
                if file_id not in admitted_corpus_ids:
                    self.error(
                        f"{program_location}.admitted_file_ids",
                        f"unknown or non-admitted corpus id {file_id!r}",
                    )
                observed_admitted_files.add(file_id)
                root_rows["admitted_files"].append(
                    {"program_id": program_id, "file_id": file_id}
                )

            def typed_rows(
                field: str,
                expected_keys: set[str],
                *,
                allow_empty: bool = False,
            ) -> list[dict[str, Any]]:
                rows = program.get(field)
                if not isinstance(rows, list) or (not rows and not allow_empty):
                    qualifier = "a list" if allow_empty else "a non-empty list"
                    self.error(f"{program_location}.{field}", f"must be {qualifier}")
                    return []
                result: list[dict[str, Any]] = []
                for row_index, row in enumerate(rows):
                    row_location = f"{program_location}.{field}[{row_index}]"
                    if self.exact_keys(row, expected_keys, row_location):
                        result.append(row)
                        root_name = "reachable_bodies" if field == "bodies" else field
                        root_rows[root_name].append({"program_id": program_id, **row})
                return result

            bodies = typed_rows(
                "bodies",
                {
                    "id",
                    "language",
                    "function_identity_sha256",
                    "source_language_semantics_id",
                    "source_language_semantics_sha256",
                    "source_semantics_sha256",
                    "trust_ir_semantics_id",
                    "trust_ir_semantics_sha256",
                    "trust_ir_sha256",
                    "ssa_epoch_sha256",
                    "effect_summary_sha256",
                },
            )
            body_ids: set[str] = set()
            semantics = authority_contracts.get("semantics", {})
            for row_index, body in enumerate(bodies):
                row_location = f"{program_location}.bodies[{row_index}]"
                body_id = body.get("id")
                if not isinstance(body_id, str) or not body_id or body_id in body_ids:
                    self.error(f"{row_location}.id", "must be a unique non-empty body id")
                else:
                    body_ids.add(body_id)
                language = body.get("language")
                if not isinstance(language, str) or language not in {"rust", "lean"}:
                    self.error(f"{row_location}.language", "must be 'rust' or 'lean'")
                else:
                    observed_languages.add(body["language"])
                    source_role = f"{body['language']}_language"
                    expected_source = semantics.get(source_role, {})
                    if body.get("source_language_semantics_id") != expected_source.get("id"):
                        self.error(
                            f"{row_location}.source_language_semantics_id",
                            "must name the owner-authorized source semantics",
                        )
                    if body.get("source_language_semantics_sha256") != expected_source.get(
                        "sha256"
                    ):
                        self.error(
                            f"{row_location}.source_language_semantics_sha256",
                            "must bind the owner-authorized source semantics",
                        )
                expected_ir = semantics.get("trust_ir", {})
                if body.get("trust_ir_semantics_id") != expected_ir.get("id"):
                    self.error(
                        f"{row_location}.trust_ir_semantics_id",
                        "must name the owner-authorized Trust-IR semantics",
                    )
                if body.get("trust_ir_semantics_sha256") != expected_ir.get("sha256"):
                    self.error(
                        f"{row_location}.trust_ir_semantics_sha256",
                        "must bind the owner-authorized Trust-IR semantics",
                    )
                for digest_field in (
                    "function_identity_sha256",
                    "source_language_semantics_sha256",
                    "source_semantics_sha256",
                    "trust_ir_semantics_sha256",
                    "trust_ir_sha256",
                    "ssa_epoch_sha256",
                    "effect_summary_sha256",
                ):
                    digest = body.get(digest_field)
                    if not isinstance(digest, str) or not HEX_DIGEST.fullmatch(digest):
                        self.error(f"{row_location}.{digest_field}", "must be 64-hex")

            entrypoints = program.get("entrypoints")
            if (
                not isinstance(entrypoints, list)
                or not entrypoints
                or not all(isinstance(item, str) and item in body_ids for item in entrypoints)
                or len(entrypoints) != len(set(entrypoints))
            ):
                self.error(
                    f"{program_location}.entrypoints",
                    "must be a non-empty duplicate-free subset of body ids",
                )

            call_edges = typed_rows(
                "call_edges",
                {
                    "id",
                    "caller_body_id",
                    "callee_body_id",
                    "direction",
                    "value_category",
                    "canonical_type_sha256",
                    "abi_id",
                    "abi_sha256",
                    "memory_model_id",
                    "memory_model_sha256",
                    "import_assumption_closure_sha256",
                    "visibility",
                },
            )
            call_edge_ids: set[str] = set()
            body_by_id = {
                body["id"]: body
                for body in bodies
                if isinstance(body.get("id"), str) and body.get("id")
            }
            abi = semantics.get("abi_memory_model", {})
            for row_index, edge in enumerate(call_edges):
                row_location = f"{program_location}.call_edges[{row_index}]"
                edge_id = edge.get("id")
                if not isinstance(edge_id, str) or not edge_id or edge_id in call_edge_ids:
                    self.error(f"{row_location}.id", "must be a unique non-empty edge ID")
                else:
                    call_edge_ids.add(edge_id)
                caller_id = edge.get("caller_body_id")
                callee_id = edge.get("callee_body_id")
                caller = body_by_id.get(caller_id) if isinstance(caller_id, str) else None
                callee = body_by_id.get(callee_id) if isinstance(callee_id, str) else None
                if caller is None:
                    self.error(f"{row_location}.caller_body_id", "must name a reachable body")
                if callee is None:
                    self.error(f"{row_location}.callee_body_id", "must name a reachable body")
                if caller is not None and callee is not None:
                    expected_direction = f"{caller.get('language')}_to_{callee.get('language')}"
                    if edge.get("direction") != expected_direction:
                        self.error(
                            f"{row_location}.direction",
                            f"must equal {expected_direction!r}",
                        )
                    if caller.get("language") != callee.get("language"):
                        observed_cross_language_directions.add(expected_direction)
                        if isinstance(edge.get("value_category"), str):
                            observed_cross_language_value_categories.add(
                                edge["value_category"]
                            )
                            observed_cross_language_matrix.add(
                                (expected_direction, edge["value_category"])
                            )
                value_category = edge.get("value_category")
                if not isinstance(value_category, str) or value_category not in {
                    "value",
                    "aggregate",
                    "reference",
                    "error",
                    "callback",
                    "result",
                }:
                    self.error(f"{row_location}.value_category", "is not a supported category")
                for digest_field in (
                    "canonical_type_sha256",
                    "abi_sha256",
                    "memory_model_sha256",
                    "import_assumption_closure_sha256",
                ):
                    digest = edge.get(digest_field)
                    if not isinstance(digest, str) or not HEX_DIGEST.fullmatch(digest):
                        self.error(f"{row_location}.{digest_field}", "must be 64-hex")
                for id_field in ("abi_id", "memory_model_id"):
                    if edge.get(id_field) != abi.get("id"):
                        self.error(
                            f"{row_location}.{id_field}",
                            "must name the owner-authorized ABI/memory model",
                        )
                for digest_field in ("abi_sha256", "memory_model_sha256"):
                    if edge.get(digest_field) != abi.get("sha256"):
                        self.error(
                            f"{row_location}.{digest_field}",
                            "must bind the owner-authorized ABI/memory model",
                        )
                if edge.get("visibility") != "call":
                    self.error(
                        f"{row_location}.visibility",
                        "cross-language computational edges must not cross the proof firewall",
                    )

            contextual_refinement = program.get("contextual_refinement")
            contextual_location = f"{program_location}.contextual_refinement"
            if self.exact_keys(
                contextual_refinement,
                {"assumption_closure_sha256", "evidence"},
                contextual_location,
            ):
                closure = contextual_refinement.get("assumption_closure_sha256")
                if not isinstance(closure, str) or not HEX_DIGEST.fullmatch(closure):
                    self.error(f"{contextual_location}.assumption_closure_sha256", "must be 64-hex")
                self.resolve_ref(contextual_refinement.get("evidence"), f"{contextual_location}.evidence")

            refinements = typed_rows(
                "refinement_certificates",
                {
                    "body_id",
                    "source_semantics_sha256",
                    "trust_ir_sha256",
                    "relation_id",
                    "relation_sha256",
                    "certificate_kind",
                    "finite_domain_sha256",
                    "exhaustiveness_evidence",
                    "all_elements_agreement_root_sha256",
                    "kernel_environment_id",
                    "kernel_environment_sha256",
                    "evidence",
                },
            )
            refinement_body_ids: list[str] = []
            body_by_id = {
                body["id"]: body
                for body in bodies
                if isinstance(body.get("id"), str) and body.get("id")
            }
            for row_index, refinement in enumerate(refinements):
                row_location = f"{program_location}.refinement_certificates[{row_index}]"
                body_id = refinement.get("body_id")
                if isinstance(body_id, str):
                    refinement_body_ids.append(body_id)
                    body = body_by_id.get(body_id)
                else:
                    body = None
                if body is None:
                    self.error(f"{row_location}.body_id", "must name a reachable body")
                else:
                    for field in ("source_semantics_sha256", "trust_ir_sha256"):
                        if refinement.get(field) != body.get(field):
                            self.error(
                                f"{row_location}.{field}",
                                "must equal the body's exact semantic digest",
                            )
                    relation_role = f"{body.get('language')}_to_trust_ir_refinement"
                    relation = semantics.get(relation_role, {})
                    if refinement.get("relation_id") != relation.get("id"):
                        self.error(
                            f"{row_location}.relation_id",
                            "must name the owner-authorized refinement relation",
                        )
                    if refinement.get("relation_sha256") != relation.get("sha256"):
                        self.error(
                            f"{row_location}.relation_sha256",
                            "must bind the owner-authorized refinement relation",
                        )
                proof_kernels = authority_contracts.get("proof_authority", {}).get(
                    "kernels",
                    {},
                )
                kernel_id = refinement.get("kernel_environment_id")
                kernel = proof_kernels.get(kernel_id, {}) if isinstance(kernel_id, str) else {}
                if not kernel:
                    self.error(
                        f"{row_location}.kernel_environment_id",
                        "must name an owner-authorized kernel environment",
                    )
                kernel_digest = refinement.get("kernel_environment_sha256")
                if not isinstance(kernel_digest, str) or not HEX_DIGEST.fullmatch(kernel_digest):
                    self.error(
                        f"{row_location}.kernel_environment_sha256",
                        "must be 64-hex",
                    )
                elif kernel_digest != kernel.get("environment_sha256"):
                    self.error(
                        f"{row_location}.kernel_environment_sha256",
                        "must equal the owner-authorized kernel environment",
                    )
                relation_digest = refinement.get("relation_sha256")
                if not isinstance(relation_digest, str) or not HEX_DIGEST.fullmatch(
                    relation_digest
                ):
                    self.error(f"{row_location}.relation_sha256", "must be 64-hex")
                certificate_kind = refinement.get("certificate_kind")
                finite_fields = (
                    refinement.get("finite_domain_sha256"),
                    refinement.get("exhaustiveness_evidence"),
                    refinement.get("all_elements_agreement_root_sha256"),
                )
                if certificate_kind == "universal":
                    if finite_fields != (None, None, None):
                        self.error(
                            row_location,
                            "universal certificates must not carry finite-domain substitutes",
                        )
                elif certificate_kind == "finite-exhaustive":
                    for field in (
                        "finite_domain_sha256",
                        "all_elements_agreement_root_sha256",
                    ):
                        digest = refinement.get(field)
                        if not isinstance(digest, str) or not HEX_DIGEST.fullmatch(digest):
                            self.error(f"{row_location}.{field}", "must be 64-hex")
                    self.resolve_ref(
                        refinement.get("exhaustiveness_evidence"),
                        f"{row_location}.exhaustiveness_evidence",
                    )
                else:
                    self.error(
                        f"{row_location}.certificate_kind",
                        "must be 'universal' or 'finite-exhaustive'",
                    )
                self.resolve_ref(refinement.get("evidence"), f"{row_location}.evidence")
            if sorted(refinement_body_ids) != sorted(body_ids):
                self.error(
                    f"{program_location}.refinement_certificates",
                    "must contain exactly one universal refinement certificate per body",
                )

            obligations = typed_rows(
                "obligations",
                {
                    "id",
                    "body_id",
                    "function_identity_sha256",
                    "formula_sha256",
                    "canonical_proposition_sha256",
                    "formula_encoder_id",
                    "formula_encoder_sha256",
                    "proposition_encoder_id",
                    "proposition_encoder_sha256",
                    "formula_to_proposition_evidence",
                    "policy_rule_id",
                    "ssa_epoch_sha256",
                    "effect_summary_sha256",
                    "module_id",
                },
            )
            obligation_ids: set[str] = set()
            obligation_by_id: dict[str, dict[str, Any]] = {}
            for row_index, obligation in enumerate(obligations):
                row_location = f"{program_location}.obligations[{row_index}]"
                obligation_id = obligation.get("id")
                if (
                    not isinstance(obligation_id, str)
                    or not obligation_id
                    or obligation_id in obligation_ids
                ):
                    self.error(f"{row_location}.id", "must be a unique non-empty obligation id")
                else:
                    obligation_ids.add(obligation_id)
                    obligation_by_id[obligation_id] = obligation
                obligation_body_id = obligation.get("body_id")
                if not isinstance(obligation_body_id, str) or obligation_body_id not in body_ids:
                    self.error(f"{row_location}.body_id", "must name a reachable body")
                body = body_by_id.get(obligation_body_id, {}) if isinstance(
                    obligation_body_id,
                    str,
                ) else {}
                for field in (
                    "function_identity_sha256",
                    "ssa_epoch_sha256",
                    "effect_summary_sha256",
                ):
                    if obligation.get(field) != body.get(field):
                        self.error(
                            f"{row_location}.{field}",
                            "must equal the reachable body's exact identity/state/effect digest",
                        )
                for field in (
                    "function_identity_sha256",
                    "formula_sha256",
                    "canonical_proposition_sha256",
                    "formula_encoder_sha256",
                    "proposition_encoder_sha256",
                    "ssa_epoch_sha256",
                    "effect_summary_sha256",
                ):
                    digest = obligation.get(field)
                    if not isinstance(digest, str) or not HEX_DIGEST.fullmatch(digest):
                        self.error(f"{row_location}.{field}", "must be 64-hex")
                formula_encoder = authority_contracts.get("obligations", {}).get(
                    "formula_encoder",
                    {},
                )
                if obligation.get("formula_encoder_id") != formula_encoder.get("id"):
                    self.error(
                        f"{row_location}.formula_encoder_id",
                        "must name the owner-authorized formula encoder",
                    )
                if obligation.get("formula_encoder_sha256") != formula_encoder.get("sha256"):
                    self.error(
                        f"{row_location}.formula_encoder_sha256",
                        "must bind the owner-authorized formula encoder",
                    )
                proposition_encoder = authority_contracts.get("proof_authority", {}).get(
                    "canonical_proposition_encoder",
                    {},
                )
                if obligation.get("proposition_encoder_id") != proposition_encoder.get("id"):
                    self.error(
                        f"{row_location}.proposition_encoder_id",
                        "must name the owner-authorized canonical proposition encoder",
                    )
                if obligation.get("proposition_encoder_sha256") != proposition_encoder.get(
                    "sha256"
                ):
                    self.error(
                        f"{row_location}.proposition_encoder_sha256",
                        "must bind the owner-authorized canonical proposition encoder",
                    )
                self.resolve_ref(
                    obligation.get("formula_to_proposition_evidence"),
                    f"{row_location}.formula_to_proposition_evidence",
                )
                if not isinstance(obligation.get("policy_rule_id"), str) or not obligation.get(
                    "policy_rule_id"
                ):
                    self.error(f"{row_location}.policy_rule_id", "must be non-empty")
                else:
                    rule = authority_contracts.get("obligations", {}).get(
                        "rules",
                        {},
                    ).get(obligation.get("policy_rule_id"))
                    if not isinstance(rule, dict):
                        self.error(
                            f"{row_location}.policy_rule_id",
                            "must name an owner-authorized obligation rule",
                        )
                    elif isinstance(rule.get("class"), str):
                        observed_obligation_classes.add(rule["class"])

            proof_certificates = typed_rows(
                "proof_certificates",
                {
                    "id",
                    "obligation_id",
                    "body_id",
                    "function_identity_sha256",
                    "proposition_sha256",
                    "ssa_epoch_sha256",
                    "effect_summary_sha256",
                    "module_id",
                    "kernel_environment_id",
                    "kernel_environment_sha256",
                    "proof_grade",
                    "axiom_allowlist_root_sha256",
                    "evidence",
                },
            )
            proof_ids: set[str] = set()
            certified_obligation_ids: list[str] = []
            for row_index, certificate in enumerate(proof_certificates):
                row_location = f"{program_location}.proof_certificates[{row_index}]"
                certificate_id = certificate.get("id")
                if (
                    not isinstance(certificate_id, str)
                    or not certificate_id
                    or certificate_id in proof_ids
                ):
                    self.error(f"{row_location}.id", "must be a unique non-empty certificate id")
                else:
                    proof_ids.add(certificate_id)
                obligation_id = certificate.get("obligation_id")
                if isinstance(obligation_id, str):
                    certified_obligation_ids.append(obligation_id)
                    obligation = obligation_by_id.get(obligation_id)
                else:
                    obligation = None
                if obligation is None:
                    self.error(f"{row_location}.obligation_id", "must name an obligation")
                else:
                    for field in (
                        "body_id",
                        "function_identity_sha256",
                        "ssa_epoch_sha256",
                        "effect_summary_sha256",
                        "module_id",
                    ):
                        if certificate.get(field) != obligation.get(field):
                            self.error(
                                f"{row_location}.{field}",
                                "must equal the exact obligation identity/state/module binding",
                            )
                if obligation is not None and certificate.get(
                    "proposition_sha256"
                ) != obligation.get("canonical_proposition_sha256"):
                    self.error(
                        f"{row_location}.proposition_sha256",
                        "must equal the exact canonical Lean proposition digest",
                    )
                kernel_id = certificate.get("kernel_environment_id")
                kernel = (
                    authority_contracts.get("proof_authority", {})
                    .get("kernels", {})
                    .get(kernel_id, {})
                    if isinstance(kernel_id, str)
                    else {}
                )
                if not kernel:
                    self.error(
                        f"{row_location}.kernel_environment_id",
                        "must name an owner-authorized kernel environment",
                    )
                if certificate.get("kernel_environment_sha256") != kernel.get(
                    "environment_sha256"
                ):
                    self.error(
                        f"{row_location}.kernel_environment_sha256",
                        "must equal the owner-authorized kernel environment",
                    )
                proof_grade = certificate.get("proof_grade")
                grades = kernel.get("proof_grades")
                # A list, not a str: `in` on a str would test for a substring.
                if (
                    not isinstance(proof_grade, str)
                    or not isinstance(grades, list)
                    or proof_grade not in grades
                ):
                    self.error(
                        f"{row_location}.proof_grade",
                        "must be an owner-authorized proof grade",
                    )
                if certificate.get("axiom_allowlist_root_sha256") != kernel.get(
                    "axiom_allowlist_root_sha256"
                ):
                    self.error(
                        f"{row_location}.axiom_allowlist_root_sha256",
                        "must bind the owner-authorized axiom allowlist",
                    )
                for digest_field in (
                    "function_identity_sha256",
                    "proposition_sha256",
                    "ssa_epoch_sha256",
                    "effect_summary_sha256",
                    "kernel_environment_sha256",
                    "axiom_allowlist_root_sha256",
                ):
                    digest = certificate.get(digest_field)
                    if not isinstance(digest, str) or not HEX_DIGEST.fullmatch(digest):
                        self.error(f"{row_location}.{digest_field}", "must be 64-hex")
                self.resolve_ref(certificate.get("evidence"), f"{row_location}.evidence")
            if sorted(certified_obligation_ids) != sorted(obligation_ids):
                self.error(
                    f"{program_location}.proof_certificates",
                    "must contain exactly one proof certificate per required obligation",
                )

            modules = typed_rows(
                "modules",
                {
                    "id",
                    "artifact",
                    "body_ids",
                    "call_edge_ids",
                    "obligation_ids",
                    "refinement_certificate_body_ids",
                    "proof_certificate_ids",
                    "assumption_closure_sha256",
                    "contextual_refinement_evidence",
                },
            )
            module_ids: set[str] = set()
            module_artifacts: dict[str, str] = {}
            module_body_ids: list[str] = []
            module_call_edge_ids: list[str] = []
            module_obligation_ids: list[str] = []
            module_refinement_ids: list[str] = []
            module_proof_ids: list[str] = []
            for row_index, module in enumerate(modules):
                row_location = f"{program_location}.modules[{row_index}]"
                module_id = module.get("id")
                if not isinstance(module_id, str) or not module_id or module_id in module_ids:
                    self.error(f"{row_location}.id", "must be a unique non-empty module id")
                else:
                    module_ids.add(module_id)
                module_path = self.resolve_ref(module.get("artifact"), f"{row_location}.artifact")
                artifact = module.get("artifact")
                if module_path is not None and isinstance(artifact, dict):
                    digest = artifact.get("sha256")
                    if isinstance(digest, str):
                        artifact_digests["modules"].add(digest)
                        if isinstance(module_id, str):
                            module_artifacts[module_id] = digest
                closure = module.get("assumption_closure_sha256")
                if not isinstance(closure, str) or not HEX_DIGEST.fullmatch(closure):
                    self.error(f"{row_location}.assumption_closure_sha256", "must be 64-hex")
                elif isinstance(contextual_refinement, dict) and closure != contextual_refinement.get(
                    "assumption_closure_sha256"
                ):
                    self.error(
                        f"{row_location}.assumption_closure_sha256",
                        "must equal the whole-program contextual refinement closure",
                    )
                self.resolve_ref(
                    module.get("contextual_refinement_evidence"),
                    f"{row_location}.contextual_refinement_evidence",
                )
                for field, sink in (
                    ("body_ids", module_body_ids),
                    ("call_edge_ids", module_call_edge_ids),
                    ("obligation_ids", module_obligation_ids),
                    ("refinement_certificate_body_ids", module_refinement_ids),
                    ("proof_certificate_ids", module_proof_ids),
                ):
                    ids = module.get(field)
                    if not isinstance(ids, list) or not all(
                        isinstance(item, str) and item for item in ids
                    ):
                        self.error(f"{row_location}.{field}", "must be a string list")
                    else:
                        sink.extend(ids)
            expected_module_sets = (
                ("body_ids", module_body_ids, body_ids),
                ("call_edge_ids", module_call_edge_ids, call_edge_ids),
                ("obligation_ids", module_obligation_ids, obligation_ids),
                (
                    "refinement_certificate_body_ids",
                    module_refinement_ids,
                    body_ids,
                ),
                ("proof_certificate_ids", module_proof_ids, proof_ids),
            )
            for field, observed, expected_ids in expected_module_sets:
                if sorted(observed) != sorted(expected_ids):
                    self.error(
                        f"{program_location}.modules.{field}",
                        "module inventory must be an exact duplicate-free partition",
                    )

            for row_index, obligation in enumerate(obligations):
                module_id = obligation.get("module_id")
                if not isinstance(module_id, str) or module_id not in module_ids:
                    self.error(
                        f"{program_location}.obligations[{row_index}].module_id",
                        "must name the owning admitted module",
                    )
            for row_index, certificate in enumerate(proof_certificates):
                module_id = certificate.get("module_id")
                if not isinstance(module_id, str) or module_id not in module_ids:
                    self.error(
                        f"{program_location}.proof_certificates[{row_index}].module_id",
                        "must name the owning admitted module",
                    )

            objects = typed_rows(
                "objects",
                {
                    "id",
                    "module_id",
                    "codegen_cell_id",
                    *CODEGEN_CELL_FIELDS,
                    "artifact",
                },
            )
            object_ids: set[str] = set()
            object_pairs: list[tuple[str, str]] = []
            object_records: dict[str, dict[str, Any]] = {}
            for row_index, obj in enumerate(objects):
                row_location = f"{program_location}.objects[{row_index}]"
                object_id = obj.get("id")
                object_id_valid = True
                if not isinstance(object_id, str) or not object_id or object_id in object_ids:
                    self.error(f"{row_location}.id", "must be a unique non-empty object id")
                    object_id_valid = False
                else:
                    object_ids.add(object_id)
                module_id = obj.get("module_id")
                if not isinstance(module_id, str) or module_id not in module_ids:
                    self.error(f"{row_location}.module_id", "must name an admitted module")
                cell = self.validate_codegen_cell_binding(obj, row_location, signed_cells)
                cell_id = obj.get("codegen_cell_id")
                if isinstance(module_id, str) and module_id in module_ids and cell is not None:
                    object_pairs.append((module_id, cell["id"]))
                artifact_path = self.resolve_ref(obj.get("artifact"), f"{row_location}.artifact")
                artifact = obj.get("artifact")
                artifact_digest = (
                    artifact.get("sha256") if isinstance(artifact, dict) else None
                )
                if artifact_path is not None and isinstance(artifact_digest, str):
                    artifact_digests["objects"].add(artifact_digest)
                if object_id_valid and isinstance(object_id, str):
                    object_records[object_id] = {
                        "module_id": module_id,
                        "codegen_cell_id": cell_id,
                        "artifact_sha256": artifact_digest,
                        "module_sha256": (
                            module_artifacts.get(module_id)
                            if isinstance(module_id, str)
                            else None
                        ),
                        "configuration": {
                            field: obj.get(field) for field in CODEGEN_CELL_FIELDS
                        },
                    }
            expected_object_pairs = {
                (module_id, cell_id)
                for module_id in module_ids
                for cell_id in signed_cells
            }
            if (
                len(object_pairs) != len(set(object_pairs))
                or set(object_pairs) != expected_object_pairs
            ):
                self.error(
                    f"{program_location}.objects",
                    "must contain exactly one object for every admitted module/codegen-cell pair",
                )
            object_records_by_program[program_id] = object_records

            translation_evidence = typed_rows(
                "translation_evidence",
                {
                    "id",
                    "object_id",
                    "module_id",
                    "codegen_cell_id",
                    *CODEGEN_CELL_FIELDS,
                    "translation_relation_id",
                    "translation_relation_sha256",
                    "module_sha256",
                    "object_sha256",
                    "evidence",
                },
            )
            evidence_ids: set[str] = set()
            evidence_object_ids: list[str] = []
            relation = codegen.get("translation_relation", {}) if isinstance(codegen, dict) else {}
            for row_index, evidence in enumerate(translation_evidence):
                row_location = f"{program_location}.translation_evidence[{row_index}]"
                evidence_id = evidence.get("id")
                if (
                    not isinstance(evidence_id, str)
                    or not evidence_id
                    or evidence_id in evidence_ids
                ):
                    self.error(f"{row_location}.id", "must be a unique non-empty evidence id")
                else:
                    evidence_ids.add(evidence_id)
                object_id = evidence.get("object_id")
                if isinstance(object_id, str) and object_id:
                    evidence_object_ids.append(object_id)
                else:
                    self.error(f"{row_location}.object_id", "must be a non-empty string")
                cell = self.validate_codegen_cell_binding(evidence, row_location, signed_cells)
                joined_object = object_records.get(object_id) if isinstance(object_id, str) else None
                if joined_object is None:
                    self.error(f"{row_location}.object_id", "must name an emitted object")
                else:
                    if evidence.get("module_id") != joined_object.get("module_id"):
                        self.error(
                            f"{row_location}.module_id",
                            "must equal the joined object's module",
                        )
                    if evidence.get("codegen_cell_id") != joined_object.get("codegen_cell_id"):
                        self.error(
                            f"{row_location}.codegen_cell_id",
                            "must equal the joined object's codegen cell",
                        )
                    for field in CODEGEN_CELL_FIELDS:
                        if evidence.get(field) != joined_object["configuration"].get(field):
                            self.error(
                                f"{row_location}.{field}",
                                "must equal the joined object's codegen configuration",
                            )
                    if evidence.get("module_sha256") != joined_object.get("module_sha256"):
                        self.error(
                            f"{row_location}.module_sha256",
                            "must bind the exact joined Trust-IR module artifact",
                        )
                    if evidence.get("object_sha256") != joined_object.get("artifact_sha256"):
                        self.error(
                            f"{row_location}.object_sha256",
                            "must bind the exact joined object artifact",
                        )
                if evidence.get("translation_relation_id") != relation.get("id"):
                    self.error(
                        f"{row_location}.translation_relation_id",
                        "must name the owner-authorized machine translation relation",
                    )
                if evidence.get("translation_relation_sha256") != relation.get("sha256"):
                    self.error(
                        f"{row_location}.translation_relation_sha256",
                        "must bind the owner-authorized machine translation relation",
                    )
                evidence_path = self.resolve_ref(
                    evidence.get("evidence"), f"{row_location}.evidence"
                )
                evidence_ref = evidence.get("evidence")
                if evidence_path is not None and isinstance(evidence_ref, dict):
                    digest = evidence_ref.get("sha256")
                    if isinstance(digest, str):
                        artifact_digests["translation_evidence"].add(digest)
            if (
                len(evidence_object_ids) != len(set(evidence_object_ids))
                or set(evidence_object_ids) != object_ids
            ):
                self.error(
                    f"{program_location}.translation_evidence",
                    "must contain exactly one translation-evidence row per emitted object",
                )

            executables = typed_rows(
                "executables",
                {
                    "id",
                    "codegen_cell_id",
                    *CODEGEN_CELL_FIELDS,
                    "object_ids",
                    "artifact",
                    "system_library_closure_sha256",
                    "composition_evidence",
                    "binary_semantics_evidence",
                },
            )
            executable_ids: set[str] = set()
            executable_cell_ids: list[str] = []
            partitioned_object_ids: list[str] = []
            for row_index, executable in enumerate(executables):
                row_location = f"{program_location}.executables[{row_index}]"
                executable_id = executable.get("id")
                executable_id_valid = True
                if (
                    not isinstance(executable_id, str)
                    or not executable_id
                    or executable_id in executable_ids
                ):
                    self.error(f"{row_location}.id", "must be a unique non-empty executable id")
                    executable_id_valid = False
                else:
                    executable_ids.add(executable_id)
                cell = self.validate_codegen_cell_binding(executable, row_location, signed_cells)
                cell_id = executable.get("codegen_cell_id")
                if isinstance(cell_id, str) and cell_id:
                    executable_cell_ids.append(cell_id)
                executable_path = self.resolve_ref(
                    executable.get("artifact"), f"{row_location}.artifact"
                )
                executable_artifact = executable.get("artifact")
                executable_digest = (
                    executable_artifact.get("sha256")
                    if isinstance(executable_artifact, dict)
                    else None
                )
                if executable_path is not None and isinstance(executable_digest, str):
                    artifact_digests["executables"].add(executable_digest)
                executable_object_ids = executable.get("object_ids")
                valid_object_list = (
                    isinstance(executable_object_ids, list)
                    and all(
                        isinstance(object_id, str) and object_id
                        for object_id in executable_object_ids
                    )
                    and len(executable_object_ids) == len(set(executable_object_ids))
                )
                if not valid_object_list:
                    self.error(
                        f"{row_location}.object_ids",
                        "must be a duplicate-free string list",
                    )
                    executable_object_ids = []
                expected_cell_objects = {
                    object_id
                    for object_id, record in object_records.items()
                    if record.get("codegen_cell_id") == cell_id
                }
                if set(executable_object_ids) != expected_cell_objects:
                    self.error(
                        f"{row_location}.object_ids",
                        "must contain exactly the objects emitted for the same codegen cell",
                    )
                partitioned_object_ids.extend(executable_object_ids)
                digest = executable.get("system_library_closure_sha256")
                if not isinstance(digest, str) or not HEX_DIGEST.fullmatch(digest):
                    self.error(f"{row_location}.system_library_closure_sha256", "must be 64-hex")
                for field in ("composition_evidence", "binary_semantics_evidence"):
                    self.resolve_ref(executable.get(field), f"{row_location}.{field}")
                if executable_id_valid and isinstance(executable_id, str):
                    executable_records[(program_id, executable_id)] = {
                        "artifact_sha256": executable_digest,
                        "codegen_cell_id": cell_id,
                        "object_ids": executable_object_ids,
                    }
            if (
                len(executable_cell_ids) != len(set(executable_cell_ids))
                or set(executable_cell_ids) != set(signed_cells)
            ):
                self.error(
                    f"{program_location}.executables",
                    "must contain exactly one linked executable per signed codegen cell",
                )
            if (
                len(partitioned_object_ids) != len(set(partitioned_object_ids))
                or set(partitioned_object_ids) != object_ids
            ):
                self.error(
                    f"{program_location}.executables.object_ids",
                    "executable object lists must exactly partition the emitted objects by cell",
                )

        if observed_languages != {"rust", "lean"}:
            self.error(
                f"{location}.programs.languages",
                "subject graph must contain reachable Rust and Lean bodies",
            )
        if observed_cross_language_directions != {"rust_to_lean", "lean_to_rust"}:
            self.error(
                f"{location}.programs.call_edges",
                "subject graph must contain typed Rust-to-Lean and Lean-to-Rust edges",
            )
        required_categories = {
            "value",
            "aggregate",
            "reference",
            "error",
            "callback",
            "result",
        }
        required_cross_language_matrix = {
            (direction, category)
            for direction in ("rust_to_lean", "lean_to_rust")
            for category in required_categories
        }
        if observed_cross_language_matrix != required_cross_language_matrix:
            self.error(
                f"{location}.programs.call_edges.value_category",
                "mixed subject must witness every direction/value-category pair in the complete cross-language matrix",
            )
        if observed_obligation_classes != OBLIGATION_CLASSES:
            self.error(
                f"{location}.programs.obligations.policy_classes",
                "subject graph must witness every owner-required obligation class",
            )
        if observed_admitted_files != admitted_corpus_ids:
            self.error(
                f"{location}.programs.admitted_file_ids",
                "program index must cover exactly the admitted corpus IDs",
            )
        release_record: Optional[dict[str, Any]] = None
        if release_locator_valid and isinstance(release_locator, dict):
            release_program_id = release_locator.get("program_id")
            release_executable_id = release_locator.get("executable_id")
            if not isinstance(release_program_id, str) or not release_program_id:
                self.error(
                    f"{location}.release_executable.program_id",
                    "must be a non-empty string",
                )
            if not isinstance(release_executable_id, str) or not release_executable_id:
                self.error(
                    f"{location}.release_executable.executable_id",
                    "must be a non-empty string",
                )
            if isinstance(release_program_id, str) and isinstance(
                release_executable_id, str
            ):
                release_record = executable_records.get(
                    (release_program_id, release_executable_id)
                )
            if release_record is None:
                self.error(
                    f"{location}.release_executable",
                    "must resolve to exactly one typed executable row",
                )
            else:
                if release_record.get("artifact_sha256") != release_artifact_digest:
                    self.error(
                        f"{location}.release_executable",
                        "must select the exact receipt release artifact",
                    )
                release_objects = object_records_by_program.get(
                    release_program_id, {}
                )
                linked_inputs = [
                    release_objects[object_id].get("module_sha256")
                    for object_id in release_record.get("object_ids", [])
                    if object_id in release_objects
                ]
                if linked_inputs.count(linked_module_digest) != 1:
                    self.error(
                        f"{location}.release_executable",
                        "must consume exactly one object produced from the designated linked module",
                    )
        for root_name in sorted(root_names):
            rows = sorted(
                root_rows[root_name],
                key=lambda row: json.dumps(row, sort_keys=True, separators=(",", ":")),
            )
            actual_root = _canonical_json_sha256(rows)
            if roots.get(root_name) != actual_root:
                self.error(
                    f"{location}.roots.{root_name}",
                    f"canonical root mismatch: recorded {roots.get(root_name)!r}, "
                    f"actual {actual_root!r}",
                )
        if (
            not isinstance(linked_module_digest, str)
            or linked_module_digest not in artifact_digests["modules"]
        ):
            self.error("receipt.linked_module", "must name a typed module artifact")
        if (
            not isinstance(release_artifact_digest, str)
            or release_artifact_digest not in artifact_digests["executables"]
        ):
            self.error("receipt.release_artifact", "must name a typed linked executable")
        return artifact_digests

    def validate_policy(
        self,
        value: Optional[dict[str, Any]],
        source_revision: Any,
        acceptance_run_id: Any,
        authorized_inputs: dict[str, Any],
    ) -> None:
        location = "authority_policy"
        if value is None:
            return
        self.exact_keys(
            value,
            {
                "schema",
                "goal_id",
                "repository_id",
                "completion_schema",
                "authorized_source_revision",
                "authorized_acceptance_run_id",
                "owner_key_fingerprint",
                "authorized_inputs",
                "contracts",
                "authorized_checkers",
            },
            location,
        )
        expected = {
            "schema": POLICY_SCHEMA,
            "goal_id": GOAL_ID,
            "repository_id": REPOSITORY_ID,
            "completion_schema": SCHEMA,
            "authorized_source_revision": source_revision,
            "authorized_acceptance_run_id": acceptance_run_id,
        }
        for key, wanted in expected.items():
            if value.get(key) != wanted:
                self.error(f"{location}.{key}", f"must equal {wanted!r}")
        fingerprint = value.get("owner_key_fingerprint")
        if not isinstance(fingerprint, str) or len(fingerprint) < 16:
            self.error(
                f"{location}.owner_key_fingerprint",
                "must name the externally trusted owner signing key",
            )
        inputs = value.get("authorized_inputs")
        if self.exact_keys(inputs, set(authorized_inputs), f"{location}.authorized_inputs"):
            for key, wanted in authorized_inputs.items():
                if inputs.get(key) != wanted:
                    self.error(
                        f"{location}.authorized_inputs.{key}",
                        "must equal the exact owner-authorized receipt input digest",
                    )
        contracts = value.get("contracts")
        if isinstance(contracts, dict):
            self.exact_keys(contracts, set(AUTHORITY_CONTRACTS), f"{location}.contracts")
        authorized = value.get("authorized_checkers")
        if not isinstance(authorized, dict) or set(authorized) != set(GATES):
            self.error(
                f"{location}.authorized_checkers",
                "must contain exactly G1-G8",
            )
            return
        for gate in GATES:
            row_location = f"{location}.authorized_checkers.{gate}"
            row = authorized.get(gate)
            if not self.exact_keys(row, {"id", "path", "sha256"}, row_location):
                continue
            expected_row = {
                "id": CHECKER_IDS[gate],
                "path": CHECKER_PATHS[gate],
            }
            for key, wanted in expected_row.items():
                if row.get(key) != wanted:
                    self.error(f"{row_location}.{key}", f"must equal {wanted!r}")
            if not isinstance(row.get("sha256"), str) or not HEX_DIGEST.fullmatch(
                row["sha256"]
            ):
                self.error(f"{row_location}.sha256", "must be a lowercase 64-hex digest")

    def verify_policy_authorization(
        self,
        envelope_path: Optional[Path],
        policy_path: Optional[Path],
        policy_digest: Any,
        policy_value: Optional[dict[str, Any]],
    ) -> None:
        """Verify candidate policy against an Ed25519 key supplied outside --root."""
        location = "policy_authorization"
        if self.trusted_owner_key is None:
            self.error(
                location,
                "--trusted-owner-key is required and must be rooted outside --root",
            )
            return
        # Existence first: a missing key cannot be stat'ed, which the identity
        # check below would otherwise report as "inside the repository".
        mode, problem = _file_mode(self.trusted_owner_key)
        if problem is not None:
            self.error(location, f"trusted owner key cannot be stat'ed: {problem}")
            return
        if mode is None or not stat.S_ISREG(mode):
            self.error(location, f"trusted owner key does not exist: {self.trusted_owner_key}")
            return
        inside = _inside_root_by_identity(self.trusted_owner_key, self.root)
        if inside is not None:
            self.error(
                location,
                f"trusted owner key must be outside the candidate repository: {inside}",
            )
            return
        try:
            key_fields = self.trusted_owner_key.read_text(encoding="utf-8").strip().split()
        except (OSError, UnicodeError) as exc:
            self.error(location, f"cannot read trusted owner key: {exc}")
            return
        if len(key_fields) < 2 or key_fields[0] != "ssh-ed25519":
            self.error(location, "trusted owner key must contain one ssh-ed25519 public key")
            return
        if not SSH_KEYGEN.is_file():
            self.error(location, f"required verifier is unavailable: {SSH_KEYGEN}")
            return
        fingerprint_process = _ssh_keygen(
            "-lf", str(self.trusted_owner_key), "-E", "sha256"
        )
        fingerprint_fields = fingerprint_process.stdout.decode(
            "utf-8", errors="replace"
        ).split()
        if fingerprint_process.returncode != 0 or len(fingerprint_fields) < 2:
            self.error(location, "cannot derive trusted owner key fingerprint")
            return
        fingerprint = fingerprint_fields[1]
        self.trusted_owner_fingerprint = fingerprint
        if policy_value is None or policy_value.get("owner_key_fingerprint") != fingerprint:
            self.error(
                f"{location}.signer_fingerprint",
                "policy fingerprint does not equal the externally trusted owner key",
            )
        if envelope_path is None or not _is_regular_file(envelope_path) or policy_path is None:
            return
        envelope = self.load_json(envelope_path, location)
        if envelope is None:
            return
        self.exact_keys(
            envelope,
            {
                "schema",
                "algorithm",
                "namespace",
                "signer_fingerprint",
                "policy_sha256",
                "signature",
            },
            location,
        )
        expected = {
            "schema": POLICY_AUTH_SCHEMA,
            "algorithm": "ssh-ed25519",
            "namespace": POLICY_SIGNATURE_NAMESPACE,
            "signer_fingerprint": fingerprint,
            "policy_sha256": policy_digest,
        }
        for key, wanted in expected.items():
            if envelope.get(key) != wanted:
                self.error(f"{location}.{key}", f"must equal {wanted!r}")
        signature_path = self.resolve_ref(envelope.get("signature"), f"{location}.signature")
        if signature_path is None or not _is_regular_file(signature_path):
            return
        # The signature is checked over bytes read once, which must be the
        # bytes whose digest the receipt binds.  A policy that is not a
        # readable regular file is refused here; resolve_ref said why.
        try:
            policy_bytes = _read_file(policy_path)
        except (OSError, ValueError) as exc:
            self.error(location, f"cannot read the authority policy: {exc}")
            return
        if hashlib.sha256(policy_bytes).hexdigest() != policy_digest:
            self.error(location, "the authority policy read for verification is not the bound one")
            return
        with tempfile.TemporaryDirectory(prefix="trust-owner-policy-") as tmp:
            allowed_signers = Path(tmp) / "allowed_signers"
            allowed_signers.write_text(
                f"trust-owner {key_fields[0]} {key_fields[1]}\n",
                encoding="utf-8",
            )
            verify = _ssh_keygen(
                "-Y",
                "verify",
                "-f",
                str(allowed_signers),
                "-I",
                "trust-owner",
                "-n",
                POLICY_SIGNATURE_NAMESPACE,
                "-s",
                str(signature_path),
                stdin=policy_bytes,
            )
        if verify.returncode != 0:
            detail = verify.stderr.decode("utf-8", errors="replace").strip()
            self.error(location, f"owner policy signature verification failed: {detail}")

    def post_run_integrity_check(self) -> None:
        """Close ordinary concurrent-mutation races around checker execution."""
        for path, expected in sorted(self.bound_files.items(), key=lambda item: str(item[0])):
            if not _is_regular_file(path):
                self.error("post_run_integrity", f"bound file disappeared: {path}")
                continue
            try:
                actual = _sha256(path)
            except OSError as exc:
                self.error("post_run_integrity", f"bound file cannot be re-read: {path}: {exc}")
                continue
            if actual != expected:
                self.error(
                    "post_run_integrity",
                    f"bound file changed during checker execution: {path}",
                )
        # A tree refused before the run stays refused; proving it again would
        # repeat the most expensive inspection without changing the verdict.
        if not self.worktree_clean_before_run:
            return
        for refusal in worktree_refusals(self.root, self.head_before_run):
            self.error(
                "post_run_integrity",
                f"worktree became dirty during checker execution: {refusal}",
            )

    def validate(self) -> dict[str, Any]:
        receipt, receipt_bytes = self.load_json_bytes(self.receipt_path, "receipt")
        gate_results = {gate: False for gate in GATES}
        if receipt is None or receipt_bytes is None:
            return self.verdict(gate_results)

        receipt_keys = {
            "schema",
            "goal_id",
            "repository_id",
            "acceptance_run_id",
            "source_revision",
            "toolchain_manifest",
            "corpus_manifest",
            "subject_graph",
            "linked_module",
            "release_artifact",
            "authority_policy",
            "policy_authorization",
            "gates",
        }
        self.exact_keys(receipt, receipt_keys, "receipt")
        if receipt.get("schema") != SCHEMA:
            self.error("receipt.schema", f"must equal {SCHEMA!r}")
        if receipt.get("goal_id") != GOAL_ID:
            self.error("receipt.goal_id", f"must equal {GOAL_ID!r}")
        if receipt.get("repository_id") != REPOSITORY_ID:
            self.error("receipt.repository_id", f"must equal {REPOSITORY_ID!r}")

        acceptance_run_id = receipt.get("acceptance_run_id")
        if not isinstance(acceptance_run_id, str) or not HEX_DIGEST.fullmatch(
            acceptance_run_id
        ):
            self.error(
                "receipt.acceptance_run_id",
                "must be a lowercase 64-hex run/subject identity",
            )

        source_revision = receipt.get("source_revision")
        if not isinstance(source_revision, str) or not GIT_REVISION.fullmatch(source_revision):
            self.error("receipt.source_revision", "must be a lowercase 40-64 hex revision")

        head_process = _git_run(self.root, "rev-parse", "HEAD", timeout=GIT_QUICK_TIMEOUT)
        head_rc = head_process.returncode
        head = head_process.stdout.decode("utf-8", errors="replace").strip()
        if head_rc != 0:
            self.error(
                "repository",
                f"--root is not a readable Git worktree: {_diagnostic(head_process)}",
            )
        elif source_revision != head:
            self.error(
                "receipt.source_revision",
                f"does not match --root HEAD: recorded {source_revision!r}, actual {head!r}",
            )
        if head_rc == 0 and GIT_REVISION.fullmatch(head):
            self.head_before_run = head
        origin_process = _git_run(
            self.root, "config", "--get", "remote.origin.url", timeout=GIT_QUICK_TIMEOUT
        )
        origin = origin_process.stdout.decode("utf-8", errors="replace").strip()
        canonical_origin = origin[:-4] if origin.endswith(".git") else origin
        if origin_process.returncode != 0 or canonical_origin != REPOSITORY_ID:
            detail = f" ({_diagnostic(origin_process)})" if origin_process.returncode else ""
            self.error(
                "repository.origin",
                f"must identify {REPOSITORY_ID!r}; actual {origin!r}{detail}",
            )
        refusals = worktree_refusals(self.root, self.head_before_run)
        for refusal in refusals:
            self.error("repository", f"worktree is not clean: {refusal}")
        self.worktree_clean_before_run = not refusals
        self.checkout_refused = bool(refusals)

        # The digest of the bytes parsed above, not of a second read.
        self.bound_files[self.receipt_path] = hashlib.sha256(receipt_bytes).hexdigest()
        toolchain_path = self.resolve_ref(
            receipt.get("toolchain_manifest"),
            "receipt.toolchain_manifest",
        )
        corpus_path = self.resolve_ref(receipt.get("corpus_manifest"), "receipt.corpus_manifest")
        subject_graph_path = self.resolve_ref(
            receipt.get("subject_graph"),
            "receipt.subject_graph",
        )
        linked_module_path = self.resolve_ref(
            receipt.get("linked_module"),
            "receipt.linked_module",
        )
        release_artifact_path = self.resolve_ref(
            receipt.get("release_artifact"),
            "receipt.release_artifact",
        )
        policy_path = self.resolve_ref(
            receipt.get("authority_policy"),
            "receipt.authority_policy",
        )
        policy_authorization_path = self.resolve_ref(
            receipt.get("policy_authorization"),
            "receipt.policy_authorization",
        )
        toolchain_digest = (
            receipt.get("toolchain_manifest", {}).get("sha256")
            if isinstance(receipt.get("toolchain_manifest"), dict)
            else None
        )
        corpus_digest = (
            receipt.get("corpus_manifest", {}).get("sha256")
            if isinstance(receipt.get("corpus_manifest"), dict)
            else None
        )
        subject_graph_digest = (
            receipt.get("subject_graph", {}).get("sha256")
            if isinstance(receipt.get("subject_graph"), dict)
            else None
        )
        linked_module_digest = (
            receipt.get("linked_module", {}).get("sha256")
            if isinstance(receipt.get("linked_module"), dict)
            else None
        )
        release_artifact_digest = (
            receipt.get("release_artifact", {}).get("sha256")
            if isinstance(receipt.get("release_artifact"), dict)
            else None
        )
        policy_digest = (
            receipt.get("authority_policy", {}).get("sha256")
            if isinstance(receipt.get("authority_policy"), dict)
            else None
        )
        policy_authorization_digest = (
            receipt.get("policy_authorization", {}).get("sha256")
            if isinstance(receipt.get("policy_authorization"), dict)
            else None
        )
        common_paths = {
            "toolchain_manifest": toolchain_path,
            "corpus_manifest": corpus_path,
            "subject_graph": subject_graph_path,
            "linked_module": linked_module_path,
            "release_artifact": release_artifact_path,
            "authority_policy": policy_path,
            "policy_authorization": policy_authorization_path,
        }
        non_null_common_paths = [path for path in common_paths.values() if path is not None]
        # Distinct files, not only distinct spellings: a case alias or a hard
        # link names one file twice.  A path that cannot be stat'ed is already
        # refused by resolve_ref.
        common_identities = [
            identity for identity in map(_identity_or_none, non_null_common_paths)
            if identity is not None
        ]
        if len(non_null_common_paths) != len(set(non_null_common_paths)) or len(
            common_identities
        ) != len(set(common_identities)):
            self.error("receipt", "all common bound artifacts must use distinct paths")

        toolchain_manifest = (
            self.load_json(toolchain_path, "toolchain_manifest")
            if toolchain_path is not None and _is_regular_file(toolchain_path)
            else None
        )
        corpus_manifest = (
            self.load_json(corpus_path, "corpus_manifest")
            if corpus_path is not None and _is_regular_file(corpus_path)
            else None
        )
        subject_graph = (
            self.load_json(subject_graph_path, "subject_graph")
            if subject_graph_path is not None and _is_regular_file(subject_graph_path)
            else None
        )
        authority_policy = (
            self.load_json(policy_path, "authority_policy")
            if policy_path is not None and _is_regular_file(policy_path)
            else None
        )
        authorized_inputs = {
            "toolchain_manifest_sha256": toolchain_digest,
            "corpus_manifest_sha256": corpus_digest,
            "subject_graph_sha256": subject_graph_digest,
            "linked_module_sha256": linked_module_digest,
            "release_artifact_sha256": release_artifact_digest,
        }
        self.validate_policy(
            authority_policy,
            source_revision,
            acceptance_run_id,
            authorized_inputs,
        )
        self.verify_policy_authorization(
            policy_authorization_path,
            policy_path,
            policy_digest,
            authority_policy,
        )
        authority_contracts = self.validate_authority_contracts(authority_policy)
        self.validate_toolchain_manifest(
            toolchain_manifest,
            acceptance_run_id,
            source_revision,
            authority_contracts,
        )
        admitted_corpus_ids = self.validate_corpus_manifest(
            corpus_manifest,
            acceptance_run_id,
            source_revision,
            authority_contracts,
        )
        self.validate_subject_graph(
            subject_graph,
            acceptance_run_id,
            source_revision,
            admitted_corpus_ids,
            linked_module_digest,
            release_artifact_digest,
            authority_contracts,
        )
        if (
            policy_authorization_path is not None
            and _is_regular_file(policy_authorization_path)
            and _file_size(policy_authorization_path) == 0
        ):
            self.error("receipt.policy_authorization", "must not be empty")

        gates = receipt.get("gates")
        if not isinstance(gates, dict):
            self.error("receipt.gates", "must be an object")
            return self.verdict(gate_results)
        actual_gates = set(gates)
        if actual_gates != set(GATES):
            missing = sorted(set(GATES) - actual_gates)
            unknown = sorted(actual_gates - set(GATES))
            if missing:
                self.error("receipt.gates", f"missing gates {missing}")
            if unknown:
                self.error("receipt.gates", f"unknown gates {unknown}")

        common_binding_ok = not self.errors
        descriptors: dict[str, tuple[str, Path, str, bytes, Path, Any]] = {}
        descriptor_ok = {gate: False for gate in GATES}
        checker_ids: set[str] = set()
        evidence_paths: set[Path] = set()
        evidence_identities: set[tuple[int, int]] = set()
        for gate in GATES:
            before = len(self.errors)
            descriptor = gates.get(gate)
            location = f"receipt.gates.{gate}"
            if not self.exact_keys(
                descriptor,
                {"checker", "checker_sha256", "evidence"},
                location,
            ):
                continue
            checker = descriptor.get("checker")
            if not isinstance(checker, str) or not CHECKER_ID.fullmatch(checker):
                self.error(f"{location}.checker", "has an invalid checker id")
                continue
            if checker != CHECKER_IDS[gate]:
                self.error(
                    f"{location}.checker",
                    f"must equal the schema-owned checker id {CHECKER_IDS[gate]!r}",
                )
            if checker in checker_ids:
                self.error(f"{location}.checker", "checker ids must be distinct across G1-G8")
            checker_ids.add(checker)
            checker_result = self.resolve_checker(
                gate,
                source_revision,
                descriptor.get("checker_sha256"),
                f"{location}.checker_sha256",
            )
            authorized_checker = (
                authority_policy.get("authorized_checkers", {}).get(gate)
                if isinstance(authority_policy, dict)
                and isinstance(authority_policy.get("authorized_checkers"), dict)
                else None
            )
            if (
                not isinstance(authorized_checker, dict)
                or descriptor.get("checker_sha256") != authorized_checker.get("sha256")
            ):
                self.error(
                    f"{location}.checker_sha256",
                    "does not equal the owner-authorized checker digest",
                )
            evidence_path = self.resolve_ref(descriptor.get("evidence"), f"{location}.evidence")
            if checker_result is None or evidence_path is None:
                continue
            checker_path, checker_digest, checker_bytes = checker_result
            evidence_identity = _identity_or_none(evidence_path)
            if evidence_path in evidence_paths or evidence_identity in evidence_identities:
                self.error(f"{location}.evidence.path", "evidence receipts must be distinct")
            evidence_paths.add(evidence_path)
            if evidence_identity is not None:
                evidence_identities.add(evidence_identity)
            evidence_digest = (
                descriptor.get("evidence", {}).get("sha256")
                if isinstance(descriptor.get("evidence"), dict)
                else None
            )
            descriptors[gate] = (
                checker,
                checker_path,
                checker_digest,
                checker_bytes,
                evidence_path,
                evidence_digest,
            )
            descriptor_ok[gate] = len(self.errors) == before

        metadata_paths = {
            self.receipt_path,
            *evidence_paths,
            *(descriptor[1] for descriptor in descriptors.values()),
        }
        for metadata_path in (
            toolchain_path,
            corpus_path,
            subject_graph_path,
            policy_path,
            policy_authorization_path,
        ):
            if metadata_path is not None:
                metadata_paths.add(metadata_path)
        forbidden = self.metadata(metadata_paths)

        common_paths_ready = common_binding_ok and all(
            path is not None and _is_regular_file(path) for path in common_paths.values()
        )
        checker_verdicts: dict[str, dict[str, Any]] = {}

        def validate_gate(gate: str, prior_gates_root: Optional[str]) -> None:
            before = len(self.errors)
            if gate not in descriptors:
                return
            if self.checkout_refused:
                # The receipt is refused already; executing a checker snapshot
                # taken from a checkout that is not the accepted commit proves
                # nothing and runs the candidate's code for no verdict.
                self.error(f"{gate}.checker_run", "checker not run: the checkout was refused")
                return
            if not common_paths_ready:
                self.error(f"{gate}.checker_run", "common bound artifacts are unavailable")
                return
            (
                checker,
                _checker_path,
                checker_digest,
                checker_bytes,
                evidence_path,
                evidence_digest,
            ) = descriptors[gate]
            assert toolchain_path is not None
            assert corpus_path is not None
            assert subject_graph_path is not None
            assert linked_module_path is not None
            assert release_artifact_path is not None
            assert policy_path is not None
            assert policy_authorization_path is not None
            checker_verdict = self.run_checker(
                gate,
                checker_bytes,
                evidence_path,
                toolchain_path,
                corpus_path,
                subject_graph_path,
                linked_module_path,
                release_artifact_path,
                policy_path,
                policy_authorization_path,
                acceptance_run_id,
                subject_graph_digest,
                linked_module_digest,
                release_artifact_digest,
                policy_digest,
                policy_authorization_digest,
                source_revision,
                checker_digest,
                evidence_digest,
                toolchain_digest,
                corpus_digest,
                prior_gates_root,
            )
            if checker_verdict is None:
                return
            checker_verdicts[gate] = checker_verdict
            verdict_keys = {
                "schema",
                "goal_id",
                "gate",
                "checker",
                "repository_id",
                "acceptance_run_id",
                "checker_sha256",
                "evidence_sha256",
                "source_revision",
                "toolchain_sha256",
                "corpus_manifest_sha256",
                "subject_graph_sha256",
                "linked_module_sha256",
                "release_artifact_sha256",
                "authority_policy_sha256",
                "policy_authorization_sha256",
                "prior_gates_root",
                "passed",
                "checks",
            }
            self.exact_keys(checker_verdict, verdict_keys, f"{gate}.checker_verdict")
            expected_scalars = {
                "schema": CHECKER_VERDICT_SCHEMA,
                "goal_id": GOAL_ID,
                "gate": gate,
                "checker": checker,
                "repository_id": REPOSITORY_ID,
                "acceptance_run_id": acceptance_run_id,
                "checker_sha256": checker_digest,
                "evidence_sha256": evidence_digest,
                "source_revision": source_revision,
                "toolchain_sha256": toolchain_digest,
                "corpus_manifest_sha256": corpus_digest,
                "subject_graph_sha256": subject_graph_digest,
                "linked_module_sha256": linked_module_digest,
                "release_artifact_sha256": release_artifact_digest,
                "authority_policy_sha256": policy_digest,
                "policy_authorization_sha256": policy_authorization_digest,
                "prior_gates_root": prior_gates_root,
            }
            for key, expected in expected_scalars.items():
                if checker_verdict.get(key) != expected:
                    self.error(
                        f"{gate}.checker_verdict.{key}",
                        f"must equal the receipt-bound value {expected!r}",
                    )
            if checker_verdict.get("passed") is not True:
                self.error(
                    f"{gate}.checker_verdict.passed",
                    "fresh checker verdict must be the boolean true",
                )

            checks = checker_verdict.get("checks")
            if not isinstance(checks, list) or not checks:
                self.error(f"{gate}.checker_verdict.checks", "must be a non-empty list")
                return
            rows: dict[str, dict[str, Any]] = {}
            for index, row in enumerate(checks):
                row_location = f"{gate}.checker_verdict.checks[{index}]"
                if not self.exact_keys(row, {"id", "passed", "artifacts"}, row_location):
                    continue
                check_id = row.get("id")
                if not isinstance(check_id, str) or not check_id:
                    self.error(f"{row_location}.id", "must be a non-empty string")
                    continue
                if check_id in rows:
                    self.error(f"{row_location}.id", f"duplicate check id {check_id!r}")
                rows[check_id] = row
                if row.get("passed") is not True:
                    self.error(f"{row_location}.passed", "must be the boolean true")
                artifacts = row.get("artifacts")
                if not isinstance(artifacts, list) or not artifacts:
                    self.error(f"{row_location}.artifacts", "must be a non-empty list")
                    continue
                seen_artifacts: set[Path] = set()
                for artifact_index, artifact in enumerate(artifacts):
                    artifact_path = self.resolve_ref(
                        artifact,
                        f"{row_location}.artifacts[{artifact_index}]",
                        forbidden=forbidden,
                    )
                    if artifact_path is not None and artifact_path in seen_artifacts:
                        self.error(
                            f"{row_location}.artifacts[{artifact_index}]",
                            "duplicates an artifact in the same check",
                        )
                    if artifact_path is not None:
                        seen_artifacts.add(artifact_path)

            required = set(REQUIRED_CHECKS[gate])
            observed = set(rows)
            if required - observed:
                self.error(
                    f"{gate}.checker_verdict.checks",
                    f"missing required checks {sorted(required - observed)}",
                )
            if observed - required:
                self.error(
                    f"{gate}.checker_verdict.checks",
                    f"unknown checks {sorted(observed - required)}",
                )
            gate_results[gate] = (
                common_binding_ok
                and descriptor_ok[gate]
                and len(self.errors) == before
            )

        for gate in GATES[:-1]:
            validate_gate(gate, None)

        if all(gate_results[gate] for gate in GATES[:-1]):
            root_payload = {
                "schema": "trust.two-language.prior-gates-root/v1",
                "goal_id": GOAL_ID,
                "repository_id": REPOSITORY_ID,
                "acceptance_run_id": acceptance_run_id,
                "source_revision": source_revision,
                "subject_graph_sha256": subject_graph_digest,
                "linked_module_sha256": linked_module_digest,
                "release_artifact_sha256": release_artifact_digest,
                "gates": {gate: checker_verdicts[gate] for gate in GATES[:-1]},
            }
            canonical = json.dumps(
                root_payload,
                sort_keys=True,
                separators=(",", ":"),
            ).encode("utf-8")
            self.prior_gates_root = hashlib.sha256(canonical).hexdigest()
            validate_gate("G8", self.prior_gates_root)
        else:
            self.error("G8.checker_run", "G1-G7 must pass before the G8 seal checker runs")

        self.post_run_integrity_check()

        return self.verdict(gate_results)

    def verdict(self, gate_results: dict[str, bool]) -> dict[str, Any]:
        accepted = not self.errors and all(gate_results.values())
        return {
            "schema": VERDICT_SCHEMA,
            "goal_id": GOAL_ID,
            "accepted": accepted,
            "result": (
                "checker-verified-structurally-complete" if accepted else "incomplete"
            ),
            "gate_results": gate_results,
            "prior_gates_root": self.prior_gates_root,
            "trusted_owner_key_fingerprint": self.trusted_owner_fingerprint,
            "errors": self.errors,
            "scope": "checker-executed structural conjunction of G1-G8 evidence",
            "does_not_establish": (
                "the semantic correctness of an evidence-producing checker; "
                "that checker and its independent controls own that claim"
            ),
        }


def validate_receipt(
    receipt_path: Union[str, Path],
    root: Union[str, Path],
    trusted_owner_key: Optional[Union[str, Path]] = None,
    external_verifier: Optional[Union[str, Path]] = None,
    external_verifier_sha256: Optional[str] = None,
) -> dict[str, Any]:
    root_path = Path(root)
    resolved_receipt = Path(receipt_path)
    if not resolved_receipt.is_absolute():
        resolved_receipt = root_path / resolved_receipt
    owner_key_path = Path(trusted_owner_key) if trusted_owner_key is not None else None
    verifier_path = Path(external_verifier) if external_verifier is not None else None
    return ReceiptValidator(
        root_path, resolved_receipt, owner_key_path,
        verifier_path, external_verifier_sha256,
    ).validate()


def main(argv: Optional[list[str]] = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--receipt", required=True, help="completion receipt JSON")
    parser.add_argument("--root", default=".", help="Git worktree and artifact root")
    parser.add_argument(
        "--trusted-owner-key",
        help="external ssh-ed25519 key for policy verification; caller input is not independent owner authorization",
    )
    parser.add_argument(
        "--external-verifier",
        help="external G8 verifier-copy path; comparison alone grants no proof authority",
    )
    parser.add_argument(
        "--external-verifier-sha256",
        help="caller-supplied G8 verifier digest; not an independently authorized pin",
    )
    parser.add_argument(
        "--candidate-verifier",
        help=(
            "candidate-tree verifier whose bytes must equal this externally pinned "
            "verifier before validating a release"
        ),
    )
    parser.add_argument("--text", action="store_true", help="print a concise human verdict")
    args = parser.parse_args(argv)
    if args.candidate_verifier is not None:
        root_path, problem = _resolved(Path(args.root))
        if problem is not None:
            parser.error(f"--root cannot be resolved: {problem}")
        running_path = Path(__file__)
        if os.path.islink(running_path):
            parser.error("running verifier must not be a symlink")
        running_verifier, problem = _resolved(running_path)
        if problem is not None:
            parser.error(f"running verifier cannot be resolved: {problem}")
        inside = _inside_root_by_identity(running_verifier, root_path)
        if inside is not None:
            parser.error(f"running verifier must be outside --root: {inside}")
        candidate = Path(args.candidate_verifier)
        if not candidate.is_absolute():
            candidate = root_path / candidate
        mode, problem = _file_mode(candidate, follow_symlinks=False)
        if problem is not None:
            parser.error(f"--candidate-verifier cannot be stat'ed: {problem}")
        if mode is not None and stat.S_ISLNK(mode):
            parser.error("--candidate-verifier must not be a symlink")
        candidate, problem = _resolved(candidate)
        if problem is not None:
            parser.error(f"--candidate-verifier cannot be resolved: {problem}")
        try:
            candidate.relative_to(root_path)
        except ValueError:
            parser.error("--candidate-verifier must resolve inside --root")
        try:
            same_bytes = _sha256(candidate) == _sha256(running_verifier)
        except OSError:
            same_bytes = False
        if not same_bytes:
            parser.error(
                "candidate verifier bytes do not equal the externally pinned verifier"
            )
    verdict = validate_receipt(
        args.receipt, args.root, args.trusted_owner_key,
        args.external_verifier, args.external_verifier_sha256,
    )
    if args.text:
        print(f"{verdict['goal_id']}: {verdict['result'].upper()}")
        for gate, passed in verdict["gate_results"].items():
            print(f"  {gate}: {'PASS' if passed else 'INCOMPLETE'}")
        for error in verdict["errors"]:
            print(f"  ERROR: {error}")
    else:
        print(json.dumps(verdict, indent=2, sort_keys=True))
    return 0 if verdict["accepted"] else 1


if __name__ == "__main__":
    sys.exit(main())
