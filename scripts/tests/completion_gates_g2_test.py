#!/usr/bin/env python3
"""Controls for the G2 schema-owned gate checker.

The checker is driven EXACTLY as ``scripts/two_language_completion_gate.py``
drives it — a read-only snapshot, ``python -I``, the sandbox environment, the
full argv — against a temp root that is a REAL git superproject whose
``first-party/clean`` is an initialized submodule at a committed pin (a mini
clean repository carrying the ledgers, the corpus MANIFEST and the corpus
files the checker consults).  Tree mutations commit through both repositories
so they test the RULE; the binding tests leave edits uncommitted, symlink a
ledger, strip the submodule's ``.git``, or commit files in place of the
gitlink, and must each be refused by name (every one of these passed on the
first landing of the checker — adversarial review, 2026-09-16).

The bundle every test starts from is what the instruments could produce
today plus the fixed contracts: only the ledger classification passes,
while even favorable authored pin, inventory and suite reports stay red.  The
``vanilla_lean_build`` envelope reads red for the reason its instrument
states, and the other unavailable-producer conjuncts refuse by name.  Each
mutation must then change exactly its own conjunct's (verdict, diagnostic)
pair and nothing else.
"""

from __future__ import annotations

import hashlib
import importlib.util
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
import unittest
from datetime import datetime, time, timedelta, timezone
from pathlib import Path
from unittest import mock

ROOT = Path(__file__).resolve().parents[2]
CHECKER = ROOT / "scripts" / "completion_gates" / "check_g2_lean_input.py"
GATE_SCRIPT = ROOT / "scripts" / "two_language_completion_gate.py"
CHECKER_ID = "trust.two-language.g2.lean-input/v2"
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
PIN, BUILD, OLEAN, CENSUS, SUITE, LEDGER, PARITY, TOTALITY, SURFACE = REQUIRED
VERDICT_KEYS = {
    "schema", "goal_id", "gate", "checker", "repository_id", "acceptance_run_id",
    "checker_sha256", "evidence_sha256", "source_revision", "toolchain_sha256",
    "corpus_manifest_sha256", "subject_graph_sha256", "linked_module_sha256",
    "release_artifact_sha256", "authority_policy_sha256", "policy_authorization_sha256",
    "prior_gates_root", "passed", "checks",
}
ZERO = "0" * 64
SOURCE_REVISION = "a" * 40
FIXTURE_TODAY = datetime.now(timezone.utc).date()

# The slice of the accepted tree the checker reads, at the paths it fixes.
CLEAN = "first-party/clean"
TOOLCHAIN_PIN = f"{CLEAN}/lean-toolchain"
BASELINE = f"{CLEAN}/tests/upstream-lean/baseline.toml"
EXCEPTIONS = f"{CLEAN}/tests/upstream-lean/exceptions.toml"
CORPUS = f"{CLEAN}/tests/upstream-lean/corpus.toml"
MANIFEST = f"{CLEAN}/tests/lean4_compat/MANIFEST.json"
CORPUS_DIR = f"{CLEAN}/tests/lean4_compat/lean4_tests"
COMMIT = "db93fe1608548721853390a10cd40580fe7d22ae"
VERSION = "v4.27.0"
SUITE_FILES = ("1007.lean", "1011.lean", "1021.lean")
PROBES = tuple(f"upstream-lean.{name[:-5]}.decl" for name in SUITE_FILES)
FIXTURE_SOURCE = "def wsum (a b : UInt64) : UInt64 := a + b\ntheorem trivialProof : True := True.intro\n"
SEMANTICS_ROLES = (
    "rust_language", "lean_language", "trust_ir", "rust_to_trust_ir_refinement",
    "lean_to_trust_ir_refinement", "observation_model", "undefined_behavior", "abi_memory_model",
)
# Fixture-side copies of the checker's fixed vocabularies: a drift here is a
# contract change and must be visible in BOTH files.
FAMILIES = {
    "Expr": ("bvar", "fvar", "mvar", "sort", "const", "app", "lam", "forallE", "letE", "lit", "mdata", "proj"),
    "Level": ("zero", "succ", "max", "imax", "param", "mvar"),
    "Literal": ("natVal", "strVal"),
    "ConstantInfo": ("axiomInfo", "defnInfo", "thmInfo", "opaqueInfo", "quotInfo", "inductInfo", "ctorInfo", "recInfo"),
    "Syntax": ("missing", "node", "atom", "ident"),
}
FEATURES = (
    "macro_rules", "syntax_and_macro_commands", "elab_commands", "notation", "do_notation",
    "io_actions", "partial_def", "unsafe_def", "implemented_by", "extern_ffi",
    "opaque_definitions", "initialize_commands",
)
# What lean_build.rs writes (LITERAL_LIMITATIONS), verbatim.
REAL_LIMITATIONS = [
    "Only local-source wrapping binops, ordinary UInt8/16/32/64 parameter projections and in-range UInt literal returns "
    "admitted by the independent actual-SSA gate are supported; literal parameters must share the result width.",
    "External .olean packages, general runtime-body completeness, mixed-language linking and native codegen remain unavailable.",
    "Serialized gate bindings are not transferable proof authority or G1-G8 completion evidence.",
]
UNSEEDED_BANNER = (
    "=" * 72 + "\nUPSTREAM-LEAN CORPUS IS UNSEEDED — nothing was executed.\n\n"
    "  corpus.toml carries no probes, so this run measures NOTHING about\n" + "=" * 72 + "\n"
)


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def sha(tag: str) -> str:
    return hashlib.sha256(tag.encode()).hexdigest()


def corpus_text(name: str) -> str:
    return f"-- upstream Lean test {name}\ndef value : Nat := {len(name)}\n"


def semantics_definition(role: str) -> dict[str, str]:
    return {"id": f"trust.semantics.{role}", "path": f"semantics-{role}.def", "sha256": sha(f"def:{role}")}


DEFAULT_POLICY = {
    "schema": "trust.two-language.authority-policy/v2",
    "contracts": {
        "semantics": {
            "schema": "trust.two-language.semantics-contract/v1",
            "goal_id": "TRUST-TWO-LANGUAGE-100",
            "repository_id": "https://github.com/alabsystems/trust",
            "definitions": {role: semantics_definition(role) for role in SEMANTICS_ROLES},
        }
    },
}


# ── the tree slice ─────────────────────────────────────────────────────────


def baseline_toml(version: str = VERSION, commit: str = COMMIT, representative: bool = True,
                  file_count: int = len(SUITE_FILES)) -> str:
    return f'''# fixture baseline — the shape of first-party/clean/tests/upstream-lean/baseline.toml
schema_version = "0.1.0"
id = "upstream-lean.toolchain-baseline.fixture"

[upstream]
channel = "lean4"
revision = "leanprover/lean4:{commit}"
version = "{version}"
snapshot_date = "2026-01-28"
corpus_path = "tests/lean4_compat/lean4_tests"
manifest_path = "tests/lean4_compat/MANIFEST.json"
file_count = {file_count}

[local]
revision = "clean:main"

[corpus]
selection = "stratified-full"
selection_is_representative = {"true" if representative else "false"}
selection_defect = "alphabetical head of ~2,500 files"  # only meaningful when false

[seeding]
unseeded_until = "2026-12-01"

[[entries]]
id = "lean.parse"
surface = "parser"
status = "compatible"
labels = ["upstream-lean", "parser"]

[entries.expectation]
upstream_behavior = "Lean 4 parses the file — a # inside a string is not a comment"

[[entries]]
id = "lean.elab"
surface = "elaborator"
status = "compatible"

[[entries]]
id = "lean.trust-ir"
surface = "trust_ir"
status = "compatible"
'''


def manifest_json(version: str = VERSION, commit: str = COMMIT, files: tuple[str, ...] = SUITE_FILES) -> dict:
    return {
        "lean4_version": version, "lean4_commit": commit, "tests_path": "tests/lean",
        "downloaded_at": "2026-01-28T18:29:11.843602Z", "file_count": len(files),
        "checksums": {name: "sha256:" + sha256_bytes(corpus_text(name).encode()) for name in files},
    }


def corpus_toml(probes: tuple[str, ...] = PROBES) -> str:
    if not probes:
        return 'schema_version = "0.1.0"\nprobes = []\n'
    rows = "".join(
        f'\n[[probes]]\nid = "{probe}"\nfile = "{probe.split(".")[1]}.lean"\ndecl = "decl"\nexpected = "lowers"\n'
        for probe in probes
    )
    return f'schema_version = "0.1.0"\n{rows}'


def ledger_row(**overrides: str) -> str:
    row = {
        "id": "upstream-lean.exc.needs-lake", "probe_id": PROBES[2], "observed": "rejected",
        "kind": "environmental_skip", "status": "active", "owner": "lean-frontend",
        "reason": "fixture: the probe needs Lake, which the sandbox does not carry",
        "issue": "local:docs/fixture.md",
        "reviewed_on": (FIXTURE_TODAY - timedelta(days=30)).isoformat(),
        "expires_on": (FIXTURE_TODAY + timedelta(days=30)).isoformat(),
    }
    row.update(overrides)
    return "\n[[exceptions]]\n" + "".join(f'{key} = "{value}"\n' for key, value in row.items())


def exceptions_toml(extra_rows: str = "") -> str:
    resolved = ledger_row(id="upstream-lean.exc.retired", probe_id="upstream-lean.retired.decl", status="resolved")
    return 'schema_version = "0.1.0"\n' + ledger_row() + resolved + extra_rows


# ── the harness: a real superproject with an initialized submodule ──────────


def git(cwd: Path, *args: str, check: bool = True) -> str:
    process = subprocess.run(
        ["git", "-c", "commit.gpgsign=false", "-c", "protocol.file.allow=always", *args],
        cwd=str(cwd), check=False, capture_output=True, text=True,
    )
    if check and process.returncode != 0:
        raise RuntimeError(f"git {' '.join(args)} failed in {cwd}: {process.stderr.strip()}")
    return process.stdout


def init_repo(path: Path) -> None:
    path.mkdir(parents=True, exist_ok=True)
    git(path, "init", "-q")
    git(path, "config", "user.email", "g2@test.invalid")
    git(path, "config", "user.name", "g2-test")


class GateRoot:
    """A temp superproject (``root``) with ``first-party/clean`` an initialized
    submodule of a mini clean repository (``clean_src``) at a committed pin,
    plus artifacts, a bundle and the runner-side inputs."""

    def __init__(self, *, gitlink: bool = True) -> None:
        self.tmp = tempfile.TemporaryDirectory(prefix="trust-g2-gate-")
        base = Path(self.tmp.name).resolve()
        self.clean_src = base / "clean-src"
        self.root = base / "root"
        init_repo(self.clean_src)
        for relative, text in self.clean_files().items():
            path = self.clean_src / relative
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(text, encoding="utf-8")
        git(self.clean_src, "add", "-A")
        git(self.clean_src, "commit", "-q", "-m", "clean at the pin")
        init_repo(self.root)
        (self.root / ".gitignore").write_text("evidence/\n*.json\n*.bin\n", encoding="utf-8")
        (self.root / "Fixture.lean").write_text(FIXTURE_SOURCE, encoding="utf-8")
        if gitlink:
            git(self.root, "submodule", "add", "-q", str(self.clean_src), CLEAN)
            # A clone does not inherit its source repository's local identity.
            # Mutation controls commit inside this checkout as well.
            git(self.sub, "config", "user.email", "g2@test.invalid")
            git(self.sub, "config", "user.name", "g2-test")
        else:
            # Files committed IN PLACE of the gitlink: the shape a plain copy has.
            shutil.copytree(self.clean_src, self.root / CLEAN, ignore=shutil.ignore_patterns(".git"))
        git(self.root, "add", "-A")
        git(self.root, "commit", "-q", "-m", "fixture superproject")
        (self.root / "evidence").mkdir()
        self.linked_module = self.root / "linked.trust-ir.bin"
        self.linked_module.write_bytes(b"TRUST_IR\x00linked-module-bytes")
        admission_entries = [{
            "id": "lean.fixture",
            "kind": "lean-source",
            "admitted": True,
            "source": {"path": "Fixture.lean", "sha256": sha256_bytes(FIXTURE_SOURCE.encode("utf-8"))},
            "expected_outcome": "accept",
        }]
        self.admission_contract = self.root / "evidence" / "admission-contract.json"
        self.admission_contract.write_text(json.dumps({
            "schema": "trust.two-language.admission-contract/v1",
            "goal_id": "TRUST-TWO-LANGUAGE-100",
            "repository_id": "https://github.com/alabsystems/trust",
            "lanes": {"lean": {"upstream_revision": COMMIT, "entries": admission_entries}},
        }), encoding="utf-8")
        admission_digest = sha256_bytes(self.admission_contract.read_bytes())
        self.policy = self.root / "policy.json"
        self.policy.write_text(json.dumps({
            **DEFAULT_POLICY,
            "contracts": {
                **DEFAULT_POLICY["contracts"],
                "admission": {
                    "id": "trust.two-language.contract.admission",
                    "path": str(self.admission_contract.relative_to(self.root)),
                    "sha256": admission_digest,
                },
            },
        }), encoding="utf-8")
        self.corpus_manifest = self.root / "corpus.json"
        self.corpus_manifest.write_text(json.dumps({
            "schema": "trust.two-language.corpus-manifest/v1",
            "goal_id": "TRUST-TWO-LANGUAGE-100",
            "acceptance_run_id": "run-1",
            "source_revision": SOURCE_REVISION,
            "repository_id": "https://github.com/alabsystems/trust",
            "lean": {
                "upstream_revision": COMMIT,
                "admission_policy_sha256": admission_digest,
                "entries": admission_entries,
            },
        }), encoding="utf-8")
        for name in ("toolchain", "subject-graph", "release", "policy-auth"):
            (self.root / f"{name}.json").write_text("{}", encoding="utf-8")
        self.artifacts: dict[str, dict[str, str]] = {}

    @staticmethod
    def clean_files() -> dict[str, str]:
        files = {
            "lean-toolchain": f"leanprover/lean4:{VERSION}\n",
            "tests/upstream-lean/baseline.toml": baseline_toml(),
            "tests/lean4_compat/MANIFEST.json": json.dumps(manifest_json(), indent=1),
            "tests/upstream-lean/corpus.toml": corpus_toml(),
            "tests/upstream-lean/exceptions.toml": exceptions_toml(),
        }
        for name in SUITE_FILES:
            files[f"tests/lean4_compat/lean4_tests/{name}"] = corpus_text(name)
        return files

    # -- the tree -----------------------------------------------------------

    @property
    def sub(self) -> Path:
        return self.root / CLEAN

    def tree_write(self, relative: str, text: str, *, commit: bool = True) -> None:
        path = self.root / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text, encoding="utf-8")
        if commit:
            self.commit_tree()

    def tree_remove(self, relative: str, *, commit: bool = True) -> None:
        (self.root / relative).unlink()
        if commit:
            self.commit_tree()

    def tree_text(self, relative: str) -> str:
        return (self.root / relative).read_text(encoding="utf-8")

    def commit_tree(self) -> None:
        """Commit the submodule worktree and move the superproject's gitlink to it."""
        git(self.sub, "add", "-A")
        git(self.sub, "commit", "-q", "--allow-empty", "-m", "mutate")
        git(self.root, "add", "-A")
        git(self.root, "commit", "-q", "--allow-empty", "-m", "mutate")

    # -- artifacts ----------------------------------------------------------

    def write(self, check_id: str, document: dict | bytes, name: str | None = None) -> Path:
        data = document if isinstance(document, bytes) else json.dumps(document, indent=1).encode()
        path = self.root / "evidence" / (name or f"{check_id}.json")
        path.write_bytes(data)
        self.artifacts[check_id] = {"path": str(path.relative_to(self.root)), "sha256": sha256_bytes(data)}
        return path

    def bind_tree(self, check_id: str, relative: str) -> None:
        self.artifacts[check_id] = {"path": relative, "sha256": sha256_bytes((self.root / relative).read_bytes())}

    def rebind(self) -> None:
        """Refresh every recorded digest after a tree or artifact mutation."""
        for ref in self.artifacts.values():
            path = self.root / ref["path"]
            if path.is_file():
                ref["sha256"] = sha256_bytes(path.read_bytes())

    def bundle(self, **overrides) -> Path:
        doc = {
            "schema": "trust.two-language.gate-evidence/v1",
            "gate": "G2",
            "checker": CHECKER_ID,
            "artifacts": dict(self.artifacts),
        }
        doc.update(overrides)
        path = self.root / "bundle.json"
        path.write_text(json.dumps(doc), encoding="utf-8")
        return path

    def run(self, bundle: Path, *, receipt: bool = False, policy_sha256: str | None = None) -> tuple[int, dict, str]:
        checker_bytes = CHECKER.read_bytes()
        snapshot = self.root / "checker.py"
        if snapshot.exists():
            snapshot.chmod(0o644)
        snapshot.write_bytes(checker_bytes)
        snapshot.chmod(0o444)
        command = [
            sys.executable, "-I", str(snapshot),
            "--verify-evidence", str(bundle), "--root", str(self.root),
            "--toolchain-manifest", str(self.root / "toolchain.json"),
            "--corpus-manifest", str(self.root / "corpus.json"),
            "--subject-graph", str(self.root / "subject-graph.json"),
            "--linked-module", str(self.linked_module),
            "--release-artifact", str(self.root / "release.json"),
            "--authority-policy", str(self.policy),
            "--policy-authorization", str(self.root / "policy-auth.json"),
            "--acceptance-run-id", "run-1", "--source-revision", SOURCE_REVISION,
            "--checker-sha256", sha256_bytes(checker_bytes),
            "--evidence-sha256", sha256_bytes(bundle.read_bytes()),
            "--toolchain-sha256", ZERO,
            "--corpus-manifest-sha256", sha256_bytes(self.corpus_manifest.read_bytes()),
            "--subject-graph-sha256", ZERO,
            "--linked-module-sha256", sha256_bytes(self.linked_module.read_bytes()),
            "--release-artifact-sha256", ZERO,
            "--authority-policy-sha256", policy_sha256 or sha256_bytes(self.policy.read_bytes()),
            "--policy-authorization-sha256", ZERO,
        ]
        if receipt:
            command += ["--receipt", str(self.root / "receipt.json"), "--prior-gates-root", ZERO]
        env = {"HOME": self.tmp.name, "LANG": "C.UTF-8", "LC_ALL": "C.UTF-8",
               "PATH": "/usr/bin:/bin", "PYTHONHASHSEED": "0", "TZ": "UTC"}
        process = subprocess.run(command, cwd=self.root, env=env, check=False,
                                 capture_output=True, text=True, timeout=300)
        verdict = json.loads(process.stdout)
        return process.returncode, verdict, process.stderr


def diagnostics(err: str) -> dict[str, str]:
    """``{check id: diagnostic}`` from the checker's stderr."""
    out: dict[str, str] = {}
    for line in err.splitlines():
        if line.startswith("G2: "):
            check_id, sep, message = line[4:].partition(": ")
            if sep and check_id in REQUIRED:
                out[check_id] = message
    return out


def rows_of(verdict: dict) -> dict[str, bool]:
    return {row["id"]: row["passed"] for row in verdict["checks"]}


# ── the starting bundle ────────────────────────────────────────────────────


def ir_library_envelope() -> dict:
    """Shaped EXACTLY like targo-trust/src/lean_build.rs's LibraryEnvelope:
    native_codegen the string "unavailable", the real LITERAL_LIMITATIONS."""
    binary = b"TRUST_IR\x00fixture-module-bytes"
    helper = ["Foo", "helper"]  # a structured kernel Name, compared by identity not spelling
    return {
        "schema": "trust.lean.ir-library/v1",
        "authority": "recheck-sources-and-re-earn-gate-on-import",
        "native_codegen": "unavailable",
        "source_closure_sha256": sha("closure"),
        "owned_declarations_sha256": sha("owned"),
        "sources": [{"module": "Fixture", "path": "Fixture.lean", "source": FIXTURE_SOURCE,
                     "sha256": sha256_bytes(FIXTURE_SOURCE.encode("utf-8"))}],
        "owned_declarations": ["wsum", "trivialProof", helper],
        "kernel_only_declarations": ["trivialProof"],
        "bodies": [
            {"declaration": "wsum", "function_id": 0, "kernel_payload_sha256": sha("payload-wsum"),
             "subject_digest": "sha256:" + sha("subject-wsum"), "carrier": "UInt64", "method": "actual-ssa-gate"},
            {"declaration": helper, "function_id": 1, "kernel_payload_sha256": sha("payload-helper"),
             "subject_digest": "sha256:" + sha("subject-helper"), "carrier": "UInt8", "method": "actual-ssa-gate"},
        ],
        "module_binary_hex": binary.hex(),
        "module_sha256": sha256_bytes(binary),
        "module_stable_digest": "sha256:" + sha("stable"),
        "limitations": list(REAL_LIMITATIONS),
    }


def olean_import_graph() -> dict:
    def module(name, origin, imports, path=None):
        row = {"name": name, "origin": origin, "path": path or f"{name.replace('.', '/')}.olean",
               "imports": imports, "admission": "loaded"}
        if origin == "olean":
            row["olean_sha256"] = sha(f"olean:{name}")
        return row
    return {
        "schema": "trust.two-language.lean-olean-import-graph/v1",
        "authority": "admitted-external-imports",
        "toolchain": f"leanprover/lean4:{VERSION}",
        "modules": [
            module("Main", "source", ["Mathlib.Data.Nat.Basic"], "Main.lean"),
            module("Mathlib.Data.Nat.Basic", "olean", ["Mathlib.Init", "Init"]),
            module("Mathlib.Init", "olean", ["Init"]),
            module("Init", "olean", []),
        ],
    }


def kernel_roster() -> dict:
    """Shaped like targo-trust/src/lean_cli/census.rs's report around
    trust-certify's kernel roster, under the ADMITTING authority the checker
    fixes (no instrument writes it), with the denominator verified and every
    row's runtime classification measured — what the instrument does not do."""
    def row(name, kind, runtime, role="constant"):
        return {
            "identity": name, "name": name, "kernel_role": role, "constant_kind": "Definition",
            "has_value": True, "noncomputable": False, "kernel_payload_sha256": sha(f"payload:{name}"),
            "ownership": "elaborator-introduces" if role != "constructor" else "kernel-inductive-owner",
            "source_declarations": [0], "type_value_and_recursor_dependencies": [], "unresolved_dependencies": [],
            "kernel_classification": {"kind": kind}, "runtime_classification": runtime,
        }
    def body(index):
        return {"trust_ir_body": {"function_id": index, "subject_digest": "sha256:" + sha(f"subject{index}")}}
    return {
        "schema": "trust.lean.check-kernel-roster/v1",
        "authority": "post-lowering-inventory",
        "tool_version": "0.1.0",
        "tool_source_revision": SOURCE_REVISION,
        "requested_files": ["Fixture.lean"],
        "kernel_roster": {
            "schema": "trust.lean.kernel-roster/v1", "authority": "post-lowering-inventory",
            "scope": "new-owned-kernel-identities",
            "kernel_classification_schema": "trust.lean.kernel-classification/v1",
            "check_rejected": False,
            "declarations": [
                row("wsum", "computational-candidate", body(0)),
                row("trivialProof", "proof-only", "kernel-only"),
                row("Choice", "type-family", "kernel-only", "inductive"),
                row("Choice.one", "primitive-candidate", body(1), "constructor"),
            ],
            "unattributed_declarations": 0,
            "runtime_body_universe": "measured",
            "denominator_status": "denominator_verified",
            "limitations": [], "errors": [],
        },
        "check_report": {"language": "clean", "accepted": 1, "rejected": 0},
        "source_graph": {
            "schema": "trust.lean.source-check-observation/v1", "operation": "build",
            "source_closure_accepted": True,
            "sources": [{"path": "Fixture.lean", "module": "Fixture", "sha256": sha256_bytes(FIXTURE_SOURCE.encode("utf-8")),
                         "bytes": len(FIXTURE_SOURCE.encode("utf-8")), "read_status": "read-utf8"}],
            "unresolved_imports": [], "tool_path_bytes_stable": True,
            "denominator_status": "denominator_verified", "runtime_body_universe": "measured",
        },
    }


def suite_run(results: list[dict] | None = None) -> dict:
    """Shaped like run_upstream_lean.py --json over the pinned probes.  The
    third probe is rejected and covered by the ledger's environmental_skip row."""
    if results is None:
        results = [{"probe_id": probe, "file": f"{probe.split('.')[1]}.lean", "decl": "decl",
                    "expected": "lowers", "observed": "lowers", "detail": ""} for probe in PROBES]
        results[2]["observed"] = "rejected"
        results[2]["detail"] = "exit 1: unknown package Lake"
    matched = sum(1 for r in results if r["observed"] == r["expected"])
    return {
        "summary": {"probes": len(results), "executed": len(results), "matched_pin": matched,
                    "unseeded": not results, "findings": 0},
        "results": results,
        "findings": [],
    }


def surface_parity() -> dict:
    pinned = semantics_definition("lean_language")
    return {
        "schema": "trust.two-language.lean-surface-parity/v1",
        "lean_language_definition": {"id": pinned["id"], "sha256": pinned["sha256"]},
        "upstream_revision": f"leanprover/lean4:{COMMIT}",
        "programs": [
            {"id": "accepts-unicode-def", "source_sha256": sha("p1"), "upstream_verdict": "accept", "trust_verdict": "accept"},
            {"id": "rejects-ill-typed", "source_sha256": sha("p2"), "upstream_verdict": "reject", "trust_verdict": "reject"},
        ],
    }


def constructor_totality() -> dict:
    return {
        "schema": "trust.two-language.lean-elaborator-constructor-totality/v1",
        "families": {family: {c: {"status": "handled", "evidence_sha256": sha(f"{family}.{c}")} for c in constructors}
                     for family, constructors in FAMILIES.items()},
    }


def macro_io_surface() -> dict:
    kernel_only = {"macro_rules", "syntax_and_macro_commands", "elab_commands", "notation"}
    return {
        "schema": "trust.two-language.lean-macro-io-unsafe-ffi-surface/v1",
        "features": {f: {"status": "supported", "lowering": "kernel-only" if f in kernel_only else "trust-ir-body",
                         "evidence_sha256": sha(f)} for f in FEATURES},
    }


def g2_bundle(gr: GateRoot) -> None:
    gr.bind_tree(PIN, BASELINE)
    gr.write(BUILD, ir_library_envelope(), "fixture.trust-ir.json")
    gr.write(OLEAN, olean_import_graph())
    gr.write(CENSUS, kernel_roster(), "census.json")
    gr.write(SUITE, suite_run(), "upstream-lean-run.json")
    gr.bind_tree(LEDGER, EXCEPTIONS)
    gr.write(PARITY, surface_parity())
    gr.write(TOTALITY, constructor_totality())
    gr.write(SURFACE, macro_io_surface())


# What the starting bundle reads: (passed, a substring of the diagnostic when red).
EXPECTED_BASELINE = {
    PIN: (False, "no independent enumeration"),
    BUILD: (False, "the instrument's own refusal"),
    OLEAN: (False, "no instrument produces"),
    CENSUS: (False, "no independent producer binds"),
    SUITE: (False, "no independent runner/compiler"),
    LEDGER: (True, ""),
    PARITY: (False, "no instrument produces"),
    TOTALITY: (False, "no instrument produces"),
    SURFACE: (False, "no instrument produces"),
}


# ── one independent mutation set per conjunct: mutate(gr) edits the tree or an artifact ──


def json_mut(check_id: str, fn):
    def mutate(gr: GateRoot) -> None:
        path = gr.root / gr.artifacts[check_id]["path"]
        gr.write(check_id, fn(json.loads(path.read_text(encoding="utf-8"))), path.name)
    return mutate


def tree_mut(relative: str, fn):
    def mutate(gr: GateRoot) -> None:
        gr.tree_write(relative, fn(gr.tree_text(relative)))
    return mutate


def setting(key, value):
    def fn(doc):
        doc[key] = value
        return doc
    return fn


def _pins_move_without_the_toolchain(gr: GateRoot) -> None:
    gr.tree_write(BASELINE, baseline_toml(version="v4.28.0"), commit=False)
    gr.tree_write(MANIFEST, json.dumps(manifest_json(version="v4.28.0")))


def _zero_one_checksum(gr: GateRoot) -> None:
    manifest = manifest_json()
    manifest["checksums"][SUITE_FILES[1]] = "sha256:" + ZERO
    gr.tree_write(MANIFEST, json.dumps(manifest))


def _shift_owner_revision(gr: GateRoot) -> None:
    contract = json.loads(gr.admission_contract.read_text(encoding="utf-8"))
    contract["lanes"]["lean"]["upstream_revision"] = "e" * 40
    gr.admission_contract.write_text(json.dumps(contract), encoding="utf-8")
    digest = sha256_bytes(gr.admission_contract.read_bytes())
    policy = json.loads(gr.policy.read_text(encoding="utf-8"))
    policy["contracts"]["admission"]["sha256"] = digest
    gr.policy.write_text(json.dumps(policy), encoding="utf-8")
    corpus = json.loads(gr.corpus_manifest.read_text(encoding="utf-8"))
    corpus["lean"]["upstream_revision"] = "e" * 40
    corpus["lean"]["admission_policy_sha256"] = digest
    gr.corpus_manifest.write_text(json.dumps(corpus), encoding="utf-8")


def _drop_a_probe(doc):
    del doc["results"][1]
    doc["summary"].update(probes=2, executed=2, matched_pin=1)
    return doc


def _unseeded(doc):
    return {"summary": {"probes": 0, "executed": 0, "matched_pin": 0, "unseeded": True, "findings": 0},
            "results": [], "findings": []}


def _banner_capture(gr: GateRoot) -> None:
    path = gr.root / gr.artifacts[SUITE]["path"]
    gr.write(SUITE, UNSEEDED_BANNER.encode("utf-8") + path.read_bytes(), path.name)


def _break_the_chain(doc):
    for module in doc["modules"]:
        if module["name"] in ("Mathlib.Data.Nat.Basic", "Mathlib.Init"):
            module["imports"] = []
    return doc


def _cycle(doc):
    for module in doc["modules"]:
        if module["name"] == "Init":
            module["imports"] = ["Mathlib.Init"]
    return doc


def _row(index, **changes):
    def fn(doc):
        doc["kernel_roster"]["declarations"][index].update(changes)
        return doc
    return fn


def _families(fn):
    def apply(doc):
        fn(doc["families"])
        return doc
    return apply


def _rewritten_source(doc):
    text = FIXTURE_SOURCE + "-- a line the tree does not carry\n"
    doc["sources"][0].update(source=text, sha256=sha256_bytes(text.encode("utf-8")))
    return doc


G2_MUTATIONS = {
    PIN: [
        tree_mut(BASELINE, lambda t: t.replace("selection_is_representative = true", "selection_is_representative = false")),
        tree_mut(BASELINE, lambda t: t.replace('status = "compatible"', 'status = "unknown"', 1)),
        tree_mut(BASELINE, lambda t: t.replace('id = "lean.elab"', 'id = "lean.elab-missing"')),
        _shift_owner_revision,
        _pins_move_without_the_toolchain,
        lambda gr: gr.tree_write(MANIFEST, json.dumps(manifest_json(commit="e" * 40))),
        lambda gr: gr.tree_write(BASELINE, baseline_toml(file_count=100)),
        _zero_one_checksum,
        lambda gr: gr.tree_remove(f"{CORPUS_DIR}/{SUITE_FILES[1]}"),
        lambda gr: gr.tree_write(f"{CORPUS_DIR}/9999.lean", "-- a file the MANIFEST does not pin\n"),
    ],
    BUILD: [
        json_mut(BUILD, setting("native_codegen", {"status": "executable-produced", "executable_sha256": ZERO, "target": "x"})),
        json_mut(BUILD, setting("limitations", [])),
        json_mut(BUILD, setting("limitations", REAL_LIMITATIONS[:2])),
        json_mut(BUILD, lambda d: (d["sources"][0].__setitem__("sha256", "0" * 64), d)[1]),
        json_mut(BUILD, lambda d: (d["sources"][0].__setitem__("path", "Missing.lean"), d)[1]),
        json_mut(BUILD, _rewritten_source),
        json_mut(BUILD, setting("module_sha256", "f" * 64)),
        json_mut(BUILD, lambda d: (d["owned_declarations"].append("orphan"), d)[1]),
        json_mut(BUILD, lambda d: (d["sources"][0].__setitem__("path", "Fixture.rs"), d)[1]),
        json_mut(BUILD, lambda d: (d["kernel_only_declarations"].append("wsum"), d)[1]),
    ],
    OLEAN: [
        json_mut(OLEAN, setting("schema", "trust.lean.olean-closure-observation/v1")),
        json_mut(OLEAN, _cycle),
        json_mut(OLEAN, lambda d: (d["modules"][3].pop("olean_sha256"), d)[1]),
        json_mut(OLEAN, _break_the_chain),
        json_mut(OLEAN, lambda d: (d["modules"][0]["imports"].append("Lake.Ghost"), d)[1]),
        json_mut(OLEAN, lambda d: (d["modules"][1].__setitem__("admission", "observed"), d)[1]),
        json_mut(OLEAN, setting("toolchain", "leanprover/lean4:v4.30.0-rc2")),
    ],
    CENSUS: [
        json_mut(CENSUS, setting("authority", "diagnostic-only")),
        json_mut(CENSUS, lambda d: (d["kernel_roster"].__setitem__("authority", "diagnostic-only"), d)[1]),
        json_mut(CENSUS, setting("tool_source_revision", "b" * 40)),
        json_mut(CENSUS, setting("requested_files", ["Ghost.lean"])),
        json_mut(CENSUS, lambda d: (d["source_graph"]["sources"][0].__setitem__("sha256", "0" * 64), d)[1]),
        json_mut(CENSUS, lambda d: (d["kernel_roster"].__setitem__("denominator_status", "denominator_unverified"), d)[1]),
        json_mut(CENSUS, _row(0, runtime_classification="unmeasured")),
        json_mut(CENSUS, _row(0, kernel_classification={"kind": "unknown", "reason": "telescope too deep"})),
        json_mut(CENSUS, lambda d: (d["kernel_roster"].__setitem__("check_rejected", True), d)[1]),
        json_mut(CENSUS, lambda d: (d["source_graph"].__setitem__("unresolved_imports", [{"module": "Helper"}]), d)[1]),
        json_mut(CENSUS, lambda d: (d["source_graph"].__setitem__("runtime_body_universe", "unmeasured"), d)[1]),
        json_mut(CENSUS, _row(1, runtime_classification={"trust_ir_body": {"function_id": 9, "subject_digest": sha("x")}})),
    ],
    SUITE: [
        json_mut(SUITE, _unseeded),
        json_mut(SUITE, lambda d: (d["results"][0].__setitem__("observed", "rejected"), d)[1]),
        json_mut(SUITE, lambda d: (d["results"][0].__setitem__("expected", "rejected"), d)[1]),
        json_mut(SUITE, _drop_a_probe),
        json_mut(SUITE, lambda d: (d.__setitem__("findings", ["x: CRASHED"]), d["summary"].__setitem__("findings", 1), d)[2]),
        json_mut(SUITE, lambda d: (d["results"][2].__setitem__("observed", "crashed"), d)[1]),
        json_mut(SUITE, lambda d: (d["results"][0].__setitem__("probe_id", "forged.1007"), d)[1]),
        json_mut(SUITE, lambda d: (d["summary"].__setitem__("matched_pin", -5), d)[1]),
        json_mut(SUITE, lambda d: (d["summary"].__setitem__("probes", 100), d)[1]),
        _banner_capture,
    ],
    LEDGER: [
        tree_mut(EXCEPTIONS, lambda t: t + ledger_row(id="upstream-lean.exc.waiver", probe_id=PROBES[0], kind="expected_fail")),
        tree_mut(EXCEPTIONS, lambda t: t + ledger_row(id="upstream-lean.exc.diverge", probe_id=PROBES[1], kind="intentional_divergence")),
        tree_mut(EXCEPTIONS, lambda t: t + ledger_row(id="upstream-lean.exc.crash", probe_id=PROBES[0], observed="crashed")),
        tree_mut(EXCEPTIONS, lambda t: t + ledger_row(id="upstream-lean.exc.ghost", probe_id="upstream-lean.ghost.decl")),
        tree_mut(EXCEPTIONS, lambda t: t + ledger_row(
            id="upstream-lean.exc.stale", probe_id=PROBES[0],
            expires_on=(FIXTURE_TODAY - timedelta(days=1)).isoformat(),
        )),
    ],
    PARITY: [
        json_mut(PARITY, lambda d: (d["programs"][1].__setitem__("trust_verdict", "accept"), d)[1]),
        json_mut(PARITY, lambda d: (d.__setitem__("programs", d["programs"][:1]), d)[1]),
        json_mut(PARITY, lambda d: (d["lean_language_definition"].__setitem__("sha256", "9" * 64), d)[1]),
    ],
    TOTALITY: [
        json_mut(TOTALITY, _families(lambda f: f["Expr"].pop("proj"))),
        json_mut(TOTALITY, _families(lambda f: f["ConstantInfo"]["quotInfo"].__setitem__("status", "partial"))),
        json_mut(TOTALITY, _families(lambda f: f["Expr"].__setitem__("quux", {"status": "handled", "evidence_sha256": sha("q")}))),
    ],
    SURFACE: [
        json_mut(SURFACE, lambda d: (d["features"]["extern_ffi"].__setitem__("status", "refused-by-name"), d)[1]),
        json_mut(SURFACE, lambda d: (d["features"].pop("io_actions"), d)[1]),
        json_mut(SURFACE, lambda d: (d["features"]["partial_def"].__setitem__("lowering", "runtime-stub"), d)[1]),
    ],
}


def load_gate_module():
    spec = importlib.util.spec_from_file_location("two_language_completion_gate", GATE_SCRIPT)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def load_checker_module():
    spec = importlib.util.spec_from_file_location("check_g2_lean_input", CHECKER)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


class GateTestCase(unittest.TestCase):
    """The harness every G2 test class shares; it carries no tests itself."""

    def root(self, **kwargs) -> GateRoot:
        gr = GateRoot(**kwargs)
        self.addCleanup(gr.tmp.cleanup)
        return gr

    def run_bundle(self, gr: GateRoot) -> tuple[int, dict, dict[str, str]]:
        code, verdict, err = gr.run(gr.bundle())
        self.assertNotIn("Traceback", err)
        return code, verdict, diagnostics(err)

    def assert_verdict_shape(self, verdict: dict) -> None:
        self.assertEqual(set(verdict), VERDICT_KEYS)
        self.assertEqual(verdict["schema"], "trust.two-language.gate-checker-verdict/v2")
        self.assertEqual(verdict["gate"], "G2")
        self.assertEqual(verdict["checker"], CHECKER_ID)
        self.assertEqual([row["id"] for row in verdict["checks"]], list(REQUIRED))
        for row in verdict["checks"]:
            self.assertEqual(set(row), {"id", "passed", "artifacts"})


class CheckerContractTests(GateTestCase):
    def test_checker_is_the_one_the_gate_names(self) -> None:
        gate = load_gate_module()
        self.assertEqual(CHECKER, ROOT / gate.CHECKER_PATHS["G2"])
        self.assertEqual(CHECKER_ID, gate.CHECKER_IDS["G2"])
        self.assertEqual(REQUIRED, gate.REQUIRED_CHECKS["G2"])
        self.assertTrue(CHECKER.is_file() and not CHECKER.is_symlink())

    def test_starting_bundle_reads_as_documented(self) -> None:
        """Only the ledger check passes. Authored favorable pin, census
        and suite reports remain red, as do unavailable producer surfaces."""
        gr = self.root(); g2_bundle(gr)
        code, verdict, diag = self.run_bundle(gr)
        self.assert_verdict_shape(verdict)
        self.assertEqual(code, 1); self.assertFalse(verdict["passed"])
        rows = rows_of(verdict)
        for check_id, (passed, needle) in EXPECTED_BASELINE.items():
            self.assertEqual(rows[check_id], passed, f"{check_id}: {diag.get(check_id)}")
            if needle:
                self.assertIn(needle, diag[check_id])
        self.assertIn("G1-G8 completion evidence", diag[BUILD])
        self.assertIn('native_codegen is "unavailable"', diag[BUILD])
        self.assertEqual(verdict["authority_policy_sha256"], sha256_bytes(gr.policy.read_bytes()))
        # Every tree file a conjunct consulted is recorded beside its bound artifact.
        artifacts = {row["id"]: row["artifacts"] for row in verdict["checks"]}
        self.assertEqual([a["path"] for a in artifacts[LEDGER]], [EXCEPTIONS, CORPUS])
        self.assertIn(TOOLCHAIN_PIN, [a["path"] for a in artifacts[PIN]])
        self.assertIn(f"{CORPUS_DIR}/{SUITE_FILES[0]}", [a["path"] for a in artifacts[PIN]])
        for refs in artifacts.values():
            for ref in refs:
                self.assertEqual(set(ref), {"path", "sha256"})
                self.assertEqual(sha256_bytes((gr.root / ref["path"]).read_bytes()), ref["sha256"])
            self.assertEqual(len({ref["path"] for ref in refs}), len(refs))

    def test_authored_favorable_inventory_and_suite_remain_red(self) -> None:
        gr = self.root(); g2_bundle(gr)
        code, verdict, diag = self.run_bundle(gr)
        self.assertEqual(code, 1)
        self.assertFalse(rows_of(verdict)[PIN])
        self.assertIn("selection_is_representative alone is not G2 completeness evidence", diag[PIN])
        self.assertFalse(rows_of(verdict)[CENSUS])
        self.assertIn("owner-admitted Lean population", diag[CENSUS])
        self.assertFalse(rows_of(verdict)[SUITE])
        self.assertIn("owner-bound non-applicable classification", diag[SUITE])

    def test_pin_refuses_unknown_surface_and_owner_revision_drift(self) -> None:
        gr = self.root(); g2_bundle(gr)
        gr.tree_write(BASELINE, gr.tree_text(BASELINE).replace('status = "compatible"', 'status = "unknown"', 1))
        gr.rebind()
        _, verdict, diag = self.run_bundle(gr)
        self.assertFalse(rows_of(verdict)[PIN])
        self.assertIn("status 'unknown'", diag[PIN])

        gr = self.root(); g2_bundle(gr)
        _shift_owner_revision(gr)
        _, verdict, diag = self.run_bundle(gr)
        self.assertFalse(rows_of(verdict)[PIN])
        self.assertIn("disagrees with the owner admission and receipt corpus revision", diag[PIN])

        gr = self.root(); g2_bundle(gr)
        corpus = json.loads(gr.corpus_manifest.read_text(encoding="utf-8"))
        corpus["lean"]["upstream_revision"] = "e" * 40
        gr.corpus_manifest.write_text(json.dumps(corpus), encoding="utf-8")
        _, verdict, diag = self.run_bundle(gr)
        self.assertFalse(rows_of(verdict)[PIN])
        self.assertIn("receipt corpus Lean revision disagrees", diag[PIN])

    def test_duplicate_toml_keys_and_tables_are_refused(self) -> None:
        for mutate, expected in (
            (
                lambda text: text.replace(
                    "selection_is_representative = true",
                    "selection_is_representative = false\nselection_is_representative = true",
                ),
                "duplicate key `selection_is_representative`",
            ),
            (lambda text: text + "\n[corpus]\nselection_is_representative = true\n", "duplicate table `corpus`"),
        ):
            with self.subTest(expected=expected):
                gr = self.root(); g2_bundle(gr)
                gr.tree_write(BASELINE, mutate(gr.tree_text(BASELINE)))
                gr.rebind()
                _, verdict, diag = self.run_bundle(gr)
                self.assertFalse(rows_of(verdict)[PIN])
                self.assertIn(expected, diag[PIN])

    def test_each_conjunct_fails_independently(self) -> None:
        """Every mutation changes exactly its own conjunct's (verdict,
        diagnostic) pair; every other conjunct's pair is byte-identical to
        the starting bundle's."""
        self.assertEqual(set(G2_MUTATIONS), set(REQUIRED))
        base = self.root(); g2_bundle(base)
        _, base_verdict, base_diag = self.run_bundle(base)
        base_rows = rows_of(base_verdict)
        for check_id, mutations in G2_MUTATIONS.items():
            for index, mutate in enumerate(mutations):
                with self.subTest(check=check_id, mutation=index):
                    gr = self.root(); g2_bundle(gr)
                    mutate(gr)
                    gr.rebind()
                    code, verdict, diag = self.run_bundle(gr)
                    self.assertEqual(code, 1); self.assertFalse(verdict["passed"])
                    rows = rows_of(verdict)
                    self.assertFalse(rows[check_id], diag.get(check_id))
                    self.assertNotEqual(diag.get(check_id), base_diag.get(check_id), "the mutation must change the reason")
                    for other in REQUIRED:
                        if other == check_id:
                            continue
                        self.assertEqual(rows[other], base_rows[other], f"{other} changed under a {check_id} mutation: {diag.get(other)}")
                        self.assertEqual(diag.get(other), base_diag.get(other), f"{other} changed under a {check_id} mutation")

    # -- B1: tree reads are pin-bound ----------------------------------------

    def test_tree_bound_conjuncts_refuse_an_uncommitted_edit(self) -> None:
        gr = self.root(); g2_bundle(gr)
        gr.tree_write(BASELINE, gr.tree_text(BASELINE).replace("selection_is_representative = true",
                                                               "selection_is_representative = false"), commit=False)
        gr.rebind()
        code, verdict, diag = self.run_bundle(gr)
        rows = rows_of(verdict)
        for check_id in (PIN, LEDGER, SUITE):
            self.assertFalse(rows[check_id], check_id)
            self.assertIn("not the blob at the pin", diag[check_id])
        self.assertFalse(rows[CENSUS])
        self.assertIn("no independent producer", diag[CENSUS])

    def test_tree_bound_conjuncts_refuse_a_symlink(self) -> None:
        gr = self.root(); g2_bundle(gr)
        forged = gr.root / "evidence" / "forged-baseline.toml"
        forged.write_text(gr.tree_text(BASELINE).replace("selection_is_representative = true",
                                                         "selection_is_representative = false"), encoding="utf-8")
        (gr.root / BASELINE).unlink()
        os.symlink(os.path.relpath(forged, (gr.root / BASELINE).parent), gr.root / BASELINE)
        gr.rebind()
        code, verdict, diag = self.run_bundle(gr)
        self.assertFalse(rows_of(verdict)[PIN])
        self.assertIn("symlink", diag[PIN])
        # Bound at the copy's own path while the tracked path is that symlink: still the symlink.
        gr.artifacts[PIN] = {"path": "evidence/forged-baseline.toml", "sha256": sha256_bytes(forged.read_bytes())}
        code, verdict, diag = self.run_bundle(gr)
        self.assertFalse(rows_of(verdict)[PIN])
        self.assertIn("symlink", diag[PIN])
        # A copy bound at its own path while the tracked ledger is intact: a copy is not the pin.
        gr3 = self.root(); g2_bundle(gr3)
        for check_id, relative in ((PIN, BASELINE), (LEDGER, EXCEPTIONS)):
            gr3.write(check_id, gr3.tree_text(relative).encode("utf-8"), Path(relative).name)
        code, verdict, diag = self.run_bundle(gr3)
        for check_id in (PIN, LEDGER):
            self.assertFalse(rows_of(verdict)[check_id])
            self.assertIn("a copy is not the pin", diag[check_id])
        # A symlinked submodule directory is refused before any of it is read.
        gr2 = self.root(); g2_bundle(gr2)
        shutil.move(str(gr2.sub), str(gr2.root / "build-fake-clean"))
        os.symlink("../build-fake-clean", gr2.sub)
        code, verdict, diag = self.run_bundle(gr2)
        self.assertFalse(rows_of(verdict)[LEDGER])
        self.assertIn("symlink", diag[LEDGER])

    def test_unmaterialized_clean_submodule_reads_red_by_name(self) -> None:
        # (a) an uninitialized directory HOLDING files — the worktree's own shape, and forgery shape A/B.
        gr = self.root(); g2_bundle(gr)
        (gr.sub / ".git").unlink()
        code, verdict, diag = self.run_bundle(gr)
        rows = rows_of(verdict)
        for check_id in (PIN, OLEAN, SUITE, LEDGER):
            self.assertFalse(rows[check_id], check_id)
            self.assertIn("has no .git", diag[check_id])
            self.assertIn("materialize the clean submodule", diag[check_id])
        self.assertFalse(rows[CENSUS])
        self.assertIn("no independent producer", diag[CENSUS])
        # (b) an empty directory.
        gr = self.root(); g2_bundle(gr)
        shutil.rmtree(gr.sub); gr.sub.mkdir()
        code, verdict, diag = self.run_bundle(gr)
        self.assertIn("has no .git", diag[OLEAN])
        self.assertIn("pinned_upstream_lean_revision", diag)
        # (c) the directory removed.
        gr = self.root(); g2_bundle(gr)
        shutil.rmtree(gr.sub)
        code, verdict, diag = self.run_bundle(gr)
        self.assertIn("has no .git", diag[OLEAN])

    def test_submodule_at_another_commit_or_files_in_place_of_the_gitlink_are_not_the_pin(self) -> None:
        # The submodule moved on but the superproject still pins the old commit.
        gr = self.root(); g2_bundle(gr)
        (gr.sub / "tests/upstream-lean/baseline.toml").write_text(baseline_toml(representative=False), encoding="utf-8")
        git(gr.sub, "add", "-A"); git(gr.sub, "commit", "-q", "-m", "moved on")
        gr.rebind()
        code, verdict, diag = self.run_bundle(gr)
        self.assertFalse(rows_of(verdict)[PIN])
        self.assertIn("only the pin is the pin", diag[PIN])
        # Files committed in place of the gitlink.
        gr = self.root(gitlink=False); g2_bundle(gr)
        code, verdict, diag = self.run_bundle(gr)
        self.assertFalse(rows_of(verdict)[LEDGER])
        self.assertIn("not a submodule gitlink", diag[LEDGER])
        # A root that is not a git worktree at all.
        gr = self.root(); g2_bundle(gr)
        shutil.rmtree(gr.root / ".git")
        code, verdict, diag = self.run_bundle(gr)
        self.assertFalse(rows_of(verdict)[LEDGER])
        self.assertIn("not the top level of a git worktree", diag[LEDGER])
        self.assertFalse(rows_of(verdict)[CENSUS])

    # -- B3 / B4 / B5 ---------------------------------------------------------

    def test_unseeded_corpus_refuses_a_seeded_looking_run(self) -> None:
        gr = self.root(); g2_bundle(gr)
        gr.tree_write(CORPUS, corpus_toml(()))
        gr.rebind()
        code, verdict, diag = self.run_bundle(gr)
        self.assertFalse(rows_of(verdict)[SUITE])
        self.assertIn("corpus.toml pins 0 probes but the run carries 3", diag[SUITE])
        self.assertIn("--seed-from-corpus-dir", diag[SUITE])

    def test_active_ledger_expiry_uses_system_utc_not_authored_as_of(self) -> None:
        for days_from_today in (-1, 0):
            with self.subTest(days_from_today=days_from_today):
                gr = self.root(); g2_bundle(gr)
                expiry = (FIXTURE_TODAY + timedelta(days=days_from_today)).isoformat()
                gr.tree_write(EXCEPTIONS, 'schema_version = "0.1.0"\n' + ledger_row(
                    expires_on=expiry, as_of="2000-01-01",
                ))
                gr.rebind()
                code, verdict, diag = self.run_bundle(gr)
                self.assertEqual(code, 1)
                self.assertFalse(rows_of(verdict)[LEDGER])
                self.assertIn(f"expires_on {expiry} has lapsed", diag[LEDGER])
                self.assertIn("system UTC date", diag[LEDGER])

    def test_active_ledger_refuses_future_review_dates(self) -> None:
        for reviewed, expiry in (
            ((FIXTURE_TODAY + timedelta(days=1)).isoformat(),
             (FIXTURE_TODAY + timedelta(days=2)).isoformat()),
            ("9999-01-01", "9999-12-31"),
        ):
            with self.subTest(reviewed_on=reviewed):
                gr = self.root(); g2_bundle(gr)
                gr.tree_write(EXCEPTIONS, 'schema_version = "0.1.0"\n' + ledger_row(
                    reviewed_on=reviewed, expires_on=expiry, as_of=reviewed,
                ))
                gr.rebind()
                code, verdict, diag = self.run_bundle(gr)
                self.assertEqual(code, 1)
                self.assertFalse(rows_of(verdict)[LEDGER])
                self.assertIn(f"reviewed_on {reviewed} is after system UTC date", diag[LEDGER])
                self.assertIn("future review cannot authorize a skip", diag[LEDGER])

    def test_active_ledger_uses_one_as_of_across_midnight(self) -> None:
        gr = self.root(); g2_bundle(gr)
        reviewed = FIXTURE_TODAY.isoformat()
        expiry = (FIXTURE_TODAY + timedelta(days=1)).isoformat()
        gr.tree_write(EXCEPTIONS, 'schema_version = "0.1.0"\n' + ledger_row(
            id="upstream-lean.exc.first", probe_id=PROBES[0],
            reviewed_on=reviewed, expires_on=expiry,
        ) + ledger_row(
            id="upstream-lean.exc.second", probe_id=PROBES[1],
            reviewed_on=reviewed, expires_on=expiry,
        ))
        checker = load_checker_module()
        cx = checker.Context(
            gr.root, gr.policy, sha256_bytes(gr.policy.read_bytes()),
            gr.corpus_manifest, sha256_bytes(gr.corpus_manifest.read_bytes()),
            "run-1", SOURCE_REVISION,
        )
        before_midnight = datetime.combine(FIXTURE_TODAY, time(23, 59, 59), tzinfo=timezone.utc)
        with mock.patch.object(checker, "datetime") as clock:
            clock.now.side_effect = (before_midnight, before_midnight + timedelta(seconds=1))
            checker.verify_non_applicable_lean_harness_rows_only(gr.root / EXCEPTIONS, cx)
            clock.now.assert_called_once_with(timezone.utc)

    def test_ledger_refuses_impossible_calendar_dates(self) -> None:
        for changes, field in (
            ({"expires_on": "2026-99-99"}, "expires_on"),
            ({"reviewed_on": "2026-02-30", "status": "resolved"}, "reviewed_on"),
        ):
            with self.subTest(field=field):
                gr = self.root(); g2_bundle(gr)
                gr.tree_write(EXCEPTIONS, 'schema_version = "0.1.0"\n' + ledger_row(**changes))
                gr.rebind()
                code, verdict, diag = self.run_bundle(gr)
                self.assertEqual(code, 1)
                self.assertFalse(rows_of(verdict)[LEDGER])
                self.assertIn(f"{field} {changes[field]!r} is not a real calendar date", diag[LEDGER])

    def test_active_ledger_refuses_when_system_clock_unavailable(self) -> None:
        gr = self.root(); g2_bundle(gr)
        checker = load_checker_module()
        cx = checker.Context(
            gr.root, gr.policy, sha256_bytes(gr.policy.read_bytes()),
            gr.corpus_manifest, sha256_bytes(gr.corpus_manifest.read_bytes()),
            "run-1", SOURCE_REVISION,
        )
        with mock.patch.object(checker, "datetime") as clock:
            clock.now.side_effect = OSError("clock unavailable")
            with self.assertRaisesRegex(checker.Refusal, "cannot be accepted without a system UTC date"):
                checker.verify_non_applicable_lean_harness_rows_only(gr.root / EXCEPTIONS, cx)

    def test_no_v1_envelope_can_pass(self) -> None:
        gr = self.root(); g2_bundle(gr)
        code, verdict, diag = self.run_bundle(gr)
        self.assertIn("the instrument's own refusal", diag[BUILD])
        for mutate, needle in (
            (json_mut(BUILD, setting("native_codegen", {"status": "executable-produced", "executable_sha256": ZERO, "target": "x"})),
             "not a trust.lean.ir-library/v1 envelope"),
            (json_mut(BUILD, setting("limitations", [])), "limitations is empty"),
            (json_mut(BUILD, setting("limitations", ["only this"])), "do not end with the instrument disclosure"),
            (json_mut(BUILD, _rewritten_source), "not built from this tree"),
        ):
            gr = self.root(); g2_bundle(gr); mutate(gr)
            code, verdict, diag = self.run_bundle(gr)
            self.assertFalse(rows_of(verdict)[BUILD])
            self.assertIn(needle, diag[BUILD])

    def test_census_diagnostic_authority_is_refused_by_name(self) -> None:
        gr = self.root(); g2_bundle(gr)
        json_mut(CENSUS, lambda d: (d.__setitem__("authority", "diagnostic-only-no-import-admission"),
                                    d["kernel_roster"].__setitem__("authority", "diagnostic-only"), d)[2])(gr)
        code, verdict, diag = self.run_bundle(gr)
        self.assertFalse(rows_of(verdict)[CENSUS])
        self.assertIn("diagnostic", diag[CENSUS]); self.assertIn("post-lowering-inventory", diag[CENSUS])

    def test_the_diagnostic_olean_census_cannot_stand_in_for_admission(self) -> None:
        gr = self.root(); g2_bundle(gr)
        gr.write(OLEAN, {
            "schema": "trust.lean.olean-closure-observation/v1",
            "authority": "diagnostic-only-no-import-admission",
            "modules": [{"name": "Init", "status": "one-observed-candidate", "candidates": []}],
            "issues": [], "denominator_status": "denominator_unverified"})
        code, verdict, diag = self.run_bundle(gr)
        self.assertFalse(rows_of(verdict)[OLEAN])
        self.assertIn("diagnostic-only-no-import-admission", diag[OLEAN])

    def test_pin_disagreement_names_both_pins_and_a_nightly_reads_as_disagreement(self) -> None:
        # The live defect (2026-09-16): baseline v4.27.0 against lean-toolchain v4.30.0-rc2.
        gr = self.root(); g2_bundle(gr)
        gr.tree_write(TOOLCHAIN_PIN, "leanprover/lean4:v4.30.0-rc2\n")
        gr.rebind()
        code, verdict, diag = self.run_bundle(gr)
        self.assertFalse(rows_of(verdict)[PIN])
        self.assertIn("v4.30.0-rc2", diag[PIN]); self.assertIn("v4.27.0", diag[PIN]); self.assertIn("two pins", diag[PIN])
        # Independent defects accumulate: both are named at once.
        gr.tree_write(BASELINE, baseline_toml(representative=False))
        gr.rebind()
        code, verdict, diag = self.run_bundle(gr)
        self.assertIn("selection_is_representative", diag[PIN]); self.assertIn("v4.30.0-rc2", diag[PIN])
        # A nightly pin is a disagreement, not a malformed pin.
        gr = self.root(); g2_bundle(gr)
        gr.tree_write(TOOLCHAIN_PIN, "leanprover/lean4:nightly-2026-09-01\n")
        gr.rebind()
        code, verdict, diag = self.run_bundle(gr)
        self.assertIn("nightly-2026-09-01", diag[PIN]); self.assertIn("two pins", diag[PIN])
        self.assertNotIn("must pin", diag[PIN])

    # -- protocol ---------------------------------------------------------------

    def test_evidence_binding_is_fail_closed(self) -> None:
        # Digest mismatch — on a tree-bound and on an evidence-bound artifact.
        for check_id in (LEDGER, SURFACE):
            gr = self.root(); g2_bundle(gr)
            gr.artifacts[check_id]["sha256"] = "e" * 64
            code, verdict, err = gr.run(gr.bundle())
            self.assertEqual(code, 1); self.assertIn("hash mismatch", err)
            self.assertEqual([r["artifacts"] for r in verdict["checks"] if r["id"] == check_id], [[]])
        # Absolute path / root escape.
        for bad in [str(gr.root / EXCEPTIONS), "../outside.toml"]:
            gr2 = self.root(); g2_bundle(gr2)
            gr2.artifacts[LEDGER]["path"] = bad
            code, verdict, err = gr2.run(gr2.bundle())
            self.assertEqual(code, 1, bad); self.assertFalse(verdict["passed"])
        # A hand-authored `passed` in the bundle is a header violation, not a verdict.
        gr3 = self.root(); g2_bundle(gr3)
        code, verdict, err = gr3.run(gr3.bundle(passed=True))
        self.assertEqual(code, 1); self.assertIn("header", err)
        # Unknown check ids are refused.
        gr4 = self.root(); g2_bundle(gr4)
        gr4.artifacts["made_up"] = dict(gr4.artifacts[SURFACE])
        code, verdict, err = gr4.run(gr4.bundle())
        self.assertEqual(code, 1); self.assertIn("unknown check ids", err)
        # G8-only inputs are a protocol violation for G2.
        gr5 = self.root(); g2_bundle(gr5)
        code, verdict, err = gr5.run(gr5.bundle(), receipt=True)
        self.assertEqual(code, 1); self.assertIn("G8-only", err)
        # The owner-pinned surface comes from the policy: a policy with no semantics contract refuses parity.
        gr6 = self.root(); g2_bundle(gr6)
        gr6.policy.write_text(json.dumps({"schema": "trust.two-language.authority-policy/v2"}), encoding="utf-8")
        code, verdict, diag = self.run_bundle(gr6)
        self.assertFalse(rows_of(verdict)[PARITY])
        self.assertIn("no semantics contract", diag[PARITY])

    def test_empty_bundle_names_every_missing_conjunct(self) -> None:
        gr = self.root()
        code, verdict, err = gr.run(gr.bundle())
        self.assertEqual(code, 1); self.assertFalse(verdict["passed"])
        for check_id in REQUIRED:
            self.assertIn(f"{check_id}: no artifact bound", err)

    def test_real_ledgers_are_within_the_stated_toml_subset(self) -> None:
        """Read the pinned Clean blobs even from a sparse superproject worktree.
        The live seeded corpus must remain a measured refusal, not a parse gap."""
        # A linked worktree keeps its submodule objects under its OWN git dir
        # (`--git-path modules/<name>`); the common dir's store is the main
        # checkout's and may lag the pin. A sparse worktree has only the common
        # store. Objects are content-addressed, so read the first store that holds
        # the pinned commit, own store first; scripts/check_completion_gate_tests.sh
        # resolves the same way before it runs this suite.
        def absolute(raw: str) -> Path:
            path = Path(raw.strip())
            return path if path.is_absolute() else ROOT / path

        stores = [
            store for store in (
                absolute(git(ROOT, "rev-parse", "--git-path", f"modules/{CLEAN}")),
                absolute(git(ROOT, "rev-parse", "--git-common-dir")) / "modules" / CLEAN,
            )
            if store.is_dir()
        ]
        if not stores:
            self.skipTest("pinned Clean submodule objects are not initialized")
        pin = git(ROOT, "ls-tree", "HEAD", CLEAN).split()[2]
        clean_git_dir = next(
            (
                store for store in stores
                if subprocess.run(
                    ["git", f"--git-dir={store}", "cat-file", "-e", f"{pin}^{{commit}}"],
                    cwd=ROOT, check=False, capture_output=True,
                ).returncode == 0
            ),
            stores[0],
        )

        def pinned_bytes(relative: str) -> bytes:
            inner = relative.removeprefix(CLEAN + "/")
            process = subprocess.run(
                ["git", f"--git-dir={clean_git_dir}", "show", f"{pin}:{inner}"],
                cwd=ROOT, check=False, capture_output=True,
            )
            if process.returncode != 0:
                raise RuntimeError(f"cannot read pinned Clean blob {inner}: {process.stderr.decode(errors='replace')}")
            return process.stdout

        gr = self.root(); g2_bundle(gr)
        shutil.rmtree(gr.sub / "tests/lean4_compat/lean4_tests")
        for relative in (TOOLCHAIN_PIN, BASELINE, EXCEPTIONS, CORPUS, MANIFEST):
            path = gr.root / relative
            path.write_bytes(pinned_bytes(relative))
        corpus_files = git(
            ROOT, f"--git-dir={clean_git_dir}", "ls-tree", "-r", "--name-only", pin,
            "--", "tests/lean4_compat/lean4_tests",
        ).splitlines()
        for inner in corpus_files:
            path = gr.root / CLEAN / inner
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(pinned_bytes(f"{CLEAN}/{inner}"))
        gr.commit_tree()
        gr.rebind()
        probes = load_checker_module().read_toml_subset(gr.tree_text(CORPUS), CORPUS)["probes"]
        self.assertEqual(len(probes), 56)
        # The split is the pinned Clean's corpus.toml. Clean bb54c0a8b (Trust
        # ledger 2026-10-07 (s)) re-pinned 1569, 1657 and 2077 lowers -> rejected,
        # read against real Lean; Clean d3a9d47e9 (in the D1b train's Clean pin
        # 612d29f2c, Trust ledger 2026-10-13) re-pinned 2077 rejected -> lowers
        # once a universe-typed constructor field lowered as an erased type, and
        # real Lean v4.30.0-rc2 accepts the file. A later clean move that changes
        # it updates this.
        self.assertEqual(sum(probe["expected"] == "lowers" for probe in probes), 10)
        self.assertEqual(sum(probe["expected"] == "rejected" for probe in probes), 46)
        gr.write(SUITE, suite_run([
            {"probe_id": probe["id"], "file": probe["file"], "decl": probe["decl"],
             "expected": probe["expected"], "observed": probe["expected"], "detail": ""}
            for probe in probes
        ]), "upstream-lean-run.json")
        code, verdict, diag = self.run_bundle(gr)
        for message in diag.values():
            self.assertNotIn("outside the ledger TOML subset", message)
        rows = rows_of(verdict)
        self.assertTrue(rows[LEDGER], diag.get(LEDGER))
        self.assertFalse(rows[SUITE]); self.assertIn("recording a non-lowering as normal", diag[SUITE])
        # Since Clean's MANIFEST, baseline and lean-toolchain agree (v4.30.0-rc2,
        # 3dc1a088), the "two pins" refusal no longer fires on the real ledgers;
        # the row stays refused on the baseline-vs-owner-admission revision split.
        self.assertFalse(rows[PIN])
        self.assertIn("disagrees with the owner admission and receipt corpus revision", diag[PIN])


# ── self-protection and hostile-input regressions (adversarial review, 2026-09-27) ──


LINE_SEPARATOR = "\u2028"


def hidden_waiver_ledger() -> str:
    """An ACTIVE expected_fail waiver as TOML reads it, which str.splitlines
    would show as an environmental_skip row: U+2028 inside a comment hides a
    benign ``kind`` line, and a comment-hidden ``[[junk]]`` header moves the
    real ``kind`` line into a table the ledger reader ignores."""
    lines = ledger_row(id="upstream-lean.exc.waiver", probe_id=PROBES[0], kind="expected_fail").splitlines()
    real_kind = next(line for line in lines if line.startswith("kind"))
    body = [
        line + f' # {LINE_SEPARATOR}kind = "environmental_skip"' if line.startswith("observed") else line
        for line in lines if not line.startswith("kind")
    ]
    body += [f"# {LINE_SEPARATOR}[[junk]]", real_kind]
    return 'schema_version = "0.1.0"\n' + "\n".join(body) + "\n"


def hidden_probe_corpus() -> str:
    """corpus.toml as TOML reads it (the three pinned probes), plus a fourth
    probe hidden in comments that only a str.splitlines reader sees."""
    hidden = ("[[probes]]", 'id = "upstream-lean.ghost.decl"', 'file = "1007.lean"', 'decl = "decl"', 'expected = "lowers"')
    return corpus_toml() + "".join(f"# {LINE_SEPARATOR}{line}\n" for line in hidden)


class SelfProtectionTests(GateTestCase):
    """Direct runs of the checker (no runner in front of it) against hostile
    repository state and hostile evidence.  Each case must yield one JSON
    verdict with the affected row refused BY NAME, and no candidate-chosen
    program may run."""

    def run_bundle(self, gr: GateRoot, **kwargs) -> tuple[int, dict, dict[str, str]]:
        code, verdict, err = gr.run(gr.bundle(), **kwargs)
        self.assertNotIn("Traceback", err)
        self.assert_verdict_shape(verdict)
        return code, verdict, diagnostics(err)

    def assert_refused(self, gr: GateRoot, check_id: str, *needles: str, **kwargs) -> dict[str, str]:
        code, verdict, diag = self.run_bundle(gr, **kwargs)
        self.assertEqual(code, 1)
        self.assertFalse(rows_of(verdict)[check_id], f"{check_id} passed")
        for needle in needles:
            self.assertRegex(diag.get(check_id, ""), needle)
        return diag

    # -- G2-F1: the TOML subset sees exactly the lines TOML sees ------------------

    def test_toml_subset_ends_lines_only_at_lf_or_crlf(self) -> None:
        checker = load_checker_module()
        for char in ("\x0b", "\x0c", "\x1c", "\x1d", "\x1e", "\x85", "\u2028", "\u2029", "\r", "\x00", "\x7f"):
            with self.subTest(char=hex(ord(char))):
                with self.assertRaisesRegex(checker.Refusal, r"ledger line 1: control character or non-TOML line break"):
                    checker.read_toml_subset(f"a = 1 # x{char}b = 2\n", "ledger")
        # CRLF is a TOML line ending and still reads.
        self.assertEqual(
            checker.read_toml_subset('a = 1\r\n[t]\r\nb = "x" # note\r\n', "ledger"),
            {"a": 1, "t": {"b": "x"}},
        )

    def test_a_waiver_hidden_by_a_unicode_line_break_is_refused(self) -> None:
        gr = self.root(); g2_bundle(gr)
        gr.tree_write(EXCEPTIONS, hidden_waiver_ledger())
        gr.rebind()
        self.assert_refused(gr, LEDGER, r"exceptions\.toml line \d+: control character or non-TOML line break U\+2028")

    def test_a_ghost_probe_hidden_in_corpus_comments_cannot_carry_a_waiver(self) -> None:
        gr = self.root(); g2_bundle(gr)
        gr.tree_write(CORPUS, hidden_probe_corpus(), commit=False)
        gr.tree_write(EXCEPTIONS, exceptions_toml(ledger_row(id="upstream-lean.exc.ghost", probe_id="upstream-lean.ghost.decl")))
        gr.rebind()
        self.assert_refused(gr, LEDGER, r"corpus\.toml line \d+: control character or non-TOML line break U\+2028")

    def test_unknown_top_level_ledger_and_corpus_tables_are_refused(self) -> None:
        for relative, text, needle in (
            (EXCEPTIONS, exceptions_toml() + '\n[notes]\nkind = "expected_fail"\n', r"exceptions\.toml carries unknown top-level keys or tables \['notes'\]"),
            (CORPUS, corpus_toml() + '\n[notes]\nid = "x"\n', r"corpus\.toml carries unknown top-level keys or tables \['notes'\]"),
        ):
            with self.subTest(relative=relative):
                gr = self.root(); g2_bundle(gr)
                gr.tree_write(relative, text)
                gr.rebind()
                self.assert_refused(gr, LEDGER, needle)

    # -- G2-F2 / F3 / F4: Git answers for the committed tree and runs no candidate program --

    def _waiver_at_the_pin_and_dropped_on_disk(self, gr: GateRoot) -> tuple[str, str]:
        """Commit a ledger carrying an expected_fail waiver (the pin reads red),
        then drop the waiver on disk without committing.  Returns (pinned, edited)."""
        good = exceptions_toml()
        bad = good + ledger_row(id="upstream-lean.exc.waiver", probe_id=PROBES[0], kind="expected_fail")
        gr.tree_write(EXCEPTIONS, bad)
        gr.rebind()
        self.assert_refused(gr, LEDGER, "is kind 'expected_fail'")
        return bad, good

    def test_replacement_refs_are_refused_before_any_tree_read(self) -> None:
        # In the clean submodule: a forged commit replaces the pin.
        gr = self.root(); g2_bundle(gr)
        _, good = self._waiver_at_the_pin_and_dropped_on_disk(gr)
        pin = git(gr.root, "ls-tree", "HEAD", "--", CLEAN).split()[2]
        gr.tree_write(EXCEPTIONS, good, commit=False)
        git(gr.sub, "add", "-A")
        tree = git(gr.sub, "write-tree").strip()
        parent = git(gr.sub, "rev-parse", pin + "^").strip()
        forged = git(gr.sub, "commit-tree", tree, "-p", parent, "-m", "forged").strip()
        git(gr.sub, "replace", pin, forged)
        gr.rebind()
        self.assert_refused(gr, LEDGER, rf"{CLEAN} carries refs/replace/\* object substitutions \(refs/replace/{pin}\)")
        # In the superproject: a forged commit replaces HEAD.
        gr = self.root(); g2_bundle(gr)
        head = git(gr.root, "rev-parse", "HEAD").strip()
        tree = git(gr.root, "rev-parse", "HEAD^{tree}").strip()
        forged = git(gr.root, "commit-tree", tree, "-m", "forged").strip()
        git(gr.root, "replace", head, forged)
        self.assert_refused(gr, LEDGER, r"the superproject carries refs/replace/\* object substitutions")
        self.assert_refused(gr, BUILD, r"the superproject carries refs/replace/\*")

    def test_an_fsmonitor_hook_never_runs(self) -> None:
        for repo_of in (lambda gr: gr.sub, lambda gr: gr.root):
            gr = self.root(); g2_bundle(gr)
            repo = repo_of(gr)
            marker = gr.root.parent / "FSMONITOR_RAN"
            hook = gr.root.parent / "fsmonitor-hook.sh"
            hook.write_text(f"#!/bin/sh\necho ran >> '{marker}'\nexit 1\n", encoding="utf-8")
            hook.chmod(0o755)
            git(repo, "config", "core.fsmonitor", str(hook))
            with self.subTest(repo=repo.name):
                self.assert_refused(gr, LEDGER, r"configuration starts a program .*: core\.fsmonitor")
                self.assertFalse(marker.exists(), "the checker ran the candidate's fsmonitor hook")

    def test_a_filter_driver_neither_runs_nor_binds_edited_bytes(self) -> None:
        gr = self.root(); g2_bundle(gr)
        pinned, good = self._waiver_at_the_pin_and_dropped_on_disk(gr)
        pinned_copy = gr.root.parent / "pinned-ledger.toml"
        pinned_copy.write_text(pinned, encoding="utf-8")
        marker = gr.root.parent / "FILTER_RAN"
        driver = gr.root.parent / "clean-filter.sh"
        driver.write_text(f"#!/bin/sh\necho ran >> '{marker}'\ncat >/dev/null\ncat '{pinned_copy}'\n", encoding="utf-8")
        driver.chmod(0o755)
        for repo, pattern in ((gr.sub, "tests/upstream-lean/exceptions.toml"), (gr.root, "exceptions.toml")):
            git(repo, "config", "filter.pin.clean", str(driver))
            info = Path(git(repo, "rev-parse", "--absolute-git-dir").strip()) / "info"
            info.mkdir(exist_ok=True)
            (info / "attributes").write_text(f"{pattern} filter=pin\n", encoding="utf-8")
        # Same size as the pinned bytes, so status must re-hash (and filter) it.
        padded = good + "#" * (len(pinned.encode()) - len(good.encode()) - 1) + "\n"
        gr.tree_write(EXCEPTIONS, padded, commit=False)
        gr.rebind()
        self.assert_refused(gr, LEDGER, r"the superproject carries a repository-local info/attributes")
        self.assertFalse(marker.exists(), "the checker ran the candidate's filter driver")
        # Without info/attributes, the driver's configuration alone is refused by name.
        for repo in (gr.sub, gr.root):
            (Path(git(repo, "rev-parse", "--absolute-git-dir").strip()) / "info" / "attributes").unlink()
        self.assert_refused(gr, LEDGER, r"configuration starts a program .*: filter\.pin\.clean")
        self.assertFalse(marker.exists(), "the checker ran the candidate's filter driver")

    def test_consulted_files_bind_raw_bytes_not_converted_ones(self) -> None:
        """Committed attributes alone (no configuration, no program): ``ident``
        makes status and a filtering hash-object collapse ``$Id: ...$`` back
        to ``$Id$``, so edited raw bytes would bind as the pinned blob."""
        gr = self.root(); g2_bundle(gr)
        gr.tree_write(EXCEPTIONS, exceptions_toml() + "# $Id$\n", commit=False)
        (gr.sub / ".gitattributes").write_text("tests/upstream-lean/exceptions.toml ident\n", encoding="utf-8")
        (gr.root / ".gitattributes").write_text("exceptions.toml ident\n", encoding="utf-8")
        gr.commit_tree()
        # A real checkout smudges `$Id$` to `$Id: <blob> $`; then edit the expansion
        # in place at the same size, so status re-reads it through the conversion.
        inner = EXCEPTIONS[len(CLEAN) + 1:]
        (gr.root / EXCEPTIONS).unlink()
        git(gr.sub, "checkout", "--", inner)
        smudged = gr.tree_text(EXCEPTIONS)
        self.assertRegex(smudged, r"\$Id: [0-9a-f]{40} \$")
        gr.tree_write(EXCEPTIONS, re.sub(r"\$Id: [0-9a-f]{40} \$", "$Id: " + "e" * 40 + " $", smudged), commit=False)
        self.assertEqual(git(gr.sub, "status", "--porcelain"), "", "the conversion hides the edit from status")
        gr.rebind()
        self.assert_refused(gr, LEDGER, r"exceptions\.toml on disk \(blob [0-9a-f]{12}\) is not the blob at the clean pin")

    def test_a_tree_path_with_a_line_break_is_not_bound_to_its_twin(self) -> None:
        """``hash-object --stdin-paths`` strips a trailing CR, so ``Twin\\r``
        would be hashed from the committed ``Twin`` while its own edited
        bytes are what the checker reads."""
        gr = self.root(); g2_bundle(gr)
        (gr.root / "Twin").write_text("pinned\n", encoding="utf-8")
        (gr.root / "Twin\r").write_text("pinned\n", encoding="utf-8")
        git(gr.root, "add", "-A"); git(gr.root, "commit", "-q", "-m", "twins")
        (gr.root / "Twin\r").write_text("EDITED, never committed\n", encoding="utf-8")
        checker = load_checker_module()
        cx = checker.Context(
            gr.root, gr.policy, sha256_bytes(gr.policy.read_bytes()),
            gr.corpus_manifest, sha256_bytes(gr.corpus_manifest.read_bytes()),
            "run-1", SOURCE_REVISION,
        )
        with self.assertRaisesRegex(checker.Refusal, r"holds a control character"):
            cx.tree_files(["Twin\r"])
        self.assertEqual(cx.consulted, {})

    # -- G2-C1..C7: hostile evidence yields one verdict with the row refused by name --

    def test_a_lone_surrogate_source_text_is_refused_by_name(self) -> None:
        gr = self.root(); g2_bundle(gr)
        envelope = ir_library_envelope()
        envelope["sources"][0]["source"] = "\ud800"
        gr.write(BUILD, envelope, "fixture.trust-ir.json")
        self.assert_refused(gr, BUILD, r"source 'Fixture\.lean' text is not encodable UTF-8")

    def test_an_unhashable_kernel_kind_is_refused_by_name(self) -> None:
        gr = self.root(); g2_bundle(gr)
        json_mut(CENSUS, _row(0, kernel_classification={"kind": ["proof-only"]}))(gr)
        self.assert_refused(gr, CENSUS, r"kernel classification is \['proof-only'\]")

    def test_an_overlong_path_component_is_refused_by_name(self) -> None:
        long_name = "x" * 300 + ".lean"
        gr = self.root(); g2_bundle(gr)
        json_mut(CENSUS, setting("requested_files", [long_name]))(gr)
        json_mut(BUILD, lambda d: (d["sources"][0].__setitem__("path", long_name), d)[1])(gr)
        self.assert_refused(gr, CENSUS, r"cannot inspect it: File name too long")
        self.assert_refused(gr, BUILD, r"cannot inspect it: File name too long")

    def test_a_symlink_loop_is_refused_by_name(self) -> None:
        gr = self.root(); g2_bundle(gr)
        os.symlink("loop", gr.root / "evidence" / "loop")
        gr.artifacts[SURFACE] = {"path": "evidence/loop", "sha256": ZERO}
        policy = json.loads(gr.policy.read_text(encoding="utf-8"))
        policy["contracts"]["semantics"] = {"path": "evidence/loop", "sha256": ZERO}
        gr.policy.write_text(json.dumps(policy), encoding="utf-8")
        # Python 3.9 raises RuntimeError from resolve(); later interpreters
        # resolve the loop lexically and then find no file.
        self.assert_refused(gr, SURFACE, r"artifact path cannot be resolved|artifact file does not exist")
        self.assert_refused(gr, PARITY, r"semantics contract path cannot be resolved|semantics contract file does not exist")

    def test_an_unreadable_artifact_is_refused_by_name(self) -> None:
        gr = self.root(); g2_bundle(gr)
        path = gr.root / gr.artifacts[SURFACE]["path"]
        path.chmod(0)
        self.addCleanup(path.chmod, 0o644)
        self.assert_refused(gr, SURFACE, r"artifact cannot be read: Permission denied")

    def test_an_unlistable_corpus_directory_is_refused_by_name(self) -> None:
        # (a) the tracked corpus directory; (b) an ignored, untracked one the baseline names.
        for ignored in (False, True):
            with self.subTest(ignored=ignored):
                gr = self.root(); g2_bundle(gr)
                corpus_rel = CORPUS_DIR
                if ignored:
                    (gr.sub / ".gitignore").write_text("hidden/\n", encoding="utf-8")
                    gr.tree_write(BASELINE, gr.tree_text(BASELINE).replace(
                        'corpus_path = "tests/lean4_compat/lean4_tests"', 'corpus_path = "hidden"'))
                    gr.rebind()
                    corpus_rel = f"{CLEAN}/hidden"
                    (gr.root / corpus_rel).mkdir()
                directory = gr.root / corpus_rel
                directory.chmod(0)
                self.addCleanup(directory.chmod, 0o755)
                self.assert_refused(gr, PIN, rf"corpus directory {corpus_rel} cannot be listed: Permission denied")

    def test_a_non_utf8_tree_path_does_not_cost_the_verdict(self) -> None:
        gr = self.root(); g2_bundle(gr)
        _, _, base = self.run_bundle(gr)
        blob = subprocess.run(["git", "hash-object", "-w", "--stdin"], cwd=gr.root, input=b"x",
                              capture_output=True, check=True).stdout.strip()
        subprocess.run(["git", "update-index", "--index-info"], cwd=gr.root,
                       input=b"100644 " + blob + b"\t\xff.lean\n", check=True)
        git(gr.root, "commit", "-q", "-m", "a tree path that is not UTF-8")
        code, verdict, diag = self.run_bundle(gr)
        self.assertTrue(rows_of(verdict)[LEDGER], diag.get(LEDGER))
        self.assertEqual(diag[BUILD], base[BUILD])
        self.assertEqual(diag[CENSUS], base[CENSUS])

    # -- G2-U1: the semantics contract comes from the BOUND policy ----------------

    def test_the_semantics_contract_is_read_from_the_bound_policy(self) -> None:
        gr = self.root(); g2_bundle(gr)
        recorded = sha256_bytes(gr.policy.read_bytes())
        policy = json.loads(gr.policy.read_text(encoding="utf-8"))
        policy["contracts"]["semantics"]["definitions"]["lean_language"]["sha256"] = "9" * 64
        gr.policy.write_text(json.dumps(policy), encoding="utf-8")
        json_mut(PARITY, lambda d: (d["lean_language_definition"].__setitem__("sha256", "9" * 64), d)[1])(gr)
        self.assert_refused(gr, PARITY, r"authority policy hash mismatch: recorded " + recorded, policy_sha256=recorded)

    # -- G2-O1: counts are integers, not bools or floats --------------------------

    def test_bool_and_float_counts_are_refused_by_name(self) -> None:
        def body_ids(doc):
            doc["bodies"][0]["function_id"] = True
            doc["bodies"][1]["function_id"] = 0
            return doc

        def float_file_count(gr: GateRoot) -> None:
            manifest = manifest_json()
            manifest["file_count"] = 3.0
            gr.tree_write(MANIFEST, json.dumps(manifest, indent=1))

        for check_id, mutate, needle in (
            (SUITE, json_mut(SUITE, lambda d: (d["summary"].__setitem__("findings", False), d)[1]), r"summary\.findings must be an integer count, got False"),
            (SUITE, json_mut(SUITE, lambda d: (d["summary"].__setitem__("probes", 3.0), d)[1]), r"summary\.probes must be an integer count, got 3\.0"),
            (SUITE, json_mut(SUITE, lambda d: (d["summary"].__setitem__("executed", 3.0), d)[1]), r"summary\.executed must be an integer count, got 3\.0"),
            (SUITE, json_mut(SUITE, lambda d: (d["summary"].__setitem__("matched_pin", 2.0), d)[1]), r"summary\.matched_pin must be an integer count, got 2\.0"),
            (BUILD, json_mut(BUILD, body_ids), r"body \"wsum\" function_id must be a unique non-negative integer"),
            (CENSUS, json_mut(CENSUS, _row(0, runtime_classification={"trust_ir_body": {"function_id": True, "subject_digest": "sha256:" + sha("s")}})),
             r"trust_ir_body\.function_id must be a non-negative integer"),
            (PIN, float_file_count, r"corpus MANIFEST file_count must be an integer, got 3\.0"),
        ):
            with self.subTest(check=check_id, needle=needle):
                gr = self.root(); g2_bundle(gr)
                mutate(gr)
                gr.rebind()
                self.assert_refused(gr, check_id, needle)

    # -- G2-T1: integers and arrays are TOML's, bounded before int() or recursion --

    HOSTILE_TOML_VALUES = (
        # (value, what the reader must refuse it as)
        ("\u0663", r"value outside the ledger TOML subset"),  # ARABIC-INDIC DIGIT THREE: int() reads 3
        ("03", r"value outside the ledger TOML subset"),  # a leading zero TOML refuses
        ("9" * 5000, r"value outside the ledger TOML subset"),  # int() raises past 4300 digits on 3.11+
        ("9223372036854775808", r"TOML integer outside the 64-bit range"),
        ("[" * 2000 + "1" + "]" * 2000, r"TOML array nesting exceeds 8"),  # RecursionError when unbounded
    )

    def test_toml_integers_and_array_nesting_are_bounded(self) -> None:
        checker = load_checker_module()
        for value, needle in self.HOSTILE_TOML_VALUES:
            with self.subTest(value=value[:24]):
                with self.assertRaisesRegex(checker.Refusal, r"ledger line 2: " + needle):
                    checker.read_toml_subset(f"# note\na = {value}\n", "ledger")
        # The forms the tracked ledgers use, and the i64 edges, still read.
        self.assertEqual(
            checker.read_toml_subset(
                "a = 0\nb = -0\nc = 3\nd = 9223372036854775807\ne = -9223372036854775808\n"
                "f = [[[[[[[[1]]]]]]]]\n",
                "ledger",
            ),
            {"a": 0, "b": 0, "c": 3, "d": 2 ** 63 - 1, "e": -(2 ** 63), "f": [[[[[[[[1]]]]]]]]},
        )

    def test_malformed_toml_arrays_are_refused_not_read_around(self) -> None:
        # The splitter dropped empty elements and ignored an unterminated
        # string, so `[1,,2]` read as [1, 2] and `[,]` as [] -- arrays TOML
        # refuses.  G1's reader refuses both; G2's now does too.
        checker = load_checker_module()
        for value, needle in (
            ("[1,,2]", r"empty TOML array element"),
            ("[,]", r"empty TOML array element"),
            ("[, 1]", r"empty TOML array element"),
            ('["a, b]', r"unterminated TOML array string"),
        ):
            with self.subTest(value=value):
                with self.assertRaisesRegex(checker.Refusal, r"ledger line 1: " + needle):
                    checker.read_toml_subset(f"a = {value}\n", "ledger")
        # A trailing comma is TOML, and an empty array stays empty.
        self.assertEqual(
            checker.read_toml_subset('a = [1, 2,]\nb = []\nc = ["x, y", "z"]\n', "ledger"),
            {"a": [1, 2], "b": [], "c": ["x, y", "z"]},
        )

    def test_a_hostile_baseline_integer_is_refused_by_name(self) -> None:
        for value, needle in self.HOSTILE_TOML_VALUES:
            with self.subTest(value=value[:24]):
                gr = self.root(); g2_bundle(gr)
                text = baseline_toml()
                count = f"file_count = {len(SUITE_FILES)}\n"
                self.assertIn(count, text)
                gr.tree_write(BASELINE, text.replace(count, f"file_count = {value}\n"))
                gr.rebind()
                self.assert_refused(gr, PIN, r"baseline\.toml line \d+: " + needle)


if __name__ == "__main__":
    unittest.main()
