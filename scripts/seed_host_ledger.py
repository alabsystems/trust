#!/usr/bin/env python3
"""Host-local mint records for a shared stage0 release.

These checks bind recorded producer evidence; they do not perform a build or
authenticate a public signature. Only the native mint workflow creates the
receipt after its real DDC, archive comparison, rebuild, and sanity checks.
Foreign archives without that host's completed native receipt are insufficient.
"""

from __future__ import annotations

import hashlib
import importlib.util
import json
import os
import re
import stat
from pathlib import Path

SCHEMA = "trust-seed-host-record-v1"
MAX_PROOF_BYTES = 4 * 1024 * 1024
MAX_HOSTS = 32
MAX_TOTAL_PROOF_BYTES = 64 * 1024 * 1024
COMPONENTS = (
    "targo", "targo-trust", "tippy", "trust-analyzer", "trust-src",
    "trust-std", "trustc", "trustc-dev", "trustfmt",
)
MINT_FIELDS = (
    "pinned_seed_commit", "ddc_seed_relation", "ddc_seed_commit", "ddc_seed_lineage",
    "lineage_disjoint_anchor", "stage2_tree_sha256_pinned_seed",
    "stage2_tree_sha256_ddc_seed", "self_host_proof",
)
HOST = re.compile(r"[A-Za-z0-9_][A-Za-z0-9_.-]{2,127}")
SHA = re.compile(r"[0-9a-f]{64}")
COMMIT = re.compile(r"[0-9a-f]{40,64}")
DATE = re.compile(r"[0-9]{4}-[0-9]{2}-[0-9]{2}")
GENESIS_SCHEMA = "trust-seed-genesis-host-record-v1"
LEGACY_SCHEMA = "trust-seed-legacy-host-record-v1"
# A first Linux seed admitted as a fixed point of an unpinned host chain
# (docs/PLAN.md PKG-S6; the evidence rules are scripts/seed_fixed_point.py).
FIXED_POINT_SCHEMA = "trust-seed-fixed-point-host-record-v1"
# The only stage2 files a build by the pinned seed may fail to reproduce: the
# 43f29371e7 ThinLTO fix is not an ancestor of the pinned commit. Any other
# difference refuses (seed_fixed_point C4).
FIXED_POINT_UNREPRODUCED_ALLOWED = ("bin/targo-trust", "bin/ty")
# THE DOOR. host -> {"commit": the pinned compiler commit, "receipt_sha256": the
# sha256 of the tracked SEED-FIXED-POINT}. Empty: until a reviewed code edit adds
# an entry, every record of the fixed-point kind is refused (rule A1), and
# replacing the cohort or the receipt needs another edit here.
FIXED_POINT_FIRST_HOSTS: dict[str, dict[str, str]] = {}
HOST_SCHEMAS = {SCHEMA, GENESIS_SCHEMA, LEGACY_SCHEMA, FIXED_POINT_SCHEMA}


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def initialization_module():
    path = Path(__file__).with_name("seed_root_initialization.py")
    if "__trust_source_loader__" in globals():
        return __trust_source_loader__.module("trust_seed_root_initialization", path)
    spec = importlib.util.spec_from_file_location("trust_seed_root_initialization", path)
    require(spec is not None and spec.loader is not None, "missing root initialization validator")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


_FIXED_POINT = None


def fixed_point_module():
    """scripts/seed_fixed_point.py, the fixed-point evidence validator, loaded once."""
    global _FIXED_POINT
    if _FIXED_POINT is None:
        path = Path(__file__).with_name("seed_fixed_point.py")
        if "__trust_source_loader__" in globals():
            _FIXED_POINT = __trust_source_loader__.module("trust_seed_fixed_point", path)
        else:
            spec = importlib.util.spec_from_file_location("trust_seed_fixed_point", path)
            require(spec is not None and spec.loader is not None, "missing fixed-point evidence validator")
            module = importlib.util.module_from_spec(spec)
            spec.loader.exec_module(module)
            _FIXED_POINT = module
    return _FIXED_POINT


def proof_paths(host: str) -> tuple[str, str]:
    require(isinstance(host, str) and HOST.fullmatch(host) is not None,
            "seed host is not canonical")
    prefix = f"host-proofs/{host}"
    return f"{prefix}/SEED-MINT", f"{prefix}/seed-surface.json"


def record_path(host: str) -> str:
    proof_paths(host)
    return f"host-proofs/{host}/host-record.json"


def record_bytes(record: dict[str, object]) -> bytes:
    return (json.dumps(record, sort_keys=True, indent=2) + "\n").encode("utf-8")


def host_payloads(pins: dict[str, str], host: str) -> dict[str, str]:
    proof_paths(host)
    result = {}
    for component in COMPONENTS:
        version = pins.get("rustfmt_version" if component == "trustfmt" else "compiler_version")
        suffix = "" if component == "trust-src" else f"-{host}"
        key = f"dist/{pins.get('compiler_date')}/{component}-{version}{suffix}.tar.xz"
        digest = pins.get(key)
        require(isinstance(digest, str) and SHA.fullmatch(digest) is not None,
                f"missing exact {host} seed archive: {key}")
        result[key] = digest
    return result


def pinned_hosts(pins: dict[str, str]) -> list[str]:
    """Cover every pinned archive; do not infer a host from just trustc."""
    hosts = set()
    source = f"dist/{pins.get('compiler_date')}/trust-src-{pins.get('compiler_version')}.tar.xz"
    for key in pins:
        if not key.startswith("dist/") or not key.endswith(".tar.xz"):
            continue
        if key == source:
            continue
        matched = False
        for component in COMPONENTS:
            if component == "trust-src":
                continue
            version = pins.get("rustfmt_version" if component == "trustfmt" else "compiler_version")
            prefix = f"dist/{pins.get('compiler_date')}/{component}-{version}-"
            if key.startswith(prefix):
                host = key[len(prefix):-len('.tar.xz')]
                proof_paths(host)
                hosts.add(host)
                matched = True
                break
        require(matched, f"archive is outside the exact seed cohort: {key}")
    require(bool(hosts), "seed cohort has no host archives")
    require(len(hosts) <= MAX_HOSTS, "seed cohort exceeds its bounded native host count")
    for host in hosts:
        host_payloads(pins, host)
    return sorted(hosts)


def parse_receipt(payload: bytes) -> dict[str, str]:
    require(0 < len(payload) <= MAX_PROOF_BYTES, "seed receipt exceeds its bounded input size")
    receipt = {}
    files = 0
    for line in payload.decode("utf-8").splitlines():
        if not line or line.startswith("#"):
            continue
        key, separator, value = line.partition("=")
        require(bool(separator), "malformed seed receipt line")
        if key in ("compiler_file", "compiler_link"):
            identity, space, path = value.partition(" ")
            require(bool(space) and bool(path) and not path.startswith("/")
                    and all(part not in ("", ".", "..") for part in path.split("/")),
                    "seed receipt compiler row escapes stage2")
            if key == "compiler_file":
                require(SHA.fullmatch(identity) is not None, "malformed compared compiler digest")
                files += 1
            continue
        require(key not in receipt, f"duplicate seed receipt field: {key}")
        receipt[key] = value
    require(files > 0, "seed receipt contains no compared compiler files")
    return receipt


def validate_receipt(receipt: dict[str, str], pins: dict[str, str], host: str) -> None:
    version = pins.get("compiler_version", "")
    require(version.endswith("-trust"), "seed compiler version is not Trust-owned")
    expected = {
        "schema": "trust-seed-mint-v1", "source_commit": pins.get("compiler_git_commit_hash"),
        "source_commit_date": pins.get("compiler_date"), "source_version": version[:-6],
        "host": host, "ddc_verdict": "identical", "self_host_proof": "pass",
        "ddc_build_driver": "the pinned seed's cargo, in both builds",
        "ddc_scope": "<build>/<host>/stage2 after x.py build --stage 2 compiler/rustc library/std",
    }
    for key, value in expected.items():
        require(receipt.get(key) == value, f"host seed receipt {key} disagrees with its pinned cohort")
    for key in ("source_commit", "pinned_seed_commit", "ddc_seed_commit"):
        require(COMMIT.fullmatch(receipt.get(key, "")) is not None,
                f"host seed receipt {key} is not a commit")
    for key in ("source_commit_date", "pinned_seed_date", "ddc_seed_date"):
        require(DATE.fullmatch(receipt.get(key, "")) is not None,
                f"host seed receipt {key} is not a date")
    for key in ("pinned_seed_compiler_sha256", "pinned_seed_driver_sha256",
                "ddc_seed_compiler_sha256", "ddc_seed_driver_sha256",
                "stage2_tree_sha256_pinned_seed", "stage2_tree_sha256_ddc_seed"):
        require(SHA.fullmatch(receipt.get(key, "")) is not None,
                f"host seed receipt {key} is not a digest")
    require(receipt["stage2_tree_sha256_pinned_seed"] == receipt["stage2_tree_sha256_ddc_seed"],
            "host seed receipt DDC trees differ")
    relation = receipt.get("ddc_seed_relation")
    lineage = receipt.get("ddc_seed_lineage")
    require((relation == "lineage-disjoint" and lineage == "stock")
            or (relation in ("same-lineage", "pin-ancestor") and lineage == "trust"),
            "host seed receipt has no admissible DDC relation and lineage")
    require(receipt["pinned_seed_commit"] != receipt["ddc_seed_commit"],
            "host seed receipt is a reproducibility control")
    anchor = receipt.get("lineage_disjoint_anchor", "")
    require(anchor == "none" or COMMIT.fullmatch(anchor) is not None,
            "host seed receipt lineage anchor is malformed")
    if relation == "lineage-disjoint":
        require(anchor == receipt["source_commit"], "diverse cut does not name its own anchor")


def json_object(pairs: list[tuple[str, object]]) -> dict[str, object]:
    result = {}
    for key, value in pairs:
        require(key not in result, f"duplicate seed surface field: {key}")
        result[key] = value
    return result


def make_host_record(pins: dict[str, str], host: str, receipt_bytes: bytes,
                     surface_bytes: bytes) -> dict[str, object]:
    receipt_path, surface_path = proof_paths(host)
    for suffix in ("date", "version", "git_commit_hash", "channel_manifest_hash"):
        require(pins.get(f"compiler_{suffix}") == pins.get(f"rustfmt_{suffix}"),
                f"compiler and formatter host cohort {suffix} disagree")
    payloads = host_payloads(pins, host)
    receipt = parse_receipt(receipt_bytes)
    validate_receipt(receipt, pins, host)
    surface = validate_surface(surface_bytes, host, receipt["source_version"])
    identities, entrypoints = surface["tool_versions"], surface["entrypoint_sha256"]
    return {
        "schema": SCHEMA, "host": host,
        "source_commit": receipt["source_commit"],
        "source_commit_date": receipt["source_commit_date"],
        "source_version": receipt["source_version"],
        "pinned_seed_date": receipt["pinned_seed_date"],
        "receipt_path": receipt_path, "receipt_sha256": hashlib.sha256(receipt_bytes).hexdigest(),
        "surface_path": surface_path, "surface_sha256": hashlib.sha256(surface_bytes).hexdigest(),
        "reported_product_identities": {name: value.splitlines()[0] for name, value in identities.items()},
        "entrypoint_sha256": dict(entrypoints),
        "mint": {key: receipt[key] for key in MINT_FIELDS}, "payloads": payloads,
    }


def validate_surface(surface_bytes: bytes, host: str, version: str) -> dict:
    require(0 < len(surface_bytes) <= MAX_PROOF_BYTES, "seed surface exceeds its bounded input size")
    surface = json.loads(surface_bytes.decode("utf-8"), object_pairs_hook=json_object)
    require(isinstance(surface, dict), "seed surface is not an object")
    for key, value in {"schema": "trust-self-host-seed-surface-v1", "host": host,
                       "source_version": version}.items():
        require(surface.get(key) == value, f"host seed surface {key} disagrees with its receipt")
    identities = surface.get("tool_versions")
    require(isinstance(identities, dict) and set(identities) == {"trustc", "targo", "trustfmt"}
            and all(isinstance(value, str) and value.strip() for value in identities.values()),
            "host seed surface has incomplete reported product identities")
    entrypoints = surface.get("entrypoint_sha256")
    require(isinstance(entrypoints, dict)
            and set(entrypoints) == {"trustc", "rustc", "trustdoc", "targo", "cargo", "trustfmt"}
            and all(isinstance(value, str) and SHA.fullmatch(value) for value in entrypoints.values()),
            "host seed surface has incomplete native entrypoint digests")
    tree = surface.get("tree")
    require(isinstance(tree, dict) and isinstance(tree.get("sha256"), str)
            and SHA.fullmatch(tree["sha256"]) is not None,
            "host seed surface has no installed-tree digest")
    return surface


def make_genesis_host_record(pins: dict[str, str], host: str, receipt_bytes: bytes,
                            surface_bytes: bytes) -> dict:
    proof_paths(host)
    require(all(pins.get(f"compiler_{suffix}") == pins.get(f"rustfmt_{suffix}")
                for suffix in ("date", "version", "git_commit_hash", "channel_manifest_hash")),
            "compiler and formatter genesis cohort disagree")
    module = initialization_module()
    receipt = parse_receipt(receipt_bytes)
    admission = module.policy(read_proof_file)
    module.validate_receipt(receipt, pins, host, admission)
    payloads = host_payloads(pins, host)
    require(payloads[f"dist/{pins['compiler_date']}/trust-src-{pins['compiler_version']}.tar.xz"]
            == admission["std_source_archive_sha256"],
            "genesis cannot replace the shared authenticated std source archive")
    surface = validate_surface(surface_bytes, host, receipt["source_version"])
    return {
        "schema": GENESIS_SCHEMA, "host": host, "admission_kind": "genesis-root",
        "source_commit": receipt["source_commit"], "source_commit_date": receipt["source_commit_date"],
        "source_version": receipt["source_version"],
        "receipt_path": f"host-proofs/{host}/GENESIS-ROOT",
        "receipt_sha256": hashlib.sha256(receipt_bytes).hexdigest(),
        "surface_path": f"host-proofs/{host}/seed-surface.json",
        "surface_sha256": hashlib.sha256(surface_bytes).hexdigest(),
        "reported_product_identities": {name: value.splitlines()[0]
                                        for name, value in surface["tool_versions"].items()},
        "entrypoint_sha256": dict(surface["entrypoint_sha256"]),
        "root_initialization": {key: receipt[key] for key in module.GENESIS_FIELDS},
        "payloads": payloads,
    }


def fixed_point_receipt_path(host: str) -> str:
    proof_paths(host)
    return f"host-proofs/{host}/SEED-FIXED-POINT"


def make_fixed_point_host_record(pins: dict[str, str], host: str, receipt_bytes: bytes,
                                 surface_bytes: bytes, *, door: dict[str, dict[str, str]] | None = None) -> dict:
    """The host record of a fixed-point receipt (rules A1-A4, B, D). `door` is
    FIXED_POINT_FIRST_HOSTS unless the producer script passes a candidate entry
    for the record it is about to propose; every other caller uses the table."""
    receipt_path = fixed_point_receipt_path(host)
    _, surface_path = proof_paths(host)
    table = FIXED_POINT_FIRST_HOSTS if door is None else door
    entry = table.get(host)
    digest = hashlib.sha256(receipt_bytes).hexdigest()
    require(isinstance(entry, dict) and entry.get("commit") == pins.get("compiler_git_commit_hash")
            and entry.get("receipt_sha256") == digest,
            f"fixed-point A1: the door (seed_host_ledger.FIXED_POINT_FIRST_HOSTS) has no entry for {host} at the "
            f"pinned compiler commit and this receipt's sha256 {digest}; a fixed-point record is admitted only by "
            "a reviewed code edit that names both")
    require(host in initialization_module().LINUX_HOSTS,
            f"fixed-point A2: {host} is not a native Linux host; only a first Linux seed can be a fixed point")
    require(all(pins.get(f"compiler_{suffix}") == pins.get(f"rustfmt_{suffix}")
                for suffix in ("date", "version", "git_commit_hash", "channel_manifest_hash")),
            "fixed-point A3: the compiler and formatter cohort fields disagree")
    payloads = host_payloads(pins, host)
    module = fixed_point_module()
    receipt = module.parse_receipt(receipt_bytes)
    module.validate_receipt(receipt, pins, host, allowed=FIXED_POINT_UNREPRODUCED_ALLOWED, components=COMPONENTS)
    module.require_canonical(receipt_bytes, receipt)
    fields = receipt.fields
    surface = validate_surface(surface_bytes, host, fields["source_version"])
    return {
        "schema": FIXED_POINT_SCHEMA, "host": host, "admission_kind": module.KIND,
        "source_commit": fields["source_commit"], "source_commit_date": fields["source_commit_date"],
        "source_version": fields["source_version"],
        "receipt_path": receipt_path, "receipt_sha256": digest,
        "surface_path": surface_path, "surface_sha256": hashlib.sha256(surface_bytes).hexdigest(),
        "evidence_sha256": module.evidence_sha256(fields),
        "reported_product_identities": {name: value.splitlines()[0]
                                        for name, value in surface["tool_versions"].items()},
        "entrypoint_sha256": dict(surface["entrypoint_sha256"]),
        "root_disclosure": module.root_disclosure(fields),
        "payloads": payloads,
    }


def fixed_point_actual(seed_root: Path, pins: dict[str, str], host: str, *,
                       door: dict[str, dict[str, str]] | None = None) -> dict:
    """The fixed-point host record re-derived from tracked bytes: the record's
    own rules, then every evidence rule (seed_fixed_point.capture_evidence)."""
    _, surface_path = proof_paths(host)
    receipt_bytes = read_proof(seed_root, fixed_point_receipt_path(host))
    surface_bytes = read_proof(seed_root, surface_path)
    actual = make_fixed_point_host_record(pins, host, receipt_bytes, surface_bytes, door=door)
    module = fixed_point_module()
    # C1 binds each evidence file to its receipt digest, so the record's
    # evidence_sha256 (a digest of those digests) is the evidence's; the final
    # comparison of capture_host_record binds the record to it.
    module.capture_evidence(
        seed_root, pins, host, module.parse_receipt(receipt_bytes), receipt_bytes,
        validate_surface(surface_bytes, host, actual["source_version"]), surface_bytes, read_proof,
        payloads=actual["payloads"], allowed=FIXED_POINT_UNREPRODUCED_ALLOWED)
    return actual


def capture_fixed_point_record(seed_root: Path, pins: dict[str, str], host: str, record: dict[str, object], *,
                               door: dict[str, dict[str, str]] | None = None) -> tuple[dict[str, object], str]:
    """capture_host_record for a fixed-point record, with the producer script's
    candidate door: the same derivation and the same final comparison."""
    metadata = read_proof(seed_root, record_path(host))
    original = json.loads(metadata.decode("utf-8"), object_pairs_hook=json_object)
    actual = fixed_point_actual(seed_root, pins, host, door=door)
    require(record == actual and record == original,
            "seed admission host record differs from its original native record, receipt, surface, or archive pins")
    return actual, hashlib.sha256(metadata).hexdigest()


def make_legacy_host_record(pins: dict[str, str], host: str, receipt_bytes: bytes) -> dict:
    proof_paths(host)
    module = initialization_module()
    require(0 < len(receipt_bytes) <= MAX_PROOF_BYTES, "legacy proof exceeds its bounded input size")
    payloads = host_payloads(pins, host)
    data = module.legacy_admission(pins, host, payloads, receipt_bytes, module.policy(read_proof_file))
    return {
        "schema": LEGACY_SCHEMA, "host": host, "admission_kind": "legacy-bound",
        "source_commit": pins["compiler_git_commit_hash"], "source_commit_date": pins["compiler_date"],
        "source_version": pins["compiler_version"][:-6],
        "receipt_path": f"host-proofs/{host}/LEGACY-ADMISSION",
        "receipt_sha256": hashlib.sha256(receipt_bytes).hexdigest(), "payloads": payloads, **data,
    }


def read_proof_file(path: Path) -> bytes:
    """Capture a bounded regular proof file before any receipt or JSON parsing."""
    metadata = path.lstat()
    require(stat.S_ISREG(metadata.st_mode), "seed host proof is not a regular file")
    require(0 < metadata.st_size <= MAX_PROOF_BYTES, "seed host proof exceeds its bounded input size")
    fd = os.open(path, os.O_RDONLY | getattr(os, "O_NOFOLLOW", 0)
                 | getattr(os, "O_NONBLOCK", 0))
    with os.fdopen(fd, "rb") as handle:
        opened = os.fstat(handle.fileno())
        require(stat.S_ISREG(opened.st_mode), "opened seed host proof is not a regular file")
        fields = ("st_dev", "st_ino", "st_size", "st_mtime_ns", "st_ctime_ns")
        require(tuple(getattr(opened, name) for name in fields)
                == tuple(getattr(metadata, name) for name in fields),
                "seed host proof changed before capture")
        payload = handle.read(MAX_PROOF_BYTES + 1)
        after = os.fstat(handle.fileno())
    require(tuple(getattr(after, name) for name in fields)
            == tuple(getattr(opened, name) for name in fields),
            "seed host proof changed during capture")
    require(0 < len(payload) <= MAX_PROOF_BYTES, "seed host proof exceeds its bounded input size")
    require(len(payload) == opened.st_size, "seed host proof capture length differs from its file size")
    return payload


def read_proof(seed_root: Path, relative: str) -> bytes:
    require(seed_root.resolve(strict=True) == seed_root,
            "seed proof root or one of its parents contains a symlink")
    path = seed_root
    for part in relative.split("/"):
        path = path / part
        metadata = path.lstat()
        require(not stat.S_ISLNK(metadata.st_mode), "seed host proof path contains a symlink")
    return read_proof_file(path)


def collect_host_records(seed_root: Path, pins: dict[str, str], native_host: str,
                         receipt_bytes: bytes, surface_bytes: bytes
                         ) -> tuple[dict[str, dict[str, object]], dict[str, bytes]]:
    records = {}
    proof_bytes = {}
    retained_bytes = 0
    hosts = pinned_hosts(pins)
    require(native_host in hosts, "native producer has no pinned archive cohort")
    for host in hosts:
        if host == native_host:
            receipt, surface = receipt_bytes, surface_bytes
        else:
            receipt_path, surface_path = proof_paths(host)
            receipt = read_proof(seed_root, receipt_path)
            surface = read_proof(seed_root, surface_path)
        records[host] = make_host_record(pins, host, receipt, surface)
        metadata_path = record_path(host)
        if host == native_host:
            metadata = record_bytes(records[host])
        else:
            metadata = read_proof(seed_root, metadata_path)
            original = json.loads(metadata.decode("utf-8"), object_pairs_hook=json_object)
            require(original == records[host],
                    "foreign native host record cannot be rebound to changed archives or proof bytes")
        retained_bytes += len(receipt) + len(surface) + len(metadata)
        require(retained_bytes <= MAX_TOTAL_PROOF_BYTES,
                "retained host proof bytes exceed the aggregate metadata bound")
        receipt_path, surface_path = proof_paths(host)
        proof_bytes[receipt_path] = receipt
        proof_bytes[surface_path] = surface
        proof_bytes[metadata_path] = metadata
    return records, proof_bytes


def select_host_record(release: dict[str, object], host: str) -> dict[str, object] | None:
    """None is the legacy single-host format, never a foreign-host fallback."""
    if "hosts" not in release:
        require(release.get("host_triple") == host, "seed admission ledger host_triple does not match the build host")
        return None
    hosts = release["hosts"]
    require(isinstance(hosts, dict) and bool(hosts), "seed admission host table is malformed")
    record = hosts.get(host)
    require(isinstance(record, dict) and record.get("schema") in HOST_SCHEMAS
            and record.get("host") == host, "seed admission has no exact build-host mint record")
    if len(hosts) > 1:
        require(not any(key in release for key in ("host_triple", "mint", "reported_product_identities")),
                "dual-host ledger also declares ambiguous single-host authority")
    return record


def capture_host_record(seed_root: Path, pins: dict[str, str], host: str,
                        record: dict[str, object]) -> tuple[dict[str, object], str]:
    metadata = read_proof(seed_root, record_path(host))
    original = json.loads(metadata.decode("utf-8"), object_pairs_hook=json_object)
    schema = record.get("schema")
    receipt_path, surface_path = proof_paths(host)
    if schema == SCHEMA:
        actual = make_host_record(pins, host, read_proof(seed_root, receipt_path),
                                  read_proof(seed_root, surface_path))
    elif schema == GENESIS_SCHEMA:
        receipt_bytes = read_proof(seed_root, f"host-proofs/{host}/GENESIS-ROOT")
        actual = make_genesis_host_record(pins, host, receipt_bytes,
                                          read_proof(seed_root, surface_path))
        module = initialization_module()
        module.capture_evidence(seed_root, host, parse_receipt(receipt_bytes), receipt_bytes, read_proof,
                                module.policy(read_proof_file))
        module.validate_completed_producer(seed_root, host, parse_receipt(receipt_bytes))
        module.check_archive_joins(seed_root, pins, host, parse_receipt(receipt_bytes),
                                   validate_surface(read_proof(seed_root, surface_path), host, actual["source_version"]),
                                   read_proof)
    elif schema == LEGACY_SCHEMA:
        actual = make_legacy_host_record(pins, host, read_proof(seed_root, f"host-proofs/{host}/LEGACY-ADMISSION"))
    elif schema == FIXED_POINT_SCHEMA:
        actual = fixed_point_actual(seed_root, pins, host)
    else:
        raise ValueError("unsupported seed host evidence kind")
    require(record == actual and record == original,
            "seed admission host record differs from its original native record, receipt, surface, or archive pins")
    return actual, hashlib.sha256(metadata).hexdigest()


def check_entrypoint_bindings(record: dict[str, object], archive_members: dict[str, dict[str, object]]) -> None:
    """Bind native producer probes to the selected host's pinned archive bytes."""
    # The unchanged legacy admission never had native surface/DDC evidence.
    # Compiler/archive identity is still checked by the recreator's legacy path.
    if record.get("schema") == LEGACY_SCHEMA:
        require(record.get("admission_kind") == "legacy-bound" and "entrypoint_sha256" not in record,
                "legacy admission cannot acquire native surface evidence")
        return
    require(record.get("schema") in (SCHEMA, GENESIS_SCHEMA, FIXED_POINT_SCHEMA),
            "unsupported seed entrypoint evidence kind")
    for name, digest in record["entrypoint_sha256"].items():
        member = archive_members.get(f"bin/{name}", {})
        require(member.get("member_sha256") == digest,
                f"native host surface {name} differs from its pinned archive member")


def check_fixed_point_member_bindings(seed_root: Path, host: str, record: dict[str, object],
                                     archive_members: dict[str, dict[str, object]]) -> None:
    """Every pinned archive member the recreator hashed must be the receipt's
    compiler_file row at its path (E: the per-capture binding of the fixed-point
    kind); a hashed member with no row refuses."""
    require(record.get("schema") == FIXED_POINT_SCHEMA, "only a fixed-point record binds members to its receipt rows")
    receipt_bytes = read_proof(seed_root, fixed_point_receipt_path(host))
    require(hashlib.sha256(receipt_bytes).hexdigest() == record.get("receipt_sha256"),
            "fixed-point receipt is not the one its host record binds")
    rows = fixed_point_module().member_rows(receipt_bytes)
    require(bool(archive_members), "fixed-point member binding has no hashed archive member")
    for path, member in sorted(archive_members.items()):
        require(path in rows, f"pinned archive member {path} has no compiler_file row in the fixed-point receipt")
        require(rows[path] == member.get("member_sha256"),
                f"pinned archive member {path} differs from its fixed-point receipt row")


def render_host_tables(records: dict[str, dict[str, object]]) -> list[str]:
    lines = []
    for host, record in sorted(records.items()):
        table = f"release.hosts.{json.dumps(host)}"
        lines.extend(["", f"[{table}]"])
        require(record.get("schema") in HOST_SCHEMAS, "unsupported seed host evidence kind")
        for key in ("schema", "host", "admission_kind", "source_commit", "source_commit_date", "source_version",
                    "pinned_seed_date", "receipt_path", "receipt_sha256", "surface_path", "surface_sha256",
                    "evidence_sha256"):
            if key in record:
                lines.append(f"{key} = {json.dumps(record[key])}")
        for section in ("reported_product_identities", "entrypoint_sha256", "mint", "root_initialization",
                        "legacy_admission", "root_disclosure", "payloads"):
            if section not in record:
                continue
            lines.extend(["", f"[{table}.{section}]"])
            for key, value in sorted(record[section].items()):
                lines.append(f"{json.dumps(key)} = {json.dumps(value)}")
    return lines
