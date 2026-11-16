"""Assemble initialization payloads without minting native or legacy authority.

The first Linux host must share the original source archive with Darwin. A
freshly repacked trust-src is retained as producer evidence, never substituted
for that pin. GENESIS admission and the final host ledger remain separate.
"""

from __future__ import annotations

import copy
import hashlib
from importlib import util
import json
from pathlib import Path
import shutil
import tarfile
import tomllib

HERE = Path(__file__).resolve().parent


def load(name, path):
    if "__trust_source_loader__" in globals():
        return __trust_source_loader__.module(name, path)
    spec = util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise ValueError("missing initialization cohort helper")
    result = util.module_from_spec(spec)
    spec.loader.exec_module(result)
    return result


support = load("trust_initialization_cohort_mint", HERE / "mint_seed_support.py")
ledger = load("trust_initialization_cohort_ledger", HERE / "seed_host_ledger.py")
initialization = ledger.initialization_module()
prepare = load("trust_initialization_cohort_prepare", HERE.parent / "src/tools/trust-stage0-dist/prepare.py")
require = ledger.require
SERVER = "file://{trust-root}/bootstrap/trust-stage0"
PACKAGES = {"tippy": "tippy-preview", "trustfmt": "trustfmt-preview",
            "trust-analyzer": "trust-analyzer-preview"}
IDENTITY_KEYS = tuple(f"{role}_{field}" for role in ("compiler", "rustfmt")
                      for field in ("git_commit_hash", "date", "version"))


def pins_bytes(payload):
    pins = {}
    for row in payload.decode("utf-8").splitlines():
        if not row or row.startswith("#"):
            continue
        key, sep, value = row.partition("=")
        require(bool(sep) and key not in pins, "duplicate or malformed initialization pin")
        pins[key] = value
    return pins


def archive_capture(path, expected, commit):
    path = support.canonical_regular_file(path, "initialization cohort archive")
    require(support.sha256_file(path) == expected, "initialization cohort archive checksum mismatch")
    with tarfile.open(path, "r:xz") as bundle:
        support.archive_metadata(bundle, path, path.name.removesuffix(".tar.xz"), commit)
    require(support.sha256_file(path) == expected, "initialization archive changed during capture")
    return {"path": str(path), "sha256": expected, "bytes": path.stat().st_size}


def legacy_inputs(receipt_path, archives, manifest_path, admission):
    payload = ledger.read_proof_file(receipt_path)
    document = json.loads(payload, object_pairs_hook=ledger.json_object)
    require(isinstance(document, dict) and isinstance(document.get("stage0"), str),
            "missing original legacy stage0 bytes")
    pins = pins_bytes(document["stage0"].encode())
    # The real legacy dispatcher checks both exact historical text hashes,
    # source tuple, every payload pin, original scope and reported identities.
    record = ledger.make_legacy_host_record(pins, admission["legacy_admission"]["host"], payload)
    manifest_bytes = ledger.read_proof_file(manifest_path)
    manifest_sha = hashlib.sha256(manifest_bytes).hexdigest()
    require(all(pins.get(role + "_channel_manifest_hash") == manifest_sha
                for role in ("compiler", "rustfmt")), "legacy channel differs from its exact original pin")
    files = {relative: archive_capture(archives / Path(relative).name, sha, admission["source_commit"])
             for relative, sha in record["payloads"].items()}
    return {"record": record, "receipt_sha256": hashlib.sha256(payload).hexdigest(),
            "manifest_sha256": manifest_sha, "archives": files}, pins, tomllib.loads(manifest_bytes.decode())


def manifest_payloads(manifest, pins, expected, server=SERVER):
    """Require a bijection, including the host-independent source component."""
    found = {}
    for package, entry in manifest.get("pkg", {}).items():
        for host, target in entry.get("target", {}).items():
            require(isinstance(target, dict), "initialization channel target is malformed")
            require(type(target.get("available")) is bool, "initialization target availability is not boolean")
            if not target.get("available"):
                require(not any(k in target for k in ("xz_url", "xz_hash", "url", "hash")),
                        "unavailable initialization target carries a payload")
                continue
            require(set(target) == {"available", "xz_url", "xz_hash"},
                    "initialization target is not an exact xz payload")
            url = target["xz_url"]
            require(isinstance(url, str) and url.startswith(server + "/"),
                    "initialization payload URL leaves its canonical namespace")
            relative = url[len(server) + 1:]
            component = package.removesuffix("-preview")
            suffix = "" if component == "trust-src" else "-" + host
            canonical = f"dist/{pins['compiler_date']}/{component}-{pins['compiler_version']}{suffix}.tar.xz"
            require(component in ledger.COMPONENTS and relative == canonical
                    and (host == "*" if component == "trust-src" else host in ledger.pinned_hosts(pins)),
                    "initialization target has another component, host or archive identity")
            require(relative not in found and expected.get(relative) == target["xz_hash"],
                    "initialization channel omits or changes a payload pin")
            found[relative] = target["xz_hash"]
    require(found == expected, "initialization channel/pin payload domains differ")


def assemble(native_root, host, receipt_path, archives, legacy_manifest, std_source, output):
    admission = initialization.policy(ledger.read_proof_file)
    require(host in initialization.LINUX_HOSTS, "initialization cohort requires a native Linux host")
    legacy, old_pins, old_manifest = legacy_inputs(receipt_path, archives, legacy_manifest, admission)
    native_pins_bytes = ledger.read_proof_file(native_root / "src-stage0")
    native_pins = pins_bytes(native_pins_bytes)
    require(all(native_pins.get(k) == old_pins.get(k) for k in IDENTITY_KEYS)
            and ledger.pinned_hosts(native_pins) == [host], "native preparation has another source or host cohort")
    native_seed = native_root / "bootstrap/trust-stage0"
    date = admission["source_date"]
    native_manifest_bytes = ledger.read_proof_file(native_seed / "dist" / date / "channel-rust-trust.toml")
    native_manifest_sha = hashlib.sha256(native_manifest_bytes).hexdigest()
    require(all(native_pins.get(role + "_channel_manifest_hash") == native_manifest_sha
                for role in ("compiler", "rustfmt")), "native channel differs from its prepared pin")
    native_manifest = tomllib.loads(native_manifest_bytes.decode())
    require(prepare._manifest_release_identity(native_manifest) == prepare._manifest_release_identity(old_manifest),
            "initialization channel source identities differ")
    shared = f"dist/{date}/trust-src-{old_pins['compiler_version']}.tar.xz"
    require(old_pins.get(shared) == admission["std_source_archive_sha256"], "original shared source pin changed")
    std = archive_capture(std_source, old_pins[shared], admission["source_commit"])
    source_inputs = {k: archive_capture(native_seed / k, sha, admission["source_commit"])
                     for k, sha in ledger.host_payloads(native_pins, host).items()}
    manifest_payloads(native_manifest, native_pins, ledger.host_payloads(native_pins, host), native_pins["dist_server"])
    manifest = copy.deepcopy(native_manifest)
    for component in ledger.COMPONENTS:
        package = PACKAGES.get(component, component)
        triple = "*" if component == "trust-src" else admission["legacy_admission"]["host"]
        old_package = old_manifest.get("pkg", {}).get(package, {})
        new_package = manifest.get("pkg", {}).get(package, {})
        require(all(old_package.get(k) == new_package.get(k) for k in ("version", "git_commit_hash")),
                "initialization component source identity differs")
        require(triple in old_package.get("target", {}) and isinstance(new_package.get("target"), dict),
                "initialization channel lacks an original component")
        new_package["target"][triple] = copy.deepcopy(old_package["target"][triple])
    payloads = {**ledger.host_payloads(native_pins, host), **legacy["record"]["payloads"]}
    payloads[shared] = old_pins[shared]
    combined = {**native_pins, **payloads}
    # Normalize only URLs; exact native and historical archive bytes stay fixed.
    for entry in manifest["pkg"].values():
        for target in entry.get("target", {}).values():
            if target.get("available"):
                target["xz_url"] = SERVER + "/dist/" + date + "/" + Path(target["xz_url"]).name
    manifest_payloads(manifest, combined, payloads)
    manifest_payloads(old_manifest, old_pins, legacy["record"]["payloads"])
    require(not output.exists() and not output.is_symlink(), "initialization cohort output must be fresh")
    output.mkdir(mode=0o700)
    seed = output / "bootstrap/trust-stage0"
    for relative, sha in payloads.items():
        source = Path(std["path"]) if relative == shared else Path((legacy["archives"] if relative in legacy["archives"] else source_inputs)[relative]["path"])
        destination = seed / relative
        destination.parent.mkdir(mode=0o700, parents=True, exist_ok=True)
        support.copy_authenticated(source, destination)
        require(support.sha256_file(destination) == sha, "copied initialization archive changed")
    channel = prepare.dump_toml(manifest).encode()
    (seed / "dist" / date / "channel-rust-trust.toml").write_bytes(channel)
    stage0 = prepare.stage0_content(manifest=manifest, manifest_hash=hashlib.sha256(channel).hexdigest(),
                git_commit_hash=admission["source_commit"], dist_server=SERVER, owned_channel="trust",
                compiler_version=old_pins["compiler_version"], rustfmt_version=old_pins["rustfmt_version"],
                checksums=dict(sorted(payloads.items())), metadata_only_checkout=False)
    (output / "src-stage0").write_text(stage0)
    proof = seed / "host-proofs" / admission["legacy_admission"]["host"]
    proof.mkdir(mode=0o700, parents=True)
    (proof / "LEGACY-ADMISSION").write_bytes(ledger.read_proof_file(receipt_path))
    (proof / "host-record.json").write_bytes(ledger.record_bytes(legacy["record"]))
    require(legacy_inputs(receipt_path, archives, legacy_manifest, admission)[0] == legacy
            and support.sha256_file(std_source) == std["sha256"], "original initialization inputs changed")
    for row in source_inputs.values():
        require(support.sha256_file(Path(row["path"])) == row["sha256"], "native preparation input changed")
    require(ledger.read_proof_file(native_root / "src-stage0") == native_pins_bytes
            and ledger.read_proof_file(native_seed / "dist" / date / "channel-rust-trust.toml") == native_manifest_bytes,
            "native preparation metadata changed during cohort assembly")
    result = {"schema": "trust.initialization-cohort-payloads.v1", "host": host,
              "source_commit": admission["source_commit"], "payloads": payloads, "legacy": legacy,
              "shared_source": std, "displaced_native_source_sha256": native_pins[shared],
              "stage0_sha256": hashlib.sha256(stage0.encode()).hexdigest(),
              "channel_manifest_sha256": hashlib.sha256(channel).hexdigest(),
              "admitted_root_seed": False, "counts_as_trust_stage0_evidence": False,
              "remaining": "completed native GENESIS producer custody and exact initialized host ledger"}
    support.write_json_exclusive(output / "cohort-payloads.json", result)
    return result
