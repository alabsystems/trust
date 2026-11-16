"""First native Linux root evidence, separate from an ordinary Trust seed mint.

This validates recorded producer evidence, not a signature or execution proof.
The external adapter remains non-evidentiary. Only a completed native producer
may supply GENESIS-ROOT after self-host, DDC, full tools, archive and rebuild
checks. No external compiler is an admitted Trust predecessor.
"""

from __future__ import annotations

import hashlib
import json
from pathlib import Path, PurePosixPath
import re
import tarfile
import tomllib

POLICY_PATH = Path(__file__).resolve().parents[1] / "bootstrap/trust-linux-root-initialization.json"
GENESIS_SCHEMA = "trust-seed-genesis-host-record-v1"
LEGACY_SCHEMA = "trust-seed-legacy-host-record-v1"
RECEIPT_SCHEMA = "trust-genesis-root-v1"
HISTORICAL_CONTRACT = "trust.original629-bootstrap-surface.v1"
LINUX_HOSTS = {"aarch64-unknown-linux-gnu", "x86_64-unknown-linux-gnu"}
DDC_SCOPE = "<build>/<host>/stage2 after x.py build --stage 2 compiler/rustc library/std"
DDC_CAVEAT = "shared rust-lang bootstrap ancestry and the common build driver are not covered"
SHA = re.compile(r"[0-9a-f]{64}")
COMMIT = re.compile(r"[0-9a-f]{40,64}")
GENESIS_FIELDS = (
    "predecessor", "external_root_commit", "external_root_manifest_sha256",
    "external_root_sysroot_sha256", "ddc_seed_commit", "ddc_seed_manifest_sha256",
    "ddc_seed_sysroot_sha256", "ddc_seed_relation", "ddc_lineage_caveat",
    "stage2_tree_sha256_self_host", "stage2_tree_sha256_ddc_seed",
    "source_closure_sha256", "self_host_proof", "archive_rebuild",
    "full_tools_contract", "current_toolchain_qualification",
)
DIGEST_FIELDS = (
    "source_closure_sha256", "source_tree_sha256", "orchestration_sha256",
    "external_root_manifest_sha256", "external_root_sysroot_sha256",
    "external_root_compiler_sha256", "external_root_driver_sha256",
    "ddc_seed_manifest_sha256", "ddc_seed_sysroot_sha256",
    "ddc_seed_compiler_sha256", "ddc_seed_driver_sha256", "ddc_build_driver_sha256",
    "stage2_tree_sha256_self_host", "stage2_tree_sha256_ddc_seed",
    "self_host_inputs_sha256", "ddc_inputs_sha256", "full_tools_receipt_sha256",
    "archive_comparison_receipt_sha256", "archive_rebuild_receipt_sha256",
    "native_runtime_receipt_sha256", "inputs_before_sha256", "inputs_after_sha256",
)
EVIDENCE = {
    "source-closure.json": "source_closure_sha256",
    "external-root.json": "external_root_sysroot_sha256",
    "ddc-root.json": "ddc_seed_sysroot_sha256",
    "genesis-channel.toml": "external_root_manifest_sha256",
    "ddc-channel.toml": "ddc_seed_manifest_sha256",
    "inputs-before.json": "inputs_before_sha256", "inputs-after.json": "inputs_after_sha256",
    "full-tools.json": "full_tools_receipt_sha256",
    "archive-comparison.json": "archive_comparison_receipt_sha256",
    "archive-rebuild.json": "archive_rebuild_receipt_sha256",
    "native-runtime.json": "native_runtime_receipt_sha256",
}
FULL_TOOLS = ("bin/trustc", "bin/ay", "bin/ty", "bin/clean", "bin/rustc", "bin/cargo",
              "bin/targo", "bin/targo-trust", "bin/trustd", "bin/trustdoc", "bin/rustdoc",
              "bin/trustfmt", "bin/targo-fmt", "bin/tippy", "bin/targo-tippy", "bin/tippy-driver",
              "bin/trust-analyzer", "libexec/trust-analyzer-proc-macro-srv")
SOURCE_SNAPSHOTS = ("lib/rustlib/src", "lib/rustlib/rustc-src")


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def json_object(pairs) -> dict:
    result = {}
    for key, value in pairs:
        require(key not in result, "duplicate initialization JSON field")
        result[key] = value
    return result


def policy(read_file) -> dict:
    document = json.loads(read_file(POLICY_PATH).decode("utf-8"), object_pairs_hook=json_object)
    require(isinstance(document, dict)
            and document.get("schema") == "trust.linux-root-initialization-policy.v1",
            "unsupported Linux root initialization policy")
    return document


def validate_evidence(payloads: dict, receipt: dict, files: dict, admission: dict) -> None:
    documents = {name: json.loads(payload.decode("utf-8"), object_pairs_hook=json_object)
                 for name, payload in payloads.items() if name.endswith(".json")}
    source = documents["source-closure.json"]
    require(source.get("schema") == "trust.genesis-source-closure.v1"
            and source.get("source_commit") == receipt["source_commit"]
            and isinstance(source.get("repositories"), list) and source["repositories"],
            "genesis source closure is empty or names another source")
    repositories = {row.get("path"): row for row in source["repositories"]}
    require(len(repositories) == len(source["repositories"]), "duplicate genesis source repository")
    for path, commit in {".": admission["source_commit"], **admission["providers"]}.items():
        row = repositories.get(path, {})
        require(row.get("commit") == commit and type(row.get("tracked_files")) is int and row["tracked_files"] > 0
                and isinstance(row.get("tracked_bytes_sha256"), str) and SHA.fullmatch(row["tracked_bytes_sha256"]),
                "genesis source closure omits or changes an original pinned provider")
    require(repositories["."]["tracked_bytes_sha256"] == receipt["source_tree_sha256"],
            "genesis actual tracked compiler source digest differs from its receipt")
    for role, name, prefix in (("genesis", "external-root.json", "external_root"),
                               ("ddc", "ddc-root.json", "ddc_seed")):
        root = documents[name]
        identity = root.get("identity", {})
        require(root.get("admission") == "external-bootstrap-root-only"
                and root.get("counts_as_trust_stage0_evidence") is False
                and identity.get("lineage") == "stock" and identity.get("host") == receipt["host"]
                and identity.get("commit") == receipt[prefix + "_commit"]
                and identity.get("compiler_sha256") == receipt[prefix + "_compiler_sha256"]
                and identity.get("driver_sha256") == receipt[prefix + "_driver_sha256"],
                "genesis external oracle evidence has different identity or authority")
        channel = tomllib.loads(payloads["genesis-channel.toml" if role == "genesis" else "ddc-channel.toml"].decode())
        components = root.get("components", [])
        require(isinstance(components, list) and len(components) == 3
                and {r.get("component") for r in components} == {"rustc", "cargo", "rust-std"},
                "genesis external root is missing an authenticated tool/std component")
        for component in components:
            entry = channel.get("pkg", {}).get(component["component"], {}).get("target", {}).get(receipt["host"], {})
            require(entry.get("available") is True and entry.get("xz_hash") == component.get("archive_sha256")
                    and component.get("payloads"), "genesis external archive evidence differs from its native channel")
    tools = documents["full-tools.json"]
    require(tools.get("schema") == "trust.genesis-native-tools.v1" and tools.get("passed") is True
            and tools.get("contract") == HISTORICAL_CONTRACT
            and tools.get("source_commit") == receipt["source_commit"]
            and tools.get("current_toolchain_qualification") is False
            and tools.get("supports_modern_native_lane") is False
            and tools.get("host") == receipt["host"] and set(tools.get("tools", {})) == set(FULL_TOOLS)
            and all(isinstance(v, str) and SHA.fullmatch(v) for v in tools["tools"].values()),
            "genesis requires the complete native 18-tool inventory")
    require(tools["tools"]["bin/trustc"] == files["bin/trustc"],
            "genesis full native tools probe used another compiler")
    comparison = documents["archive-comparison.json"]
    require(comparison.get("schema") == "trust.genesis-archive-comparison.v1"
            and comparison.get("host") == receipt["host"] and comparison.get("passed") is True
            and isinstance(comparison.get("files"), dict) and comparison["files"]
            and all(files.get(k) == v for k, v in comparison["files"].items())
            and len(comparison["files"]) == int(receipt["archive_compared_files"]),
            "genesis archives do not bind their compared compiler/std bytes")
    require("bin/trustc" in comparison["files"] and any("/librustc_driver-" in p for p in comparison["files"])
            and any("/libstd-" in p for p in comparison["files"]),
            "genesis archives omit their compared compiler, driver or std")
    rebuild = documents["archive-rebuild.json"]
    require(rebuild.get("schema") == "trust.genesis-archive-rebuild.v1" and rebuild.get("passed") is True
            and rebuild.get("source_commit") == receipt["source_commit"] and rebuild.get("host") == receipt["host"]
            and rebuild.get("stage2_tree_sha256") == receipt["stage2_tree_sha256_self_host"],
            "genesis archive rebuild did not reproduce the compared native compiler/std")
    runtime = documents["native-runtime.json"]
    observations = runtime.get("observations")
    optional = {"/etc/ld.so.cache", "/etc/ld.so.preload"}
    require(runtime.get("checked") is True and runtime.get("format") == "elf"
            and runtime.get("host") == receipt["host"] and runtime.get("unresolved") == []
            and isinstance(observations, dict) and observations
            and len(observations) == int(receipt["native_runtime_observations"])
            and any(isinstance(v, str) and SHA.fullmatch(v) for v in observations.values())
            and all((isinstance(v, str) and SHA.fullmatch(v)) or (p in optional and v is None)
                    for p, v in observations.items()),
            "genesis native runtime evidence is empty, foreign or unresolved")


def mint_support():
    from importlib import util

    path = Path(__file__).with_name("mint_seed_support.py")
    if "__trust_source_loader__" in globals():
        return __trust_source_loader__.module("trust_genesis_mint_support", path)
    spec = util.spec_from_file_location("trust_genesis_mint_support", path)
    require(spec is not None and spec.loader is not None, "missing compiler tree validator")
    support = util.module_from_spec(spec)
    spec.loader.exec_module(support)
    return support


def tree_manifest(payload: bytes, host: str) -> dict:
    support = mint_support()
    document = json.loads(payload.decode("utf-8"), object_pairs_hook=json_object)
    require(document.get("schema") == "trust-stage2-tree-v1" and isinstance(document.get("records"), list),
            "genesis compiler comparison has no canonical stage2 manifest")
    records = document["records"]
    require(records and support.records_sha256(records) == document.get("sha256"),
            "genesis compiler comparison manifest digest differs from its records")
    paths = set()
    for row in records:
        path = row.get("path")
        require(isinstance(path, str) and not path.startswith("/")
                and all(part not in ("", ".", "..") for part in path.split("/")),
                "genesis comparison path escapes its stage2")
        require(path not in paths, "duplicate genesis comparison path")
        paths.add(path)
        require(row.get("kind") in ("file", "directory", "symlink"), "unsupported genesis compared entry kind")
        if row["kind"] == "file":
            require(isinstance(row.get("sha256"), str) and SHA.fullmatch(row["sha256"]),
                    "genesis compared file has no exact digest")
    files = {row["path"]: row.get("sha256") for row in records if row.get("kind") == "file"}
    require("bin/trustc" in files and any(re.fullmatch(r"lib/librustc_driver-[^/]+\.so", p) for p in files)
            and any(re.fullmatch(rf"lib/rustlib/{re.escape(host)}/lib/libstd-[^/]+\.rlib", p) for p in files),
            "genesis comparison omits its native compiler, driver or std")
    return document


def archive_payloads(seed_root: Path, pins: dict, host: str) -> dict:
    """Hash the actual canonical component payloads, including driver and std."""
    support = mint_support()
    bindings, compressed, expanded = {}, 0, 0
    for component in support.SEED_COMPONENTS:
        version = pins["rustfmt_version" if component == "trustfmt" else "compiler_version"]
        suffix = "" if component == "trust-src" else "-" + host
        relative = f"dist/{pins['compiler_date']}/{component}-{version}{suffix}.tar.xz"
        archive = support.canonical_regular_file(seed_root / relative, "pinned genesis component archive")
        compressed += archive.stat().st_size
        require(compressed <= support.MAX_TOTAL_ARCHIVE_BYTES, "genesis component archives exceed their size bound")
        require(support.sha256_file(archive) == pins.get(relative), "genesis component archive checksum mismatch")
        top = archive.name.removesuffix(".tar.xz")
        with tarfile.open(archive, "r:xz") as bundle:
            members, size = support.archive_metadata(bundle, archive, top, pins["compiler_git_commit_hash"])
            expanded += size
            require(expanded <= support.MAX_TOTAL_UNPACKED_BYTES, "genesis archive expansion exceeds its aggregate bound")
            for member in members:
                path = support.normalized_member(member.name)
                if len(path.parts) < 4 or path.parts[1] != component or path.parts[2] not in ("bin", "lib", "libexec"):
                    continue
                if member.isdir():
                    continue
                stream = bundle.extractfile(member)
                require(stream is not None, "genesis archive payload is unreadable")
                digest = support.sha256_stream(stream)
                destination = "/".join(path.parts[2:])
                require(destination not in bindings or bindings[destination] == digest,
                        "genesis archives install conflicting payload bytes")
                bindings[destination] = digest
        require(support.sha256_file(archive) == pins[relative], "genesis archive changed during payload capture")
    return bindings


def native_pack_payloads(archive: Path, expected_sha256: str, manifest_bytes: bytes, host: str) -> dict:
    """Bind every packaged native entry, with literal link topology and modes."""
    support = mint_support()
    try:
        return _native_pack_payloads(support, archive, expected_sha256, manifest_bytes, host)
    except (support.WorkflowError, tarfile.TarError) as error:
        raise ValueError(str(error)) from error


def native_projection(manifest: dict, source: Path | None = None) -> tuple[list, list]:
    """Keep runtime surfaces; retain, but do not ship, local source-root links."""
    omitted, targets = [], set()
    for prefix in SOURCE_SNAPSHOTS:
        rows = {r["path"]: r for r in manifest["records"]
                if r["path"] == prefix or r["path"].startswith(prefix + "/")}
        if not rows:
            continue
        root, link = rows.get(prefix, {}), rows.get(prefix + "/rust", {})
        target = link.get("target")
        require(set(rows) == {prefix, prefix + "/rust"} and root.get("kind") == "directory"
                and link.get("kind") == "symlink" and isinstance(target, str)
                and target.startswith("/") and "\n" not in target and "\r" not in target
                and all(p not in ("", ".", "..") for p in target.split("/")[1:]),
                "native source snapshot is not the exact bootstrap source-root link")
        require(source is None or target == str(source.resolve(strict=True)),
                "native source snapshot names another authenticated source")
        targets.add(target)
        omitted.extend(rows.values())
    require(len(targets) <= 1, "native source snapshots name different source roots")
    excluded = {r["path"] for r in omitted}
    projected = [r for r in manifest["records"] if r["path"].split("/", 1)[0] in ("bin", "lib", "libexec")
                 and r["path"] not in excluded]
    return projected, sorted(omitted, key=lambda r: r["path"])


def native_link_target(support, path: PurePosixPath, linkname: str, *, hard: bool) -> str:
    # Ordinary components have separate package roots. This artifact has one
    # native root shared by bin/lib/libexec, so preserve internal cross-links.
    link = support.normalized_member(linkname) if hard else linkname
    target = support.resolved_link(PurePosixPath("native-root", path),
                                  str(PurePosixPath("native-root", link)) if hard else link,
                                  hard=hard)
    return str(PurePosixPath(*target.parts[1:]))


def _native_pack_payloads(support, archive: Path, expected_sha256: str, manifest_bytes: bytes, host: str) -> dict:
    manifest = tree_manifest(manifest_bytes, host)
    records = {row["path"]: row for row in native_projection(manifest)[0]}
    files = {p: row["sha256"] for p, row in records.items() if row["kind"] == "file"}
    require(all(p in files for p in FULL_TOOLS), "native package tree omits a required tool")
    archive = support.canonical_regular_file(archive, "full native initialization package")
    require(0 < archive.stat().st_size <= support.MAX_TOTAL_ARCHIVE_BYTES
            and support.sha256_file(archive) == expected_sha256, "native package checksum/size mismatch")
    seen, expanded = set(), 0
    with tarfile.open(archive, "r:xz") as bundle:
        for member in bundle:
            path = support.normalized_member(member.name)
            name = str(path)
            require(name not in seen and len(seen) < support.MAX_ARCHIVE_MEMBERS,
                    "native package has duplicate or excessive entries")
            seen.add(name)
            row = records.get(name)
            require(row is not None and not member.mode & 0o6000, "native package has an unobserved or privileged entry")
            if member.isdir():
                require(row["kind"] == "directory" and member.mode == row.get("mode"), "native package directory mode/kind changed")
            elif member.issym():
                require(row["kind"] == "symlink" and member.linkname == row.get("target"), "native package link topology changed")
                target = native_link_target(support, path, member.linkname, hard=False)
                require(target in records, "native package link leaves its retained payload closure")
            else:
                require(row["kind"] == "file" and (member.isfile() or member.islnk())
                        and member.mode == row.get("mode"), "native package file mode/kind changed")
                if member.islnk():
                    target = native_link_target(support, path, member.linkname, hard=True)
                    require(files.get(target) == row["sha256"], "native package hardlink bytes changed")
                else:
                    expanded += member.size
                    require(member.size == row.get("bytes") and expanded <= support.MAX_TOTAL_UNPACKED_BYTES,
                            "native package file size/expansion mismatch")
                stream = bundle.extractfile(member)
                require(stream is not None and support.sha256_stream(stream) == row["sha256"], "native package file bytes changed")
    require(seen == set(records), "native package omits retained payload entries")
    require(support.sha256_file(archive) == expected_sha256, "native package changed during capture")
    return files


def check_archive_joins(seed_root: Path, pins: dict, host: str, receipt: dict, surface: dict, read_proof) -> None:
    prefix = f"host-proofs/{host}/initialization/"
    manifest = tree_manifest(read_proof(seed_root, prefix + "stage2-self-host.json"), host)
    files = {row["path"]: row["sha256"] for row in manifest["records"] if row["kind"] == "file"}
    bindings = archive_payloads(seed_root, pins, host)
    compared = {p: sha for p, sha in files.items() if p in bindings}
    require(compared and all(bindings[p] == sha for p, sha in compared.items()),
            "genesis archives differ from the compared native compiler/std bytes")
    require("bin/trustc" in compared and any(re.fullmatch(r"lib/librustc_driver-[^/]+\.so", p) for p in compared)
            and any(re.fullmatch(rf"lib/rustlib/{re.escape(host)}/lib/libstd-[^/]+\.rlib", p) for p in compared),
            "genesis archives omit the compared native compiler, driver or std")
    comparison = json.loads(read_proof(seed_root, prefix + "archive-comparison.json"), object_pairs_hook=json_object)
    require(comparison.get("files") == compared and len(compared) == int(receipt["archive_compared_files"]),
            "genesis archive comparison omits available compared payloads")
    # The minimal bootstrap deliberately omits compatibility rustdoc and several
    # native frontends. Their complete byte join belongs to the full native pack.
    tools = json.loads(read_proof(seed_root, prefix + "full-tools.json"), object_pairs_hook=json_object)["tools"]
    require(all(bindings[p] == sha for p, sha in tools.items() if p in bindings),
            "genesis canonical tool payload differs from its native probe")
    require(all(bindings.get("bin/" + p) == sha for p, sha in surface["entrypoint_sha256"].items()),
            "genesis installed surface differs from its actual pinned archive bytes")
    require(surface["entrypoint_sha256"]["trustc"] == files["bin/trustc"],
            "genesis installed compiler differs from its recorded DDC compiler")


def validate_completed_producer(seed_root: Path, host: str, receipt: dict) -> None:
    """Fail closed until the executable native producer's custody seam exists."""
    raise ValueError("GENESIS-ROOT admission is pending: native producer/owner/command/input custody is not implemented")


def capture_evidence(seed_root: Path, host: str, receipt: dict, receipt_bytes: bytes, read_proof, admission: dict) -> dict:
    prefix = f"host-proofs/{host}/initialization/"
    payloads = {name: read_proof(seed_root, prefix + name) for name in EVIDENCE}
    for name, field in EVIDENCE.items():
        require(hashlib.sha256(payloads[name]).hexdigest() == receipt[field],
                f"genesis evidence {name} differs from its exact receipt digest")
    left_bytes = read_proof(seed_root, prefix + "stage2-self-host.json")
    right_bytes = read_proof(seed_root, prefix + "stage2-ddc.json")
    left, right = tree_manifest(left_bytes, host), tree_manifest(right_bytes, host)
    require(left == right and left["sha256"] == receipt["stage2_tree_sha256_self_host"],
            "genesis recorded stage2 comparison is not byte-identical")
    expected = {row["path"]: row["sha256"] for row in left["records"] if row["kind"] == "file"}
    actual = {}
    for line in receipt_bytes.decode("utf-8").splitlines():
        if line.startswith("compiler_file="):
            digest, _, path = line[len("compiler_file="):].partition(" ")
            require(path not in actual, "duplicate genesis compared compiler file")
            actual[path] = digest
    require(actual == expected and len(actual) == int(receipt["compared_files"]),
            "genesis compared file rows differ from its retained compiler manifests")
    validate_evidence(payloads, receipt, expected, admission)
    total = sum(map(len, payloads.values())) + len(left_bytes) + len(right_bytes)
    require(total <= 64 * 1024 * 1024, "genesis evidence exceeds its aggregate metadata bound")
    return {"sha256": hashlib.sha256(b"".join(payloads[name] for name in sorted(payloads))
                                     + left_bytes + right_bytes).hexdigest(), "bytes": total}


def validate_receipt(receipt: dict, pins: dict, host: str, admission: dict) -> None:
    require(host in LINUX_HOSTS, "genesis root requires a supported native Linux host")
    expected = {
        "schema": RECEIPT_SCHEMA, "kind": "genesis-root", "host": host,
        "source_commit": admission["source_commit"], "source_commit_date": admission["source_date"],
        "source_version": admission["source_version"], "predecessor": "absent",
        "external_root_admission": "external-bootstrap-root-only",
        "external_root_counts_as_trust_stage0_evidence": "false",
        "ddc_seed_admission": "external-bootstrap-root-only",
        "ddc_seed_counts_as_trust_stage0_evidence": "false",
        "ddc_seed_relation": "trust-lineage-disjoint-only", "ddc_lineage_caveat": DDC_CAVEAT,
        "ddc_build_driver": "self-hosted candidate's Targo, in both builds",
        "ddc_scope": DDC_SCOPE, "ddc_verdict": "identical", "self_host_proof": "pass",
        "full_tools": "pass", "archives_carry_compared": "pass", "archive_rebuild": "pass",
        "full_tools_contract": HISTORICAL_CONTRACT, "current_toolchain_qualification": "false",
        "native_runtime": "pass", "native_runtime_unresolved": "0",
    }
    for role, prefix in (("genesis", "external_root"), ("ddc", "ddc_seed")):
        root = admission["external_roots"][role]
        expected.update({f"{prefix}_commit": root["commit"],
                         f"{prefix}_manifest_sha256": root["manifest_sha256"]})
    for key, value in expected.items():
        require(receipt.get(key) == value, f"genesis root {key} disagrees with its initialization policy")
    require(receipt["source_commit"] == pins.get("compiler_git_commit_hash")
            and receipt["source_commit_date"] == pins.get("compiler_date")
            and receipt["source_version"] + "-trust" == pins.get("compiler_version"),
            "genesis root source disagrees with its archive cohort")
    require(not any(key.startswith("pinned_seed_") for key in receipt),
            "genesis root cannot invent a pinned predecessor")
    for key in DIGEST_FIELDS:
        require(isinstance(receipt.get(key), str) and SHA.fullmatch(receipt[key]) is not None,
                f"genesis root {key} is not an exact digest")
    require(COMMIT.fullmatch(receipt.get("orchestration_commit", "")) is not None,
            "genesis root has no exact orchestration commit")
    for left, right in (("stage2_tree_sha256_self_host", "stage2_tree_sha256_ddc_seed"),
                        ("self_host_inputs_sha256", "ddc_inputs_sha256"),
                        ("inputs_before_sha256", "inputs_after_sha256")):
        require(receipt[left] == receipt[right], f"genesis root {left} and {right} differ")
    require(receipt["external_root_commit"] != receipt["ddc_seed_commit"],
            "genesis root DDC cannot reuse its external genesis compiler")
    for key in ("self_host_build_path", "ddc_build_path"):
        value = receipt.get(key, "")
        require(isinstance(value, str) and value.startswith("/") and "\n" not in value,
                "genesis root comparison needs the actual absolute build path")
    require(receipt["self_host_build_path"] == receipt["ddc_build_path"],
            "genesis root DDC was not performed at the same build path")
    for key in ("compared_files", "archive_compared_files", "native_runtime_observations"):
        value = receipt.get(key, "")
        require(isinstance(value, str) and value.isascii() and value.isdigit() and int(value) > 0,
                f"genesis root {key} is empty or malformed")


def legacy_admission(pins: dict, host: str, payloads: dict, receipt_bytes: bytes,
                     admission: dict) -> dict:
    document = json.loads(receipt_bytes.decode("utf-8"), object_pairs_hook=json_object)
    require(isinstance(document, dict) and set(document) == {"schema", "ledger", "stage0"}
            and document["schema"] == "trust.legacy-seed-admission.v1",
            "unsupported legacy seed admission receipt")
    original = admission["legacy_admission"]
    require(host == original["host"], "legacy admission is restricted to its original host")
    for name in ("ledger", "stage0"):
        require(isinstance(document[name], str), "legacy admission bytes are not UTF-8 text")
        require(hashlib.sha256(document[name].encode("utf-8")).hexdigest()
                == original[f"{name}_sha256"], "legacy admission differs from its exact original bytes")
    ledger = tomllib.loads(document["ledger"])
    release = ledger.get("release", {})
    require(ledger.get("scope") == "internal" and ledger.get("promotion_decision") == "admit-internal"
            and release.get("host_triple") == host and "hosts" not in release,
            "legacy admission cannot change its original host or evidence class")
    old_pins = {}
    for line in document["stage0"].splitlines():
        key, sep, value = line.partition("=")
        if sep and not key.startswith("#"):
            require(key not in old_pins, "duplicate original legacy pin")
            old_pins[key] = value
    for key in ("compiler_git_commit_hash", "compiler_date", "compiler_version",
                "rustfmt_git_commit_hash", "rustfmt_date", "rustfmt_version"):
        require(old_pins.get(key) == pins.get(key), "legacy admission source tuple changed")
    require({k: v for k, v in old_pins.items() if k.startswith("dist/")} == payloads,
            "legacy admission archive tuple changed")
    require(all("sha256:" + value in ledger.get("checksums", []) for value in payloads.values()),
            "original legacy admission lacks an archive checksum")
    identities = release.get("reported_product_identities")
    require(isinstance(identities, dict) and set(identities) == {"trustc", "targo", "trustfmt"},
            "legacy admission lacks its original reported product identities")
    return {"reported_product_identities": identities, "legacy_admission": {
        "original_commit": original["commit"], "original_ledger_sha256": original["ledger_sha256"],
        "original_stage0_sha256": original["stage0_sha256"],
        "counts_as_native_mint_evidence": False, "counts_as_root_initialization_evidence": False,
    }}
