#!/usr/bin/env python3
"""Revalidate a retained mint before its ordinary archive/self-host tail.

The compiler checkout is an explicit input, separate from this orchestration
checkout. Recovery does not write stage provenance, reconstruct a pre-build
observation, or grant a seed/self-host/release verdict.
"""
from __future__ import annotations

import argparse
from contextlib import redirect_stdout
import hashlib
import importlib.util
import json
import os
from pathlib import Path, PurePosixPath
import re
import stat
import sys
import tomllib

ENGINE = Path(__file__).resolve().parents[1]
SCHEMA = "trust.mint-continuation.v1"
MAX_JSON = 32 * 1024 * 1024
AUDIT_MODE = "retained-work-at-provenance"
AUDIT_INPUTS = (
    "mint-stage-observation.json", "stage2-pinned-seed.json", "stage2-ddc-seed.json",
    "ddc-seed.json", "ddc-seed-post-build.json", "safe-path.json",
    "bootstrap-config-closure.json", "cargo-home-inputs.json", "clean-lean-inputs.json",
    "mint-toolchain-inputs.json", "native-library-inputs.json", "pinned-seed.json",
    "seed-dylib-inputs.json",
)


class RecoveryError(RuntimeError):
    pass


def require(condition, message):
    if not condition:
        raise RecoveryError(message)


def digest(path):
    path = Path(path)
    before = path.lstat()
    require(stat.S_ISREG(before.st_mode), f"not a regular file: {path}")
    fd = os.open(path, os.O_RDONLY | getattr(os, "O_NOFOLLOW", 0))
    with os.fdopen(fd, "rb") as stream:
        opened = os.fstat(stream.fileno())
        require((opened.st_dev, opened.st_ino) == (before.st_dev, before.st_ino), f"file changed: {path}")
        value = hashlib.file_digest(stream, "sha256").hexdigest()
        after = os.fstat(stream.fileno())
    require((before.st_dev, before.st_ino, before.st_size, before.st_mtime_ns) ==
            (after.st_dev, after.st_ino, after.st_size, after.st_mtime_ns), f"file changed: {path}")
    named = path.lstat()
    require((named.st_dev, named.st_ino, named.st_size, named.st_mtime_ns) ==
            (after.st_dev, after.st_ino, after.st_size, after.st_mtime_ns), f"file replaced: {path}")
    return value


def read_regular(path, maximum=MAX_JSON):
    path = Path(path)
    before = path.lstat()
    require(stat.S_ISREG(before.st_mode) and before.st_size <= maximum, f"invalid or oversize file: {path}")
    fd = os.open(path, os.O_RDONLY | getattr(os, "O_NOFOLLOW", 0))
    with os.fdopen(fd, "rb") as stream:
        opened = os.fstat(stream.fileno())
        require((opened.st_dev, opened.st_ino) == (before.st_dev, before.st_ino), f"file changed: {path}")
        raw = stream.read(maximum + 1)
        after = os.fstat(stream.fileno())
    require(len(raw) <= maximum and
            (before.st_dev, before.st_ino, before.st_size, before.st_mtime_ns) ==
            (after.st_dev, after.st_ino, after.st_size, after.st_mtime_ns), f"file changed: {path}")
    named = path.lstat()
    require((named.st_dev, named.st_ino, named.st_size, named.st_mtime_ns) ==
            (after.st_dev, after.st_ino, after.st_size, after.st_mtime_ns), f"file replaced: {path}")
    return raw


def document(path, expected_sha256=None):
    path = Path(path)
    raw = read_regular(path)
    if expected_sha256 is not None:
        require(hashlib.sha256(raw).hexdigest() == expected_sha256, f"JSON input changed: {path}")

    def unique(pairs):
        result = {}
        for key, value in pairs:
            require(key not in result, f"duplicate JSON key {key!r}: {path}")
            result[key] = value
        return result

    value = json.loads(raw, object_pairs_hook=unique,
                       parse_constant=lambda value: require(False, f"nonfinite JSON: {path}"))
    require(isinstance(value, dict), f"JSON object required: {path}")
    return value


def inside(root, relative):
    require(isinstance(relative, str), "relative path must be text")
    p = PurePosixPath(relative)
    require(p.as_posix() == relative and not p.is_absolute() and
            ".." not in p.parts and relative not in ("", "."), f"unconfined path: {relative}")
    path = root / relative
    require(path.resolve(strict=True).is_relative_to(root), f"escaping path: {relative}")
    return path


def load_support():
    spec = importlib.util.spec_from_file_location("trust_recovery_support", ENGINE / "scripts/mint_seed_support.py")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def engine_identity(support):
    head = support.git_command(ENGINE, "rev-parse", "HEAD")
    status = support.git_command(ENGINE, "status", "--porcelain=v1", "--untracked-files=normal", "--ignore-submodules=all")
    require(head.returncode == status.returncode == 0 and not status.stdout.strip(),
            "orchestration checkout must be clean and committed")
    commit = head.stdout.strip()
    require(support.COMMIT_RE.fullmatch(commit), "orchestration commit is not canonical")
    return {"root": str(ENGINE), "commit": commit,
            "entrypoint_sha256": digest(Path(__file__)),
            "support_sha256": digest(ENGINE / "scripts/mint_seed_support.py"),
            "verifier_sha256": digest(ENGINE / "scripts/recreate_bootstrap.py")}


def declared_environment(root, receipt, terminal):
    command = terminal.get("command")
    require(isinstance(command, list) and all(isinstance(v, str) for v in command), "missing original argv")
    require(len(command) >= 2 and command[0] in ("bash", "/bin/bash") and
            Path(command[1]) == root / "scripts/mint_and_prove_seed.sh", "foreign original entrypoint")

    def option(name):
        require(command.count(name) == 1, f"original argv must contain exactly one {name}")
        index = command.index(name)
        require(index + 1 < len(command), f"missing original {name} value")
        return command[index + 1]

    host = option("--host")
    jobs_text = option("--jobs")
    require(re.fullmatch(r"[1-9][0-9]*", jobs_text), "invalid original job count")
    jobs = int(jobs_text)
    configuration = receipt["bootstrap_lineage"]["mint_configuration"]
    require(host == receipt["host"] == configuration["host"], "original host differs")
    require(configuration["xpy_config_overrides"].get("build.jobs") == jobs, "original jobs differ")
    lean = configuration["clean_lean_inputs"]
    require(option("--clean-lean-lib") == lean["library_path"], "original Lean selection differs")
    authority = receipt["build_authority"]
    cargo = Path(authority["cargo_environment"]["cargo_home"])
    work = cargo.parent
    require(work.parent == root / "build" and work.name.startswith(".mint-and-prove.") and
            cargo.name == "cargo-home", "foreign retained operational namespace")
    env = {"CARGO_HOME": str(cargo), "CARGO_NET_OFFLINE": "true", "GIT_CONFIG_NOSYSTEM": "1",
           "GIT_CONFIG_GLOBAL": os.devnull,
           "RUSTUP_HOME": str(work / "environment-mint/rustup-home"),
           }
    # The epoch is the source commit's timestamp, not the run start. Its exact
    # value is recovered by Git and checked against the recorded environment.
    env.update(lean["environment"])
    require(set(lean["environment"]) == {"CLEAN_OLEAN_PINNED_LEAN_LIB", "CLEAN_OLEAN_REQUIRE_PINNED_LEAN"},
            "foreign Lean environment")
    require(authority["declared_rustup_home"]["selected_local_path"] == env["RUSTUP_HOME"] and
            authority["declared_rustup_home"]["entries"] == [] and
            authority["declared_rustup_home"]["errors"] == [], "retained rustup home was not empty")
    for name, rows in authority.get("declared_native_library_paths", {}).items():
        require(name in ("LIBRARY_PATH", "DYLD_LIBRARY_PATH") and isinstance(rows, list), "foreign native environment")
        env[name] = os.pathsep.join(row["selected_local_path"] for row in rows)
    return host, jobs, work, cargo, env, Path(option("--ddc-seed")), Path(option("--cargo-home"))


def validate(root, build, evidence, *, support, owner, engine):
    """Read retained/current identities; never write the compiler checkout."""
    root = support.canonical_directory(Path(root), "frozen product checkout")
    build = support.canonical_directory(Path(build), "retained mint")
    evidence = support.canonical_directory(Path(evidence), "retained evidence")
    terminal = document(evidence / "mint-result.json")
    require(type(terminal.get("exit")) is int and terminal["exit"] == 1, "original mint must be terminal exit1")
    source = support.repository_state(root)
    commit = source["commit"]
    require(terminal.get("source") == terminal.get("source_after") == commit, "original/current source differs")
    state = document(evidence / "state.json")
    require(state.get("source") == commit, "foreign retained state")
    expected_sha = state["canonical_stage_provenance"]["sha256"]
    require(isinstance(expected_sha, str) and support.SHA256_RE.fullmatch(expected_sha), "missing retained provenance hash")
    captured = evidence / "canonical-stage-provenance-before-selfhost.json"
    require(digest(captured) == expected_sha, "retained provenance capture changed")
    receipt = document(captured, expected_sha)
    host, jobs, work, cargo, env, oracle_root, cargo_source = declared_environment(root, receipt, terminal)
    host = support.canonical_host(host)
    version = support.canonical_version(root)
    require(build == root / "build" / f"pack-mint-{version}-{host}-{commit[:12]}", "foreign retained build")
    stage = build / host / "stage2"
    require(digest(stage / "tool-provenance.json") == expected_sha, "in-stage provenance changed")
    require(receipt.get("schema") == "trust.stage-tool-provenance.v2" and
            receipt.get("status") == "internal-release-ready" and receipt.get("errors") == [] and
            receipt.get("writer") == "scripts/mint_and_prove_seed.sh" and receipt.get("stage") == 2 and
            receipt["compiler"]["source_commit"] == commit, "retained stage is not an admitted frozen mint")
    require(not os.path.lexists(work), "recorded private WORK must be absent before rebind")
    require(not os.path.lexists(build.with_name(build.name + ".pinned")), "unrestored DDC build conflicts")
    for output in (build / "trust-seed-mint", build / "repin",
                   root / "build" / f"self-host-proof-{version}-{host}-{commit[:12]}",
                   root / "build" / f"trust-seed-{version}-{host}-{commit[:12]}"):
        require(not os.path.lexists(output), f"conflicting final/proof output: {output}")
    lineage = owner.capture_source_lineage(root)
    recorded = receipt["source_lineage"]
    require(lineage.get("status") == "immutable_release" and lineage.get("errors") == [] and
            lineage.get("repositories") == recorded.get("repositories") and
            lineage.get("closure_sha256") == recorded.get("pre_build_closure_sha256") ==
            recorded.get("post_build_closure_sha256") == recorded.get("closure_sha256") and
            recorded.get("stable_across_build") is True, "recursive source/pin closure changed")
    authority = receipt["bootstrap_lineage"]["validated_seed"]["authority"]
    current_pins = support.read_stage0_pin(root)
    scalar_pins = {key: value for key, value in current_pins.items() if not key.startswith("dist/")}
    payload_pins = {key: value for key, value in current_pins.items() if key.startswith("dist/")}
    # The stage-authority writer separates scalar identity from archive pins;
    # the strict support reader intentionally returns their combined map.
    require(authority["pins"] == scalar_pins, "stage0 scalar pin map changed")
    inputs = []
    observed_payload_pins = {}
    for row in authority["payloads"]:
        p = inside(root, row["path"])
        relative = p.relative_to(root / "bootstrap/trust-stage0").as_posix()
        require(payload_pins.get(relative) == row["pinned_sha256"], "stage0 payload pin map changed")
        require(relative not in observed_payload_pins, "stage0 payload pin is duplicated")
        observed_payload_pins[relative] = row["pinned_sha256"]
        actual = digest(p)
        require(actual == row["actual_sha256"] == row["pinned_sha256"] and row["matches_pin"] is True,
                f"original seed archive changed: {p}")
        inputs.append({"path": row["path"], "sha256": actual})
    require(observed_payload_pins == payload_pins, "stage0 payload pin inventory changed")
    require(len({row["path"] for row in inputs}) == len(support.SEED_COMPONENTS) == len(inputs),
            "original seed archive inventory is incomplete or duplicated")
    for field in ("src_stage0", "channel_manifest"):
        row = authority[field]
        require(digest(inside(root, row["path"])) == row["sha256"], f"original seed {field} changed")
    config = inside(root, receipt["bootstrap_lineage"]["config_path"])
    require(support.configuration_closure(root, config) ==
            receipt["bootstrap_lineage"]["mint_configuration"]["configuration_closure"], "config closure changed")
    lean = support.clean_lean_inputs(root, Path(env["CLEAN_OLEAN_PINNED_LEAN_LIB"]))
    require(lean == receipt["build_authority"]["clean_lean_inputs"] ==
            receipt["bootstrap_lineage"]["mint_configuration"]["clean_lean_inputs"], "Lean closure changed")
    safe_path = evidence / "safe-path-v3-initial.json"
    safe_anchor = state["native_profile"]["sha256"]
    require(state["native_profile"].get("source") == commit and digest(safe_path) == safe_anchor,
            "saved helper manifest differs from original admitted hash")
    safe = document(safe_path, safe_anchor)
    require(safe.get("schema") == "trust-sanitized-path-v2" and safe.get("profile") == support.SANITIZED_PATH_PROFILE and
            safe.get("host") == host and set(safe["admitted"]) == set(support.build_helper_names(host)),
            "native helper profile or inventory differs")
    for name, row in safe["admitted"].items():
        require(support.sanitized_tool_identity(Path(row["path"])) == row, f"native helper changed: {name}")
    require(all(safe["admitted"][name]["path"] == safe["python"] for name in support.PYTHON_BUILD_HELPERS),
            "Python aliases differ")
    for row in receipt["tools"]:
        for path_key, hash_key in (("path", "sha256"), ("producer_path", "producer_sha256")):
            require(digest(inside(root, row[path_key])) == row[hash_key], f"stage tool/producer changed: {row['name']}")
    ddc_dir = evidence / "ddc-equality-evidence"
    observation = document(ddc_dir / "observation.json")
    require(observation.get("source") == commit and observation.get("state") == "actual_canonical_DDC_equality_observed",
            "foreign or incomplete DDC observation")
    expected = {}
    for row in observation["captured_manifests"]:
        name = Path(row["file"]).name
        require(name not in expected, "duplicate DDC evidence row")
        expected[name] = row["sha256"]
    names = {"stage2-pinned-seed.json", "stage2-ddc-seed.json", "ddc-seed.json", "ddc-seed-post-build.json"}
    require(set(expected) == names, "missing or foreign DDC evidence")
    ddc_docs = {}
    for name in sorted(names):
        p = ddc_dir / name
        require(digest(p) == expected[name], f"DDC evidence changed: {name}")
        ddc_docs[name] = document(p, expected[name])
    pinned = ddc_docs["stage2-pinned-seed.json"]
    independent = ddc_docs["stage2-ddc-seed.json"]
    require(support.stage2_records(pinned, "retained pinned stage") ==
            support.stage2_records(independent, "retained oracle stage"), "DDC compared entries differ")
    require(observation.get("stage2_tree_sha256") == pinned["sha256"], "DDC observation tree differs")
    require(state["ddc"].get("stage2_tree_sha256") == pinned["sha256"], "DDC tree differs from original cut")
    require(ddc_docs["ddc-seed.json"] == ddc_docs["ddc-seed-post-build.json"], "DDC oracle changed during build")
    oracle = ddc_docs["ddc-seed.json"]
    require(observation.get("oracle_commit") == oracle.get("commit") and
            observation.get("relation") == oracle.get("relation"), "DDC observation oracle differs")
    require(state["ddc"].get("oracle_commit") == oracle.get("commit") and
            state["ddc"].get("relation") == oracle.get("relation"), "DDC oracle relation/identity differs from original cut")
    require(oracle.get("relation") in support.DDC_RELATIONS and oracle["relation"] != "reproducibility-control" and
            oracle.get("sysroot") == str(oracle_root) and oracle.get("host") == host, "foreign oracle relation/root/host")
    for key in ("compiler", "driver"):
        require(digest(inside(oracle_root, oracle[key])) == oracle[key + "_sha256"], "current oracle bytes changed")
    support.verify_stage2_unchanged(ddc_dir / "stage2-pinned-seed.json", stage)
    env["SOURCE_DATE_EPOCH"] = str(source["source_date_epoch"])
    expected_environment = receipt["build_authority"]["declared_environment_sha256"]
    require({key: hashlib.sha256(value.encode()).hexdigest() for key, value in env.items()} == expected_environment,
            "recorded closed environment cannot be recovered exactly")
    dist = build / "dist"
    expected_files = {f"{component}-{version}-trust{'' if component == 'trust-src' else '-'+host}.tar.{fmt}"
                      for component in support.SEED_COMPONENTS for fmt in ("xz", "gz")}
    expected_files.update({"channel-rust-trust.toml", "channel-rust-trust-date.txt", "channel-rust-trust-git-commit-hash.txt"})
    require(not dist.is_symlink() and {p.name for p in dist.iterdir()} == expected_files, "retained dist inventory differs")
    inventory = {name: digest(dist / name) for name in sorted(expected_files)}
    channel = tomllib.loads((dist / "channel-rust-trust.toml").read_text())
    matched = set()
    for pkg in channel["pkg"].values():
        for row in pkg.get("target", {}).values():
            for url, hash_key in (("url", "hash"), ("xz_url", "xz_hash")):
                name = str(row.get(url, "")).rsplit("/", 1)[-1]
                if name in inventory:
                    require(row.get(hash_key) == inventory[name], f"archive/channel hash differs: {name}")
                    matched.add(name)
    require(matched == {name for name in expected_files if name.endswith((".tar.xz", ".tar.gz"))}, "channel archive coverage differs")
    require((dist / "channel-rust-trust-git-commit-hash.txt").read_text().strip() == commit and
            (dist / "channel-rust-trust-date.txt").read_text().strip() == source["commit_date"], "channel source identity differs")
    return {"schema": SCHEMA, "state": "inspected", "qualification": False,
            "product_source": {"root": str(root), "commit": commit}, "engine_source": engine,
            "root": str(root), "build": str(build),
            "host": host, "version": version, "original_jobs": jobs, "work": str(work),
            "safe_bin": str(work / "safe-bin"), "cargo_home": str(cargo), "cargo_source": str(cargo_source),
            "path_manifest": str(work / "safe-path.json"),
            "ddc_seed": str(oracle_root),
            "config": str(config), "declared_environment": env, "original_terminal_exit": 1,
            "evidence": str(evidence), "evidence_sha256": {"terminal": digest(evidence / "mint-result.json"),
                "stage_provenance": expected_sha, "safe_path": digest(safe_path), "ddc": expected},
            "dist_sha256": inventory, "source_closure_sha256": lineage["closure_sha256"],
            "ddc_tree_sha256": pinned["sha256"], "ddc_records": len(pinned["records"]),
            "original_work_retained": False, "original_private_cargo_retained": False,
            "strict_native_verifier_passed": False,
            "remaining": ["fresh archive admission/install", "seed validation/carry-compared", "fresh selfhost/sanity", "all final revalidations"]}


def prepare(record, *, support, owner):
    """Recreate only absent aliases/empty private directories, then reverify."""
    root, work = Path(record["root"]), Path(record["work"])
    require(not os.path.lexists(work), "recorded private WORK already exists")
    safe_source = Path(record["evidence"]) / "safe-path-v3-initial.json"
    safe_raw = read_regular(safe_source)
    require(hashlib.sha256(safe_raw).hexdigest() == record["evidence_sha256"]["safe_path"], "saved helper manifest changed")
    safe = document(safe_source, record["evidence_sha256"]["safe_path"])
    retained = {}
    for name, expected in record["evidence_sha256"]["ddc"].items():
        raw = read_regular(Path(record["evidence"]) / "ddc-equality-evidence" / name)
        require(hashlib.sha256(raw).hexdigest() == expected, f"retained DDC evidence changed before rebind: {name}")
        retained[name] = raw
    original_stage = Path(record["build"]) / record["host"] / "stage2/tool-provenance.json"
    require(digest(original_stage) == record["evidence_sha256"]["stage_provenance"], "stage changed before rebind")
    work.mkdir(mode=0o700)
    try:
        safe_bin = Path(record["safe_bin"])
        safe_bin.mkdir(mode=0o700)
        for name, row in safe["admitted"].items():
            (safe_bin / name).symlink_to(row["path"])
        for name in ("home", "tmp", "rustup-home", "xdg-config"):
            (work / "environment-mint" / name).mkdir(mode=0o700, parents=True, exist_ok=True)
        cargo = Path(record["cargo_home"])
        cargo.mkdir(mode=0o700)
        manifest = Path(record["path_manifest"])
        with manifest.open("xb") as stream:
            stream.write(safe_raw)
        require(digest(manifest) == record["evidence_sha256"]["safe_path"], "restored helper manifest differs")
        for name, raw in retained.items():
            with (work / name).open("xb") as stream:
                stream.write(raw)
            require(digest(work / name) == record["evidence_sha256"]["ddc"][name], "restored DDC evidence differs")
        support.revalidate_sanitized_path(safe_bin, manifest)
        receipt = document(original_stage, record["evidence_sha256"]["stage_provenance"])
        configuration = receipt["bootstrap_lineage"]["mint_configuration"]
        environment = {**record["declared_environment"], "HOME": str(work / "environment-mint/home"),
                       "USER": "trust-seed", "LOGNAME": "trust-seed", "PATH": str(safe_bin),
                       "TMPDIR": str(work / "environment-mint/tmp"), "XDG_CONFIG_HOME": str(work / "environment-mint/xdg-config"),
                       "LANG": "C", "LC_ALL": "C", "TZ": "UTC"}
        saved = dict(os.environ)
        try:
            os.environ.clear()
            os.environ.update(environment)
            require(owner.verify_stage_tool_provenance(root, record["host"], 2,
                        require_immutable_lineage=True, require_llvm_identity=True,
                        build_root=Path(record["build"]), config_path=Path(record["config"]), cargo_home=cargo,
                        declared_environment=record["declared_environment"], mint_configuration=configuration),
                    "unchanged strict stage provenance verifier refused the rebind")
        finally:
            os.environ.clear()
            os.environ.update(saved)
        require(digest(original_stage) == record["evidence_sha256"]["stage_provenance"], "original stage receipt changed")
        support.revalidate_sanitized_path(safe_bin, manifest)
        require(not list(cargo.iterdir()), "read-only verifier changed empty Cargo home")
        cargo.rmdir()  # Canonical cargo-home-inputs must create the fresh input copy itself.
        record.update(state="prepared", strict_native_verifier_passed=True,
                      cargo_home_absent_for_fresh_inputs=True,
                      rebind={"kind": "fresh aliases and empty private directories", "original_observation_rewritten": False,
                              "prebuild_observation_reconstructed": False, "phase_split": True})
        return record
    except BaseException:
        # Keep failed owned recovery state for diagnosis. It cannot be mistaken
        # for a prepared record, and the next prepare refuses its presence.
        raise


def retained_files(evidence):
    """Bind raw originals to their preserved copies, without interpreting a failure as success."""
    retained = document(evidence / "RETAINED.json")
    require(retained.get("schema") == "trust.failed-mint-retained-evidence.v1" and
            type(retained.get("actual_exit")) is int and retained["actual_exit"] == 1,
            "retained history must describe an actual failed mint")
    rows = retained.get("files")
    require(isinstance(rows, list) and rows, "missing retained file inventory")
    originals, copies = {}, set()
    for row in rows:
        original, copy = Path(row["original"]), Path(row["retained"])
        require(original.is_absolute() and original not in originals and copy not in copies and
                copy.parent == evidence and copy.resolve(strict=True) == copy,
                "duplicate, foreign or redirected retained file")
        require(re.fullmatch(r"[0-9a-f]{64}", row["sha256"]) and type(row["bytes"]) is int and row["bytes"] >= 0,
                "malformed retained file identity")
        require(original.stat().st_size == copy.stat().st_size == row["bytes"] and
                digest(original) == digest(copy) == row["sha256"], "retained original/copy changed")
        originals[original] = row
        copies.add(copy)
    return retained, originals


def validate_at_provenance(root, build, evidence, *, support, owner, engine):
    """Admit only a genuinely retained pre-build observation and completed DDC/dist population."""
    root = support.canonical_directory(Path(root), "frozen product checkout")
    build = support.canonical_directory(Path(build), "retained mint")
    evidence = support.canonical_directory(Path(evidence), "retained evidence")
    retained, files = retained_files(evidence)
    source = support.repository_state(root)
    commit, version = source["commit"], support.canonical_version(root)
    require(retained.get("source") == commit, "retained source differs")
    work = support.canonical_directory(Path(retained["original_work"]), "original retained WORK")
    require(work.parent == root / "build" and work.name.startswith(".mint-and-prove."), "foreign retained WORK")
    for name in AUDIT_INPUTS:
        require(work / name in files, f"missing retained original {name}")
    terminals = [(path, document(path)) for path in files if path.parent != work and path.name != "tool-provenance.json"]
    mint = [(path, doc) for path, doc in terminals if isinstance(doc.get("phases"), list)]
    controllers = [(path, doc) for path, doc in terminals if "admission_exit" in doc]
    require(len(mint) == len(controllers) == 1 and len(terminals) == 2 and len(files) == len(AUDIT_INPUTS) + 3,
            "missing, foreign or duplicated failure history")
    mint_path, terminal = mint[0]
    controller = controllers[0][1]
    require(terminal.get("source") == controller.get("source") == commit and
            type(terminal.get("exit")) is int and terminal["exit"] == 1 and
            type(controller.get("admission_exit")) is int and controller["admission_exit"] == 1 and
            controller.get("child_result") == str(mint_path) and
            controller.get("managed_inputs_unchanged") is True and terminal.get("source_config_operator_unchanged") is True,
            "original mint/controller failure or input history differs")
    phases = terminal["phases"]
    require(phases and phases[-1].get("phase") == "canonical-mint" and
            type(phases[-1].get("exit")) is int and phases[-1]["exit"] == 1 and
            all(type(row.get("exit")) is int and row["exit"] == 0 for row in phases[:-1]),
            "failure history did not reach the canonical mint")
    before = document(work / "mint-stage-observation.json")
    require(before.get("schema") == support.MINT_OBSERVATION_SCHEMA, "missing genuine pre-build observation")
    require(before["llvm_before"].get("mode") == "in-tree" and not before["llvm_before"].get("mode_reasons") and
            before["llvm_before"].get("output", {}).get("present") is False,
            "original observation did not establish an absent in-tree LLVM build")
    host = support.canonical_host(before["host"])
    require(build == root / "build" / f"pack-mint-{version}-{host}-{commit[:12]}" and
            before["build_root"] == build.relative_to(root).as_posix(), "foreign retained build")
    rejected_path = build / host / "stage2/tool-provenance.json"
    require(rejected_path in files, "missing original rejected stage receipt")
    rejected = document(rejected_path)
    require(rejected.get("schema") == "trust.stage-tool-provenance.v2" and rejected.get("status") == "rejected" and
            rejected.get("writer") == "scripts/mint_and_prove_seed.sh" and rejected.get("stage") == 2 and
            rejected["compiler"]["source_commit"] == commit, "retained receipt is not the failed mint audit")
    # Read the producer's actual argv shape; do not manufacture an old success receipt.
    original = {"command": phases[-1]["argv"]}
    observed_host, jobs, observed_work, cargo, env, oracle, cargo_source = declared_environment(root, rejected, original)
    require(observed_host == host and observed_work == work and cargo.is_dir() and not cargo.is_symlink(),
            "retained operational namespace differs")
    config = inside(root, before["config_path"])
    command = original["command"]
    require(command.count("--config") == 1 and command[command.index("--config") + 1] == str(config),
            "original configuration selector differs")
    require(before["mint_configuration"] == rejected["bootstrap_lineage"]["mint_configuration"] and
            before["mint_configuration"]["xpy_config_overrides"].get("build.jobs") == jobs,
            "original mint configuration/jobs differ")
    env["SOURCE_DATE_EPOCH"] = str(source["source_date_epoch"])
    require({key: env[key] for key in support.MINT_ENVIRONMENT if key in env} == before["declared_environment"] and
            {key: hashlib.sha256(value.encode()).hexdigest() for key, value in env.items()} == rejected["build_authority"]["declared_environment_sha256"],
            "original closed environment differs")
    require(support.configuration_closure(root, config) == document(work / "bootstrap-config-closure.json") ==
            before["mint_configuration"]["configuration_closure"], "configuration closure changed")
    lean = support.clean_lean_inputs(root, Path(env["CLEAN_OLEAN_PINNED_LEAN_LIB"]))
    require(lean == document(work / "clean-lean-inputs.json") == before["mint_configuration"]["clean_lean_inputs"],
            "retained Lean inputs changed")
    lineage = owner.capture_source_lineage(root)
    require(lineage.get("status") == "immutable_release" and lineage.get("errors") == [] and
            lineage == before["source_lineage"], "original source/pin closure changed")
    authority = before["bootstrap_lineage"]["validated_seed"]["authority"]
    current_pins = support.read_stage0_pin(root)
    require(authority["pins"] == {k: v for k, v in current_pins.items() if not k.startswith("dist/")},
            "retained stage0 scalar pins changed")
    payloads = {}
    for row in authority["payloads"]:
        path = inside(root, row["path"])
        key = path.relative_to(root / "bootstrap/trust-stage0").as_posix()
        require(key not in payloads and current_pins.get(key) == row["pinned_sha256"] == row["actual_sha256"] == digest(path)
                and row["matches_pin"] is True, "retained stage0 payload changed")
        payloads[key] = row["pinned_sha256"]
    require(payloads == {k: v for k, v in current_pins.items() if k.startswith("dist/")} and
            len(payloads) == len(support.SEED_COMPONENTS), "retained stage0 payload coverage differs")
    for field in ("src_stage0", "channel_manifest"):
        row = authority[field]
        require(digest(inside(root, row["path"])) == row["sha256"], "retained seed authority changed")
    for row in rejected["tools"]:
        for path_key, hash_key in (("path", "sha256"), ("producer_path", "producer_sha256")):
            require(digest(inside(root, row[path_key])) == row[hash_key], "retained stage tool/producer changed")
    require(support.mint_tool_manifest(root, config) == document(work / "mint-toolchain-inputs.json"),
            "retained configured tool inputs changed")
    support.verify_cargo_home_source(work / "cargo-home-inputs.json")
    require(document(work / "cargo-home-inputs.json")["source"] == str(cargo_source), "original Cargo source differs")
    for name, selector in (("native-library-inputs.json", "LIBRARY_PATH"), ("seed-dylib-inputs.json", "DYLD_LIBRARY_PATH")):
        paths = [Path(p) for p in env.get(selector, "").split(os.pathsep) if p]
        require(support.native_library_manifest(paths) == document(work / name), "retained native library inputs changed")
    safe = document(work / "safe-path.json")
    require(safe.get("schema") == "trust-sanitized-path-v2" and safe.get("profile") == support.SANITIZED_PATH_PROFILE and
            safe.get("host") == host and set(safe["admitted"]) == set(support.build_helper_names(host)),
            "retained helper profile differs")
    support.revalidate_sanitized_path(work / "safe-bin", work / "safe-path.json")
    pinned = document(work / "stage2-pinned-seed.json")
    require(support.stage2_records(pinned, "retained pinned stage") ==
            support.stage2_records(document(work / "stage2-ddc-seed.json"), "retained oracle stage"), "retained DDC entries differ")
    support.verify_stage2_unchanged(work / "stage2-pinned-seed.json", build / host / "stage2")
    oracle_doc = document(work / "ddc-seed.json")
    require(oracle_doc == document(work / "ddc-seed-post-build.json") and oracle_doc["sysroot"] == str(oracle) and
            oracle_doc["host"] == host and oracle_doc["relation"] in support.DDC_RELATIONS and
            oracle_doc["relation"] != "reproducibility-control", "retained DDC oracle differs")
    for key in ("compiler", "driver"):
        require(digest(inside(oracle, oracle_doc[key])) == oracle_doc[key + "_sha256"], "current DDC oracle changed")
    for output in (build.with_name(build.name + ".pinned"), build / "trust-seed-mint", build / "repin",
                   root / "build" / f"self-host-proof-{version}-{host}-{commit[:12]}",
                   root / "build" / f"trust-seed-{version}-{host}-{commit[:12]}",
                   work / "seed-inputs.json", work / "seed", work / "unpack"):
        require(not os.path.lexists(output), f"conflicting continuation output: {output}")
    dist = build / "dist"
    names = {f"{component}-{version}-trust{'' if component == 'trust-src' else '-'+host}.tar.{fmt}"
             for component in support.SEED_COMPONENTS for fmt in ("xz", "gz")}
    names.update({"channel-rust-trust.toml", "channel-rust-trust-date.txt", "channel-rust-trust-git-commit-hash.txt"})
    require(not dist.is_symlink() and {p.name for p in dist.iterdir()} == names, "retained dist inventory differs")
    inventory = {name: digest(dist / name) for name in sorted(names)}
    channel = tomllib.loads((dist / "channel-rust-trust.toml").read_text())
    matched = set()
    for pkg in channel["pkg"].values():
        for row in pkg.get("target", {}).values():
            for url, hash_key in (("url", "hash"), ("xz_url", "xz_hash")):
                name = str(row.get(url, "")).rsplit("/", 1)[-1]
                if name in inventory:
                    require(row.get(hash_key) == inventory[name], "retained dist/channel hash differs")
                    matched.add(name)
    require(matched == {name for name in names if name.endswith((".tar.xz", ".tar.gz"))} and
            (dist / "channel-rust-trust-git-commit-hash.txt").read_text().strip() == commit and
            (dist / "channel-rust-trust-date.txt").read_text().strip() == source["commit_date"], "retained channel/source coverage differs")
    return {"schema": SCHEMA, "mode": AUDIT_MODE, "state": "inspected", "qualification": False,
            "product_source": {"root": str(root), "commit": commit}, "engine_source": engine,
            "root": str(root), "build": str(build), "host": host, "version": version,
            "original_jobs": jobs, "work": str(work), "safe_bin": str(work / "safe-bin"),
            "path_manifest": str(work / "safe-path.json"), "cargo_home": str(cargo), "cargo_source": str(cargo_source),
            "ddc_seed": str(oracle), "config": str(config), "declared_environment": env,
            "evidence": str(evidence), "original_terminal_exit": 1,
            "evidence_sha256": {"retained_inventory": digest(evidence / "RETAINED.json"),
                                "rejected_stage_provenance": digest(rejected_path), "safe_path": digest(work / "safe-path.json")},
            "dist_sha256": inventory, "ddc_tree_sha256": pinned["sha256"], "ddc_records": len(pinned["records"]),
            "original_work_retained": True, "original_private_cargo_retained": True,
            "strict_native_verifier_passed": False,
            "remaining": ["actual repaired-engine provenance audit", "archive admission/install", "carry-compared", "fresh selfhost/sanity", "all final gates"]}


def prepare_at_provenance(record, receipt_path, *, support, owner):
    """Perform a NEW actual audit against the original observation, never rewriting failed history."""
    require(record.get("mode") == AUDIT_MODE and record.get("state") == "inspected", "wrong recovery boundary")
    root, work, build = (Path(record[key]) for key in ("root", "work", "build"))
    receipt_path = Path(receipt_path)
    require(receipt_path.is_absolute() and receipt_path.parent == Path(record["evidence"]) and
            not receipt_path.is_relative_to(build) and
            re.fullmatch(r"mint-continuation-[A-Za-z0-9-]+-stage-provenance\.json", receipt_path.name) and
            not os.path.lexists(receipt_path),
            "repaired stage audit requires a new external receipt")
    environment = {**record["declared_environment"], "HOME": str(work / "environment-mint/home"),
                   "USER": "trust-seed", "LOGNAME": "trust-seed", "PATH": record["safe_bin"],
                   "TMPDIR": str(work / "environment-mint/tmp"), "XDG_CONFIG_HOME": str(work / "environment-mint/xdg-config"),
                   "LANG": "C", "LC_ALL": "C", "TZ": "UTC"}
    for name in ("HOME", "TMPDIR", "XDG_CONFIG_HOME", "RUSTUP_HOME"):
        require(Path(environment[name]).is_dir() and not Path(environment[name]).is_symlink(), "original closed namespace is missing")
    saved = dict(os.environ)
    try:
        os.environ.clear(); os.environ.update(environment)
        support.finish_mint_stage_evidence(root, build, Path(record["config"]), record["host"],
            work / "mint-stage-observation.json", jobs=record["original_jobs"], receipt_path=receipt_path)
    finally:
        os.environ.clear(); os.environ.update(saved)
    require(digest(Path(record["evidence"]) / "RETAINED.json") == record["evidence_sha256"]["retained_inventory"],
            "original retained inventory changed during re-audit")
    retained_files(Path(record["evidence"]))
    receipt = document(receipt_path)
    require(receipt.get("status") == "internal-release-ready" and receipt.get("errors") == [] and
            receipt["compiler"]["source_commit"] == record["product_source"]["commit"], "new actual provenance audit did not qualify")
    record["evidence_sha256"]["stage_provenance"] = digest(receipt_path)
    record.update(state="prepared", strict_native_verifier_passed=True,
                  stage_provenance_path=str(receipt_path), cargo_home_absent_for_fresh_inputs=False,
                  rebind={"kind": "none: original operational namespace retained", "original_observation_rewritten": False,
                          "failed_attempt_relabelled": False, "new_audit_engine": record["engine_source"]})
    record["remaining"] = record["remaining"][1:]
    return record


def write_record(output, record):
    output = Path(output)
    require(not os.path.lexists(output), f"continuation record exists: {output}")
    fd = os.open(output, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600)
    with os.fdopen(fd, "w", encoding="utf-8") as stream:
        json.dump(record, stream, indent=2, allow_nan=False)
        stream.write("\n")
        stream.flush()
        os.fsync(stream.fileno())
    output.chmod(0o444)


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("mode", choices=("inspect", "prepare", "inspect-at-provenance", "prepare-at-provenance"))
    for name in ("root", "build", "evidence", "output"):
        parser.add_argument("--" + name, type=Path, required=True)
    args = parser.parse_args(argv)
    try:
        require(not os.path.lexists(args.output), "continuation output already exists")
        output = args.output.resolve()
        if output.is_relative_to(args.root.resolve()):
            require(output.parent == args.build.resolve() and
                    re.fullmatch(r"mint-continuation-[A-Za-z0-9-]+\.json", output.name),
                    "only a new named continuation record may be written inside retained MINT")
        support = load_support()
        with redirect_stdout(sys.stderr):
            audit = args.mode.endswith("-at-provenance")
            validator = validate_at_provenance if audit else validate
            record = validator(args.root, args.build, args.evidence, support=support,
                              owner=support.stage_evidence_owner(), engine=engine_identity(support))
            if args.mode == "prepare-at-provenance":
                require(args.output.parent.resolve() == Path(record["evidence"]) and
                        re.fullmatch(r"mint-continuation-[A-Za-z0-9-]+\.json", args.output.name),
                        "retained audit record must be a new named file in its evidence directory")
                receipt_path = Path(record["evidence"]) / (args.output.stem + "-stage-provenance.json")
                record = prepare_at_provenance(record, receipt_path,
                                               support=support, owner=support.stage_evidence_owner())
            elif args.mode == "prepare":
                record = prepare(record, support=support, owner=support.stage_evidence_owner())
        write_record(args.output, record)
        print(json.dumps({"record": str(args.output), "state": record["state"], "qualification": False}))
        return 0
    except (RecoveryError, OSError, ValueError, KeyError, TypeError, RuntimeError) as error:
        print(f"error: retained mint recovery refused: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
