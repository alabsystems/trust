#!/usr/bin/env python3
"""Native qualification; requires a coherently rebuilt toolchain, never PATH defaults.

Run after the compiler, native Targo, targo-trust and trustd from this exact tree
have been built into one sysroot:
  build-slot -- python3 tests/native-admission-census/run.py --bin /abs/sysroot/bin
Add --verify-stage-provenance to require this tree's canonical Stage2 bin and
verify immutable stage provenance before and after native work. Without that
flag the surrounding build must perform those stage audits. Local checks also
bind the compiler to source HEAD and each receipt to the selected daemon bytes.
"""
import argparse
import ast
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile


EXPECTED_BODIES = {"lib": {"same_name::value"}, "bin": {"same_name::main"}}


def require(condition, message):
    # Qualification checks must survive -O and inherited PYTHONOPTIMIZE.
    if not condition:
        raise AssertionError(message)


def digest_file(path):
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def validate_report(admission, canonical, daemon_hash, source_commit, host):
    """Check external fixture facts, independently of the compiler's inventories."""
    require(admission["proof_report_hash"] == "sha256:" + hashlib.sha256(canonical).hexdigest(),
            "resource artifact does not bind the exact canonical report")
    require(admission["availability"] == "complete" and not admission["problems"],
            f"incomplete native admission report: {admission}")
    units = admission["units"]
    require(len(units) == len(EXPECTED_BODIES), "expected exactly the fixture lib and bin")
    targets = [unit["cargo_target"] for unit in units]
    encode = lambda target: json.dumps(target, sort_keys=True)
    require(sorted(map(encode, admission["expected_units"])) == sorted(map(encode, targets)),
            "declared and observed Cargo unit populations differ")
    require(len({target["unit_identity_sha256"] for target in targets}) == len(targets),
            "same-name lib and bin share a unit identity")
    identities = {}
    runs = set()
    grants = 0
    for unit in units:
        target = unit["cargo_target"]
        kinds = target["target_kinds"]
        require(len(kinds) == 1 and kinds[0] in EXPECTED_BODIES, "unexpected fixture target kind")
        kind = kinds[0]
        require(kind not in identities, "duplicate fixture target kind")
        require(target["package_name"] == "native-admission-fixture"
                and target["target_name"] == "same_name"
                and target["compile_mode"] == target["proof_unit_mode"] == "check"
                and target["proof_unit_role"] == "primary"
                and target["compile_target"] == host, "wrong fixture Cargo identity")
        for name in ("unit_identity_sha256", "semantics_sha256"):
            require(re.fullmatch(r"[0-9a-f]{64}", target[name]), f"invalid {name}")
        census = unit["census"]
        binding = census["binding"]
        require(census["complete"] and not census["problems"], "unit did not close")
        require(census["package_name"] == target["package_name"]
                and census["crate_name"] == target["target_name"], "wrong census package/crate")
        require(binding["unit_digest"] == target["unit_identity_sha256"]
                and binding["semantics_digest"] == target["semantics_sha256"]
                and binding["role"] == target["proof_unit_role"]
                and binding["target"] == target["compile_target"], "misbound unit census")
        require(re.fullmatch(r"[0-9a-f]{64}", binding["run_digest"]), "invalid run digest")
        runs.add(binding["run_digest"])
        roots = census["bodies"]
        require({body["function"] for body in roots} == EXPECTED_BODIES[kind]
                and len(roots) == len(EXPECTED_BODIES[kind]), "missing or wrong fixture body")
        body_key = lambda body: (body["function"], body["body_digest"])
        population = [body_key(body) for body in roots + census["auxiliary_bodies"]]
        require(len(set(population)) == len(population), "duplicate body inventory")
        attempts = census["attempts"]
        require(attempts and all(attempt["terminal"] for attempt in attempts),
                "missing or unclosed per-unit work")
        require({body_key(attempt["body"]) for attempt in attempts} == set(population),
                "work attempts do not cover the per-unit body inventory")
        for attempt in attempts:
            if attempt["outcome"]["state"] != "admitted":
                continue
            grants += 1
            grant = attempt["outcome"]["receipt"]["grant"]
            require(grant["bytes"] > 0 and grant["token"] > 0, "nonpositive native grant")
            work = grant["work"]
            require(work["work_digest"] == attempt["work_digest"]
                    and work["attempt"] == attempt["attempt"]
                    and work["run_digest"] == binding["run_digest"]
                    and work["unit_digest"] == binding["unit_digest"]
                    and work["semantics_digest"] == binding["semantics_digest"],
                    "grant does not belong to this run/unit/work")
            daemon = grant["authority"]["daemon"]
            require(daemon["executable_sha256"] == daemon_hash
                    and daemon["commit"] == source_commit, "grant came from another daemon build")
        # Compare each target separately; digest sets conceal a lib/bin swap.
        # The exact unit digest includes the fresh invocation nonce, and graph
        # indices are run-local. Neither belongs in the cross-run projection.
        identities[kind] = {key: value for key, value in target.items()
                            if key not in ("unit_identity_sha256", "proof_unit_index")}
    require(set(identities) == set(EXPECTED_BODIES), "missing fixture target")
    require(len(runs) == 1, "units do not belong to one fresh run")
    require(grants > 0, "positive native trustd receipt required, not only cache/skip rows")
    return next(iter(runs)), identities


def validate_runs(reports):
    require(len(reports) == 2, "two native runs required")
    require(reports[0][0] != reports[1][0], "verification run was reused")
    require(reports[0][1] == reports[1][1], "per-target descriptor or semantics changed between runs")


def run(argv, cwd, env):
    result = subprocess.run(argv, cwd=cwd, env=env, text=True, capture_output=True, timeout=1800)
    if result.returncode:
        raise AssertionError(f"{argv!r}: exit {result.returncode}\n{result.stdout}\n{result.stderr}")
    return result


def qualification_environment(source_root, verify_stage_provenance):
    env = dict(os.environ)
    if verify_stage_provenance:
        # Read the source policy as data; importing the build driver would execute it.
        keys = {"BUILD_AUTHORITY_ENV_NAMES", "BUILD_AUTHORITY_ENV_PREFIXES"}
        policy = {}
        driver = source_root / "scripts/recreate_bootstrap.py"
        for statement in ast.parse(driver.read_text()).body:
            if isinstance(statement, ast.Assign):
                for target in statement.targets:
                    if isinstance(target, ast.Name) and target.id in keys:
                        require(target.id not in policy, "duplicate build authority environment policy")
                        policy[target.id] = ast.literal_eval(statement.value)
        require(set(policy) == keys, "missing build authority environment policy")
        names = policy["BUILD_AUTHORITY_ENV_NAMES"]
        prefixes = policy["BUILD_AUTHORITY_ENV_PREFIXES"]
        require(isinstance(names, set) and all(isinstance(name, str) and name for name in names)
                and isinstance(prefixes, tuple)
                and all(isinstance(prefix, str) and prefix for prefix in prefixes),
                "invalid build authority environment policy")
        for name in list(env):
            if name in names or name.startswith(prefixes):
                del env[name]
    # Preserve the existing local-mode compiler override policy as well.
    for name in list(env):
        if name.startswith(("CARGO_", "RUSTC_", "TRUST_", "TRUSTD_")) or name in ("RUSTFLAGS", "RUSTC", "RUSTDOC"):
            del env[name]
    return env


def verify_stage_provenance(source_root, bindir, host, env):
    require(re.fullmatch(r"[A-Za-z0-9_.-]+", host) and host not in (".", ".."),
            "invalid compiler host")
    expected = (source_root / "build" / host / "stage2/bin").resolve(strict=True)
    require(bindir == expected, "provenance mode requires this source tree's canonical Stage2 bin")
    run([sys.executable, str(source_root / "scripts/recreate_bootstrap.py"),
         "--verify-stage-provenance", "--require-immutable-lineage", "--stage", "2",
         "--host", host], source_root, env)


def main(argv=None):
    parser = argparse.ArgumentParser()
    parser.add_argument("--bin", required=True, type=Path)
    parser.add_argument("--verify-stage-provenance", action="store_true",
                        help="require this tree's Stage2 bin and immutable provenance before and after native work")
    args = parser.parse_args(argv)
    bindir = args.bin.resolve(strict=True)
    for tool in ("trustc", "targo", "targo-trust", "trustd"):
        if not (bindir / tool).is_file():
            raise AssertionError(f"missing same-sysroot {tool}: {bindir}")
    source_root = Path(__file__).resolve().parents[2]
    env = qualification_environment(source_root, args.verify_stage_provenance)
    env["PATH"] = str(bindir) + os.pathsep + env.get("PATH", "")
    source_commit = run(["git", "rev-parse", "HEAD"], source_root, env).stdout.strip()
    require(not run(["git", "status", "--porcelain", "--untracked-files=no"],
                    source_root, env).stdout.strip(), "native qualification requires clean source")
    version = run([str(bindir / "trustc"), "-vV"], bindir, env).stdout
    identity = dict(line.split(": ", 1) for line in version.splitlines() if ": " in line)
    require(identity.get("commit-hash") == source_commit, "compiler does not match source HEAD")
    host = identity["host"]
    if args.verify_stage_provenance:
        verify_stage_provenance(source_root, bindir, host, env)
    tool_hashes = {tool: digest_file(bindir / tool)
                   for tool in ("trustc", "targo", "targo-trust", "trustd")}
    # The discriminator must run on the same binary used below.
    run([str(bindir / "targo"), "--unverified", "--version"], bindir, env)
    with tempfile.TemporaryDirectory(prefix="trust-native-admission-") as directory:
        root = Path(directory)
        (root / "src").mkdir()
        (root / "Cargo.toml").write_text('''[package]
name = "native-admission-fixture"
version = "0.1.0"
edition = "2021"
[lib]
name = "same_name"
[[bin]]
name = "same_name"
path = "src/main.rs"
''')
        (root / "src/lib.rs").write_text("pub fn value() -> u64 { 7 }\n")
        (root / "src/main.rs").write_text("fn main() {}\n")
        reports = []
        for number in range(2):
            destination = root / f"report-{number}"
            run([str(bindir / "targo"), "trust", "check", "--report-dir", str(destination)], root, env)
            admission = json.loads((destination / "compiler-admission.json").read_bytes())
            canonical = (destination / "report.json").read_bytes()
            reports.append(validate_report(admission, canonical, tool_hashes["trustd"],
                                           source_commit, host))
        validate_runs(reports)
        require(tool_hashes == {tool: digest_file(bindir / tool) for tool in tool_hashes},
                "selected native binaries changed during qualification")
        require(run(["git", "rev-parse", "HEAD"], source_root, env).stdout.strip() == source_commit,
                "source HEAD changed during qualification")
        require(not run(["git", "status", "--porcelain", "--untracked-files=no"],
                        source_root, env).stdout.strip(), "source changed during qualification")
        if args.verify_stage_provenance:
            verify_stage_provenance(source_root, bindir, host, env)
        print("native admission: two fresh joined runs, same-name units, positive receipts, terminal census")


if __name__ == "__main__":
    main()
