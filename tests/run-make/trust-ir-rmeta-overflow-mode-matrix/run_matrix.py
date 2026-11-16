#!/usr/bin/env python3
"""Bounded canonical schema-5 protocol/custody matrix; never builds an SDK.

Execution requires Root's matching fresh compiler/std/private closure and build
receipt. --plan prepares an explicitly NOT RUN record without those inputs.
"""
from pathlib import Path
import argparse
import hashlib
import json
import os
import re
import shutil
import subprocess
import time

_TRANSPORT_NAMES = {"CARGO_MAKEFLAGS", "MAKEFLAGS", "MFLAGS", "CARGO_JOBSERVER_HANDOFF"}
_TRANSPORT_OPAQUE = {"CARGO_JOBSERVER_HANDOFF", "TRUST_CPU_HANDOFF", "ATERM_SDK_LEASE_V3"}
def _transport_key(key):
    return key in _TRANSPORT_NAMES or key.startswith(("BUILD_SLOT_", "HEAVY_GATE_", "TRUST_CPU_", "ATERM_SDK_")) or key == "CARGO_BUILD_JOBS"
def _with_live_transport(environment):
    # Historical receipt bytes do not restore a live owner. Replace only old
    # context with this invocation's actual context; never strip actual markers.
    result = {k: v for k, v in environment.items() if not _transport_key(k)}
    result.update({k: v for k, v in os.environ.items() if _transport_key(k)})
    return result
def _record_environment(environment):
    return {k: ("<live-capability-sha256:" + hashlib.sha256(v.encode()).hexdigest() + ">" if k in _TRANSPORT_OPAQUE else v) for k, v in environment.items()}

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[2]
PROBE = REPO / "crates/trust-thir-lower/probes/rmeta_overflow_mode.rs"
PROTOCOL = "d1c4dfcde4a39f7e5117be4304090e4dffb449e3"
GUARD = "7e98e8115cde1c5205b646f195e5537b652c6900"


def digest(path):
    hashed = hashlib.sha256()
    with Path(path).open("rb") as stream:
        for block in iter(lambda: stream.read(1 << 20), b""):
            hashed.update(block)
    return hashed.hexdigest()


def write(path, value):
    Path(path).write_text(json.dumps(value, indent=2) + "\n")


def mode(value):
    return "on" if value else "off"


def output(argv, cwd=None, env=None):
    result = subprocess.run(argv, cwd=cwd, env=env, text=True,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    if result.returncode:
        raise RuntimeError(f"command failed ({result.returncode}): {argv!r}\n{result.stdout}")
    return result.stdout


def manifest(path, package, source, *, binary=False):
    path.parent.mkdir(parents=True, exist_ok=True)
    target = "[[bin]]\nname=\"mode-observer\"" if binary else "[lib]\nname=\"mode_user\""
    if package.startswith("mode-producer"):
        target = "[lib]\nname=\"mode_dep\""
    path.write_text(f'[package]\nname={json.dumps(package)}\nversion="0.1.0"\nedition="2021"\n'
                    f'{target}\npath={json.dumps(str(source))}\n[workspace]\n'
                    '[profile.dev]\ndebug=0\nincremental=false\n')


def channel_rows(stderr, producer, consumer):
    found = {}
    for name in ["mix", "identity", "inherited"]:
        rows = [line for line in stderr.splitlines()
                if line.startswith("TRUST-WALLA-PROBE C sym=")
                and f" def=mode_dep::{name} " in line]
        if len(rows) != 1:
            raise AssertionError(f"one actual channel-C row required for {name}: {rows!r}")
        row = rows[0]
        if name == "inherited":
            expected = "rmeta=absent(inherited-overflow-checks)"
        elif producer == consumer:
            expected = "rmeta=entry(digest-ok,functions=1,"
        else:
            expected = ("rmeta=entry-refused(overflow-check-mode("
                        f"producer_{str(producer).lower()},_consumer_{str(consumer).lower()}))")
        if expected not in row:
            raise AssertionError(f"expected {expected!r} in actual row {row!r}")
        found[name] = row
    return found


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--plan", action="store_true")
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--sdk-root", type=Path,
                        help="completed native build root containing stage0, stage1 and stage1-rustc")
    parser.add_argument("--compiler-source", type=Path)
    parser.add_argument("--compiler-commit", help="actual full commit reported by supplied trustc -vV")
    parser.add_argument("--guard-commit", default=GUARD, help="additional expected guard ancestor; exact known guard is always required")
    parser.add_argument("--build-receipt", type=Path, help="Root's immutable actual SDK build/qualification record")
    args = parser.parse_args()
    args.out = args.out.resolve()
    if args.compiler_source is not None:
        args.compiler_source = args.compiler_source.resolve()
    if args.build_receipt is not None:
        args.build_receipt = args.build_receipt.resolve()
    if args.out.exists():
        parser.error("--out must be a fresh owned path; previous evidence is never replaced")
    args.out.mkdir(parents=True)
    sources = {str(p): digest(p) for p in
               [HERE / "producer.rs", HERE / "consumer.rs", HERE / "rmake.rs", Path(__file__), PROBE]}
    record = {"schema": "trust.schema5.overflow-mode-matrix.v1", "status": "PREPARED_NOT_RUN",
              "protocol_commit": PROTOCOL, "required_guard_commit": GUARD, "source_files": sources, "cells": [], "steps": [],
              "expected": {"producer_sessions": 2, "canonical_consumer_sessions": 4,
                           "read_only_consumer_sessions": 4, "cells": 4,
                           "required_R_rows_per_cell": 2, "named_no_entry_rows_per_cell": 1},
              "scope": "Protocol/custody only. No F1 admission, selected trust-cg backend, execution, ABI/NoUB or proof authority."}
    write(args.out / "MATRIX.json", record)
    if args.plan:
        record["reason"] = "Requires Root's matching fresh schema5 compiler/std/private closure ; exact inherited-overflow guard is already bound. No compilation or matrix execution."
        write(args.out / "MATRIX.json", record)
        return
    required = ["sdk_root", "compiler_source", "compiler_commit", "guard_commit", "build_receipt"]
    if any(getattr(args, key) is None for key in required):
        parser.error("execution requires --sdk-root, --compiler-source, --compiler-commit, --guard-commit and --build-receipt")
    if os.environ.get("BUILD_SLOT_HELD") != "1":
        parser.error("execute through build-slot; this runner starts no SDK build or background worker")
    record["status"] = "RUNNING"
    started = time.time()
    try:
        for commit in [args.compiler_commit, args.guard_commit]:
            if not re.fullmatch(r"[0-9a-f]{40}", commit):
                raise ValueError("full immutable source commits required")
        actual_source = output(["git", "rev-parse", "HEAD"], cwd=args.compiler_source).strip()
        if actual_source != args.compiler_commit:
            raise AssertionError("compiler source checkout must name the exact supplied SDK commit")
        for ancestor in dict.fromkeys([PROTOCOL, GUARD, args.guard_commit]):
            output(["git", "merge-base", "--is-ancestor", ancestor, args.compiler_commit], cwd=args.compiler_source)
        protected = args.compiler_source / "crates/trust-thir-lower/src/rmeta_entry.rs"
        if not re.search(r"pub const ENTRY_SCHEMA:\s*u32\s*=\s*5\s*;", protected.read_text()):
            raise AssertionError("source is not the schema5 protocol")
        if output(["git", "status", "--porcelain", "--untracked-files=no"], cwd=args.compiler_source).strip():
            raise AssertionError("matching compiler source must have no tracked edits")
        sdk = args.sdk_root.resolve()
        compiler = sdk / "stage1/bin/trustc"
        version = output([str(compiler), "-vV"])
        if f"commit-hash: {args.compiler_commit}\n" not in version:
            raise AssertionError("actual compiler identity differs; old SDKs are not relabelled")
        host = next(line.removeprefix("host: ") for line in version.splitlines() if line.startswith("host: "))
        candidates = [sdk / "stage1/bin/targo", sdk / f"stage1-tools-bin/{host}/targo"]
        targo = next((p for p in candidates if p.is_file()), None)
        if targo is None:
            raise AssertionError("provided completed SDK needs its genuine Targo")
        targo_version = output([str(targo), "--unverified", "--version"])
        if not targo_version.startswith("targo "):
            raise AssertionError("not genuine Targo")
        deps = sdk / f"stage1-rustc/{host}/release/deps"
        host_deps = sdk / "stage1-rustc/release/deps"
        drivers = list((sdk / "stage1/lib").glob("librustc_driver-*.dylib"))
        private_drivers = list(deps.glob("librustc_driver-*.dylib"))
        if len(drivers) != 1 or len(private_drivers) != 1 or digest(drivers[0]) != digest(private_drivers[0]):
            raise AssertionError("canonical compiler and supplied private driver closure must match")
        record["SDK"] = {"root": str(sdk), "source": str(args.compiler_source),
                         "commit": args.compiler_commit, "guard_commit": args.guard_commit,
                         "compiler_sha256": digest(compiler), "driver_sha256": digest(drivers[0]),
                         "compiler_version": version, "targo": str(targo), "targo_sha256": digest(targo),
                         "targo_version": targo_version, "source_rmeta_sha256": digest(protected),
                         "build_receipt": str(args.build_receipt), "build_receipt_sha256": digest(args.build_receipt)}
        env = _with_live_transport({key: os.environ[key] for key in ["HOME", "LANG"] if key in os.environ})
        env.update(PATH=str(targo.parent) + ":/usr/bin:/bin:/usr/sbin:/sbin",
                   CARGO_HOME=str(args.out / "cargo-home"), CARGO_INCREMENTAL="0",
                   RUST_MIN_STACK="134217728", RUSTC=str(compiler),
                   DYLD_LIBRARY_PATH=":".join(map(str, [deps, sdk / "stage0/lib", sdk / "stage1/lib"])))
        env.update({key: value for key, value in os.environ.items()
                    if key.startswith("BUILD_SLOT_") or key == "CARGO_BUILD_JOBS"})

        def run(label, manifest_path, target, flags, *, rustc=compiler, extra_env=None):
            target.mkdir(parents=True)
            job_env = dict(env, RUSTC=str(rustc), CARGO_TARGET_DIR=str(target),
                           CARGO_ENCODED_RUSTFLAGS="\x1f".join(flags))
            job_env.update(extra_env or {})
            argv = [str(targo), "--unverified", "build", "--offline", "--manifest-path", str(manifest_path)]
            step = {"label": label, "argv": argv, "environment": _record_environment(job_env), "started": time.time()}
            record["steps"].append(step)
            write(args.out / "MATRIX.json", record)
            with (args.out / f"{label}.stdout").open("w") as out, (args.out / f"{label}.stderr").open("w") as err:
                result = subprocess.run(argv, cwd=args.out, env=job_env, stdout=out, stderr=err)
            step.update(exit=result.returncode, seconds=time.time() - step["started"])
            if result.returncode:
                raise RuntimeError(f"{label} failed; raw evidence retained")

        # Real SDK private libraries only; never a source-model decoder substitute.
        private_flags = ["-C", "prefer-dynamic", "--sysroot", str(sdk / "stage0"),
                         "-L", "dependency=" + str(deps), "-L", "dependency=" + str(host_deps)]
        private_inputs = {}
        for name in ["rustc_driver", "rustc_data_structures", "rustc_interface", "rustc_middle", "rustc_span", "trust_thir_lower", "trust_ir", "serde_json"]:
            for extension in ["rmeta", "dylib", "rlib"]:
                paths = list(deps.glob(f"lib{name}-*.{extension}"))
                if not paths:
                    continue
                if len(paths) != 1:
                    raise AssertionError(f"ambiguous SDK private input: {name}/{extension}")
                path = paths[0]
                private_flags += ["--extern", name + "=" + str(path)]
                private_inputs[str(path)] = digest(path)
                if extension == "dylib":
                    break
            if not any(Path(p).name.startswith("lib" + name + "-") for p in private_inputs):
                raise AssertionError(f"missing actual SDK private library: {name}")
        record["private_inputs"] = private_inputs
        probe_manifest = args.out / "probe/Cargo.toml"
        manifest(probe_manifest, "mode-matrix-observer", PROBE, binary=True)
        run("probe-build", probe_manifest, args.out / "probe-target.noindex", private_flags,
            rustc=sdk / "stage0/bin/trustc")
        observer = args.out / "probe-target.noindex/debug/mode-observer"
        record["observer_sha256"] = digest(observer)
        preserved = {}
        for producer in [False, True]:
            producer_manifest = args.out / f"producer-{mode(producer)}/Cargo.toml"
            manifest(producer_manifest, f"mode-producer-{mode(producer)}", HERE / "producer.rs")
            producer_target = args.out / f"producer-{mode(producer)}-target.noindex"
            run(f"producer-{mode(producer)}", producer_manifest, producer_target,
                ["--sysroot", str(sdk / "stage1"), "-Copt-level=0",
                 f"-Coverflow-checks={mode(producer)}", "-Ztrust-ir-lower"])
            library = producer_target / "debug/libmode_dep.rlib"
            for consumer in [False, True]:
                label = f"p-{mode(producer)}-c-{mode(consumer)}"
                consumer_manifest = args.out / label / "Cargo.toml"
                manifest(consumer_manifest, "mode-user-" + label, HERE / "consumer.rs")
                flags = ["--sysroot", str(sdk / "stage1"), "-Copt-level=0", "-Ccodegen-units=1",
                         f"-Coverflow-checks={mode(consumer)}", "--extern", "mode_dep=" + str(library)]
                run(label + "-canonical", consumer_manifest, args.out / (label + "-canonical-target.noindex"),
                    flags + ["-Ztrust-ir-lower", "-Ztrust-instance-flip-probe=*"])
                diagnostics = channel_rows((args.out / (label + "-canonical.stderr")).read_text(), producer, consumer)
                observed = args.out / label / "reader"
                run(label + "-observer", consumer_manifest, args.out / (label + "-observer-target.noindex"), flags,
                    rustc=observer, extra_env={"MODE_MATRIX_PRODUCER": mode(producer),
                        "MODE_MATRIX_CONSUMER": mode(consumer), "MODE_MATRIX_OUT": str(observed),
                        "MODE_MATRIX_SYSROOT": str(sdk / "stage1")})
                rows = json.loads((observed / "ALL.json").read_text())
                if len(rows) != 3:
                    raise AssertionError("complete three-row observed population required")
                for subject in ["mix", "identity"]:
                    blob = (observed / (subject + ".entry")).read_bytes()
                    key = (producer, subject)
                    if key in preserved and preserved[key] != blob:
                        raise AssertionError("consumer must not repair or rewrite producer bytes")
                    preserved[key] = blob
                record["cells"].append({"producer": producer, "consumer": consumer,
                    "producer_library_sha256": digest(library), "canonical_diagnostics": diagnostics,
                    "observer_rows": rows, "reader_record": str(observed / "ALL.json")})
        if len(record["cells"]) != 4:
            raise AssertionError("all four actual mode cells required")
        if not all(digest(path) == value for path, value in private_inputs.items()):
            raise AssertionError("SDK private inputs changed during matrix")
        if not all(digest(path) == value for path, value in sources.items()):
            raise AssertionError("fixture source changed during matrix")
        record["status"] = "PASS_PROTOCOL_CUSTODY_ONLY"
    except Exception as error:
        record.update(status="FAILED", error=str(error))
        raise
    finally:
        record["seconds"] = time.time() - started
        write(args.out / "MATRIX.json", record)


if __name__ == "__main__":
    main()
