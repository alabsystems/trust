"""The exact629 bootstrap surface, never a current native-toolchain contract.

629 predates native --unverified, product identity fields and trustd's info
CLI. Its original source and actual producer custody must be authenticated
separately. These runtime observations cannot qualify a current package.
"""

from __future__ import annotations

import hashlib
import json
import math
import os
from pathlib import Path
import socket
import stat
import struct
import subprocess
import tempfile
import time

SOURCE = "629729f69eefb1cfe6ed766c6c01ee38aa7b0484"
CONTRACT = "trust.original629-bootstrap-surface.v1"


def require(condition, message):
    if not condition:
        raise ValueError(message)


def digest(path):
    h = hashlib.sha256()
    with path.open("rb") as stream:
        for data in iter(lambda: stream.read(2**20), b""):
            h.update(data)
    return h.hexdigest()


def remaining(deadline, maximum=30):
    require(math.isfinite(deadline), "historical probe has no finite original deadline")
    left = deadline - time.monotonic()
    require(left > 0, "original historical bootstrap deadline expired")
    return min(left, maximum)


def fields(output):
    result = {}
    for line in output.splitlines():
        key, sep, value = line.partition(": ")
        if sep:
            require(key not in result, "duplicate historical tool identity field")
            result[key] = value
    return result


def probe(path, arguments, env, deadline):
    if '__trust_source_loader__' in globals() and __trust_source_loader__.context is not None:
        live = __trust_source_loader__.context
        started = time.monotonic()
        child = live.observed.open_object_reader('historical-probe','seed_historical_surface.probe',
            [str(path),*arguments],Path.cwd(),env,maximum=65536,
            seconds=remaining(deadline),input_pipe=False)
        row = child.finish_observed_child()
        return {'argv':[str(path),*arguments], 'pid':row['pid'], 'returncode':row['returncode'],
                'started_monotonic':started,'completed_monotonic':time.monotonic(),
                'original_deadline_monotonic':deadline,
                'stdout':live.observed.read_output(row).decode('utf-8'),
                'stderr':live.observed.read_output(row,'stderr').decode('utf-8'),
                'sha256':child.spec['executable']['sha256'],'auxiliary_command':child.number,
                'scope_closed':False}
    before = digest(path)
    remaining(deadline)
    started = time.monotonic()
    process = subprocess.Popen([str(path), *arguments], env=env, stdin=subprocess.DEVNULL,
                               stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
    try:
        stdout, stderr = process.communicate(timeout=remaining(deadline))
    finally:
        if process.poll() is None:
            process.kill()
            process.wait(timeout=1)
        process.stdout.close()
        process.stderr.close()
    require(len(stdout) + len(stderr) <= 65536, "historical tool probe output exceeds its bound")
    require(digest(path) == before, "historical tool changed during its probe")
    return {"argv": [str(path), *arguments], "pid": process.pid, "returncode": process.returncode,
            "started_monotonic": started, "completed_monotonic": time.monotonic(),
            "original_deadline_monotonic": deadline,
            "stdout": stdout, "stderr": stderr, "sha256": before}


def candidate(root, host, version, env, deadline):
    require(version == "1.99.0" and host in ("aarch64-unknown-linux-gnu", "x86_64-unknown-linux-gnu"),
            "historical bootstrap contract cannot be generalized to another cohort")
    require(root.is_dir() and not root.is_symlink(), "historical sysroot must be an owned non-symlink directory")
    for name in ("trustc", "rustc", "targo", "cargo"):
        path = root / "bin" / name
        require(path.is_file() and not path.is_symlink() and os.access(path, os.X_OK)
                and path.resolve(strict=True).is_relative_to(root.resolve(strict=True)),
                "historical candidate entrypoint is not a contained regular executable")
    compiler = probe(root / "bin/trustc", ["-vV"], env, deadline)
    frontend = probe(root / "bin/targo", ["--version", "--verbose"], env, deadline)
    c, f = fields(compiler["stdout"]), fields(frontend["stdout"])
    require(compiler["returncode"] == frontend["returncode"] == 0
            and c.get("binary") == "trustc" and c.get("commit-hash") == SOURCE
            and c.get("host") == f.get("host") == host and c.get("release", "").startswith(version)
            and frontend["stdout"].startswith("targo ") and version in frontend["stdout"],
            "historical candidate is not the actual original native compiler/driver")
    # These fields did not exist in this source. Never fabricate them or use a
    # modern artifact merely because its Rust compatibility version matches.
    require("trust" not in c and "trust-repo-commit-hash" not in f,
            "historical surface unexpectedly carries another identity epoch")
    require(digest(root / "bin/rustc") == compiler["sha256"]
            and digest(root / "bin/cargo") == frontend["sha256"], "historical compatibility aliases differ")
    sysroot = probe(root / "bin/trustc", ["--print", "sysroot"], env, deadline)
    require(sysroot["returncode"] == 0 and Path(sysroot["stdout"].strip()).resolve(strict=True) == root.resolve(strict=True),
            "historical compiler escaped its installed sysroot")
    return {"contract": CONTRACT, "source_commit": SOURCE, "host": host,
            "compiler": compiler, "frontend": frontend, "sysroot": sysroot,
            "supports_modern_native_lane": False, "current_toolchain_qualification": False}


def json_object(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, "duplicate historical daemon status field")
        result[key] = value
    return result


def validate_status(value):
    counters = ("budget_bytes", "reserved_bytes", "free_bytes", "queue_depth",
                "granted_total", "released_total", "started_at")
    require(isinstance(value, dict) and set(value) == {"version", "active", *counters}
            and value["version"] == "trustd.status.v1"
            and all(type(value[k]) is int and 0 <= value[k] < 2**64 for k in counters)
            and value["budget_bytes"] > 0 and value["free_bytes"] == value["budget_bytes"]
            and all(value[k] == 0 for k in ("reserved_bytes", "queue_depth", "granted_total", "released_total"))
            and value["started_at"] > 0 and value["active"] == [],
            "historical private daemon returned an invalid or nonempty status")


def daemon(path, env, deadline):
    if '__trust_source_loader__' in globals() and __trust_source_loader__.context is not None:
        live = __trust_source_loader__.context
        endpoint = live.observed.root / ('daemon-' + str(live.observed.account.commands) + '.sock')
        child = live.observed.open_object_reader('historical-daemon','seed_historical_surface.daemon',
            [str(path),'--socket',str(endpoint)],Path.cwd(),env,maximum=65536,
            seconds=remaining(deadline),input_pipe=False)
        result = child.run_daemon_session(endpoint)
        status = json.loads(result['status_raw'],object_pairs_hook=json_object)
        validate_status(status)
        return {'argv':[str(path),'--socket',str(endpoint)],'sha256':child.spec['executable']['sha256'],
                'observations':{'pid':result['pid'],'uid':result['uid'],'gid':result['gid'],'status':status},
                'owned_child_reaped':result['child']['direct_reaped'],
                'scope_closed':False,'auxiliary_command':child.number,
                'current_identity_protocol':'unsupported','current_toolchain_qualification':False}
    require(hasattr(socket, "SO_PEERCRED"), "historical Linux daemon probe needs kernel peer credentials")
    remaining(deadline)
    before, observations = digest(path), {}
    process = None
    # A short fresh private path avoids Unix socket path truncation in deep
    # build directories. It never contacts a user's ambient coordinator.
    with tempfile.TemporaryDirectory(prefix="trust-root-daemon-", dir=Path("/tmp").resolve(strict=True)) as temporary:
        root = Path(temporary)
        sock = root / "endpoint.sock"
        require(stat.S_IMODE(root.stat().st_mode) == 0o700, "historical daemon endpoint is not private")
        with (root / "stdout").open("w+b") as out, (root / "stderr").open("w+b") as err:
            try:
                process = subprocess.Popen([str(path), "--socket", str(sock)], env=env,
                            stdin=subprocess.DEVNULL, stdout=out, stderr=err)
                endpoint = min(deadline, time.monotonic() + 30)
                while not sock.exists():
                    require(process.poll() is None, "historical daemon exited before binding")
                    remaining(endpoint)
                    time.sleep(.02)
                require(stat.S_ISSOCK(sock.lstat().st_mode) and sock.lstat().st_uid == os.geteuid(),
                        "historical daemon endpoint has another kind or owner")
                with socket.socket(socket.AF_UNIX, socket.SOCK_STREAM) as stream:
                    stream.settimeout(remaining(endpoint))
                    stream.connect(str(sock))
                    pid, uid, gid = struct.unpack("3i", stream.getsockopt(socket.SOL_SOCKET, socket.SO_PEERCRED, 12))
                    require(pid == process.pid and uid == os.geteuid(), "historical daemon peer is not the owned process")
                    stream.sendall(b"PING\nSTATUS\n")
                    with stream.makefile("rb") as incoming:
                        require(incoming.readline(16) == b"PONG\n", "historical daemon did not answer PING")
                        raw = incoming.readline(65537)
                        require(raw.endswith(b"\n") and len(raw) <= 65536, "historical daemon status exceeds its bound")
                        status = json.loads(raw, object_pairs_hook=json_object)
                        validate_status(status)
                        observations = {"pid": pid, "uid": uid, "gid": gid, "status": status}
                require(digest(path) == before, "historical daemon changed during its probe")
            finally:
                if process is not None and process.poll() is None:
                    process.terminate()
                    try:
                        process.wait(timeout=max(.01, min(2, deadline - time.monotonic())))
                    except subprocess.TimeoutExpired:
                        process.kill()
                        process.wait(timeout=1)
                require(process is None or process.poll() is not None, "historical daemon child did not retire")
    return {"argv": [str(path), "--socket", str(sock)],
            "sha256": before, "observations": observations, "owned_child_reaped": True,
            "current_identity_protocol": "unsupported", "current_toolchain_qualification": False}


def native_tools(root, tools, host, version, env, deadline):
    identity = candidate(root, host, version, env, deadline)
    hashes, probes = {}, {}
    for name in tools:
        path = root / name
        require(path.is_file() and not path.is_symlink() and os.access(path, os.X_OK),
                "historical native surface is missing a regular executable: " + name)
        hashes[name] = digest(path)
        if name == "bin/trustd":
            probes[name] = daemon(path, env, deadline)
        elif name == "libexec/trust-analyzer-proc-macro-srv":
            probes[name] = {"scope": "shape-only; original stdio protocol has no info CLI"}
        elif name not in ("bin/trustc", "bin/rustc", "bin/targo", "bin/cargo"):
            attempts = []
            for arguments in (["--version"], ["-V"], ["--help"]):
                row = probe(path, arguments, env, deadline)
                attempts.append(row)
                if row["returncode"] == 0 and (row["stdout"] or row["stderr"]):
                    break
            require(attempts[-1]["returncode"] == 0 and (attempts[-1]["stdout"] or attempts[-1]["stderr"]),
                    "historical native tool did not answer a bounded original probe: " + name)
            probes[name] = attempts
    require(digest(root / "bin/trustdoc") == digest(root / "bin/rustdoc"), "historical documentation aliases differ")
    require(all(digest(root / p) == sha for p, sha in hashes.items()), "historical native tools changed during probes")
    remaining(deadline)
    return {"schema": "trust.genesis-native-tools.v1", "passed": True, "contract": CONTRACT,
            "host": host, "source_commit": SOURCE, "tools": hashes, "probes": probes,
            "candidate_identity": identity, "current_toolchain_qualification": False,
            "supports_modern_native_lane": False}


def installed_seed(root, host, version, env, deadline, support):
    identity = candidate(root, host, version, env, deadline)
    names = ("trustc", "rustc", "trustdoc", "targo", "cargo", "trustfmt")
    entrypoints = {}
    for name in names:
        path = root / "bin" / name
        require(path.is_file() and not path.is_symlink() and os.access(path, os.X_OK),
                "historical installed seed is missing a regular executable: " + name)
        entrypoints[name] = digest(path)
    formatter = probe(root / "bin/trustfmt", ["--version"], env, deadline)
    require(formatter["returncode"] == 0 and formatter["stdout"].strip(), "historical seed formatter does not run")
    for base, directories, files in os.walk(root, followlinks=False):
        for name in directories + files:
            path = Path(base) / name
            if path.is_symlink():
                require(path.resolve(strict=True).is_relative_to(root.resolve(strict=True)),
                        "historical installed seed contains an outbound link")
    records = support.tree_records(root, "actual historical installed seed")
    remaining(deadline)
    return {"schema": "trust-self-host-seed-surface-v1", "host": host, "source_version": version,
            "bootstrap_contract": CONTRACT, "current_toolchain_qualification": False,
            "entrypoint_sha256": entrypoints, "historical_identity": identity,
            "tool_versions": {"trustc": identity["compiler"]["stdout"], "targo": identity["frontend"]["stdout"],
                              "trustfmt": formatter["stdout"]},
            "tree": {"sha256": support.records_sha256(records), "records": records}}
