#!/usr/bin/env python3
"""Actual-compiler control for the unencoded deferred offload-check surface.

Run after building stage1/stage2, with TRUST_WITNESS_TRUSTC selecting that exact
compiler. Metadata-only device compilation needs no GPU/toolkit or device codegen.
The neighboring plain kernel must mint/replay, while its valid offload caller must
not mint. Exercise both solvers: a coherence run catches this guard independently
of the next solver's pending diagnostic goals. Preserve errors on an invalid call.
"""
import glob
import hashlib
import os
from pathlib import Path
import re
import shutil
import subprocess

ROOT = Path(__file__).resolve().parents[2]
TRUSTC = os.environ.get("TRUST_WITNESS_TRUSTC")
if not TRUSTC or not Path(TRUSTC).is_file():
    raise SystemExit("set TRUST_WITNESS_TRUSTC to the actual matching Trust compiler")
WORK = ROOT / "build" / "trust-witness-offload-regression"
FIXTURE = ROOT / "tests" / "trust-witness" / "fixtures" / "offload.rs"
BASE = ["--crate-type=lib", "--edition=2021", "--emit=metadata", "-Zthreads=1",
        "-Ztrust-verify=off", "-Zunstable-options", "-Zoffload=Device", "-Clto=fat"]


def run(src, out, solver, store=None, stats=False):
    out.mkdir(parents=True)
    env = dict(os.environ)
    if stats:
        env["TRUST_WITNESS_STATS"] = "1"
    cmd = [TRUSTC, *BASE, *solver, "--out-dir", str(out),
           "-Ztrust-witness=" + (store or "off"), str(src)]
    result = subprocess.run(cmd, capture_output=True, text=True, env=env)
    out.with_suffix(".stdout").write_text(result.stdout)
    out.with_suffix(".stderr").write_text(result.stderr)
    return result


def normalized(stderr):
    return "\n".join(line for line in stderr.splitlines()
                     if not line.startswith("TRUST_REPLAY "))


def digests(out):
    return [hashlib.sha256(Path(p).read_bytes()).hexdigest()
            for p in sorted(glob.glob(str(out / "*.rmeta")))]


shutil.rmtree(WORK, ignore_errors=True)
for name, solver in [("coherence", ["-Znext-solver=coherence"]), ("next", [])]:
    work = WORK / name
    store = work / "store"
    cold = run(FIXTURE, work / "cold", solver, "mint:" + str(store))
    warm = run(FIXTURE, work / "warm", solver, "replay:" + str(store), stats=True)
    off = run(FIXTURE, work / "off", solver)
    assert cold.returncode == warm.returncode == off.returncode == 0, (cold, warm, off)
    assert normalized(cold.stderr) == normalized(warm.stderr) == normalized(off.stderr)
    assert digests(work / "cold") == digests(work / "warm") == digests(work / "off")
    assert len(digests(work / "off")) == 1
    stores = list(store.glob("*.twit"))
    assert len(stores) == 1
    packed = stores[0].read_bytes()
    assert packed[:8] == b"TWSTORE2"
    # Exactly the plain kernel is mintable. Before the offloads guard, coherence
    # minted BOTH roots, so a failure to mint anything cannot pass this control.
    assert int.from_bytes(packed[8:12], "little") == 1, "deferred offload state was omitted"
    assert re.search(r"^TRUST_REPLAY ACCEPT .*::kernel\)", warm.stderr, re.M), warm.stderr
    assert not re.search(r"^TRUST_REPLAY ACCEPT .*::offload_u32\)", warm.stderr, re.M)
    assert re.search(r"^TRUST_REPLAY MISS-source-offload .*::offload_u32\)", warm.stderr, re.M)

    # A real deferred-check error must remain an error, without minting a store.
    invalid = work / "invalid.rs"
    invalid.write_text(FIXTURE.read_text().replace("(x,))", "(f64::from(x),))"))
    bad_store = work / "bad-store"
    bad_mint = run(invalid, work / "bad-mint", solver, "mint:" + str(bad_store))
    bad_warm = run(invalid, work / "bad-warm", solver, "replay:" + str(bad_store), stats=True)
    bad_off = run(invalid, work / "bad-off", solver)
    assert bad_mint.returncode == bad_warm.returncode == bad_off.returncode != 0
    assert "type mismatch in offload kernel argument" in bad_off.stderr
    assert normalized(bad_mint.stderr) == normalized(bad_warm.stderr) == normalized(bad_off.stderr)
    assert not list(bad_store.glob("*.twit")), "an erroneous crate committed a witness"
    assert "TRUST_REPLAY ACCEPT" not in bad_warm.stderr
    print(f"PASS {name}: deferred offload refused; kernel ACCEPT; metadata identical; invalid call refused")
