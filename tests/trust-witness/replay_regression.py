#!/usr/bin/env python3
"""Durable regression harness for the typeck-witness warm-replay lane.

Unlike the session-scratchpad probe, this is repo-relative and checked in: it
drives the stage2 `trustc` over a fixture per confirmed soundness/fail-safe bug
family (2026-07-22 audit) plus a positive case, and asserts the same-answers +
fail-safe contract. Run after `x.py build --stage 2`:

    TRUST_SEED_STAIRCASE=1 python3 tests/trust-witness/replay_regression.py

Contract per fixture:
  * same-answers: warm replay's emitted rmeta+obj are BYTE-IDENTICAL to a
    no-flag build, and replay's exit code matches no-flag (so an ICE or a
    diverging codegen both fail the test);
  * positive (pos_method): the root's method/operator picks ACCEPT on replay;
  * each bug family (extern_c_fnptr rank1, offset_of rank3, child_pick rank2):
    the named at-risk root must NOT be ACCEPTed (it must MISS -> real typeck),
    and the compile must not ICE;
  * child_plain: a child body with no pick also must MISS, because all of its
    TypeckResults maps are outside the single-body checker's coverage;
  * transmute: an omitted cold-only TypeckResults surface must block minting;
  * warning_unreachable: a root that emits a typeck warning must not mint,
    because replay does not serialize diagnostics;
  * expect_unreachable: a root that silently fulfills a lint expectation must
    not mint, because replay does not serialize fulfilled-expectation state;
  * borrow_bad: replay reproduces the identical borrow error and non-zero exit.
"""
import subprocess, os, sys, hashlib, glob, re, shutil

REPO = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", ".."))
TRUSTC = os.environ.get(
    "TRUST_WITNESS_TRUSTC",
    os.path.join(REPO, "build", "host", "stage2", "bin", "trustc"),
)
FIX = os.path.join(REPO, "tests", "trust-witness", "fixtures")
WORK = os.path.join(REPO, "build", "trust-witness-regression")

# Pin the auto lane OFF so this suite exercises the EXPLICIT mint/replay flags
# deterministically; the managed (default-on, router-gated) lane is covered
# separately by auto_router_smoke.py.
BASE = ["-Zthreads=1", "-Ztrust-verify=off", "--edition", "2021",
        "--crate-type=lib", "--emit=metadata,obj", "-Ztrust-witness=off"]


def run(args, outdir, store_flag=None, stats=False):
    os.makedirs(outdir, exist_ok=True)
    env = dict(os.environ)
    env["TRUST_SEED_STAIRCASE"] = "1"
    if stats:
        env["TRUST_WITNESS_STATS"] = "1"
    cmd = [TRUSTC] + BASE + (["--out-dir", outdir])
    if store_flag:
        cmd.append(store_flag)
    cmd.append(src)
    return subprocess.run(cmd, capture_output=True, text=True, env=env)


def digests(outdir):
    d = {}
    for ext in ("rmeta", "o"):
        fs = sorted(glob.glob(os.path.join(outdir, f"*.{ext}")))
        d[ext] = [hashlib.sha256(open(f, "rb").read()).hexdigest() for f in fs]
    return d


def norm(stderr):
    # Strip absolute paths so a diff reflects the diagnostic, not the CWD, and
    # drop the env-gated `TRUST_REPLAY ...` census lines (debug instrumentation
    # that only the stats-enabled replay run emits — not compiler output).
    lines = [l for l in stderr.splitlines() if not l.startswith("TRUST_REPLAY ")]
    return re.sub(r"/[^\s:]+/", "", "\n".join(lines))


def accepted_roots(stderr):
    return set(re.findall(r"TRUST_REPLAY ACCEPT DefId\([^)]*::(\w+)\)", stderr))


def _entry_digest(key_bytes, payload):
    """Python mirror of store.rs `entry_digest` (FNV-1a/64 over key || payload)."""
    h = 0xCBF29CE484222325
    for b in bytes(key_bytes) + bytes(payload):
        h ^= b
        h = (h * 0x100000001B3) & 0xFFFFFFFFFFFFFFFF
    return h


def corrupt_all_first_node_ids(store_dir, refresh_digest=True):
    """Set each payload's first node HirId to u32::MAX, preserving framing.

    Store format TWSTORE2: each entry is `key_len(u16) key payload_len(u32) payload
    digest(u64)`. With ``refresh_digest=True`` the trailing per-entry digest is
    recomputed so the corruption passes the load-time integrity check and reaches
    the DECODE boundary (exercises decode rejection). With ``refresh_digest=False``
    the stale digest makes `store::unpack` DROP the entry at load (exercises the
    per-entry checksum layer -> clean per-root MISS)."""
    stores = glob.glob(os.path.join(store_dir, "*.twit"))
    if len(stores) != 1:
        raise RuntimeError(f"expected one packed store, found {len(stores)}")
    path = stores[0]
    data = bytearray(open(path, "rb").read())
    if data[:8] != b"TWSTORE2":
        raise RuntimeError("unexpected store magic")
    nentries = int.from_bytes(data[8:12], "little")
    off = 12
    changed = 0
    for _ in range(nentries):
        key_start = off + 2
        key_len = int.from_bytes(data[off:off + 2], "little")
        key = bytes(data[key_start:key_start + key_len])
        off = key_start + key_len
        payload_len = int.from_bytes(data[off:off + 4], "little")
        off += 4
        payload_start = off
        payload_end = off + payload_len
        if data[off:off + 4] != b"TWV1":
            raise RuntimeError("unexpected witness magic")
        cursor = off + 4
        ntypes = int.from_bytes(data[cursor:cursor + 4], "little")
        cursor += 4
        for _ in range(ntypes):
            ty_len = int.from_bytes(data[cursor:cursor + 2], "little")
            cursor += 2 + ty_len
        nnodes = int.from_bytes(data[cursor:cursor + 4], "little")
        cursor += 4
        if nnodes:
            data[cursor:cursor + 4] = b"\xff\xff\xff\xff"
            changed += 1
        if refresh_digest:
            new_d = _entry_digest(key, data[payload_start:payload_end])
            data[payload_end:payload_end + 8] = new_d.to_bytes(8, "little")
        off = payload_end + 8  # skip the per-entry digest
    if off != len(data) or changed == 0:
        raise RuntimeError("packed store framing mismatch or no node IDs to corrupt")
    with open(path, "wb") as f:
        f.write(data)


# fixture -> (at_risk_root_that_must_not_accept | None, expect_error)
CASES = {
    "pos_method":     (None,     False),   # positive: picks must ACCEPT
    # rank 1 was conservatively ESCAPED at lock-in; scope widening (schema v5)
    # round-trips the fn-ptr ABI, so the extern-"C" fn-ptr root is re-admitted and
    # must now ACCEPT byte-identically (positive).
    "extern_c_fnptr": (None,     False),
    "offset_of":      ("off_b",  False),   # rank 3 (still MISS: offset_of_data excluded at mint)
    # forest-check increment 1: inline-const child bodies are now WALKED + re-derived,
    # so these flip from must-MISS bug families to positives that ACCEPT byte-identical.
    "child_pick":     (None,     False),   # inline-const child method pick re-derived
    "child_plain":    (None,     False),   # inline-const child (no pick) validated
    "closure_root":   ("g",      False),   # forest predicate: a CLOSURE child => MISS (captures = later increment)
    "transmute":      ("transmute_u32", False),  # omitted cold-only field
    "warning_unreachable": ("warns", False),  # typeck diagnostic side effect
    "expect_unreachable": ("fulfills_expectation", False),  # suppressed expectation
    "borrow_bad":     (None,     True),    # fail-safe: identical error
}

EXPECT_EMPTY_STDERR = {"expect_unreachable"}

fails = []
for name, (at_risk, expect_error) in CASES.items():
    src = os.path.join(FIX, f"{name}.rs")
    store = os.path.join(WORK, name, "store")
    mint_dir = os.path.join(WORK, name, "mint")
    noflag_dir = os.path.join(WORK, name, "noflag")
    replay_dir = os.path.join(WORK, name, "replay")
    for path in (store, mint_dir, noflag_dir, replay_dir):
        shutil.rmtree(path, ignore_errors=True)
    mint = run(BASE, mint_dir,
               store_flag=f"-Ztrust-witness=mint:{store}")
    noflag = run(BASE, noflag_dir)
    replay = run(BASE, replay_dir,
                 store_flag=f"-Ztrust-witness=replay:{store}", stats=True)

    probs = []
    # same-answers: both mint and replay match no-flag diagnostics, exit, and
    # (for successful compilations) emitted artifacts.
    if mint.returncode != noflag.returncode:
        probs.append(f"mint exit {mint.returncode} != no-flag {noflag.returncode}")
    if replay.returncode != noflag.returncode:
        probs.append(f"exit {replay.returncode} != no-flag {noflag.returncode} (ICE/divergence?)")
    if norm(mint.stderr) != norm(noflag.stderr):
        probs.append("mint stderr differs from no-flag")
    if norm(replay.stderr) != norm(noflag.stderr):
        probs.append("replay stderr differs from no-flag (diagnostic masked/changed)")
    if name in EXPECT_EMPTY_STDERR and norm(noflag.stderr).strip():
        probs.append("no-flag build did not silently fulfill its lint expectation")
    if not expect_error:
        baseline_digests = digests(noflag_dir)
        if baseline_digests != digests(mint_dir):
            probs.append("mint rmeta/obj NOT byte-identical to no-flag")
        if baseline_digests != digests(replay_dir):
            probs.append("replay rmeta/obj NOT byte-identical to no-flag (miscompile)")
    if expect_error:
        if replay.returncode == 0:
            probs.append("expected a compile error, replay exited 0")
    else:
        acc = accepted_roots(replay.stderr)
        if at_risk is None and not acc:
            probs.append("positive fixture minted no ACCEPT (picks not replayed)")
        if at_risk is not None and at_risk in acc:
            probs.append(f"at-risk root `{at_risk}` wrongly ACCEPTed (soundness hole open)")

    status = "PASS" if not probs else "FAIL"
    print(f"  {status}  {name}: {'; '.join(probs) if probs else 'same-answers + fail-safe hold'}")
    if probs:
        fails.append(name)

# A witness-supplied ItemLocalId used to reach rustc HIR indexing before any
# panic boundary. Corrupt every positive payload while keeping the packed
# framing valid: replay must reject during decode, transparently fall back, and
# produce the exact no-flag artifacts without an ICE diagnostic.
name = "corrupt_local_id"
src = os.path.join(FIX, "pos_method.rs")
store = os.path.join(WORK, "pos_method", "store")
probs = []
try:
    corrupt_all_first_node_ids(store)
    replay = run(BASE, os.path.join(WORK, name, "replay"),
                 store_flag=f"-Ztrust-witness=replay:{store}", stats=True)
    if replay.returncode != 0:
        probs.append(f"replay exited {replay.returncode} (corrupt ID caused an ICE/error)")
    if digests(os.path.join(WORK, "pos_method", "noflag")) != \
            digests(os.path.join(WORK, name, "replay")):
        probs.append("fallback artifacts differ from no-flag")
    if accepted_roots(replay.stderr):
        probs.append("a payload with an invalid HIR ID was ACCEPTed")
    if "MISS-decode" not in replay.stderr:
        probs.append("invalid HIR ID was not rejected at the decode boundary")
except (OSError, RuntimeError) as e:
    probs.append(str(e))

status = "PASS" if not probs else "FAIL"
print(f"  {status}  {name}: {'; '.join(probs) if probs else 'decode rejection + transparent fallback hold'}")
if probs:
    fails.append(name)

# B.9 graceful degradation (SOUNDNESS_AUDIT rank 5): a payload byte corruption whose
# per-entry DIGEST is NOT refreshed is dropped by `store::unpack` at LOAD (clean
# per-root MISS) BEFORE decode — so a would-be `node_type` fault never happens.
# Replay must exit 0, produce the exact no-flag artifacts, and ACCEPT nothing.
name = "corrupt_digest_skip"
src = os.path.join(FIX, "pos_method.rs")
fresh = os.path.join(WORK, name, "store")
shutil.rmtree(os.path.join(WORK, name), ignore_errors=True)
probs = []
try:
    run(BASE, os.path.join(WORK, name, "mint"), store_flag=f"-Ztrust-witness=mint:{fresh}")
    corrupt_all_first_node_ids(fresh, refresh_digest=False)
    replay = run(BASE, os.path.join(WORK, name, "replay"),
                 store_flag=f"-Ztrust-witness=replay:{fresh}", stats=True)
    if replay.returncode != 0:
        probs.append(f"replay exited {replay.returncode} (stale-digest store caused an ICE/error)")
    if digests(os.path.join(WORK, "pos_method", "noflag")) != digests(os.path.join(WORK, name, "replay")):
        probs.append("fallback artifacts differ from no-flag")
    if accepted_roots(replay.stderr):
        probs.append("a digest-mismatched entry was ACCEPTed (checksum layer bypassed!)")
except (OSError, RuntimeError) as e:
    probs.append(str(e))
status = "PASS" if not probs else "FAIL"
print(f"  {status}  {name}: {'; '.join(probs) if probs else 'stale-digest entry dropped at load -> clean MISS, no ICE'}")
if probs:
    fails.append(name)

print()
if fails:
    print(f"FAILED: {', '.join(fails)}")
    sys.exit(1)
print("ALL trust-witness replay regressions PASS")
