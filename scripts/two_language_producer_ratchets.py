#!/usr/bin/env python3
"""Producer ratchets for the two-language program (roadmap WS5.1): the Part A and
Part A-Lean rows of the 2026-09-17 proof program, as flip-on-fix gates.

WHAT IT IS.  The judge behind the `trustc-ir` lane of
tests/e2e_two_language_programs.sh.  Every row is a directory
tests/two-language-programs/ir-* holding real SOURCE (a Rust crate with a
`clean {}` island, a standalone `.lean` file, a hand-written trust-ir module)
plus `expected.json`, which pins ONE verdict per ratchet id.  A row is green
only when every ratchet it measures matches its pin:

  PASS      the feature is demonstrated (and, where the row has one, its
            negative twin was refused for the right reason);
  GAP       a KNOWN defect, asserted by its NAMED SIGNATURE only - the verbatim
            refusal text, or a named absence measured over a key set AND its
            value.  A GAP pin matches only when the measured signature is
            byte-identical to the pinned one;
  REFUSED   a negative control that was (correctly) refused, same signature rule;
  FAIL      anything else.  Never pinnable.

A ratchet whose outcome moves for ANY reason - a GAP that turns PASS, a GAP whose
refusal changes class, a PASS that regresses - fails the row until expected.json
is updated in the same commit.  So every fix flips its rows visibly, and a gap
can never silently change shape.

It ports parta/analyze.py + parta/run.sh (Part A: Rust + Clean island ->
trust-ir) and parta-lean/run.py (Part A-Lean: the standalone Lean lane, the
hand-written format homes and the Clean general pipeline) from
reports/2026-09-17-two-language-proof-program (trust-ir), fixing the harness
defects recorded as F-120:

  * NO module-rewriting code.  `repair_fndef.py` ran unconditionally and turned
    18 correct GENERAL modules into FAILs; it is not ported (WS8.8 conflict
    resolution, binding here).  A GENERAL module is judged AS EMITTED, and the
    F-108 signature (a validator refusing ONLY ConstTypeMismatch) is a FAIL that
    names F-108.  The Part A attribution experiments that rewrote the
    producer's module (repair.py, carry.py, rename.py) are not ported either:
    they are FORMAT attributions, owned by the trust-ir conformance port; see
    NOT_PORTED.  The only module edits left are the negative twins, whose
    outcome must be a REFUSAL and which never feed a producer PASS.
  * STANDALONE refusal signatures pin the whole refusal (the declaration, the
    `[class/...]` and the message head), never the class string alone.
  * The crash controls run whenever a linked GENERAL declaration crashes,
    whether or not it linked with the shipped shims.
  * PASS prose is regenerated from the measurement, never kept from a run.
  * Every field-absence GAP is judged on the field's VALUE (`is None`, empty),
    never on key presence, so a `skip_serializing_if` field cannot pass as
    present.
  * The verdict of a run is computed from what THIS run measured; nothing
    reads a report a run did not write.

The judges (trust-ir CLI, `clean` with the trust-ir backend, the trust-cg CLI)
are BUILT FROM THE first-party/ GITLINKS by `tools` and resolved only through
the provenance stamp that build writes; an installed binary is never used
(F-118/F-119: a judge at a different pin than the producer reads a skew as a
producer regression).

Usage:
  two_language_producer_ratchets.py tools [--build]
  two_language_producer_ratchets.py list
  two_language_producer_ratchets.py run --row ir-ta01_rust_contracts --work DIR \\
        --trustc T --targo G [--write-expected]
  two_language_producer_ratchets.py audit-check      # static: every pin vs the audit corpus
  two_language_producer_ratchets.py replay REPORT.json FEATURES.txt
  two_language_producer_ratchets.py evidence --work DIR --out FILE  # G1/G2/G3/G5/G6-tagged artifact

Standard library only; Python 3.9+.
"""

from __future__ import annotations

import argparse
import copy
import hashlib
import json
import os
import re
import shlex
import shutil
import struct
import subprocess
import sys
import tempfile
import time
from pathlib import Path

TRUST_ROOT = Path(__file__).resolve().parents[1]
ROWS_DIR = TRUST_ROOT / "tests" / "two-language-programs"
AUDIT_DIR = ROWS_DIR / "ir-audit"
DEFAULT_TOOLS_DIR = TRUST_ROOT / "build" / "two-language-ir-tools"
EXPECTED_SCHEMA = "trust.two-language.producer-ratchets.expected/v1"
REPORT_SCHEMA = "trust.two-language.producer-ratchets.report/v1"
PROVENANCE_SCHEMA = "trust.two-language.producer-ratchets.tool/v1"
STEP_TIMEOUT = int(os.environ.get("TRUST_IR_RATCHET_STEP_TIMEOUT", "900"))
VERDICTS = ("PASS", "GAP", "REFUSED", "FAIL")
GAP_CLASSES = ("producer-gap", "consumer-gap", "format-gap", "refused")

# The audit trees the pins are compared against (audit-check).  Part A: the
# from-source stage1 at 5b45b83b8 (parta/out/5b45b83b8).  Part A-Lean: the same
# compiler with the clean and trust-cg PINNED by it, built from source
# (rerun-lean-head/out.run3-allsrc); its 18 GENERAL `.validate` FAILs are the
# repair_fndef defect, which audit-check reads as `harness` moves.
AUDIT_FILES = {
    "parta": "parta-5b45b83b8.features.txt",
    "parta-lean": "parta-lean-5b45b83b8.features.txt",
}

SCRUB_VARS = ("TRUSTC", "RUSTUP_TOOLCHAIN", "RUSTC", "RUSTDOC", "RUSTFLAGS",
              "CARGO_ENCODED_RUSTFLAGS", "RUSTC_WRAPPER", "RUSTC_WORKSPACE_WRAPPER",
              "CARGO_BUILD_RUSTC", "CARGO_BUILD_RUSTDOC", "CARGO_TARGET_DIR", "TRUST_NO_VERIFY")


def scrubbed_env(extra=None):
    env = {k: v for k, v in os.environ.items() if k not in SCRUB_VARS}
    env.update(extra or {})
    return env


# ============================================================ small readers
def read(p, default=""):
    try:
        with open(p, errors="replace") as f:
            return f.read()
    except OSError:
        return default


def rc(p):
    try:
        return int(read(p).strip())
    except ValueError:
        return None


def sha256_file(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def first_line(s, n=1):
    return " | ".join([l for l in s.strip().splitlines() if l.strip()][:n])


def squash(s):
    return " ".join(str(s).split())


def interp_error(stderr):
    """The interpreter's DIAGNOSTIC lines, selected by what they say rather than
    by where they sit in the stream.

    `first_line(e, 3)` used to serve this, and it silently stopped working.
    `trust-ir run --validate` prints its linking preamble to STDERR, and that
    preamble grew to four lines:

        stripped 0 summaries / 0 ProofRefs / 0 call proof contexts (...)
        linked image is well-formed (as linked)
        linked 2 module(s): 13 function(s) (...)
        lowered image is well-formed
        interpreter error: undefined_behavior at bb2: unsigned division by zero

    so the only line that carries the reason is the FIFTH, and a 3-line window
    returns pure preamble. MEASURED 2026-09-21: that is what made
    FORMAT_HOME.p13_division fail. Its twin asserts the mutant (`icmp eq` ->
    `icmp ne`, which inverts the div-by-zero guard) still validates and is caught
    by the interpreter trapping "unsigned division by zero". The mutant DOES trap
    with exactly that text — `t_quot_1` and `t_quot_3` both do — but the reason
    never reached the check, so a working negative control read as a broken one.

    Selecting by content also survives the next preamble line, which positional
    slicing cannot. Falls back to the first three lines when nothing matches, so
    an unrecognized failure still reports something rather than nothing.
    """
    lines = [l.strip() for l in str(stderr).strip().splitlines() if l.strip()]
    hits = [l for l in lines
            if re.search(r"error|refus|trap|undefined_behavior|panic|exceeded", l, re.I)]
    return " | ".join((hits or lines)[:3])


# ============================================================ steps
def step(d, name, cmd, env=None, cwd=None, timeout=None):
    """Run one command; keep <name>.cmd/.log/.rc/.secs in d (the run.sh layout)."""
    os.makedirs(d, exist_ok=True)
    with open(os.path.join(d, name + ".cmd"), "w") as f:
        f.write(" ".join(shlex.quote(str(c)) for c in cmd) + "\n")
    t0 = time.time()
    with open(os.path.join(d, name + ".log"), "w") as log:
        try:
            p = subprocess.run([str(c) for c in cmd], stdout=log, stderr=subprocess.STDOUT, env=env, cwd=cwd,
                               timeout=timeout or STEP_TIMEOUT)
            code = p.returncode
        except subprocess.TimeoutExpired:
            log.write("\nTIMEOUT: step exceeded %ss\n" % (timeout or STEP_TIMEOUT))
            code = 124
        except OSError as e:
            log.write("\nEXEC-FAILED: %s\n" % e)
            code = 127
    with open(os.path.join(d, name + ".rc"), "w") as f:
        f.write("%d\n" % code)
    with open(os.path.join(d, name + ".secs"), "w") as f:
        f.write("%d\n" % int(time.time() - t0))
    return code


def sh(cmd, cwd=None, env=None, timeout=None):
    e = dict(os.environ)
    e.update(env or {})
    try:
        p = subprocess.run([str(c) for c in cmd], cwd=cwd, env=e, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                           timeout=timeout or STEP_TIMEOUT)
    except OSError as exc:
        return 127, "", "EXEC-FAILED: %s" % exc
    return p.returncode, p.stdout.decode("utf-8", "replace"), p.stderr.decode("utf-8", "replace")


# ============================================================ tools (built from the gitlinks)
# name -> (submodule, cargo args, binary path relative to the target dir)
TOOL_SPECS = {
    "trust-ir": ("first-party/trust-ir", ["-p", "trust-ir-cli"], "release/trust-ir"),
    "clean": ("first-party/clean", ["-p", "clean", "--features", "trust-ir-backend"], "release/clean"),
    "trust-cg": ("first-party/trust-cg", ["-p", "trust-cg-cli", "--bin", "trust-cg"], "release/trust-cg"),
}


class ToolError(Exception):
    pass


def gitlink(submodule):
    out = subprocess.run(["git", "-C", str(TRUST_ROOT), "ls-tree", "HEAD", submodule],
                         stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
    parts = out.stdout.split()
    if out.returncode != 0 or len(parts) < 3 or parts[1] != "commit":
        raise ToolError("%s is not a gitlink at HEAD" % submodule)
    return parts[2]


def submodule_state(submodule):
    path = TRUST_ROOT / submodule
    head = subprocess.run(["git", "-C", str(path), "rev-parse", "HEAD"], stdout=subprocess.PIPE,
                          stderr=subprocess.PIPE, text=True)
    dirty = subprocess.run(["git", "-C", str(path), "status", "--porcelain", "--untracked-files=no"],
                           stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
    if head.returncode != 0:
        raise ToolError("%s has no checkout (run scripts/submodule_sync.sh --restore)" % submodule)
    return head.stdout.strip(), dirty.stdout.strip()


def tool_checkout_ok(name):
    sub = TOOL_SPECS[name][0]
    want = gitlink(sub)
    head, dirty = submodule_state(sub)
    if head != want:
        raise ToolError("%s: submodule HEAD %s is not the gitlink %s — the judge would be built from a tree "
                        "the superproject does not name (F-118); run scripts/submodule_sync.sh --restore"
                        % (sub, head[:12], want[:12]))
    if dirty:
        raise ToolError("%s: submodule working tree is dirty; the judge must be the gitlink's bytes" % sub)
    return want


def build_tool(name, tools_dir, builder):
    sub, args, rel = TOOL_SPECS[name]
    rev = tool_checkout_ok(name)
    target = Path(tools_dir) / (name + "-target")
    cmd = [builder, "--unverified", "build", "--release", "--locked", "--manifest-path",
           str(TRUST_ROOT / sub / "Cargo.toml"), "--target-dir", str(target)] + args
    log = Path(tools_dir) / (name + ".build.log")
    Path(tools_dir).mkdir(parents=True, exist_ok=True)
    with open(log, "w") as f:
        p = subprocess.run(cmd, stdout=f, stderr=subprocess.STDOUT, env=scrubbed_env())
    binary = target / rel
    if p.returncode != 0 or not binary.is_file():
        raise ToolError("%s: build from %s@%s failed (rc=%s); see %s" % (name, sub, rev[:12], p.returncode, log))
    head, dirty = submodule_state(sub)
    if head != rev or dirty:
        raise ToolError("%s: %s moved or was dirtied during its own build" % (name, sub))
    prov = {"schema": PROVENANCE_SCHEMA, "tool": name, "submodule": sub, "gitlink": rev,
            "binary": str(binary), "sha256": sha256_file(binary), "builder": builder,
            "command": cmd}
    (Path(tools_dir) / (name + ".provenance.json")).write_text(json.dumps(prov, indent=1) + "\n")
    return prov


def resolve_tool(name, tools_dir):
    """The ONLY way the judge finds a tool: its provenance stamp, which must name the CURRENT gitlink
    and the binary's current bytes."""
    rev = tool_checkout_ok(name)
    stamp = Path(tools_dir) / (name + ".provenance.json")
    try:
        prov = json.loads(stamp.read_text())
    except (OSError, ValueError):
        raise ToolError("%s: no provenance stamp at %s (run `%s tools --build`)" % (name, stamp, sys.argv[0]))
    if prov.get("schema") != PROVENANCE_SCHEMA or prov.get("gitlink") != rev:
        raise ToolError("%s: stamp names %s, the gitlink is %s — rebuild (`tools --build`)"
                        % (name, str(prov.get("gitlink"))[:12], rev[:12]))
    binary = prov.get("binary")
    if not binary or not os.path.isfile(binary) or sha256_file(binary) != prov.get("sha256"):
        raise ToolError("%s: the stamped binary is missing or its bytes changed since the stamp" % name)
    return prov


class Tools:
    def __init__(self, tools_dir, trustc, targo, build=False, builder="targo", need=("trust-ir",)):
        self.tools_dir = Path(tools_dir)
        self.trustc, self.targo = trustc, targo
        self.cc = os.environ.get("CC", "cc")
        self.prov, self.errors = {}, {}
        for name in TOOL_SPECS:
            try:
                self.prov[name] = build_tool(name, tools_dir, builder) if build else resolve_tool(name, tools_dir)
            except ToolError as e:
                self.errors[name] = str(e)
        missing = [n for n in need if n in self.errors]
        if missing:
            raise ToolError("; ".join(self.errors[n] for n in missing))

    def path(self, name):
        if name not in self.prov:
            raise ToolError(self.errors.get(name, name + ": unresolved"))
        return self.prov[name]["binary"]

    @property
    def cli(self):
        return self.path("trust-ir")

    def identities(self):
        ids = {}
        for label, path in (("trustc", self.trustc), ("targo", self.targo)):
            if path:
                ident = sh([path, "-vV"] if label == "trustc" else [path, "--unverified", "--version"],
                           env=scrubbed_env())[1]
                ids[label] = "%s @ %s" % (first_line(ident), path)
        for name, prov in self.prov.items():
            ids[name] = "%s@%s sha256:%s" % (prov["submodule"], prov["gitlink"][:12], prov["sha256"][:16])
        for name, err in self.errors.items():
            ids[name] = "UNRESOLVED: " + err
        return ids


# ============================================================ rows
class Rows:
    """Ratchet rows.  `sig` is the NAMED SIGNATURE a GAP / REFUSED row is pinned by."""

    def __init__(self):
        self.rows = []

    def add(self, fid, verdict, detail, klass=None, evidence=None, sig=None):
        assert verdict in VERDICTS, verdict
        if verdict == "GAP":
            assert klass in GAP_CLASSES, (fid, klass)
            assert sig, "a GAP row needs its named signature: " + fid
        if verdict == "REFUSED":
            assert sig, "a REFUSED row needs its named signature: " + fid
        row = dict(id=fid, verdict=verdict, detail=squash(detail), evidence=evidence or "")
        if klass:
            row["class"] = klass
        if sig is not None:
            row["signature"] = squash(sig)
        self.rows.append(row)

    def lines(self):
        out = []
        for r in self.rows:
            d = ("[%s] " % r["class"] if r.get("class") else "") + r["detail"]
            out.append("FEATURE %s %s %s" % (r["id"], r["verdict"], d))
        return out


def wire_version(path):
    try:
        b = open(path, "rb").read(12)
    except OSError:
        return None
    if len(b) < 12 or b[:8] != b"TRUST_IR":
        return None
    return struct.unpack_from("<I", b, 8)[0]


def first_errors(log, limit=3, width=700):
    """Verbatim compiler refusal: each `error...` line plus the explanatory `= note:` that follows."""
    lines = log.splitlines()
    out = []
    for i, line in enumerate(lines):
        if re.match(r"^error(\[E\d+\])?:", line) and "aborting due to" not in line:
            text = line
            for nxt in lines[i + 1:i + 14]:
                if re.match(r"^\s+= note: ", nxt) or re.match(r"^note: `", nxt):
                    text += " || " + nxt.strip()
                    break
            out.append(text[:width])
            if len(out) >= limit:
                break
    return out


# ============================================================ Part A: measurement (port of parta/run.sh)
# Every Rust(+island) unit: native build + run in BOTH lanes, `--emit=trust-ir` (verify on, advisory; the
# verify-off `-Ztrust-ir-lower=on` lane only as a recorded fallback), then the module checks: validate,
# 4-format round trip, reference-interpreter run of nullary `program`, negative twins.
PARTA_PROBES = [
    # (unit = probe stem, row dir, needs the dep crate)
    ("p01_rust_contracts", "ir-ta01_rust_contracts", False),
    ("p02_rust_loop_invariant", "ir-ta02_rust_loop_invariant", False),
    ("p03_rust_struct_enum_match", "ir-ta03_rust_struct_enum_match", False),
    ("p04_rust_slice_index", "ir-ta04_rust_slice_index", False),
    ("p05_rust_checked_arith", "ir-ta05_rust_checked_arith", False),
    ("p06_rust_closure", "ir-ta06_rust_closure", False),
    ("p07_rust_u128", "ir-ta07_rust_u128", False),
    ("p08_rust_mut_ref", "ir-ta08_rust_mut_ref", False),
    ("p09_rust_std_call", "ir-ta09_rust_std_call", False),
    ("p10_lean_wrapping_uint64", "ir-ta10_lean_wrapping_uint64", False),
    ("p11_lean_projection_literal", "ir-ta11_lean_projection_literal", False),
    ("p12a_lean_bool_cmp", "ir-ta12a_lean_bool_cmp", False),
    ("p12b_lean_bool_connective", "ir-ta12b_lean_bool_connective", False),
    ("p13_lean_let", "ir-ta13_lean_let", False),
    ("p14_lean_select", "ir-ta14_lean_select", False),
    ("p15a_lean_inductive_in_module", "ir-ta15a_lean_inductive_in_module", False),
    ("p15b_lean_inductive_called", "ir-ta15b_lean_inductive_called", False),
    ("p15c_lean_inductive_wrapped", "ir-ta15c_lean_inductive_wrapped", False),
    ("p16_lean_nat_structural", "ir-ta16_lean_nat_structural", False),
    ("p17_lean_nat_wf", "ir-ta17_lean_nat_wf", False),
    ("p18_theorem_citation", "ir-ta18_theorem_citation", False),
    ("p19_lean_calls_rust", "ir-ta19_lean_calls_rust", False),
    ("p20_cross_crate", "ir-ta20_cross_crate", True),
]
PROBE_ROW = {u: r for u, r, _ in PARTA_PROBES}
GEN_APP = ROWS_DIR / "ir-ta-app" / "gen_app.py"


class PartA:
    """One Part A measurement tree (WORK/parta).  Units are measured ONCE per tree and reused by every
    row that reads them (the aggregate rows read all of them)."""

    def __init__(self, work, tools):
        self.out = os.path.join(work, "parta")
        self.t = tools
        os.makedirs(self.out, exist_ok=True)
        self._stamp = json.dumps(tools.identities(), sort_keys=True)

    # ---- memoisation: a unit is re-measured when its sources or the tool identities change
    def _fresh(self, key, sources):
        mark = os.path.join(self.out, "done", key)
        want = hashlib.sha256((self._stamp + "".join(read(s) for s in sources)).encode()).hexdigest()
        if read(mark).strip() == want:
            return None
        return (mark, want)

    def _done(self, token):
        if token:
            os.makedirs(os.path.dirname(token[0]), exist_ok=True)
            with open(token[0], "w") as f:
                f.write(token[1] + "\n")

    def trustc(self, *args):
        return [self.t.trustc] + list(args)

    # ---- one Rust(+island) compilation unit
    def unit(self, name, src, with_dep=False):
        src = str(src)
        extra_src = [str(ROWS_DIR / "ir-ta-dep" / "dep.rs")] if with_dep else []
        tok = self._fresh("unit-" + name, [src] + extra_src)
        if tok is None:
            return
        if with_dep:
            self.build_dep()
        U = os.path.join(self.out, "units", name)
        shutil.rmtree(U, ignore_errors=True)
        os.makedirs(U)
        shutil.copy(src, os.path.join(U, "source.rs"))
        crate = os.path.basename(src)[:-3]
        dep_rlib = os.path.join(self.out, "units", "dep", "rlib")
        ext = ["--extern", "dep=" + os.path.join(dep_rlib, "libdep.rlib"), "-L", dep_rlib] if with_dep else []
        env = scrubbed_env()
        for lane in ("native-off", "native-adv"):
            flags = ["-Ztrust-verify=off"] if lane == "native-off" else ["-Ztrust-verify=on", "-Ztrust-policy=advisory"]
            L = os.path.join(U, lane)
            if step(L, "build", self.trustc(src, "--edition=2024", "--crate-name", crate, *flags, *ext,
                                             "-o", os.path.join(L, "prog")), env=env) == 0:
                step(L, "exec", [os.path.join(L, "prog")])
        E = os.path.join(U, "emit")
        step(E, "emit", self.trustc(src, "--edition=2024", "--crate-name", crate, "--crate-type=lib", "--cfg", "parta_lib",
                                    "--emit=trust-ir", "-Ztrust-verify=on", "-Ztrust-policy=advisory", *ext,
                                    "--out-dir", E), env=env)
        binp = os.path.join(E, crate + ".trust-ir.bin")
        lane = "emit"
        if not (os.path.exists(binp) and os.path.getsize(binp)):
            EO = os.path.join(U, "emit-off")
            step(EO, "emit", self.trustc(src, "--edition=2024", "--crate-name", crate, "--crate-type=lib", "--cfg",
                                         "parta_lib", "--emit=trust-ir", "-Ztrust-verify=off", "-Ztrust-ir-lower=on",
                                         *ext, "--out-dir", EO), env=env)
            binp = os.path.join(EO, crate + ".trust-ir.bin")
            lane = "emit-off" if os.path.exists(binp) and os.path.getsize(binp) else "none"
        with open(os.path.join(U, "module-lane"), "w") as f:
            f.write(lane + "\n")
        if lane != "none":
            link = []
            dep_mod = os.path.join(self.out, "units", "dep", "module", "module.bin")
            if with_dep and os.path.exists(dep_mod) and os.path.getsize(dep_mod):
                link = [dep_mod]
            self.check_module(U, binp, link)
        self._done(tok)

    def build_dep(self):
        src = str(ROWS_DIR / "ir-ta-dep" / "dep.rs")
        tok = self._fresh("unit-dep", [src])
        if tok is None:
            return
        U = os.path.join(self.out, "units", "dep")
        shutil.rmtree(U, ignore_errors=True)
        os.makedirs(U)
        shutil.copy(src, os.path.join(U, "source.rs"))
        env = scrubbed_env()
        step(os.path.join(U, "rlib"), "build", self.trustc(src, "--edition=2024", "--crate-name", "dep", "--crate-type=rlib",
                                                           "-Ztrust-verify=off", "--out-dir", os.path.join(U, "rlib")), env=env)
        step(os.path.join(U, "rlib-adv"), "build", self.trustc(src, "--edition=2024", "--crate-name", "dep", "--crate-type=rlib",
                                                               "-Ztrust-verify=on", "-Ztrust-policy=advisory",
                                                               "--out-dir", os.path.join(U, "rlib-adv")), env=env)
        E = os.path.join(U, "emit")
        step(E, "emit", self.trustc(src, "--edition=2024", "--crate-name", "dep", "--crate-type=lib", "--emit=trust-ir",
                                    "-Ztrust-verify=on", "-Ztrust-policy=advisory", "--out-dir", E), env=env)
        binp = os.path.join(E, "dep.trust-ir.bin")
        ok = os.path.exists(binp) and os.path.getsize(binp) > 0
        with open(os.path.join(U, "module-lane"), "w") as f:
            f.write(("emit" if ok else "none") + "\n")
        if ok:
            self.check_module(U, binp, [])
        self._done(tok)

    # ---- module checks shared by the Rust lane and the Lean lane
    def check_module(self, U, binp, link):
        cli = self.t.cli
        M = os.path.join(U, "module")
        os.makedirs(M, exist_ok=True)
        mbin = os.path.join(M, "module.bin")
        shutil.copy(binp, mbin)
        step(M, "validate", [cli, "validate", "--format", "bin", mbin])
        step(M, "to-json", [cli, "convert", "--from", "bin", "--to", "json", mbin, os.path.join(M, "module.json")])
        for f in ("bin", "json", "msgpack", "text"):
            mid, back = os.path.join(M, "rt." + f), os.path.join(M, "rt.%s.bin" % f)
            for p in (mid, back):
                if os.path.exists(p):
                    os.remove(p)
            if step(M, "rt-%s-out" % f, [cli, "convert", "--from", "bin", "--to", f, mbin, mid]) == 0:
                if step(M, "rt-%s-back" % f, [cli, "convert", "--from", f, "--to", "bin", mid, back]) == 0:
                    if step(M, "rt-%s-cmp" % f, ["cmp", mbin, back]) != 0:
                        step(M, "rt-%s-json" % f, [cli, "convert", "--from", "bin", "--to", "json", back,
                                                    os.path.join(M, "rt.%s.json" % f)])
        entry = entry_symbol(load_json_or_none(os.path.join(M, "module.json")))
        step(M, "run", [cli, "run", "--format", "bin", "--entry", entry, mbin] + list(link))
        twins(M, cli, list(link))

    # ---- rows' sources
    def probe(self, unit):
        row = PROBE_ROW[unit]
        with_dep = next(d for u, _, d in PARTA_PROBES if u == unit)
        self.unit(unit, ROWS_DIR / row / (unit + ".rs"), with_dep)
        if unit == "p15a_lean_inductive_in_module":
            M = os.path.join(self.out, "units", unit, "module")
            if os.path.exists(os.path.join(M, "module.bin")):
                shutil.copy(os.path.join(M, "module.bin"), os.path.join(M, "module.tmbc"))
                step(M, "drive-inductive", [self.t.cli, "run", "--entry", "drive",
                                            str(ROWS_DIR / PROBE_ROW[unit] / "inductive_driver.trust_ir"),
                                            os.path.join(M, "module.tmbc")])

    def all_probes(self):
        for u, _, _ in PARTA_PROBES:
            self.probe(u)

    def app(self):
        self.unit("app", ROWS_DIR / "ir-ta-app" / "app.rs", True)

    def generated_app(self, name):
        """app_max / app_exec: the gen_app.py program over the blocks whose probe this compiler accepted
        (app_max) or whose probe the interpreter executed to the native value (app_exec)."""
        self.all_probes()
        features = accepted(self.out) if name == "app_max" else executed(self.out)
        with open(os.path.join(self.out, name + ".features"), "w") as f:
            f.write(",".join(features) + "\n")
        srcdir = os.path.join(self.out, "generated")
        os.makedirs(srcdir, exist_ok=True)
        src = os.path.join(srcdir, name + ".rs")
        subprocess.run([sys.executable, str(GEN_APP), "--features", ",".join(features), "-o", src], check=True)
        self.unit(name, src, True)

    def lean_oracle(self):
        self.unit("lean_oracle", ROWS_DIR / "ir-ta-lean_oracle" / "lean_oracle.rs")

    def island_mutant(self):
        """WS8.8 mutation control: p10 with ONE island line edited (the Rust side untouched)."""
        self.unit(ISLAND_MUTANT_UNIT, ROWS_DIR / "ir-ta-island_mutant" / (ISLAND_MUTANT_UNIT + ".rs"))

    def neg(self):
        srcs = sorted(str(p) for p in (ROWS_DIR / "ir-ta-neg").glob("*.rs"))
        pos = str(ROWS_DIR / "ir-ta18_theorem_citation" / "p18_theorem_citation.rs")
        tok = self._fresh("neg", srcs + [pos])
        if tok is None:
            return
        N = os.path.join(self.out, "neg")
        shutil.rmtree(N, ignore_errors=True)
        os.makedirs(os.path.join(N, "o"))
        env = scrubbed_env()
        for f in srcs:
            step(N, os.path.basename(f)[:-3], self.trustc(f, "--edition=2024", "--crate-type=lib", "-Ztrust-verify=on",
                                                          "--out-dir", os.path.join(N, "o")), env=env)
        step(N, "p18_POS_strict", self.trustc(pos, "--edition=2024", "--crate-type=lib", "--cfg", "parta_lib",
                                              "-Ztrust-verify=on", "--out-dir", os.path.join(N, "o")), env=env)
        self._done(tok)

    def lean(self):
        rowd = ROWS_DIR / "ir-ta-lean"
        srcs = sorted(str(p) for p in rowd.iterdir())
        tok = self._fresh("lean", srcs)
        if tok is None:
            return
        self.lean_oracle()
        L = os.path.join(self.out, "lean")
        shutil.rmtree(L, ignore_errors=True)
        os.makedirs(os.path.join(L, "src"))
        for p in rowd.glob("*.lean"):
            shutil.copy(p, os.path.join(L, "src"))
        src = os.path.join(L, "src")
        env = scrubbed_env()
        tg = self.t.targo
        step(L, "check-both", [tg, "trust", "check", "Lib.lean", "Use.lean"], env=env, cwd=src)
        step(L, "check-use", [tg, "trust", "check", "Use.lean"], env=env, cwd=src)
        step(L, "check-bad", [tg, "trust", "check", "Bad.lean"], env=env, cwd=src)
        for f in ("Lib", "Use"):
            step(L, "build-" + f, [tg, "trust", "build", f + ".lean", "--emit=trust-ir", "--out",
                                   os.path.join(L, f + ".irlib.json"), "--census", os.path.join(L, f + ".census.json")],
                 env=env, cwd=src)
        for p in sorted(Path(src).glob("L_*.lean")):
            n = p.name[:-5]
            step(L, "build-" + n, [tg, "trust", "build", p.name, "--emit=trust-ir", "--out",
                                   os.path.join(L, n + ".irlib.json"), "--verbose"], env=env, cwd=src)
        for f in ("Lib", "Use"):
            envp = os.path.join(L, f + ".irlib.json")
            if os.path.exists(envp) and os.path.getsize(envp):
                os.makedirs(os.path.join(L, f), exist_ok=True)
                d = json.load(open(envp))
                blob = os.path.join(L, f, "envelope.bin")
                with open(blob, "wb") as fh:
                    fh.write(bytes.fromhex(d["module_binary_hex"]))
                self.check_module(os.path.join(L, f), blob, [])
        mlib = os.path.join(L, "Lib", "module")
        if os.path.exists(os.path.join(mlib, "module.bin")):
            drv = str(rowd / "lean_driver.trust_ir")
            shutil.copy(os.path.join(mlib, "module.bin"), os.path.join(L, "Lib", "Lib.tmbc"))
            step(os.path.join(L, "Lib"), "drive", [self.t.cli, "run", "--entry", "drive", "--validate", drv,
                                                   os.path.join(L, "Lib", "Lib.tmbc")])
            # negative twin: the same link against a Lib whose `addmul` multiplies no more (Mul -> Add)
            try:
                d = json.load(open(os.path.join(mlib, "module.json")))
                f = next(f for f in d["functions"] if f["name"] == "addmul")
                n = next(n for b in f["blocks"] for n in b["body"]
                         if isinstance(n["inst"], dict) and n["inst"].get("BinOp", {}).get("op") == "Mul")
                n["inst"]["BinOp"]["op"] = "Add"
                json.dump(d, open(os.path.join(L, "Lib", "mutant.json"), "w"))
                if step(os.path.join(L, "Lib"), "drive-mutant-encode",
                        [self.t.cli, "convert", "--from", "json", "--to", "bin", os.path.join(L, "Lib", "mutant.json"),
                         os.path.join(L, "Lib", "mutant.tmbc")]) == 0:
                    step(os.path.join(L, "Lib"), "drive-mutant", [self.t.cli, "run", "--entry", "drive", "--validate",
                                                                  drv, os.path.join(L, "Lib", "mutant.tmbc")])
            except (OSError, ValueError, StopIteration, KeyError):
                pass
        self._done(tok)

    def attrib(self):
        rowd = ROWS_DIR / "ir-ta-attrib"
        srcs = sorted(str(p) for p in rowd.glob("*.trust_ir"))
        tok = self._fresh("attrib", srcs)
        if tok is None:
            return
        A = os.path.join(self.out, "attrib")
        shutil.rmtree(A, ignore_errors=True)
        os.makedirs(A)
        for f in srcs:
            n = os.path.basename(f)[:-len(".trust_ir")]
            step(A, n + ".validate", [self.t.cli, "validate", f])
            step(A, n + ".run", [self.t.cli, "run", "--entry", "program", "--validate", f])
        self._done(tok)

    def f1(self):
        """F1 exit: machine code FROM the trust-ir spelling (trust-cg backend + trust-ir frontend), foreign main."""
        rowd = ROWS_DIR / "ir-ta-f1"
        srcs = sorted(str(p) for p in rowd.iterdir())
        tok = self._fresh("f1", srcs)
        if tok is None:
            return
        F = os.path.join(self.out, "f1")
        shutil.rmtree(F, ignore_errors=True)
        os.makedirs(os.path.join(F, "probe"))
        env = scrubbed_env()
        main_c = str(rowd / "main.c")
        for c in ("f1_rust", "f1_lib"):
            D = os.path.join(F, "native-" + c)
            if step(D, "build", self.trustc(str(rowd / (c + ".rs")), "--edition=2024", "--crate-type=staticlib",
                                            "--crate-name", c, "-Cpanic=abort", "-Ztrust-verify=off", "--out-dir", D),
                    env=env) == 0:
                if step(D, "link", [self.t.cc, main_c, os.path.join(D, "lib%s.a" % c), "-o", os.path.join(D, "main")]) == 0:
                    step(D, "exec", [os.path.join(D, "main")])
        probe = os.path.join(F, "probe", "probe.rs")
        with open(probe, "w") as f:
            f.write("pub fn f1_probe(x: u64) -> u64 { x }\n")
        prc = step(F, "backend-probe", self.trustc(probe, "--edition=2024", "--crate-type=lib", "-Cpanic=abort",
                                                   "-Zunstable-options", "-Zcodegen-backend=trust-cg", "-Ztrust-verify=off",
                                                   "-Ztrust-ir-lower", "-Ztrust-cg-frontend=trust-ir",
                                                   "--out-dir", os.path.join(F, "probe")), env=env)
        with open(os.path.join(F, "backend"), "w") as f:
            f.write(("present" if prc == 0 else "absent") + "\n")
        if prc == 0:
            def cg(d, crate, *extra):
                D = os.path.join(F, d)
                os.makedirs(os.path.join(D, "x"), exist_ok=True)
                if step(D, "build", self.trustc(str(rowd / (crate + ".rs")), "--edition=2024", "--crate-type=lib",
                                                "--crate-name", crate, "-Cpanic=abort", "-Zunstable-options",
                                                "-Zcodegen-backend=trust-cg", "-Ztrust-verify=on", "-Ztrust-policy=advisory",
                                                "-Ztrust-ir-lower", "-Ztrust-cg-frontend=trust-ir", *extra, "--out-dir", D),
                        env=env) != 0:
                    return
                subprocess.run(["ar", "x", os.path.join(D, "lib%s.rlib" % crate)], cwd=os.path.join(D, "x"),
                               stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
                objs = sorted(str(p) for p in Path(D, "x").glob("*.o"))
                if step(D, "link", [self.t.cc, main_c] + objs + ["-o", os.path.join(D, "main")]) == 0:
                    step(D, "exec", [os.path.join(D, "main")])
            cg("control-strict", "f1_rust")
            cg("control-allow", "f1_rust", "-Ztrust-cg-output-gate=allow-unknown")
            cg("subject-allow", "f1_lib", "-Ztrust-cg-output-gate=allow-unknown")
            # -Ztrust-ir-upstream-mir was removed by a4e15ca586 (the upstream-MIR diversion is
            # retired; D39/D40's sealed importer is the route), so the license lane is the
            # crate-module selection alone now. Passing the removed flag aborted trustc
            # before it ran, which only fed the GAP classifier unknown-flag noise.
            cg("subject-license", "f1_lib", "-Ztrust-cg-output-gate=allow-unknown", "-Ztrust-ir-crate-module=on")
        self._done(tok)


# ---- negative twins (port of parta/twins.py): ONE mutation of the emitted module each, refused for the
# right reason.  A twin never feeds a producer PASS: its only admissible outcome is a refusal.
SWAP_BIN = {"Add": "Sub", "Sub": "Add", "Mul": "Add", "Xor": "Or", "And": "Or", "Or": "And"}
SWAP_CMP = {"Ult": "Ugt", "Ule": "Ugt", "Eq": "Ne", "Ne": "Eq", "Ugt": "Ult", "Uge": "Ult",
            "Slt": "Sgt", "Sle": "Sgt", "Sgt": "Slt", "Sge": "Slt"}
SWAP_OVF = {"AddOverflow": "SubOverflow", "SubOverflow": "AddOverflow", "MulOverflow": "AddOverflow"}
NAME_OK = re.compile(r"^[A-Za-z0-9_.$]+$")


def fn_label(f):
    """WS5.2: the name a row MEANS a function by -- its `display_path` (a Rust def path, a Clean row's
    Lean spelling).  `Function.name` is the link-time symbol since WS5.2, so every semantic lookup keys
    on this label; a hand-written module (or any row without a display path) falls back to the name."""
    return (f or {}).get("display_path") or (f or {}).get("name", "")


def entry_symbol(js, label="program"):
    """The link-time symbol `trust-ir run --entry` must name for the row's `label` entry: the ONE defined,
    non-Clean function displaying `label`.  A module that names its entry directly (hand-written, or a
    pre-WS5.2 producer) has no such display path, and `label` itself is returned."""
    hits = [f for f in (js or {}).get("functions", [])
            if f.get("blocks") and f.get("producer") != "Clean" and fn_label(f) == label and f.get("name") != label]
    return hits[0]["name"] if len(hits) == 1 else label


def load_json_or_none(path):
    try:
        with open(path) as fh:
            return json.load(fh)
    except (OSError, ValueError):
        return None
MAX_TRIES = 6


def _run(cmd):
    try:
        p = subprocess.run([str(c) for c in cmd], stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True, timeout=300)
    except (OSError, subprocess.TimeoutExpired) as e:
        return 127, str(e)
    return p.returncode, p.stdout


def _encode(cli, js, path_json, path_bin):
    json.dump(js, open(path_json, "w"))
    return _run([cli, "convert", "--from", "json", "--to", "bin", path_json, path_bin])


def interp_value(log):
    vals = [l.strip() for l in log.splitlines() if re.fullmatch(r"-?\d+", l.strip())]
    return vals[-1] if vals else None


def mutate_exec(js):
    """(description, mutated json) candidates reachable from `program`: Producer::Clean bodies first, then
    Rust bodies, `program` last."""
    by_id = {f["id"]: f for f in js["functions"]}
    entry = next((f for f in js["functions"] if fn_label(f) == "program" and f.get("producer") != "Clean"), None)
    reach, todo = set(), [entry["id"]] if entry else []
    while todo:
        i = todo.pop()
        if i in reach or i not in by_id:
            continue
        reach.add(i)
        for b in by_id[i].get("blocks", []):
            for n in b.get("body", []):
                inst = n.get("inst")
                if isinstance(inst, dict):
                    for k in ("Call", "Invoke"):
                        if k in inst and isinstance(inst[k].get("callee"), int):
                            todo.append(inst[k]["callee"])
    fns = [f for f in js["functions"] if f.get("blocks") and f["id"] in reach]
    order = [f for f in fns if f.get("producer") == "Clean"] \
        + [f for f in fns if f.get("producer") != "Clean" and fn_label(f) != "program"] \
        + [f for f in fns if fn_label(f) == "program" and f.get("producer") != "Clean"]
    for f in order:
        fi = js["functions"].index(f)
        for bi, b in enumerate(f["blocks"]):
            for ii, n in enumerate(b.get("body", [])):
                inst = n.get("inst")
                if not isinstance(inst, dict):
                    continue
                want = next(iter(inst))
                m = copy.deepcopy(js)
                tgt = m["functions"][fi]["blocks"][bi]["body"][ii]["inst"][want]
                where = "%s fn @%s bb%d#%d" % (f.get("producer"), f["name"], bi, ii)
                if want == "BinOp" and tgt.get("op") in SWAP_BIN:
                    old = tgt["op"]; tgt["op"] = SWAP_BIN[old]
                    yield "%s: BinOp %s -> %s" % (where, old, tgt["op"]), m
                elif want == "Overflow" and tgt.get("op") in SWAP_OVF:
                    old = tgt["op"]; tgt["op"] = SWAP_OVF[old]
                    yield "%s: Overflow %s -> %s" % (where, old, tgt["op"]), m
                elif want == "ICmp" and tgt.get("op") in SWAP_CMP:
                    old = tgt["op"]; tgt["op"] = SWAP_CMP[old]
                    yield "%s: ICmp %s -> %s" % (where, old, tgt["op"]), m
                elif want == "Select" and f.get("producer") == "Clean":
                    tgt["then_val"], tgt["else_val"] = tgt["else_val"], tgt["then_val"]
                    yield "%s: Select arms swapped" % where, m
                elif want == "Return" and f.get("producer") == "Clean" and len(b.get("params", [])) >= 2 \
                        and len(tgt.get("values", [])) == 1 and len(b["body"]) == 1:
                    ids = [p[0] for p in b["params"]]
                    old = tgt["values"][0]
                    new = next(i for i in ids if i != old)
                    tgt["values"] = [new]
                    yield "%s: projection returns %%%s instead of %%%s" % (where, new, old), m
                elif want == "Const" and isinstance(tgt.get("value"), dict) and isinstance(tgt["value"].get("Int"), int) \
                        and tgt.get("ty") in ("U64", "U32", "U8", "U16", "Usize"):
                    tgt["value"]["Int"] += 1
                    yield "%s: literal %d -> %d" % (where, tgt["value"]["Int"] - 1, tgt["value"]["Int"]), m


def twins(mdir, cli, extra):
    tdir = os.path.join(mdir, "twins")
    os.makedirs(tdir, exist_ok=True)
    out = {}
    try:
        js = json.load(open(os.path.join(mdir, "module.json")))
    except (OSError, ValueError):
        json.dump(out, open(os.path.join(mdir, "twins.json"), "w"))
        return
    binp = os.path.join(mdir, "module.bin")
    tb = os.path.join(tdir, "trailing.bin")
    open(tb, "wb").write(open(binp, "rb").read() + b"\x00")
    code, log = _run([cli, "validate", "--format", "bin", tb])
    out["codec.trailing"] = dict(mutation="module.bin + one 0x00 byte", rc=code, log=log.strip()[-300:],
                                 refused=code != 0, right_reason=bool(re.search(r"trailing", log, re.I)))
    base_ok = _run([cli, "validate", "--format", "bin", binp])[0] == 0
    if base_ok and any(o.get("site") for o in js.get("proof_obligations", [])):
        m = copy.deepcopy(js)
        o = next(o for o in m["proof_obligations"] if o.get("site"))
        o["site"]["inst_index"] = 99999
        rc1, l1 = _encode(cli, m, os.path.join(tdir, "site.json"), os.path.join(tdir, "site.bin"))
        code, log = _run([cli, "validate", "--format", "bin", os.path.join(tdir, "site.bin")]) if rc1 == 0 else (rc1, l1)
        out["validate.site"] = dict(mutation="obligation %s site.inst_index := 99999" % o.get("id"), rc=code,
                                    log=log.strip()[-400:], refused=code != 0, right_reason="ObligationSiteOutOfRange" in log)
    if base_ok:
        m = copy.deepcopy(js)
        prog = next((f for f in m["functions"] if fn_label(f) == "program" and f.get("producer") != "Clean"), None) \
            or next(f for f in m["functions"] if f.get("blocks"))
        ft = copy.deepcopy(m["func_types"][prog["ty"]])
        ft["is_vararg"] = True
        m["func_types"].append(ft)
        prog["ty"] = len(m["func_types"]) - 1
        rc1, l1 = _encode(cli, m, os.path.join(tdir, "vararg.json"), os.path.join(tdir, "vararg.bin"))
        code, log = _run([cli, "validate", "--format", "bin", os.path.join(tdir, "vararg.bin")]) if rc1 == 0 else (rc1, l1)
        out["validate.vararg"] = dict(mutation="@%s re-typed to a fresh variadic copy of its own FuncTy" % prog["name"],
                                      rc=code, log=log.strip()[-400:], refused=code != 0,
                                      right_reason=bool(re.search(r"RustAbiVararg[^\n]*" + re.escape(prog["name"]), log)))
    all_ok = all(NAME_OK.match(r.get("name", "")) for t in ("functions", "structs", "enums") for r in js.get(t) or [])
    if base_ok and all_ok:
        cands = [("format.text_fn_name", "functions", lambda r: r.get("blocks") and fn_label(r) != "program", lambda n: "m::" + n),
                 ("format.text_typedef_name", "structs", lambda r: True, lambda n: "m::" + n + "<u8>")]
        for key, table, pick, respell in cands:
            idx = next((i for i, r in enumerate(js.get(table) or []) if pick(r)), None)
            if idx is None:
                continue
            m = copy.deepcopy(js)
            old = m[table][idx]["name"]
            m[table][idx]["name"] = respell(old)
            stem = os.path.join(tdir, key.replace(".", "_"))
            rc1, _ = _encode(cli, m, stem + ".json", stem + ".bin")
            ent = dict(mutation="%s[%d].name %r -> %r" % (table, idx, old, respell(old)), json_to_bin_rc=rc1)
            if rc1 == 0:
                ent["validate_rc"], vlog = _run([cli, "validate", "--format", "bin", stem + ".bin"])
                ent["validate_ok"] = ent["validate_rc"] == 0 and "module is well-formed" in vlog
                rcb, _ = _run([cli, "convert", "--from", "bin", "--to", "bin", stem + ".bin", stem + ".rt.bin"])
                ent["bin_roundtrip_identical"] = rcb == 0 and open(stem + ".bin", "rb").read() == open(stem + ".rt.bin", "rb").read()
                rct, _ = _run([cli, "convert", "--from", "bin", "--to", "text", stem + ".bin", stem + ".text"])
                ent["text_encode_rc"] = rct
                if rct == 0:
                    rcd, ld = _run([cli, "convert", "--from", "text", "--to", "bin", stem + ".text", stem + ".text.bin"])
                    ent["text_decode_rc"] = rcd
                    ent["text_decode_log"] = ld.strip()[-200:]
                    ent["text_identical"] = rcd == 0 and open(stem + ".bin", "rb").read() == open(stem + ".text.bin", "rb").read()
            out[key] = ent
    entry = entry_symbol(js)
    rc0, log0 = _run([cli, "run", "--format", "bin", "--entry", entry, binp] + extra)
    if rc0 == 0:
        v0 = interp_value(log0)
        tried = []
        for k, (desc, m) in enumerate(mutate_exec(js)):
            if k >= MAX_TRIES:
                break
            rc1, l1 = _encode(cli, m, os.path.join(tdir, "mutant.json"), os.path.join(tdir, "mutant.bin"))
            code, log = _run([cli, "run", "--format", "bin", "--entry", entry, os.path.join(tdir, "mutant.bin")] + extra) \
                if rc1 == 0 else (rc1, l1)
            v1 = interp_value(log) if code == 0 else None
            observed = code != 0 or v1 != v0
            tried.append(dict(mutation=desc, mutant=v1, mutant_rc=code, observed=observed,
                              mutant_error=None if code == 0 else (log.strip().splitlines() or [""])[-1][:200]))
            if observed:
                break
        out["exec.mutant"] = dict(original=v0, tried=tried, observed=any(t["observed"] for t in tried),
                                  mutation=next((t["mutation"] for t in tried if t["observed"]), None))
    json.dump(out, open(os.path.join(mdir, "twins.json"), "w"), indent=1)


# ============================================================ Part A: judge (port of parta/analyze.py)
def blocks():
    rows = subprocess.check_output([sys.executable, str(GEN_APP), "--list"], text=True)
    out = []
    for r in rows.splitlines():
        if r.strip():
            fid, probe, exp = r.split()
            out.append((fid, probe, int(exp)))
    return out


EXTRA_PROBES = [("lean.inductive_called", "p15b_lean_inductive_called", 2)]


def accepted(out):
    ok = []
    for fid, probe, _ in blocks():
        u = os.path.join(out, "units", probe)
        native = rc(os.path.join(u, "native-off", "build.rc")) == 0 or rc(os.path.join(u, "native-adv", "build.rc")) == 0
        if native and read(os.path.join(u, "module-lane")).strip() == "emit":
            ok.append(fid)
    return ok


def executed(out):
    """Blocks whose probe the reference interpreter ran to the native value."""
    ok = []
    for fid, probe, _ in blocks():
        info = load_unit(out, probe)
        if not info or "module" not in info or info["module_lane"] != "emit":
            continue
        v, _, probs = native_oracle(info)
        r = info["module"]["run"]
        if v is not None and not probs and r["rc"] == 0 and r.get("value") == v:
            ok.append(fid)
    return ok


NATIVE_REFUSALS = [
    # (regex over the build log, class, short name)
    (r"did not become callable from Rust[\s\S]*?no selection row for `", "refused",
     "clean-origin instruction-selection table has no row for this head"),
    (r"did not become callable from Rust[\s\S]*?IS selected — by rows? `", "refused",
     "clean-origin row selects this head, but not in the shape the body applies it"),
    (r"did not become callable from Rust[\s\S]*?no Rust carrier is modeled for the Clean type", "refused",
     "no Rust carrier for the Clean type (inductive cannot cross the seam)"),
    (r"cannot find `\w+` in `\w+`[\s\S]*did not become callable from Rust", "refused",
     "island inductive is not nameable from Rust"),
    (r"no diagnostic E6 facet record exists for", "refused",
     "citation needs verification ON (no E6 facet record in the -Ztrust-verify=off lane)"),
]
EMIT_REFUSALS = [
    (r"trust-ir-lower semantic finalization failed: fatal clean-origin evidence disagreement", "producer-gap",
     "clean-origin evidence disagreement at semantic finalization (compiler labels it a PRODUCER defect)"),
    (r"TrustIr\(Invalid\(\[ConstTypeMismatch", "producer-gap",
     "general-lane Clean module refused by the compiler's own embedded trust-ir validator (ConstTypeMismatch)"),
]


def load_unit(out, name):
    u = os.path.join(out, "units", name)
    if not os.path.isdir(u):
        return None
    info = dict(name=name, dir=u)
    src = read(os.path.join(u, "source.rs"))
    m = re.search(r"^// EXPECT: (\d+)", src, re.M)
    info["expect"] = int(m.group(1)) if m else None
    info["native"] = {}
    for lane in ("native-off", "native-adv"):
        b = rc(os.path.join(u, lane, "build.rc"))
        log = read(os.path.join(u, lane, "build.log"))
        ent = dict(build_rc=b, secs=rc(os.path.join(u, lane, "build.secs")))
        if b == 0:
            ent["exec_rc"] = rc(os.path.join(u, lane, "exec.rc"))
            ent["stdout"] = read(os.path.join(u, lane, "exec.log")).strip()
        elif b is not None:
            ent["refusal"] = first_errors(log)
            ent["signature"] = next(((k, n) for rx, k, n in NATIVE_REFUSALS if re.search(rx, log)), None)
            ent["uncallable_clean_defs"] = sorted(set(re.findall(r"note: `([\w']+)` is declared in this `clean", log)))
        m = re.findall(r"Trust verification: (\d+) proved, (\d+) failed, (\d+) unknown, (\d+) timed out, (\d+) runtime-checked", log)
        if m:
            ent["verification_totals"] = dict(zip(("proved", "failed", "unknown", "timed_out", "runtime_checked"),
                                                  [sum(int(x[i]) for x in m) for i in range(5)]))
        cit = re.findall(r"citation `(\w+)` kernel-discharges", log)
        if cit:
            ent["citations_kernel_discharged"] = cit
        info["native"][lane] = ent
    lane = read(os.path.join(u, "module-lane")).strip() or "none"
    info["module_lane"] = lane
    info["emit"] = {}
    for el in ("emit", "emit-off"):
        r = rc(os.path.join(u, el, "emit.rc"))
        if r is None:
            continue
        log = read(os.path.join(u, el, "emit.log"))
        ent = dict(rc=r, secs=rc(os.path.join(u, el, "emit.secs")))
        produced = any(f.endswith(".trust-ir.bin") and os.path.getsize(os.path.join(u, el, f))
                       for f in os.listdir(os.path.join(u, el)))
        ent["module_written"] = produced
        if not produced:
            ent["refusal"] = (first_errors(log) or [l[:900] for l in log.splitlines() if re.match(r"^(warning|error): trust-ir", l)]
                              or [l for l in log.splitlines() if "error" in l][:2])
            ent["signature"] = next(((k, n) for rx, k, n in EMIT_REFUSALS + NATIVE_REFUSALS if re.search(rx, log)), None)
        info["emit"][el] = ent
    if lane != "none":
        island_defs = set(re.findall(r"^\s*def\s+([A-Za-z_][\w']*)", src, re.M))
        info["module"] = load_module(os.path.join(u, "module"), os.path.join(u, lane), island_defs)
        info["module"]["_verification_totals"] = (info["native"].get("native-adv") or {}).get("verification_totals")
        info["module"]["_attrib"] = attrib_view(out)
    return info


def load_module(mdir, emit_dir=None, island_defs=frozenset()):
    mod = dict(dir=mdir)
    mod["wire_version"] = wire_version(os.path.join(mdir, "module.bin"))
    mod["bytes"] = os.path.getsize(os.path.join(mdir, "module.bin"))
    js = None
    try:
        js = json.load(open(os.path.join(mdir, "module.json")))
    except (OSError, ValueError):
        pass
    cov = None
    if emit_dir and os.path.isdir(emit_dir):
        for f in sorted(os.listdir(emit_dir)):
            if f.endswith(".trust-ir.coverage.json"):
                try:
                    cov = json.load(open(os.path.join(emit_dir, f)))
                except ValueError:
                    pass
    mod["coverage"] = coverage_view(cov)
    mod["census"] = census(js) if js is not None else None
    mod["validate"] = validate_view(mdir, js, cov, island_defs)
    try:
        mod["twins"] = json.load(open(os.path.join(mdir, "twins.json")))
    except (OSError, ValueError):
        mod["twins"] = None
    mod["roundtrip"] = roundtrip_view(mdir, js)
    mod["run"] = run_view(mdir)
    mod["_json"] = js
    return mod


def coverage_view(cov):
    if not cov:
        return None
    co = cov.get("clean_origin") or {}
    view = dict(schema=cov.get("schema"), clean_origin_reason=co.get("reason"), proof_authority=cov.get("proof_authority"),
                native_verification_requests=cov.get("native_verification_requests"),
                direct_obligation_capability=cov.get("direct_obligation_capability"),
                totals=cov.get("totals"), recorded=co.get("recorded"))
    view["emitted"] = [dict(name=e.get("clean_name"), def_path=e.get("def_path"), shape=e.get("shape"),
                            tier=e.get("tier"), body_gate=e.get("body_gate"), judgment=e.get("judgment"),
                            func_id=e.get("func_id"), gate_method=e.get("gate_method"),
                            gate_scope=e.get("gate_scope"))
                       for e in co.get("emitted", [])]
    view["skipped"] = [dict(name=e.get("clean_name") or e.get("def_path"), shape=e.get("shape"),
                            reason=(e.get("reason") or e.get("detail") or json.dumps(e))[:600])
                       for e in co.get("skipped", [])]
    view["linked"] = [dict(def_path=e.get("def_path"), decl_func_id=e.get("decl_func_id"),
                           target_func_id=e.get("target_func_id"), edges_repointed=e.get("edges_repointed"),
                           retired_declaration=e.get("retired_declaration"))
                      for e in co.get("linked", [])]
    gen = co.get("general")
    if gen is not None:
        view["general"] = gen if isinstance(gen, (dict, list)) and len(json.dumps(gen)) < 1500 else str(gen)[:1500]
    view["unlowered_bodies"] = [b.get("def_path") for b in cov.get("bodies", []) if not b.get("lowered")]
    view["unsupported"] = {b.get("def_path"): b.get("unsupported") for b in cov.get("bodies", []) if b.get("unsupported")}
    return view


def walk(o):
    yield o
    if isinstance(o, dict):
        for v in o.values():
            yield from walk(v)
    elif isinstance(o, list):
        for v in o:
            yield from walk(v)


def census(js):
    """Which trust-ir surfaces the emitted module populates.  Every count is over a field's VALUE
    (non-null / non-empty), never over key presence."""
    fns = js.get("functions", [])
    defined = [f for f in fns if f.get("blocks")]
    prod = {}
    for f in fns:
        p = f.get("producer")
        p = p if isinstance(p, str) else json.dumps(p)
        prod.setdefault(p, dict(defined=0, declared=0))
        prod[p]["defined" if f.get("blocks") else "declared"] += 1
    obls = js.get("proof_obligations") or []
    certs = js.get("proof_certificates") or []
    summaries = [f for f in fns if f.get("summary")]
    bindings = 0
    for f in summaries:
        for n in walk(f["summary"]):
            if isinstance(n, dict) and n.get("bindings"):
                bindings += len(n["bindings"])
    for o in obls:
        fm = o.get("formula")
        if isinstance(fm, dict) and fm.get("bindings"):
            bindings += len(fm["bindings"])
    types_blob = json.dumps([js.get("types"), js.get("func_types"), js.get("structs"), js.get("enums")])
    insts = {}
    for f in defined:
        for b in f["blocks"]:
            for n in b.get("body", []):
                i = n.get("inst")
                k = i if isinstance(i, str) else next(iter(i)) if isinstance(i, dict) else "?"
                insts[k] = insts.get(k, 0) + 1
            t = b.get("terminator") or b.get("term")
            if isinstance(t, dict):
                ti = t.get("inst", t)
                k = ti if isinstance(ti, str) else next(iter(ti)) if isinstance(ti, dict) else "?"
                insts[k] = insts.get(k, 0) + 1
    kinds, statuses = {}, {}
    for o in obls:
        k = o.get("kind"); k = k if isinstance(k, str) else json.dumps(k)
        kinds[k] = kinds.get(k, 0) + 1
        s = o.get("status"); s = s if isinstance(s, str) else json.dumps(s)
        statuses[s] = statuses.get(s, 0) + 1
    ev = {}
    for c in certs:
        e = c.get("evidence")
        k = e if isinstance(e, str) else next(iter(e)) if isinstance(e, dict) else "?"
        ev[k] = ev.get(k, 0) + 1
    vararg_rust_decls = []
    fts = js.get("func_types", [])
    for f in fns:
        ft = fts[f["ty"]] if isinstance(f.get("ty"), int) and f["ty"] < len(fts) else {}
        if ft.get("is_vararg") and f.get("calling_conv") == "Rust":
            vararg_rust_decls.append(fn_label(f))
    return dict(
        module_name=js.get("name"),
        functions=len(fns), defined=len(defined), producers=prod,
        body_gate_populated=sum(1 for f in fns if f.get("body_gate") is not None),
        display_path_populated=sum(1 for f in fns if f.get("display_path")),
        display_path_on_rust_definitions=sum(1 for f in defined if f.get("producer") == "Trust" and f.get("display_path")),
        rust_definitions=sum(1 for f in defined if f.get("producer") == "Trust"),
        body_gate_by_fn={fn_label(f): f.get("body_gate") for f in defined if f.get("producer") == "Clean"},
        summary_populated=len(summaries), clause_bindings=bindings,
        imports=len(js.get("imports") or []),
        tuple_layouts=len(js.get("tuple_layouts") or []),
        handle_types=types_blob.count('"Handle"'),
        structs=len(js.get("structs") or []), enums=len(js.get("enums") or []),
        enum_layout_descriptors=sum(1 for e in js.get("enums") or [] if e.get("layout")),
        closure_types=len(js.get("closure_types") or []),
        globals=len(js.get("globals") or []),
        obligations=len(obls), obligation_kinds=kinds, obligation_statuses=statuses,
        obligations_with_function=sum(1 for o in obls if o.get("function") is not None),
        obligations_with_site=sum(1 for o in obls if o.get("site")),
        obligations_with_formula=sum(1 for o in obls if o.get("formula")),
        obligations_with_source=sum(1 for o in obls if o.get("source")),
        certificates=len(certs), certificate_evidence=ev,
        instr_annotations=sum(1 for f in defined for b in f["blocks"] for n in b.get("body", []) if n.get("proofs")),
        function_proofs=sum(len(f.get("proofs") or []) for f in fns),
        spec_modules=[dict(name=s.get("name"), invariants=len(s.get("invariants") or []),
                           enforcement=s.get("enforcement")) for s in js.get("spec_modules") or []],
        target_info=js.get("target_info"),
        inst_histogram=insts,
        names_outside_text_charset=[f["name"] for f in fns if not NAME_OK.match(f.get("name", ""))],
        typedef_names_outside_text_charset=["%s:%s" % (t, r.get("name")) for t in ("structs", "enums")
                                            for r in js.get(t) or [] if not NAME_OK.match(r.get("name", ""))],
        rust_vararg_functions=vararg_rust_decls,
    )


def validate_view(mdir, js, cov, island_defs=frozenset()):
    log = read(os.path.join(mdir, "validate.log"))
    r = rc(os.path.join(mdir, "validate.rc"))
    view = dict(rc=r, ok=(r == 0 and "module is well-formed" in log))
    m = re.search(r"give-back: (\d+) &mut functions kernel-certified \((\d+) declined", log)
    if m:
        view["giveback"] = dict(certified=int(m.group(1)), declined=int(m.group(2)))
    errs = re.findall(r"^\s+\[(\d+)\] (\w+)(.*)$", log, re.M)
    by_variant, attributed = {}, {}
    skipped = {s.get("name") for s in ((coverage_view(cov) or {}).get("skipped") or [])}
    fns = (js or {}).get("functions", [])
    items = []
    for _, variant, rest in errs:
        by_variant[variant] = by_variant.get(variant, 0) + 1
        cause = "UNATTRIBUTED"
        if variant == "RustAbiVararg":
            m = re.search(r"function: (\d+)", rest)
            f = fns[int(m.group(1))] if m and int(m.group(1)) < len(fns) else None
            name = fn_label(f) if f else ""
            if "<shadowed-by-clean-origin" in name:
                cause = "producer:retired-clean-origin-declaration-left-variadic"
            elif "indirect call edge" in rest:
                cause = "producer:indirect-call-edge-unknown-signature"
            elif f is not None and not f.get("blocks"):
                leaf = name.split("::")[-1]
                if leaf in skipped or name in skipped:
                    cause = "producer:skipped-clean-def-left-as-variadic-placeholder"
                elif leaf in island_defs:
                    cause = "producer:clean-def-without-Clean-body-left-as-variadic-placeholder"
                elif name.startswith("dep::"):
                    cause = "producer:cross-crate-callee-variadic-placeholder"
                else:
                    cause = "producer:upstream-callee-variadic-placeholder"
            items.append(dict(variant=variant, function=name, cause=cause))
        else:
            items.append(dict(variant=variant, text=rest.strip()[:400], cause=cause))
        attributed[cause] = attributed.get(cause, 0) + 1
    view["errors"] = len(errs)
    view["by_variant"] = by_variant
    view["by_cause"] = attributed
    view["items"] = items[:60]
    if r not in (0, None) and not errs:
        view["raw"] = log[-600:]
    return view


# The text codec is layout-agnostic: a struct prints as its field TYPES only and EnumDef.layout is not
# parsed back.  A text leg whose ONLY loss is these paths is the named format gap.
TEXT_LAYOUT_LOSS = re.compile(r"^/(enums\[\d+\]/layout|structs\[\d+\]/fields\[\d+\]/(name|offset))$")


def json_diff(x, y, p="", out=None):
    out = [] if out is None else out
    if type(x) is not type(y):
        out.append(p)
    elif isinstance(x, dict):
        for k in sorted(set(x) | set(y)):
            if k not in x or k not in y:
                out.append("%s/%s" % (p, k))
            else:
                json_diff(x[k], y[k], "%s/%s" % (p, k), out)
    elif isinstance(x, list):
        if len(x) != len(y):
            out.append(p)
        else:
            for i, (u, v) in enumerate(zip(x, y)):
                json_diff(u, v, "%s[%d]" % (p, i), out)
    elif x != y:
        out.append(p)
    return out


def roundtrip_view(mdir, js):
    view = {}
    for f in ("bin", "json", "msgpack", "text"):
        o, b, c = (rc(os.path.join(mdir, "rt-%s-%s.rc" % (f, s))) for s in ("out", "back", "cmp"))
        if o == 0 and b == 0 and c == 0:
            view[f] = dict(ok=True)
        else:
            stage = "encode" if o != 0 else "decode" if b != 0 else "byte-compare"
            log = read(os.path.join(mdir, "rt-%s-%s.log" % (f, "out" if o != 0 else "back" if b != 0 else "cmp")))
            view[f] = dict(ok=False, stage=stage, message=log.strip()[-400:])
    t = view.get("text")
    if t and not t["ok"] and t["stage"] == "byte-compare":
        try:
            back = json.load(open(os.path.join(mdir, "rt.text.json")))
            paths = json_diff(js, back)
            t["lost_paths"] = paths[:40]
            t["lost_only_layout"] = bool(paths) and all(TEXT_LAYOUT_LOSS.match(p) for p in paths)
        except (OSError, ValueError, TypeError):
            t["lost_paths"] = None
    if t and not t["ok"] and t["stage"] == "decode":
        t["parse_site"] = text_parse_site(os.path.join(mdir, "rt.text"), t["message"])
    return view


def text_parse_site(text_path, message):
    """Where the text parser stopped, read from the text the CLI printed: (`fn`|`struct`|`enum`, name) when
    the error column falls inside an `@name` of that item header, else None.  No module is rewritten."""
    m = re.search(r"parse error at (\d+):(\d+)", message)
    if not m:
        return None
    lines = read(text_path).splitlines()
    ln, col = int(m.group(1)), int(m.group(2))
    if not 1 <= ln <= len(lines):
        return None
    line = lines[ln - 1]
    hm = re.match(r"^\s*(?:[a-z]+ )*(fn|struct|enum) @(\S+?)(?:\(|\s*\{|\s*=|\s*$)", line)
    if not hm:
        hm = re.match(r"^\s*(?:[a-z]+ )*(fn|struct|enum) @(\S+)", line)
    if not hm:
        return None
    start, end = hm.start(2) + 1, hm.end(2) + 1        # 1-based columns of the name
    if not start <= col <= end + 1:
        return None
    return [hm.group(1), hm.group(2)]


def run_view(mdir):
    log = read(os.path.join(mdir, "run.log"))
    r = rc(os.path.join(mdir, "run.rc"))
    view = dict(rc=r)
    m = re.search(r"^linked (\d+) module\(s\): (\d+) function\(s\) \((\d+) defined, (\d+) builtin, (\d+) trap stub", log, re.M)
    if m:
        view["linked"] = dict(modules=int(m.group(1)), functions=int(m.group(2)), defined=int(m.group(3)),
                              builtin=int(m.group(4)), trap_stubs=int(m.group(5)))
    if r == 0:
        vals = [l for l in log.splitlines() if re.fullmatch(r"-?\d+", l.strip())]
        view["value"] = vals[-1].strip() if vals else None
        m = re.search(r"executed (\d+) step", log)
        view["steps"] = int(m.group(1)) if m else None
    else:
        err = [l for l in log.splitlines() if re.match(r"^(interpreter error|error|trap)", l)]
        view["error"] = (err[-1] if err else log.strip()[-300:])[:500]
    return view


# ---- judging helpers
def native_oracle(info):
    """(value, lanes-that-ran, problems)"""
    vals, probs = {}, []
    for lane, e in info["native"].items():
        if e.get("build_rc") == 0:
            if e.get("exec_rc") == 0:
                vals[lane] = e.get("stdout")
            else:
                probs.append("%s: program exited %s" % (lane, e.get("exec_rc")))
    distinct = set(vals.values())
    if len(distinct) > 1:
        probs.append("native lanes disagree: %s" % vals)
    v = next(iter(distinct)) if len(distinct) == 1 else None
    if v is not None and info.get("expect") is not None and str(info["expect"]) != v:
        probs.append("native output %s != hand-computed EXPECT %s" % (v, info["expect"]))
    return v, vals, probs


def judge_native(R, fid, info):
    v, vals, probs = native_oracle(info)
    refusals = {l: e for l, e in info["native"].items() if e.get("build_rc") not in (0, None)}
    if probs:
        R.add(fid + ".native", "FAIL", "; ".join(probs))
        return v
    if vals and not refusals:
        R.add(fid + ".native", "PASS", "builds+runs in %s = %s (== EXPECT)" % (sorted(vals), v))
    elif vals:
        l, e = next(iter(refusals.items()))
        sig = e.get("signature")
        if sig:
            R.add(fid + ".native", "GAP", "runs = %s in %s but %s REFUSES: %s" % (v, sorted(vals), l, sig[1]), sig[0],
                  " ## ".join(e.get("refusal", [])), sig="native:%s-refuses:%s" % (l, sig[1]))
        else:
            R.add(fid + ".native", "FAIL", "%s refused with an UNNAMED error: %s" % (l, e.get("refusal")))
    else:
        sigs = [e.get("signature") for e in refusals.values()]
        ev = " ## ".join(x for e in refusals.values() for x in e.get("refusal", [])[:2])
        if refusals and all(sigs):
            unc = sorted({d for e in refusals.values() for d in e.get("uncallable_clean_defs", [])})
            R.add(fid + ".native", "GAP", "compiler refuses the feature in every lane: %s" % sigs[0][1]
                  + ("; Clean defs that did not become callable from Rust: %s" % unc if unc else ""), sigs[0][0], ev,
                  sig="native:all-lanes-refuse:%s:uncallable=%s" % (sigs[0][1], unc))
        else:
            R.add(fid + ".native", "FAIL", "native build failed with an UNNAMED error: %s" % ev[:600])
    return v


def judge_module(R, fid, info, oracle, want_exec=True):
    """emit / validate / roundtrip / exec / twin rows for one unit.  Returns the module dict or None."""
    lane = info["module_lane"]
    em = info["emit"].get("emit", {})
    if lane == "emit":
        R.add(fid + ".emit", "PASS", "--emit=trust-ir (verify on, advisory) wrote a module, wire v%s, %s bytes"
              % (info["module"]["wire_version"], info["module"]["bytes"]))
    else:
        sig = em.get("signature")
        tail = "" if lane == "none" else " (a module exists ONLY from the -Ztrust-verify=off -Ztrust-ir-lower=on lane)"
        if sig:
            R.add(fid + ".emit", "GAP", "verified emit refused: %s%s" % (sig[1], tail), sig[0],
                  " ## ".join(map(str, em.get("refusal", []))), sig="emit:%s:fallback=%s" % (sig[1], lane))
        else:
            R.add(fid + ".emit", "FAIL", "verified emit produced no module, UNNAMED error%s: %s" % (tail, em.get("refusal")))
        if lane == "none":
            return None
    mod = info["module"]
    v = mod["validate"]
    if v["ok"]:
        R.add(fid + ".validate", "PASS", "`trust-ir validate` (the gitlink's CLI): module is well-formed")
    elif v["errors"] and set(v["by_variant"]) == {"RustAbiVararg"} and "UNATTRIBUTED" not in v["by_cause"]:
        R.add(fid + ".validate", "GAP", "%d error(s), all RustAbiVararg: %s" % (v["errors"], v["by_cause"]),
              "producer-gap", "; ".join(sorted({i["function"] for i in v["items"]}))[:500],
              sig="validate:RustAbiVararg:%s" % json.dumps(v["by_cause"], sort_keys=True))
    else:
        R.add(fid + ".validate", "FAIL", "validator errors outside the named producer defect: %s %s %s"
              % (v["by_variant"], v.get("raw", ""), [i for i in v["items"] if i["cause"] == "UNATTRIBUTED"][:3]))
    rt = mod["roundtrip"]
    bad = {k: x for k, x in rt.items() if not x["ok"]}
    if not bad:
        R.add(fid + ".roundtrip", "PASS", "bin/json/msgpack/text -> bin all byte-identical")
    elif set(bad) == {"text"} and bad["text"]["stage"] == "decode" and "parse error" in bad["text"]["message"]:
        judge_text_names(R, fid, mod, bad["text"])
    elif set(bad) == {"text"} and bad["text"].get("lost_only_layout"):
        R.add(fid + ".roundtrip", "GAP", "bin/json/msgpack byte-identical; TEXT parses back but is LOSSY, and the loss is exactly the "
              "concrete-layout facts the text format is layout-agnostic about (struct field names/offsets, EnumDef.layout): %s"
              % bad["text"]["lost_paths"][:6], "format-gap", "; ".join(bad["text"]["lost_paths"]),
              sig="roundtrip:text-lossy-layout:%s" % sorted(bad["text"]["lost_paths"]))
    else:
        R.add(fid + ".roundtrip", "FAIL", "round trip broke outside the named text defects: %s" % bad)
    if want_exec:
        judge_exec(R, fid, mod, oracle)
    judge_twins(R, fid, mod)
    return mod


def judge_exec(R, fid, mod, oracle):
    r = mod["run"]
    if r["rc"] == 0:
        if oracle is not None and r.get("value") == oracle:
            R.add(fid + ".exec", "PASS", "reference interpreter `program` = %s == native (%s steps, %s unreached trap stub(s))"
                  % (r["value"], r.get("steps"), (r.get("linked") or {}).get("trap_stubs")))
        elif oracle is None:
            R.add(fid + ".exec", "GAP", "interpreter = %s but there is NO native oracle (source refused natively)" % r.get("value"),
                  "refused", sig="exec:no-native-oracle")
        else:
            R.add(fid + ".exec", "FAIL", "DIFFERENTIAL MISMATCH interpreter=%s native=%s" % (r.get("value"), oracle))
        return
    e = r.get("error", "") or ""
    if "non-executable vararg signature" in e:
        R.add(fid + ".exec", "GAP", "interpreter refuses the callee: %s — the same variadic-placeholder declaration the validator "
              "rejects; the callee body is not in the module" % e, "producer-gap", e,
              sig="exec:non-executable-vararg-signature")
    elif re.search(r"reached extern builtin stub @clean_", e):
        stub = re.search(r"stub @(clean_\w+)", e).group(1)
        R.add(fid + ".exec", "GAP", "%s — reference interpreter has no Clean runtime ABI builtins" % e[:200], "consumer-gap", e,
              sig="exec:clean-runtime-stub:@%s" % stub)
    elif "reached extern builtin stub" in e:
        stub = (re.search(r"reached extern builtin stub @(.+?) — ", e) or re.search(r"stub @(\S+)", e)).group(1)
        # WS5.2: the interpreter names the stub by its link-time SYMBOL; attribution reads the row's
        # display path (the def path / Lean spelling the rest of this judgment speaks in).
        stub = next((fn_label(f) for f in (mod.get("_json") or {}).get("functions", []) if f.get("name") == stub), stub)
        cov = mod.get("coverage") or {}
        skipped = {x.get("name"): x.get("reason", "") for x in cov.get("skipped") or []}
        leaf = stub.split("::")[-1]
        if leaf in skipped or stub in skipped:
            key, why = "skipped-clean-def", ("a Clean def the TrustIR Clean-origin producer SKIPPED (%s), left as a body-less declaration"
                                             % (skipped.get(leaf) or skipped.get(stub))[:120])
        elif cov.get("recorded") is False:
            key, why = "verify-off-lane", "a Clean def with no Producer::Clean body (the module comes from the verify-off lane: clean_origin.recorded=false)"
        elif stub.startswith("dep::"):
            key, why = "cross-crate-def-path", "a cross-crate callee declared under its DEF-PATH, so the linked dep module's symbol does not bind to it"
        else:
            key, why = "upstream-callee", "an UPSTREAM callee (core / trust_bignum): declared with its exact signature, body not emitted into any trust-ir module"
        R.add(fid + ".exec", "GAP", "interpreter traps at the body-less declaration @%s: %s" % (stub, why), "producer-gap", e,
              sig="exec:bodyless:@%s:%s" % (stub, key))
    else:
        R.add(fid + ".exec", "FAIL", "interpreter failed outside the named signatures: %s" % e)


def judge_text_names(R, fid, mod, t):
    """A TEXT leg that does not parse back.  Attribution READS the site the parser names (no module is
    rewritten): a def-path Function.name is the producer's spelling (Function.name is the link symbol);
    a StructDef/EnumDef name is a type PATH, which no trust-ir rule makes a link symbol, so the text codec
    not reading it is a FORMAT property."""
    msg = t["message"].splitlines()[-1][:160]
    site = t.get("parse_site")
    c = mod["census"] or {}
    if site is None:
        # replay of an archived run whose printed text was not kept: the token the parser wanted names the
        # item kind (`(` after a fn name, `{` after a struct name)
        if "expected '(', got ':'" in msg and c.get("names_outside_text_charset"):
            site = ["fn", c["names_outside_text_charset"][0]]
        elif "expected '{', got ':'" in msg and c.get("typedef_names_outside_text_charset"):
            site = ["struct", c["typedef_names_outside_text_charset"][0].split(":", 1)[1]]
    if site and site[0] == "fn" and not NAME_OK.match(site[1]):
        R.add(fid + ".roundtrip", "GAP", "bin/json/msgpack byte-identical; TEXT does not parse back: %s — at the def-path Function.name "
              "%r (%d such name(s) in the module); Function.name is normatively the link-time symbol and display_path is where a "
              "def-path belongs" % (msg, site[1], len(c.get("names_outside_text_charset") or [])), "producer-gap",
              json.dumps(c.get("names_outside_text_charset") or [])[:600], sig="roundtrip:text-parse:fn-name")
    elif site and site[0] in ("struct", "enum") and not NAME_OK.match(site[1]):
        R.add(fid + ".roundtrip", "GAP", "bin/json/msgpack byte-identical; TEXT does not parse back: %s — at the %s name %r, a type "
              "PATH the binary/JSON/MessagePack codecs and the validator accept: the text codec is not total over names (format)"
              % (msg, site[0], site[1]), "format-gap", json.dumps(c.get("typedef_names_outside_text_charset") or [])[:600],
              sig="roundtrip:text-parse:%s-name" % site[0])
    else:
        R.add(fid + ".roundtrip", "FAIL", "TEXT does not parse back (%s) at a site that is not a name outside the text alphabet: %s"
              % (msg, site))


def judge_twins(R, fid, mod):
    tw = mod.get("twins")
    if not tw:
        R.add(fid + ".twin", "FAIL", "negative twins did not run (twins.json missing)")
        return
    for key in ("codec.trailing", "validate.site", "validate.vararg"):
        t = tw.get(key)
        if not t:
            continue
        good = t.get("refused") and t.get("right_reason")
        R.add("%s.twin.%s" % (fid, key), "PASS" if good else "FAIL",
              "%s => " % t["mutation"] + ("refused for the right reason: " if good else "NOT refused for the right reason: ")
              + squash(t.get("log", ""))[-230:])
    t = tw.get("exec.mutant")
    if t:
        blind = [x["mutation"] for x in t.get("tried", []) if not x["observed"]]
        if t.get("observed"):
            hit = next(x for x in t["tried"] if x["observed"])
            R.add(fid + ".twin.exec.mutant", "PASS", "%s => interpreter %s -> %s" % (
                hit["mutation"], t["original"], hit["mutant"] if hit["mutant_rc"] == 0 else "TRAP: " + str(hit["mutant_error"]))
                + (" (output-insensitive candidates tried first: %s)" % blind if blind else ""))
        else:
            R.add(fid + ".twin.exec.mutant", "FAIL", "no tried mutation changed the interpreter result %s: %s" % (t.get("original"), blind))


def clean_fn(js, name):
    for f in js.get("functions", []):
        if fn_label(f) == name and f.get("producer") == "Clean":
            return f
    return None


def fn_insts(f):
    out = []
    for b in f.get("blocks", []):
        for n in b.get("body", []):
            i = n.get("inst")
            out.append(i if isinstance(i, str) else next(iter(i)))
    return out


def contract_disclosure_text(js):
    return json.dumps([s for s in js.get("spec_modules") or [] if "contract-disclosure" in (s.get("name") or "")])


def judge_dep_carried(R, mod):
    """dep.rs = a contracted Rust `pub fn` + an exported gate-tier Clean def.  What does dep's OWN module carry?"""
    js, c, cov = mod["_json"], mod["census"], mod["coverage"] or {}
    if js is None:
        R.add("a.unit.dep.carried.clean_def", "FAIL", "module JSON unavailable")
        return
    f = clean_fn(js, "dep_mix")
    e = next((x for x in cov.get("emitted", []) if x.get("name") == "dep_mix"), {})
    if f and f.get("blocks"):
        R.add("a.unit.dep.carried.clean_def", "PASS", "dep_mix is a Producer::Clean body (%s), sidecar tier=%s body_gate=%s, linkage=%s, "
              "in-module body_gate=%s" % ("+".join(fn_insts(f)), e.get("tier"), e.get("body_gate"), f.get("linkage"),
                                          json.dumps(f.get("body_gate"))))
    else:
        R.add("a.unit.dep.carried.clean_def", "FAIL", "dep_mix has no Producer::Clean body in dep's module")
    text = contract_disclosure_text(js)
    seen = [k for k in ("requires", "ensures") if '\\"kind\\":\\"%s\\"' % k in text]
    clamp = next((x for x in js["functions"] if fn_label(x).split("::")[-1] == "dep_clamp"), None)
    if clamp is not None and clamp.get("summary"):
        R.add("a.unit.dep.carried.contract", "PASS", "dep_clamp carries a FunctionSummary: %s" % json.dumps(clamp["summary"])[:300])
    else:
        R.add("a.unit.dep.carried.contract", "GAP", "dep_clamp's `requires hi >= 1` / `ensures result <= hi` reach dep's module only as "
              "DesignOnly disclosure strings %s; Function.summary is null, obligations=%s, certificates=%s — so there is nothing an "
              "importer's `backed_by` / `InheritedFromCallee{external}` could name" % (seen, c["obligation_kinds"], c["certificates"]),
              "producer-gap", sig="carried:dep_clamp.summary=null:disclosed=%s:certificates=%d" % (seen, c["certificates"]))


def judge_inductive_exec(R, mod):
    """Execute the emitted general-tier inductive+match body through inductive_driver.trust_ir (linked by symbol)."""
    log, r = read(os.path.join(mod["dir"], "drive-inductive.log")), rc(os.path.join(mod["dir"], "drive-inductive.rc"))
    vals = [l.strip() for l in log.splitlines() if re.fullmatch(r"-?\d+", l.strip())]
    m = re.search(r"reached extern builtin stub @(clean_\w+|l_\w+)", log)
    if r is None:
        R.add("a.lean.inductive_in_module.exec_body", "FAIL", "inductive driver did not run")
    elif r == 0 and vals and vals[-1] == "2":
        R.add("a.lean.inductive_in_module.exec_body", "PASS", "symbol-linked driver: triRank(Tri.two) = 2 (hand-computed; the compiler "
              "admits no native route to this body, so there is NO native oracle)")
    elif m:
        R.add("a.lean.inductive_in_module.exec_body", "GAP", "the emitted triRank body CANNOT be executed by the reference interpreter: a "
              "symbol-linked driver (clean_box_uint64(1) -> triRank) traps at the body-less Clean runtime-ABI extern @%s; the CLI's builtin "
              "set knows mem*/__rust_alloc*/core intrinsics and no clean_* name" % m.group(1), "consumer-gap", log.strip()[-300:],
              sig="exec_body:clean-runtime-stub:@%s" % m.group(1))
    else:
        R.add("a.lean.inductive_in_module.exec_body", "FAIL", "rc=%s: %s" % (r, log.strip()[-300:]))


LEAN_DEFS = {   # feature -> clean defs that should arrive as Producer::Clean bodies
    "lean.wrapping_uint64": ["wsum", "addmul", "wsub"],
    "lean.projection_literal": ["snd", "k32"],
    "lean.bool_cmp": ["lt", "eqf"],
    "lean.bool_connective": ["neg", "conj", "disj"],
    "lean.let": ["sq_let", "nested_let"],
    "lean.select": ["min2"],
    "lean.inductive_in_module": ["triRank"],
    "lean.inductive_called": ["triRank"],
    "lean.inductive_wrapped": ["triRank", "rankOfTwo"],
    "lean.nat_structural": ["tozero"],
    "lean.nat_wf": ["countdownSum"],
    "two_lang.lean_calls_rust": ["thrice_rx"],
}
CONTRACT_KINDS = ("Precondition", "Postcondition", "LoopInvariant", "Termination", "Liveness")


def judge_carried(R, fid, mod):
    """Feature-specific: is the feature CARRIED by the module (not merely compiled)?  Ids are unprefixed here."""
    js, c, cov = mod["_json"], mod["census"], mod["coverage"] or {}
    if js is None:
        R.add(fid + ".carried", "FAIL", "module JSON unavailable")
        return
    if fid in LEAN_DEFS and cov.get("recorded") is False:
        rust_side = [fn_label(f) for f in js["functions"] if fn_label(f).split("::")[-1] in LEAN_DEFS[fid]]
        R.add(fid + ".carried", "GAP", "the only module this compiler writes for this crate comes from the -Ztrust-verify=off lane, whose "
              "coverage says clean_origin.recorded=false: no Producer::Clean body; the defs appear only as body-less declarations %s"
              % rust_side, "producer-gap", sig="carried:verify-off-lane:clean_origin.recorded=false")
        return
    if fid in LEAN_DEFS:
        emitted = {e["name"]: e for e in cov.get("emitted", [])}
        skipped = {s["name"]: s for s in cov.get("skipped", [])}
        ok, gaps, fails, sigs = [], [], [], []
        for d in LEAN_DEFS[fid]:
            f = clean_fn(js, d)
            gen = next((g for g in (cov.get("general") or []) if isinstance(g, dict) and g.get("clean_name") == d), None) \
                if isinstance(cov.get("general"), list) else None
            if f and f.get("blocks") and gen and d not in emitted:
                stubs = sorted({x["name"] for x in js["functions"] if x["name"].startswith("clean_") and not x.get("blocks")})
                ok.append("%s[tier=%s/%s/tv_mint_certified=%s/in-module body_gate=%s; boxed `ptr` values over %d body-less clean_* "
                          "runtime-ABI declarations; %s; NOT reachable from Rust, so NOT covered by the differential]"
                          % (d, gen.get("tier"), gen.get("disposition"), gen.get("tv_mint_certified"), json.dumps(f.get("body_gate")),
                             len(stubs), "+".join(sorted(set(fn_insts(f))))))
            elif f and f.get("blocks"):
                e = emitted.get(d, {})
                ok.append("%s[%s/tier=%s/sidecar body_gate=%s/in-module body_gate=%s; %s]" % (
                    d, e.get("shape"), e.get("tier"), e.get("body_gate"), json.dumps(f.get("body_gate")), "+".join(fn_insts(f)) or "no-insts"))
            elif d in skipped:
                gaps.append("%s SKIPPED by the TrustIR Clean-origin producer: %s" % (d, skipped[d]["reason"][:260]))
                sigs.append("%s:skipped:%s" % (d, squash(skipped[d]["reason"])[:200]))
            else:
                fails.append("%s: no Producer::Clean body and no `skipped` disclosure" % d)
        if fails:
            R.add(fid + ".carried", "FAIL", "; ".join(fails + gaps))
        elif gaps:
            R.add(fid + ".carried", "GAP", "; ".join(gaps) + (" | carried: %s" % ", ".join(ok) if ok else ""), "producer-gap",
                  sig="carried:" + " || ".join(sigs))
        else:
            R.add(fid + ".carried", "PASS", "Producer::Clean bodies in the crate module: " + ", ".join(ok))
        return
    if fid in ("rust.contracts", "rust.loop_invariant"):
        want = {"rust.contracts": ("requires", "ensures", "decreases"), "rust.loop_invariant": ("invariant", "decreases")}[fid]
        ck = {k: v for k, v in c["obligation_kinds"].items() if k in CONTRACT_KINDS}
        vt = mod.get("_verification_totals")
        if ck:
            R.add(fid + ".obligations", "PASS", "contract-kind obligations in-module: %s; statuses %s" % (ck, c["obligation_statuses"]))
        else:
            R.add(fid + ".obligations", "GAP", "NO contract-kind ProofObligation (none of %s) reaches the module: kinds=%s, statuses=%s, "
                  "certificates=%s — while the SAME compiler, same flags, reports %s for this crate (its verdicts stay in the build log)"
                  % (list(CONTRACT_KINDS), c["obligation_kinds"], c["obligation_statuses"], c["certificates"], vt), "producer-gap",
                  sig="obligations:no-contract-kind:kinds=%s:certificates=%d" % (sorted(c["obligation_kinds"]), c["certificates"]))
        if fid == "rust.loop_invariant":
            # a loop `invariant` is NOT a FunctionSummary clause: its carrier is an ObligationKind::LoopInvariant row
            # (formula + v34 site).  A populated summary (the fn's `requires`) must not pass this row.
            li = [o for o in js.get("proof_obligations") or [] if o.get("kind") == "LoopInvariant"]
            if li and all(o.get("site") and o.get("formula") for o in li):
                R.add(fid + ".carried", "PASS", "%d LoopInvariant obligation(s) with site + formula; statuses %s" % (len(li), c["obligation_statuses"]))
                return
        elif c["summary_populated"]:
            # look for the AUTHORED clauses on the functions that authored them, not for "some summary somewhere"
            by = {fn_label(f).split("::")[-1]: (f.get("summary") or {}) for f in js["functions"]}
            need = [("clamp_add", "requires", 2), ("clamp_add", "ensures", 1), ("countdown", "decreases", 1)]
            short = ["%s.%s: %d/%d" % (fn, k, len(by.get(fn, {}).get(k) or []), n) for fn, k, n in need
                     if len(by.get(fn, {}).get(k) or []) < n]
            unbound = [fn for fn in ("clamp_add", "countdown") for k in ("requires", "ensures", "decreases")
                       for cl in (by.get(fn, {}).get(k) or []) if not (isinstance(cl, dict) and cl.get("bindings"))]
            if not short and not unbound:
                R.add(fid + ".carried", "PASS", "FunctionSummary carries clamp_add requires x2 + ensures x1 and countdown decreases x1, "
                      "every clause with bindings (%d binding(s)); proved flags: %s" % (
                          c["clause_bindings"], {fn: by[fn].get("proved") for fn in ("clamp_add", "countdown")}))
            else:
                R.add(fid + ".carried", "GAP", "FunctionSummary is populated but INCOMPLETE: missing clauses %s; clauses with EMPTY bindings "
                      "(= unbindable) on %s" % (short, sorted(set(unbound))), "producer-gap",
                      sig="carried:summary-incomplete:%s:unbound=%s" % (short, sorted(set(unbound))))
            return
        text = contract_disclosure_text(js)
        seen = [k for k in want if '\\"kind\\":\\"%s\\"' % k in text or '"kind\\":\\"%s' % k in text or ":%s:" % k in text]
        if seen:
            R.add(fid + ".carried", "GAP", "clauses %s reach the module ONLY as JSON strings inside the DesignOnly SpecModule "
                  "`@trust-internal::contract-disclosure-v1`; Function.summary is null on every function; missing kinds: %s"
                  % (seen, [k for k in want if k not in seen]), "producer-gap",
                  sig="carried:disclosure-only:%s:summary=null" % seen)
        else:
            R.add(fid + ".carried", "GAP", "no FunctionSummary and no contract disclosure for %s: the clauses do not reach the module at all"
                  % (want,), "producer-gap", sig="carried:absent:%s" % list(want))
        return
    if fid in ("rust.slice_index", "rust.checked_arith"):
        kind = {"rust.slice_index": "BoundsCheck", "rust.checked_arith": "ArithmeticSafety"}[fid]
        n = c["obligation_kinds"].get(kind, 0)
        descs = [o.get("description", "") for o in js.get("proof_obligations") or [] if o.get("kind") == kind]
        need = {"rust.slice_index": ["bounds"], "rust.checked_arith": ["overflow", "div_by_zero"]}[fid]
        missing = [w for w in need if not any(w in d.lower().replace("-", "_").replace(" ", "_") or (w == "bounds" and "index" in d.lower())
                                              for d in descs)]
        if n and c["obligations_with_site"] >= n and missing:
            R.add(fid + ".carried", "FAIL", "%d %s obligation(s) but none describes %s: %s" % (n, kind, missing, [d[:90] for d in descs]))
        elif n and c["obligations_with_site"] >= n:
            R.add(fid + ".carried", "PASS", "%d %s obligation(s) covering %s (by description), each with function scope + v34 site; "
                  "statuses %s; formula populated on %d/%d" % (n, kind, need, c["obligation_statuses"], c["obligations_with_formula"],
                                                              c["obligations"]))
        else:
            R.add(fid + ".carried", "FAIL", "expected sited %s obligations, got kinds=%s sited=%s" % (kind, c["obligation_kinds"],
                                                                                                     c["obligations_with_site"]))
        return
    if fid == "rust.struct_enum_match":
        if c["structs"] and c["enums"] and c["inst_histogram"].get("Switch"):
            R.add(fid + ".carried", "PASS", "%d StructDef, %d EnumDef (%d with a normative layout descriptor), Switch x%d"
                  % (c["structs"], c["enums"], c["enum_layout_descriptors"], c["inst_histogram"]["Switch"]))
        else:
            R.add(fid + ".carried", "FAIL", "structs=%s enums=%s Switch=%s" % (c["structs"], c["enums"], c["inst_histogram"].get("Switch")))
        return
    if fid == "rust.closure":
        names = [fn_label(f) for f in js["functions"] if "closure" in fn_label(f)]
        if c["closure_types"]:
            R.add(fid + ".carried", "PASS", "%d ClosureTy; closure bodies %s" % (c["closure_types"], names))
        elif names:
            R.add(fid + ".carried", "GAP", "closure body lowered as a plain function %s over an env aggregate; Ty::Closure/ClosureTy unused "
                  "(closure_types=0)" % names, "producer-gap", sig="carried:closure-as-plain-fn:closure_types=0")
        else:
            R.add(fid + ".carried", "FAIL", "no closure body and no ClosureTy in the module")
        return
    if fid == "rust.u128":
        want = str(0xFFFF_FFFF_0000_0000_0000_0000_0000_0000)
        consts = [n["Const"]["value"]["U128"] for n in walk(js["functions"])
                  if isinstance(n, dict) and isinstance(n.get("Const"), dict) and isinstance(n["Const"].get("value"), dict)
                  and "U128" in n["Const"]["value"]]
        if want in [str(x) for x in consts]:
            R.add(fid + ".carried", "PASS", "Constant::U128 (value > i128::MAX) carries 0xFFFFFFFF<<96 exactly: %s" % consts)
        else:
            R.add(fid + ".carried", "FAIL", "the literal above i128::MAX is not carried as Constant::U128 == %s; U128 constants seen: %s"
                  % (want, consts))
        return
    if fid == "rust.mut_ref":
        blob = json.dumps(js.get("func_types"))
        gb = mod["validate"].get("giveback")
        if "RefMut" in blob or "BorrowMut" in c["inst_histogram"]:
            R.add(fid + ".carried", "PASS", "RefMut in a signature / BorrowMut x%d; give-back pass: %s" % (c["inst_histogram"].get("BorrowMut", 0), gb))
        else:
            R.add(fid + ".carried", "GAP", "`&mut u64` parameter is not spelled Ty::RefMut (func_types=%s); no BorrowMut/EndBorrow; give-back "
                  "pass: %s" % (blob[:200], gb), "producer-gap", sig="carried:no-RefMut:no-BorrowMut")
        return
    if fid == "rust.std_call":
        v = [n for n in c["rust_vararg_functions"] if "wrapping_add" in n]
        if v:
            R.add(fid + ".carried", "GAP", "the `core` callee is a body-less Rust-ABI VARIADIC placeholder under a def-path name: %s" % v,
                  "producer-gap", sig="carried:core-callee-variadic-placeholder:%s" % v)
        else:
            f = [f for f in js["functions"] if "wrapping_add" in fn_label(f)]
            if f and f[0].get("blocks"):
                R.add(fid + ".carried", "PASS", "the upstream callee arrives WITH a body: %s" % [(fn_label(x), len(x["blocks"])) for x in f])
            elif f:
                ft = js["func_types"][f[0]["ty"]]
                R.add(fid + ".carried", "GAP", "the `core` callee is a body-less declaration %r with its exact signature %s->%s (validates), "
                      "under a DEF-PATH name, body NOT emitted: the call edge is carried, the callee is not"
                      % (fn_label(f[0]), ft["params"], ft["returns"]), "producer-gap",
                      sig="carried:core-callee-bodyless:%s" % fn_label(f[0]))
            else:
                R.add(fid + ".carried", "FAIL", "no row for the upstream callee at all")
        return
    if fid == "two_lang.citation":
        cert = c["certificate_evidence"]
        if c["obligation_statuses"].get("Certified") and cert.get("CleanCic"):
            R.add(fid + ".carried", "PASS", "Certified obligation + CleanCic certificate in-module: %s" % cert)
        else:
            R.add(fid + ".carried", "GAP", "the compiler reports the citation kernel-discharged, but the module carries no Certified status and "
                  "no CleanCic certificate (obligation kinds %s, statuses %s, certificates %s). What DOES arrive: the theorem as a "
                  "general-tier Producer::Clean FUNCTION %s — a computational row, not a proof row"
                  % (c["obligation_kinds"], c["obligation_statuses"], c["certificates"],
                     [(g.get("clean_name"), g.get("disposition")) for g in (cov.get("general") or []) if isinstance(g, dict)]),
                  "producer-gap", sig="carried:citation:certified=%s:clean_cic=%s" % (
                      c["obligation_statuses"].get("Certified", 0), cert.get("CleanCic", 0)))
        return
    if fid == "two_lang.cross_crate":
        decls = [(f["name"], f.get("producer")) for f in js["functions"] if not f.get("blocks") and "dep" in fn_label(f)]
        dep_defined = []
        try:
            dj = json.load(open(os.path.join(os.path.dirname(os.path.dirname(mod["dir"])), "dep", "module", "module.json")))
            dep_defined = [(f["name"], f.get("producer")) for f in dj["functions"] if f.get("blocks")]
        except (OSError, ValueError):
            pass
        linkable = [n for n, _ in decls if n in {d for d, _ in dep_defined}]
        if c["imports"] and len(linkable) == len(decls):
            R.add(fid + ".carried", "PASS", "Module.imports has %d row(s); declarations %s link by symbol to dep's %s"
                  % (c["imports"], decls, dep_defined))
        else:
            blob = json.dumps(js)
            var = [js["func_types"][f["ty"]].get("is_vararg") for f in js["functions"] if not f.get("blocks") and "dep" in fn_label(f)]
            shape = "VARIADIC placeholder" if var and all(var) else "exact-signature (non-variadic)" if var and not any(var) else "mixed-signature"
            sees = [k for k in ("hi >= 1", "result <= hi", 'dep_clamp\\",\\"kind') if k in blob]
            R.add(fid + ".carried", "GAP", "Module.imports rows=%d; `backed_by`/ExternRef occurrences in the importer's JSON: %d/%d; dep's "
                  "contract text visible in the importer: %s; the cross-crate edges are body-less %s declarations under DEF-PATH names %s, "
                  "while the dep module defines %s: %d/%d names match, so link-by-symbol cannot bind them"
                  % (c["imports"], blob.count("backed_by"), blob.count("ExternRef"), sees or "none", shape, decls, dep_defined,
                     len(linkable), len(decls)), "producer-gap",
                  sig="carried:cross-crate:imports=%d:linkable=%d/%d:%s" % (c["imports"], len(linkable), len(decls), shape))
        return
    R.add(fid + ".carried", "FAIL", "no carried-check defined for this feature")


def judge_carried_wrap(R, fid, mod):
    before = len(R.rows)
    judge_carried(R, fid, mod)
    for r in R.rows[before:]:
        r["id"] = "a." + r["id"]


SURFACES = [
    ("wire_v41_plus", "binary wire version >= 41 selected by the writer", lambda u: (u["module"]["wire_version"] or 0) >= 41),
    ("producer_tags", "both Producer::Trust and Producer::Clean rows in one Module",
     lambda u: {"Trust", "Clean"} <= set(u["module"]["census"]["producers"])),
    ("body_gate", "Function.body_gate populated", lambda u: u["module"]["census"]["body_gate_populated"] > 0),
    ("display_path", "Function.display_path populated on ANY row", lambda u: u["module"]["census"]["display_path_populated"] > 0),
    ("display_path_rust", "Function.display_path populated on the Rust-producer DEFINITIONS",
     lambda u: u["module"]["census"]["display_path_on_rust_definitions"] > 0),
    ("summary", "FunctionSummary populated", lambda u: u["module"]["census"]["summary_populated"] > 0),
    ("bindings", "ProofFormula.bindings populated", lambda u: u["module"]["census"]["clause_bindings"] > 0),
    ("imports", "Module.imports populated", lambda u: u["module"]["census"]["imports"] > 0),
    ("tuple_layouts", "Module.tuple_layouts populated", lambda u: u["module"]["census"]["tuple_layouts"] > 0),
    ("handle", "Ty::Handle present", lambda u: u["module"]["census"]["handle_types"] > 0),
    ("obligations", "proof obligations present", lambda u: u["module"]["census"]["obligations"] > 0),
    ("obligation_site", "every obligation carries function scope + site",
     lambda u: u["module"]["census"]["obligations"] > 0 and u["module"]["census"]["obligations_with_site"] == u["module"]["census"]["obligations"]),
    ("obligation_formula", "ProofObligation.formula populated", lambda u: u["module"]["census"]["obligations_with_formula"] > 0),
    ("non_pending_status", "any obligation status other than Pending",
     lambda u: any(k != "Pending" for k in u["module"]["census"]["obligation_statuses"])),
    ("certificates", "proof certificates present", lambda u: u["module"]["census"]["certificates"] > 0),
    ("target_info", "Module.target_info populated (triple + pointer size + endianness)",
     lambda u: bool((u["module"]["census"]["target_info"] or {}).get("triple"))),
    ("struct_passing_classified", "target_info.struct_passing is a concrete ABI policy (not Unclassified)",
     lambda u: (u["module"]["census"]["target_info"] or {}).get("struct_passing") not in (None, "Unclassified")),
    ("symbol_names", "every Function.name is inside the text charset (link-symbol-shaped)",
     lambda u: not u["module"]["census"]["names_outside_text_charset"]),
]


def surface(R, units):
    units = {n: u for n, u in units.items() if u.get("module") and u["module"].get("census")}
    for key, desc, pred in SURFACES:
        hits = sorted(n for n, u in units.items() if pred(u))
        if hits and (key not in ("obligation_site", "symbol_names")
                     or len(hits) == len([n for n in units if key != "obligation_site" or units[n]["module"]["census"]["obligations"]])):
            R.add("a.surface." + key, "PASS", "%s: %d/%d emitted modules (%s%s)" % (desc, len(hits), len(units), ", ".join(hits[:5]),
                                                                                   "..." if len(hits) > 5 else ""))
        elif hits:
            miss = sorted(set(units) - set(hits))
            R.add("a.surface." + key, "GAP", "%s: only %d/%d modules; failing: %s" % (desc, len(hits), len(units), ", ".join(miss[:8])),
                  "producer-gap", sig="surface:%s:populated_in=%s" % (key, hits))
        else:
            R.add("a.surface." + key, "GAP", "%s: 0/%d emitted modules — the format carrier exists, this compiler never writes it"
                  % (desc, len(units)), "producer-gap", sig="surface:%s:populated_in=[]" % key)
    tiers = {}
    for n, u in units.items():
        for e in (u["module"].get("coverage") or {}).get("emitted", []):
            tiers.setdefault("%s/tier=%s/body_gate=%s" % (e["shape"], e["tier"], e["body_gate"]), []).append("%s:%s" % (n, e["name"]))
    in_band = sum(u["module"]["census"]["body_gate_populated"] for u in units.values())
    disagree = []
    for n, u in units.items():
        bg = u["module"]["census"].get("body_gate_by_fn") or {}
        for e in (u["module"].get("coverage") or {}).get("emitted", []):
            g = bg.get(e["name"])
            want_gated = e.get("body_gate") == "carrier-faithful"
            is_gated = isinstance(g, dict) and "Gated" in g
            if not (g is not None and want_gated == is_gated):
                disagree.append("%s:%s[sidecar=%s, in-module=%s]" % (n, e["name"], e.get("body_gate"), json.dumps(g)))
    tv_cert = sum(1 for u in units.values() if u["module"]["census"]["obligation_kinds"].get("TranslationValidation")
                  and u["module"]["census"]["certificate_evidence"].get("CleanCic"))
    if tiers and tv_cert:
        R.add("a.surface.clean_tier_in_band", "PASS", "%d module(s) carry a TranslationValidation obligation + CleanCic certificate for their "
              "Clean-origin bodies; tiers: %s" % (tv_cert, sorted(tiers)))
    elif tiers and in_band:
        earned = [d for d in disagree if "sidecar=carrier-faithful" in d]
        R.add("a.surface.clean_tier_in_band", "GAP", "Function.body_gate IS written (%d function(s)) but it is a CODEGEN LICENSE, not the "
              "tier: %d def(s) the sidecar records as tier=gate/carrier-faithful are stamped otherwise (e.g. %s); the earned evidence "
              "reaches the module only as DesignOnly SpecModule text + coverage.json; a TranslationValidation obligation at Certified "
              "with ProofEvidence::CleanCic is never emitted. tiers seen: %s" % (in_band, len(earned), earned[:2], sorted(tiers)),
              "producer-gap", sig="clean_tier_in_band:body_gate-written:earned-not-gated:tv_cert=0")
    elif tiers:
        R.add("a.surface.clean_tier_in_band", "GAP", "per-Clean-def tier/body_gate exists ONLY in the coverage.json sidecar and as JSON text in "
              "a DesignOnly SpecModule invariant; tiers seen: %s" % sorted(tiers), "producer-gap",
              sig="clean_tier_in_band:sidecar-only:tv_cert=0")
    else:
        R.add("a.surface.clean_tier_in_band", "FAIL", "no Clean-origin rows recorded in any coverage sidecar")


def attrib_view(out):
    A = os.path.join(out, "attrib")
    val = lambda n: read(os.path.join(A, n + ".validate.log"))
    runlog = read(os.path.join(A, "bool_not_xor.run.log"))
    vals = [l.strip() for l in runlog.splitlines() if re.fullmatch(r"-?\d+", l.strip())]
    m = re.search(r"\[0\] (\w+ \{[^\n]*\})", val("bool_not_unop"))
    return dict(unop=m.group(1) if m else None, xor_valid="module is well-formed" in val("bool_not_xor"),
                xor_value=vals[-1] if vals and rc(os.path.join(A, "bool_not_xor.run.rc")) == 0 else None,
                utf8_rc=rc(os.path.join(A, "text_utf8_comment.validate.rc")), utf8_log=val("text_utf8_comment").strip()[:300],
                unop_ok="module is well-formed" in val("bool_not_unop"))


def attrib_rows(R, at, p12b_native):
    nat = p12b_native
    if at["unop"] and "BinOpRequiresInteger" in at["unop"] and at["xor_valid"]:
        ok_val = nat is None or at["xor_value"] == nat
        variant = at["unop"].split(" ", 1)[0]
        R.add("a.format.unop_not_bool", "GAP" if ok_val else "FAIL",
              "scalar `not bool` is refused by the validator (%s) although `and/or/xor bool` are accepted. Closest well-formed module: "
              "bool_not_xor.trust_ir (validates, program=%s%s); single change `xor bool %%b,true` -> `not bool %%b` => the error above"
              % (at["unop"], at["xor_value"], " == native p12b %s" % nat if nat is not None else "; no native p12b oracle"),
              "format-gap" if ok_val else None, sig="unop_not_bool:%s:op=not" % variant if ok_val else None)
    elif at["unop"] is None and at.get("unop_ok"):
        R.add("a.format.unop_not_bool", "PASS", "scalar `not bool` validates (gap closed)")
    else:
        R.add("a.format.unop_not_bool", "FAIL", "attribution modules behaved unexpectedly: %s" % at)
    if at["utf8_rc"] == 101 and "panicked at" in at["utf8_log"] and "parser.rs" in at["utf8_log"]:
        R.add("a.format.text_parser_utf8", "GAP", "the text PARSER PANICS (exit 101, not a ParseError) on one multi-byte UTF-8 character "
              "in a `;` comment: %s" % squash(at["utf8_log"])[:200], "format-gap", at["utf8_log"],
              sig="text_parser_utf8:exit=101:panic-in-parser.rs")
    elif at["utf8_rc"] in (0, 1, 2):
        R.add("a.format.text_parser_utf8", "PASS", "text parser handles a multi-byte comment without panicking (rc=%s)" % at["utf8_rc"])
    else:
        R.add("a.format.text_parser_utf8", "FAIL", "rc=%s: %s" % (at["utf8_rc"], at["utf8_log"]))


FORMAT_TWINS = [
    ("format.text_fn_name", "a.format.text_fn_name", "a Function.name outside alphanumeric|_|.|$ (e.g. a def-path)"),
    ("format.text_typedef_name", "a.format.text_typedef_name", "a StructDef.name that is a type PATH (`m::Pt<u8>`)"),
]


def format_rows(R, units):
    """FORMAT ratchets: a module the compiler emitted that VALIDATES, plus ONE rename; observed: validator ok,
    bin->bin identical, text does not parse."""
    for key, fid, what in FORMAT_TWINS:
        hit = next(((n, u["module"]["twins"][key]) for n, u in sorted(units.items())
                    if u.get("module") and (u["module"].get("twins") or {}).get(key)), None)
        if hit is None:
            R.add(fid, "FAIL", "no emitted module was eligible for the %s twin (needs a validating module whose names are all text-safe)" % key)
            continue
        n, t = hit
        if t.get("validate_ok") and t.get("bin_roundtrip_identical") and t.get("text_encode_rc") == 0 \
                and t.get("text_decode_rc") not in (0, None) and "parse error" in t.get("text_decode_log", ""):
            R.add(fid, "GAP", "text codec is not total over names the rest of the format accepts: %s. Specimen %s: %s => validator "
                  "`module is well-formed`, bin->bin byte-identical, text PRINTS but does not parse back: %s"
                  % (what, n, t["mutation"], t["text_decode_log"][-90:]), "format-gap", n,
                  sig="%s:validates:bin-identical:text-parse-refused" % key)
        elif t.get("validate_ok") and t.get("text_identical"):
            R.add(fid, "PASS", "text codec round-trips %s byte-identically (gap closed) — specimen %s" % (t["mutation"], n))
        else:
            R.add(fid, "FAIL", "%s twin on %s behaved unexpectedly: %s" % (key, n, t))


NEG = [
    # (step, must_build, right-reason regex, what it twins)
    ("n01_POS_true_ensures", True, None, "rust.contracts positive control (strict)"),
    ("n01_NEG_false_ensures", False, r"\[postcond\] (FAILED|UNKNOWN)[\s\S]*strict verification failed", "rust.contracts: FALSE ensures"),
    ("p18_POS_strict", True, r"citation `min2_le_left` kernel-discharges", "two_lang.citation positive control (strict, lib)"),
    ("n18_NEG_wrong_citation", False, r"citation `nat_le_doubled` failed the strict Clean statement/certification audit",
     "two_lang.citation: WRONG theorem cited"),
    ("n10_NEG_false_island_theorem", False, r"`pick_wrong` did not elaborate: Type mismatch", "island: FALSE theorem"),
]


def negatives(R, out):
    N = os.path.join(out, "neg")
    for stepn, must_build, rx, what in NEG:
        r, log = rc(os.path.join(N, stepn + ".rc")), read(os.path.join(N, stepn + ".log"))
        errs = first_errors(log, limit=4, width=500)
        if r is None:
            R.add("a.neg." + stepn, "FAIL", "negative-twin lane did not run")
        elif must_build:
            good = r == 0 and (rx is None or re.search(rx, log))
            R.add("a.neg." + stepn, "PASS" if good else "FAIL",
                  "%s: builds under the default STRICT policy (rc=%s)" % (what, r) if good else "%s: rc=%s %s" % (what, r, errs))
        else:
            m = re.search(rx, log)
            how = ""
            if stepn == "n01_NEG_false_ensures" and m:
                how = " — the postcondition is reported " + m.group(1) + (
                    ", i.e. refused fail-closed as unproved, not REFUTED with a counterexample" if m.group(1) == "UNKNOWN" else "")
            good = r not in (0, None) and m
            R.add("a.neg." + stepn, "PASS" if good else "FAIL",
                  ("%s: refused for the right reason%s: " % (what, how) if good else "%s: rc=%s, right-reason text absent: " % (what, r))
                  + " ## ".join(errs)[:420])


LEAN_REFUSAL = re.compile(r"refus|REFUSED|not .*admitted|unsupported|no-total-carrier|carrier", re.I)


def lean_rows(R, out):
    """a.lean.*: the standalone Lean lane as Part A drove it (Lib.lean / Use.lean / L_*.lean)."""
    L = os.path.join(out, "lean")
    if not os.path.isdir(L):
        R.add("a.lean.lane", "FAIL", "standalone Lean lane not run")
        return
    both, bad = read(os.path.join(L, "check-both.log")), read(os.path.join(L, "check-bad.log"))
    if rc(os.path.join(L, "check-both.rc")) == 0 and len(re.findall(r"^PROVED ", both, re.M)) == 2:
        R.add("a.lean.check", "PASS", "`targo trust check Lib.lean Use.lean`: both PROVED by the in-process Clean CIC kernel; Use.lean "
              "`import Lib` resolves from local source")
    else:
        R.add("a.lean.check", "FAIL", both.strip()[-300:])
    if "REJECTED" in bad and rc(os.path.join(L, "check-bad.rc")) != 0:
        R.add("a.lean.check.negative_twin", "PASS", "false theorem REJECTED: " + squash(bad)[:200])
    else:
        R.add("a.lean.check.negative_twin", "FAIL", "Bad.lean was not rejected (rc=%s): %s" % (rc(os.path.join(L, "check-bad.rc")), bad[-200:]))
    lib_names = set()
    for f in ("Lib", "Use"):
        env_p = os.path.join(L, f + ".irlib.json")
        if not os.path.exists(env_p):
            R.add("a.lean.build." + f, "FAIL", "no envelope: " + read(os.path.join(L, "build-%s.log" % f)).strip()[-300:])
            continue
        env = json.load(open(env_p))
        mod = load_module(os.path.join(L, f, "module"))
        js = mod.pop("_json") or {}
        R.add("a.lean.build." + f, "PASS", "`targo trust build %s.lean --emit=trust-ir`: envelope %s, %d carrier-gated bodies %s, kernel-only "
              "%s, module wire v%s, native_codegen=%s" % (f, env.get("schema"), len(env.get("bodies") or []),
                                                         [b.get("declaration") for b in env.get("bodies") or []],
                                                         env.get("kernel_only_declarations"), mod["wire_version"], env.get("native_codegen")))
        v, rt, run = mod["validate"], mod["roundtrip"], mod["run"]
        R.add("a.lean.module.%s.validate" % f, "PASS" if v["ok"] else "FAIL", "module is well-formed" if v["ok"] else str(v["by_variant"]))
        badrt = {k: x for k, x in rt.items() if not x["ok"]}
        R.add("a.lean.module.%s.roundtrip" % f, "PASS" if not badrt else "FAIL", "4-format byte-identical" if not badrt else str(badrt))
        lit = re.search(r"^def program : UInt64 := (\d+)\s*$", read(os.path.join(L, "src", "Lib.lean")), re.M)
        lit = lit.group(1) if lit else None
        if run["rc"] == 0 and lit is not None and run.get("value") == lit:
            R.add("a.lean.module.%s.exec" % f, "PASS", "interpreter runs the Lean nullary `program` = %s == the literal READ FROM Lib.lean "
                  "(%s steps); a literal-only check — the natively-oracled differential is a.lean.module.Lib.exec_bodies" % (lit, run.get("steps")))
        else:
            R.add("a.lean.module.%s.exec" % f, "FAIL", "Lib.lean literal=%s run=%s" % (lit, run))
        judge_twins(R, "a.lean.module." + f, mod)
        if f == "Lib":
            lib_names = {x["name"] for x in js.get("functions", []) if x.get("blocks")}
            dlog, mlog = read(os.path.join(L, "Lib", "drive.log")), read(os.path.join(L, "Lib", "drive-mutant.log"))
            dv = [l.strip() for l in dlog.splitlines() if re.fullmatch(r"\d+", l.strip())]
            mv = [l.strip() for l in mlog.splitlines() if re.fullmatch(r"\d+", l.strip())]
            orc = load_unit(out, "lean_oracle")
            ov, olanes, oprobs = native_oracle(orc) if orc else (None, {}, ["lean_oracle unit was not run"])
            norm = lambda t: sorted(" ".join(l.split()) for l in t.splitlines() if l.strip().startswith("def "))
            same_defs = orc is not None and norm(read(os.path.join(L, "src", "Lib.lean"))) == norm(read(os.path.join(orc["dir"], "source.rs")))
            if oprobs or ov is None or not same_defs:
                R.add("a.lean.module.Lib.exec_bodies", "FAIL", "no usable NATIVE oracle for the Lean lane: value=%s problems=%s island defs "
                      "identical to Lib.lean=%s" % (ov, oprobs, same_defs))
            elif dv and dv[-1] == ov and "linked image is well-formed" in dlog:
                R.add("a.lean.module.Lib.exec_bodies", "PASS", "DIFFERENTIAL: driver linked BY SYMBOL with the standalone-Lean module computes "
                      "addmul(6,7)+pick(5,9)+lit8(100)+program = %s == %s, the value the SAME defs (text identical to Lib.lean, checked) "
                      "produce NATIVELY inside a `clean {}` island (lanes %s); linked image well-formed" % (dv[-1], ov, sorted(olanes)))
            else:
                R.add("a.lean.module.Lib.exec_bodies", "FAIL", "driver=%s native oracle=%s: %s" % (dv[-1:], ov, dlog.strip()[-300:]))
            if mv and ov is not None and mv[-1] != ov:
                R.add("a.lean.module.Lib.exec_bodies.twin", "PASS", "same link against Lib with addmul Mul->Add => %s != native %s" % (mv[-1], ov))
            else:
                R.add("a.lean.module.Lib.exec_bodies.twin", "FAIL", "mutant not observed: %s" % mlog.strip()[-200:])
        c = mod["census"] or {}
        if f == "Use":
            mine = {x["name"] for x in js.get("functions", []) if x.get("blocks")}
            if c.get("imports"):
                R.add("a.lean.module.Use.imports", "PASS", "Use's module records %d Module.imports row(s) for `import Lib`" % c["imports"])
            else:
                R.add("a.lean.module.Use.imports", "GAP", "`import Lib` is carried by RE-EMBEDDING: Use's module re-defines Lib's bodies %s next "
                      "to its own %s; Module.imports rows = 0, so no digest-authenticated dependency edge exists between the two Lean modules"
                      % (sorted(lib_names & mine), sorted(mine - lib_names)), "producer-gap",
                      sig="imports=0:re-embedded=%s" % sorted(lib_names & mine))
        gate_in_band = c.get("body_gate_populated") or c.get("certificates") or c.get("obligations")
        if gate_in_band:
            R.add("a.lean.module.%s.gate_in_band" % f, "PASS", "body_gate=%s obligations=%s certificates=%s"
                  % (c["body_gate_populated"], c["obligations"], c["certificates"]))
        else:
            R.add("a.lean.module.%s.gate_in_band" % f, "GAP", "every gate fact (kernel_payload_sha256, subject_digest, method) lives in the "
                  "JSON ENVELOPE; the module has body_gate=None, 0 obligations, 0 certificates, producers=" + json.dumps(c.get("producers")),
                  "producer-gap", sig="gate_in_band:body_gate=0:obligations=0:certificates=0")
    for fn in sorted(os.listdir(L)):
        m = re.fullmatch(r"build-L_(\w+)\.log", fn)
        if not m:
            continue
        n = m.group(1)
        log = read(os.path.join(L, fn))
        r = rc(os.path.join(L, "build-L_%s.rc" % n))
        wrote = os.path.exists(os.path.join(L, "L_%s.irlib.json" % n))
        msg = squash(log)[:420]
        if wrote and r == 0:
            R.add("a.lean.standalone." + n, "PASS", "standalone lane admits it: %s" % msg[:200])
        elif r not in (0, None) and LEAN_REFUSAL.search(log):
            R.add("a.lean.standalone." + n, "GAP", "standalone Lean -> trust-ir lane refuses the whole artifact: %s" % msg, "refused",
                  log.strip()[:1200], sig=standalone_refusal_signature(log) or "refused:" + msg[:160])
        else:
            R.add("a.lean.standalone." + n, "FAIL", "rc=%s wrote=%s: %s" % (r, wrote, msg))


def standalone_refusal_signature(log):
    """The WHOLE refusal of the standalone lane: every refused declaration with its `[class/sub]` and message
    head, in log order - never the class string alone."""
    heads = []
    for m in re.finditer(r"`([^`]+)` \[([a-z0-9-]+/[a-z0-9-]+)\]:?([^\n]*)", log):
        heads.append("`%s` [%s]:%s" % (m.group(1), m.group(2), squash(m.group(3))[:120]))
    return " | ".join(heads) if heads else None


def f1_rows(R, out):
    """F1 exit: machine code FROM the trust-ir spelling.  Every expected value is the NATIVE oracle."""
    F = os.path.join(out, "f1")
    state = read(os.path.join(F, "backend")).strip()
    log = read(os.path.join(F, "backend-probe.log"))

    def lane(d):
        D = os.path.join(F, d)
        blog = read(os.path.join(D, "build.log"))
        m = re.search(r"trust-cg trust-ir frontend: (\d+)/(\d+) reachable function", blog)
        return dict(build_rc=rc(os.path.join(D, "build.rc")), link_rc=rc(os.path.join(D, "link.rc")), exec_rc=rc(os.path.join(D, "exec.rc")),
                    value=read(os.path.join(D, "exec.log")).strip() or None, frontend=[m.group(1), m.group(2)] if m else None,
                    errors=[squash(l)[:700] for l in blog.splitlines() if l.startswith("error") and "aborting" not in l][:3],
                    refusals=[squash(l)[:420] for l in blog.splitlines() if re.search(r"^\s+e\.g\. `", l)][:4],
                    # The classifier reads the WHOLE lines: since the `[clean-below-gate]` census (plan step 3)
                    # each sample opens with the def's tier and shape, which put `Producer::Clean` past the 420
                    # characters kept above as evidence, so a truncated match called the known gap "unnamed".
                    text=" ".join(squash(l) for l in blog.splitlines()
                                  if (l.startswith("error") and "aborting" not in l) or re.search(r"^\s+e\.g\. `", l)))

    o_rust, o_lib = lane("native-f1_rust")["value"], lane("native-f1_lib")["value"]
    if state == "absent":
        if re.search(r"codegen-backends|codegen backend|unknown codegen|failed to find", log):
            R.add("a.f1.codegen", "GAP", "F1 exit not exercisable: this compiler ships no trust-cg backend (native oracles: f1_rust=%s, "
                  "f1_lib=%s) — %s" % (o_rust, o_lib, squash(log)[:240]), "consumer-gap", log.strip()[:600], sig="f1:no-trust-cg-backend")
        else:
            R.add("a.f1.codegen", "FAIL", "backend probe failed with an unnamed error: " + squash(log)[:300])
        return
    if state != "present":
        R.add("a.f1.codegen", "FAIL", "F1 hook did not run")
        return
    cs, ca, sa, sl = lane("control-strict"), lane("control-allow"), lane("subject-allow"), lane("subject-license")
    R.add("a.f1.codegen.backend", "PASS", "trust-cg backend + trust-ir frontend present")
    if o_rust is None:
        R.add("a.f1.codegen.rust_control", "FAIL", "no native oracle for f1_rust")
    elif ca["exec_rc"] == 0 and ca["value"] == o_rust and ca["frontend"] and ca["frontend"][0] == ca["frontend"][1]:
        R.add("a.f1.codegen.rust_control", "PASS", "Rust-only C-ABI crate: object FROM its trust-ir spelling (%s/%s reachable functions, no "
              "MIR fallback) linked with a foreign C main prints %s == NATIVE %s. Gate: -Ztrust-cg-output-gate=allow-unknown"
              % (ca["frontend"][0], ca["frontend"][1], ca["value"], o_rust))
    else:
        R.add("a.f1.codegen.rust_control", "FAIL", "control did not reproduce the native value %s: %s" % (o_rust, ca))
    if cs["build_rc"] not in (0, None) and any("could not be proven output-preserving" in e for e in cs["errors"]):
        R.add("a.f1.codegen.rust_control.strict_gate", "GAP", "under the DEFAULT (strict proven-output) gate the same Rust-only crate is "
              "REFUSED, fail-closed: " + cs["errors"][0][:420], "consumer-gap", " ## ".join(cs["errors"]),
              sig="f1:strict-gate:could not be proven output-preserving")
    elif cs["exec_rc"] == 0 and cs["value"] == o_rust:
        R.add("a.f1.codegen.rust_control.strict_gate", "PASS", "strict proven-output gate admits the control: prints %s == native" % cs["value"])
    else:
        R.add("a.f1.codegen.rust_control.strict_gate", "FAIL", "unnamed outcome: %s" % cs)
    blob = sa["text"]
    if sa["exec_rc"] == 0 and o_lib is not None and sa["value"] == o_lib:
        R.add("a.f1.codegen.two_language", "PASS", "two-language crate (Rust -> Lean call edge): object FROM trust-ir prints %s == NATIVE %s"
              % (sa["value"], o_lib))
    elif sa["build_rc"] not in (0, None) and "is not admitted to codegen" in blob and "Producer::Clean" in blob:
        lic = sl["text"]
        producer_refused = "the producer REFUSED the codegen license" in lic
        R.add("a.f1.codegen.two_language", "GAP", "the TWO-LANGUAGE crate cannot take the F1 exit (native oracle = %s). Default handoff lane: "
              "the trust-ir codegen frontend refuses EVERY `Producer::Clean` body fail-closed — %s. License lane: %s"
              % (o_lib, blob[:400], lic[:420]), "producer-gap" if producer_refused else "consumer-gap",
              " ## ".join(sa["errors"] + sa["refusals"] + sl["errors"] + sl["refusals"]),
              sig="f1:two-language:Producer::Clean not admitted to codegen:license=%s"
                  % ("producer-refused" if producer_refused else "no-producer-refusal-text"))
    else:
        R.add("a.f1.codegen.two_language", "FAIL", "unnamed outcome (native oracle %s): %s" % (o_lib, sa))


# ---- Part A rows: which units a row needs, and which ratchets it owns
def parta_probe_rows(pa, R, unit):
    pa.probe(unit)
    fid = next((f for f, p, _ in blocks() + EXTRA_PROBES if p == unit), None)
    info = load_unit(pa.out, unit)
    if fid is None or info is None:
        R.add("a." + unit, "FAIL", "probe unit %s was not run or has no feature id" % unit)
        return
    oracle = judge_native(R, "a." + fid, info)
    mod = judge_module(R, "a." + fid, info, oracle)
    if mod is not None:
        judge_carried_wrap(R, fid, mod)
        if fid == "lean.inductive_in_module":
            judge_inductive_exec(R, mod)


def parta_units(pa):
    """Every emitted unit the aggregate rows read (the probes, dep, app, app_max, app_exec)."""
    pa.all_probes()
    pa.build_dep()
    pa.app()
    pa.generated_app("app_max")
    pa.generated_app("app_exec")
    units = {}
    for name in [u for u, _, _ in PARTA_PROBES] + ["dep", "app", "app_max", "app_exec"]:
        info = load_unit(pa.out, name)
        if info is not None:
            units[name] = info
    return units


def parta_unit_rows(pa, R, name):
    if name == "dep":
        pa.build_dep()
        info = load_unit(pa.out, "dep")
        r1, r2 = rc(os.path.join(info["dir"], "rlib", "build.rc")), rc(os.path.join(info["dir"], "rlib-adv", "build.rc"))
        R.add("a.unit.dep.native", "PASS" if r1 == 0 and r2 == 0 else "FAIL", "rlib builds: verify-off rc=%s, verify-on/advisory rc=%s" % (r1, r2))
        m = judge_module(R, "a.unit.dep", info, None, want_exec=False)
        if m is not None:
            judge_dep_carried(R, m)
        return
    if name == "app":
        pa.app()
    elif name in ("app_max", "app_exec"):
        pa.generated_app(name)
    elif name == "lean_oracle":
        pa.lean_oracle()
    info = load_unit(pa.out, name)
    if info is None:
        R.add("a.unit." + name, "FAIL", "unit was not run")
        return
    oracle = judge_native(R, "a.unit." + name, info)
    if name == "lean_oracle":
        elog = read(os.path.join(info["dir"], "emit", "emit.log"))
        m = re.search(r"DuplicateFunctionName\]: name=\"(\w+)\" ids=\[([^\]]*)\]", elog)
        if m:
            R.add("a.unit.lean_oracle.symbol_collision", "GAP", "verified emit writes NO module: the producer names a Clean def by its BARE "
                  "LEAF (`%s`), so the island def `m::%s` collides with the Rust fn `%s` and the compiler's embedded trust-ir validator "
                  "refuses the crate module: DuplicateFunctionName name=%r ids=[%s]" % (m.group(1), m.group(1), m.group(1), m.group(1), m.group(2)),
                  "producer-gap", squash(elog)[-400:], sig="DuplicateFunctionName:name=%s" % m.group(1))
        elif info["module_lane"] == "emit":
            R.add("a.unit.lean_oracle.symbol_collision", "PASS", "a Clean def `m::program` and a Rust fn `program` coexist in one emitted module")
        else:
            R.add("a.unit.lean_oracle.symbol_collision", "FAIL", "verified emit failed for an unnamed reason: %s" % info["emit"])
        return
    judge_module(R, "a.unit." + name, info, oracle)
    if name in ("app_max", "app_exec"):
        allf = [f for f, _, _ in blocks()]
        inc = [x for x in read(os.path.join(pa.out, name + ".features")).strip().split(",") if x]
        excluded = [f for f in allf if f not in inc]
        what = ("maximal accepted program = %d/%d feature blocks" if name == "app_max" else
                "ONE program whose single interpreter-vs-native differential covers %d/%d feature blocks") % (len(inc), len(allf))
        if not excluded:
            R.add("a.unit.%s.coverage" % name, "PASS", what)
        else:
            R.add("a.unit.%s.coverage" % name, "GAP", "%s; excluded: %s" % (what, excluded),
                  "refused" if name == "app_max" else "producer-gap", sig="coverage:excluded=%s" % excluded)


# ---- WS8.8 mutation control: "mutating the Clean body changes the value"
# The interpreter-vs-native differential (`.exec` PASS on every Rust -> Lean row) is evidence only if the
# interpreter is executing the Clean body the producer emitted FROM THE SOURCE — not a Rust stub, not a
# constant the producer folded, not a body copied from somewhere else. The proof program stated this as
# prose (REPORT.md: "mutating the Clean body changes the value"); this row makes it a ratchet: p10's
# island with ONE line edited must (1) print a different native value, (2) still pass its own straight
# differential, and (3) FAIL both cross differentials (mutant module vs original native, original module
# vs mutant native). A control that cannot be measured is a FAIL, never a GAP: it is the evidence the
# positive rows rest on.
ISLAND_MUTANT_UNIT = "p10m_lean_wrapping_uint64_island_mutant"
ISLAND_MUTANT_ORIGINAL = "p10_lean_wrapping_uint64"
ISLAND_MUTANT_FID = "a.island_mutant"


def island_line_diff(orig_src, mut_src):
    """-> (changed_lines, inside_island) over the two sources with their leading `//` comment headers (the
    `// FEATURE` / `// EXPECT` block) dropped: the list of (line_no, original, mutant) pairs that differ,
    and whether EVERY one of them lies inside a `clean { ... }` block of the original. Line-aligned on
    purpose: the twin is one EDITED line, never an insertion, so a length difference is itself a difference."""
    def body(src):
        lines = src.splitlines()
        while lines and lines[0].startswith("//"):
            lines.pop(0)
        return lines
    a, b = body(orig_src), body(mut_src)
    changed = []
    for i in range(max(len(a), len(b))):
        x = a[i] if i < len(a) else None
        y = b[i] if i < len(b) else None
        if x != y:
            changed.append((i + 1, x, y))
    inside = set()
    depth, in_island = 0, False
    for i, l in enumerate(a):
        if not in_island and re.search(r"\bclean\s*\{", l):
            in_island, depth = True, 0
        if in_island:
            depth += l.count("{") - l.count("}")
            inside.add(i + 1)
            if depth <= 0:
                in_island = False
    return changed, bool(changed) and all(n in inside for n, _, _ in changed)


def island_mutant_control(R, orig, mut, orig_src, mut_src):
    """The three control ratchets over the ORIGINAL and MUTANT unit views (load_unit shape)."""
    changed, inside = island_line_diff(orig_src, mut_src)
    # WS8.8 review: the twin must be one EDITED line, so both sides of the pair
    # must exist. A deleted or appended last island line lands here as
    # `x is None` / `y is None`; that is a DELETION, not the edit this control
    # is about, and it used to reach `x.strip()` and crash the judge instead of
    # failing the row. A control that cannot be measured is a FAIL, never a GAP
    # and never a traceback.
    if len(changed) == 1 and inside and changed[0][1] is not None and changed[0][2] is not None:
        n, x, y = changed[0]
        R.add(ISLAND_MUTANT_FID + ".control.one_island_line", "PASS",
              "the twin differs from %s by exactly one line, inside the `clean {}` island: L%d %r -> %r" % (ISLAND_MUTANT_ORIGINAL, n, x.strip(), y.strip()))
    else:
        R.add(ISLAND_MUTANT_FID + ".control.one_island_line", "FAIL",
              "the twin must differ from %s by exactly ONE line inside the island; measured %d changed line(s), all inside the island=%s: %s"
              % (ISLAND_MUTANT_ORIGINAL, len(changed), inside, changed[:4]))
    o_nat, _, o_probs = native_oracle(orig)
    m_nat, _, m_probs = native_oracle(mut)
    if o_nat is None or m_nat is None or o_probs or m_probs:
        R.add(ISLAND_MUTANT_FID + ".control.native_differs", "FAIL",
              "no clean native oracle on both sides: original=%s %s mutant=%s %s" % (o_nat, o_probs, m_nat, m_probs))
    elif o_nat != m_nat:
        R.add(ISLAND_MUTANT_FID + ".control.native_differs", "PASS",
              "one island line changed the NATIVE value: original %s, mutant %s" % (o_nat, m_nat))
    else:
        R.add(ISLAND_MUTANT_FID + ".control.native_differs", "FAIL",
              "the island edit did not change the native value (%s == %s): the twin is not a mutation of the executed body" % (o_nat, m_nat))

    def interp(info):
        r = ((info.get("module") or {}).get("run") or {}) if info.get("module_lane") == "emit" else {}
        return r.get("value") if r.get("rc") == 0 else None
    o_int, m_int = interp(orig), interp(mut)
    if o_int is None or m_int is None:
        R.add(ISLAND_MUTANT_FID + ".control.differential_fails", "FAIL",
              "the reference interpreter has no value on both sides (verified-emit module + `run` rc 0 required): original=%s mutant=%s"
              % (o_int, m_int))
    elif o_nat is None or m_nat is None or o_nat == m_nat:
        R.add(ISLAND_MUTANT_FID + ".control.differential_fails", "FAIL",
              "cross differential not measurable without two distinct native oracles (original=%s, mutant=%s)" % (o_nat, m_nat))
    elif o_int == m_int:
        R.add(ISLAND_MUTANT_FID + ".control.differential_fails", "FAIL",
              "the interpreter result did NOT move with the island body (%s on both modules, natives %s / %s): the interpreter is "
              "not executing the emitted Clean body" % (o_int, o_nat, m_nat))
    elif o_int != o_nat or m_int != m_nat:
        R.add(ISLAND_MUTANT_FID + ".control.differential_fails", "FAIL",
              "a STRAIGHT differential fails: interpreter(original)=%s native(original)=%s; interpreter(mutant)=%s native(mutant)=%s"
              % (o_int, o_nat, m_int, m_nat))
    else:
        R.add(ISLAND_MUTANT_FID + ".control.differential_fails", "PASS",
              "both CROSS differentials fail as required — interpreter(mutant)=%s != native(original)=%s and interpreter(original)=%s != "
              "native(mutant)=%s — while both straight differentials hold" % (m_int, o_nat, o_int, m_nat))


def island_mutant_rows(pa, R):
    pa.probe(ISLAND_MUTANT_ORIGINAL)
    pa.island_mutant()
    orig, mut = load_unit(pa.out, ISLAND_MUTANT_ORIGINAL), load_unit(pa.out, ISLAND_MUTANT_UNIT)
    if orig is None or mut is None:
        R.add(ISLAND_MUTANT_FID, "FAIL", "unit not run: original=%s mutant=%s" % (orig is not None, mut is not None))
        return
    oracle = judge_native(R, ISLAND_MUTANT_FID, mut)
    judge_module(R, ISLAND_MUTANT_FID, mut, oracle)
    island_mutant_control(R, orig, mut, read(os.path.join(orig["dir"], "source.rs")), read(os.path.join(mut["dir"], "source.rs")))


def parta_row(row, pa, R):
    if row in PROBE_ROW.values():
        parta_probe_rows(pa, R, next(u for u, r in PROBE_ROW.items() if r == row))
    elif row in ("ir-ta-dep", "ir-ta-app", "ir-ta-app_max", "ir-ta-app_exec", "ir-ta-lean_oracle"):
        parta_unit_rows(pa, R, row[len("ir-ta-"):])
    elif row == "ir-ta-neg":
        pa.neg()
        negatives(R, pa.out)
    elif row == "ir-ta-lean":
        pa.lean()
        lean_rows(R, pa.out)
    elif row == "ir-ta-attrib":
        pa.attrib()
        pa.probe("p12b_lean_bool_connective")
        p12 = (load_unit(pa.out, "p12b_lean_bool_connective") or {}).get("native", {})
        nat = next((e.get("stdout") for e in p12.values() if e.get("build_rc") == 0 and e.get("exec_rc") == 0), None)
        attrib_rows(R, attrib_view(pa.out), nat)
    elif row == "ir-ta-format":
        format_rows(R, parta_units(pa))
    elif row == "ir-ta-surface":
        surface(R, parta_units(pa))
    elif row == "ir-ta-f1":
        pa.f1()
        f1_rows(R, pa.out)
    elif row == "ir-ta-island_mutant":
        island_mutant_rows(pa, R)
    else:
        raise KeyError(row)


# ============================================================ Part A-Lean (port of parta-lean/run.py)
W64 = 2 ** 64
M8, M16, M32 = 2 ** 8, 2 ** 16, 2 ** 32
# The standalone-Lean library (ir-tl-library): name -> (param widths, ret width, python model of the LEAN def).
# The model only PROPOSES expected values; every one is restated as `theorem : f args = v := rfl` and
# certified by the kernel of the compiler under test (kernel_oracle) before it is trusted.
LIB_DEFS = {
    "addmul": ([64, 64], 64, lambda a, b: (a * b + a) % W64),
    "poly": ([64, 64, 64], 64, lambda x, y, z: (((x * x + y * 3) % W64) - ((z * x - 7) % W64)) % W64),
    "fst3": ([64, 64, 64], 64, lambda a, b, c: a),
    "snd32": ([32, 32], 32, lambda a, b: b),
    "lit64": ([], 64, lambda: 18446744073709551615),
    "lit8": ([], 8, lambda: 255),
    "wrap8": ([8], 8, lambda a: (a + 200) % M8),
    "mul16": ([16, 16], 16, lambda a, b: (a * b - 1) % M16),
    "sub32": ([32, 32], 32, lambda a, b: (a - b) % M32),
    "mixproj": ([8, 16, 32, 64], 32, lambda a, b, c, d: c),
    "horner": ([64], 64, lambda x: ((((x * 5 + 3) * x) + 2) * x + 1) % W64),
    "negate32": ([32], 32, lambda a: (0 - a) % M32),
    "program": ([], 64, lambda: 6),
    "letsq": ([64], 64, lambda a: (((a + 1) % W64) ** 2) % W64),
}
LIB_VEC = {
    "addmul": [(3, 4), (2 ** 63, 3), (2 ** 64 - 1, 2 ** 64 - 1)],
    "poly": [(1, 2, 3), (2 ** 40, 5, 2 ** 30), (0, 0, 0)],
    "fst3": [(11, 22, 33)],
    "snd32": [(1, 4294967295)],
    "lit64": [()], "lit8": [()], "program": [()],
    "wrap8": [(0,), (56,), (100,), (255,)],
    "mul16": [(0, 0), (300, 300), (65535, 65535)],
    "sub32": [(1, 2), (5, 5), (0, 4294967295)],
    "mixproj": [(1, 2, 3000000000, 4)],
    "horner": [(0,), (2,), (2 ** 33 + 7,)],
    "negate32": [(0,), (1,), (4294967295,)],
    "letsq": [(3,), (2 ** 64 - 1,), (2 ** 32,)],
}
CTY = {8: "uint8_t", 16: "uint16_t", 32: "uint32_t", 64: "uint64_t", "bool": "uint8_t"}


def tyname(w):
    return "bool" if w == "bool" else "u%d" % w


def gen_driver(out_txt, out_exp, defs, vecs):
    """Nullary-driver TrustIr TEXT module: one `t_<def>_<k>` per vector calling the def BY SYMBOL."""
    ftys, exp, body = [], {}, []

    def fty(params, ret):
        s = "(%s) -> (%s)" % (", ".join(tyname(p) for p in params), tyname(ret))
        if s not in ftys:
            ftys.append(s)
        return ftys.index(s)
    names = list(defs)
    decl_id = {n: i for i, n in enumerate(names)}
    for n in names:
        p, r, _ = defs[n]
        body.append("rustcc fn @%s(functy.%d) {\n    ; #producer: clean\n}\n" % (n, fty(p, r)))
    for n in names:
        p, r, f = defs[n]
        for k, v in enumerate(vecs[n]):
            t = "t_%s_%d" % (n, k)
            exp[t] = {"def": n, "args": list(v), "ret_bits": r, "expected": int(f(*v))}
            ls = ["rustcc fn @%s(functy.%d) {" % (t, fty([], r)), "    ; #producer: trust-ir", "bb0:"]
            for i, (w, a) in enumerate(zip(p, v)):
                ls.append("    %%%d = const %s %s" % (i, tyname(w), ("true" if a else "false") if w == "bool" else a))
            ls.append("    %%%d = call @func.%d(%s)" % (len(p), decl_id[n], ", ".join("%%%d" % i for i in range(len(p)))))
            ls += ["    ret %%%d" % len(p), "}", ""]
            body.append("\n".join(ls))
    hdr = ["; TrustIr text format v1", 'module "parta-lean-driver"', ""] + ["functy.%d = %s\n" % (i, s) for i, s in enumerate(ftys)]
    open(out_txt, "w").write("\n".join(hdr) + "\n" + "\n".join(body))
    json.dump(exp, open(out_exp, "w"), indent=1)


def c_main(path, defs, vecs):
    lines = ["/* native differential main (trust-cg object) */", "#include <stdio.h>", "#include <stdint.h>"]
    for n, (p, r, _) in defs.items():
        lines.append("extern %s %s(%s);" % (CTY[r], n, ", ".join(CTY[w] for w in p) or "void"))
    lines.append("int main(void){")
    for n, (p, r, _) in defs.items():
        for k, v in enumerate(vecs[n]):
            args = ", ".join("(%s)%dULL" % (CTY[w], a) for w, a in zip(p, v))
            lines.append('  printf("t_%s_%d %%llu\\n", (unsigned long long)%s(%s));' % (n, k, n, args))
    lines += ["  return 0;", "}", ""]
    open(path, "w").write("\n".join(lines))


# ---- general-pipeline C mains + expected outputs (port of gen_mains.py).  Expected values are LEAN semantics
# computed here (wrapping UIntN, Nat, x/0=0), never read from the object under test, and each is restated as a
# kernel-checked `rfl` theorem (GENERAL_ORACLE).
GENERAL_SCALAR = {
    "isLt": ([64, 64], "bool", lambda a, b: int(a < b), [(3, 5), (5, 3), (W64 - 1, 0), (0, W64 - 1)]),
    "min2": ([64, 64], 64, lambda a, b: a if a < b else b, [(7, 9), (W64 - 1, 1), (4, 4)]),
    "sqLet": ([64], 64, lambda a: ((a + 1) % W64) ** 2 % W64, [(3,), (W64 - 1,), (2 ** 32,)]),
    "areaOfRect": ([64, 64], 64, lambda w, h: w * h % W64, [(6, 7), (2 ** 32, 2 ** 32)]),
    "dotOf": ([64] * 4, 64, lambda a, b, c, d: (a * c + b * d) % W64, [(1, 2, 3, 4), (W64 - 1, W64 - 1, 2, 3)]),
    "sumThree": ([64] * 3, 64, lambda a, b, c: (a + b + c) % W64, [(1, 2, 3), (W64 - 1, 1, 5)]),
    "addK": ([64, 64], 64, lambda k, x: (x + 2 * k) % W64, [(5, 10), (W64 - 1, 1)]),
    "triple": ([64], 64, lambda x: x * 3 % W64, [(7,), (2 ** 63,)]),
    "w8": ([8, 8], 8, lambda a, b: (a * b + 1) % 256, [(16, 16), (15, 17), (3, 4)]),
    "w32": ([32, 32], 32, lambda a, b: (a + b * a) % 2 ** 32, [(2 ** 31, 3), (5, 6)]),
    "quot": ([64, 64], 64, lambda a, b: 0 if b == 0 else a // b, [(7, 2), (7, 0), (W64 - 1, 3)]),
    "inc2": ([64], 64, lambda a: (a + 2) % W64, [(W64 - 1,), (40,)]),
    "mask": ([64, 64], 64, lambda a, b: (a & b) | 1, [(12, 10), (W64 - 1, W64 - 2)]),
    "both": ([64] * 3, "bool", lambda a, b, c: int(a < b and b < c), [(3, 4, 5), (3, 5, 4), (W64 - 1, 0, 1), (0, W64 - 2, W64 - 1)]),
}


def gen_mains(out):
    """Write <decl>_main.c + <decl>.expected under `out`; return {decl: [(lean lhs, lean rhs)]}."""
    import math
    os.makedirs(out, exist_ok=True)
    oracle = {}
    for d, (ps, r, f, vs) in GENERAL_SCALAR.items():
        proto = "extern %s %s(%s);" % (CTY[r], d, ", ".join(CTY[p] for p in ps))
        body, exp = [], []
        for v in vs:
            args = ", ".join("(%s)%dULL" % (CTY[p], a) for p, a in zip(ps, v))
            body.append('  printf("%s(%s)=%%llu\\n", (unsigned long long)%s(%s));' % (d, ",".join(map(str, v)), d, args))
            exp.append("%s(%s)=%d" % (d, ",".join(map(str, v)), f(*v)))
            oracle.setdefault(d, []).append((" ".join([d] + [str(a) for a in v]),
                                             ("true" if f(*v) else "false") if r == "bool" else str(f(*v))))
        open(os.path.join(out, d + "_main.c"), "w").write(
            '#include <stdio.h>\n#include <stdint.h>\n#include "clean_runtime.h"\n%s\nint main(void){\n  clean_runtime_init();\n%s\n'
            "  clean_runtime_finalize();\n  return 0;\n}\n" % (proto, "\n".join(body)))
        open(os.path.join(out, d + ".expected"), "w").write("\n".join(exp) + "\n")
    hdr = ('#include <stdio.h>\n#include <stdint.h>\n#include "clean_runtime.h"\n#define NAT(x) clean_nat_of_u64(x)\n'
           "#define U(x) ((unsigned long long)clean_nat_to_u128(x))\n")

    def hand(d, proto, stmts, exp, lean):
        open(os.path.join(out, d + "_main.c"), "w").write(
            hdr + proto + "\nint main(void){\n  clean_runtime_init();\n" + "".join("  %s\n" % s for s in stmts)
            + "  clean_runtime_finalize();\n  return 0;\n}\n")
        open(os.path.join(out, d + ".expected"), "w").write("\n".join(exp) + "\n")
        oracle[d] = [(l, e.split("=")[-1]) for l, e in zip(lean, exp)]
    ns = [0, 1, 10, 100, 1000]
    hand("sumTo", "extern clean_obj* sumTo(clean_obj*);",
         ['printf("sumTo(%d)=%%llu\\n", U(sumTo(NAT(%d))));' % (n, n) for n in ns],
         ["sumTo(%d)=%d" % (n, n * (n + 1) // 2) for n in ns], ["sumTo %d" % n for n in ns])
    g = [(12, 18), (270, 192), (7, 13), (0, 5), (5, 0)]
    hand("gcdF", "extern clean_obj* gcdF(clean_obj*, clean_obj*, clean_obj*);",
         ['printf("gcdF(%d,%d,%d)=%%llu\\n", U(gcdF(NAT(%d),NAT(%d),NAT(%d))));' % (a + 2 * b, a, b, a + 2 * b, a, b) for a, b in g],
         ["gcdF(%d,%d,%d)=%d" % (a + 2 * b, a, b, math.gcd(a, b)) for a, b in g], ["gcdF %d %d %d" % (a + 2 * b, a, b) for a, b in g])
    hand("greetLen", "extern clean_obj* greetLen(uint64_t);", ['printf("greetLen(0)=%llu\\n", U(greetLen(0)));'], ["greetLen(0)=6"],
         ["greetLen 0"])
    hand("arrSize", "extern clean_obj* arrSize(uint64_t, uint64_t);", ['printf("arrSize(1,2)=%llu\\n", U(arrSize(1,2)));'],
         ["arrSize(1,2)=3"], ["arrSize 1 2"])
    hand("applyTwice", "extern uint64_t applyTwice(clean_obj*, uint64_t);\nstatic clean_obj* add5(clean_obj* x){ uint64_t v = "
         "clean_unbox_uint64(x); clean_dec(x); return clean_box_uint64(v + 5); }",
         ["clean_obj* f = clean_alloc_closure((void*)add5, 1, 0);",
          'printf("applyTwice(add5,1)=%llu\\n", (unsigned long long)applyTwice(f, 1));'], ["applyTwice(add5,1)=11"],
         ["applyTwice (fun x => x + 5) 1"])
    hand("area", "extern uint64_t area(clean_obj*);",
         ["clean_obj* s = clean_alloc_ctor(1, 0, 16);", "clean_ctor_set_uint64(s, 0, 6);", "clean_ctor_set_uint64(s, 8, 7);",
          'printf("area(rect 6 7)=%llu\\n", (unsigned long long)area(s));',
          "clean_obj* q = clean_alloc_ctor(0, 0, 8);", "clean_ctor_set_uint64(q, 0, 9);",
          'printf("area(sq 9)=%llu\\n", (unsigned long long)area(q));'], ["area(rect 6 7)=42", "area(sq 9)=81"],
         ["area (.rect 6 7)", "area (.sq 9)"])
    return oracle


# probe -> (standalone expectation kind, refused/rejected DECLARATION (the whole refusal text is pinned by the row's
#           expected.json signature, never here), exec spec, [general decls])
TL_PROBES = [
    ("p01_bool_result", ("refused", "isLt"), "should", ["isLt"]),
    ("p02_if_select", ("refused", "min2"), "should", ["min2"]),
    ("p03_let", ("built", ""), ({"sqLet": ([64], 64, lambda a: (((a + 1) % W64) ** 2) % W64)}, {"sqLet": [(3,), (W64 - 1,), (2 ** 32,)]}), ["sqLet"]),
    ("p04_nat_structural_rec", ("refused", "sumTo"), None, ["sumTo"]),
    ("p05_nat_wf_rec", ("refused", "gcdF"), None, ["gcdF"]),
    ("p06_inductive_match", ("refused", "area"), None, ["area", "areaOfRect"]),
    ("p07_structure", ("refused", "dot"), None, ["dotOf"]),
    ("p08_string", ("refused", "greet"), None, ["greetLen"]),
    ("p09_array_list", ("refused", "sumList"), None, ["sumThree", "arrSize"]),
    ("p10_closure_higher_order", ("refused", "applyTwice"), None, ["applyTwice", "addK"]),
    # `refused`, not `rejected`, since 2026-09-21: MEASURED on this tree, `targo
    # trust check p11_typeclass_instance.lean` answers "PROVED — 3 declaration(s)
    # kernel-checked", so the elaboration error this row used to pin ("was
    # registered with a different signature") no longer happens. The build then
    # refuses the lowering: exit 1, "The whole artifact was refused", with
    # `triple` [source-shape/not-emittable] (and `Scale`, `instScaleU64`). That is
    # the `refused` shape — PROVED source, producer declines — and the judge's
    # `rejected` branch cannot express it: it tests `not proved`, so a source that
    # now PROVES scored FAIL and printed the self-contradictory line "source
    # REJECTED at elaboration/kernel (no artifact): PROVED ... kernel-checked".
    # This keeps the row a NAMED GAP; it does not make it pass.
    ("p11_typeclass_instance", ("refused", "triple"), None, ["triple"]),
    ("p12_mixed_widths", ("built", ""), ({"w8": ([8, 8], 8, lambda a, b: (a * b + 1) % M8), "w16": ([16, 16], 16, lambda a, b: (a - b) % M16),
                                          "w32": ([32, 32], 32, lambda a, b: (a + b * a) % M32),
                                          "pickWide": ([8, 16, 32, 64], 16, lambda a, b, c, d: b)},
                                         {"w8": [(16, 16), (15, 17)], "w16": [(1, 2), (9, 4)], "w32": [(2 ** 31, 3), (5, 6)],
                                          "pickWide": [(1, 65535, 3, 4)]}), ["w8", "w32"]),
    # `refused`, not `rejected`, for the same measured reason as p11: `targo trust
    # check p12b_width_conversion.lean` answers "PROVED — 1 declaration(s)
    # kernel-checked", so "Unknown identifier: toUInt64" is gone — `UInt8.toUInt64`
    # resolves now. The build refuses: exit 1, "The whole artifact was refused",
    # `widen` [source-shape/not-emittable].
    ("p12b_width_conversion", ("refused", "widen"), None, ["widen"]),
    ("p13_division", ("refused", "quot"), "should", ["quot"]),
    ("p14_lean_to_lean_call", ("refused", "inc2"), "should", ["inc2"]),
    ("p15_bitwise", ("refused", "mask"), "should", ["mask"]),
    ("p16_tree_33_nodes", ("refused", "big33"), None, []),
    ("p17_tree_32_nodes", ("built", ""), ({"big32": ([64], 64, lambda a: 33 * a % W64)}, {"big32": [(1,), (2 ** 60 + 5,)]}), []),
    ("p18_literal_out_of_range", ("refused", "lit300"), "should", []),
    ("p19_false_theorem", ("rejected", "dbl_wrong"), None, []),
    ("p20_bool_connective", ("refused", "both"), "should", ["both"]),
]
TL_PROBE = {p[0]: p for p in TL_PROBES}
TL_ROW = {p[0]: "ir-tl" + p[0][1:] for p in TL_PROBES}
# Negative controls: a refusal here is the CORRECT outcome (REFUSED), not a gap.
TL_TWINS = {"p16_tree_33_nodes", "p19_false_theorem"}

# FORMAT HOMES for what the standalone lane refuses: HAND-WRITTEN modules (ir-tl-format_home), one function per
# refused Lean def.  probe -> (module, {def: (widths, ret, model)}, {def: vectors}, (fn, old, new, expectation)).
SHOULD = {
    "p01_bool_result": ("scalar", {"isLt": ([64, 64], "bool", lambda a, b: a < b)}, {"isLt": [(3, 5), (5, 3), (W64 - 1, 0), (0, W64 - 1), (4, 4)]},
                        ("isLt", "icmp ult u64", "icmp ugt u64", "differs")),
    "p02_if_select": ("scalar", {"min2": ([64, 64], 64, lambda a, b: a if a < b else b)}, {"min2": [(7, 9), (W64 - 1, 1), (4, 4)]},
                      ("min2", "select u64 %2, %0, %1", "select u64 %2, %1, %0", "differs")),
    "p12b_width_conversion": ("scalar", {"widen": ([8], 64, lambda a: a)}, {"widen": [(0,), (200,), (255,)]},
                              ("widen", "zext u8 %0 to u64", "trunc u8 %0 to u64", "CastWidthDirectionInvalid")),
    "p13_division": ("scalar", {"quot": ([64, 64], 64, lambda a, b: 0 if b == 0 else a // b)}, {"quot": [(7, 2), (7, 0), (W64 - 1, 3), (0, 0)]},
                     ("quot", "%3 = icmp eq u64 %1, %2", "%3 = icmp ne u64 %1, %2", "traps:unsigned division by zero")),
    "p14_lean_to_lean_call": ("scalar", {"inc2": ([64], 64, lambda a: (a + 2) % W64), "inc": ([64], 64, lambda a: (a + 1) % W64)},
                              {"inc2": [(W64 - 1,), (40,)], "inc": [(W64 - 1,)]},
                              ("inc2", "%2 = call @func.3(%1)", "%2 = copy u64 %1", "differs")),
    "p15_bitwise": ("scalar", {"mask": ([64, 64], 64, lambda a, b: (a & b) | 1)}, {"mask": [(12, 10), (W64 - 1, W64 - 2), (0, 0)]},
                    ("mask", "and u64", "or u64", "differs")),
    "p18_literal_out_of_range": ("scalar", {"lit300": ([], 8, lambda: 300 % 256)}, {"lit300": [()]},
                                 ("lit300", "const u8 44", "const u8 300", "ConstTypeMismatch")),
    "p20_bool_connective": ("scalar", {"both": ([64, 64, 64], "bool", lambda a, b, c: a < b and b < c)},
                            {"both": [(3, 4, 5), (3, 5, 4), (W64 - 1, 0, 1), (0, W64 - 2, W64 - 1)]},
                            ("both", "and bool", "or bool", "differs")),
    "p06_inductive_match": ("enum", {"areaOfRect": ([64, 64], 64, lambda w, h: w * h % W64)}, {"areaOfRect": [(6, 7), (2 ** 32, 2 ** 32), (3, 3)]},
                            ("area", "0: bb1 1: bb2", "0: bb2 1: bb1", "differs")),
    "p07_structure": ("struct", {"dotOf": ([64] * 4, 64, lambda a, b, c, d: (a * c + b * d) % W64)}, {"dotOf": [(1, 2, 3, 4), (W64 - 1, W64 - 1, 2, 3)]},
                      ("dot", "add u64 %4, %7", "sub u64 %4, %7", "differs")),
}
SHOULD_HOME = {
    "p01_bool_result": "Ty::Bool + Inst::ICmp", "p02_if_select": "ICmp + Inst::Select", "p12b_width_conversion": "Inst::Cast{ZExt}",
    "p13_division": "BinOp::UDiv guarded by ICmp+CondBr (Lean x/0 = 0 is a BRANCH)", "p14_lean_to_lean_call": "Inst::Call",
    "p15_bitwise": "BinOp::And/Or", "p18_literal_out_of_range": "the REDUCED constant `const u8 44`",
    "p20_bool_connective": "BinOp::And at Ty::Bool", "p06_inductive_match": "Ty::Enum/EnumDef + ExtractField(tag) + Switch + InsertField",
    "p07_structure": "Ty::Struct/StructDef + ExtractField/InsertField",
}
# The general pipeline's closure-FnDef typing defect.  Closed upstream (WS6.14): its reappearance is a
# regression, judged FAIL by name — never "repaired" into a pass.
F108 = "F-108"


def lean_lit(w, a):
    return ("true" if a else "false") if w == "bool" else str(a)


def vec_statements(defs, vecs):
    out = []
    for n, (p, r, f) in defs.items():
        for v in vecs[n]:
            out.append((" ".join([n] + [lean_lit(w, a) for w, a in zip(p, v)]), lean_lit(r, int(f(*v)))))
    return out


def wrong(rhs):
    return {"true": "false", "false": "true"}.get(rhs) or str(int(rhs) + 1)


def mutate_fn(text, func, old, new):
    i = text.index("fn @%s(" % func)
    j = text.index("\n}", i)
    if text[i:j].count(old) != 1:
        raise ValueError("mutation anchor %r is not unique in @%s" % (old, func))
    return text[:i] + text[i:j].replace(old, new) + text[j:]


class PartALean:
    """One Part A-Lean tree (WORK/tl).  cwd for every tool is this tree, so the probe paths the tools print
    (`probes/<name>.lean`) are the audit's."""

    def __init__(self, work, tools):
        self.t = tools
        self.W = os.path.join(work, "tl")
        os.makedirs(os.path.join(self.W, "probes"), exist_ok=True)
        for name in TL_ROW:
            shutil.copy(ROWS_DIR / TL_ROW[name] / (name + ".lean"), os.path.join(self.W, "probes", name + ".lean"))
        for f in ("Lib.lean", "Use.lean"):
            shutil.copy(ROWS_DIR / "ir-tl-library" / f, os.path.join(self.W, f))
        # A WALL-CLOCK bound, so it must absorb machine load: measured 2026-09-19 on a shared host, ONE
        # `sub32 1 2 = 4294967295 := rfl` check took 38 s of CPU and 3:30 of wall time, and the archive's
        # 180 s default read it UNDECIDED (a FAIL).  Undecided stays a FAIL at any bound; this only stops
        # load from manufacturing one.
        self.oracle_timeout = int(os.environ.get("ORACLE_TIMEOUT", "900"))
        self.clean_repo = TRUST_ROOT / "first-party" / "clean"

    # ---- trust-ir helpers
    def validate(self, path, fmt=None):
        code, o, e = sh([self.t.cli, "validate"] + (["--format", fmt] if fmt else []) + [path])
        txt = o + e
        variants = sorted(set(re.findall(r"^\s*\[\d+\] (\w+)", txt, re.M)))
        return code == 0 and "module is well-formed" in txt, variants, txt

    def convert(self, src, sfmt, dst, dfmt):
        return sh([self.t.cli, "convert", "--from", sfmt, "--to", dfmt, src, dst])

    def roundtrip4(self, src, sfmt, stem):
        """canonical bin B0; then B0 -> {text,json,msgpack} -> bin must be byte-identical to B0."""
        wd = os.path.join(self.W, "rt")
        os.makedirs(wd, exist_ok=True)
        b0 = os.path.join(wd, stem + ".rt0.tmbc")
        if sfmt == "bin":
            shutil.copyfile(src, b0)
        else:
            code, o, e = self.convert(src, sfmt, b0, "bin")
            if code:
                return False, {"to-bin": first_line(o + e)}, 0
        res = {}
        ext = {"text": "trust_ir", "json": "json", "msgpack": "msgpack"}
        for f in ("text", "json", "msgpack"):
            mid, back = os.path.join(wd, "%s.rt.%s" % (stem, ext[f])), os.path.join(wd, "%s.rt.%s.tmbc" % (stem, f))
            rc1, o1, e1 = self.convert(b0, "bin", mid, f)
            rc2, o2, e2 = self.convert(mid, f, back, "bin") if rc1 == 0 else (1, "", "")
            res[f] = rc1 == 0 and rc2 == 0 and open(back, "rb").read() == open(b0, "rb").read()
            if not res[f]:
                res[f + "_err"] = first_line(o1 + e1 + o2 + e2)
        ver = int.from_bytes(open(b0, "rb").read()[8:12], "little")
        return all(res[f] for f in ("text", "json", "msgpack")), res, ver

    def interp(self, mods, entry):
        code, o, e = sh([self.t.cli, "run", "--validate", "--entry", entry] + list(mods))
        val = o.strip().splitlines()[-1].strip() if code == 0 and o.strip() else None
        return code, val, interp_error(e)

    def exec_vectors(self, module_path, defs, vecs, stem):
        """nullary-driver differential: reference interpreter vs the kernel-certified expected values."""
        drv, exp = os.path.join(self.W, stem + ".driver.trust_ir"), os.path.join(self.W, stem + ".expected.json")
        gen_driver(drv, exp, defs, vecs)
        ok, _, txt = self.validate(drv)
        if not ok:
            return False, "driver invalid: " + first_line(txt, 3), 0, drv
        expd, bad = json.load(open(exp)), []
        for t, x in expd.items():
            code, val, err = self.interp([module_path, drv], t)
            if code != 0 or val is None or int(val) != x["expected"]:
                bad.append("%s got=%s want=%s %s" % (t, val, x["expected"], err))
        return not bad, "; ".join(bad[:4]), len(expd), drv

    def kernel_oracle(self, sources, imports, stmts):
        """Each expected value restated as `theorem k_i : lhs = rhs := rfl` and checked by the kernel of the
        compiler under test (`targo trust check`).  Twin: the first proved vector off by one must be REJECTED."""
        def check(thms, td, fname):
            body = "".join("theorem k_%d : %s = %s := rfl\n" % (i, l, r) for i, (l, r) in enumerate(thms))
            text = (open(sources[0]).read() + "\n" + body) if imports is None else "".join("import %s\n" % m for m in imports) + body
            open(os.path.join(td, fname), "w").write(text)
            try:
                code, o, e = sh([self.t.targo, "trust", "check", fname], cwd=td, timeout=self.oracle_timeout, env=scrubbed_env())
            except subprocess.TimeoutExpired:
                return "undecided", "kernel check exceeded the time limit"
            return ("proved" if code == 0 and ("PROVED " + fname) in (o + e) else "refuted"), o + e
        td = tempfile.mkdtemp(dir=self.W, prefix="oracle.")
        try:
            if imports is not None:
                for s in sources:
                    shutil.copy(s, td)
            st_all, _ = check(stmts, td, "K.lean")
            each = ["proved"] * len(stmts) if st_all == "proved" else [check([s], td, "K1.lean")[0] for s in stmts]
            first = each.index("proved") if "proved" in each else 0
            l0, r0 = stmts[first]
            st_bad, txt_bad = check([(l0, wrong(r0))], td, "Kbad.lean")
            twin = st_bad == "refuted" and "k_0" in txt_bad
        finally:
            shutil.rmtree(td, ignore_errors=True)
        note = "; ".join("%s: %s = %s" % (st.upper(), l, r) for st, (l, r) in zip(each, stmts) if st != "proved")
        return each.count("proved"), len(stmts), twin, note[:300]

    @staticmethod
    def oracle_phrase(c, n, twin, who):
        return "expected values KERNEL-CERTIFIED by %s: %d/%d `f args = v := rfl` theorems PROVED; twin(first vector off by one) REJECTED=%s" % (
            who, c, n, twin)

    def targo(self, *args, cwd=None):
        return sh([self.t.targo] + list(args), cwd=cwd or self.W, env=scrubbed_env())

    # ================================================= LEAN.*: the standalone library lane (Lib.lean + Use.lean)
    def library(self, R):
        W, lane = self.W, "tool=targo-standalone-lean"
        code, o, e = self.targo("trust", "check", "Lib.lean", "Use.lean")
        proved = re.findall(r"^PROVED (\S+) — (\d+) declaration", o + e, re.M)
        ok_check = code == 0 and len(proved) == 2
        td = tempfile.mkdtemp(dir=W, prefix="lone.")
        try:
            shutil.copy(os.path.join(W, "Use.lean"), td)
            rc2, o2, e2 = self.targo("trust", "check", "Use.lean", cwd=td)
        finally:
            shutil.rmtree(td, ignore_errors=True)
        twin1 = rc2 != 0 and "REJECTED Use.lean" in (o2 + e2)
        rc3, o3, e3 = self.targo("trust", "check", "probes/p19_false_theorem.lean")
        twin2 = rc3 != 0 and "REJECTED" in (o3 + e3) and "dbl_wrong" in (o3 + e3)
        R.add("LEAN.check.multi_file", "PASS" if ok_check and twin1 and twin2 else "FAIL",
              "%s; check Lib.lean Use.lean -> %s; twin(lone Use.lean in empty dir) rejected=%s [%s]; twin(false theorem dbl_wrong) rejected=%s"
              % (lane, proved, twin1, first_line(o2 + e2)[:160], twin2))
        env_path, cen = os.path.join(W, "lib.irlib.json"), os.path.join(W, "lib.census.json")
        for p in (env_path, cen):
            if os.path.exists(p):
                os.remove(p)
        code, o, e = self.targo("trust", "build", "Use.lean", "--emit=trust-ir", "--out", env_path, "--census", cen)
        if code != 0 or not os.path.exists(env_path):
            R.add("LEAN.build.envelope", "FAIL", lane + "; " + first_line(o + e, 4))
            return
        rcx, ox, ex = self.targo("trust", "build", "Use.lean", "--emit=trust-ir", "--out", env_path)
        twin_exist = rcx != 0 and "already exists" in (ox + ex)
        envd = json.load(open(env_path))
        bodies = {b["declaration"]["Str"][1]: b for b in envd["bodies"]}
        konly = [d["Str"][1] for d in envd["kernel_only_declarations"]]
        want_thm = {"fst3_eq", "addmul_def", "snd32_eq", "fst3_again", "horner_def"}
        ok = (envd["schema"] == "trust.lean.ir-library/v1" and set(bodies) == set(LIB_DEFS) and set(konly) == want_thm
              and all(b["method"] == "definitional-equality" for b in bodies.values()))
        R.add("LEAN.build.envelope", "PASS" if ok and twin_exist else "FAIL",
              "%s; schema=%s authority=%s native_codegen=%s bodies=%d (all method=definitional-equality: %s) kernel_only_theorems=%d "
              "sources=%s; twin(existing --out) refused=%s" % (lane, envd["schema"], envd["authority"], envd["native_codegen"], len(bodies),
                                                              ok, len(konly), [s["path"] for s in envd["sources"]], twin_exist))
        mod = os.path.join(W, "lib.tmbc")
        raw = bytes.fromhex(envd["module_binary_hex"])
        open(mod, "wb").write(raw)
        sha_ok = hashlib.sha256(raw).hexdigest() == envd["module_sha256"]
        neg = os.path.join(W, "neg")
        os.makedirs(neg, exist_ok=True)
        open(os.path.join(neg, "trailing.tmbc"), "wb").write(raw + b"\0")
        okt, _, txtt = self.validate(os.path.join(neg, "trailing.tmbc"))
        twin_trail = (not okt) and "trailing bytes after canonical module payload" in txtt
        R.add("LEAN.envelope.module_sha256", "PASS" if sha_ok and twin_trail else "FAIL",
              "sha256(module_binary_hex)==module_sha256 %s; twin(+1 trailing byte) refused by decoder=%s" % (sha_ok, twin_trail))
        ok, variants, _ = self.validate(mod)
        text = os.path.join(W, "lib.trust_ir")
        self.convert(mod, "bin", text, "text")
        src = open(text).read()
        i = src.index("fn @addmul")
        j = src.index("}", i)
        open(os.path.join(neg, "ty_mut.trust_ir"), "w").write(src[:i] + src[i:j].replace("mul u64 %0, %1", "mul u32 %0, %1") + src[j:])
        okm, varm, txtm = self.validate(os.path.join(neg, "ty_mut.trust_ir"))
        twin_ty = (not okm) and "OperandTypeMismatch" in varm and re.search(r'OperandTypeMismatch \{ block: 0, op: "mul"', txtm) is not None
        R.add("LEAN.module.validate", "PASS" if ok and twin_ty else "FAIL",
              "validate_module (gitlink CLI) ok=%s; twin(addmul `mul u64`->`mul u32`) refused with %s" % (ok, varm))
        rt_ok, res, ver = self.roundtrip4(mod, "bin", "lib")
        R.add("LEAN.module.roundtrip4", "PASS" if rt_ok and twin_trail else "FAIL",
              "bin->{text,json,msgpack}->bin byte-identical=%s; wire header v%d; twin = trailing-byte blob refused" % (res, ver))
        jpath = os.path.join(W, "lib.json")
        self.convert(mod, "bin", jpath, "json")
        m = json.load(open(jpath))
        fn = {f["name"]: f for f in m["functions"]}
        fty = m["func_types"]
        ty_name = lambda t: t.lower() if isinstance(t, str) else json.dumps(t)
        carr_ok = all(n in fn and ty_name(fty[fn[n]["ty"]]["returns"][0]) == b["carrier"].replace("UInt", "u") for n, b in bodies.items())
        prod_ok = all(f["producer"] == "Clean" for f in m["functions"])
        R.add("LEAN.module.producer_and_carrier", "PASS" if carr_ok and prod_ok and m["files"] == [s["path"] for s in envd["sources"]] else "FAIL",
              "every function producer=Clean (%s); envelope carrier UIntN == FuncTy return uN for all %d bodies (%s); Module.files=%s; "
              "twin = ty_mut (carrier/body width skew is OperandTypeMismatch)" % (prod_ok, len(bodies), carr_ok, m["files"]))
        okx, badx, n, drv = self.exec_vectors(mod, LIB_DEFS, LIB_VEC, "lib")
        kc, kn, ktwin, knote = self.kernel_oracle([os.path.join(W, "Lib.lean"), os.path.join(W, "Use.lean")], ["Lib", "Use"],
                                                  vec_statements(LIB_DEFS, LIB_VEC))
        R.add("LEAN.oracle.kernel_vectors", "PASS" if kc == kn == n and ktwin else "FAIL",
              "tool=targo kernel: %s %s — the python model is therefore not the oracle, the Lean kernel is"
              % (self.oracle_phrase(kc, kn, ktwin, "`targo trust check`"), knote))
        open(os.path.join(neg, "sem_mut.trust_ir"), "w").write(src[:i] + src[i:j].replace("mul u64", "add u64") + src[j:])
        _, vmut, _ = self.interp([os.path.join(neg, "sem_mut.trust_ir"), drv], "t_addmul_0")
        _, vgood, _ = self.interp([mod, drv], "t_addmul_0")
        twin_sem = vmut == "10" and vgood == "15"
        drvtxt = open(drv).read()
        open(os.path.join(neg, "driver_sig.trust_ir"), "w").write(re.sub(r"fn @wrap8\(functy\.\d+\)", "fn @wrap8(functy.0)", drvtxt, 1))
        rcl, ol, el = sh([self.t.cli, "run", "--validate", "--entry", "t_wrap8_0", mod, os.path.join(neg, "driver_sig.trust_ir")])
        twin_link = rcl != 0 and "signature mismatch for @wrap8" in (ol + el)
        R.add("LEAN.module.interpret", "PASS" if okx and twin_sem and twin_link and kc == kn == n else "FAIL",
              "%d nullary-driver vectors over %d Lean defs == kernel-certified Lean semantics under `trust-ir run` %s; twin(mul->add body) "
              "detected (10 vs 15)=%s; twin(driver declares wrap8 at the wrong FuncTy) link refused=%s" % (n, len(bodies), badx, twin_sem, twin_link))
        # ---- which envelope facts have a HOME in the module?  (named absences, judged on VALUES)
        none_gate = all(f.get("body_gate") is None for f in m["functions"])
        if none_gate:
            R.add("LEAN.home.body_gate.populated", "GAP", "the per-body gate verdict lives only in the envelope: all %d functions carry "
                  "body_gate=None and the writer selected v%d. Home EXISTS: Function.body_gate / BodyGate; a v41 producer MUST emit "
                  "Ungated or Gated" % (len(m["functions"]), ver), "producer-gap", sig="body_gate=None on %d/%d functions" % (
                      len(m["functions"]), len(m["functions"])))
        else:
            R.add("LEAN.home.body_gate.populated", "PASS", "body_gate stamped on %d/%d functions: %s" % (
                sum(1 for f in m["functions"] if f.get("body_gate") is not None), len(m["functions"]),
                sorted({json.dumps(f.get("body_gate")) for f in m["functions"]})))
        nob, ncert = len(m.get("proof_obligations") or []), len(m.get("proof_certificates") or [])
        nsum, nimp = sum(1 for f in m["functions"] if f.get("summary")), len(m.get("imports") or [])
        R.add("LEAN.home.gate_evidence.populated", "GAP" if (nob, ncert, nsum, nimp) == (0, 0, 0, 0) else "FAIL",
              "envelope bodies[].{method,kernel_payload_sha256,subject_digest} have a home as ProofObligation{TranslationValidation} + "
              "ProofCertificate{CleanCic} but the module carries obligations=%d certificates=%d summaries=%d imports=%d" % (nob, ncert, nsum, nimp),
              "producer-gap" if (nob, ncert, nsum, nimp) == (0, 0, 0, 0) else None,
              sig="obligations=0:certificates=0:summaries=0:imports=0" if (nob, ncert, nsum, nimp) == (0, 0, 0, 0) else None)
        g = json.loads(json.dumps(m))
        for f in g["functions"]:
            f["body_gate"] = {"Gated": {"authority": "trust.lean.ir-library/v1:definitional-equality"}}
        gp = os.path.join(W, "home_gated.json")
        json.dump(g, open(gp, "w"))
        okg, _, _ = self.validate(gp)
        rtg, _, verg = self.roundtrip4(gp, "json", "home_gated")
        self.convert(os.path.join(W, "rt", "home_gated.rt0.tmbc"), "bin", os.path.join(W, "home_gated.rt.json"), "json")
        try:
            same = json.load(open(os.path.join(W, "home_gated.rt.json"))) == g
        except (OSError, ValueError):
            same = False
        bad = json.loads(json.dumps(g))
        bad["functions"][0]["body_gate"] = {"Gated": {}}
        bp = os.path.join(neg, "gated_no_authority.json")
        json.dump(bad, open(bp, "w"))
        okb, _, txtb = self.validate(bp)
        twin_g = (not okb) and "missing field `authority`" in txtb
        R.add("LEAN.home.body_gate", "PASS" if okg and rtg and same and verg >= 41 and twin_g else "FAIL",
              "the same module re-stamped body_gate=Gated{authority} validates, round-trips 4 formats losslessly and the writer selects v%d; "
              "twin(Gated without authority) refused=%s [%s]" % (verg, twin_g, first_line(txtb)[:120]))
        h = json.loads(json.dumps(g))
        for f in h["functions"]:
            f["body_gate"]["Gated"]["subject_digest"] = bodies.get(f["name"], {}).get("subject_digest")
            f["body_gate"]["Gated"]["kernel_payload_sha256"] = bodies.get(f["name"], {}).get("kernel_payload_sha256")
        hp, hb, hj = os.path.join(W, "home_gated_digest.json"), os.path.join(W, "home_gated_digest.tmbc"), os.path.join(W, "home_gated_digest.rt.json")
        json.dump(h, open(hp, "w"))
        rc1, _, _ = self.convert(hp, "json", hb, "bin")
        self.convert(hb, "bin", hj, "json")
        back = json.load(open(hj))["functions"][0]["body_gate"] if rc1 == 0 and os.path.exists(hj) else None
        lost = back == {"Gated": {"authority": "trust.lean.ir-library/v1:definitional-equality"}}
        R.add("LEAN.home.gate_digest_slot", "GAP" if lost else "FAIL",
              "format gap: BodyGate::Gated is {authority: String} only — the envelope per-body subject_digest / kernel_payload_sha256 have no "
              "slot; added beside authority they are silently DROPPED by decode->encode (round-tripped body_gate=%s)" % json.dumps(back),
              "format-gap" if lost else None, sig="Gated{authority} only: subject_digest+kernel_payload_sha256 dropped" if lost else None)
        k = json.loads(json.dumps(m))
        k["files"] = [{"path": s["path"], "sha256": s["sha256"]} for s in envd["sources"]]
        kp = os.path.join(W, "home_files_digest.json")
        json.dump(k, open(kp, "w"))
        okk, _, txtk = self.validate(kp)
        name_has = envd.get("source_closure_sha256", "\0") in m["name"]
        hit = (not okk) and "invalid type: map, expected a string" in txtk and name_has
        R.add("LEAN.home.source_digest", "GAP" if hit else "FAIL",
              "format gap: Module.files is Vec<String> of paths — a {path,sha256} row is refused (%s); the envelope sources[].sha256 have no "
              "home, and source_closure_sha256 survives only as a substring of Module.name" % first_line(txtk)[:90],
              "format-gap" if hit else None, sig="Module.files: invalid type: map, expected a string" if hit else None)
        thm_absent = not any(t in open(text).read() or t in json.dumps(m) for t in konly)
        kot = thm_absent and nob == 0 and ncert == 0
        R.add("LEAN.home.kernel_only_theorems.populated", "GAP" if kot else "FAIL",
              "the %d kernel-only theorems (%s) leave NO trace in the emitted module (no obligation, no certificate, name absent from text and "
              "JSON) although the format can carry statement + proof term" % (len(konly), ",".join(sorted(konly))),
              "producer-gap" if kot else None, sig="theorems=%s:absent" % sorted(konly) if kot else None)
        fid = fn["fst3"]["id"]

        def thm_module(status, kind="Postcondition"):
            t = json.loads(json.dumps(m))
            t["proof_obligations"] = [{"id": 0, "kind": kind, "status": status, "description": "Lean theorem fst3_eq (Lib.lean)",
                                       "formula": {"schema": "lean4.prop", "payload": "∀ (a b c : UInt64), fst3 a b c = a",
                                                   "smtlib": None, "sort": None, "bindings": []},
                                       "function": fid, "source": None, "site": None}]
            t["proof_certificates"] = [{"obligation": 0, "prover": "clean-kernel", "evidence": {"LeanProof": "fun a b c => rfl"}}]
            return t
        tp = os.path.join(W, "home_theorem.json")
        json.dump(thm_module("Pending"), open(tp, "w"), ensure_ascii=False)
        okt2, _, _ = self.validate(tp)
        rtd = os.path.join(W, "rt")
        tb, tj, tm, tb2 = (os.path.join(rtd, x) for x in ("home_theorem.tmbc", "home_theorem.back.json", "home_theorem.msgpack", "home_theorem.2.tmbc"))
        self.convert(tp, "json", tb, "bin")
        self.convert(tb, "bin", tj, "json")
        self.convert(tb, "bin", tm, "msgpack")
        self.convert(tm, "msgpack", tb2, "bin")
        back = json.load(open(tj)) if os.path.exists(tj) else {}

        def norm(x):     # serde skips trailing None / [] fields: compare modulo absent-vs-empty
            if isinstance(x, dict):
                return {kk: norm(v) for kk, v in x.items() if v not in (None, [])}
            return [norm(v) for v in x] if isinstance(x, list) else x
        lossless = (norm(back.get("proof_obligations")) == norm(thm_module("Pending")["proof_obligations"])
                    and (back.get("proof_certificates") or [{}])[0].get("evidence") == {"LeanProof": "fun a b c => rfl"}
                    and os.path.exists(tb2) and open(tb, "rb").read() == open(tb2, "rb").read())
        twins = {}
        for status, want in (("Discharged", "DischargedWithoutCertificate"), ("Certified", "CertifiedWithoutCleanCic")):
            qp = os.path.join(neg, "theorem_%s.json" % status.lower())
            json.dump(thm_module(status), open(qp, "w"), ensure_ascii=False)
            okq, varq, _ = self.validate(qp)
            twins[status] = (not okq) and varq == [want]
        qp = os.path.join(neg, "theorem_custom_ns.json")
        json.dump(thm_module("Pending", {"Custom": {"namespace": "lean4.theorem", "name": "fst3_eq"}}), open(qp, "w"), ensure_ascii=False)
        okq, varq, _ = self.validate(qp)
        twins["custom-namespace"] = (not okq) and varq == ["UnpinnedCustomObligationNamespace"]
        R.add("LEAN.home.theorem_statement", "PASS" if okt2 and lossless and twins["Discharged"] and twins["custom-namespace"] else "FAIL",
              "a Lean theorem HAS a carrier: the emitted module + ONE ProofObligation{Postcondition, Pending, formula{lean4.prop}} + ONE "
              "ProofCertificate{LeanProof} validates (%s) and is lossless through binary/json/msgpack (%s). Twins: status=Discharged -> "
              "DischargedWithoutCertificate=%s; kind=Custom{lean4.theorem} -> UnpinnedCustomObligationNamespace=%s"
              % (okt2, lossless, twins["Discharged"], twins["custom-namespace"]))
        cert_gap = okt2 and twins["Certified"]
        R.add("LEAN.home.theorem_certified_tier", "GAP" if cert_gap else "FAIL",
              "format gap: from the WELL-FORMED Pending theorem row above, the single change status=Certified is refused with "
              "CertifiedWithoutCleanCic=%s — Certified requires ProofEvidence::CleanCic, whose re-checker resolves a CLOSED anchor list with "
              "no anchor meaning \"this user theorem, re-checked\"" % twins["Certified"], "format-gap" if cert_gap else None,
              sig="status=Certified -> [CertifiedWithoutCleanCic]" if cert_gap else None)
        libonly = os.path.join(W, "libonly.irlib.json")
        if os.path.exists(libonly):
            os.remove(libonly)
        rcl1, ol1, el1 = self.targo("trust", "build", "Lib.lean", "--emit=trust-ir", "--out", libonly)
        if rcl1 == 0 and os.path.exists(libonly):
            le = json.load(open(libonly))
            lib_bodies = {b["declaration"]["Str"][1] for b in le["bodies"]}
            flattened = lib_bodies < set(bodies) and all(any(f["name"] == nm and f["blocks"] for f in m["functions"]) for nm in lib_bodies)
            hit = flattened and not (m.get("imports") or []) and le["module_sha256"] != envd["module_sha256"]
            R.add("LEAN.home.cross_file_import.populated", "GAP" if hit else "FAIL",
                  "separate compilation is not used: building Use.lean (`import Lib`) RE-EMITS all %d Lib bodies as local definitions in one "
                  "module (Lib.lean alone builds its own, different module), and Module.imports=[] — no ModuleImport/ExternRef edge"
                  % len(lib_bodies), "producer-gap" if hit else None, sig="imports=[]:Lib bodies re-embedded=%d" % len(lib_bodies) if hit else None)
        else:
            R.add("LEAN.home.cross_file_import.populated", "FAIL", "Lib.lean alone did not build: " + first_line(ol1 + el1, 2))
        self.library_consumers(R, mod, text, m, neg)

    def library_consumers(self, R, mod, text, m, neg):
        W = self.W
        try:
            tcg = self.t.path("trust-cg")
        except ToolError as e:
            for rid in ("LEAN.consumer.binary_container", "LEAN.module.native_differential", "LEAN.consumer.ungated_codegen"):
                R.add(rid, "FAIL", "trust-cg judge unavailable: %s" % e)
            return
        nat = os.path.join(W, "native")
        os.makedirs(nat, exist_ok=True)
        rcb, ob, eb = sh([tcg, "-c", "-o", os.path.join(nat, "lib_bin.o"), mod])
        rca, oa, ea = sh([tcg, "--format=auto", "-c", "-o", os.path.join(nat, "lib_bin_auto.o"), mod])
        if rcb == 0 and rca == 0:
            R.add("LEAN.consumer.binary_container", "PASS", "trust-cg reads the canonical trust-ir binary (magic TRUST_IR) in both the default "
                  "and the --format=auto lane")
        elif rcb != 0 and "tMBC magic" in (ob + eb) and rca != 0 and "tMBC magic" in (oa + ea):
            R.add("LEAN.consumer.binary_container", "GAP", "tool=trust-cg: the canonical trust-ir binary (magic TRUST_IR) is refused under the "
                  "default `binary` format (%s) AND under --format=auto (%s) — trust-cg's \"binary\" is its own tMBC container"
                  % (first_line(ob + eb)[:160], first_line(oa + ea)[-90:]), "consumer-gap", sig="default+auto: expected tMBC magic")
        else:
            R.add("LEAN.consumer.binary_container", "FAIL", "unnamed outcome: default rc=%s (%s); auto rc=%s (%s)"
                  % (rcb, first_line(ob + eb)[:120], rca, first_line(oa + ea)[:120]))
        rct, ot, et = sh([tcg, "--format=text", "-c", "-o", os.path.join(nat, "lib.o"), text])
        cm = os.path.join(nat, "lib_main.c")
        c_main(cm, LIB_DEFS, LIB_VEC)
        rcc = sh([self.t.cc, "-O1", "-w", cm, os.path.join(nat, "lib.o"), "-o", os.path.join(nat, "lib_native")])[0] if rct == 0 else 1
        expd = json.load(open(os.path.join(W, "lib.expected.json")))
        bad = []
        if rcc == 0:
            got = dict(l.split() for l in sh([os.path.join(nat, "lib_native")])[1].strip().splitlines())
            bad = [t for t, x in expd.items() if int(got.get(t, -1)) != x["expected"]]
        caught = False
        if sh([tcg, "--format=text", "-c", "-o", os.path.join(nat, "sem_mut.o"), os.path.join(neg, "sem_mut.trust_ir")])[0] == 0 and \
                sh([self.t.cc, "-O1", "-w", cm, os.path.join(nat, "sem_mut.o"), "-o", os.path.join(nat, "sem_mut_native")])[0] == 0:
            gm = dict(l.split() for l in sh([os.path.join(nat, "sem_mut_native")])[1].strip().splitlines())
            caught = int(gm.get("t_addmul_0", -1)) == 10
        R.add("LEAN.module.native_differential", "PASS" if rct == 0 and rcc == 0 and not bad and caught else "FAIL",
              "tool=trust-cg --format=text rc=%s; the object run natively agrees with Lean semantics AND the reference interpreter on all %d "
              "vectors (mismatches=%s); twin(mul->add mutant object) caught=%s" % (rct, len(expd), bad, caught))
        u = json.loads(json.dumps(m))
        for f in u["functions"]:
            f["body_gate"] = "Ungated"
        up = os.path.join(W, "home_ungated.json")
        json.dump(u, open(up, "w"))
        oku, _, _ = self.validate(up)
        rcu, ou, eu = sh([tcg, "--format=json", "-c", "-o", os.path.join(nat, "ungated.o"), up])
        honours = rcu != 0 and "ungated" in (ou + eu)
        if oku and honours:
            R.add("LEAN.consumer.ungated_codegen", "PASS", "tool=trust-cg REFUSES the module re-stamped body_gate=Ungated (which validates): %s"
                  % first_line(ou + eu)[:200])
        elif oku and rcu == 0:
            R.add("LEAN.consumer.ungated_codegen", "GAP", "tool=trust-cg compiles a module every function of which is stamped body_gate=Ungated "
                  "(\"Codegen must refuse\"): %s" % first_line(ou + eu)[:160], "consumer-gap", sig="Ungated module compiled")
        else:
            R.add("LEAN.consumer.ungated_codegen", "FAIL", "Ungated module validates=%s, trust-cg rc=%s: %s" % (oku, rcu, first_line(ou + eu)[:200]))

    # ================================================= FORMAT_HOME.*: the hand-written should_emit modules
    def format_homes(self, R):
        W = self.W
        hdir = os.path.join(W, "should_emit")
        os.makedirs(hdir, exist_ok=True)
        base = {}
        for kind in ("scalar", "struct", "enum"):
            path = str(ROWS_DIR / "ir-tl-format_home" / (kind + ".trust_ir"))
            ok, var, _ = self.validate(path)
            rt, _, ver = self.roundtrip4(path, "text", "should_" + kind)
            base[kind] = (path, ok, var, rt, ver)
        for name, (kind, defs, vecs, (mfn, old, new, want)) in SHOULD.items():
            path, ok, var, rt, ver = base[kind]
            okx, bad, n, _ = self.exec_vectors(path, defs, vecs, "should_emit/" + name)
            src = os.path.join(W, "probes", name + ".lean")
            if name == "p12b_width_conversion":
                kc, kn, ktwin = 0, 0, True
                kphrase = "NO kernel oracle possible: `UInt8.toUInt64` does not elaborate in this Clean prelude (STANDALONE.p12b)"
            else:
                kc, kn, ktwin, knote = self.kernel_oracle([src], None, vec_statements(defs, vecs))
                kphrase = self.oracle_phrase(kc, kn, ktwin, "`targo trust check` on probes/%s.lean" % name) + (" " + knote if knote else "")
            mpath = os.path.join(hdir, name + ".mutant.trust_ir")
            open(mpath, "w").write(mutate_fn(open(path).read(), mfn, old, new))
            okm, varm, _ = self.validate(mpath)
            if want == "differs":
                okmx, badm, _, _ = self.exec_vectors(mpath, defs, vecs, "should_emit/%s.mutant" % name)
                twin, tdesc = okm and not okmx, "vectors catch it (%s)" % badm[:80]
            elif want.startswith("traps:"):
                okmx, badm, _, _ = self.exec_vectors(mpath, defs, vecs, "should_emit/%s.mutant" % name)
                twin, tdesc = okm and (not okmx) and want[6:] in badm, "still validates, interpreter traps \"%s\"" % want[6:]
            else:
                twin, tdesc = (not okm) and varm == [want], "validator refuses with %s" % varm
            good = ok and rt and okx and kc == kn and ktwin and twin
            R.add("FORMAT_HOME." + name, "PASS" if good else "FAIL",
                  "HAND-WRITTEN %s.trust_ir (producer=clean) carries what the standalone lane refuses via %s: validate ok=%s; 4-format round "
                  "trip=%s (v%d); %d interpreter vectors == expected %s; %s; twin(@%s: `%s` -> `%s`): %s => %s"
                  % (kind, SHOULD_HOME[name], ok, rt, ver, n, bad, kphrase, mfn, old, new, tdesc, twin))
        try:
            tcg = self.t.path("trust-cg")
        except ToolError as e:
            for rid in ("FORMAT_HOME.native.scalar", "FORMAT_HOME.native.struct", "FORMAT_HOME.native.enum"):
                R.add(rid, "FAIL", "trust-cg judge unavailable: %s" % e)
            return
        nat = os.path.join(W, "native")
        os.makedirs(nat, exist_ok=True)
        for kind in ("scalar", "struct"):
            defs, vecs = {}, {}
            for name, (k, d, v, _) in SHOULD.items():
                if k == kind:
                    defs.update(d)
                    vecs.update(v)
            cm = os.path.join(nat, "should_%s_main.c" % kind)
            c_main(cm, defs, vecs)

            def native_bad(text_path, stem):
                o_, x_ = os.path.join(nat, stem + ".o"), os.path.join(nat, stem)
                code_, oo, ee = sh([tcg, "--format=text", "-c", "-o", o_, text_path])
                if code_ or sh([self.t.cc, "-O1", "-w", cm, o_, "-o", x_])[0]:
                    return None, first_line(oo + ee)
                got_ = dict(l.split() for l in sh([x_])[1].strip().splitlines())
                return ({"t_%s_%d" % (n_, k_): got_.get("t_%s_%d" % (n_, k_)) for n_, (_, _, f) in defs.items() for k_, v in enumerate(vecs[n_])
                         if int(got_.get("t_%s_%d" % (n_, k_), -1)) != int(f(*v))}, first_line(oo + ee))
            bad, msg = native_bad(base[kind][0], "should_" + kind)
            if kind == "struct" and bad:
                # MISCOMPILE control: give the second InsertField chain its OWN seed and change nothing else; if that object is right,
                # the consumer is updating the shared SSA aggregate in place.
                t0 = open(base[kind][0]).read()
                old_ = "    %7 = insertfield struct.0 %4, 0, %2\n    %8 = insertfield struct.0 %7, 1, %3\n    %9 = call @func.0(%6, %8)\n    ret %9"
                new_ = ("    %7 = const struct.0 { 0, 0 }\n    %8 = insertfield struct.0 %7, 0, %2\n    %9 = insertfield struct.0 %8, 1, %3\n"
                        "    %10 = call @func.0(%6, %9)\n    ret %10")
                ctrl = os.path.join(hdir, "struct.distinct_seed.trust_ir")
                open(ctrl, "w").write(t0.replace(old_, new_))
                okc, _, _ = self.validate(ctrl)
                cbad, _ = native_bad(ctrl, "should_struct_distinct_seed")
                alias = bad.get("t_dotOf_0") == "25"
                hit = t0.count(old_) == 1 and okc and cbad == {} and alias
                R.add("FORMAT_HOME.native.struct", "GAP" if hit else "FAIL",
                      "tool=trust-cg --format=text SILENT MISCOMPILE: the valid, interpreter-correct struct module compiles without a "
                      "diagnostic and dotOf(1,2,3,4)=25 instead of 11 (mismatches=%s): two InsertField chains from ONE SSA aggregate are "
                      "lowered as in-place updates of shared storage. Control (private seed, no other change) natively correct: %s"
                      % (bad, cbad == {}), "consumer-gap" if hit else None,
                      sig="dotOf(1,2,3,4)=25: shared-seed InsertField aliasing; distinct-seed control correct" if hit else None)
                continue
            R.add("FORMAT_HOME.native." + kind, "PASS" if bad == {} else "FAIL",
                  "tool=trust-cg --format=text: %s; natively run object == the kernel-certified expected values on all %d vectors (mismatches=%s)"
                  % (msg[:80], sum(len(v) for v in vecs.values()), bad))
        code, o, e = sh([tcg, "--format=text", "-c", "-o", os.path.join(nat, "should_enum.o"), base["enum"][0]])
        # TWO named refusal classes, not one loose substring. `got Enum` is the
        # older, generic type-mismatch refusal. Since 2026-09-21 trust-cg refuses
        # this module far more specifically — MEASURED verbatim:
        #
        #   adapter error: enum 0 (`Shape`): InsertField at payload element 1 needs
        #   value-semantic (fresh-slot) insert lowering, which is not implemented;
        #   refusing rather than update shared storage in place
        #
        # That is an IMPROVEMENT in the fail-closed direction and it must stay a
        # named GAP, not decay to `unnamed refusal` + FAIL. It is the same defect
        # `FORMAT_HOME.native.struct` pins as a SILENT MISCOMPILE (two InsertField
        # chains from one SSA aggregate lowered as in-place updates of shared
        # storage, dotOf(1,2,3,4)=25 instead of 11) — on the enum path trust-cg now
        # REFUSES it instead of emitting the wrong answer, which is exactly the
        # trade this project wants. Each class carries its OWN signature, so a move
        # BETWEEN them still flips the ratchet rather than passing silently, and any
        # third refusal shape is still an unnamed FAIL.
        enum_out = o + e
        enum_refusal = None
        if "got Enum" in enum_out:
            enum_refusal = ("enum module refused: got Enum",
                            "by-value Ty::Enum ExtractField/InsertField has no lowering")
        elif "InsertField" in enum_out and "not implemented" in enum_out:
            enum_refusal = ("enum module refused: InsertField needs value-semantic (fresh-slot) insert lowering",
                            "refusing rather than lowering an InsertField as an in-place update of shared storage "
                            "(the miscompile FORMAT_HOME.native.struct pins)")
        if code != 0 and enum_refusal is not None and base["enum"][1]:
            R.add("FORMAT_HOME.native.enum", "GAP", "tool=trust-cg: the valid, interpreter-executable enum module is refused by this consumer: "
                  "%s — %s" % (first_line(enum_out)[-200:], enum_refusal[1]), "consumer-gap",
                  sig=enum_refusal[0])
        elif code == 0:
            R.add("FORMAT_HOME.native.enum", "PASS", "tool=trust-cg lowers the by-value enum module")
        else:
            R.add("FORMAT_HOME.native.enum", "FAIL", "unnamed refusal: %s" % first_line(o + e)[-200:])

    # ================================================= STANDALONE.<probe>
    def standalone(self, R, name):
        kind, decl = TL_PROBE[name][1]
        execspec = TL_PROBE[name][2]
        if execspec == "should":      # vectors for a probe the recorded compiler refuses: used if a newer one BUILDS it
            execspec = (SHOULD[name][1], SHOULD[name][2])
        src = "probes/%s.lean" % name
        code, o, e = self.targo("trust", "check", src)
        chk = o + e
        proved = "PROVED" in chk and code == 0
        pdir = os.path.join(self.W, "probes-out")
        os.makedirs(pdir, exist_ok=True)
        envp = os.path.join(pdir, name + ".irlib.json")
        if os.path.exists(envp):
            os.remove(envp)
        rcb, ob, eb = self.targo("trust", "build", src, "--emit=trust-ir", "--out", envp)
        bld = ob + eb
        rid = "STANDALONE." + name
        if os.path.exists(envp):
            envd = json.load(open(envp))
            mod = os.path.join(pdir, name + ".tmbc")
            open(mod, "wb").write(bytes.fromhex(envd["module_binary_hex"]))
            ok, _, _ = self.validate(mod)
            rt, _, ver = self.roundtrip4(mod, "bin", name)
            if execspec:
                okx, bad, n, _ = self.exec_vectors(mod, execspec[0], execspec[1], "probes-out/" + name)
                kc, kn, ktwin, knote = self.kernel_oracle([os.path.join(self.W, src)], None, vec_statements(execspec[0], execspec[1]))
            else:
                okx, bad, n, (kc, kn, ktwin, knote) = False, "NO VECTORS for this probe in the battery — add them", 0, (0, 1, False, "")
            good = ok and rt and okx and kc == kn and ktwin and name not in TL_TWINS
            R.add(rid, "PASS" if good else "FAIL",
                  "tool=targo-standalone-lean: check PROVED=%s; envelope built (%d bodies); validate ok=%s; 4-format round trip=%s (v%d); %d "
                  "interpreter vectors == Lean semantics %s; %s %s%s" % (
                      proved, len(envd["bodies"]), ok, rt, ver, n, bad, self.oracle_phrase(kc, kn, ktwin, "`targo trust check`"), knote,
                      "; a NEGATIVE CONTROL that now builds is a FAIL" if name in TL_TWINS else ""))
            return
        if kind == "rejected":
            errs = [l for l in chk.splitlines() if l.startswith("error:")]
            head = squash(errs[0] if errs else first_line(chk))
            hit = (not proved) and decl in chk
            verdict = ("REFUSED" if name in TL_TWINS else "GAP") if hit else "FAIL"
            R.add(rid, verdict, "tool=targo-standalone-lean: source REJECTED at elaboration/kernel (no artifact): %s" % head[:260],
                  "producer-gap" if verdict == "GAP" else None, src,
                  sig=re.sub(r"fvar#\d+", "fvar#N", head)[:240] if hit else None)
        else:
            sig = standalone_refusal_signature(bld)
            hit = proved and rcb != 0 and "The whole artifact was refused" in bld and sig is not None and ("`%s` [" % decl) in sig
            verdict = ("REFUSED" if name in TL_TWINS else "GAP") if hit else "FAIL"
            R.add(rid, verdict, "tool=targo-standalone-lean: check PROVED=%s, build refused (all-or-nothing): %s"
                  % (proved, first_line(bld, 3)[:300]), "producer-gap" if verdict == "GAP" else None, src, sig=sig if hit else None)

    # ================================================= GENERAL.<probe>.<decl>: clean -> trust-ir -> trust-cg
    def general_setup(self):
        mains = os.path.join(self.W, "mains")
        if not os.path.exists(os.path.join(self.W, "mains.oracle.json")):
            oracle = gen_mains(mains)
            json.dump(oracle, open(os.path.join(self.W, "mains.oracle.json"), "w"))
        return json.load(open(os.path.join(self.W, "mains.oracle.json")))

    def general_oracle(self, name, decls):
        """Kernel oracle for the C mains' expected values (memoised per probe)."""
        memo = os.path.join(self.W, "general", name + ".oracle.json")
        if os.path.exists(memo):
            d = json.load(open(memo))
            return d["ok"], d["phrase"]
        oracle = self.general_setup()
        stmts = [tuple(st) for d in decls for st in oracle.get(d, [])]
        srcp = os.path.join(self.W, "probes", name + ".lean")
        if not stmts or name == "p12b_width_conversion":
            ok, phrase = False, "no kernel oracle (source does not elaborate)"
        elif self.targo("trust", "check", srcp)[0] == 0:
            c, n, tw, note = self.kernel_oracle([srcp], None, stmts)
            ok, phrase = c == n and tw, self.oracle_phrase(c, n, tw, "`targo trust check` on probes/%s.lean" % name) + (" " + note if note else "")
        else:
            ok, phrase = False, "targo rejects this source, so no kernel certifies the C mains' expected values"
        os.makedirs(os.path.dirname(memo), exist_ok=True)
        json.dump({"ok": ok, "phrase": phrase}, open(memo, "w"))
        return ok, phrase

    def runtime_objs(self):
        rt = self.clean_repo / "crates" / "clean-runtime"
        out = os.path.join(self.W, "runtime")
        os.makedirs(out, exist_ok=True)
        objs = []
        for c in ("clean_runtime", "runtime_extern"):
            o = os.path.join(out, c + ".o")
            if not os.path.exists(o):
                sh([self.t.cc, "-O2", "-std=c11", "-w", "-I", str(rt / "include"), "-c", str(rt / "src" / (c + ".c")), "-o", o])
            objs.append(o)
        return objs

    def shims_for(self, obj, dest):
        """Clean's own PreludeShim C definitions (read-only, from the clean gitlink) for the l_* symbols obj leaves undefined."""
        need = sorted({s[1:] if s.startswith("_") else s for s in sh(["nm", "-u", obj])[1].split() if s.lstrip("_").startswith("l_")})
        src = read(self.clean_repo / "crates" / "clean-cli" / "src" / "native_build.rs")

        def unescape(s):
            s = re.sub(r"\\\n\s*", "", s)
            return s.replace("\\n", "\n").replace('\\"', '"').replace("\\'", "'").replace("\\\\", "\\")
        shims = {}
        for m in re.finditer(r'symbol:\s*"([^"]+)",\s*definition:\s*"((?:[^"\\]|\\.|\\\n)*)"', src, re.S):
            shims.setdefault(m.group(1), unescape(m.group(2)))
        with open(dest, "w") as f:
            f.write('#include <stdio.h>\n#include <string.h>\n#include "clean_runtime.h"\n\n')
            for s in need:
                if s in shims:
                    f.write(shims[s] + "\n")
        return [s for s in need if s not in shims], (lambda sym: sym in shims)

    def linkrun(self, obj, decl, extra=None, suffix=""):
        ldir = os.path.join(self.W, "link")
        os.makedirs(ldir, exist_ok=True)
        exe = os.path.join(ldir, decl + suffix)
        shim = exe + ".shims.c"
        missing, _ = self.shims_for(obj, shim)
        rt = self.clean_repo / "crates" / "clean-runtime"
        cmd = [self.t.cc, "-O2", "-std=c11", "-w", "-I", str(rt / "include"), os.path.join(self.W, "mains", decl + "_main.c"), shim] \
            + ([extra] if extra else []) + [obj] + self.runtime_objs() + ["-lm", "-o", exe]
        code, o, e = sh(cmd)
        undefined = sorted(set(re.findall(r'"_(\w+)", referenced from', e)))
        if code != 0:
            return "link-failed", undefined, ""
        rcr, orun, erun = sh([exe])
        want = read(os.path.join(self.W, "mains", decl + ".expected"))
        if rcr == 0 and orun == want:
            return "match", [], orun.strip().replace("\n", " ")
        return "run-rc=%d" % rcr, [], first_line(orun + erun, 2)

    def crash_controls(self, name, decl, stem):
        """-> (c_backend_status, c_double_consume).  Control: the SAME decl through Clean's own `--emit c` backend
        (no trust-ir, no trust-cg), same main, runtime and shims.  Runs for EVERY crashing decl."""
        clean = self.t.path("clean")
        ldir = os.path.join(self.W, "link")
        rt = self.clean_repo / "crates" / "clean-runtime"
        csrc = stem + ".c"
        code, _, _ = sh([clean, "compile", "probes/%s.lean" % name, "--decl", decl, "--emit", "c", "-o", csrc], cwd=self.W)
        if code != 0 or not os.path.exists(csrc):
            return "c-emit-failed", False
        ctext = open(csrc).read()
        md = re.search(r"l_%s\([^)]*\)\s*\{" % re.escape(decl), ctext)
        body = ctext[md.start():ctext.index("\n}", md.start())] if md else ""
        m_ = re.search(r"l_HMul_hMul\([^;]*?(_x\d+), \1\)", body)
        dbl = bool(m_) and ("clean_inc(%s)" % m_.group(1)) not in body
        shim = os.path.join(ldir, decl + "_cbackend.shims.c")
        self.shims_for(stem + ".o", shim)
        exe = os.path.join(ldir, decl + "_cbackend")
        allc = os.path.join(ldir, decl + "_cbackend_all.c")
        open(allc, "w").write(read(shim) + "\n" + read(str(ROWS_DIR / "ir-tl-general" / "local_shims.c")) + "\n" + ctext)
        rcc, _, _ = sh([self.t.cc, "-O2", "-std=c11", "-w", "-D%s=l_%s" % (decl, decl), "-I", str(rt / "include"),
                        os.path.join(self.W, "mains", decl + "_main.c"), allc] + self.runtime_objs() + ["-lm", "-o", exe])
        if rcc != 0:
            return "c-link-failed", dbl
        rcr, orun, _ = sh([exe])
        return ("match" if rcr == 0 and orun == read(os.path.join(self.W, "mains", decl + ".expected")) else "run-rc=%d" % rcr), dbl

    def general_decl(self, R, name, decl):
        rid = "GENERAL.%s.%s" % (name, decl)
        try:
            clean, tcg = self.t.path("clean"), self.t.path("trust-cg")
        except ToolError as e:
            R.add(rid + ".emit", "FAIL", "general-pipeline judges unavailable (clean with trust-ir-backend + trust-cg from the gitlinks): %s" % e)
            return None
        self.general_setup()
        gdir = os.path.join(self.W, "general")
        os.makedirs(gdir, exist_ok=True)
        stem = os.path.join(gdir, "%s__%s" % (name, decl))
        for ext in (".trust_ir", ".o"):
            if os.path.exists(stem + ext):
                os.remove(stem + ext)
        src = "probes/%s.lean" % name
        rc1, o1, e1 = sh([clean, "compile", src, "--decl", decl, "--emit", "trustir", "-o", stem + ".trust_ir"], cwd=self.W)
        rc2, o2, e2 = sh([clean, "compile", src, "--decl", decl, "--emit", "obj", "-o", stem + ".o"], cwd=self.W,
                         env={"CLEAN_TRUST_CG_BIN": tcg})
        rec = {"decl": decl, "emitted": False, "valid": False, "compiled": False, "shape": None}
        if rc1 != 0 or not os.path.exists(stem + ".trust_ir"):
            msg = first_line(o1 + e1)
            if name == "p12b_width_conversion" and "Unknown identifier: toUInt64" in (o1 + e1):
                R.add(rid + ".emit", "GAP", "tool=clean --emit trustir: %s — UIntN.toUIntM is not in the Clean prelude" % msg[:220],
                      "producer-gap", sig="Unknown identifier: toUInt64")
            else:
                R.add(rid + ".emit", "FAIL", "tool=clean --emit trustir rc=%s: %s" % (rc1, msg[:300]))
            return rec
        rec["emitted"] = True
        R.add(rid + ".emit", "PASS", "tool=clean --emit trustir rc=0, %d-line text module" % sum(1 for _ in open(stem + ".trust_ir")))
        ok, variants, txt = self.validate(stem + ".trust_ir")
        rec["valid"] = ok
        if ok:
            rt, res, ver = self.roundtrip4(stem + ".trust_ir", "text", "%s__%s" % (name, decl))
            R.add(rid + ".validate", "PASS" if rt else "FAIL", "validate_module ok AS EMITTED (no rewrite of any kind); 4-format round trip=%s (v%d)%s"
                  % (rt, ver, "" if rt else " %s" % res))
            if rt:
                mj = os.path.join(self.W, "rt", "%s__%s.json" % (name, decl))
                self.convert(os.path.join(self.W, "rt", "%s__%s.rt0.tmbc" % (name, decl)), "bin", mj, "json")
                try:
                    js = json.load(open(mj))
                    rec["shape"] = dict(enums=len(js.get("enums") or []), structs=len(js.get("structs") or []),
                                        closure_types=len(js.get("closure_types") or []),
                                        obligations=len(js.get("proof_obligations") or []),
                                        body_gates=sorted({json.dumps(f.get("body_gate")) for f in js["functions"] if f.get("blocks")}))
                except (OSError, ValueError):
                    pass
        elif variants == ["ConstTypeMismatch"]:
            R.add(rid + ".validate", "FAIL", "%s signature: the validator refuses the emitted module with ONLY ConstTypeMismatch (closure "
                  "`fndef` constants at a placeholder type). %s closed upstream (WS6.14): this is a REGRESSION, and the module is never "
                  "rewritten into a pass" % (F108, F108))
        else:
            R.add(rid + ".validate", "FAIL", "validator refuses the emitted module: %s %s" % (variants, first_line(txt, 2)[:200]))
        if rc2 == 0 and os.path.exists(stem + ".o"):
            rec["compiled"] = True
            R.add(rid + ".obj", "PASS", "tool=clean --emit obj via trust-cg: %s" % first_line(o2 + e2)[-90:])
            self.general_linkrun(R, name, decl, stem, rid)
        elif "affirmatively ungated" in (o2 + e2) and "body_gate: ungated" in (o2 + e2):
            R.add(rid + ".obj", "GAP", "tool=clean --emit obj: trust-cg refuses the body the PRODUCER stamped `body_gate: ungated` (the v41 "
                  "codegen license, honoured by the consumer): %s" % squash(o2 + e2)[-260:], "producer-gap",
                  sig="codegen license: affirmatively ungated (`body_gate: ungated`, trust-ir v41)")
        else:
            R.add(rid + ".obj", "FAIL", "tool=clean --emit obj rc=%s: %s" % (rc2, first_line(o2 + e2, 2)[:240]))
        json.dump(rec, open(stem + ".record.json", "w"))
        return rec

    def general_linkrun(self, R, name, decl, stem, rid):
        oracle_ok, phrase = self.general_oracle(name, TL_PROBE[name][3])
        st, undef, outp = self.linkrun(stem + ".o", decl)
        if st == "match":
            R.add(rid + ".linkrun", "PASS" if oracle_ok else "FAIL", "linked with Clean's OWN C runtime + PreludeShims and a C main; output == "
                  "Lean semantics: %s; %s" % (outp, phrase))
            return
        if st == "link-failed" and undef and set(undef) <= {"l_UInt64_ofNat", "l_UInt8_ofNat", "l_UInt16_ofNat"}:
            st2, undef2, outp2 = self.linkrun(stem + ".o", decl, str(ROWS_DIR / "ir-tl-general" / "local_shims.c"), "_local")
            if st2 == "match":
                R.add(rid + ".linkrun", "GAP" if oracle_ok else "FAIL", "does NOT link against Clean as shipped: undefined %s (no PreludeShim "
                      "in the clean gitlink's native_build.rs). With TEST-LOCAL analogue shims it links and output == Lean semantics: %s; %s"
                      % (undef, outp2, phrase), "producer-gap" if oracle_ok else None, sig="undefined=%s" % undef if oracle_ok else None)
                return
            st = st2
        if st.startswith("run-rc="):
            # the crash controls run for EVERY crashing decl, whichever link attempt reached the crash (F-120 defect 3)
            cst, dbl = self.crash_controls(name, decl, stem)
            if cst != "match":
                R.add(rid + ".linkrun", "GAP", "the linked executable dies (%s); control: the SAME decl through Clean's own `--emit c` backend "
                      "(no trust-ir/trust-cg), same main/runtime/shims, also fails (%s)%s — an upstream Clean defect, not trust-ir" % (
                          st, cst, "; its C also passes one owned value twice with no clean_inc" if dbl else ""), "producer-gap",
                      sig="crash:%s:c-backend-control=%s:double-consume=%s" % (st, cst, dbl))
            else:
                R.add(rid + ".linkrun", "FAIL", "the linked executable dies (%s) but Clean's own C backend runs the same decl correctly: the "
                      "defect is in the trust-ir lane and is not isolated%s" % (st, " (double consume in the C: %s)" % dbl))
            return
        R.add(rid + ".linkrun", "FAIL", "%s undefined=%s %s" % (st, undef, outp))

    def probe_row(self, R, name):
        self.standalone(R, name)
        for decl in TL_PROBE[name][3]:
            self.general_decl(R, name, decl)

    def general_records(self):
        recs = {}
        for name, _, _, decls in TL_PROBES:
            for decl in decls:
                p = os.path.join(self.W, "general", "%s__%s.record.json" % (name, decl))
                if not os.path.exists(p):
                    self.general_decl(Rows(), name, decl)
                if os.path.exists(p):
                    recs[(name, decl)] = json.load(open(p))
        return recs

    def general_aggregate(self, R):
        try:
            self.t.path("clean")
            tcg = self.t.path("trust-cg")
        except ToolError as e:
            for rid in ("GENERAL.consumer.accepts_head_invalid_modules", "GENERAL.representation", "GENERAL.link.no_shims", "GENERAL.interpret"):
                R.add(rid, "FAIL", "general-pipeline judges unavailable: %s" % e)
            return
        recs = self.general_records()
        emitted = [r for r in recs.values() if r["emitted"]]
        invalid_compiled = [r["decl"] for r in emitted if not r["valid"] and r["compiled"]]
        R.add("GENERAL.consumer.accepts_head_invalid_modules", "PASS" if not invalid_compiled else "GAP",
              "tool=trust-cg (via clean --emit obj) compiled %d module(s) the gitlink trust-ir CLI refuses%s"
              % (len(invalid_compiled), ": %s" % invalid_compiled if invalid_compiled else ""),
              "consumer-gap" if invalid_compiled else None, sig="compiled-invalid=%s" % invalid_compiled if invalid_compiled else None)
        shapes = [r["shape"] for r in emitted if r.get("shape")]
        tot = {k: sum(s[k] for s in shapes) for k in ("enums", "structs", "closure_types", "obligations")}
        gates = sorted({g for s in shapes for g in s["body_gates"]})
        if shapes and tot["enums"] == tot["structs"] == tot["closure_types"] == 0:
            R.add("GENERAL.representation", "GAP", "across %d valid general modules: EnumDefs=0 StructDefs=0 ClosureTys=0 obligations=%d, body "
                  "gates %s. Inductives/structures/closures/Nat/String are spelled as boxed `ptr` + bodyless clean_* runtime calls; Ty::Enum / "
                  "Ty::Closure / Ty::Rc / Ty::Handle / HeapAlloc{CleanHeap} exist and are unused" % (len(shapes), tot["obligations"], gates),
                  "producer-gap", sig="EnumDef=0:StructDef=0:ClosureTy=0:obligations=%d:body_gates=%s" % (tot["obligations"], gates))
        elif shapes:
            R.add("GENERAL.representation", "PASS", "general modules use typed carriers: %s" % tot)
        else:
            R.add("GENERAL.representation", "FAIL", "no valid general module to inspect")
        sobj = os.path.join(self.W, "general", "p04_nat_structural_rec__sumTo.o")
        if os.path.exists(sobj):
            rt = self.clean_repo / "crates" / "clean-runtime"
            code, _, e = sh([self.t.cc, "-w", "-I", str(rt / "include"), os.path.join(self.W, "mains", "sumTo_main.c"), sobj]
                            + self.runtime_objs() + ["-o", os.path.join(self.W, "link", "sumTo_noshim")])
            undef = sorted(set(re.findall(r'"_(\w+)", referenced from', e)))
            R.add("GENERAL.link.no_shims", "REFUSED" if code != 0 and "l_Nat_add" in undef else "FAIL",
                  "negative twin: sumTo.o + Clean runtime WITHOUT the prelude shims is refused by the linker (undefined %s)" % undef,
                  sig="undefined includes l_Nat_add" if code != 0 and "l_Nat_add" in undef else None)
        else:
            R.add("GENERAL.link.no_shims", "GAP", "the negative twin has no object to link: clean --emit obj produced no sumTo.o (see "
                  "GENERAL.p04_nat_structural_rec.sumTo.obj)", "producer-gap", sig="no sumTo.o")
        target = os.path.join(self.W, "general", "p06_inductive_match__areaOfRect.trust_ir")
        if recs.get(("p06_inductive_match", "areaOfRect"), {}).get("valid"):
            drv = os.path.join(self.W, "gen_interp_driver.trust_ir")
            open(drv, "w").write('; TrustIr text format v1\nmodule "parta-lean-general-driver"\n\nfuncty.0 = (u64, u64) -> (u64)\n\n'
                                 'functy.1 = () -> (u64)\n\nfn @areaOfRect(functy.0) {\n    ; #producer: clean\n}\n\nrustcc fn @program(functy.1) '
                                 '{\n    ; #producer: trust-ir\nbb0:\n    %0 = const u64 6\n    %1 = const u64 7\n    %2 = call @func.0(%0, %1)\n'
                                 '    ret %2\n}\n')
            code, o, e = sh([self.t.cli, "run", "--validate", target, drv])
            if code == 0 and (o.strip().splitlines() or [""])[-1].strip() == "42":
                R.add("GENERAL.interpret", "PASS", "the reference interpreter executes the valid areaOfRect module: 6*7 = 42")
            elif code != 0 and "non-executable vararg signature" in (o + e):
                R.add("GENERAL.interpret", "GAP", "tool=trust-ir run: the VALID areaOfRect module links but cannot execute: \"%s\" — the "
                      "interpreter has no host-call hook for the Clean runtime" % first_line(e.split("well-formed")[-1])[:140],
                      "consumer-gap", sig="non-executable vararg signature")
            else:
                R.add("GENERAL.interpret", "FAIL", "rc=%s: %s" % (code, first_line(o + e, 2)[:240]))
        else:
            R.add("GENERAL.interpret", "FAIL", "areaOfRect's general module is not valid as emitted")


def partalean_row(row, pl, R):
    if row == "ir-tl-library":
        pl.library(R)
    elif row == "ir-tl-format_home":
        pl.format_homes(R)
    elif row == "ir-tl-general":
        pl.general_aggregate(R)
    else:
        name = next(n for n, r in TL_ROW.items() if r == row)
        pl.probe_row(R, name)


# ============================================================ rows, pins, and the audit corpus
PARTA_ROWS = [r for _, r, _ in PARTA_PROBES] + [
    "ir-ta-dep", "ir-ta-app", "ir-ta-lean_oracle", "ir-ta-neg", "ir-ta-lean", "ir-ta-attrib", "ir-ta-f1",
    "ir-ta-island_mutant", "ir-ta-app_max", "ir-ta-app_exec", "ir-ta-format", "ir-ta-surface"]
PARTALEAN_ROWS = ["ir-tl-library"] + [TL_ROW[p[0]] for p in TL_PROBES] + ["ir-tl-format_home", "ir-tl-general"]
ALL_ROWS = PARTA_ROWS + PARTALEAN_ROWS

# Audit rows deliberately NOT ported, each with its reason.  audit-check requires every audit row to be either
# pinned by exactly one row or matched here, so nothing is dropped silently.
NOT_PORTED = [
    (r"^a\..+\.(repair_experiment|upstream_body_experiment)$",
     "attribution experiment that REWROTE the producer's module (repair.py: re-typed variadic placeholders / hand-wrote a body); "
     "the judge contains no module-rewriting code (WS8.8 ruling). A FORMAT attribution: owned by the trust-ir conformance port"),
    (r"^a\..+\.carry_experiment(\.text)?$",
     "attribution experiment that built a FunctionSummary INTO the producer's module (carry.py); not a producer measurement and no "
     "module-rewriting code is ported (WS8.8 ruling). The format half (summary carriage, text leg) is trust-ir conformance (WS8.6/WS8.7)"),
]


def not_ported_reason(fid):
    return next((why for rx, why in NOT_PORTED if re.match(rx, fid)), None)


# Audit rows that this judge DOES port and WILL pin — but only on a build that
# ships the optional component they measure. They are not NOT_PORTED (that says
# "deliberately not measured, and pinning one is an error") and they cannot be
# pinned unconditionally either, because `compare` fails a pin the run did not
# measure. Without a third answer the coverage gate is unsatisfiable in BOTH
# directions at once, which is what left these four rows reported as uncovered:
#
#   NOT_PORTED  -> on a backend-PRESENT build the judge emits them, the row pins
#                  them, and `pin_problems` then says "pinned although NOT_PORTED
#                  excludes it".
#   pinned      -> on a backend-ABSENT build the judge returns early after the
#                  single collapsed `a.f1.codegen` GAP, and `compare` says
#                  "pinned <v> but not measured by this row".
#
# So: covered when absent, pinnable when present. `pin_problems` deliberately
# does NOT consult this table — a conditional row MAY be pinned, and on a build
# that measures it, it MUST be.
CONDITIONAL = [
    (r"^a\.f1\.codegen\.",
     "reachable only on a build that ships the OPT-IN trust-cg codegen backend. `trust-cg` is feature-gated and "
     "not in a default build (CLAUDE.md, Backends), so on a default build the F1 hook's backend probe answers "
     "`absent` and `f1_rows` returns after the single collapsed `a.f1.codegen` GAP — these four downstream rows "
     "are never emitted. The audit corpus recorded them from a build where the backend WAS present. They stay "
     "ported and pinnable: enable the backend and the judge emits them, the row must pin them, and this entry "
     "stops applying because the pin covers them."),
]


def conditional_reason(fid):
    """Why an audit row can be uncovered on THIS build without being a gap in the
    port. Coverage only; never an excuse for a pin that IS measured."""
    return next((why for rx, why in CONDITIONAL if re.match(rx, fid)), None)


def normalize_verdict(v, detail=""):
    """Audit vocabulary -> ratchet vocabulary: (verdict, class)."""
    if v in ("PRODUCER-GAP", "CONSUMER-GAP"):
        return "GAP", v.lower()
    if v == "GAP":
        m = re.match(r"\[([a-z-]+)\]", detail or "")
        return "GAP", m.group(1) if m else "format-gap"
    return v, None


def load_audit(part):
    path = AUDIT_DIR / AUDIT_FILES[part]
    out = {}
    for line in read(path).splitlines():
        m = re.match(r"^FEATURE (\S+) (\S+) ?(.*)$", line)
        if m:
            out[m.group(1)] = normalize_verdict(m.group(2), m.group(3))
    return out


def row_part(row):
    return "parta" if row in PARTA_ROWS else "parta-lean"


def expected_path(row):
    return ROWS_DIR / row / "expected.json"


def load_expected(row):
    try:
        doc = json.loads(expected_path(row).read_text())
    except (OSError, ValueError):
        return None
    return doc


def compare(rows, expected):
    """-> list of (id, status, text).  OK: the pin holds.  FLIPPED: the verdict moved (a GAP that turned PASS, a
    PASS that regressed to a GAP) - red until expected.json is updated in the same commit.  FAIL: everything
    else - a measured FAIL (never pinnable), an unpinned or unmeasured ratchet, and a GAP / REFUSED whose class
    or named signature changed (a refusal that changes class is a FAIL, never "the same gap").

    SKIP is the third answer the CONDITIONAL table's own comment asks for.  A pin may carry
    `"measured_only_when": "<condition>"`, naming the build-matrix condition under which this ratchet is
    measured at all.  The condition is free text for a reader; the judge only uses its PRESENCE.
    Such a pin, unmeasured, is SKIPped instead of failing.  Without it the coverage gate is unsatisfiable in
    both directions at once - which is exactly what `ir-ta-f1` hit: pin the collapsed `a.f1.codegen` GAP and a
    build that SHIPS trust-cg fails four "measured but no pin" plus one "pinned but not measured"; pin the four
    downstream rows instead and a DEFAULT build (no trust-cg) fails them all as unmeasured.  Both builds are
    legitimate, so both sets are pinned and each build skips the set it cannot reach.

    THREE THINGS KEEP THIS FROM BEING A HOLE.  A measured ratchet with no pin is still a FAIL, so the marker
    cannot smuggle in an unaudited result - it only ever excuses ABSENCE.  The marker is per pin and written by
    hand, never by `--write-expected`, so a row cannot acquire one by being re-pinned.  And a row that measured
    NOTHING is red however many pins it skips (see `green`), so "skip everything" is not a way to pass."""
    pins = (expected or {}).get("ratchets") or {}
    out, seen = [], set()
    for r in rows:
        fid = r["id"]
        seen.add(fid)
        p = pins.get(fid)
        if r["verdict"] == "FAIL":
            out.append((fid, "FAIL", "measured FAIL: %s" % r["detail"][:400]))
        elif p is None:
            out.append((fid, "FAIL", "measured %s but no pin in expected.json" % r["verdict"]))
        elif p.get("verdict") != r["verdict"]:
            out.append((fid, "FLIPPED", "pinned %s, measured %s%s — update expected.json in the same commit: %s" % (
                p.get("verdict"), r["verdict"], " [%s]" % r.get("signature") if r.get("signature") else "", r["detail"][:300])))
        elif r["verdict"] in ("GAP", "REFUSED") and (p.get("signature") != r.get("signature") or p.get("class") != r.get("class")):
            out.append((fid, "FAIL", "%s changed its named signature: pinned [%s] %r, measured [%s] %r" % (
                r["verdict"], p.get("class"), p.get("signature"), r.get("class"), r.get("signature"))))
        else:
            out.append((fid, "OK", r["verdict"]))
    for fid in sorted(set(pins) - seen):
        p = pins[fid]
        condition = p.get("measured_only_when")
        if condition and rows:
            out.append((fid, "SKIP", "pinned %s; not measured on this build — %s"
                        % (p.get("verdict"), condition)))
            continue
        out.append((fid, "FAIL", "pinned %s but not measured by this row" % p.get("verdict")))
    return out


def pin_for(r, old, audit):
    pin = {"verdict": r["verdict"]}
    if r.get("class"):
        pin["class"] = r["class"]
    if r.get("signature"):
        pin["signature"] = r["signature"]
    a = audit.get(r["id"])
    pin["audit"] = a[0] if a else None
    moved_from_audit = a is None or a[0] != r["verdict"] or (r["verdict"] == "GAP" and a[1] != r.get("class"))
    same_as_old = old and all(old.get(k) == pin.get(k) for k in ("verdict", "class", "signature"))
    if same_as_old:
        for k in ("moved", "note", "finding"):
            if old.get(k):
                pin[k] = old[k]
    # `measured_only_when` survives a re-pin whatever else moved: it names the build-matrix
    # condition under which this ratchet is measured at all, which is a fact about the build
    # matrix, not about the verdict. Losing it on a re-pin would silently make the row red on
    # the other build. It is only ever written by hand — nothing here can add one.
    if old and old.get("measured_only_when"):
        pin["measured_only_when"] = old["measured_only_when"]
    if moved_from_audit and not pin.get("moved"):
        pin["moved"] = "UNREVIEWED: audit %s, measured %s — replace with the named reason" % (a[0] if a else "absent", r["verdict"])
    if not moved_from_audit:
        pin.pop("moved", None)
    return pin


def write_expected(row, rows, identities):
    old = (load_expected(row) or {}).get("ratchets") or {}
    audit = load_audit(row_part(row))
    fails = [r["id"] for r in rows if r["verdict"] == "FAIL"]
    ratchets = {r["id"]: pin_for(r, old.get(r["id"]), audit) for r in rows if r["verdict"] != "FAIL"}
    # a FAIL is never pinned, and it never ERASES the pin it failed against: the row stays red on that pin
    ratchets.update({fid: old[fid] for fid in fails if fid in old})
    doc = {"schema": EXPECTED_SCHEMA, "row": row,
           "measured_on": {k: (identities.get(k) or "").split(" @ ")[0] for k in ("trustc", "trust-ir", "clean", "trust-cg")},
           "ratchets": dict(sorted(ratchets.items()))}
    expected_path(row).write_text(json.dumps(doc, indent=1, ensure_ascii=False) + "\n")
    return fails


def measure_row(row, work, tools):
    R = Rows()
    try:
        if row in PARTA_ROWS:
            parta_row(row, PartA(work, tools), R)
        elif row in PARTALEAN_ROWS:
            partalean_row(row, PartALean(work, tools), R)
        else:
            raise KeyError(row)
    except ToolError as e:
        R.add("%s.harness" % row, "FAIL", "judge tool unavailable: %s" % e)
    return R.rows


def cmd_run(args):
    if args.row not in ALL_ROWS:
        print("unknown row %r (see `list`)" % args.row, file=sys.stderr)
        return 2
    work = os.path.abspath(args.work)
    if re.match(r"^/(private/)?tmp/", work):
        print("--work must not be under /tmp: `targo trust` refuses world-writable path components", file=sys.stderr)
        return 2
    os.makedirs(work, exist_ok=True)
    for label, path in (("--trustc", args.trustc), ("--targo", args.targo)):
        if not (os.path.isfile(path) and os.access(path, os.X_OK)):
            print("IR-ROW %s FAIL %s %s is not an executable file — nothing was measured" % (args.row, label, path))
            return 1
    try:
        tools = Tools(args.tools_dir, args.trustc, args.targo)
    except ToolError as e:
        print("IR-ROW %s FAIL judge unavailable: %s" % (args.row, e))
        return 1
    ids = tools.identities()
    before = {p: sha256_file(p) for p in (args.trustc, args.targo)}
    rows = measure_row(args.row, work, tools)
    after = {p: sha256_file(p) if os.path.isfile(p) else None for p in before}
    if after != before:
        # a shared build tree rebuilt under the run: the rows measure two compilers (or none)
        print("IR-ROW %s FAIL the compiler under test changed or vanished DURING the run (%s) — nothing is judged or pinned"
              % (args.row, sorted(p for p in before if after[p] != before[p])))
        return 1
    rep_dir = os.path.join(work, "reports")
    os.makedirs(rep_dir, exist_ok=True)
    if args.write_expected:
        fails = write_expected(args.row, rows, ids)
        print("wrote %s (%d pins)%s" % (expected_path(args.row), len(rows) - len(fails),
                                        "; NOT pinnable (FAIL): %s" % fails if fails else ""))
    results = compare(rows, load_expected(args.row))
    json.dump({"schema": REPORT_SCHEMA, "row": args.row, "identities": ids, "rows": rows,
               "judge_sha256": sha256_file(Path(__file__).resolve()),
               "results": [dict(id=i, status=s, text=t) for i, s, t in results]},
              open(os.path.join(rep_dir, args.row + ".json"), "w"), indent=1)
    for i, s, t in results:
        print("RATCHET %s %s %s" % (i, s, t))
    n = {k: sum(1 for _, s, _ in results if s == k) for k in ("OK", "FLIPPED", "FAIL", "SKIP")}
    verdicts = {v: sum(1 for r in rows if r["verdict"] == v) for v in VERDICTS}
    # `bool(rows)`, not just `bool(results)`: a SKIP is a result, so without this a row
    # whose every pin is optional and whose judge measured nothing would read GREEN.
    green = n["FLIPPED"] == n["FAIL"] == 0 and bool(results) and bool(rows)
    print("IR-ROW %s %s ok=%d flipped=%d fail=%d%s (PASS=%d GAP=%d REFUSED=%d)" % (
        args.row, "GREEN" if green else "RED", n["OK"], n["FLIPPED"], n["FAIL"],
        " skip=%d" % n["SKIP"] if n["SKIP"] else "",
        verdicts["PASS"], verdicts["GAP"], verdicts["REFUSED"]))
    return 0 if green else 1


def pin_problems(fid, pin, audit):
    """What is wrong with ONE pin, judged against the audit corpus of its part."""
    problems = []
    v = pin.get("verdict")
    if v not in ("PASS", "GAP", "REFUSED"):
        problems.append("verdict %r is not pinnable" % v)
    if v == "GAP" and (pin.get("class") not in GAP_CLASSES or not pin.get("signature")):
        problems.append("a GAP pin needs a class and its named signature")
    if v == "REFUSED" and not pin.get("signature"):
        problems.append("a REFUSED pin needs its named signature")
    a = audit.get(fid)
    want_audit = a[0] if a else None
    if pin.get("audit") != want_audit:
        problems.append("`audit` says %r but the audit corpus says %r" % (pin.get("audit"), want_audit))
    moved = a is None or a[0] != v or (v == "GAP" and a[1] != pin.get("class"))
    reason = (pin.get("moved") or "").strip()
    if moved and (not reason or reason.startswith("UNREVIEWED")):
        problems.append("moved from the audit (%s -> %s) without a named reason" % (want_audit, v))
    if not moved and reason:
        problems.append("carries a `moved` reason but did not move from the audit")
    if not_ported_reason(fid):
        problems.append("pinned although NOT_PORTED excludes it")
    return problems


def audit_problems():
    """Static checks over every row's expected.json against the audit corpus (no toolchain)."""
    problems = []
    audits = {part: load_audit(part) for part in AUDIT_FILES}
    for part, a in audits.items():
        if not a:
            problems.append("audit file for %s is missing or empty: %s" % (part, AUDIT_DIR / AUDIT_FILES[part]))
    owner = {}
    for row in ALL_ROWS:
        doc = load_expected(row)
        if doc is None:
            problems.append("%s: expected.json missing or not JSON" % row)
            continue
        if doc.get("schema") != EXPECTED_SCHEMA or doc.get("row") != row:
            problems.append("%s: expected.json header must be schema=%s row=%s" % (row, EXPECTED_SCHEMA, row))
        audit = audits[row_part(row)]
        for fid, pin in (doc.get("ratchets") or {}).items():
            where = "%s: %s" % (row, fid)
            if fid in owner:
                problems.append("%s: also pinned by %s" % (where, owner[fid]))
            owner[fid] = row
            problems.extend("%s: %s" % (where, p) for p in pin_problems(fid, pin, audit))
    for part, a in audits.items():
        for fid in sorted(a):
            if fid not in owner and not not_ported_reason(fid) and not conditional_reason(fid):
                problems.append("audit row %s (%s) is neither pinned by any row, NOT_PORTED, nor CONDITIONAL with a reason"
                                % (fid, part))
    for row in ALL_ROWS:
        if not (ROWS_DIR / row).is_dir():
            problems.append("%s: row directory missing" % row)
    on_disk = sorted(p.name for p in ROWS_DIR.glob("ir-t*") if p.is_dir())
    for extra in sorted(set(on_disk) - set(ALL_ROWS)):
        problems.append("%s: a row directory the judge does not know" % extra)
    return problems


def cmd_audit_check(_args):
    problems = audit_problems()
    for p in problems:
        print("AUDIT %s" % p)
    total = sum(len((load_expected(r) or {}).get("ratchets") or {}) for r in ALL_ROWS)
    print("audit-check: %d rows, %d pins, %d problem(s)" % (len(ALL_ROWS), total, len(problems)))
    return 1 if problems else 0


# ============================================================ replay (the positive test of the port)
def replay_parta(report):
    """Re-judge an ARCHIVED Part A run (analyze.py's report.json) with this judge: the rows whose inputs the
    archive keeps (native / emit / validate / roundtrip / exec / twins / surface / format / attrib / coverage).
    `.carried` / `.obligations` need the module JSON, which the archive does not keep."""
    R = Rows()
    units = {}
    for name, info in (report.get("units") or {}).items():
        info = copy.deepcopy(info)
        mod = info.get("module")
        if mod:
            mod["_json"] = None
            cen = mod.get("census")
            if cen is not None and "typedef_names_outside_text_charset" not in cen:
                cen["typedef_names_outside_text_charset"] = list((mod.get("rename") or {}).get("typedef_names_outside_text_alphabet") or [])
        units[name] = info
    for fid, probe, _ in sorted(blocks() + EXTRA_PROBES, key=lambda x: x[1]):
        info = units.get(probe)
        if info is None:
            continue
        oracle = judge_native(R, "a." + fid, info)
        judge_module(R, "a." + fid, info, oracle)
    for name in ("dep", "app", "app_max", "app_exec"):
        info = units.get(name)
        if info is None:
            continue
        if name == "dep":
            judge_module(R, "a.unit.dep", info, None, want_exec=False)
            continue
        oracle = judge_native(R, "a.unit." + name, info)
        judge_module(R, "a.unit." + name, info, oracle)
        if name in ("app_max", "app_exec"):
            allf = [f for f, _, _ in blocks()]
            inc = info.get("features") or []
            excluded = [f for f in allf if f not in inc]
            R.add("a.unit.%s.coverage" % name, "PASS" if not excluded else "GAP", "replayed", None if not excluded else
                  ("refused" if name == "app_max" else "producer-gap"), sig="coverage:excluded=%s" % excluded if excluded else None)
    surface(R, units)
    format_rows(R, units)
    if report.get("attrib"):
        p12 = (units.get("p12b_lean_bool_connective") or {}).get("native", {})
        nat = next((e.get("stdout") for e in p12.values() if e.get("build_rc") == 0 and e.get("exec_rc") == 0), None)
        at = dict(report["attrib"])
        at.setdefault("unop_ok", False)
        attrib_rows(R, at, nat)
    return R.rows


def parse_features(path):
    out = {}
    for line in read(path).splitlines():
        m = re.match(r"^FEATURE (\S+) (\S+) ?(.*)$", line)
        if m:
            out[m.group(1)] = normalize_verdict(m.group(2), m.group(3))
    return out


def replay_mismatches(report, features):
    """-> (replayed count, [mismatch lines]).  Verdict AND class must reproduce the archived judgment."""
    rows = replay_parta(report)
    bad = []
    for r in rows:
        a = features.get(r["id"])
        if a is None:
            bad.append("%s: replayed %s but the archive has no such row" % (r["id"], r["verdict"]))
        elif a[0] != r["verdict"] or (r["verdict"] == "GAP" and a[1] != r.get("class")):
            bad.append("%s: archive %s/%s, replay %s/%s — %s" % (r["id"], a[0], a[1], r["verdict"], r.get("class"), r["detail"][:200]))
    return len(rows), bad


def cmd_replay(args):
    report = json.load(open(args.report))
    n, bad = replay_mismatches(report, parse_features(args.features))
    for b in bad:
        print("REPLAY %s" % b)
    print("replay: %d rows re-judged, %d mismatch(es)" % (n, len(bad)))
    return 1 if bad or n == 0 else 0


# ============================================================ evidence (the completion-gate artifact)
EVIDENCE_SCHEMA = "trust.two-language.producer-ratchets.evidence/v1"


def ratchet_gates(fid):
    """The TRUST-TWO-LANGUAGE-100 goals (docs/TWO_LANGUAGE_100_PERCENT_GOAL.md) a ratchet is evidence FOR.
    A tag only says which gate checker may read the row; it never makes a row count as affirmative, and a
    GAP / REFUSED row is evidence that the conjunct is NOT met.  Rules, first match wins per family:
      a.rust.*                           G1 (Rust input) + G3 (producer totality)
      a.lean.*, STANDALONE, LEAN, GENERAL, FORMAT_HOME   G2 (Lean input) + G3
      a.two_lang.*, a.unit.*, a.f1.*     G5 (one linked two-language program) + G3
      a.island_mutant.*                  G5 + G3 (the control behind every G5 differential, WS8.8)
      a.format.*                         G3
      a.surface.*, a.neg.*               G6 (obligation completeness / proof authority)
    and any `.carried` / `.obligations` ratchet additionally G6."""
    head = fid.split(".", 2)
    fam = head[0] if not fid.startswith("a.") else ".".join(head[:2])
    gates = {"a.rust": ["G1", "G3"], "a.lean": ["G2", "G3"], "a.two_lang": ["G3", "G5"], "a.unit": ["G3", "G5"],
             "a.f1": ["G3", "G5"], "a.island_mutant": ["G3", "G5"], "a.format": ["G3"], "a.surface": ["G6"], "a.neg": ["G6"],
             "STANDALONE": ["G2", "G3"], "LEAN": ["G2", "G3"], "GENERAL": ["G2", "G3"],
             "FORMAT_HOME": ["G2", "G3"]}.get(fam, [])
    if re.search(r"\.(carried|obligations)(\.|$)", fid) and "G6" not in gates:
        gates = gates + ["G6"]
    return sorted(gates)


def build_evidence(work):
    """Aggregate the per-row reports ONE battery run wrote under WORK/reports into one content-bound artifact.
    Every row of ALL_ROWS must have a report from this run; a missing row is recorded (and makes the artifact
    `complete: false`), never filled from a pin. Every report must carry the same tool identities and name
    THIS judge; a work dir mixing two compilers or two judges is recorded as `skew` (complete=false,
    green=false) rather than attributed to the first report's identities."""
    rep_dir = Path(work) / "reports"
    judge = sha256_file(Path(__file__).resolve())
    rows, missing, identities, skew = [], [], None, []
    for row in ALL_ROWS:
        rp = rep_dir / (row + ".json")
        try:
            rep = json.loads(rp.read_text())
        except (OSError, ValueError):
            missing.append(row)
            continue
        ep = expected_path(row)
        results = rep.get("results") or []
        status = {k: sum(1 for x in results if x.get("status") == k) for k in ("OK", "FLIPPED", "FAIL")}
        measured = {r["id"]: r for r in rep.get("rows") or []}
        # ONE run means one judge and one set of tool identities: a work dir that mixes reports from two
        # compilers (or two judges) is not evidence of either. The first report sets them; every other
        # report must agree, and a report that does not name its judge is a report this judge did not write.
        ids = rep.get("identities") or {}
        if identities is None:
            identities = ids
        if ids != identities:
            skew.append("%s: identities differ from %s's" % (row, rows[0]["row"] if rows else "?"))
        if rep.get("judge_sha256") != judge:
            skew.append("%s: written by judge %s, this judge is %s" % (row, rep.get("judge_sha256"), judge))
        rows.append({
            "row": row,
            "green": bool(results) and status["FLIPPED"] == status["FAIL"] == 0,
            "status_counts": status,
            "report_sha256": sha256_file(rp),
            "expected_sha256": sha256_file(ep) if ep.is_file() else None,
            "ratchets": [{"id": x["id"], "status": x["status"],
                          "verdict": (measured.get(x["id"]) or {}).get("verdict"),
                          "class": (measured.get(x["id"]) or {}).get("class"),
                          "signature": (measured.get(x["id"]) or {}).get("signature"),
                          "gates": ratchet_gates(x["id"])} for x in results],
        })
    by_gate = {}
    for r in rows:
        for x in r["ratchets"]:
            for g in x["gates"]:
                c = by_gate.setdefault(g, {"PASS": 0, "GAP": 0, "REFUSED": 0, "FAIL": 0, "unmeasured": 0})
                c[x["verdict"] if x["verdict"] in c else "unmeasured"] += 1
    return {"schema": EVIDENCE_SCHEMA, "judge_sha256": judge,
            "identities": identities or {}, "complete": not missing and not skew, "missing_rows": missing,
            "skew": skew, "green": not missing and not skew and all(r["green"] for r in rows),
            "by_gate": dict(sorted(by_gate.items())), "rows": rows}


def cmd_evidence(args):
    doc = build_evidence(args.work)
    text = json.dumps(doc, indent=1, ensure_ascii=False) + "\n"
    Path(args.out).write_text(text)
    for line in doc["skew"]:
        print("EVIDENCE-SKEW %s" % line)
    print("EVIDENCE %s rows=%d missing=%d skew=%d green=%s sha256:%s" % (
        args.out, len(doc["rows"]), len(doc["missing_rows"]), len(doc["skew"]), doc["green"], sha256_file(args.out)))
    return 0 if doc["complete"] else 1


# ============================================================ tools / list / main
def cmd_tools(args):
    ok = True
    for name in TOOL_SPECS:
        try:
            prov = build_tool(name, args.tools_dir, args.builder) if args.build else resolve_tool(name, args.tools_dir)
            print("TOOL %s %s@%s sha256:%s %s" % (name, prov["submodule"], prov["gitlink"][:12], prov["sha256"][:16], prov["binary"]))
        except ToolError as e:
            ok = False
            print("TOOL %s UNRESOLVED %s" % (name, e))
    return 0 if ok else 1


def cmd_list(_args):
    for r in ALL_ROWS:
        print(r)
    return 0


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest="cmd", required=True)
    t = sub.add_parser("tools", help="build (--build) or resolve the gitlink-built judges")
    t.add_argument("--build", action="store_true")
    t.add_argument("--builder", default=os.environ.get("TRUST_IR_RATCHET_BUILDER", "targo"))
    t.add_argument("--tools-dir", default=str(DEFAULT_TOOLS_DIR))
    sub.add_parser("list", help="row names in battery order")
    r = sub.add_parser("run", help="measure one row and hold it to its pins")
    r.add_argument("--row", required=True)
    r.add_argument("--work", required=True)
    r.add_argument("--trustc", required=True)
    r.add_argument("--targo", required=True)
    r.add_argument("--tools-dir", default=str(DEFAULT_TOOLS_DIR))
    r.add_argument("--write-expected", action="store_true",
                   help="re-pin the row from this measurement (moved pins are marked UNREVIEWED until a reason is written)")
    sub.add_parser("audit-check", help="static: every pin against the audit corpus")
    p = sub.add_parser("replay", help="re-judge an archived Part A report.json and compare with its features.txt")
    p.add_argument("report")
    p.add_argument("features")
    e = sub.add_parser("evidence", help="aggregate one battery run's row reports into the completion-gate artifact")
    e.add_argument("--work", required=True)
    e.add_argument("--out", required=True)
    args = ap.parse_args(argv)
    return {"tools": cmd_tools, "list": cmd_list, "run": cmd_run, "audit-check": cmd_audit_check, "replay": cmd_replay,
            "evidence": cmd_evidence}[args.cmd](args)


if __name__ == "__main__":
    sys.exit(main())
