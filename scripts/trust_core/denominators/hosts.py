#!/usr/bin/env python3
"""E0.12 denominator `hosts`: D0.11, the probe-host roster.

Design of record: docs/design/2026-09-16-trust-core-architecture.md, §5.2 Stage 0.5 ("D0.11, the
probe-host roster: which Apple silicon generations, Linux AArch64 cores, Intel and AMD hosts are
available, and which must be acquired for E1.6.5 and E2.7.3", exit E0.12 "All published, each with
its predicate: 0 denominators without one"). What consumes it:

  E1.6.5  "Silicon probes on the roster (at least two Apple silicon generations and one Linux AArch64
          core, D0.11)" refute or leave `Cfg_t` standing for aarch64-apple-darwin and
          aarch64-unknown-linux-gnu.
  E2.7.3  "Silicon differential on at least one Intel and one AMD host from the roster, plus Rosetta
          and the X86ISA emulator"; D-8(h) says the roster "must add native Intel and AMD hosts
          before E2.7.3 can pass".
  also    E2.1.3 (hardware float differentials "on the roster's AArch64 hosts"; "binary128, which no
          roster host implements in hardware [K]", Appendix B's row verified by D0.11) and M0.4
          (litmus runs "on the roster's hosts").

A host is CONFIRMED only by this script's probe run ON that host (`--probe`). Nothing else confirms
one: a host that the pinned trees merely mention is RECORDED, and its row says
"blocked: unavailable until a probe runs on it" (fail-closed: a recorded host is not a host the
project has). Three parts, each a predicate:

  PROBE     (runs on any host, Python 3.9+, stdlib only; `--probe` prints it as JSON)
            macOS: sysctl (hw.model, machdep.cpu.brand_string, hw.cpufamily, core counts by
            performance level, hw.memsize, every hw.optional key), the IOPlatformUUID (recorded
            only as a salted sha256), whether `/usr/bin/arch -x86_64 /usr/bin/true` executes
            (Rosetta 2), `acl2` on PATH with $ACL2_SYSTEM_BOOKS/projects/x86isa (the X86ISA
            emulator). Linux: /proc/cpuinfo (vendor_id, model name, CPU implementer/part per
            processor, flags), /proc/meminfo, /etc/os-release, a salted sha256 of /etc/machine-id.
            The host's classes follow from the facts by the CLASS predicates below.
  RECORDS   every host identity the pinned trees record: the superproject at --rev outside the
            upstream directories (compiler/ library/ src/ tests/ vendor/), and each first-party
            sibling at the commit its gitlink names at --rev, read from git objects (no worktree).
            --rev defaults to HEAD; scripts/trust_core/denominators.py passes the record's
            measured_at_commit.
            `git grep -E GREP` finds candidate lines; the EXTRACTORS turn each line into canonical
            identities (an Apple brand string, a Mac model identifier, an x86 model, an Arm core or
            SoC name, a host name from a `host`/`host_name`/`hostname` field, a `Host: `-quoted
            name, or a fleet-style host name). Every occurrence is classified by the first RULE that
            matches (repo, path, identity): either a roster row or a named not-a-host category. An
            occurrence no rule classifies, or a rule naming a row that is not defined, is a finding
            (exit 1): the scan is fail-closed, so a newly recorded host cannot pass unseen.
  ROSTER    per required class: the members confirmed by probes, the minimum the design states,
            the shortfall, and the recorded rows that would close it once a probe runs on
            them. Each FACT cited for a recorded row is re-found, verbatim, in its file at
            the pin (a missing quote is a finding).

Usage (measurement needs Python 3.11+ for common.py and tomllib; --probe needs 3.9+ only):
    python3.14 scripts/trust_core/denominators/hosts.py            # measure and print
    python3.14 scripts/trust_core/denominators/hosts.py --write    # rewrite the TOML record
    python3.14 scripts/trust_core/denominators/hosts.py --check    # the TOML equals a re-measurement
    python3 hosts.py --probe > probe.json                          # on any host (copy the file alone)
    python3.14 scripts/trust_core/denominators/hosts.py --write --with-probe probe.json
                                                                   # add that host as CONFIRMED

--check re-probes this host only when the record holds a probe of this machine (same salted machine
digest); any other host's probe is carried from the record, because it can be measured only there.
On this machine it compares the ROSTER FACTS (ROSTER_FACTS: every probe fact a class predicate, a row
or a design reading reads, such as the CPU brand, hw.memsize, whether Rosetta executes, X86ISA) with the
recorded probe's and fails when one changed; the rest of the probe (OS version, kernel release, feature
flags no predicate reads, tools on PATH) is a dated observation carried from the record and reported,
not compared, so an OS update is not drift. It ignores measured_at_commit and each checkout_head
(informational).

Exit codes: 0 measured (rows may be `blocked`, with the reason) and, with --check, the record matches;
1 a finding (an unclassified identity, a missing fact quote, a design quote not found) or a record
mismatch; 2 the superproject or a pinned sibling cannot be read.

Author: Andrew Yates <andrewyates.name@gmail.com>
Copyright 2026 Andrew Yates | License: Apache-2.0 OR MIT
"""

from __future__ import annotations

import os as _floor_os
import shutil as _floor_shutil
import sys as _floor_sys

# Trust: python floor (scripts/tests/python_floor_test.py). This file needs tomllib (3.11+) and plain
# `python3` is 3.9 on macOS CommandLineTools, so an old interpreter re-execs here, before any import
# that needs 3.11 runs.
if __name__ == "__main__" and _floor_sys.version_info < (3, 11):
    for _floor_candidate in ("python3.14", "python3.13", "python3.12", "python3.11"):
        _floor_path = _floor_shutil.which(_floor_candidate)
        if _floor_path:
            _floor_argv = [_floor_path, _floor_os.path.abspath(__file__), *_floor_sys.argv[1:]]
            _floor_os.execv(_floor_path, _floor_argv)
    _floor_sys.exit("hosts.py requires Python 3.11+ (tomllib); none found on PATH")

import argparse
import hashlib
import json
import os
import platform
import re
import shutil
import subprocess
import sys
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

KEY = "hosts"
SCHEMA = "trust.core.denominator.v1"
PROBE_SCHEMA = "trust.core.host-probe.v1"
RECORD_REL = f"docs/trust-core/denominators/{KEY}.toml"
SCRIPT_REL = f"scripts/trust_core/denominators/{KEY}.py"
DESIGN_REL = "docs/design/2026-09-16-trust-core-architecture.md"
FIRST_PARTY = ("ay", "clean", "ny", "trust-cg", "trust-ir", "trust-mc", "trust-vc", "trust-wp", "ty")
UPSTREAM_EXCLUDES = ("compiler", "library", "src", "tests", "vendor")
SALT = "trust-core-hosts-v1:"
BLOCKED = "blocked: unavailable until a probe runs on it"
CLASS_BLOCKED = {
    "rosetta-2": "blocked: Rosetta 2 is not installed on the confirmed Apple silicon host; installing it accepts Apple's "
                 "license, which is the owner's act (or a probe on another Apple silicon host that has it)",
    "x86isa-emulator": "blocked: no X86ISA installation is recorded or pinned; the installing agent picks a roster host "
                       "and pins the revision it installs (ACL2 community books, projects/x86isa)",
}

# ======================================================================================
# PROBE: this part runs on any host with Python 3.9+ and nothing but the stdlib.
# ======================================================================================

SYSCTL_KEYS = (
    "hw.model", "hw.machine", "machdep.cpu.brand_string", "machdep.cpu.vendor", "hw.cpufamily",
    "hw.cpusubfamily", "hw.ncpu", "hw.physicalcpu", "hw.logicalcpu", "hw.nperflevels",
    "hw.perflevel0.name", "hw.perflevel0.physicalcpu", "hw.perflevel1.name", "hw.perflevel1.physicalcpu",
    "hw.memsize", "hw.pagesize", "hw.cachelinesize", "kern.osproductversion", "kern.osversion",
    "kern.hv_support", "sysctl.proc_translated",
)
INT_SYSCTLS = {"hw.cpufamily", "hw.cpusubfamily", "hw.ncpu", "hw.physicalcpu", "hw.logicalcpu", "hw.nperflevels",
               "hw.perflevel0.physicalcpu", "hw.perflevel1.physicalcpu", "hw.memsize", "hw.pagesize",
               "hw.cachelinesize", "kern.hv_support", "sysctl.proc_translated"}
VM_TOOLS = ("docker", "podman", "limactl", "colima", "utmctl", "tart", "vfkit", "prlctl", "VBoxManage", "multipass",
            "qemu-system-aarch64", "qemu-system-x86_64", "qemu-x86_64", "qemu-aarch64")
ROSETTA_COMMAND = ("/usr/bin/arch", "-x86_64", "/usr/bin/true")
# A feature key or CPU flag naming a hardware 128-bit binary floating-point format.
BINARY128_FLAG = re.compile(r"(?i)(binary128|float128|fp128|f128|quad)")
APPLE_BRAND = re.compile(r"^Apple M([1-9][0-9]?)(?: (Pro|Max|Ultra))?$")
APPLE_IMPLEMENTER = "0x61"
# MIDR_EL1 (implementer, part) -> name, for the parts a recorded host carries and their neighbours.
ARM_PARTS = {
    ("0x41", "0xd85"): "Cortex-X925", ("0x41", "0xd87"): "Cortex-A725", ("0x41", "0xd4f"): "Neoverse-V2",
    ("0x41", "0xd40"): "Neoverse-V1", ("0x41", "0xd0c"): "Neoverse-N1", ("0x41", "0xd49"): "Neoverse-N2",
    ("0x41", "0xd8e"): "Neoverse-N3", ("0x41", "0xd84"): "Neoverse-V3",
}


def _run(argv, timeout: int = 60):
    try:
        done = subprocess.run(list(argv), capture_output=True, timeout=timeout)
    except (OSError, subprocess.TimeoutExpired) as error:
        return None, "", str(error)
    return done.returncode, done.stdout.decode("utf-8", "replace"), done.stderr.decode("utf-8", "replace")


def _salted(text: str) -> str:
    return hashlib.sha256((SALT + text).encode()).hexdigest()[:16]


def _probe_darwin() -> dict:
    facts: dict = {}
    for key in SYSCTL_KEYS:
        code, out, _ = _run(["/usr/sbin/sysctl", "-n", key])
        value = out.strip() if code == 0 else None
        if value is not None and key in INT_SYSCTLS:
            try:
                value = int(value)
            except ValueError:
                pass
        facts[key] = value
    if isinstance(facts.get("hw.cpufamily"), int):
        facts["hw.cpufamily"] = "0x%08x" % (facts["hw.cpufamily"] & 0xFFFFFFFF)
    code, out, _ = _run(["/usr/sbin/sysctl", "hw.optional"])
    optional = {}
    for line in (out if code == 0 else "").splitlines():
        name, sep, value = line.partition(": ")
        if sep and name.startswith("hw.optional."):
            optional[name[len("hw.optional."):]] = value.strip()
    facts["arm_features_present"] = sorted(k[len("arm."):] for k, v in optional.items()
                                           if k.startswith("arm.FEAT_") and v == "1")
    facts["arm_features_absent"] = sorted(k[len("arm."):] for k, v in optional.items()
                                          if k.startswith("arm.FEAT_") and v == "0")
    facts["hw_optional_other"] = {k: v for k, v in sorted(optional.items()) if not k.startswith("arm.FEAT_")}
    facts["binary128_flags"] = sorted(k for k in optional if BINARY128_FLAG.search(k))
    code, out, _ = _run(["/usr/sbin/ioreg", "-rd1", "-c", "IOPlatformExpertDevice"])
    uuid = re.search(r'"IOPlatformUUID" = "([0-9A-Fa-f-]+)"', out or "")
    facts["machine_digest"] = _salted(uuid.group(1)) if uuid else None
    facts["machine_digest_source"] = "sha256(salt + IOPlatformUUID)[:16]"
    return facts


def _read(path: str) -> str | None:
    try:
        return Path(path).read_text(encoding="utf-8", errors="replace")
    except OSError:
        return None


def _probe_linux() -> dict:
    facts: dict = {}
    processors, current = [], {}
    for line in (_read("/proc/cpuinfo") or "").splitlines() + [""]:
        if not line.strip():
            if current:
                processors.append(current)
            current = {}
            continue
        name, _, value = line.partition(":")
        current[name.strip()] = value.strip()
    facts["logical_cpus"] = sum(1 for p in processors if "processor" in p)
    facts["vendor_ids"] = sorted({p["vendor_id"] for p in processors if "vendor_id" in p})
    facts["model_names"] = sorted({p["model name"] for p in processors if "model name" in p})
    cores = sorted({(p["CPU implementer"].lower(), p["CPU part"].lower()) for p in processors
                    if "CPU implementer" in p and "CPU part" in p})
    facts["arm_cores"] = ["%s:%s" % core for core in cores]
    flag_sets = [set((p.get("flags") or p.get("Features") or "").split()) for p in processors if "processor" in p]
    common = sorted(set.intersection(*flag_sets)) if flag_sets else []
    facts["cpu_flags_common"] = common
    facts["hypervisor_flag"] = "hypervisor" in common
    facts["binary128_flags"] = sorted(f for f in common if BINARY128_FLAG.search(f))
    mem = re.search(r"^MemTotal:\s+(\d+) kB", _read("/proc/meminfo") or "", re.M)
    facts["mem_total_kib"] = int(mem.group(1)) if mem else None
    release = re.search(r'^PRETTY_NAME="?([^"\n]*)"?', _read("/etc/os-release") or "", re.M)
    facts["os_release"] = release.group(1) if release else None
    machine_id = (_read("/etc/machine-id") or "").strip()
    facts["machine_digest"] = _salted(machine_id) if machine_id else None
    facts["machine_digest_source"] = "sha256(salt + /etc/machine-id)[:16]"
    return facts


def _trust_build_dir() -> bool | None:
    """Whether the Trust checkout this script sits in (its main checkout, for a git worktree) holds a
    build/ directory: what makes this host the design's `build host`. None outside a checkout."""
    here = Path(__file__).resolve()
    root = here.parents[3] if len(here.parents) > 3 else None
    if root is None or not (root / "x.py").is_file():
        return None
    main = root
    dotgit = root / ".git"
    if dotgit.is_file():
        found = re.match(r"gitdir: (.+)", (_read(str(dotgit)) or "").strip())
        if found:
            gitdir = Path(found.group(1))
            gitdir = gitdir if gitdir.is_absolute() else (root / gitdir).resolve()
            if gitdir.parent.name == "worktrees":
                main = gitdir.parent.parent.parent
    return (main / "build").is_dir()


def probe() -> dict:
    """The facts of the host this runs on. Deterministic on one host except for what the host changes
    (an OS update, Rosetta installed, a tool added to PATH); nothing volatile (load, free memory)."""
    uname = platform.uname()
    facts = {"schema": PROBE_SCHEMA, "system": uname.system, "machine": uname.machine, "kernel_release": uname.release,
             "hostname": re.sub(r"\.(local|localdomain)$", "", uname.node)}
    if uname.system == "Darwin":
        facts["darwin"] = _probe_darwin()
        if uname.machine == "arm64":
            code, _, err = _run(ROSETTA_COMMAND, timeout=30)
            facts["rosetta"] = {"command": " ".join(ROSETTA_COMMAND), "exit": code,
                                "stderr": (err.strip().splitlines() or [""])[0], "executes": code == 0}
    elif uname.system == "Linux":
        facts["linux"] = _probe_linux()
    acl2 = shutil.which("acl2")
    books = os.environ.get("ACL2_SYSTEM_BOOKS")
    facts["x86isa"] = {"acl2_on_path": acl2 is not None,
                       "x86isa_books": bool(books) and Path(books, "projects", "x86isa").is_dir()}
    facts["vm_tools_on_path"] = sorted(t for t in VM_TOOLS if shutil.which(t))
    facts["trust_checkout_build_dir"] = _trust_build_dir()
    facts["classes"] = probe_classes(facts)
    return facts


def probe_classes(facts: dict) -> dict:
    """The CLASS predicates, applied to one probe. Each list names what satisfies the class here."""
    out = {c: [] for c in CLASS_ORDER}
    system, machine = facts.get("system"), facts.get("machine")
    darwin, linux = facts.get("darwin") or {}, facts.get("linux") or {}
    if system == "Darwin" and darwin.get("sysctl.proc_translated") == 1:
        return out  # the probe itself ran under Rosetta: nothing it saw is native
    if system == "Darwin" and machine == "arm64":
        brand = APPLE_BRAND.match(darwin.get("machdep.cpu.brand_string") or "")
        if brand:
            out["apple-silicon-generation"].append("M" + brand.group(1))
        if (facts.get("rosetta") or {}).get("executes"):
            out["rosetta-2"].append("an x86_64 Mach-O executes under Rosetta 2")
    if system == "Darwin" and machine == "x86_64" and darwin.get("machdep.cpu.vendor") == "GenuineIntel":
        out["x86-64-intel"].append(darwin.get("machdep.cpu.brand_string") or "GenuineIntel")
    if system == "Linux" and machine == "aarch64":
        for core in linux.get("arm_cores") or []:
            implementer, _, part = core.partition(":")
            if implementer != APPLE_IMPLEMENTER:
                out["linux-aarch64-core"].append(core + " " + ARM_PARTS.get((implementer, part), "unnamed part"))
    if system == "Linux" and machine == "x86_64" and not linux.get("hypervisor_flag"):
        for vendor, cls in (("GenuineIntel", "x86-64-intel"), ("AuthenticAMD", "x86-64-amd")):
            if vendor in (linux.get("vendor_ids") or []):
                out[cls].append(", ".join(linux.get("model_names") or [vendor]))
    x86isa = facts.get("x86isa") or {}
    if x86isa.get("acl2_on_path") and x86isa.get("x86isa_books"):
        out["x86isa-emulator"].append("acl2 on PATH with $ACL2_SYSTEM_BOOKS/projects/x86isa")
    return out


# The probe facts some class predicate, row or design reading reads (probe_classes, probe_label, the
# binary128 rows, design_readings): a change to one changes the roster, so --check compares exactly these.
ROSTER_FACTS = {
    "": ("system", "machine", "trust_checkout_build_dir"),
    "rosetta": ("executes",),
    "x86isa": ("acl2_on_path", "x86isa_books"),
    "darwin": ("machdep.cpu.brand_string", "machdep.cpu.vendor", "sysctl.proc_translated", "hw.memsize", "hw.model",
               "binary128_flags"),
    "linux": ("arm_cores", "hypervisor_flag", "vendor_ids", "model_names", "mem_total_kib", "binary128_flags"),
}


def roster_facts(facts: dict) -> dict:
    """The ROSTER_FACTS projection of one probe, keyed `section.fact`."""
    out = {}
    for section, keys in ROSTER_FACTS.items():
        src = facts if section == "" else (facts.get(section) or {})
        for k in keys:
            out[f"{section}.{k}" if section else k] = src.get(k)
    return out


def observation_changes(recorded: dict, live: dict) -> list[str]:
    """The probe facts outside ROSTER_FACTS whose value differs (reported, not compared)."""
    def flat(d, prefix=""):
        for k, v in d.items():
            if isinstance(v, dict):
                yield from flat(v, f"{prefix}{k}.")
            else:
                yield f"{prefix}{k}", v
    a, b = dict(flat(_probe_payload(recorded))), dict(flat(_probe_payload(live)))
    roster = set(roster_facts(live))
    return sorted(k for k in set(a) | set(b) if k not in roster and a.get(k) != b.get(k))


def probe_identity(facts: dict) -> str:
    darwin, linux = facts.get("darwin") or {}, facts.get("linux") or {}
    return (darwin.get("machine_digest") or linux.get("machine_digest")
            or _salted(json.dumps([facts.get("system"), facts.get("machine"), darwin.get("hw.model"),
                                   linux.get("model_names")], sort_keys=True)))


def probe_label(facts: dict) -> str:
    darwin, linux = facts.get("darwin") or {}, facts.get("linux") or {}
    if darwin:
        return "%s (%s), %s %s" % (darwin.get("machdep.cpu.brand_string"), darwin.get("hw.model"), facts.get("system"),
                                   facts.get("machine"))
    return "%s, %s %s" % (", ".join(linux.get("model_names") or linux.get("arm_cores") or ["unknown CPU"]),
                          facts.get("system"), facts.get("machine"))


# ======================================================================================
# REQUIREMENTS: the host classes, and the design text each rests on.
# ======================================================================================

CLASS_ORDER = ("apple-silicon-generation", "linux-aarch64-core", "x86-64-intel", "x86-64-amd", "rosetta-2",
               "x86isa-emulator")
CLASSES = {
    "apple-silicon-generation": dict(
        minimum=2, exits=["E1.6.5"], also=["E2.1.3 (the roster's AArch64 hosts)", "M0.4"], quotes=["e1.6.5"],
        unit="distinct Apple silicon generations",
        predicate="the N of machdep.cpu.brand_string `Apple M<N>[ Pro| Max| Ultra]` on a probe with system Darwin, "
                  "machine arm64 and sysctl.proc_translated 0; Pro/Max/Ultra variants of one N are one generation"),
    "linux-aarch64-core": dict(
        minimum=1, exits=["E1.6.5"], also=["E2.1.3 (the roster's AArch64 hosts)", "M0.4"], quotes=["e1.6.5"],
        unit="distinct non-Apple AArch64 core types running aarch64-unknown-linux-gnu natively",
        predicate="each distinct /proc/cpuinfo (CPU implementer, CPU part) pair with implementer != 0x61 (Apple) on a "
                  "probe with system Linux and machine aarch64",
        interpretation="The design says `one Linux AArch64 core`. This record reads it as a non-Apple core, since "
                       "E1.6.5 probes the aarch64-unknown-linux-gnu target baseline and two Apple generations are "
                       "already required: a Linux VM on Apple silicon runs on an Apple core (implementer 0x61) and is "
                       "not counted. This is the fail-closed reading; a ruling recorded in docs/DECISION_QUEUE.md may widen "
                       "it, and then any native aarch64 Linux probe counts."),
    "x86-64-intel": dict(
        minimum=1, exits=["E2.7.3"], also=["D-8(h)", "M0.4"], quotes=["e2.7.3", "d8h-roster"],
        unit="native x86-64 hosts with an Intel CPU",
        predicate="vendor GenuineIntel (Linux /proc/cpuinfo vendor_id without the `hypervisor` flag, or macOS "
                  "machdep.cpu.vendor on machine x86_64 with sysctl.proc_translated 0)"),
    "x86-64-amd": dict(
        minimum=1, exits=["E2.7.3"], also=["D-8(h)", "M0.4"], quotes=["e2.7.3", "d8h-roster"],
        unit="native x86-64 hosts with an AMD CPU",
        predicate="vendor AuthenticAMD in Linux /proc/cpuinfo vendor_id, without the `hypervisor` flag"),
    "rosetta-2": dict(
        minimum=1, exits=["E2.7.3"], also=["D-8(h)"], quotes=["e2.7.3", "d8h-oracle"],
        unit="Apple silicon hosts on which an x86_64 Mach-O executes under Rosetta 2",
        predicate="`/usr/bin/arch -x86_64 /usr/bin/true` exits 0 on a probe with system Darwin and machine arm64"),
    "x86isa-emulator": dict(
        minimum=1, exits=["E2.7.3"], also=[], quotes=["e2.7.3"],
        unit="hosts with the ACL2 X86ISA emulator installed",
        predicate="`acl2` resolves on PATH and $ACL2_SYSTEM_BOOKS/projects/x86isa is a directory"),
}

# Design text this record rests on, matched with whitespace collapsed; the line is where it starts.
DESIGN_QUOTES = (
    ("d0.11", "D0.11, the probe-host roster: which Apple silicon generations, Linux AArch64 cores, Intel and AMD "
              "hosts are available, and which must be acquired for E1.6.5 and E2.7.3."),
    ("e0.12", "**E0.12** All published, each with its predicate: 0 denominators without one."),
    ("e1.6.5", "Silicon probes on the roster (at least two Apple silicon generations and one Linux AArch64 core, "
               "D0.11) leave 0 refutations of `Cfg_t` unaccounted"),
    ("e2.7.3", "**E2.7.3** Silicon differential on at least one Intel and one AMD host from the roster, plus Rosetta "
               "and the X86ISA emulator: 0 unadjudicated divergences"),
    ("d8h-oracle", "The only x86 oracle on the current host is Rosetta"),
    ("d8h-roster", "so the probe-host roster (D0.11) must add native Intel and AMD hosts before E2.7.3 can pass."),
    ("e2.1.3", "binary32 and binary64 on the roster's AArch64 hosts show 0 mismatches"),
    ("e2.1.3-b128", "binary128, which no roster host implements in hardware [K]"),
    ("appendix-b", "| No roster host implements binary128 in hardware | E2.1.3 | D0.11 |"),
    ("m0.4", "built on the LLVM lane and run many times on the roster's hosts."),
    ("k2", "peak RSS ≤ 64 GB on the 128 GB build host"),
    ("i-cfg-target", "`Cfg_t : SysState → Prop` is fixed **per target**, not per CPU."),
)

# ======================================================================================
# RECORDS: what the pinned trees say about other hosts.
# ======================================================================================

GREP = ('Apple M[1-9]|(Mac|MacBookPro|MacBookAir|Macmini|iMac|MacPro)[0-9]+,[0-9]+|i[3579]-[0-9]{4,5}|Xeon|EPYC'
        '|Ryzen|Threadripper|Cortex-[AX][0-9]|Neoverse|Graviton|GB10|"(host|host_name|hostname)" ?: ?"|Host: `'
        '|spark-[0-9a-f]{4}|m[0-9]{1,2}-tower|m[0-9]{1,2}Mac[A-Za-z]*[0-9]+GB|m[0-9]{1,2}-Macbook-'
        '|"host" ?: ?"M[1-9]')


def _hostname(value: str) -> str | None:
    head = value.split(" | ")[0].strip()
    if not head:
        return None
    return "hostname=" + re.sub(r"\.(local|localdomain)$", "", head.split()[0])


EXTRACTORS = (
    ("apple-brand", re.compile(r"Apple M([1-9])(?: (Pro|Max|Ultra))?"),
     lambda m: "Apple M" + m.group(1) + (" " + m.group(2) if m.group(2) else "")),
    ("apple-brand-in-host-field", re.compile(r'"host"\s*:\s*"M([1-9])(?: (Pro|Max|Ultra))? /'),
     lambda m: "Apple M" + m.group(1) + (" " + m.group(2) if m.group(2) else "")),
    ("mac-model", re.compile(r"\b((?:Mac|MacBookPro|MacBookAir|Macmini|iMac|MacPro)\d{1,2},\d{1,2})\b"),
     lambda m: m.group(1)),
    ("x86-model", re.compile(r"\b(AMD (?:Ryzen(?: Threadripper)?(?: PRO)? \d \d{4}[A-Z0-9]*|EPYC \d{4}[A-Z0-9]*))"),
     lambda m: m.group(1)),
    ("intel-core", re.compile(r"\b(i[3579]-\d{4,5}[A-Z]{0,2})\b"), lambda m: "Intel Core " + m.group(1)),
    ("x86-family", re.compile(r"\b(Xeon|EPYC|Ryzen|Threadripper)\b"), lambda m: m.group(1)),
    ("arm-core-or-soc", re.compile(r"\b(Cortex-[AX]\d+|Neoverse[- ][A-Z]\d*[A-Z0-9]*|Graviton\d*|GB10)\b"),
     lambda m: m.group(1)),
    ("host-field", re.compile(r'"(?:host|host_name|hostname)"\s*:\s*"([^"]*)"'), lambda m: _hostname(m.group(1))),
    ("host-quoted", re.compile(r"Host: `([^`]+)`"), lambda m: _hostname(m.group(1))),
    ("fleet-name", re.compile(r"\b(spark-[0-9a-f]{4}|m\d{1,2}-tower|m\d{1,2}Mac[A-Za-z]*\d+GB\d+TB"
                              r"|m\d{1,2}-Macbook-[A-Za-z0-9-]*[A-Za-z0-9])(?:\.local(?:domain)?)?\b"),
     lambda m: "hostname=" + m.group(1)),
)

NOT_A_HOST = {
    "third-party": "text shipped with a vendored third-party crate or its test data",
    "os-or-target-string": "a `host` field holding a target triple, an architecture or an OS string, not a machine",
    "fixture": "a test fixture's placeholder host",
    "code-example": "a docstring, schema sample or test mock in code",
    "literature": "a cited microarchitecture study, not a machine this project ran on",
    "negative": "a statement that a host is NOT this part",
    "external": "another party's machines (competition infrastructure) or a test spec of them",
    "descriptive-host-field": "the first word of a free-text `host` field; its CPU is extracted separately",
}

# First match wins: (repo, path, identity) regexes -> disposition. `host:{N}` takes group N of the
# identity match as the row id.
RULES = (
    ("ty", r"^crates/tla-(url|portable-atomic|sha2|xml|foldhash|fst|simd-adler32|adler2|base64)/", r".", "not:third-party"),
    (".*", r".", r"^hostname=((aarch64|x86_64|arm64|riscv64)([-_ ].*)?|Darwin|macOS-.*|\$\(uname|…)$", "not:os-or-target-string"),
    (".*", r".", r"^hostname=(test-host|fixture-host|qualification-test-host|test)$", "not:fixture"),
    ("ty", r".", r"^hostname=(Apple|Mac|M[1-9])$", "not:descriptive-host-field"),
    ("trust-cg", r"^(benchmarks/beat-llvm/(hostinfo|test_run_provenance)\.py|scripts/tests/)", r".", "not:code-example"),
    (".*", r"(^|/)benchmarking\.md$", r"^Xeon$", "not:code-example"),
    ("ay", r"^crates/ay-bench/", r"^MacBookPro18,3$", "not:code-example"),
    ("trust-cg", r"^crates/trust-cg-(ir|opt)/", r"^Apple M1$", "not:literature"),
    ("trust-cg", r"^reports/perf/2026-09-23-linux-icache-in-place-control/", r"^Neoverse V2$", "not:negative"),
    ("ay", r"^(benchmarks/comparisons\.toml|crates/ay/src/cmd_bench_compare\.rs|competition/)",
     r"^(AMD EPYC .*|EPYC|Xeon|Apple M2 Max)$", "not:external"),
    ("ay", r".", r"^(Cortex-(X925|A725)|GB10)$", "host:gb10"),
    ("trust-cg|ty", r".", r"^(hostname=spark-d5a4|Cortex-(X925|A725))$", "host:spark-d5a4"),
    (".*", r".", r"^hostname=(spark-[0-9a-f]{4})$", "host:{1}"),
    (".*", r".", r"^(GB10|hostname=gb10)$", "host:gb10"),
    ("ny|trust-cg", r".", r"^(hostname=m17-tower|AMD Ryzen 9 9900X3D|Ryzen)$", "host:m17-tower"),
    ("trust-cg", r".", r"^(MacBookPro14,3|Intel Core i7-7920HQ)$", "host:macbookpro14-3"),
    (".*", r".", r"^hostname=(m\d{1,2})(?=[-A-Za-z])", "host:{1}"),
    ("ay", r"^docs/z3-parity/", r"^(Apple M4 Max|Mac16,5)$", "host:m13"),
    ("ny", r".", r"^Apple M4 Pro$", "host:m11"),
    (".*", r".", r"^(Apple M4( Pro| Max)?|Mac16,5)$", "host:apple-m4-other"),
    (".*", r".", r"^Apple M3$", "host:apple-m3"),
    (".*", r".", r"^hostname=(Andrews-MBP(-2)?|Andrews-MacBook-Pro(-2)?|AY-MacBook-Pro-3|MacBook-Pro)$", "host:{1}"),
    ("trust-mc|ny", r".", r"^(Apple M5|Mac17,4)$", "host:apple-m5-other"),
    (".*", r".", r"^(Apple M5 Max|Mac17,6)$", "host:apple-m5-max"),
)
COMPILED_RULES = tuple((re.compile(r), re.compile(p), re.compile(i), d) for r, p, i, d in RULES)


def F(repo: str, path: str, quote: str) -> dict:
    return {"repo": repo, "path": path, "quote": quote}


# The recorded rows. `generation` is the Apple generation where a record binds one (with its
# source); `classes` maps a required class to what this host would contribute if available.
RECORDED = {
    "spark-d5a4": dict(
        target="aarch64-unknown-linux-gnu",
        cpu="NVIDIA GB10 ('Grace-class'), 20 cores: 10 Cortex-X925 (MIDR_EL1 0x410fd851) + 10 Cortex-A725 (0x410fd871); 121 GiB",
        classes={"linux-aarch64-core": ["0x41:0xd85 Cortex-X925", "0x41:0xd87 Cortex-A725"]},
        facts=[F("trust-cg", "docs/linux-aarch64-host-provisioning.md", "## Host identity (observed 2026-09-22)"),
               F("trust-cg", "docs/linux-aarch64-host-provisioning.md", "the ratchet ledger names this host `spark-d5a4`"),
               F("trust-cg", "docs/linux-aarch64-host-provisioning.md", "Ubuntu 24.04.4 LTS, Linux `6.17.0-1026-nvidia`"),
               F("trust-cg", "docs/linux-aarch64-host-provisioning.md", "NVIDIA Grace-class, 20 cores (Cortex-X925 + Cortex-A725)"),
               F("trust-cg", "docs/linux-aarch64-host-provisioning.md", "| Memory | 121 GiB;"),
               F("trust-cg", "reports/perf/2026-09-23-linux-icache-in-place-control/README.md", "`0x410fd871` (CPUs 0-4 and 10-14). Ten Cortex-X925 cores have"),
               F("trust-cg", "reports/perf/2026-09-23-linux-icache-in-place-control/README.md", "`0x410fd851` (CPUs 5-9 and 15-19)")]),
    "spark-f904": dict(
        target="aarch64-unknown-linux-gnu",
        cpu="unrecorded (`unknown-cpu`), 20 cores, 121 GiB; GPU adapter NVIDIA GB10",
        classes={"linux-aarch64-core": ["core type unrecorded"]},
        facts=[F("ny", "reports/measured-2026/lsnc_relu_artifacts/sweep_manifest.json", '"target_arch": "aarch64",'),
               F("ny", "reports/measured-2026/lsnc_relu_artifacts/sweep_manifest.json", "wgpu adapter: Vulkan (NVIDIA GB10, IntegratedGpu)"),
               F("ny", "reports/measured-2026/lsnc_relu_artifacts/sweep_manifest.json", '"host": "spark-f904 | unknown-cpu | 20 cores | 121 GiB",'),
               F("ny", "docs/abc_cgan_nCh3_prop0_trace_2026-09-01.log", "Experiments at Tue Sep  1 13:14:43 2026 on spark-f904")]),
    "spark-49f7": dict(
        target="unrecorded", cpu="unrecorded (only the host name is recorded)", classes={},
        facts=[F("ny", "reports/falsification_audit/blind_rows_300s.json", '"generated_utc": "2026-08-08T20:15:05Z",'),
               F("ny", "reports/falsification_audit/blind_rows_300s.json", '"host": "spark-49f7",')]),
    "gb10": dict(
        target="aarch64-unknown-linux-gnu",
        cpu="NVIDIA GB10; records that name no host, so possibly one of the spark-* rows",
        classes={"linux-aarch64-core": ["core type unrecorded"]},
        facts=[F("trust", "reports/2026-09-02-verified-lane-unblocked-on-linux.md", "(GB10, umask 0002, 127 GB RAM)"),
               F("ny", "CLAUDE.md", "**this GB10** (Linux aarch64, 121 GiB unified CPU+GPU memory)")]),
    "m17-tower": dict(
        target="x86_64-unknown-linux-gnu",
        cpu="AMD Ryzen 9 9900X3D 12-Core Processor, 24 logical CPUs, 61 GiB; Linux 7.0.0-31-generic",
        classes={"x86-64-amd": ["AMD Ryzen 9 9900X3D 12-Core Processor"]},
        facts=[F("trust-cg", "reports/perf/2026-09-20-linux-x86-64-baseline/beat-llvm-diag/166093c1a96f-dirty-20260921T024651Z.json", '"host_model": "AMD Ryzen 9 9900X3D 12-Core Processor",'),
               F("trust-cg", "reports/perf/2026-09-20-linux-x86-64-baseline/beat-llvm-diag/166093c1a96f-dirty-20260921T024651Z.json", '"host_name": "m17-tower",'),
               F("trust-cg", "reports/perf/2026-09-20-linux-x86-64-baseline/beat-llvm-diag/166093c1a96f-dirty-20260921T024651Z.json", '"os": "Linux 7.0.0-31-generic x86_64",'),
               F("trust-cg", "reports/perf/2026-09-20-linux-x86-64-baseline/README.md", "Linux 7.0.0-31-generic, 24 cores, 61 GiB"),
               F("ny", "docs/RTX5080_ABC_GAP_WIN_PLAN_2026-08-12.md", "Ryzen 9 9900X3D, 12 cores / 24 threads, 61 GiB host RAM")]),
    "macbookpro14-3": dict(
        target="x86_64-apple-darwin",
        cpu="MacBookPro14,3, 4 cores, 16 GB, macOS 13.7.8. An Intel Core i7-7920HQ (4-core/8-thread, 16 GB) is "
            "recorded for `the dev box` with no model identifier; no record binds the two",
        classes={"x86-64-intel": ["x86_64-apple-darwin MacBookPro14,3 (CPU vendor unprobed)"]},
        facts=[F("trust-cg", "reports/perf/2026-09-22-darwin-x86-64-census/README.md", "`x86_64-apple-darwin`, macOS 13.7.8, MacBookPro14,3 (4 cores, 16 GB)"),
               F("trust-cg", "reports/2026-09-21-mac-x86-64-portable-qualification/README.md", "(MacBookPro14,3, 4 cores, 16 GB;"),
               F("trust-cg", "docs/archive/enc8-phase1-lrat-throughput-2026-07-02.md", "Intel Core i7-7920HQ (4-core/8-thread, 2017), 16 GB RAM"),
               F("trust-cg", "docs/linux-x86-64-completion.md", "**The bridge now builds and loads on the Darwin x86-64 workstation**")]),
    "m13": dict(
        target="aarch64-apple-darwin", cpu="Apple M4 Max (Mac16,5), 16 cores, 48 GB, macOS 26.6.2",
        generation=("M4", "ay docs/z3-parity: `Mac16,5 Apple M4 Max` in the run whose JSONL names the host m13"),
        facts=[F("ay", "docs/z3-parity/2026-09-20-time-exits-T60.md", "**Machine:** Mac16,5 Apple M4 Max, 16 cores, 48 GB, macOS 26.6.2"),
               F("ay", "docs/z3-parity/2026-09-20-time-exits-T60.jsonl", '"host": "m13-Macbook-M4-Max-48GB-1TB.local"')]),
    "m11": dict(
        target="aarch64-apple-darwin", cpu="Apple M4 Pro, 14 cores, 48 GB",
        generation=("M4", "ny: `Host: m11Macbo48GB2TB (Apple M4 Pro, 14 cores, 48 GB)`"),
        facts=[F("ny", "docs/ORT_WITNESS_REPAIR_CHARACTERIZATION_2026-08-20.md", "Host: `m11Macbo48GB2TB` (Apple M4 Pro, 14 cores, 48 GB)")]),
    "apple-m4-other": dict(
        target="aarch64-apple-darwin",
        cpu="Apple M4-generation records naming no host: an M4 Max Mac16,5 recorded 2026-09-19; an M4 Max Mac16,5 with "
            "36 GiB; an M4 Pro with 24 GB; an M4 Max with 128 GB. Possibly several machines, possibly m11 or m13",
        generation=("M4", "the brand strings themselves"),
        facts=[F("trust-cg", "crates/trust-cg-verify/tests/fixtures/aarch64_nzcv_silicon_truth.json", '"recorded_on_cpu": "Apple M4 Max",'),
               F("trust-cg", "crates/trust-cg-verify/tests/fixtures/aarch64_nzcv_silicon_truth.json", '"hardware_model": "Mac16,5",'),
               F("trust-cg", "crates/trust-cg-verify/tests/fixtures/aarch64_nzcv_silicon_truth.json", '"recorded_at": "2026-09-19T01:04:02Z",'),
               F("ty", "scripts/ty_memory_guard.py", "This box (Mac16,5 / M4 Max / 36 GiB / macOS 26.5.2 25F84)"),
               F("ty", "docs/perf/profiling-the-shipped-binary.md", "Apple M4 Pro / 24 GB, macOS 26.5.2, 2026-08-01"),
               F("trust-ir", "reports/2026-04-17-lean4-baseline.md", "| Hardware | Apple M4 Max, 16 cores, 128 GB RAM |")]),
    "apple-m3": dict(
        target="aarch64-apple-darwin", cpu="Apple M3 Mac (integrated GPU), 16 GB",
        generation=("M3", "clean docs/BENCHMARKS.md"),
        facts=[F("clean", "docs/BENCHMARKS.md", "**Commit:** dd65eedd2 (2025-12-30)"),
               F("clean", "docs/BENCHMARKS.md", "**Hardware:** Apple M3 Mac (integrated GPU), 16GB RAM")]),
    "apple-m5-max": dict(
        target="aarch64-apple-darwin",
        cpu="Apple M5 Max / Mac17,6 records naming no host; the confirmed host is an Apple M5 Max Mac17,6, so they may be it",
        generation=("M5", "the brand strings themselves"),
        facts=[F("trust", "reports/2026-09-17-phase0-k7-coinductive.md", "Apple M5 Max (Mac17,6), 18 cores, 128 GB, macOS 26.6.2")]),
    "apple-m5-other": dict(
        target="aarch64-apple-darwin", cpu="Apple M5, Mac17,4, 32 GiB (trust-mc); ny's Metal adapter name `Apple M5`",
        generation=("M5", "trust-mc `Host: Apple M5, 32 GiB`"),
        facts=[F("trust-mc", "docs/ay-asks/2026-09-11-const-store-chain-memout/README.md", "Host: Apple M5, 32 GiB (`hw.memsize` 34359738368), Darwin 25.6.0"),
               F("trust-mc", "docs/ay-asks/2026-09-13-copy-overlap-disjoint-slices/README.md", "Apple Mac17,4, 32 GiB")]),
    "m7": dict(
        target="aarch64-apple-darwin", cpu="Apple M5 Max, 18 CPUs, 128 GiB",
        generation=("M5", "ay evals: `cpu_model` in the record naming the host"),
        facts=[F("ay", "evals/results/chccomp-2025-extra-small-lia/2026-06-15T16-30-05Z/results.json", '"hostname": "m7-Macbook-M5-Max-128GB-8TB.local",'),
               F("ay", "evals/results/chccomp-2025-extra-small-lia/2026-06-15T16-30-05Z/results.json", '"cpu_model": "Apple M5 Max",')]),
    "m15": dict(target="unrecorded", cpu="unrecorded; the host name reads `M5-Max-128GB-8TB`",
                generation=("M5", "host name text only")),
    "m16": dict(target="unrecorded", cpu="unrecorded; the host name reads `M5-Max-128GB-8TB`",
                generation=("M5", "host name text only")),
    "m21": dict(target="unrecorded", cpu="unrecorded; the host name reads `M5-Max-128GB-8TB`",
                generation=("M5", "host name text only")),
    "m2": dict(target="unrecorded", cpu="unrecorded; the host name reads `128GB8TB`"),
    "m8": dict(target="unrecorded", cpu="unrecorded; the host name reads `128GB8TB`"),
    "m19": dict(target="unrecorded", cpu="unrecorded; the host name reads `128GB2TB`"),
    "m22": dict(target="unrecorded", cpu="unrecorded; the host name reads `128GB8TB`"),
    "MacBook-Pro": dict(
        target="aarch64-apple-darwin", cpu="Apple M5 Max, 18 CPUs, 128 GiB",
        generation=("M5", "ay evals: `cpu_model` in the record naming the host"),
        facts=[F("ay", "evals/results/chccomp-2025-extra-small-lia/2026-05-31T12-56-10Z/results.json", '"hostname": "MacBook-Pro.local",'),
               F("ay", "evals/results/chccomp-2025-extra-small-lia/2026-05-31T12-56-10Z/results.json", '"cpu_model": "Apple M5 Max",')]),
    "AY-MacBook-Pro-3": dict(
        target="aarch64-apple-darwin", cpu="Apple M5 Max, 128 GiB",
        generation=("M5", "ay evals: `cpu_model` in the record naming the host"),
        facts=[F("ay", "evals/results/chccomp-2025-extra-small-lia/2026-06-05T16-22-00Z/results.json", '"hostname": "AY-MacBook-Pro-3.local",'),
               F("ay", "evals/results/chccomp-2025-extra-small-lia/2026-06-05T16-22-00Z/results.json", '"cpu_model": "Apple M5 Max",')]),
    "Andrews-MacBook-Pro-2": dict(
        target="aarch64-apple-darwin", cpu="hw.model Mac17,6 (the model the confirmed Mac17,6 probe reports as Apple M5 Max)",
        generation=("M5", "ty provenance: `hw.model` Mac17,6 in the record naming the host"),
        facts=[F("ty", "reports/perf/2026-09-22-corpus-rescreen-a814972loss-rows-nary-memo/provenance.json", '"hw.model": "Mac17,6",'),
               F("ty", "reports/perf/2026-09-22-corpus-rescreen-a814972loss-rows-nary-memo/provenance.json", '"hostname": "Andrews-MacBook-Pro-2.local",')]),
    "Andrews-MacBook-Pro": dict(target="arm64 Darwin", cpu="unrecorded",
                                facts=[F("ty", "reports/perf/2026-09-21-multipaxos-ab/campaign.json", '"host": "Andrews-MacBook-Pro.local arm64 26.6.2"')]),
    "Andrews-MBP": dict(target="arm64 Darwin", cpu="unrecorded",
                        facts=[F("ty", "reports/perf/2026-09-15-nbacg-join-ab/aba_asyn_byz-diagnostic/campaign.json", '"host": "Andrews-MBP.localdomain arm64 26.6.2"')]),
    "Andrews-MBP-2": dict(target="arm64 Darwin", cpu="unrecorded",
                          facts=[F("ty", "reports/perf/2026-09-14-unchanged-unresolved-identifier/mcewd687a_main_vs_branch_ab.json", '"host": "Andrews-MBP-2.localdomain"')]),
}


class Fatal(Exception):
    """An input the measurement cannot proceed without (exit 2)."""


def collapse_with_lines(text: str) -> tuple[str, list[int]]:
    """Whitespace-collapsed text and, per character, the 1-based line it came from."""
    out, where, line, space = [], [], 1, False
    for ch in text:
        if ch.isspace():
            if not space and out:
                out.append(" ")
                where.append(line)
            space = True
            if ch == "\n":
                line += 1
            continue
        space = False
        out.append(ch)
        where.append(line)
    return "".join(out), where


def scan_tree(C, name: str, store: Path, rev: str, git_dir: bool) -> list[tuple]:
    args = ["grep", "-I", "-n", "-E", GREP, rev, "--"]
    if name == "trust":
        args += ["."] + [f":(exclude){d}" for d in UPSTREAM_EXCLUDES]
    out = C.git(store, *args, git_dir=git_dir, ok_codes=(0, 1))
    if out is None:
        raise Fatal(f"git grep failed in {name} at {rev}")
    found = []
    for line in out.splitlines():
        parts = line.split(":", 3)
        if len(parts) < 4 or parts[0] != rev:
            continue
        _, path, number, text = parts
        for extractor, rx, make in EXTRACTORS:
            for match in rx.finditer(text):
                identity = make(match)
                if identity:
                    found.append((name, path, int(number), identity, text.strip()[:240], extractor))
    return found


def classify(occurrence: tuple) -> str | None:
    repo, path, _, identity, _, _ = occurrence
    for repo_rx, path_rx, ident_rx, disposition in COMPILED_RULES:
        if not repo_rx.fullmatch(repo):
            continue
        if not path_rx.search(path):
            continue
        match = ident_rx.search(identity)
        if not match:
            continue
        if "{1}" in disposition:
            return disposition.replace("{1}", match.group(1))
        return disposition
    return None


def measure(C, repo: Path, live: dict | None, extra_probes: list[dict], recorded_probes: list[dict],
            rev: str = "HEAD") -> dict:
    findings: list[str] = []
    head = (C.git(repo, "rev-parse", "--verify", f"{rev}^{{commit}}") or "").strip()
    if not C.HEX40.match(head):
        raise Fatal(f"cannot read {rev} of {repo}")
    design_blob = (C.git(repo, "rev-parse", f"{head}:{DESIGN_REL}") or "").strip()
    design_text = C.git(repo, "show", f"{head}:{DESIGN_REL}")
    if not design_text:
        raise Fatal(f"cannot read {DESIGN_REL} at {head}")
    collapsed, where = collapse_with_lines(design_text)
    quotes = []
    for qid, quote in DESIGN_QUOTES:
        at = collapsed.find(" ".join(quote.split()))
        if at < 0:
            findings.append(f"DESIGN: quote {qid!r} not found in {DESIGN_REL} at {head[:12]}")
            quotes.append({"id": qid, "line": 0, "quote": quote})
        else:
            quotes.append({"id": qid, "line": where[at], "quote": quote})

    # The trees, at their pins.
    common_dir = Path((C.git(repo, "rev-parse", "--path-format=absolute", "--git-common-dir") or "").strip())
    main_checkout = common_dir.parent if common_dir.name == ".git" else None
    trees = {"trust": (repo, head, False)}
    pins = {}
    for name in FIRST_PARTY:
        tree = C.first_party_tree(repo, name, head)
        if tree is None:
            raise Fatal(f"first-party/{name}: no readable object store for the gitlink at {head[:12]}")
        checkout = None
        if main_checkout is not None and (main_checkout / "first-party" / name / ".git").exists():
            checkout = (C.git(main_checkout / "first-party" / name, "rev-parse", "HEAD") or "").strip() or None
        trees[name] = (tree.repo, tree.rev, True)
        pins[name] = {"pin": tree.rev, "checkout_head": checkout or "not checked out",
                      "read": "git objects at the pin (the superproject's modules store)"}
        if C.git(tree.repo, "cat-file", "-e", f"{tree.rev}^{{commit}}", git_dir=True) is None:
            raise Fatal(f"first-party/{name}: pin {tree.rev} is not in {tree.repo}")

    with ThreadPoolExecutor(max_workers=len(trees)) as pool:
        futures = {name: pool.submit(scan_tree, C, name, *trees[name]) for name in trees}
        occurrences = [o for name in trees for o in futures[name].result()]
    order = {n: i for i, n in enumerate(("trust",) + FIRST_PARTY)}
    occurrences.sort(key=lambda o: (order[o[0]], o[1], o[2], o[3]))

    by_row: dict[str, list] = {}
    by_not: dict[str, set] = {}
    unclassified = []
    for occ in occurrences:
        disposition = classify(occ)
        if disposition is None:
            unclassified.append(occ)
        elif disposition.startswith("host:"):
            by_row.setdefault(disposition[5:], []).append(occ)
        else:
            by_not.setdefault(disposition[4:], set()).add((occ[0], occ[1], occ[3]))
    for occ in unclassified[:50]:
        findings.append(f"UNCLASSIFIED: {occ[0]}:{occ[1]}:{occ[2]} identity {occ[3]!r} ({occ[4][:120]!r})")
    if len(unclassified) > 50:
        findings.append(f"UNCLASSIFIED: {len(unclassified) - 50} more")
    for row in sorted(set(by_row) - set(RECORDED)):
        findings.append(f"ROW: identities classified to host row {row!r}, which has no definition in RECORDED")
    for row in sorted(set(RECORDED) - set(by_row)):
        findings.append(f"ROW: RECORDED row {row!r} is supported by no occurrence in the pinned trees")

    # Facts, each re-found verbatim at its pin.
    texts: dict = {}

    def lines_of(repo_name: str, path: str):
        if (repo_name, path) not in texts:
            store, rev, git_dir = trees[repo_name]
            text = C.git(store, "show", f"{rev}:{path}", git_dir=git_dir)
            texts[(repo_name, path)] = None if text is None else text.split("\n")
        return texts[(repo_name, path)]

    rows = []
    for row_id in sorted(RECORDED, key=lambda r: (_row_sort(r), r)):
        spec = RECORDED[row_id]
        occ = by_row.get(row_id, [])
        facts = []
        for fact in spec.get("facts", []):
            lines = lines_of(fact["repo"], fact["path"])
            line = next((i + 1 for i, text in enumerate(lines or []) if fact["quote"] in text), 0)
            if not line:
                findings.append(f"FACT: {row_id}: {fact['repo']}:{fact['path']} does not contain {fact['quote']!r} at the pin")
            facts.append(dict(fact, line=line))
        files = sorted({(o[0], o[1]) for o in occ}, key=lambda f: (order[f[0]], f[1]))
        per_repo = {}
        for r, _ in files:
            per_repo[r] = per_repo.get(r, 0) + 1
        seen, first = set(), []
        for o in occ:
            if o[0] not in seen:
                seen.add(o[0])
                first.append({"repo": o[0], "path": o[1], "line": o[2], "identity": o[3]})
        identities = sorted({o[3] for o in occ})
        generation = spec.get("generation")
        classes = dict(spec.get("classes", {}))
        if generation:
            classes = {"apple-silicon-generation": [generation[0]], **classes}
        rows.append({"id": row_id, "status": BLOCKED, "target": spec["target"], "cpu": spec["cpu"],
                     "generation": generation[0] if generation else "unrecorded",
                     "generation_source": generation[1] if generation else "no record binds a generation",
                     "would_satisfy": classes, "identities": identities, "files_by_repo": per_repo,
                     "files": len(files), "first_occurrence_per_repo": first, "facts": facts})

    # Confirmed hosts: probes.
    confirmed = []
    live_id = probe_identity(live) if live else None
    seen_ids = set()
    for facts in ([live] if live else []) + extra_probes + recorded_probes:
        ident = probe_identity(facts)
        if ident in seen_ids:
            continue
        seen_ids.add(ident)
        facts = dict(facts, classes=probe_classes(facts))
        confirmed.append({"machine": ident, "label": probe_label(facts), "hostname": facts.get("hostname"),
                          "status": "measured", "measured_here": ident == live_id, "probe": facts})
    confirmed.sort(key=lambda c: c["machine"])

    # The roster, per class.
    classes = []
    for cid in CLASS_ORDER:
        spec = CLASSES[cid]
        members = sorted({m for c in confirmed for m in c["probe"]["classes"].get(cid, [])})
        if cid == "apple-silicon-generation":
            count = len(members)
        elif cid == "linux-aarch64-core":
            count = len({m.split()[0] for m in members})
        else:
            count = sum(1 for c in confirmed if c["probe"]["classes"].get(cid))
        candidates = [r["id"] for r in rows if cid in r["would_satisfy"]]
        if cid == "apple-silicon-generation":
            recorded_gens = sorted({r["generation"] for r in rows if r["generation"] != "unrecorded"}, key=_gen_key)
            new_gens = [g for g in recorded_gens if g not in members]
            candidates = [r["id"] for r in rows if r["generation"] in new_gens]
        else:
            recorded_gens, new_gens = None, None
        if cid == "rosetta-2":
            candidates = [f"confirmed {c['machine']} ({c['label']}) once Rosetta 2 is installed" for c in confirmed
                          if c["probe"].get("system") == "Darwin" and c["probe"].get("machine") == "arm64"
                          and not c["probe"]["classes"].get("rosetta-2")] + [
                r["id"] for r in rows if r["target"] == "aarch64-apple-darwin"]
        shortfall = max(0, spec["minimum"] - count)
        entry = {"id": cid, "minimum": spec["minimum"], "unit": spec["unit"], "exits": spec["exits"],
                 "also": spec["also"], "design_quotes": spec["quotes"], "predicate": spec["predicate"],
                 "confirmed": count, "confirmed_members": members, "shortfall": shortfall,
                 "recorded_candidates": candidates,
                 "status": "measured" if shortfall == 0 else CLASS_BLOCKED.get(cid, BLOCKED),
                 "acquire": _acquire(cid, shortfall, candidates, new_gens)}
        if recorded_gens is not None:
            entry["recorded_generations"] = recorded_gens
            entry["recorded_generations_not_confirmed"] = new_gens
        if "interpretation" in spec:
            entry["interpretation"] = spec["interpretation"]
        classes.append(entry)

    return {"head": head, "design_blob": design_blob, "quotes": quotes, "pins": pins, "rows": rows,
            "confirmed": confirmed, "classes": classes, "not_a_host": {k: sorted(v) for k, v in by_not.items()},
            "occurrences": occurrences, "unclassified": len(unclassified), "findings": findings,
            }


def _gen_key(gen: str) -> int:
    return int(gen[1:]) if gen[1:].isdigit() else 99


def _row_sort(row_id: str) -> int:
    spec = RECORDED[row_id]
    target = spec["target"]
    if "linux" in target and "aarch64" in target:
        return 1
    if target.startswith("x86_64"):
        return 2
    if spec.get("generation"):
        return 3
    return 4


def _acquire(cid: str, shortfall: int, candidates: list, new_gens) -> str:
    if shortfall == 0:
        return "nothing: the confirmed hosts meet the minimum"
    names = ", ".join(candidates) if candidates else "none recorded"
    if cid == "apple-silicon-generation":
        return (f"{shortfall} more generation(s). Run `--probe` on a host of a recorded, unconfirmed "
                f"generation ({', '.join(new_gens) or 'none'}: rows {names}); otherwise "
                f"acquire an Apple silicon Mac of another generation than those confirmed.")
    if cid == "rosetta-2":
        return ("The owner installs Rosetta 2 on the confirmed Apple silicon host (`softwareupdate --install-rosetta "
                "--agree-to-license`, the x86-semantic-differential harness README's first step; accepting Apple's "
                "license is the owner's act), then --write is re-run; or `--probe` runs on another Apple silicon host with "
                "Rosetta installed.")
    if cid == "x86isa-emulator":
        return ("Install ACL2 and the community books' projects/x86isa on a roster host at a pinned revision (no "
                "X86ISA pin exists in docs/trust-core/EXTERNAL_PINS.toml; recording one is the first step) and "
                "re-probe with $ACL2_SYSTEM_BOOKS set. No record of an X86ISA installation exists in the pinned trees.")
    return (f"{shortfall} host(s). Run `--probe` on a recorded row ({names}); otherwise acquire one.")


# ======================================================================================
# The record.
# ======================================================================================

BARE = re.compile(r"^[A-Za-z0-9_-]+$")


def tq(value) -> str:
    if isinstance(value, bool):
        return "true" if value else "false"
    if isinstance(value, int):
        return str(value)
    if isinstance(value, str):
        return json.dumps(value, ensure_ascii=False)
    if isinstance(value, (list, tuple)):
        return "[" + ", ".join(tq(v) for v in value) + "]"
    if isinstance(value, dict):
        return "{ " + ", ".join(f"{tk(k)} = {tq(v)}" for k, v in value.items() if v is not None) + " }" if value else "{}"
    raise TypeError(f"no TOML form for {value!r}")


def tk(key: str) -> str:
    return key if BARE.match(key) else json.dumps(key, ensure_ascii=False)


def multiline(key: str, values: list) -> list[str]:
    if not values:
        return [f"{key} = []"]
    return [f"{key} = ["] + [f"  {tq(v)}," for v in values] + ["]"]


def summary_rows(data: dict) -> list[dict]:
    rows = [
        {"name": "required-host-classes", "value": len(CLASS_ORDER), "status": "measured",
         "predicate": "the classes E1.6.5 and E2.7.3 state (design quotes e1.6.5, e2.7.3), one [[class]] each: "
                      + ", ".join(f"{c} >= {CLASSES[c]['minimum']}" for c in CLASS_ORDER)},
        {"name": "hosts-confirmed", "value": len(data["confirmed"]), "status": "measured",
         "predicate": "distinct machine digests among the probes this record holds (a probe runs on the host itself)"},
        {"name": "hosts-recorded-unconfirmed", "value": len(data["rows"]), "status": "blocked",
         "predicate": "the [[recorded]] rows: host rows the fail-closed scan of the pinned trees supports, none probed",
         "blocked": BLOCKED[len("blocked: "):] + ": a host the pinned trees record is not a host the project has, "
                    "until the probe runs on it",
         "unblock": "on each [[recorded]] host that can be reached, `python3 "
                    f"{SCRIPT_REL} --probe > probe.json`, then `--write --with-probe probe.json` here confirms it"},
        {"name": "classes-short", "value": sum(1 for c in data["classes"] if c["shortfall"]), "status": "measured",
         "predicate": "the [[class]] entries whose confirmed count is below the design's minimum"},
    ]
    for c in data["classes"]:
        rows.append({"name": f"{c['id']}.confirmed", "value": c["confirmed"], "of": c["minimum"], "status": "measured",
                     "predicate": c["predicate"], "members": c["confirmed_members"]})
        row = {"name": f"{c['id']}.shortfall", "value": c["shortfall"],
               "status": "measured" if c["status"] == "measured" else "blocked",
               "predicate": f"max(0, {c['minimum']} - {c['id']}.confirmed)"}
        if row["status"] == "blocked":
            row["blocked"] = c["status"][len("blocked: "):]
            row["unblock"] = c["acquire"]
        rows.append(row)
    gens = next(c for c in data["classes"] if c["id"] == "apple-silicon-generation")
    rows.append({"name": "apple-silicon-generations-recorded", "value": len(gens["recorded_generations"]),
                 "status": "measured", "members": gens["recorded_generations"],
                 "predicate": "distinct `generation` of the [[recorded]] rows (a generation a record binds to a host); "
                              "recorded is not available: each such row is " + BLOCKED})
    for c in data["confirmed"]:
        facts = c["probe"]
        flags = (facts.get("darwin") or facts.get("linux") or {}).get("binary128_flags", [])
        rows.append({"name": f"host.{c['machine']}.binary128-hardware-flags", "value": len(flags), "status": "measured",
                     "members": flags,
                     "predicate": "hw.optional keys (macOS) or common /proc/cpuinfo flags (Linux) matching "
                                  f"`{BINARY128_FLAG.pattern}`: a feature naming a hardware 128-bit binary float format"})
        darwin, linux = facts.get("darwin") or {}, facts.get("linux") or {}
        memory = darwin.get("hw.memsize") if darwin else (linux.get("mem_total_kib") or 0) * 1024
        rows.append({"name": f"host.{c['machine']}.memory-bytes", "value": memory, "status": "measured",
                     "predicate": "sysctl hw.memsize (macOS) or 1024 * /proc/meminfo MemTotal kB (Linux)"})
    rows.append({"name": "scan.occurrences", "value": len(data["occurrences"]), "status": "measured",
                 "predicate": "identities EXTRACTORS find on the lines `git grep -E GREP` matches in the pinned trees"})
    rows.append({"name": "scan.unclassified", "value": data["unclassified"], "status": "measured",
                 "predicate": "occurrences no RULE classifies (must be 0)"})
    return rows


def design_readings(data: dict) -> list[str]:
    builders = [c for c in data["confirmed"] if c["probe"].get("trust_checkout_build_dir")]
    if not builders:
        return ["No confirmed host is the build host (a probe whose Trust checkout holds build/): the readings "
                "of k2 and d8h-oracle need one."]
    out = []
    for host in builders:
        facts = host["probe"]
        darwin = facts.get("darwin") or {}
        rosetta = facts.get("rosetta") or {}
        gib = (darwin.get("hw.memsize") or 0) / 2**30
        out.append(f"k2 `128 GB build host`: the build host {host['machine']} ({host['label']}) has hw.memsize "
                   f"{darwin.get('hw.memsize')} bytes = {gib:g} GiB: " + ("reproduced." if gib == 128 else "NOT reproduced."))
        native_x86 = facts.get("machine") == "x86_64" and darwin.get("sysctl.proc_translated") != 1
        x86 = facts.get("x86isa") or {}
        out.append("d8h-oracle `The only x86 oracle on the current host is Rosetta`: machine "
                   f"{facts.get('machine')} (native x86-64: {'yes' if native_x86 else 'no'}); Rosetta 2 "
                   + ("executes an x86_64 Mach-O" if rosetta.get("executes") else
                      f"does NOT execute one (`{rosetta.get('command')}` exit {rosetta.get('exit')}: "
                      f"{rosetta.get('stderr')!r})")
                   + f"; X86ISA {'present' if x86.get('acl2_on_path') and x86.get('x86isa_books') else 'absent'}. "
                   + ("Reproduced." if rosetta.get("executes") and not native_x86 else
                      "Reproduced only as `Rosetta is the only x86 oracle this host could run`: at measurement no "
                      "x86 oracle executes here, until the owner installs Rosetta 2 (the harness README's own "
                      "first step)."))
    flagged = sum(len((c["probe"].get("darwin") or c["probe"].get("linux") or {}).get("binary128_flags", []))
                  for c in data["confirmed"])
    out.append("e2.1.3-b128/appendix-b `no roster host implements binary128 in hardware [K]`: the confirmed hosts "
               f"show {flagged} hardware binary128 feature flags in total; every recorded host is {BLOCKED}, so the "
               "claim stays [K] for the roster as a whole.")
    return out


def render(data: dict) -> str:
    L = []
    L.append("# E0.12 denominator `hosts`: D0.11, the probe-host roster (E1.6.5 and E2.7.3).")
    L.append("#")
    L.append(f"# GENERATED by {SCRIPT_REL} --write; do not edit.")
    L.append("# Its --check re-measures the scan of the pinned trees, the facts, the design quotes, and the probe of")
    L.append("# the machine it runs on when the record holds one, and fails when anything differs, except")
    L.append("# measured_at_commit and each checkout_head (informational). Probes of other machines are carried.")
    L.append(f"# Design of record: {DESIGN_REL} §5.2 Stage 0.5 (D0.11, exit E0.12).")
    L.append("# A host is CONFIRMED only by the probe run on it; every other host is a [[recorded]] row with status")
    L.append(f"# \"{BLOCKED}\". Nothing here is an estimate.")
    L.append("#")
    L.append("# Readings of the design's claims against this measurement:")
    for reading in design_readings(data):
        L.append("# * " + reading)
    L.append("#")
    L.append("# What must be acquired (or confirmed by a probe), per required class:")
    for c in data["classes"]:
        L.append(f"# * {c['id']} (>= {c['minimum']}, {', '.join(c['exits'])}): confirmed {c['confirmed']}, "
                 f"shortfall {c['shortfall']}. {c['acquire']}")
    L.append("")
    L.append(f"schema = {tq(SCHEMA)}")
    L.append(f"key = {tq(KEY)}")
    L.append('deliverable = "D0.11"')
    L.append(f"design = {tq(DESIGN_REL)}")
    L.append(f"script = {tq(SCRIPT_REL)}")
    L.append('exit = "E0.12"')
    L.extend(multiline("consumers", [
        "E1.6.5 Cfg_t silicon probes: at least two Apple silicon generations and one Linux AArch64 core",
        "E2.7.3 x86-64 silicon differential: at least one Intel and one AMD host, plus Rosetta and the X86ISA emulator",
        "D-8(h) the roster must add native Intel and AMD hosts before E2.7.3 can pass",
        "E2.1.3 hardware float differentials on the roster's AArch64 hosts; binary128 in hardware on no roster host",
        "M0.4 litmus probe run on the roster's hosts",
        "Appendix B row `No roster host implements binary128 in hardware`, verified by D0.11",
    ]))
    L.append("# The pin: the superproject commit whose trees (and whose first-party gitlinks) the scan reads.")
    L.append("# scripts/trust_core/denominators.py re-measures at it (--rev); this script's own --check measures")
    L.append("# at --rev (default HEAD) and ignores this line.")
    L.append(f"measured_at_commit = {tq(data['head'])}")
    L.append("")
    L.append("[inputs.design]")
    L.append(f"path = {tq(DESIGN_REL)}")
    L.append(f"blob = {tq(data['design_blob'])}")
    L.append("quotes = [")
    for q in data["quotes"]:
        L.append(f"  {tq(q)},")
    L.append("]")
    L.append("")
    L.append("[inputs.scan]")
    L.append('what = "the superproject at measured_at_commit outside the upstream directories, and each first-party sibling at its gitlink there, from git objects"')
    L.append(f"excluded_superproject_paths = {tq(list(UPSTREAM_EXCLUDES))}")
    L.append(f"grep = {tq(GREP)}")
    L.append("extractors = [")
    for name, rx, _ in EXTRACTORS:
        L.append(f"  {tq({'name': name, 'regex': rx.pattern})},")
    L.append("]")
    L.append("rules = [")
    for r, p, i, d in RULES:
        L.append(f"  {tq({'repo': r, 'path': p, 'identity': i, 'disposition': d})},")
    L.append("]")
    digest = hashlib.sha256("".join(f"{o[0]}\t{o[1]}\t{o[3]}\n" for o in sorted({(o[0], o[1], o[2], o[3]) for o in data["occurrences"]})).encode()).hexdigest()
    L.append(f'occurrences_digest = "sha256:{digest}"')
    L.append('digest_rule = "sha256 over the sorted distinct lines `<repo>\\t<path>\\t<identity>\\n` of the occurrences"')
    L.append("")
    for name in FIRST_PARTY:
        pin = data["pins"][name]
        L.append(f"[inputs.first-party.{tk(name)}]")
        L.append(f"pin = {tq(pin['pin'])}")
        L.append(f"read = {tq(pin['read'])}")
        L.append(f"checkout_head = {tq(pin['checkout_head'])}")
        L.append("")
    L.append("# The probes the [[confirmed]] rows carry: sha256 of each probe_json (a probe is re-taken only on")
    L.append("# its own machine).")
    L.append("[inputs.probes]")
    L.append("sha256 = " + tq({c["machine"]: "sha256:" + hashlib.sha256(json.dumps(
        _probe_payload(c["probe"]), sort_keys=True, ensure_ascii=False).encode()).hexdigest() for c in data["confirmed"]}))
    L.append("")
    L.append("# ---------------------------------------------------------------------------------------------")
    L.append("# The required host classes.")
    L.append("# ---------------------------------------------------------------------------------------------")
    for c in data["classes"]:
        L.append("")
        L.append("[[class]]")
        for key in ("id", "minimum", "unit", "exits", "also", "design_quotes", "predicate", "confirmed",
                    "confirmed_members", "shortfall", "recorded_generations", "recorded_generations_not_confirmed",
                    "status", "interpretation", "acquire"):
            if key in c:
                L.append(f"{key} = {tq(c[key])}")
        L.extend(multiline("recorded_candidates", c["recorded_candidates"]))
    L.append("")
    L.append("# ---------------------------------------------------------------------------------------------")
    L.append("# CONFIRMED hosts: each is a probe (`hosts.py --probe`) run on that host.")
    L.append("# ---------------------------------------------------------------------------------------------")
    for c in data["confirmed"]:
        facts = c["probe"]
        L.append("")
        L.append("[[confirmed]]")
        L.append(f"machine = {tq(c['machine'])}")
        L.append(f"label = {tq(c['label'])}")
        L.append(f"hostname = {tq(c['hostname'] or '')}")
        L.append(f"status = {tq(c['status'])}")
        L.append(f"classes = {tq({k: v for k, v in facts['classes'].items() if v})}")
        L.append(f"probe_json = {tq(json.dumps(_probe_payload(facts), sort_keys=True, ensure_ascii=False))}")
    L.append("")
    L.append("# ---------------------------------------------------------------------------------------------")
    L.append(f"# RECORDED hosts: the pinned trees mention them; none is probed. Every row: {BLOCKED}.")
    L.append("# `would_satisfy` is what the row would contribute if a probe on it")
    L.append("# agrees; `facts` are quotes re-found verbatim at the pin (line = where); `first_occurrence_per_repo`")
    L.append("# and `files_by_repo` come from the classified scan.")
    L.append("# ---------------------------------------------------------------------------------------------")
    for r in data["rows"]:
        L.append("")
        L.append("[[recorded]]")
        for key in ("id", "status", "target", "cpu", "generation", "generation_source", "would_satisfy",
                    "identities", "files", "files_by_repo"):
            L.append(f"{key} = {tq(r[key])}")
        L.extend(multiline("first_occurrence_per_repo", r["first_occurrence_per_repo"]))
        L.extend(multiline("facts", r["facts"]))
    L.append("")
    L.append("# ---------------------------------------------------------------------------------------------")
    L.append("# Occurrences the rules classify as not a host of this project, by category: (repo, path, identity).")
    L.append("# ---------------------------------------------------------------------------------------------")
    L.append("# digest: sha256 over the sorted distinct lines `<repo>\\t<path>\\t<identity>\\n` of the category.")
    for cat in sorted(data["not_a_host"]):
        items = data["not_a_host"][cat]
        idents = sorted({i[2] for i in items})
        files = sorted({(i[0], i[1]) for i in items})
        digest = hashlib.sha256("".join(f"{r}\t{p}\t{i}\n" for r, p, i in items).encode()).hexdigest()
        L.append("")
        L.append(f"[not_a_host.{tk(cat)}]")
        L.append(f"why = {tq(NOT_A_HOST[cat])}")
        L.append(f"occurrences = {len(items)}")
        L.append(f"files_by_repo = {tq(_count_by_repo(files))}")
        L.append(f"distinct_identities = {len(idents)}")
        if len(idents) <= 40:
            L.append(f"identities = {tq(idents)}")
        else:
            L.append(f"identities_first_40 = {tq(idents[:40])}")
        L.append(f'digest = "sha256:{digest}"')
    L.append("")
    L.append("# ---------------------------------------------------------------------------------------------")
    L.append("# The denominators.")
    L.append("# ---------------------------------------------------------------------------------------------")
    for row in summary_rows(data):
        L.append("")
        L.append("[[row]]")
        for key in ("name", "value", "of", "status", "predicate", "blocked", "unblock", "members"):
            if key in row:
                L.append(f"{key} = {tq(row[key])}")
    return "\n".join(L) + "\n"


def _count_by_repo(files) -> dict:
    order = {n: i for i, n in enumerate(("trust",) + FIRST_PARTY)}
    out: dict = {}
    for repo, _ in sorted(files, key=lambda f: (order[f[0]], f[1])):
        out[repo] = out.get(repo, 0) + 1
    return out


def _probe_payload(facts: dict) -> dict:
    return {k: v for k, v in facts.items() if k != "classes"}


IGNORED = re.compile(r"^(measured_at_commit|checkout_head) = ")


def comparable(text: str) -> str:
    return "\n".join(line for line in text.split("\n") if not IGNORED.match(line))


def recorded_probes(C, record: Path, exclude: str | None) -> list[dict]:
    import tomllib
    try:
        data = tomllib.loads(record.read_text(encoding="utf-8"))
    except (OSError, tomllib.TOMLDecodeError):
        return []
    out = []
    for entry in data.get("confirmed", []):
        facts = json.loads(entry["probe_json"])
        if probe_identity(facts) != exclude:
            out.append(facts)
    return out


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n", 1)[0])
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--probe", action="store_true", help="print this host's probe as JSON and exit (any host)")
    mode.add_argument("--write", action="store_true", help="rewrite the record from this measurement")
    mode.add_argument("--check", action="store_true", help="fail unless the record equals this measurement")
    parser.add_argument("--with-probe", action="append", default=[], type=Path,
                        help="a probe JSON produced by --probe on another host (repeatable; --write only)")
    parser.add_argument("--repo", type=Path, default=Path(__file__).resolve().parents[3])
    parser.add_argument("--rev", default="HEAD", help="the superproject revision whose trees are scanned (default HEAD)")
    parser.add_argument("--record", type=Path, help=f"the record (default {RECORD_REL} in --repo)")
    args = parser.parse_args(argv)

    if args.probe:
        print(json.dumps(probe(), indent=1, sort_keys=True, ensure_ascii=False))
        return 0

    sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
    import common as C  # noqa: E402  (refuses an interpreter older than 3.11)

    record = args.record or args.repo / RECORD_REL
    live = probe()
    live_id = probe_identity(live)
    extra = [json.loads(p.read_text(encoding="utf-8")) for p in args.with_probe]
    for path, facts in zip(args.with_probe, extra):
        if facts.get("schema") != PROBE_SCHEMA:
            print(f"{path}: not a {PROBE_SCHEMA} probe", file=sys.stderr)
            return 2
    carried = recorded_probes(C, record, live_id) if (args.write or args.check) and record.exists() else []
    recorded_here = []
    if args.check and record.exists():
        recorded_here = [f for f in recorded_probes(C, record, None) if probe_identity(f) == live_id]
    use_live = live if not args.check else None
    if recorded_here:
        # This machine's recorded probe stands for it while its roster facts are unchanged: an OS update
        # or a new tool on PATH is a dated observation, not a change to the roster.
        was, now = roster_facts(recorded_here[0]), roster_facts(live)
        changed = sorted(k for k in was if was[k] != now[k])
        if changed:
            for k in changed:
                print(f"ROSTER FACT CHANGED on this host: {k}: recorded {was[k]!r}, probed now {now[k]!r}",
                      file=sys.stderr)
            print(f"RECORD: this host's roster facts changed; re-run `hosts.py --write` and review {RECORD_REL}",
                  file=sys.stderr)
            return 1
        drift = observation_changes(recorded_here[0], live)
        if drift:
            print(f"  this host's probe observations changed since the record (carried, not compared): "
                  f"{', '.join(drift[:12])}{' ...' if len(drift) > 12 else ''}")
        use_live = recorded_here[0]
    try:
        data = measure(C, args.repo, use_live, extra, carried, args.rev)
    except Fatal as error:
        print(f"FATAL: {error}", file=sys.stderr)
        return 2
    text = render(data)

    here = next((c for c in data["confirmed"] if c["measured_here"]), None)
    print(f"D0.11 probe-host roster at {data['head'][:12]}")
    if here:
        print(f"  this host (measured): {here['label']}; classes "
              f"{ {k: v for k, v in here['probe']['classes'].items() if v} }")
    elif args.check:
        print(f"  this host ({probe_label(live)}) has no probe in the record: its probe is not compared")
    for c in data["classes"]:
        print(f"  {c['id']:26s} minimum {c['minimum']}  confirmed {c['confirmed']} {c['confirmed_members']}  "
              f"shortfall {c['shortfall']}  recorded candidates {c['recorded_candidates']}")
    print(f"  recorded hosts ({BLOCKED}): {len(data['rows'])}: {', '.join(r['id'] for r in data['rows'])}")
    print(f"  scan: {len(data['occurrences'])} occurrences, {data['unclassified']} unclassified")
    for reading in design_readings(data):
        print("  design: " + reading)
    for finding in data["findings"]:
        print("FINDING " + finding)

    status = 1 if data["findings"] else 0
    if args.write:
        record.parent.mkdir(parents=True, exist_ok=True)
        record.write_text(text, encoding="utf-8")
        print(f"wrote {RECORD_REL}")
    elif args.check:
        if not record.exists():
            print(f"RECORD: {RECORD_REL} is missing; run --write")
            return 1
        if comparable(record.read_text(encoding="utf-8")) != comparable(text):
            print(f"RECORD: {RECORD_REL} differs from a re-measurement at {data['head'][:12]}; re-run with --write and review the diff")
            return 1
        print(f"{RECORD_REL} matches the re-measurement")
    return status


if __name__ == "__main__":
    sys.exit(main())
