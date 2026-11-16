#!/usr/bin/env python3
"""Trust's one host-scaling helper: measure the machine NOW, derive job counts,
per-child memory caps and admission from what it measured, and say so.

WHY ONE HELPER. Before 2026-10-14 every lane sized itself with its own constant,
each picked for one host: `.cargo/config.toml` `jobs = 4` (the 128 GiB Spark),
scripts/hooks/pre-push's overlap rule (>= 64 GiB and >= 12 CPUs, of TOTAL
memory), scripts/check_crates_tests_scoped.py's one binary per 16 GiB of TOTAL
memory, scripts/build-mem-governor.sh's 6 / 12 GiB floors and ~5 GiB per job,
and the train runbooks' `-j 4` / CARGO_BUILD_JOBS=4. A 24 GiB laptop and a
128 GiB host got the same numbers, and none of them looked at memory a
neighbour was already using. docs/LANDING_GATE.md lists them all.

WHAT IT READS, every call (never cached):
  * logical CPUs online (`hw.ncpu` on macOS, sched_getaffinity / cpu_count on
    Linux);
  * physical RAM (`hw.memsize`; MemTotal);
  * memory available RIGHT NOW: on macOS vm_stat's free + speculative +
    inactive + purgeable pages times its page size (the reading ay's
    scripts/_oom_guard.py and scripts/build-mem-governor.sh take); on Linux
    /proc/meminfo MemAvailable;
  * the 1-minute load average (logged; it does not size anything, see below).
A reading that fails raises HostUnmeasurable: a caller that cannot measure the
host does not guess one (fail closed: nothing is admitted).

WHAT IT DERIVES, for one kind of child (KINDS below):
  reserve = max(1 GiB, physical / 8)   room left for neighbours to GROW after the
                                       reading (proportional, never a GiB figure
                                       sized for one host)
  room    = available - reserve
  jobs    = min(cpus, admitted_cpu_share, floor(room / want), max_jobs), at least 1
  cap     = floor(room / jobs)         the per-child memory each child may use
  REFUSED only when room < floor: not even one child of this kind fits.
So jobs * cap <= room < available always (scripts/tests/land_gate_test.py holds
it, with a mutant that oversubscribes). On a busy host the jobs shrink toward 1
and the cap stays >= want; between floor and want one child runs with the whole
room. The existing pressure watch (scripts/build-mem-governor.sh) stays the
backstop for growth after admission: its floors are derived here too
(`governor` below).

BUILD-SLOT ADMISSION. Inside BUILD_SLOT_HELD=1, CARGO_BUILD_JOBS is the
positive CPU share already admitted by the machine-wide gate, and bounds
EVERY child plan in addition to measured CPUs and memory. Missing or malformed
share data refuses; unmanaged callers keep the ordinary measured-host plan.
Concurrent heavy pre-push lanes are serialized inside one admission: giving
each the same share would spend it twice.

WHY LOAD DOES NOT SIZE JOBS. CPU oversubscription slows a build; it does not
kill it, and the load average lags by a minute and counts this run's own
children once they start. Memory is what kills a build (an OOM SIGKILL loses the
run), and available memory already reflects every neighbour. Timing-sensitive
test pools keep their own measured ceilings (check_crates_tests_scoped.py's
MAX_DEFAULT_JOBS) on top of what this returns.

THE KINDS. `want` and `floor` are properties of the WORKLOAD (how much one
child of that kind uses), not of a host; each cites where its number comes
from. Override one with TRUST_HOST_<KIND>_WANT_GIB / _FLOOR_GIB (KIND upper-case,
`-` as `_`); the log line says when an override was used.

CLI:
  host_budget.py measure                 one JSON object: the measurement
  host_budget.py plan KIND [--max N]     JSON plan; exit 0 admitted, 3 refused
  host_budget.py jobs KIND [--max N]     just the job count (exit 3 refused)
  host_budget.py admit-overlap           exit 0 when the pre-push overlap fits
  host_budget.py governor                the pressure watch's floors (shell vars)
Every subcommand prints one `host-budget:` line to stderr saying what it
measured and what it chose.

Python 3.9 compatible on purpose: scripts/hooks/pre-push and the harness rows
run bare `python3`, which is 3.9 on a stock macOS.

Author: Andrew Yates <andrewyates.name@gmail.com>
Copyright 2026 Andrew Yates | License: Apache-2.0 OR MIT
"""
import json
import math
import os
import platform
import re
import subprocess
import sys
import typing

GIB = 1024 ** 3


class HostUnmeasurable(RuntimeError):
    """The host's CPUs or memory could not be read; nothing is admitted."""


class AdmissionInvalid(HostUnmeasurable):
    """A managed job lost its positive build-slot CPU share; do not fall back."""


def admitted_jobs(env: typing.Optional[typing.Mapping[str, str]] = None) -> typing.Optional[int]:
    """The already-admitted CPU share, or None for an unmanaged caller."""
    caller = os.environ if env is None else env
    if caller.get("BUILD_SLOT_HELD") != "1":
        return None
    raw = caller.get("CARGO_BUILD_JOBS", "")
    if not re.fullmatch(r"[0-9]+", raw):
        raise AdmissionInvalid("BUILD_SLOT_HELD=1 requires positive integer CARGO_BUILD_JOBS")
    try:
        jobs = int(raw)
    except ValueError:
        raise AdmissionInvalid("CARGO_BUILD_JOBS is too large to parse") from None
    if jobs < 1:
        raise AdmissionInvalid("BUILD_SLOT_HELD=1 requires positive integer CARGO_BUILD_JOBS")
    return jobs


class Host(typing.NamedTuple):
    os: str
    cpus: int
    mem_total: int
    mem_avail: int
    avail_source: str
    load1: float


class Plan(typing.NamedTuple):
    kind: str
    jobs: int
    cap: int
    want: int
    floor: int
    reserve: int
    room: int
    cpu_bound: int
    mem_bound: int
    refused: typing.Optional[str]
    overrides: typing.Tuple[str, ...]

    @property
    def admitted(self) -> bool:
        return self.refused is None


# want/floor in GiB per child. Sources:
#  rustc-build   x.py build/check and cargo builds. build.sh and
#                scripts/build-mem-governor.sh budget ~5 GiB per rustc job for a
#                full compiler build; most compiler crates check in well under
#                that, and the train runbooks ran -j 4 inside ~10 GiB of free
#                memory without an OOM (docs/first-party-pin-ledger.md, train
#                E1: "-j 4 on a 14-core, 24 GiB host shared with three other
#                chains"), i.e. ~2.5 GiB per job held. want 2.5, floor 1.5.
#  ui-test       one compiletest child: a trustc on one small file plus its
#                verifier. want 1, floor 0.5 (the stage-1 trustc of a ui test
#                stays under ~0.5 GiB in KNOWN_HAZARDS' measured runs; the
#                verifier's solver can double it).
#  crates-test   one libtest binary of crates/ (it runs its tests on every
#                core). check_crates_tests_scoped.py sized these at one per
#                16 GiB of memory; kept as want, read against AVAILABLE memory
#                now instead of total. floor 2.
#  fast-lane     one push-profile `fast.*` row: a python or bash check over the
#                tree. want 0.5, floor 0.25.
KINDS = {
    "rustc-build": (2.5, 1.5),
    "ui-test": (1.0, 0.5),
    "crates-test": (16.0, 2.0),
    "fast-lane": (0.5, 0.25),
}


def _run(argv: typing.Sequence[str]) -> str:
    try:
        return subprocess.run(list(argv), capture_output=True, text=True, check=True).stdout
    except (OSError, subprocess.CalledProcessError) as exc:
        raise HostUnmeasurable(f"`{' '.join(argv)}` failed: {exc}") from None


def _positive_int(text: str, what: str) -> int:
    try:
        value = int(str(text).strip())
    except ValueError:
        raise HostUnmeasurable(f"{what} is not an integer: {text!r}") from None
    if value <= 0:
        raise HostUnmeasurable(f"{what} is not positive: {value}")
    return value


def parse_vm_stat(text: str) -> typing.Tuple[int, str]:
    """macOS available bytes from `vm_stat` output: (free + speculative +
    inactive + purgeable) pages times the page size its header states."""
    m = re.search(r"page size of (\d+) bytes", text)
    if not m:
        raise HostUnmeasurable("vm_stat printed no page size")
    page = int(m.group(1))
    pages = {}
    for key in ("free", "speculative", "inactive", "purgeable"):
        mm = re.search(r"^Pages %s:\s+(\d+)\.?\s*$" % key, text, re.M)
        if not mm:
            raise HostUnmeasurable(f"vm_stat printed no 'Pages {key}' line")
        pages[key] = int(mm.group(1))
    return sum(pages.values()) * page, "vm_stat free+speculative+inactive+purgeable"


def parse_meminfo(text: str) -> typing.Tuple[int, int]:
    """Linux (MemTotal, MemAvailable) bytes from /proc/meminfo."""
    vals = {}
    for line in text.splitlines():
        m = re.match(r"^(MemTotal|MemAvailable):\s+(\d+)\s+kB", line)
        if m:
            vals[m.group(1)] = int(m.group(2)) * 1024
    if "MemTotal" not in vals or "MemAvailable" not in vals:
        raise HostUnmeasurable("/proc/meminfo has no MemTotal/MemAvailable")
    return vals["MemTotal"], vals["MemAvailable"]


def measure() -> Host:
    """Read the host now. Raises HostUnmeasurable rather than guessing."""
    system = platform.system()
    try:
        load1 = os.getloadavg()[0]
    except (OSError, AttributeError):
        load1 = float("nan")
    if system == "Darwin":
        cpus = _positive_int(_run(["sysctl", "-n", "hw.ncpu"]), "hw.ncpu")
        total = _positive_int(_run(["sysctl", "-n", "hw.memsize"]), "hw.memsize")
        avail, source = parse_vm_stat(_run(["vm_stat"]))
    elif system == "Linux":
        try:
            cpus = len(os.sched_getaffinity(0))  # type: ignore[attr-defined]
        except (AttributeError, OSError):
            cpus = os.cpu_count() or 0
        cpus = _positive_int(str(cpus), "CPU count")
        try:
            with open("/proc/meminfo", encoding="ascii") as fh:
                total, avail = parse_meminfo(fh.read())
        except OSError as exc:
            raise HostUnmeasurable(f"cannot read /proc/meminfo: {exc}") from None
        source = "/proc/meminfo MemAvailable"
    else:
        raise HostUnmeasurable(f"no memory reading for {system!r}")
    # A nested gate must retain the machine-wide admission share. Otherwise
    # rescaling x.py to every physical CPU undoes build-slot's scheduling.
    share = admitted_jobs()
    if share is not None:
        admitted = min(cpus, share)
        source += f"; build-slot CPU share {admitted}/{cpus}"
        cpus = admitted
    if avail > total:
        avail = total
    return Host(system, cpus, total, max(0, avail), source, load1)


def _gib(env_key: str, default: float, overrides: typing.List[str]) -> int:
    raw = os.environ.get(env_key)
    if raw is None or raw == "":
        return int(default * GIB)
    try:
        value = float(raw)
    except ValueError:
        raise ValueError(f"{env_key}={raw!r} is not a number of GiB") from None
    if not value > 0:
        raise ValueError(f"{env_key}={raw!r} must be positive")
    overrides.append(f"{env_key}={raw}")
    return int(value * GIB)


def reserve_for(host: Host) -> int:
    """Room kept for neighbours to grow after the reading: an eighth of physical
    memory, at least 1 GiB. Proportional, so a 24 GiB and a 128 GiB host each
    keep their own share."""
    return max(GIB, host.mem_total // 8)


def plan(host: Host, kind: str, max_jobs: typing.Optional[int] = None) -> Plan:
    """Jobs and per-child cap for `kind` on `host`, sized into the measured room."""
    if kind not in KINDS:
        raise ValueError(f"unknown kind {kind!r} (known: {', '.join(sorted(KINDS))})")
    if max_jobs is not None and max_jobs < 1:
        raise ValueError("max_jobs must be at least 1")
    want_d, floor_d = KINDS[kind]
    key = "TRUST_HOST_" + kind.upper().replace("-", "_")
    overrides: typing.List[str] = []
    want = _gib(key + "_WANT_GIB", want_d, overrides)
    floor = _gib(key + "_FLOOR_GIB", floor_d, overrides)
    if floor > want:
        floor = want
    reserve = reserve_for(host)
    room = host.mem_avail - reserve
    admitted = admitted_jobs()
    cpu_bound = min(host.cpus, admitted) if admitted is not None else host.cpus
    if admitted is not None:
        overrides.append(f"build-slot CARGO_BUILD_JOBS={admitted}")
    mem_bound = room // want if room > 0 else 0
    if room < floor:
        return Plan(kind, 0, 0, want, floor, reserve, max(room, 0), cpu_bound, int(mem_bound),
                    f"not even one {kind} child fits: {fmt(host.mem_avail)} available "
                    f"- {fmt(reserve)} reserve = {fmt(max(room, 0))} room < {fmt(floor)} floor",
                    tuple(overrides))
    jobs = max(1, min(cpu_bound, int(mem_bound)))
    if max_jobs is not None:
        jobs = min(jobs, max_jobs)
    cap = room // jobs
    return Plan(kind, jobs, cap, want, floor, reserve, room, cpu_bound, int(mem_bound), None,
                tuple(overrides))


def admit_overlap(host: Host) -> typing.Tuple[bool, str]:
    """May scripts/hooks/pre-push overlap the crates-tests build with the
    compiler check? Both are rustc builds; overlap is admitted when the room
    holds a full CPU's worth of rustc-build children at `want` (each build then
    has half the cores' worth), so the two together never plan past the room.
    Replaces the fixed ">= 64 GiB and >= 12 CPUs of TOTAL memory" rule."""
    p = plan(host, "rustc-build")
    if admitted_jobs() is not None:
        return False, "build-slot CPU share belongs to one heavy lane at a time"
    need = host.cpus * p.want
    if p.refused:
        return False, p.refused
    if p.room < need:
        return False, (f"room {fmt(p.room)} < {host.cpus} CPUs x {fmt(p.want)} per rustc job "
                       f"= {fmt(need)} for two concurrent builds")
    return True, (f"room {fmt(p.room)} >= {host.cpus} CPUs x {fmt(p.want)} per rustc job "
                  f"= {fmt(need)} for two concurrent builds")


def governor_floors(host: Host) -> typing.Tuple[int, int]:
    """scripts/build-mem-governor.sh's pause / resume floors, in GiB: pause the
    heaviest child below a sixteenth of physical memory (at least 1 GiB),
    resume above twice that. Was a fixed 6 / 12 GiB: a quarter of a 24 GiB
    host, and under five percent of a 128 GiB one."""
    crit = max(GIB, host.mem_total // 16)
    return int(math.ceil(crit / GIB)), int(math.ceil(2 * crit / GIB))


def fmt(n: int) -> str:
    return f"{n / GIB:.1f} GiB"


def describe(host: Host) -> str:
    load = "n/a" if host.load1 != host.load1 else f"{host.load1:.1f}"
    return (f"{host.os} {host.cpus} CPUs, {fmt(host.mem_total)} physical, "
            f"{fmt(host.mem_avail)} available now ({host.avail_source}), load1 {load}")


def describe_plan(host: Host, p: Plan) -> str:
    head = f"host-budget: {describe(host)}; {p.kind}"
    tail = f" [overrides: {', '.join(p.overrides)}]" if p.overrides else ""
    if p.refused:
        return f"{head}: REFUSED — {p.refused}{tail}"
    return (f"{head}: want {fmt(p.want)}/child (floor {fmt(p.floor)}), reserve {fmt(p.reserve)}, "
            f"room {fmt(p.room)} -> jobs {p.jobs} (cpu bound {p.cpu_bound}, memory bound "
            f"{p.mem_bound}), cap {fmt(p.cap)}/child{tail}")


def _plan_json(host: Host, p: Plan) -> dict:
    return {
        "host": host._asdict(),
        "kind": p.kind, "jobs": p.jobs, "cap_bytes": p.cap, "want_bytes": p.want,
        "floor_bytes": p.floor, "reserve_bytes": p.reserve, "room_bytes": p.room,
        "cpu_bound": p.cpu_bound, "mem_bound": p.mem_bound, "refused": p.refused,
        "overrides": list(p.overrides),
    }


def main(argv: typing.Optional[typing.Sequence[str]] = None) -> int:
    args = list(sys.argv[1:] if argv is None else argv)
    if not args or args[0] in ("-h", "--help"):
        print(__doc__)
        return 0
    cmd, rest = args[0], args[1:]
    max_jobs = None
    if "--max" in rest:
        i = rest.index("--max")
        try:
            max_jobs = int(rest[i + 1])
        except (IndexError, ValueError):
            print("host-budget: --max needs a whole number", file=sys.stderr)
            return 2
        del rest[i:i + 2]
    try:
        host = measure()
    except HostUnmeasurable as exc:
        print(f"host-budget: CANNOT MEASURE this host ({exc}); nothing is admitted", file=sys.stderr)
        return 3
    try:
        if cmd == "measure":
            print(f"host-budget: {describe(host)}", file=sys.stderr)
            print(json.dumps(host._asdict()))
            return 0
        if cmd in ("plan", "jobs"):
            if len(rest) != 1:
                print(f"host-budget: {cmd} needs exactly one KIND", file=sys.stderr)
                return 2
            p = plan(host, rest[0], max_jobs)
            print(describe_plan(host, p), file=sys.stderr)
            print(json.dumps(_plan_json(host, p)) if cmd == "plan" else p.jobs)
            return 0 if p.admitted else 3
        if cmd == "admit-overlap":
            ok, why = admit_overlap(host)
            print(f"host-budget: {describe(host)}; overlap {'ADMITTED' if ok else 'NOT admitted'}: {why}",
                  file=sys.stderr)
            print(why)
            return 0 if ok else 1
        if cmd == "governor":
            crit, resume = governor_floors(host)
            print(f"host-budget: {describe(host)}; governor pause < {crit} GiB, resume >= {resume} GiB",
                  file=sys.stderr)
            print(f"TRUST_GOV_CRITICAL_GIB={crit}\nTRUST_GOV_RESUME_GIB={resume}")
            return 0
    except HostUnmeasurable as exc:
        print(f"host-budget: REFUSED — {exc}; nothing is admitted", file=sys.stderr)
        return 3
    except ValueError as exc:
        print(f"host-budget: {exc}", file=sys.stderr)
        return 2
    print(f"host-budget: unknown subcommand {cmd!r}", file=sys.stderr)
    return 2


if __name__ == "__main__":
    sys.exit(main())
