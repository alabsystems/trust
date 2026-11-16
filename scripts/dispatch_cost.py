#!/usr/bin/env python3
"""dispatch-cost: the fixed cost of one GPU dispatch on Apple silicon.

    python3 scripts/dispatch_cost.py            # build the probe, run it, print the row
    python3 scripts/dispatch_cost.py --json     # the same numbers as one JSON object

The row is docs/STATUS.md "Dispatch cost". The probe (scripts/dispatch-cost, built
with `targo --unverified`) hands Metal a kernel that does one store into a shared
buffer, waits, and checks that the CPU sees the store. It prints every sample;
this file owns the statistics, so they are tested without a GPU
(scripts/tests/dispatch_cost_test.py).

What the row says, per call, in nanoseconds of the raw uptime clock:

  round trip      call to return, the call's Metal objects released
  visible         call until the CPU has read the kernel's store
  on the GPU      the command buffer's own GPU start-to-end time, as the 10th
                  percentile, median and 90th: it moves with the GPU's power
                  state from run to run and is not one figure
  wake-up penalty the median round trip of the first dispatch after an idle gap,
                  minus the back-to-back median. `sleep`: the calling thread
                  slept for the gap, so its core and the GPU both went idle.
                  `spin`: the thread spun, so only the GPU went idle; the
                  difference is the sleeping thread's cost, not the device's.

It is a floor: an empty kernel, one thread, one queue, a synchronous wait. It is
a measurement of one machine at one moment and no input to any verdict. The load
average is read when sampling starts and again when it ends. One run at a time:
a second dispatch-cost on the machine is refused. What other processes do with
the GPU meanwhile is not observed.

Exit status: 0 the row was printed; 1 the probe or its build failed (a Mac whose
Metal device cannot be set up is this), its output is not what the probe prints,
or `--keep-samples` could not be written (the row is still printed); 2 this host
or these arguments cannot produce the row.
"""
from __future__ import annotations

import argparse
import contextlib
import fcntl
import json
import math
import os
import platform
import re
import subprocess
import sys
import tempfile
from pathlib import Path
from typing import Dict, List, Optional, Sequence, Tuple

ROOT = Path(__file__).resolve().parents[1]
MANIFEST = ROOT / "scripts" / "dispatch-cost" / "Cargo.toml"
# The 99.9th percentile of fewer samples than this is the maximum under another name.
MIN_TAIL_SAMPLES = 1000
TARGET_DIR_VARIABLES = ("CARGO_TARGET_DIR", "CARGO_BUILD_TARGET_DIR", "TARGO_TARGET_DIR")
HEADER_KEYS = ("device", "unified", "qos", "warm")
# What the probe prints, and nothing wider: ASCII decimal, no sign, no padding.
NUMBER = re.compile(r"0|[1-9][0-9]*")
QOS = ("user-interactive", "default")
# The probe's series prefix -> what the calling thread did during the gap.
IDLE_KINDS = {"idle": "sleep", "spin": "spin"}
SERIES = re.compile(r"hot|(idle|spin)(0|[1-9][0-9]*)")
# The probe's counts are u32, and it multiplies a gap by 1e6 in u64.
MAX_COUNT = 2**32 - 1
MAX_GAP_MS = 3_600_000
# The probe leaves with this status only from its usage message.
PROBE_USAGE_STATUS = 2


class Refused(Exception):
    """This host or these arguments cannot produce the row (exit 2)."""


class Malformed(Exception):
    """The probe failed, or its output is not what the probe prints (exit 1)."""


def percentile(ordered: Sequence[int], fraction: float) -> int:
    """Nearest rank: the smallest sample with at least `fraction` of the
    samples at or below it. `ordered` is sorted ascending and not empty."""
    if not ordered:
        raise ValueError("no samples")
    if not 0.0 < fraction <= 1.0:
        raise ValueError(f"fraction {fraction} is outside (0, 1]")
    return ordered[max(1, math.ceil(fraction * len(ordered))) - 1]


def median(ordered: Sequence[int]) -> int:
    return percentile(ordered, 0.5)


def parse(text: str) -> Tuple[Dict[str, str], Dict[str, List[Tuple[int, int, int]]]]:
    """The probe's header fields and its samples by series, in printed order."""
    header: Dict[str, str] = {}
    series: Dict[str, List[Tuple[int, int, int]]] = {}
    for number, line in enumerate(text.splitlines(), 1):
        if not line.strip():
            continue
        word, _, rest = line.partition(" ")
        if word == "S":
            fields = rest.split(" ")
            if len(fields) != 4:
                raise Malformed(f"line {number}: a sample has a series and three numbers: {line!r}")
            if not SERIES.fullmatch(fields[0]):
                raise Malformed(f"line {number}: not a series the probe prints: {fields[0]!r}")
            if not all(NUMBER.fullmatch(field) for field in fields[1:]):
                raise Malformed(f"line {number}: a sample's numbers are decimal integers: {line!r}")
            call, visible, gpu = (int(field) for field in fields[1:])
            if visible > call:
                raise Malformed(f"line {number}: visible <= round trip does not hold: {line!r}")
            series.setdefault(fields[0], []).append((call, visible, gpu))
        elif word in HEADER_KEYS:
            if word in header:
                raise Malformed(f"line {number}: `{word}` is stated twice")
            header[word] = rest
        else:
            raise Malformed(f"line {number}: not a line the probe prints: {line!r}")
    missing = [key for key in HEADER_KEYS if key not in header]
    if missing:
        raise Malformed("the probe did not state: " + ", ".join(missing))
    if header["unified"] not in ("0", "1"):
        raise Malformed(f"`unified` is 0 or 1, not {header['unified']!r}")
    if header["qos"] not in QOS:
        raise Malformed(f"`qos` is one of {', '.join(QOS)}, not {header['qos']!r}")
    if not NUMBER.fullmatch(header["warm"]):
        raise Malformed(f"`warm` is a count, not {header['warm']!r}")
    return header, series


def idle_gap(name: str) -> Optional[Tuple[str, int]]:
    """`idle<ms>` -> ("sleep", ms); `spin<ms>` -> ("spin", ms); `hot` -> None."""
    match = SERIES.fullmatch(name)
    if match is None or match.group(1) is None:
        return None
    return IDLE_KINDS[match.group(1)], int(match.group(2))


def summarize(header: Dict[str, str], series: Dict[str, List[Tuple[int, int, int]]]) -> dict:
    if header["unified"] != "1":
        raise Refused(f"{header['device']} has no unified memory; the row is about unified memory")
    hot = series.get("hot", [])
    if len(hot) < MIN_TAIL_SAMPLES:
        raise Refused(f"{len(hot)} back-to-back samples; the 99.9th percentile needs at least "
                      f"{MIN_TAIL_SAMPLES}")
    calls = sorted(sample[0] for sample in hot)
    on_gpu = sorted(sample[2] for sample in hot)
    hot_median = median(calls)
    gaps = []
    named = {idle_gap(name): name for name in series if idle_gap(name) is not None}
    for kind, gap in sorted(named):
        after = sorted(sample[0] for sample in series[named[(kind, gap)]])
        gaps.append({
            "thread": kind,
            "idle_ms": gap,
            "samples": len(after),
            "median_ns": median(after),
            "max_ns": after[-1],
            "penalty_ns": median(after) - hot_median,
        })
    return {
        "device": header["device"],
        "unified_memory": True,
        "qos": header["qos"],
        "warm_up": int(header["warm"]),
        "samples": len(hot),
        "round_trip_ns": {
            "median": hot_median,
            "p99_9": percentile(calls, 0.999),
            "max": calls[-1],
            "min": calls[0],
        },
        "visible_median_ns": median(sorted(sample[1] for sample in hot)),
        "gpu_ns": {
            "p10": percentile(on_gpu, 0.1),
            "median": median(on_gpu),
            "p90": percentile(on_gpu, 0.9),
        },
        "wake_up": gaps,
    }


def duration(ns: int) -> str:
    sign = "-" if ns < 0 else ""
    ns = abs(ns)
    if ns < 1_000:
        return f"{sign}{ns} ns"
    if ns < 1_000_000:
        return f"{sign}{ns / 1_000:.1f} us"
    if ns < 1_000_000_000:
        return f"{sign}{ns / 1_000_000:.2f} ms"
    return f"{sign}{ns / 1_000_000_000:.2f} s"


def render(summary: dict, host: Dict[str, str]) -> str:
    trip = summary["round_trip_ns"]
    where = ", ".join(f"{key} {value}" for key, value in host.items())
    lines = [
        f"dispatch-cost: {summary['device']}, Metal, unified memory"
        + (f" ({where})" if where else ""),
        f"  {summary['samples']} back-to-back dispatches of an empty kernel after "
        f"{summary['warm_up']} warm-up, thread QoS {summary['qos']}",
        f"  round trip          median {duration(trip['median'])}   "
        f"99.9th {duration(trip['p99_9'])}   max {duration(trip['max'])}   "
        f"min {duration(trip['min'])}",
        f"  result visible      median {duration(summary['visible_median_ns'])}",
        f"  on the GPU          10th {duration(summary['gpu_ns']['p10'])}   "
        f"median {duration(summary['gpu_ns']['median'])}   "
        f"90th {duration(summary['gpu_ns']['p90'])}   (moves with the GPU's power state)",
    ]
    if summary["wake_up"]:
        lines.append("  wake-up penalty: first dispatch after an idle gap, median over the "
                     "back-to-back median")
        for gap in summary["wake_up"]:
            penalty = gap["penalty_ns"]
            lines.append(
                f"    {gap['thread']:<5} {gap['idle_ms']:>5} ms   "
                f"{'+' if penalty >= 0 else ''}{duration(penalty)}"
                f"   (median {duration(gap['median_ns'])}, max {duration(gap['max_ns'])}, "
                f"n={gap['samples']})")
    else:
        lines.append("  wake-up penalty: not measured (no sample follows an idle gap)")
    return "\n".join(lines)


def ask(*command: str) -> str:
    """A host command's output, or nothing when the host does not answer."""
    try:
        done = subprocess.run(command, stdin=subprocess.DEVNULL, capture_output=True,
                              text=True, errors="replace", timeout=20)
    except (OSError, subprocess.SubprocessError):
        return ""
    return done.stdout.strip() if done.returncode == 0 else ""


def read_load() -> str:
    try:
        return f"{os.getloadavg()[0]:.1f}"
    except OSError:
        return ""


def read_host() -> Dict[str, str]:
    """What the row's reader needs to know about the machine, read when
    sampling starts. Each field is left out when the host does not answer."""
    host: Dict[str, str] = {}
    model = ask("sysctl", "-n", "hw.model")
    if model:
        host["model"] = model
    release = platform.mac_ver()[0]
    if release:
        host["macOS"] = release
    power = ask("pmset", "-g", "batt").splitlines()
    if power:
        host["power"] = "AC" if "AC Power" in power[0] else "battery" if "Battery" in power[0] else "?"
    load = read_load()
    if load:
        host["load"] = load
    return host


@contextlib.contextmanager
def only_run():
    """One dispatch-cost at a time on this machine: two would share the GPU
    queue and, with one target directory, replace each other's probe."""
    path = os.path.join(tempfile.gettempdir(), "trust-dispatch-cost.lock")
    try:
        handle = open(path, "a")
    except OSError as error:
        raise Refused(f"the run lock {path} cannot be opened: {error}") from None
    with handle:
        try:
            fcntl.flock(handle, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except OSError:
            raise Refused(f"another dispatch-cost is running on this machine ({path} is held)") from None
        yield


def targo_command(targo: str, verb: str) -> List[str]:
    return [targo, "--unverified", verb, "--release", "--locked", "--quiet",
            "--manifest-path", str(MANIFEST)]


def probe_arguments(plan: argparse.Namespace) -> List[str]:
    return ["--warm", str(plan.warm), "--hot", str(plan.hot),
            "--idle-ms", ",".join(str(gap) for gap in plan.idle_ms),
            "--idle-reps", str(plan.idle_reps), "--spin", "0" if plan.no_spin else "1"]


def run_probe(targo: str, plan: argparse.Namespace) -> Tuple[Dict[str, str], str]:
    """Builds the probe, reads the host, then samples: (host, probe output)."""
    if sys.platform != "darwin" or platform.machine() != "arm64":
        raise Refused(f"Metal on Apple silicon is the only device measured so far; this host is "
                      f"{sys.platform} {platform.machine()}")
    env = dict(os.environ)
    if not any(env.get(name) for name in TARGET_DIR_VARIABLES):
        # atpkg's targo refuses the target `.cargo/config.toml` names and takes
        # the same directory from the environment, by its real path.
        env["CARGO_TARGET_DIR"] = os.path.realpath(ROOT / "crates" / "target")

    def targo_run(command: List[str]) -> subprocess.CompletedProcess:
        try:
            return subprocess.run(command, cwd=ROOT, env=env, stdin=subprocess.DEVNULL,
                                  capture_output=True, text=True, errors="replace")
        except OSError as error:
            raise Refused(f"`{targo}` did not start: {error}") from None

    def tail(done: subprocess.CompletedProcess) -> str:
        return "\n".join(done.stderr.strip().splitlines()[-12:])

    with only_run():
        built = targo_run(targo_command(targo, "build"))
        if built.returncode != 0:
            raise Malformed(f"`targo build` of the probe exited {built.returncode}:\n{tail(built)}")
        # The probe is built: what is read now is the machine sampling starts on.
        host = read_host()
        done = targo_run(targo_command(targo, "run") + ["--"] + probe_arguments(plan))
        after = read_load()
    if done.returncode == PROBE_USAGE_STATUS:
        raise Refused(f"the probe does not take these arguments:\n{tail(done)}")
    if done.returncode != 0:
        raise Malformed(f"`targo run` of the probe exited {done.returncode}:\n{tail(done)}")
    if host.get("load") and after:
        host["load"] = f"{host['load']} -> {after}"
    return host, done.stdout


def gaps(text: str) -> List[int]:
    try:
        values = [int(part) for part in text.split(",") if part]
    except ValueError:
        raise argparse.ArgumentTypeError(f"not a list of milliseconds: {text!r}") from None
    if any(not 0 <= value <= MAX_GAP_MS for value in values) or len(set(values)) != len(values):
        raise argparse.ArgumentTypeError(
            f"idle gaps are distinct, not negative and at most {MAX_GAP_MS} ms: {text!r}")
    return values


def count(text: str) -> int:
    try:
        value = int(text)
    except ValueError:
        raise argparse.ArgumentTypeError(f"not a count: {text!r}") from None
    if not 0 <= value <= MAX_COUNT:
        raise argparse.ArgumentTypeError(f"a count is from 0 to {MAX_COUNT}: {text!r}")
    return value


def main(argv: Optional[Sequence[str]] = None) -> int:
    parser = argparse.ArgumentParser(
        prog="dispatch-cost",
        description="The fixed cost of one GPU dispatch on Apple silicon unified memory.")
    parser.add_argument("--hot", type=count, default=20000,
                        help="back-to-back dispatches measured (default 20000)")
    parser.add_argument("--warm", type=count, default=2000,
                        help="dispatches before the first measured one (default 2000)")
    parser.add_argument("--idle-ms", type=gaps, default=[1, 10, 100, 1000],
                        help="idle gaps, in ms, for the wake-up penalty (default 1,10,100,1000)")
    parser.add_argument("--idle-reps", type=count, default=50,
                        help="dispatches measured after each idle gap (default 50)")
    parser.add_argument("--no-spin", action="store_true",
                        help="measure only the gaps the thread sleeps through")
    parser.add_argument("--targo", default="targo", help="the targo to build the probe with")
    parser.add_argument("--samples", metavar="FILE",
                        help="summarize probe output saved earlier instead of running the probe")
    parser.add_argument("--keep-samples", metavar="FILE",
                        help="also write the probe's output to FILE")
    parser.add_argument("--json", action="store_true", help="print one JSON object")
    plan = parser.parse_args(argv)
    unwritten = ""
    try:
        if plan.samples:
            try:
                text = Path(plan.samples).read_text(encoding="utf-8")
            except UnicodeDecodeError as error:
                raise Malformed(f"{plan.samples} is not UTF-8: {error}") from None
            host: Dict[str, str] = {}
        else:
            if plan.hot < MIN_TAIL_SAMPLES and not plan.keep_samples:
                raise Refused(f"{plan.hot} back-to-back samples; the 99.9th percentile needs at "
                              f"least {MIN_TAIL_SAMPLES}")
            if plan.keep_samples:
                keep = Path(plan.keep_samples)
                if keep.is_dir() or not os.access(keep.parent, os.W_OK):
                    raise Refused(f"--keep-samples {plan.keep_samples} cannot be written")
            targo = plan.targo
            if os.sep in targo or (os.altsep and os.altsep in targo):
                # A path is the caller's, not the repo root's the probe is built from.
                targo = os.path.abspath(targo)
            host, text = run_probe(targo, plan)
            if plan.keep_samples:
                try:
                    Path(plan.keep_samples).write_text(text, encoding="utf-8")
                except OSError as error:
                    unwritten = f"{plan.keep_samples}: {error}"
        summary = summarize(*parse(text))
    except Refused as why:
        print(f"dispatch-cost: no row: {why}", file=sys.stderr)
        return 2
    except Malformed as why:
        print(f"dispatch-cost: failed: {why}", file=sys.stderr)
        return 1
    except OSError as why:
        print(f"dispatch-cost: no row: {why}", file=sys.stderr)
        return 2
    if plan.json:
        print(json.dumps({"host": host, **summary}, indent=2, sort_keys=True))
    else:
        print(render(summary, host))
    if unwritten:
        print(f"dispatch-cost: failed: the row above stands, but the samples were not kept: "
              f"{unwritten}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
