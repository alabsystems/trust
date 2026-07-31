#!/usr/bin/env python3
"""Program 3 — the completeness-gap ruling's direction battery.

The ruling (`docs/design/2026-07-25-completeness-gap-policy-ruling.md`,
§"What must be true before any code lands", item 3) requires a fixture proving
each direction of policy B:

    a `runtime-checked` row builds clean by default and is rejected under
    `certify`; a genuinely overflowing fixture still fails; a no-fallback row
    still fails.

C.7 measured the first two ad-hoc and recorded the numbers in a commit message.
Nothing pinned them, and the THIRD — the no-fallback row — was never measured at
all. That third one is the load-bearing direction: it is the only thing
separating policy B from "accept anything unproved". Accepting an unproved
overflow row is safe because rustc still checks it at runtime; accepting an
unproved `ensures` clause ships unverified behaviour with nothing catching it.

    python3 tests/trust-provability/policy_directions.py          # CI gate

HAZARD, and the reason this file is careful about exit codes. Here the exit code
IS the measurement — "does the build succeed?" is the whole question — so unlike
the other instruments in this directory we cannot simply classify on the
transport. That makes the classic failure mode live: a renamed flag exits
non-zero, and a battery that reads non-zero as "correctly rejected" reports
all-green while pinning nothing. It has happened in this repo
(`tests/trust-contract/README.md`). So every run is screened for the compiler
refusing our FLAGS, or ICEing, before its exit code is read as a verdict; and
the no-fallback case additionally asserts the transport actually produced the
kind of row it claims to be about, so it cannot pass for the wrong reason.
"""
import glob
import json
import os
import subprocess
import sys
import tempfile

REPO = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", ".."))
TRUSTC = os.environ.get(
    "TRUST_PROVABILITY_TRUSTC",
    os.path.join(REPO, "build", "host", "stage2", "bin", "trustc"),
)
FIXTURES = os.path.join(os.path.dirname(__file__), "directions")

# Each case names the direction it pins and what the ruling requires of it.
# `default_builds` / `certify_builds` are the REQUIRED dispositions.
CASES = [
    {
        "file": "gap_with_fallback.rs",
        "direction": "completeness gap WITH a runtime fallback",
        "default_builds": True,
        "certify_builds": False,
        "why": "rustc still checks this overflow at runtime, so B keeps the check "
               "and succeeds; certify demands static discharge and must reject it",
    },
    {
        "file": "refutation.rs",
        "direction": "genuine refutation",
        "default_builds": False,
        "certify_builds": False,
        "why": "the verifier found a real counterexample; B tolerates gaps, never "
               "refutations",
    },
    {
        "file": "nofallback.rs",
        "direction": "unproved row with NO runtime fallback",
        "default_builds": False,
        "certify_builds": False,
        # Two guards against passing for the wrong reason.
        #
        # (a) The fixture must actually produce a contract-postcondition
        #     obligation. If it instead failed on an arithmetic refutation, this
        #     case would be green while pinning nothing about no-fallback rows.
        #
        # (b) That row must be a completeness GAP, not a refutation. This is the
        #     subtle one and it is the whole point of the direction: a refuted
        #     row already fails under direction 2, so if the postcondition were
        #     merely false (say `ensures result >= x` over a wrapping multiply,
        #     which is false at x = 65536) this case would silently collapse into
        #     a duplicate of `refutation.rs`. What must be pinned is that an
        #     unproved-but-not-disproved row with no runtime fallback ALSO fails.
        "require_kind_substring": "postcond",
        "forbid_row_outcomes": ("failed", "refuted", "violated"),
        "why": "rustc emits no check for an `ensures` clause, so an unproved one "
               "must keep failing — this is what separates B from accepting "
               "anything unproved",
    },
]

BASE_FLAGS = [
    "-Zthreads=1",
    "-Ztrust-verify=on",
    "-Ztrust-verify-output=json",
    "-Coverflow-checks=on",
    "--edition=2021",
    "--crate-type=lib",
    "--emit=metadata",
]


class HarnessError(Exception):
    """The compiler refused our invocation — not a verdict about the program."""


def run(path, certify):
    """-> (built: bool, rows: [transport rows]).  Raises HarnessError."""
    out_dir = tempfile.mkdtemp(prefix="directions_")
    env = dict(os.environ)
    env["TRUST_SEED_STAIRCASE"] = "1"
    cmd = [TRUSTC, *BASE_FLAGS]
    if certify:
        cmd.append("-Ztrust-policy=certify")
    cmd += ["--out-dir", out_dir, path]
    try:
        proc = subprocess.run(
            cmd, capture_output=True, text=True, env=env, timeout=300
        )
    except subprocess.TimeoutExpired:
        raise HarnessError(f"timed out: {' '.join(cmd)}")

    # Screen for "the compiler refused my FLAGS" and for a crash BEFORE reading
    # the exit code as a verdict. Both exit non-zero and would otherwise read as
    # "correctly rejected".
    err = proc.stderr
    for probe in ("unknown unstable option", "Unrecognized option", "unknown debugging option"):
        if probe in err:
            raise HarnessError(
                f"a flag this battery passes no longer exists ({probe!r}); fix the "
                f"battery rather than reading its failure as a verdict"
            )
    if "unexpectedly panicked" in err or "internal compiler error" in err:
        raise HarnessError(f"ICE on {os.path.basename(path)} — a crash is not a verdict")

    rows = []
    for line in err.splitlines():
        i = line.find("TRUST_JSON:")
        if i < 0:
            continue
        try:
            obj = json.loads(line[i + len("TRUST_JSON:"):].strip())
        except json.JSONDecodeError:
            continue
        if obj.get("type") == "function_result":
            rows.extend(obj.get("results") or [])
    return proc.returncode == 0, rows


def main():
    if not os.path.exists(TRUSTC):
        print(f"SKIP: no stage2 trustc at {TRUSTC}")
        return 0

    version = subprocess.run([TRUSTC, "-V"], capture_output=True, text=True).stdout.strip()
    print(f"trustc: {version}\n")

    known = {os.path.basename(p) for p in glob.glob(os.path.join(FIXTURES, "*.rs"))}
    declared = {c["file"] for c in CASES}
    if known != declared:
        print(f"FAIL: fixture directory and CASES disagree: "
              f"only-on-disk={sorted(known - declared)} only-in-CASES={sorted(declared - known)}")
        return 1

    failures = []
    for case in CASES:
        path = os.path.join(FIXTURES, case["file"])
        try:
            default_built, default_rows = run(path, certify=False)
            certify_built, _ = run(path, certify=True)
        except HarnessError as exc:
            print(f"  {case['file']}: HARNESS ERROR — {exc}")
            return 2

        def disposition(built):
            return "builds" if built else "rejected"

        print(f"  {case['file']:24s} [{case['direction']}]")
        print(f"      default = {disposition(default_built):8s} "
              f"certify = {disposition(certify_built)}")

        if default_built != case["default_builds"]:
            failures.append(
                f"{case['file']}: under the DEFAULT policy expected "
                f"{disposition(case['default_builds'])}, got {disposition(default_built)} "
                f"— {case['why']}")
        if certify_built != case["certify_builds"]:
            failures.append(
                f"{case['file']}: under CERTIFY expected "
                f"{disposition(case['certify_builds'])}, got {disposition(certify_built)}")

        want_kind = case.get("require_kind_substring")
        if want_kind:
            kinds = [str(r.get("kind", "")) for r in default_rows]
            if not any(want_kind in k for k in kinds):
                failures.append(
                    f"{case['file']}: no obligation of the kind this case exists to "
                    f"pin (wanted a kind containing {want_kind!r}); observed "
                    f"{sorted(set(kinds)) or '[]'}. The case may be passing for the "
                    f"wrong reason — a rejection for an unrelated cause is not "
                    f"evidence about the no-fallback class.")
            else:
                matching = [r for r in default_rows if want_kind in str(r.get("kind", ""))]
                outcomes = sorted({str(r.get("outcome", "")).lower() for r in matching})
                print(f"      pinned kind present: "
                      f"{sorted({str(r.get('kind')) for r in matching})} outcome={outcomes}")
                forbidden = set(case.get("forbid_row_outcomes", ()))
                if forbidden and all(o in forbidden for o in outcomes):
                    failures.append(
                        f"{case['file']}: every pinned row is {outcomes} — a REFUTATION, "
                        f"not a completeness gap. This case then duplicates "
                        f"refutation.rs and pins nothing about unproved no-fallback "
                        f"rows. Replace the fixture with a postcondition that is TRUE "
                        f"but not provable.")

    if failures:
        print("\nDIRECTION BATTERY FAILED:")
        for line in failures:
            print(f"  - {line}")
        print("\nDo not 'fix' this by relaxing an assertion: each direction is a "
              "clause of the ratified ruling.")
        return 1

    print("\nall three directions hold")
    return 0


if __name__ == "__main__":
    sys.exit(main())
