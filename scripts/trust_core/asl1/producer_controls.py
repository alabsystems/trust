#!/usr/bin/env python3
"""Focused controls against an explicitly supplied actual ASLRef extractor.

No mock producer, language interpreter, executable fallback or proof authority.
Control errors are separated from ASL errors and profile refusals by phase/kind.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess

HERE = Path(__file__).resolve().parent
EXPECTED = {
    "zero", "eight", "max", "frame_offset", "renamed", "integer", "bad_width",
    "bad_type", "unsupported_mul", "unsupported_neg", "extra_function", "syntax",
    "extra_statement",
}


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--producer", type=Path, required=True)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    binary = args.producer.resolve()
    output = args.out.resolve()
    output.mkdir(parents=True, exist_ok=False)
    fixtures = HERE / "fixtures"
    cases_path = fixtures / "CASES.json"
    cases = json.loads(cases_path.read_text())
    require({row["case"] for row in cases} == EXPECTED and len(cases) == len(EXPECTED),
            "changed source-control denominator")
    inputs = {str(binary): digest(binary), str(cases_path): digest(cases_path),
              str(Path(__file__).resolve()): digest(Path(__file__))}
    rows = []
    good = True
    for case in cases:
        name = case["case"]
        source = fixtures / (name + ".asl")
        inputs[str(source)] = digest(source)
        run = subprocess.run([str(binary), str(source)], capture_output=True, timeout=30)
        (output / (name + ".bin")).write_bytes(run.stdout)
        (output / (name + ".stderr")).write_bytes(run.stderr)
        text = run.stderr.decode(errors="replace")
        metadata = [json.loads(line) for line in text.splitlines() if line.startswith("{")]
        if case["expect_accept"]:
            expected_packet = fixtures / "packets" / (name + ".bin")
            inputs[str(expected_packet)] = digest(expected_packet)
            passed = (
                run.returncode == 0 and len(metadata) == 1
                and metadata[0]["pin"] == "ffad2692c4580538e8db7bf6631aa886edfc7423"
                and metadata[0]["source_name"] == case["source_name"]
                and metadata[0]["reference_value"] == case["reference_value"]
                and metadata[0]["declarations"] == 1
                and metadata[0]["strict_typecheck"] == "TypeCheck"
                and run.stdout == expected_packet.read_bytes()
            )
        else:
            marker = f"ASLREF_REFUSAL phase={case['phase']} kind={case['kind']}"
            passed = (run.returncode == (3 if case["kind"] == "asl_error" else 4)
                      and not run.stdout and not metadata and marker in text
                      and case["refusal"] in text and "construction_error" not in text)
        good = good and passed
        rows.append({"case": name, "passed": passed, "exit": run.returncode,
                     "metadata": metadata, "packet_sha256": digest(output / (name + ".bin")),
                     "stderr_sha256": digest(output / (name + ".stderr")), "expected": case})
        print(name, "PASS" if passed else "FAILED", flush=True)
    # Bind every positive Lean fixture directly to actual producer packet bytes.
    lean = HERE / "Asl1/WireFixtures.lean"
    inputs[str(lean)] = digest(lean)
    text = lean.read_text()
    for case in cases:
        if not case["expect_accept"]:
            continue
        suffix = "".join(part.title() for part in case["case"].split("_"))
        match = re.search(r"def packet" + suffix + r" : List Nat := \[([0-9,]+)\]", text)
        require(match is not None, "missing exact Lean packet fixture: " + suffix)
        packet = bytes(int(number) for number in match.group(1).split(","))
        require(packet == (output / (case["case"] + ".bin")).read_bytes(),
                "actual producer packet differs from Lean fixture: " + suffix)
    changed = [path for path, wanted in inputs.items() if digest(Path(path)) != wanted]
    good = good and not changed
    report = {"status": "ACTUAL_ASLREF_CONTROLS_PASS" if good else "FAILED",
              "cases": rows, "inputs": inputs, "changed_inputs": changed,
              "positive_packets": 6, "ASL_typecheck_rejections": 2,
              "ASL_parser_rejections": 1, "explicit_profile_refusals": 4,
              "scope": "Actual parser/strict typing/reference interpreter and packet custody; no whole-ASL, source-refinement, ISA or proof-grade claim"}
    (output / "RESULT.json").write_text(json.dumps(report, indent=2) + "\n")
    raise SystemExit(0 if good else 1)


if __name__ == "__main__":
    main()
