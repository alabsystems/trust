#!/usr/bin/env python3
"""Actual compiler source-profile controls; no proof or compiler admission claim.

Run under build-slot and the original SDK/build input leases. The observer must
be built from source with one matching private compiler dependency closure.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT / "scripts/lib"))
import landing_targo


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--observer", type=Path, required=True)
    parser.add_argument("--targo", type=Path, required=True)
    parser.add_argument("--sysroot", type=Path, required=True)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    args.out.mkdir(parents=True, exist_ok=False)
    fixtures = Path(__file__).resolve().parent / "fixtures"
    old = fixtures / "source_word64_addition_controls"
    new = fixtures / "source_word64_self_addition_controls"
    old_names = {"c_abi", "checked_add", "effect_receiver", "i64", "let_argument", "local",
                 "max", "nonliteral", "swapped", "trait", "u32", "zero"}
    new_names = {"inline", "nested", "other_parameter", "effect_argument", "caller_attribute"}
    for folder, names in [(old, old_names), (new, new_names)]:
        if {path.stem for path in folder.glob("*.rs")} != names:
            raise RuntimeError(f"source-profile control roster changed: {folder}")
    literal, same = "word64-literal-addition", "word64-self-addition"
    cases = [(fixtures / "source_word64_addition_original.rs", "addition", literal)]
    cases += [(path, "addition", literal if path.stem in ("zero", "max") else
               same if path.stem == "nonliteral" else None) for path in sorted(old.glob("*.rs"))]
    cases += [(path, "double", same if path.stem == "inline" else None)
              for path in sorted(new.glob("*.rs"))]
    cases += [(ROOT / "tests/trust-f1-ladder/lean/l03_lean_calls_rust.rs", "double", same)]
    if len(cases) != 19:
        raise RuntimeError("source-profile control population changed; review every case")
    captures = fixtures / "source_word64_capture_controls"
    if {path.stem for path in captures.glob("*.rs")} != {
            "registered_add", "local_lookalike", "unsupported_intrinsic"}:
        raise RuntimeError("original source capture control roster changed")
    cases += [(path, "original_add", None) for path in sorted(captures.glob("*.rs"))]
    paths = [path for path, _, _ in cases] + [Path(__file__).resolve(),
             ROOT / "crates/trust-thir-lower/src/source_word64.rs",
             Path(__file__).with_name("source_word64_capture_component.rs"),
             Path(__file__).with_name("source_word64_addition.rs")]
    digest = lambda: {str(path): hashlib.sha256(path.read_bytes()).hexdigest() for path in paths}
    before = digest()
    observer_digest = hashlib.sha256(args.observer.read_bytes()).hexdigest()
    env = dict(os.environ, RUSTC=str(args.observer.resolve()))
    fds = landing_targo.resource_fds(env)
    rows = []
    for index, (source, function, expected) in enumerate(cases):
        work = args.out / f"case-{index:02d}-{source.stem}"
        work.mkdir()
        output = work / "capture"
        output.mkdir()
        manifest = work / "Cargo.toml"
        manifest.write_text('[package]\nname="source-profile-' + str(index) +
                            '"\nversion="0.0.0"\nedition="2021"\n[workspace]\n[lib]\npath=' +
                            json.dumps(str(source)) + '\n')
        child_env = dict(env, TRUST_ACTUAL_ADDITION_OUT=str(output.resolve()),
                         TRUST_ACTUAL_ADDITION_FUNCTION=function)
        command = [str(args.targo), "--unverified", "rustc", "--offline", "--manifest-path",
                   str(manifest), "--target-dir", str(work / "target"), "--", "--sysroot",
                   str(args.sysroot.resolve())]
        with (work / "compiler.log").open("w") as log:
            result = subprocess.run(command, env=child_env, stdout=log, stderr=subprocess.STDOUT,
                                    pass_fds=fds)
        if result.returncode:
            raise RuntimeError(
                f"actual compiler failed: {source}; retained {work / 'compiler.log'}")
        facts = json.loads((output / "ACTUAL-THIR.json").read_text())
        profile = facts["word64_source_profile"]
        if facts["closed_profile"]["accepted"] != (expected == literal):
            raise RuntimeError(f"historical literal profile changed for {source}")
        if profile["accepted"] != (expected is not None):
            raise RuntimeError(f"wrong source profile for {source}: {profile}")
        retained_inputs = None
        if expected is not None:
            if profile["source_operation"] != expected:
                raise RuntimeError(f"wrong operation for {source}: {profile}")
            assembly = json.loads((output / "QUERY-ASSEMBLY.json").read_text())
            if (not assembly["assembled"] or assembly["validator"] != "[]" or
                    assembly["declarations"] != 1):
                raise RuntimeError(f"canonical structural assembly refused {source}: {assembly}")
            if (output / "original-source.rs").read_bytes() != source.read_bytes():
                raise RuntimeError(f"original source changed: {source}")
            callees = [call for call in facts["calls"]
                       if call.get("selected_primitive_model") == "core-u64-wrapping-add-v1"]
            if len(callees) != 1:
                raise RuntimeError(f"expected one actual wrapping-add callee: {source}")
            entry = callees[0]["retained_entry"]
            if (not entry["retained"] or entry["validator"] != "[]" or
                    entry["function_count"] != 1 or entry["defined_count"] != 1 or
                    entry["declaration_count"] != 0):
                raise RuntimeError(f"actual wrapping-add implementation unavailable: {entry}")
            snapshot = facts["source_snapshot"]
            if (not snapshot["captured"] or not snapshot["belongs_to_actual_owner"] or
                    snapshot["expression"]["kind"] != "OrdinaryCall" or
                    snapshot["expression"]["definition"] != callees[0]["def_path_hash"] or
                    len(snapshot["original_expressions"]) != len(facts["thir_exprs"])):
                raise RuntimeError(f"original Rust call was lost or reinterpreted: {snapshot}")
            if source.name == "l03_lean_calls_rust.rs" and not snapshot["rejects_other_owner"]:
                raise RuntimeError("source snapshot accepted a different original owner")
            retained_inputs = {"actual_callee": callees[0]["def_path_hash"],
                               "binding": entry["binding"]}
            for field in ("envelope", "decoded_module"):
                data = (output / entry[field]).read_bytes()
                if not data:
                    raise RuntimeError(f"actual callee input is empty: {entry[field]}")
                retained_inputs[field + "_sha256"] = hashlib.sha256(data).hexdigest()
        if source.parent == captures:
            snapshot = facts["source_snapshot"]
            if source.stem == "unsupported_intrinsic":
                if snapshot["captured"]:
                    raise RuntimeError(
                        "unsupported registered intrinsic acquired source semantics")
            else:
                kind = ("RegisteredWrappingAdd" if source.stem == "registered_add"
                        else "OrdinaryCall")
                if (not snapshot["captured"] or snapshot["expression"]["kind"] != kind or
                        not snapshot["belongs_to_actual_owner"] or
                        (source.stem == "local_lookalike" and
                         snapshot["rejects_other_owner"] is not True)):
                    raise RuntimeError(
                        f"registered-intrinsic/source-call distinction lost: {snapshot}")
                operands = [item["value"] for item in snapshot["expression"]["operands"]]
                if operands != [{"kind": "parameter", "index": 0},
                                {"kind": "parameter", "index": 1}]:
                    raise RuntimeError("original source parameter order changed")
        snapshot = facts["source_snapshot"]
        if snapshot["captured"]:
            record = snapshot["source_record"]
            if (record["schema"] != 1 or not 0 < record["bytes"] <= 4096 or
                    any(record[key] is not True for key in
                        ("roundtrip", "every_truncation_refused",
                         "owner_matches_original", "claim_only"))):
                raise RuntimeError(f"original source transport qualification failed: {record}")
        rows.append({"source": str(source), "expected_source_operation": expected,
                     "profile": profile, "raw_query_validator": facts["validator"],
                     "retained_callee_inputs": retained_inputs})
        print(f"PASS {index + 1}/{len(cases)} {source.name}", flush=True)
    if (digest() != before or
            hashlib.sha256(args.observer.read_bytes()).hexdigest() != observer_digest):
        raise RuntimeError("source-profile qualification inputs changed during execution")
    (args.out / "results.json").write_text(json.dumps({"inputs": before, "cases": rows,
        "observer_sha256": observer_digest,
        "scope": "Typed source/profile and canonical structural assembly only; "
                 "no source/IR theorem, closed callee implementation, ABI, NoUB, proof grade "
                 "or admission."}, indent=2) + "\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
