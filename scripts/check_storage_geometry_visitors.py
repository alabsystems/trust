#!/usr/bin/env python3
"""Execute exact production type visitors without building rustc-private code.

Only the complete selected declarations/functions are extracted. Their bytes
and full source files are hashed; real IR types and its canonical validator
are dependencies. No semantics, facts or refusal types are reimplemented.
This is a source-coupled regression probe, not TCX or proof qualification.
"""
from pathlib import Path
import argparse
import hashlib
import json
import os
import re
import subprocess
import sys


def between(text, start, end):
    if text.count(start) != 1 or text.count(end) != 1:
        raise ValueError(f"source boundary is absent or ambiguous: {start!r} / {end!r}")
    left = text.index(start)
    right = text.index(end, left)
    return text[left:right]


def ordinary_ir_imports(text):
    imports = re.findall(r"^use trust_ir::\{[^;]*\};", text, re.M)
    if len(imports) != 1:
        raise ValueError("one complete production trust_ir import block is required")
    return imports[0]


def check_generated_artifacts(producer, output):
    source = producer["source_sha256"]
    required = {"src/lib.rs": producer["generated_sha256"],
                "src/diagnostic.rs": source["crate_module/validation_type_context.rs"]}
    adjacent = "crate_module/validation_type_context_caller_tests.rs"
    if adjacent in source:
        required["src/validation_type_context_caller_tests.rs"] = source[adjacent]
    actual_map = producer.get("generated_artifacts_sha256")
    if actual_map is None:
        # The original six-file producer copied only lib.rs and diagnostic.rs.
        # Their exact hashes are already present in its sealed input receipt.
        if adjacent in source:
            raise ValueError("complete generated artifact map is missing")
        actual_map = required
    if actual_map != required:
        raise ValueError("generated artifact map differs from complete production/control inputs")
    for name, expected in actual_map.items():
        if hashlib.sha256((output / name).read_bytes()).hexdigest() != expected:
            raise ValueError(f"generated production/control source changed: {name}")


def check_generated_manifest(producer, output, template_bytes):
    expected = template_bytes.decode("utf-8").replace("@IR@", producer["ir_root"]).encode("utf-8")
    expected_sha256 = hashlib.sha256(expected).hexdigest()
    if producer.get("generated_manifest_sha256", expected_sha256) != expected_sha256:
        raise ValueError("generated manifest receipt differs from its original template and IR root")
    if (output / "Cargo.toml").read_bytes() != expected:
        raise ValueError("generated Cargo manifest changed its original dependency binding")


EXPECTED_TESTS = {
    "template_source::storage_geometry_has_no_sentinel_or_hidden_row",
    "template_source::storage_geometry_level_map_preserves_both_u64_fields_and_generic_neighbors",
    "template_source::storage_geometry_join_remap_preserves_geometry_and_still_remaps_real_ids",
    "template_source::storage_geometry_mapping_does_not_authorize_by_value_or_invalid_geometry",
    "diagnostic::tests::storage_geometry_diagnostic_keeps_exact_fields_and_no_authority",
}


def test_population(raw):
    summaries = re.findall(r"^test result: (ok|FAILED)\. (\d+) passed; (\d+) failed; (\d+) ignored; (\d+) measured; (\d+) filtered out;", raw, re.M)
    rows = re.findall(r"^test (\S+) \.\.\. (ok|FAILED|ignored)$", raw, re.M)
    if len(summaries) != 1:
        raise ValueError("one actual libtest population is required")
    status, passed, failed, ignored, measured, filtered = summaries[0]
    counts = dict(passed=int(passed), failed=int(failed), ignored=int(ignored),
                  measured=int(measured), filtered=int(filtered))
    if status != "ok" or (counts["passed"], counts["failed"], counts["ignored"], counts["measured"]) != (5, 0, 0, 0):
        raise ValueError(f"the five native controls did not all execute successfully: {counts}")
    if len(rows) != 5 or {name for name, result in rows if result == "ok"} != EXPECTED_TESTS:
        raise ValueError("the actual successful native controls differ from the five named source controls")
    return counts


def qualify_existing(root, output, raw_log):
    producer = json.loads((output / "SOURCE-INPUTS.json").read_text())
    frozen = json.loads((output / "FROZEN-PRODUCER-HELPERS.json").read_text())
    if hashlib.sha256((output / "SOURCE-INPUTS.json").read_bytes()).hexdigest() != frozen["source_inputs_sha256"]:
        raise ValueError("the original producer input receipt changed")
    if hashlib.sha256((output / "src/lib.rs").read_bytes()).hexdigest() != frozen["generated_source_sha256"]:
        raise ValueError("the actual generated native controls changed")
    check_generated_artifacts(producer, output)
    for name, expected in producer["source_sha256"].items():
        path = root / "crates/trust-thir-lower/src" / name
        if hashlib.sha256(path.read_bytes()).hexdigest() != expected:
            raise ValueError(f"the original native production input changed: {name}")
    for name, row in frozen["helpers"].items():
        if hashlib.sha256(Path(row["retained_exact_bytes"]).read_bytes()).hexdigest() != row["sha256"]:
            raise ValueError("an original frozen producer helper changed")
        if not name.endswith("check_storage_geometry_visitors.py") and hashlib.sha256((root / name).read_bytes()).hexdigest() != row["sha256"]:
            raise ValueError("the native control or manifest template changed")
    manifest_name = "crates/trust-thir-lower/probes/storage_geometry_visitors/Cargo.toml.in"
    templates = [row for name, row in frozen["helpers"].items()
                 if name == manifest_name or name.endswith("/" + manifest_name)]
    if len(templates) != 1:
        raise ValueError("the original generated manifest template custody is missing or ambiguous")
    check_generated_manifest(producer, output, Path(templates[0]["retained_exact_bytes"]).read_bytes())
    dependency = json.loads((output / "FROZEN-DEPENDENCY-IDENTITY.json").read_text())
    identity = subprocess.check_output(["git", "--no-replace-objects", "-C", dependency["ir_root"], "rev-parse", "HEAD", "HEAD^{tree}"], text=True).splitlines()
    if identity != [dependency["ir_commit"], dependency["ir_tree"]]:
        raise ValueError("the selected native IR dependency identity changed")
    if hashlib.sha256((output / "Cargo.lock").read_bytes()).hexdigest() != dependency["cargo_lock_sha256"]:
        raise ValueError("the selected native dependency lock changed")
    original = json.loads((output / "RESULT.json").read_text())
    if original["exit"] != 0:
        raise ValueError("the original native command failed")
    tools = original["command"]
    tool = Path(tools[tools.index("--unverified") - 1])
    for name, expected in dependency["tools"].items():
        if hashlib.sha256((tool.parent / name).read_bytes()).hexdigest() != expected:
            raise ValueError("the native tool identity changed")
    raw = raw_log.read_bytes()
    counts = test_population(raw.decode())
    report = dict(native_exit=0, exit=0, counts=counts, raw_log=str(raw_log),
                  raw_log_sha256=hashlib.sha256(raw).hexdigest(),
                  producer_helpers=frozen, dependency_identity=dependency, qualifier_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                  production_and_control_inputs_unchanged=True, proof_claim="none")
    with (output / "QUALIFIED-RESULT.json").open("x") as handle:
        handle.write(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report, indent=2))
    return 0


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source-root", type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument("--ir-root", type=Path)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--targo", type=Path)
    parser.add_argument("--qualify-existing", type=Path)
    parser.add_argument("--native-log", type=Path)
    parser.add_argument("--prepare-only", action="store_true",
                        help="write source-coupled inputs; execute no Rust and make no native claim")
    args = parser.parse_args()
    root = args.source_root.resolve()
    if args.qualify_existing:
        if args.native_log is None:
            parser.error("--qualify-existing requires --native-log")
        return qualify_existing(root, args.qualify_existing.resolve(), args.native_log.resolve())
    if args.output is None or (args.targo is None and not args.prepare_only):
        parser.error("a new native run requires --output and --targo")
    ir = (args.ir_root or root / "first-party/trust-ir").resolve()
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    source = root / "crates/trust-thir-lower/src"
    paths = ["template_lowering.rs", "template_key.rs", "effect_conservation.rs",
             "rmeta_entry.rs", "clean_origin_join.rs", "crate_module/validation_type_context.rs",
             "crate_module.rs", "crate_module/validation_type_context_caller_tests.rs"]
    bodies = {name: (source / name).read_text() for name in paths}
    hashes = {name: hashlib.sha256((source / name).read_bytes()).hexdigest() for name in paths}
    helper_paths = [Path(__file__).resolve(),
                    root / "crates/trust-thir-lower/probes/storage_geometry_visitors/tests.rs",
                    root / "crates/trust-thir-lower/probes/storage_geometry_visitors/Cargo.toml.in"]
    helper_hashes = {str(path): hashlib.sha256(path.read_bytes()).hexdigest() for path in helper_paths}
    ir_identity = subprocess.check_output(["git", "--no-replace-objects", "-C", str(ir), "rev-parse", "HEAD", "HEAD^{tree}"], text=True).splitlines()
    template = bodies["template_lowering.rs"]
    prefix = between(template, '/// The dialect namespace of the lane\'s type sentinels',
                     '/// The lane state a template-mode lowering carries')
    sentinel = between(template, '/// What a dialect type or a symbol address is, to the lane.',
                       'fn symbol_sentinel(')
    walk = between(template, "struct SentinelWalk<'m>", "/// THE ESCAPE CHECK")
    abstraction = between(template, "fn abstract_ty(", "/// The constant half of the level map")
    invalid = between(template, "fn invalid(", "/// Does a type mention the lane's sentinel space")
    type_sentinel = between(template, "pub fn type_param_sentinel(",
                            '/// The sentinel constant of scalar const parameter')
    key = between(bodies["template_key.rs"], "/// DefPathHash's stable crate identity",
                  '#[derive(Clone, Debug, PartialEq, Eq)]\npub struct KeyError')
    lanes = between(bodies["effect_conservation.rs"], "/// The two placeholder lanes",
                    "/// The effect SHAPE")
    refusals = between(bodies["rmeta_entry.rs"], "/// Why the encoder wrote no entry", "impl EntryRefusal")
    remap = between(bodies["clean_origin_join.rs"], "fn remap_general_ty(",
                    "\nfn remap_general_inst_tys(")
    # Keep private production functions private within one native source module;
    # append its tests there instead of changing their visibility.
    probe = root / "crates/trust-thir-lower/probes/storage_geometry_visitors"
    (output / "src").mkdir()
    (output / "Cargo.toml").write_text((probe / "Cargo.toml.in").read_text().replace("@IR@", str(ir)))
    (output / "src/diagnostic.rs").write_text(bodies["crate_module/validation_type_context.rs"])
    # Keep the real module's adjacent test source and its production caller
    # closure. A newly added mod must not turn the durable probe into an
    # incomplete copy or tempt it to strip tests / invent a caller stub.
    (output / "src/validation_type_context_caller_tests.rs").write_text(
        bodies["crate_module/validation_type_context_caller_tests.rs"])
    caller = between(bodies["crate_module.rs"], "fn functions_returning_in_block(",
                     "\n#[cfg(test)]\nmod final_module_validation_gate_tests")
    actual = "\n".join([
        'use std::collections::{BTreeMap,BTreeSet};',
        ordinary_ir_imports(template),
        'use trust_ir::template::TemplateArg;',
        lanes, refusals, prefix, sentinel, walk, invalid, type_sentinel, abstraction,
    ])
    # Tests are appended inside the production module and may see its private helpers.
    tests = (probe / "tests.rs").read_text().replace("use template_source::*;\n", "").replace(
        "use trust_ir::{StorageLayout, Ty, TyG, TyId, FuncTyId, Module};", "use trust_ir::StorageLayout;")
    generated = ('#![allow(dead_code)]\nuse std::collections::BTreeMap;\n'
                 'use trust_ir::{Module,Inst,FuncId};\nuse diagnostic as validation_type_context;\n'
                 + caller + '\nmod template_key {\n' + key + '\n}\nmod template_source {\n'
                 + actual + '\n' + remap + '\n' + tests + '\n}\nmod diagnostic;\n')
    (output / "src/lib.rs").write_text(generated)
    record = {"source_root": str(root), "ir_root": str(ir), "source_sha256": hashes,
              "generated_sha256": hashlib.sha256(generated.encode()).hexdigest(),
              "helper_sha256": helper_hashes, "ir_commit": ir_identity[0], "ir_tree": ir_identity[1],
              "semantics_reimplemented": False, "proof_claim": "none"}
    generated_artifacts = {str(path.relative_to(output)): hashlib.sha256(path.read_bytes()).hexdigest()
                           for path in sorted((output / "src").glob("*.rs"))}
    record["generated_artifacts_sha256"] = generated_artifacts
    record["generated_manifest_sha256"] = hashlib.sha256((output / "Cargo.toml").read_bytes()).hexdigest()
    check_generated_manifest(record, output, (probe / "Cargo.toml.in").read_bytes())
    (output / "SOURCE-INPUTS.json").write_text(json.dumps(record, indent=2) + "\n")
    if args.prepare_only:
        print("Prepared exact source inputs; no Rust executed, no native or proof claim.")
        return 0
    tool_identity = subprocess.check_output([str(args.targo), "--unverified", "--version"], text=True).strip()
    if not tool_identity.startswith("targo ") or "(targo " not in tool_identity:
        raise ValueError("the probe requires genuine authenticated Targo")
    record["targo_identity"] = tool_identity
    record["targo_sha256"] = hashlib.sha256(args.targo.read_bytes()).hexdigest()
    (output / "SOURCE-INPUTS.json").write_text(json.dumps(record, indent=2) + "\n")
    env = dict(os.environ, PYTHONDONTWRITEBYTECODE="1")
    metadata = [str(args.targo), "metadata", "--format-version", "1", "--manifest-path", str(output / "Cargo.toml")]
    with (output / "METADATA.json").open("w") as stdout:
        subprocess.run(metadata, cwd=output, env=env, stdout=stdout, check=True)
    command = [str(root / "scripts/build-slot"), "--cpus", "4", "--mem-gb", "8", "--",
               str(args.targo), "--unverified", "test", "--locked", "--manifest-path", str(output / "Cargo.toml"),
               "--lib", "storage_geometry", "--", "--nocapture"]
    raw_path = output / "NATIVE-TEST.log"
    with raw_path.open("x") as raw:
        process = subprocess.Popen(command, cwd=output, env=env, stdout=subprocess.PIPE,
                                   stderr=subprocess.STDOUT, text=True)
        for line in process.stdout:
            raw.write(line); raw.flush(); print(line, end="", flush=True)
        native_exit = process.wait()
    if hashes != {name: hashlib.sha256((source / name).read_bytes()).hexdigest() for name in paths}:
        raise ValueError("production source changed during the native probe")
    if helper_hashes != {str(path): hashlib.sha256(path.read_bytes()).hexdigest() for path in helper_paths}:
        raise ValueError("producer/control helper changed during the native probe")
    check_generated_artifacts(record, output)
    check_generated_manifest(record, output, (probe / "Cargo.toml.in").read_bytes())
    current_ir = subprocess.check_output(["git", "--no-replace-objects", "-C", str(ir), "rev-parse", "HEAD", "HEAD^{tree}"], text=True).splitlines()
    if current_ir != ir_identity or hashlib.sha256(args.targo.read_bytes()).hexdigest() != record["targo_sha256"]:
        raise ValueError("the selected native dependency/tool identity changed")
    result = dict(native_exit=native_exit, exit=native_exit, command=command,
                  production_source_unchanged=True, helper_inputs_unchanged=True,
                  raw_log=str(raw_path), raw_log_sha256=hashlib.sha256(raw_path.read_bytes()).hexdigest(),
                  proof_claim="none")
    try:
        result["counts"] = test_population(raw_path.read_text())
    except ValueError as error:
        result["population_refusal"] = str(error)
        result["exit"] = native_exit or 1
    (output / "RESULT.json").write_text(json.dumps(result, indent=2) + "\n")
    return result["exit"]


if __name__ == "__main__":
    raise SystemExit(main())
