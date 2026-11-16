#!/usr/bin/env python3
"""Read passive compiletest observations; no proof or corpus-completion authority.

A valid hash chain detects accidental truncation/corruption, not a forged producer.
The caller retains responsibility for process custody and selecting the corpus.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path

import rust_instance_census
import trust_ir_producer_scorecard

SCHEMA = "trust.compiletest.invocation-census.v1"
MAX_RECORD = 8 * 1024 * 1024
MAX_ARTIFACT = 32 * 1024 * 1024


def unique(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise ValueError(f"duplicate JSON key: {key}")
        result[key] = value
    return result


def require(value, message):
    if not value:
        raise ValueError(message)


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def text_arg(value):
    require(isinstance(value, dict) and set(value) == {"utf8", "encoded_bytes_hex"},
            "malformed OS argument")
    raw = bytes.fromhex(value["encoded_bytes_hex"])
    if value["utf8"] is None:
        return None
    require(type(value["utf8"]) is str and os.fsencode(value["utf8"]) == raw,
            "OS string/byte mismatch on this host")
    return value["utf8"]


def artifact(directory, row):
    require(isinstance(row, dict), "missing retained artifact")
    path = Path(row["path"])
    require(path.is_absolute() and path.parent == directory and not path.is_symlink(),
            "retained artifact escapes census directory or is a symlink")
    require(type(row["bytes"]) is int and 0 <= row["bytes"] <= MAX_ARTIFACT,
            "retained artifact exceeds bound")
    with path.open("rb") as stream:
        raw = stream.read(MAX_ARTIFACT + 1)
    require(len(raw) == row["bytes"] and sha(raw) == row["sha256"],
            "retained artifact hash/length mismatch")
    return raw


def current_file(row):
    if row.get("status") != "read":
        return "unmeasured"
    try:
        path = Path(row["path"])
        with path.open("rb") as stream:
            hasher = hashlib.sha256()
            for block in iter(lambda: stream.read(65536), b""):
                hasher.update(block)
            digest = hasher.hexdigest()
        return "matched-current-file" if path.stat().st_size == row["bytes"] and digest == row["sha256"] else "changed"
    except OSError:
        return "unavailable"


def flag_values(args, flag):
    values = []
    for i, arg in enumerate(args):
        if arg == flag and i + 1 < len(args):
            values.append(args[i + 1])
        elif arg.startswith(flag + "="):
            values.append(arg[len(flag) + 1:])
    return values


def z_values(args, flag):
    values = []
    for i, arg in enumerate(args):
        token = args[i + 1] if arg == "-Z" and i + 1 < len(args) else arg[2:] if arg.startswith("-Z") else ""
        if token == flag:
            values.append("yes")
        elif token.startswith(flag + "="):
            values.append(token[len(flag) + 1:])
    return values


def boolean_lane(args, flag):
    values = z_values(args, flag)
    if not values:
        return False  # Current compiler option defaults; no proof authority.
    value = values[-1]
    require(value in ("yes", "on", "strict", "true", "1", "no", "off", "false", "0"), "unknown compiler lane flag")
    return value in ("yes", "on", "strict", "true", "1")


def join_observations(directory, attempt, terminal):
    observations = terminal.get("observations", [])
    output = []
    args = [text_arg(a) for a in attempt["argv"]]
    if any(a is None for a in args) or any(a.startswith("@") for a in args):
        return [{"kind": obs["kind"], "status": "unjoined", "reason": "non-UTF8 or response-file argv requires an explicit parser"} for obs in observations]
    cwd = Path(attempt["cwd"])
    roots = [str(cwd / a) for a in args if a.endswith(".rs") and not a.startswith("-")]
    before = {r["path"]: r for r in attempt["argument_files"] if r.get("status") == "read"}
    after = {r["path"]: r for r in terminal["argument_files_after"] if r.get("status") == "read"}
    root = roots[0] if len(roots) == 1 else None
    bound = root is not None and root in before and before[root] == after.get(root)
    program_before, program_after = attempt.get("program_file"), terminal.get("program_after")
    program = text_arg(attempt["program"]) if "program" in attempt else None
    stable_program = (program is not None and Path(program).is_absolute() and isinstance(program_before, dict) and program_before.get("status") == "read"
                      and program_before == program_after and current_file(program_before) == "matched-current-file")
    for observation in observations:
        row = {"kind": observation["kind"], "capture_status": observation["status"]}
        if observation["status"] != "retained-unvalidated":
            row.update(status="unjoined", reason="observer output missing, reused or ambiguous")
            output.append(row)
            continue
        raw = artifact(directory, observation["artifact"])
        if attempt["kind"] != "selected-rustc" or not bound or not stable_program:
            row.update(status="unjoined", reason="no single unchanged command source input and compiler file")
        elif current_file(before[root]) != "matched-current-file":
            row.update(status="unjoined", reason="command source no longer matches recorded bytes")
        else:
            lowering = boolean_lane(args, "trust-ir-lower")
            verification = boolean_lane(args, "trust-verify")
            kind = observation["kind"]
            if kind == "trust-body-census":
                kinds = flag_values(args, "--crate-type")
                mapping = {"bin": "Executable", "dylib": "Dylib", "rlib": "Rlib", "lib": "Rlib", "staticlib": "StaticLib", "cdylib": "Cdylib", "proc-macro": "ProcMacro", "sdylib": "Sdylib"}
                if not kinds or verification:
                    row.update(status="unjoined", reason="HIR join requires explicit crate types and verification-off argv")
                else:
                    if any(k not in mapping for value in kinds for k in value.split(",")):
                        row.update(status="unjoined", reason="unrecognized explicit crate type")
                        output.append(row)
                        continue
                    expected = [mapping[k] for value in kinds for k in value.split(",")]
                    parsed = trust_ir_producer_scorecard.parse_compiler_census(raw.decode("utf-8"), input_path=root,
                        lowering=lowering, exit_code=terminal["exit_code"], expected_crate_types=expected)
                    row.update(status="parsed", observation=parsed)
            elif kind == "trust-instance-census":
                parsed = rust_instance_census.parse_census(raw, input_path=root, exit_code=terminal["exit_code"],
                    lowering=lowering, verification=verification)
                row.update(status="parsed", observation=parsed)
            else:
                row.update(status="retained-unjoined", reason="Lean computational declaration parser is a separate unfinished census")
            if row.get("status") == "parsed" and (header := row["observation"].get("header")):
                target, edition = flag_values(args, "--target"), flag_values(args, "--edition")
                if not target or not edition or header["target"] != target[-1] or header["edition"] != edition[-1]:
                    row.update(status="unjoined", reason="observer target/edition does not match explicit command argv")
            row["root_source_binding"] = "same before/after/current file bytes; process custody remains caller-owned"
        output.append(row)
    return output


def read_census(directory):
    directory = Path(directory).absolute()
    require(not directory.is_symlink(), "census directory must not be a symlink")
    planned, selected, cases, attempts, terminals, spawned = {}, None, {}, {}, {}, set()
    exclusions = []
    begin = end = None
    previous = None
    plan_complete = False
    records = 0
    with (directory / "events.jsonl").open("rb") as stream:
        while raw := stream.readline(MAX_RECORD + 2):
            require(len(raw) <= MAX_RECORD + 1 and raw.endswith(b"\n"), "truncated or oversized record")
            row = json.loads(raw, object_pairs_hook=unique, parse_constant=lambda _: require(False, "non-finite JSON"))
            require(isinstance(row, dict) and row.get("schema") == SCHEMA, "unknown census schema")
            require(type(row.get("sequence")) is int and row["sequence"] == records and row.get("previous_record_sha256") == previous,
                    "record sequence/hash chain mismatch")
            require(end is None, "record after terminal footer")
            previous, records = sha(raw), records + 1
            event = row.get("event")
            if event == "begin":
                require(begin is None and records == 1, "duplicate/misplaced begin")
                begin = row
            elif event == "collection-excluded":
                require(begin is not None and not plan_complete, "misplaced collection exclusion")
                exclusions.append(row)
            elif event == "planned":
                require(begin is not None and not plan_complete and row["case"] not in planned, "duplicate/misplaced planned case")
                planned[row["case"]] = row
            elif event == "plan-complete":
                require(not plan_complete and row["planned"] == len(planned), "planned population mismatch")
                plan_complete = True
            elif event == "selection":
                require(plan_complete and selected is None and len(set(row["cases"])) == len(row["cases"]), "invalid/duplicate selection")
                selected = set(row["cases"])
                require(selected <= planned.keys(), "selected case omitted from plan")
            elif event == "case-terminal":
                require(selected is not None and row["case"] in selected and row["case"] not in cases, "unexpected/duplicate case terminal")
                require(row["outcome"] in ("ok", "failed", "ignored"), "unknown case outcome")
                cases[row["case"]] = row
            elif event == "command-attempt":
                i = row["command"]
                require(selected is not None and type(i) is int and i == len(attempts) and row["case"] in selected,
                        "unexpected command identity/case")
                attempts[i] = row
            elif event == "command-spawned":
                i = row["command"]
                require(i in attempts and i not in spawned and i not in terminals and type(row["pid"]) is int and row["pid"] > 0,
                        "unexpected duplicate spawn")
                spawned.add(i)
            elif event in ("command-terminal", "command-spawn-failed"):
                i = row["command"]
                require(i in attempts and i not in terminals, "unexpected/duplicate command terminal")
                if event == "command-terminal":
                    require(type(row["success"]) is bool and (row["exit_code"] is None or type(row["exit_code"]) is int), "invalid process status")
                    require(row["success"] == (row["exit_code"] == 0), "process status contradiction")
                    artifact(directory, row["stdout"])
                    artifact(directory, row["stderr"])
                terminals[i] = row
            elif event == "end":
                require(selected is not None and row["authority"] == "diagnostic-only" and row["runtime_body_universe"] == "unmeasured", "invalid terminal scope")
                require(set(row["pending_cases"]) == selected - cases.keys() and set(row["pending_commands"]) == attempts.keys() - terminals.keys(), "terminal population mismatch")
                require(not row["suite_passed"] or (not row["pending_cases"] and not row["pending_commands"] and all(r["outcome"] != "failed" for r in cases.values())), "successful suite with incomplete/failed cases")
                end = row
            else:
                raise ValueError(f"unknown event: {event}")
    require(begin is not None and plan_complete and selected is not None, "missing plan or selection")
    commands = []
    for i, attempt in attempts.items():
        terminal = terminals.get(i)
        row = {"attempt": attempt, "terminal": terminal, "spawn_pid_recorded": i in spawned,
               "observations": [], "producer_body_join": {"status": "unmeasured"}}
        if terminal and terminal["event"] == "command-terminal":
            row["observations"] = join_observations(directory, attempt, terminal)
            # Exact per-invocation def paths only: no leaf-name or cross-crate join.
            if attempt["kind"] != "selected-rustc":
                row["producer_body_join"] = {"status": "not-selected-compiler"}
            elif terminal["output_truncated"]:
                row["producer_body_join"] = {"status": "truncated-output"}
            else:
                try:
                    stderr = artifact(directory, terminal["stderr"]).decode("utf-8")
                except UnicodeError:
                    row["producer_body_join"] = {"status": "non-UTF8-output"}
                    commands.append(row)
                    continue
                bodies, anomalies = trust_ir_producer_scorecard.parse_bodies(stderr)
                hir = [obs["observation"] for obs in row["observations"] if obs["kind"] == "trust-body-census" and obs["status"] == "parsed"]
                if len(hir) == 1 and hir[0]["status"] == "complete":
                    body_map = {body["def"]: body for body in bodies}
                    known = {body["def"] for body in hir[0]["bodies"]}
                    row["producer_body_join"] = {"status": "parsed-diagnostic-only", "anomalies": anomalies,
                        "bodies": [{"hir": body, "producer": body_map.get(body["def"])} for body in hir[0]["bodies"]],
                        "unjoined_producer_events": [body for body in bodies if body["def"] not in known]}
                else:
                    row["producer_body_join"] = {"status": "no-complete-bound-HIR-census", "unjoined_producer_events": bodies, "anomalies": anomalies}
        commands.append(row)
    return {"schema": "trust.compiletest.census-report.v1", "authority": "diagnostic-only; caller must authenticate producer/corpus/process custody",
        "whole_corpus_complete": False, "runtime_body_universe": "unmeasured", "records": records,
        "recording_status": "footer-present" if end else "interrupted", "begin": begin, "end": end,
        "planned": [{**r, "current_source": current_file(r["source"]), "selected": key in selected, "terminal": cases.get(key)} for key, r in planned.items()],
        "collection_exclusions": exclusions, "commands": commands, "unmeasured": ["owner-admitted complete corpus", "unintercepted nested commands", "loaded executable image", "full dynamic/linked dependency closure", "Rust/Lean source refinement", "Lean computational declaration census"]}


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("directory", type=Path)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args(argv)
    result = read_census(args.directory)
    text = json.dumps(result, indent=2, sort_keys=True) + "\n"
    if args.output:
        with args.output.open("x") as stream:
            stream.write(text)
    else:
        print(text, end="")


if __name__ == "__main__":
    main()
