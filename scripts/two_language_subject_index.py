#!/usr/bin/env python3
"""Assemble the G3 subject index and producer body join from measured inputs.

This is the producer side of `scripts/completion_gates/check_g3_producer_totality.py`:
it writes the `trust.two-language.subject-index/v3` document the checker reads
through `--subject-graph` and the `trust.two-language.g3.producer-body-join/v1`
artifact it reads as `body_join`, from

  * a Rust producer scorecard (`trust.trust-ir.producer-scorecard.v1` data.json)
    whose per-file `measurement.control.census_raw` retains the compiler's HIR
    body census (`trust.rust.hir-body-census.v1` or `.v2`);
  * the Lean scorecard's supplied body census (`trust.clean-corpus.body-census/v1`)
    and, optionally, the compiler's Lean island census JSONL per admitted file
    (`-Ztrust-lean-census`), whose kernel roster names each declaration's payload,
    each given with the observed exit status of the compile that wrote it
    (`--lean-island-census FILE=CENSUS:EXIT`; the status is required);
  * the corpus manifest (`trust.two-language.corpus-manifest/v1`), which alone
    names admitted file IDs, lanes, paths and source hashes.

IDENTITY, and how every body is paired (each row discloses `paired_by`):

  stable-identity  a v2 HIR census row with a measured owning source, from a
                   control compile that exited 0: crate NAME + crate-free def
                   path + owning file SHA-256.  Independent of the
                   StableCrateId, which v1 is not.  The owning digest is
                   cross-checked, never taken from the row alone: it must be
                   the digest the SAME compile lists for that file in its own
                   loaded-source footer, and the digest that compile lists for
                   its own root input must equal the admitted file's manifest
                   SHA-256 (for every row, whichever file owns it).  A row
                   failing either check is demoted to printed-path and counted
                   as a reconciliation error.  (The body-census row finds its
                   compiler row by exact printed def WITHIN one compile, where
                   the census makes the printed def unique; and the scorecard
                   derives its body census from that same control census, so
                   that row match is a consistency read, not independent
                   evidence.  The identity is what is stable across compilers,
                   not the row match.)
  stable-identity-from-failed-compile
                   the same, from a control compile that exited non-zero.
                   Never counted as stable-identity; the file is also a
                   `rust.compiler-census-compile-failed` reconciliation error.
                   The exit status is read directly: the scorecard's census
                   status is not used for it, because `input_closure_incomplete`
                   there overwrites `compiler_failed`.  A control compile with
                   no integer exit status is printed-path and a
                   `rust.compiler-census-exit-unmeasured` error.
  kernel-identity  a Lean kernel-roster declaration from a compile that exited
                   0 and whose completion footer lists, for its own root input,
                   the admitted file's SHA-256 as its source-map checksum:
                   admitted file SHA-256 + declaration name + kernel payload
                   SHA-256.  A transcript whose root-input checksum is not the
                   admitted digest pairs printed-path, with a
                   `lean.island-input-differs-from-admitted` error.  (Only the
                   digest binds the transcript to the admitted file; its own
                   input label is not compared with the manifest path.)
  kernel-identity-from-failed-compile
                   the same, from an island census whose compile exited
                   non-zero.  Never counted as kernel-identity; the file is also
                   a `lean.island-census-compile-failed` reconciliation error.
  printed-path     everything else: the printed def path with its crate
                   disambiguator stripped (or the Lean name), plus the admitted
                   file SHA-256.  This is the correspondence the 4b2c audit
                   called diagnostic, and it is never reported as anything else.

Every pairing row also carries `process_status` (success / failed /
unmeasured) of the compile its identity was read from, and
`owning_source_checks`: for a v2 Rust row, `census_sources` and
`admitted_root_input`; for a Lean row with a usable island census,
`island_input_source`; otherwise null.

WHAT THIS DOES NOT DO.  It authors no authority.  Every subject-index field the
inputs do not measure is either `null` (where the checker reads no value) or,
where the checker demands a SHA-256, the published sentinel
`sha256("trust.two-language.subject-index.unmeasured/v1:<field>")`; every
sentinel is listed in the pairing report.  No Trust-IR module is retained by any
input, so the one joined module's artifact is an explicit `unretained` locator,
not a module.  Only the three roots the checker recomputes are real roots; the
other eight are sentinels.  The checker's authority refusals (authenticated body
census, body identity/content binding, module validator, the other eight roots)
therefore stay red by construction: that is the measurement, not a defect.

RETIREMENT HAZARD.  The sentinel body digests, the eight sentinel roots and the
`unretained` module locator are well-formed SHA-256s and a well-formed module
reference, so they are refused today ONLY because the checker's authority
conjuncts (`require_body_identity_authority`, `all_joined_modules_valid`,
`subject_index_roots_match`) refuse everything this producer can emit.  Before
any of those conjuncts is retired or relaxed, the checker must first learn to
reject these placeholders by value (every `sha256(SENTINEL_PREFIX + field)`,
and a module artifact whose document says `"trust_ir": "unretained"`);
otherwise retiring the conjunct turns a published placeholder into a pass.

Output (all under --out-dir, root-relative, deterministic bytes):
  subject-index.json, body-join.json, pairing-report.json,
  modules/<program>.unretained-module.json

Exit: 0 emitted with zero reconciliation errors; 3 emitted WITH reconciliation
errors (listed by class in the report); 2 refused malformed input, nothing written.
"""

from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
import re
import sys
from pathlib import Path
from typing import Any

SUBJECT_SCHEMA = "trust.two-language.subject-index/v3"
JOIN_SCHEMA = "trust.two-language.g3.producer-body-join/v1"
REPORT_SCHEMA = "trust.two-language.g3.subject-identity-pairing/v1"
MODULE_SCHEMA = "trust.two-language.g3.unretained-module/v1"
IDENTITY_SCHEMA = "trust.two-language.body-identity/v1"
CORPUS_SCHEMA = "trust.two-language.corpus-manifest/v1"
RUST_SCORECARD_SCHEMA = "trust.trust-ir.producer-scorecard.v1"
LEAN_CENSUS_SCHEMA = "trust.clean-corpus.body-census/v1"
GOAL = "TRUST-TWO-LANGUAGE-100"
SENTINEL_PREFIX = "trust.two-language.subject-index.unmeasured/v1:"
# The checker recomputes exactly these three roots from rows.
RECOMPUTED_ROOTS = ("admitted_files", "reachable_bodies", "modules")
ROOT_NAMES = ("admitted_files", "reachable_bodies", "refinement_certificates", "obligations",
              "proof_certificates", "modules", "codegen_matrix_cells", "objects",
              "translation_evidence", "call_edges", "executables")
BODY_DIGESTS = ("source_language_semantics_sha256", "source_semantics_sha256",
                "trust_ir_semantics_sha256", "trust_ir_sha256", "ssa_epoch_sha256",
                "effect_summary_sha256")
PAIRED_BY = ("stable-identity", "stable-identity-from-failed-compile", "kernel-identity",
             "kernel-identity-from-failed-compile", "printed-path")
# `def_path_debug_str`: `<crate>[<top 16 bits of StableCrateId, 4 hex>]<path>`.
PRINTED_PATH = re.compile(r"^([^\[\]:]+)\[[0-9a-f]{4}\](::.*)$")
# A program ID is also a filename component; never accept path syntax here.
PROGRAM_ID = re.compile(r"[A-Za-z0-9][A-Za-z0-9_-]*")
SCRIPTS = Path(__file__).resolve().parent


class InputRefusal(Exception):
    """Malformed input: nothing is written."""


def sentinel(name: str) -> str:
    return hashlib.sha256((SENTINEL_PREFIX + name).encode("utf-8")).hexdigest()


def canonical_bytes(value: Any) -> bytes:
    return json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=True,
                      allow_nan=False).encode("utf-8")


def canonical_root(rows: list[Any]) -> str:
    """Exactly the checker's `canonical_root` over its sort order."""
    ordered = sorted(rows, key=lambda row: json.dumps(row, sort_keys=True, separators=(",", ":")))
    return hashlib.sha256(canonical_bytes(ordered)).hexdigest()


def _unique(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise ValueError(f"duplicate JSON key {key!r}")
        result[key] = value
    return result


def _no_constant(value: str) -> Any:
    raise ValueError(f"non-finite JSON constant {value}")


def load_json(path: Path) -> Any:
    try:
        return json.loads(path.read_text(encoding="utf-8"), object_pairs_hook=_unique,
                          parse_constant=_no_constant)
    except (OSError, UnicodeError, ValueError, RecursionError) as exc:
        raise InputRefusal(f"cannot read {path} as strict JSON: {exc}") from exc


def root_path(root: Path, raw: str, where: str) -> Path:
    path = Path(raw)
    if path.is_absolute() or "\\" in raw or any(part in {"", ".", ".."} for part in raw.split("/")):
        raise InputRefusal(f"{where}: path must be canonical and root-relative: {raw!r}")
    resolved = (root / path).resolve()
    if not resolved.is_relative_to(root):
        raise InputRefusal(f"{where}: path escapes root: {raw!r}")
    return resolved


def file_sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def load_by_path(name: str, path: Path) -> Any:
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise InputRefusal(f"cannot load {path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


def identity_digest(identity: dict[str, Any]) -> str:
    return hashlib.sha256(canonical_bytes({"schema": IDENTITY_SCHEMA, **identity})).hexdigest()


class Producer:
    def __init__(self, root: Path) -> None:
        self.root = root
        self.errors: dict[str, list[str]] = {}
        self.inputs: list[dict[str, str]] = []
        self._scorecard = None
        self._lean_census = None

    def error(self, kind: str, detail: str) -> None:
        self.errors.setdefault(kind, []).append(detail)

    def read(self, raw: str, where: str) -> Any:
        path = root_path(self.root, raw, where)
        self.inputs.append({"role": where, "path": raw, "sha256": file_sha256(path)})
        return load_json(path)

    # ---- admission -------------------------------------------------------

    def admission(self, corpus: Any, run_id: str, revision: str) -> dict[str, tuple[str, str, str]]:
        if not isinstance(corpus, dict) or corpus.get("schema") != CORPUS_SCHEMA:
            raise InputRefusal("corpus manifest has the wrong schema")
        if (corpus.get("goal_id"), corpus.get("acceptance_run_id"), corpus.get("source_revision")) != (
                GOAL, run_id, revision):
            raise InputRefusal("corpus manifest does not name this acceptance run and revision")
        admitted: dict[str, tuple[str, str, str]] = {}
        for lane in ("rust", "lean", "mixed"):
            entries = corpus.get(lane, {}).get("entries") if isinstance(corpus.get(lane), dict) else None
            if not isinstance(entries, list):
                raise InputRefusal(f"corpus manifest lane {lane} has no entries")
            for entry in entries:
                if not isinstance(entry, dict) or not isinstance(entry.get("id"), str) or not entry["id"]:
                    raise InputRefusal(f"corpus manifest {lane}: malformed entry")
                if entry["id"] in admitted:
                    raise InputRefusal(f"corpus manifest: duplicate admitted id {entry['id']}")
                if entry.get("admitted") is not True:
                    continue
                source = entry.get("source")
                if (not isinstance(source, dict) or not isinstance(source.get("path"), str)
                        or not isinstance(source.get("sha256"), str)):
                    raise InputRefusal(f"corpus manifest {entry['id']}: malformed source")
                admitted[entry["id"]] = (lane, source["path"], source["sha256"])
        return admitted

    # ---- Rust ------------------------------------------------------------

    def scorecard(self) -> Any:
        if self._scorecard is None:
            self._scorecard = load_by_path("trust_ir_producer_scorecard_for_subject_index",
                                           SCRIPTS / "trust_ir_producer_scorecard.py")
        return self._scorecard

    def rust_census_rows(self, file_row: dict[str, Any], path: str) -> dict[str, Any]:
        """The control (lowering-off) compiler's HIR census for one file,
        validated by the scorecard's own strict reader: `rows` by printed def
        (None when there is no usable census), `schema` (or why not),
        `sources` (the footer's own loaded-source digests), `input` (the
        compile's root input label) and `process_status` of that compile."""
        measurement = file_row.get("measurement") if isinstance(file_row, dict) else None
        control = measurement.get("control") if isinstance(measurement, dict) else None
        exit_code = control.get("exit_code") if isinstance(control, dict) else None
        context: dict[str, Any] = {"rows": None, "sources": {}, "input": None,
                                   "process_status": process_status(exit_code)}
        if not isinstance(control, dict) or not isinstance(control.get("census_raw"), str):
            self.error("rust.compiler-census-absent", path)
            return {**context, "schema": "no retained control compiler census"}
        parsed = self.scorecard().parse_compiler_census(
            control["census_raw"], input_path=control.get("input"), lowering=False,
            exit_code=exit_code)
        if parsed["status"] not in {"complete", "input_closure_incomplete"}:
            self.error("rust.compiler-census-unusable", f"{path}: {parsed['status']} {parsed['errors'][:2]}")
            return {**context, "schema": f"control compiler census is {parsed['status']}"}
        # The scorecard's census status does not carry the exit on its own:
        # `input_closure_incomplete` (any tracked file or env! read) replaces
        # `compiler_failed`.  The process outcome is therefore read here from
        # the exit status itself, never from `parsed["status"]`.
        if context["process_status"] == "failed":
            self.error("rust.compiler-census-compile-failed", f"{path}: exit {exit_code}")
        elif context["process_status"] != "success":
            self.error("rust.compiler-census-exit-unmeasured", f"{path}: exit {exit_code!r}")
        return {**context, "rows": {body["def"]: body for body in parsed["bodies"]},
                "schema": parsed["schema"], "input": control["input"],
                "sources": {source["file"]: source["sha256"] for source in parsed["sources"]}}

    def rust_bodies(self, doc: Any, admitted: dict[str, tuple[str, str, str]]) -> list[dict[str, Any]]:
        if not isinstance(doc, dict) or doc.get("schema") != RUST_SCORECARD_SCHEMA:
            raise InputRefusal("Rust scorecard has the wrong schema")
        corpora = doc.get("corpora")
        if not isinstance(corpora, dict) or not corpora:
            raise InputRefusal("Rust scorecard has no corpora")
        by_path = {path: (fid, sha) for fid, (lane, path, sha) in admitted.items() if lane == "rust"}
        bodies: list[dict[str, Any]] = []
        seen: set[tuple[str, str, str]] = set()
        measured: set[str] = set()
        for name in sorted(corpora):
            corpus = corpora[name]
            census = corpus.get("body_census") if isinstance(corpus, dict) else None
            if not isinstance(census, dict) or not isinstance(census.get("bodies"), list):
                raise InputRefusal(f"Rust corpus {name}: no body census")
            files = {row.get("file"): row for row in corpus.get("files", []) if isinstance(row, dict)}
            measured |= {path for path in files if isinstance(path, str)}
            compiler: dict[str, dict[str, Any]] = {}
            listed: dict[str, set[str]] = {}
            for row in census["bodies"]:
                if not isinstance(row, dict) or set(row) != {"file", "def", "kind"} or not all(
                        isinstance(row[key], str) and row[key] for key in row):
                    raise InputRefusal(f"Rust corpus {name}: malformed body census row")
                key = (row["file"], row["def"], row["kind"])
                if key in seen:
                    raise InputRefusal(f"duplicate Rust body census row {key}")
                seen.add(key)
                path = row["file"]
                if path not in by_path:
                    self.error("admission.producer-file-not-admitted", f"rust {path}")
                    continue
                if path not in compiler:
                    compiler[path] = self.rust_census_rows(files.get(path, {}), path)
                context = compiler[path]
                listed.setdefault(path, set()).add(row["def"])
                fid, admitted_sha = by_path[path]
                hir = None
                if context["rows"] is not None:
                    hir = context["rows"].get(row["def"])
                    if hir is None:
                        self.error("rust.body-census-row-without-compiler-row", f"{path} {row['def']}")
                bodies.append(self.rust_identity(row, hir, context, fid, admitted_sha, path))
            # A measured admitted file with NO listed body still has its census
            # read: an unlisted compiler row there is an omission, not zero.
            for path in sorted(p for p in files if isinstance(p, str) and p in by_path and p not in compiler):
                compiler[path] = self.rust_census_rows(files[path], path)
            for path, context in sorted(compiler.items()):
                for extra in sorted(set(context["rows"] or ()) - listed.get(path, set())):
                    self.error("rust.compiler-census-row-unlisted", f"{path} {extra}")
        for path, (fid, _) in sorted(by_path.items()):
            if path not in measured:
                self.error("admission.admitted-file-unmeasured", f"rust {fid} {path}")
        return bodies

    def rust_identity(self, row: dict[str, str], hir: dict[str, Any] | None, context: dict[str, Any],
                      fid: str, admitted_sha: str, path: str) -> dict[str, Any]:
        """`context["schema"]` is the census schema, or why there is no usable census."""
        schema = context["schema"]
        source = hir.get("source") if hir is not None else None
        v2 = schema == "trust.rust.hir-body-census.v2"
        measured = v2 and isinstance(source, dict) and isinstance(source.get("sha256"), str)
        checks = None
        demoted = None
        status = context["process_status"]
        if hir is not None and measured:
            # Cross-check the row's owning digest against the SAME compile's
            # loaded-source footer, and the digest that compile lists for its
            # own root input against the admitted file's, for EVERY row: a
            # body owned by a module file of a compile that built other root
            # bytes is not a body of the admitted file.
            listed_sha = context["sources"].get(source["file"])
            root_sha = context["sources"].get(context["input"])
            checks = {"census_sources": "match" if listed_sha == source["sha256"] else "mismatch",
                      "admitted_root_input": "match" if root_sha == admitted_sha else "mismatch"}
            if checks["census_sources"] != "match":
                self.error("rust.owning-source-not-in-census-sources", f"{path} {row['def']}")
                demoted = ("v2 owning source digest is not the digest this compile lists for "
                           f"{source['file']}")
            elif checks["admitted_root_input"] != "match":
                self.error("rust.compile-root-input-differs-from-admitted", f"{path} {row['def']}")
                demoted = "the compile's own root-input digest is not the admitted file's"
            elif status not in {"success", "failed"}:
                demoted = f"control compile exit status is {status}"
        if hir is not None and measured and demoted is None:
            # A compile that did not exit 0 is disclosed as such, never
            # counted as stable-identity (its file is also a
            # `rust.compiler-census-compile-failed` reconciliation error).
            failed = status != "success"
            identity = {"language": "rust",
                        "basis": "stable-identity-from-failed-compile" if failed else "stable-identity",
                        "crate_name": hir["crate_name"], "def_path_no_crate": hir["def_path_no_crate"],
                        "owning_source_sha256": source["sha256"]}
            reason = f"control compile process is {status}" if failed else None
        else:
            match = PRINTED_PATH.fullmatch(row["def"])
            printed = match.group(1) + match.group(2) if match else row["def"]
            identity = {"language": "rust", "basis": "printed-path",
                        "admitted_source_sha256": admitted_sha, "printed_path": printed}
            if hir is None:
                reason = ("no compiler census row for this def" if schema.startswith("trust.")
                          else schema)
            elif not v2:
                reason = f"compiler census is {schema}: no crate-independent identity fields"
            elif demoted is not None:
                reason = demoted
            else:
                reason = "v2 census row discloses its owning source as unmeasured"
            if not match:
                reason += "; printed path carries no crate disambiguator, used verbatim"
        return {"language": "rust", "file_id": fid, "source_body": row["def"],
                "source_kind": row["kind"], "identity": identity, "reason": reason,
                "process_status": context["process_status"], "owning_source_checks": checks}

    # ---- Lean ------------------------------------------------------------

    def lean_rosters(self, specs: list[str], admitted: dict[str, tuple[str, str, str]]) -> dict[str, dict]:
        """Per admitted Lean file path: {"names": {declaration name: kernel
        roster row}, "process_status": of the compile that wrote the census,
        "input_source": whether the digest the transcript's own completion
        footer lists for its root input is the admitted file's SHA-256}."""
        by_path = {path: sha for lane, path, sha in admitted.values() if lane == "lean"}
        rosters: dict[str, dict] = {}
        for spec in specs:
            path, sep, located = spec.partition("=")
            census, colon, exit_text = located.rpartition(":")
            if not sep or not colon or not census or not re.fullmatch(r"-?[0-9]+", exit_text) or path in rosters:
                raise InputRefusal(f"--lean-island-census expects unique FILE=CENSUS:EXIT "
                                   f"(EXIT the compile's observed integer exit status), got {spec!r}")
            exit_code = int(exit_text)
            if path not in by_path:
                raise InputRefusal(f"--lean-island-census names unadmitted Lean file {path}")
            census_path = root_path(self.root, census, "lean island census")
            raw = census_path.read_bytes()
            self.inputs.append({"role": f"lean island census {path}", "path": census,
                                "sha256": hashlib.sha256(raw).hexdigest()})
            try:
                begin = json.loads(raw.split(b"\n", 1)[0])
                label = begin["input"]
                verification, lowering = begin["verification_enabled"], begin["direct_lowering"]
            except (ValueError, KeyError, TypeError) as exc:
                raise InputRefusal(f"Lean island census {census}: no begin record: {exc}") from exc
            if self._lean_census is None:
                self._lean_census = load_by_path("lean_island_census_for_subject_index",
                                                 SCRIPTS / "lean_island_census.py")
            # The transcript is parsed against its own labels (an internal-
            # consistency read); it is bound to the admitted file only by the
            # root-input digest check below, never by label.
            parsed = self._lean_census.parse_census(raw, input_path=label, verification=verification,
                                                    lowering=lowering, exit_code=exit_code)
            status = parsed["process_status"]
            if status != "success":
                self.error("lean.island-census-compile-failed", f"{path}: exit {exit_code}")
            if parsed["record_status"] != "observed-complete" or parsed["errors"]:
                self.error("lean.island-census-unusable", f"{path}: {parsed['record_status']}")
                rosters[path] = {"names": {}, "process_status": status, "input_source": None}
                continue
            # The Lean counterpart of the Rust census-sources check: the
            # compile's own checksum of its root input must be the admitted
            # file's digest (a source-map checksum, which for a text file is
            # the SHA-256 of its bytes; the labels differ and are not compared).
            [footer] = [event for event in parsed["validated_prefix"] if event["event"] == "complete"]
            listed = {source["file"]: source["source_map_checksum_sha256"]
                      for source in footer["loaded_sources"]}
            input_source = "match" if listed.get(label) == by_path[path] else "mismatch"
            if input_source != "match":
                self.error("lean.island-input-differs-from-admitted", f"{path}: {label}")
            names: dict[str, dict] = {}
            for entry in parsed["declarations"]:
                declaration = entry["declaration"]
                if declaration["name"] in names:
                    self.error("lean.kernel-roster-duplicate-name", f"{path} {declaration['name']}")
                    continue
                names[declaration["name"]] = declaration
            rosters[path] = {"names": names, "process_status": status, "input_source": input_source}
        return rosters

    def lean_bodies(self, census: Any, admitted: dict[str, tuple[str, str, str]],
                    rosters: dict[str, dict]) -> list[dict[str, Any]]:
        if not isinstance(census, dict) or census.get("schema") != LEAN_CENSUS_SCHEMA or not isinstance(
                census.get("declarations"), list):
            raise InputRefusal("Lean body census has the wrong schema")
        by_path = {path: (fid, sha) for fid, (lane, path, sha) in admitted.items() if lane == "lean"}
        bodies: list[dict[str, Any]] = []
        seen: set[tuple[str, str]] = set()
        listed: dict[str, set[str]] = {}
        for row in census["declarations"]:
            if not isinstance(row, dict) or set(row) != {"file", "name", "kind"} or not all(
                    isinstance(row[key], str) and row[key] for key in row):
                raise InputRefusal("Lean body census: malformed declaration")
            if (row["file"], row["name"]) in seen:
                raise InputRefusal(f"duplicate Lean body census declaration {row['file']}:{row['name']}")
            seen.add((row["file"], row["name"]))
            if row["file"] not in by_path:
                self.error("admission.producer-file-not-admitted", f"lean {row['file']}")
                continue
            listed.setdefault(row["file"], set()).add(row["name"])
            if row["kind"] != "computational":
                continue
            fid, admitted_sha = by_path[row["file"]]
            supplied = rosters.get(row["file"])
            roster = supplied["names"] if supplied else None
            status = supplied["process_status"] if supplied else "unmeasured"
            input_source = supplied["input_source"] if supplied else None
            kernel = roster.get(row["name"]) if roster else None
            if (kernel is not None and isinstance(kernel.get("kernel_payload_sha256"), str)
                    and input_source == "match"):
                # A roster from a compile that did not exit 0 is disclosed as
                # such, never counted as kernel-identity.
                failed = status != "success"
                identity = {"language": "lean",
                            "basis": "kernel-identity-from-failed-compile" if failed else "kernel-identity",
                            "admitted_source_sha256": admitted_sha, "name": row["name"],
                            "kernel_payload_sha256": kernel["kernel_payload_sha256"]}
                reason = f"island census compile process is {status}" if failed else None
            else:
                kernel_row = kernel is not None and isinstance(kernel.get("kernel_payload_sha256"), str)
                if roster and not kernel_row:
                    self.error("lean.census-declaration-without-kernel-row", f"{row['file']} {row['name']}")
                identity = {"language": "lean", "basis": "printed-path",
                            "admitted_source_sha256": admitted_sha, "printed_path": row["name"]}
                reason = ("no usable Lean island census supplied for this file" if not roster
                          else "no kernel roster row for this name" if not kernel_row
                          else "the island compile's root-input checksum is not the admitted file's")
            bodies.append({"language": "lean", "file_id": fid, "source_body": row["name"],
                           "source_kind": row["kind"], "identity": identity, "reason": reason,
                           "process_status": status,
                           "owning_source_checks": (None if input_source is None
                                                    else {"island_input_source": input_source})})
        for path, supplied in sorted(rosters.items()):
            for name, declaration in sorted(supplied["names"].items()):
                classification = (declaration.get("kernel_classification") or {}).get("kind")
                if classification == "computational-candidate" and name not in listed.get(path, set()):
                    self.error("lean.kernel-computational-unlisted", f"{path} {name}")
        return bodies

    # ---- assembly --------------------------------------------------------

    def assemble(self, bodies: list[dict[str, Any]], admitted: dict[str, tuple[str, str, str]],
                 program_id: str, run_id: str, revision: str, out_dir: str) -> dict[str, Any]:
        module_id = f"{program_id}.joined"
        index: dict[str, dict[str, Any]] = {}
        for body in bodies:
            digest = identity_digest(body["identity"])
            body_id = f"{body['language']}/{body['identity']['basis']}/{digest}"
            if body_id in index:
                raise InputRefusal(f"two bodies share one identity {body_id}: "
                                   f"{index[body_id]['source_body']} and {body['source_body']}")
            index[body_id] = {**body, "function_identity_sha256": digest}
        ordered = sorted(index)
        subject_bodies = [{
            "id": body_id, "language": index[body_id]["language"],
            "function_identity_sha256": index[body_id]["function_identity_sha256"],
            "source_language_semantics_id": None, "trust_ir_semantics_id": None,
            **{field: sentinel(field) for field in BODY_DIGESTS},
        } for body_id in ordered]
        module_doc = {"schema": MODULE_SCHEMA, "program_id": program_id, "module_id": module_id,
                      "trust_ir": "unretained", "body_ids": ordered,
                      "note": "No input retains a Trust-IR module; this is a locator, not a module."}
        module_path = f"{out_dir}/modules/{program_id}.unretained-module.json"
        module_bytes = serialize(module_doc)
        module = {"id": module_id,
                  "artifact": {"path": module_path, "sha256": hashlib.sha256(module_bytes).hexdigest()},
                  "body_ids": ordered, "call_edge_ids": None, "obligation_ids": None,
                  "refinement_certificate_body_ids": None, "proof_certificate_ids": None,
                  "assumption_closure_sha256": None, "contextual_refinement_evidence": None}
        file_ids = sorted(admitted)
        program = {"id": program_id, "entrypoints": None, "admitted_file_ids": file_ids,
                   "bodies": subject_bodies, "refinement_certificates": None, "obligations": None,
                   "proof_certificates": None, "modules": [module], "objects": None,
                   "translation_evidence": None, "executables": None, "call_edges": None,
                   "contextual_refinement": None}
        populations = {
            "admitted_files": [{"program_id": program_id, "file_id": fid} for fid in file_ids],
            "reachable_bodies": [{"program_id": program_id, **body} for body in subject_bodies],
            "modules": [{"program_id": program_id, **module}],
        }
        roots = {name: (canonical_root(populations[name]) if name in RECOMPUTED_ROOTS
                        else sentinel(f"roots.{name}")) for name in ROOT_NAMES}
        subject = {"schema": SUBJECT_SCHEMA, "goal_id": GOAL, "acceptance_run_id": run_id,
                   "source_revision": revision, "programs": [program], "roots": roots,
                   "release_executable": None}
        join = {"schema": JOIN_SCHEMA, "rows": [{
            "program_id": program_id, "file_id": index[body_id]["file_id"],
            "language": index[body_id]["language"], "source_body": index[body_id]["source_body"],
            "source_kind": index[body_id]["source_kind"], "body_id": body_id, "module_id": module_id,
        } for body_id in ordered]}
        pairing = [{"body_id": body_id, "file_id": index[body_id]["file_id"],
                    "language": index[body_id]["language"], "source_body": index[body_id]["source_body"],
                    "paired_by": index[body_id]["identity"]["basis"],
                    "identity": index[body_id]["identity"], "reason": index[body_id]["reason"],
                    "process_status": index[body_id]["process_status"],
                    "owning_source_checks": index[body_id]["owning_source_checks"]}
                   for body_id in ordered]
        counts = {basis: sum(row["paired_by"] == basis for row in pairing) for basis in PAIRED_BY}
        report = {
            "schema": REPORT_SCHEMA, "authority": "none: identity correlation only; no field is proof, "
            "census or module authority", "acceptance_run_id": run_id, "source_revision": revision,
            "inputs": sorted(self.inputs, key=lambda row: (row["role"], row["path"])),
            "bodies": len(pairing), "paired_by": counts,
            "by_language": {lang: {basis: sum(1 for row in pairing if row["language"] == lang
                                              and row["paired_by"] == basis) for basis in PAIRED_BY}
                            for lang in ("rust", "lean")},
            "rows": pairing,
            "reconciliation_errors": {kind: sorted(details) for kind, details in sorted(self.errors.items())},
            "reconciliation_error_counts": {kind: len(details) for kind, details in sorted(self.errors.items())},
            "unmeasured": {
                "body_digest_sentinels": {field: sentinel(field) for field in BODY_DIGESTS},
                "null_body_fields": ["source_language_semantics_id", "trust_ir_semantics_id"],
                "root_sentinels": {name: roots[name] for name in ROOT_NAMES if name not in RECOMPUTED_ROOTS},
                "null_program_fields": sorted(key for key, value in program.items() if value is None),
                "null_module_fields": sorted(key for key, value in module.items() if value is None),
                "module_artifact": "unretained locator, not a Trust-IR module",
                "mixed_lane": "admitted mixed files carry no producer census; their bodies are not indexed",
            },
        }
        return {"subject-index.json": subject, "body-join.json": join, "pairing-report.json": report,
                f"modules/{program_id}.unretained-module.json": module_doc}


def process_status(exit_code: Any) -> str:
    """The observed process outcome, as lean_island_census.parse_census names it."""
    if type(exit_code) is not int:
        return "unmeasured"
    return "success" if exit_code == 0 else "failed"


def serialize(value: Any) -> bytes:
    return json.dumps(value, sort_keys=True, indent=1, ensure_ascii=True, allow_nan=False).encode() + b"\n"


def produce(args: argparse.Namespace) -> tuple[int, dict[str, Any]]:
    if not isinstance(args.program_id, str) or PROGRAM_ID.fullmatch(args.program_id) is None:
        raise InputRefusal("--program-id must be one ASCII filename component matching "
                           "[A-Za-z0-9][A-Za-z0-9_-]*")
    root = Path(args.root).resolve()
    producer = Producer(root)
    admitted = producer.admission(producer.read(args.corpus_manifest, "corpus manifest"),
                                  args.acceptance_run_id, args.source_revision)
    bodies = producer.rust_bodies(producer.read(args.rust_scorecard, "rust scorecard"), admitted)
    rosters = producer.lean_rosters(args.lean_island_census, admitted)
    bodies += producer.lean_bodies(producer.read(args.lean_body_census, "lean body census"),
                                   admitted, rosters)
    outputs = producer.assemble(bodies, admitted, args.program_id, args.acceptance_run_id,
                                args.source_revision, args.out_dir)
    return (3 if producer.errors else 0), outputs


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--root", required=True)
    parser.add_argument("--corpus-manifest", required=True, help="root-relative")
    parser.add_argument("--rust-scorecard", required=True, help="root-relative data.json")
    parser.add_argument("--lean-body-census", required=True, help="root-relative")
    parser.add_argument("--lean-island-census", action="append", default=[], metavar="FILE=CENSUS:EXIT",
                        help="admitted Lean file path = root-relative compiler island census JSONL "
                        ": the observed integer exit status of the compile that wrote it")
    parser.add_argument("--acceptance-run-id", required=True)
    parser.add_argument("--source-revision", required=True)
    parser.add_argument("--program-id", default="program",
                        help="one ASCII filename component: [A-Za-z0-9][A-Za-z0-9_-]*")
    parser.add_argument("--out-dir", required=True, help="root-relative; created, never overwritten")
    args = parser.parse_args(argv)
    try:
        code, outputs = produce(args)
        root = Path(args.root).resolve()
        out = root_path(root, args.out_dir, "--out-dir")
        rendered = {name: serialize(value) for name, value in outputs.items()}
        if out.exists():
            raise InputRefusal(f"--out-dir already exists: {args.out_dir}")
    except (InputRefusal, OSError, ValueError, KeyError, TypeError) as exc:
        print(f"two_language_subject_index: refused: {exc}", file=sys.stderr)
        return 2
    for name, data in sorted(rendered.items()):
        target = out / name
        target.parent.mkdir(parents=True, exist_ok=True)
        with target.open("xb") as stream:
            stream.write(data)
    report = outputs["pairing-report.json"]
    print(json.dumps({"bodies": report["bodies"], "paired_by": report["paired_by"],
                      "reconciliation_error_counts": report["reconciliation_error_counts"],
                      "out_dir": args.out_dir}, sort_keys=True))
    return code


if __name__ == "__main__":
    raise SystemExit(main())
