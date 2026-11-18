#!/usr/bin/env python3
"""Trust's landing gate: the legs a landing needs beyond the pre-push hook,
selected from what the change can reach, sized to the host, and never run twice
on the same inputs.

    python3 scripts/land_gate.py plan    [--base REF] [--head REF] [--json] [--run [--no-cache]]
    python3 scripts/land_gate.py run     [--base REF] [--dry-run] [--only LEG ...] [--no-cache]
    python3 scripts/land_gate.py land    [--base REF] [--no-cache]
    python3 scripts/land_gate.py replay  [--last N] [--ref origin/main] [--json PATH]
    python3 scripts/land_gate.py explain PATH ...
    python3 scripts/land_gate.py key     LEG [--base REF]
    python3 scripts/land_gate.py prefetch [--check]   (fill the local registry the graph check reads)
    python3 scripts/land_gate.py push-rows [--expect-tip SHA]   (the push-rows leg's runner)
    python3 scripts/land_gate.py rows --check [--rev REV]   (gates/land.toml covers the pushed commit)

WHAT A LANDING RUNS. The pre-push hook (scripts/hooks/pre-push) runs the push
profile: the `fast.*` rows, verify.executes, and the four `scoped.*` lanes,
which scope themselves to the pushed diff. Until 2026-10-14 everything else a
landing needed was a runbook: the cohort trains (E1: docs/first-party-pin-ledger.md)
ran `x.py check --stage 1 --all-targets`, the tests/ui/trust suite, the trust
run-make tests, the compiler unit-test lane and the crates/ tests of every crate
a move reached, by hand, after every merge of a moving main (E1: about 15 hours
of gate time). This script is those legs, automated:

  compiler-check        x.py check --stage 1 --all-targets
  ui-trust              x.py test --stage 1 tests/ui/trust (or only the changed tests)
  run-make-trust        x.py test --stage 1 tests/run-make --test-args trust (or only the changed dirs),
                        less the trust-cg subset compiler-unit-tests judges with its stricter rule
  compiler-unit-tests   scripts/check_compiler_unit_tests.sh, for every compiler crate (and
                        rustc_private crate) the change REACHES, not only the ones it touches
  crates-tests          scripts/check_crates_tests_scoped.py, for every crates/ member the change
                        reaches that the hook's lane (the members the landing PUSH touches) does
                        not run; with no hook crates lane answering (no hook, or a push profile
                        without it), the hook's lane itself
                        over the landing range too (touched members, moved instruments under its
                        instrument rules), never a touched member from a cached PASS; never a
                        member the lane cannot build on this host. A member whose tests compile
                        through a Trust rustc (it is, or depends on, crates/trust-integration-tests)
                        runs against THIS tree's stage 1: the leg prepares it as the stage-1
                        suites do and passes it as TRUST_RUSTC (TRUST_RUSTC-1)
  push-rows             with no hook answering only, and FIRST: every push-profile row the hook
                        would run that no leg here covers, run and graded as the hook grades it
                        on the landing push (this checkout's HEAD onto origin's main tip, read
                        from the remote when the leg runs; NOT JUDGED unless HEAD contains it
                        and it is the tip the other legs were planned onto)
  olean-audit           scripts/regen-trustir-oleans.sh --check
  bootstrap-tests       x.py test --stage 1 src/bootstrap (its step-graph snapshots count the crate graph)
  targo-trust           targo --unverified test --manifest-path targo-trust/Cargo.toml: its own
                        workspace, whose test targets no x.py step compiles
  native-targo-tests    x.py test --stage 1 src/tools/targo: native Cargo's workspace and fixtures,
                        using bootstrap's tested compiler/std/rustdoc and fixture shims
  tidy                  x.py test --stage 1 tidy (every tracked path is its input)
  tcb-panic-ratchet     scripts/check_tcb_panic_freedom.sh
  ir-cohort             scripts/check_ir_cohort.py

The last three were added 2026-10-19: all three Inc 6 defects (368d75f732)
got past the gate, a red bootstrap snapshot, an E0308 in a targo-trust test
target, and tidy's own reds, because no leg ran those.

WHETHER THE HOOK RUNS AT ALL (LAND-GATE-HOOKLESS-1, 2026-11-02). Everything
above assumes the push that lands this tree runs scripts/hooks/pre-push. Hook
state is per clone and defaults to unset, and a clone without it pushes with
no hook row run: the combined G1+G3 landing (a4c4157ffe) changed
crates/trust-vcgen, its GREEN gate's crates leg left trust-vcgen to the hook
(the member was touched), no hook was installed, and main took a deterministic
trust-vcgen red. So every run decides (push_hook_state) whether the hook is
ACTIVE, by four rules, each named when it decides:
  installed     git resolves this worktree's hooks directory (`git rev-parse
                --git-path hooks`, which answers core.hooksPath) to THIS tree's
                scripts/hooks, and scripts/hooks/pre-push there is an executable
                file (hook_installed). Git is asked twice (hook_query_envs) and
                both must answer: with its repository-local variables and every
                environment-scoped config variable removed (git_query_env: a
                GIT_CONFIG_COUNT/KEY/VALUE triple or a `git -c` only this process
                carries is not the clone's, and a plain `git push` from another
                shell would run no hook; round 2, D4), and in this process's own
                environment (the ACTIVE line says to push from this shell, and
                such a value that sends its hooks elsewhere makes that push run
                none; round 3, D1).
  push-range    what the landing push carries can be read (read_landing:
                origin's main tip from the remote, a commit in this clone).
  hook-path     neither the change (base..head) nor the landing push (the tree
                diff origin's main tip..head; round 3, D2: `--base C` must not
                hide a hook edit made before C) edits anything the hook on its
                own push runs or reads: scripts/hooks/, the push-profile
                manifest, the crates lane and the scripts/lib modules it imports
                (HOOK_ANSWER_PATHS, round 2, D2). The hook that runs on the push
                is the landed tree's.
  push-profile  the push profile at the landed head can be read (`--list
                push`): the hook runs every row it lists. Which covered rows
                a leg leaves to the hook is that profile's own answer
                (PushHook.answers, hook_row_problem): a required row running
                exactly the argued command (round 2, D2).
Anything else, or a question git cannot answer, is NOT active. Not active,
the crates leg runs the hook's lane itself over the landing push's range
(`--range <tip>...<head>`: the touched members and the moved instruments, judged
by the lane's own rules, round 2's D3; the tip, not the selection base, round
3's D2) beside the reached members, never answers a touched member from a
cached PASS; compiler-check, which stands in for the hook's scoped row, is
selected when the push's range reaches it too; and the push-rows leg runs
first (round 3's D5) the hook's other rows on the landing push onto origin's
main tip (round 2's D1). A row is covered only when its leg's verdict implies
the row's whole judgement (round 4's D3: scoped.targo-trust-unit-tests FAILs a
zero-passed unit run, which the targo-trust leg's exit status cannot see, so
push-rows runs it). A covered row runs there anyway when its script is not the
bytes its coverage was argued for, when the push edits what its leg reads
another way, or when the pushed ledger quarantines its lane
(covered_row_problem, round 3's D3 and D4). push-rows grades each row's raw
output bytes with patterns that imply the hook's greps (round 4's D4). With no
hook answering, `run` judges nothing before any leg when the landing push
cannot be stated (round 3's D5). The mode is in the crates leg's key (only
that leg's), so a PASS cached in one mode never answers for the other.
Active, the crates leg leaves to the hook only the members its lane tests on
the landing push, origin's main tip..head (hook_lane_members, round 4's D1:
with `run --base C` after a merge of main, a member only the merge touched is
on no push the hook judges, so it runs here); a push that cannot be stated
leaves it none. In either mode a member the lane takes out on this host (a
crate-level `#![cfg(target_os = ...)]` for another OS: host_limited_members,
round 4's D2) is named NOT RUN and neither handed to the lane nor cached.
`plan` and `run` print which mode applies, which rule decided it and why on a
`LAND-GATE:` line, and the push's range on a `LANDING PUSH:` line; active, it
says to push the landing from THIS worktree and shell.

SELECTION is scripts/lib/land_select.py's, fail-closed (its header lists the
rules). The subject is the tree diff from BASE (default: the merge base with
origin/main) to HEAD. A leg the change does not reach is SKIPPED with its
reason; a leg it reaches runs, unless the CACHE can serve a PASS for exactly its
inputs.

THE CACHE (<git-common-dir>/trust-land/cache/<key>.json) holds every outcome a
key's run ended in: PASS, FAIL, NOT JUDGED, COULD NOT RUN (EW-21). Only a PASS is
ever served, and only from a key no FAIL contradicts: a key holding both is a
SPLIT KEY, the same inputs gave two answers, so the leg runs again and the gate
names the key (cache_split). A multi-member run's FAIL cannot name its member,
so it contradicts a PASS only once every key of that run holds one; a run that
also did work no key covers (force_run) contradicts nothing. A file that
cannot be read as a list of outcomes serves nothing, and keeps serving nothing
after a later PASS.
A leg's key is sha256 over: the leg and its exact targets; the fingerprint of
every tracked file under the leg's input prefixes (the whole tree when any
input is unresolved); HEAD's commit when the leg reads git history; the
toolchain by content (each PATH tool's runtime closure: its shim, every file the
shim runs, the whole install tree a binary sits in; the gate's Python, the C
toolchain xcrun names, the configured seed binaries; the sealed system volume by
the OS build: toolchain_identity, EW-1);
the selected bootstrap configuration and its include/profile closure; the
environment (every variable but a short list of terminal/session ones and the
scheduling knobs this gate sets itself); the gate's own code (this file,
scripts/lib/*.py, the escape audits, and each script the leg runs); and the
host's OS and arch. A leg that declares its reads (Leg.reads; today
tcb-panic-ratchet) also names them as observed when its key is taken, and
`declared:<leg>` in place of the global fingerprint when no full graph was
computed (run --development); a read it cannot observe exactly gives it no
key, and a PASS whose reads moved while it ran is not filed. Such a leg is
sealed: it runs in an environment the gate builds (sealed_environment), its
programs pinned, so its env element is a constant (LEG-READS-1).
The date is not in the key: one UTC date is declared to
every leg (DATE_ENV), and each outcome holds for [date, valid_until] only
(gate_date, serves_on). A
missing element is a miss. Scheduling (x.py -j, RUST_TEST_THREADS, the crates
pool size) is NOT in the key: it orders work, it is not an input, and a PASS at
four threads is a PASS. scripts/tests/land_gate_test.py holds every element to
the key with a mutant that drops it.

A RE-MERGE OF MAIN re-runs only what the merged commits can reach (ay's DR-40):
a leg whose inputs the merge did not move keeps its key, so its PASS is found
in the cache.

STAGE 1 is built once per compiler-side input tree. After a stage-1 suite
passes, build/<host>/trust-land-stage1.json records the stage-1 input key and
the identity of build/<host>/stage1/bin/rustc. A later stage-1 suite whose
stage-1 key matches (a fixture-only or docs change: nothing the compiler is
built from moved) passes `--keep-stage 0 --keep-stage-std 1`, which is exact
here because the stamp proves the kept stage is the one these inputs build;
otherwise the stamp is deleted BEFORE x.py runs, so an interrupted rebuild never
leaves a stamp that matches. x.py itself would otherwise rebuild the compiler
and std after every commit, because the commit hash is compiled in.

SCALING. Every job count comes from scripts/lib/host_budget.py at the moment
the leg starts: x.py -j and CARGO_BUILD_JOBS from the rustc-build plan,
RUST_TEST_THREADS from the ui-test plan for UI/run-make, and defaults from
the rustc-build plan for direct crates/Targo Trust harnesses; Bootstrap keeps
its own memory-rescaled harness default. RAYON_NUM_THREADS defaults to the
rustc-build plan without overriding a caller. Its effective value IS keyed,
including a default changed by rescaling. TRUST_CRATES_TESTS_JOBS comes from
the crates-test plan. Each leg but a sealed one (LEG-READS-1, which runs alone)
runs beside scripts/build-mem-governor.sh with floors from the same helper. Inside build-slot, every plan is capped by its
admitted CARGO_BUILD_JOBS share. The run record logs what was measured and chosen.

EXIT: 0 every selected leg passed (or was cached); 1 a leg failed; 2 nothing
could be judged (dirty tree, unparsable graph that also cannot fall back,
host unmeasurable, a leg that judged nothing, or, with no hook answering, a
landing push that cannot be stated: checked before any leg runs).

Author: Andrew Yates <andrewyates.name@gmail.com>
Copyright 2026 Andrew Yates | License: Apache-2.0 OR MIT
"""
from __future__ import annotations

import os
import shutil
import sys


def _reexec_if_old() -> None:
    if sys.version_info >= (3, 11):
        return
    if sys.argv[0] == "-":
        sys.stderr.write("land-gate: cannot restart consumed stdin; use Python >= 3.11\n")
        sys.exit(2)
    original = getattr(sys, "orig_argv", None)
    if original:
        arguments = original[1:]
    else:
        # Python 3.9 has no orig_argv, and unittest rewrites argv[0] to
        # "python -m unittest". Recover the actual entry point, not its label.
        main = sys.modules.get("__main__")
        spec = getattr(main, "__spec__", None)
        entry = getattr(main, "__file__", None)
        if spec is not None:
            arguments = ["-m", spec.name, *sys.argv[1:]]
        elif entry and sys.argv[0] not in ("-", "-c"):
            arguments = [entry, *sys.argv[1:]]
        else:
            # An imported module cannot replay code already consumed from
            # stdin/-c. Re-executing "-" would silently run nothing and pass.
            sys.stderr.write("land-gate: cannot restart consumed stdin/-c; use Python >= 3.11\n")
            sys.exit(2)
        if sys.dont_write_bytecode:
            arguments.insert(0, "-B")
    for cand in ("python3.14", "python3.13", "python3.12", "python3.11"):
        path = shutil.which(cand)
        if path:
            os.execv(path, [path, *arguments])
    sys.stderr.write("land-gate: needs Python >= 3.11 (tomllib); none on PATH\n")
    sys.exit(2)


_reexec_if_old()

import argparse  # noqa: E402
import builtins  # noqa: E402
import ast  # noqa: E402
from enum import Enum  # noqa: E402
import codecs  # noqa: E402
import contextlib  # noqa: E402
import io  # noqa: E402
import selectors  # noqa: E402
import shlex  # noqa: E402
import select  # noqa: E402
import datetime  # noqa: E402
import fcntl  # noqa: E402
import gc  # noqa: E402
import hashlib  # noqa: E402
import hmac  # noqa: E402
import importlib.util  # noqa: E402
import importlib.machinery  # noqa: E402
import json  # noqa: E402
import marshal  # noqa: E402
import platform  # noqa: E402
import pwd  # noqa: E402
import re  # noqa: E402
import signal  # noqa: E402
import stat  # noqa: E402
import subprocess  # noqa: E402
import tempfile  # noqa: E402
import threading  # noqa: E402
import time  # noqa: E402
import tomllib  # noqa: E402
import types  # noqa: E402
import sysconfig  # noqa: E402
import unicodedata  # noqa: E402
import warnings  # noqa: E402
from dataclasses import dataclass, field  # noqa: E402
from pathlib import Path  # noqa: E402
from typing import Callable, Dict, FrozenSet, Iterable, List, Optional, Sequence, Set, Tuple  # noqa: E402

REPO_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(REPO_ROOT / "scripts" / "lib"))

# Source provenance starts before this gate imports any repository implementation.
# A completed preloaded module cannot acquire a binding from newer disk bytes.
def _discovery_loaded_modules(root):
    for module in tuple(sys.modules.values()):
        filename = getattr(module, "__file__", None)
        if not isinstance(filename, str):
            continue
        path = Path(filename)
        if path.suffix == ".pyc":
            try:
                path = Path(importlib.util.source_from_cache(str(path)))
            except ValueError:
                continue
        if path.suffix != ".py":
            continue
        try:
            yield module, path.resolve().relative_to(root).as_posix()
        except (OSError, ValueError):
            pass


class _DiscoveryImportUnbound(BaseException):
    """A source import refusal must escape ordinary classifier fallbacks."""


class _DiscoveryReaderExecution:
    def __init__(self, module, record, role, complete):
        self.module, self.record, self.role, self.complete = module, record, role, complete
        self.imports = []


class _DiscoveryReaderImports:
    def __init__(self, root):
        self.root, self.records, self.kinds, self.pending = root, {}, {}, set()
        self.executions, self.namespaces, self.created, self.active = {}, {}, {}, []
        self.program = hashlib.sha256((root / "scripts/land_gate.py").read_bytes()).hexdigest()

    def record(self, module, path, raw, metadata, kind, *, role="caller", complete=False):
        if not stat.S_ISREG(metadata.st_mode):
            return
        relative = path.resolve().relative_to(self.root).as_posix()
        mode = "100755" if metadata.st_mode & stat.S_IXUSR else "100644"
        record = relative, (mode, hashlib.sha256(raw).hexdigest())
        self.records[module], self.kinds[module] = record, kind
        execution = _DiscoveryReaderExecution(module, record, role, complete)
        self.executions[module] = execution
        self.namespaces[id(module.__dict__)] = execution
        return execution

    def importer(self, namespace):
        execution = self.namespaces.get(id(namespace))
        return execution if execution is not None and execution.module.__dict__ is namespace else None

    def owns(self, module):
        filename = getattr(module, "__file__", None)
        return isinstance(filename, str) and Path(filename).resolve().is_relative_to(self.root)

    def execute_bytes(self, module, path, raw, metadata, parent=None):
        # Captured implementation epochs start in a fresh namespace. Neither
        # reload nor a caller-frame attestation can upgrade retained bindings.
        namespace = self.created.pop(module, None)
        if (module in self.executions or namespace is None or namespace.keys() != module.__dict__.keys()
                or any(module.__dict__[key] is not value for key, value in namespace.items())):
            raise RuntimeError("discovery implementation requires a fresh captured module; restart the gate")
        code = compile(raw, str(path), "exec", dont_inherit=True)
        execution = self.record(module, path, raw, metadata, "captured-source", role="implementation")
        if execution is None:
            raise ImportError("discovery reader is not a regular source file")
        self.pending.add(module)
        try:
            exec(code, module.__dict__)
            execution.complete = True
        except BaseException:
            self.records.pop(module, None); self.kinds.pop(module, None)
            self.executions.pop(module, None); self.namespaces.pop(id(module.__dict__), None)
            raise
        finally:
            self.pending.discard(module)
        if parent is not None:
            self.note(parent, module)

    def execute(self, loader, module, namespace):
        path = Path(loader.path)
        self.execute_bytes(module, path, path.read_bytes(), path.lstat(), self.importer(namespace))

    def note(self, importer, module):
        if not isinstance(module, types.ModuleType) or not self.owns(module):
            return
        edge = module, self.executions.get(module)
        if importer is not None and edge not in importer.imports:
            importer.imports.append(edge)
        if self.active:
            reason = self.implementation_problem(module, edge[1], physical=False)
            if reason:
                for proof in tuple(self.active): proof["problem"] = reason
                raise _DiscoveryImportUnbound(reason)

    def imported(self, namespace, name, fromlist, level, result):
        importer = self.importer(namespace)
        if importer is None and not self.active:
            return
        self.note(importer, result)
        absolute = name
        if level:
            package = namespace.get("__package__") or namespace.get("__name__", "")
            try: absolute = importlib.util.resolve_name("." * level + name, package)
            except (ImportError, ValueError): absolute = ""
        target = sys.modules.get(absolute)
        if target is not None:
            self.note(importer, target)
        if isinstance(result, types.ModuleType):
            for item in fromlist or ():
                child = vars(result).get(item)
                if isinstance(child, types.ModuleType): self.note(importer, child)

    def implementation_problem(self, module, execution, seen=None, *, physical=True):
        seen = set() if seen is None else seen
        if execution is None or execution.module is not module or execution.role not in ("entry", "implementation"):
            return "loaded discovery reader has no matching captured source for an implementation import; restart the gate"
        if execution in seen:
            return None
        seen.add(execution)
        if not execution.complete and execution.record[0] != "scripts/land_gate.py":
            return "loaded discovery reader has no completed captured source for an implementation import; restart the gate"
        if physical:
            path, expected = execution.record
            try:
                metadata, raw = (self.root / path).lstat(), (self.root / path).read_bytes()
                current = ("100755" if metadata.st_mode & stat.S_IXUSR else "100644", hashlib.sha256(raw).hexdigest())
                if not stat.S_ISREG(metadata.st_mode) or current != expected:
                    return "discovery implementation import source changed; restart the gate"
            except OSError:
                return "discovery implementation import source unavailable; restart the gate"
        dependencies = list(execution.imports)
        # Preserve the original direct module-reference boundary as well as
        # actual import edges, which also retain function/class/method imports.
        dependencies.extend((value, self.executions.get(value)) for value in tuple(vars(module).values())
                            if isinstance(value, types.ModuleType) and self.owns(value))
        for dependency, captured in dependencies:
            reason = self.implementation_problem(dependency, captured, seen, physical=physical)
            if reason: return reason
        return None

    def attest_active_modules(self):
        # A matching active frame is caller evidence, never an implementation
        # epoch. Only the actual gate entry can root the import provenance graph.
        frames = {}
        frame = sys._getframe()
        while frame is not None:
            if frame.f_code.co_name == "<module>": frames[id(frame.f_globals)] = frame.f_code
            frame = frame.f_back
        for module, relative in _discovery_loaded_modules(self.root):
            if module in self.records: continue
            code = frames.get(id(module.__dict__))
            if code is None: continue
            spec = getattr(module, "__spec__", None)
            initial = (getattr(spec, "_initializing", False) is True
                       and type(getattr(spec, "loader", None)) is importlib.machinery.SourceFileLoader
                       and sys.modules.get(getattr(spec, "name", None)) is module)
            if module is not sys.modules.get("__main__") and not initial:
                continue
            path = self.root / relative
            try:
                metadata, raw = path.lstat(), path.read_bytes()
                if code == compile(raw, code.co_filename, "exec", dont_inherit=True):
                    role = "entry" if relative == "scripts/land_gate.py" else "caller"
                    self.record(module, path, raw, metadata, "active-module-code", role=role)
            except (OSError, ValueError, SyntaxError): continue


def _discovery_source_imports(root):
    transport = importlib.machinery.SourceFileLoader.exec_module
    registry = getattr(transport, "_trust_discovery_source_registry", None)
    if registry is None:
        registry = {}
        original = transport
        def execute(loader, module):
            if type(loader) is importlib.machinery.SourceFileLoader:
                path = Path(loader.path).resolve()
                for origin, owner in registry.items():
                    if path.is_relative_to(origin):
                        return owner.execute(loader, module, sys._getframe(1).f_globals)
            return original(loader, module)
        execute._trust_discovery_source_registry = registry
        importlib.machinery.SourceFileLoader.exec_module = execute
        transport = execute
        original_import = builtins.__import__
        def imported(name, globals=None, locals=None, fromlist=(), level=0):
            namespace = globals if isinstance(globals, dict) else sys._getframe(1).f_globals
            result = original_import(name, globals, locals, fromlist, level)
            for owner in tuple(registry.values()): owner.imported(namespace, name, fromlist, level, result)
            return result
        builtins.__import__ = imported
        original_dynamic = importlib.import_module
        def dynamic(name, package=None):
            namespace = sys._getframe(1).f_globals
            result = original_dynamic(name, package)
            for owner in tuple(registry.values()):
                importer = owner.importer(namespace)
                # A standard-library resolver can be the immediate caller.
                # Active classification still requires a qualified binding.
                if importer is not None or owner.active: owner.note(importer, result)
            return result
        importlib.import_module = dynamic
        original_factory = importlib._bootstrap.module_from_spec
        if importlib.util.module_from_spec is not original_factory:
            raise RuntimeError("module factory is not the canonical import factory; restart the gate")
        def factory(spec):
            module = original_factory(spec)
            if type(spec.loader) is importlib.machinery.SourceFileLoader:
                for owner in tuple(registry.values()):
                    if owner.owns(module): owner.created[module] = dict(module.__dict__)
            return module
        importlib.util.module_from_spec = factory
        importlib._bootstrap.module_from_spec = factory
        transport._trust_discovery_import_hooks = imported, dynamic, factory, factory
    program = hashlib.sha256((root / "scripts/land_gate.py").read_bytes()).hexdigest()
    if any(owner.program != program for owner in registry.values()):
        raise RuntimeError("a different loaded discovery program requires a new interpreter")
    if root not in registry: registry[root] = _DiscoveryReaderImports(root)
    owner = registry[root]
    owner.transport = transport
    owner.hooks = transport._trust_discovery_import_hooks
    owner.attest_active_modules()
    return owner


_DISCOVERY_SOURCE_ROOT = REPO_ROOT
_DISCOVERY_SOURCE_IMPORTS = _discovery_source_imports(_DISCOVERY_SOURCE_ROOT)


import host_budget  # noqa: E402
import land_select as ls  # noqa: E402
import mint_seed_support  # noqa: E402
import landing_targo  # noqa: E402
import native_serial  # noqa: E402


def _load_captured_source(path: Path, prefix: str = "_trust_land_remote_tips_"):
    """Compile the captured authority source, ignoring pyc/module caches:
    (module, sha256 of the source, the source bytes compiled)."""
    source = path.read_bytes()
    digest = hashlib.sha256(source).hexdigest()
    name = prefix + digest
    module = types.ModuleType(name)
    module.__file__ = str(path)
    sys.modules[name] = module  # dataclasses resolves its actual module here
    _DISCOVERY_SOURCE_IMPORTS.created[module] = dict(module.__dict__)
    try:
        _DISCOVERY_SOURCE_IMPORTS.execute_bytes(module, path, source, path.lstat(),
            _DISCOVERY_SOURCE_IMPORTS.importer(globals()))
    except BaseException:
        sys.modules.pop(name, None)
        raise
    return module, digest, source


remote_tips, _REMOTE_TIPS_SOURCE_SHA256, _ = _load_captured_source(REPO_ROOT / "scripts/lib/remote_tips.py")
# checkout_problem's per-file check: its worker processes run these same bytes
# (_CheckoutWorkers), never a file read from the checkout being inspected.
checkout_inputs, _CHECKOUT_INPUTS_SOURCE_SHA256, _CHECKOUT_INPUTS_SOURCE = _load_captured_source(
    REPO_ROOT / "scripts/lib/checkout_inputs.py", "_trust_land_checkout_inputs_")
native_checkout, _NATIVE_CHECKOUT_ADAPTER_SHA256, _ = _load_captured_source(
    REPO_ROOT / "scripts/lib/native_checkout.py", "_trust_land_native_checkout_")
try:
    # Compatibility data captured before any leg, never an authentication claim.
    _NATIVE_CHECKOUT_READER_SHA256 = hashlib.sha256((REPO_ROOT / native_checkout.NATIVE_SOURCE).read_bytes()).hexdigest()
except OSError:
    _NATIVE_CHECKOUT_READER_SHA256 = None

# /2 (EW-1): the date left the key for each outcome's validity window, and the
# toolchain is the content of its runtime closure.
SCHEMA = "trust-land-gate/2"
GATE_FILES = ("scripts/land_gate.py", "scripts/lib/land_select.py", "scripts/lib/land_manifest.py", "scripts/lib/remote_operation.py",
              "scripts/lib/land_development.py", "scripts/lib/rust_lex.py",
              "scripts/lib/host_budget.py", "scripts/gates/land-escape-audits.toml",
              "scripts/mint_seed_support.py", "scripts/lib/native_serial.py", "scripts/lib/landing_targo.py", "scripts/lib/remote_tips.py",
              # The crates lane's member rule, which the selector reads (round 5, D1).
              "scripts/lib/crates_lane_members.py",
              "scripts/lib/checkout_inputs.py", "scripts/lib/native_checkout.py",
              # The row table land_select builds its validation tables from (PKG-LIVE-4):
              # a change to it changes every key, as a change to those tables always did.
              ls.LAND_ROWS_FILE)
# Checked-in data, not code this process compiled: hashed as it is when a key is
# taken. The audit rows are read again from every judged tree. The row table is
# loaded once, at import, so it is also a loaded reader (_loaded_discovery_readers)
# whose tables _compose_discovery replaces when incoming main changes it.
GATE_DATA_FILES = frozenset({ls.AUDITS_FILE, ls.LAND_ROWS_FILE})
# `clean`: under aterm, `lean` is a reroute stub that runs `clean` from PATH
# (`aterm help reroute`); `elan`: the olean audit selects its Lean through it.
TOOLS = ("targo", "trustc", "trustd", "tippy", "lean", "clean", "lake", "elan", "git", "agh", "python3")
# Environment variables that are terminal/session noise, the scheduling this
# gate sets itself, or the validated build-lock lease identity. Everything else
# is in the key; the lease token remains in the environment for lock reentrancy.
ENV_IGNORED = re.compile(
    r"^(PWD|OLDPWD|SHLVL|_|TERM|TERM_.*|COLORTERM|ITERM_.*|TMUX.*|STY|WINDOW|SSH_.*|DISPLAY|"
    r"SECURITYSESSIONID|Apple_PubSub_Socket_Render|LaunchInstanceID|XPC_.*|__CF.*|LOGNAME|"
    r"CLAUDE.*|ANTHROPIC.*|ATERM.*|OTEL_.*|MallocNanoZone|"
    r"RUST_TEST_THREADS|CARGO_BUILD_JOBS|TRUST_CRATES_TESTS_JOBS|TRUST_CRATES_TESTS_BUDGET_S|"
    r"TRUST_CRATES_TESTS_STALL_S|TRUST_XPY_JOBS|"
    r"TRUST_PUSHED_REFS|TRUST_PUSH_REMOTE|TRUST_BUILD_LOCK_TOKEN\Z|"
    # The declared date (DATE_ENV): carried by each outcome's window instead.
    r"TRUST_GATE_DATE\Z|TRUST_UPSTREAM_COMPAT_VALIDATION_DATE\Z)$")
UNIT_SUBSET_RUN_MAKE = ("trust-cg-", "trust-instance-", "trust-ir-emit")
# Where the Python processes a leg, a push row or the Targo probe starts read
# and write their compiled modules: a fresh empty directory the gate made for
# that process tree, removed once it exits. `-B` only stops writes; Python
# still runs a __pycache__/*.pyc whose header (the source's mtime and size)
# matches, whatever code it holds. A leg that left such a file beside a
# tracked module made a later leg run other code than the commit's while every
# tracked byte, which is all a checkout pass reads, still matched: a false
# PASS. With the prefix set, Python neither reads nor writes the tree's
# __pycache__; `land`'s ordinary push gets one too (ordinary_push), for the
# pre-push hook's rows. The gate's own imports of the checkout's modules run
# their source bytes (_discovery_source_imports), never a .pyc. An
# interpreter started with -E or -I ignores the variable, and no gate can add
# `-X pycache_prefix` to the command lines a leg's own programs build: the
# checkout pass refuses instead any __pycache__ bytecode such an interpreter
# would load for a tracked source unless it is exactly that source's code
# (python_import_problem, LAND-GATE-PY-SHADOW-1).
PYCACHE_ENV = "PYTHONPYCACHEPREFIX"
# What a key's env element holds for it: each run makes its own.
LEG_PYCACHE = "<the run's fresh directory of the leg's compiled Python>"


def fresh_pycache(run_dir: Path, owner: str) -> Path:
    """A new empty directory under `run_dir`/pycache for one process tree's
    compiled Python (PYCACHE_ENV)."""
    (run_dir / "pycache").mkdir(exist_ok=True)
    return Path(tempfile.mkdtemp(prefix=f"{owner}.", dir=run_dir / "pycache"))


def git(*args: str, check: bool = True) -> str:
    proc = subprocess.run(["git", "-C", str(REPO_ROOT), *args], capture_output=True, text=True)
    if check and proc.returncode != 0:
        raise RuntimeError(f"git {' '.join(args)}: {proc.stderr.strip()}")
    return proc.stdout.strip()


def common_dir() -> Path:
    return Path(git("rev-parse", "--path-format=absolute", "--git-common-dir"))


def sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    try:
        with open(path, "rb") as fh:
            for chunk in iter(lambda: fh.read(1 << 20), b""):
                h.update(chunk)
    except OSError as exc:
        return f"unreadable:{exc.__class__.__name__}"
    return h.hexdigest()


# ---------------------------------------------------------------------------
# Whether the push that lands this tree runs the pre-push hook.
# ---------------------------------------------------------------------------

HOOK_DIR = "scripts/hooks"
HOOK_FILE = "scripts/hooks/pre-push"
HARNESS = "tests/run_trust_comprehensive_harness.sh"
QUARANTINE_LEDGER = "tests/trust-comprehensive/divergences.toml"

# The push-profile rows a leg of this gate covers when the hook does not run,
# each keyed by its id AND its exact command (the manifest's): a row whose
# command changed is no longer known to be covered, and push-rows runs it. The
# command string is not all a row runs (round 3, D3): COVERED_ROW_PINS holds the
# bytes of the script behind a row whose leg runs a FIXED command, and
# COVERED_ROW_LANDING the files a leg runs only through another reading than the
# row's; a row whose script is not those bytes, whose push edits those files, or
# whose lane the pushed ledger quarantines (round 3, D4) runs in push-rows
# (covered_row_problem).
#   scoped.compiler-check: compiler-check runs `x.py check --stage 1
#     --all-targets` (a superset of the row's targets) whenever the selector says
#     x.py check's inputs moved, the same selector the row consults for any range
#     outside compiler/, library/ and src/ (and a path there that the selector
#     does not reach cannot move what x.py check compiles, §3c's soundness
#     argument); under a configured seed the leg is NOT JUDGED where the row would
#     build anyway. The pinned script's verdict is `x.py check --stage 1`'s exit
#     status and nothing else (exit 0 exactly when it exits 0; a red's preflight
#     classification changes only the message), so the leg, judged on its exit
#     status, applies the row's judgement (round 4, D3).
#   scoped.crates-tests: crates-tests run as the hook runs the lane, over the
#     landing range (`--range <base>...<head>`: the touched members, their
#     FEATURE_RUNS tails and own-workspace runs, and each moved instrument judged
#     by the lane's instrument rules, INSTRUMENT_REQUIRED_PASSES included), plus
#     the reached members (`--also-members`), never a touched member from a
#     cached PASS (build_legs, round 2's D3). The leg runs the lane itself, so the
#     lane's own judgement is the leg's.
# scoped.targo-trust-unit-tests is in no push profile since 39b35cb9f7
# (DEV-MAIN-FOCUSED-VALIDATION, 2026-11-02), so push-rows never runs it, and
# nothing else here runs it either (round 5, D3; round 4's D3 had push-rows run
# it). Its zero-passed rule (ZERO TESTS IS NOT A PASS: a full-suite success
# need not mean the unit binary passed a test) is carried only by the
# targo-trust leg's own command, landing_targo.COMMAND, which passes
# `--require-test-bin targo-trust` (9f709bc793). Targo then requires that
# binary to run and report passing tests, or exits non-zero. A targo that does
# not accept the option makes the leg NOT JUDGED before it runs (targo_unready),
# never a FAIL of the change. Under `land`, the leg is handed to the hook's
# scoped Targo row only while the pushed profile has one (round 5, D2). This
# table does not extend coverage or reuse to that row.
# A covered row is one whose leg's verdict implies the row's: the same subject or
# a superset, AND the row's whole judgement (a script judging anything beyond the
# exit status of the command its leg also runs is not covered).
HOOK_ROWS_COVERED: Dict[str, Tuple[str, str]] = {
    "scoped.compiler-check": ("bash scripts/check_compiler_targets_build.sh", "compiler-check"),
    "scoped.crates-tests": ("python3 scripts/check_crates_tests_scoped.py --push-context", "crates-tests"),
}
# The script each fixed-command leg's coverage was argued for, as git blob ids
# (`git rev-parse HEAD:<path>`). compiler-check runs `x.py check --stage 1
# --all-targets`, never this script, so an edit to it (a new assertion after
# x.py check, a step judged on its output) is not covered until someone
# re-argues that the leg covers what it now runs and judges, and moves its pin
# (land_gate_test's test_the_covered_rows_are_the_manifests holds the pins to
# the tree, so an edit cannot drift silently). Until then push-rows runs the row.
COVERED_ROW_PINS: Dict[str, Tuple[Tuple[str, str], ...]] = {
    "scoped.compiler-check": (("scripts/check_compiler_targets_build.sh",
                               "53689c70bbb85b66b3f922dd19ae5885c11a3999"),),
}


# What the gate leans on when it leaves the touched crates/ members to the hook
# (LAND-GATE-HOOKLESS-1 round 2, D2): the hook itself and the helpers it sources
# beside it (scripts/hooks/), the manifest it reads its lanes from, and the
# crates lane with the scripts/lib modules it imports (CRATES_LANE_IMPORTS; a
# test holds that list to the lane's own imports). A change to any of them
# changes the hook that runs on this landing's own push, so the gate cannot
# lean on it: the run is hookless whatever the clone's configuration says.
CRATES_LANE = "scripts/check_crates_tests_scoped.py"
CRATES_LANE_IMPORTS = ("scripts/lib/crates_tests_time.py", "scripts/lib/host_budget.py",
                       "scripts/lib/crates_lane_members.py")
HOOK_ANSWER_PATHS = (HOOK_DIR + "/", HARNESS, CRATES_LANE, *CRATES_LANE_IMPORTS)
CRATES_ROW = "scoped.crates-tests"
# The files a covering leg runs as of HEAD, but through another reading than the
# row's own command (round 3, D3): the crates leg runs the lane itself, with
# `--range` where the row runs `--push-context`, so a landing that edits the lane
# or its imports could break the row's reading with the leg still green. Such a
# landing runs the row in push-rows too; any other landing leaves it covered
# (the lane's bytes are whatever HEAD holds, so no pin is needed).
COVERED_ROW_LANDING: Dict[str, Tuple[str, ...]] = {CRATES_ROW: (CRATES_LANE, *CRATES_LANE_IMPORTS)}
# Environment-scoped git configuration and git's repository-local variables:
# what one shell can set and the shell that pushes need not have (D4).
GIT_ENV_CONFIG = ("GIT_CONFIG_COUNT", "GIT_CONFIG_PARAMETERS", "GIT_CONFIG_GLOBAL", "GIT_CONFIG_SYSTEM",
                  "GIT_CONFIG_NOSYSTEM")
GIT_ENV_CONFIG_INDEXED = re.compile(r"^GIT_CONFIG_(KEY|VALUE)_\d+$")


@dataclass(frozen=True)
class PushHook:
    """Whether scripts/hooks/pre-push answers for the landing push (`active`):
    it runs every row of the push profile at the landed head there, so the
    gate leaves those rows to it (push-rows does not run them); the one-line
    reason the plan prints; and which rule decided it (`rule`): `installed`
    (active), `not-installed`, `push-range` (what the landing push carries
    cannot be read), `hook-path` (the change or the landing push edits what
    the hook runs or reads) or `push-profile` (the profile the hook would read
    cannot be read).

    `answers`: the covered rows (HOOK_ROWS_COVERED) that profile holds as
    their coverage requires (required, that exact command). Only for those
    does a leg here leave its part to the hook: the touched crates/ members
    to `scoped.crates-tests`, the landing push's compiler-check to
    `scoped.compiler-check`. A covered row the profile lacks is judged here,
    as with no hook (`gaps` says why). Until 2026-11-13 a profile without the
    crates row made the whole hook inactive (rule `push-profile`): the gate
    then ran every push row in push-rows and the hook ran the same rows again
    on the push."""
    active: bool
    why: str
    rule: str = ""
    answers: FrozenSet[str] = frozenset()
    gaps: str = ""

    @property
    def mode(self) -> str:
        return "active" if self.active else "absent"

    def runs(self, row: str) -> bool:
        """Whether the hook runs covered `row` on the landing push, so a leg
        here may leave that row's part to it."""
        return self.active and row in self.answers

    @property
    def fired(self) -> str:
        return self.rule or ("installed" if self.active else "not-installed")


def git_query_env(env: Optional[Dict[str, str]] = None) -> Dict[str, str]:
    """The environment in which to ask git about THIS clone as a plain shell's
    `git push` would see it: git's repository-local variables (`git rev-parse
    --local-env-vars`, as the hook and row_environment unset them) and every
    environment-scoped configuration variable removed, so a GIT_DIR, a
    GIT_CONFIG_COUNT/KEY/VALUE triple, a GIT_CONFIG_PARAMETERS (`git -c`) or a
    GIT_CONFIG_GLOBAL in the gate's own environment cannot answer for the shell
    that pushes (D4). A credential prompt fails instead of waiting."""
    out = dict(os.environ if env is None else env)
    try:
        local = subprocess.run(["git", "rev-parse", "--local-env-vars"], capture_output=True, text=True,
                               env={k: v for k, v in out.items() if not k.startswith("GIT_")}).stdout.split()
    except OSError:
        local = []
    for var in (*(local or GIT_LOCAL_ENV_VARS), *GIT_ENV_CONFIG):
        out.pop(var, None)
    for var in [k for k in out if GIT_ENV_CONFIG_INDEXED.match(k)]:
        out.pop(var)
    out["GIT_TERMINAL_PROMPT"] = "0"
    return out


def hook_answer_paths(changed: Sequence[str]) -> List[str]:
    """The changed paths the hook on this landing's push runs or reads
    (HOOK_ANSWER_PATHS: a directory entry ends in `/`)."""
    return sorted(p for p in changed
                  if any(p.startswith(x) if x.endswith("/") else p == x for x in HOOK_ANSWER_PATHS))


def hook_row_problem(profile: Sequence["PushRow"], row: str, rev: str) -> Optional[str]:
    """Why the push profile `profile` (read at `rev`, the tree being landed,
    whose hook and manifest run on its push) would not run covered `row` as
    the leg that leaves its part to the hook needs, or None: a required row
    running exactly HOOK_ROWS_COVERED's command. An optional row only WARNs
    when red; another command is not the lane whose coverage was argued."""
    want = HOOK_ROWS_COVERED[row][0]
    rows = [r for r in profile if r.id == row]
    if any(r.required == "true" and r.command == want for r in rows):
        return None
    if not rows:
        return f"the push profile at {rev[:12]} (`{HARNESS} --list push`) has no {row} row"
    r = rows[0]
    if r.command != want:
        return f"its {row} row runs `{r.command}`, not `{want}`"
    return f"its {row} row is not required (required={r.required}): the hook would only WARN on a red"


def push_hook_state(changed: Sequence[str], head: str = "HEAD", root: Optional[Path] = None,
                    landing: Optional["LandingRange"] = None) -> PushHook:
    """ACTIVE only when the hook is installed for this worktree (hook_installed)
    AND it answers for this landing: neither the gate's subject (`changed`,
    base..head) nor what the landing push carries (`landing.changed`, the tree
    diff from origin's main tip to `head`, read_landing; read here when not
    given) edits anything the hook runs or reads (HOOK_ANSWER_PATHS: the hook
    and its helpers, the push-profile manifest, the crates lane and its
    scripts/lib imports), and the push profile at `head` can be read. Any rule
    failing is NOT active, named by its rule: the hook on the landing push is
    the landed tree's, and a landing that changes it cannot lean on it (round
    2, D2). The selection base alone does not decide it (round 3, D2): `run
    --base C` is "the last gated tree", and an edit to the hook made before C
    still runs on the push. A push whose range cannot be read is NOT active
    (rule `push-range`). Fail closed: NOT active costs the landing more work.

    Active, the hook runs every row of that profile on the push, and
    `answers` names the covered rows it holds as their coverage requires
    (hook_row_problem, over the one profile read here): the profile as `--list push`
    prints it decides what a leg leaves to the hook, never a row the gate
    expects it to have."""
    root = Path(root or REPO_ROOT)
    installed = hook_installed(root)
    if not installed.active:
        return installed
    if landing is None:
        landing = read_landing(root, head)
    if landing.changed is None:
        return PushHook(False, f"{installed.why}, but what the landing push carries cannot be read ({landing.why}), "
                               "so whether it edits what the hook runs cannot be judged", "push-range")
    hit = hook_answer_paths(sorted(set(changed) | set(landing.changed)))
    if hit:
        more = f" and {len(hit) - 1} more" if len(hit) > 1 else ""
        return PushHook(False, f"{installed.why}, but this change edits {hit[0]}{more}, which the hook on its "
                               "own push runs or reads", "hook-path")
    try:
        profile = push_profile_rows(root, rev=head)
    except RuntimeError as exc:
        return PushHook(False, f"{installed.why}, but the push profile at {head[:12]} cannot be read ({exc}), "
                               "so which rows the hook runs on the push cannot be said", "push-profile")
    gaps = {row: hook_row_problem(profile, row, head) for row in sorted(HOOK_ROWS_COVERED)}
    missing = {row: why for row, why in gaps.items() if why}
    return PushHook(True, installed.why, "installed", frozenset(gaps) - set(missing),
                    "; ".join(f"{row}: {why}" for row, why in missing.items()))


def hook_query_envs(env: Optional[Dict[str, str]] = None) -> List[Tuple[str, Dict[str, str]]]:
    """The environments hook_installed asks git in, each named for the
    LAND-GATE line: the clone's own configuration (git_query_env: what a plain
    shell's `git push` reads, round 2's D4), then this process's environment as
    it stands (what a `git push` from THIS shell reads: an environment-scoped
    core.hooksPath, a GIT_CONFIG_GLOBAL, a GIT_DIR; round 3's D1), asked only
    when it differs from the first. Both must answer this tree's scripts/hooks:
    the ACTIVE line tells the user to push from this shell, and a value only
    this shell carries that sends hooks elsewhere makes that push run none."""
    own = dict(os.environ if env is None else env)
    own["GIT_TERMINAL_PROMPT"] = "0"
    clean = git_query_env(env)
    out = [("the clone's configuration", clean)]
    if own != clean:
        out.append(("this shell's environment", own))
    return out


def _hooks_reading(root: Path, env: Dict[str, str]) -> Tuple[Optional[str], str]:
    """(why git, asked in `env`, does not run this tree's scripts/hooks, or
    None; what it said about core.hooksPath)."""

    def ask(*args: str) -> subprocess.CompletedProcess:
        return subprocess.run(["git", "-C", str(root), *args], capture_output=True, text=True, env=env)

    try:
        cfg = ask("config", "--get", "core.hooksPath")
        resolved = ask("rev-parse", "--path-format=absolute", "--git-path", "hooks")
    except OSError as exc:
        return f"cannot ask git where hooks run ({exc.__class__.__name__}: {exc})", ""
    if cfg.returncode not in (0, 1) or resolved.returncode != 0 or not resolved.stdout.strip():
        err = (resolved.stderr or cfg.stderr).strip().splitlines()
        return f"cannot tell where git runs hooks ({err[-1] if err else 'no answer'})", ""
    configured = cfg.stdout.strip() if cfg.returncode == 0 else ""
    where = Path(resolved.stdout.strip())
    said = f"core.hooksPath={configured}" if configured else "core.hooksPath unset"
    want = root / HOOK_DIR
    try:
        same = where.resolve(strict=True) == want.resolve(strict=True)
    except OSError:
        return (f"{said}; git runs hooks from {where}, which does not exist" if configured
                else f"{said}; git runs hooks from {where}, not this tree's {HOOK_DIR}"), said
    if not same:
        return f"{said}; git runs hooks from {where}, not this tree's {HOOK_DIR}", said
    return None, said


def hook_installed(root: Optional[Path] = None) -> PushHook:
    """Installed only when git resolves this worktree's hooks directory
    (`git rev-parse --path-format=absolute --git-path hooks`: core.hooksPath as
    git reads it from every config scope, a relative value taken from the
    worktree root, `~` expanded; `<git-common-dir>/hooks` when it is unset) to
    this tree's scripts/hooks in EVERY environment hook_query_envs names, and
    scripts/hooks/pre-push there is a regular file this user may execute.
    Anything else is NOT installed: unset (git's own hooks directory: an
    untracked copy there is not the reviewed hook), another directory (another
    worktree's scripts/hooks runs another tree's hook), a path that does not
    exist, a missing or non-executable pre-push, and every question git cannot
    answer. The clone's configuration alone must answer (configuration only this
    process's environment carries is not the clone's, and another shell need not
    have it: round 2's D4), and so must this shell's environment as it stands
    (the push the ACTIVE line asks for is made from it: round 3's D1). Fail
    closed: NOT installed costs a landing more work, a wrong ACTIVE lets touched
    members and hook rows go untested."""
    root = Path(root or REPO_ROOT)
    envs = hook_query_envs()
    problem, said = _hooks_reading(root, envs[0][1])
    if problem:
        return PushHook(False, problem)
    for label, env in envs[1:]:
        other, _said = _hooks_reading(root, env)
        if other:
            clean = envs[0][1]
            moved = sorted(k for k in set(env) | set(clean) if k.startswith("GIT_") and k != "GIT_TERMINAL_PROMPT"
                           and env.get(k) != clean.get(k))
            named = ", ".join(moved) or "its git variables"
            return PushHook(False, f"{said}, this tree's {HOOK_DIR}, but {label} ({named}) says otherwise: "
                                   f"{other}; a push from this shell runs no hook of this tree")
    hook = root / HOOK_FILE
    if not hook.is_file():
        return PushHook(False, f"{said}; {HOOK_FILE} is missing")
    if not os.access(hook, os.X_OK):
        return PushHook(False, f"{said}; {HOOK_FILE} is not executable")
    agree = " (this shell's git environment agrees)" if len(envs) > 1 else ""
    return PushHook(True, f"{said}, this tree's {HOOK_DIR}, whose pre-push is executable{agree}")


# ---------------------------------------------------------------------------
# Key elements.
# ---------------------------------------------------------------------------


def _bootstrap_config_paths() -> List[Path]:
    explicit = os.environ.get("RUST_BOOTSTRAP_CONFIG")
    if explicit is not None:
        path = Path(explicit)
        return [path if path.is_absolute() else REPO_ROOT / path]
    return [REPO_ROOT / "bootstrap.toml", REPO_ROOT / "config.toml"]


def _bootstrap_build_config(origins: Optional[Dict[str, Path]] = None
                            ) -> Tuple[Dict[str, object], Dict[Path, str]]:
    """Use the same include/profile reader as seed admission, from x.py's cwd.
    An explicit missing config never falls back to a default config. `origins`,
    when given, receives the file each `[build]` key's value came from."""
    cfgs = _bootstrap_config_paths()
    selected = next((p for p in cfgs if p.exists()), None)
    if selected is None:
        if "RUST_BOOTSTRAP_CONFIG" in os.environ:
            raise RuntimeError(f"RUST_BOOTSTRAP_CONFIG names an unavailable file: {cfgs[0]}")
        return {}, {}
    inputs: Dict[Path, str] = {}
    try:
        build = mint_seed_support.effective_build_table(
            REPO_ROOT, selected.resolve(strict=True), confine=False, inputs=inputs, origins=origins)
    except (OSError, mint_seed_support.WorkflowError) as exc:
        raise RuntimeError(f"cannot read bootstrap configuration {selected}: {exc}") from exc
    return build, inputs


def _stage0_binaries() -> List[str]:
    build, _inputs = _bootstrap_build_config()
    # Python bootstrap may use downloaded tools before its Rust config reader
    # merges includes. Bind both that seed surface and effective overrides.
    seed = REPO_ROOT / "build" / host_triple() / "stage0" / "bin"
    out = [str(seed / tool) for tool in
           ("trustc", "rustc", "cargo", "trustdoc", "rustdoc", "trustfmt", "targo-tippy")]
    out.append(str(REPO_ROOT / "build" / host_triple() / "trustfmt" / "bin" / "trustfmt"))
    configured: Dict[str, Path] = {}
    for key in ("rustc", "cargo", "rustdoc", "rustfmt", "cargo-clippy"):
        value = build.get(key)
        if isinstance(value, str):
            path = Path(value).expanduser()
            configured[key] = path if path.is_absolute() else REPO_ROOT / path
            out.append(str(configured[key]))
    if "rustc" in configured and "rustdoc" not in configured:
        # Session derives this sibling before resolving a compiler symlink.
        out.append(str(configured["rustc"].with_name("rustdoc")))
    return out


# ---------------------------------------------------------------------------
# Toolchain identity (EW-1): the digest of each tool's runtime closure.
# ---------------------------------------------------------------------------
# A tool on PATH is most often a shim: atpkg's are ~160-byte shell scripts that
# exec a versioned store directory (store/trust/<n>/bin/trustc), and targo's
# also execs aterm's own binary (`atpkg __build_admit`). Their realpath, size and
# mtime said nothing about the compiler, sysroot and helpers that run, and a
# version string is the tool's claim about itself. The identity is now the
# content of what the tool runs, found by following the shim to every absolute
# file it names (the shebang's interpreter, an `exec '<path>'`) and expanding
# a binary inside an install tree (<root>/bin or <root>/libexec beside a lib/,
# libexec/, share/ or include/; an app bundle) to that whole tree: the sysroot,
# the driver dylibs, the helpers. A Python is its executable and its standard
# library, asked of the interpreter. On macOS a path on the sealed system volume
# (/usr/bin/python3's stub, /bin/sh) is named by the OS build, which names those
# bytes. No path, mtime or version string is part of it.
#
# A tree larger than TREE_MAX_ENTRIES (a shared prefix: /usr on Linux, all of
# Homebrew) has no bounded identity. That tool's part is then a fresh nonce:
# the run is judged, but nothing it records can ever serve, and nothing cached
# serves it (fail-closed; the hermetic action's declared toolchain, TR-0, is the
# lasting answer). A dynamic library loaded from outside the tool's own tree and
# the sealed system is not in the identity: measured 2026-11-06, no tool here
# links one (`otool -L` of the atpkg store's trustc, targo, lake, git, clean
# and of aterm).
#
# Digests are taken once per process per stat snapshot (every entry's inode,
# size, mtime and ctime): an entry written since is hashed again. Nothing is
# stored between runs.
SEALED_SYSTEM = ("/bin/", "/sbin/", "/usr/bin/", "/usr/sbin/", "/usr/lib/", "/usr/libexec/", "/System/")
_SEALED_FOLDED = tuple(prefix.casefold() for prefix in SEALED_SYSTEM)
INSTALL_TREE_MARKERS = ("lib", "libexec", "share", "include")
TREE_MAX_ENTRIES = 100_000
SHIM_MAX_BYTES = 1 << 20
_QUOTED_ABSOLUTE = re.compile(r"""'(/[^'\n]+)'|"(/[^"$`\\\n]+)"|(?:^|[\s;|&(])exec\s+(/[^\s'";|&)]+)""")
_DIGEST_MEMO: Dict[Tuple[str, str], str] = {}


class UnboundedTree(RuntimeError):
    """A tree too large to identify (a shared prefix)."""


def os_build() -> str:
    """What names the sealed system volume's bytes: the OS build on macOS."""
    try:
        build = subprocess.run(["/usr/bin/sw_vers", "-buildVersion"], capture_output=True, text=True,
                               timeout=30).stdout.strip()
    except (OSError, subprocess.TimeoutExpired) as exc:
        raise RuntimeError(f"cannot read the macOS build: {exc}") from exc
    if not build:
        raise RuntimeError("sw_vers named no macOS build")
    return f"macOS {platform.mac_ver()[0]} ({build})"


def sealed_system_path(real: str) -> bool:
    """On the read-only system volume: a sealed-system prefix (APFS is case
    insensitive, so compared case-folded) on a file system mounted read-only.
    /System/Volumes/ (the writable Data, Preboot and Update volumes, where a
    root link such as /nix resolves, in any spelling) and the read-write
    firmlinks under those prefixes are digested like any other path; one
    whose volume cannot be read is too (review of EW-1)."""
    if platform.system() != "Darwin" or not real.casefold().startswith(_SEALED_FOLDED):
        return False
    try:
        return bool(os.statvfs(real).f_flag & os.ST_RDONLY)
    except OSError:
        return False


def _walk(path: Path) -> List[Tuple[Path, str]]:
    """Every entry under the tree `path` (itself when it is no directory), as
    (path, relative path) in a fixed order. UnboundedTree past the limit."""
    if not path.is_dir() or path.is_symlink():
        return [(path, "")]
    out: List[Tuple[Path, str]] = []
    for dirpath, dirs, files in os.walk(path):
        dirs.sort()
        for name in sorted(dirs + files):
            p = Path(dirpath) / name
            out.append((p, str(p.relative_to(path))))
        if len(out) > TREE_MAX_ENTRIES:
            raise UnboundedTree(f"{path} holds more than {TREE_MAX_ENTRIES} entries")
    return out


def _snapshot(entries: List[Tuple[Path, str]]) -> str:
    """The stat facts of `entries`: a digest taken under this snapshot holds
    while it is unchanged (a write moves ctime)."""
    h = hashlib.sha256()
    for p, rel in entries:
        st = os.lstat(p)
        h.update(f"{rel}\0{st.st_mode}\0{st.st_ino}\0{st.st_dev}\0{st.st_size}\0{st.st_mtime_ns}\0"
                 f"{st.st_ctime_ns}\n".encode("utf-8", "surrogateescape"))
    return h.hexdigest()


def content_digest(path: Path) -> str:
    """sha256 over a file's bytes, or over a tree: every entry's relative path,
    kind, permission bits and content (a link by its target). RuntimeError when
    it cannot be read or keeps changing; UnboundedTree past the limit."""
    for _attempt in range(3):
        try:
            entries = _walk(path)
            before = _snapshot(entries)
            memo = _DIGEST_MEMO.get((str(path), before))
            if memo is not None:
                return memo
            h = hashlib.sha256()
            for p, rel in entries:
                st = os.lstat(p)
                if stat.S_ISLNK(st.st_mode):
                    h.update(f"L\0{rel}\0{os.readlink(p)}\n".encode("utf-8", "surrogateescape"))
                elif stat.S_ISDIR(st.st_mode):
                    h.update(f"D\0{rel}\n".encode("utf-8", "surrogateescape"))
                elif stat.S_ISREG(st.st_mode):
                    digest = sha256_file(p)
                    if digest.startswith("unreadable:"):
                        raise OSError(f"{p}: {digest}")
                    h.update(f"F\0{rel}\0{st.st_mode & 0o7777:o}\0{digest}\n".encode("utf-8", "surrogateescape"))
                else:
                    h.update(f"O\0{rel}\0{stat.S_IFMT(st.st_mode)}\n".encode("utf-8", "surrogateescape"))
            digest = h.hexdigest()
            if _snapshot(_walk(path)) != before:
                continue
            _DIGEST_MEMO[(str(path), before)] = digest
            return digest
        except OSError as exc:
            raise RuntimeError(f"cannot read {path} to identify it: {exc}") from exc
    raise RuntimeError(f"{path} kept changing while it was identified")


def install_tree(real: Path) -> Optional[Path]:
    """The nearest tree a binary loads from: <root> for a binary at
    <root>/bin/... or <root>/libexec/... when <root> also holds lib/, libexec/,
    share/ or include/, or else the app bundle it is in (Xcode's clang is its
    toolchain's usr/, not all of Xcode.app)."""
    for anc in real.parents:
        if anc.name in ("bin", "libexec") and any((anc.parent / m).is_dir() for m in INSTALL_TREE_MARKERS
                                                   if (anc.parent / m) != anc):
            return anc.parent
        if anc.suffix == ".app" and (anc / "Contents").is_dir():
            return anc
    return None


def tree_entry(spelled: str, tree: Path) -> str:
    """Which entry of the install tree `tree` runs when `spelled` is executed,
    and under what name, relative to the tree: a store's multicall binaries
    choose what they do by their name (`cargo` beside `targo`), so the tree's
    content alone does not say what runs (review of EW-1)."""
    named = os.path.join(os.path.realpath(os.path.dirname(spelled) or "."), os.path.basename(spelled))
    real = os.path.realpath(spelled)
    root = str(tree)
    name = os.path.relpath(named, root) if named.startswith(root + "/") else os.path.basename(spelled)
    runs = os.path.relpath(real, root)
    return name if name == runs else f"{name}->{runs}"


def runtime_closure(entry: str) -> List[Tuple[str, str]]:
    """[(kind, what)] for the executable `entry`: kind "tree", "file" or
    "shim" (a path to digest), "entry" (which file of a tree runs, by what
    name), "system" (the sealed system volume) or "absent" (it does not
    exist). A script is followed to every absolute file it names, wherever it
    sits; a binary in an install tree is the tree."""
    out: List[Tuple[str, str]] = []
    seen: set = set()
    todo = [entry]
    while todo:
        spelled = todo.pop(0)
        real = os.path.realpath(spelled)
        if real in seen:
            continue
        seen.add(real)
        if sealed_system_path(real):
            out.append(("system", "sealed"))
            continue
        p = Path(real)
        if not p.exists():
            out.append(("absent", real))
            continue
        tree = install_tree(p)
        named = shim_targets(p)
        if tree is not None:
            # A script inside a tree (a wrapper in ~/.local/bin, a venv entry
            # point) still runs what it names outside it (review of EW-1).
            out.append(("tree", str(tree)))
            out.append(("entry", tree_entry(spelled, tree)))
        else:
            out.append(("shim", real) if named is not None else ("file", real))
        todo.extend(named or ())
    return out


def _shim_text(path: Path) -> Optional[str]:
    try:
        with open(path, "rb") as fh:
            head = fh.read(SHIM_MAX_BYTES + 1)
    except OSError as exc:
        raise RuntimeError(f"cannot read {path} to identify it: {exc}") from exc
    if not head.startswith(b"#!") or len(head) > SHIM_MAX_BYTES:
        return None
    return head.decode("utf-8", "surrogateescape")


def shim_targets(path: Path) -> Optional[List[str]]:
    """The absolute files a script names, its shebang's interpreter first,
    each as spelled in the script; None for what is not a script."""
    text = _shim_text(path)
    if text is None:
        return None
    named: List[str] = []
    shebang = text.splitlines()[0][2:].strip().split() if text.splitlines() else []
    if shebang and shebang[0].startswith("/"):
        named.append(shebang[0])
    for m in _QUOTED_ABSOLUTE.finditer(text):
        target = next(g for g in m.groups() if g)
        if os.path.exists(target) and not os.path.isdir(target):
            named.append(target)
    return list(dict.fromkeys(named))


def _named_identity(target: str) -> str:
    """What a file a script names stands for in the script's digest: the
    entry of its install tree and the name it is run by, the sealed system
    path, or the file's content. Never its directory: the same store at
    another path is the same toolchain (review of EW-1)."""
    real = os.path.realpath(target)
    if sealed_system_path(real):
        return f"system:{target}"
    tree = install_tree(Path(real))
    if tree is not None:
        return f"tree:{tree_entry(target, tree)}"
    return f"file:{content_digest(Path(real))}"


def shim_digest(path: Path) -> str:
    """A script by its text, with every file it names (each of which is a
    part of the same closure) spelled by _named_identity: the store directory
    a shim names is not part of what runs; which entry runs, and its content,
    are."""
    text = _shim_text(path)
    if text is None:
        raise RuntimeError(f"{path} stopped being a script while it was identified")
    for target in sorted(shim_targets(path) or (), key=len, reverse=True):
        text = text.replace(target, f"\0{_named_identity(target)}\0")
    return hashlib.sha256(f"S\0{os.stat(path).st_mode & 0o7777:o}\0".encode() +
                          text.encode("utf-8", "surrogateescape")).hexdigest()


def python_closure(executable: str) -> List[str]:
    """What the Python `executable` really runs, as the interpreter reports
    it: its executable and its standard library (pure and platform)."""
    if os.path.realpath(executable) == os.path.realpath(sys.executable):
        import sysconfig
        paths = sysconfig.get_paths()
        return [sys.executable, paths["stdlib"], paths["platstdlib"]]
    try:
        proc = subprocess.run([executable, "-I", "-c", "import sys, sysconfig; p = sysconfig.get_paths(); "
                               "print(sys.executable); print(p['stdlib']); print(p['platstdlib'])"],
                              capture_output=True, text=True, timeout=60)
    except (OSError, subprocess.TimeoutExpired) as exc:
        raise RuntimeError(f"cannot ask {executable} what it runs: {exc}") from exc
    lines = proc.stdout.splitlines()
    if proc.returncode != 0 or len(lines) < 3:
        raise RuntimeError(f"{executable} did not report what it runs (exit {proc.returncode})")
    return lines[:3]


def closure_parts(entry: str, python: bool = False) -> List[Tuple[str, str]]:
    parts = runtime_closure(entry)
    if python:
        try:
            exe, *stdlib = python_closure(entry)
        except RuntimeError as exc:
            # Not a Python that says what it runs: judged, never cached.
            return [*dict.fromkeys(parts), ("opaque", f"{entry}: {exc}")]
        parts += runtime_closure(exe)
        for d in stdlib:
            real = os.path.realpath(d)
            if sealed_system_path(real):
                parts.append(("system", "sealed"))
            elif os.path.isdir(real):
                parts.append(("tree", real))
            else:
                parts.append(("absent", real))
    trees = [w for k, w in parts if k == "tree"]
    # A tree inside another of this closure is already in that one's digest.
    return [part for part in dict.fromkeys(parts)
            if not (part[0] == "tree" and any(part[1].startswith(t + "/") for t in trees))]


def part_identity(kind: str, what: str) -> str:
    if kind == "system":
        return f"system:{os_build()}"
    if kind == "absent":
        return "absent"
    if kind == "entry":
        return f"entry:{what}"
    if kind == "shim":
        return f"shim:{shim_digest(Path(what))}"
    if kind == "opaque":
        print(f"land-gate: no bounded identity for {what}; no cached outcome serves this run, and none it "
              "records can serve another", file=sys.stderr)
        return f"unbounded:{os.urandom(16).hex()}"
    try:
        return f"{kind}:{content_digest(Path(what))}"
    except UnboundedTree as exc:
        print(f"land-gate: no bounded identity for {what} ({exc}); no cached outcome serves this run, and none "
              "it records can serve another", file=sys.stderr)
        return f"unbounded:{os.urandom(16).hex()}"


def c_toolchain_parts() -> List[Tuple[str, str]]:
    """The linker and C compiler every compile leg reaches through `cc` and
    `c++` on PATH (rustc's default linker and cc-rs both run the bare name),
    and the SDK it links against. On macOS /usr/bin/cc is a stub on the sealed
    volume that runs what the developer-directory selection names, so that is
    asked of xcrun (in this environment, which the legs inherit and the key
    holds); a `cc` or `c++` PATH finds ahead of the stub is identified by its
    own closure (review of EW-1). Elsewhere `cc` is PATH's."""
    if platform.system() != "Darwin":
        cc = shutil.which("cc")
        return list(dict.fromkeys([*(closure_parts(cc) if cc else [("absent", "cc")]), *override_tool_parts()]))
    found: List[str] = []
    for argv in (["/usr/bin/xcrun", "-f", "cc"], ["/usr/bin/xcrun", "-f", "ld"],
                 ["/usr/bin/xcrun", "--show-sdk-path"]):
        try:
            proc = subprocess.run(argv, capture_output=True, text=True, timeout=60)
        except (OSError, subprocess.TimeoutExpired) as exc:
            return [("opaque", f"{' '.join(argv)}: {exc}")]
        if proc.returncode != 0 or not proc.stdout.strip():
            return [("opaque", f"{' '.join(argv)}: exit {proc.returncode}")]
        found.append(proc.stdout.strip())
    cc, ld, sdk = found
    sdk_real = os.path.realpath(sdk)
    sdk_part = ("tree", sdk_real) if os.path.isdir(sdk_real) else ("absent", sdk_real)
    on_path: List[Tuple[str, str]] = []
    for name in ("cc", "c++"):
        found_at = shutil.which(name)
        if found_at is None:
            on_path.append(("absent", name))
        elif not sealed_system_path(os.path.realpath(found_at)):
            on_path.extend(closure_parts(found_at))
    return list(dict.fromkeys([*closure_parts(cc), *closure_parts(ld), sdk_part, *on_path,
                               *override_tool_parts()]))


# What a leg may run in place of PATH's tools (review of EW-1): cc-rs runs
# CC/CXX/AR/RANLIB in their CC_<target>, TARGET_ and HOST_ forms before PATH's
# `cc`, rustc runs a configured linker before `cc`, and bootstrap hands its
# [target.*] cc, cxx, ar, ranlib and linker to both. The env key holds only a
# variable's text; the tool behind it is identified by its content here.
_TOOL_ENV = re.compile(r"(?:(?:TARGET|HOST)_)?(?:CC|CXX|AR|RANLIB)(?:_[A-Za-z0-9_.-]+)?|CARGO_TARGET_[A-Z0-9_]+_LINKER|MAKE")
_FLAG_ENV = re.compile(r"RUSTFLAGS|RUSTDOCFLAGS|CARGO_BUILD_RUSTFLAGS|CARGO_ENCODED_RUSTFLAGS|"
                       r"CARGO_ENCODED_RUSTDOCFLAGS|CARGO_TARGET_[A-Z0-9_]+_RUSTFLAGS")
_LINKER_FLAG = re.compile(r"(?:-C\s*|--codegen[=\s]+)linker=(\S+)")
_TARGET_TOOL_KEYS = ("cc", "cxx", "ar", "ranlib", "linker")


def _bootstrap_target_tables() -> Dict[str, object]:
    """The effective bootstrap configuration's [target.*] tables (includes and
    profile merged, as x.py reads them); {} with no configuration."""
    selected = next((p for p in _bootstrap_config_paths() if p.exists()), None)
    if selected is None:
        return {}
    try:
        config = mint_seed_support.effective_bootstrap_config(REPO_ROOT, selected.resolve(strict=True), confine=False)
    except (OSError, mint_seed_support.WorkflowError) as exc:
        raise RuntimeError(f"cannot read bootstrap configuration {selected}: {exc}") from exc
    target = config.get("target", {})
    return target if isinstance(target, dict) else {}


def toolchain_overrides(env: Optional[Dict[str, str]] = None) -> List[Tuple[str, str]]:
    """(where it is named, the command) for every compiler, archiver or
    linker a leg may run in place of PATH's."""
    env = os.environ if env is None else env
    named: List[Tuple[str, str]] = []
    for name in sorted(env):
        value = env[name]
        if _TOOL_ENV.fullmatch(name) and value.strip():
            named.append((name, value))
        elif _FLAG_ENV.fullmatch(name):
            named.extend((name, m.group(1)) for m in _LINKER_FLAG.finditer(value.replace("\x1f", " ")))
    for triple, table in sorted(_bootstrap_target_tables().items()):
        if isinstance(table, dict):
            for key in _TARGET_TOOL_KEYS:
                value = table.get(key)
                if isinstance(value, str) and value.strip():
                    named.append((f"target.{triple}.{key}", value))
    return named


def override_tool_parts() -> List[Tuple[str, str]]:
    """The runtime closure of every word of each override that names a
    program (a wrapper such as `ccache cc` names two); one that names none
    that exists is absent, by its text."""
    parts: List[Tuple[str, str]] = []
    for origin, command in toolchain_overrides():
        try:
            # MAKE is an executable path consumed by Command, not shell words.
            # A path containing spaces must retain its complete file identity.
            words = [command] if origin == "MAKE" else shlex.split(command)
        except ValueError:
            words = command.split()
        found = False
        for word in words:
            if word.startswith("-"):
                continue
            path = (word if os.path.isabs(word) else str(REPO_ROOT / word)) if "/" in word else shutil.which(word)
            if path and os.path.exists(path) and not os.path.isdir(path):
                parts.extend(closure_parts(path))
                found = True
        if not found:
            parts.append(("absent", f"{origin}={command}"))
    return parts


def closure_identity(entry: str, python: bool = False) -> List[str]:
    """The content identity of `entry`'s runtime closure, one string per part."""
    return list(dict.fromkeys(part_identity(k, w) for k, w in closure_parts(entry, python)))


def toolchain_identity() -> Dict[str, object]:
    """Every tool a leg may run from PATH, the gate's own Python, and the
    seed (stage0) and formatter binaries bootstrap uses, each by the content
    of its runtime closure (EW-1)."""
    ident: Dict[str, object] = {}
    parts: Dict[str, Optional[List[Tuple[str, str]]]] = {}
    # Shell legs can still read PATH's Python; direct Python legs inherit ours.
    for tool, path in ([(tool, shutil.which(tool)) for tool in TOOLS]
                       + [("gate-python", sys.executable), ("row-system-bash", "/bin/bash")]):
        try:
            parts[tool] = closure_parts(path, python=tool in ("python3", "gate-python")) if path else None
        except RuntimeError as exc:
            raise RuntimeError(f"cannot identify {tool}: {exc}") from exc
    try:
        parts["cc"] = c_toolchain_parts()
    except RuntimeError as exc:
        raise RuntimeError(f"cannot identify the C toolchain: {exc}") from exc
    for b in _stage0_binaries():
        try:
            os.stat(b)
        except FileNotFoundError:
            parts[f"stage0:{b}"] = None
            continue
        except OSError as exc:
            raise RuntimeError(f"cannot inspect seed binary {b}: {exc}") from exc
        try:
            parts[f"stage0:{b}"] = closure_parts(b)
        except RuntimeError as exc:
            raise RuntimeError(f"cannot hash seed binary {b}: {exc}") from exc
    # Each tree once, however many tools run from it.
    seen: Dict[Tuple[str, str], str] = {}
    for tool, ps in parts.items():
        if ps is None:
            ident[tool] = None
            continue
        try:
            for part in ps:
                if part not in seen:
                    seen[part] = part_identity(*part)
        except RuntimeError as exc:
            if tool.startswith("stage0:"):
                raise RuntimeError(f"cannot hash seed binary {tool[len('stage0:'):]}: {exc}") from exc
            raise RuntimeError(f"cannot identify {tool}: {exc}") from exc
        ident[tool] = list(dict.fromkeys(seen[part] for part in ps))
    return ident


def _cargo_config_paths() -> List[Path]:
    """Cargo reads .cargo/config(.toml) in the working directory and every
    ancestor, then $CARGO_HOME: the untracked ones are build inputs no tree
    fingerprint holds (the checkout's own .cargo/ is tracked: a global input)."""
    out: List[Path] = []
    d = REPO_ROOT.parent
    while True:
        out += [d / ".cargo" / "config.toml", d / ".cargo" / "config"]
        if d.parent == d:
            break
        d = d.parent
    home = Path(os.environ.get("CARGO_HOME") or (Path.home() / ".cargo"))
    out += [home / "config.toml", home / "config"]
    return out


def config_identity() -> Dict[str, str]:
    out: Dict[str, str] = {}
    _build, included = _bootstrap_build_config()
    for p in list(_bootstrap_config_paths()) + _cargo_config_paths():
        try:
            key = str(p.relative_to(REPO_ROOT))
        except ValueError:
            key = str(p)
        out[key] = sha256_file(p) if p.exists() else "absent"
    for p, digest in included.items():
        try:
            key = str(p.relative_to(REPO_ROOT))
        except ValueError:
            key = str(p)
        out[key] = digest
    return out


_GLOBAL_FP: Dict[str, str] = {}


def global_fingerprint(g: ls.Graph) -> str:
    """The fingerprint of every path that selects every leg (land_select.global_inputs):
    part of every key, so a change the selector answers with "run everything"
    can never be answered by the cache instead."""
    if g.index.rev not in _GLOBAL_FP:
        _GLOBAL_FP[g.index.rev] = g.index.fingerprint(ls.global_inputs(g))
    return _GLOBAL_FP[g.index.rev]


def env_identity(env: Optional[Dict[str, str]] = None) -> Dict[str, str]:
    env = dict(os.environ if env is None else env)
    return {k: v for k, v in sorted(env.items()) if not ENV_IGNORED.match(k)}


_GATE_SNAPSHOT: Dict[str, str] = {}


def gate_code_identity(extra_scripts: Sequence[str]) -> Dict[str, str]:
    """The gate's own files as THIS process loaded them (hashed once, on first
    use, which is before any leg runs: an edit on disk during a long run must
    not let a PASS of the old code be stored under the new code's key), and
    refreshed review data and the row table (GATE_DATA_FILES), and the scripts
    a leg runs, as they are on disk when its key is taken (just before the leg
    starts them)."""
    if not _GATE_SNAPSHOT:
        _GATE_SNAPSHOT.update({p: sha256_file(REPO_ROOT / p) for p in GATE_FILES if p not in GATE_DATA_FILES})
    out = {p: (sha256_file(REPO_ROOT / p) if p in GATE_DATA_FILES
               else _GATE_SNAPSHOT.get(p) or sha256_file(REPO_ROOT / p)) for p in GATE_FILES}
    out["scripts/lib/remote_tips.py"] = _REMOTE_TIPS_SOURCE_SHA256
    out["scripts/lib/checkout_inputs.py"] = _CHECKOUT_INPUTS_SOURCE_SHA256
    out["scripts/lib/native_checkout.py"] = _NATIVE_CHECKOUT_ADAPTER_SHA256
    out[native_checkout.NATIVE_SOURCE] = _NATIVE_CHECKOUT_READER_SHA256 or "unavailable"
    out.update({p: sha256_file(REPO_ROOT / p) for p in extra_scripts if p not in GATE_FILES})
    return dict(sorted(out.items()))


class RescaleRefused(RuntimeError):
    """The current host budget does not admit the resources this leg uses."""


def crates_test_threads(test_jobs: int, pool_jobs: int) -> int:
    """Share libtest workers across the concurrent crate binaries, at least one."""
    return max(1, test_jobs // max(1, pool_jobs))


def budget_plans(host: host_budget.Host,
                 kinds: Sequence[str] = tuple(host_budget.KINDS)) -> Dict[str, host_budget.Plan]:
    """Size to current memory without expanding a machine-wide admission share.
    One parser owns the share: a missing or malformed one refuses (AdmissionInvalid)."""
    max_jobs = host_budget.admitted_jobs()
    return {k: host_budget.plan(host, k, max_jobs=max_jobs) for k in kinds}


def rescale(leg: "Leg", host: host_budget.Host) -> Dict[str, object]:
    """Size `leg` to the host as measured NOW, just before it starts (a gate run
    lasts hours and its neighbours come and go): x.py's -j and CARGO_BUILD_JOBS
    from the rustc-build plan, UI RUST_TEST_THREADS from ui-test shared across the crates pool
    from crates-test. Direct harness and Rayon defaults follow rustc-build;
    callers keep their explicit values. Effective Rayon settings stay keyed.
    Scheduling only: no key holds these. Refuse a leg whose current memory plan
    admits no child; the governor is a backstop, not an admission override.
    Invalid build-slot shares never keep an older plan.
    Returns what it chose, for the run record."""
    plans = budget_plans(host, ("rustc-build", "ui-test", "crates-test"))
    required = {kind for var, kind in (("CARGO_BUILD_JOBS", "rustc-build"),
                ("RUST_TEST_THREADS", "ui-test"), ("TRUST_CRATES_TESTS_JOBS", "crates-test"))
                if var in leg.env}
    if "-j" in leg.command or (leg.prepare and "-j" in leg.prepare):
        required.add("rustc-build")
    if any(var in leg.default_env for var in ("RAYON_NUM_THREADS", "RUST_TEST_THREADS")):
        required.add("rustc-build")
    refused = [plans[k].refused for k in sorted(required) if plans[k].refused]
    if refused:
        raise RescaleRefused("; ".join(refused))
    jobs = {k: p.jobs for k, p in plans.items()}
    cmd = list(leg.command)
    for i, c in enumerate(cmd[:-1]):
        if c == "-j":
            cmd[i + 1] = str(jobs["rustc-build"])
    leg.command = cmd
    if leg.prepare:
        prep = list(leg.prepare)
        for i, c in enumerate(prep[:-1]):
            if c == "-j":
                prep[i + 1] = str(jobs["rustc-build"])
        leg.prepare = prep
    for var, kind in (("CARGO_BUILD_JOBS", "rustc-build"), ("RUST_TEST_THREADS", "ui-test"),
                      ("TRUST_CRATES_TESTS_JOBS", "crates-test")):
        if var in leg.env:
            budget = jobs[kind]
            if var == "RUST_TEST_THREADS" and leg.id == "crates-tests":
                budget = crates_test_threads(budget, jobs["crates-test"])
            leg.env[var] = str(budget)
    for var in ("RAYON_NUM_THREADS", "RUST_TEST_THREADS"):
        if var in leg.default_env:
            leg.default_env[var] = str(jobs["rustc-build"])
    for k, p in plans.items():
        print(host_budget.describe_plan(host, p))
    return {"mem_avail": host.mem_avail, "load1": host.load1, "jobs": jobs,
            "refused": {k: p.refused for k, p in plans.items() if p.refused}}


@dataclass
class KeyParts:
    leg: str
    targets: Optional[List[str]]
    command: List[str]
    fingerprint: str
    global_fingerprint: str
    history_head: Optional[str]
    toolchain: Dict[str, object]
    config: Dict[str, str]
    env: Dict[str, str]
    gate_code: Dict[str, str]
    host: str
    # Whether the pre-push hook runs on the push (PushHook.mode), for a leg
    # whose work depends on it (the crates leg: touched members): a PASS
    # cached in one mode never answers for the other (LAND-GATE-HOOKLESS-1).
    hook_mode: Optional[str] = None
    # What a leg that declares its reads (Leg.reads, LEG-READS-1) read, as
    # observed when the key is taken. None for every other leg, and then not
    # in the hashed document, so their keys are the keys they always were.
    reads: Optional[Dict[str, object]] = None

    def key(self) -> str:
        fields = {k: v for k, v in self.__dict__.items() if not (k == "reads" and v is None)}
        doc = {"schema": SCHEMA, **fields}
        return hashlib.sha256(json.dumps(doc, sort_keys=True, default=str).encode()).hexdigest()


# ---------------------------------------------------------------------------
# Legs.
# ---------------------------------------------------------------------------


@dataclass
class Leg:
    id: str
    command: List[str]
    scripts: List[str]                  # tracked scripts the leg runs (in the key)
    inputs: List[str]                   # input prefixes (from the selector)
    history: bool
    targets: Optional[List[str]]
    selected: bool
    reasons: List[str]
    needs_stage1: bool = False
    env: Dict[str, str] = field(default_factory=dict)
    # Runtime defaults have lower precedence than the caller's environment.
    # Unlike libtest scheduling, effective Rayon and target-directory choices
    # remain in the key.
    default_env: Dict[str, str] = field(default_factory=dict)
    cache_members: List[str] = field(default_factory=list)   # per-crate legs: one cache row per member
    # Per-member legs: the inputs of a member that is not a crate (the trust-cg
    # run-make fixtures the unit lane runs with --run-make), and the members
    # whose cached PASS also names the stage 1 it ran on.
    member_inputs: Dict[str, List[str]] = field(default_factory=dict)
    stage1_members: List[str] = field(default_factory=list)
    run_targets: Optional[List[str]] = None  # what a partial suite run runs (its known-red rows are judged there)
    # A command run first, in the same log: the stage-1 suites build the
    # batteries-on sysroot (STAGE1_PREPARE). Its failure is the leg's FAIL.
    prepare: Optional[List[str]] = None
    # PushHook.mode for a leg whose selection depends on whether the hook runs
    # (crates-tests); keyed (KeyParts.hook_mode). None: the leg does not depend on it.
    hook_mode: Optional[str] = None
    # The members this leg tests only because the hook does not run (the
    # touched members): the plan's LAND-GATE line names them. They are in the
    # command on every run and never in cache_members: no cached PASS answers
    # for a member the hook would have tested (it replays no verdict).
    hookless_members: List[str] = field(default_factory=list)
    # The hosts of the lane's instruments the change moves (hookless only): the
    # lane runs each from the landing range, under its instrument rules.
    hookless_instruments: List[str] = field(default_factory=list)
    # Work the cache can never answer for (hookless_members, moved
    # instruments): the leg runs even when every cache member hits, and takes
    # no whole-leg key.
    force_run: bool = False
    # {member dir: why} for the members the crates lane takes out of every run
    # on this host (host_limited_members, round 4's D2): never in the command,
    # never a cache member, named in the reasons and the LAND-GATE line.
    host_limited: Dict[str, str] = field(default_factory=dict)
    # Beside a hook, the members the selection touches that the landing push
    # does not carry (round 4's D1: a merge of main, `run --base C`): the
    # hook's lane does not test them, so this leg does.
    beyond_push: List[str] = field(default_factory=list)
    # {crate dir: why} for each [workspace] crate nested inside a crates/
    # member that the change touches or reaches (round 5, D1): no crate of the
    # crates lane, so never in the command or the cache members; named NOT
    # COVERED in the reasons and the LAND-GATE line, never counted tested.
    not_covered: Dict[str, str] = field(default_factory=dict)
    # {shared build: "build" | "check"} (SHARED_BUILDS, EW-19): the builds this
    # leg compiles (or only checks) that other legs compile too. A compile
    # error in one ends every later leg that needs the same build as COULD
    # NOT RUN instead of rebuilding to the same error.
    shared_builds: Dict[str, str] = field(default_factory=dict)
    # Explicit development profile: retain the full diagnostic selection and
    # its reasons, but never execute/cache it as a source-main prerequisite.
    diagnostic_only: bool = False
    # The leg's complete read set beyond the tracked tree, declared
    # (LEG-READS-1): called with the leg and the caller's environment, it
    # returns exact observations of everything the leg's verdict can depend on
    # that no other key element holds (KeyParts.reads), or raises
    # ReadUnobservable, and then the leg runs fresh and records under no key.
    # A leg that declares it needs no full graph to be keyed: its key names
    # `declared:<leg>` where the global fingerprint would be. None: the leg
    # is keyed as before (or not at all: force_run, UNCACHED_LEGS).
    reads: Optional[Callable[["Leg", Optional[Dict[str, str]]], Dict[str, object]]] = None
    # A sealed leg (LEG-READS-1) runs in an environment the gate builds, in
    # every profile, and never in the caller's: sealed_environment, its
    # command's scripts by absolute path, and each program it runs by a bare
    # name, listed here, pinned in a gate-owned directory first on its PATH to
    # the binary `pinned` names. Its reads set `pinned` when its key is taken
    # (sealed_program), so the run starts the binaries its key identifies.
    # Empty: the leg inherits the caller's environment (leg_environment).
    sealed_programs: Tuple[str, ...] = ()
    pinned: Optional[Dict[str, str]] = None
    # The gitlinks (first-party/<repo>) whose pinned sources this leg builds.
    # An unpopulated one makes the leg NOT JUDGED before it runs (targo_unready);
    # a populated one is bound to its pin by the checkout binding.
    required_gitlinks: List[str] = field(default_factory=list)
    # `run` hands the leg's command its checkout binding (CHECKOUT_BOUND_FLAG:
    # push-rows), and the boundary after the leg is a complete pass whatever
    # was reused before it.
    checkout_handoff: bool = False


# The trust-cg run-make fixtures, as a member of the compiler-unit-tests leg:
# check_compiler_unit_tests.sh runs them (--run-make) with its stricter
# all-passed judgement, and run-make-trust leaves them out.
RUN_MAKE_MEMBER = "@trust-cg-run-make"

# scripts/check_crates_tests_scoped.py exits 3 when it ran out of time (a
# stall or its budget: NOT JUDGED, never a pass) and 2 when it judged nothing;
# every other leg says NOT JUDGED with 2.
NOT_JUDGED_EXITS = {"crates-tests": (2, 3)}


def stage1_prepare(jobs: int) -> List[str]:
    """`x.py build --stage 1 library`: the stage-1 sysroot Trust ships, with its
    verifier batteries (ay, clean, ty, trustd, targo, targo-trust) in bin/.
    Bootstrap installs those only for a BUILD (tool.rs,
    should_ensure_default_verifier_tool_bins: "Tests likewise own the packages
    they exercise"), and `x.py test` alone leaves them out, so
    tests/run-make/trust-sysroot-clean-carcara-verify ("batteries-on sysroot must
    ship its Alethe checker") failed on a sysroot only `x.py test` had built
    (measured at this landing). check_compiler_unit_tests.sh builds the same
    sysroot for its rustc_private suites."""
    return [sys.executable, "x.py", "build", "--stage", "1", "-j", str(jobs), "library"]


# The package of the ONE resolver every crates test that compiles through a
# Trust rustc calls (trust_integration_tests::trust_rustc::require_trust_rustc:
# TRUST_RUSTC when set, else discovery under build/; it panics with what it
# searched when nothing qualifies and never skips). A member runs such tests
# when it is this package or depends on it.
TRUST_RUSTC_RESOLVER = "crates/trust-integration-tests"


def stage1_crates_members(g: "ls.Graph", members: Sequence[str]) -> List[str]:
    """The crates-tests members whose tests need a Trust rustc: those whose
    dependency closure (dev-dependencies included) holds the resolver."""
    return sorted(m for m in members if TRUST_RUSTC_RESOLVER in g.closure({m}))


def _xpy_test_cmd(paths: List[str], jobs: int, extra: Sequence[str] = ()) -> List[str]:
    # _reexec_if_old selected Python >= 3.11; do not resolve an older python3 again.
    return [sys.executable, "x.py", "test", "--stage", "1", "-j", str(jobs), "--force-rerun", "--no-fail-fast",
            *paths, *extra]


# Trust: bootstrap's source readiness (src/bootstrap/src/utils/trust_preparation.rs,
# PreparationScope::for_config) is request-scoped only for an explicit `--stage`
# 0 or 1 with explicit paths and no --include-default-paths. Any other producing
# request first checks the whole locked offline recipe envelope, whose Darwin
# fetches run under scripts/bootstrap_dependency_closure.py's retirement
# custodian (DARWIN-DEPENDENCY-FETCH-CUSTODIAN-1). A path-scoped x.py leg names its
# stage, even where it equals the default, so it readies only what it selects; the
# legs listed here need the full request and say why (LAND-GATE-DARWIN-READINESS-1).
XPY_FULL_REQUESTS: Dict[str, str] = {
    "compiler-check": "names no path: it checks bootstrap's whole default check set, the request the full "
                      "envelope readies; listing paths would copy that set here and drop any new default step",
    "compiler-unit-tests": "scripts/check_compiler_unit_tests.sh's second phase is `x.py test --stage 2`: the "
                           "default suites need the in-tree compiler, and stage 2 keeps full readiness",
}


_CRATES_LANE = None


def crates_lane():
    """scripts/check_crates_tests_scoped.py, loaded from beside this file (the
    lane the crates leg runs): its instrument tables are the hook lane's."""
    global _CRATES_LANE
    if _CRATES_LANE is None:
        import importlib.util
        path = Path(__file__).resolve().parent / "check_crates_tests_scoped.py"
        try:
            spec = importlib.util.spec_from_file_location("land_gate_crates_lane", path)
            module = importlib.util.module_from_spec(spec)
            spec.loader.exec_module(module)
        except Exception as exc:  # noqa: BLE001 - any failure is "cannot tell"
            raise RuntimeError(f"cannot load the crates lane's instrument tables from {path}: "
                               f"{exc.__class__.__name__}: {exc}") from exc
        _CRATES_LANE = module
    return _CRATES_LANE


def moved_instrument_hosts(g: ls.Graph, changed: Sequence[str], members: Sequence[str]) -> Dict[str, str]:
    """{member dir: why} for the host of every instrument the hook's crates
    lane would run for `changed` (its CROSS_CRATE_INSTRUMENTS and
    CORPUS_INSTRUMENTS, moved_instruments). The hookless crates leg does NOT
    test these hosts as members for it: a member run is judged by the
    zero-test rule only, and an instrument run by its own (each filter must
    report a test, INSTRUMENT_REQUIRED_PASSES must pass), so the leg hands the
    lane the landing range and the lane runs the instrument itself (round 2,
    D3). This map names them, makes the leg run whatever the cache holds, and
    refuses a host that names no crates/ member here (RuntimeError, NOT
    JUDGED: the lane's `-p <host>` could not run)."""
    out: Dict[str, str] = {}
    for host, tail in crates_lane().moved_instruments(list(changed)):
        dirs = sorted(d for d in g.by_name.get(host, set()) if d in members)
        if not dirs:
            raise RuntimeError(f"the crates lane's instrument host {host!r} is no crates/ member of this tree")
        for d in dirs:
            out.setdefault(d, f"{d}: hosts the hook lane's instrument `{' '.join(tail)}`, whose subject changed; "
                              "the lane runs it from the landing range, under its instrument rules")
    return out


def hook_lane_members(g: ls.Graph, member_dirs: Sequence[str], landing: "LandingRange") -> set:
    """The crates/ members the pre-push hook's crates lane tests on the landing
    push (round 4, D1): its `--push-context` reads the tree diff origin's main
    tip..head (`landing.changed`), never the gate's selection base, and tests
    the member each changed path belongs to. A member counts only when the
    lane's longest-prefix attribution (plan_for) and the selector's owner both
    name it for some path the push changes: a path the two attribute
    differently leaves its member to this gate (fail closed: both run it). A
    push that cannot be stated (`landing.stated` false: the head does not
    contain the tip, or the diff cannot be read) leaves no member to the hook,
    since what it would test is not known.

    The lane's attribution is the lane's own function (path_owner) over the
    lane's own member sets (ls.crates_lane_sets: its default-members and its
    own-workspace roots), never a longest prefix over `member_dirs` (round 5,
    D1). Round 4's longest prefix over the gate's list gave a nested
    `[workspace]` crate a path that the real lane gives to its parent, and the
    two attributions then "agreed" on a crate the lane never tests. Only a
    member of `member_dirs` (this leg's members) is returned."""
    if not landing.stated or landing.changed is None:
        return set()
    lane_owner_of = lane_attribution(g)
    wanted = set(member_dirs)
    out = set()
    for p in landing.changed:
        lane_owner = lane_owner_of(p)
        if lane_owner is not None and lane_owner in wanted and g.owner(p) == lane_owner:
            out.add(lane_owner)
    return out


def lane_attribution(g: ls.Graph):
    """The crates lane's attribution of a changed path, as a function of the
    path: the lane's own path_owner over the lane's own member sets
    (ls.crates_lane_sets: the default-members, then the crates/<dir>
    own-workspace roots), loaded as crates_lane. None for a path the lane
    gives no crate. One function for every place this gate asks what the lane
    tests for a path (round 5, D1)."""
    lane = crates_lane()
    defaults, roots = ls.crates_lane_sets(g)
    members = {d: g.packages[d].name for d in defaults}
    own_roots = sorted(roots - defaults)
    return lambda p: lane.path_owner(p, members, own_roots) if p.startswith("crates/") else None


def host_limited_members(root: Path, dirs: Sequence[str]) -> Dict[str, str]:
    """{member dir: why} for each of `dirs` the crates lane takes out of every
    run on this host (round 4, D2): its own apply_host_limits, asked about the
    tree it runs in (a crate-level `#![cfg(target_os = "<other>")]` in
    src/lib.rs, as crates/trust-worker-linux has). Such a member is never
    tested here, by this gate or by the hook's lane on this host: handed to the
    lane it is only named NOT RUN, so it cannot make the crates leg run (a run
    holding nothing else prints SKIPPED and the gate is NOT JUDGED on every
    cached re-run, the review's scenario) and must not be stored as a cached
    PASS. The lane is loaded as crates_lane (RuntimeError when it cannot be:
    NOT JUDGED, never a guess)."""
    lane = crates_lane()
    plan = lane.Plan()
    plan.own_workspaces = sorted(set(dirs))
    lane.apply_host_limits(plan, Path(root), {})
    return {d: why for d, why in plan.host_limited}


def push_rows_leg(base: str, hook: PushHook, landing: "LandingRange") -> Leg:
    """push-rows: with no hook, the push-profile rows it would run that no leg
    here covers (HOOK_ROWS_COVERED, covered_row_problem), run and graded as the
    hook grades them on the landing push: this checkout's HEAD onto origin's
    main tip as the remote names it when the leg runs (`land_gate.py
    push-rows`, landing_push; never this selection's base, round 2's D1). With
    a landing `run` read (`landing.remote`), the expected remote and tip name the
    publication the other legs were planned onto; push-rows is NOT JUDGED on any other
    (round 3, D5). Never cached: the rows read history, origin/main and the
    ledger (the hook's own reason it replays no verdict, HOOK-NO-REPLAY-2).
    `run` hands it its checkout binding (CHECKOUT_BOUND_FLAG) only with the
    planned HEAD to hold it to (`--expect-head`); without one it binds the
    checkout itself."""
    covered = ", ".join(f"{r} ({leg_id})" for r, (_c, leg_id) in sorted(HOOK_ROWS_COVERED.items()))
    command = [sys.executable, "scripts/land_gate.py", "push-rows"]
    if landing.remote and landing.tip:
        command += ["--expect-tip", landing.tip, "--expect-remote", landing.remote]
    if landing.head:
        command += ["--expect-head", landing.head]
    return Leg("push-rows", command, [HARNESS, HOOK_FILE, QUARANTINE_LEDGER], [ls.EVERYTHING], True, None,
               not hook.active,
               [f"the pre-push hook will not run these rows on the landing push ({hook.fired}: {hook.why}): "
                f"every row of `{HARNESS} --list push` runs here, graded as the hook grades it, but the "
                f"{len(HOOK_ROWS_COVERED)} a leg below covers: {covered} (a covered row still runs here when its "
                "script is not the one its coverage was argued for, when the push edits what its leg reads "
                "another way, or when the pushed ledger quarantines its lane)",
                "on the landing push: THIS CHECKOUT'S HEAD onto origin's main tip as `git ls-remote` names it "
                f"when the leg runs (not the selection base {base[:12]}); a HEAD that does not contain that "
                "tip, or a tip other than the one the legs were planned onto, is NOT JUDGED (merge origin/main "
                "first). A land transaction qualifies its captured source first, then runs these "
                "fresh publication rows; a moved destination requires composition and requalification"]
               if not hook.active else
               [f"the pre-push hook is installed and answers for this landing ({hook.why}): it runs these "
                "rows on the push"],
               checkout_handoff=bool(landing.head))


def landing_selection(g: ls.Graph, sel: ls.Selection, landing: Optional["LandingRange"]) -> Optional[ls.Selection]:
    """The selector's answer for what the landing push carries (origin's main
    tip..head), or None when that cannot be read. The selection itself when
    the push changes exactly what the gate's subject does (the default base is
    the tip)."""
    if landing is None or landing.changed is None:
        return None
    # A path the subject modifies in place may be one the push creates (origin
    # deleted it since the base): the push's own statuses decide its listings.
    in_place = (in_place_changes(str(REPO_ROOT), landing.tip, landing.head)
                if landing.tip and landing.head else set())
    if sorted(landing.changed) == sorted(sel.changed) and in_place == sel.in_place:
        return sel
    if isinstance(sel, DeclaredDevelopmentSelection):
        return declared_development_selection(g, landing.tip, list(landing.changed), in_place)
    return ls.select(g, landing.tip, list(landing.changed), extra_everything=[
        r for r in sel.everything if r.startswith("unverified graph:")], in_place=in_place)


def build_legs(g: ls.Graph, sel: ls.Selection, base: str, plans: Dict[str, host_budget.Plan],
               hook: PushHook, landing: Optional["LandingRange"] = None) -> List[Leg]:
    """The legs for the selection `sel` (base..head). `landing` is what the
    landing push carries (read_landing); None means the gate's subject is the
    push's (replay, and tests that build a selection by hand). With no hook
    answering, the legs that stand in for the hook's scoped rows judge the
    push's range as well as the selection's (round 3, D2): compiler-check is
    selected when either reaches it, and the crates leg hands the lane origin's
    main tip...head, the subject the hook's crates row reads. Beside a hook, the
    crates leg leaves to it only the members the push carries (round 4, D1)."""
    # Trust: never build a leg past the machine-wide admission, whatever
    # plans the caller sized (a stale or unmanaged plan must not leak
    # host-wide -j/env worker counts before rescale() runs).
    admitted = host_budget.admitted_jobs()

    def capped(kind: str) -> int:
        return min(plans[kind].jobs, admitted) if admitted is not None else plans[kind].jobs

    jobs = capped("rustc-build")
    ui_jobs = capped("ui-test")
    crates_jobs = capped("crates-test")
    legs: List[Leg] = []
    d = sel.decisions
    if landing is None:
        landing = LandingRange(base, sel.head, "", True, tuple(sel.changed), "")
    covers = {leg_id: row for row, (_c, leg_id) in HOOK_ROWS_COVERED.items()}
    # A covered row the hook does not run on the push (no hook, or a profile
    # without it: PushHook.answers) is judged here over the push's range.
    push_sel = (landing_selection(g, sel, landing)
                if any(not hook.runs(row) for row in HOOK_ROWS_COVERED) else sel)
    crates_hook = hook.runs(CRATES_ROW)

    def stand_in(leg_id: str) -> Tuple[bool, List[str], List[str]]:
        """(selected, reasons, inputs) for a leg that, when the hook does not
        run the row `covers[leg_id]` on the landing push, stands in for it."""
        dec = d[leg_id]
        if hook.runs(covers[leg_id]):
            return dec.selected, dec.reasons, dec.inputs
        if push_sel is None:
            return True, ([f"stands in for the hook's {covers[leg_id]}, which would judge the landing push, and "
                           f"that push cannot be read ({landing.why}): runs (fail closed)"] + dec.reasons), dec.inputs
        p = push_sel.decisions[leg_id]
        inputs = sorted(set(dec.inputs) | set(p.inputs))
        if dec.selected or not p.selected:
            return dec.selected, dec.reasons, inputs
        return True, ([f"stands in for the hook's {covers[leg_id]}, which judges the landing push (origin's main "
                       f"tip {landing.tip[:12]}..{landing.head[:12]}), and that push reaches it: " +
                       (p.reasons[0] if p.reasons else "selected")] + dec.reasons), inputs

    # push-rows FIRST (round 3, D5): it reads origin's main tip itself and is
    # NOT JUDGED once main moved past HEAD, so every leg before it widened the
    # window in which that can happen (hours, with the compiler and crates legs
    # first). Run first, the window is the plan's own minutes; `run` also
    # refuses before any leg when HEAD does not contain the tip.
    legs.append(push_rows_leg(base, hook, landing))
    # compiler-check
    c = d["compiler-check"]
    c_selected, c_reasons, c_inputs = stand_in("compiler-check")
    legs.append(Leg("compiler-check", [sys.executable, "x.py", "check", "--stage", "1", "--all-targets", "-j", str(jobs)],
                    [], c_inputs, bool(c.history), None, c_selected, c_reasons))
    # ui-trust
    u = d["ui-trust"]
    ui_paths = u.targets if u.targets else ["tests/ui/trust"]
    legs.append(Leg("ui-trust", _xpy_test_cmd(ui_paths, jobs), [SUITE_BASELINES["ui-trust"]], u.inputs,
                    bool(u.history), u.targets,
                    u.selected, u.reasons, needs_stage1=True,
                    env={"RUST_TEST_THREADS": str(ui_jobs)}, run_targets=u.targets,
                    prepare=stage1_prepare(jobs)))
    # run-make-trust: the trust run-make dirs, less the subset the unit-test lane judges.
    r = d["run-make-trust"]
    all_dirs = sorted(ls.run_make_trust_dirs(g))
    mine = [x for x in (r.targets if r.targets is not None else all_dirs)
            if not any(x.split("/")[-1].startswith(p) for p in UNIT_SUBSET_RUN_MAKE)]
    legs.append(Leg("run-make-trust", _xpy_test_cmd(mine, jobs), [SUITE_BASELINES["run-make-trust"]], r.inputs,
                    bool(r.history), r.targets,
                    r.selected and bool(mine), r.reasons if mine else r.reasons + ["(only the unit lane's subset)"],
                    needs_stage1=True, env={"RUST_TEST_THREADS": str(ui_jobs)}, run_targets=mine,
                    prepare=stage1_prepare(jobs)))
    # compiler-unit-tests: every reached crate with tests, and the trust-cg
    # run-make fixtures whenever the backend or one of those fixtures is reached
    # (run-make-trust leaves them to this leg, so a change that reaches only a
    # fixture must select this leg even when it reaches no crate).
    per = sel.per_crate["compiler-unit-tests"]
    reached = sorted(k for k, v in per.items() if v.selected)
    subset_reached = r.selected and (r.targets is None or any(
        x.split("/")[-1].startswith(UNIT_SUBSET_RUN_MAKE) for x in (r.targets or [])))
    run_make_subset = "compiler/rustc_codegen_trust_cg" in reached or subset_reached
    members = reached + ([RUN_MAKE_MEMBER] if run_make_subset else [])
    unit_inputs = sorted({i for k in reached for i in per[k].inputs} | (set(r.inputs) if run_make_subset else set()))
    cmd = ["bash", "scripts/check_compiler_unit_tests.sh", base, "--also", " ".join(reached)]
    if run_make_subset:
        cmd.append("--run-make")
    why = [f"{k}: {per[k].reasons[0]}" for k in reached[:8]]
    if run_make_subset:
        why.append("the trust-cg run-make fixtures: " + ("the backend is reached" if not subset_reached
                                                          else (r.reasons[0] if r.reasons else "reached")))
    legs.append(Leg("compiler-unit-tests", cmd,
                    ["scripts/check_compiler_unit_tests.sh", "scripts/check_trust_verify_suite_ratchet.sh",
                     "tests/known-red/rustc_mir_transform.txt", "tests/known-red/rustc_codegen_trust_cg.txt"],
                    unit_inputs, any(per[k].history for k in reached) or (run_make_subset and bool(r.history)),
                    members, bool(members), why or ["no compiler crate with tests is reached"],
                    env={"CARGO_BUILD_JOBS": str(jobs)}, cache_members=members,
                    member_inputs={RUN_MAKE_MEMBER: list(r.inputs)} if run_make_subset else {},
                    stage1_members=[RUN_MAKE_MEMBER] if run_make_subset else []))
    # crates-tests: reached members the hook's lane (touched members) does not
    # run. With no hook to run that lane (LAND-GATE-HOOKLESS-1), what the lane
    # would have tested is this leg's too, judged by the lane's own rules: the
    # leg hands the lane the landing range (`--range <base>...<head>`, the
    # hook lane's own reading of a range), so the lane itself plans the touched
    # members with their FEATURE_RUNS tails and own-workspace runs, and each
    # instrument the range moves with its per-filter non-zero-test rule and
    # INSTRUMENT_REQUIRED_PASSES (round 2, D3: a host tested only as a member
    # is judged by the zero-test rule, which an #[ignore]d digest test passes).
    # The reached members ride along as `--also-members`; so do the touched
    # members, by the selector's owner as well as the lane's longest prefix
    # (either answer adds one), and those are never answered from a cached PASS.
    # Beside a hook (round 4, D1), the members left to it are those its lane
    # tests on the landing PUSH (hook_lane_members: origin's main tip..head),
    # not those the selection touches: with `run --base C` after a merge of
    # main, a member only main's merge changed lies in C..head and not in what
    # the push carries, and the hook's lane never sees it.
    per = sel.per_crate["crates-tests"]
    if crates_hook:
        hook_tests = hook_lane_members(g, list(per), landing)
        beyond = sorted(k for k in {g.owner(p) for p in sel.changed} & set(per) if k not in hook_tests)
    else:
        hook_tests, beyond = set(), []
    reached = sorted(k for k, v in per.items() if (v.selected or k in beyond) and k not in hook_tests)
    added: Dict[str, str] = {}  # touched member -> why: tested here only because no hook runs
    instruments: Dict[str, str] = {}  # moved instrument's host -> why
    lane_range = "HEAD...HEAD"  # no diff: the lane tests exactly --also-members
    if not crates_hook:
        # What the hook's crates row would judge is the landing push (origin's
        # main tip...head, round 3's D2), not only the selection's base..head:
        # with `--base C`, a member touched before C is still on the push.
        # The lane reads the push's range; a path either range changes makes
        # its member a touched one. When the push cannot be read (`plan` only:
        # `run` refuses before any leg, landing_refusal, whenever the hook does
        # not run this row), the lane reads the selection's range.
        pushed = list(landing.changed) if landing.changed is not None else []
        subject = sorted(set(sel.changed) | set(pushed))
        touched_here = {g.owner(p) for p in subject}
        # The lane attributes a path by its own path_owner (lane_attribution:
        # the member whose directory is its longest prefix, then an
        # own-workspace root); g.owner's deepest package may be a nested
        # non-member. Either answer adds the member.
        lane_owner_of = lane_attribution(g)
        lane_owned = {lane_owner_of(p) for p in subject}
        for k in sorted(per):
            if k in touched_here or k in lane_owned:
                added[k] = (f"{k}: touched; the pre-push hook would test it and will not on this landing, "
                            "so it runs here on every gate (never from a cached PASS)")
        instruments = moved_instrument_hosts(g, pushed if landing.changed is not None else sel.changed, list(per))
        lane_range = (f"{landing.tip}...{sel.head}" if landing.changed is not None and landing.tip
                      else f"{base}...{sel.head}")
    # A member the lane takes out on this host (round 4, D2) is neither handed
    # to it nor cached: it cannot be tested here, by this leg or by the hook's
    # lane on this host, and a run holding only such members prints SKIPPED.
    limited = host_limited_members(Path(g.index.repo), sorted(set(reached) | set(added)))
    for k in limited:
        added.pop(k, None)
    cached = [k for k in reached if k not in added and k not in limited]
    members = sorted(set(cached) | set(added))
    if beyond:
        why_left = (f"origin's main tip {landing.tip[:12]}..{landing.head[:12]}" if landing.stated else
                    f"which cannot be stated ({landing.why or 'unreadable'})")
        beyond_why = {k: (f"{k}: touched by the selection ({base[:12]}..{sel.head[:12]}) but not by the landing push "
                          f"({why_left}); the pre-push hook's lane tests only what the push carries, so it runs here")
                      for k in beyond if k in cached}
    else:
        beyond_why = {}
    limited_why = [f"{k}: NOT RUN on this host ({why}); the crates lane takes it out of every run here, as the "
                   "hook's lane on this host does, so it neither makes this leg run nor is stored as a PASS"
                   for k, why in sorted(limited.items())]
    # A [workspace] crate nested inside a member (ls.nested_workspace_crates:
    # the trust-disasm harnesses, two fixture crates) is no crate of the lane,
    # so it is never handed to it or cached (round 5, D1). One the change
    # touches or reaches is named NOT COVERED: nothing here builds or tests it.
    nested_paths = sel.changed if crates_hook else subject
    nested_touched = {g.owner(p) for p in nested_paths}
    not_covered = {
        k: (f"{k}: NOT COVERED — a separate [workspace] nested inside a crates/ member, "
            f"{'touched' if k in nested_touched else (v.reasons[0] if v.reasons else 'reached')}; the crates lane "
            "tests only its default-members and its crates/<dir> own-workspace crates, so no leg here builds or "
            "tests it and none counts it tested")
        for k, v in sorted(sel.per_crate.get(ls.NESTED_CRATES, {}).items()) if v.selected or k in nested_touched}
    not_covered_why = [not_covered[k] for k in sorted(not_covered)]
    crate_inputs = sorted({i for k in sorted(set(members) | set(instruments)) for i in per[k].inputs})
    # The members whose tests compile through a Trust rustc get THIS tree's
    # stage 1 (TRUST_RUSTC-1): the leg builds it first (or reuses it when the
    # stamp matches), hands it to the lane as TRUST_RUSTC (authoritative in
    # the one resolver, so no other build/ compiler is measured and an
    # operator's override does not reach the gate), and stores each such
    # member's PASS with the sysroot it ran on. Without this a gate whose
    # selection builds no stage 1 (a docs-only change) ran those tests against
    # whatever build/ held: nothing in a fresh worktree, so seven of them
    # panicked "No executable Trust rustc found" (P5A2 record, 2026-11-03).
    stage1_users = stage1_crates_members(g, members)
    # Its time bound is the lane's own: scripts/lib/crates_tests_time.py, the
    # one rule the hook's lane runs under too, over the members this leg hands
    # it (the lane prints it as its `time bound:` line). The leg sets no bound
    # of its own, so the two callers cannot disagree (CRATES-TIME-1); a
    # caller's TRUST_CRATES_TESTS_BUDGET_S or TRUST_CRATES_TESTS_STALL_S still
    # reaches the lane through the environment. Out of time the lane exits 3,
    # NOT JUDGED (NOT_JUDGED_EXITS). The rule is one of the scripts the leg
    # runs, so it is in the leg's key.
    legs.append(Leg("crates-tests", [sys.executable, "scripts/check_crates_tests_scoped.py", "--range", lane_range,
                                     "--also-members", ",".join(members)],
                    ["scripts/check_crates_tests_scoped.py", "scripts/lib/crates_tests_time.py",
                     "scripts/lib/crates_lane_members.py", "tests/known-red/crates-tests.txt"],
                    crate_inputs, any(per[k].history for k in members), members,
                    bool(members) or bool(instruments),
                    ([added[k] for k in sorted(added)] + [instruments[k] for k in sorted(instruments)] +
                     [beyond_why[k] for k in sorted(beyond_why)] + limited_why + not_covered_why +
                     [f"{k}: {per[k].reasons[0]}" for k in cached if k not in beyond_why])[:8]
                    if members or instruments else
                    ([f"no crates/ member this host can test is reached or touched and no instrument moved "
                      f"({hook.why if not hook.active else hook.gaps}: no hook lane runs either)"]
                     if not crates_hook else
                     ["no crates/ member this host can test is reached beyond those the push hook's lane tests"]) +
                    (limited_why + not_covered_why)[:7],
                    env={"CARGO_BUILD_JOBS": str(jobs),
                         "TRUST_CRATES_TESTS_JOBS": str(crates_jobs),
                         # The pool and each binary's libtest harness are nested:
                         # giving both the whole UI budget would multiply it.
                         "RUST_TEST_THREADS": str(crates_test_threads(
                             ui_jobs, crates_jobs)),
                         **({"TRUST_RUSTC": str(stage1_dir() / "bin" / "rustc")} if stage1_users else {})},
                    prepare=stage1_prepare(jobs) if stage1_users else None, stage1_members=stage1_users,
                    cache_members=cached, hook_mode="active" if crates_hook else "absent",
                    hookless_members=sorted(added),
                    hookless_instruments=sorted(instruments), force_run=bool(added) or bool(instruments),
                    host_limited=dict(limited), beyond_push=sorted(beyond_why), not_covered=dict(not_covered)))
    # olean audit
    o = d["olean-audit"]
    # The audit builds and runs trust-clean's example with a targo it finds
    # (TRUST_REGEN_TARGO, else the newest under build/, else PATH). Name the one
    # on PATH: its identity is in the cache key (toolchain_identity), a
    # build-tree one is not, and the newest under build/ moves with any x.py run.
    path_targo = shutil.which("targo")
    olean_env = {"CARGO_BUILD_JOBS": str(jobs)}
    if path_targo:
        olean_env["TRUST_REGEN_TARGO"] = path_targo
    legs.append(Leg("olean-audit", ["bash", "scripts/regen-trustir-oleans.sh", "--check"],
                    ["scripts/regen-trustir-oleans.sh", "scripts/lean_olean_bignums.py"],
                    o.inputs, bool(o.history), None, o.selected, o.reasons,
                    env=olean_env))
    # bootstrap's own tests (Inc 6's five 118-crate snapshots got past every leg).
    b = d["bootstrap-tests"]
    legs.append(Leg("bootstrap-tests", [sys.executable, "x.py", "test", "src/bootstrap", "-j", str(jobs),
                                        "--stage", "1"], [],
                    b.inputs, bool(b.history), None, b.selected, b.reasons))
    # targo-trust's own workspace, every test target. x.py check builds none of
    # it, so compiler-check never compiled them (Inc 6's E0308).
    # Require the named binary inside the full resolved suite: passing library
    # or integration tests cannot replace a missing or empty binary harness.
    # That flag is the only place scoped.targo-trust-unit-tests' zero-passed
    # rule is applied now: the row is in no push profile (round 5, D3), and a
    # targo without the flag makes this leg NOT JUDGED (targo_unready). Under
    # `land` the hook's scoped Targo row runs this same full command once, but
    # only when the pushed profile has that row (round 5, D2); otherwise the
    # leg runs here, never from a cached PASS.
    t = d["targo-trust"]
    legs.append(Leg("targo-trust", landing_targo.COMMAND[:], [], t.inputs, bool(t.history), None,
                    t.selected, t.reasons, env={"CARGO_BUILD_JOBS": str(jobs),
                         "RUST_TEST_THREADS": str(ui_jobs)}))
    # Native Cargo's own tests are not the targo-trust subcommand suite. Let
    # bootstrap construct the tested compiler, std, rustdoc and fixture shims.
    n = d["native-targo-tests"]
    legs.append(Leg("native-targo-tests", _xpy_test_cmd(["src/tools/targo"], jobs), [],
                    n.inputs, bool(n.history), None, n.selected, n.reasons,
                    needs_stage1=True, prepare=stage1_prepare(jobs),
                    env={"CARGO_BUILD_JOBS": str(jobs),
                         "RUST_TEST_THREADS": str(ui_jobs)}))

    # A validator change exercises the validator. It does not change all the
    # compiler's inputs: actual readers still select their normal legs above.
    # Never answer these tests from an older cached PASS while changing a judge.
    validation_modules = sorted(set(ls.validation_test_modules(sel.changed))
                                | set(getattr(sel, "owner_refresh_tests", ())))
    legs.append(Leg("validation-tests", [sys.executable, "-B", "scripts/land_gate.py", "validation-tests", *validation_modules],
                    ls.validation_program_paths(), ls.validation_program_paths(),
                    False, validation_modules, bool(validation_modules),
                    ["changed validation programs: run their tests; compiled inputs follow their own dependencies"]
                    if validation_modules else ["no validation program changed"], force_run=True))
    # tidy reads every tracked path (licenses, widths, the dependency lists, the
    # style ratchet) and asks git: always selected, keyed on the whole tree and HEAD.
    legs.append(Leg("tidy", [sys.executable, "x.py", "test", "tidy", "-j", str(jobs), "--stage", "1"], [],
                    [ls.EVERYTHING], True, None, True, ["always (tidy reads the whole tree)"]))
    # Cheap tree-wide checks: always selected. ir-cohort is never cached (it
    # judges live remote mains; UNCACHED_LEGS says why); tcb-panic-ratchet is
    # keyed on its declared reads (LEG-READS-1).
    legs.append(tcb_panic_ratchet_leg(["always (seconds; reads the TCB crates and its baseline)"]))
    legs.append(ir_cohort_leg())
    for leg in legs:
        leg.shared_builds = shared_builds_of(leg)
        if leg.sealed_programs:
            continue  # its environment is built, and nothing it runs is a rayon pool (LEG-READS-1)
        leg.default_env["RAYON_NUM_THREADS"] = str(jobs)
        if leg.id in ("crates-tests", "targo-trust"):
            leg.default_env["RUST_TEST_THREADS"] = str(jobs)
            # These direct workspace legs run serially in this owning checkout.
            # Share compatible dependency artifacts; Cargo still fingerprints
            # profiles/features, and explicit feature --target-dir lanes stay isolated.
            leg.default_env["CARGO_TARGET_DIR"] = crates_target_dir()
    return fail_fast_order(legs)


def ir_cohort_leg() -> Leg:
    """The same uncached checker for full plans and explicit IR diagnostics.

    It judges waiver expiry on the run's declared date (`--date`, gate_date()),
    raised to the current UTC date when that is later (check_ir_cohort.py
    judged_date), read when each waiver is judged, after the remote phase; the
    checker reads no date from the environment."""
    return Leg("ir-cohort", [sys.executable, "scripts/check_ir_cohort.py", "--date", gate_date().isoformat()],
               ["scripts/check_ir_cohort.py"],
               [ls.EVERYTHING], True, None, True, ["always (seconds; reads every first-party declaration)"])


# ---------------------------------------------------------------------------
# Declared reads and the sealed environment (LEG-READS-1, PLAN PKG-LIVE-3): a
# leg whose complete read set the gate observes itself is keyed on it, in every
# profile, with no graph. It runs in an environment the gate builds, never the
# caller's, so nothing an inherited variable names can reach its run.
# ---------------------------------------------------------------------------


class ReadUnobservable(RuntimeError):
    """A declared read this run cannot observe exactly. The leg runs fresh and
    records under no key: there is never a key without one of its reads."""


# Where the gate resolves a sealed leg's programs (sealed_program): the system
# directories, one list on every host. No caller's PATH is consulted. The
# leg's own PATH is only its directory of pinned programs (sealed_launch), so
# a name the gate did not pin resolves to nothing rather than to a binary no
# key identifies.
SEALED_PATH = ("/usr/bin", "/bin", "/usr/sbin", "/sbin")
# The directory under which each sealed run gets its own fresh directories
# (sealed_launch), chosen by the gate rather than derived from the clone's or
# the caller's paths. Its real path must be literal (SEALED_LITERAL_PATH).
SEALED_BASE_ROOT = "/tmp"
# A path a sealed leg's environment may carry: absolute, every component
# made of these characters only. PATH splits at ':', awk -v processes a
# backslash's escape, a line break ends what sort and the lexer read as one
# line; a path outside this set (a clone at <home>/src:trust among them)
# would put a directory no key element holds on the leg's PATH, or give its
# programs other paths than the run made.
SEALED_LITERAL_PATH = re.compile(r"(/[A-Za-z0-9._+-]+)+")
# A sealed leg that runs git runs it in a checkout whose top level that git,
# in the sealed environment, names as REPO_ROOT (sealed_git_toplevel): a git
# that refuses the checkout (no global safe.directory in the sealed
# environment for a checkout another user owns) or names another top level
# would make the script skip its committed-source check silently.
# git configuration a sealed leg's git takes over every file it reads
# (GIT_CONFIG_COUNT is the command-line scope, above the repository's own
# .git/config and whatever that includes). The ratchet runs two git commands,
# `git rev-parse --show-toplevel` and `git ls-tree -r --name-only -z HEAD --
# <roots>`, which read the repository's configuration, refs and objects:
#   core.fsmonitor=false      an fsmonitor is a program git runs when it reads
#                             the index; neither command reads it, and none can
#                             start one;
#   core.hooksPath=/dev/null  neither command runs a hook, and none can;
#   protocol.allow=never      a partial clone fetches a missing object from its
#                             promisor remote through a transport helper or
#                             ssh (GIT_NO_LAZY_FETCH says the same to a git
#                             that knows it): the object stays missing, and the
#                             run ends NOT JUDGED.
# A pager runs only on a terminal (the leg writes to a pipe), an alias never
# replaces a built-in command, and trace2 is configured only by the system and
# global files the environment turns off. What else the repository's
# configuration says (core.worktree among it) moves only the script's NOT
# JUDGED branch, never its count (LEG-READS-1).
SEALED_GIT_CONFIG = (("core.fsmonitor", "false"), ("core.hooksPath", "/dev/null"), ("protocol.allow", "never"))
# What the key's env element holds for the per-run directories: each run gets
# fresh ones of its own (sealed_launch), and the key holds the shape.
SEALED_HOME = "<gate-owned empty directory>"
SEALED_TMPDIR = "<fresh gate-owned empty directory>"
SEALED_BIN = "<gate-owned directory of the pinned programs>"
SEALED_PYCACHE = "<fresh gate-owned empty directory of compiled Python>"
# The first bytes of a native executable: ELF, and Mach-O thin (32 or 64 bits,
# either byte order) or universal. Anything else is a script run by an
# interpreter, or a text file a shell runs itself when exec refuses it
# (ENOEXEC): either may run programs by names no key element resolves.
NATIVE_MAGIC = (b"\x7fELF", b"\xfe\xed\xfa\xce", b"\xfe\xed\xfa\xcf", b"\xce\xfa\xed\xfe", b"\xcf\xfa\xed\xfe",
                b"\xca\xfe\xba\xbe", b"\xbe\xba\xfe\xca")
# What marks a macOS developer-tool stub (/usr/bin/git among them): it links
# libxcselect and runs the tool of its name in the developer directory that
# xcode-select or DEVELOPER_DIR names, state no key element holds.
DEVELOPER_STUB_MARK = b"/usr/lib/libxcselect.dylib"


def sealed_environment(home: str = SEALED_HOME, tmpdir: str = SEALED_TMPDIR, bindir: str = SEALED_BIN,
                       pycache: str = SEALED_PYCACHE) -> Dict[str, str]:
    """The whole environment of a sealed leg's process; nothing is inherited.
    BASH_ENV, ENV, CDPATH, SHELLOPTS, BASHOPTS, PS4, GREP_OPTIONS, exported
    functions (BASH_FUNC_*), ZDOTDIR, LD_*, DYLD_*, locale directories and
    every other variable a shell or program consults are absent by
    construction; the locale is C, whose data is built in. PATH is only the
    directory of pinned programs: a name the gate did not pin runs nothing.
    PYTHONPYCACHEPREFIX is the run's own empty directory (PYCACHE_ENV)."""
    env = {"PATH": bindir, "LC_ALL": "C", "LANG": "C", "HOME": home,
           "TMPDIR": tmpdir, PYCACHE_ENV: pycache, "GIT_CONFIG_NOSYSTEM": "1", "GIT_CONFIG_GLOBAL": "/dev/null",
           "GIT_NO_REPLACE_OBJECTS": "1", "GIT_OPTIONAL_LOCKS": "0", "GIT_NO_LAZY_FETCH": "1",
           "GIT_CONFIG_COUNT": str(len(SEALED_GIT_CONFIG))}
    for i, (name, value) in enumerate(SEALED_GIT_CONFIG):
        env[f"GIT_CONFIG_KEY_{i}"], env[f"GIT_CONFIG_VALUE_{i}"] = name, value
    return env


def _developer_stub(real: str) -> bool:
    if not sealed_system_path(real):
        return False
    try:
        with open(real, "rb") as fh:
            return DEVELOPER_STUB_MARK in fh.read()
    except OSError as exc:
        raise ReadUnobservable(f"{real}: cannot be read ({exc.__class__.__name__})") from exc


def _xcrun_find(name: str) -> str:
    """The binary the developer-tool stub `name` would run now, as xcrun
    names it with no DEVELOPER_DIR and the sealed PATH."""
    try:
        proc = subprocess.run(["/usr/bin/xcrun", "--find", name], capture_output=True, text=True, timeout=60,
                              env={"PATH": os.pathsep.join(SEALED_PATH), "LC_ALL": "C", "LANG": "C"})
    except (OSError, subprocess.TimeoutExpired) as exc:
        raise ReadUnobservable(f"{name}: xcrun cannot name what its stub runs ({exc.__class__.__name__})") from exc
    found = proc.stdout.strip()
    if proc.returncode != 0 or not found.startswith("/") or "\n" in found:
        raise ReadUnobservable(f"{name}: xcrun named nothing its stub runs (exit {proc.returncode})")
    return found


def _native_executable(shown: str, real: str) -> str:
    """`real` when it is an executable regular file whose first bytes are a
    native executable's; ReadUnobservable otherwise."""
    if not os.path.isfile(real) or not os.access(real, os.X_OK):
        raise ReadUnobservable(f"{shown}: {real} is no executable regular file")
    try:
        with open(real, "rb") as fh:
            magic = fh.read(4)
    except OSError as exc:
        raise ReadUnobservable(f"{shown}: {real} cannot be read ({exc.__class__.__name__})") from exc
    if magic not in NATIVE_MAGIC:
        raise ReadUnobservable(f"{shown}: {real} is not a native executable, and a script or text file may run "
                               "programs by names no key element resolves")
    return real


def sealed_program(name: str) -> str:
    """The binary a sealed leg runs as `name`: the first executable regular
    file of that name in SEALED_PATH, followed to its real file, with a macOS
    developer-tool stub resolved now through xcrun to the binary it would run.
    It must be a native executable. ReadUnobservable otherwise."""
    for directory in SEALED_PATH:
        found = os.path.join(directory, name)
        if os.path.isfile(found) and os.access(found, os.X_OK):
            break
    else:
        raise ReadUnobservable(f"{name}: no executable of that name on the sealed PATH")
    real = os.path.realpath(found)
    if _developer_stub(real):
        real = os.path.realpath(_xcrun_find(name))
        if _developer_stub(real):
            raise ReadUnobservable(f"{name}: xcrun names another developer-tool stub")
    return _native_executable(name, real)


def pin_programs(leg: Leg) -> List[ReadUnobservable]:
    """Resolve each of the leg's sealed programs (sealed_program) into
    leg.pinned, which its run starts; what cannot be resolved is left out and
    returned, and then the leg neither has a key nor runs (sealed_unrunnable)."""
    pinned: Dict[str, str] = {}
    problems: List[ReadUnobservable] = []
    for name in leg.sealed_programs:
        try:
            pinned[name] = sealed_program(name)
        except ReadUnobservable as exc:
            problems.append(exc)
    leg.pinned = pinned
    return problems


def sealed_literal(path: str, what: str) -> str:
    """`path` when every program of a sealed leg takes it literally
    (SEALED_LITERAL_PATH); ReadUnobservable otherwise."""
    if not SEALED_LITERAL_PATH.fullmatch(path):
        raise ReadUnobservable(f"{what} {path!r} is no absolute path of letters, digits and ._+- "
                               "that a sealed leg's PATH and programs take literally")
    return path


def sealed_base_root() -> str:
    """The real directory under which a sealed run makes its own
    (SEALED_BASE_ROOT), literal and a directory; ReadUnobservable otherwise:
    then the leg neither has a key nor runs."""
    real = sealed_literal(os.path.realpath(SEALED_BASE_ROOT), "the sealed base root")
    if not os.path.isdir(real):
        raise ReadUnobservable(f"the sealed base root {real} is no directory")
    return real


def sealed_checkout_root() -> Path:
    """REPO_ROOT's real path, which the ratchet reaches as
    `$(cd -P "$(dirname "$0")/.." && pwd -P)`. Command substitution strips
    trailing newlines, so a checkout whose path holds a newline would be read
    as another directory (a sibling `/x/repo` for `/x/repo\n`) that no key
    element holds: ReadUnobservable, so no key and no run. A newline is the
    only character that substitution changes; any other path stays judged."""
    for spelled in (str(REPO_ROOT), os.path.realpath(REPO_ROOT)):
        if "\n" in spelled:
            raise ReadUnobservable(f"the checkout's path {spelled!r} holds a newline, which the script's "
                                   "$(...) strips, so it would read another directory")
    return Path(os.path.realpath(REPO_ROOT))


def sealed_git_toplevel(git: str, env: Dict[str, str]) -> None:
    """ReadUnobservable unless `git` (the pinned one), run in the sealed
    environment `env` at REPO_ROOT, names REPO_ROOT's real path as its top
    level, as the ratchet's `git rev-parse --show-toplevel` must for its
    committed-source check to run at all."""
    want = os.path.realpath(REPO_ROOT)
    try:
        proc = subprocess.run([git, "rev-parse", "--show-toplevel"], cwd=want, env=env, stdin=subprocess.DEVNULL,
                              capture_output=True, text=True, errors="replace", timeout=60)
    except (OSError, subprocess.TimeoutExpired) as exc:
        raise ReadUnobservable(f"git cannot read the checkout in the sealed environment ({exc.__class__.__name__})"
                               ) from exc
    named = proc.stdout[:-1] if proc.stdout.endswith("\n") else proc.stdout
    if proc.returncode != 0 or named != want:
        why = proc.stderr.strip().splitlines()[:1] or [f"it names {named!r}"]
        raise ReadUnobservable(f"git in the sealed environment does not name {want} as its top level "
                               f"(exit {proc.returncode}: {why[0]})")


def sealed_unrunnable(leg: Leg) -> Optional[str]:
    """Why the sealed leg cannot run sealed, or None. It runs only with every
    program it names pinned (leg.pinned; resolved now when its key pinned
    none or not all) and its command's first word an absolute path to a
    native executable: a name left to SEALED_PATH would run what no key
    identifies, or nothing (a host whose git is elsewhere), and the script
    then takes another branch than the one its key was taken for."""
    problems: List[ReadUnobservable] = []
    if leg.pinned is None or set(leg.pinned) != set(leg.sealed_programs):
        problems = pin_programs(leg)
    program = leg.command[0] if leg.command else ""
    try:
        if not os.path.isabs(program):
            raise ReadUnobservable(f"{program!r}: a sealed leg names its program by absolute path")
        _native_executable(program, os.path.realpath(program))
    except ReadUnobservable as exc:
        problems.append(exc)
    return "; ".join(str(p) for p in problems) or None


# What a sealed run holds in its gate-owned program directory while the leg
# runs: nobody writes it (the gate starts nothing beside a sealed leg).
SEALED_BIN_MODE = 0o555


@contextlib.contextmanager
def sealed_launch(leg: Leg, command: List[str]):
    """(command, env, moved) for a sealed leg's run, in fresh gate-owned
    directories under the sealed base root (never a path the clone or the
    caller chose), each literal: an empty HOME, an empty TMPDIR, an empty
    directory of compiled Python (PYCACHE_ENV), and a read-only directory, the whole of PATH, holding for each sealed program a
    link to the binary leg.pinned names (sealed_unrunnable: all of them).
    When git is one of them it must name REPO_ROOT as its top level there
    (sealed_git_toplevel). ReadUnobservable before anything of the leg starts
    otherwise. The command's scripts are named by absolute path. `moved()`
    says how that directory differs, after the run, from what the run was
    started with, or None. The directories are removed when it ends."""
    pinned = dict(leg.pinned or {})
    if set(pinned) != set(leg.sealed_programs):
        raise RuntimeError(f"{leg.id}: a sealed leg starts only with every program pinned (sealed_unrunnable)")
    sealed_checkout_root()
    try:
        base = Path(tempfile.mkdtemp(prefix=f"{leg.id}.sealed.", dir=sealed_base_root()))
    except OSError as exc:
        raise ReadUnobservable(f"a sealed run's directory cannot be made ({exc.__class__.__name__})") from exc
    try:
        home, tmpdir, bindir, pycache = base / "home", base / "tmp", base / "bin", base / "pycache"
        for directory in (home, tmpdir, bindir, pycache):
            directory.mkdir()
            sealed_literal(str(directory), "a sealed run's directory")
        for name, real in sorted(pinned.items()):
            os.symlink(real, bindir / name)
        os.chmod(bindir, SEALED_BIN_MODE)
        env = sealed_environment(str(home), str(tmpdir), str(bindir), str(pycache))
        if "git" in pinned:
            sealed_git_toplevel(str(bindir / "git"), env)

        def moved() -> Optional[str]:
            try:
                mode = stat.S_IMODE(os.lstat(bindir).st_mode)
                held = {e.name: os.readlink(e.path) if e.is_symlink() else None for e in os.scandir(bindir)}
            except OSError as exc:
                return f"its program directory cannot be read after the run ({exc.__class__.__name__})"
            if mode != SEALED_BIN_MODE or held != pinned:
                return "its program directory changed while it ran"
            return None

        scripts = set(leg.scripts)
        yield ([str(REPO_ROOT / word) if word in scripts else word for word in command], env, moved)
    finally:
        with contextlib.suppress(OSError):
            os.chmod(base / "bin", 0o755)
        shutil.rmtree(base, ignore_errors=True)


def _program_identity(real: str, seen: Dict[Tuple[str, str], str]) -> List[str]:
    """A pinned binary by its path and the content of its runtime closure (on
    a sealed system volume, the OS build that names its bytes)."""
    try:
        parts = closure_parts(real)
        for part in parts:
            if part not in seen:
                seen[part] = part_identity(*part)
    except RuntimeError as exc:
        raise ReadUnobservable(f"cannot identify {real}: {exc}") from exc
    ident = list(dict.fromkeys(seen[part] for part in parts))
    if any(i.startswith("unbounded:") for i in ident):
        raise ReadUnobservable(f"{real} has no bounded identity")
    return [real, *ident]


TCB_RATCHET_SCRIPT = "scripts/check_tcb_panic_freedom.sh"
TCB_RATCHET_BASELINE = "scripts/check_tcb_panic_freedom.baseline"
# The script's TCB_ROOTS, spelled as it spells them (a trailing slash
# included): TcbRatchetReadTests holds them to what bash makes of the array.
TCB_RATCHET_ROOTS = (
    "crates/trust-vcgen/src",
    "crates/trust-router/src",
    "crates/trust-types/src",
    "crates/trust-loop/src",
    "crates/trust-cache/src",
    "crates/trust-ir-bridge/src",
    "crates/trust-vc-bridge/src",
    "crates/trust-cg-bridge/src",
    "crates/trust-wasm-bridge/src",
    "compiler/rustc_mir_transform/src/trust_verify.rs",
    "compiler/rustc_mir_transform/src/trust_verify/",
)
# The shell the gate starts the script with, by absolute path, reading no
# startup file (--noprofile --norc; BASH_ENV is absent).
TCB_RATCHET_SHELL = "/bin/bash"
# Every program the script runs by its bare name; the rest of what it does is
# bash builtins. Each is pinned (sealed_program). `mv` runs only under
# --update-baseline and `rm` in its exit trap: both are pinned anyway.
TCB_RATCHET_PROGRAMS = ("awk", "dirname", "find", "git", "grep", "mktemp", "mv", "rm", "sort")
# sha256 of the script whose reads are declared here. The declaration is an
# audit of those bytes (DECISION_QUEUE.md LEG-READS-1 lists what they read);
# other bytes may read anything, so they run fresh until the audit is renewed
# here (TcbRatchetReadTests.test_the_audited_script_is_the_trees fails until then).
TCB_RATCHET_AUDITED_SHA256 = "80c37dcc9b1a9c7fb74058b70dff07f37396b493dd4cc70b43c44560dcc88e1c"


def _read_through(path: Path, shown: str) -> str:
    """sha256 of the bytes a reader that opens `path` gets (awk and grep
    follow a link); ReadUnobservable unless that is a regular file."""
    try:
        st = os.stat(path)
    except OSError as exc:
        raise ReadUnobservable(f"{shown}: cannot be read ({exc.__class__.__name__})") from exc
    if not stat.S_ISREG(st.st_mode):
        raise ReadUnobservable(f"{shown}: listed, but neither a regular file nor a link to one")
    digest = sha256_file(path)
    if digest.startswith("unreadable:"):
        raise ReadUnobservable(f"{shown}: {digest}")
    return digest


def _find_rs(top: Path, shown: str) -> Dict[str, str]:
    """`find <top> -name '*.rs'` as find -P lists it (no link followed, every
    directory entered whatever its name, every entry whose name ends `.rs`
    listed whatever its kind), each listed path by the bytes read through it.
    A name that sort and the lexer cannot read as one line of UTF-8 text is
    unobservable, and so is a link find neither lists nor enters: the
    script's `[ -f ]` of a committed source below it follows it."""
    out: Dict[str, str] = {}
    pending = [(top, shown.rstrip("/") + "/")]
    while pending:
        directory, prefix = pending.pop()
        try:
            with os.scandir(directory) as listing:
                entries = list(listing)
        except OSError as exc:
            raise ReadUnobservable(f"{prefix}: cannot be listed ({exc.__class__.__name__})") from exc
        for e in entries:
            try:
                e.name.encode("utf-8")
            except UnicodeEncodeError:
                raise ReadUnobservable(f"{prefix}: a name that is not UTF-8") from None
            if "\n" in e.name:
                raise ReadUnobservable(f"{prefix}: a name with a line break")
            rel = prefix + e.name
            try:
                is_dir = e.is_dir(follow_symlinks=False)
                is_link = e.is_symlink()
            except OSError as exc:
                raise ReadUnobservable(f"{rel}: cannot be inspected ({exc.__class__.__name__})") from exc
            if e.name.endswith(".rs"):
                out[rel] = _read_through(Path(e.path), rel)
            elif is_link:
                raise ReadUnobservable(f"{rel}: a link find neither lists nor enters, which the script's `[ -f ]` "
                                       "of a committed source below it follows")
            if is_dir:
                pending.append((Path(e.path), rel + "/"))
    return out


def tcb_ratchet_reads(leg: Leg, env: Optional[Dict[str, str]] = None) -> Dict[str, object]:
    """Everything scripts/check_tcb_panic_freedom.sh reads that no other key
    element holds, as it runs in the sealed environment (LEG-READS-1): the
    shell and each program the script runs by name, pinned (leg.pinned, which
    the run starts), by its path and the content of its runtime closure; each
    root's own kind; every entry its `find <root> -name '*.rs'` lists, by the
    bytes read through it (an untracked or ignored file, and the target of a
    link, wherever it is, included); the baseline's bytes. The caller's
    environment (`env`) reaches neither the run nor this: the env element
    holds the constructed one. The tracked tree under the roots (the script's
    `git ls-tree` of HEAD) is the key's fingerprint; the script is gate code;
    the host is an element of its own; the date is the outcome's window."""
    problems = pin_programs(leg)
    if problems:
        raise problems[0]
    sealed_base_root()  # a leg that cannot run sealed has no key either
    seen: Dict[Tuple[str, str], str] = {}
    programs: Dict[str, List[str]] = {
        "bash": _program_identity(_native_executable("bash", os.path.realpath(TCB_RATCHET_SHELL)), seen)}
    for name, real in sorted((leg.pinned or {}).items()):
        programs[name] = _program_identity(real, seen)
    root = sealed_checkout_root()
    if sha256_file(root / TCB_RATCHET_SCRIPT) != TCB_RATCHET_AUDITED_SHA256:
        raise ReadUnobservable(f"{TCB_RATCHET_SCRIPT} is not the script whose reads were audited "
                               "(TCB_RATCHET_AUDITED_SHA256)")
    # The script reads below `cd -P "$(dirname "$0")/.."`: this checkout
    # only while scripts/ is a directory of it, not a link to another tree.
    if (root / "scripts").is_symlink() or not (root / "scripts").is_dir():
        raise ReadUnobservable("scripts/ is no directory of this checkout: the script would read another tree")
    kinds: Dict[str, str] = {}
    sources: Dict[str, str] = {}
    for spelled in TCB_RATCHET_ROOTS:
        path = root / spelled.rstrip("/")
        try:
            st = os.lstat(path)
        except (FileNotFoundError, NotADirectoryError):
            kinds[spelled] = "absent"
            continue
        except OSError as exc:
            raise ReadUnobservable(f"{spelled}: cannot be inspected ({exc.__class__.__name__})") from exc
        if stat.S_ISDIR(st.st_mode):
            if spelled.rstrip("/").endswith(".rs"):
                raise ReadUnobservable(f"{spelled}: a directory find would list as a source")
            kinds[spelled] = "directory"
            sources.update(_find_rs(path, spelled))
        elif stat.S_ISREG(st.st_mode) and not spelled.endswith("/"):
            kinds[spelled] = "file"
            sources[spelled] = _read_through(path, spelled)
        elif stat.S_ISREG(st.st_mode):
            kinds[spelled] = "absent"  # `[ -f x/ ]` and `[ -d x/ ]` are both false
        else:
            raise ReadUnobservable(f"{spelled}: a root that is a link or another kind of file")
    if os.path.lexists(root / TCB_RATCHET_BASELINE):
        baseline = _read_through(root / TCB_RATCHET_BASELINE, TCB_RATCHET_BASELINE)
    else:
        baseline = "absent"
    return {"roots": kinds, "sources": dict(sorted(sources.items())), "baseline": baseline, "programs": programs}


def tcb_panic_ratchet_leg(reasons: List[str]) -> Leg:
    """The TCB panic ratchet, one leg in every profile: sealed (run by
    /bin/bash with no startup file, in sealed_environment, its programs
    pinned) and keyed on its declared reads (tcb_ratchet_reads): the tracked
    tree only under its roots, the baseline and the script; neither HEAD nor
    the global inputs."""
    inputs = sorted({r.rstrip("/") for r in TCB_RATCHET_ROOTS} | {TCB_RATCHET_BASELINE, TCB_RATCHET_SCRIPT})
    return Leg("tcb-panic-ratchet", [TCB_RATCHET_SHELL, "--noprofile", "--norc", TCB_RATCHET_SCRIPT],
               [TCB_RATCHET_SCRIPT], inputs, False, None, True, reasons, reads=tcb_ratchet_reads,
               sealed_programs=TCB_RATCHET_PROGRAMS)


# Trust: fail fast (EW-19). The legs that take about a minute together run
# right after push-rows (which stays first, round 3's D5), then the gate's own
# tests, then the compiler and workspace legs that take hours: a red the cheap
# legs can show is shown before any long build starts.
CHEAP_LEGS = ("tidy", "tcb-panic-ratchet", "ir-cohort", "validation-tests")


def fail_fast_order(legs: List[Leg]) -> List[Leg]:
    """`legs` with push-rows first, then CHEAP_LEGS, then the rest in their
    built order."""
    rank = {leg_id: i for i, leg_id in enumerate(("push-rows",) + CHEAP_LEGS)}
    return sorted(legs, key=lambda leg: rank.get(leg.id, len(rank)))


# Trust: the builds more than one leg compiles (EW-19). A deterministic compile
# error in one of them is the same error for every leg that needs it: gate run
# 20261027T175434 spent 3.4 h while three legs each rebuilt to one E0658 seed
# failure. Each is {name: (what it is, the bootstrap section that compiles it;
# None: whatever the leg's prepare step compiles)}. A Cargo line names a crate,
# not the build that compiled it (compiler crates are also path dependencies of
# Trust tools, std is reached by name from the compiler's graph), so a failure
# is attributed by the section bootstrap printed before it (Session::msg:
# `Building stage1 compiler artifacts (stage0 -> stage1, <target>)`), never by
# crate name. A crate-name closure reduced the seed's set to rustc-main on the
# real tree (review of EW-19, 2026-11-04).
SHARED_BUILDS: Dict[str, Tuple[str, Optional["re.Pattern[str]"]]] = {
    "seed-compiler": ("the stage-1 compiler, compiled by the seed (stage 0)",
                      re.compile(r"^(?:Building|Checking) stage1 compiler artifacts\b.*"
                                 r"\(stage0(?::\S+)? -> stage1\b")),
    "stage1-library": ("the stage-1 standard library, compiled by the stage-1 compiler",
                       re.compile(r"^Building stage1 library artifacts\b.*\(stage1(?::\S+)? -> stage1\b")),
    "stage1-sysroot": ("the batteries-on stage-1 sysroot (`x.py build --stage 1 library`, each leg's "
                       "identical prepare step)", None),
}
# Any bootstrap section header (`<Action> stage<N> <what> ...`): a section ends
# at the next one.
_BOOTSTRAP_SECTION = re.compile(r"^[A-Z][a-z]+ stage\d+ \S.*$", re.M)


# How each leg takes part in a shared build:
#   "check"  checks it (x.py check): its compile error there is one every leg
#            that builds it repeats, since checking a library target runs the
#            front end the build runs; a build error (codegen, a
#            post-monomorphisation error) need not be a check error, so a
#            builder's failure never stops a checker;
#   "build"  builds it: its compile error stops every later checker or builder;
#   "uses"   builds it among other things it cannot tell apart in its log
#            (compiler-unit-tests also runs `x.py test --stage 2`, where the
#            stage-1 compiler compiles the compiler crates again): stopped by
#            another leg's failure, never the leg that names one;
#   "prepare" builds it in its prepare step only, and its own command is no
#            x.py build of it (crates-tests when it prepares the stage 1 for
#            the members that compile through a Trust rustc, TRUST_RUSTC-1):
#            stopped as a builder is, and it names a broken build only when
#            its prepare step is what failed (a crates/ compile error in its
#            Cargo run is the workspace's, not the compiler's build).
# Bootstrap itself is no shared build here: `x.py check` checks the bootstrap
# crate as well, so its error there is no proof x.py cannot run, and a broken
# bootstrap ends each x.py leg within about a minute anyway.
SHARED_BUILD_LEGS: Dict[str, Dict[str, str]] = {
    "compiler-check": {"seed-compiler": "check"},
    "ui-trust": {"seed-compiler": "build", "stage1-library": "build", "stage1-sysroot": "build"},
    "run-make-trust": {"seed-compiler": "build", "stage1-library": "build", "stage1-sysroot": "build"},
    "native-targo-tests": {"seed-compiler": "build", "stage1-library": "build", "stage1-sysroot": "build"},
    "compiler-unit-tests": {"seed-compiler": "uses", "stage1-library": "uses"},
}


def shared_builds_of(leg: Leg) -> Dict[str, str]:
    if leg.id not in SHARED_BUILD_LEGS and leg.stage1_members and leg.prepare:
        # A leg that prepares this tree's stage 1 for its own command
        # (TRUST_RUSTC-1) builds every one of them in that step, and only there.
        return ({b: "prepare" for b in SHARED_BUILDS}
                if _sans_jobs(leg.prepare) == _sans_jobs(stage1_prepare(1)) else {})
    out = dict(SHARED_BUILD_LEGS.get(leg.id, {}))
    # The sysroot is shared only by an identical prepare step (-j aside).
    if "stage1-sysroot" in out and _sans_jobs(leg.prepare or []) != _sans_jobs(stage1_prepare(1)):
        del out["stage1-sysroot"]
    return out


def _sans_jobs(command: Sequence[str]) -> List[str]:
    out, skip = [], False
    for c in command:
        if skip:
            skip = False
        elif c == "-j":
            skip = True
        else:
            out.append(c)
    return out


# Cargo's line for a target whose rustc ended with errors. `due to N previous
# errors` is printed only when rustc reported errors: a killed or crashed
# compiler (memory, a signal) ends without it, and is no deterministic failure
# another leg would repeat. Neither is a target whose only errors are the
# linker's or the file system's (a killed linker, a full disk): rustc reports a
# failed link as an error too. Test, bench and example targets are the leg's
# own, never a shared build.
_COULD_NOT_COMPILE = re.compile(
    r"^error: could not (?:compile|check) `([^`]+)` \((lib|bin \"[^\"]+\"|build script)\)"
    r"(?: \([^)]*\))? due to (?:\d+ )?previous errors?\b", re.M)
_ANY_COULD_NOT = re.compile(r"^error: could not (?:compile|check) `", re.M)
_RUSTC_ERROR = re.compile(r"^error(?:\[E\d{4}\])?: (?!could not (?:compile|check) `|aborting due to).*$", re.M)
_NOT_DETERMINISTIC = re.compile(r"linking with|linker|No space left on device|failed to write|could not write|"
                                r"os error 28|Broken pipe|Killed|SIGKILL|out of memory|Cannot allocate memory",
                                re.I)


def shared_build_failures(log_text: str, leg: Leg, prepare_failed: bool = False) -> List[Tuple[str, str, str]]:
    """[(shared build, how the leg takes part in it, why)] for each shared
    build `leg` names (never one it only "uses") that a deterministic compile
    error in `log_text` breaks: one in that build's bootstrap section, or, for
    the prepare step's sysroot, any one when that step is what failed."""
    out: List[Tuple[str, str, str]] = []
    for m in _COULD_NOT_COMPILE.finditer(log_text):
        crate, target = m.group(1), m.group(2)
        # The errors since the previous target's Cargo line of any kind (a
        # test target's too); parallel jobs may still interleave, so the one
        # cited is the leg's first error there, not a proof of cause.
        start = max((x.end() for x in _ANY_COULD_NOT.finditer(log_text, 0, m.start())), default=0)
        errors = [e.group(0).strip() for e in _RUSTC_ERROR.finditer(log_text, start, m.start())
                  if not _NOT_DETERMINISTIC.search(e.group(0))]
        if not errors:
            continue  # no compile error of its own: a link or I/O failure, or one this log does not show
        sections = list(_BOOTSTRAP_SECTION.finditer(log_text, 0, m.start()))
        section = sections[-1].group(0) if sections else ""
        why = f"`{crate}` ({target}) did not compile: {errors[0][:240]}"
        for build, mode in leg.shared_builds.items():
            if mode == "uses" or (mode == "prepare" and not prepare_failed) or any(b == build for b, _m, _w in out):
                continue
            pattern = SHARED_BUILDS[build][1]
            if (pattern is None and prepare_failed) or (pattern is not None and pattern.search(section)):
                out.append((build, mode, why))
    return out


def note_shared_failures(broken: Dict[str, Tuple[str, str, str]], leg: Leg, entry: Dict[str, object],
                         shared: Sequence[Tuple[str, str, str]]) -> None:
    """Record the shared builds `leg`, which did not pass, failed: the first
    leg to fail one names it for every later leg."""
    if str(entry.get("outcome", "")).startswith("PASS"):
        return
    for build, mode, why in shared:
        if build in broken:
            continue
        broken[build] = (leg.id, mode, why)
        entry.setdefault("shared_build_failed", []).append({"build": build, "mode": mode, "why": why})
        print(f"{leg.id}: failed building {SHARED_BUILDS[build][0]}: {why}; every later leg that needs it "
              "ends COULD NOT RUN")


def could_not_run(leg: Leg, broken: Dict[str, Tuple[str, str, str]]) -> Optional[str]:
    """Why `leg` cannot run, when a leg before it failed in a build it needs:
    any error there stops a later leg that builds it; only a check error stops
    a later leg that checks it (a build error need not be a check error)."""
    for build, mode in leg.shared_builds.items():
        if build not in broken:
            continue
        failed, failed_mode, why = broken[build]
        if mode in ("build", "uses", "prepare") or failed_mode == "check":
            return (f"{failed} failed building {SHARED_BUILDS[build][0]}, which this leg needs too, "
                    f"and would rebuild to the same error: {why}")
    return None


# Trust: the target-directory variables the gate passes to a child. Each is
# named by its resolved real path (EW-24): on Macs set up before 2026-09-10
# crates/target is a symlink to crates/target.noindex, and atpkg refuses an
# explicit target named through a symlink ("build cache ownership refused:
# explicit build target is unmanaged or unsupported"), so crates-tests and
# targo-trust ended in 3 s with exit 75 having built nothing. Named by its
# real path, atpkg adopts the same directory.
TARGET_DIR_VARS = ("CARGO_TARGET_DIR", "TARGO_TARGET_DIR")


def real_target_dir(value: str, cwd: Path) -> str:
    """`value` (a target directory as a child would read it, relative to its
    working directory `cwd`) as its real path: every symlink in it resolved,
    a missing tail kept as written. An empty value stays empty: Targo judges
    that spelling itself."""
    if not value:
        return value
    return os.path.realpath(os.path.join(str(cwd), value))


def crates_target_dir(root: Optional[Path] = None) -> str:
    """The direct workspace legs' shared target: `crates/target` of the owning
    checkout, named by its real path (crates/target.noindex where it is a
    symlink to that)."""
    root = REPO_ROOT if root is None else root
    return real_target_dir(str(root / "crates" / "target"), root)


def resolve_target_dirs(env: Dict[str, str], cwd: Path) -> Dict[str, str]:
    """`env` with each target-directory variable it sets named by its real
    path (in place; also returned)."""
    for var in TARGET_DIR_VARS:
        if var in env:
            env[var] = real_target_dir(env[var], cwd)
    return env


# ---------------------------------------------------------------------------
# Cache.
# ---------------------------------------------------------------------------


def cache_dir() -> Path:
    return common_dir() / "trust-land" / "cache"


LANDING_RANGE_KEY = "<the landing range: its work is never cached>"


def command_for_key(leg: Leg) -> List[str]:
    """The leg's command without its scheduling (-j N), without the member
    list a per-crate leg narrows (each member has its own key), and, for the
    hookless crates leg, without its landing range's commits: what the range
    adds (touched members, moved instruments) runs on every gate (force_run)
    and is never stored, so a reached member's PASS, which the range does not
    change, survives a re-merge of main that moves the base."""
    out: List[str] = []
    skip = False
    for i, c in enumerate(leg.command):
        if skip:
            skip = False
            continue
        if c == "-j":
            skip = True
            continue
        if leg.cache_members and c in ("--also", "--also-members"):
            out.append(c)
            skip = True
            continue
        if leg.id == "crates-tests" and c == "--range" and leg.command[i + 1:i + 2] != ["HEAD...HEAD"]:
            out += [c, LANDING_RANGE_KEY]
            skip = True
            continue
        out.append(c)
    return out


def leg_environment(leg: Leg, env: Optional[Dict[str, str]] = None, *,
                    pycache: Optional[Path] = None) -> Dict[str, str]:
    """The same defaults, caller choices and mandatory settings for keys and
    execution. `pycache` is the fresh directory the leg's process compiles
    Python into (PYCACHE_ENV); a key, which has none, holds LEG_PYCACHE, and
    every program the gate starts with this environment is given one."""
    if leg.sealed_programs:
        # A sealed leg's environment is built, never inherited (LEG-READS-1):
        # its key holds this shape, and its run the same with real directories
        # (sealed_launch). The leg's own settings would be a second source.
        if leg.env or leg.default_env:
            raise RuntimeError(f"{leg.id}: a sealed leg takes no environment settings of its own")
        return sealed_environment()
    caller = os.environ if env is None else env
    defaults = dict(leg.default_env)
    # Native Targo imports TARGO_TARGET_DIR only when CARGO_TARGET_DIR is absent.
    # A fallback must not suppress the caller's explicit native spelling.
    if "TARGO_TARGET_DIR" in caller and "CARGO_TARGET_DIR" not in caller:
        defaults.pop("CARGO_TARGET_DIR", None)
    # The caller's value keeps its precedence and is resolved as the default is.
    merged = resolve_target_dirs({**defaults, **caller, **leg.env}, REPO_ROOT)
    # Trust: inside a build-slot admission a caller's worker count survives only
    # within the admitted share; a larger or malformed one (or an unreadable
    # share) takes the sized default.
    share = host_budget.admitted_jobs(caller)
    if share is not None:
        for var in ("RAYON_NUM_THREADS", "RUST_TEST_THREADS"):
            if var in defaults and var in caller and var not in leg.env:
                raw = caller[var]
                try:
                    within_share = bool(re.fullmatch(r"[1-9][0-9]*", raw)) and int(raw) <= share
                except ValueError:
                    within_share = False
                if not within_share:
                    merged[var] = defaults[var]
        # Trust: a leg built from plans sized before (or without) this
        # admission must not leak host-wide worker counts through its
        # mandatory env or runtime defaults either: cap each to the share.
        # A smaller explicit value survives; rescale() still owns the
        # memory sizing and the crates pool's thread division.
        for var in ("CARGO_BUILD_JOBS", "RUST_TEST_THREADS",
                    "RAYON_NUM_THREADS", "TRUST_CRATES_TESTS_JOBS"):
            if var in merged and (var in leg.env or var in defaults):
                raw = merged[var]
                if not re.fullmatch(r"[1-9][0-9]*", raw):
                    raise RescaleRefused(f"{var} has no positive worker plan")
                try:
                    workers = int(raw)
                except ValueError:
                    raise RescaleRefused(f"{var} worker plan is too large to parse") from None
                merged[var] = str(min(workers, share))
    # The one declared date (EW-1), over any caller's: what a leg reads as
    # today is the date its outcome is recorded under.
    merged.update({var: gate_date().isoformat() for var in DATE_ENV})
    # Over any caller's: compiled Python is read from the gate's own fresh
    # directory, never from the checkout's __pycache__ (PYCACHE_ENV).
    merged[PYCACHE_ENV] = LEG_PYCACHE if pycache is None else str(pycache)
    return merged


def key_parts(leg: Leg, idx: ls.TreeIndex, member: Optional[str] = None,
              inputs: Optional[List[str]] = None, env: Optional[Dict[str, str]] = None,
              toolchain: Optional[Dict[str, object]] = None, global_fp: Optional[str] = None) -> KeyParts:
    targets = [member] if member is not None else leg.targets
    # Observed first: a read this run cannot observe raises ReadUnobservable
    # before any other element is computed, and no key exists without it.
    reads = None if leg.reads is None else leg.reads(leg, env)
    if global_fp is None:
        global_fp = global_fingerprint(ls.build_graph(idx))
    return KeyParts(
        leg=leg.id,
        targets=targets,
        command=command_for_key(leg),
        fingerprint=idx.fingerprint(inputs if inputs is not None else leg.inputs),
        global_fingerprint=global_fp,
        history_head=idx.rev if leg.history else None,
        toolchain=toolchain if toolchain is not None else toolchain_identity(),
        config=config_identity(),
        env=env_identity(leg_environment(leg, env)),
        gate_code=gate_code_identity(leg.scripts),
        host=f"{platform.system()}-{platform.machine()}",
        hook_mode=leg.hook_mode,
        reads=reads,
    )


# ---------------------------------------------------------------------------
# The date (EW-1): one declared input, and each outcome's validity window.
# ---------------------------------------------------------------------------
# A leg's answer can depend on the date: the ledgers it reads hold entries that
# lapse (`expires_on` in tests/upstream-rust/ and
# tests/trust-comprehensive/). The gate takes one UTC date when a run starts,
# hands it to every leg under the names its readers take (DATE_ENV), and
# records it on every outcome with `valid_until`, the last date the outcome
# answers for. A lookup refuses a PASS whose window does not hold the run's
# date, and a FAIL contradicts only a PASS whose window it meets. Each outcome
# is valid through its own date only: no leg is known to read the date only
# through DATE_ENV (targo-trust's trust-added ledgers read the clock and refuse
# an override, TRUST_EXCEPTION_VALIDATION_DATE; tests may call the clock), so
# none may claim a later bound. That keeps today's same-day reuse. Bounding a
# window by the ledgers an action reads (the earliest `expires_on`) needs the
# date to be its only clock: the shared result schema (DV-1) and the sandbox
# that refuses an undeclared clock read (TR-0) own that.
DATE_ENV = ("TRUST_GATE_DATE", "TRUST_UPSTREAM_COMPAT_VALIDATION_DATE")
_GATE_DATE: List[datetime.date] = []


def gate_date() -> datetime.date:
    """The run's declared date: the UTC date when this process first asked."""
    if not _GATE_DATE:
        _GATE_DATE.append(datetime.datetime.now(datetime.timezone.utc).date())
    return _GATE_DATE[0]


def outcome_window(row: dict) -> Optional[Tuple[datetime.date, datetime.date]]:
    """(date, valid_until) of a recorded outcome; None for a row without a
    well-formed window (an older format, a damaged record)."""
    try:
        start = datetime.date.fromisoformat(str(row["date"]))
        end = datetime.date.fromisoformat(str(row["valid_until"]))
    except (KeyError, TypeError, ValueError):
        return None
    return (start, end) if start <= end else None


def serves_on(row: dict, day: datetime.date) -> bool:
    window = outcome_window(row)
    return window is not None and window[0] <= day <= window[1]


def windows_meet(a: dict, b: dict) -> bool:
    """Could two outcomes answer for the same date? A row without a window
    meets every other (it may have)."""
    wa, wb = outcome_window(a), outcome_window(b)
    return wa is None or wb is None or (wa[0] <= wb[1] and wb[0] <= wa[1])


CACHE_SCHEMA = "trust-land-cache/2"
CACHE_PASS, CACHE_FAIL, CACHE_NOT_JUDGED, CACHE_COULD_NOT_RUN = "PASS", "FAIL", "NOT JUDGED", "COULD NOT RUN"
# What stands in for a file this gate cannot read: it may have held a FAIL.
CACHE_UNREADABLE = "UNREADABLE"
CACHE_VERDICTS = (CACHE_PASS, CACHE_FAIL, CACHE_NOT_JUDGED, CACHE_COULD_NOT_RUN, CACHE_UNREADABLE)


def cache_outcomes(key: str) -> List[dict]:
    """Every outcome recorded under exactly `key`, oldest first. Anything that
    is not this key's list of outcomes (a file from before EW-21 among them: no
    key this gate computes names one) reads as one UNREADABLE outcome, which
    serves nothing (cache_split)."""
    def unreadable(why: str) -> List[dict]:
        return [{"key": key, "verdict": CACHE_UNREADABLE, "why": why}]

    try:
        rec = json.loads((cache_dir() / f"{key}.json").read_text(encoding="utf-8"))
    except FileNotFoundError:
        return []
    except (OSError, ValueError) as exc:
        return unreadable(f"cannot read it: {exc}")
    if not isinstance(rec, dict) or rec.get("key") != key:
        return unreadable("it is not this key's record")
    rows = rec.get("outcomes")
    if not (isinstance(rows, list) and rows
            and all(isinstance(r, dict) and r.get("verdict") in CACHE_VERDICTS for r in rows)):
        return unreadable("it holds no list of known outcomes")
    return rows


def _fail_contradicts_pass(key: str, fail: dict, passed: dict, assumed: FrozenSet[str] = frozenset()) -> bool:
    """Does this FAIL, recorded under `key`, say the same inputs gave another
    answer than the PASS `passed` under `key` does? Not when their validity
    windows do not meet: the date is an input (EW-1). One naming only `key`
    does. A run of several members failed as a whole: it contradicts once
    every key of that run holds a PASS that answers for its date (a member
    fixed since has a new key, which leaves its old one without a PASS, so a
    fix never reads as a split). A run that also did work no key covers may
    have failed there, and contradicts nothing. Another key whose record cannot
    be read may have held its PASS, so it counts as one, and so does a key in
    `assumed` when the FAIL's window holds this run's date: one the run asking
    is about to run, whose fresh PASS would complete the contradiction (review
    of EW-21)."""
    if not windows_meet(fail, passed):
        return False
    if fail.get("unkeyed_work"):
        return False
    run_keys = fail.get("run_keys") or [key]
    if not isinstance(run_keys, list):
        return True  # not a record this gate wrote: read the worst way
    others = [k for k in run_keys if k != key]
    today = {"date": gate_date().isoformat(), "valid_until": gate_date().isoformat()}
    return all((k in assumed and windows_meet(today, fail))
               or any(r.get("verdict") == CACHE_UNREADABLE
                      or (r.get("verdict") == CACHE_PASS and windows_meet(r, fail))
                      for r in cache_outcomes(str(k)))
               for k in others)


def cache_split(key: str, rows: Optional[List[dict]] = None, assumed: FrozenSet[str] = frozenset()) -> Optional[str]:
    """Why `key` serves no PASS although it holds one or may, or None: it holds
    a PASS for the run's date and a FAIL that contradicts it, or a record that
    cannot be read. A PASS that no longer answers for this date cannot serve,
    so a contradiction of it splits nothing now. `assumed`: keys counted as
    holding a PASS for this date (_fail_contradicts_pass)."""
    rows = cache_outcomes(key) if rows is None else rows
    unreadable = [r for r in rows if r.get("verdict") == CACHE_UNREADABLE]
    if unreadable:
        return f"its record is unreadable ({unreadable[0].get('why')}) and may have held a FAIL"
    passes = [r for r in rows if r.get("verdict") == CACHE_PASS and serves_on(r, gate_date())]
    fails = [r for r in rows if r.get("verdict") == CACHE_FAIL]
    against = [r for r in fails if any(_fail_contradicts_pass(key, r, p, assumed) for p in passes)]
    if not against:
        return None
    return (f"{len(passes)} PASS (last {passes[-1].get('run')}) and {len(against)} FAIL "
            f"(last {against[-1].get('run')}) under one complete key: the same inputs gave two answers")


def cache_lookup(key: str, sysroot: Optional[object] = None, assumed: FrozenSet[str] = frozenset()) -> Optional[dict]:
    """The latest PASS recorded under exactly `key`, unless the key is split:
    no other outcome ever serves. For a stage-1 suite also the stage 1 it ran on
    (`sysroot`, rustc_identity): a sysroot rebuilt or replaced since (by
    anything) is a miss, so a cached PASS always describes the stage 1 that is
    there now. A split ignores the sysroot: the key does not name one, so a
    FAIL on another stage 1 still contradicts. `assumed`: the keys the asking
    run will run (cache_split)."""
    rows = cache_outcomes(key)
    if cache_split(key, rows, assumed):
        return None
    passes = [r for r in rows if r.get("verdict") == CACHE_PASS and serves_on(r, gate_date())
              and (sysroot is None or r.get("sysroot") == sysroot)]
    return passes[-1] if passes else None


def cache_record(key: str, verdict: str, record: dict,
                 window: Optional[Tuple[datetime.date, datetime.date]] = None, unbounded: bool = False) -> None:
    """Add one outcome beside what `key` holds. Worktrees share this directory:
    the read and the write are one step under a lock, so no writer loses another's
    FAIL, and the file moves whole, so a reader needs no lock. Only a PASS
    waits on a pending cancellation: every other outcome serves nothing, and an
    exit already observed is recorded however the gate ends (review of EW-21).
    The outcome is dated by this run's date (gate_date), or by `window` when the
    caller ran under a date another process declared; `unbounded` writes no
    window, so the row meets every PASS (a non-PASS only)."""
    publishes = verdict == CACHE_PASS
    if unbounded and publishes:
        raise ValueError("a PASS always carries its window")
    if publishes:
        _check_cancellation()
    d = cache_dir()
    d.mkdir(parents=True, exist_ok=True)
    with (d / ".lock").open("a", encoding="utf-8") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        start, end = window or (gate_date(), gate_date())
        dated = {} if unbounded else {"date": start.isoformat(), "valid_until": end.isoformat()}
        rows = [*cache_outcomes(key), {**record, "key": key, "verdict": verdict, **dated}]
        tmp = d / f".{key}.{os.getpid()}.tmp"
        tmp.write_text(json.dumps({"schema": CACHE_SCHEMA, "key": key, "outcomes": rows}, indent=1), encoding="utf-8")
        try:
            if publishes:
                _check_cancellation()
            os.replace(tmp, d / f"{key}.json")
        finally:
            tmp.unlink(missing_ok=True)


def cache_store(key: str, record: dict) -> None:
    """Publish a PASS: the one outcome that can later serve."""
    cache_record(key, CACHE_PASS, record)


# ---------------------------------------------------------------------------
# Stage-1 stamp.
# ---------------------------------------------------------------------------


def host_triple() -> str:
    m = platform.machine()
    arch = {"arm64": "aarch64", "x86_64": "x86_64", "aarch64": "aarch64"}.get(m, m)
    return f"{arch}-apple-darwin" if platform.system() == "Darwin" else f"{arch}-unknown-linux-gnu"


def stage1_stamp_path() -> Path:
    return REPO_ROOT / "build" / host_triple() / "trust-land-stage1.json"


def stage1_dir() -> Path:
    return REPO_ROOT / "build" / host_triple() / "stage1"


def rustc_identity(stage1: Optional[Path] = None) -> Optional[List[object]]:
    """What a kept stage 1 is: the content of its lib/ (std, the driver dylib)
    and bin/ (rustc and the tools a suite runs beside it: trustd, ay, clean, ty,
    rustdoc), every file by path, permission bits and sha256 (EW-1), so a std or
    a driver dylib rebuilt by anything else since the stamp was written breaks
    the match, whatever its size and mtime. None when there is no stage-1 rustc;
    RuntimeError when it cannot be read (nothing is judged on it)."""
    stage1 = stage1 or stage1_dir()
    if not (stage1 / "bin" / "rustc").is_file():
        return None
    return [f"{sub}:{content_digest(stage1 / sub)}" for sub in ("lib", "bin")]


def stage1_key(g: ls.Graph, toolchain: Dict[str, object],
               env: Optional[Dict[str, str]] = None) -> str:
    inputs, unresolved, hist = ls.leg_inputs(g, ls.roots_stage1(g), ("compile", "runtime"), False, cwd=False)
    doc = {"schema": SCHEMA, "fingerprint": g.index.fingerprint(inputs), "global": global_fingerprint(g),
           # A stage 1 whose build reads git history is the build of one commit.
           "history_head": g.index.rev if hist else None,
           "toolchain": toolchain,
           "config": config_identity(), "env": env_identity(env), "gate": gate_code_identity([])}
    return hashlib.sha256(json.dumps(doc, sort_keys=True, default=str).encode()).hexdigest()


def stage1_environment_key(inputs_key: str, leg: Leg) -> str:
    """Bind the actual prepare environment without rescanning the stage-1 input tree."""
    doc = {"inputs": inputs_key, "env": env_identity(leg_environment(leg))}
    return hashlib.sha256(json.dumps(doc, sort_keys=True).encode()).hexdigest()


def stage1_reusable(key: str, stamp: Optional[Path] = None, stage1: Optional[Path] = None) -> bool:
    """True only when the stamp names exactly this stage-1 input key AND the
    stage 1 on disk is, file for file and byte for byte (lib/ and bin/), the
    one the stamp was written beside."""
    try:
        rec = json.loads((stamp or stage1_stamp_path()).read_text(encoding="utf-8"))
    except (OSError, ValueError):
        return False
    ident = rustc_identity(stage1)
    return ident is not None and rec.get("key") == key and rec.get("rustc") == ident


def stage1_member_key(key: str, leg: Leg, member: Optional[str], s1_key: str) -> str:
    """The cache key of `member` of `leg`: its own key, and for a member whose
    tests compile through a Trust rustc in a leg that is no stage-1 suite
    (crates-tests, TRUST_RUSTC-1) also this tree's stage-1 environment key
    (`stage1_environment_key`). Such a member's inputs are its crate's alone,
    so without that a PASS measured on the stage 1 an earlier tree built would
    answer for this tree while that stage 1 is still on disk; a stage-1
    suite's own inputs already hold the compiler and library."""
    if member is None or leg.needs_stage1 or member not in leg.stage1_members:
        return key
    doc = {"member": key, "stage1": s1_key}
    return hashlib.sha256(json.dumps(doc, sort_keys=True).encode()).hexdigest()


def cache_keys(leg: Leg, g: ls.Graph, sel: ls.Selection, toolchain: Dict[str, object], gfp: Optional[str],
               s1_inputs_key) -> List[Tuple[Optional[str], str]]:
    """Every (member, key) a run of `leg` looks up and records under: one per
    member of a per-member leg, else the leg's own key ([] for a leg never
    cached). `s1_inputs_key`: this tree's stage-1 inputs key, or a callable
    giving it, asked only for a TRUST_RUSTC-1 member. `run` and `key` both
    use this, so `key` shows the keys a run uses (review of EW-21)."""
    keys: List[Tuple[Optional[str], str]] = []
    if leg.cache_members:
        per = sel.per_crate["crates-tests" if leg.id == "crates-tests" else "compiler-unit-tests"]
        member_s1_key = ""
        if leg.stage1_members and not leg.needs_stage1:
            # A Trust-rustc member's key also names this tree's stage-1
            # inputs (stage1_member_key, TRUST_RUSTC-1).
            member_s1_key = stage1_environment_key(s1_inputs_key() if callable(s1_inputs_key) else s1_inputs_key,
                                                   leg)
        for m in leg.cache_members:
            inputs = leg.member_inputs[m] if m in leg.member_inputs else per[m].inputs
            keys.append((m, stage1_member_key(
                key_parts(leg, g.index, m, inputs, toolchain=toolchain, global_fp=gfp).key(),
                leg, m, member_s1_key)))
    elif leg.id not in UNCACHED_LEGS and not leg.force_run:
        # A leg that declares its reads is keyed without the full graph a
        # global fingerprint needs (run --development computes none): its
        # declared reads stand in for the global inputs (LEG-READS-1).
        if gfp is None and leg.reads is not None:
            gfp = f"declared:{leg.id}"
        try:
            keys.append((None, key_parts(leg, g.index, toolchain=toolchain, global_fp=gfp).key()))
        except ReadUnobservable as exc:
            print(f"land-gate: {leg.id}: {exc}; it runs fresh, and nothing it records serves another run",
                  file=sys.stderr)
            return []
    return keys


def cached_sysroot(leg: Leg, member: Optional[str], on_disk: List[object]) -> Optional[List[object]]:
    """The stage 1 a cached PASS must have run on to answer now (cache_lookup's
    `sysroot`): the one on disk, for a stage-1 suite and for a member that
    compiles through a Trust rustc; None (any) for the rest."""
    return on_disk if (leg.needs_stage1 or member in leg.stage1_members) else None


def stage1_prepare_needed(leg: Leg, todo: Sequence[str]) -> bool:
    """Whether a narrowed leg that prepares the stage 1 for its Trust-rustc
    members (TRUST_RUSTC-1) still needs that step: some such member is still
    to run (not answered by a cached PASS, or a hookless member that always
    runs). A stage-1 suite always keeps its prepare."""
    if leg.needs_stage1 or not leg.prepare or not leg.stage1_members:
        return True
    return bool(set(leg.stage1_members) & (set(todo) | set(leg.hookless_members)))


# ---------------------------------------------------------------------------
# Running.
# ---------------------------------------------------------------------------


XPY_LEGS = ("compiler-check", "ui-trust", "run-make-trust", "compiler-unit-tests", "bootstrap-tests",
            "native-targo-tests", "tidy", "development-recipes", "development-package-compiletest")
# Legs never cached: they judge live remotes, and are cheaper to run than to key
# (push-rows: the hook's rows, HOOK-NO-REPLAY-2; docs/DECISION_QUEUE.md
# LIVE-REMOTE-FRESH-1). ir-cohort's verdict depends on each first-party
# repository's remote main, which moved at least 189 times across the 7 judged
# repositories in 24 h measured 2026-11-15 (2.3% chance that none moves in 30
# minutes, and a development run takes about 24): a sound key on the tips would
# hit about 2% of runs and save about 6 s of local work plus one after-leg
# pass. Its cost is its remote reads (378.8 s in run 20261114T134816, 15
# one-at-a-time ancestry reads); check_ir_cohort.py now batches them per store,
# in parallel, with remembered answers (REACH-MEMO-1), and one cold run still
# spent 355.6 s of 392.2 s in per-store remote work (docs/STATUS.md). The sealed
# split design that could key it is LIVE-REMOTE-FRESH-1's reversal.
# tcb-panic-ratchet left this list when it declared its reads (LEG-READS-1).
UNCACHED_LEGS = ("ir-cohort", "push-rows")
# Legs whose own runner grades each row's `SKIPPED: ` (a row that judged
# nothing) as the hook does; their log carrying one is no "judged nothing".
SELF_GRADED_LEGS = ("push-rows",)


def targo_unready(leg: Leg) -> Optional[str]:
    """Why the `targo` a leg's command runs cannot run that command, or None.
    Only a leg whose command is `targo ...` is asked (targo-trust's,
    landing_targo.COMMAND; a development leg's). The leg runs whatever targo
    its environment's PATH names. landing_targo.COMMAND passes
    `--require-test-bin targo-trust` (9f709bc793), which carries
    scoped.targo-trust-unit-tests' zero-passed rule, and since 39b35cb9f7 no
    push row runs that rule. A targo built before 9f709bc793 rejects the flag
    ("unexpected argument '--require-test-bin'", exit 1), and cmd_run graded
    that FAIL, a red for the landing that its diff cannot fix (round 5, D3).
    landing_targo.capability_gap asks the same targo, in the leg's own
    environment and directory, to parse the leg's own command (`--help` in
    place of anything after `--`). A targo that refuses an argument, or none
    on PATH, makes the leg NOT JUDGED naming the argument, that targo's path
    and its version, never a FAIL of the change or a PASS
    (GATE-TARGO-CAPABILITY-1; round 5's probe grepped `<subcommand> --help`
    for each `--option` and named neither the version nor a refusal targo
    itself gave). The hook's landing suite asks the same question
    (landing_targo.run_targo). The leg never falls back to a shorter command
    or another targo: the canonical environment, whose PATH tools are in the
    key, names the one that runs. That environment's compiled Python goes to
    a fresh directory of the probe's own, removed after it (PYCACHE_ENV), never
    LEG_PYCACHE: a key's text, which as a relative path would put a cache in
    the checkout that every later probe reads."""
    command = list(leg.command)
    if not command or command[0] != "targo":
        return None
    unpopulated = [path for path in leg.required_gitlinks if not (REPO_ROOT / path / ".git").exists()]
    if unpopulated:
        # A fresh worktree has empty gitlinks: Cargo would fail on the missing
        # path dependencies, which is no verdict on the change.
        return (f"{leg.id} builds the pinned first-party sources of {', '.join(unpopulated)}, which this "
                "checkout has not populated; populate the exact committed pins "
                f"(`git submodule update --init -- {' '.join(unpopulated)}`) and run again; no test ran")
    with tempfile.TemporaryDirectory(prefix="land-gate-probe-pycache.") as pycache:
        return _targo_unready(leg, command, leg_environment(leg, pycache=Path(pycache)))


def _targo_unready(leg: Leg, command: List[str], env: Dict[str, str]) -> Optional[str]:
    from land_development import (LOCAL_GIT_CORE_LEG, LOCAL_GIT_FIXTURE_LEG, TARGO_CLEANUP_LEG,
                                  TARGO_NATIVE_CORE_LEG, TARGO_CORE_EXAMPLE_LEG, TOOL_NAME_LEG)
    if leg.id in (TARGO_CLEANUP_LEG, TARGO_NATIVE_CORE_LEG, TARGO_CORE_EXAMPLE_LEG, TOOL_NAME_LEG):
        problem = development_native_target_problem(env)
        if problem:
            return problem
    if leg.id == TOOL_NAME_LEG:
        problem = development_tool_name_resolution_problem(env)
        if problem:
            return problem
    if leg.id in (LOCAL_GIT_FIXTURE_LEG, TARGO_CLEANUP_LEG):
        variable = "TARGO_LOCAL_SOURCE_TEST_BINARY" if leg.id == LOCAL_GIT_FIXTURE_LEG else "TARGO_CLEAN_TEST_BINARY"
        if variable in env:
            return f"native fixture must run the Targo built from this source; unset {variable}"
    # DATA checks do not run rustdoc; cleanup's separate fixture does.
    required = (["MAKE"] if leg.id in (LOCAL_GIT_CORE_LEG, LOCAL_GIT_FIXTURE_LEG) else [])
    if leg.id == LOCAL_GIT_FIXTURE_LEG:
        required.append("RUSTC")
    if leg.id == TARGO_CLEANUP_LEG:
        required.extend(("RUSTC", "RUSTDOC"))
    for name in required:
        value = env.get(name, "")
        if not (os.path.isabs(value) and Path(value).is_file() and os.access(value, os.X_OK)):
            return f"native fixture requires {name} to name its original executable by absolute path"
    return landing_targo.capability_gap(command, env, REPO_ROOT)


def xpy_unready() -> Optional[str]:
    """Check seed paths and the native layout this gate can identify.
    Other prerequisites (including target LLVM configs) are judged by x.py.
    Unsupported setup is NOT JUDGED, never a FAIL of the change or a PASS.

    A configured seed (`[build] rustc` or `cargo` in the effective table, its
    includes and profile read as seed admission reads them) is NOT JUDGED too,
    even when it exists and builds: x.py then compiles with a trustc, or builds
    with a cargo, that is not the committed `src/stage0` pin (a cargo-only
    override still extracts the pinned trustc; session.rs `initial_rustc`), so
    the leg judges a build no fresh checkout makes (D12: the committed pin is
    the only seed; `check_seed_freshness.py` refuses the same keys). The reason
    names the file the key came from: the selected config, an include, or the
    profile defaults. Main stopped building from its pin on 2026-10-25 while
    landing gates ran green on worktree-local stage0 overrides (LAND-GATE-11;
    SEED-NEVER-TYPE-1 and SEED-BRIDGE-1 in docs/DECISION_QUEUE.md)."""
    origins: Dict[str, Path] = {}
    try:
        build, _inputs = _bootstrap_build_config(origins)
    except RuntimeError as exc:
        return str(exc)
    cfgs = [p for p in _bootstrap_config_paths() if p.exists()]
    if not cfgs:
        return "no bootstrap.toml/config.toml in this checkout (x.py has no build configuration)"
    # Stage1 stamps currently bind the default native layout. Refuse another
    # layout rather than checking an unrelated build/<host>/stage1 sysroot.
    build_dir = build.get("build-dir", "build")
    if (not isinstance(build_dir, str)
            or (REPO_ROOT / build_dir).resolve() != (REPO_ROOT / "build").resolve()):
        return "landing gates require the default build/ directory for stage1 identity"
    if build.get("build", host_triple()) != host_triple():
        return "landing gates require the native build triple for stage1 identity"
    if build.get("host", [host_triple()]) != [host_triple()]:
        return "landing gates require exactly the native host for stage1 identity"
    for key, tool in (("rustc", "trustc"), ("cargo", "cargo")):
        if key not in build:
            continue
        value = build[key]
        origin = origins.get(key, cfgs[0])
        if isinstance(value, str) and not (REPO_ROOT / Path(value).expanduser()).exists():
            return f"{origin} names {key} = {value}, which does not exist"
        verb = "compile" if key == "rustc" else "build"
        return (f"{origin} configures its own seed ([build] {key} = {value!r}): x.py would {verb} "
                f"with a {tool} outside the src/stage0 pin, so the leg would not judge the build a "
                f"fresh checkout makes (D12); remove that key from {origin} and x.py extracts the "
                f"pinned {tool}")
    return None


def run_leg(leg: Leg, log_dir: Path, extra_env: Dict[str, str], governor: Tuple[int, int]
            ) -> Tuple[int, float, str, bool]:
    """Run one leg (its prepare step first, when it has one) beside the memory
    governor, into one log. Returns (rc, seconds, log path, whether the PREPARE
    step is what failed)."""
    log = log_dir / f"{leg.id}.log"
    t0 = time.monotonic()
    # Line-buffered, and the echo flushed per line: a leg runs for hours, and a
    # log that lags by a buffer reads as a stall.
    prepare = bool(leg.prepare)
    try:
        with open(log, "w", encoding="utf-8", buffering=1) as fh:
            if leg.prepare:
                rc = _run_one(leg, leg.prepare, fh, extra_env, governor, log_dir)
                if rc != 0:
                    return rc, time.monotonic() - t0, str(log), True
            prepare = False
            rc = _run_one(leg, leg.command, fh, extra_env, governor, log_dir, hand_off=leg.checkout_handoff)
    except LegCleanupFailed as exc:
        # A prepare that exited 0 is not this leg's exit: its command never ran.
        if prepare and exc.returncode == 0:
            raise RuntimeError(str(exc)) from exc
        exc.prepare, exc.seconds, exc.log = prepare and exc.returncode != 0, time.monotonic() - t0, str(log)
        raise
    except GateCancelled as exc:
        # A cancellation after the leg's own exit was observed carries that
        # exit (_run_one); _cmd_run records it before it stops.
        if exc.observed_returncode is not None:
            if prepare and exc.observed_returncode == 0:
                exc.observed_returncode = None
            exc.prepare, exc.seconds, exc.log = prepare, time.monotonic() - t0, str(log)
        raise
    return rc, time.monotonic() - t0, str(log), False


class GateCancelled(BaseException):
    """A cancellation is never a leg verdict, even if its child exits zero."""

    def __init__(self, signum: int):
        self.signum = signum
        # Set by _run_one when the leg's own exit was observed before the
        # cancellation took effect (review of EW-1): run_leg adds prepare,
        # seconds and log, and _cmd_run records that exit.
        self.observed_returncode: Optional[int] = None
        self.prepare = False
        self.seconds = 0.0
        self.log = ""
        super().__init__(f"cancelled by signal {signum}")


class _Cancellation:
    def __init__(self):
        self.first: Optional[int] = None
        self.count = 0

    def record(self, signum, _frame):
        # Never raise here: a signal can arrive inside Popen, before its
        # returned child can be registered, or during wait/reap bookkeeping.
        if self.first is None:
            self.first = signum
        self.count += 1

    def check(self):
        if self.first is not None:
            raise GateCancelled(self.first)


_ACTIVE_CANCELLATION: Optional[_Cancellation] = None
_CANCEL_SIGNALS = (signal.SIGINT, signal.SIGTERM, signal.SIGHUP)


@contextlib.contextmanager
def _cancellation_scope():
    global _ACTIVE_CANCELLATION
    if _ACTIVE_CANCELLATION is not None:
        yield _ACTIVE_CANCELLATION
        return
    state = _Cancellation()
    previous = {}
    if set(signal.pthread_sigmask(signal.SIG_BLOCK, [])) & set(_CANCEL_SIGNALS):
        raise RuntimeError('landing cancellation signals must be unblocked before spawning')
    try:
        for sig in _CANCEL_SIGNALS:
            previous[sig] = signal.signal(sig, state.record)
        _ACTIVE_CANCELLATION = state
        yield state
    finally:
        # No children remain here. Restore every handler before a pending
        # original raising handler could interrupt the restoration loop.
        old_mask = signal.pthread_sigmask(signal.SIG_BLOCK, _CANCEL_SIGNALS)
        try:
            for sig, handler in previous.items():
                signal.signal(sig, handler)
            for sig in _CANCEL_SIGNALS:
                if sig in signal.sigpending():
                    state.record(signal.sigwait({sig}), None)
        finally:
            _ACTIVE_CANCELLATION = None
            signal.pthread_sigmask(signal.SIG_SETMASK, old_mask)


def _check_cancellation():
    if _ACTIVE_CANCELLATION is not None:
        _ACTIVE_CANCELLATION.check()


CENSUS_TIMEOUTS_S = (1, 5, 10)
# After the leader's exit is observed, how long its output may still be in
# flight: kqueue's NOTE_EXIT can precede the kernel's close of the exiting
# child's descriptors. A pipe still open past this is held by a descendant.
EXIT_DRAIN_GRACE_S = 2.0


class LegCleanupFailed(RuntimeError):
    """The leg's child exited and was reaped with `returncode`; only the
    cleanup after it failed. The exit is a verdict the gate records before it
    refuses (review of EW-21)."""

    def __init__(self, message: str, returncode: int, cause: str = "its cleanup failed after the exit"):
        super().__init__(message)
        self.returncode = returncode
        self.cause = cause
        self.prepare = False
        self.seconds = 0.0
        self.log = ""


class LegOutputRetained(RuntimeError):
    """Raised by _stream_leg only after the leader's own exit was observed: a
    descendant still held the output pipe past EXIT_DRAIN_GRACE_S. The exit is
    the leg's verdict, recorded before the gate refuses (review of EW-1)."""


class _OwnedGroup:
    """A new-session child stays unreaped until its last group signal.

    Nonreaping exit observation (waitid or Darwin kqueue) pins the leader
    PID, so its process-group identity cannot be recycled during cleanup.
    Deliberately escaped sessions are outside this containment boundary;
    no host-wide command/name matching is used.
    """

    def __init__(self, process):
        self.process = process
        self.reaped = False
        # True once _stream_leg saw the leader exit by itself: the gate signals
        # the group only in retire, after streaming (review of EW-1).
        self.exit_observed = False

    def exited(self):
        return landing_targo.wait_child_exit(self.process.pid, nohang=True)

    def send(self, sig):
        if self.reaped or self.process.returncode is not None:
            raise RuntimeError("refusing a group signal after leader reap")
        terminal = self.exited()  # Confirm our unreaped direct-child identity.
        if not terminal:
            try:
                if os.getpgid(self.process.pid) != self.process.pid:
                    raise RuntimeError('owned child lost its new-session group identity')
            except ProcessLookupError:
                # The live leader may have exited between these observations.
                if not self.exited():
                    raise RuntimeError('owned live leader group cannot be identified')
                terminal = True
        try:
            os.killpg(self.process.pid, sig)
        except ProcessLookupError:
            pass
        except PermissionError:
            # Darwin can return EPERM for a terminal group's zombies. This
            # is acceptable only with the waitable leader pin and no live
            # members; final post-reap absence is still mandatory.
            if not terminal or any('Z' not in status for _pid, status in self.members()):
                raise

    def members(self):
        # A census that times out on a loaded host is asked again, longer,
        # before it fails a cleanup (review of EW-21: at load 50-100 one ps
        # in 70 gates took over a second, and the leg's verdict was lost).
        for timeout in CENSUS_TIMEOUTS_S:
            try:
                observed = subprocess.run(['/bin/ps', '-axo', 'pid=,pgid=,stat='],
                                          capture_output=True, text=True, timeout=timeout)
                break
            except subprocess.TimeoutExpired:
                if timeout == CENSUS_TIMEOUTS_S[-1]:
                    raise
        if observed.returncode not in (0, 1):
            raise RuntimeError("cannot inspect owned process group")
        members = []
        for line in observed.stdout.splitlines():
            pid, pgid, status = line.split()
            if int(pgid) == self.process.pid:
                members.append((int(pid), status))
        return members

    def wait_quiet(self, seconds, cancellation):
        deadline = time.monotonic() + seconds
        while True:
            if not any('Z' not in status for _pid, status in self.members()):
                return True
            if time.monotonic() >= deadline or cancellation.count > 1:
                return False
            time.sleep(.02)

    def retire(self, cancellation, stop_signal=None, before_reap=None):
        errors = []
        abnormal_leftovers = False
        try:
            leftovers = [(pid, status) for pid, status in self.members()
                         if pid != self.process.pid and 'Z' not in status]
            abnormal_leftovers = stop_signal is None and bool(leftovers)
        except BaseException as error:
            errors.append(error)
        # Observation failures must not bypass termination/reap. All group
        # signals happen while our unreaped direct-child identity is pinned.
        if stop_signal is not None or abnormal_leftovers or errors:
            for sig, seconds in ((stop_signal or signal.SIGTERM, 1), (signal.SIGTERM, 1)):
                try:
                    self.send(signal.SIGCONT)
                    self.send(sig)
                    if self.wait_quiet(seconds, cancellation):
                        break
                except BaseException as error:
                    errors.append(error)
        try:
            self.send(signal.SIGKILL)
        except BaseException as error:
            errors.append(error)
        # Observe termination without releasing the group pin.
        deadline = time.monotonic() + 2
        while not self.exited():
            if time.monotonic() >= deadline:
                raise RuntimeError('owned leader did not stop within cleanup deadline')
            time.sleep(.02)
        try:
            if not self.wait_quiet(2, cancellation):
                errors.append(RuntimeError('owned group did not become quiet'))
        except BaseException as error:
            errors.append(error)
        if before_reap is not None:
            before_reap()
        self.process.wait(timeout=1)
        self.reaped = True
        # Readonly absence checking is safe after reap; never signal again.
        deadline = time.monotonic() + 2
        try:
            while self.members():
                if time.monotonic() >= deadline:
                    raise RuntimeError('owned group not confirmed drained after reap')
                time.sleep(.02)
        except BaseException as error:
            errors.append(error)
        if abnormal_leftovers:
            errors.append(RuntimeError('leg exited with running process-group descendants'))
        if errors:
            raise RuntimeError(f'owned child cleanup errors: {errors!r}')


class _CancellableEcho:
    """Keep pipe/terminal backpressure from blocking cancellation cleanup."""

    def __init__(self, stream, cancellation):
        self.stream = stream
        self.cancellation = cancellation
        self.fd = None
        self.was_blocking = None
        try:
            self.fd = stream.fileno()
        except (AttributeError, io.UnsupportedOperation):
            return  # StringIO and other in-memory test streams.
        self.was_blocking = os.get_blocking(self.fd)
        os.set_blocking(self.fd, False)

    def ready(self):
        self.cancellation.check()
        select.select([], [self.fd], [], .1)

    def write(self, text):
        self.cancellation.check()
        if self.fd is None:
            self.stream.write(text)
            self.stream.flush()
            return
        # Flush pre-leg Python output before bypassing its text buffer.
        while True:
            self.cancellation.check()
            try:
                self.stream.flush()
                break
            except BlockingIOError:
                self.ready()
        data = memoryview(text.encode(self.stream.encoding or 'utf-8',
                                      self.stream.errors or 'strict'))
        while data:
            self.cancellation.check()
            try:
                count = os.write(self.fd, data)
                if count == 0:
                    raise OSError('stdout write made no progress')
                data = data[count:]
            except BlockingIOError:
                self.ready()

    def restore(self):
        if self.fd is not None and self.was_blocking is not None:
            os.set_blocking(self.fd, self.was_blocking)


class _EchoStream:
    def __init__(self, echo):
        self.echo = echo

    def write(self, text):
        self.echo.write(text)
        return len(text)

    def flush(self):
        self.echo.write('')

    def __getattr__(self, name):
        return getattr(self.echo.stream, name)


@contextlib.contextmanager
def _cancellable_stdout(cancellation):
    original = sys.stdout
    echo = _CancellableEcho(original, cancellation)
    try:
        # All real cmd_run output, including print_plan/RUN and verdicts,
        # goes directly through this writer before it can fill a text buffer.
        sys.stdout = _EchoStream(echo)
        yield
    finally:
        sys.stdout = original
        echo.restore()


def _stream_leg(owned, leg, fh, cancellation, echo):
    process = owned.process
    assert process.stdout is not None
    fd = process.stdout.fileno()
    os.set_blocking(fd, False)
    decoder = io.IncrementalNewlineDecoder(
        codecs.getincrementaldecoder(process.stdout.encoding)(errors='replace'), translate=True)
    pending = ''
    eof = False

    def relay(data, final=False):
        nonlocal pending
        pending += decoder.decode(data, final=final)
        while '\n' in pending:
            cancellation.check()
            line, pending = pending.split('\n', 1)
            line += '\n'
            fh.write(line)
            echo.write(f"  [{leg.id}] {line}")
        if final and pending:
            fh.write(pending)
            echo.write(f"  [{leg.id}] {pending}")
            pending = ''

    def drain(selector):
        nonlocal eof
        while not eof:
            cancellation.check()
            try:
                data = os.read(fd, 65536)
            except BlockingIOError:
                break
            if not data:
                eof = True
                selector.unregister(fd)
                relay(b'', final=True)
            else:
                relay(data)

    with selectors.DefaultSelector() as selector:
        selector.register(fd, selectors.EVENT_READ)
        while True:
            cancellation.check()
            if selector.select(.1):
                drain(selector)
            if owned.exited():
                # A verdict only when no cancellation came first: a leader the
                # same tree signal killed is the cancellation's, not its own
                # (review of EW-1).
                owned.exit_observed = cancellation.first is None
                deadline = time.monotonic() + EXIT_DRAIN_GRACE_S
                while not eof:
                    drain(selector)
                    if eof or time.monotonic() >= deadline:
                        break
                    cancellation.check()
                    selector.select(.05)
                if not eof:
                    raise LegOutputRetained("leg exited while descendants retained its output pipe")
                return


def _run_one(leg: Leg, command: List[str], fh, extra_env: Dict[str, str], governor: Tuple[int, int],
             log_dir: Path, hand_off: bool = False) -> int:
    # Fail before spawning if the OS cannot retain a waitable identity pin.
    if not landing_targo.exit_observation_available():
        raise RuntimeError("landing child cleanup requires nonreaping exit observation")
    if signal.getsignal(signal.SIGCHLD) != signal.SIG_DFL:
        raise RuntimeError('landing child cleanup requires sole direct-child wait ownership')
    if leg.sealed_programs:
        # LEG-READS-1: the leg's process gets exactly the environment the gate
        # builds, and its stdin is /dev/null. The gate starts nothing beside
        # it: no memory governor (it pauses compiler and linker hogs, and a
        # sealed leg runs none), so no process that inherits the gate's
        # environment can act on the leg or its directories while it runs.
        if extra_env:
            raise RuntimeError(f"{leg.id}: a sealed leg takes no environment from the gate")
        unrunnable = sealed_unrunnable(leg)
        if unrunnable:
            return _sealed_not_judged(fh, f"the leg cannot run sealed: {unrunnable}")
        try:
            # sealed_launch raises ReadUnobservable before the leg starts;
            # neither _run_process nor moved() raises it.
            with sealed_launch(leg, command) as (sealed_command, sealed_env, moved):
                rc = _run_process(leg, sealed_command, fh, sealed_env, None, governor, log_dir,
                                  stdin=subprocess.DEVNULL)
                changed = moved()
        except ReadUnobservable as exc:
            return _sealed_not_judged(fh, f"the leg cannot run sealed: {exc}")
        if changed and rc == 0:
            return _sealed_not_judged(fh, changed)
        return rc
    env = dict(leg_environment(leg), **extra_env)
    pycache = fresh_pycache(log_dir, leg.id)
    env[PYCACHE_ENV] = str(pycache)
    try:
        return _run_unsealed(leg, command, fh, env, governor, log_dir, hand_off)
    finally:
        # Its process tree has exited (_run_process reaps the group): what it
        # compiled serves nothing after, and a run directory is never reused.
        shutil.rmtree(pycache, ignore_errors=True)


def _run_unsealed(leg: Leg, command: List[str], fh, env: Dict[str, str], governor: Tuple[int, int],
                  log_dir: Path, hand_off: bool) -> int:
    command = development_native_command(leg, command, fh, env)
    if leg.id == "development-recipes":
        case_directory = log_dir / "development-recipes.cases"
        case_directory.mkdir()  # fresh actual invocation data; never reuse old output
        env["TRUST_UPSTREAM_RUST_PROOF_DIR"] = str(case_directory)
    if not hand_off:
        # Every other leg and its governor share one environment.
        return _run_process(leg, command, fh, env, env, governor, log_dir)
    # Every descriptor the environment advertises is checked live before the
    # pipe exists, as _CheckoutWorkers.start checks before its pipes: a closed
    # advertised number would otherwise be the pipe's, and the leg would be
    # handed the token as that resource. RuntimeError, as for any other leg;
    # once all are live, the pipe cannot take one of their numbers.
    row_resource_fds(env)
    handed, digest = checkout_handoff_pipe()
    try:
        line = f"run: {leg.id} is handed this run's checkout binding (token {digest}) on descriptor {handed}\n"
        fh.write(line)
        sys.stdout.write(line)
        rc = _run_process(leg, [*command, CHECKOUT_BOUND_FLAG, str(handed)], fh, env, env, governor, log_dir,
                          keep_fds=(handed,))
    finally:
        os.close(handed)
    if rc == SEALED_NOT_JUDGED_EXIT:
        return rc
    # The leg judged rows on run's binding only if it read run's own pipe: it
    # names that token's digest (cmd_push_rows) before any row starts.
    fh.flush()
    said = Path(fh.name).read_text(encoding="utf-8", errors="replace")
    if not re.search(rf"^{re.escape(CHECKOUT_BOUND_REPORT)}{digest}:", said, re.M):
        return _sealed_not_judged(fh, f"{leg.id} never reported reading this run's checkout binding (token "
                                      f"{digest}), so its exit {rc} is bound to no pass of this run")
    return rc


# A sealed leg that did not run sealed, or whose run cannot be trusted, says
# NOT JUDGED with the exit every leg but crates-tests uses for it.
SEALED_NOT_JUDGED_EXIT = 2


def _sealed_not_judged(fh, why: str) -> int:
    line = f"NOT JUDGED: {why}\n"
    fh.write(line)
    sys.stdout.write(line)
    return SEALED_NOT_JUDGED_EXIT


def _run_process(leg: Leg, command: List[str], fh, env: Dict[str, str], gov_env: Optional[Dict[str, str]],
                 governor: Tuple[int, int], log_dir: Path, stdin=None, keep_fds: Tuple[int, ...] = ()) -> int:
    """Run `command` as the leg, beside the memory governor in `gov_env`, or
    alone when `gov_env` is None. `keep_fds` reach the leg's process (never
    the governor) under their own numbers."""
    passing = tuple(sorted(set(row_resource_fds(env)) | set(keep_fds)))
    if gov_env is not None:
        gov_env['TRUST_GOV_CRITICAL_GIB'], gov_env['TRUST_GOV_RESUME_GIB'] = str(governor[0]), str(governor[1])
        gov_env['TRUST_GOV_LOG'] = str(log_dir / f'{leg.id}.governor.log')
    process = gov = echo = child = None
    failure = None
    cleanup_errors = []
    with _cancellation_scope() as cancellation:
        try:
            cancellation.check()
            echo = _CancellableEcho(sys.stdout, cancellation)
            fh.write(f"$ {' '.join(command)}\n")
            fh.flush()
            process = subprocess.Popen(command, cwd=REPO_ROOT, env=env, stdin=stdin, stdout=subprocess.PIPE,
                                       stderr=subprocess.STDOUT, text=True, errors='replace',
                                       start_new_session=True, pass_fds=passing)
            # The record-only handlers make this registration interval safe.
            child = _OwnedGroup(process)
            cancellation.check()
            gov_script = REPO_ROOT / 'scripts' / 'build-mem-governor.sh'
            if gov_env is not None and gov_script.exists():
                gov = subprocess.Popen(['bash', str(gov_script), str(process.pid)], cwd=REPO_ROOT,
                                       env=gov_env, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL,
                                       start_new_session=True)
            cancellation.check()
            _stream_leg(child, leg, fh, cancellation, echo)
        except BaseException as error:
            failure = error
        finally:
            # Governor first: its TERM trap resumes anything it paused. Keep
            # the leg leader pinned until this governor can no longer use it.
            for index, direct in ((1, gov), (0, process)):
                if direct is None:
                    continue
                group = _OwnedGroup(direct)
                try:
                    stop = signal.SIGTERM if index else (
                        cancellation.first or (signal.SIGTERM if failure else None))
                    def governor_terminal_before_leg_reap():
                        if gov is not None and gov.returncode is None and not _OwnedGroup(gov).exited():
                            raise RuntimeError('cannot release leg identity while governor may still act')
                    group.retire(cancellation, stop,
                                 governor_terminal_before_leg_reap if index == 0 else None)
                except BaseException as error:
                    cleanup_errors.append(error)
                finally:
                    try:
                        if group.process.stdout is not None:
                            group.process.stdout.close()
                    except BaseException as error:
                        cleanup_errors.append(error)
            if echo is not None:
                try:
                    echo.restore()
                except BaseException as error:
                    cleanup_errors.append(error)
        # The leader's own exit, observed while streaming and reaped since: a
        # verdict the gate records whatever stops it now (review of EW-1).
        observed = (child is not None and child.exit_observed and process is not None
                    and process.returncode is not None)
        if cancellation.first is not None:
            error = GateCancelled(cancellation.first)
            if observed:
                error.observed_returncode = process.returncode
            for cleanup_error in cleanup_errors:
                error.add_note(f'cleanup: {cleanup_error!r}')
            raise error from failure
        if observed and (cleanup_errors or isinstance(failure, Exception)):
            # Whatever failed after the observed exit (a pipe a descendant
            # kept, an echo whose reader went away, a cleanup) stops the gate
            # but not the exit's record (review of EW-1).
            cause = ("a descendant retained its output pipe after the exit"
                     if isinstance(failure, LegOutputRetained) else
                     f"{type(failure).__name__} after the exit" if failure is not None else
                     "its cleanup failed after the exit")
            message = (f'landing child cleanup failed: {cleanup_errors!r}' if cleanup_errors else str(failure))
            raise LegCleanupFailed(message, process.returncode, cause) from failure
        if cleanup_errors:
            message = f'landing child cleanup failed: {cleanup_errors!r}'
            if failure is None and process is not None and process.returncode is not None:
                raise LegCleanupFailed(message, process.returncode) from failure
            raise RuntimeError(message) from failure
        if failure is not None:
            raise failure
    # A signal that came after the check above (while the scope closed) is
    # still a cancellation after an observed exit (review of EW-1).
    if cancellation.first is not None:
        error = GateCancelled(cancellation.first)
        if observed:
            error.observed_returncode = process.returncode
        raise error
    return process.returncode


# The stage-1 suites are judged against a checked-in known-red SET, the way
# scripts/check_trust_verify_suite_ratchet.sh judges a compiler crate's unit
# suite: main's tests/ui/trust is not green (docs/KNOWN_HAZARDS.md names its
# reds), so a whole-suite run, which any scripts/ change forces, could never
# pass on an absolute rule and would tell a landing nothing about itself. A
# failure NOT in the set fails the leg; a row whose test ran and passed fails it
# too (a stale row would silently re-accept a re-break); a run whose failures
# cannot be attributed, or that reached no result, is NOT JUDGED.
SUITE_BASELINES = {"ui-trust": "tests/known-red/ui-trust.txt",
                   "run-make-trust": "tests/known-red/run-make-trust.txt"}
ANSI = re.compile(r"\x1b\[[0-9;]*[A-Za-z]")
RESULT = re.compile(r"^test result: .*?(\d+) failed;")
SUITE_START = re.compile(r"^Testing stage\d+ with compiletest suite=\S+ mode=\S+ \([^)]+\)$")


def baseline_rows(text: str) -> List[str]:
    """Rows of a known-red file: comment- and blank-stripped, one test name per
    line exactly as compiletest's failures list spells it (`[ui] tests/ui/trust/x.rs#rev`)."""
    out = []
    for line in text.splitlines():
        if line.lstrip().startswith("#"):
            continue  # a comment line; a row's own comment follows two spaces and a `#`
        row = line.split("  #", 1)[0].strip()
        if row:
            out.append(row)
    return sorted(set(out))


def judge_suite(log_text: str, xpy_rc: int, accepted: Sequence[str],
                targets: Optional[Sequence[str]]) -> Tuple[int, str]:
    """(0 pass | 1 fail | 2 not judged, why) for an x.py compiletest run.
    Every `test result:` line (one per target the configuration tests: an Apple
    host tests both architectures) must be accounted for by the failures list
    printed just before it; the observed set is their union. An interruption
    or a started target without a result cannot reuse an earlier target's red
    set as a complete verdict."""
    if xpy_rc not in (0, 1):
        return 2, f"x.py did not complete normally (exit {xpy_rc}); earlier results are incomplete evidence"
    lines = ANSI.sub("", log_text).splitlines()
    observed: set = set()
    pending: List[str] = []
    results = 0
    started = 0
    i = 0
    while i < len(lines):
        line = lines[i]
        if SUITE_START.match(line):
            started += 1
        if line == "failures:":
            names = []
            j = i + 1
            while j < len(lines) and lines[j].startswith("    ") and not lines[j].startswith("     "):
                names.append(lines[j].strip())
                j += 1
            if names:
                pending = names
            i = j
            continue
        m = RESULT.match(line)
        if m:
            results += 1
            failed = int(m.group(1))
            if failed != len(set(pending)):
                return 2, (f"a result line reports {failed} failed but the failures list before it names "
                           f"{len(set(pending))}: the red set cannot be attributed")
            observed.update(pending)
            pending = []
        i += 1
    if results == 0:
        return 2, f"the suite reached no test result (x.py exit {xpy_rc})"
    if started and started != results:
        return 2, f"{started} target suite(s) started but {results} result(s) completed; the suite is incomplete"
    if xpy_rc != 0 and not observed:
        return 2, f"x.py exited {xpy_rc} with no failing test: something other than a test failed"
    acc = set(accepted)
    new = sorted(observed - acc)

    def ran(row: str) -> bool:
        if targets is None:
            return True
        path = row.split("] ", 1)[-1].split("#", 1)[0]
        return any(path == t or path.startswith(t.rstrip("/") + "/") for t in targets)
    stale = sorted(r for r in acc - observed if ran(r))
    if new or stale:
        why = []
        if new:
            why.append("NEW failures not in the known-red set: " + ", ".join(new))
        if stale:
            why.append("known-red rows whose tests now PASS (delete them): " + ", ".join(stale))
        return 1, "; ".join(why)
    return 0, f"failing set within the known-red set ({len(observed)} accepted red)"


def skipped_token(log_path: str) -> bool:
    try:
        text = Path(log_path).read_text(encoding="utf-8", errors="replace")
    except OSError:
        return False
    return bool(re.search(r"^\s*(?:\[[^\]]+\]\s*)?SKIPPED: ", text, re.M))


METADATA_WORKSPACES = ("Cargo.toml", "library/Cargo.toml",
                       "src/tools/targo/Cargo.toml")
# A complete lockfile does not make `targo metadata --offline` work (EW-2).
# Resolving still reads every locked package's summary from the local index
# cache, and the output serializes every package, so it reads every manifest
# from the local registry: those of every platform's dependencies, where a build
# downloads only what its own host reaches. On a host that has only built, the
# wasm and Windows dependencies are absent, so the graph check failed and every
# leg ran. An online `targo metadata --locked` fills exactly what the offline one
# reads. It cannot move the lock, and registry downloads are held to the lock's
# checksums. `targo fetch` would too, but atpkg's shim refuses it in this tree.
METADATA_FILL_TIMEOUT_S = 120
# The offline call reads only local files, but every resolve first takes
# Cargo's lock on $CARGO_HOME/.package-cache and waits for it with no bound
# ("Blocking waiting for file lock", on stderr, which is captured): a Cargo
# stopped or stalled while holding it would hang a gate or a hook install
# (review of EW-2). Past this bound the workspace cannot answer.
METADATA_OFFLINE_TIMEOUT_S = 60
_REGISTRY_GAP = re.compile(r"but --offline was specified")
# Cargo says this only from a git source's checkout. Every git dependency of
# this tree's gated workspaces is a [patch] to a first-party path, so one
# reached offline is a patch that escaped (a first-party worktree off its
# gitlink, or a manifest the lock does not match), which no fetch repairs:
# fetching it would only ask a private remote (review of EW-2).
_GIT_CHECKOUT_OFFLINE = "you are in the offline mode"
# Cargo's offline spelling for a git source whose database is on this host but
# lacks the revision a manifest pins (review of EW-1).
_GIT_REV_OFFLINE = "failed to lookup reference in preexisting repository"


def escaped_git_source(stderr: str) -> bool:
    """Did offline metadata reach a git source (a [patch] that escaped)?"""
    return _GIT_CHECKOUT_OFFLINE in stderr or _GIT_REV_OFFLINE in stderr


FIRST_PARTY_STATUS_TIMEOUT_S = 60


def first_party_drift() -> Tuple[List[str], List[str]]:
    """(drifted, unknown): the first-party worktrees that are not the committed
    input (a checkout off the commit HEAD's gitlink names, a staged gitlink, or
    tracked edits), and why that could not be read. Inputs Cargo read that are
    not the committed ones. One bounded `git status --porcelain=v2` of
    first-party/, asked as a plain shell would (git_query_env: an exported
    GIT_DIR cannot answer for it). An unpopulated gitlink is no drift. `run`
    refuses these through checkout_problem before it reads the graph;
    `prefetch` and `needs` meet them here (review of EW-1)."""
    try:
        proc = subprocess.run(["git", "-C", str(REPO_ROOT), "status", "--porcelain=v2",
                               "--ignore-submodules=untracked", "--untracked-files=no", "--", "first-party/"],
                              capture_output=True, text=True,
                              env=git_query_env(), timeout=FIRST_PARTY_STATUS_TIMEOUT_S)
    except (OSError, subprocess.TimeoutExpired) as exc:
        return [], [f"first-party/ (git status: {exc})"]
    if proc.returncode != 0:
        return [], [f"first-party/ (git status exit {proc.returncode}: {cargo_error(proc.stderr or '')})"]
    drifted: List[str] = []
    for line in (proc.stdout or "").splitlines():
        fields = line.split(" ")
        if fields[0] not in ("1", "2") or len(fields) < 9 or not fields[2].startswith("S"):
            continue
        path = " ".join(fields[8:] if fields[0] == "1" else fields[9:]).split("\t", 1)[0]
        # A staged gitlink (the index is not HEAD), another commit checked
        # out, or tracked edits; untracked files are no committed input.
        if fields[1][0] != "." or fields[2][1] == "C" or fields[2][2] == "M":
            drifted.append(path)
    return drifted, []


def _once(scan):
    """`scan`, asked at most once: one verify_graph or prefetch call reads
    the first-party worktrees once, so its wording and its refusal agree."""
    memo: List[Tuple[List[str], List[str]]] = []

    def ask() -> Tuple[List[str], List[str]]:
        if not memo:
            memo.append(scan())
        return memo[0]
    return ask


def offline_failure(proc: Optional[subprocess.CompletedProcess], hung: Optional[str], no_network: Optional[str],
                    asked: bool = True, drift=None, ws: Optional[str] = None) -> Tuple[str, str, List[str]]:
    """(kind, what it is and what a gate here does, the drifted worktrees) for
    a workspace whose offline `targo metadata` did not answer: the one wording
    verify_graph and prefetch share (review of EW-1). Kinds: `timeout`,
    `drift`, `stale_lock` and `old_targo` (all refuse before any leg),
    `escaped`, `gap`, `other`. Any failure first asks `drift`
    (first_party_drift, once per call): a worktree that is not the committed
    input explains whatever Cargo said, and `run` refuses it whatever the
    cause; a lock refusal beside drift cannot
    be judged until the worktrees are the committed inputs. A worktree whose
    state cannot be read is named, and the failure keeps its own kind."""
    if proc is None:
        return "timeout", f"{hung}; a gate here selects every leg without asking the network", []
    err = cargo_error(proc.stderr)
    drifted, unknown = (drift or first_party_drift)()
    if drifted:
        return "drift", (f"{err} (first-party worktree(s) off their gitlink or with uncommitted edits: "
                         f"{', '.join(drifted)}: Cargo read inputs that are not the committed ones; "
                         "scripts/submodule_sync.sh; a gate here refuses before any leg)"), drifted
    kind, said = _offline_cause(proc, err, no_network, asked, ws)
    if unknown:
        said += f" (first-party drift could not be checked: {'; '.join(unknown)})"
    return kind, said, []


def _offline_cause(proc: subprocess.CompletedProcess, err: str, no_network: Optional[str],
                   asked: bool, ws: Optional[str] = None) -> Tuple[str, str]:
    locked, escaped = locked_metadata_refusal(proc.stderr), escaped_git_source(proc.stderr)
    older = path_targo_predates_unused_patch_sort(ws) if locked and ws else None
    if older:
        return "old_targo", f"{older}: a gate here refuses before any leg: {err}"
    if locked:
        return "stale_lock", (f"the committed lock needs repair (`targo metadata --locked` refuses it): a gate here "
                              f"refuses before any leg: {err}")
    if escaped:
        return "escaped", (f"{err} (a git source reached offline: no [patch] captures it. Either a first-party "
                           "worktree is off its gitlink (scripts/submodule_sync.sh), or the committed manifests "
                           "and lock name a git source no [patch] covers, which tidy's extdeps refuses: fix the "
                           "[patch] or the sibling's version and regenerate the lock. A gate here selects every "
                           "leg; no fetch repairs this)")
    if registry_gap(proc.stderr):
        network = (f"did not fill it: {no_network}" if no_network
                   else "was asked and it still fails" if asked else "was not asked (--check)")
        return "gap", (f"{err} (offline it needs what the local registry lacks; the network {network}; "
                       "`python3 scripts/land_gate.py prefetch` where the registry is reachable. A gate here asks "
                       "the network once, and without an answer selects every leg)")
    return "other", f"{err} (a gate here selects every leg; no fetch repairs this)"
# Cargo adds this note to every resolver failure, whatever source it searched:
# a gap only when a searched location is a registry, never a path source.
_OFFLINE_NOTE = "offline mode (via `--offline`)"


# The variables that name `resolver.lockfile-path`, the lock Cargo reads: its
# Cargo spelling, and the TARGO_ twin targo reads as it when the Cargo one is
# unset (src/tools/targo/crates/targo-core/src/context/environment.rs).
METADATA_ENV_DROP = ("CARGO_RESOLVER_LOCKFILE_PATH", "TARGO_RESOLVER_LOCKFILE_PATH")
# And every variable targo reads as an `[unstable]` key, in either spelling:
# `avoid-dev-deps` turns the `--locked` comparison off (targo-core's
# `command_prelude.rs` clears `require_optional_deps`, and `ops/resolve.rs`
# then neither writes nor compares the lock).
METADATA_ENV_DROP_PREFIXES = ("CARGO_UNSTABLE_", "TARGO_UNSTABLE_")


def metadata_env(env: Optional[Dict[str, str]] = None) -> Dict[str, str]:
    """The environment for a lock-judging metadata call: the caller's, without
    METADATA_ENV_DROP or any variable that starts with one of
    METADATA_ENV_DROP_PREFIXES, so the lock beside the manifest is the one
    judged, and it is judged. Measured on a scratch workspace whose lock
    lacked an edge (rc 101): it passed (rc 0) with either lockfile variable
    naming a current lock elsewhere (CARGO_ 2026-11-06, TARGO_ 2026-11-10),
    and with either spelling of `UNSTABLE_AVOID_DEV_DEPS=true` (2026-11-10).
    A config file can do either too; `lock_redirect` refuses that call
    instead."""
    source = os.environ if env is None else env
    return {var: value for var, value in source.items()
            if var not in METADATA_ENV_DROP and not var.startswith(METADATA_ENV_DROP_PREFIXES)}


# The names targo reads in each `.cargo` directory (`get_file_path`: one of
# them, `config` when both stand; both are read here).
LOCK_CONFIG_NAMES = ("config.toml", "config")


def textual_path(path: Path) -> Path:
    """`path` with `.` and `..` removed by text, as targo's
    `paths::normalize_path` does: it does not follow a link before `..`."""
    return Path(os.path.normpath(path))


def lock_config_files(cwd: Path, env: Optional[Dict[str, str]] = None,
                      home: Optional[Path] = None) -> List[Tuple[Path, bool]]:
    """(path, outside the tree) for each config file targo may read from
    `cwd`: `.cargo/` in `cwd` and every directory above it (targo-core's
    `context/mod.rs`, `walk_tree`), then its home's (`homedir`). The home is
    `$CARGO_HOME` (or, by main's targo, `$TARGO_HOME`) joined to `cwd`, or
    `~/.cargo`, the account's home coming from `$HOME` unless it is empty
    (the `home` crate); each by text. Every home it may choose is listed.
    Only `cwd/.cargo/config.toml` is inside: callers pass REPO_ROOT, where
    it is the committed file. KeyError when `$HOME` is empty and the
    account has no entry."""
    env = os.environ if env is None else env
    if home is None:
        home = Path(env.get("HOME") or pwd.getpwuid(os.getuid()).pw_dir)
    homes = [textual_path(cwd / env[var]) for var in ("CARGO_HOME", "TARGO_HOME") if env.get(var)]
    homes.append(textual_path(home / ".cargo"))
    committed = cwd / ".cargo" / "config.toml"
    return [(directory / name, directory / name != committed)
            for directory in [base / ".cargo" for base in (cwd, *cwd.parents)] + homes
            for name in LOCK_CONFIG_NAMES]


def lock_config_reason(path: Path, outside: bool) -> Optional[str]:
    """Why the config file at `path` may make a lock-judging call judge
    another lock, not compare it, or answer from other inputs than a clean
    host has: it sets `resolver.lockfile-path` or an `include` (which can
    set it), or an `[unstable]` table (whose `avoid-dev-deps` turns the
    comparison off); or, outside the tree, a `[patch]` (which the
    comparison resolves against) or `paths` (which replaces packages in the
    graph the gate reads after the comparison: it lets no stale lock pass);
    or it cannot be read or parsed. None when nothing stands there, as when
    a `.cargo` above is a file (targo then reads nothing there either), or
    it sets none of these."""
    try:
        text = path.read_text(encoding="utf-8")
    except (FileNotFoundError, NotADirectoryError):
        return None
    except (OSError, UnicodeDecodeError) as exc:
        return f"{path} cannot be read ({exc}), so the lock it may name is unknown"
    try:
        config = tomllib.loads(text)
    except tomllib.TOMLDecodeError as exc:
        return f"{path} does not parse as TOML 1.0 ({exc}), so the lock it may name is unknown"
    resolver = config.get("resolver")
    if "include" in config or (isinstance(resolver, dict) and "lockfile-path" in resolver):
        return (f"{path} sets resolver.lockfile-path or an include, so Cargo may judge "
                "another lock than the committed one")
    if resolver is not None and not isinstance(resolver, dict):
        return f"{path} sets resolver to a {type(resolver).__name__}, not a table, so the lock it names is unknown"
    if "unstable" in config:
        return (f"{path} sets an [unstable] table, whose avoid-dev-deps turns the --locked "
                "comparison off")
    if outside and "patch" in config:
        return (f"{path} sets [patch], so this host resolves the committed lock against other "
                "sources than a clean host does")
    if outside and "paths" in config:
        return (f"{path} sets paths, so the graph this host reports replaces packages a clean "
                "host's does not")
    return None


def lock_redirect(cwd: Path, env: Optional[Dict[str, str]] = None,
                  home: Optional[Path] = None) -> Optional[str]:
    """Why a metadata call run in `cwd` may not judge the committed lock as a
    clean host does (`lock_config_reason` of any file `lock_config_files`
    lists), or None. Measured 2026-11-10: a `.cargo/config.toml` above the
    working directory, a file one includes, and `$CARGO_HOME/config.toml`
    each let a current lock elsewhere pass for a stale one, and an
    `[unstable] avoid-dev-deps` there let a stale lock pass. A
    `cwd/.cargo/config` is refused whatever it sets: targo reads it in place
    of the committed `config.toml`. atpkg's targo shim refuses some such
    calls itself (exit 75, aterm 335cd34820a,
    `lockfile_may_land_in_a_target`), but by the configs above the
    manifest, not the working directory, so neither rule contains the
    other; this one holds for every targo. The caller then has no answer."""
    shadow = cwd / ".cargo" / "config"
    if shadow.is_symlink() or shadow.exists():
        return (f"{shadow} stands beside the committed config.toml, and targo reads it instead, "
                "so the lock it names is unknown")
    try:
        files = lock_config_files(cwd, env, home)
    except KeyError:
        return (f"$HOME is empty and uid {os.getuid()} has no account entry, so the home whose "
                "config targo reads is unknown")
    for path, outside in files:
        why = lock_config_reason(path, outside)
        if why:
            return why
    return None


def metadata_argv(ws: str, offline: bool = True, locked: bool = True) -> List[str]:
    """`locked=False` only for a private lock copy (unused_order_answer)."""
    return ["targo", "metadata", "--format-version", "1", *(["--offline"] if offline else []),
            *(["--locked"] if locked else []), "--manifest-path", ws]


def registry_gap(stderr: str) -> bool:
    """Did offline metadata fail for want of something the network would bring?
    Anything else (a bad manifest, an unpopulated submodule, a path dependency
    whose version no longer matches) no fetch can repair."""
    if _REGISTRY_GAP.search(stderr):
        return True
    if _OFFLINE_NOTE not in stderr:
        return False
    searched = [line.strip() for line in re.findall(r"^location searched:(.*)$", stderr, re.M)]
    return not searched or any(not where.startswith("/") for where in searched)


def cargo_error(stderr: str) -> str:
    """What failed and why: Cargo's first `error:` line and its last cause line
    (Cargo ends with `help:` and `note:` lines, which say neither)."""
    lines = [line.strip() for line in stderr.strip().splitlines() if line.strip()]
    if not lines:
        return "?"
    first = next((line for line in lines if line.startswith("error:")), lines[-1])
    cause = next((line for line in reversed(lines) if not line.startswith(("help:", "note:"))), first)
    return (first if cause == first else f"{first[:120]} ... {cause[:120]}")


def offline_metadata(ws: str) -> Tuple[Optional[subprocess.CompletedProcess], Optional[str]]:
    """The offline call, bounded: (its process, None), or (None, why it did
    not finish). OSError propagates: a targo that cannot start is no answer."""
    redirect = lock_redirect(REPO_ROOT)
    if redirect:
        return None, f"offline targo metadata was not run: {redirect}"
    try:
        return subprocess.run(metadata_argv(ws), cwd=REPO_ROOT, capture_output=True, text=True,
                              env=metadata_env(), timeout=METADATA_OFFLINE_TIMEOUT_S), None
    except subprocess.TimeoutExpired as exc:
        err = exc.stderr.decode("utf-8", "replace") if isinstance(exc.stderr, bytes) else (exc.stderr or "")
        cause = ("another Cargo holds $CARGO_HOME/.package-cache" if "Blocking waiting for file lock" in err
                 else f"no answer in {METADATA_OFFLINE_TIMEOUT_S} s")
        return None, f"offline targo metadata did not finish: {cause}"


def fill_registry(ws: str, locked: bool = True) -> Tuple[Optional[subprocess.CompletedProcess], Optional[str]]:
    """Run the online form once. (its process when it finished, why it did not
    fill the local registry or None). Never raises for a network that is not
    there: the caller's fallback is to select every leg. `locked=False` only
    for a private lock copy (unused_order_answer), whose rewrite is judged."""
    redirect = lock_redirect(REPO_ROOT)
    if redirect:
        return None, f"not run: {redirect}"
    try:
        proc = subprocess.run(metadata_argv(ws, offline=False, locked=locked), cwd=REPO_ROOT, capture_output=True,
                              text=True, env=metadata_env(), timeout=METADATA_FILL_TIMEOUT_S)
    except subprocess.TimeoutExpired:
        return None, f"no answer from the registry in {METADATA_FILL_TIMEOUT_S} s"
    except OSError as exc:
        return None, str(exc)
    if proc.returncode != 0:
        return proc, cargo_error(proc.stderr) if proc.stderr.strip() else f"exit {proc.returncode}"
    return proc, None


def answer_offline(ws: str, no_network: Optional[str], may_fill: bool = True,
                   say=lambda line: print(line, file=sys.stderr, flush=True), drift=None
                   ) -> Tuple[Optional[subprocess.CompletedProcess], Optional[str], Optional[str]]:
    """One workspace's graph, offline, filling the local registry once from
    the network when what it lacks is all that stops it (EW-2); the one step
    both the gate (verify_graph) and host setup (cmd_prefetch) take. Returns
    (the offline answer, or the online one when it reached the lock's own
    refusal, or None; why the offline call did not finish; the network
    verdict for the next workspace: once the network failed to fill one, no
    later one asks it again). A tree whose first-party worktrees are not the
    committed inputs (`drift`, first_party_drift) is not filled: what it lacks
    is not what the commit needs (review of EW-1). OSError propagates."""
    proc, hung = offline_metadata(ws)
    if proc is None or proc.returncode == 0 or not registry_gap(proc.stderr) or not may_fill:
        return proc, hung, no_network
    if (drift or first_party_drift)()[0]:
        return proc, hung, no_network
    if no_network is not None:
        say(f"registry: {ws}: not asking the network again: {no_network}")
        return proc, hung, no_network
    say(f"registry: {ws}: the local registry cannot answer offline; filling it from the network "
        f"(at most {METADATA_FILL_TIMEOUT_S} s)")
    filled, why = fill_registry(ws)
    if why is None:
        proc, hung = offline_metadata(ws)
        return proc, hung, None
    say(f"registry: {ws}: the network did not fill it: {why}")
    if filled is not None and locked_metadata_refusal(filled.stderr):
        return filled, None, None  # the gap hid it: the online form reached the lock's own refusal
    return proc, hung, why


class LockedWorkspaceInputs(RuntimeError):
    """Cargo definitively refused the committed inputs before any build."""

    def __init__(self, head: str, failures: List[dict]):
        self.head, self.failures = head, failures
        names = ", ".join(row["workspace"] for row in failures if row["stale_lock"])
        drifted = sorted({d for row in failures for d in row.get("drifted", [])})
        why = [f"locked workspace inputs require repair before building: {names}"] if names else []
        why += [f"{row['workspace']}: {row['old_targo']}" for row in failures if row.get("old_targo")]
        if drifted:
            why.append(f"first-party worktree(s) are not the committed inputs: {', '.join(drifted)}; "
                       "scripts/submodule_sync.sh")
        super().__init__("; ".join(why))


# The commit that made targo treat a lock's `[[patch.unused]]` rows as an
# unordered collection: sorted on write (`resolver/encode.rs`) and in the
# `--locked` comparison (`ops/lockfile/mod.rs` `are_equal_lockfiles`). A targo without it writes
# them in its own order and compares the text (LAND-GATE-UNUSED-PATCH-ORDER-1).
UNUSED_PATCH_SORT_COMMIT = "aef6192a8a92442dce7f571e909af3f74741c495"
TARGO_VERSION_TIMEOUT_S = 30


def path_targo_predates_unused_patch_sort(ws: str) -> Optional[str]:
    """Why the PATH targo cannot judge `ws`'s lock, when that is provable,
    else None (the refusal is the lock's). It is provable when the committed
    lock beside `ws` has `[[patch.unused]]` rows and this repository's history
    shows that the PATH targo's commit (`targo --unverified --version`, `+g`)
    does not contain UNUSED_PATCH_SORT_COMMIT: that targo refuses the tree's
    sorted order as a difference, so its refusal cannot tell a stale lock from
    an order it does not know. The answer is NOT JUDGED either way; only its
    cause changes. A version that does not parse, a commit this clone lacks,
    or any failure keeps the stale-lock reading. Ancestry between two commit
    ids is immutable; the version is read on each call."""
    try:
        lock = tomllib.loads(((REPO_ROOT / ws).parent / "Cargo.lock").read_text(encoding="utf-8"))
        rows = (lock.get("patch") or {}).get("unused") or []
        if not isinstance(rows, list) or not rows:
            return None
        version = subprocess.run(["targo", "--unverified", "--version"], cwd=REPO_ROOT, capture_output=True,
                                 text=True, env=metadata_env(), timeout=TARGO_VERSION_TIMEOUT_S)
        found = re.search(r"\(targo [^()\s]*\+g([0-9a-f]{7,40})\)", version.stdout or "")
        if version.returncode != 0 or not found:
            return None
        ancestry = subprocess.run(["git", "merge-base", "--is-ancestor", UNUSED_PATCH_SORT_COMMIT,
                                   found.group(1)], cwd=REPO_ROOT, capture_output=True, text=True,
                                  timeout=TARGO_VERSION_TIMEOUT_S)
    except (OSError, ValueError, AttributeError, subprocess.TimeoutExpired):
        return None
    if ancestry.returncode != 1:  # 0: it has the sort; 128: this clone cannot tell
        return None
    return (f"NOT JUDGED: the PATH targo (g{found.group(1)}) predates {UNUSED_PATCH_SORT_COMMIT[:12]}, which "
            f"made targo treat the lock's {len(rows)} [[patch.unused]] rows as unordered; it compares their "
            "order as text, so its `--locked` refusal cannot tell a stale lock from the tree's sorted order "
            "(LAND-GATE-UNUSED-PATCH-ORDER-1). Put a targo whose commit contains "
            f"{UNUSED_PATCH_SORT_COMMIT[:12]} on PATH (a newer atpkg `trust` pack)")


def locked_metadata_refusal(stderr: str) -> bool:
    # Cargo's three observed spellings: a lock to update (two wordings) and a
    # missing lock, "cannot create the lock file X because --locked was passed"
    # (measured 2026-11-06, LOCK-STALE-1). A generic offline/cache/tool failure
    # is still uncertainty and retains the conservative all-leg fallback.
    return bool(re.search(
        r"(?:cannot (?:update|create) the lock file[^\n]*"
        r"|(?:the )?lock file[^\n]*needs to be updated[^\n]*)--locked\b",
        stderr))


# LAND-GATE-UNUSED-PATCH-ORDER-1. The tree's resolver sorts the
# `[[patch.unused]]` records before it writes a lock
# (src/tools/targo/crates/targo-core/src/resolver/encode.rs, `patch.unused.sort()`).
# atpkg's pack 16387 targo (0.12.0+g29ebb403d) predates that sort and refuses,
# under --locked, both the committed lock and its own rewrite of it (3/3 each,
# 2026-11-13), so on a host whose PATH targo is that pack no lock passes. Its
# unlocked rewrite is judged on a private copy of the lock instead, never on
# the committed file: the copy is a directory of links beside the workspace
# (so every relative path dependency names the same package) holding its own
# Cargo.lock. atpkg's shim refuses a `resolver.lockfile-path` redirect (exit 75,
# measured 2026-11-13), and pack 16387 has no `--lockfile-path`.
UNUSED_ORDER_COPY_PREFIX = ".trust-land-unused-order."


def tree_unused_order(rows) -> bool:
    """Are these `[[patch.unused]]` rows in the order the tree's resolver
    writes them? Its sort is the derived Ord of `TomlLockfileDependency`:
    `name`, then `version`, as Rust strings (UTF-8 byte order), then `source`,
    whose own Ord is not reproduced here: two rows equal in name and version
    must be equal rows, or the order is not judged (False)."""
    if not isinstance(rows, list) or not all(
            isinstance(row, dict) and isinstance(row.get("name"), str) and isinstance(row.get("version"), str)
            for row in rows):
        return False
    for a, b in zip(rows, rows[1:]):
        ka = (a["name"].encode("utf-8"), a["version"].encode("utf-8"))
        kb = (b["name"].encode("utf-8"), b["version"].encode("utf-8"))
        if ka > kb or (ka == kb and a != b):
            return False
    return True


def unused_rows_only_permuted(committed: bytes, rewritten: bytes) -> bool:
    """Does `rewritten` differ from `committed`, and only in the order of
    complete `[[patch.unused]]` rows in the writer's framing
    (land_development.targo_unused_patch_blocks)? Every byte before the first
    such row, `[[package]]` rows and metadata included, must be equal."""
    from collections import Counter
    from land_development import targo_unused_patch_blocks
    if rewritten == committed:
        return False
    try:
        (head, rows), (new_head, new_rows) = (targo_unused_patch_blocks(committed),
                                              targo_unused_patch_blocks(rewritten))
    except (UnicodeError, ValueError, KeyError, TypeError):
        return False
    return head == new_head and Counter(rows) == Counter(new_rows)


def unused_order_copy_parents() -> List[Path]:
    """Where a private lock copy can stand: beside each workspace of
    METADATA_WORKSPACES but the root."""
    return sorted({(REPO_ROOT / Path(ws).parent).parent for ws in METADATA_WORKSPACES
                   if Path(ws).parent != Path(".")})


def _remove_unused_order_copy(copy: Path, say) -> None:
    """Remove a private lock copy: its links and its lock, never what a link
    names. The directory is opened without following a link, and each entry
    is removed relative to that descriptor. Anything else in it stays, and is
    said."""
    try:
        fd = os.open(copy, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW)
    except FileNotFoundError:
        return
    except OSError as exc:
        say(f"lock: {copy} was not removed: {exc}")
        return
    left = []
    try:
        with os.scandir(fd) as entries:
            found = [(entry.name, entry.is_symlink(), entry.is_file(follow_symlinks=False)) for entry in entries]
        for name, link, regular in found:
            try:
                if link or (name == "Cargo.lock" and regular):
                    os.unlink(name, dir_fd=fd)
                else:
                    left.append(name)
            except OSError as exc:
                left.append(f"{name} ({exc})")
    finally:
        os.close(fd)
    try:
        copy.rmdir()
    except OSError as exc:
        say(f"lock: {copy} was not removed ({exc}); it still holds: {', '.join(left) or 'nothing'}")


def sweep_dead_unused_order_copies(say=lambda line: print(line, file=sys.stderr, flush=True),
                                   parents: Optional[Iterable[Path]] = None) -> None:
    """Remove the private lock copies a killed gate left (their process is
    gone) beside every workspace a copy can stand beside: `parents`, or by
    default those of METADATA_WORKSPACES. verify_graph and prefetch run it
    first, whatever the lock's outcome, and the lock hygiene check runs it
    over the parents of the workspaces it judges. Only a real directory (not
    a link) this user owns is removed; a live process's copy is its own. The
    tree's .gitignore ignores the name, so a leftover is never staged."""
    for parent in (unused_order_copy_parents() if parents is None else parents):
        try:
            names = [name for name in os.listdir(parent) if name.startswith(UNUSED_ORDER_COPY_PREFIX)]
        except OSError:
            continue
        for name in names:
            pid = name[len(UNUSED_ORDER_COPY_PREFIX):].split(".", 1)[0]
            if not pid.isdigit() or int(pid) == os.getpid():
                continue
            try:
                info = os.lstat(parent / name)
            except OSError:
                continue
            if not stat.S_ISDIR(info.st_mode) or info.st_uid != os.getuid():
                continue
            try:
                os.kill(int(pid), 0)
                continue
            except ProcessLookupError:
                _remove_unused_order_copy(parent / name, say)
            except OSError:
                continue


def unused_order_answer(ws: str, committed: bytes, no_network: Optional[str] = "not asked", may_fill: bool = False,
                        say=lambda line: print(line, file=sys.stderr, flush=True)
                        ) -> Tuple[Optional[subprocess.CompletedProcess], Optional[str]]:
    """For a workspace whose offline `--locked` metadata refused the lock
    (LAND-GATE-UNUSED-PATCH-ORDER-1): (the graph of an unlocked offline call on
    a private copy of `committed`, or None, and the refusal stands; the
    network verdict, as answer_offline returns it). It answers only when
    every one of these holds:
    * the workspace is not the tree's root (its copy stands beside it), and
      the worktree's lock is `committed`, byte for byte;
    * `committed` holds `[[patch.unused]]` rows in the order the tree's
      resolver writes them (tree_unused_order);
    * no config redirects or disables the lock comparison (lock_redirect);
    * the call succeeds, and its rewrite of the copy differs from `committed`
      only in the order of complete unused rows (unused_rows_only_permuted).
    When the copy's call fails only for what the local registry lacks, the
    network may be asked (`may_fill`) and has not failed (`no_network` None),
    and the resolve that call wrote to the copy before it failed already
    differs from `committed` only in unused-row order, one online unlocked
    call on the copy fills the registry, and the offline call is asked again.
    It is unlocked because this targo refuses its own rewrite under
    `--locked` too; the order check keeps its downloads to the packages
    `committed` names. The graph's paths into the copy are mapped back to the
    workspace's. Each way the refusal stands is said."""
    ws_dir = Path(ws).parent
    if ws_dir == Path("."):
        say(f"lock: {ws}: the root workspace's lock is not judged on a private copy (a copy beside it would stand "
            "outside the checkout); the refusal stands")
        return None, no_network
    source = REPO_ROOT / ws_dir
    try:
        if (source / "Cargo.lock").is_symlink() or (source / "Cargo.lock").read_bytes() != committed:
            return None, no_network
        patch = tomllib.loads(committed.decode("utf-8")).get("patch")
        rows = patch.get("unused") if isinstance(patch, dict) else None
    except (OSError, UnicodeError, ValueError):
        return None, no_network
    if not rows or not tree_unused_order(rows) or lock_redirect(REPO_ROOT):
        return None, no_network
    try:
        copy = Path(tempfile.mkdtemp(prefix=f"{UNUSED_ORDER_COPY_PREFIX}{os.getpid()}.",
                                     suffix=f".{ws_dir.name}", dir=source.parent))
    except OSError as exc:
        say(f"lock: {ws}: no private lock copy could be made beside it ({exc}); the refusal stands")
        return None, no_network
    copy_rel = copy.relative_to(REPO_ROOT)
    manifest = str(copy_rel / "Cargo.toml")

    def offline() -> subprocess.CompletedProcess:
        return subprocess.run(metadata_argv(manifest, locked=False), cwd=REPO_ROOT, capture_output=True, text=True,
                              env=metadata_env(), timeout=METADATA_OFFLINE_TIMEOUT_S)
    try:
        for entry in sorted(os.listdir(source)):
            if entry == "Cargo.lock":
                (copy / entry).write_bytes(committed)
            elif entry != "target" and not entry.startswith(".git"):
                os.symlink(source / entry, copy / entry)
        proc = offline()
        if proc.returncode != 0 and registry_gap(proc.stderr) and may_fill and no_network is None:
            # Targo writes its resolve before it downloads, so a call that
            # failed only on a download has left that resolve in the copy. The
            # unlocked fill runs only when that resolve is the committed lock's
            # own, its unused rows reordered: then every package it downloads
            # is one the committed lock names, held to its checksum. A resolve
            # that moved, or none written, asks no network.
            if not unused_rows_only_permuted(committed, (copy / "Cargo.lock").read_bytes()):
                say(f"lock: {ws}: the private lock copy cannot answer offline, and its partial rewrite is not the "
                    "committed lock with its unused rows reordered; the network is not asked and the refusal stands")
                return None, no_network
            say(f"registry: {ws}: the private lock copy cannot answer offline; filling the local registry from "
                f"the network (at most {METADATA_FILL_TIMEOUT_S} s)")
            _filled, no_network = fill_registry(manifest, locked=False)
            if no_network is None:
                proc = offline()
            else:
                say(f"registry: {ws}: the network did not fill it: {no_network}")
        rewritten = (copy / "Cargo.lock").read_bytes()
    except (OSError, subprocess.TimeoutExpired) as exc:
        say(f"lock: {ws}: the unlocked call on a private lock copy did not answer ({exc}); the refusal stands")
        return None, no_network
    finally:
        _remove_unused_order_copy(copy, say)
    if proc.returncode != 0:
        say(f"lock: {ws}: the unlocked call on a private lock copy failed too ({cargo_error(proc.stderr)}); "
            "the refusal stands")
        return None, no_network
    if not unused_rows_only_permuted(committed, rewritten):
        say(f"lock: {ws}: the PATH targo's rewrite of a private lock copy differs from the committed lock in more "
            "than the order of unused rows; the refusal stands")
        return None, no_network
    inside = re.compile(re.escape("/" + copy_rel.as_posix()) + r"(?=[/#\"]|$)", re.M)
    stdout = inside.sub(lambda _m: "/" + ws_dir.as_posix(), proc.stdout)
    if copy.name in stdout:
        say(f"lock: {ws}: the private lock copy's graph names the copy where its paths cannot be mapped back; "
            "the refusal stands")
        return None, no_network
    try:
        json.loads(stdout)
    except ValueError:
        return None, no_network
    say(f"lock: {ws}: the PATH targo refuses the committed lock under --locked; its rewrite of a private copy "
        f"differs only in the order of {len(rows)} complete [[patch.unused]] rows, which the committed lock holds "
        "in the order the tree's resolver writes (LAND-GATE-UNUSED-PATCH-ORDER-1): the graph is that copy's")
    return subprocess.CompletedProcess(proc.args, 0, stdout, proc.stderr), no_network


def record_locked_input_refusal(error: LockedWorkspaceInputs) -> Path:
    path = common_dir() / "trust-land" / "refusals" / f"{time.time_ns()}-{os.getpid()}" / "record.json"
    path.parent.mkdir(parents=True, exist_ok=False)
    path.write_text(json.dumps({
        "schema": "trust-land-input-refusal/1", "head": error.head,
        "outcome": "NOT JUDGED", "compilation_or_proof_run": False,
        "failures": error.failures,
    }, indent=2), encoding="utf-8")
    return path


def verify_graph(g: ls.Graph) -> List[str]:
    """Hold the selector's graph to the real build graph: every edge between
    two packages of this tree that `targo metadata` resolves, in each Cargo
    workspace a leg builds, must be an edge of the selector's graph. Returns
    the reasons it is not (each selects every leg); [] when it holds.
    `targo metadata` that fails or cannot parse conservatively selects more.
    A process-launch error refuses with a not-judged diagnostic; a definite
    stale-lock refusal, or a first-party worktree that is not the committed
    input (first_party_drift), raises because more builds cannot repair its
    inputs.
    The call is offline. Only when it fails for what the local registry lacks
    does it go online, once per such workspace, to fill that (host setup does it
    first: `prefetch`; main can move the lock past it), and ask again offline.
    After one fill fails, no later workspace asks the network, and every leg
    runs as before."""
    problems: List[str] = []
    failures: List[dict] = []
    no_network: Optional[str] = None
    drift = _once(first_party_drift)
    root = str(REPO_ROOT) + "/"
    sweep_dead_unused_order_copies()
    for ws in METADATA_WORKSPACES:
        if ws not in g.index.entries:
            continue
        try:
            proc, hung, no_network = answer_offline(ws, no_network, drift=drift)
        except OSError as exc:
            raise RuntimeError(f"cannot execute targo metadata --manifest-path {ws}: {exc}; "
                               "restore the selected Trust Targo on PATH") from exc
        lock_rel = str(Path(ws).parent / "Cargo.lock")
        if (proc is not None and proc.returncode != 0 and locked_metadata_refusal(proc.stderr)
                and lock_rel in g.index.entries and not any(drift())):
            copied, no_network = unused_order_answer(ws, g.index.read_blobs([lock_rel])[lock_rel],
                                                     no_network, may_fill=True)
            proc = copied or proc
        if proc is None or proc.returncode != 0:
            kind, said, drifted = offline_failure(proc, hung, no_network, drift=drift, ws=ws)
            if proc is not None:
                failures.append({"workspace": ws, "exit": proc.returncode,
                                 "stderr": proc.stderr, "stdout": proc.stdout,
                                 "stale_lock": kind == "stale_lock", "drifted": drifted,
                                 "old_targo": said if kind == "old_targo" else None})
            problems.append(f"targo metadata --manifest-path {ws} failed: {said}")
            continue
        try:
            meta = json.loads(proc.stdout)
        except ValueError as exc:
            problems.append(f"targo metadata --manifest-path {ws}: unparsable output ({exc})")
            continue
        pkgs = {p["id"]: p for p in meta.get("packages", [])}

        def rel(pid: str) -> Optional[str]:
            p = pkgs.get(pid)
            if p is None or p.get("source") is not None:
                return None
            d = os.path.dirname(p["manifest_path"])
            return d[len(root):] if d.startswith(root) else "<outside>" + d

        for node in (meta.get("resolve") or {}).get("nodes", []):
            a = rel(node["id"])
            if a is None:
                continue
            for dep in node.get("deps", []):
                b = rel(dep["pkg"])
                if b is None:
                    continue
                if a.startswith("<outside>") or b.startswith("<outside>"):
                    problems.append(f"{ws}: a path package outside the checkout ({a} -> {b})")
                    continue
                na = a if a in g.packages else g.owner(a + "/Cargo.toml")
                nb = b if b in g.packages else g.owner(b + "/Cargo.toml")
                if na in g.gitlinks or na == nb:
                    continue
                if na not in g.packages or nb not in g.packages[na].deps:
                    problems.append(f"{ws}: targo metadata resolves {a} -> {b}, which the selector's graph lacks")
    if any(row["stale_lock"] or row["drifted"] or row["old_targo"] for row in failures):
        raise LockedWorkspaceInputs(g.index.rev, failures)
    return problems


def resolve_base(base: Optional[str]) -> str:
    if base:
        return git("rev-parse", "--verify", f"{base}^{{commit}}")
    return git("merge-base", "origin/main", "HEAD")


class _DiscoveryProgress:
    """Flushed stderr observations; no graph, receipt, cache or timer thread.

    `phases`: seconds spent in each phase, from its "start" to the next event
    of that phase that is not "start" or "progress" (a phase run more than once,
    the module closure's rounds, adds up). Observations only: the run record
    itemises them (record.json "discovery"), nothing reads them back."""
    def __init__(self, *, started=None, clock=None, stream=None, echo=True):
        self.clock = time.monotonic if clock is None else clock
        self.stream = sys.stderr if stream is None else stream
        self.started = self.clock() if started is None else started
        self.last_time = self.started
        self.last_phase = None
        self.disabled = not echo
        self.phases: Dict[str, float] = {}
        self.opened: Dict[str, float] = {}

    def timing(self) -> Dict[str, float]:
        """The phases' seconds, longest first, rounded for the record."""
        return {phase: round(seconds, 2)
                for phase, seconds in sorted(self.phases.items(), key=lambda item: (-item[1], item[0]))}

    def __call__(self, phase, state, counts):
        now = self.clock()
        if state == "start":
            self.opened[phase] = now
        elif state != "progress" and phase in self.opened:
            self.phases[phase] = self.phases.get(phase, 0.0) + now - self.opened.pop(phase)
        if self.disabled:
            return
        if state == "progress" and phase == self.last_phase and now - self.last_time < 5:
            return
        details = "".join(f" {key}={value}" for key, value in sorted(counts.items()))
        self.write(f"land-gate: discovery {phase} {state}{details}; elapsed={now - self.started:.2f}s")
        self.last_time, self.last_phase = now, phase

    def write(self, message):
        if self.disabled:
            return
        try:
            print(message, file=self.stream, flush=True)
        except (OSError, ValueError):
            # Additional observations cannot turn an unchanged computation
            # into a different verdict when the diagnostic stream closes.
            self.disabled = True


def discovery_record(progress: Optional["_DiscoveryProgress"], graph, *, seconds: Optional[float] = None) -> dict:
    """What one discovery cost and reused, for the run record (record.json
    "discovery"): reported, never a reuse or selection input. Without a
    progress observer the discovery was timed whole (`seconds`) and its
    "phases" are null: not itemised, rather than none."""
    if progress is None:
        record = {"seconds": round(seconds or 0.0, 2), "phases": None}
    else:
        record = {"seconds": round(progress.clock() - progress.started, 2), "phases": progress.timing()}
    if isinstance(graph, ls.Graph):
        record.update(packages=len(graph.packages), reused_packages=len(graph.reused_packages),
                      reused_tokenizations=graph.reused_tokenizations,
                      reused_grep_answers=graph.__dict__.get("_reused_grep_answers", 0),
                      reused_blob_facts=graph.__dict__.get("_reused_blob_facts", 0),
                      stored_tree=graph.__dict__.get("_stored_tree"))
    return record


def compute(base: Optional[str], head: str = "HEAD", verify: bool = False,
            previous: Optional[ls.Graph] = None, *, progress=None
            ) -> Tuple[ls.Graph, ls.Selection, str]:
    ls._report_discovery(progress, "index", "start")
    base_sha = resolve_base(base)
    idx = ls.TreeIndex.load(str(REPO_ROOT), head)
    ls._report_discovery(progress, "index", "complete", tracked_entries=len(idx.entries))
    def build(earlier):
        if progress is None:
            return ls.build_graph(idx, earlier) if earlier is not None else ls.build_graph(idx)
        return ls.build_graph(idx, earlier, progress=progress)
    # A process that holds no earlier graph starts from the clone's stored one
    # (land_select's graph store); what it may reuse is build_graph's decision.
    g = ls.refresh_graph(idx, ls.graph_store_directory(idx.repo), previous, build=build, progress=progress)
    ls._report_discovery(progress, "selection", "start")
    changed = ls.changed_paths(str(REPO_ROOT), base_sha, idx.rev)
    in_place = in_place_changes(str(REPO_ROOT), base_sha, idx.rev)
    sel = ls.select(g, base_sha, changed, in_place=in_place)
    if verify:
        ls._report_discovery(progress, "resolver verification", "start", packages=len(g.packages))
        problems = verify_graph(g)
        if problems:
            # The graph the selection used is not the build's: select everything.
            sel = ls.select(g, base_sha, changed, extra_everything=[f"unverified graph: {p}" for p in problems[:5]],
                            in_place=in_place)
        ls._report_discovery(progress, "resolver verification", "complete", problems=len(problems))
    ls._report_discovery(progress, "selection", "complete", changed_paths=len(changed))
    return g, sel, base_sha


def _loaded_discovery_readers(root: Optional[Path] = None) -> Set[str]:
    readers = (set(GATE_FILES) | set(IR_DIAGNOSTIC_READERS)) - GATE_DATA_FILES
    # Data, but loaded: land_select built its validation tables from the row
    # table when this process imported it, and reads the file no more.
    readers.add(ls.LAND_ROWS_FILE)
    root = (REPO_ROOT if root is None else root).resolve()
    for module in tuple(sys.modules.values()):
        path = getattr(module, "__file__", None)
        if not isinstance(path, str):
            continue
        source = Path(path)
        if source.suffix == ".pyc":
            try:
                source = Path(importlib.util.source_from_cache(str(source)))
            except ValueError:
                continue
        try:
            readers.add(source.resolve().relative_to(root).as_posix())
        except (OSError, ValueError):
            pass
    return readers


def _selection_owner_data(source: str) -> Tuple[str, Dict[str, dict], Dict[str, tuple]]:
    """Decode the row table's ownership data (ls.LAND_ROWS_FILE) from its text.

    The table is data, so decoding executes nothing, and a table the selector
    would refuse to load is refused here (LandRowsError is a ValueError). The
    two path tables are returned for refresh. Everything else the loaded
    selector took from the table (what it covers, and the modules nothing
    selects with their reasons) is the first value: it is compared, never
    refreshed, as the rest of land_select.py's source was while the tables were
    literals in it. The table declares no alias, so the third value is empty.
    """
    table = ls.parse_land_rows(source)
    fixed = {"schema": ls.LAND_ROWS_SCHEMA, "covered": table.covered,
             "VALIDATION_UNJUDGED_MODULES": table.unjudged_modules,
             "VALIDATION_UNMAPPED_RED": table.unmapped_red}
    tables = {"VALIDATION_PROGRAM_TESTS": table.program_tests,
              "VALIDATION_TEST_SUBJECTS": table.test_subjects}
    return json.dumps(fixed, sort_keys=True), tables, {}


def _data_reader_text(path: str) -> str:
    """A data reader's text as the checkout holds it. The row table is read as
    land_select itself reads it: from a regular file only, never through a
    symbolic link (ls.read_land_rows_text), so a table that incoming main turns
    into a link is refused here and not decoded from the link's target."""
    if path == ls.LAND_ROWS_FILE:
        return ls.read_land_rows_text(str(REPO_ROOT))
    return (REPO_ROOT / path).read_text()


def _program_owner_data(source: str) -> Tuple[str, Dict[str, dict], Dict[str, tuple]]:
    """Decode one closed ownership binding; never execute incoming source.

    Import-time observations may read only literal keys. Their original rows
    must survive composition, so already constructed constants stay current.
    A whole-table capture, dynamic key or eager callback refuses refresh.
    """
    import copy
    tree = ast.parse(source)
    binding = None
    rows, bindings, aliases = {}, {}, {}

    def closed_tuple(expression, *, record=False):
        if isinstance(expression, ast.Name) and expression.id in bindings:
            if record:
                aliases[expression.id] = bindings[expression.id]
            return bindings[expression.id]
        if isinstance(expression, ast.BinOp) and isinstance(expression.op, ast.Add):
            return (closed_tuple(expression.left, record=record)
                    + closed_tuple(expression.right, record=record))
        value = ast.literal_eval(expression)
        if not isinstance(value, tuple) or not value or any(not isinstance(item, str) for item in value):
            raise ValueError("ownership value is not a closed string tuple")
        return value

    for node in tree.body:
        if (isinstance(node, ast.Assign) and len(node.targets) == 1
                and isinstance(node.targets[0], ast.Name)
                and node.targets[0].id == "PROGRAM_TESTS"):
            if binding is not None or not isinstance(node.value, ast.Dict):
                raise ValueError("invalid or duplicate program ownership binding")
            binding = node
            for key_node, value_node in zip(node.value.keys, node.value.values):
                key, value = ast.literal_eval(key_node), closed_tuple(value_node, record=True)
                if (not isinstance(key, str) or key in rows or not isinstance(value, tuple)
                        or not value or any(not isinstance(item, str) for item in value)):
                    raise ValueError("invalid program ownership row")
                rows[key] = value
        elif binding is None:
            target = (node.target if isinstance(node, ast.AnnAssign) else
                      node.targets[0] if isinstance(node, ast.Assign) and len(node.targets) == 1 else None)
            try:
                if not isinstance(target, ast.Name):
                    raise ValueError("not a closed data binding")
                bindings[target.id] = closed_tuple(node.value)
            except (ValueError, TypeError, SyntaxError):
                bindings.clear()
    if binding is None:
        raise ValueError("missing program ownership binding")
    definitions = {node.name: node for node in tree.body
                   if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef))}
    captures = {name for name, node in definitions.items()
                if any(isinstance(child, ast.Name) and child.id == "PROGRAM_TESTS"
                       for child in ast.walk(node))}
    while True:
        expanded = captures | {name for name, node in definitions.items()
                               if any(isinstance(child, ast.Call)
                                      and isinstance(child.func, ast.Name)
                                      and child.func.id in captures for child in ast.walk(node))}
        if expanded == captures:
            break
        captures = expanded

    class EagerReads(ast.NodeTransformer):
        def visit_ClassDef(self, node):
            if node.name in captures:
                raise ValueError("class body may capture program ownership data")
            return self.generic_visit(node)

        def visit_Call(self, node):
            if isinstance(node.func, ast.Name) and node.func.id in (
                    captures | {"eval", "exec", "globals", "locals", "vars"}):
                raise ValueError("eager callback may capture program ownership data")
            return self.generic_visit(node)

        def visit_FunctionDef(self, node):
            # Bodies run after refresh; defaults, decorators and annotations
            # can capture old data during import and must be checked now.
            for expression in [*node.decorator_list, node.args, node.returns,
                               *getattr(node, "type_params", [])]:
                if expression is not None:
                    self.visit(expression)
            return node

        visit_AsyncFunctionDef = visit_FunctionDef

        def visit_Subscript(self, node):
            if isinstance(node.value, ast.Name) and node.value.id == "PROGRAM_TESTS":
                key = ast.literal_eval(node.slice)
                if not isinstance(key, str) or key not in rows:
                    raise ValueError("dynamic or absent eager ownership key")
                return ast.Tuple(elts=[ast.Constant(item) for item in rows[key]], ctx=ast.Load())
            return self.generic_visit(node)

        def visit_Name(self, node):
            if node.id == "PROGRAM_TESTS" or node.id in captures:
                raise ValueError("eager capture of program ownership table")
            return node

    for node in tree.body:
        if node is not binding:
            # Check a separate AST: the complete original executable AST stays
            # in the identity comparison, including every derived constant.
            EagerReads().visit(copy.deepcopy(node))
    binding.value = ast.Constant(value=None)
    return ast.dump(tree, include_attributes=False), {"PROGRAM_TESTS": rows}, aliases



def _discovery_reader_identity(root: Optional[Path] = None):
    """Current physical reader bytes, never a cached verdict or remote fact."""
    root = REPO_ROOT if root is None else root
    rows = []
    for relative in sorted(p for p in _loaded_discovery_readers(root) if p.endswith(".py")):
        path = root / relative
        try:
            metadata = path.lstat()
            if not stat.S_ISREG(metadata.st_mode):
                value = ("not-regular", None)
            else:
                value = ("100755" if metadata.st_mode & stat.S_IXUSR else "100644", sha256_file(path))
        except FileNotFoundError:
            value = None
        except OSError:
            value = ("unreadable", None)
        rows.append((relative, value))
    return str(root.resolve()), tuple(rows)


def _discovery_interpreter_problem():
    """(why this interpreter's loaded readers are unbound or None, current identity).

    Reads only: it changes no binding, so a test harness can ask it after each
    test without changing what the next discovery session is judged against."""
    # This baseline is captured at module initialization, before an importing
    # caller can edit/commit readers and start its first DiscoverySession.
    # Inspect the loaded program's origin even when a caller selects a different
    # repository as its graph input. New unbound readers require a new process.
    if importlib.machinery.SourceFileLoader.exec_module is not _DISCOVERY_SOURCE_IMPORTS.transport:
        return "discovery source loader changed; restart the gate", None
    current = _discovery_reader_identity(_DISCOVERY_SOURCE_ROOT)
    before, after = dict(_DISCOVERY_INTERPRETER_READERS[1]), dict(current[1])
    if any(after.get(path) != value for path, value in before.items()):
        return "loaded discovery reader changed since interpreter initialization; restart the gate", current
    if (builtins.__import__, importlib.import_module, importlib.util.module_from_spec,
            importlib._bootstrap.module_from_spec) != _DISCOVERY_SOURCE_IMPORTS.hooks:
        return "discovery import provenance hooks changed; restart the gate", current
    problem = _DISCOVERY_SOURCE_IMPORTS.implementation_problem(sys.modules.get(__name__),
        _DISCOVERY_SOURCE_IMPORTS.executions.get(sys.modules.get(__name__)))
    if problem:
        return problem, current
    implementation_paths = (set(GATE_FILES) | set(IR_DIAGNOSTIC_READERS)) - GATE_DATA_FILES
    for module, path in _discovery_loaded_modules(_DISCOVERY_SOURCE_ROOT):
        execution = _DISCOVERY_SOURCE_IMPORTS.executions.get(module)
        caller_implementation = (path in implementation_paths and path != "scripts/land_gate.py"
                                 and (execution is None or execution.role != "implementation"))
        if _DISCOVERY_SOURCE_IMPORTS.records.get(module) != (path, after[path]) or caller_implementation:
            return ("loaded discovery reader has no matching captured source or active code binding; restart the gate",
                    current)
    added = after.keys() - before.keys()
    if added:
        expected = _discovery_origin_readers(added)
        if expected != {path: after[path] for path in added} or current != _discovery_reader_identity(_DISCOVERY_SOURCE_ROOT):
            return "new discovery reader is not bound to the interpreter origin; restart the gate", current
    return None, current


def _check_discovery_interpreter():
    global _DISCOVERY_INTERPRETER_READERS
    problem, current = _discovery_interpreter_problem()
    if problem:
        raise LandingUnjudged(problem)
    if dict(current[1]).keys() - dict(_DISCOVERY_INTERPRETER_READERS[1]).keys():
        # Rebind only for an added reader, which passed the origin binding
        # above: later sessions are judged against it. Any other difference
        # that passed (a reader recorded absent at initialization and since
        # unloaded) keeps the baseline, so that path reappearing is refused
        # as changed rather than adopted as an addition.
        _DISCOVERY_INTERPRETER_READERS = current


def _discovery_origin_readers(paths):
    if not _DISCOVERY_ORIGIN_COMMIT:
        return {}
    env = dict(git_query_env(), GIT_NO_REPLACE_OBJECTS="1")
    listed = _git_ask(_DISCOVERY_SOURCE_ROOT, env, "--literal-pathspecs", "ls-tree", "-z",
                      _DISCOVERY_ORIGIN_COMMIT, "--", *sorted(paths), timeout=10)
    if listed.returncode:
        return {}
    rows = {}
    try:
        for record in listed.stdout.split("\0"):
            if not record:
                continue
            metadata, path = record.split("\t", 1)
            mode, kind, oid = metadata.split()
            if path not in paths or path in rows or mode not in ("100644", "100755") or kind != "blob":
                return {}
            blob = subprocess.run(["git", "-C", str(_DISCOVERY_SOURCE_ROOT), "cat-file", "blob", oid],
                                  capture_output=True, env=env, timeout=10)
            if blob.returncode:
                return {}
            digest = hashlib.new("sha1" if len(oid) == 40 else "sha256")
            digest.update(f"blob {len(blob.stdout)}\0".encode()); digest.update(blob.stdout)
            if digest.hexdigest() != oid:
                return {}
            rows[path] = mode, hashlib.sha256(blob.stdout).hexdigest()
    except (OSError, ValueError, subprocess.TimeoutExpired):
        return {}
    return rows








def _refresh_discovery_interpreter_readers(paths):
    # Only _compose_discovery's validated ownership or identical-AST transitions
    # can update a loaded reader binding. No executable reader is hot-reloaded.
    global _DISCOVERY_INTERPRETER_READERS
    if REPO_ROOT.resolve() != _DISCOVERY_SOURCE_ROOT:
        return
    current = _discovery_reader_identity(_DISCOVERY_SOURCE_ROOT)
    before, after = dict(_DISCOVERY_INTERPRETER_READERS[1]), dict(current[1])
    if before.keys() != after.keys() or any(before[p] != after[p] for p in before if p not in paths):
        raise LandingUnjudged("loaded discovery reader changed during composition; restart the gate")
    _DISCOVERY_INTERPRETER_READERS = current
    for module, path in _discovery_loaded_modules(_DISCOVERY_SOURCE_ROOT):
        if path in paths and module in _DISCOVERY_SOURCE_IMPORTS.records:
            _DISCOVERY_SOURCE_IMPORTS.records[module] = path, after[path]
            _DISCOVERY_SOURCE_IMPORTS.kinds[module] = "validated-composition-refresh"
            execution = _DISCOVERY_SOURCE_IMPORTS.executions.get(module)
            if execution is not None and execution.role in ("entry", "implementation"):
                execution.record = path, after[path]


def _discovery_readers_bound(graph, identity):
    """The remembered classifier ran with the exact committed reader bytes."""
    if (type(graph) is not ls.Graph or type(graph.index) is not ls.TreeIndex
            or not graph._classification_reads_complete or not graph.__dict__.get("_scan_complete", False)
            or str(Path(graph.index.repo).resolve()) != identity[0]):
        return False
    rows = dict(identity[1])
    if any(value is not None and path not in graph.index.entries for path, value in rows.items()):
        return False
    paths = [path for path in rows if path in graph.index.entries]
    try:
        blobs = graph.index.read_blobs(paths)
    except (OSError, RuntimeError, ValueError):
        return False
    return all(rows[path] == (graph.index.entries[path][0], hashlib.sha256(blobs[path]).hexdigest())
               for path in paths)


def _same_discovery_readers(before, after):
    # A newly imported dependency can extend the observed reader set. Existing
    # reader bytes cannot silently become a new interpreter/code generation.
    return before[0] == after[0] and dict(before[1]).items() <= dict(after[1]).items()


def _compute_in_session(session, base, head, verify, profile, *, progress=None, checkout=None):
    # Reuse only completed classification. Each invocation still loads the
    # exact index and recomputes selection, resolver checks and live facts.
    try:
        _check_discovery_interpreter()
    except LandingUnjudged:
        session.graph = None
        raise
    before = _discovery_reader_identity()
    remembered = getattr(session, "readers", None)
    if not isinstance(remembered, tuple):
        remembered = None
    if remembered is not None and not _same_discovery_readers(remembered, before):
        session.graph = None
        raise LandingUnjudged("loaded discovery reader changed; restart the gate")
    previous = session.graph if remembered is not None else None
    session.readers = before
    proof = {"problem": None, "identity": object()}
    _DISCOVERY_SOURCE_IMPORTS.active.append(proof)
    try:
        result = compute_discovery(base, head, verify, previous, profile, progress=progress, checkout=checkout)
    except _DiscoveryImportUnbound as error:
        session.graph = None
        raise LandingUnjudged(str(error)) from None
    finally:
        _DISCOVERY_SOURCE_IMPORTS.active.remove(proof)
    if proof["problem"]:
        session.graph = None
        raise LandingUnjudged(proof["problem"])
    _check_cancellation()
    graph = result[0]
    try:
        _check_discovery_interpreter()
    except LandingUnjudged:
        session.graph = None
        raise
    after = _discovery_reader_identity()
    if not _same_discovery_readers(before, after):
        session.graph = None
        raise LandingUnjudged("loaded discovery reader changed during classification; restart the gate")
    session.graph = graph if _discovery_readers_bound(graph, after) else None
    session.readers = after
    return result


@dataclass
class DiscoverySession:
    graph: Optional[ls.Graph] = field(default=None, init=False)
    tip: str = field(default="", init=False)
    remaining_compositions: int = field(default=3, init=False)
    owner_refresh_tests: Set[str] = field(default_factory=set, init=False)
    readers: Optional[tuple] = field(default=None, init=False, repr=False)


    def compose(self, landing: "LandingRange") -> None:
        if self.remaining_compositions == 0:
            raise LandingUnjudged("discovery composition limit reached: " + landing.why)
        _check_discovery_interpreter()
        readers_were_bound = self.readers == _discovery_reader_identity()
        self.owner_refresh_tests.update(_compose_discovery(landing, self.tip) or ())
        # Composition already rejects executable reader changes, allowing only
        # its reviewed literal ownership-table refresh. Retain ordinary package
        # scan reuse across that existing transition, never arbitrary hot reload.
        if readers_were_bound:
            self.readers = _discovery_reader_identity()
        self.remaining_compositions -= 1


class DiscoveryProfile(Enum):
    FULL = "full"
    DEVELOPMENT = "development"


@dataclass
class DeclaredDevelopmentSelection(ls.Selection):
    """Fresh registered owner checks, with no full reachability attestation."""


class DevelopmentReachabilityRequired(RuntimeError):
    """A declared owner's actual checks also consume full compiler inputs."""


def declared_development_selection(graph, base, changed, in_place):
    import land_development
    if not land_development.has_declared_source_ownership(graph.index, changed, base):
        raise LandingUnjudged("declared development ownership does not cover this source delta")
    selection = DeclaredDevelopmentSelection(base, graph.index.rev, changed, [], in_place=in_place)
    scope = land_development.scope(graph, selection)
    if scope.errors:
        raise LandingUnjudged("declared development ownership refused: " + "; ".join(scope.errors))
    registered = {*land_development.INTEGRATION_RECIPES, land_development.EXIT_RECIPE}
    if scope.local_git_import or not set(scope.recipes) <= registered:
        raise DevelopmentReachabilityRequired("declared owner requires unknown compiler/recipe reachability")
    return selection


def development_discovery_inputs(base, head, *, progress=None, checkout=None):
    """Refuse impossible development scopes before scanning package sources.

    This is only a negative filter over the same immutable tree diff used by
    discovery. A possible scope still needs its existing ownership, graph and
    semantic checks; no result here selects a leg or grants a diagnostic SKIP.
    """
    import land_development
    ls._report_discovery(progress, "declared index", "start")
    base_sha = resolve_base(base)
    index = ls.TreeIndex.load(str(REPO_ROOT), head)
    ls._report_discovery(progress, "declared index", "complete", tracked_entries=len(index.entries))
    changed = ls.changed_paths(str(REPO_ROOT), base_sha, index.rev)
    # An empty committed diff cannot describe a candidate still in the index
    # or worktree. Explicit historical heads and clean diagnostics retain
    # their full stated discovery; this grants no eligibility or SKIP. The
    # subject is the checkout when it names HEAD, or when the caller says so:
    # discover_landing binds an implicit HEAD to the transaction's sha, and a
    # bound sha is still this checkout, unlike a sha a person states.
    if checkout is None:
        checkout = head == "HEAD"
    if not changed and checkout and git(
            "status", "--porcelain", "--untracked-files=no", "--ignore-submodules=untracked"):
        raise LandingUnjudged("empty committed development subject with uncommitted tracked changes; "
                              "commit first so the candidate is in the stated tree diff")
    if not land_development.may_have_scope(changed):
        unsupported = [path for path in changed if not land_development.may_have_scope([path])]
        raise LandingUnjudged("development scope refused: unsupported changed owner/input: "
                              + "; ".join(unsupported[:5]))
    return base_sha, index, changed


def compute_discovery(base, head, verify, previous, profile, *, progress=None, checkout=None):
    if profile is DiscoveryProfile.DEVELOPMENT:
        import land_development
        if progress is None:
            base_sha, index, changed = development_discovery_inputs(base, head, checkout=checkout)
        else:
            base_sha, index, changed = development_discovery_inputs(base, head, progress=progress, checkout=checkout)
        if land_development.has_declared_source_ownership(index, changed, base_sha):
            ls._report_discovery(progress, "declared manifest graph", "start")
            graph = ls.build_manifest_graph(index)
            ls._report_discovery(progress, "declared manifest graph", "complete", packages=len(graph.packages))
            ls._report_discovery(progress, "declared selection", "start")
            try:
                selection = declared_development_selection(
                    graph, base_sha, changed, in_place_changes(str(REPO_ROOT), base_sha, index.rev))
            except DevelopmentReachabilityRequired:
                ls._report_discovery(progress, "declared selection", "full graph required")
                pass
            else:
                ls._report_discovery(progress, "declared selection", "complete", changed_paths=len(changed))
                return graph, selection, base_sha
    if progress is not None:
        return compute(base, head, verify, previous, progress=progress)
    return compute(base, head, verify, previous)


def _reader_ast(source: bytes) -> str:
    # Parse bytes so Python's encoding declaration has its real meaning.
    # Keep every executable/data node, docstring and type comment. Source
    # locations are diagnostics, as in the existing ownership-data proof.
    return ast.dump(ast.parse(source, type_comments=True), include_attributes=False)


def _compose_discovery(landing: "LandingRange", previous_tip: str = "") -> Set[str]:
    """Normal composition only for explicit land, before any validation leg."""
    if not landing.tip or not landing.remote:
        raise LandingUnjudged(landing.why or "remote main cannot be bound")
    environment = git_query_env()
    def query(*args, timeout=30):
        done = _git_ask(REPO_ROOT, environment, *args, timeout=timeout)
        if done.returncode:
            raise LandingUnjudged(f"discovery Git operation failed: {_git_said(done)}")
        return done.stdout.strip()
    def tracked_changes():
        # Unlike the ref and object lookups here, a status stats every tracked
        # file of the checkout and of each submodule, which beside other builds
        # outlasts a lookup's bound. It has the bound of the merge it guards, and
        # it takes no index lock: a status that is ended must not leave
        # `index.lock` behind to fail the next Git command in this checkout.
        return query("--no-optional-locks", "status", "--porcelain", "--untracked-files=no",
                     "--ignore-submodules=none", timeout=remote_tips.FETCH_TIMEOUT_S)
    head = query("rev-parse", "--verify", "HEAD^{commit}")
    if landing.head != head:
        raise LandingUnjudged("HEAD changed during discovery; refusing composition")
    if tracked_changes():
        raise LandingUnjudged("discovery cannot compose a dirty source tree")
    # Fetch the authenticated original snapshot, then merge only that exact
    # object. A changing tracking ref never substitutes another destination.
    fetched = remote_tips.fetch_exact_source(landing.remote, REPO_ROOT, landing.tip, env=environment)
    if fetched.returncode:
        raise LandingUnjudged(f"discovery source intake failed: {_git_said(fetched)}")
    if query("cat-file", "-t", landing.tip) != "commit":
        raise LandingUnjudged("discovery source intake did not retain the exact commit")
    if previous_tip and _git_ask(REPO_ROOT, git_query_env(), "merge-base", "--is-ancestor",
                                previous_tip, landing.tip).returncode != 0:
        raise LandingUnjudged("remote main no longer extends the discovery snapshot")
    common = query("merge-base", head, landing.tip)
    incoming = set(ls.changed_paths(str(REPO_ROOT), common, landing.tip))
    changed_readers = incoming.intersection(_loaded_discovery_readers())
    import land_development
    # The selector's ownership tables are the row table's, so that file is the
    # data reader; land_select.py itself is now code alone and must not change.
    data_readers = {
        ls.LAND_ROWS_FILE: (ls, _selection_owner_data),
        "scripts/lib/land_development.py": (land_development, _program_owner_data),
    }
    # A maintained Python reader whose entire AST is identical needs no
    # reload. This is not a table/statement exemption: changed executable
    # code or data still requires a fresh process. Unknown transitive readers
    # retain that refusal even when a textual edit looks harmless.
    trivia_readers = changed_readers - data_readers.keys()
    declared_readers = set(GATE_FILES) | set(IR_DIAGNOSTIC_READERS)
    if trivia_readers - declared_readers:
        raise LandingUnjudged("incoming main changes a loaded gate reader; compose and restart the gate")
    trivia_sources = {}
    if trivia_readers:
        try:
            original_index = ls.TreeIndex.load(str(REPO_ROOT), common)
            incoming_index = ls.TreeIndex.load(str(REPO_ROOT), landing.tip)
            base_sources = original_index.read_blobs(sorted(trivia_readers))
            incoming_sources = incoming_index.read_blobs(sorted(trivia_readers))
        except (OSError, KeyError, RuntimeError, ValueError) as error:
            raise LandingUnjudged("incoming loaded reader source could not be bound") from error
        for path in sorted(trivia_readers):
            try:
                mode = original_index.entries[path][0]
                if (not path.endswith(".py") or mode not in ("100644", "100755")
                        or incoming_index.entries[path][0] != mode):
                    raise ValueError("reader is not unchanged regular Python source")
                original_mode = (REPO_ROOT / path).lstat().st_mode
                if not stat.S_ISREG(original_mode):
                    raise ValueError("loaded reader is not regular source")
                original = (REPO_ROOT / path).read_bytes()
                if path in _GATE_SNAPSHOT and hashlib.sha256(original).hexdigest() != _GATE_SNAPSHOT[path]:
                    raise ValueError("reader differs from its loaded snapshot")
                if _reader_ast(base_sources[path]) != _reader_ast(incoming_sources[path]):
                    raise ValueError("incoming reader executable/data AST changed")
                # Local implementation work need not already be on main.
                # Preserve its complete loaded shape across the actual merge.
                trivia_sources[path] = (_reader_ast(original), original_mode)
            except (OSError, KeyError, ValueError, SyntaxError, UnicodeError) as error:
                raise LandingUnjudged("incoming main changes a loaded gate reader; compose and restart the gate") from error
    try:
        old_readers = {path: _data_reader_text(path) for path in changed_readers & data_readers.keys()}
    except (OSError, ValueError) as error:
        raise LandingUnjudged("incoming main changes a loaded gate reader; compose and restart the gate") from error
    merged = remote_tips._run(["git", "-C", str(REPO_ROOT), "merge", "--no-edit", landing.tip],
                              timeout=remote_tips.FETCH_TIMEOUT_S, env=environment, cwd=REPO_ROOT)
    if merged.returncode:
        raise LandingUnjudged(f"discovery composition failed: {_git_said(merged)}")
    if query("rev-parse", "--verify", "HEAD^{commit}") == head:
        raise LandingUnjudged("discovery composition made no progress: " + landing.why)
    if tracked_changes():
        raise LandingUnjudged("discovery composition left tracked source changes or unsynchronized "
                              "submodule worktrees; materialize the exact committed pins before rediscovery")
    # Bookend the actual merged source before changing any loaded identity
    # or ownership binding. It must preserve all local executable/data nodes,
    # too; a remote-only blob cannot describe the local implementation.
    for path, (original_shape, original_mode) in trivia_sources.items():
        try:
            if (REPO_ROOT / path).lstat().st_mode != original_mode:
                raise ValueError("merged reader mode changed")
            composed_source = (REPO_ROOT / path).read_bytes()
            if _reader_ast(composed_source) != original_shape:
                raise ValueError("merged reader executable/data AST changed")
        except (OSError, ValueError, SyntaxError, UnicodeError) as error:
            raise LandingUnjudged("composed reader differs from its proved loaded code") from error
        trivia_sources[path] = hashlib.sha256(composed_source).hexdigest()
    updates = []
    refresh_tests = set()
    for path, old_source in sorted(old_readers.items()):
        module, decode = data_readers[path]
        try:
            old_code, old_tables, old_aliases = decode(old_source)
            new_code, new_tables, new_aliases = decode(_data_reader_text(path))
            if old_code != new_code:
                raise ValueError("reader code, or row-table data that is not refreshed, changed")
            if decode is _program_owner_data and any(
                    new_tables[name].get(key) != value
                    for name, rows in old_tables.items() for key, value in rows.items()):
                raise ValueError("required original program ownership row changed")
            if any(getattr(module, name, None) != value
                   for name, value in {**old_aliases, **new_aliases}.items()):
                raise ValueError("loaded ownership alias differs from its literal declaration")
            if any(getattr(module, name, None) != value for name, value in old_tables.items()):
                raise ValueError("loaded ownership tables differ from the original source")
        except (OSError, ValueError, SyntaxError, TypeError) as error:
            raise LandingUnjudged("incoming main changes a loaded gate reader; compose and restart the gate") from error
        for name, rows in new_tables.items():
            for key, modules in rows.items():
                if old_tables[name].get(key) != modules:
                    refresh_tests.update(modules)
        updates.append((path, module, new_tables))
    # Validate every reader before replacing any loaded binding. Discovery
    # recomputes selection and required legs; this imports no test verdict.
    for path, module, new_tables in updates:
        for name, value in new_tables.items():
            setattr(module, name, value)
        if path in _GATE_SNAPSHOT:
            _GATE_SNAPSHOT[path] = sha256_file(REPO_ROOT / path)
    for path, digest in trivia_sources.items():
        if path in _GATE_SNAPSHOT:
            _GATE_SNAPSHOT[path] = digest
    _refresh_discovery_interpreter_readers(changed_readers)
    return refresh_tests


def discover_landing(base: Optional[str], head: str = "HEAD", verify: bool = False,
                     compose: bool = False,
                     session: Optional[DiscoverySession] = None,
                     profile: DiscoveryProfile = DiscoveryProfile.FULL) -> Tuple[ls.Graph, ls.Selection, str, "LandingRange"]:
    """Capture an immutable source range. Only explicit land may compose.

    Package scan reuse is in-process and content-bound. Selection and native
    resolver checking always run on the newly composed immutable source.
    Existing leg keys still decide whether any prior execution is reusable.
    """
    session = session if session is not None else DiscoverySession()
    # One session owns the bound across discovery and publication retries.
    for refresh in range(4):
        _check_cancellation()
        before = read_landing(head=head)
        _check_cancellation()
        if not before.stated:
            if not compose:
                raise LandingUnjudged(before.why)
            session.compose(before)
            head = "HEAD"
            continue
        session.tip = before.tip
        started = time.monotonic()
        progress = _DiscoveryProgress(started=started)
        progress("planning", "start", {"attempt":refresh + 1})
        # Shared tracking refs may move while another worktree fetches. Bind
        # the implicit landing subject to this transaction's authenticated tip.
        graph, selection, selected_base = _compute_in_session(session, base if base is not None else before.tip,
                                                             before.head, verify, profile, progress=progress,
                                                             checkout=head == "HEAD")
        # The original operation has returned with its owned work retired.
        # Recorded cancellation must not begin another remote probe/merge.
        _check_cancellation()
        selection.owner_refresh_tests = tuple(sorted(session.owner_refresh_tests))
        stored = graph.__dict__.get("_stored_tree") if isinstance(graph, ls.Graph) else None
        selection.discovery = discovery_record(progress, graph)
        progress.write(f"land-gate: discovery {selection.head[:12]} in {time.monotonic() - started:.2f}s; "
                       f"{len(graph.reused_packages)}/{len(graph.packages)} package scans and "
                       f"{graph.reused_tokenizations} tokenizations and "
                       f"{graph.__dict__.get('_reused_blob_facts', 0)} blob facts reused by exact inputs"
                       + (f", from the stored graph of tree {stored[:12]}" if stored else ""))
        if selection.discovery["phases"]:
            progress.write("land-gate: discovery phases " + " ".join(
                f"{phase.replace(' ', '-')}={seconds:.2f}s"
                for phase, seconds in selection.discovery["phases"].items()))
        # Qualify this immutable source before chasing another publication.
        # The live push rows and final preflight still require the current
        # destination, composition, re-selection and exact input keys. Checking
        # it here instead can consume every discovery attempt without running
        # a single source check on a busy main branch.
        if compose:
            return graph, selection, selected_base, before
        after = read_landing(head=selection.head)
        _check_cancellation()
        if after.stated:
            return graph, selection, selected_base, after
        raise LandingUnjudged(after.why + "; discovery source remains unchanged")


def ir_diagnostic_selection(base: Optional[str], head: str) -> Tuple[ls.Selection, str]:
    """Record the subject without interpreting unrelated Rust build inputs.

    The explicit checker is always selected, has no cache key, and inventories
    its own complete manifest/semantic inputs. This is not a reachability answer
    for any other leg. The caller must first bind the audited reader versions.
    """
    base_sha = resolve_base(base)
    changed = ls.changed_paths(str(REPO_ROOT), base_sha, head)
    return ls.Selection(base_sha, head, changed, []), base_sha


def in_place_changes(repo: str, base: str, head: str) -> Set[str]:
    """ls.changed_in_place, or no statuses at all when git cannot answer: a
    listing read then counts every change, as a content read does."""
    try:
        return ls.changed_in_place(repo, base, head)
    except (RuntimeError, ValueError, OSError):
        return set()


def hook_mode_line(hook: PushHook, legs: List[Leg], landing: Optional["LandingRange"] = None) -> str:
    """The one line saying which mode applies, which rule decided it and why
    (LAND-GATE-HOOKLESS-1)."""
    crates = next((l for l in legs if l.id == "crates-tests"), None)
    limited = sorted(crates.host_limited) if crates else []
    not_here = (f"; {len(limited)} member(s) this host cannot build ({', '.join(limited[:4])}"
                f"{', ...' if len(limited) > 4 else ''}) are NOT RUN here, as in the hook's lane on this host"
                if limited else "")
    uncovered = sorted(crates.not_covered) if crates else []
    not_here += (f"; {len(uncovered)} [workspace] crate(s) nested inside a crates/ member that the change touches "
                 f"or reaches ({', '.join(uncovered[:4])}{', ...' if len(uncovered) > 4 else ''}) are NOT COVERED: "
                 "the crates lane tests no such crate, so nothing here builds or tests them" if uncovered else "")
    if hook.active and not hook.runs(CRATES_ROW):
        return (f"LAND-GATE: the pre-push hook is installed in this clone and answers for this landing "
                f"({hook.why}): it runs every push-profile row on the push, so push-rows does not run here. "
                f"Its profile leaves this gate the covered rows it lacks ({hook.gaps}): crates-tests runs the "
                f"{len(crates.hookless_members) if crates else 0} touched crates/ member(s) and "
                f"{len(crates.hookless_instruments) if crates else 0} moved instrument(s) here{not_here}. Push the "
                "landing from THIS worktree and shell without --no-verify: another clone or shell may run no hook "
                "(this shell's git environment was read; another's was not)")
    if hook.active:
        beyond = crates.beyond_push if crates else []
        also = (f"; crates-tests runs the {len(beyond)} touched member(s) the landing push does not carry "
                f"({', '.join(beyond[:4])}{', ...' if len(beyond) > 4 else ''}): the hook's lane tests only what "
                "the push carries" if beyond else "")
        return (f"LAND-GATE: the pre-push hook is installed in this clone and answers for this landing "
                f"({hook.why}); it tests the crates/ members the landing push touches and runs the push-profile "
                f"rows on the push, so this gate does not{also}{not_here}. Push the landing from THIS worktree and "
                f"shell without --no-verify: another clone or shell may run no hook (this shell's git environment "
                f"was read; another's was not)")
    added = crates.hookless_members if crates else []
    moved = crates.hookless_instruments if crates else []
    named = f" ({', '.join(added[:6])}{', ...' if len(added) > 6 else ''})" if added else ""
    hosts = f" ({', '.join(moved[:4])}{', ...' if len(moved) > 4 else ''})" if moved else ""
    head = (f"the pre-push hook is not installed in this clone ({hook.why})" if hook.fired == "not-installed"
            else f"the pre-push hook does not answer for this landing (rule {hook.fired}: {hook.why})")
    onto = (f" (origin's main tip {landing.tip[:12]}...{landing.head[:12]})"
            if landing is not None and landing.tip and landing.changed is not None else "")
    return (f"LAND-GATE: {head}; crates-tests also runs the hook lane over the landing range{onto}: the "
            f"{len(added)} touched crates/ member(s){named} the hook's lane would have tested, and {len(moved)} "
            f"moved instrument(s){hosts} under its instrument rules{not_here}; push-rows runs first, the "
            f"push-profile rows no other leg covers, on this checkout's HEAD onto origin's main tip")


# These legs inspect the selected source and never stand in for a push check.
# Keep the set explicit: an unreviewed future leg still needs a stated landing.
SOURCE_DIAGNOSTIC_LEGS = frozenset({"tcb-panic-ratchet", "ir-cohort"})


# This read-set audit is valid only for these executor/import versions. A new
# reader falls back to complete physical checking until its reads are audited.
# Each module a reader imports and runs is one: land_select's lexer (rust_lex)
# and the crates lane build_legs loads (check_crates_tests_scoped, and its
# crates_tests_time) were not (round 6 of LAND-GATE-EW1-FOLLOWUP-REVIEW-4, the
# IR reader audit), and native_serial was not when efadef1b78 moved the managed
# serial admission into it ((12)). crates_lane_members is one too: land_select and the
# crates lane import it for the lane's own member set (LAND-GATE-HOOKLESS-1 round 5).
IR_DIAGNOSTIC_READ_SET = "scripts/ir_cohort_physical_read_set.json"
IR_DIAGNOSTIC_READERS = frozenset({
    "scripts/land_gate.py", "scripts/check_ir_cohort.py", "scripts/lib/remote_tips.py", "scripts/lib/remote_operation.py",
    "scripts/lib/host_budget.py", "scripts/lib/land_select.py", "scripts/lib/landing_targo.py",
    "scripts/lib/land_manifest.py", "scripts/lib/land_development.py", "scripts/lib/rust_lex.py",
    "scripts/check_crates_tests_scoped.py", "scripts/lib/crates_tests_time.py",
    "scripts/mint_seed_support.py", "src/bootstrap/stage0_identity.py", "scripts/lib/native_serial.py",
    "scripts/lib/crates_lane_members.py",
    "scripts/lib/checkout_inputs.py",
})


def ir_diagnostic_readers_match(revision: str) -> bool:
    """Bind every audited reader, including this module, without a self-hash cycle.

    The separate manifest is read from the selected Git tree, never trusted
    from its mutable worktree copy. Its physical copy is checked with the
    other diagnostic inputs before execution and publication.
    """
    env = dict(git_query_env(), GIT_NO_REPLACE_OBJECTS="1")
    manifest = _git_ask(REPO_ROOT, env, "show", revision + ":" + IR_DIAGNOSTIC_READ_SET, timeout=10)
    if manifest.returncode:
        return False
    def unique_object(pairs):
        result = {}
        for key, value in pairs:
            if key in result:
                raise ValueError("duplicate read-set field")
            result[key] = value
        return result
    try:
        document = json.loads(manifest.stdout, object_pairs_hook=unique_object)
    except (ValueError, TypeError):
        return False
    if (not isinstance(document, dict) or set(document) != {"schema", "readers"}
            or document["schema"] != "trust.land-gate.ir-cohort-read-set.v1"
            or not isinstance(document["readers"], dict)
            or set(document["readers"]) != IR_DIAGNOSTIC_READERS
            or any(not isinstance(oid, str) or not re.fullmatch(r"[0-9a-f]{40}(?:[0-9a-f]{24})?", oid)
                   for oid in document["readers"].values())):
        return False
    result = _git_ask(REPO_ROOT, env, "ls-tree", "-r", "-z", revision,
                      "--", *sorted(IR_DIAGNOSTIC_READERS), timeout=10)
    if result.returncode:
        return False
    actual = {}
    for row in result.stdout.split("\0"):
        if not row:
            continue
        header, tab, path = row.partition("\t")
        fields = header.split()
        if not tab or len(fields) != 3 or fields[1] != "blob":
            return False
        actual[path] = fields[2]
    return actual == document["readers"] and not ir_diagnostic_import_shadowed(revision, env)


# The directories the IR-only run imports from: land_gate.py and
# check_ir_cohort.py run as scripts (sys.path[0] is scripts/), and each puts
# scripts/lib first.
IR_DIAGNOSTIC_IMPORT_DIRS = ("scripts", "scripts/lib")


def ir_diagnostic_import_shadowed(revision: str, env: Dict[str, str]) -> bool:
    """Whether the commit holds code Python may run in place of a reader or
    of a standard-library module during the IR-only run; True also when the
    listing cannot be read. Such code runs in-process unpinned, and may read
    outside the IR physical scope. It is, in a directory the run imports
    from or a reader's own directory:
    - a `__pycache__` directory: its bytecode stands for a module's source
      (an unchecked-hash `.pyc` is never compared with it), for a reader
      loaded by path (`stage0_identity.py`) too;
    - a module named (case-folded) as a standard-library module, any module
      the interpreter's own library directories hold included
      (`_sysconfigdata_*`, which `sysconfig` imports by a computed name):
      `<name>.py`, an extension module or `.pyc`, or a package, a gitlink
      being one too;
    - a module named as any reader, in either import directory, other than
      that reader itself: scripts/lib precedes scripts/ on the search path.
    (Round 7 of LAND-GATE-EW1-FOLLOWUP-REVIEW-4: a tracked scripts/shlex.py
    ran inside land_gate.py with the narrowed scope kept; round 8: tracked
    bytecode, a gitlink package, a scripts/lib module named for a scripts/
    reader and `_sysconfigdata_*` still did.)"""
    directories = sorted(set(IR_DIAGNOSTIC_IMPORT_DIRS)
                         | {reader.rpartition("/")[0] for reader in IR_DIAGNOSTIC_READERS})
    listing = _git_ask(REPO_ROOT, env, "ls-tree", "-z", "--full-tree", revision, "--",
                       *(d + "/" for d in directories), timeout=10)
    if listing.returncode:
        return True
    names = python_standard_modules()
    readers: Dict[str, Set[str]] = {}
    for reader in IR_DIAGNOSTIC_READERS:
        directory, _slash, base = reader.rpartition("/")
        if directory in IR_DIAGNOSTIC_IMPORT_DIRS:
            readers.setdefault(_ir_fold(base.removesuffix(".py")), set()).add(reader)
    for row in listing.stdout.split("\0"):
        if not row:
            continue
        header, tab, path = row.partition("\t")
        fields = header.split()
        if not tab or len(fields) != 3:
            return True
        directory, _slash, base = path.rpartition("/")
        if _ir_fold(base) == "__pycache__":
            return True
        if directory not in IR_DIAGNOSTIC_IMPORT_DIRS:
            continue
        # A directory or a gitlink may be a package (importable_name).
        stem = importable_name(base, fields[1] in ("tree", "commit"))
        if stem is None:
            continue
        if stem in names or (stem in readers and path not in readers[stem]):
            return True
    return False


# The names an interpreter on PATH reports as its standard library
# (python_standard_modules), written for any Python from 2.7 on: those it
# lists or builds in, and every module its library directories hold.
_STANDARD_QUERY = """\
import os, sys, sysconfig
names = set(sys.builtin_module_names) | set(getattr(sys, "stdlib_module_names", ()))
paths = sysconfig.get_paths()
for root in set([paths.get("stdlib"), paths.get("platstdlib")]) - set([None]):
    for directory in (root, os.path.join(root, "lib-dynload")):
        try:
            names.update(entry.partition(".")[0] for entry in os.listdir(directory))
        except OSError:
            pass
sys.stdout.write("\\n".join(sorted(name for name in names if name)))
"""
# An executable a command starts by the name `python`, `python3` or
# `python3.N` (a free-threaded build adds `t`).
PYTHON_EXECUTABLE = re.compile(r"python(?:\d+(?:\.\d+)*t?)?")
# The running interpreter's names, then each interpreter's by
# (real path, inode, size, mtime): read once per process.
_STANDARD_MODULES: List[FrozenSet[str]] = []
_INTERPRETER_MODULES: Dict[Tuple[str, int, int, int], FrozenSet[str]] = {}


def python_interpreters() -> List[str]:
    """Every Python a leg or push row may start by name, by real path: each
    PYTHON_EXECUTABLE in an absolute directory of the gate's PATH (rows and
    legs inherit it; the pre-push hook's `python3 scripts/...` rows resolve
    through it) or of SEALED_PATH (the sealed leg's, and the `/usr/bin:/bin`
    verify.executes puts first)."""
    found: Dict[str, None] = {}
    for directory in [*os.environ.get("PATH", os.defpath).split(os.pathsep), *SEALED_PATH]:
        if not os.path.isabs(directory):
            continue
        try:
            entries = sorted(os.listdir(directory))
        except OSError:
            continue
        for name in entries:
            path = os.path.join(directory, name)
            if PYTHON_EXECUTABLE.fullmatch(name) and os.path.isfile(path) and os.access(path, os.X_OK):
                found.setdefault(os.path.realpath(path))
    return list(found)


def _interpreter_standard_modules(path: str) -> FrozenSet[str]:
    """The standard-library names the interpreter `path` reports
    (_STANDARD_QUERY), case-folded. It runs with -E -S (no PYTHON* variable,
    no site) in an empty directory, so the query imports nothing a checkout
    holds. An interpreter that does not answer reports nothing: it runs no
    Python under these flags, so it imports no shadow either."""
    try:
        st = os.stat(path)
    except OSError:
        return frozenset()
    key = (path, st.st_ino, st.st_size, st.st_mtime_ns)
    if key in _INTERPRETER_MODULES:
        return _INTERPRETER_MODULES[key]
    names: FrozenSet[str] = frozenset()
    with tempfile.TemporaryDirectory(prefix="land-gate-stdlib.") as empty:
        try:
            done = subprocess.run([path, "-E", "-S", "-c", _STANDARD_QUERY], cwd=empty, stdin=subprocess.DEVNULL,
                                  capture_output=True, timeout=60)
        except (OSError, subprocess.SubprocessError):
            done = None
    if done is not None and done.returncode == 0:
        names = frozenset(_ir_fold(name) for name in done.stdout.decode("utf-8", "replace").split("\n") if name)
    _INTERPRETER_MODULES[key] = names
    return names


def python_standard_modules() -> FrozenSet[str]:
    """Every standard-library module name, case-folded, of every Python a
    leg or push row may start: the running interpreter's (those it lists,
    and every module its library directories hold: sys.stdlib_module_names
    omits names computed per platform, such as
    `_sysconfigdata_<abi>_<platform>`), each interpreter's on PATH
    (python_interpreters; a push row's `python3` resolves to another
    release, whose standard library holds modules this one's lacks, such as
    3.9's `_compression`), and the names `site` imports (`sitecustomize`,
    `usercustomize`)."""
    if not _STANDARD_MODULES:
        names = set(sys.stdlib_module_names) | {"sitecustomize", "usercustomize"}
        paths = sysconfig.get_paths()
        for root in {paths.get("stdlib"), paths.get("platstdlib")} - {None}:
            for directory in (root, os.path.join(root, "lib-dynload")):
                try:
                    entries = os.listdir(directory)
                except OSError:
                    continue
                names.update(entry.partition(".")[0] for entry in entries)
        _STANDARD_MODULES.append(frozenset(_ir_fold(name) for name in names if name))
    names = set(_STANDARD_MODULES[0])
    for interpreter in python_interpreters():
        names |= _interpreter_standard_modules(interpreter)
    return frozenset(names)


IMPORT_SUFFIX = re.compile(r"pyw?|pyc|(?:.*\.)?(?:so|pyd)")


def importable_name(base: str, package: bool) -> Optional[str]:
    """The case-folded module name under which Python may import the entry
    `base` of a directory it imports from, or None. A directory (`package`;
    a gitlink is one once populated) is a package, regular or namespace, read
    under its name before any dot; a file is a module only by an import
    suffix (IMPORT_SUFFIX: source `.py`/`.pyw`, sourceless `.pyc`, an
    extension module's `.so`/`.pyd` after any ABI tag)."""
    stem, dot, suffix = base.partition(".")
    if not package and not (dot and IMPORT_SUFFIX.fullmatch(_ir_fold(suffix))):
        return None
    return _ir_fold(stem) or None


# LAND-GATE-PY-SHADOW-1. A checkout pass binds tracked files only, but Python
# imports from a directory whatever it holds: an untracked or ignored entry
# can run in place of a committed module, or of a standard-library one, while
# every tracked byte still matches, and the leg's PASS is false. The
# directories a leg or a push row imports from, read from how each starts
# Python (python_import_roots):
# - the repository root: `land_gate.py validation-tests` puts it first to
#   load scripts.tests.<module> (cmd_validation_tests); tests insert it
#   (REPO_ROOT, ROOT); `python3 -` and `python3 -c` started in it (the
#   pre-push hook's here-documents, every row and leg runs from the root)
#   hold it as sys.path[0];
# - every tracked directory under scripts/: scripts/ is a package
#   (scripts/__init__.py) and sys.path[0] of every scripts/*.py; programs and
#   tests put scripts/lib, scripts/tests, scripts/trust_core, their own and
#   their parents' directories first; each scripts/**/<x>.py run as a script
#   holds its own directory as sys.path[0];
# - src/bootstrap, which x.py inserts (the bootstrap-tests, tidy and
#   native-targo-tests legs run x.py from the root);
# - every other tracked directory holding a tracked .py file: a script run
#   there holds it as sys.path[0], and its package's modules are found in it.
# The first three share search paths, in orders their programs choose, so a
# name tracked in any of them counts in each (PYTHON_SHARED_ROOTS); any other
# directory counts its own. A `.pth` file is read only in a site directory
# (site.addsitedir), which none of these is, so it is no entry here. A
# populated submodule is checked the same way from its own root, with no
# shared directories. Not refused: an untracked module under a name that
# neither the commit nor the standard library holds; it runs only where
# tracked code imports a name its commit lacks (an optional import such as
# `tomli`, which some scripts fall back to without tomllib).
PYTHON_SHARED_ROOTS = (".", "src/bootstrap")
PYTHON_SHARED_TREE = "scripts"
# A name Python imports from any package directory, whatever it holds.
PACKAGE_MODULES = frozenset({"__init__", "__main__"})
# Code objects compared field by field (same_code): every field the
# interpreter executes or reports, not co_filename, which the loader rewrites
# to the source's own path.
_CODE_FIELDS = ("co_argcount", "co_posonlyargcount", "co_kwonlyargcount", "co_nlocals", "co_stacksize",
                "co_flags", "co_firstlineno", "co_code", "co_names", "co_varnames", "co_freevars",
                "co_cellvars", "co_name", "co_qualname", "co_linetable", "co_exceptiontable")
# (sha256 of the bytecode file, sha256 of the source, optimization level) ->
# whether the bytecode is the source's code: the same bytes give the same
# answer, so each distinct file is compiled once per process.
_BYTECODE_VERDICTS: Dict[Tuple[str, str, int], bool] = {}


def _directory_children(committed: Iterable[str]) -> Dict[str, Set[str]]:
    """Each tracked directory ("." the root) -> the names of its tracked
    entries, files and directories."""
    children: Dict[str, Set[str]] = {}
    for path in committed:
        child = path
        while True:
            parent, _slash, name = child.rpartition("/")
            parent = parent or "."
            known = parent in children
            children.setdefault(parent, set()).add(name)
            if known or parent == ".":
                break
            child = parent
    return children


def python_import_roots(committed: Dict[str, Tuple[str, str]], children: Dict[str, Set[str]],
                        top: bool) -> Tuple[Set[str], Set[str]]:
    """(the shared import directories, every import directory) of a
    repository whose commit holds `committed` (the comment above
    PYTHON_SHARED_ROOTS); `top` is the checkout itself, not a submodule."""
    shared: Set[str] = set()
    if top:
        shared = {d for d in children if d in PYTHON_SHARED_ROOTS or d == PYTHON_SHARED_TREE
                  or d.startswith(PYTHON_SHARED_TREE + "/")}
    sources = {path.rpartition("/")[0] or "." for path, (mode, _oid) in committed.items()
               if path.endswith(".py") and mode != "160000"}
    return shared, shared | sources


def same_code(held: object, compiled: object) -> bool:
    """Whether two compiled constants are one program: code objects field by
    field (_CODE_FIELDS), containers (a tuple, a frozenset, a slice, which
    Python 3.14 folds `a[1:2]` into) element by element, the rest by exact
    type and value (1, 1.0 and True differ, and so do 0.0 and -0.0; so do
    slice(1, 2) and slice(True, 2), which `==` holds equal)."""
    if type(held) is not type(compiled):
        return False
    if isinstance(held, slice):
        return same_code((held.start, held.stop, held.step), (compiled.start, compiled.stop, compiled.step))
    if isinstance(held, types.CodeType):
        return (all(getattr(held, f) == getattr(compiled, f) for f in _CODE_FIELDS)
                and same_code(held.co_consts, compiled.co_consts))
    if isinstance(held, tuple):
        return len(held) == len(compiled) and all(map(same_code, held, compiled))
    if isinstance(held, frozenset):
        return len(held) == len(compiled) and all(
            map(same_code, sorted(held, key=repr), sorted(compiled, key=repr)))
    if isinstance(held, (float, complex)):
        return repr(held) == repr(compiled)
    return held == compiled


def bytecode_problem(pyc: Path, source: Path, tag: str, optimize: int) -> Optional[str]:
    """Why Python could run `pyc` (a __pycache__ file for the tracked `source`
    under cache tag `tag` and optimization level `optimize`) in place of the
    source's own code, or None.

    An interpreter started with -E or -I ignores PYCACHE_ENV and reads the
    checkout's __pycache__, and the gate cannot add `-X pycache_prefix` to
    the command lines a leg's programs build. Refusing every __pycache__
    would refuse the bytecode those interpreters themselves write, from the
    commit's source, when started without -B. So the file is read as Python
    reads it: one Python ignores (short, unknown flags, a stale timestamp)
    is no problem; one it would load must hold exactly the code this
    interpreter compiles from the source (same_code). Bytecode of another
    interpreter (another cache tag or magic number) whose header could
    match cannot be compared here, and is refused."""
    try:
        data = pyc.read_bytes()
        raw = source.read_bytes()
        st = source.stat()
    except OSError:
        return None  # Python reads no bytecode it cannot open: it compiles the source
    stamp = ((int(st.st_mtime) & 0xFFFFFFFF).to_bytes(4, "little")
             + (st.st_size & 0xFFFFFFFF).to_bytes(4, "little"))
    flags = int.from_bytes(data[4:8], "little") if len(data) >= 16 else -1
    if tag != _ir_fold(sys.implementation.cache_tag) or data[:4] != importlib.util.MAGIC_NUMBER:
        # The header layouts since Python 3.3: a timestamp after the magic
        # number (3.3-3.6) or after the flags (3.7 on), or a source hash.
        if len(data) >= 12 and (data[4:12] == stamp or data[8:16] == stamp or flags in (1, 3)):
            return (f"bytecode for another interpreter ({tag}) whose header can match the source; "
                    f"this gate cannot compare it with the source")
        return None
    if flags < 0 or flags & ~0b11:
        return None  # Python rejects the header and compiles the source
    if not flags & 0b1 and data[8:16] != stamp:
        return None  # stale: Python compiles the source
    # A source-hash header is loaded unchecked under its own flag or
    # --check-hash-based-pycs never: compared whatever its hash says.
    key = (hashlib.sha256(data).hexdigest(), hashlib.sha256(raw).hexdigest(), optimize)
    same = _BYTECODE_VERDICTS.get(key)
    if same is None:
        try:
            held = marshal.loads(data[16:])
            with warnings.catch_warnings():
                warnings.simplefilter("ignore")
                compiled = compile(raw, str(source), "exec", dont_inherit=True, optimize=optimize)
            same = same_code(held, compiled)
        except (ValueError, EOFError, TypeError, SyntaxError, MemoryError, RecursionError):
            same = False
        _BYTECODE_VERDICTS[key] = same
    return None if same else "bytecode Python would load for the tracked source holds other code"


def _bytecode_source(name: str, sources: Set[str]) -> Optional[Tuple[str, str, int]]:
    """(the tracked source, case-folded cache tag, optimization level) a
    __pycache__ entry `name` is for (importlib's cache_from_source:
    `<stem>.<tag>[.opt-N].pyc` for `<stem>.py`), or None: no tracked source,
    or a level no interpreter flag selects. Compared case-folded (_ir_fold):
    the loader opens the cache path it builds with open(), so on a file
    system that folds case `PROBE.CPYTHON-314.OPT-1.PYC` is what it reads
    for `probe.py` under -O."""
    name = _ir_fold(name)
    if not name.endswith(".pyc"):
        return None
    for source in sorted(sources):
        stem = _ir_fold(source[:-len(".py")])
        if not name.startswith(stem + "."):
            continue
        parts = name[len(stem) + 1:-len(".pyc")].split(".")
        if len(parts) == 1 and parts[0]:
            return source, parts[0], 0
        if len(parts) == 2 and parts[0] and parts[1] in ("opt-1", "opt-2"):
            return source, parts[0], int(parts[1][-1])
    return None


def python_import_problem(repo: Path, committed: Dict[str, Tuple[str, str]], label: str,
                          top: bool) -> Optional[str]:
    """Why Python a leg or push row starts in `repo` (`label`; `top` is the
    checkout, not a populated submodule) could run code its commit, which
    holds `committed` (path -> (mode, oid)), does not, or None. In each
    import directory (python_import_roots) it refuses:
    - an untracked or ignored entry Python imports under the name of a
      standard-library module, of a module or package tracked there or (a
      shared directory) in any shared directory, or `__init__`/`__main__`
      (PACKAGE_MODULES): a package directory, regular or namespace (a
      package wins over a module beside it, and a namespace directory
      imports a standard-library name this platform lacks), an extension
      module (extension loaders come before source), a sourceless `.pyc`
      (loaded where no source is beside it) or a source; names compare
      case-folded (_ir_fold), as a case-insensitive file system or
      PYTHONCASEOK matches them, and an entry that is a tracked one's own
      file under another spelling is that entry;
    - an untracked __pycache__ file Python would load for a tracked source
      that is not exactly that source's code (bytecode_problem).
    An entry the directory cannot list is refused; an absent directory
    (sparse) holds nothing to import."""
    children = _directory_children(committed)
    shared, roots = python_import_roots(committed, children, top)
    standard = python_standard_modules() | PACKAGE_MODULES

    def path_of(directory: str, name: str) -> str:
        return name if directory == "." else directory + "/" + name

    def spelled(directory: str, name: str) -> str:
        return f"{label}/{path_of(directory, name)}"

    def tracked_names(directory: str) -> Set[str]:
        names = set()
        for name in children.get(directory, ()):
            path = path_of(directory, name)
            stem = importable_name(name, path in children or committed.get(path, ("",))[0] == "160000")
            if stem:
                names.add(stem)
        return names

    shared_names = set().union(*(tracked_names(d) for d in shared)) if shared else set()
    for directory in sorted(roots):
        here = repo if directory == "." else repo / directory
        try:
            entries = sorted(entry.name for entry in os.scandir(here))
        except (FileNotFoundError, NotADirectoryError):
            continue
        except OSError as exc:
            return f"cannot list the Python import directory {spelled(directory, '')!r} ({exc.strerror})"
        tracked = children.get(directory, set())
        folded = {_ir_fold(name): name for name in tracked}
        names = standard | (shared_names if directory in shared else tracked_names(directory))
        for name in entries:
            if name in tracked or _ir_fold(name) == "__pycache__":
                continue
            twin = folded.get(_ir_fold(name))
            if twin is not None:
                try:
                    if os.path.samestat(os.lstat(here / name), os.lstat(here / twin)):
                        continue
                except OSError:
                    pass
            package = os.path.isdir(here / name)
            stem = importable_name(name, package)
            if stem is not None and stem in names:
                return (f"untracked {'package' if package else 'module'} {spelled(directory, name)!r} shadows the module "
                        f"{stem!r}: Python a leg or push row starts imports it ahead of, or instead of, a tracked "
                        f"or standard-library module, and no checkout pass reads it (LAND-GATE-PY-SHADOW-1); "
                        f"remove it")
        sources = {name for name in tracked if name.endswith(".py")
                   and committed.get(path_of(directory, name), ("",))[0] in ("100644", "100755")}
        # Every spelling: on a file system that keeps case, `__PYCACHE__`
        # sorts ahead of the `__pycache__` Python reads.
        for cache_dir in (name for name in entries if sources and _ir_fold(name) == "__pycache__"):
            cache = here / cache_dir
            try:
                cached = sorted(entry.name for entry in os.scandir(cache))
            except (FileNotFoundError, NotADirectoryError):
                continue
            except OSError as exc:
                return f"cannot list the compiled-Python directory {spelled(directory, cache_dir)!r} ({exc.strerror})"
            held = children.get(path_of(directory, cache_dir), set())
            for name in cached:
                found = None if name in held else _bytecode_source(name, sources)
                if found is None:
                    continue
                source, tag, optimize = found
                problem = bytecode_problem(cache / name, here / source, tag, optimize)
                if problem:
                    return (f"untracked compiled Python {spelled(directory, cache_dir + '/' + name)!r}: {problem}; an "
                            f"interpreter started with -E or -I runs it in place of the tracked source "
                            f"(LAND-GATE-PY-SHADOW-1); remove it")
    return None


def ir_diagnostic_physical_input(path: str) -> bool:
    """Conservative physical read closure of explicit IR-only diagnostics.

    The executor reads tracked Cargo manifests, exclusions and waivers. Its
    semantic surfaces are read from immutable Git objects. Include all TOML,
    script and Cargo configuration inputs used by gate planning as well;
    excluded historical manifests cost little and need no second skip policy.
    This is never the physical scope of a normal run or a landing.
    """
    # Folded (_ir_fold): the readers open these names on a host whose file
    # system folds case and Unicode (APFS), so `src/Lib.rs` or `.GitAttributes`
    # is what a read of `src/lib.rs` or `.gitattributes` gets. (Round 7 of
    # LAND-GATE-EW1-FOLLOWUP-REVIEW-4: the scope was matched as spelled.)
    path = _ir_fold(path.removeprefix("./"))
    parts = path.split("/")
    # A .gitattributes anywhere: until LAND-IR-READER-GAPS-1 the selector's
    # `git grep -I` (land_select's _scanned_before) took binary marks from the
    # worktree's attribute files; it now reads the judged commit's from its
    # tree (_committed_attribute_git). They stay in the scope: checking them
    # physically only makes the run stricter, and no audit has shown that no
    # other git query of the run reads a worktree attributes file.
    # A crate root: gate planning's host limits read each crates-tests
    # member's src/lib.rs (check_crates_tests_scoped.apply_host_limits). (Round
    # 6 of LAND-GATE-EW1-FOLLOWUP-REVIEW-4, the IR reader audit.)
    return (path.startswith("scripts/") or path.endswith(".toml")
            or ".cargo" in parts or parts[-1] in {"cargo.lock", ".gitmodules", ".gitattributes"}
            or path == "src/lib.rs" or path.endswith("/src/lib.rs")
            or path in IR_DIAGNOSTIC_EXACT_INPUTS)


IR_DIAGNOSTIC_EXACT_INPUTS = frozenset({
    "rust-toolchain", "src/stage0", "src/bootstrap/stage0_identity.py",
    "docs/audits/first-party-constellation-exclusions-v1.json",
})


def _ir_fold(path: str) -> str:
    """`path` as a case- and normalization-insensitive file system compares it
    (Unicode canonical caseless matching: `Lib.rſ` is `lib.rs`)."""
    return unicodedata.normalize("NFD", unicodedata.normalize("NFD", path).casefold())


def ir_diagnostic_link_redirects(path: str) -> bool:
    """Whether a committed link at `path` could stand, in a path the IR-only
    run's readers open, for a component its physical scope names
    (ir_diagnostic_physical_input): a link named `src` (a crate root's
    `src/lib.rs`), `scripts`, or a directory above an exact input
    (`docs`, `docs/audits`, `src`, `src/bootstrap`). The scope's other names
    are a file's own (`.toml`, `Cargo.lock`, `.gitattributes`) or hold a
    `.cargo` component, so a link above them leaves the file selected, and a
    link at them is selected itself. (Round 7 of
    LAND-GATE-EW1-FOLLOWUP-REVIEW-4: `crates/a/src -> impl` and
    `docs/audits -> ../meta` hid edits the readers read.)"""
    path = _ir_fold(path.removeprefix("./"))
    return (path.split("/")[-1] == "src" or path == "scripts"
            or any(exact.startswith(path + "/") for exact in IR_DIAGNOSTIC_EXACT_INPUTS))


def source_diagnostic_only(only: Optional[Sequence[str]], land_transaction: bool) -> bool:
    return not land_transaction and bool(only) and set(only) <= SOURCE_DIAGNOSTIC_LEGS


def landing_refusal(hook: PushHook, landing: "LandingRange", *,
                    source_diagnostic: bool = False) -> Optional[str]:
    """Why `run` judges nothing before its first leg (round 3, D5), or None.

    A leg here stands in for each covered row (HOOK_ROWS_COVERED) the hook
    does not run (`hook.runs`), and for every push row when no hook answers
    (push-rows). Each of those judges the landing push, so a push that cannot
    be stated now (origin unreadable, its main tip not in this clone, or not
    contained in HEAD: the push would not fast-forward) leaves it unjudgeable:
    push-rows ends NOT JUDGED, and the crates leg could read only the
    selection's range, missing members the push carries beyond it. Spending
    the other legs' hours first would only end NOT JUDGED, or GREEN over
    members nobody tested. Only when the hook runs every covered row (and so,
    being active, every push row) does no leg judge the push itself.

    An active hook is not enough: since the push profile lost its scoped rows
    (39b35cb9f7) an installed hook is active with `answers` empty, and the
    crates leg then stands in for `scoped.crates-tests` on the push."""
    if source_diagnostic or landing.stated:
        return None
    if all(hook.runs(row) for row in HOOK_ROWS_COVERED):
        return None
    return landing.why or "the landing push cannot be stated"


def development_legs(g: ls.Graph, sel: ls.Selection, legs: List[Leg], jobs: int,
                     landing: Optional["LandingRange"] = None) -> List[Leg]:
    """Focused real tests; full diagnostic readsets/selection stay visible."""
    import land_development
    scope = land_development.scope(g, sel)
    scope.tests = sorted(set(scope.tests) | set(getattr(sel, "owner_refresh_tests", ())))
    if scope.errors:
        raise RuntimeError("development scope refused: " + "; ".join(scope.errors[:5]))
    # The caller's --base subject may omit work this actual push carries.
    # Reuse the same immutable graph; no second whole-tree scan is needed.
    if landing is not None and landing.stated and landing.contained:
        outgoing = landing_selection(g, sel, landing)
        if outgoing is None:
            raise RuntimeError("development outgoing scope cannot be stated")
        pushed = land_development.scope(g, outgoing)
        if pushed.errors:
            raise RuntimeError("development outgoing scope refused: " + "; ".join(pushed.errors[:5]))
        scope.packages = sorted(set(scope.packages) | set(pushed.packages))
        scope.recipes = sorted(set(scope.recipes) | set(pushed.recipes))
        scope.tests = sorted(set(scope.tests) | set(pushed.tests))
        scope.local_git_import |= pushed.local_git_import
        scope.controller_descriptors |= pushed.controller_descriptors
        scope.oracle_citations |= pushed.oracle_citations
        scope.targo_native_core |= pushed.targo_native_core
        scope.targo_cleanup |= pushed.targo_cleanup
        scope.targo_core_example |= pushed.targo_core_example
        scope.tool_name_guide |= pushed.tool_name_guide
        scope.targo_trust |= pushed.targo_trust
        scope.reader_tests = sorted(set(scope.reader_tests) | set(pushed.reader_tests))
        scope.reader_checks = sorted(set(scope.reader_checks) | set(pushed.reader_checks))
    for leg in legs:
        if leg.id not in ("push-rows", "tcb-panic-ratchet", "ir-cohort"):
            leg.diagnostic_only = True
        if leg.id == "push-rows" and leg.selected:
            # No omitted full leg can claim coverage of a push row. Execute
            # every fresh row; scoped rows may honestly report out of scope.
            # With a hook that answers for the landing (push_rows_leg not
            # selected) it runs every row on the push itself: once, there.
            leg.selected = leg.force_run = True
            leg.command.append("--all-rows")
            leg.reasons = ["development profile: every fresh push/live proof-integrity row, no diagnostic coverage exemptions"]
    if scope.targo_trust:
        # The full profile's own leg, unchanged: its complete suite, readset,
        # environment and --require-test-bin rule. No x.py stage-1 leg runs.
        leg = next((leg for leg in legs if leg.id == land_development.TARGO_TRUST_LEG), None)
        if (leg is None or leg.command != landing_targo.COMMAND or leg.prepare
                or leg.needs_stage1 or leg.stage1_members or leg.cache_members):
            raise RuntimeError("development scope refused: targo-trust owner requires the full profile's "
                               "targo-trust leg")
        leg.diagnostic_only = False
        leg.selected = leg.force_run = True
        leg.required_gitlinks = sorted(set(g.gitlinks) & g.closure({land_development.TARGO_TRUST_COMPONENT}))
        leg.reasons = ["development profile: targo-trust's complete fresh suite for a change targo-trust owns",
                       *leg.reasons]
        # The same complete suite on the feature surface Bootstrap ships: the
        # default-feature run cfg-removes every in-process code path.
        features = land_development.targo_trust_shipped_features(g)
        if not features:
            raise RuntimeError("development scope refused: targo-trust's shipped feature surface "
                               f"({land_development.TARGO_TRUST_SHIPPED_FEATURES_SOURCE} "
                               f"{land_development.TARGO_TRUST_SHIPPED_FEATURES_FN}) cannot be read as one "
                               "literal list of features targo-trust declares")
        legs.append(Leg(land_development.TARGO_TRUST_SHIPPED_LEG,
                        [*landing_targo.COMMAND, "--features", ",".join(features)], [],
                        sorted({*leg.inputs, land_development.TARGO_TRUST_SHIPPED_FEATURES_SOURCE}),
                        leg.history, None, True,
                        ["development profile: targo-trust's complete fresh suite on the feature surface "
                         "Bootstrap ships (" + ", ".join(features) + ")"],
                        env=dict(leg.env), default_env=dict(leg.default_env), force_run=True,
                        required_gitlinks=list(leg.required_gitlinks)))
    for leg_id in scope.reader_checks:
        if leg_id == land_development.TARGO_TRUST_TRIPWIRE_LEG:
            # trust-cg-bridge's text tripwire over targo-trust: exactly its one
            # libtest test, fresh, with the gitlinks its package builds.
            owner = land_development.TARGO_TRUST_TRIPWIRE_COMPONENT
            legs.append(Leg(leg_id,
                            ["targo", "--unverified", "test", "--locked", "--offline",
                             "--manifest-path", owner + "/Cargo.toml", "--lib", "--",
                             land_development.TARGO_TRUST_TRIPWIRE_TEST, "--exact"],
                            ["scripts/lib/land_development.py"], sorted(g.closure({owner})), False, [owner], True,
                            ["fresh " + land_development.TARGO_TRUST_TRIPWIRE_TEST
                             + ": it scans every targo-trust source and manifest"],
                            force_run=True, required_gitlinks=sorted(set(g.gitlinks) & g.closure({owner}))))
            continue
        # A non-Cargo reader of a changed targo-trust file: its own check, on
        # this tree, uncached.
        command, readers = land_development.TARGO_TRUST_READER_CHECKS[leg_id]
        legs.append(Leg(leg_id, [sys.executable, "-B", *command], [command[0], "scripts/lib/land_development.py"],
                        [ls.EVERYTHING], False, None, True,
                        ["fresh " + command[0] + ": it reads the changed targo-trust source"], force_run=True))
    audits = ls.load_audits(g) if scope.reader_tests else {}
    for owner, test, source in scope.reader_tests:
        # Another package's audited test reads the changed targo-trust file:
        # that exact integration test target runs fresh, with every gitlink
        # its package builds or its audit says it reads populated.
        audit = audits.get(source) or {}
        named = [*audit.get("reads", ()), *audit.get("lists", ())]
        gitlinks = (set(g.gitlinks) & g.closure({owner})) | {
            link for link in g.gitlinks if any(t == link or t.startswith(link + "/") for t in named)}
        # A development-package- leg: its one target must run a nonempty passing suite.
        legs.append(Leg("development-package-reader-" + g.packages[owner].name + "-" + test,
                        ["targo", "--unverified", "test", "--locked", "--offline",
                         "--manifest-path", owner + "/Cargo.toml", "--test", test],
                        ["scripts/lib/land_development.py"], sorted(g.closure({owner})), False, [owner], True,
                        [f"fresh {source}: its audited reads include the changed targo-trust source"],
                        force_run=True, required_gitlinks=sorted(gitlinks)))
    if scope.tests:
        legs.append(Leg("development-validation-tests",
                        [sys.executable, "scripts/land_gate.py", "validation-tests", *scope.tests],
                        ["scripts/land_gate.py", "scripts/lib/land_development.py"], [ls.EVERYTHING],
                        False, scope.tests, True, ["focused tests of each changed validation program"], force_run=True))
    if scope.oracle_citations:
        # The mandatory fresh fast.oracle-freeze row judges the actual ledger.
        # Its complete selftest also remains fresh for every locator repair.
        legs.append(Leg("development-oracle-freeze-selftest",
                        ["bash", "scripts/check_frozen_files.sh", "--selftest"],
                        [land_development.ORACLE_WAIVERS, "scripts/check_frozen_files.sh"],
                        [ls.EVERYTHING], False, None, True,
                        ["citation-only owner: full oracle reader selftest and every fresh push row"], force_run=True))
    for owner in scope.packages:
        name = g.packages[owner].name
        if owner == "src/jobserver_utils":
            for suffix, features in (("", []), ("-no-client", ["--no-default-features"])):
                legs.append(Leg("development-package-" + name + suffix,
                                ["targo", "--unverified", "test", "--locked", "--offline",
                                 "--manifest-path", owner + "/Cargo.toml", "--lib", *features],
                                ["scripts/lib/land_development.py"], sorted(g.closure({owner})),
                                False, [owner], True,
                                ["fresh complete GNU-client and close-only jobserver library boundaries"], force_run=True))
            continue
        if owner == "crates/trust-build-cpu":
            for suffix, targets in (("", ["--lib"]),
                                    ("-all-features", ["--all-targets", "--all-features"])):
                legs.append(Leg("development-package-" + name + suffix,
                                ["targo", "--unverified", "test", "--locked", "--offline",
                                 "--manifest-path", owner + "/Cargo.toml", *targets],
                                ["scripts/lib/land_development.py"], sorted(g.closure({owner})),
                                False, [owner], True,
                                ["fresh complete CPU default and optional native-host/member APIs"], force_run=True))
            continue
        if owner == land_development.PROVENANCE_COMPONENT:
            legs.append(Leg("development-package-" + name,
                            ["targo", "--unverified", "test", "--locked", "--offline",
                             "--manifest-path", owner + "/Cargo.toml", "--all-targets", "--all-features"],
                            ["scripts/lib/land_development.py"], sorted(g.closure({owner})),
                            False, [owner], True,
                            ["fresh complete native provenance targets and features"], force_run=True))
            continue
        if owner == land_development.CONTROLLER_COMPONENT:
            # Keep the three minimal API closures and the optional helper closure.
            # Always execute complete cohorts; a filter cannot qualify the API matrix.
            for cohort, features in (("dto", []), ("receiver", ["--features", "bootstrap-receiver"]),
                                     ("client", ["--features", "client"]),
                                     ("all-features", ["--all-features"])):
                legs.append(Leg("development-package-" + name + "-" + cohort,
                                ["targo", "--unverified", "test", "--locked", "--offline",
                                 "--manifest-path", owner + "/Cargo.toml", "--lib", "--no-default-features", *features],
                                ["scripts/lib/land_development.py"], sorted(g.closure({owner})),
                                False, [owner], True,
                                ["fresh complete controller " + cohort + " cohort"], force_run=True))
            continue
        if owner == land_development.BUILD_TREE_COMPONENT:
            # Exercise each admission feature boundary without enabling the
            # separate native CLI qualification, which needs real producers.
            for cohort, features in (("default", []),
                                     ("machine-admission", ["--features", "machine-admission"]),
                                     ("native-exec", ["--features", "native-exec"])):
                legs.append(Leg("development-package-" + name + "-" + cohort,
                                ["targo", "--unverified", "test", "--locked", "--offline",
                                 "--manifest-path", owner + "/Cargo.toml", "--lib", "--no-default-features", *features],
                                ["scripts/lib/land_development.py"], sorted(g.closure({owner})),
                                False, [owner], True,
                                ["fresh complete build-tree " + cohort + " library cohort"], force_run=True))
            continue
        if owner == "src/tools/compiletest":
            # Compiletest self-tests query the staged compiler. Bootstrap owns
            # TEST_RUSTC and the matching harness configuration; direct Cargo
            # invocation silently omits that required runtime input.
            legs.append(Leg("development-package-" + name,
                            _xpy_test_cmd([owner], jobs),
                            ["scripts/lib/land_development.py"], [ls.EVERYTHING],
                            False, [owner], True,
                            ["fresh full compiletest self-tests through their normal Bootstrap owner"],
                            needs_stage1=True, force_run=True))
            continue
        if owner == land_development.BOOTSTRAP_COMPONENT:
            # Bootstrap has an independent workspace. Run every library test,
            # retaining its native ignored-test census and compiler cohort.
            legs.append(Leg("development-package-" + name,
                            ["targo", "--unverified", "test", "--locked", "--offline",
                             "--manifest-path", owner + "/Cargo.toml", "--lib"],
                            ["scripts/lib/land_development.py"], sorted(g.closure({owner})),
                            False, [owner], True,
                            ["fresh complete Bootstrap library tests"], force_run=True))
            continue
        legs.append(Leg("development-package-" + name,
                        ["targo", "--unverified", "test", "--locked", "--offline", "-p", name, "--lib"],
                        ["scripts/lib/land_development.py"], sorted(g.closure({owner})), False, [owner], True,
                        ["fresh complete library tests of affected execution component " + owner], force_run=True))
    if scope.tool_name_guide:
        owner = land_development.TOOL_NAME_OWNER
        legs.append(Leg(land_development.TOOL_NAME_LEG,
                        ["targo", "--unverified", "test", "--locked", "--offline", "--manifest-path",
                         owner + "/Cargo.toml", "--test", "tool_name_source_inputs",
                         "--", "--test-threads=1"],
                        ["scripts/lib/land_development.py"], sorted(g.closure({owner})), False,
                        [owner], True, ["current-source production tool-name reader on the actual guide and refusal controls"],
                        force_run=True))
    if scope.controller_descriptors:
        owner = land_development.CONTROLLER_DESCRIPTORS
        legs.append(Leg(land_development.CONTROLLER_DESCRIPTOR_LEG,
                        ["targo", "--unverified", "test", "--locked", "--offline", "--manifest-path",
                         owner + "/Cargo.toml", "--all-features", "--lib", "descriptors::tests",
                         "--", "--test-threads=1"],
                        ["scripts/lib/land_development.py"], sorted(g.closure({owner})), False,
                        [owner], True, ["fresh all-features controller descriptor library tests"], force_run=True))
    if scope.local_git_import:
        manifest = land_development.LOCAL_GIT_WORKSPACE + "/Cargo.toml"
        prefix = ["targo", "--unverified", "test", "--locked", "--offline", "--manifest-path", manifest]
        core = land_development.LOCAL_GIT_CORE
        workspace = land_development.LOCAL_GIT_WORKSPACE
        for leg_id, owner, args, reason in (
            (land_development.LOCAL_GIT_CORE_LEG, core,
             ["-p", "targo-core", "--lib", "--features", "vendored-openssl,vendored-libgit2",
              "sources::git::local_import"],
             "fresh local Git importer library tests"),
            (land_development.LOCAL_GIT_FIXTURE_LEG, workspace,
             ["-p", "targo", "--test", "local_git_source_cache",
              "--features", "vendored-openssl,vendored-libgit2",
              # Override every field of this fixture-only environment entry.
              # A Cargo config must not inject a prior binary after preflight.
              "--config", 'env.TARGO_LOCAL_SOURCE_TEST_BINARY.value=""',
              "--config", "env.TARGO_LOCAL_SOURCE_TEST_BINARY.force=true",
              "--config", "env.TARGO_LOCAL_SOURCE_TEST_BINARY.relative=false"],
             "fresh native local Git importer tests on the Targo built from this source"),
        ):
            legs.append(Leg(leg_id, [*prefix, *args, "--", "--test-threads=1"],
                            ["scripts/lib/land_development.py"], sorted(g.closure({owner})), False,
                            [owner], True, [reason], force_run=True))
    if scope.targo_native_core or scope.targo_cleanup or scope.targo_core_example:
        prefix = ["targo", "--unverified", "test", "--locked", "--offline", "--manifest-path",
                  land_development.LOCAL_GIT_WORKSPACE + "/Cargo.toml", "--features", "all-static",
                  # Match the maintained bootstrap/source qualification recipe;
                  # constant native-library config does not alter Rust policy.
                  "--config", 'env.LZMA_API_STATIC.value="1"',
                  "--config", "env.LZMA_API_STATIC.force=true",
                  "--config", "env.LZMA_API_STATIC.relative=false"]
        if scope.targo_core_example:
            owner = land_development.LOCAL_GIT_CORE
            legs.append(Leg(land_development.TARGO_CORE_EXAMPLE_LEG,
                            [*prefix[:2], "check", *prefix[3:], "--message-format=json", "-p", "targo-core", "--example", "trust_compiler_query"],
                            ["scripts/lib/land_development.py"], sorted(g.closure({owner})), False,
                            [owner], True, ["fresh compilation of the changed native compiler-query example"], force_run=True))
        if scope.targo_native_core:
            # Four selected custody cases are macOS/aarch64-only. No other
            # host may turn their absent bodies into a green filtered suite.
            if host_triple() != "aarch64-apple-darwin":
                raise RuntimeError("native Targo core development cases require aarch64-apple-darwin")
            owner = land_development.LOCAL_GIT_CORE
            legs.append(Leg(land_development.TARGO_NATIVE_CORE_LEG,
                            [*prefix, "-p", "targo-core", "--lib",
                             "--", "--exact", "--test-threads=1",
                             *land_development.TARGO_NATIVE_CORE_CASES],
                            ["scripts/lib/land_development.py"], sorted(g.closure({owner})), False,
                            [owner], True, ["fresh exact native-core custody, projection, bank and fresh-kernel parent cases"],
                            force_run=True))
        if scope.targo_cleanup:
            if platform.system() not in ("Darwin", "Linux"):
                raise RuntimeError("native Targo cleanup development cases require macOS or Linux")
            owner = land_development.LOCAL_GIT_WORKSPACE
            legs.append(Leg(land_development.TARGO_CLEANUP_LEG,
                            [*prefix, "-p", "targo", "--test", "clean_intermediates_only",
                             "--config", 'env.TARGO_CLEAN_TEST_BINARY.value=""',
                             "--config", "env.TARGO_CLEAN_TEST_BINARY.force=true",
                             "--config", "env.TARGO_CLEAN_TEST_BINARY.relative=false",
                             "--", "--exact", "--test-threads=1", *land_development.TARGO_CLEANUP_CASES],
                            ["scripts/lib/land_development.py"], sorted(g.closure({owner})), False,
                            [owner], True, ["fresh exact native cleanup CLI cases on the Targo built from this source"],
                            force_run=True))
    if scope.recipes:
        legs.append(Leg("development-recipes", _xpy_test_cmd(scope.recipes, jobs),
                        ["scripts/lib/land_development.py"], [ls.EVERYTHING], False, scope.recipes, True,
                        ["fresh normal compiletest integration recipes for affected execution components/fixtures"],
                        needs_stage1=True, run_targets=scope.recipes, force_run=True))
    return legs


def declared_development_legs(g, selection, jobs, hook, landing):
    """No omitted reachability computation can answer for a required check."""
    legs = [Leg(spec.id, [], [], [], False, None, False,
                ["full reachability NOT COMPUTED; diagnostic NOT RUN"], diagnostic_only=True)
            for spec in ls.LEGS]
    legs.extend(Leg(name, [], [], [], False, None, False,
                    ["full reachability NOT COMPUTED; diagnostic NOT RUN"], diagnostic_only=True)
                for name in ("compiler-unit-tests", "crates-tests", "tidy"))
    legs.extend([
        push_rows_leg(selection.base, hook, landing),
        tcb_panic_ratchet_leg(["TCB source/baseline check, served only on its unchanged declared reads"]),
        ir_cohort_leg(),
    ])
    legs = development_legs(g, selection, legs, jobs, landing)
    for leg in legs:
        if not leg.diagnostic_only and (leg.prepare or leg.cache_members or leg.stage1_members
                or (leg.needs_stage1 and leg.id not in ("development-recipes", "development-package-compiletest"))
                or not (leg.force_run or leg.id in UNCACHED_LEGS or leg.reads is not None)):
            raise LandingUnjudged("declared development leg requires full reachability: " + leg.id)
    return legs


def development_native_target_problem(env) -> Optional[str]:
    """The working native invocation has no target selector at all.

    In particular build.target=[] is *not* a native selector: current Targo
    accepts it as an empty compile-kind population and may succeed doing no
    work. Refuse configured/ambient target selection and opaque includes.
    """
    if any(name in env for name in ("CARGO_BUILD_TARGET", "TARGO_BUILD_TARGET")):
        return "native Targo development checks require unset CARGO_BUILD_TARGET/TARGO_BUILD_TARGET"
    if any(name.startswith(("CARGO_TARGET_", "TARGO_TARGET_")) and name.endswith("_RUNNER") for name in env):
        return "native Targo development checks require direct execution without an ambient target runner"
    try:
        for path, _outside in lock_config_files(REPO_ROOT, env):
            try:
                config = tomllib.loads(path.read_text(encoding="utf-8"))
            except (FileNotFoundError, NotADirectoryError):
                continue
            build = config.get("build", {})
            if "include" in config or not isinstance(build, dict) or "target" in build:
                return f"{path}: native Targo development checks require no build.target or opaque include"
            targets = config.get("target", {})
            if not isinstance(targets, dict) or any(not isinstance(value, dict) or "runner" in value
                                                   for value in targets.values()):
                return f"{path}: native Targo development checks require direct execution without configured runners"
    except (OSError, UnicodeError, ValueError, KeyError) as error:
        return f"native Targo target configuration cannot be established: {error}"
    return None


def development_tool_name_resolution_problem(env) -> Optional[str]:
    """Keep the reviewed caller namespace, including untracked host config."""
    from land_development import TOOL_NAME_ABSENT_CONFIGS
    try:
        caller_config = REPO_ROOT / "targo-trust" / ".cargo"
        if caller_config.is_symlink():
            return f"{caller_config}: tool-name caller config must not be redirected"
        for relative in TOOL_NAME_ABSENT_CONFIGS:
            path = REPO_ROOT / relative
            if path.is_symlink() or path.exists():
                return f"{path}: tool-name qualification requires the reviewed absent config"
        for cwd in (REPO_ROOT, REPO_ROOT / "targo-trust"):
            problem = lock_redirect(cwd, env)
            if problem:
                return problem
    except (OSError, UnicodeError, ValueError) as error:
        return f"tool-name source-resolution context cannot be established: {error}"
    return None


def development_native_command(leg: Leg, command: List[str], log, env=None) -> List[str]:
    """Retain cleanup worlds outside source without a test runner trampoline.

    The fixture uses std::env::temp_dir(). Cargo supplies TMPDIR to its
    actual source-built executable alongside its assembled loader environment.
    In particular no protected Darwin shell/env process drops DYLD_* keys.
    Each invocation gets a fresh directory, retained with the log's path.
    """
    from land_development import TARGO_CLEANUP_LEG
    if leg.id != TARGO_CLEANUP_LEG:
        return command
    if command != leg.command or "--" not in command or any(arg == "--target" or arg.startswith("--target=") for arg in command):
        raise RuntimeError("native cleanup command differs from its declared source check")
    problem = development_native_target_problem(os.environ if env is None else env)
    if problem:
        raise RuntimeError(problem)
    temporary_root = Path("/tmp").resolve()
    if temporary_root.is_relative_to(REPO_ROOT.resolve()):
        raise RuntimeError("native cleanup requires an external temporary root")
    world = Path(tempfile.mkdtemp(prefix="trust-native-clean-", dir=temporary_root)).resolve()
    value = "env.TMPDIR.value=" + json.dumps(str(world))
    log.write(f"Native cleanup retained world root: {world}\n")
    offset = command.index("--")
    return [*command[:offset], "--config", value, "--config", "env.TMPDIR.force=true",
            "--config", "env.TMPDIR.relative=false", *command[offset:]]


def development_test_result(text: str, exit_code: int, *, all_required: bool = False,
                            expected_count: Optional[int] = None,
                            multiple_suites: bool = False) -> Tuple[int, str]:
    """A native package leg must execute a nonempty passing libtest suite."""
    if exit_code:
        return exit_code, "native component command failed"
    summary = re.compile(r"^test result: (\w+)\. (\d+) passed; (\d+) failed; (\d+) ignored;", re.M)
    starts = re.compile(r"^running (\d+) tests?\s*$")
    announcements = re.compile(r"^\s*Running\s+(?:(unittests)\s+)?(.+?)\s+\(.+\)\s*$")
    rows = []
    required = []
    if not any(starts.match(line) for line in text.splitlines()):
        # Legacy single-suite output still requires its one complete result.
        # It cannot identify several targets or distinguish helper output.
        if multiple_suites:
            return 2, "multiple native targets lack announced suite boundaries"
        rows = summary.findall(text)
        if len(rows) != 1:
            return 2, "no complete passing native component test result"
        required = rows
    else:
        frames = []
        roots = []
        active = None
        pending = None
        try:
            for line in text.splitlines():
                announcement = announcements.match(line)
                if announcement and active is None:
                    if pending is not None:
                        return 2, "native target has no complete test suite"
                    pending = bool(announcement[1] and announcement[2] == "src/lib.rs")
                    continue
                start = starts.match(line)
                if start:
                    population = int(start[1])
                    if active is None:
                        if roots and not multiple_suites:
                            return 2, "single native target emitted additional root suites"
                        if multiple_suites and pending is None:
                            return 2, "native root suite lacks its target announcement"
                        active = {"population": population, "library": pending, "result": None}
                        roots.append(active)
                        pending = None
                        frames.append((population, True))
                    else:
                        # Equal populations cannot identify which summary is
                        # the required root. Do not guess from their order.
                        if population == active["population"]:
                            return 2, "native helper and root suite boundaries are ambiguous"
                        frames.append((population, False))
                    continue
                result = summary.match(line)
                if result:
                    row = result.groups()
                    population = sum(int(value) for value in row[1:])
                    matches = [i for i, frame in enumerate(frames) if frame[0] == population]
                    if not matches:
                        return 2, "native result has no matching announced suite"
                    index = matches[-1]
                    _population, root = frames.pop(index)
                    if root:
                        if active is None:
                            return 2, "native result has no active root suite"
                        # Cleanup controls deliberately _exit/kill helper
                        # processes before libtest can print a footer. Their
                        # output supplies no credit; only the completed root
                        # determines whether its ownership assertions passed.
                        frames.clear()
                        active["result"] = row
                        active = None
            if frames or active is not None or pending is not None:
                return 2, "native suite output is incomplete"
            rows = [root["result"] for root in roots]
            required = [root["result"] for root in roots if root["library"]] if multiple_suites else rows
        except (ValueError, TypeError):
            return 2, "native suite counters are invalid"
        # Helpers supply no positive credit. An all-targets invocation must
        # identify its selected library independently of auxiliary targets.
        if not rows or (multiple_suites and len(required) != 1):
            return 2, "no unambiguous selected native library suite"
    if not required or any(status != "ok" or int(failed) for status, _, failed, _ in rows):
        return 2, "no complete passing native component test result"
    if any(not int(passed) for _, passed, _, _ in required):
        return 2, "native component suite executed no passing test (empty/ignored-only)"
    if all_required and any(int(ignored) for _, _, _, ignored in rows):
        return 2, "native component suite ignored required tests"
    if expected_count is not None and (type(expected_count) is not int or expected_count < 1
                                      or len(required) != 1 or int(required[0][1]) != expected_count
                                      or int(required[0][3])):
        return 2, "native component suite differs from its exact required case population"
    return 0, "fresh nonempty native component suite"


def development_example_result(text: str, exit_code: int) -> Tuple[int, str]:
    from land_development import TARGO_CORE_EXAMPLE, LOCAL_GIT_CORE
    if exit_code:
        return exit_code, "native compiler-query example command failed"
    expected = (REPO_ROOT / TARGO_CORE_EXAMPLE).resolve()
    manifest = (REPO_ROOT / LOCAL_GIT_CORE / "Cargo.toml").resolve()
    try:
        artifacts = []
        for line in text.splitlines():
            if not line.startswith("{"):
                continue
            row = json.loads(line)
            if not isinstance(row, dict):
                raise ValueError("unknown compiler message")
            target = row.get("target", {})
            if not isinstance(target, dict):
                raise ValueError("unknown compiler target")
            if row.get("reason") == "compiler-artifact" and target.get("name") == "trust_compiler_query":
                artifacts.append(row)
        if len(artifacts) != 1:
            raise ValueError("missing/duplicate actual example compiler artifact (possibly no-op)")
        row = artifacts[0]
        if (row["target"]["kind"] != ["example"] or not Path(row["target"]["src_path"]).is_absolute()
                or Path(row["target"]["src_path"]).resolve() != expected
                or not Path(row["manifest_path"]).is_absolute() or Path(row["manifest_path"]).resolve() != manifest
                or row.get("trust_compile_kind") != "host" or row.get("trust_compile_target") != host_triple()
                or row.get("trust_compile_mode") != "check"
                or not isinstance(row.get("trust_unit_identity_sha256"), str)
                or re.fullmatch(r"[0-9a-f]{64}", row["trust_unit_identity_sha256"]) is None
                or type(row.get("fresh")) is not bool or not isinstance(row.get("filenames"), list)
                or not row["filenames"] or not all(isinstance(name, str) and Path(name).is_absolute()
                                                 and stat.S_ISREG(Path(name).lstat().st_mode)
                                                 for name in row["filenames"])):
            raise ValueError("example source/native host/unit identity or retained compiler artifact differs")
        return 0, "actual source-bound native compiler-query example artifact"
    except (OSError, ValueError, KeyError, TypeError) as error:
        return 2, f"native compiler-query example NOT JUDGED: {error}"


def print_plan(sel: ls.Selection, legs: List[Leg], hook: PushHook,
               landing: Optional["LandingRange"] = None, source_diagnostic: bool = False,
               development: bool = False) -> None:
    print(hook_mode_line(hook, legs, landing))
    if source_diagnostic:
        print("SOURCE DIAGNOSTIC ONLY: selected source checks do not judge a landing push; "
              "the result remains PARTIAL.")
    print(f"SUBJECT: tree diff {sel.base[:12]}..{sel.head[:12]} ({len(sel.changed)} path(s) changed)")
    if isinstance(sel, DeclaredDevelopmentSelection):
        print("DECLARED DEVELOPMENT OWNERSHIP: full reachability NOT COMPUTED; broad diagnostics NOT RUN. "
              "Registered owner checks and every fresh push row remain mandatory.")
    if landing is not None:
        if landing.changed is not None:
            print(f"LANDING PUSH: tree diff origin's main tip {landing.tip[:12]}..{landing.head[:12]} "
                  f"({len(landing.changed)} path(s) changed){'' if landing.contained else ': ' + landing.why}")
        else:
            print(f"LANDING PUSH: cannot be read ({landing.why})")
        refused = landing_refusal(hook, landing, source_diagnostic=source_diagnostic)
        if refused:
            print(f"LANDING NOT JUDGED; independent development source checks still run ({refused})"
                  if development else f"NOT JUDGED BEFORE ANY LEG: `run` stops here ({refused})")
    if sel.everything:
        print("EVERY LEG IS SELECTED:")
        for r in sel.everything[:10]:
            print(f"  - {r}")
        if len(sel.everything) > 10:
            print(f"  ... {len(sel.everything) - 10} more")
    for leg in legs:
        state = "DIAG" if leg.diagnostic_only else ("RUN " if leg.selected else "SKIP")
        tgt = "" if leg.targets is None else f" [{len(leg.targets)} target(s)]"
        print(f"{state} {leg.id}{tgt}")
        for r in leg.reasons[:4]:
            print(f"       {r}")


def landing_json(landing: "LandingRange") -> Dict[str, object]:
    return {"tip": landing.tip, "head": landing.head, "contained": landing.contained,
            "changed": None if landing.changed is None else len(landing.changed), "why": landing.why}


def cmd_plan(args, discovery: Optional[DiscoverySession] = None) -> int:
    if getattr(args, "no_cache", False) and not getattr(args, "run", False):
        raise RuntimeError("plan --no-cache requires --run")
    if getattr(args, "run", False):
        if args.head != "HEAD" or args.json:
            raise RuntimeError("plan --run requires HEAD and text output")
        session = discovery if discovery is not None else DiscoverySession()
        plan_args = argparse.Namespace(**vars(args))
        plan_args.run, plan_args.no_cache = False, False
        with _cancellation_scope():
            status = cmd_plan(plan_args, session)
            if status:
                return status
            # Validation only: publication remains the caller's ordinary Agh
            # operation. No land/hook/transport alternative is introduced.
            return cmd_run(argparse.Namespace(base=args.base, dry_run=False,
                                             no_cache=getattr(args, "no_cache", False), only=None,
                                             development=getattr(args, "development", False)), session)
    try:
        if args.head == "HEAD":
            g, sel, base, landing = discover_landing(
                args.base, args.head, verify=args.verify_graph, session=discovery,
                profile=(DiscoveryProfile.DEVELOPMENT if getattr(args, "development", False)
                         else DiscoveryProfile.FULL))
        else:
            # An explicit historical head is a diagnostic, even when it could
            # not fast-forward today's main. Preserve its full stated plan.
            if getattr(args, "development", False):
                development_discovery_inputs(args.base, args.head)
            g, sel, base = compute(args.base, args.head, verify=args.verify_graph)
            landing = read_landing(head=sel.head)
    except LandingUnjudged as error:
        print(f"LAND-GATE: NOT JUDGED — {error}. No graph or leg is judged.")
        return 2
    host = host_budget.measure()
    plans = budget_plans(host)
    hook = push_hook_state(sel.changed, sel.head, landing=landing)
    legs = (declared_development_legs(g, sel, plans["rustc-build"].jobs, hook, landing)
            if isinstance(sel, DeclaredDevelopmentSelection)
            else build_legs(g, sel, base, plans, hook, landing))
    development = getattr(args, "development", False)
    if development and not isinstance(sel, DeclaredDevelopmentSelection):
        try:
            legs = development_legs(g, sel, legs, plans["rustc-build"].jobs, landing)
        except RuntimeError as exc:
            print(f"LAND-GATE: NOT JUDGED — {exc}")
            return 2
    try:
        checkout = git("rev-parse", "--verify", "HEAD^{commit}")
    except RuntimeError:
        checkout = ""
    if sel.head != checkout:
        # The plan describes --head; push-rows runs whatever this checkout's HEAD
        # is when `run` reaches it, and `run` judges only the checkout's HEAD.
        for l in legs:
            if l.id == "push-rows" and l.selected:
                l.reasons.insert(0, f"`--head {args.head}` ({sel.head[:12]}) is not what it runs: `run` judges "
                                    f"this checkout's HEAD ({checkout[:12] or 'unreadable'}), and push-rows pushes "
                                    "that HEAD onto origin's main tip")
    if args.json:
        print(json.dumps({"selection": sel.as_json(),
                          "profile": "development" if development else "full-diagnostic",
                          "push_hook": {"active": hook.active, "why": hook.why, "rule": hook.fired,
                                        "answers": sorted(hook.answers), "gaps": hook.gaps},
                          "landing": landing_json(landing), "refused": landing_refusal(hook, landing),
                          "legs": {l.id: {"selected": l.selected, "diagnostic_only": l.diagnostic_only,
                                          "targets": l.targets, "command": l.command}
                                   for l in legs}}, indent=1))
        return 0
    print_plan(sel, legs, hook, landing, development=development)
    return 0


# Seconds this process has spent in Git plumbing asked through _git_ask:
# a checkout pass's timing row takes its own share as `git_seconds`.
_GIT_ASK_SECONDS = [0.0]


def _git_ask(root: Path, env: Dict[str, str], *args: str, **options) -> subprocess.CompletedProcess:
    started = time.monotonic()
    try:
        return checkout_inputs.git_ask(root, env, *args, **options)
    finally:
        _GIT_ASK_SECONDS[0] += time.monotonic() - started


def _git_said(proc: subprocess.CompletedProcess) -> str:
    streams = [[line.strip() for line in (output or "").splitlines() if line.strip()]
               for output in (proc.stderr, proc.stdout)]
    lines = [line for stream in streams for line in stream]
    # Git reports merge conflicts on stdout while unrelated advice can occupy
    # stderr. Keep one causal line and the existing fatal/error priority.
    for prefixes in (("fatal:", "error:"), ("CONFLICT",), ("Automatic merge failed",)):
        message = next((line for line in lines if line.startswith(prefixes)), None)
        if message is not None:
            return message
    return next((stream[-1] for stream in streams if stream), f"exit {proc.returncode}")


_physical_stat_key = checkout_inputs.physical_stat_key


def _history_overlay_problem(repo: Path, env: Dict[str, str]) -> Optional[str]:
    """Refuse local alternate history before it can select or key a check."""
    replacements = _git_ask(repo, env, "for-each-ref", "--format=%(refname)", "refs/replace/", timeout=10)
    graft = _git_ask(repo, env, "rev-parse", "--path-format=absolute", "--git-path", "info/grafts", timeout=10)
    if replacements.returncode or graft.returncode or not graft.stdout.strip():
        return "cannot inspect Git history overlays"
    if replacements.stdout.strip():
        return "Git replacement refs change the history used to select checks"
    try:
        info = Path(graft.stdout.strip()).lstat()
    except FileNotFoundError:
        return None
    except OSError as exc:
        return f"cannot inspect Git grafts ({exc})"
    if not stat.S_ISREG(info.st_mode) or info.st_size:
        return "Git grafts change the history used to select checks"
    return None


_committed_crlf_matches = checkout_inputs.committed_crlf_matches
# Compare physical bytes/type/mode directly, without Git conversion filters.
_raw_tracked_problem = checkout_inputs.raw_tracked_problem


def _sparse_exclusion_problem(repo: Path, paths: set, label: str,
                              env: Dict[str, str]) -> Optional[str]:
    """Accept absent skip-worktree entries only when Git's current sparse rules exclude them.

    The flag alone is never authority: update-index can set it on an arbitrary
    existing or missing file. Keep the index/commit comparison separate, and
    ask Git to interpret its own patterns instead of approximating their syntax.
    Observation never clears flags or changes the checkout.
    """
    if not paths:
        return None
    first = label + "/" + min(paths)

    def refused(reason: str) -> str:
        return f"hidden index flag 'S' on tracked path {first!r} ({reason})"

    def present_problem() -> Optional[str]:
        for path in sorted(paths):
            current = repo
            parts = Path(path).parts
            for index, part in enumerate(parts):
                current /= part
                try:
                    info = current.lstat()  # exists() would overlook a dangling symlink.
                except FileNotFoundError:
                    break
                except OSError as exc:
                    return refused(f"cannot inspect sparse exclusion {path!r}: {exc}")
                if index == len(parts) - 1:
                    return refused(f"sparse exclusion is present in the worktree: {path!r}")
                if not stat.S_ISDIR(info.st_mode):
                    return refused(f"sparse exclusion has a non-directory parent: {path!r}")
        return None

    problem = present_problem()
    if problem:
        return problem
    configured = _git_ask(repo, env, "config", "--bool", "--get", "core.sparseCheckout", timeout=10)
    if configured.returncode or configured.stdout.strip() != "true":
        return refused("sparse checkout is not configured")
    pattern_path = _git_ask(repo, env, "rev-parse", "--path-format=absolute", "--git-path",
                            "info/sparse-checkout", timeout=10)
    if pattern_path.returncode or not pattern_path.stdout.strip():
        return refused("cannot locate sparse-checkout patterns")
    patterns = Path(pattern_path.stdout.strip())
    try:
        before = patterns.lstat()
        if not stat.S_ISREG(before.st_mode):
            return refused("sparse-checkout patterns are not a regular file")
    except OSError as exc:
        return refused(f"cannot inspect sparse-checkout patterns: {exc}")
    included = _git_ask(repo, env, "sparse-checkout", "check-rules", "-z",
                        input="\0".join(sorted(paths)) + "\0", timeout=10)
    if included.returncode:
        return refused(f"cannot check sparse-checkout exclusions: {_git_said(included)}")
    if included.stdout:
        return refused("Git's sparse-checkout rules include a skipped path")
    try:
        if _physical_stat_key(patterns.lstat()) != _physical_stat_key(before):
            return refused("sparse-checkout patterns changed during inspection")
    except OSError as exc:
        return refused(f"sparse-checkout patterns changed during inspection: {exc}")
    configured_after = _git_ask(repo, env, "config", "--bool", "--get", "core.sparseCheckout", timeout=10)
    if configured_after.returncode or configured_after.stdout != configured.stdout:
        return refused("sparse-checkout configuration changed during inspection")
    return present_problem()


# A complete physical pass reads every tracked file. One repository's files are
# spread over worker processes once there are this many (threads cannot help:
# the per-file work holds the interpreter lock). Each worker runs the unchanged
# per-file check, checkout_inputs.raw_tracked_problem, on contiguous runs of
# the committed order, and the parent reports the first problem in that order:
# only the scheduling differs from checking in line.
CHECKOUT_PARALLEL_MIN_FILES = 2048
CHECKOUT_BATCH_FILES = (256, 4096)


def checkout_jobs() -> int:
    """Worker processes for a complete physical pass: TRUST_CHECKOUT_JOBS when
    set (anything but a positive whole number is 1: check in this process),
    else min(8, CPUs). Measured 2026-11-09 at load 22-28 on 18 cores: 8
    workers read first-party/clean (39k files) in 2.3 s; in line, 9.2 s."""
    raw = os.environ.get("TRUST_CHECKOUT_JOBS", "")
    if raw:
        return max(1, min(64, int(raw))) if re.fullmatch(r"[0-9]{1,6}", raw) else 1
    return max(1, min(8, os.cpu_count() or 1))


# A worker is forked from the gate as the gate run begins (_CheckoutWorkers):
# it executes no program and reads no interpreter or library file, so it holds
# exactly the modules the gate imported before anything ran. It compiles the
# checkout_inputs source the gate captured at import (in memory) and serves
# marshalled batches; a batch that loads anything new stops it (serve).
def _checkout_worker_descriptors(requests_fd: int, answers_fd: int) -> None:
    """In a forked worker: leave the gate's cancellation signals
    (_CANCEL_SIGNALS) to the gate, make descriptors 0 and 1 /dev/null, and
    close every other descriptor but 2 and the two pipes. Nothing the worker
    starts (the `git` the check runs) inherits a pipe; the worker holds no
    other worker's pipe, so each sees its input end when the gate closes it."""
    for sig in _CANCEL_SIGNALS:
        signal.signal(sig, signal.SIG_IGN)
    null = os.open(os.devnull, os.O_RDWR)
    os.dup2(null, 0)
    os.dup2(null, 1)
    keep = {0, 1, 2, requests_fd, answers_fd}
    for name in os.listdir("/dev/fd"):
        if name.isdigit() and int(name) not in keep:
            try:
                os.close(int(name))
            except OSError:
                pass


def _checkout_worker(requests_fd: int, answers_fd: int, key: bytes) -> None:
    """The body of a forked checkout worker; it never returns to the gate."""
    _checkout_worker_descriptors(requests_fd, answers_fd)
    module = types.ModuleType("checkout_inputs")
    exec(compile(_CHECKOUT_INPUTS_SOURCE, "checkout_inputs.py", "exec"), module.__dict__)
    with open(requests_fd, "rb") as requests, open(answers_fd, "wb") as answers:
        module.serve(requests, answers, key)


def _checkout_answer(reply: object, nonce: bytes, request: bytes, key: bytes) -> list:
    """The results in a worker's `reply` to the marshalled `request` sent with
    `nonce`: (nonce, the request's sha256, the marshalled results, their
    HMAC-SHA256 under `key`). The key exists only in the memory of the gate and
    the workers it forked, and the digest names the request bytes the worker
    parsed: an answer to anything else that reached a worker's input (another
    request, or this nonce with other contents), or one written by anything
    else, fails the batch."""
    if (not isinstance(reply, tuple) or len(reply) != 4 or reply[0] != nonce
            or reply[1] != hashlib.sha256(request).digest()
            or not isinstance(reply[2], bytes) or not isinstance(reply[3], bytes)
            or not hmac.compare_digest(reply[3], hmac.digest(key, nonce + reply[1] + reply[2], "sha256"))):
        raise ValueError("an answer to another request")
    answer = marshal.loads(reply[2])
    if not isinstance(answer, list) or not all(problem is None or isinstance(problem, str) for problem in answer):
        raise ValueError("a malformed answer")
    return answer


class _ForkedWorker:
    """A forked checkout worker: requests go to `stdin`, answers come from
    `stdout` (the gate's ends of its two pipes)."""

    def __init__(self, pid: int, stdin, stdout) -> None:
        self.pid, self.stdin, self.stdout = pid, stdin, stdout
        self.returncode: Optional[int] = None

    def poll(self) -> Optional[int]:
        if self.returncode is None:
            try:
                pid, status = os.waitpid(self.pid, os.WNOHANG)
            except ChildProcessError:
                self.returncode = -1
            else:
                if pid:
                    self.returncode = os.waitstatus_to_exitcode(status)
        return self.returncode

    def wait(self, timeout: float) -> int:
        deadline = time.monotonic() + timeout
        while self.poll() is None:
            if time.monotonic() >= deadline:
                raise subprocess.TimeoutExpired([str(self.pid)], timeout)
            time.sleep(0.01)
        assert self.returncode is not None
        return self.returncode

    def kill(self) -> None:
        if self.poll() is None:
            try:
                os.kill(self.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass


# The installed targo answers "no such command" to `source-check` until a
# sealed pack carries it (STATUS.md), and asking costs a whole package
# admission first: `atpkg verify` of the store and a digest of targo, 9.1 s
# of the measured development run's worker start (run 20261114T134816).
# That one answer is remembered, keyed on the managed targo image's path and
# physical stat key (path, dev, ino, size, mtime, ctime). "Available" is never
# stored, and no other refusal is: a stale key can only leave a pass on the
# Python reader, which reads every file as the native one does, never skip one.
NATIVE_UNAVAILABLE_FILE = "native-reader-unavailable.json"
NATIVE_NO_COMMAND = "no such command: `source-check`"


def native_reader_key(env: Dict[str, str]) -> Optional[List[object]]:
    """The managed targo image's path and physical stat key, or None."""
    try:
        path = native_checkout.selected_executable(env)
        st = os.stat(path)
    except (OSError, RuntimeError, ValueError):
        return None
    return [str(path), st.st_dev, st.st_ino, st.st_size, st.st_mtime_ns, st.st_ctime_ns]


def _native_unavailable_path() -> Path:
    common = common_dir()
    if not common.is_absolute():
        # Never a file under whatever directory the gate was started in.
        raise ValueError(f"the Git common directory {str(common)!r} is not absolute")
    return common / "trust-land" / NATIVE_UNAVAILABLE_FILE


def remembered_native_unavailable(key: Optional[List[object]]) -> Optional[str]:
    """The remembered "no such command" answer for exactly `key`, or None."""
    if key is None:
        return None
    try:
        doc = json.loads(_native_unavailable_path().read_text(encoding="utf-8"))
    except (OSError, RuntimeError, ValueError, subprocess.SubprocessError):
        return None
    if isinstance(doc, dict) and doc.get("key") == key and isinstance(doc.get("why"), str) \
            and NATIVE_NO_COMMAND in doc["why"]:
        return doc["why"]
    return None


def remember_native_unavailable(key: Optional[List[object]], why: str) -> None:
    """Store `why` under `key` when it is the reader's "no such command" and
    the image's key is unchanged since it was read; nothing else is stored."""
    if key is None or NATIVE_NO_COMMAND not in why:
        return
    try:
        if native_reader_key(dict(os.environ)) != key:
            return
        path = _native_unavailable_path()
        path.parent.mkdir(parents=True, exist_ok=True)
        fd, staged = tempfile.mkstemp(prefix=".native-reader.", dir=path.parent)
        with os.fdopen(fd, "w", encoding="utf-8") as fh:
            json.dump({"key": key, "why": why}, fh)
        os.replace(staged, path)
    except (OSError, RuntimeError, ValueError, subprocess.SubprocessError):
        return


class _CheckoutWorkers:
    """Worker processes for complete passes, all forked (start) when a gate run
    begins and each fed one batch at a time by its own thread (which only waits
    on pipes). None starts later: a pass is read by these workers or, if they
    could not start or failed, in line. `jobs` 1: none; check in line."""

    READY_SECONDS = 120

    def __init__(self, jobs: Optional[int] = None) -> None:
        self.jobs = checkout_jobs() if jobs is None else jobs
        self.fallback = ""
        self._procs: List[_ForkedWorker] = []
        self._ready = 0  # how many of _procs, in order, have said `ready`
        self._key = b""
        self.native = None
        self.native_fallback = ""
        self.native_corruption = ""
        self.native_bytes = 0
        self.startup = {"python_seconds":0.0,"native_seconds":0.0,"native":"not selected"}

    def start(self) -> None:
        """Fork every worker and wait until each says `ready`, or leave every
        pass in line (jobs 1, `fallback` says why). The pool's pipes must not
        take a descriptor number the environment advertises to the programs
        the run starts (landing_targo.resource_fds): with one that is not
        open, a pipe could take its number and be handed on, so no worker
        starts and the numbers stay as the gate found them. A fork copies only
        the calling thread, so with any other thread running (one could hold a
        lock a worker needs) none starts either."""
        if self.jobs <= 1:
            return
        started = time.monotonic()
        try:
            landing_targo.resource_fds(dict(os.environ))
            self._start()
        except (OSError, RuntimeError, ValueError) as exc:
            self.decline(str(exc))
        finally:
            self.startup["python_seconds"] = round(time.monotonic()-started,6)
        if (self.jobs > 1 and _NATIVE_CHECKOUT_READER_SHA256 is not None
                and _ACTIVE_CANCELLATION is not None and sys.platform == "darwin" and platform.machine() == "arm64"):
            program = None
            started = time.monotonic()
            key = native_reader_key(dict(os.environ))
            remembered = remembered_native_unavailable(key)
            if remembered is not None:
                self.native_fallback = f"native reader unavailable (remembered for this targo): {remembered}"
                self.startup.update({"native": "unavailable", "remembered": True,
                                     "native_seconds": round(time.monotonic() - started, 6)})
                return
            try:
                program = native_checkout.managed_program(dict(os.environ))
                share = host_budget.admitted_jobs()
                selected, program = program, None  # Reader owns original handles even on refusal
                self.native = native_checkout.Reader(selected, _NATIVE_CHECKOUT_READER_SHA256,
                    min(self.jobs, share) if share is not None else self.jobs,
                    dict(os.environ), _OwnedGroup, _ACTIVE_CANCELLATION, _check_cancellation)
                self.startup.update({"native":"ready","executable":str(selected.executable),
                    "image_sha256":selected.expected,"runtime_identity_report":self.native.runtime_identity})
            except native_checkout.Corrupt as error:
                self.native_corruption = str(error)
                self.startup["native"] = "corrupt"
            except (OSError, RuntimeError, ValueError, KeyError, TypeError) as error:
                self.native_fallback = f"native reader unavailable: {error}"
                self.startup["native"] = "unavailable"
                remember_native_unavailable(key, str(error))
            finally:
                self.startup["native_seconds"] = round(time.monotonic()-started,6)
                if program is not None and self.native is None:
                    program.close()

    def decline(self, why: str) -> None:
        self.fallback = why
        self.jobs = 1
        self.close()

    def _start(self) -> None:
        if threading.active_count() != 1:
            raise RuntimeError("the gate runs another thread; a forked worker could copy a lock it holds")
        if not self._key:
            self._key = os.urandom(32)
        while len(self._procs) < self.jobs:
            requests_fd, requests_gate = os.pipe()
            answers_gate, answers_fd = os.pipe()
            if min(requests_fd, answers_fd) < 3:  # a standard descriptor was closed: the worker needs 0-2
                for fd in (requests_fd, requests_gate, answers_gate, answers_fd):
                    os.close(fd)
                raise RuntimeError("descriptors 0-2 are not all open")
            pid = os.fork()
            if pid == 0:  # the worker: it never returns into the gate's code
                # The gate's objects, garbage included, are never collected
                # here: no finalizer of the gate's runs in a worker.
                gc.freeze()
                status = 70
                try:
                    _checkout_worker(requests_fd, answers_fd, self._key)
                    status = 0
                except BaseException as exc:  # noqa: BLE001 - the gate falls back on its exit
                    try:
                        os.write(2, f"checkout worker: {type(exc).__name__}: {exc}\n".encode(errors="replace"))
                    except OSError:
                        pass
                finally:
                    os._exit(status)
            os.close(requests_fd)
            os.close(answers_fd)
            self._procs.append(_ForkedWorker(pid, open(requests_gate, "wb"), open(answers_gate, "rb")))
        deadline = time.monotonic() + self.READY_SECONDS
        for proc in self._procs[self._ready:]:
            assert proc.stdout is not None
            if not select.select([proc.stdout], [], [], max(0.0, deadline - time.monotonic()))[0] \
                    or proc.stdout.readline() != b"ready\n":
                raise RuntimeError("a checkout worker did not start")
            self._ready += 1

    def run(self, repo: str, revision: str, env: Dict[str, str],
            batches: Sequence[List[Tuple[str, str, str, str]]]) -> List[Optional[list]]:
        """checkout_inputs.raw_tracked_batch of each batch, by index, from the
        workers start() readied. Batches are taken in order, and none after the
        first one with a problem is begun, so every batch before that one is
        answered; the rest may be None. Each answer must carry its request's
        random nonce, the digest of its bytes and the pool's HMAC
        (_checkout_answer): anything else that reached a worker's input or
        answer pipe can only make the batch fail."""
        procs = self._procs
        if self.jobs <= 1 or not procs or self._ready != len(procs):
            raise RuntimeError("no checkout worker was started when the gate run began")
        answers: List[Optional[list]] = [None] * len(batches)
        lock = threading.Lock()
        state = {"next": 0, "stop": len(batches)}
        failures: List[BaseException] = []

        def feed(proc: _ForkedWorker) -> None:
            while True:
                with lock:
                    index = state["next"]
                    if index >= state["stop"] or failures:
                        return
                    state["next"] = index + 1
                nonce = os.urandom(16)
                try:
                    request = marshal.dumps((repo, revision, env, batches[index]))
                    marshal.dump((nonce, request), proc.stdin)
                    proc.stdin.flush()
                    answer = _checkout_answer(marshal.load(proc.stdout), nonce, request, self._key)
                except BaseException as exc:  # noqa: BLE001 - re-raised by run
                    with lock:
                        failures.append(exc)
                    return
                answers[index] = answer
                if any(answer):
                    with lock:
                        state["stop"] = min(state["stop"], index + 1)

        threads = [threading.Thread(target=feed, args=(proc,), daemon=True) for proc in procs]
        for thread in threads:
            thread.start()
        for thread in threads:
            thread.join()
        if failures:
            raise RuntimeError(f"checkout worker failed ({type(failures[0]).__name__}: {failures[0]})")
        return answers

    def close(self) -> None:
        errors = []
        native, self.native = self.native, None
        if native is not None:
            try:
                native.close()
            except BaseException as error:
                errors.append(error)
        procs, self._procs, self._ready = self._procs, [], 0
        for proc in procs:
            try:
                if proc.stdin is not None:
                    proc.stdin.close()
            except BaseException as error:
                errors.append(error)
        for proc in procs:
            try:
                proc.wait(timeout=30)
            except subprocess.TimeoutExpired:
                try:
                    proc.kill()
                    proc.wait(timeout=30)
                except BaseException as error:
                    errors.append(error)
            except BaseException as error:
                errors.append(error)
            finally:
                try:
                    if proc.stdout is not None:
                        proc.stdout.close()
                except BaseException as error:
                    errors.append(error)
        if len(errors) == 1:
            raise errors[0]
        if errors:
            raise RuntimeError(f"checkout worker cleanup errors: {errors!r}") from errors[0]


def _inspect_tracked_files(repo: Path, revision: str, items: Sequence[Tuple[str, str, str, str]],
                           env: Dict[str, str], workers: _CheckoutWorkers) -> Optional[str]:
    """Read each (path, mode, oid, label) in full: the first problem in `items`
    order, or None. Workers that cannot start, or that fail, leave every item
    to this process."""
    if workers.native_corruption:
        return f"native checkout protocol refused: {workers.native_corruption}"
    if workers.native is not None and items:
        for offset in range(0, len(items), native_checkout.MAX_ITEMS):
            batch = items[offset:offset + native_checkout.MAX_ITEMS]
            try:
                count, failures = workers.native.batch(repo, batch)
            except native_checkout.Corrupt as error:
                workers.native_corruption = str(error)
                return f"native checkout protocol refused: {error}"
            workers.native_bytes += count
            for failure in failures:
                problem = native_checkout.physical_problem(failure, batch[failure["index"]],
                                                           repo, revision, env, checkout_inputs)
                if problem:
                    return problem
                # The native bytes counter excludes mismatches; this original
                # committed-CRLF exception just accepted the captured full read.
                workers.native_bytes += failure["stat"]["bytes"]
        return None
    if workers.jobs > 1 and len(items) >= CHECKOUT_PARALLEL_MIN_FILES:
        low, high = CHECKOUT_BATCH_FILES
        size = max(low, min(high, len(items) // (workers.jobs * 8)))
        batches = [list(items[i:i + size]) for i in range(0, len(items), size)]
        try:
            answers = workers.run(os.fspath(repo), revision, env, batches)
        except (OSError, RuntimeError, ValueError) as exc:
            workers.decline(str(exc))
        else:
            answered = 0
            for batch, answer in zip(batches, answers):
                if answer is None:
                    break  # after a batch with a problem: never begun
                for problem in answer:
                    if problem:
                        return problem
                if len(answer) != len(batch):
                    return (f"a checkout worker answered {len(answer)} of {len(batch)} tracked inputs "
                            f"at {batch[0][3]!r}")
                answered += len(answer)
            if answered != len(items):
                return f"checkout workers answered {answered} of {len(items)} tracked inputs"
            return None
    for item in items:
        problem = _raw_tracked_problem(repo, revision, *item, env)
        if problem:
            return problem
    return None


# The pool of the gate run in progress (_checkout_workers_scope), if any.
_ACTIVE_CHECKOUT_WORKERS: Optional[_CheckoutWorkers] = None
_ACTIVE_CHECKOUT_TIMINGS = None
_CHECKOUT_BOUNDARY = "checkout"


def _at_checkout_boundary(name, operation):
    global _CHECKOUT_BOUNDARY
    previous, _CHECKOUT_BOUNDARY = _CHECKOUT_BOUNDARY, name
    try:
        return operation()
    finally:
        _CHECKOUT_BOUNDARY = previous


# How many programs the commit supplies, or that run in the checkout under its
# configuration, this process has started (_started_program): a leg, its
# prepare step, the push profile's `--list`, a Targo capability probe, the
# push. SourceBinding reads a boundary again whenever it moved.
_PROGRAMS_STARTED = 0


def _started_program() -> None:
    global _PROGRAMS_STARTED
    _PROGRAMS_STARTED += 1


class SourceBinding:
    """The checkout passes of one `run`: one complete pass wherever a program
    has started since the last pass that held (_started_program: a leg, its
    prepare step, the push profile's `--list`, a Targo capability probe, the
    push), and none where none has. The gate's own code between them (judging
    a log, storing a PASS, sizing and keying the next leg) starts none.

    Until 2026-11-13 `run` read every tracked file at each of "after X",
    "before publishing X" and "before Y", back to back with no program
    between them: 9 to 11 complete passes on a three-leg development run,
    355-720 s of 868-1,679 s (the four development runs of 2026-11-13,
    `record.json` `checkout_checks`). The second and third read the bytes the
    first had just read, with only this process running. A boundary answered
    by the last pass is recorded with `reused` naming it and reads no file.

    What is unchanged: a leg's verdict is published only after a complete
    pass that ended after the leg and after every read that judged it
    (`after X` follows the judgment), and a leg starts only after a complete
    pass with no program started since. A change that persists across a leg
    is refused at that leg's own after-pass. As before, a change made and
    undone while nothing looks is not detected: the one-writer-per-worktree
    rule forbids it (docs/LANDING_GATE.md). Reuse widens that window from a
    leg's own run to the run plus the gate's code after its after-pass and
    before the next leg's after-pass: an outside edit of a tracked file's
    bytes (in the checkout or in a populated submodule) made and undone
    there, or before a cached PASS or the final record, is not detected
    (DECISION_QUEUE READS-ONCE-WINDOW-1, docs/KNOWN_HAZARDS.md). No pass
    trusts a stat key (LAND-GATE-PUSHROWS-SPEED-1).

    `state` (`run` passes checkout_git_state) guards a reused boundary
    against a writer outside the gate: it is read before each complete pass,
    and a boundary reuses that pass only while it reads the same again; any
    other answer, or none, reads the checkout in full. It reads each
    repository's HEAD, index records and history overlays, the checkout's and
    every populated submodule's, and no file's bytes. So a commit, checkout
    or reset, in the checkout or in a populated submodule, an index edit
    (`git add`, an `update-index` flag) or a replacement ref made by another
    process between boundaries (CheckoutBindingTests: before the first leg,
    during a cache lookup; GitStateGuardTests) is refused before the next leg
    runs or a cached PASS is accepted, as when every boundary read. A change
    to sparse-checkout patterns or Git configuration is not in it: like a
    file edit, the next complete pass judges it if it is still there."""

    def __init__(self, check, state=None) -> None:
        self.check = check
        self.state = state
        self.held_at: Optional[str] = None  # the boundary of the last pass that held
        self.epoch = -1  # _PROGRAMS_STARTED when it held
        self.anchor: Optional[str] = None  # `state` read before that pass
        self.guard_seconds = 0.0  # time spent reading `state` at the current boundary

    def ran(self, what: str) -> None:
        """`what`, a program, is about to start: the next boundary reads."""
        _started_program()

    def _read_state(self) -> Optional[str]:
        started = time.monotonic()
        try:
            return self.state()
        finally:
            self.guard_seconds += time.monotonic() - started

    def _reusable(self) -> bool:
        if self.held_at is None or self.epoch != _PROGRAMS_STARTED:
            return False
        return self.state is None or (self.anchor is not None and self._read_state() == self.anchor)

    def problem(self, where: str, fresh: bool = False) -> Optional[str]:
        """Why the checkout no longer binds the planned commit at `where`, or
        None. `fresh` reads it in full whatever was reused before.

        Every read of `state` at this boundary (the guard of a reuse, and the
        anchor read before a complete pass, summed when a guard that did not
        match preceded that pass) is timed into `guard_seconds` on this boundary's
        `checkout_checks` row: a reused row's `seconds` is 0.0 because it
        read no file, and a complete row's `seconds` is the pass alone, so
        `targo trust meter` attributes the guard's time to the guard."""
        self.guard_seconds = 0.0
        timings = _ACTIVE_CHECKOUT_TIMINGS
        if not fresh and self._reusable():
            if timings is not None:
                timings.append({"boundary": where, "reused": self.held_at, "files": 0,
                                "seconds": 0.0, "refused": False,
                                **({"git_state": self.anchor,
                                    "guard_seconds": round(self.guard_seconds, 6)} if self.state else {})})
            return None
        epoch = _PROGRAMS_STARTED
        written = len(timings) if timings is not None else 0
        # Read before the pass: a commit, checkout or index edit made while it
        # reads leaves the anchor behind it, so the next boundary reads again.
        anchor = self._read_state() if self.state else None
        problem = _at_checkout_boundary(where, self.check)
        if self.state and timings is not None:
            row = next((row for row in timings[written:] if row.get("boundary") == where), None)
            if row is not None:
                row["guard_seconds"] = round(self.guard_seconds, 6)
        # A program started while the pass read leaves the epoch moved, so
        # the next boundary reads again.
        self.held_at, self.epoch, self.anchor = (None, -1, None) if problem else (where, epoch, anchor)
        return problem


# A gitlink record of `ls-files --cached --stage -v -z`: flag, object, path.
_INDEX_GITLINK = re.compile(r"(?:^|\0)(\S) 160000 ([0-9a-f]{40}(?:[0-9a-f]{24})?) 0\t([^\0]+)")


def checkout_git_state(root: Optional[Path] = None) -> Optional[str]:
    """One digest of the Git state a complete pass binds besides the bytes of
    tracked files, as _tracked_checkout_walk reads it, or None when any part
    cannot be read or the pass would refuse it: for the checkout and, in
    turn, every populated gitlink the pass would walk into
    (_populated_gitlink, sparse entries skipped as the pass skips them), the
    repository's HEAD (no replacement objects, the clone's own Git
    configuration), its index records with their flags (`ls-files --cached
    --stage -v` with sparse checkout off, the walk's own read) and its
    history overlays (_history_overlay_problem). An outside commit, checkout
    or reset, in the checkout or in a populated submodule, an outside
    `git add`, `rm --cached` or `update-index` flag, and a replacement ref or
    graft each change it. It reads no tracked file's bytes. SourceBinding's
    guard between complete passes."""
    env = git_query_env()
    env["GIT_NO_REPLACE_OBJECTS"] = "1"
    env.pop("GIT_REPLACE_REF_BASE", None)
    env.pop("GIT_GRAFT_FILE", None)
    try:
        top = Path(root or REPO_ROOT).resolve(strict=True)
    except (OSError, RuntimeError):
        return None
    digest = hashlib.sha256()

    def part(value: str) -> None:
        data = value.encode("utf-8", "surrogateescape")
        digest.update(len(data).to_bytes(8, "big") + data)

    pending, seen = [(top, ".")], set()
    while pending:
        repo, label = pending.pop()
        if repo in seen or len(seen) >= 1024:
            return None
        seen.add(repo)
        head = _git_ask(repo, env, "rev-parse", "--verify", "HEAD^{commit}", timeout=10)
        listing = _git_ask(repo, env, "-c", "core.sparseCheckout=false", "ls-files",
                           "--cached", "--stage", "-v", "-z", timeout=10)
        if head.returncode or listing.returncode or not head.stdout.strip():
            return None
        if _history_overlay_problem(repo, env):
            return None
        for value in (label, head.stdout.strip(), listing.stdout):
            part(value)
        for flag, oid, path in _INDEX_GITLINK.findall(listing.stdout):
            if flag == "S":
                continue
            refusal, child = _populated_gitlink(repo, top, path, oid, label + "/" + path, env, False)
            if refusal:
                return None
            part("populated" if child is not None else "absent")
            if child is not None:
                pending.append((child, label + "/" + path))
    return digest.hexdigest()


@contextlib.contextmanager
def _checkout_workers_scope():
    """One worker pool for every complete pass of a gate run (`run`,
    `push-rows`), forked and ready on entry, before the run asks Git or Targo
    anything and while the gate is single-threaded. No worker starts after
    that; every pass is read by these workers or in this process."""
    global _ACTIVE_CHECKOUT_WORKERS, _ACTIVE_CHECKOUT_TIMINGS
    if _ACTIVE_CHECKOUT_WORKERS is not None:
        yield _ACTIVE_CHECKOUT_WORKERS
        return
    workers = _CheckoutWorkers()
    _ACTIVE_CHECKOUT_WORKERS = workers
    _ACTIVE_CHECKOUT_TIMINGS = []
    try:
        workers.start()
        yield workers
    finally:
        _ACTIVE_CHECKOUT_WORKERS = None
        try:
            workers.close()
        finally:
            _ACTIVE_CHECKOUT_TIMINGS = None


@dataclass
class CheckoutTally:
    """What one complete checkout_problem pass did (tally=): `files` tracked
    files read in full and compared with the commit, in `seconds`, by `jobs`
    worker processes where a repository was big enough for them (1: all in the
    gate's own, as after any worker failure)."""
    files: int = 0
    jobs: int = 1
    seconds: float = 0.0
    backend: str = "python"
    native_seconds: float = 0.0
    native_bytes: Optional[int] = None
    native_threads: int = 0
    fallback: str = ""
    # Seconds of the pass spent in Git plumbing in the gate's process (the
    # inventory, history overlays, gitlinks, sparse rules, HEAD). The bytes a
    # pass read are native_bytes, the native reader's own count; the Python
    # reader counts none, and the inventory asks Git for no object sizes
    # (`ls-tree -l` reads every blob's header, and in a partial clone fetches
    # each one it lacks, sparse-excluded ones included).
    git_seconds: float = 0.0


def _populated_gitlink(repo: Path, root: Path, relative: str, expected: str, child_label: str,
                       env: Dict[str, str], ir_diagnostic: bool) -> Tuple[Optional[str], Optional[Path]]:
    """(problem, None), (None, None) for a gitlink left to its leg's own input
    gate, or (None, the populated repository to inspect at `expected`)."""
    child = repo / relative
    try:
        try:
            child.lstat()
        except FileNotFoundError:
            if ir_diagnostic:
                return f"IR diagnostic inventory requires populated gitlink {child_label!r}", None
            return None, None  # unpopulated; the leg's own input gate judges availability
        if not child.is_dir():
            return f"tracked gitlink is not a directory at {child_label!r}", None
        if not (child / ".git").exists():
            if ir_diagnostic or any(child.iterdir()):
                return f"populated gitlink has no inspectable index at {child_label!r}", None
            return None, None
        child = child.resolve(strict=True)
        child.relative_to(root)
    except (OSError, RuntimeError, ValueError):
        return f"cannot inspect or confine populated gitlink {child_label!r}", None
    top = _git_ask(child, env, "rev-parse", "--show-toplevel", timeout=10)
    head = _git_ask(child, env, "rev-parse", "--verify", "HEAD^{commit}", timeout=10)
    if top.returncode or head.returncode:
        return f"cannot read populated gitlink identity at {child_label!r}", None
    try:
        same_root = Path(top.stdout.strip()).resolve(strict=True) == child
    except (OSError, RuntimeError):
        same_root = False
    if not same_root or head.stdout.strip() != expected:
        return f"tracked inputs changed at populated gitlink {child_label!r}", None
    return None, child


def _tracked_checkout_problem(root: Path, revision: str, env: Dict[str, str], *,
                              ir_diagnostic: bool = False, tally: Optional[CheckoutTally] = None,
                              workers: Optional[_CheckoutWorkers] = None) -> Optional[str]:
    """Bind tracked physical inputs and gitlinks, regardless of Git hiding config.

    Only the explicit, version-bound IR diagnostic may restrict raw-file reads.
    Its required input files and repositories must still be present.
    `workers`: the caller's, left open; else the gate run's pool
    (_checkout_workers_scope); else none: outside a gate run, whose pool is
    started before anything it runs, the check is read in this process.
    """
    try:
        root = root.resolve(strict=True)
    except (OSError, RuntimeError) as exc:
        return f"cannot resolve the planned checkout ({exc})"
    workers = workers if workers is not None else _ACTIVE_CHECKOUT_WORKERS
    workers = _CheckoutWorkers(1) if workers is None else workers
    tally = tally if tally is not None else CheckoutTally()
    tally.files, tally.jobs = 0, 1
    started, git_before = time.monotonic(), _GIT_ASK_SECONDS[0]
    native_started = workers.native is not None
    tally.native_threads = workers.native.jobs if workers.native is not None else 0
    workers.native_bytes = 0
    problem = None
    try:
        if workers.native is not None:
            workers.native.program.bookend()
        problem = _tracked_checkout_walk(root, revision, env, ir_diagnostic, workers, tally)
        if workers.native is not None:
            workers.native.program.bookend()
            tally.backend = "native"
            tally.native_bytes = workers.native_bytes
    except native_checkout.Unavailable as error:
        # A lost process/capability supplied no physical verdict. Discard all
        # its observations and reread the ENTIRE pass through frozen Python.
        tally.native_seconds = time.monotonic() - started
        workers.native_fallback = str(error)
        native, workers.native = workers.native, None
        if native is not None:
            native.close()
        if problem is None:
            tally.files, tally.jobs = 0, 1
            problem = _tracked_checkout_walk(root, revision, env, ir_diagnostic, workers, tally)
            tally.backend = "python-fallback"
        else:
            # An already observed physical/protocol refusal is never erased by
            # a later runtime/capability loss or a concurrent repair.
            tally.backend = "native-refusal"
    if native_started and tally.backend == "native":
        tally.native_seconds = time.monotonic() - started
    tally.fallback = workers.native_fallback
    tally.seconds = time.monotonic() - started
    tally.git_seconds = _GIT_ASK_SECONDS[0] - git_before
    if workers.fallback:
        tally.jobs = 1
    if _ACTIVE_CHECKOUT_TIMINGS is not None:
        _ACTIVE_CHECKOUT_TIMINGS.append({"boundary":_CHECKOUT_BOUNDARY, "head":revision,
            "files":tally.files, "jobs":tally.jobs, "seconds":round(tally.seconds, 6),
            "backend":tally.backend, "native_seconds":round(tally.native_seconds, 6),
            "native_bytes":tally.native_bytes, "fallback":tally.fallback,
            "native_threads":tally.native_threads,
            "git_seconds":round(tally.git_seconds, 6),
            "files_per_s":round(tally.files / tally.seconds, 1) if tally.seconds > 0 else 0.0,
            "refused":problem is not None})
    return problem


def _tracked_checkout_walk(root: Path, revision: str, env: Dict[str, str], ir_diagnostic: bool,
                           workers: _CheckoutWorkers, tally: CheckoutTally) -> Optional[str]:
    pending = [(root, ".", revision)]
    seen = set()
    while pending:
        repo, label, revision = pending.pop()
        if repo in seen:
            return f"repeated or cyclic populated submodule at {label!r}"
        seen.add(repo)
        if len(seen) > 1024:
            return "populated submodule inventory exceeds the inspection bound"
        problem = _history_overlay_problem(repo, env)
        if problem:
            return f"{problem} at {label!r}"
        # A normal sparse-aware index read clears S in memory for a path that
        # reappeared on disk. Inspect the stored flags before judging presence;
        # the configuration override is local to this read and changes no flags.
        listing = _git_ask(repo, env, "-c", "core.sparseCheckout=false", "ls-files",
                           "--cached", "--stage", "-v", "-z", timeout=10)
        tree = _git_ask(repo, env, "ls-tree", "-r", "-z", revision, timeout=10)
        if listing.returncode or tree.returncode:
            failed = listing if listing.returncode else tree
            return f"cannot inspect tracked inventory at {label!r} ({_git_said(failed)})"
        index, committed, sparse = {}, {}, set()
        for row in listing.stdout.split("\0"):
            if not row:
                continue
            header, tab, path = row.partition("\t")
            fields = header.split()
            if not tab or len(fields) != 4 or not path:
                return f"unreadable tracked index record at {label!r}"
            flag, mode, oid, stage = fields
            if Path(path).is_absolute() or ".." in Path(path).parts:
                return f"unconfined tracked path at {label!r}"
            if len(flag) != 1 or not re.fullmatch(r"[0-7]{6}", mode) or stage != "0":
                return f"unreadable or unmerged tracked index at {label!r}"
            if flag.islower():
                return f"hidden index flag {flag!r} on tracked path {label + '/' + path!r}"
            if flag not in "HMRCKS" or not re.fullmatch(r"[0-9a-f]{40}(?:[0-9a-f]{24})?", oid):
                return f"unrecognized tracked index record at {label!r}"
            if path in index:
                return f"duplicate tracked index path at {label!r}"
            index[path] = (mode, oid)
            if flag == "S":
                sparse.add(path)
        for row in tree.stdout.split("\0"):
            if not row:
                continue
            header, tab, path = row.partition("\t")
            fields = header.split()
            if not tab or len(fields) != 3 or not path or path in committed:
                return f"unreadable committed tree at {label!r}"
            mode, kind, oid = fields
            if kind != ("commit" if mode == "160000" else "blob"):
                return f"unsupported committed tree entry at {label!r}"
            committed[path] = (mode, oid)
        if index != committed:
            return f"tracked inputs changed: index differs from HEAD at {label!r}"
        problem = _sparse_exclusion_problem(repo, sparse, label, env)
        if problem:
            return problem
        # Files are read after the walk over the commit, in its order; a
        # refusal met on the walk is reported only when no file before it has
        # a problem, as a check of each entry in turn would report it.
        files: List[Tuple[str, str, str, str]] = []
        refusal = None
        for relative, (mode, expected) in committed.items():
            child_label = label + "/" + relative
            physical_input = not ir_diagnostic or ir_diagnostic_physical_input(child_label)
            if relative in sparse and not (ir_diagnostic and (physical_input or mode == "160000")):
                continue
            if mode != "160000":
                if ir_diagnostic and mode == "120000" and ir_diagnostic_link_redirects(child_label):
                    refusal = (f"IR diagnostic: a committed link may stand for a path its readers open; "
                               f"complete physical checking required at {child_label!r}")
                    break
                if not physical_input:
                    continue
                if ir_diagnostic and mode == "120000":
                    refusal = f"IR diagnostic selected symlink requires complete physical checking at {child_label!r}"
                    break
                files.append((relative, mode, expected, child_label))
                continue
            refusal, child = _populated_gitlink(repo, root, relative, expected, child_label, env, ir_diagnostic)
            if refusal:
                break
            if child is not None:
                pending.append((child, child_label, expected))
        try:
            problem = _inspect_tracked_files(repo, revision, files, env, workers)
        except native_checkout.Unavailable as error:
            if not refusal:
                raise  # no physical verdict: the caller rereads the entire pass
            # This traversal already observed a definite deferred refusal.
            # Preserve its position after preceding files; a repaired gitlink
            # cannot erase it during a whole-pass retry after capability loss.
            workers.native_fallback = str(error)
            native, workers.native = workers.native, None
            if native is not None:
                native.close()
            tally.backend = "native-refusal"
            problem = _inspect_tracked_files(repo, revision, files, env, workers)
        tally.files += len(files)
        if workers.native is None and workers.jobs > 1 and len(files) >= CHECKOUT_PARALLEL_MIN_FILES:
            tally.jobs = workers.jobs  # this repository's files were read by the workers
        if problem or refusal:
            return problem or refusal
        # What Python imports here beside the tracked files (LAND-GATE-PY-SHADOW-1).
        problem = python_import_problem(repo, committed, label, label == ".")
        if problem:
            return problem
        current = _git_ask(repo, env, "rev-parse", "--verify", "HEAD^{commit}", timeout=10)
        if current.returncode or current.stdout.strip() != revision:
            return f"HEAD changed during tracked-input inspection at {label!r}"
    return None


def checkout_problem(expected_head: Optional[str], root: Optional[Path] = None, *,
                     history_only: bool = False, ir_diagnostic: bool = False,
                     tally: Optional[CheckoutTally] = None,
                     workers: Optional[_CheckoutWorkers] = None) -> Optional[str]:
    """Bind a verdict to the planned commit and unchanged tracked inputs.

    Check at execution and publication boundaries, including cached passes.
    This detects concurrent checkout/commit/edits; worktree ownership still
    forbids another writer during a leg rather than trusting an endpoint check
    to detect edits which a writer makes and then undoes. The IR-only diagnostic
    may restrict physical reads; it never claims complete checkout identity.
    Every tracked file is read in full on every call; `tally` (CheckoutTally)
    counts them, and `workers` (the caller's; else the gate run's pool; else
    this process) read them.
    """
    root = Path(root or REPO_ROOT)
    if expected_head is not None and not re.fullmatch(r"[0-9a-f]{40}(?:[0-9a-f]{24})?", expected_head):
        return "the planned HEAD is not a full commit identity"
    if os.environ.get("GIT_REPLACE_REF_BASE", "refs/replace/") != "refs/replace/" or "GIT_GRAFT_FILE" in os.environ:
        return "alternate Git replacement/graft environment changes check selection"
    env = git_query_env()
    env["GIT_NO_REPLACE_OBJECTS"] = "1"
    env.pop("GIT_REPLACE_REF_BASE", None)
    env.pop("GIT_GRAFT_FILE", None)
    head = _git_ask(root, env, "rev-parse", "--verify", "HEAD^{commit}", timeout=10)
    if head.returncode or not head.stdout.strip():
        return f"cannot read the current HEAD ({_git_said(head)})"
    if expected_head is not None and head.stdout.strip() != expected_head:
        return f"HEAD changed from planned {expected_head[:12]} to {head.stdout.strip()[:12]}"
    if history_only:
        # The selector has not run yet. Check root history now; the complete
        # physical/rooted-child check follows selection before any leg runs.
        return _history_overlay_problem(root, env)
    return _tracked_checkout_problem(root, head.stdout.strip(), env, ir_diagnostic=ir_diagnostic, tally=tally,
                                     workers=workers)


LANDING_TARGO_ROW = "scoped.targo-trust-unit-tests"
LANDING_TARGO_ROW_COMMAND = "bash scripts/check_targo_trust_unit_tests.sh"


def landing_targo_rows(head: str) -> List["PushRow"]:
    """The push profile's scoped Targo rows at `head`, read from git objects
    (push_profile_rows). The pre-push hook runs the landing Targo suite only
    inside such a row (pre-push's run_lane sets LAND_TARGO_STATUS only for
    it), so `land` defers the targo-trust leg into the push only when there is
    one (round 5, D2). RuntimeError when the profile cannot be read."""
    return [row for row in push_profile_rows(REPO_ROOT, rev=head) if row.id == LANDING_TARGO_ROW]


def land_runs_fresh(leg: Leg, land_transaction: bool) -> bool:
    """Whether `leg` must run in this gate even when every key is a cached
    PASS: under `land`, the targo-trust suite (landing_targo's contract: one
    ordinary push runs the full Targo suite, never a cached PASS). With no
    scoped Targo row in the pushed profile to carry it (round 5, D2) it runs
    here, fresh, before the push."""
    return land_transaction and leg.id == "targo-trust"


def transaction_hook_problem(head: str) -> Optional[str]:
    """The synchronous land action requires this checkout's real hook.

    This does not change standalone run's conservative hook-path decision.
    A live transaction may add the full suite, but cannot skip any hook row.

    A push profile WITHOUT the scoped Targo row is no problem (round 5, D2).
    Since 39b35cb9f7 (DEV-MAIN-FOCUSED-VALIDATION, 2026-11-02) the profile
    holds no scoped.* row, and round 4's "exactly one" rule refused every
    `land`. The hook then runs no Targo suite, so `land` defers nothing: the
    gate runs the targo-trust leg itself, fresh and never from a cached PASS
    (_cmd_run), and the push carries no handoff. A profile that HAS the row
    must hold exactly one, required, with the canonical command. Only that row
    can carry the deferred suite, and the hook's final check requires its exit.
    """
    installed = hook_installed()
    if not installed.active:
        return installed.why
    try:
        rows = landing_targo_rows(head)
    except RuntimeError as exc:
        return f"cannot read the push profile the hook runs: {exc}"
    if rows and (len(rows) != 1 or rows[0].required != "true" or rows[0].command != LANDING_TARGO_ROW_COMMAND):
        return "a push profile with a scoped Targo row needs exactly one, required, with the canonical command"
    return landing_targo.protocol_problem(REPO_ROOT)


_ACTIVE_PUBLICATION_CHECK = None


@contextlib.contextmanager
def publication_lease():
    """Serialize cooperating local worktrees, never remote writers or grants.

    The original kernel lock stays owned through discovery, fresh qualification,
    composition and the actual CAS/ACK. Its persistent file is never unlinked.
    Existing outer machine admission remains independently owned while waiting.
    """
    global _ACTIVE_PUBLICATION_CHECK
    previous = _ACTIVE_PUBLICATION_CHECK
    path = common_dir() / "trust-land-publication.lock"
    fd = os.open(path, os.O_RDWR | os.O_CREAT | os.O_CLOEXEC | os.O_NOFOLLOW, 0o600)
    try:
        original = os.fstat(fd)
        if (not stat.S_ISREG(original.st_mode) or original.st_nlink != 1
                or original.st_uid != os.getuid() or original.st_mode & 0o077):
            raise RuntimeError("unsafe repository publication lease")
        def current():
            held = os.fstat(fd)
            if (held.st_dev, held.st_ino) != (original.st_dev, original.st_ino):
                raise RuntimeError("original repository publication lease changed")
            observed = path.stat(follow_symlinks=False)
            if (observed.st_dev, observed.st_ino) != (original.st_dev, original.st_ino):
                raise RuntimeError("repository publication lease was replaced")
        print("land-gate: waiting for local repository publication lease", flush=True)
        while True:
            _check_cancellation()
            current()
            try:
                fcntl.flock(fd, fcntl.LOCK_EX | fcntl.LOCK_NB)
                break
            except BlockingIOError:
                time.sleep(0.05)
        current()
        print("land-gate: acquired local repository publication lease", flush=True)
        _ACTIVE_PUBLICATION_CHECK = current
        yield current
        current()
    finally:
        _ACTIVE_PUBLICATION_CHECK = previous
        # Explicit unlock also releases ownership if a transient fork retained
        # a non-owning copy before exec. Close is the original-owner crash path.
        try:
            fcntl.flock(fd, fcntl.LOCK_UN)
        finally:
            os.close(fd)


def cmd_land(args) -> int:
    with _cancellation_scope():
        with publication_lease() as current:
            return _cmd_land_owned(args, current)


def _cmd_land_owned(args, current) -> int:
    args.land, args.only, args.dry_run = True, None, False
    session = DiscoverySession()
    for _attempt in range(4):
        try:
            current()
            return cmd_run(args, session)
        except LandingRefreshRequired as changed:
            try:
                session.compose(changed.landing)
            except RuntimeError as error:
                print(f"LAND-GATE: NOT JUDGED — {error}")
                return 2
    return 2


def cmd_run(args, discovery: Optional[DiscoverySession] = None) -> int:
    with _cancellation_scope() as cancellation:
        with _cancellable_stdout(cancellation):
            result = _cmd_run(args, discovery)
        cancellation.check()
    cancellation.check()
    return result


def _cmd_run(args, discovery: Optional[DiscoverySession] = None) -> int:
    with _checkout_workers_scope():
        return _cmd_run_in_scope(args, discovery)


def _cmd_run_in_scope(args, discovery: Optional[DiscoverySession] = None) -> int:
    land_transaction = getattr(args, "land", False)
    discovery = discovery if discovery is not None else DiscoverySession()
    development = getattr(args, "development", False)
    source_diagnostic = source_diagnostic_only(getattr(args, "only", None), land_transaction)
    if git("status", "--porcelain", "--untracked-files=no", "--ignore-submodules=none"):
        print("land-gate: the worktree has uncommitted changes to tracked files; commit first. "
              "A landing judges a commit, and a cache key names one.", file=sys.stderr)
        return 2
    problem = checkout_problem(None, history_only=True)
    if problem:
        print(f"LAND-GATE: NOT JUDGED — {problem}. No selection or leg ran.")
        return 2
    # The run's wall clock: record.json `seconds` is read from it, and nothing
    # else binds this name (the discovery below keeps its own monotonic clock;
    # rebinding this one made `seconds` epoch-minus-uptime, about 1.79e9).
    run_started = time.time()
    try:
        host = host_budget.measure()
    except host_budget.HostUnmeasurable as exc:
        print(f"land-gate: CANNOT MEASURE this host ({exc}); nothing was judged", file=sys.stderr)
        return 2
    plans = budget_plans(host)
    for p in plans.values():
        print(host_budget.describe_plan(host, p))
    if not plans["rustc-build"].admitted:
        print("land-gate: REFUSED — not even one compiler job fits in the measured room; nothing was judged")
        return 2
    governor = host_budget.governor_floors(host)
    # Explicit IR-only diagnostics always report PARTIAL. No source push or
    # proof result may reuse this narrower physical-read or planning scope.
    requested_ir = source_diagnostic and set(args.only) == {"ir-cohort"}
    diagnostic_head = git("rev-parse", "--verify", "HEAD^{commit}") if requested_ir else None
    ir_diagnostic = requested_ir and ir_diagnostic_readers_match(diagnostic_head)
    if ir_diagnostic:
        sel, base = ir_diagnostic_selection(args.base, diagnostic_head)
        g = None
    else:
        # Unknown reader versions and every ordinary plan retain the complete
        # Rust selector. Development makes no full resolver attestation.
        try:
            if (development or source_diagnostic) and not land_transaction:
                # Source diagnostics remain useful when publication cannot be
                # judged. The existing runner withholds push rows in that case.
                # Timed whole, not itemised: this path takes no progress
                # observer and prints no discovery lines.
                discovery_started = time.monotonic()
                if development:
                    g, sel, base = _compute_in_session(discovery,
                        args.base, "HEAD", verify=False, profile=DiscoveryProfile.DEVELOPMENT)
                else:
                    g, sel, base = _compute_in_session(discovery, args.base, "HEAD", verify=True,
                                                     profile=DiscoveryProfile.FULL)
                sel.discovery = discovery_record(None, g, seconds=time.monotonic() - discovery_started)
                landing = read_landing(head=sel.head)
            else:
                g, sel, base, landing = discover_landing(args.base, verify=not development,
                                                       compose=land_transaction, session=discovery,
                                                       profile=(DiscoveryProfile.DEVELOPMENT if development
                                                                else DiscoveryProfile.FULL))
        except LockedWorkspaceInputs:
            # Preserve the typed refusal and its complete resolver evidence
            # for main()'s existing durable record owner.
            raise
        except RuntimeError as error:
            print(f"LAND-GATE: NOT JUDGED — {error}. No leg or push ran.")
            return 2
    revision = sel.head
    def check_source():
        return checkout_problem(revision, ir_diagnostic=True) if ir_diagnostic else checkout_problem(revision)
    binding = SourceBinding(check_source, state=checkout_git_state)
    agh_publication = land_transaction and remote_tips.github_repository(landing.remote) is not None
    if ir_diagnostic:
        landing = read_landing(head=sel.head)
    # Before the pass below: the hook's state runs the push profile's
    # `--list`, a program of the commit (SourceBinding).
    hook = (PushHook(False, "native Agh publication executes fresh push rows inside this gate")
            if agh_publication else push_hook_state(sel.changed, sel.head, landing=landing))
    # Whether `land` hands the targo-trust leg to the pushed hook's scoped
    # Targo row (round 5, D2): only when the profile being pushed has one.
    defer_targo = False
    if land_transaction:
        problem = None if agh_publication else transaction_hook_problem(revision)
        if problem:
            print(f"LAND-GATE: NOT JUDGED — {problem}. No leg or push ran.")
            return 2
        try:
            defer_targo = not agh_publication and bool(landing_targo_rows(revision))
        except RuntimeError as exc:
            print(f"LAND-GATE: NOT JUDGED — cannot read the push profile the hook runs: {exc}. "
                  "No leg or push ran.")
            return 2
        if landing.head == landing.tip:
            print("LAND-GATE: NOT JUDGED — remote main already has HEAD; no hook would execute")
            return 2
    # After every program the gate runs before its legs (the hook state's and
    # `land`'s reads of the push profile run the commit's `--list`), so the
    # first leg's own boundary reuses this pass (SourceBinding).
    problem = binding.problem("before legs")
    if problem:
        print(f"LAND-GATE: NOT JUDGED — {problem}. No leg ran.")
        return 2
    if ir_diagnostic:
        legs = [ir_cohort_leg()]
        admitted = host_budget.admitted_jobs()
        jobs = plans["rustc-build"].jobs
        legs[0].default_env["RAYON_NUM_THREADS"] = str(min(jobs, admitted) if admitted is not None else jobs)
    elif isinstance(sel, DeclaredDevelopmentSelection):
        legs = declared_development_legs(g, sel, plans["rustc-build"].jobs, hook, landing)
    else:
        legs = build_legs(g, sel, base, plans, hook, landing)
    if development and not ir_diagnostic and not isinstance(sel, DeclaredDevelopmentSelection):
        try:
            legs = development_legs(g, sel, legs, plans["rustc-build"].jobs, landing)
        except RuntimeError as exc:
            print(f"LAND-GATE: NOT JUDGED — {exc}. No leg ran.")
            return 2
    if land_transaction:
        # Source checks bind the captured immutable tree. Publication rows are
        # deliberately last: their live destination check must not starve all
        # component qualification when main advances during discovery.
        legs = [leg for leg in legs if leg.id != "push-rows"] + [
            leg for leg in legs if leg.id == "push-rows"]
    print_plan(sel, legs, hook, landing, source_diagnostic, development)
    refused = landing_refusal(hook, landing, source_diagnostic=source_diagnostic)
    if refused and not development:
        print(f"LAND-GATE: NOT JUDGED — a leg here judges this landing's push (no hook runs every row a leg "
              f"stands in for) and that push cannot be stated: {refused}. No leg ran: it would be NOT JUDGED, "
              "or test only the selection's range, after every other leg had spent its time.")
        return 2
    toolchain = {} if ir_diagnostic else toolchain_identity()
    # Each gate its own directory, made atomically: worktrees of one clone
    # share these, and two gates started in one second shared one before, its
    # leg logs (one gate graded the other's output) and every row's `run`. The
    # first gate of a second keeps the plain name readers match; a later one
    # takes `.002`, `.003`, ..., so names still sort in start order.
    runs = common_dir() / "trust-land" / "runs"
    runs.mkdir(parents=True, exist_ok=True)
    stamp = time.strftime("%Y%m%dT%H%M%S")
    n = 1
    while True:
        run_dir = runs / (stamp if n == 1 else f"{stamp}.{n:03d}")
        try:
            run_dir.mkdir()
            break
        except FileExistsError:
            n += 1
    record = {"schema": SCHEMA, "head": revision, "base": base, "changed": len(sel.changed),
              "profile": "development" if development else "full-diagnostic",
              "everything": sel.everything[:20], "host": host._asdict(),
              "plans": {k: v._asdict() for k, v in plans.items()}, "governor_gib": governor,
              "push_hook": {"active": hook.active, "why": hook.why, "rule": hook.fired,
                            "answers": sorted(hook.answers), "gaps": hook.gaps},
              "landing": landing_json(landing), "source_diagnostic_only": source_diagnostic,
              "discovery": getattr(sel, "discovery", None),
              "physical_input_scope": "ir-cohort-declared-reads" if ir_diagnostic else "complete-checkout",
              "selection_scope": ("explicit-ir-cohort" if ir_diagnostic else
                                  "declared-development-ownership" if isinstance(sel, DeclaredDevelopmentSelection)
                                  else "Rust-reachability"),
              "legs": {}}
    development_push_problem = ((landing.why or "a fresh stated contained landing is required")
                                if development and (not landing.stated or not landing.contained) else None)
    failed = judged_nothing = 0
    not_run_selected: List[str] = []
    deferred_targo = None
    deferred_keys: List[str] = []
    # {shared build: (the leg that failed it, how it compiled it, why)} (EW-19).
    broken: Dict[str, Tuple[str, str, str]] = {}

    def source_refusal(where: str, fresh: bool = False) -> bool:
        problem = binding.problem(where, fresh=fresh)
        if not problem:
            return False
        record["source_refusal"] = {"boundary": where, "reason": problem}
        print(f"LAND-GATE: NOT JUDGED — {problem} ({where}). No further result is accepted.")
        return True

    no_reachability = ir_diagnostic or isinstance(sel, DeclaredDevelopmentSelection)
    gfp = None if no_reachability else global_fingerprint(g)
    # Bind the effective child environment once, after each leg is rescaled.
    s1_inputs_key = None if no_reachability else stage1_key(g, toolchain, env={})
    split_keys: Dict[str, str] = {}
    recorded: set = set()  # legs whose outcome is in the cache (record_observed_exit)

    def leg_keys(leg: Leg) -> List[Tuple[Optional[str], str]]:
        if ir_diagnostic:
            if (leg.id != "ir-cohort" or leg.needs_stage1 or leg.prepare
                    or leg.stage1_members or leg.cache_members or leg.id not in UNCACHED_LEGS):
                raise RuntimeError("explicit IR diagnostic cannot key or run another leg")
            return []
        return cache_keys(leg, g, sel, toolchain, gfp, s1_inputs_key)

    def note_splits(leg: Leg, entry: Dict[str, object], keys: Sequence[Tuple[Optional[str], str]]) -> None:
        """Name every key here that is split (EW-21), once each."""
        for m, k in keys:
            why = cache_split(k)
            if why and k not in split_keys:
                name = f"{leg.id} {m}" if m else leg.id
                split_keys[k] = f"{name}: {why}"
                entry.setdefault("split_keys", []).append({"key": k, "member": m, "why": why})
                print(f"SPLIT KEY {k} ({name}): {why}; it serves no PASS")

    def record_outcome(leg: Leg, entry: Dict[str, object], keys: Sequence[Tuple[Optional[str], str]],
                       verdict: str, why: str = "", seconds: Optional[float] = None, quiet: bool = False) -> None:
        """Record a run's outcome that is not a PASS under each key it answers
        for. A record that cannot be written (the disk that failed the leg)
        never changes the verdict: the record says so. `quiet`: a cancelled
        gate, whose every print raises, records and says nothing."""
        recorded.add(leg.id)
        for m, k in keys:
            row = {"leg": leg.id, "member": m, "run": str(run_dir), "head": revision, "seconds": seconds, "why": why}
            if verdict == CACHE_FAIL:
                row["run_keys"] = [key for _m, key in keys]
                row["unkeyed_work"] = sorted({*leg.hookless_members, *leg.hookless_instruments}) or leg.force_run
            try:
                cache_record(k, verdict, row)
            except OSError as exc:
                entry["cache_record_failed"] = str(exc)
                if not quiet:
                    print(f"{leg.id}: could not record {verdict} under {k}: {exc}")
        if not quiet:
            note_splits(leg, entry, keys)

    def record_observed_exit(leg: Leg, entry: Dict[str, object], rc: int, log: str, prepare_failed: bool,
                             failed_in: Sequence[Tuple[Optional[str], str]], secs: float, cause: str) -> None:
        """The leg's own exit was observed, and the gate stops before it
        records its outcome (a cancellation; a cleanup that failed after the
        exit): record that exit as the run would have judged it, without a
        print (under a cancellation each raises) and without the source check
        (a FAIL under a key the tree no longer has only makes a later run of
        it run). A PASS is never recorded here: such a gate publishes none.
        As after any leg, a source that changed while it ran makes the exit
        NOT JUDGED rather than evidence about the commit (review of EW-1); the
        check prints nothing."""
        if leg.id in recorded:
            return
        try:
            moved = check_source()
        except Exception as exc:  # noqa: BLE001 - an unchecked source judges nothing
            moved = f"the source could not be checked: {exc}"
        if moved:
            record.setdefault("source_refusal", {"boundary": f"after {leg.id} (stopped)", "reason": moved})
            record_outcome(leg, entry, ran, CACHE_NOT_JUDGED, "the source changed", round(secs, 1), True)
            return
        why = f"exit {rc}, recorded unjudged: {cause}"
        if prepare_failed:
            named = [mk for mk in failed_in if leg.needs_stage1 or mk[0] in leg.stage1_members]
            record_outcome(leg, entry, named, CACHE_FAIL, f"its prepare step exited {rc}", round(secs, 1), True)
            record_outcome(leg, entry, [mk for mk in failed_in if mk not in named], CACHE_COULD_NOT_RUN,
                           f"the stage-1 prepare it needed exited {rc}; its tests never ran", round(secs, 1), True)
            return
        if leg.id in SUITE_BASELINES:
            try:
                accepted = baseline_rows((REPO_ROOT / SUITE_BASELINES[leg.id]).read_text(encoding="utf-8"))
                rc, _why = judge_suite(Path(log).read_text(encoding="utf-8", errors="replace"), rc, accepted,
                                       leg.run_targets)
            except OSError:
                rc = 2
        if rc == 0:
            return
        if rc in NOT_JUDGED_EXITS.get(leg.id, (2,)):
            record_outcome(leg, entry, ran, CACHE_NOT_JUDGED, why, round(secs, 1), True)
        else:
            record_outcome(leg, entry, failed_in, CACHE_FAIL, why, round(secs, 1), True)

    def record_unrun(leg: Leg, entry: Dict[str, object], verdict: str, why: str, size: bool = True) -> None:
        """Record why a leg that never started has no answer, under the key a
        run of it would have looked up (sized as a run would be, unless sizing
        is what refused it): best effort, since a leg that cannot be sized or
        keyed has no complete key to name."""
        try:
            if size:
                rescale(leg, host_budget.measure())
        except (RuntimeError, ValueError):
            pass  # host_budget's refusals: the start-of-run plan stands
        try:
            keys = leg_keys(leg)
        except (RuntimeError, ValueError, KeyError, OSError) as exc:
            entry["cache_record_failed"] = f"no complete key: {exc}"
            return
        record_outcome(leg, entry, keys, verdict, why)

    retry_landing = None
    unavailable_publication_prerequisite = None
    for leg in legs:
        _check_cancellation()
        entry: Dict[str, object] = {"selected": leg.selected, "reasons": leg.reasons, "command": leg.command,
                                    "targets": leg.targets}
        record["legs"][leg.id] = entry
        if leg.id == "push-rows" and development_push_problem:
            entry["outcome"] = "NOT JUDGED (fresh stated landing required)"
            entry["reason"] = development_push_problem
            judged_nothing += 1
            print(f"\nPUSH-ROWS NOT JUDGED: {development_push_problem}; independent source checks continue")
            continue
        if leg.diagnostic_only:
            entry["outcome"] = "NOT RUN (explicit development profile; full diagnostic selection retained)"
            print(f"\nDIAGNOSTIC NOT RUN {leg.id}: full selection={leg.selected}; " + "; ".join(leg.reasons[:2]))
            continue
        if args.only and leg.id not in args.only:
            entry["outcome"] = "NOT RUN (--only)"
            if leg.selected:
                not_run_selected.append(leg.id)
            continue
        if not leg.selected:
            entry["outcome"] = "SKIPPED"
            print(f"\nSKIPPED {leg.id}: {leg.reasons[0]}")
            continue
        if unavailable_publication_prerequisite is not None:
            entry["outcome"] = f"NOT RUN (publication prerequisite {unavailable_publication_prerequisite} not judged)"
            not_run_selected.append(leg.id)
            print(f"\n{entry['outcome']} {leg.id}")
            continue
        # Before the cache: a cached PASS of a leg whose build fails now
        # answers for nothing. COULD NOT RUN is never a PASS (EW-19).
        blocked = could_not_run(leg, broken)
        if blocked:
            entry["outcome"] = f"COULD NOT RUN ({blocked})"
            judged_nothing += 1
            print(f"\nCOULD NOT RUN {leg.id}: {blocked}")
            record_unrun(leg, entry, CACHE_COULD_NOT_RUN, blocked)
            continue
        # A leg that prepares the stage 1 runs x.py too, under the same seed
        # admission (crates-tests with TRUST_RUSTC-1 members).
        runs_xpy = leg.id in XPY_LEGS or bool(leg.prepare and leg.stage1_members)
        unready = xpy_unready() if runs_xpy else None
        # A targo leg whose command this PATH's targo cannot run (round 5, D3):
        # NOT JUDGED, as an unready x.py is, never the change's FAIL.
        if not unready and not args.dry_run:
            if leg.command[:1] == ["targo"]:
                binding.ran(f"the Targo capability probe for {leg.id}")  # targo_unready runs that targo
            unready = targo_unready(leg)
        if unready and not args.dry_run:
            entry["outcome"] = f"NOT JUDGED ({unready})"
            judged_nothing += 1
            print(f"NOT JUDGED {leg.id}: {unready}")
            record_unrun(leg, entry, CACHE_NOT_JUDGED, unready)
            continue
        try:
            # Validate admission before measuring: a failed host read must not
            # turn a missing managed share into the older-plan fallback.
            host_budget.admitted_jobs()
            entry["scaled"] = rescale(leg, host_budget.measure())
            entry["command"] = leg.command
        except (host_budget.AdmissionInvalid, RescaleRefused) as exc:
            entry["outcome"] = f"NOT JUDGED (host budget refused: {exc})"
            judged_nothing += 1
            print(f"NOT JUDGED {leg.id}: host budget refused: {exc}")
            record_unrun(leg, entry, CACHE_NOT_JUDGED, f"host budget refused: {exc}", size=False)
            continue
        except host_budget.HostUnmeasurable as exc:
            entry["scaled"] = f"kept the start-of-run plan: {exc}"
        if land_transaction and leg.id == "targo-trust" and defer_targo:
            if leg.command != landing_targo.COMMAND or leg.prepare:
                raise RuntimeError("the full Targo command changed; live handoff requires review")
            deferred_targo = leg
            # The keys its run under `run` would record under: the hook files
            # its FAIL or NOT JUDGED there (cmd_landing_targo).
            deferred_keys = [k for _m, k in leg_keys(leg)]
            note_splits(leg, entry, leg_keys(leg))
            entry["outcome"] = "PENDING (ordinary pre-push execution, not a PASS)"
            print("PENDING targo-trust: its full suite will execute inside this action's ordinary push")
            continue
        # Rayon defaults can change with this measurement. Key the settings the
        # child will actually receive, before looking up or storing a PASS.
        keys = leg_keys(leg)
        note_splits(leg, entry, keys)
        on_disk = None if ir_diagnostic else (rustc_identity() or ["no stage 1"])
        hits = [cache_lookup(k, cached_sysroot(leg, m, on_disk))
                for m, k in keys] if (keys and not args.no_cache
                                      and not land_runs_fresh(leg, land_transaction)) else []
        # A member this run is about to run may be the last key a joint FAIL
        # lacks a PASS for: its fresh PASS would split a member served here,
        # after the fact. Each miss counts as passing, until none moves.
        while hits and not all(hits):
            misses = frozenset(k for (_m, k), h in zip(keys, hits) if not h)
            again = [h and cache_lookup(k, cached_sysroot(leg, m, on_disk), misses)
                     for (m, k), h in zip(keys, hits)]
            if [bool(h) for h in again] == [bool(h) for h in hits]:
                break
            hits = again
        if keys and hits and all(hits) and not leg.force_run:
            if source_refusal(f"before cached {leg.id}"):
                entry["outcome"] = "NOT JUDGED (source changed)"
                judged_nothing += 1
                record_outcome(leg, entry, keys, CACHE_NOT_JUDGED, "the source changed")
                break
            entry["outcome"] = "CACHED PASS"
            entry["cached_from"] = [h.get("run") for h in hits]
            print(f"\nCACHED PASS {leg.id}: every input identical to a passing run ({hits[0].get('run')})")
            continue
        # What this run answers for: a member a PASS still serves is not in it.
        ran = [mk for mk, h in zip(keys, hits) if not h] if hits else keys
        # What its failure may belong to. check_compiler_unit_tests.sh only
        # ADDS --also to the suites its own diff selects, so a narrowed run can
        # still run (and fail in) a member a PASS answered for here: its FAIL
        # names every member the script says it ran (unit_scope, read from the
        # log below), every key of the leg when it says nothing. Its PASS still
        # names only `ran`: no row without a run behind it.
        failed_in = ran
        if leg.cache_members and hits:
            todo = [m for (m, _k), h in zip(keys, hits) if not h]
            if todo != leg.cache_members:
                leg.command = _narrow(leg, todo)
                entry["cached_members"] = sorted(set(leg.cache_members) - set(todo))
                entry["command"] = leg.command
                if not stage1_prepare_needed(leg, todo):
                    # Every member that needed the stage 1 is answered by a
                    # PASS stored with this very sysroot and this tree's
                    # stage-1 inputs: nothing left runs it.
                    leg.prepare = None
        extra_env: Dict[str, str] = {}
        # A leg builds the stage 1 when it is a stage-1 suite, or when it
        # prepares one for the members that run it (crates-tests, TRUST_RUSTC-1).
        builds_stage1 = leg.needs_stage1 or bool(leg.prepare and leg.stage1_members)
        if builds_stage1:
            # No declared component plan computed a compiler readset. It must
            # execute normal x.py freshness, never import or publish a gate
            # stage1 stamp from that incomplete knowledge.
            s1_key = (stage1_environment_key(s1_inputs_key, leg)
                      if s1_inputs_key is not None else None)
            if s1_key is not None and stage1_reusable(s1_key):
                if leg.needs_stage1:
                    leg.command = leg.command + ["--keep-stage", "0", "--keep-stage-std", "1"]
                if leg.prepare:
                    leg.prepare = leg.prepare + ["--keep-stage", "0", "--keep-stage-std", "1"]
                entry["stage1"] = "reused (stamp matches the stage-1 inputs)"
            else:
                try:
                    stage1_stamp_path().unlink()
                except OSError:
                    pass
                entry["stage1"] = ("built" if s1_key is not None else
                                   "normal x.py freshness; gate stage1 stamp disabled")
        entry["command"] = leg.command
        print(f"\nRUN {leg.id}: {(' '.join(leg.prepare) + ' && ') if leg.prepare else ''}{' '.join(leg.command)}")
        if args.dry_run:
            entry["outcome"] = "DRY RUN"
            continue
        if source_refusal(f"before {leg.id}"):
            entry["outcome"] = "NOT JUDGED (source changed)"
            judged_nothing += 1
            record_outcome(leg, entry, ran, CACHE_NOT_JUDGED, "the source changed")
            break
        def fail_scope(rc: int, log: str) -> List[Tuple[Optional[str], str]]:
            if leg.id != "compiler-unit-tests" or rc == 0:
                return failed_in
            try:
                scope = unit_scope(Path(log).read_text(encoding="utf-8", errors="replace"))
            except OSError:
                scope = None
            return keys if scope is None else [mk for mk in keys if mk in ran or mk[0] in scope]

        binding.ran(leg.id)
        try:
            rc, secs, log, prepare_failed = run_leg(leg, run_dir, extra_env, governor)
        except LegCleanupFailed as exc:
            # The exit was observed and reaped; only the cleanup after it
            # failed. Record it, then refuse as before.
            entry.update({"rc": exc.returncode, "seconds": round(exc.seconds, 1), "log": exc.log,
                          "outcome": f"NOT JUDGED (cleanup failed after exit {exc.returncode})"})
            record_observed_exit(leg, entry, exc.returncode, exc.log, exc.prepare,
                                 fail_scope(exc.returncode, exc.log), exc.seconds, exc.cause)
            raise
        except GateCancelled as exc:
            # Cancelled while the exit it had already made was drained or its
            # group retired: that exit is still this leg's (review of EW-1).
            if exc.observed_returncode is not None:
                record_observed_exit(leg, entry, exc.observed_returncode, exc.log, exc.prepare,
                                     fail_scope(exc.observed_returncode, exc.log), exc.seconds,
                                     "the gate was cancelled")
            raise
        entry.update({"rc": rc, "seconds": round(secs, 1), "log": log})
        failed_in = fail_scope(rc, log)
        try:
            shared: List[Tuple[str, str, str]] = []
            if rc != 0 and leg.shared_builds:
                try:
                    shared = shared_build_failures(Path(log).read_text(encoding="utf-8", errors="replace"), leg,
                                                   prepare_failed)
                except OSError:
                    shared = []
            # Every read that judges the leg (its log, a known-red set, a
            # recipe's case data) comes before the pass after it, so that pass
            # binds the verdict as well as the leg's run (SourceBinding).
            suite_said = None
            if not prepare_failed:
                if leg.id.startswith("development-package-"):
                    from land_development import (CONTROLLER_DESCRIPTOR_LEG, LOCAL_GIT_CORE_LEG, LOCAL_GIT_FIXTURE_LEG,
                                                  TARGO_NATIVE_CORE_LEG, TARGO_CLEANUP_LEG, TARGO_NATIVE_CORE_CASES,
                                                  TARGO_CLEANUP_CASES, TOOL_NAME_LEG, TOOL_NAME_CASES,
                                                  TARGO_TRUST_TRIPWIRE_LEG)
                    # The tripwire leg names one exact test: exactly one must pass.
                    required_count = {TARGO_NATIVE_CORE_LEG: len(TARGO_NATIVE_CORE_CASES),
                                      TARGO_CLEANUP_LEG: len(TARGO_CLEANUP_CASES),
                                      TOOL_NAME_LEG: TOOL_NAME_CASES,
                                      TARGO_TRUST_TRIPWIRE_LEG: 1}.get(leg.id)
                    rc, why = development_test_result(
                        Path(log).read_text(encoding="utf-8", errors="replace"), rc,
                        all_required=leg.id in (LOCAL_GIT_CORE_LEG, LOCAL_GIT_FIXTURE_LEG, CONTROLLER_DESCRIPTOR_LEG),
                        expected_count=required_count, multiple_suites="--all-targets" in leg.command)
                    entry["judged"] = why
                from land_development import TARGO_CORE_EXAMPLE_LEG
                if leg.id == TARGO_CORE_EXAMPLE_LEG:
                    rc, why = development_example_result(Path(log).read_text(encoding="utf-8", errors="replace"), rc)
                    entry["judged"] = why
                if leg.id == "development-recipes":
                    import land_development
                    rc, why = land_development.recipe_result(run_dir / "development-recipes.cases", leg.run_targets,
                                                            Path(log).read_text(encoding="utf-8", errors="replace"), rc,
                                                            REPO_ROOT, host_triple())
                    entry["judged"] = why
                if leg.id in SUITE_BASELINES:
                    try:
                        accepted = baseline_rows((REPO_ROOT / SUITE_BASELINES[leg.id]).read_text(encoding="utf-8"))
                        verdict, why = judge_suite(Path(log).read_text(encoding="utf-8", errors="replace"), rc, accepted,
                                                   leg.run_targets)
                    except OSError as exc:
                        verdict, why = 2, f"cannot read the known-red set or the log: {exc}"
                    entry["x.py rc"], entry["judged"] = rc, why
                    suite_said = f"{leg.id}: {why}"
                    rc = verdict
            if source_refusal(f"after {leg.id}", fresh=leg.checkout_handoff):
                entry["outcome"] = "NOT JUDGED (source changed)"
                judged_nothing += 1
                record_outcome(leg, entry, ran, CACHE_NOT_JUDGED, "the source changed", round(secs, 1))
                break
            if suite_said is not None:
                print(suite_said)
            if prepare_failed:
                entry["outcome"] = f"FAIL (its prepare step `{' '.join(leg.prepare or [])}` exited {rc})"
                failed += 1
                print(f"FAIL {leg.id}: the prepare step failed (exit {rc}, {secs:.0f} s)")
                # No member's tests ran. The failure is the stage 1's: a FAIL only
                # under the keys that name its inputs (a stage-1 suite's, a
                # TRUST_RUSTC-1 member's), COULD NOT RUN under the rest, as a later
                # leg on that broken build is (EW-19; review of EW-21).
                named = [mk for mk in failed_in if leg.needs_stage1 or mk[0] in leg.stage1_members]
                record_outcome(leg, entry, named, CACHE_FAIL, f"its prepare step exited {rc}", round(secs, 1))
                record_outcome(leg, entry, [mk for mk in failed_in if mk not in named], CACHE_COULD_NOT_RUN,
                               f"the stage-1 prepare it needed exited {rc}; its tests never ran", round(secs, 1))
                note_shared_failures(broken, leg, entry, shared)
                continue
            if rc == 0 and leg.id not in SELF_GRADED_LEGS and skipped_token(log):
                entry["outcome"] = "SKIPPED (the lane judged nothing)"
                judged_nothing += 1
                record_outcome(leg, entry, ran, CACHE_NOT_JUDGED, "the lane judged nothing", round(secs, 1))
            elif rc == 0:
                _check_cancellation()
                if source_refusal(f"before publishing {leg.id}"):
                    entry["outcome"] = "NOT JUDGED (source changed)"
                    judged_nothing += 1
                    record_outcome(leg, entry, ran, CACHE_NOT_JUDGED, "the source changed", round(secs, 1))
                    break
                entry["outcome"] = "PASS"
                after = rustc_identity() if (leg.needs_stage1 or leg.stage1_members) else None
                stored = ran
                if leg.reads is not None and ran:
                    # The source passes bind only tracked files. A declared
                    # read (an untracked source, a link's target, a program
                    # on PATH) that moved while the leg ran makes this PASS
                    # one of no key: it is not filed (LEG-READS-1).
                    try:
                        moved = leg_keys(leg) != keys
                    except (RuntimeError, ValueError, KeyError, OSError) as exc:
                        moved = True
                        entry["cache_record_failed"] = f"no complete key after the run: {exc}"
                    if moved:
                        stored = []
                        entry["cache_record_skipped"] = "a declared read changed while the leg ran"
                        print(f"{leg.id}: a declared read changed while it ran; its PASS is not recorded")
                for m, k in stored:
                    try:
                        cache_store(k, {"leg": leg.id, "member": m, "run": str(run_dir), "head": revision,
                                        "seconds": round(secs, 1), "sysroot": after})
                    except OSError as exc:
                        entry["cache_record_failed"] = str(exc)
                        print(f"{leg.id}: could not record PASS under {k}: {exc}")
                # Every key of the leg: a fresh PASS can complete the FAIL that
                # splits a member it did not run.
                note_splits(leg, entry, keys)
                if builds_stage1 and entry.get("stage1") == "built":
                    ident = rustc_identity()
                    if ident is not None:
                        _check_cancellation()
                        stage1_stamp_path().write_text(json.dumps({"key": s1_key, "rustc": ident}), encoding="utf-8")
            elif rc in NOT_JUDGED_EXITS.get(leg.id, (2,)):
                entry["outcome"] = "NOT JUDGED"
                judged_nothing += 1
                record_outcome(leg, entry, ran, CACHE_NOT_JUDGED, f"exit {rc}", round(secs, 1))
                # A publication cannot proceed without current IR containment.
                # In particular, an unavailable remote API must not hold the
                # machine through another compiler/test battery. Diagnostic
                # runs still execute their independent selected checks.
                if land_transaction and leg.id == "ir-cohort":
                    unavailable_publication_prerequisite = leg.id
                if land_transaction and not failed and judged_nothing == 1:
                    retry_landing = push_row_refresh(leg.id, rc, landing, revision)
                    if retry_landing is not None:
                        record["remote_refresh"] = landing_json(retry_landing.landing)
                        break
            else:
                entry["outcome"] = "FAIL"
                failed += 1
                record_outcome(leg, entry, failed_in, CACHE_FAIL, f"exit {rc}", round(secs, 1))
            print(f"{entry['outcome']} {leg.id} (exit {rc}, {secs:.0f} s)")
            note_shared_failures(broken, leg, entry, shared)
        except GateCancelled:
            # The exit above was observed: it is recorded however the gate ends.
            record_observed_exit(leg, entry, int(entry["rc"]), log, prepare_failed, failed_in, secs,
                                 "the gate was cancelled")
            raise
    if land_transaction and not (failed or judged_nothing or not_run_selected):
        # The push is the one effect no later pass can take back, and the
        # hook it starts runs in this worktree: read it in full first.
        if source_refusal("before ordinary push", fresh=True):
            judged_nothing += 1
        else:
            try:
                if _ACTIVE_PUBLICATION_CHECK is not None:
                    _ACTIVE_PUBLICATION_CHECK()
                problem = None if agh_publication else transaction_hook_problem(revision)
                if problem:
                    raise RuntimeError(problem)
                current = read_landing(head=revision)
                if current.remote != landing.remote:
                    raise LandingUnjudged("publication remote changed after source qualification")
                if current.tip != landing.tip and current.remote == landing.remote and current.tip:
                    raise LandingRefreshRequired(current)
                current_push = landing_preflight(landing, revision, check_source)
                # The push runs the pre-push hook (or a native publication):
                # the final record's boundary reads the checkout again.
                binding.ran("the ordinary push")
                log_path = run_dir / "ordinary-push.log"
                with log_path.open("w", encoding="utf-8", buffering=1) as log:
                    if agh_publication:
                        record["ordinary_push"] = publish_native_source(current_push, log)
                        push_rc = 0
                    else:
                        targo_pycache = (fresh_pycache(run_dir, deferred_targo.id)
                                         if deferred_targo is not None else None)
                        try:
                            coordinator = landing_targo.Coordinator(
                                current_push.head, current_push.destination,
                                leg_environment(deferred_targo, pycache=targo_pycache)
                                if deferred_targo is not None else None,
                                checkout_problem, remote=current_push.remote, keys=deferred_keys)
                            push_rc = ordinary_push(coordinator, log, run_dir)
                        finally:
                            if targo_pycache is not None:
                                shutil.rmtree(targo_pycache, ignore_errors=True)
                        record["ordinary_push"] = {"rc": push_rc, "log": str(log_path), **coordinator.receipt()}
                        if deferred_targo is not None:
                            record["live_targo"] = coordinator.receipt()
                            record["legs"]["targo-trust"]["outcome"] = (
                                "PASS (executed by ordinary pre-push)" if push_rc == 0 else "NOT JUDGED or FAIL")
                if push_rc:
                    failed += 1
            except LandingRefreshRequired as changed:
                retry_landing = changed
                record["ordinary_push"] = {"rc": 2, "reason": str(changed)}
                judged_nothing += 1
            except (OSError, RuntimeError) as exc:
                record["ordinary_push"] = {"rc": 2, "reason": str(exc)}
                judged_nothing += 1
                print(f"LAND-GATE: ordinary push not judged — {exc}")
    if "source_refusal" not in record and source_refusal("before final record"):
        judged_nothing += 1
    record["seconds"] = round(time.time() - run_started, 1)
    record["checkout_checks"] = list(_ACTIVE_CHECKOUT_TIMINGS or [])
    record["checkout_startup"] = dict(_ACTIVE_CHECKOUT_WORKERS.startup) if _ACTIVE_CHECKOUT_WORKERS else {}
    record["split_keys"] = split_keys
    (run_dir / "record.json").write_text(json.dumps(record, indent=1, default=str), encoding="utf-8")
    print(f"\nrecord: {run_dir / 'record.json'}")
    print(hook_mode_line(hook, legs, landing))
    for k, why in split_keys.items():
        print(f"LAND-GATE: SPLIT KEY {k}: {why}")
    if failed:
        print("LAND-GATE: RED")
        return 1
    if (retry_landing is not None and judged_nothing == 1 and not not_run_selected
            and "source_refusal" not in record):
        raise retry_landing
    if judged_nothing:
        if (development and development_push_problem and judged_nothing == 1 and not not_run_selected
                and "source_refusal" not in record):
            print("LAND-GATE: DEVELOPMENT SOURCE CHECKS PASSED; LANDING NOT JUDGED — "
                  "fresh stated push/live rows remain mandatory at actual landing; broad diagnostics NOT RUN")
        else:
            print("LAND-GATE: NOT JUDGED — a selected leg judged nothing")
        return 2
    if source_diagnostic:
        print("LAND-GATE: PARTIAL — only source diagnostics were requested; "
              "the landing push was not judged")
        return 2
    if not_run_selected:
        print(f"LAND-GATE: PARTIAL — selected legs not run (--only): {', '.join(not_run_selected)}; "
              "this is no landing verdict")
        return 2
    if args.dry_run:
        print("LAND-GATE: DRY RUN — the plan above; nothing was judged")
        return 0
    _check_cancellation()
    print(("LAND-GATE: DEVELOPMENT CHECKS PASSED — broad diagnostics NOT RUN; no full diagnostic verdict"
           if development else "LAND-GATE: GREEN") + push_rows_verdict_note(hook, legs, record))
    return 0


def push_rows_verdict_note(hook: PushHook, legs: List[Leg], record: Dict[str, object]) -> str:
    """What a passing verdict says of the push rows when push-rows did not run
    them because an active hook runs every one on the push (PKG-LIVE-3,
    HOOK-NO-REPLAY-2): the verdict covers no push row, and a red row appears
    only at the push. Under `land` the push this run made ran them; its exit
    says how they went."""
    if not hook.active or any(l.id == "push-rows" and l.selected for l in legs):
        return ""
    push = record.get("ordinary_push")
    if isinstance(push, dict) and push.get("rc") == 0:
        return "; the push-profile rows ran once, in the pre-push hook of this run's push"
    return ("; the push-profile rows are NOT judged here: the pre-push hook runs every one on the push, "
            "and a red row refuses that push")


def cmd_landing_targo(args) -> int:
    """The pre-push hook's full Targo suite under `land`. Its FAIL or NOT
    JUDGED is recorded under the keys the gate handed it, as a run of the leg
    records it, so a later PASS under one of them is a split (review of EW-21).
    It records no PASS: the hook, not this gate, gates that push."""
    head = os.environ.get(landing_targo.HEAD_ENV, "")
    # The suite ran under the date the gate declared (DATE_ENV, in the
    # environment it handed over), not this hook process's own: its rows are
    # dated by that date, widened over every UTC day the hook ran through,
    # from its start to the moment the outcome is filed, which a ledger that
    # reads the clock saw. Without a well-formed declared date the row carries
    # no window, so it serves nothing and meets every PASS (review of EW-1).
    def utc_today() -> datetime.date:
        return datetime.datetime.now(datetime.timezone.utc).date()
    started = utc_today()
    declared: Optional[datetime.date] = None
    try:
        handed = json.loads(os.environ[landing_targo.INPUT_ENV])
        dates = {datetime.date.fromisoformat(str(handed[name])) for name in DATE_ENV}
        if len(dates) == 1:
            [declared] = dates
    except (KeyError, TypeError, ValueError, AttributeError):
        declared = None

    def record(keys: List[str], verdict: str, why: str) -> None:
        filed = utc_today()
        window = None if declared is None else (min(declared, started), max(declared, started, filed))
        if verdict not in (CACHE_FAIL, CACHE_NOT_JUDGED):
            raise ValueError(f"the landing suite records no {verdict}")
        row: Dict[str, object] = {"leg": "targo-trust", "member": None, "run": f"ordinary push of {head}",
                                  "head": head, "seconds": None, "why": why}
        if verdict == CACHE_FAIL:
            row.update({"run_keys": list(keys), "unkeyed_work": False})
        for k in keys:
            try:
                cache_record(k, verdict, row, window=window, unbounded=window is None)
            except OSError as exc:
                print(f"landing Targo suite: could not record {verdict} under {k}: {exc}", flush=True)

    return landing_targo.run_targo(REPO_ROOT, checkout_problem, record)


def cmd_landing_hook_finish(args) -> int:
    return landing_targo.finish_hook(REPO_ROOT, checkout_problem)


def unit_scope(log_text: str) -> Optional[Set[str]]:
    """The members check_compiler_unit_tests.sh says it runs, from the scope
    block it prints before it builds or runs anything (`in scope against
    <base>:`, one bootstrap path per line, and `run-make at stage 1:` for the
    trust-cg fixtures): None when the log holds no such block."""
    lines = log_text.splitlines()
    for i, line in enumerate(lines):
        if line.startswith("in scope against ") and line.rstrip().endswith(":"):
            scope: Set[str] = set()
            for row in lines[i + 1:]:
                if not row.startswith("  "):
                    break
                row = row.strip()
                scope.add(RUN_MAKE_MEMBER if row.startswith("run-make at stage 1:") else row)
            return scope
    return None


def _narrow(leg: Leg, todo: List[str]) -> List[str]:
    cmd = list(leg.command)
    if leg.id == "crates-tests":
        # A hookless leg's touched members (hookless_members) are never in
        # cache_members, so never in `todo`'s complement: they always run.
        cmd[cmd.index("--also-members") + 1] = ",".join(sorted(set(todo) | set(leg.hookless_members)))
    elif leg.id == "compiler-unit-tests":
        cmd[cmd.index("--also") + 1] = " ".join(m for m in todo if m != RUN_MAKE_MEMBER)
        if RUN_MAKE_MEMBER not in todo and "--run-make" in cmd:
            cmd.remove("--run-make")  # its PASS is cached; the script still runs a fixture its own diff names
    return cmd


# ---------------------------------------------------------------------------
# push-rows: the hook's rows, when no hook runs them (LAND-GATE-HOOKLESS-1).
# ---------------------------------------------------------------------------
#
# The hook declares no lanes: it runs `tests/run_trust_comprehensive_harness.sh
# --list push`. So does this, at run time, less the rows HOOK_ROWS_COVERED maps
# to a leg (by id and exact command). Each row runs as the hook runs it
# (`bash -o pipefail -c <command>` from the root, stdin closed, output and
# errors together) and is graded as the hook grades it ON THE LANDING PUSH:
# the push of the checkout's HEAD onto origin's refs/heads/main, whose tip is
# read from the remote when the leg runs (landing_push: `git ls-remote`, never
# the gate's selection base; a HEAD that does not contain it is NOT JUDGED),
# `HEAD <head> refs/heads/main <tip>`, exported as TRUST_PUSHED_REFS with
# TRUST_PUSH_REMOTE naming origin's push URL, exactly as the hook exports what
# git hands it. Not the standing reading: with no push in flight the history
# rows (revert-rationale, measurement-provenance, ...) judge all of main's
# history, which carries reds no landing can fix, so every hookless gate would
# be red (measured 2026-11-02: 10 FAIL, two of them that history). The quarantine
# ledger is read from git objects as the hook reads it in a push (PushQuarantine),
# and a required fast row red on main already is graded INHERITED as the hook
# grades it (inherit_candidate, judge_inherited). The fast rows run in a pool
# sized as the hook sizes its own (TRUST_PRE_PUSH_FAST_JOBS, else the
# `fast-lane` plan, at most 16), the rows the hook's FAST_SOLO_RE names alone
# after it (read from the hook; a hook whose FAST_SOLO_RE cannot be read runs
# every row in line), then the inherited reds are judged, then the scoped rows
# run in line, in manifest order.

#
# THE HOOK READS BYTES (round 4, D4). It `tee`s a lane's output to a file, no
# newline translation, and greps that file with grep -E and sed in the pushing
# shell's locale (LC_CTYPE here is UTF-8): `^[[:space:]]*SKIPPED: `,
# `^FINDING: [^[:space:]]`, `^FINDINGS: complete$` and `sed -n 's/^FINDING:
# //p'`, each over lines split at `\n` only. So push-rows keeps each row's
# output as raw bytes (_run_row). A
# `\r` is an ordinary byte, as it is to grep: `FINDINGS: complete\r` is not
# complete and `x\rSKIPPED: ` is not SKIPPED (a universal-newline read made
# both so). SKIPPED must agree in both directions: omitting a locale's blank
# can turn SKIPPED into PASS, while adding a blank can hide a quarantined GREEN
# row. row_skipped therefore runs the hook's actual grep in the row environment.
# The FINDING key's first byte stays ASCII only (a conservative prerequisite
# for inheriting a red, never a way to turn a skipped row into PASS), and a key read from
# output that is not valid UTF-8 is never compared (keys_knowable: there the
# hook's sed stops at the first invalid byte with "illegal byte sequence").
# scripts/tests/land_gate_test.py runs the hook's own commands, in the C and a
# UTF-8 locale, against these patterns over adversarial output.
ROW_SKIPPED_PATTERN = "^[[:space:]]*SKIPPED: "
ROW_FINDING_LEAD = re.compile(rb"^FINDING: [\x21-\x7e]", re.M)
ROW_FINDING = re.compile(rb"^FINDING: (.*)$", re.M)
ROW_FINDINGS_COMPLETE = re.compile(rb"^FINDINGS: complete$", re.M)
LANDING_REMOTE_REF = "refs/heads/main"
# `git rev-parse --local-env-vars` (git 2.54), for when git cannot be asked.
GIT_LOCAL_ENV_VARS = ("GIT_ALTERNATE_OBJECT_DIRECTORIES", "GIT_CONFIG", "GIT_CONFIG_PARAMETERS",
                      "GIT_CONFIG_COUNT", "GIT_OBJECT_DIRECTORY", "GIT_DIR", "GIT_WORK_TREE",
                      "GIT_IMPLICIT_WORK_TREE", "GIT_GRAFT_FILE", "GIT_INDEX_FILE", "GIT_NO_REPLACE_OBJECTS",
                      "GIT_REPLACE_REF_BASE", "GIT_PREFIX", "GIT_SHALLOW_FILE", "GIT_COMMON_DIR")


@dataclass
class PushRow:
    id: str
    required: str  # the manifest's column as the hook compares it: "true", "false", anything else
    command: str


@dataclass(frozen=True)
class LandingPush:
    """The push a landing makes: `head` (the checkout's HEAD) onto main, whose
    tip on the remote is `destination` (landing_push reads it from the remote;
    never the gate's selection base); `remote` is TRUST_PUSH_REMOTE.
    `checkout` tallies the complete pass that bound the checkout to `head`
    before any row ran (None when none was tallied)."""
    destination: str
    head: str
    remote: str = ""
    checkout: Optional[CheckoutTally] = field(default=None, compare=False, repr=False)

    @property
    def refs(self) -> str:
        """TRUST_PUSHED_REFS: the line git hands the hook for this push."""
        return f"HEAD {self.head} {LANDING_REMOTE_REF} {self.destination}"

    @property
    def destination_refs(self) -> str:
        """The hook's INHERITED-RED replay: the destination tip as the pushed revision."""
        return f"{LANDING_REMOTE_REF} {self.destination} {LANDING_REMOTE_REF} {self.destination}"


def push_profile_rows(root: Optional[Path] = None, rev: Optional[str] = None) -> List[PushRow]:
    """The hook's lane list, parsed as its `read -r gate_id _category required
    _last_green command` does (the command keeps any tab after it): the
    worktree's manifest (what the hook runs at push time), or, with `rev`, that
    commit's, read from git objects and run from a scratch copy (`--list`
    reads nothing beside the manifest), so a plan of another head or a dirty
    worktree is judged on the tree being landed."""
    import tempfile
    root = Path(root or REPO_ROOT)
    with tempfile.TemporaryDirectory(prefix="land-gate-profile.") as tmp:
        script = HARNESS
        if rev is not None:
            blob = subprocess.run(["git", "-C", str(root), "show", f"{rev}:{HARNESS}"], capture_output=True,
                                  env=git_query_env())
            if blob.returncode != 0:
                raise RuntimeError(f"no {HARNESS} at {rev[:12]}: "
                                   f"{(blob.stderr.decode('utf-8', 'replace').strip().splitlines() or ['?'])[-1]}")
            script = str(Path(tmp) / Path(HARNESS).name)
            Path(script).write_bytes(blob.stdout)
        _started_program()  # the manifest is the commit's program, run in the checkout (SourceBinding)
        proc = subprocess.run(["bash", script, "--list", "push"], cwd=root, capture_output=True, text=True)
    if proc.returncode != 0:
        raise RuntimeError(f"`{HARNESS} --list push` failed (exit {proc.returncode}): "
                           f"{(proc.stderr.strip().splitlines() or ['?'])[-1]}")
    rows = []
    for line in proc.stdout.splitlines():
        parts = line.split("\t", 4)
        if not parts[0]:
            continue
        if len(parts) < 5:
            raise RuntimeError(f"`{HARNESS} --list push` printed a row without five fields: {line!r}")
        rows.append(PushRow(parts[0], parts[2], parts[4]))
    if not rows:
        raise RuntimeError("the push profile is EMPTY: a gate with no lanes is not a green gate")
    return rows


def git_blob_id(data: bytes) -> str:
    """Git's object id of a blob holding `data` (`git hash-object`, sha1)."""
    return hashlib.sha1(b"blob %d\0" % len(data) + data).hexdigest()


def pinned_script_problem(root: Path, push: LandingPush, path: str, pinned: str) -> Optional[str]:
    """Why `path`, in the pushed commit or in the worktree the rows run from,
    is not the bytes (git blob `pinned`) a covered row's coverage was argued
    for, or None. Unreadable is a problem (fail closed)."""
    proc = subprocess.run(["git", "-C", str(root), "rev-parse", "--verify", "--quiet", f"{push.head}:{path}"],
                          capture_output=True, text=True, env=git_query_env())
    at_head = proc.stdout.strip() if proc.returncode == 0 else "absent"
    try:
        here = git_blob_id((root / path).read_bytes())
    except OSError as exc:
        here = f"unreadable ({exc.__class__.__name__})"
    if at_head == pinned and here == pinned:
        return None
    return (f"{path} is not the script its coverage was argued for (blob {pinned[:12]}; the pushed HEAD "
            f"{push.head[:12]} holds {at_head[:12]}, the worktree {here[:24]}): the leg runs a fixed command, "
            "not this script")


def landing_edit_problem(root: Path, push: LandingPush, paths: Sequence[str]) -> Optional[str]:
    """Why the landing push edits one of `paths` (tree diff origin's main tip
    to the pushed HEAD, and the tip to the worktree the rows run from), or
    None. A diff git refuses is a problem (fail closed)."""
    moved: set = set()
    for spec in ((push.destination, push.head), (push.destination,)):
        proc = subprocess.run(["git", "-C", str(root), "-c", "diff.renames=false", "diff", "--no-renames",
                               "--name-only", "-z", *spec, "--", *paths], capture_output=True, env=git_query_env())
        if proc.returncode != 0:
            return (f"cannot tell whether the landing push edits {', '.join(paths)} "
                    f"({proc.stderr.decode('utf-8', 'replace').strip() or proc.returncode})")
        moved.update(p for p in proc.stdout.decode("utf-8", "surrogateescape").split("\0") if p)
    if not moved:
        return None
    return (f"the landing push edits {', '.join(sorted(moved))}, which its leg runs only through another reading "
            f"than the row's own command (origin's main tip {push.destination[:12]}..HEAD)")


def covered_row_problem(row: PushRow, root: Path, push: LandingPush,
                        table: Optional["PushQuarantine"] = None) -> Optional[str]:
    """None when a leg of this gate covers `row` on this landing push, else
    why it does not (push-rows then runs the row and grades it as the hook
    does). A row is covered only when (a) it is in HOOK_ROWS_COVERED with
    exactly the command that coverage was argued for; (b) each script behind a
    command its leg does not run is the pinned bytes (COVERED_ROW_PINS, round
    3's D3: the command string can stay while the script it runs changes);
    (c) the push edits none of the files a leg runs only through another
    reading than the row's (COVERED_ROW_LANDING); and (d) the pushed ledger
    holds no active quarantine row for it (round 3's D4: the hook grades that
    lane against the row, which a leg's exit status cannot). An unreadable
    ledger row for it raises RuntimeError (the hook exits 2)."""
    spec = HOOK_ROWS_COVERED.get(row.id)
    if spec is None:
        return "no leg covers it"
    command, leg_id = spec
    if row.command != command:
        return f"its command is `{row.command}`, not `{command}`, the command {leg_id}'s coverage was argued for"
    for path, pinned in COVERED_ROW_PINS.get(row.id, ()):
        problem = pinned_script_problem(root, push, path, pinned)
        if problem:
            return problem
    paths = COVERED_ROW_LANDING.get(row.id, ())
    if paths:
        problem = landing_edit_problem(root, push, paths)
        if problem:
            return problem
    if table is not None and row.required == "true":
        _q, published, _why = table.lookup(row.id)
        if published:
            return (f"the pushed ledger holds an active quarantine row for it ({published}); the hook grades this "
                    f"lane against that row, which {leg_id}'s exit status cannot, so the row runs here")
    return None


def uncovered_rows(rows: Sequence[PushRow], root: Optional[Path] = None, push: Optional[LandingPush] = None,
                   table: Optional["PushQuarantine"] = None) -> Tuple[List[PushRow], List[str], List[str]]:
    """(the rows push-rows runs, the ids a leg covers, a note for each row of
    HOOK_ROWS_COVERED that runs here anyway and why: covered_row_problem).
    With no `push` nothing is covered (fail closed: a covered row's scripts
    and quarantine are judged on the push)."""
    root = Path(root or REPO_ROOT)
    run, covered, notes = [], [], []
    for r in rows:
        why = covered_row_problem(r, root, push, table) if push is not None else "no landing push to judge it on"
        if why is None:
            covered.append(r.id)
            continue
        run.append(r)
        if r.id in HOOK_ROWS_COVERED:
            notes.append(f"{r.id} runs here, though {HOOK_ROWS_COVERED[r.id][1]} would cover it: {why}")
    return run, covered, notes


def push_refs_readers(root: Path) -> Optional[frozenset]:
    """The hook's PUSH_REFS_READERS (the rows that read TRUST_PUSHED_REFS), or
    None when it cannot be derived: then, as in the hook, no red is inherited."""
    try:
        proc = subprocess.run([sys.executable, "scripts/check_gate_lane_coverage.py", "--push-refs-readers"],
                              cwd=root, capture_output=True, text=True)
    except OSError:
        return None
    return frozenset(proc.stdout.split()) if proc.returncode == 0 else None


def _active_row(rows, gate_id: str, today: datetime.date) -> Optional[str]:
    """The hook's `active`: the first active, unexpired row for `gate_id`
    (`<id> :: expires <date> :: <required_action>`), or None. Raises
    ValueError/TypeError on an unparsable expiry, as the hook's python does."""
    for row in rows:
        if not isinstance(row, dict) or row.get("gate_id") != gate_id:
            continue
        if str(row.get("status", "")).lower() != "active":
            continue
        expires = row.get("expires_on")
        if isinstance(expires, str):
            expires = datetime.date.fromisoformat(expires)
        if not isinstance(expires, datetime.date) or expires < today:
            continue
        return f"{row.get('id')} :: expires {expires} :: {row.get('required_action', '')}"
    return None


class PushQuarantine:
    """The hook's build_push_quarantine for the landing push's one update. The
    ledger is read from GIT OBJECTS, never the worktree: a red required row is
    shielded only by a row active in the pushed tree AND on the destination tip
    (a push cannot author its own quarantine); a green or skipped row is judged
    against a row active in the pushed tree (the push publishes it). An
    unreadable pushed ledger, or an unreadable row for a lane, refuses every
    row (RuntimeError, the hook's exit 2); an unreadable destination shields
    nothing."""

    def __init__(self, root: Path, ledger: str, push: LandingPush, today: Optional[datetime.date] = None):
        self.root, self.ledger = Path(root), ledger
        self.today = today or datetime.datetime.now(datetime.timezone.utc).date()
        self.dest_label = f"{LANDING_REMOTE_REF} {push.destination[:12]}"
        self.pushed_label = f"HEAD {push.head[:12]}"
        try:
            self.pushed = self._rows(push.head)
        except Exception as exc:  # noqa: BLE001 - the hook's (OSError, ValueError, UnicodeDecodeError, TOMLDecodeError)
            raise RuntimeError(f"unreadable quarantine ledger {push.head[:12]}:{ledger} (pushed HEAD): {exc}") from exc
        try:
            self.anchor, self.anchor_why = self._rows(push.destination), ""
        except Exception as exc:  # noqa: BLE001
            self.anchor = None
            self.anchor_why = (f"the destination {self.dest_label} cannot be read here ({exc}), "
                               "so it shields nothing")

    def _git(self, *args: str) -> bytes:
        proc = subprocess.run(["git", *args], cwd=self.root, capture_output=True)
        if proc.returncode != 0:
            raise OSError(proc.stderr.decode("utf-8", "replace").strip() or f"git exit {proc.returncode}")
        return proc.stdout

    def _rows(self, commit: str):
        import tomllib
        try:
            tree = self._git("rev-parse", "--verify", "--quiet", f"{commit}^{{tree}}").decode().strip()
        except OSError:
            raise OSError(f"{commit[:12]} is not a commit in this clone") from None
        listing = self._git("ls-tree", tree, "--", self.ledger).decode("utf-8", "replace").split()
        if not listing:
            raise OSError(f"the tree has no {self.ledger}")
        if listing[1] != "blob":
            raise OSError(f"{self.ledger} is a {listing[1]} ({listing[0]}), not a file")
        return tomllib.loads(self._git("cat-file", "blob", listing[2]).decode("utf-8")).get("divergences", [])

    def lookup(self, gate_id: str) -> Tuple[str, str, str]:
        """(quarantine: the shield for a red lane, published_row: the row a
        green lane is refused for, quarantine_why: why a published row does
        not shield)."""
        try:
            published = _active_row(self.pushed, gate_id, self.today) or ""
        except (ValueError, TypeError) as exc:
            raise RuntimeError(f"unreadable quarantine row for {gate_id} in pushed "
                               f"{self.pushed_label}:{self.ledger}: {exc}") from exc
        if not published:
            return "", "", ""
        if self.anchor is None:
            return "", published, self.anchor_why
        try:
            shields = _active_row(self.anchor, gate_id, self.today)
        except (ValueError, TypeError):
            shields = None
        if not shields:
            return "", published, (f"the row is not active on the destination {self.dest_label}; a push cannot "
                                   "author its own quarantine, which shields pushes once it is there")
        return published, published, ""


def row_bytes(log: "bytes | str") -> bytes:
    """A row's output as the bytes the hook greps. push-rows hands bytes (the
    raw log _run_row wrote); a str is taken as exactly those characters, UTF-8
    encoded (no newline translation either way)."""
    return log if isinstance(log, bytes) else log.encode("utf-8", "surrogateescape")


def row_skipped(log: "bytes | str", env: Optional[Dict[str, str]] = None) -> bool:
    """Use the hook's grep and locale on the same raw bytes, without decoding.

    Only grep's match/no-match exits classify a row. An unavailable or failed
    classifier cannot grant PASS or conceal a GREEN quarantine violation.
    """
    try:
        proc = subprocess.run(["grep", "-qE", ROW_SKIPPED_PATTERN],
                              input=row_bytes(log), stdout=subprocess.DEVNULL,
                              stderr=subprocess.PIPE, env=env)
    except OSError as exc:
        raise RuntimeError(f"cannot classify SKIPPED with the hook's grep: {exc}") from exc
    if proc.returncode not in (0, 1):
        detail = proc.stderr.decode("utf-8", "replace").strip()
        raise RuntimeError(f"the hook's SKIPPED grep exited {proc.returncode}: {detail}")
    return proc.returncode == 0


def keys_knowable(log: "bytes | str") -> bool:
    """Whether the hook's `sed -n 's/^FINDING: //p'` reads the same keys from
    this output in every locale: only when it is valid UTF-8. In a UTF-8
    locale sed stops at the first invalid byte ("RE error: illegal byte
    sequence", measured 2026-11-02 with /usr/bin/sed), so the hook's key list
    is cut short there and not here (round 4, D4)."""
    try:
        row_bytes(log).decode("utf-8")
    except UnicodeDecodeError:
        return False
    return True


def key_text(key: bytes) -> str:
    """A FINDING key for a line of output: printable as itself, else escaped."""
    text = key.decode("utf-8", "backslashreplace")
    return text if text.isprintable() else repr(text)[1:-1]


def grade_row(row: PushRow, status: int, log_text: "bytes | str", quarantine: str,
              published: Optional[str] = None, why: str = "",
              env: Optional[Dict[str, str]] = None) -> Tuple[str, str]:
    """(grade, the hook's lines) as lane_grade grades a lane; `published`
    defaults to `quarantine` (the standing reading). Grades: PASS, SKIPPED,
    QUARANTINED, WARN (optional diagnostic) and FAIL; only FAIL fails, and a
    FAIL may still be INHERITED (judge_inherited). `log_text` is the row's raw
    output (row_bytes; round 4, D4)."""
    published = quarantine if published is None else published
    if status == 0:
        try:
            skipped = row_skipped(log_text, env)
        except RuntimeError as exc:
            return "FAIL", f"FAIL: {row.id}: {exc}"
        if skipped:
            if published:
                return "SKIPPED", (f"SKIPPED (quarantine row untested): {row.id} ran nothing, which is no "
                                   f"evidence the quarantined condition is gone. The row stays: {published}")
            return "SKIPPED", f"SKIPPED: {row.id} ran nothing (exit 0; no evidence either way)"
        if published:
            return "FAIL", f"FAIL: {row.id} is GREEN but still quarantined. Delete the row: {published}"
        return "PASS", f"PASS: {row.id}"
    if row.required == "false":
        return "WARN", f"WARN: {row.id} FAILED exit={status} (optional diagnostic; push may continue)"
    if quarantine:
        return "QUARANTINED", f"QUARANTINED: {row.id} is red under an active, unexpired ledger row. {quarantine}"
    line = f"FAIL: {row.id}"
    if why:
        line += f"\n      Not quarantined: {why}.\n      The row: {published}"
    return "FAIL", line


def inherit_candidate(row: PushRow, status: int, log_text: "bytes | str", readers: Optional[frozenset]) -> bool:
    """The hook's inherit_candidate, for a row lane_grade would FAIL: a fast
    row that reads the push, exited 1, and keyed every cause of its red, read
    from its raw output as the hook greps it (round 4, D4): a `FINDING: ` line
    whose key starts with an ASCII graphic byte, and a `FINDINGS: complete`
    line with nothing after it, not even a carriage return. Output whose keys
    the hook's sed may read differently (keys_knowable) is no candidate: it
    FAILs."""
    data = row_bytes(log_text)
    return (row.id.startswith("fast.") and status == 1 and readers is not None and row.id in readers
            and bool(ROW_FINDING_LEAD.search(data)) and bool(ROW_FINDINGS_COMPLETE.search(data))
            and keys_knowable(data))


def findings_of(log_text: "bytes | str") -> List[bytes]:
    """The hook's findings_of: every distinct key `sed -n 's/^FINDING: //p'`
    prints (the rest of each `FINDING: ` line, as bytes, leading blanks, a
    trailing carriage return and an empty key included; the hook compares
    every key but the empty one)."""
    return sorted(set(ROW_FINDING.findall(row_bytes(log_text))))


def _hook_solo_re(root: Path) -> Optional[re.Pattern]:
    """The hook's FAST_SOLO_RE (the rows that must not share the host), or None."""
    try:
        text = (root / HOOK_FILE).read_text(encoding="utf-8")
    except OSError:
        return None
    m = re.search(r"^FAST_SOLO_RE='([^']*)'$", text, re.M)
    if not m:
        return None
    try:
        return re.compile(m.group(1))
    except re.error:
        return None


def _row_jobs() -> int:
    """The hook's fast_jobs: TRUST_PRE_PUSH_FAST_JOBS when set (anything but a
    positive whole number is 1), else `host_budget.py jobs fast-lane` (1 when it
    cannot measure or refuses), at most 16."""
    raw = os.environ.get("TRUST_PRE_PUSH_FAST_JOBS", "")
    if raw:
        n = int(raw) if raw.isdigit() else 1
    else:
        try:
            n = host_budget.plan(host_budget.measure(), "fast-lane").jobs
        except Exception:  # noqa: BLE001 - the hook runs in line when it cannot measure
            n = 1
    return max(1, min(16, n))


def row_environment(env: Optional[Dict[str, str]], push: LandingPush,
                    root: Optional[Path] = None) -> Dict[str, str]:
    """The environment the hook gives a row in the landing push: git's local
    variables unset, TRUST_PUSHED_REFS and TRUST_PUSH_REMOTE the landing's
    (never an outer push's), and every target directory named by its real
    path (the caller's included; a relative one is read from `root`, where
    the rows run). Each row's process gets its own compiled-Python directory
    from _run_row (PYCACHE_ENV), over any caller's."""
    out = dict(os.environ if env is None else env)
    try:
        local = subprocess.run(["git", "rev-parse", "--local-env-vars"], capture_output=True, text=True).stdout.split()
    except OSError:
        local = []
    for var in local or GIT_LOCAL_ENV_VARS:
        out.pop(var, None)  # the hook unsets `git rev-parse --local-env-vars` before any row
    out["TRUST_PUSHED_REFS"] = push.refs
    out["TRUST_PUSH_REMOTE"] = push.remote
    if "CARGO_TARGET_DIR" not in out and "TARGO_TARGET_DIR" not in out:
        out["CARGO_TARGET_DIR"] = crates_target_dir()
    return resolve_target_dirs(out, REPO_ROOT if root is None else root)


def echo_bytes(data: bytes) -> None:
    """Write a row's raw output to this process's stdout as the hook's `tee`
    does (bytes, no translation); a text-only stdout (a test's StringIO) gets
    it decoded."""
    buf = getattr(sys.stdout, "buffer", None)
    if buf is None:
        sys.stdout.write(data.decode("utf-8", "replace"))
        sys.stdout.flush()
        return
    sys.stdout.flush()
    buf.write(data)
    buf.flush()


def row_resource_fds(env: Dict[str, str]) -> Tuple[int, ...]:
    return landing_targo.resource_fds(env)


# Admission. `trust-serial-command` lends an ALREADY-ADMITTED caller's one
# implicit execution and grants no CPU or memory itself: outside a build-slot
# admission it refuses (exit 75, "command requires an already-admitted
# caller"). This gate never obtained that admission and never looked for it,
# so a plain `land_gate.py run` reached the verify.executes row unadmitted and
# grade_row graded the borrower's refusal as the row's own FAIL: a RED about
# how the command was typed, after the other legs had spent their time. The
# subcommands that execute a push row now enter scripts/build-slot themselves,
# before any work (enter_admission), as scripts/prewarm_push.sh and
# scripts/check_seed_freshness.py do. The marker is read, never set: it routes,
# and the borrower still decides whether the caller really holds a slot.
BUILD_SLOT_FILE = "scripts/build-slot"
ADMITTED_COMMANDS = frozenset({"run", "land", "push-rows"})


def admission_held(env: Dict[str, str]) -> bool:
    return env.get("BUILD_SLOT_HELD") == "1"


def admission_reentry(args, env: Dict[str, str], original: Sequence[str], executable: str, entry: str,
                      root: Optional[Path] = None) -> Optional[List[str]]:
    """The argv that starts this same command line under scripts/build-slot,
    or None when there is nothing to obtain: a subcommand that executes no row
    (`run --dry-run` among them), or a caller that is admitted already. An
    admitted caller is never sent through build-slot again: its slot is the
    one its rows borrow, and a second request from inside it could only wait
    behind its own worktree lease. `original` is sys.orig_argv and `entry`
    sys.argv[0]. RuntimeError: the command line cannot be started again."""
    executes_rows = args.cmd in ADMITTED_COMMANDS or (args.cmd == "plan" and getattr(args, "run", False))
    if not executes_rows or getattr(args, "dry_run", False) or admission_held(env):
        return None
    slot = Path(REPO_ROOT if root is None else root) / BUILD_SLOT_FILE
    if not slot.is_file():
        raise RuntimeError(f"{BUILD_SLOT_FILE} is not a file in this checkout ({slot})")
    if not executable or len(original) < 2 or entry in ("", "-"):
        raise RuntimeError("this command line cannot be started again under build-slot (no interpreter path, "
                           f"or a program read from stdin); start it as `{BUILD_SLOT_FILE} -- <command>`")
    return [executable, "-B", str(slot), "--", executable, *original[1:]]


def enter_admission(args) -> Optional[str]:
    """Obtain build-slot admission for this command line before any work, by
    becoming `scripts/build-slot -- <this command line>`. Returns None when
    there is nothing to obtain (admission_reentry) and the reason when the
    admission cannot be entered; otherwise it does not return. build-slot
    waits for a slot in arrival order and says what it waits for; when it
    refuses instead it prints its reason, starts no command and exits 2, this
    gate's NOT JUDGED status. A caller that wants a bound or a CPU budget
    wraps the gate itself (`scripts/build-slot --wait-timeout S --cpus N --
    <command>`), and this function then leaves it alone."""
    try:
        command = admission_reentry(args, dict(os.environ), getattr(sys, "orig_argv", ()), sys.executable,
                                    sys.argv[0])
    except RuntimeError as exc:
        return str(exc)
    if command is None:
        return None
    sys.stdout.flush()
    print(f"land-gate: `{args.cmd}` executes rows that borrow a build-slot admission and this caller holds none; "
          f"entering {BUILD_SLOT_FILE} before any work. If it starts no command, its exit 2 is "
          "LAND-GATE: NOT JUDGED (no selection, leg or row ran), for the reason it prints.",
          file=sys.stderr, flush=True)
    try:
        os.execv(command[0], command)
    except OSError as exc:
        return f"{BUILD_SLOT_FILE} could not be started: {exc}"
    return f"{BUILD_SLOT_FILE} did not replace this process"


def row_admission_problem(rows: Sequence[PushRow], env: Dict[str, str]) -> Optional[str]:
    """Why `rows` cannot be judged from this environment, or None. The
    verify.executes row borrows the caller's admission; without one the
    borrower refuses, which says nothing about the commit."""
    if admission_held(env) or not any(r.id == "verify.executes" for r in rows):
        return None
    return ("verify.executes borrows a build-slot admission through trust-serial-command and this caller holds none "
            "(BUILD_SLOT_HELD is not 1): `land_gate.py plan --run`, `run`, `land` and `push-rows` obtain one when started as a "
            f"command, and `{BUILD_SLOT_FILE} -- <command>` gives one to anything else; never set the marker by hand")


def managed_serial_executor(env: Dict[str, str]) -> Path:
    return native_serial.managed_serial_executor(env)


def row_command(row: PushRow, root: Path, env: Dict[str, str]) -> List[str]:
    """The unchanged verifier row borrows its admitted synchronous execution."""
    bash = Path("/bin/bash")
    if not bash.is_file() or not os.access(bash, os.X_OK):
        raise RuntimeError("row custody: bash is unavailable")
    command = [str(bash), "-o", "pipefail", "-c", row.command]
    if row.id == "verify.executes":
        if row.command != "bash scripts/check_verifier_executes.sh":
            raise RuntimeError("verify.executes authored command changed; its fixed native argv needs review")
        unadmitted = row_admission_problem([row], env)
        if unadmitted:
            # Decided from the caller's admission before the launch, never from
            # the borrower's refusal after it (its exit 75 would grade FAIL).
            raise RuntimeError(f"row custody: {unadmitted}")
        executor = managed_serial_executor(env)
        # The separately packaged native owner retains the real inherited GNU
        # transport, or creates zero supplemental credits. It grants no outer
        # CPU/memory/SDK admission and preserves the row's exact argv and status.
        command = [str(executor), "--", str(bash), str(root / "scripts/check_verifier_executes.sh")]
    return command


def row_verifier_compiler(root: Path, env: Dict[str, str]) -> Path:
    """Resolve the script's original compiler selection before utility pinning.

    Preserve the selected invocation name (including a trustc symlink), because
    resolving it to another basename can change native multicall semantics.
    Relative PATH entries and explicit relative TRUSTC are relative to row cwd.
    """
    selected = env.get("TRUSTC") or "trustc"
    if "/" in selected:
        candidate = os.path.abspath(os.path.join(str(root), selected))
        found = shutil.which(candidate)
    else:
        original = env.get("PATH", os.defpath)
        search = os.pathsep.join(os.path.abspath(os.path.join(str(root), part))
                                 for part in original.split(os.pathsep))
        found = shutil.which(selected, path=search)
    if found is None:
        raise RuntimeError("verify.executes original Trust compiler selection is unavailable")
    return Path(os.path.abspath(found))


def _run_row(row: PushRow, root: Path, env: Dict[str, str], log: Path, stream: bool) -> int:
    """Run `row` as the hook runs a lane and keep its output in `log` as the
    hook's `tee` keeps it: the raw bytes (round 4, D4). A text-mode read here
    turned `\\r\\n` and a bare `\\r` into `\\n`, so `FINDINGS: complete\\r` read as
    complete and `x\\rSKIPPED: ` as SKIPPED where the hook's grep reads neither.
    The row's process compiles Python into a fresh directory of its own beside
    `log` (PYCACHE_ENV), over any caller's: a row that left a compiled module
    under a shared prefix would make a later row, or the INHERITED replay, run
    code no commit holds while every tracked byte still matched."""
    shell = Path("/bin/bash")
    shell_before = (str(shell.resolve(strict=True)), sha256_file(shell))
    command, passing = row_command(row, root, env), row_resource_fds(env)
    child_env = landing_targo.hook_environment(env)
    child_env[PYCACHE_ENV] = str(fresh_pycache(log.parent, row.id))
    compiler = None
    compiler_before = None
    if row.id == "verify.executes":
        # Its fixed script uses the system text/file tools. Keep PATH's Trust
        # compiler selection, but do not let shadowed shell utilities replace
        # the actual script or manufacture its acceptance predicates.
        compiler = row_verifier_compiler(root, env)
        compiler_before = (str(compiler.resolve(strict=True)), sha256_file(compiler))
        child_env["TRUSTC"] = str(compiler)
        child_env["PATH"] = "/usr/bin:/bin:" + env.get("PATH", "")
    with open(log, "wb") as fh, \
            subprocess.Popen(command, cwd=root, env=child_env, pass_fds=passing,
                             stdin=subprocess.DEVNULL, stdout=subprocess.PIPE, stderr=subprocess.STDOUT) as proc:
        try:
            assert proc.stdout is not None
            for line in proc.stdout:
                fh.write(line)
                fh.flush()
                if stream:
                    echo_bytes(line)
            status = proc.wait()
            if (str(shell.resolve(strict=True)), sha256_file(shell)) != shell_before:
                raise RuntimeError("row system shell changed during execution")
            if compiler is not None and (str(compiler.resolve(strict=True)), sha256_file(compiler)) != compiler_before:
                raise RuntimeError("row selected Trust compiler changed during execution")
            return status
        except BaseException:
            proc.terminate()
            proc.wait()
            raise


def judge_inherited(cands: Sequence[Tuple[PushRow, "bytes | str"]], root: Path, push: LandingPush,
                    env: Dict[str, str], tmp: Path) -> Dict[str, List[str]]:
    """The hook's judge_inherited for the landing push's one destination tip
    (origin's main tip, a commit here: landing_push): each provisional FAIL is replayed with
    the destination tip as the pushed revision, and is INHERITED only when that
    exits 1 and prints every finding the push's run printed (each non-empty key,
    byte for byte, as the hook's `grep -qxF` compares them). A replay whose
    keys the hook's sed may read differently (keys_knowable) is not inherited."""
    grades: Dict[str, List[str]] = {}
    if not cands:
        return grades
    print("\n=== inherited reds: the provisional FAILs above, judged against each destination tip ===")
    replay_env = dict(env, TRUST_PUSHED_REFS=push.destination_refs)
    d = push.destination
    for i, (row, log_text) in enumerate(cands):
        keys = [k for k in findings_of(log_text) if k]
        out = tmp / f"inherit-{i}.log"
        rc = _run_row(row, root, replay_env, out, False)
        missing: List[str] = []
        if rc != 1:
            if rc == 0:
                missing.append(f"      not inherited: the destination tip {d[:12]} is GREEN on this lane, "
                               "so every finding is this push's")
            else:
                tail = out.read_text(encoding="utf-8", errors="replace").splitlines()[-5:]
                missing.append(f"      not inherited: the lane could not judge the destination tip {d[:12]} "
                               f"(exit {rc}):")
                missing.extend(f"        | {t}" for t in tail)
        elif not keys_knowable(out.read_bytes()):
            missing.append(f"      not inherited: the destination tip {d[:12]}'s output is not valid UTF-8, where "
                           "the hook's sed stops at the first invalid byte in a UTF-8 locale, so which keys the hook "
                           "reads there cannot be known")
        else:
            dest_keys = set(findings_of(out.read_bytes()))
            missing.extend(f"      not on the destination tip {d[:12]}: {key_text(k)}" for k in keys
                           if k not in dest_keys)
        print()
        if missing:
            print(f"FAIL: {row.id} (not inherited)")
            print("\n".join(missing))
            grades.setdefault("FAIL", []).append(row.id)
        else:
            print(f"INHERITED: {row.id} is red on every destination tip ({d}) with every")
            print("           finding this push has; it adds none, so it is not this push's red:")
            print("\n".join(f"             {key_text(k)}" for k in keys))
            grades.setdefault("INHERITED", []).append(row.id)
    return grades


def run_push_rows(rows: Sequence[PushRow], root: Path, push: LandingPush, jobs: int,
                  solo: Optional[re.Pattern], env: Optional[Dict[str, str]] = None,
                  covered: Sequence[str] = (), readers: Optional[frozenset] = None,
                  today: Optional[datetime.date] = None, table: Optional["PushQuarantine"] = None) -> int:
    """Run and grade `rows` (manifest order) on the landing push; 0 no FAIL,
    1 a FAIL, 2 refused (an unreadable ledger) or nothing judged. `readers`
    is the hook's PUSH_REFS_READERS (None: no red is inherited). `table` is
    the push's quarantine table when the caller already read it. The rows'
    logs and each row's compiled Python (_run_row) live in one fresh
    directory, removed after."""
    with tempfile.TemporaryDirectory(prefix="land-gate-push-rows.") as tmp:
        return _run_push_rows_in(rows, root, push, jobs, solo, row_environment(env, push, root),
                                 covered, readers, today, table, Path(tmp))


def _run_push_rows_in(rows: Sequence[PushRow], root: Path, push: LandingPush, jobs: int,
                      solo: Optional[re.Pattern], env: Dict[str, str], covered: Sequence[str],
                      readers: Optional[frozenset], today: Optional[datetime.date],
                      table: Optional["PushQuarantine"], tmp: Path) -> int:
    import concurrent.futures
    unadmitted = row_admission_problem(rows, env)
    if unadmitted:
        print(f"PUSH-ROWS: NOT JUDGED — {unadmitted}. No row ran.")
        return 2
    if solo is None:
        jobs = 1
    fast = [r for r in rows if not r.id.startswith("scoped.")]
    scoped = [r for r in rows if r.id.startswith("scoped.")]
    pooled = [r for r in fast if jobs > 1 and not (solo and solo.search(r.id))]
    alone = [r for r in fast if r not in pooled]
    print(f"push-rows: {len(rows)} row(s) the hook would run on the landing push "
          f"(TRUST_PUSHED_REFS={push.refs}; TRUST_PUSH_REMOTE={push.remote or '(none)'})"
          f"{'; covered by a leg here: ' + ', '.join(covered) if covered else ''}")
    print(f"push-rows: {len(pooled)} in a pool of {jobs}, then {len(alone)} alone, then {len(scoped)} scoped in line")
    print("push context (TRUST_PUSHED_REFS) is read by: "
          + (" ".join(sorted(readers)) or "no lane" if readers is not None else
             "(could not derive its readers: scripts/check_gate_lane_coverage.py --push-refs-readers; "
             "no red is inherited)"))
    lookups: Dict[str, Tuple[str, str, str]] = {}
    try:
        if any(r.required == "true" for r in rows):
            table = table or PushQuarantine(root, QUARANTINE_LEDGER, push, today)
            for r in rows:
                if r.required == "true":
                    lookups[r.id] = table.lookup(r.id)
    except RuntimeError as exc:
        print(f"push-rows: {exc} — refusing to judge any row (the hook exits 2 here)")
        return 2
    grades: Dict[str, List[str]] = {}
    cands: List[Tuple[PushRow, bytes]] = []

    def judge(row: PushRow, status: int, log: Path) -> None:
        q, published, why = lookups.get(row.id, ("", "", ""))
        text = log.read_bytes()  # the raw output, as the hook greps it (round 4, D4)
        grade, line = grade_row(row, status, text, q, published, why, env=env)
        if grade == "FAIL" and status != 0 and inherit_candidate(row, status, text, readers):
            print(f"FAIL (provisional): {row.id} is red; it is judged against the destination")
            print("      after the fast lanes (INHERITED-RED, the hook's header)")
            if why:
                print(f"      Not quarantined: {why}.\n      The row: {published}")
            cands.append((row, text))
            return
        print(line)
        grades.setdefault(grade, []).append(row.id)

    logs = {r.id: tmp / f"{i}.log" for i, r in enumerate(rows)}
    try:
        if pooled:
            with concurrent.futures.ThreadPoolExecutor(max_workers=jobs) as pool:
                futs = [pool.submit(_run_row, r, root, env, logs[r.id], False) for r in pooled]
                for r, fut in zip(pooled, futs):
                    status = fut.result()
                    print(f"\n=== {r.id} ===")
                    echo_bytes(logs[r.id].read_bytes())
                    judge(r, status, logs[r.id])
        for r in alone:
            print(f"\n=== {r.id} ===", flush=True)
            judge(r, _run_row(r, root, env, logs[r.id], True), logs[r.id])
        for grade, ids in judge_inherited(cands, root, push, env, tmp).items():
            grades.setdefault(grade, []).extend(ids)
        for r in scoped:
            print(f"\n=== {r.id} ===", flush=True)
            judge(r, _run_row(r, root, env, logs[r.id], True), logs[r.id])
    except RuntimeError as exc:
        print(f"push-rows: {exc} — refusing to judge any row (the hook exits 2 here)")
        return 2
    summary = ", ".join(f"{len(v)} {k}" for k, v in sorted(grades.items()))
    if grades.get("FAIL"):
        print(f"\nPUSH-ROWS: RED ({summary}) — failed: {', '.join(grades['FAIL'])}")
        return 1
    if not any(grades.get(k) for k in ("PASS", "QUARANTINED", "WARN", "INHERITED")):
        print(f"\nPUSH-ROWS: NOT JUDGED ({summary}): no row judged anything")
        return 2
    print(f"\nPUSH-ROWS: GREEN ({summary})"
          + (f"; INHERITED from main, fix forward: {', '.join(grades['INHERITED'])}" if grades.get("INHERITED")
             else ""))
    return 0


LS_REMOTE_TIMEOUT_S = 90


class LandingUnjudged(RuntimeError):
    """The landing push cannot be stated: no destination to push to, a
    destination that cannot be read, or a HEAD that would not fast-forward it.
    push-rows judges nothing (exit 2, NOT JUDGED), never PASS."""


class LandingRefreshRequired(LandingUnjudged):
    def __init__(self, landing):
        super().__init__("remote main advanced during landing; exact source requires composition")
        self.landing = landing


def landing_preflight(landing: "LandingRange", revision: str, check_source) -> "LandingPush":
    """Keep a post-discovery remote move inside the same bounded session."""
    try:
        push = _at_checkout_boundary("landing preflight", lambda: landing_push(expect_head=revision, expect_tip=landing.tip, expect_remote=landing.remote))
        if push.remote != landing.remote or push.destination != landing.tip:
            raise LandingUnjudged("publication remote or destination changed after source qualification")
        return push
    except LandingUnjudged:
        current = read_landing(head=revision)
        if current.remote != landing.remote:
            raise LandingUnjudged("publication remote changed after source qualification")
        if current.tip and current.tip != landing.tip and not check_source():
            raise LandingRefreshRequired(current)
        raise


def push_row_refresh(leg_id: str, status: int, landing: "LandingRange", revision: str):
    """A refused row plus a real remote advance supplies no validation credit."""
    if leg_id != "push-rows" or status != 2:
        return None
    current = read_landing(head=revision)
    if current.remote == landing.remote and current.tip and current.tip != landing.tip:
        return LandingRefreshRequired(current)
    return None


def ordinary_push(coordinator, log, run_dir: Path) -> int:
    """`land`'s ordinary push (landing_targo.Coordinator.push). The pre-push
    hook's rows and every other Python process it starts compile into a
    fresh directory of the push's own (PYCACHE_ENV), removed after it, never
    the checkout's __pycache__ (LAND-GATE-PY-SHADOW-1): the push is the
    one effect no later pass can take back."""
    pycache = fresh_pycache(run_dir, "ordinary-push")
    try:
        return coordinator.push(REPO_ROOT, log, dict(git_query_env(), **{PYCACHE_ENV: str(pycache)}))
    finally:
        shutil.rmtree(pycache, ignore_errors=True)


def publish_native_source(push: "LandingPush", log) -> dict:
    problem = _at_checkout_boundary("before native publication", lambda: checkout_problem(push.head))
    if problem:
        raise LandingUnjudged(problem)
    ancestry = _git_ask(REPO_ROOT, git_query_env(), "merge-base", "--is-ancestor",
                        push.destination, push.head, timeout=30)
    if ancestry.returncode or push.destination == push.head:
        raise LandingUnjudged("native publication requires an actual fast-forward")
    done = remote_tips.push_exact_source(push.remote, REPO_ROOT, push.destination, push.head, env=git_query_env())
    log.write(done.stdout or "")
    log.write(done.stderr or "")
    log.flush()
    if done.returncode:
        raise LandingUnjudged(f"native Agh publication failed: {_git_said(done)}")
    remote, tip = remote_main_tip(REPO_ROOT, git_query_env())
    if remote != push.remote or tip != push.head:
        raise LandingUnjudged("native publication lacks an exact independent remote acknowledgement")
    problem = _at_checkout_boundary("after native publication acknowledgement", lambda: checkout_problem(push.head))
    if problem:
        raise LandingUnjudged(problem)
    return {"rc": 0, "mode": "native Agh expected-ref source publication",
            "head": push.head, "destination": push.destination, "remote": remote, "acknowledged": tip}







def remote_main_tip(root: Path, env: Dict[str, str]) -> Tuple[str, str]:
    """(origin's push URL, the sha its `refs/heads/main` names now): a fresh
    authenticated Agh inventory for GitHub, Git for literal local URLs, never
    a local tracking ref. LandingUnjudged when origin has no push URL or its
    main cannot be read as one sha, or it has multiple push destinations. Nothing is fetched and no ref moves."""
    url = _git_ask(root, env, "remote", "get-url", "--push", "--all", "origin")
    if url.returncode != 0 or not url.stdout.strip():
        raise LandingUnjudged(f"this clone has no `origin` to push the landing to ({_git_said(url)})")
    destinations = url.stdout.splitlines()
    if len(destinations) != 1 or not destinations[0].strip():
        raise LandingUnjudged("origin must name exactly one push destination; "
                              f"it names {len(destinations)}, so no single landing push can be judged")
    remote = destinations[0].strip()
    listed = remote_tips.remote_refs(remote, env=env, cwd=root, timeout=LS_REMOTE_TIMEOUT_S)
    if listed.returncode != 0:
        raise LandingUnjudged(f"cannot read {LANDING_REMOTE_REF} from {remote} (remote inventory: {_git_said(listed)})")
    tips = [sha for sha, _, ref in (line.partition("\t") for line in listed.stdout.splitlines())
            if ref.strip() == LANDING_REMOTE_REF]
    if len(tips) != 1 or not re.fullmatch(r"[0-9a-f]{40}(?:[0-9a-f]{24})?", tips[0].strip()):
        raise LandingUnjudged(f"{remote} advertises no single {LANDING_REMOTE_REF} "
                              f"({len(tips)} line(s) name it); the landing push has no destination")
    return remote, tips[0].strip()


@dataclass(frozen=True)
class LandingRange:
    """What the landing push carries, read by `plan`, `run` and `key` before
    any leg is planned (round 3, D2 and D5): origin's main `tip` as the remote
    names it, the `head` being landed, whether the head contains the tip
    (`contained`: the push would fast-forward), and `changed`, the tree diff
    tip..head, which is what the hook's rows judge on that push (None: it
    cannot be read). `why` says why the push cannot be stated (empty when it
    can). The hook-path rule, the crates lane's range and the selection of the
    legs that stand in for the hook's scoped rows read it, never the gate's
    selection base alone."""
    tip: str = ""
    head: str = ""
    remote: str = ""
    contained: bool = False
    changed: Optional[Tuple[str, ...]] = None
    why: str = ""

    @property
    def stated(self) -> bool:
        return self.contained and self.changed is not None and bool(self.tip)


def read_landing(root: Optional[Path] = None, head: str = "HEAD") -> LandingRange:
    """The landing push of `head` onto origin's main tip (LandingRange), read
    from the remote now. Never raises: a remote that cannot be read, a tip this
    clone lacks or a tree diff git refuses is a LandingRange whose `changed` is
    None, and a head that does not contain the tip is one that is not
    `contained`; each says why."""
    root = Path(root or REPO_ROOT)
    env = git_query_env()
    h = _git_ask(root, env, "rev-parse", "--verify", f"{head}^{{commit}}")
    if h.returncode != 0 or not h.stdout.strip():
        return LandingRange(why=f"{head} is no commit here ({_git_said(h)})")
    head_sha = h.stdout.strip()
    try:
        remote, tip = remote_main_tip(root, env)
    except LandingUnjudged as exc:
        return LandingRange(head=head_sha, why=str(exc))
    known = _git_ask(root, env, "cat-file", "-e", f"{tip}^{{commit}}")
    if known.returncode != 0:
        return LandingRange(tip, head_sha, remote, False, None,
                            f"origin's main tip {tip[:12]} is not in this clone, so neither what the landing push "
                            f"carries nor whether {head_sha[:12]} contains it can be read. Fetch and merge "
                            "origin/main first")
    try:
        changed = tuple(ls.changed_paths(str(root), tip, head_sha))
    except Exception as exc:  # noqa: BLE001 - any failure is "cannot tell"
        return LandingRange(tip, head_sha, remote, False, None,
                            f"cannot diff origin's main tip {tip[:12]} against {head_sha[:12]} ({exc})")
    contained = _git_ask(root, env, "merge-base", "--is-ancestor", tip, head_sha)
    if contained.returncode == 0:
        return LandingRange(tip, head_sha, remote, True, changed, "")
    why = (f"{head_sha[:12]} does not contain origin's main tip {tip[:12]}: the landing push would not be a "
           "fast-forward. Merge origin/main first" if contained.returncode == 1 else
           f"cannot tell whether {head_sha[:12]} contains origin's main tip {tip[:12]} ({_git_said(contained)})")
    return LandingRange(tip, head_sha, remote, False, changed, why)


# push-rows run as `run`'s leg: `run` binds the checkout with complete passes
# before the leg (its last one, with only push-rows started since) and after
# it (a fresh one, after every read that judges the leg), so push-rows' own
# two passes read the same bytes again around nothing but its rows: 95.0 s of
# a development run (STATUS.md, run 20261114T134816), in a worker pool of its
# own. `run` hands it that binding instead: a pipe whose write end it closed
# before the leg started, holding one random token, whose descriptor it names
# after this flag. Only a closed pipe holding one token skips the passes, and
# only with --expect-head; that proves no run handed it, so `run` requires the
# leg to report the digest of the token it read (CHECKOUT_BOUND_REPORT) or
# calls the leg NOT JUDGED. Standalone push-rows and landing_preflight read in
# full as before, and a standalone result is recorded nowhere
# (READS-ONCE-WINDOW-1).
CHECKOUT_BOUND_FLAG = "--checkout-bound-by-fd"
CHECKOUT_BOUND_REPORT = "push-rows: checkout bound by run "
CHECKOUT_TOKEN = re.compile(rb"[0-9a-f]{64}\n")


def checkout_handoff_pipe() -> Tuple[int, str]:
    """(read descriptor, token digest): a pipe holding one fresh random token,
    its write end already closed, so the reader meets the token and then EOF."""
    token = (os.urandom(32).hex() + "\n").encode("ascii")
    readable, writable = os.pipe()
    try:
        os.write(writable, token)
    except BaseException:
        os.close(readable)
        raise
    finally:
        os.close(writable)
    return readable, hashlib.sha256(token).hexdigest()[:16]


def checkout_bound_by(descriptor: int) -> str:
    """The digest of the token `run` handed on `descriptor` (checkout_handoff_pipe),
    which is then closed; LandingUnjudged unless it is a pipe holding exactly
    one token whose writer has closed it."""
    try:
        if not stat.S_ISFIFO(os.fstat(descriptor).st_mode):
            raise LandingUnjudged(f"{CHECKOUT_BOUND_FLAG} {descriptor} is no pipe")
        os.set_blocking(descriptor, False)
        data = b""
        while len(data) <= 65:
            try:
                chunk = os.read(descriptor, 128)
            except BlockingIOError:
                raise LandingUnjudged(f"{CHECKOUT_BOUND_FLAG} {descriptor} is a pipe still open for writing, "
                                      "not one a run closed after its token") from None
            if not chunk:
                break
            data += chunk
    except OSError as exc:
        raise LandingUnjudged(f"{CHECKOUT_BOUND_FLAG} {descriptor} cannot be read ({exc.__class__.__name__})") from exc
    finally:
        with contextlib.suppress(OSError):
            os.close(descriptor)
    if not CHECKOUT_TOKEN.fullmatch(data):
        raise LandingUnjudged(f"{CHECKOUT_BOUND_FLAG} {descriptor} holds no run token")
    return hashlib.sha256(data).hexdigest()[:16]


def landing_push(root: Optional[Path] = None, expect_tip: Optional[str] = None,
                 expect_head: Optional[str] = None, expect_remote: Optional[str] = None,
                 bound_by_run: bool = False) -> LandingPush:
    """The landing's push as the hook would see it (round 2, D1): this
    checkout's HEAD onto `refs/heads/main` of origin's push URL (the hook's $2),
    whose tip is read FROM THE REMOTE when the leg runs (remote_main_tip), never
    the gate's selection base and never a local tracking ref. That tip is
    TRUST_PUSHED_REFS' remote sha, the quarantine anchor and the INHERITED
    replay's destination, and the history rows judge `<tip>..HEAD` through it.
    LandingUnjudged when origin has no push URL, its main cannot be read, HEAD
    does not contain the tip (the push would not be a fast-forward, or the tip
    is not in this clone: merge origin/main first), or `expect_tip` (the tip
    `run` read when it planned the legs that stand in for the hook's scoped
    rows, round 3's D5) is not the tip the remote names now: those legs judge
    the push onto that tip, and push-rows judges no other. Nothing is fetched
    and no ref moves. `bound_by_run`: the run that started this push-rows
    binds the checkout (CHECKOUT_BOUND_FLAG), so no pass is read here and the
    remote is read once."""
    root = Path(root or REPO_ROOT)
    env = git_query_env()
    head = _git_ask(root, env, "rev-parse", "--verify", "HEAD^{commit}")
    if head.returncode != 0 or not head.stdout.strip():
        raise LandingUnjudged(f"this checkout has no HEAD commit ({_git_said(head)})")
    head_sha = head.stdout.strip()
    if expect_head is not None and head_sha != expect_head:
        raise LandingUnjudged(f"HEAD changed from planned {expect_head[:12]} to {head_sha[:12]}")
    if bound_by_run:
        remote, tip = _landing_destination(root, env, head_sha, expect_tip, expect_remote)
        return LandingPush(tip, head_sha, remote)
    # The remote is read before the complete checkout pass as well as after
    # it, so a push that main has already outrun is refused in seconds, not
    # after the pass; the tip the push is judged onto is the one read after.
    _landing_destination(root, env, head_sha, expect_tip, expect_remote)
    tally = CheckoutTally()
    problem = checkout_problem(head_sha, root, tally=tally)
    if problem:
        raise LandingUnjudged(problem)
    remote, tip = _landing_destination(root, env, head_sha, expect_tip, expect_remote)
    return LandingPush(tip, head_sha, remote, tally)


def _landing_destination(root: Path, env: Dict[str, str], head_sha: str,
                         expect_tip: Optional[str], expect_remote: Optional[str] = None) -> Tuple[str, str]:
    """landing_push's (remote, tip): origin's main tip as the remote names it
    now, which must be `expect_tip` when one is given and which HEAD must
    contain. LandingUnjudged otherwise."""
    remote, tip = remote_main_tip(root, env)
    if expect_remote is not None and remote != expect_remote:
        raise LandingUnjudged("publication remote changed after source qualification")
    if expect_tip and tip != expect_tip:
        raise LandingUnjudged(f"origin's main tip is now {tip[:12]}, not {expect_tip[:12]}, the tip this gate "
                              "planned its legs onto: main moved while the gate ran. Merge origin/main first")
    contained = _git_ask(root, env, "merge-base", "--is-ancestor", tip, head_sha)
    if contained.returncode == 1:
        raise LandingUnjudged(f"HEAD {head_sha[:12]} does not contain origin's main tip {tip[:12]}: the landing "
                              "push would not be a fast-forward. Merge origin/main first")
    if contained.returncode != 0:
        raise LandingUnjudged(f"origin's main tip {tip[:12]} is not in this clone, so HEAD {head_sha[:12]} does "
                              f"not contain it ({_git_said(contained)}). Fetch and merge origin/main first")
    return remote, tip


def cmd_push_rows(args, root: Optional[Path] = None) -> int:
    descriptor = getattr(args, "checkout_bound_by_fd", None)
    if descriptor is None:
        with _checkout_workers_scope():
            return _cmd_push_rows_in_scope(args, root, None)
    if not getattr(args, "expect_head", None):
        # With no pass here, only --expect-head ties the HEAD these rows judge
        # (TRUST_PUSHED_REFS) to the revision the run bound: a commit of the
        # same tree, moved to and back inside the leg, would pass unseen.
        with contextlib.suppress(OSError):
            os.close(descriptor)
        print(f"PUSH-ROWS: NOT JUDGED — {CHECKOUT_BOUND_FLAG} without --expect-head names no revision the run "
              "bound. No row ran.")
        return 2
    try:
        bound = checkout_bound_by(descriptor)
    except LandingUnjudged as exc:
        print(f"PUSH-ROWS: NOT JUDGED — {exc}. No row ran.")
        return 2
    # No pass here, so no worker pool either.
    print(f"{CHECKOUT_BOUND_REPORT}{bound}: it reads every tracked file before and after this leg")
    return _cmd_push_rows_in_scope(args, root, bound)


def _cmd_push_rows_in_scope(args, root: Optional[Path], bound: Optional[str]) -> int:
    root = Path(root or REPO_ROOT)
    try:
        push = landing_push(root, getattr(args, "expect_tip", None), getattr(args, "expect_head", None),
                            getattr(args, "expect_remote", None), bound_by_run=bound is not None)
    except LandingUnjudged as exc:
        print(f"PUSH-ROWS: NOT JUDGED — {exc}. No row ran.")
        return 2
    profile = push_profile_rows(root)
    try:
        table = PushQuarantine(root, QUARANTINE_LEDGER, push) if any(r.required == "true" for r in profile) \
            else None
        rows, covered, notes = (profile, [], []) if getattr(args, "all_rows", False) else uncovered_rows(profile, root, push, table)
    except RuntimeError as exc:
        print(f"push-rows: {exc} — refusing to judge any row (the hook exits 2 here)")
        return 2
    for note in notes:
        print(f"push-rows: {note}")
    if push.checkout is not None:
        print(f"push-rows: the checkout is HEAD {push.head[:12]}: {_tally_text(push.checkout)}")
    result = run_push_rows(rows, root, push, _row_jobs(), _hook_solo_re(root),
                           covered=covered, readers=push_refs_readers(root), table=table)
    if bound is not None:
        print(f"push-rows: the checkout after the rows is bound by run {bound}'s next complete pass")
        return result
    tally = CheckoutTally()
    problem = checkout_problem(push.head, root, tally=tally)
    if problem:
        print(f"PUSH-ROWS: NOT JUDGED — {problem}. The row results do not qualify this checkout.")
        return 2
    print(f"push-rows: the checkout is still HEAD {push.head[:12]} after the rows: {_tally_text(tally)}")
    return result


def _tally_text(tally: CheckoutTally) -> str:
    return (f"{tally.files} tracked files' bytes, type and mode read in full against the commit in "
            f"{tally.seconds:.1f}s ({tally.jobs} process{'es' if tally.jobs != 1 else ''})")


# ---------------------------------------------------------------------------
# Replay: before and after, over main's history. No builds.
# ---------------------------------------------------------------------------

IN_SCOPE_RE = re.compile(
    r"^(compiler/|crates/|library/|src/bootstrap/|src/tools/|src/librustdoc/|src/llvm-project/|src/stage0$"
    r"|src/version$|src/rust-compat-version$|targo-trust/|first-party/|vendor/|\.cargo/|Cargo\.(toml|lock)$"
    r"|.*/Cargo\.(toml|lock)$|release/trust-version\.toml$|x\.py$|tools/preflight\.|scripts/trust_build_lock\.sh$"
    r"|scripts/frozen-files\.txt$|tests/fixtures/binary_decomp/)")


def before_selection(changed: List[str]) -> Dict[str, object]:
    """What the pre-2026-10-14 process ran for this change: the push hook's
    scoped lanes by their own rules, and the landing runbook (train E1) for the
    rest: x.py check, the whole ui suite, the whole trust run-make set, the unit
    lane on touched crates, crates tests on touched members."""
    xpy = any(IN_SCOPE_RE.match(p) for p in changed)
    touched_compiler = sorted({"/".join(p.split("/")[:2]) for p in changed if p.startswith("compiler/")})
    touched_crates = sorted({"/".join(p.split("/")[:2]) for p in changed if p.startswith("crates/")})
    return {"compiler-check": xpy, "ui-trust": True, "run-make-trust": True,
            "compiler-unit-tests": len(touched_compiler) + sum(1 for c in touched_crates if c in (
                "crates/trust-mir-extract", "crates/trust-thir-lower", "crates/trust-witness")),
            "crates-tests": len(touched_crates)}


def cmd_replay(args) -> int:
    ls.AUDITS_OVERRIDE = (REPO_ROOT / ls.AUDITS_FILE).read_bytes()
    ls.SCAN_CACHE = {}  # history replays re-read the same blobs; the live gate never caches
    revs = git("rev-list", "--first-parent", "-n", str(args.last), args.ref).split()
    # The replay's "after" is the gate with the hook installed: the crates
    # count below adds the touched members back itself (the hook's lane).
    hooked = PushHook(True, "replay: the gate as it selects beside the hook", "installed",
                      frozenset(HOOK_ROWS_COVERED))
    rows = []
    t0 = time.time()
    for rev in revs:
        parent = git("rev-parse", f"{rev}^1")
        idx = ls.TreeIndex.load(str(REPO_ROOT), rev)
        g = ls.build_graph(idx)
        changed = ls.changed_paths(str(REPO_ROOT), parent, rev)
        sel = ls.select(g, parent, changed)
        legs = build_legs(g, sel, parent, _nominal_plans(), hooked)
        after = {l.id: (len(l.targets) if (l.targets is not None and l.selected and l.id in (
            "compiler-unit-tests", "crates-tests")) else bool(l.selected)) for l in legs}
        # crates: the hook's lane runs the touched members; the gate adds the rest it reaches.
        after["crates-tests"] = sum(1 for v in sel.per_crate["crates-tests"].values() if v.selected)
        after_partial = {l.id: l.targets is not None and l.selected and l.id in ("ui-trust", "run-make-trust")
                         for l in legs}
        before = before_selection(changed)
        rows.append({"rev": rev[:12], "changed": len(changed), "everything": bool(sel.everything),
                     "everything_why": sel.everything[:2], "before": before, "after": after,
                     "after_partial": after_partial,
                     "ui_targets": len(sel.decisions["ui-trust"].targets or []),
                     "subject": git("log", "-1", "--format=%s", rev)[:80]})
        print(f"{rev[:12]} {len(changed):4d} paths  after: " +
              " ".join(f"{k}={'P' if after_partial.get(k) else ''}{v}" for k, v in after.items()) +
              ("  [EVERYTHING]" if sel.everything else ""), flush=True)
    summary = {"commits": len(rows), "seconds": round(time.time() - t0, 1)}
    for leg in ("compiler-check", "ui-trust", "run-make-trust", "olean-audit"):
        summary[leg] = {"before": sum(1 for r in rows if r["before"].get(leg, True)),
                        "after": sum(1 for r in rows if r["after"].get(leg)),
                        "after_partial": sum(1 for r in rows if r["after_partial"].get(leg))}
    for leg in ("compiler-unit-tests", "crates-tests"):
        summary[leg] = {"before_crates": sum(r["before"][leg] for r in rows),
                        "after_crates": sum(r["after"][leg] for r in rows)}
    summary["everything"] = sum(1 for r in rows if r["everything"])
    print(json.dumps(summary, indent=1))
    if args.json:
        Path(args.json).write_text(json.dumps({"summary": summary, "rows": rows}, indent=1), encoding="utf-8")
    return 0


def _nominal_plans() -> Dict[str, host_budget.Plan]:
    host = host_budget.measure()
    return budget_plans(host)


def cmd_explain(args) -> int:
    idx = ls.TreeIndex.load(str(REPO_ROOT), args.head)
    g = ls.build_graph(idx)
    for p in args.paths:
        kind, why = ls.classify(g, p)
        print(f"{p}: {kind}{' — ' + why if why else ''}")
    return 0


def cmd_needs(args) -> int:
    """Exit 0 when LEG is selected for the tree diff BASE..HEAD, 1 when the
    change cannot reach it (printing why), 2 when the selector cannot tell
    (the caller then runs the leg: fail-closed). Used by
    scripts/check_compiler_targets_build.sh (scoped.compiler-check)."""
    try:
        idx = ls.TreeIndex.load(str(REPO_ROOT), args.head)
        base = git("rev-parse", "--verify", f"{args.base}^{{commit}}")
        changed = ls.changed_paths(str(REPO_ROOT), base, idx.rev)
        if getattr(args, "development", False):
            import land_development
            if not land_development.may_have_scope(changed):
                print("land-gate needs: development scope NOT JUDGED — unsupported changed owner/input")
                return 2
        g = ls.build_graph(idx)
        sel = ls.select(g, base, changed)
        if getattr(args, "development", False):
            import land_development
            scope = land_development.scope(g, sel)
            if scope.errors or args.leg != "compiler-check":
                print("land-gate needs: development scope NOT JUDGED — " + "; ".join(scope.errors[:3]))
                return 2
            print("land-gate needs compiler-check: diagnostic SKIP — changed inputs have declared "
                  "development dispositions; canonical run --development owns fresh selected focused "
                  "checks. Broad consumers remain diagnostic NOT RUN. This is no full compiler-check PASS.")
            return 1
        problems = verify_graph(g) if args.verify_graph else []
    except Exception as exc:  # noqa: BLE001 - any failure is "cannot tell"
        print(f"land-gate needs: cannot tell ({exc.__class__.__name__}: {exc})")
        return 2
    if problems:
        print(f"land-gate needs: the graph does not hold ({problems[0]})")
        return 2
    d = sel.decisions.get(args.leg)
    if d is None:
        print(f"land-gate needs: no leg {args.leg!r}")
        return 2
    print(f"land-gate needs {args.leg} for {base[:12]}..{idx.rev[:12]}: {'yes' if d.selected else 'no'} — "
          + "; ".join(d.reasons[:3]))
    return 0 if d.selected else 1


def cmd_key(args) -> int:
    g, sel, base = compute(args.base)
    landing = read_landing(head=sel.head)
    hook = push_hook_state(sel.changed, sel.head, landing=landing)
    legs = {l.id: l for l in build_legs(g, sel, base, _nominal_plans(), hook, landing)}
    leg = legs[args.leg]
    gfp = global_fingerprint(g)
    toolchain = toolchain_identity()
    try:
        parts = key_parts(leg, g.index, toolchain=toolchain, global_fp=gfp)
    except ReadUnobservable as exc:
        # As cache_keys: no key without every declared read.
        print(json.dumps({"leg": leg.id, "key": None, "unobservable": str(exc)}, indent=1))
        return 0
    key = parts.key()
    shown = {**parts.__dict__, "key": key, "outcomes": cache_outcomes(key), "split": cache_split(key)}
    if leg.cache_members:
        # A per-member leg is cached per member, never under the key above
        # (nominal plans: a run's rescaled Rayon default can move these keys).
        members = {m: {"key": k, "outcomes": cache_outcomes(k), "split": cache_split(k)}
                   for m, k in cache_keys(leg, g, sel, toolchain, gfp, lambda: stage1_key(g, toolchain, env={}))}
        shown = {**shown, "key": None, "outcomes": None, "split": None, "members": members}
    print(json.dumps(shown, indent=1, default=str))
    return 0


def cmd_prefetch(args) -> int:
    """Host setup (the hook installers): make every workspace's graph answerable
    offline, so that no gate run needs the network. Touches the network only for
    a workspace that cannot answer offline yet, once per call; `--check` never
    does. Exit 1 when a workspace still cannot answer (a gate would select
    every leg), 2 when a gate refuses before any leg: the committed lock needs
    repair, a first-party worktree is not the committed input, or targo cannot
    run. Each line says why, worded as verify_graph words it."""
    unanswered = stale = 0
    # As in verify_graph: an install waits on at most one fill.
    no_network: Optional[str] = None
    drift = _once(first_party_drift)
    sweep_dead_unused_order_copies(say=lambda line: print(line, flush=True))
    for ws in METADATA_WORKSPACES:
        if not (REPO_ROOT / ws).is_file():
            continue
        try:
            proc, hung, no_network = answer_offline(ws, no_network, may_fill=not args.check,
                                                    say=lambda line: print(line, flush=True), drift=drift)
        except OSError as exc:
            stale += 1
            print(f"registry: {ws}: targo cannot run ({exc}); restore the selected Trust Targo on PATH: a gate "
                  "here refuses before any leg")
            continue
        if proc is not None and proc.returncode != 0 and locked_metadata_refusal(proc.stderr) and not any(drift()):
            # As verify_graph judges it; host setup judges the worktree's lock.
            try:
                worktree_lock = (REPO_ROOT / Path(ws).parent / "Cargo.lock").read_bytes()
            except OSError:
                worktree_lock = None
            if worktree_lock is not None:
                copied, no_network = unused_order_answer(ws, worktree_lock, no_network, may_fill=not args.check,
                                                         say=lambda line: print(line, flush=True))
                proc = copied or proc
        if proc is not None and proc.returncode == 0:
            print(f"registry: {ws}: answers offline")
            continue
        kind, said, _drifted = offline_failure(proc, hung, no_network, asked=not args.check, drift=drift, ws=ws)
        if kind in ("stale_lock", "drift", "old_targo"):
            stale += 1
            print(f"registry: {ws}: {said}")
            continue
        unanswered += 1
        print(f"registry: {ws}: CANNOT answer offline: {said}")
    return 2 if stale else (1 if unanswered else 0)


def _cancelled_diagnostic(error):
    # stdout and stderr may share a full, unread pipe. A cancellation must
    # still reach process exit after cleanup; its diagnostic is best effort.
    stream = sys.stderr
    fd = blocking = None
    try:
        try:
            fd = stream.fileno()
        except (AttributeError, io.UnsupportedOperation):
            stream.write(f'land-gate: {error}\n')
            return
        blocking = os.get_blocking(fd)
        os.set_blocking(fd, False)
        os.write(fd, f'land-gate: {error}\n'.encode(stream.encoding or 'utf-8', errors='replace'))
    except (OSError, ValueError):
        pass
    finally:
        if fd is not None and blocking is not None:
            try:
                os.set_blocking(fd, blocking)
            except OSError:
                pass


def validation_module_path(name: str) -> None:
    """Put the directory of `name` (a module, or a test class or method in
    one) first on the import path, as its own run `python3 -B
    scripts/tests/<module>.py` does: many modules import a sibling by bare
    name (`from build_slot_test import ...`) and, without it, failed to import
    here (LAND-SELECT-VALIDATION-REACH-1)."""
    parts = name.split(".")
    for end in range(len(parts), 0, -1):
        source = REPO_ROOT.joinpath(*parts[:end]).with_suffix(".py")
        if source.is_file():
            if str(source.parent) not in sys.path:
                sys.path.insert(0, str(source.parent))
            return


def cmd_validation_tests(args) -> int:
    """Run every declared module, refusing empty and entirely skipped suites."""
    # Script entry puts scripts/ on the import path, but declarations name
    # repository modules such as scripts.tests.land_gate_test. Anchor imports
    # to this checkout, independent of the caller's cwd and PYTHONPATH.
    sys.path.insert(0, str(REPO_ROOT))
    import unittest
    class ExecutedResults(unittest.TextTestResult):
        completed = 0

        def addSuccess(self, test):
            super().addSuccess(test)
            self.completed += 1

        def addExpectedFailure(self, test, error):
            super().addExpectedFailure(test, error)
            self.completed += 1

    outcome = 0
    for module in args.modules:
        validation_module_path(module)
        suite = unittest.defaultTestLoader.loadTestsFromName(module)
        if suite.countTestCases() == 0:
            print(f"VALIDATION-TESTS: NOT JUDGED — {module} contains no tests")
            outcome = max(outcome, 2)
            continue
        result = unittest.TextTestRunner(verbosity=2, resultclass=ExecutedResults).run(suite)
        if not result.wasSuccessful():
            return 1
        if result.completed == 0:
            print(f"VALIDATION-TESTS: NOT JUDGED — {module} ran no unskipped test")
            outcome = max(outcome, 2)
    return outcome


# ---------------------------------------------------------------------------
# rows --check: the row table's `covered` rule on the commit being pushed
# (the push row fast.land-rows-coverage, LAND-ROWS-COVERAGE-AT-LANDING-1).
# ---------------------------------------------------------------------------
#
# gates/land.toml's `covered` rule (land_select.land_rows_gaps, the one
# implementation): every tracked scripts/tests/*_test.py is exactly one [[row]]
# or exactly one [[not_run]]. land_gate_test's ValidationDependencyTests holds a
# checkout to it, but a landing that only adds a test module selects that test
# only through its own path, so twice on 2026-11-15 (8f4a08d99b78,
# 4c33bc0df3ef) main took a module with no entry and the test went red for
# every session until someone else registered it. This judges the PUSHED
# commit from git objects, never the index or the working tree: the table is
# the blob gates/land.toml holds in that commit (a regular file reached through
# real directories, as read_land_rows_text requires of a checkout), parsed by
# land_select.parse_land_rows, and the tracked files are that commit's
# `git ls-tree` entries under each covered glob's fixed leading directories.
#
# WHICH COMMIT. `--rev REV`: that one. Else, with TRUST_PUSHED_REFS set and
# non-blank (the pre-push hook and push-rows export git's `<local_ref>
# <local_sha> <remote_ref> <remote_sha>` lines): every non-deletion pushed sha;
# a deletion-only push prints `SKIPPED:`; a malformed line exits 2. Else HEAD.
#
# FINDING KEYS, one per cause, then `FINDINGS: complete` when every cause was
# keyed, so the hook and push-rows grade a red the destination already carries
# INHERITED and FAIL a push that adds one (check_gate_lane_coverage derives
# this row as a TRUST_PUSHED_REFS reader):
#   land-rows UNCOVERED <path> | DOUBLY-COVERED <path> | UNTRACKED <path>
#   land-rows TABLE-ABSENT | TABLE-NOT-A-REGULAR-FILE <mode> | TABLE-REFUSED <why>
# A commit this clone cannot read is a red with no key.
#
# NOT IN FORCE. The rule exists only where the commit's own selector reads the
# table: a commit with no gates/land.toml whose scripts/lib/land_select.py is
# absent, or a regular file that never names gates/land.toml, predates the
# table (af39d41365ef, 2026-11-14) and cannot break it; it prints `NOT IN
# FORCE` and, when every commit judged is such, `SKIPPED:` (exit 0: the row
# judged nothing, which is not a pass). A commit whose land_select.py names the
# table, or is not a regular file (link, submodule, tree: fail-closed), and has
# no table is TABLE-ABSENT, so deleting the table is still refused.
#
# The table needs tomllib: under Python older than 3.11 this file re-executes
# itself under the newest python3.1x on PATH (_reexec_if_old) and exits 2 when
# there is none, so the row FAILs there; it never skips. land_select also reads
# the CHECKOUT's table at import and refuses a broken one, which fails the row
# too (fail-closed; the hook runs it from the checkout that pushes).
ROWS_KEY = "land-rows"
ROWS_HEX_SHA = re.compile(r"^(?:[0-9a-f]{40}|[0-9a-f]{64})$")
ROWS_ZERO_SHA = re.compile(r"^0+$")
ROWS_GLOB = re.compile(r"[*?\[]")
ROWS_MODULE_FILE = re.compile(r"scripts/tests/([A-Za-z_][A-Za-z0-9_]*)\.py\Z")
ROWS_NOT_YET_TARGO = ("a Python unittest module that land_gate.py's validation-tests runner loads; it retires when "
                      "its subject is a targo verb or a test target")
ROWS_CHECK_COMMAND = "python3 -B scripts/land_gate.py rows --check"


class RowsUnreadable(Exception):
    """A revision or object this clone cannot read: a red with no key."""


@dataclass
class RowsVerdict:
    summary: str
    findings: List[Tuple[str, str]] = field(default_factory=list)  # (key, what is wrong)
    repairs: List[Tuple[str, ...]] = field(default_factory=list)  # one block of lines per break
    in_force: bool = True  # False: the commit predates the table (no rule to judge)


def _rows_git(root: Path, *args: str) -> bytes:
    """git's answer about `root`'s objects as a plain shell's push sees them
    (git_query_env), with replace refs ignored: a push sends the objects."""
    env = dict(git_query_env(), GIT_NO_REPLACE_OBJECTS="1")
    try:
        proc = subprocess.run(["git", "--literal-pathspecs", "-C", str(root), *args], capture_output=True, env=env,
                              timeout=300)
    except (OSError, subprocess.TimeoutExpired) as exc:
        raise RowsUnreadable(f"`git {args[0]}` could not run: {exc}") from None
    if proc.returncode != 0:
        tail = proc.stderr.decode("utf-8", "replace").strip().splitlines()
        raise RowsUnreadable(f"`git {args[0]}` failed: {tail[-1] if tail else f'exit {proc.returncode}'}")
    return proc.stdout


def _rows_ls_tree(root: Path, tree: str, paths: Sequence[str], recursive: bool) -> Dict[str, Tuple[str, str, str]]:
    """{path: (mode, type, object id)} of the tree's entries at `paths` (every
    entry under them when `recursive`; the whole tree when `paths` is empty)."""
    out: Dict[str, Tuple[str, str, str]] = {}
    raw = _rows_git(root, "ls-tree", "-z", "--full-tree", *(["-r"] if recursive else []), tree, "--", *paths)
    for record in raw.split(b"\0"):
        if not record:
            continue
        meta, tab, name = record.partition(b"\t")
        fields = meta.split()
        if not tab or len(fields) != 3:
            raise RowsUnreadable(f"unreadable `git ls-tree` record {record[:80]!r}")
        mode, kind, oid = (f.decode("ascii") for f in fields)
        out[name.decode("utf-8", "surrogateescape")] = (mode, kind, oid)
    return out


def _rows_listed(pattern: str) -> str:
    """A covered glob's fixed leading directories ("" when its first part is a
    glob): every path the glob can match is under it."""
    fixed = []
    for part in pattern.split("/"):
        if ROWS_GLOB.search(part):
            break
        fixed.append(part)
    return "/".join(fixed)


def rows_repair(table: "ls.LandRows", gap: "ls.LandRowsGap") -> List[str]:
    """How to clear one break of the covered rule, the [[row]] template first."""
    if gap.kind == "doubly-covered":
        return [f"  {gap.path}: delete all but one of its entries in {ls.LAND_ROWS_FILE} (a module is one [[row]] "
                "or one [[not_run]], never both)."]
    if gap.kind == "untracked":
        return [f"  {gap.path}: the commit does not track it; delete its entry from {ls.LAND_ROWS_FILE}, or "
                "commit the file."]
    named = ROWS_MODULE_FILE.match(gap.path)
    if not named:
        return [f"  {gap.path}: no entry can name it (an entry's id is validation.<module> for "
                "scripts/tests/<module>.py, a Python identifier); rename it, or move it out of the covered globs "
                f"{', '.join(table.covered)}."]
    name = named.group(1)
    identity = f"validation.{name}"
    before = [i for i in sorted(table.row_files) if i < identity]
    where = f"after [[row]] {before[-1]}" if before else "before the first [[row]]"
    return [
        f"  {gap.path}: add its [[row]] to {ls.LAND_ROWS_FILE}, in id order ({where}):",
        "",
        "    [[row]]",
        f"    id = {json.dumps(identity)}",
        f"    command = {json.dumps([*ls.VALIDATION_ROW_COMMAND, 'scripts.tests.' + name])}",
        "    selects_on = [",
        f"        {json.dumps(gap.path)},",
        "    ]",
        "    catches = \"<the defect that would go unnoticed were this module not run>\"",
        f"    not_yet_targo = {json.dumps(ROWS_NOT_YET_TARGO)}",
        "",
        "  with every file the module imports, loads, executes or copies as its program under test in "
        "selects_on, sorted (the table's header says what belongs there; a path that is also in "
        "[validation_programs] lists this row there too). When `land_gate.py validation-tests` cannot judge it, "
        "or it is red, a [[not_run]] in id order instead:",
        "",
        "    [[not_run]]",
        f"    id = {json.dumps(identity)}",
        f"    path = {json.dumps(gap.path)}",
        "    kind = \"red\"  # or \"unjudgeable\"",
        "    why = \"<the exact failure, or why validation-tests cannot judge it>\"",
        "",
    ]


def rows_reader_names_table(root: Path, reader: Optional[Tuple[str, str, str]]) -> bool:
    """Whether the commit's own selector (its ls-tree entry for
    LAND_ROWS_READER, None when absent) reads the row table. Fail-closed: an
    entry that is not a regular file counts as a reader."""
    if reader is None:
        return False
    mode, kind, oid = reader
    if kind != "blob" or mode not in ("100644", "100755"):
        return True
    return ls.LAND_ROWS_FILE.encode("utf-8") in _rows_git(root, "cat-file", "blob", oid)


def rows_judge_tree(root: Path, tree: str) -> RowsVerdict:
    """The covered rule on one tree, from git objects."""
    table_file = ls.LAND_ROWS_FILE
    entries = _rows_ls_tree(root, tree, [table_file, ls.LAND_ROWS_READER], False)
    entry = entries.get(table_file)
    if entry is None and not rows_reader_names_table(root, entries.get(ls.LAND_ROWS_READER)):
        return RowsVerdict(f"NOT IN FORCE: the commit holds no {table_file}, and its {ls.LAND_ROWS_READER} is "
                           f"absent or never names {table_file}: it predates the row table, so the rule that "
                           "covers scripts/tests modules does not exist on it", in_force=False)
    if entry is None:
        return RowsVerdict(f"{table_file}: absent", [(
            "TABLE-ABSENT", f"the commit holds no {table_file} (none, or a name on the way is a symbolic link or a "
                            "file): the selector refuses to import without its row table")],
            [(f"  Restore {table_file}: land_select reads it at import and every land_gate.py command needs it.",)])
    mode, kind, oid = entry
    if kind != "blob" or mode not in ("100644", "100755"):
        return RowsVerdict(f"{table_file}: not a regular file", [(
            f"TABLE-NOT-A-REGULAR-FILE {mode}", f"{table_file} is a {kind} of mode {mode}, not a regular file (the "
                                                 "gate hashes and watches this path, never a link's target)")],
            [(f"  Commit {table_file} as a regular file.",)])
    try:
        table = ls.parse_land_rows(_rows_git(root, "cat-file", "blob", oid).decode("utf-8"))
    except (UnicodeDecodeError, ls.LandRowsError) as exc:
        why = " ".join(str(exc).split())
        return RowsVerdict(f"{table_file}: refused", [(f"TABLE-REFUSED {why}", f"{table_file}: {why}")],
                           [("  land_select refuses this table at import, so every land_gate.py command and "
                             "land_gate_test fail on this commit: correct the rule named above (the table's header "
                             "documents each).",)])
    listed = sorted({_rows_listed(p) for p in table.covered} | set(table.row_files.values())
                    | set(table.not_run_files.values()))
    tracked = _rows_ls_tree(root, tree, [] if "" in listed else listed, True)
    gaps = ls.land_rows_gaps(table, tracked)
    verdict = RowsVerdict(f"{table_file}: {len(table.row_files)} [[row]], {len(table.not_run_files)} [[not_run]]; "
                          f"{len(gaps)} break(s) of the rule that covers {', '.join(table.covered)}")
    for gap in gaps:
        verdict.findings.append((f"{gap.kind.upper()} {gap.path}", gap.text))
        verdict.repairs.append(tuple(rows_repair(table, gap)))
    return verdict


def rows_check(root: Path, subjects: Sequence[Tuple[str, str]], heading: str) -> int:
    """Judge each (label, revision): one verdict per distinct tree."""
    trees: Dict[str, List[str]] = {}
    unreadable: List[str] = []
    for label, rev in subjects:
        try:
            tree = _rows_git(root, "rev-parse", "--verify", "--quiet", "--end-of-options",
                             f"{rev}^{{tree}}").decode("ascii").strip()
            if not ROWS_HEX_SHA.match(tree):
                raise RowsUnreadable(f"{rev} names no tree")
            trees.setdefault(tree, []).append(label)
        except (RowsUnreadable, UnicodeDecodeError):
            unreadable.append(f"[{label}] LAND-ROWS UNREADABLE: {rev} does not name a commit in this clone; a commit "
                              "this check cannot read is not a pass")
    print(heading, flush=True)
    keys: List[str] = []
    repairs: List[Tuple[str, ...]] = []
    complete = ok = not unreadable
    in_force = False
    for line in unreadable:
        print(line)
    for tree, labels in trees.items():
        label = ", ".join(labels)
        try:
            verdict = rows_judge_tree(root, tree)
        except RowsUnreadable as exc:
            print(f"[{label}] LAND-ROWS UNREADABLE: {exc}")
            complete = ok = False
            continue
        print(f"[{label}] {verdict.summary}")
        in_force = in_force or verdict.in_force
        for key, text in verdict.findings:
            print(f"[{label}]   {text}")
            keys.append(f"{ROWS_KEY} {key}")
        ok = ok and not verdict.findings
        repairs.extend(block for block in verdict.repairs if block not in repairs)
    if ok and not in_force:
        print(f"SKIPPED: the covered rule is not in force on any commit judged (none holds {ls.LAND_ROWS_FILE} or a "
              f"{ls.LAND_ROWS_READER} that reads it) — nothing to judge")
        return 0
    if ok:
        print(f"PASS: every tracked file {ls.LAND_ROWS_FILE} covers is exactly one [[row]] or one [[not_run]]")
        return 0
    if keys:
        print(f"LAND-ROWS: {ls.LAND_ROWS_FILE} does not cover the commit judged, so land_gate_test's "
              "ValidationDependencyTests is red on it, and on every session's main once it lands. In the same "
              "commit or push:")
        for block in repairs:
            print("\n".join(block))
        print(f"  Then check with `{ROWS_CHECK_COMMAND}` (or `--rev <commit>`).")
    for key in sorted(set(keys)):
        print(f"FINDING: {key}")
    if complete and keys:
        print("FINDINGS: complete")
    return 1


def rows_check_push(root: Path, raw: str) -> int:
    """rows_check over TRUST_PUSHED_REFS: each non-deletion pushed sha."""
    pushed = []
    for line in raw.splitlines():
        if not line.strip():
            continue
        fields = line.split()
        if len(fields) != 4 or not ROWS_HEX_SHA.match(fields[1]) or not ROWS_HEX_SHA.match(fields[3]):
            print(f"LAND-ROWS INVALID: malformed TRUST_PUSHED_REFS line {line!r}; expected "
                  "`<local_ref> <local_sha> <remote_ref> <remote_sha>`", file=sys.stderr)
            return 2
        pushed.append((fields[0], fields[1]))
    live = [(ref, sha) for ref, sha in pushed if not ROWS_ZERO_SHA.match(sha)]
    deletions = len(pushed) - len(live)
    if not live:
        print(f"SUBJECT: the pushed commits (TRUST_PUSHED_REFS: {deletions} deletion(s), nothing else)")
        print("SKIPPED: deletion(s) only, no commit pushed — nothing to judge")
        return 0
    names = ", ".join(f"{ref} {sha[:12]}" for ref, sha in live)
    extra = f"; {deletions} deletion(s) not judged" if deletions else ""
    return rows_check(root, [(f"{ref} {sha[:12]}", sha) for ref, sha in live],
                      f"SUBJECT: the pushed commits (TRUST_PUSHED_REFS: {names}{extra}), from git objects, not the "
                      "working tree")


def cmd_rows(args) -> int:
    """`rows --check`: the row table's covered rule on the pushed commit(s),
    `--rev`'s, or HEAD's (the push row fast.land-rows-coverage)."""
    if args.rev is not None:
        if not args.rev.strip():
            print("LAND-ROWS INVALID: --rev names no revision (empty or blank); omit it to judge the push in "
                  "flight or HEAD", file=sys.stderr)
            return 2
        return rows_check(REPO_ROOT, [(args.rev, args.rev)], f"SUBJECT: {args.rev}, from git objects")
    raw = os.environ.get("TRUST_PUSHED_REFS", "")
    if raw.strip():
        return rows_check_push(REPO_ROOT, raw)
    return rows_check(REPO_ROOT, [("HEAD", "HEAD")], "SUBJECT: HEAD, from git objects (no push in flight: "
                                                      "TRUST_PUSHED_REFS unset or empty)")


def main(argv: Optional[Sequence[str]] = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    sub = ap.add_subparsers(dest="cmd", required=True)
    p = sub.add_parser("plan")
    p.add_argument("--base")
    p.add_argument("--head", default="HEAD")
    p.add_argument("--json", action="store_true")
    p.add_argument("--run", action="store_true", help="plan then run validation in one reader session; publish separately")
    p.add_argument("--no-cache", action="store_true", help="with --run, execute selected checks without cached PASS")
    p.add_argument("--development", action="store_true", help="focused declared source-main checks; full diagnostic selection stays visible")
    p.add_argument("--verify-graph", action="store_true",
                   help="hold the graph to `targo metadata` first, as `run` always does")
    r = sub.add_parser("run")
    r.add_argument("--base")
    r.add_argument("--dry-run", action="store_true")
    r.add_argument("--no-cache", action="store_true")
    r.add_argument("--only", nargs="*")
    r.add_argument("--development", action="store_true", help="run focused declared source-main checks; the push rows run fresh either here or, beside a pre-push hook that answers for the landing, in that hook on the push; broad diagnostics are NOT RUN")
    land = sub.add_parser("land", help="run required legs and make an ordinary hooked main push; "
                         "execute the selected full Targo suite once in that hook")
    land.add_argument("--base")
    land.add_argument("--no-cache", action="store_true")
    land.add_argument("--development", action="store_true",
                      help="use the existing explicit source-main checks; broad diagnostics remain NOT RUN")
    sub.add_parser("landing-targo", help=argparse.SUPPRESS)
    sub.add_parser("landing-hook-finish", help=argparse.SUPPRESS)
    rp = sub.add_parser("replay")
    rp.add_argument("--last", type=int, default=50)
    rp.add_argument("--ref", default="origin/main")
    rp.add_argument("--json")
    e = sub.add_parser("explain")
    e.add_argument("paths", nargs="+")
    e.add_argument("--head", default="HEAD")
    nd = sub.add_parser("needs")
    nd.add_argument("leg")
    nd.add_argument("--base", required=True)
    nd.add_argument("--head", default="HEAD")
    nd.add_argument("--verify-graph", action="store_true")
    nd.add_argument("--development", action="store_true", help="diagnostic SKIP only for a fully covered declared source-main component/program delta")
    k = sub.add_parser("key")
    k.add_argument("leg")
    k.add_argument("--base")
    pf = sub.add_parser("prefetch", help="host setup: make the build graph answerable offline")
    pf.add_argument("--check", action="store_true", help="report only; touch no network")
    vt = sub.add_parser("validation-tests", help="run declared validator tests, with nonempty execution per module")
    vt.add_argument("modules", nargs="+")
    pr = sub.add_parser("push-rows", help="run and grade the hook's push-profile rows no leg covers, on the "
                                          "landing push of this checkout's HEAD onto origin's main tip as the remote "
                                          "names it (the push-rows leg; no --base: the destination is never the "
                                          "selection base)")
    pr.add_argument("--expect-tip", help="the origin main tip `run` planned its legs onto: NOT JUDGED when the "
                                         "remote names another (it is checked, never used as the destination)")
    pr.add_argument("--expect-remote", help="the captured publication remote; refuse another identity even at the same tip")
    pr.add_argument("--expect-head", help="the commit whose inputs and legs were planned; refuse a changed HEAD")
    pr.add_argument("--all-rows", action="store_true", help="execute all fresh push rows without claiming diagnostic-leg coverage")
    pr.add_argument(CHECKOUT_BOUND_FLAG, type=int, metavar="FD",
                    help="`run`'s leg only: a pipe holding run's token; run binds the checkout around this leg, "
                         "so push-rows reads no checkout pass of its own")
    rw = sub.add_parser("rows", help="the row table gates/land.toml on the pushed commit(s) (TRUST_PUSHED_REFS), "
                                     "--rev's or HEAD's, from git objects (the push row fast.land-rows-coverage)")
    rw.add_argument("--check", action="store_true", required=True,
                    help="exit 1 naming each tracked file its covered rule leaves without exactly one entry, "
                         "with the [[row]] that registers it")
    rw.add_argument("--rev", help="judge this commit (ignores TRUST_PUSHED_REFS)")
    args = ap.parse_args(argv)
    if argv is None:
        # The command line itself, never an in-process caller's argv: hold the
        # admission the rows borrow before anything is read or run.
        unadmitted = enter_admission(args)
        if unadmitted:
            print(f"LAND-GATE: NOT JUDGED — no build-slot admission: {unadmitted}. No selection, leg or row ran.")
            return 2
    try:
        return {"plan": cmd_plan, "run": cmd_run, "land": cmd_land,
                "landing-targo": cmd_landing_targo, "landing-hook-finish": cmd_landing_hook_finish,
                "replay": cmd_replay, "explain": cmd_explain,
                "key": cmd_key, "needs": cmd_needs, "push-rows": cmd_push_rows,
                "prefetch": cmd_prefetch, "validation-tests": cmd_validation_tests, "rows": cmd_rows}[args.cmd](args)
    except LockedWorkspaceInputs as exc:
        print(f"land-gate: {exc}; no build or proof leg ran", file=sys.stderr)
        try:
            print(f"input refusal record: {record_locked_input_refusal(exc)}", file=sys.stderr)
        except OSError as record_error:
            print(f"could not write the refusal record: {record_error}\n"
                  f"{json.dumps(exc.failures, indent=2)}", file=sys.stderr)
        return 2
    except GateCancelled as exc:
        _cancelled_diagnostic(exc)
        return 128 + exc.signum
    except (RuntimeError, host_budget.HostUnmeasurable) as exc:
        print(f"land-gate: {exc}", file=sys.stderr)
        return 2


# Bind this interpreter before main() or an importing caller can start work.
# Graph inputs may use a different root; executable-reader custody may not.
_discovery_origin = _git_ask(_DISCOVERY_SOURCE_ROOT, dict(git_query_env(), GIT_NO_REPLACE_OBJECTS="1"),
                          "rev-parse", "--verify", "HEAD^{commit}", timeout=10)
_DISCOVERY_ORIGIN_COMMIT = (_discovery_origin.stdout.strip() if _discovery_origin.returncode == 0 else "")
_DISCOVERY_INTERPRETER_READERS = _discovery_reader_identity(_DISCOVERY_SOURCE_ROOT)


if __name__ == "__main__":
    sys.exit(main())
