#!/usr/bin/env python3
"""Check the full bootstrap recipe envelope's locked source availability.

`check` is always offline. `prepare` is an explicit, fetch-only preparation
ceremony; it respects the caller's network policy, then repeats `check` under
the SAME deadline. Neither mode compiles, substitutes a dependency, updates a
lockfile, admits a root, or emits native verification evidence.

The manifest authority is bootstrap's existing source-declared recipe capability
envelope. It intentionally includes optional recipes, not just a guessed default
selection. The enclosing build owner must retain source/config/cache custody;
this availability observation is not a portable or authenticated cache seal.
Normal explicit stage0/1 iteration uses each actual frozen native Cargo request
instead; this full diagnostic remains for full/distribution/provenance readiness.
On Darwin each fetch runs under a per-fetch retirement custodian (`_fetch_darwin`,
docs/DECISION_QUEUE.md DARWIN-DEPENDENCY-FETCH-CUSTODIAN-1): the custodian is the
fetch's parent and process-group leader, holds the closure fence and Cargo's GC
exclusion (both inherited by the fetch), and retires its group when this helper
is lost; this helper retires that pinned group before reaping it. A recovery
command does not settle a previous child or authorize release of its enclosing
resources. The custodian contains a process group, not a descendant that leaves
it or closes its inherited descriptors, and it supplies no native
source/cache/SDK/GNU custody: the resident native preparation owner
(docs/OPEN_ISSUES.md BOOTSTRAP-DEPENDENCY-CUSTODY-1) replaces it once it is
qualified, and until then a Mac builds stage 2 through this route.
"""

from __future__ import annotations

import argparse
import ast
import ctypes
import errno
import hashlib
import json
import os
import re
import select
import shlex
import signal
import subprocess
import sys
import tempfile
import time
from pathlib import Path


class DependencyClosureError(RuntimeError):
    """No locked offline dependency readiness has been established."""


def _stage0_rust_body(source: str, opening: int) -> str:
    """Read a balanced recipe body, ignoring braces in comments and strings."""
    opener = source[opening]
    closer = {"{": "}", "(": ")"}[opener]
    depth = 0
    for token in re.finditer(r'"(?:\\.|[^"\\])*"|//[^\n]*|/\*.*?\*/|[{}()]',
                             source[opening:], re.S):
        if token.group() == opener:
            depth += 1
        elif token.group() == closer:
            depth -= 1
            if depth == 0:
                return source[opening + 1:opening + token.start()]
    raise RuntimeError("stage0 manifest roots: unbalanced bootstrap recipe")

def dist_vendor_manifest_roots(root: Path, *, source_view=None) -> set[str]:
    """Read the exact literal dist vendoring recipe; refuse unsupported grammar.

    Comments/strings cannot supply a function, and only its top-level body is
    authority. The complete body must be the current literal table plus its
    source-root mapping: additions and dynamic post-processing cannot disappear.
    """
    path = root / "src/bootstrap/src/core/build_steps/vendor.rs"
    if not (source_view.is_file(path) if source_view is not None else path.is_file()):
        return set()  # The standalone recipe reader also serves partial fixtures.
    source = source_view.read_text(path) if source_view is not None else path.read_text(encoding="utf-8")
    # Reject lexical forms this deliberately bounded source reader cannot parse.
    # They must never turn commented/string decoys into recipe authority.
    if re.search(r'\br\#*"', source) or any("/*" in m[0][2:] for m in re.finditer(r"/\*.*?\*/", source, re.S)):
        raise RuntimeError("stage0 manifest roots: unsupported dist vendor lexical form")
    lexical = re.sub(r'"(?:\\.|[^"\\])*"|//[^\n]*|/\*.*?\*/',
                     lambda m: " " * len(m[0]) if not m[0].startswith('"') else m[0],
                     source, flags=re.S)
    shadow = re.sub(r'''"(?:\\.|[^"\\])*"|'(?:\\.|[^'\\\n])' ''',
                    lambda m: " " * len(m[0]), lexical, flags=re.X)
    matches = [m for m in re.finditer(r"\bpub\s+fn\s+default_paths_to_vendor\b", shadow)
               if shadow[:m.start()].count("{") == shadow[:m.start()].count("}")]
    if len(matches) != 1:
        raise RuntimeError("stage0 manifest roots: missing or ambiguous dist vendor recipe")
    start = matches[0].start()
    opening = shadow.find("{", matches[0].end())
    header = re.sub(r"\s+", "", lexical[start:opening])
    if header != "pubfndefault_paths_to_vendor(builder:&Builder<'_>)->Vec<(PathBuf,Vec<&'staticstr>)>":
        raise RuntimeError("stage0 manifest roots: unsupported dist vendor signature")
    body = re.sub(r'"(?:\\.|[^"\\])*"|\s+', lambda m: m[0] if m[0].startswith('"') else "",
                  _stage0_rust_body(lexical, opening))
    prefix = "letpaths:Vec<(&str,Vec<&'staticstr>)>=vec!["
    suffix = "];paths.into_iter().map(|(path,submodules)|(builder.src.join(path),submodules)).collect()"
    if not body.startswith(prefix) or not body.endswith(suffix):
        raise RuntimeError("stage0 manifest roots: unsupported dist vendor body")
    table = body[len(prefix):-len(suffix)]
    row = re.compile(r'\("([A-Za-z0-9_./-]+/Cargo\.toml)",vec!\[((?:"[A-Za-z0-9_./-]+",?)*)\]\),')
    paths = set()
    while table:
        match = row.match(table)
        if match is None:
            raise RuntimeError("stage0 manifest roots: nonliteral dist vendor table")
        paths.add(match[1])
        table = table[match.end():]
    if not paths:
        raise RuntimeError("stage0 manifest roots: empty dist vendor table")
    for relative in paths:
        manifest = source_view.path(root / relative) if source_view is not None else (root / relative).resolve()
        if not manifest.is_relative_to(root.resolve()):
            raise RuntimeError(f"stage0 manifest root escapes checkout: {relative}")
        if not (source_view.is_file(manifest) if source_view is not None else manifest.is_file()):
            raise RuntimeError(f"required dist vendor manifest is missing: {relative}")
    return paths


def _stage0_rust_code(source: str) -> str:
    """Same-length code shadow with Rust strings/chars/comments blanked."""
    if len(source) > 4 * 1024 * 1024:
        raise RuntimeError("stage0 manifest roots: tool recipe source exceeds its bound")
    # Match at an offset in the original buffer. Slicing source[i:] at every
    # ordinary character makes this bounded lexer copy a quadratic byte count.
    raw_pattern = re.compile(r'(?:br|r)(#{0,255})"')
    char_pattern = re.compile(r"b?'(?:[^'\\\n]|\\(?:[nrt0'\"\\]|x[0-9a-fA-F]{2}|u\{[0-9a-fA-F_]+\}))'")
    result, i, size = list(source), 0, len(source)
    while i < size:
        start, end = i, None
        if source.startswith("//", i):
            end = source.find("\n", i)
            end = size if end == -1 else end
        elif source.startswith("/*", i):
            depth, j = 1, i + 2
            while j < size and depth:
                if source.startswith("/*", j): depth += 1; j += 2
                elif source.startswith("*/", j): depth -= 1; j += 2
                else: j += 1
            if depth: raise RuntimeError("stage0 manifest roots: unclosed recipe comment")
            end = j
        else:
            raw = raw_pattern.match(source, i)
            if raw:
                closing = '"' + raw[1]
                found = source.find(closing, raw.end())
                if found == -1: raise RuntimeError("stage0 manifest roots: unclosed raw recipe string")
                end = found + len(closing)
            elif source[i] == '"' or source.startswith('b"', i):
                j = i + (2 if source.startswith('b"', i) else 1)
                while j < size and source[j] != '"':
                    j += 2 if source[j] == "\\" else 1
                if j >= size: raise RuntimeError("stage0 manifest roots: unclosed recipe string")
                end = j + 1
            elif source[i] == "'" or source.startswith("b'", i):
                char = char_pattern.match(source, i)
                if char: end = char.end()
        if end is not None:
            result[start:end] = ["\n" if c == "\n" else " " for c in source[start:end]]
            i = end
        else:
            i += 1
    return "".join(result)


def _stage0_recipe_body(source: str, shadow: str, opening: int) -> tuple[str, str]:
    depth = 0
    for i in range(opening, len(shadow)):
        if shadow[i] == "{": depth += 1
        elif shadow[i] == "}":
            depth -= 1
            if depth == 0: return source[opening + 1:i], shadow[opening + 1:i]
    raise RuntimeError("stage0 manifest roots: unbalanced tool recipe body")


def _stage0_tool_recipe_paths(source: str) -> set[str]:
    """Follow the fixed assembly/helper graph, refusing unparsed recipes.

    This is a source profile, not a Rust evaluator. A new recipe helper or a
    dynamic ToolBuild path must extend this reader explicitly rather than
    disappear from the offline dependency denominator.
    """
    shadow = _stage0_rust_code(source)
    helpers = {"ensure_verifier_tool_bins", "ensure_sysroot_ay", "ay_tool_build_recipe",
               "targo_tool_build_recipe", "trustup_tool_build_recipe",
               "build_trustd_tool", "trustd_tool_build_recipe"}
    steps = {"Rustdoc", "CargoClippy", "Clippy", "Cargofmt", "Rustfmt", "RustAnalyzer",
             "RustAnalyzerProcMacroSrv", "Miri", "CargoMiri"}
    completed_wrapper = "ensure_default_verifier_tool_bins"
    prerequisite_wrapper = "ensure_sysroot_verifier_prerequisites"

    def definitions(function):
        return [m for m in re.finditer(r"\bfn\s+" + function + r"\s*\(", shadow)
                if shadow[:m.start()].count("{") == shadow[:m.start()].count("}")]

    split = bool(definitions(prerequisite_wrapper))
    wrappers = {completed_wrapper: "true" if split else "false"}
    if split:
        wrappers[prerequisite_wrapper] = "false"
    pending = [*wrappers, "ensure_user_facing_tools"]
    recipe_calls = helpers | {completed_wrapper, prerequisite_wrapper}
    seen, paths, edges = set(), set(), {}
    while pending:
        function = pending.pop()
        if function in seen:
            continue
        if len(seen) >= 16:
            raise RuntimeError("stage0 manifest roots: tool recipe graph exceeds its bound")
        seen.add(function)
        matches = definitions(function)
        if len(matches) != 1:
            raise RuntimeError(f"stage0 manifest roots: missing or ambiguous bootstrap recipe {function}")
        opening = shadow.find("{", matches[0].end())
        body, body_shadow = _stage0_recipe_body(source, shadow, opening)
        constructs = list(re.finditer(r"\bToolBuild\s*\{", body_shadow))
        called = {name for name in recipe_calls if re.search(r"\b" + name + r"\s*\(", body_shadow)}
        edges[function] = called
        # The split assembly has two exact, distinct dispatches. The older
        # profile also admits an inline recipe or its single false delegate.
        # Both dispatches keep the shared recipe's entire manifest population.
        if function in wrappers and (split or not constructs):
            flag = wrappers[function]
            if re.sub(r"\s+", "", body_shadow) != f"ensure_verifier_tool_bins(builder,target_compiler,sysroot,{flag});":
                raise RuntimeError(f"stage0 manifest roots: unsupported verifier assembly wrapper {function}")
        # A new factory/variable passed to ensure cannot hide behind a still
        # present unrelated literal ToolBuild elsewhere in the same body.
        for call in re.finditer(r"\.ensure\s*\(\s*([A-Za-z_]\w*)\s*(::|\(|\))", body_shadow):
            name, shape = call.groups()
            if shape == ")" or (shape == "(" and name not in helpers) or (shape == "::" and name not in steps):
                raise RuntimeError("stage0 manifest roots: unsupported ToolBuild factory or ensure expression")
        if not constructs and not called:
            raise RuntimeError(f"stage0 manifest roots: no ToolBuild in {function}")
        pending.extend(sorted(called))
        for construct in constructs:
            fields, field_shadow = _stage0_recipe_body(body, body_shadow, construct.end() - 1)
            markers = list(re.finditer(r"\bpath\s*:", field_shadow))
            if len(markers) != 1:
                raise RuntimeError("stage0 manifest roots: missing or ambiguous ToolBuild path")
            literal = re.match(r'\s*"([A-Za-z0-9_./-]+)"\s*,', fields[markers[0].end():])
            if literal is None:
                raise RuntimeError("stage0 manifest roots: nonliteral ToolBuild path")
            paths.add(literal[1] + "/Cargo.toml")
    # A visited set bounds traversal but cannot authenticate a cyclic recipe
    # which never reaches any constructors. Check the entire reached graph.
    incoming = {function: 0 for function in seen}
    for children in edges.values():
        for child in children:
            incoming[child] += 1
    ready = sorted(function for function, count in incoming.items() if count == 0)
    completed = 0
    while ready:
        function = ready.pop()
        completed += 1
        for child in sorted(edges[function]):
            incoming[child] -= 1
            if incoming[child] == 0:
                ready.append(child)
    if completed != len(seen):
        raise RuntimeError("stage0 manifest roots: cyclic tool recipe graph")
    return paths


def stage0_bootstrap_manifest_roots(root: Path, *, source_view=None) -> list[Path]:
    """Source-declared compiler/std/bootstrap and tool recipe entry manifests.

    This is the recipe capability envelope, including optional doc/test tools:
    selection also accepts existing configurations, not just our defaults.
    Tool paths come from recipes, NOT a tools allowlist or directory census.
    Membership and dependencies are handled separately.
    Nonliteral paths in the two batteries-on assembly bodies or bootstrap_tool!
    table fail visibly. Other literal recipe fields are covered by the source
    census regression; this bounded reader is not a Rust expression evaluator.
    """
    paths = {"Cargo.toml", "library/Cargo.toml", "src/bootstrap/Cargo.toml"}
    paths.update(dist_vendor_manifest_roots(root, source_view=source_view))
    bootstrap = root / "src/bootstrap/src/core"
    metadata = bootstrap / "metadata.rs"
    if source_view.is_file(metadata) if source_view is not None else metadata.is_file():
        paths.update(re.findall(r'collect_metadata\("([^"]+Cargo\.toml|Cargo\.toml)"\)',
                                source_view.read_text(metadata) if source_view is not None else metadata.read_text(encoding="utf-8")))
    compile_recipe = bootstrap / "build_steps/compile.rs"
    if source_view.is_file(compile_recipe) if source_view is not None else compile_recipe.is_file():
        paths.update(re.findall(r'\.join\("([^"]+Cargo\.toml)"\)',
                                source_view.read_text(compile_recipe) if source_view is not None else compile_recipe.read_text(encoding="utf-8")))
    recipe = root / "src/bootstrap/src/core/build_steps/tool.rs"
    if source_view.is_file(recipe) if source_view is not None else recipe.is_file():
        source = source_view.read_text(recipe) if source_view is not None else recipe.read_text(encoding="utf-8")
        original_source = source
        source = re.sub(r'"(?:\\.|[^"\\])*"|//[^\n]*|/\*.*?\*/',
                        lambda match: match[0] if match[0].startswith('"') else " ",
                        source, flags=re.S)
        paths.update(path + "/Cargo.toml" for path in
                     re.findall(r'\bpath:\s*"([^"\n]+)"', source))
        # bootstrap_tool!'s table feeds the macro's `path: $path` constructor.
        for invocation in re.finditer(r"\bbootstrap_tool!\s*[{(]", source):
            table = _stage0_rust_body(source, invocation.end() - 1)
            entries = re.findall(r'\b\w+\s*,\s*"([^"\n]+)"\s*,\s*"[^"\n]+"', table)
            if len(entries) != table.count(";"):
                raise RuntimeError("stage0 manifest roots: nonliteral bootstrap_tool! table")
            paths.update(path + "/Cargo.toml" for path in entries)
        paths.update(_stage0_tool_recipe_paths(original_source))
    canonical_root = root.resolve()
    found = []
    for path in sorted(paths):
        manifest = source_view.path(root / path) if source_view is not None else (root / path).resolve()
        if not manifest.is_relative_to(canonical_root):
            raise RuntimeError(f"stage0 manifest root escapes checkout: {path}")
        if source_view.is_file(manifest) if source_view is not None else manifest.is_file():
            found.append(manifest)
        elif source_view is not None:
            raise RuntimeError(f"declared source recipe manifest is absent from committed inputs: {path}")
    return found


_RECIPE_INPUTS = (
    "src/bootstrap/src/core/metadata.rs",
    "src/bootstrap/src/core/build_steps/compile.rs",
    "src/bootstrap/src/core/build_steps/vendor.rs",
    "src/bootstrap/src/core/build_steps/tool.rs",
)
_BASE_MANIFESTS = ("Cargo.toml", "library/Cargo.toml", "src/bootstrap/Cargo.toml")


def _cargo_home(root: Path, env: dict[str, str]) -> Path:
    """The Cargo home a fetch under `env` uses: CARGO_HOME, else the user's."""
    home = env.get("CARGO_HOME")
    if not home:
        user_home = env.get("HOME") or env.get("USERPROFILE")
        if not user_home:
            raise DependencyClosureError("CARGO_HOME and the user home are both unknown")
        home = str(Path(user_home) / ".cargo")
    cargo_home = Path(home)
    if not cargo_home.is_absolute():
        cargo_home = root / cargo_home
    return cargo_home


def _source_inputs(root: Path, manifests: list[Path], env: dict[str, str], *,
                   source_view=None, graph_source_view=None, source_only=False,
                   require_lockfiles=False) -> list[Path]:
    """Bind the recipe entries, possible ancestor locks/configs, and driver config.

    Cargo remains the resolver. We do not infer workspace ownership from a
    nearest-lock heuristic: that loses explicit and excluded workspace roots.
    The actual fetch is run on EVERY recipe entry, with no owner guess/dedup.
    """
    owner = (graph_source_view.root if graph_source_view is not None else root) / "scripts/recreate_bootstrap.py"
    # Reuse the source owner's declared member/path/patch census, without
    # importing its unrelated CLI or consulting bytecode/import search paths.
    reader = graph_source_view if graph_source_view is not None else source_view
    nodes = [node for node in ast.parse(reader.read_text(owner) if reader is not None
                                      else owner.read_text(encoding="utf-8")).body
             if isinstance(node, ast.ClassDef) and node.name == "_Stage0ManifestGraph"]
    if len(nodes) != 1:
        raise DependencyClosureError("dependency source manifest graph owner is absent or ambiguous")
    namespace = {"Path": Path, "__name__": "trust_dependency_manifest_graph"}
    exec(compile(ast.Module(body=nodes, type_ignores=[]), str(owner), "exec"), namespace)
    graph = (namespace["_Stage0ManifestGraph"](root, source_view=source_view) if source_view is not None
             else namespace["_Stage0ManifestGraph"](root))
    graph.collect(manifests)
    if graph.inconclusive:
        raise DependencyClosureError("dependency local manifest custody is inconclusive: "
                                     + "; ".join(sorted(graph.inconclusive)))
    if require_lockfiles:
        for entry in manifests:
            lock = graph.owner(entry).with_name("Cargo.lock")
            if not (source_view.is_file(lock) if source_view is not None else lock.is_file()):
                raise DependencyClosureError(f"declared producer workspace has no committed lockfile: {lock}")
    paths = {owner, *(root / item for item in (*_RECIPE_INPUTS, *_BASE_MANIFESTS))}
    # Include inheritance owners and all read manifests, not only fetch entry
    # manifests. The owner rejects even a transitive local path escaping root.
    for manifest in graph.documents:
        paths.add(manifest)
        for directory in (manifest.parent, *manifest.parent.parents):
            if not directory.is_relative_to(root):
                break
            paths.update(directory / name for name in ("Cargo.toml", "Cargo.lock"))
            paths.update(directory / ".cargo" / name for name in ("config", "config.toml"))
    if source_only:
        return sorted(paths)
    # Cargo searches config from the invocation cwd as well as CARGO_HOME.
    for directory in root.parents:
        paths.update(directory / ".cargo" / name for name in ("config", "config.toml"))
    homes = [_cargo_home(root, env)]
    # Native Targo imports this twin only if CARGO_HOME is ABSENT; an explicit
    # empty value preserves ordinary user-home fallback. Bind both possible
    # discovery locations without changing the exact driver or environment.
    if "CARGO_HOME" not in env and env.get("TARGO_HOME"):
        native_home = Path(env["TARGO_HOME"])
        homes.append(native_home if native_home.is_absolute() else root / native_home)
    for cargo_home in homes:
        paths.update(cargo_home / name for name in ("config", "config.toml"))
    return sorted(paths)


def _snapshot(paths: list[Path]) -> dict[str, str | None]:
    result = {}
    for path in paths:
        try:
            result[str(path)] = hashlib.sha256(path.read_bytes()).hexdigest()
        except FileNotFoundError:
            result[str(path)] = None
        except OSError as error:
            raise DependencyClosureError(f"cannot bind dependency input {path}: {error}") from error
    return result


def recipe_plan(root: Path, env: dict[str, str]) -> dict:
    """Pure full-envelope planning DATA for an actually owned native child.

    This reuses the same recipe and local-source reader as dependency_closure.
    It never fetches, launches a child, admits work or certifies readiness. The
    native owner must retain the original source/config/cache inputs and repeat
    this actual read at each resolver bookend; a saved digest grants nothing.
    """
    root = root.resolve()
    for relative in (*_RECIPE_INPUTS, *_BASE_MANIFESTS, "scripts/recreate_bootstrap.py"):
        if not (root / relative).is_file():
            raise DependencyClosureError(f"required bootstrap authority is missing: {relative}")
    manifests = stage0_bootstrap_manifest_roots(root)
    if not manifests:
        raise DependencyClosureError("bootstrap recipe manifest envelope is empty")
    inputs = _source_inputs(root, manifests, env) + [Path(__file__).resolve()]
    before = _snapshot(inputs)
    # Include absent ancestor configurations too: creating one changes the next
    # bookend. Canonical JSON keeps this bounded reply independent of dict order.
    encoded = json.dumps(before, sort_keys=True, separators=(",", ":")).encode("utf-8")
    return {
        "schema": "trust.bootstrap-dependency-plan.v1",
        "source": str(root),
        "manifests": [str(path.relative_to(root)) for path in manifests],
        "source_inputs_sha256": hashlib.sha256(encoded).hexdigest(),
        "source_inputs_count": len(before),
    }


def _diagnostic_tail_without_seeking(output) -> str:
    """Read bounded diagnostics without moving an active writer's file offset.

    An unresolved child may still hold this exact open-file description. Seeking
    the parent's duplicate would move the child's write cursor too. This read
    proves nothing about exit, output completeness or custody transfer.
    """
    if not hasattr(os, "pread"):
        return "dependency output tail unavailable: positional reads unsupported"
    try:
        descriptor = output.fileno()
        size = os.fstat(descriptor).st_size
        return os.pread(descriptor, 4096, max(0, size - 4096)).decode("utf-8", errors="replace")
    except OSError as error:
        return f"dependency output tail unavailable: {error}"


# ---------------------------------------------------------------------------
# Darwin: a per-fetch retirement custodian (DARWIN-DEPENDENCY-FETCH-CUSTODIAN-1).
#
# H (this helper) starts W (the custodian) in a new session; W starts the fetch C
# inside W's own process group, so C and its descendants carry pgid W.
#   * W is C's parent, so C's exit status comes from W's own reap of C.
#   * W watches H through a lifeline pipe. When H is lost (the landing gate retires
#     its leg by SIGTERM then SIGKILL to the x.py group, which holds H), or W's own
#     deadline passes, W kills its own live group, itself included: the group number
#     is W's live PID, so that signal cannot reach another group.
#   * H keeps W unreaped. Until H reaps W, W's PID, and so the group number, cannot
#     be reused (XNU never reallocates a zombie's PID, nor a PID equal to a live
#     group's ID). On a timeout, an exception, W's loss, or stragglers after W's exit,
#     H repeats killpg(W) until a libproc census finds no live member, and only then
#     reaps W. Nothing is signalled after a reap; no other numeric PID is signalled.
#   * W holds an exclusive closure fence and a shared lock on Cargo's
#     `.package-cache-mutate` (which excludes Cargo's GC, not its fetch), and the
#     cohort inherits both. If H and W both die, the kernel keeps both held until
#     the cohort's last member exits, and the next fetch refuses before birth.
# A missing primitive, or a group census libproc cannot take, refuses before any
# child starts. Not covered: a descendant that leaves the group (setsid) escapes
# killpg, and one that closes inherited descriptors escapes the fence
# (docs/OPEN_ISSUES.md BOOTSTRAP-DEPENDENCY-CUSTODY-1). That holds for `check`'s
# offline fetches and for `prepare`'s networked ones, whose git and HTTP helpers
# stay in the group.

_DARWIN_FENCE = ".trust-dependency-closure.lock"
_CARGO_MUTATE_LOCK = ".package-cache-mutate"
_LIBSYSTEM = "/usr/lib/libSystem.B.dylib"
_PROC_PIDTBSDINFO = 3
_PROC_BSDINFO_SIZE = 136
_SZOMB = 5
# These leave the fetch's dispositions as Popen(restore_signals=True) would.
_CHILD_DEFAULT_SIGNALS = ("SIGPIPE", "SIGXFSZ", "SIGINT", "SIGTERM", "SIGHUP", "SIGQUIT", "SIGTSTP")
_KQUEUE_NAMES = ("kqueue", "kevent", "KQ_FILTER_PROC", "KQ_FILTER_READ", "KQ_NOTE_EXIT",
                 "KQ_EV_ADD", "KQ_EV_ONESHOT", "KQ_EV_EOF", "KQ_EV_ERROR")

# W's whole program. It is passed with `-c`, so W runs exactly the text this helper
# loaded; an edit of the file after load cannot change it. W starts no thread and
# installs no handler. It blocks the seven signals a sender would use to end it
# (INT, TERM, HUP, QUIT, ALRM, USR1, USR2); it has no terminal, so no job-control
# signal reaches it. Any other signal that ends or stops W leaves its group to H's
# retirement, or, if H is gone too, to the fence.
_CUSTODIAN_SOURCE = r'''
import errno, fcntl, json, os, select, signal, sys, time
args = json.loads(sys.argv[1])
signal.pthread_sigmask(signal.SIG_BLOCK, {signal.SIGINT, signal.SIGTERM, signal.SIGHUP,
                       signal.SIGQUIT, signal.SIGALRM, signal.SIGUSR1, signal.SIGUSR2})
end = time.monotonic() + args["budget"]
LIFELINE, REPORT = 3, 4
def report(text):
    try:
        os.write(REPORT, (text + "\n").encode())
    except OSError:
        pass
def refuse(why):
    report("refused " + why)
    os._exit(3)
me = os.getpid()
if os.getpgid(0) != me or os.getsid(0) != me:
    refuse("not-leader: the custodian does not lead its own session and group")
kq = select.kqueue()
def client_gone(timeout):
    for event in kq.control(None, 1, timeout):
        if event.ident == LIFELINE and event.flags & select.KQ_EV_EOF:
            return True
    return os.getppid() != args["parent"]
try:
    kq.control([select.kevent(LIFELINE, filter=select.KQ_FILTER_READ, flags=select.KQ_EV_ADD)], 0, 0)
except OSError as error:
    refuse(f"lifeline-unavailable: the helper's lifeline cannot be watched ({error})")
if client_gone(0):
    refuse("client-gone: the helper ended before the fetch was started")
home = args["cargo_home"]
os.makedirs(home, exist_ok=True)
def take(name, mode, label):
    path = os.path.join(home, name)
    fd = os.open(path, os.O_RDWR | os.O_CREAT | os.O_CLOEXEC, 0o600)
    while True:
        try:
            fcntl.flock(fd, mode | fcntl.LOCK_NB)
            break
        except OSError as error:
            if error.errno not in (errno.EWOULDBLOCK, errno.EAGAIN):
                refuse(f"{label}-unsupported {path}: {error}")
        if time.monotonic() >= end:
            refuse(f"{label}-held {path}: a previous dependency-fetch cohort, or Cargo's GC, "
                   "still holds it; nothing was started")
        if client_gone(0.05):
            refuse("client-gone: the helper ended while the custodian waited for " + path)
    held, named = os.fstat(fd), os.stat(path)
    if (held.st_dev, held.st_ino) != (named.st_dev, named.st_ino):
        refuse(f"{label}-replaced {path}: the locked file is no longer the one at that path")
    return fd
fence = take(args["fence"], fcntl.LOCK_EX, "fence")
mutate = take(args["mutate"], fcntl.LOCK_SH, "cache-gc-exclusion")
os.set_inheritable(fence, True)
os.set_inheritable(mutate, True)
os.chdir(args["root"])
defaults = [getattr(signal, name) for name in args["defaults"] if hasattr(signal, name)]
try:
    child = os.posix_spawnp(args["argv"][0], args["argv"], os.environ,
                            file_actions=[(os.POSIX_SPAWN_DUP2, 5, 1), (os.POSIX_SPAWN_DUP2, 5, 2),
                                          (os.POSIX_SPAWN_CLOSE, 3), (os.POSIX_SPAWN_CLOSE, 4),
                                          (os.POSIX_SPAWN_CLOSE, 5)],
                            setsigmask=(), setsigdef=defaults)
except OSError as error:
    refuse(f"spawn {args['argv'][0]}: {error}")
os.close(5)
watch = [select.kevent(child, filter=select.KQ_FILTER_PROC,
                       flags=select.KQ_EV_ADD | select.KQ_EV_ONESHOT, fflags=select.KQ_NOTE_EXIT)]
exited = False
try:
    for event in kq.control(watch, 1, 0):
        if event.ident == child and (event.flags & select.KQ_EV_ERROR) and event.data == errno.ESRCH:
            exited = True
        elif event.ident == child and event.fflags & select.KQ_NOTE_EXIT:
            exited = True
except ProcessLookupError:
    exited = True  # it exited before the registration; still unreaped (W is its only reaper)
while not exited:
    left = end - time.monotonic()
    if left <= 0:
        report("retired deadline")
        os.killpg(me, signal.SIGKILL)
    for event in kq.control(None, 2, left):
        if event.ident == child and event.filter == select.KQ_FILTER_PROC:
            exited = True
        elif event.ident == LIFELINE and event.flags & select.KQ_EV_EOF:
            report("retired client-gone")
            os.killpg(me, signal.SIGKILL)
# Reaping C here is safe: the group's number is pinned by W itself (alive now, and
# unreaped by H afterwards), not by C.
_, status = os.waitpid(child, 0)
report(f"exit {os.waitstatus_to_exitcode(status)}")
os._exit(0)
'''


def _darwin_libproc():
    """libproc's group census and per-process state, or None when unavailable."""
    try:
        lib = ctypes.CDLL(_LIBSYSTEM, use_errno=True)
        listing, info = lib.proc_listpgrppids, lib.proc_pidinfo
    except (OSError, AttributeError):
        return None
    listing.restype = info.restype = ctypes.c_int
    listing.argtypes = [ctypes.c_int, ctypes.c_void_p, ctypes.c_int]
    info.argtypes = [ctypes.c_int, ctypes.c_int, ctypes.c_uint64, ctypes.c_void_p, ctypes.c_int]
    return lib


def _darwin_prerequisites() -> object:
    """Refuse before birth unless every custodian primitive exists."""
    missing = []
    if signal.getsignal(signal.SIGCHLD) != signal.SIG_DFL:
        missing.append("default SIGCHLD (something here could reap the custodian)")
    if not all(callable(getattr(os, name, None)) for name in ("posix_spawn", "waitstatus_to_exitcode")):
        missing.append("os.posix_spawn and os.waitstatus_to_exitcode")
    if not all(getattr(select, name, None) is not None for name in _KQUEUE_NAMES):
        missing.append("the kqueue process and read filters")
    try:
        import fcntl  # noqa: F401  (the custodian's locks)
    except ImportError:
        missing.append("fcntl")
    lib = _darwin_libproc()
    if lib is None:
        missing.append("libproc proc_listpgrppids and proc_pidinfo")
    else:
        try:  # a census that cannot see this process would read the cohort as gone
            _darwin_census(lib, os.getpgid(0), required=os.getpid())
        except OSError as error:
            missing.append(f"a libproc group census ({error})")
    if missing:
        raise DependencyClosureError(
            "Darwin dependency fetch requires its retirement custodian, unavailable here: "
            + "; ".join(missing) + "; no child was started")
    return lib


_LEADER = object()


def _darwin_group_members(lib, pgid: int, required=_LEADER) -> list[int]:
    """Every process whose group is `pgid`, zombies included.

    `required` (by default the leader `pgid`, the unreaped custodian) is a process
    known to be in the group, so it must be listed. libproc answers a failed
    listing with 0, not -1, so a listing without it is a failure, never an empty
    group. `required=None` skips the check (a test's view of a reaped group).
    """
    if required is _LEADER:
        required = pgid
    capacity = 256
    while True:
        buffer = (ctypes.c_int * capacity)()
        ctypes.set_errno(0)
        count = lib.proc_listpgrppids(pgid, buffer, ctypes.sizeof(buffer))
        if count < 0:
            raise OSError(ctypes.get_errno(), f"proc_listpgrppids({pgid}) failed")
        if count < capacity:
            members = [buffer[index] for index in range(count)]
            if required is not None and required not in members:
                raise OSError(ctypes.get_errno() or errno.EPERM,
                              f"proc_listpgrppids({pgid}) did not list its member {required}")
            return members
        capacity *= 4


def _darwin_live(lib, pid: int) -> bool:
    """False once `pid` is a zombie or gone (libproc answers a zombie with ESRCH).

    Any other failure counts as live: a member libproc cannot read is still killed
    and recounted, and retirement ends by its deadline, never by assuming it gone.
    """
    buffer = ctypes.create_string_buffer(_PROC_BSDINFO_SIZE)
    ctypes.set_errno(0)
    size = lib.proc_pidinfo(pid, _PROC_PIDTBSDINFO, 0, buffer, _PROC_BSDINFO_SIZE)
    if size <= 0:
        return ctypes.get_errno() != errno.ESRCH
    status = int.from_bytes(buffer.raw[4:8], sys.byteorder)
    return status != _SZOMB


def _darwin_census(lib, pgid: int, required=_LEADER) -> list[int]:
    """The live members of group `pgid`, read so that none can hide.

    The listing and each member's state are read at different moments, so a member
    that forks and exits in between would hide its child. The census therefore
    counts only when a second listing, taken after the state reads, names no
    process the first did not.
    """
    while True:
        members = _darwin_group_members(lib, pgid, required)
        live = [pid for pid in members if _darwin_live(lib, pid)]
        if set(_darwin_group_members(lib, pgid, required)) <= set(members):
            return live


def _darwin_retire_group(lib, custodian: int, until: float) -> bool:
    """Kill group `custodian` until no member lives; True when it is empty.

    Called only while `custodian` is unreaped, which pins the group number. The
    group is judged empty by enumeration, never from killpg's errno (XNU answers
    EPERM for a group whose only member is a zombie).
    """
    mask = {signal.SIGINT, signal.SIGTERM, signal.SIGHUP}
    previous = signal.pthread_sigmask(signal.SIG_BLOCK, mask)
    try:
        while True:
            try:
                live = _darwin_census(lib, custodian)
            except OSError:
                return False  # fail closed: the custodian stays unreaped, its group pinned
            if not live:
                return True
            if time.monotonic() >= until:
                return False
            try:
                os.killpg(custodian, signal.SIGKILL)
            except (PermissionError, ProcessLookupError):
                pass  # the next census decides
            time.sleep(0.01)
    finally:
        signal.pthread_sigmask(signal.SIG_SETMASK, previous)


def _darwin_kevent_exit(events, pid: int, timeout: float | None) -> bool:
    """Register for `pid`'s exit without reaping it; True once it has exited."""
    change = select.kevent(pid, filter=select.KQ_FILTER_PROC,
                           flags=select.KQ_EV_ADD | select.KQ_EV_ONESHOT,
                           fflags=select.KQ_NOTE_EXIT)
    try:
        ready = events.control([change], 1, timeout)
    except ProcessLookupError:
        return True  # exited before the registration; still unreaped (we are its only reaper)
    if not ready:
        return False
    event = ready[0]
    if event.flags & select.KQ_EV_ERROR:
        if event.data == errno.ESRCH:
            return True
        raise OSError(event.data, "cannot observe the dependency custodian's exit")
    if event.ident != pid or not event.fflags & select.KQ_NOTE_EXIT:
        raise DependencyClosureError("the dependency custodian's exit notification was not established")
    return True


def _fetch_darwin(command: list[str], root: Path, env: dict[str, str], end: float) -> None:
    lib = _darwin_prerequisites()
    import fcntl
    cargo_home = _cargo_home(root, env)
    with tempfile.TemporaryFile() as output:
        lifeline_read, lifeline_write = os.pipe()
        report_read, report_write = os.pipe()
        # Move W's three descriptors above 2..5 first, so no DUP2 below is a no-op
        # that would leave a close-on-exec flag in place.
        high = [fcntl.fcntl(fd, fcntl.F_DUPFD_CLOEXEC, 10)
                for fd in (lifeline_read, report_write, output.fileno())]
        os.close(lifeline_read)
        os.close(report_write)
        args = {"parent": os.getpid(), "root": str(root), "argv": list(command),
                "cargo_home": str(cargo_home), "fence": _DARWIN_FENCE, "mutate": _CARGO_MUTATE_LOCK,
                "defaults": list(_CHILD_DEFAULT_SIGNALS),
                # W ends one second before this helper stops waiting (end - 5), so a
                # refusal it reaches at its deadline is the one reported.
                "budget": max(0.5, end - time.monotonic() - 6.0)}
        defaults = [getattr(signal, name) for name in _CHILD_DEFAULT_SIGNALS if hasattr(signal, name)]
        try:
            custodian = os.posix_spawn(
                sys.executable,
                [sys.executable, "-I", "-S", "-B", "-c", _CUSTODIAN_SOURCE, json.dumps(args)],
                env,
                file_actions=[(os.POSIX_SPAWN_OPEN, 0, "/dev/null", os.O_RDONLY, 0),
                              (os.POSIX_SPAWN_DUP2, high[0], 3), (os.POSIX_SPAWN_DUP2, high[1], 4),
                              (os.POSIX_SPAWN_DUP2, high[2], 5)],
                setsid=True, setsigmask=(), setsigdef=defaults)
        except OSError as error:
            raise DependencyClosureError(
                f"Darwin dependency custodian could not start: {error}; no child was started") from error
        finally:
            for fd in high:
                os.close(fd)
        cause = None
        retired = False
        try:
            events = select.kqueue()
            try:
                exited = _darwin_kevent_exit(events, custodian, 0)
                while not exited:
                    left = end - time.monotonic() - 5.0
                    if left <= 0:
                        break
                    exited = bool(events.control(None, 1, left))
            finally:
                events.close()
            if not exited:
                cause = "budget"
        except BaseException as error:  # noqa: BLE001 - retire first, then re-raise
            cause = error
        finally:
            # Always: the custodian is unreaped here on every path, so the group is pinned.
            # Closing the lifeline first is the fallback: a live custodian then retires
            # its own group even if this cleanup is itself interrupted.
            os.close(lifeline_write)
            leftover = []
            if cause is None:
                # A fetch that exits must not leave its group running (the landing
                # gate's `abnormal_leftovers` rule): name them, then retire them.
                try:
                    leftover = [pid for pid in _darwin_census(lib, custodian) if pid != custodian]
                except OSError as error:
                    cause = error
            retired = _darwin_retire_group(lib, custodian, min(end, time.monotonic() + 5.0))
            if retired:
                os.waitpid(custodian, 0)  # the reap comes last; nothing is signalled after it
        os.set_blocking(report_read, False)
        try:
            record = os.read(report_read, 65536).decode("utf-8", errors="replace").strip()
        except BlockingIOError:
            record = ""
        finally:
            os.close(report_read)
        if not retired:
            raise DependencyClosureError(
                "dependency fetch cohort not retired within the original budget; the custodian "
                f"{custodian} stays unreaped (its group pinned) until this process exits, and the "
                "cohort's fence stays held until its last member exits\n"
                + _diagnostic_tail_without_seeking(output))
        if isinstance(cause, BaseException):
            raise cause
        last = record.splitlines()[-1] if record else ""
        if last == "retired deadline":
            cause = "budget"
        if cause == "budget":
            raise DependencyClosureError(
                "the total budget expired while this fetch was still running; its cohort was "
                f"retired: {shlex.join(command)}\n" + _diagnostic_tail_without_seeking(output))
        if last.startswith("refused "):
            raise DependencyClosureError(
                "Darwin dependency custodian " + last + "; no fetch was started")
        if not last.startswith("exit "):
            raise DependencyClosureError(
                f"dependency custodian ended before reporting ({last or 'no record'}); its cohort "
                f"{leftover or ''} was retired: {shlex.join(command)}\n"
                + _diagnostic_tail_without_seeking(output))
        if leftover:
            raise DependencyClosureError(
                f"locked dependency fetch left running descendants {leftover}; they were retired: "
                f"{shlex.join(command)}\n" + _diagnostic_tail_without_seeking(output))
        status = int(last.split()[1])
        if status:
            raise DependencyClosureError(
                f"locked dependency fetch exited {status}: {shlex.join(command)}\n"
                + _diagnostic_tail_without_seeking(output))


def _fetch(command: list[str], root: Path, env: dict[str, str], end: float) -> None:
    # Reserve five seconds INSIDE the finite budget for child observation.
    # Never signal a numeric PGID after wait(): an interrupted wait can already
    # have reaped the leader, allowing that numeric identity to be reused. The
    # Darwin path observes without reaping and reaps last for that reason.
    remaining = end - time.monotonic() - 5.0
    if remaining <= 0:
        raise DependencyClosureError("dependency preparation/check deadline exhausted")
    if sys.platform == "darwin":
        return _fetch_darwin(command, root, env, end)
    # Known boundary off Darwin: an unresolved-child exception is NOT a custody
    # transfer, and a terminated helper leaves its new-session fetch running
    # (docs/OPEN_ISSUES.md DEPENDENCY-FETCH-PARENT-DEATH-LINUX-1). Diagnostics
    # below neither retire the child nor authorize release of enclosing guards.
    linux = sys.platform.startswith("linux")
    if linux:
        if not hasattr(os, "pidfd_open") or not hasattr(signal, "pidfd_send_signal"):
            raise DependencyClosureError("Linux dependency child requires retained pidfd authority")
        # Bind the child before any wait. Auto-reaping/custom SIGCHLD handlers
        # could otherwise destroy original-child custody before pidfd_open.
        # The caller must also honor exclusive ownership of this Popen child.
        if signal.getsignal(signal.SIGCHLD) != signal.SIG_DFL:
            raise DependencyClosureError("Linux dependency child requires default SIGCHLD custody")
    with tempfile.TemporaryFile() as output:
        child = subprocess.Popen(
            command, cwd=root, env=env, stdout=output, stderr=subprocess.STDOUT,
            start_new_session=(os.name != "nt"),
        )
        pidfd = None
        try:
            if linux:
                # No wait/poll precedes this acquisition. The FD keeps the
                # original kernel process identity even if a later wait reaps.
                pidfd = os.pidfd_open(child.pid, 0)
            status = child.wait(timeout=max(0.001, end - time.monotonic() - 5.0))
        except BaseException as error:
            signal_error = None
            try:
                if pidfd is not None:
                    signal.pidfd_send_signal(pidfd, signal.SIGKILL)
                elif os.name == "nt":
                    # Windows Popen retains the original process HANDLE.
                    child.kill()
                # Other POSIX platforms have no stable signaling handle here.
                # A wait exception can mean the child was already reaped: do
                # not guess from returncode, poll, PID, or PGID. Observe only.
            except ProcessLookupError:
                pass  # the retained original process identity is already gone
            except OSError as failed_signal:
                signal_error = failed_signal
            left = end - time.monotonic()
            if left <= 0:
                raise DependencyClosureError(
                    "dependency child closure not established within original deadline; "
                    "retain owner custody for enclosing-scope retirement\n"
                    + _diagnostic_tail_without_seeking(output)
                ) from error
            try:
                child.wait(timeout=left)
            except BaseException as observation_error:
                # Name the cause when it is the budget: this refusal read as a custody
                # fault when the P5A3 mint's fresh cargo home overran 180 s (2026-11-05).
                cause = ("the total budget expired while this fetch was still running; "
                         if isinstance(error, subprocess.TimeoutExpired) else "")
                raise DependencyClosureError(
                    cause + "dependency child closure not established; no numeric PID/PGID signal "
                    "is authorized; retain owner custody for enclosing-scope retirement\n"
                    + _diagnostic_tail_without_seeking(output)
                ) from observation_error
            if signal_error is not None:
                raise DependencyClosureError(
                    f"retained direct-child signal failed: {signal_error}; "
                    "enclosing-scope closure still required\n"
                    + _diagnostic_tail_without_seeking(output)
                ) from error
            # This is only a bounded direct-child wait observation. It does
            # not establish descendant/cgroup closure or release any lease.
            raise
        finally:
            if pidfd is not None:
                os.close(pidfd)
        if status:
            size = output.tell()
            output.seek(max(0, size - 4096))
            detail = output.read().decode("utf-8", errors="replace")
            raise DependencyClosureError(
                f"locked dependency fetch exited {status}: {shlex.join(command)}\n{detail}"
            )


# One total finite budget for the whole envelope, and the CLI's ceiling. A cargo home
# that holds only archives and git databases (the mint's private one, by design:
# mint_seed_support.CARGO_HOME_INPUT_TREES) materializes registry sources and git
# checkouts on first use. Measured 2026-11-05 on m2 at a90d8682d8: 182 s for the 54
# manifests in such a home (ay 45 s, clean 45 s, ty 17 s), 64 s once warm. The earlier
# 180 s refused the P5A3 mint at its first x.py build.
DEFAULT_BUDGET_SECONDS = 900.0


def dependency_closure(
    root: Path, targo: str, env: dict[str, str], *, prepare: bool = False,
    deadline: float | None = None,
) -> dict:
    """Perform actual locked fetches; no JSON/cache verdict can satisfy this API."""
    root = root.resolve()
    end = time.monotonic() + DEFAULT_BUDGET_SECONDS if deadline is None else deadline
    if not targo:
        raise DependencyClosureError("configured bootstrap Targo is missing")
    driver = Path(targo)
    if not driver.is_absolute():
        driver = root / driver
    targo = str(driver)
    if not driver.is_file():
        raise DependencyClosureError(f"configured bootstrap Targo is missing: {targo!r}")
    for relative in (*_RECIPE_INPUTS, *_BASE_MANIFESTS, "scripts/recreate_bootstrap.py"):
        if not (root / relative).is_file():
            raise DependencyClosureError(f"required bootstrap authority is missing: {relative}")
    manifests = stage0_bootstrap_manifest_roots(root)
    if not manifests:
        raise DependencyClosureError("bootstrap recipe manifest envelope is empty")
    inputs = _source_inputs(root, manifests, env) + [Path(__file__).resolve(), Path(targo).resolve()]
    before = _snapshot(inputs)
    modes = (False, True) if prepare else (True,)
    completed = []
    total = len(modes) * len(manifests)
    for offline in modes:
        fetch_env = dict(env)
        if offline:
            fetch_env["CARGO_NET_OFFLINE"] = "true"
        for manifest in manifests:
            label = f"{len(completed) + 1}/{total} {'offline' if offline else 'caller-network-policy'} {manifest.relative_to(root)}"
            started = time.monotonic()
            print(f"bootstrap dependency fetch {label}: requested", file=sys.stderr, flush=True)
            command = [targo, "fetch", "--locked"]
            if offline:
                command.append("--offline")
            command += ["--manifest-path", str(manifest)]
            try:
                _fetch(command, root, fetch_env, end)
                if _snapshot(inputs) != before:
                    raise DependencyClosureError("bootstrap dependency inputs changed during fetch")
            except (DependencyClosureError, OSError, subprocess.TimeoutExpired) as error:
                progress_failure = ""
                try:
                    print(f"bootstrap dependency fetch {label}: refused after {time.monotonic() - started:.3f}s",
                          file=sys.stderr, flush=True)
                except (OSError, ValueError) as progress_error:
                    # A broken diagnostic sink must not replace the original
                    # child/custody failure and its cause chain.
                    progress_failure = f"; progress output failed: {progress_error}"
                raise DependencyClosureError(
                    f"dependency closure was not established for {label}: {error}{progress_failure}"
                ) from error
            completed.append({"manifest": str(manifest.relative_to(root)), "offline": offline})
            print(f"bootstrap dependency fetch {label}: command exited zero; inputs unchanged ({time.monotonic() - started:.3f}s)",
                  file=sys.stderr, flush=True)
    if time.monotonic() > end:
        raise DependencyClosureError("dependency closure finished outside its deadline")
    return {
        "schema": "trust.bootstrap-offline-dependency-closure.v1",
        "scope": "recipe-capability-envelope; availability only; no native/proof/root admission",
        "source_inputs_sha256": before,
        "completed_fetches": completed,
    }


def _preparation_hint(root: Path, targo: str, env: dict[str, str]) -> str:
    """Describe the same explicit cache and policy; never execute shell text."""
    cargo_home = env.get("CARGO_HOME")
    if not cargo_home:
        return (
            "No explicit CARGO_HOME is set; no preparation command can be bound. "
            "Set an explicit CARGO_HOME and retry."
        )
    # Trust: Python 3.14 non-strict resolution can retain a symlink loop.
    # Bind only an existing canonical source root in the recovery command.
    root = root.resolve(strict=True)
    if not os.path.isabs(cargo_home):
        cargo_home = str(root / cargo_home)
    driver = Path(targo)
    if not driver.is_absolute():
        driver = root / driver
    # Trust: absence is policy too. A pasted command must not inherit a new
    # shell's warning overrides; explicit empty values must still be refused
    # by the actual driver rather than silently normalized into absence.
    command = ["env", "-u", "CARGO_BUILD_WARNINGS", "-u", "TARGO_BUILD_WARNINGS",
               "CARGO_HOME=" + cargo_home]
    command.extend(key + "=" + env[key]
                   for key in ("CARGO_BUILD_WARNINGS", "TARGO_BUILD_WARNINGS") if key in env)
    command += [sys.executable, "-I", "-S", "-B", str(Path(__file__).resolve()),
                "prepare", "--repo-root", str(root), "--targo", str(driver)]
    return "Prepare the SAME source and Cargo home separately, then retry:\n  " + shlex.join(command)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("mode", choices=("check", "prepare", "plan"))
    parser.add_argument("--repo-root", type=Path, default=Path(__file__).resolve().parent.parent)
    parser.add_argument("--targo", help="exact configured bootstrap Targo path")
    parser.add_argument("--timeout", type=float, default=DEFAULT_BUDGET_SECONDS,
                        help="one total finite budget")
    args = parser.parse_args()
    if not 5.0 < args.timeout <= DEFAULT_BUDGET_SECONDS:
        parser.error("the total budget must be greater than 5 and at most 900 seconds")
    if args.mode != "plan" and not args.targo:
        parser.error("--targo is required for check or prepare")
    end = time.monotonic() + args.timeout
    environment = dict(os.environ)
    try:
        if args.mode == "plan":
            report = recipe_plan(args.repo_root, environment)
        else:
            report = dependency_closure(
                args.repo_root, args.targo, environment, prepare=args.mode == "prepare", deadline=end,
            )
    except (DependencyClosureError, RuntimeError) as error:
        sys.stderr.write(f"bootstrap dependency closure REFUSED: {error}\n")
        # Trust: a diagnostic path failure must not replace the original
        # refusal or accidentally describe an unbound recovery invocation.
        try:
            hint = ("No dependency work was dispatched by the pure recipe planner."
                    if args.mode == "plan" else
                    _preparation_hint(args.repo_root, args.targo, environment))
        except (OSError, RuntimeError) as hint_error:
            hint = "Recovery command unavailable; no preparation command can be bound: " + str(hint_error)
        sys.stderr.write(hint + "\n")
        return 1
    print(json.dumps(report, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
