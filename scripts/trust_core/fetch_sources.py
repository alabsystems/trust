#!/usr/bin/env python3
"""fetch_sources — put every pinned external source the Trust core checkers read into the
durable source cache, at exactly its pinned revision.

The checkers (scripts/trust_core/*.py) read MiniRust, the Rust Reference, the FLS,
a-mir-formality, the RFCs and rust-lang/rust's standard library at the revisions
docs/trust-core/EXTERNAL_PINS.toml records. They never fetch: a checker that reached the
network would judge whatever the network served. This script is the one place that does,
and it is idempotent: a clone that already holds its pin is left alone.

The cache is `common.sources_root()`: $TRUST_CORE_SOURCES, else
$XDG_CACHE_HOME/trust/trust-core-sources, else ~/.cache/trust/trust-core-sources. It is
outside the repository (build/ belongs to x.py) and outside /tmp, which macOS empties.

How each source is fetched follows how the checkers read it (common.verify_clone):
  * read = "checkout": a plain checkout of the pin, fetched at depth 1;
  * read = "objects" with a `branch`: full history of that branch, no checkout, because
    the checker re-derives the pin as the branch's first-parent commit at the alignment;
  * rust-lang/rust: a blob-filtered sparse checkout at the alignment commit of library/
    (D0.7's standard-library corpus, the recipe static_semantics_source_map.py names) and of
    each upstream compiler file a checker compares a `Trust:`-edited file against
    (RUST_UPSTREAM_FILES: D0.3's constant-conversion evidence). The superproject does not
    hold the alignment commit's objects, so this clone is where the aligned text is read.

Exit 0 when every source holds its pin afterwards, 1 otherwise. --check reports without
fetching.

Author: Andrew Yates. Copyright 2026 Andrew Yates. License: Apache-2.0 OR MIT.
"""
from __future__ import annotations

import argparse
import subprocess
import sys
from dataclasses import replace
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import common as C  # noqa: E402

RUST_URL = "https://github.com/rust-lang/rust"
# Upstream compiler files a checker reads at the alignment commit; each is checked out, so
# its blob is local and no read of it touches the network.
RUST_UPSTREAM_FILES = ("compiler/rustc_const_eval/src/const_eval/eval_queries.rs",)
RUST_SPARSE = ("/library/",) + tuple(f"/{rel}" for rel in RUST_UPSTREAM_FILES)
RUST_LIBRARY_ROOTS = tuple(f"library/{crate}/src" for crate in ("core", "alloc", "std", "proc_macro"))


def run(args: list[str], cwd: Path | None = None) -> None:
    subprocess.run(args, cwd=cwd, check=True)


def holds(path: Path, revision: str) -> bool:
    return (path / ".git").exists() and C.git(path, "cat-file", "-e", f"{revision}^{{commit}}") is not None


def head_is(path: Path, revision: str) -> bool:
    return (C.git(path, "rev-parse", "HEAD") or "").strip() == revision


def rust_missing_blobs(path: Path, revision: str) -> list[str] | None:
    """The oids of the blobs the checkers read at the pin that this object store lacks.

    The required blobs are the sparse library inventory and each RUST_UPSTREAM_FILES
    entry, checked in one offline batch. Gitlinks name separate repositories, not blobs
    this Rust object store can supply. Other superproject sources are intentionally
    outside this cache's declared input. None when the requirement itself cannot be
    read -- no pin, a malformed inventory, an absent upstream file, or a declared library
    root that is not a tree -- because only a blob can be restored by fetching its oid.
    """
    if not holds(path, revision):
        return None
    inventory = C.git(path, "ls-tree", "-r", "-z", revision, "--", "library", *RUST_UPSTREAM_FILES,
                      binary=True)
    if inventory is None:
        return None
    blobs = set()
    upstream = set()
    for entry in inventory.split(b"\0"):
        if not entry:
            continue
        meta, separator, rel = entry.partition(b"\t")
        fields = meta.split()
        if not separator or len(fields) != 3:
            return None
        mode, kind, oid = fields
        if kind == b"commit" and mode == b"160000" and rel.startswith(b"library/"):
            continue
        if kind != b"blob" or mode not in (b"100644", b"100755", b"120000"):
            return None
        if len(oid) != 40 or any(c not in b"0123456789abcdef" for c in oid):
            return None
        blobs.add(oid.decode("ascii"))
        upstream.add(rel.decode("utf-8", "replace"))
    if not set(RUST_UPSTREAM_FILES) <= upstream:
        return None
    requests = [(f"{revision}:{root}", "tree") for root in RUST_LIBRARY_ROOTS]
    requests += [(oid, "blob") for oid in sorted(blobs)]
    observed = C.git(path, "cat-file", "--batch-check=%(objectname) %(objecttype)",
                     stdin="".join(f"{name}\n" for name, _ in requests).encode())
    if observed is None:
        return None
    lines = observed.splitlines()
    if len(lines) != len(requests):
        return None
    missing = []
    for line, (name, kind) in zip(lines, requests):
        fields = line.split()
        if len(fields) == 2 and fields[1] == kind:
            continue
        if kind == "blob" and fields == [name, "missing"]:
            missing.append(name)
            continue
        return None
    return missing


def rust_ready(path: Path, revision: str) -> bool:
    """Every required source blob is local; a pin or tree alone is insufficient."""
    return rust_missing_blobs(path, revision) == []


def fetch_checkout(path: Path, url: str, revision: str) -> None:
    if not (path / ".git").exists():
        path.mkdir(parents=True, exist_ok=True)
        run(["git", "init", "-q", str(path)])
        run(["git", "-C", str(path), "remote", "add", "origin", url])
    if not holds(path, revision):
        run(["git", "-C", str(path), "fetch", "-q", "--depth", "1", "origin", revision])
    run(["git", "-C", str(path), "checkout", "-q", "--detach", revision])


def branch_ready(path: Path, source: C.Source, pins: C.Pins) -> bool:
    """Holding the pin alone is insufficient when its derivation needs a branch."""
    if not holds(path, source.revision):
        return False
    findings = C.Findings()
    C.verify_clone(findings, path, source, pins)
    return not findings.violations


def require_history(path: Path, source: C.Source, pins: C.Pins) -> None:
    findings = C.Findings()
    C.verify_clone(findings, path, source, pins)
    if findings.violations:
        raise RuntimeError("; ".join(findings.violations))


def fetch_branch_history(path: Path, source: C.Source, pins: C.Pins) -> None:
    branch = source.branch
    assert branch is not None
    remote_branch = "refs/heads/" + branch.removeprefix("refs/remotes/origin/")
    if not (path / ".git").exists():
        run(["git", "clone", "-q", "--no-checkout", source.url, str(path)])
    advertised = subprocess.run(
        ["git", "-C", str(path), "ls-remote", "--exit-code", "origin", remote_branch],
        capture_output=True, text=True,
    )
    if advertised.returncode == 0:
        run(["git", "-C", str(path), "fetch", "-q", "origin", f"+{remote_branch}:{branch}"])
        require_history(path, source, pins)
        return
    if advertised.returncode != 2:
        # A transport/authentication failure is not evidence of a renamed branch.
        raise subprocess.CalledProcessError(advertised.returncode, advertised.args,
                                            output=advertised.stdout, stderr=advertised.stderr)
    head = subprocess.run(["git", "-C", str(path), "ls-remote", "--symref", "origin", "HEAD"],
                          capture_output=True, text=True, check=True)
    refs = [line.removeprefix("ref: ").split("\t")[0] for line in head.stdout.splitlines()
            if line.startswith("ref: refs/heads/") and line.endswith("\tHEAD")]
    tips = [line.split("\t")[0] for line in head.stdout.splitlines()
            if line.endswith("\tHEAD") and C.HEX40.fullmatch(line.split("\t")[0])]
    if len(refs) != 1 or len(tips) != 1 or refs[0] == remote_branch:
        raise RuntimeError(f"{remote_branch} is absent and origin has no distinct symbolic default branch")
    # Fetch the sampled immutable tip with full history. Do not manufacture a
    # history ending at the old pin, which would make latest-at-alignment tautological.
    tip = tips[0]
    run(["git", "-C", str(path), "fetch", "-q", "--no-tags", "--no-write-fetch-head",
         "--refmap=", "origin", tip])
    require_history(path, replace(source, branch=tip), pins)
    # Only a fully checked replacement may populate the historical local name.
    # The checkers remain unchanged and independently re-derive the same pin.
    run(["git", "-C", str(path), "update-ref", branch, tip])
    print(f"fetch_sources: {source.name}: {remote_branch} is absent; {refs[0]} at {tip} "
          f"reproduces the recorded first-parent pin {source.revision}")


def fetch_rust(path: Path, revision: str) -> None:
    if not (path / ".git").exists():
        path.mkdir(parents=True, exist_ok=True)
        run(["git", "init", "-q", str(path)])
        run(["git", "-C", str(path), "remote", "add", "origin", RUST_URL])
    if not holds(path, revision):
        run(["git", "-C", str(path), "fetch", "-q", "--depth", "1", "--filter=blob:none", "origin", revision])
    # Fetch every absent required blob by oid before the checkout. A checkout reads only
    # the blobs whose index entries changed, so a blob lost from an otherwise complete
    # clone would stay lost behind an unchanged working tree. This is the request git's
    # own lazy fetch makes, done once for the whole inventory.
    missing = rust_missing_blobs(path, revision)
    if missing:
        subprocess.run(["git", "-C", str(path), "-c", "fetch.negotiationAlgorithm=noop", "fetch", "-q",
                        "--no-tags", "--no-write-fetch-head", "--recurse-submodules=no",
                        "--filter=blob:none", "--stdin", "origin"],
                       input="".join(f"{oid}\n" for oid in missing), text=True, check=True)
    run(["git", "-C", str(path), "sparse-checkout", "set", "--no-cone", *RUST_SPARSE])
    run(["git", "-C", str(path), "checkout", "-q", "--detach", revision])


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n", 1)[0])
    parser.add_argument("--check", action="store_true", help="report which sources are missing; fetch nothing")
    args = parser.parse_args(argv)
    pins = C.load_pins()
    root = C.sources_root()
    wanted = [(s.name, root / s.directory, s) for s in pins.sources.values()]
    wanted.append(("rust", root / "rust", C.Source("rust", RUST_URL, pins.alignment, pins.alignment_date, "objects")))
    missing = []
    for name, path, source in wanted:
        if name == "rust":
            ready = rust_ready(path, source.revision)
        else:
            ready = (branch_ready(path, source, pins) if source.branch else
                     holds(path, source.revision) and (source.read == "objects" or head_is(path, source.revision)))
        if ready:
            print(f"fetch_sources: {name}: holds {source.revision[:12]} at {path}")
            continue
        if args.check:
            missing.append(name)
            print(f"fetch_sources: {name}: MISSING at {path}")
            continue
        print(f"fetch_sources: {name}: fetching {source.revision[:12]} from {source.url} into {path}")
        try:
            if name == "rust":
                fetch_rust(path, source.revision)
            elif source.read == "objects" and source.branch:
                fetch_branch_history(path, source, pins)
            else:
                fetch_checkout(path, source.url, source.revision)
        except (subprocess.CalledProcessError, RuntimeError) as error:
            print(f"fetch_sources: {name}: fetch failed: {error}", file=sys.stderr)
            missing.append(name)
            continue
        ready = (rust_ready(path, source.revision) if name == "rust" else
                 branch_ready(path, source, pins) if source.branch else holds(path, source.revision))
        if not ready:
            missing.append(name)
            print(f"fetch_sources: {name}: still does not hold {source.revision}", file=sys.stderr)
    if missing:
        print(f"fetch_sources: {len(missing)} source(s) not at their pins: {', '.join(missing)}", file=sys.stderr)
        return 1
    print(f"fetch_sources: all {len(wanted)} sources hold their pins under {root}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
