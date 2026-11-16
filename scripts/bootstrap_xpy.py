#!/usr/bin/env python3
"""Run normal stage0/1 x.py build/test with the recreator's bound producer inputs.

This neither creates a seed/config nor grants stage/release provenance. Run the
supported recreator first, then use the same explicit Clean Lean selection for
normal test-support preparation. x.py/Cargo retain all rebuild decisions.
"""
from __future__ import annotations

import argparse
import hashlib
from pathlib import Path
import sys

import recreate_bootstrap as bootstrap


def configured_bootstrap(root: Path) -> tuple[bootstrap.WrittenBootstrapConfig, Path | None]:
    """Read the existing Trust config; never select a different compiler mode."""
    import tomllib

    config, content = bootstrap._existing_bootstrap_config(root)
    if config is None:
        raise RuntimeError("normal bootstrap support needs an existing recreator configuration")
    table = tomllib.loads(content.decode("utf-8")).get("build", {})
    if not isinstance(table, dict):
        raise RuntimeError("bootstrap [build] must be a table")
    mode = bootstrap._declared_bootstrap_mode(content, table)
    identity = bootstrap.WrittenBootstrapConfig(config, hashlib.sha256(content).hexdigest())
    if mode == "seed":
        return identity, None
    if mode == "atpkg":
        if bootstrap.minted_seed_pin(root) is not None:
            raise RuntimeError("minted source pin retires configured atpkg stage0 (D12 (d))")
        authority = bootstrap._capture_atpkg_stage0_authority(table)
        if not bootstrap._atpkg_authority_ready(authority):
            raise RuntimeError("configured atpkg Trust stage0 authority was refused")
        return identity, Path(authority["authority"]["pack"]["pack_local_path"]) / "bin/trustc"
    raise RuntimeError("normal bootstrap support requires an unambiguous Trust seed/atpkg config")


def main(argv: list[str] | None = None) -> int:
    bootstrap.ensure_python_311()
    parser = argparse.ArgumentParser(description=__doc__, allow_abbrev=False)
    parser.add_argument("--host")
    parser.add_argument("--stage", type=int, choices=(0, 1), default=1)
    parser.add_argument("-j", "--jobs", type=int)
    bootstrap.add_clean_lean_arguments(parser)
    parser.add_argument("command", choices=("build", "test"))
    parser.add_argument("extra", nargs=argparse.REMAINDER,
                        help="Normal x.py arguments; put this wrapper's options before command")
    args = parser.parse_args(argv)
    root = bootstrap.repo_root()
    try:
        extra = bootstrap.normal_xpy_arguments(args.extra)
        selection = bootstrap.clean_lean_selection(args)
        if selection is None:
            raise ValueError("normal bootstrap support requires explicit Clean Lean input selection")
        config, compiler = configured_bootstrap(root)
        return bootstrap.run_xpy(
            root, args.host or bootstrap.host_triple(), args.command, args.stage, args.jobs,
            extra, seed_mode=True, seed_compiler=compiler, clean_lean=selection,
            normal_config=config,
        )
    except (RuntimeError, OSError, ValueError) as error:
        print(f"Normal x.py producer environment refused: {error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
