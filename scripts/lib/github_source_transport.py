#!/usr/bin/env python3
"""Owner-routed GitHub source data for the submodule synchronizer."""

from __future__ import annotations

import argparse
import json
import math
import re
import sys
from urllib.parse import urlsplit

import remote_tips


def github_repository(url: str) -> str | None:
    """Distinguish other transports without sending GitHub aliases to Git."""
    scp = re.fullmatch(r"(?:[^/@:\s]+@)?([^/:\s]+):.+", url)
    try:
        host = urlsplit(url).hostname
    except ValueError as error:
        raise ValueError("malformed source URL") from error
    if (host or "").lower().rstrip(".") != "github.com" and not (
        scp and scp[1].lower().rstrip(".") == "github.com"
    ):
        return None
    repository = remote_tips.github_repository(url)
    if repository is None:
        raise ValueError("GitHub source requires a credential-free canonical URL")
    return repository


def pin_refs(url: str, timeout: float) -> list[str]:
    repository = github_repository(url)
    if repository is None:
        raise ValueError("pin advertisement requires a GitHub source")
    result = remote_tips._agh(
        repository, ["repo", "refs", repository], timeout=timeout,
        env=remote_tips._env(),
    )
    if result.returncode:
        raise RuntimeError(result.stderr.strip() or "owner-routed Agh ref read refused")
    rows = json.loads(result.stdout, object_pairs_hook=remote_tips._unique_json_fields)
    if not isinstance(rows, list):
        raise ValueError("Agh ref advertisement is not an array")
    pins = {}
    for row in rows:
        if not isinstance(row, dict):
            raise ValueError("malformed Agh ref row")
        name, oid = row.get("ref"), row.get("oid")
        if not isinstance(name, str) or not isinstance(oid, str):
            raise ValueError("malformed Agh ref identity")
        if not name.startswith("refs/pins/"):
            continue
        if not re.fullmatch(r"[0-9a-f]{40}|[0-9a-f]{64}", oid) or re.search(r"\s", name):
            raise ValueError("invalid advertised pin identity")
        if name in pins and pins[name] != oid:
            raise ValueError("conflicting advertised pin")
        pins[name] = oid
    return [f"{oid} {name}" for name, oid in sorted(pins.items())]


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("operation", choices=("repository", "pins"))
    parser.add_argument("url")
    parser.add_argument("--timeout", type=float, default=20)
    args = parser.parse_args(argv)
    try:
        if args.operation == "repository":
            repository = github_repository(args.url)
            if repository is None:
                return 1
            print(repository)
        else:
            if not math.isfinite(args.timeout) or args.timeout <= 0:
                raise ValueError("source read deadline must be positive")
            for line in pin_refs(args.url, args.timeout):
                print(line)
    except (ValueError, RuntimeError, OSError) as error:
        print(f"GitHub source refused: {error}", file=sys.stderr)
        return 2
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
