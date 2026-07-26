#!/usr/bin/env bash
# Cargo places RUSTFLAGS after `cargo rustc -- ...` target-only flags in this
# toolchain, while trustc's `-Ztrust-verify=off` option is last-value-wins. Keep
# dependencies batteries-off, but append the enabling value after every Cargo
# flag for the one extraction target. This avoids verifying the dependency
# graph and makes the dump workflow both reproducible and fast.
set -euo pipefail

rustc="$1"
shift

is_extract=0
previous=""
for argument in "$@"; do
  if [[ "$previous" == "--crate-name" && "$argument" == "extract_foldmemo" ]]; then
    is_extract=1
    break
  fi
  previous="$argument"
done

if [[ "$is_extract" == 1 ]]; then
  exec "$rustc" "$@" -Ztrust-verify=on
fi
exec "$rustc" "$@"
