#!/usr/bin/env bash
# Per-unit verification scoping for `regenerate.sh`.
#
# WHY THIS EXISTS. `-Ztrust-dump=mir-only:<dir>` is gated on batteries-on
# verification (`trust_dump_domain_error` in rustc_driver_impl/src/lib.rs), so
# the extraction target must compile with `-Ztrust-verify=on`. Its DEPENDENCY
# graph must not — verifying third-party crates is the ~700-error blowup
# CLAUDE.md describes. The obvious spelling, `RUSTFLAGS=-Ztrust-verify=off` plus
# `cargo rustc --lib -- -Ztrust-verify=on`, does NOT work: Cargo places RUSTFLAGS
# AFTER the `cargo rustc -- …` target-only flags, and `-Ztrust-verify` is
# last-value-wins, so the global `off` overrides the per-target `on` and the dump
# gate rejects the invocation with
#
#   error: -Ztrust-dump=mir:<dir> and -Ztrust-dump=native-bundle:<dir> require
#          batteries-on Trust verification
#
# A wrapper is the only place that can append AFTER everything Cargo assembles.
# Identical in mechanism to `../expr-fold-corpus/regenerate-rustc-wrapper.sh`;
# kept as its own file so this corpus's recipe is self-contained.
#
# This changes NO verification semantics: the extraction target is verified
# exactly as `-Ztrust-verify=on` means, dependencies exactly as
# `-Ztrust-verify=off` means, and the run is still `-Ztrust-policy=advisory`
# dump-only (`dump_only_artifacts` reports every obligation `Unknown`, never
# `Proved`).
#
# Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0 OR MIT
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
