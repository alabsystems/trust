#!/usr/bin/env bash
# Build the checkout's std-only fact reader with Trust before each invocation.
# Its output is data, never a stored gate verdict. The caller falls back to its
# original real reader if this source build or the supported profile is absent.
set -uo pipefail
source_root="$(CDPATH= cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)" || exit 2
tool="${TARGO:-targo}"
cd "$source_root" || exit 2
exec "$source_root/scripts/build-slot" -- "$tool" --unverified run --quiet --locked --offline \
  --manifest-path "$source_root/crates/trust-oracle-freeze-facts/Cargo.toml" \
  --target-dir "$source_root/crates/trust-oracle-freeze-facts/target/native.noindex" -- "$@"
