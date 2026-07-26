#!/bin/sh
# Re-anchor the ADT-return corpus in fresh, compiler-emitted MIR dumps.
# Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0 OR MIT
set -eu

SCRIPT_DIR=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
REPO_ROOT=$(CDPATH= cd -- "$SCRIPT_DIR/../../../.." && pwd)
TRUSTC=${TRUSTC:-"$REPO_ROOT/build/host/stage2/bin/trustc"}

if [ ! -x "$TRUSTC" ]; then
    printf 'trustc is not executable: %s\n' "$TRUSTC" >&2
    exit 1
fi

case $("$TRUSTC" -V 2>/dev/null) in
    *'(trustc)'*) ;;
    *)
        printf 'compiler does not identify itself as trustc: %s\n' "$TRUSTC" >&2
        exit 1
        ;;
esac

if [ -n "${CAST_SOURCE:-}" ]; then
    SRC=$CAST_SOURCE
else
    set -- "$HOME"/.cargo/registry/src/*/cast-0.3.0/src/lib.rs
    if [ "$#" -ne 1 ] || [ ! -f "$1" ]; then
        printf '%s\n' \
            'expected exactly one cached cast-0.3.0/src/lib.rs; set CAST_SOURCE explicitly' >&2
        exit 1
    fi
    SRC=$1
fi

if [ ! -f "$SRC" ]; then
    printf 'cast source does not exist: %s\n' "$SRC" >&2
    exit 1
fi

expected_source_sha=$(awk 'NR == 1 { print $1 }' "$SCRIPT_DIR/SOURCE.sha256")
if command -v shasum >/dev/null 2>&1; then
    actual_source_sha=$(shasum -a 256 "$SRC" | awk '{ print $1 }')
elif command -v sha256sum >/dev/null 2>&1; then
    actual_source_sha=$(sha256sum "$SRC" | awk '{ print $1 }')
else
    printf '%s\n' 'need shasum or sha256sum to authenticate cast source' >&2
    exit 1
fi
if [ "$actual_source_sha" != "$expected_source_sha" ]; then
    printf 'cast source digest mismatch: expected %s, got %s\n' \
        "$expected_source_sha" "$actual_source_sha" >&2
    exit 1
fi

TMP=$(mktemp -d "${TMPDIR:-/tmp}/trust-adt-return-regenerate.XXXXXX")
pending=
cleanup() {
    rm -rf "$TMP"
    if [ -n "$pending" ]; then
        rm -f "$pending"
    fi
}
trap cleanup EXIT
trap 'exit 1' HUP INT TERM
DUMP_DIR=$TMP/dump
STAGE_DIR=$TMP/stage
mkdir -p "$DUMP_DIR" "$STAGE_DIR"

# Keep the original whole-crate extraction contract: real, unmodified crates.io
# source, compiled by Trust in dump-only/survey mode. Compiler diagnostics are
# retained on failure without flooding successful fixture refreshes.
if ! LIBRARY_PATH=${LIBRARY_PATH:-/opt/homebrew/lib} \
    "$TRUSTC" --edition 2018 --crate-type lib \
    -Z"trust-dump=mir:$DUMP_DIR" -Ztrust-policy=advisory \
    -o "$TMP/out.rlib" "$SRC" >"$TMP/trustc.log" 2>&1
then
    cat "$TMP/trustc.log" >&2
    exit 1
fi

select_dump() {
    expected=$1
    target=$2
    selected=
    count=0

    for dump in "$DUMP_DIR"/*.json; do
        # Modern dumps qualify crate-local paths with `lib::`; the historical,
        # descriptive fixture names do not. Normalize only for exact selection.
        def_path=$(jq -r '.def_path | gsub("lib::"; "")' "$dump")
        if [ "$def_path" = "$expected" ]; then
            selected=$dump
            count=$((count + 1))
        fi
    done

    if [ "$count" -ne 1 ]; then
        printf 'expected one dump for %s, found %s\n' "$expected" "$count" >&2
        exit 1
    fi

    cp "$selected" "$STAGE_DIR/$target"
}

select_dump '_64::<impl From<i16> for u16>::cast' '_64__<impl From<i16> for u16>__cast.json'
select_dump '_64::<impl From<i32> for u32>::cast' '_64__<impl From<i32> for u32>__cast.json'
select_dump '_64::<impl From<i64> for u64>::cast' '_64__<impl From<i64> for u64>__cast.json'
select_dump '_64::<impl From<i8> for u8>::cast' '_64__<impl From<i8> for u8>__cast.json'
select_dump '_64::<impl From<u16> for u8>::cast' '_64__<impl From<u16> for u8>__cast.json'
select_dump '_64::<impl From<u32> for i8>::cast' '_64__<impl From<u32> for i8>__cast.json'
select_dump '_64::<impl From<u64> for i32>::cast' '_64__<impl From<u64> for i32>__cast.json'
select_dump '_x128::<impl From<i128> for u128>::cast' '_x128__<impl From<i128> for u128>__cast.json'
select_dump '_x128::<impl From<u128> for i32>::cast' '_x128__<impl From<u128> for i32>__cast.json'
select_dump '_x128::<impl From<u128> for u8>::cast' '_x128__<impl From<u128> for u8>__cast.json'

count=$(find "$STAGE_DIR" -type f -name '*.json' | wc -l | tr -d ' ')
if [ "$count" -ne 10 ]; then
    printf 'expected ten staged fixtures, found %s\n' "$count" >&2
    exit 1
fi

# Authentication gate: the hardened ADT-return recognizer is entitled to rely
# only on first-class enum metadata. Never publish a legacy flattened Result,
# even when an old compiler can still deserialize and emit one.
for dump in "$STAGE_DIR"/*.json; do
    if ! jq -e '
        .body.locals[0].ty.Adt as $result
        | ($result.name == "core::result::Result")
          and ($result.disc_index_safe == true)
          and ($result.variants | length == 2)
          and ($result.variants[0].name == "Ok")
          and ($result.variants[0].discriminant == 0)
          and ($result.variants[0].fields | length == 1)
          and ($result.variants[1].name == "Err")
          and ($result.variants[1].discriminant == 1)
          and ($result.variants[1].fields | length == 1)
          and ($result.variants[1].fields[0][1].Adt.name | endswith("Error"))
          and ($result.variants[1].fields[0][1].Adt.disc_index_safe == true)
          and ($result.variants[1].fields[0][1].Adt.variants | length == 4)
    ' "$dump" >/dev/null
    then
        printf 'fresh dump lacks authenticated Result/Error variants: %s\n' "$dump" >&2
        exit 1
    fi
done

# All extraction and schema checks complete before the tracked corpus changes.
# Publish each complete file by same-filesystem rename so observers can never
# see a truncated JSON, even if regeneration is interrupted during publication.
for dump in "$STAGE_DIR"/*.json; do
    target=$SCRIPT_DIR/$(basename "$dump")
    pending=$target.new.$$
    cp "$dump" "$pending"
    mv "$pending" "$target"
    pending=
done

printf 're-anchored 10 ADT-return fixtures from %s with %s\n' "$SRC" "$TRUSTC"
