#!/bin/bash
# Regenerates x86_64-exec-entry-elf.hex and aarch64-exec-entry-elf.hex, or with
# --check proves the checked-in ones reproduce. PROVENANCE.md, beside this
# script, records what the two files are, the toolchains measured, and what
# their layout does and does not rule out.
#
# Each is a statically linked ELF executable (ET_EXEC) whose `.text` holds four
# global functions, in address order: `decoy_before_entry` (the start of
# `.text`), `_start` (NOT the entry), `exec_entry` (e_entry; several distinct
# instructions with a conditional branch, so three basic blocks) and
# `decoy_after_entry` (the end of `.text`). The assembly is below; it is
# assembled by clang for <arch>-unknown-linux-gnu, linked by LLD's ELF linker
# (-static -no-pie --build-id=none -e exec_entry, no libraries), and stripped
# of `.comment`, the one section that names the linker's version.
# crates/trust-integration-tests/tests/binary_to_trust_ir_e2e.rs pins the
# sha256, e_entry, `exec_entry`'s bytes and every function's address: a
# regenerated fixture must be re-pinned there.
#
# The script refuses (exit 2) an output that is not an ET_EXEC for the expected
# machine, or whose function symbols are not exactly the four above in that
# order with e_entry at `exec_entry`, the first at the start of `.text` and the
# last ending at its end. The hex format is the siblings': lowercase, 32 bytes
# per line, whitespace ignored when decoded.
#
# Tools: clang on PATH; the first ld.lld or rust-lld on PATH that runs
# (`--version` exits 0), else the first such rust-lld under
# ~/.rustup/toolchains/*/lib/rustlib/*/bin/; llvm-objcopy or rust-objcopy found
# the same way; python3. A candidate that does not run (e.g. a rustup rust-lld
# whose @rpath/libLLVM.dylib is missing) is skipped, not used.
#
# Usage:
#   tests/fixtures/binary_decomp/regenerate_exec_entry_elf.sh          # rewrite the .hex files
#   tests/fixtures/binary_decomp/regenerate_exec_entry_elf.sh --check  # rebuild, compare, write nothing
#
# Exit codes: 0 written / reproduced; 1 --check found a difference; 2 a tool is
# missing or a step failed.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"

MODE=write
case "${1:-}" in
    "") ;;
    --check) MODE=check ;;
    *) echo "usage: $0 [--check]" >&2; exit 2 ;;
esac

die() {
    echo "ERROR: $1" >&2
    exit 2
}

command -v clang >/dev/null 2>&1 || die "clang not found on PATH"
command -v python3 >/dev/null 2>&1 || die "python3 not found on PATH"

# Every candidate, from PATH or from ~/.rustup, must run before it is used.
LLD=()
try_lld() {
    local path="$1"
    shift
    if [ -x "$path" ] && { "$path" "$@" --version >/dev/null 2>&1; } 2>/dev/null; then
        LLD=("$path" "$@")
        return 0
    fi
    echo "skipping linker that does not run: $path" >&2
    return 1
}
for candidate in ld.lld rust-lld; do
    path="$(command -v "$candidate" 2>/dev/null || true)"
    [ -n "$path" ] || continue
    if [ "$candidate" = rust-lld ]; then
        try_lld "$path" -flavor gnu && break
    else
        try_lld "$path" && break
    fi
done
if [ "${#LLD[@]}" -eq 0 ]; then
    for path in "$HOME"/.rustup/toolchains/*/lib/rustlib/*/bin/rust-lld; do
        [ -e "$path" ] || continue
        try_lld "$path" -flavor gnu && break
    done
fi
[ "${#LLD[@]}" -gt 0 ] || die "no ELF linker: install ld.lld, or a rustup toolchain whose rust-lld runs"

OBJCOPY=""
try_objcopy() {
    if [ -x "$1" ] && { "$1" --version >/dev/null 2>&1; } 2>/dev/null; then
        OBJCOPY="$1"
        return 0
    fi
    echo "skipping objcopy that does not run: $1" >&2
    return 1
}
for candidate in llvm-objcopy rust-objcopy; do
    path="$(command -v "$candidate" 2>/dev/null || true)"
    [ -n "$path" ] || continue
    try_objcopy "$path" && break
done
if [ -z "$OBJCOPY" ]; then
    for path in "$HOME"/.rustup/toolchains/*/lib/rustlib/*/bin/llvm-objcopy \
        "$HOME"/.rustup/toolchains/*/lib/rustlib/*/bin/rust-objcopy; do
        [ -e "$path" ] || continue
        try_objcopy "$path" && break
    done
fi
[ -n "$OBJCOPY" ] || die "no llvm-objcopy or rust-objcopy that runs"

echo "clang:   $(command -v clang) ($(clang --version | head -n 1))"
echo "linker:  ${LLD[*]} ($("${LLD[@]}" --version | head -n 1))"
echo "objcopy: $OBJCOPY"

TMP_DIR="$(mktemp -d "${TMPDIR:-/tmp}/trust-exec-entry-elf.XXXXXX")"
trap 'rm -rf "$TMP_DIR"' EXIT

# build <name> <clang target> <e_machine> <assembly>
build() {
    local name="$1" target="$2" machine="$3" asm="$4"
    local src="$TMP_DIR/$name.s" obj="$TMP_DIR/$name.o"
    local linked="$TMP_DIR/$name.linked" exe="$TMP_DIR/$name"
    printf '%s' "$asm" >"$src"
    clang "--target=$target" -c -x assembler "$src" -o "$obj" || die "clang failed for $name"
    "${LLD[@]}" -static -no-pie --build-id=none -e exec_entry "$obj" -o "$linked" \
        || die "link failed for $name"
    "$OBJCOPY" --remove-section=.comment "$linked" "$exe" || die "objcopy failed for $name"
    python3 - "$exe" "$machine" "$TMP_DIR/$name-elf.hex" <<'PY' || die "$name is not the expected executable"
import binascii
import hashlib
import pathlib
import struct
import sys

exe = pathlib.Path(sys.argv[1])
machine = int(sys.argv[2], 0)
hex_out = pathlib.Path(sys.argv[3])
data = exe.read_bytes()
if data[:4] != b"\x7fELF" or data[4] != 2 or data[5] != 1:
    raise SystemExit(f"{exe.name}: not a little-endian ELF64 file")
e_type, e_machine, _, e_entry = struct.unpack_from("<HHIQ", data, 16)
if e_type != 2:
    raise SystemExit(f"{exe.name}: e_type {e_type}, expected 2 (ET_EXEC)")
if e_machine != machine:
    raise SystemExit(f"{exe.name}: e_machine {e_machine:#x}, expected {machine:#x}")

e_shoff, = struct.unpack_from("<Q", data, 40)
e_shentsize, e_shnum, e_shstrndx = struct.unpack_from("<HHH", data, 58)
# (sh_name, sh_type, sh_addr, sh_offset, sh_size, sh_link)
def section(index):
    sh_name, sh_type, _, sh_addr, sh_offset, sh_size, sh_link = struct.unpack_from(
        "<IIQQQQI", data, e_shoff + index * e_shentsize
    )
    return sh_name, sh_type, sh_addr, sh_offset, sh_size, sh_link
def c_string(offset):
    return data[offset : data.index(b"\0", offset)].decode("ascii")
shstr_offset = section(e_shstrndx)[3]
sections = {c_string(shstr_offset + section(i)[0]): section(i) for i in range(e_shnum)}
if ".text" not in sections or ".symtab" not in sections:
    raise SystemExit(f"{exe.name}: no .text or no .symtab")
_, _, text_addr, _, text_size, _ = sections[".text"]
_, _, _, sym_offset, sym_size, sym_link = sections[".symtab"]
str_offset = section(sym_link)[3]
functions = []
for at in range(sym_offset, sym_offset + sym_size, 24):
    st_name, st_info, _, _, st_value, st_size = struct.unpack_from("<IBBHQQ", data, at)
    if st_info & 0xF == 2:  # STT_FUNC
        functions.append((st_value, st_size, c_string(str_offset + st_name)))
functions.sort()
names = [name for _, _, name in functions]
expected = ["decoy_before_entry", "_start", "exec_entry", "decoy_after_entry"]
if names != expected:
    raise SystemExit(f"{exe.name}: function symbols {names} in address order, expected {expected}")
addresses = {name: (value, size) for value, size, name in functions}
layout = [
    (addresses["exec_entry"][0] == e_entry, "e_entry is not `exec_entry`"),
    (addresses["_start"][0] != e_entry, "`_start` is the entry"),
    (functions[0][0] == text_addr, "`decoy_before_entry` does not start .text"),
    (functions[-1][0] + functions[-1][1] == text_addr + text_size,
     "`decoy_after_entry` does not end .text"),
]
for holds, problem in layout:
    if not holds:
        raise SystemExit(f"{exe.name}: {problem}")
text = binascii.hexlify(data).decode("ascii")
hex_out.write_text(
    "".join(text[i : i + 64] + "\n" for i in range(0, len(text), 64)), encoding="ascii"
)
entry_size = addresses["exec_entry"][1]
entry_bytes = data[e_entry - text_addr + sections[".text"][3] :][:entry_size]
print(
    f"{exe.name}: {len(data)} bytes, e_entry {e_entry:#x}, sha256 {hashlib.sha256(data).hexdigest()}\n"
    f"  functions: {', '.join(f'{name} {value:#x}' for value, _, name in functions)}\n"
    f"  exec_entry bytes: {entry_bytes.hex()}"
)
PY
}

# The decoys and `_start` each set the return register to a different
# constant, so no two functions share bytes. `exec_entry` uses only
# instructions trust-lift lifts in strict mode; the conditional branch over the
# register clear splits it into three basic blocks.
build x86_64-exec-entry x86_64-unknown-linux-gnu 0x3e '
    .text
    .globl decoy_before_entry
    .type decoy_before_entry,@function
decoy_before_entry:
    xorl %eax, %eax
    retq
    .size decoy_before_entry, .-decoy_before_entry
    .globl _start
    .type _start,@function
_start:
    movl $1, %eax
    retq
    .size _start, .-_start
    .globl exec_entry
    .type exec_entry,@function
exec_entry:
    movl %edi, %eax
    addl %esi, %eax
    shll $3, %eax
    subl $7, %eax
    testl %eax, %eax
    je 1f
    xorl %edx, %edx
1:
    retq
    .size exec_entry, .-exec_entry
    .globl decoy_after_entry
    .type decoy_after_entry,@function
decoy_after_entry:
    movl $2, %eax
    retq
    .size decoy_after_entry, .-decoy_after_entry
    .section .note.GNU-stack,"",@progbits
'

build aarch64-exec-entry aarch64-unknown-linux-gnu 0xb7 '
    .text
    .globl decoy_before_entry
    .type decoy_before_entry,%function
decoy_before_entry:
    mov w0, #0
    ret
    .size decoy_before_entry, .-decoy_before_entry
    .globl _start
    .type _start,%function
_start:
    mov w0, #1
    ret
    .size _start, .-_start
    .globl exec_entry
    .type exec_entry,%function
exec_entry:
    add w0, w0, w1
    lsl w0, w0, #3
    sub w0, w0, #7
    cbz w0, 1f
    eor w2, w2, w2
1:
    ret
    .size exec_entry, .-exec_entry
    .globl decoy_after_entry
    .type decoy_after_entry,%function
decoy_after_entry:
    mov w0, #2
    ret
    .size decoy_after_entry, .-decoy_after_entry
    .section .note.GNU-stack,"",@progbits
'

status=0
for name in x86_64-exec-entry-elf.hex aarch64-exec-entry-elf.hex; do
    if [ "$MODE" = check ]; then
        if cmp -s "$TMP_DIR/$name" "$SCRIPT_DIR/$name"; then
            echo "reproduced: $name"
        else
            echo "DIFFERS: $name (rebuilt bytes are not the checked-in ones)" >&2
            status=1
        fi
    else
        cp "$TMP_DIR/$name" "$SCRIPT_DIR/$name"
        echo "wrote: $SCRIPT_DIR/$name"
    fi
done
if [ "$MODE" = write ]; then
    echo "re-pin the sha256 values above in crates/trust-integration-tests/tests/binary_to_trust_ir_e2e.rs"
fi
exit "$status"
