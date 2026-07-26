# Patches carried against third-party sources

This directory holds the local changes Trust needs in software it does not
vendor in this snapshot. Today there is exactly one, against LLVM.

## Why LLVM is not in this tree

Trust's internal development tree vendors a full `llvm-project` checkout at
`src/llvm-project` and builds it in-tree. That tree is ~1.9 GB of upstream
source, and it is not republished here. The public snapshot therefore builds
against an **external LLVM** that you supply through `--llvm-config`, and the
one Trust-specific change to LLVM is shipped as the patch beside this file
instead of as a modified copy of upstream.

Nothing else in Trust depends on `src/llvm-project` being present: the
verification pipeline, the `crates/trust-*` workspace, `targo-trust`, the
conformance suites, and the compiler crates are all here in full.

## The patch

`0001-llvm-scalarevolution-guard-cross-phi-addrec-recursion.patch`
— ~21 lines against `llvm/include/llvm/Analysis/ScalarEvolution.h` and
`llvm/lib/Analysis/ScalarEvolution.cpp`. It guards `createAddRecFromPHI`
against cross-PHI recursion cycles. Without it, a chain of header PHIs whose
operands reach back to the first PHI drives unbounded
`createSCEV` → `createAddRecFromPHI` recursion, and the compiler dies with
SIGBUS/stack overflow while building itself. The patch's own header explains
the root cause and why the fix is sound.

**This is not optional for a self-hosting build.** Upstream LLVM releases and
distribution packages (Homebrew's `llvm`, distro `libllvm-dev`, and so on)
carry the unguarded code, so an LLVM that has *not* been patched can crash
while compiling the Trust compiler. If you only want to compile ordinary
crates with an already-built `trustc`, an unpatched LLVM may be fine; if you
are building Trust from source, patch it.

## Building an LLVM for Trust

Trust needs LLVM **21 or newer** (`check_llvm_version` in
`src/bootstrap/src/core/build_steps/llvm.rs` rejects anything older); the
version Trust develops against is 22.1.x, and the patch applies cleanly to
that line.

```bash
git clone --depth 1 --branch llvmorg-22.1.2 \
    https://github.com/llvm/llvm-project.git
cd llvm-project
git apply /path/to/trust/patches/0001-llvm-scalarevolution-guard-cross-phi-addrec-recursion.patch

cmake -S llvm -B build -G Ninja \
    -DCMAKE_BUILD_TYPE=Release \
    -DLLVM_ENABLE_PROJECTS="lld" \
    -DLLVM_ENABLE_ASSERTIONS=OFF \
    -DLLVM_TARGETS_TO_BUILD="AArch64;X86" \
    -DLLVM_INCLUDE_BENCHMARKS=OFF \
    -DLLVM_INCLUDE_TESTS=OFF
cmake --build build
# -> build/bin/llvm-config
```

Set `LLVM_TARGETS_TO_BUILD` to the targets you actually need; the full upstream
default list is much slower to build. `lld` is only required if you enable
`rust.lld`.

## Pointing Trust at it

Either through the bootstrap recreator:

```bash
python3 scripts/recreate_bootstrap.py --llvm-config /path/to/llvm-project/build/bin/llvm-config
```

which writes the `llvm-config` line into the generated `bootstrap.toml` for
you, or by hand in `bootstrap.toml` before running `x.py`:

```toml
[llvm]
download-ci-llvm = false

[target.aarch64-apple-darwin]   # your host triple
llvm-config = "/path/to/llvm-project/build/bin/llvm-config"
```

With an external `llvm-config` configured, bootstrap never looks for
`src/llvm-project`, and `cmake`/`ninja` are not needed for the Trust build
itself. Building against an unpatched or too-old LLVM is the first thing to
suspect if a from-source build crashes inside `ScalarEvolution`.

## Keeping the patch honest

The patch is generated from Trust commit `1d1d11bed9`, the commit that
introduced the fix in the internal vendored tree. If that vendored change is
ever amended, regenerate this file rather than editing it by hand, so the
public instructions and the tree Trust actually builds cannot drift apart.
