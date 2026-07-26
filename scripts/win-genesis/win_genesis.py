#!/usr/bin/env python3
"""Windows genesis stage0 adapter for Trust (no #!/bin/sh, no symlinks).

Lays out build/<host>/stage0 with compiled .exe wrappers around the installed
stock rustc toolchain (whatever `rustc` is on PATH — use the pinned genesis
nightly recorded in docs/GENESIS_TRUST_ROOT.md, which must be within one minor of
src/version so bootstrap's check_stage0_version accepts it), a directory JUNCTION
for lib/, and the stage0 stamps (stamped with `compiler_date` from src/stage0).
Bin names match the canonical stage0 contract; only `rustc` and `cargo` are
retained as stock compatibility aliases. Run with the Windows `py -3`. This is
the Windows analogue of scripts/create_local_genesis_stage0.py (POSIX-only).
"""
import json, os, shutil, subprocess, sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]  # scripts/win-genesis -> repo root
HOST = "x86_64-pc-windows-msvc"
WRAPPER_SRC = Path(__file__).resolve().parent / "genesis_wrapper.rs"

def out(*a): print(*a, flush=True)

rustc = shutil.which("rustc")
if not rustc:
    sys.exit("rustc not on PATH")
sysroot = Path(subprocess.run([rustc, "--print", "sysroot"], text=True, check=True,
                              capture_output=True).stdout.strip())
sbin, slibexec = sysroot / "bin", sysroot / "libexec"

date = None
for line in (ROOT / "src" / "stage0").read_text(encoding="utf-8").splitlines():
    if line.startswith("compiler_date="):
        date = line.split("=", 1)[1].strip()
if not date:
    sys.exit("src/stage0 has no compiler_date")

STAGE0 = ROOT / "build" / HOST / "stage0"
bind, libx = STAGE0 / "bin", STAGE0 / "libexec"

# Safe teardown: a previous run leaves lib/ as a JUNCTION. shutil.rmtree would
# follow it and delete the REAL sysroot lib. Remove the junction link first.
if STAGE0.exists():
    lib = STAGE0 / "lib"
    if lib.exists() or lib.is_symlink():
        subprocess.run(["cmd", "/c", "rmdir", str(lib)], capture_output=True)
    shutil.rmtree(STAGE0, ignore_errors=True)
bind.mkdir(parents=True); libx.mkdir(parents=True)

wrapper = STAGE0 / "_genesis_wrapper.exe"
out("compiling wrapper ...")
subprocess.run([rustc, "-O", str(WRAPPER_SRC), "-o", str(wrapper)], check=True)

# trust_name -> (stock file, source-name, Trust public name)
# This surface is checked against both bootstrap implementations by
# scripts/check_toolchain_coherence.py. Do not grow compatibility aliases here.
WRAP = {
    "trustc": ("rustc.exe", "rustc", "trustc"),
    "rustc": ("rustc.exe", "rustc", "rustc"),
    "trustdoc": ("rustdoc.exe", "rustdoc", "trustdoc"),
    "targo": ("cargo.exe", "cargo", "targo"),
    "cargo": ("cargo.exe", "cargo", "cargo"),
    "trustfmt": ("rustfmt.exe", "rustfmt", "trustfmt"),
    "targo-fmt": ("cargo-fmt.exe", "cargo-fmt", "targo-fmt"),
    "tippy": ("cargo-clippy.exe", "clippy", "tippy"),
    "targo-tippy": ("cargo-clippy.exe", "clippy", "targo-tippy"),
    "tippy-driver": ("clippy-driver.exe", "clippy", "tippy-driver"),
    "trust-analyzer": ("rust-analyzer.exe", "rust-analyzer", "trust-analyzer"),
}
# Stock cargo-clippy drops argv[1] as its external-subcommand marker. Direct
# `tippy` supplies that marker. `targo-tippy` strips Targo's `tippy` marker and
# replaces it with the inherited backend's private `clippy` marker so direct
# and external-subcommand invocation have identical forwarding semantics.
ARG_PREFIX = {
    "tippy": "clippy",
    "targo-tippy": "clippy",
}
ARG_MARKER = {
    "targo-tippy": "tippy",
}
ARG_RENAME = {
    "tippy-driver": ("--trustc", "--rustc"),
}
VERSION_NAME = {
    "tippy": "tippy",
    "targo-tippy": "tippy",
    "tippy-driver": "tippy",
}
VERSION_PREFIX = {
    "tippy": "clippy",
    "targo-tippy": "clippy",
}
PRESERVE_COMPILER_INFO = {"tippy-driver"}
STUB = {
    "targo-trust": "targo-trust is not part of the inherited Rust genesis toolchain",
}
LIBWRAP = {
    "trust-analyzer-proc-macro-srv": ("rust-analyzer-proc-macro-srv.exe", "rust-analyzer-proc-macro-srv", "trust-analyzer-proc-macro-srv"),
}

def emit_wrap(
    d,
    name,
    pf,
    src,
    tr,
    srcdir,
    prefix=None,
    marker=None,
    version=None,
    version_prefix=None,
    preserve_compiler_info=False,
    arg_rename=None,
):
    real = srcdir / pf
    if not real.exists():
        sys.exit(f"missing stock tool: {real}")
    shutil.copy2(wrapper, d / f"{name}.exe")
    config = f"mode=wrap\nreal={real}\nsource={src}\ntrust={tr}\n"
    if prefix is not None:
        config += f"prefix={prefix}\n"
    if marker is not None:
        config += f"marker={marker}\n"
    if version is not None:
        config += f"version={version}\n"
    if version_prefix is not None:
        config += f"version_prefix={version_prefix}\n"
    if preserve_compiler_info:
        config += "compiler_info=1\n"
    if arg_rename is not None:
        config += f"arg_from={arg_rename[0]}\narg_to={arg_rename[1]}\n"
    (d / f"{name}.wrap").write_text(config, encoding="utf-8")

def emit_stub(d, name, msg):
    shutil.copy2(wrapper, d / f"{name}.exe")
    (d / f"{name}.wrap").write_text(f"mode=stub\nname={name}\nmsg={msg}\n", encoding="utf-8")

for name, (pf, src, tr) in WRAP.items():
    emit_wrap(
        bind,
        name,
        pf,
        src,
        tr,
        sbin,
        ARG_PREFIX.get(name),
        ARG_MARKER.get(name),
        VERSION_NAME.get(name),
        VERSION_PREFIX.get(name),
        name in PRESERVE_COMPILER_INFO,
        ARG_RENAME.get(name),
    )
for name, msg in STUB.items():
    emit_stub(bind, name, msg)
for name, (pf, src, tr) in LIBWRAP.items():
    emit_wrap(libx, name, pf, src, tr, slibexec)

# lib as a junction to the stock sysroot lib (no admin needed, no copy)
r = subprocess.run(["cmd", "/c", "mklink", "/J", str(STAGE0 / "lib"), str(sysroot / "lib")],
                   capture_output=True, text=True)
if r.returncode != 0:
    sys.exit(f"mklink /J failed: {r.stdout}{r.stderr}")

(STAGE0 / ".trustc-stamp").write_text(date, encoding="utf-8")
(STAGE0 / ".rustc-stamp").write_text(date, encoding="utf-8")
(STAGE0 / "trust-local-genesis-stage0.json").write_text(json.dumps(
    {"schema": "trust.local-genesis-stage0-adapter.v1", "admission": "local-genesis-only",
     "host": HOST, "stamp": date, "source_sysroot": str(sysroot)}, indent=2) + "\n", encoding="utf-8")

out(f"genesis stage0 -> {STAGE0}")
out("bin:", sorted(p.name for p in bind.glob("*.exe")))
out("libexec:", sorted(p.name for p in libx.glob("*.exe")))
out("lib junction ->", os.readlink(STAGE0 / "lib") if (STAGE0 / "lib").is_symlink() else "(junction) " + str(sysroot / "lib"))
