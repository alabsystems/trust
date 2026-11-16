"""Native Linux observations for the seed staircase; no seed or proof authority.

The glibc loader's --list resolves DT_NEEDED using its actual RPATH/RUNPATH,
cache and hwcaps rules (https://man7.org/linux/man-pages/man8/ld.so.8.html).
This binds those files, not future dlopen calls or kernel execution history.
"""

from __future__ import annotations

import hashlib
import os
from pathlib import Path
import re
import stat
import struct
import subprocess


class Refusal(ValueError):
    """An unsupported or unbound native input."""


SYSTEM_ROOTS = tuple(Path(p).resolve() for p in ("/lib", "/lib64", "/usr/lib", "/usr/lib64"))
ELF_MACHINES = {"aarch64-unknown-linux-gnu": 183, "x86_64-unknown-linux-gnu": 62}
LOADER_NAMES = {"aarch64-unknown-linux-gnu": "ld-linux-aarch64.so.1",
                "x86_64-unknown-linux-gnu": "ld-linux-x86-64.so.2"}
ENV = {"PATH": "/usr/bin:/bin", "LC_ALL": "C", "LANG": "C"}


def digest(path: Path) -> str:
    value = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1 << 20), b""):
            value.update(chunk)
    return value.hexdigest()


def is_system(path: Path) -> bool:
    return any(path.is_relative_to(root) for root in SYSTEM_ROOTS)


def native_elf(path: Path, host: str) -> None:
    if path.stat().st_mode & (stat.S_ISUID | stat.S_ISGID):
        raise Refusal(f"{path}: privileged ELF mode is not admitted")
    with path.open("rb") as stream:
        head = stream.read(20)
    if (len(head) != 20 or head[:4] != b"\x7fELF" or head[4:7] != b"\x02\x01\x01"
            or head[7] not in (0, 3) or struct.unpack_from("<H", head, 18)[0] != ELF_MACHINES.get(host)):
        raise Refusal(f"{path}: ELF platform differs from native {host}")


def command(argv: list[str], *, role='elf-metadata') -> str:
    if '__trust_source_loader__' in globals() and __trust_source_loader__.context is not None:
        live = __trust_source_loader__.context
        callsite = 'seed_linux.metadata' if role == 'elf-metadata' else 'seed_linux.loader'
        result = live.auxiliary(role,callsite,argv,Path('/'),ENV,maximum=4*2**20,seconds=60)
        if result.returncode:
            raise Refusal(f'{argv!r}: {result.stderr.strip()[:500]}')
        return result.stdout
    result = subprocess.run(argv, env=ENV, cwd="/", text=True, capture_output=True,
                            timeout=60, check=False)
    if result.returncode:
        raise Refusal(f"{' '.join(argv)}: {result.stderr.strip()[:500]}")
    return result.stdout



def needed_entries(path: Path) -> list[int]:
    """Read DT_NEEDED presence from ELF64 program headers, never loader text.

    ELF64 headers bound the program-header scan to fewer than 4 MiB. Refuse
    unsupported extended counts and dynamic tables above 1 MiB rather than
    walking arbitrary file contents. This reads no dependency name or code.
    Native platform/mode admission remains the caller's native_elf check.
    """
    def refused(detail):
        raise Refusal(f"{path}: invalid ELF dynamic inventory: {detail}")

    with path.open("rb") as stream:
        size = os.fstat(stream.fileno()).st_size
        head = stream.read(64)
        if len(head) != 64 or head[:7] != b"\x7fELF\x02\x01\x01":
            refused("unsupported or truncated ELF64 header")
        fields = struct.unpack("<16sHHIQQQIHHHHHH", head)
        phoff, ehsize, phsize, phcount = fields[5], fields[8], fields[9], fields[10]
        if fields[3] != 1 or ehsize != 64 or phcount == 0xffff:
            refused("unsupported ELF version, header size or extended program count")
        if phcount and (phsize != 56 or phoff < 64 or phoff + phcount * phsize > size):
            refused("program headers leave the file")
        dynamic = None
        loads = []
        for index in range(phcount):
            stream.seek(phoff + index * phsize)
            raw = stream.read(56)
            if len(raw) != 56:
                refused("truncated program header")
            kind, _flags, offset, address, _paddr, length, memory, _align = struct.unpack("<IIQQQQQQ", raw)
            if kind == 1:  # PT_LOAD determines which file bytes the loader maps.
                if length > memory or offset + length > size or address + memory > (1 << 64):
                    refused("invalid PT_LOAD extent")
                loads.append((offset, address, length, memory))
            if kind != 2:  # PT_DYNAMIC, the loader's table; section headers are not authoritative.
                continue
            if dynamic is not None:
                refused("multiple PT_DYNAMIC segments")
            if not length or length % 16 or length > (1 << 20) or length > memory or offset + length > size:
                refused("unsupported or truncated PT_DYNAMIC segment")
            if address + length > (1 << 64):
                refused("PT_DYNAMIC virtual extent overflows")
            dynamic = (offset, length, address)
        if dynamic is None:
            return []
        offset, length, address = dynamic
        covering = [load for load in loads
                    if load[1] < address + length and address < load[1] + load[3]]
        if len(covering) != 1:
            refused("PT_DYNAMIC needs one unambiguous PT_LOAD mapping")
        file_offset, start, file_length, _memory = covering[0]
        if not (start <= address and address + length <= start + file_length
                and offset == file_offset + address - start):
            refused("PT_DYNAMIC file offset differs from its file-backed PT_LOAD mapping")
        stream.seek(offset)
        needed = []
        for _ in range(dynamic[1] // 16):
            raw = stream.read(16)
            if len(raw) != 16:
                refused("truncated dynamic entry")
            tag, value = struct.unpack("<qQ", raw)
            if tag == 0:  # DT_NULL ends the loader-visible table.
                return needed
            if tag == 1:  # DT_NEEDED; its string-table offset is irrelevant to emptiness.
                needed.append(value)
        refused("missing DT_NULL terminator")


def metadata(path: Path, host: str) -> dict:
    native_elf(path, host)
    needed = needed_entries(path)
    output = command(["/usr/bin/readelf", "--wide", "--program-headers", "--dynamic", str(path)])
    if re.search(r"\((?:AUDIT|DEPAUDIT)\)", output):
        raise Refusal(f"{path}: embedded ELF audit modules are not admitted")
    for value in re.findall(r"\((?:RPATH|RUNPATH)\).*\[([^]]*)\]", output):
        if any(not entry or not entry.startswith(("/", "$ORIGIN/", "${ORIGIN}/"))
               for entry in value.split(":")):
            raise Refusal(f"{path}: cwd-dependent ELF search path is not admitted")
    interpreters = re.findall(r"Requesting program interpreter: ([^]]+)\]", output)
    if len(interpreters) > 1:
        raise Refusal(f"{path}: ambiguous ELF interpreter")
    return {"interpreter": interpreters[0] if interpreters else None,
            "dynamic": "Dynamic section at offset" in output, "needed": needed}


def loader_rows(output: str, binary: Path, *, needed: list[int] | None = None) -> list[tuple[str, Path]]:
    label = str(binary)
    if len(label) > 500:
        label = label[:240] + "..." + label[-240:]
    if "statically linked" in output:
        # GNU ld.so uses this for a dynamic ELF with no DT_NEEDED entries too.
        # It is not a provider row, and must be the whole single-line answer.
        if not re.fullmatch(r"[ \t]*statically linked[ \t]*(?:\n)?", output):
            raise Refusal(f"{label}: unresolved or unrecognized ELF loader row: mixed statically linked output")
        if not isinstance(needed, list) or needed:
            raise Refusal(f"{label}: statically linked loader row requires validated empty DT_NEEDED inventory")
        return []
    rows = []
    for line in output.splitlines():
        line = line.strip()
        if not line:
            continue
        if not rows and re.fullmatch(r"\(0x[0-9a-f]+\)", line):
            # Some glibc builds print the initial, explicitly named ELF as an
            # anonymous first mapping. Its path is our argv, not a dependency
            # guessed from a basename. A later anonymous row stays a refusal.
            rows.append((binary.name, binary))
            continue
        if re.fullmatch(r"linux-vdso\.so\.\d+\s+\(0x[0-9a-f]+\)", line):
            continue  # kernel-provided virtual image, not a file
        match = re.fullmatch(r"(.+?)\s+=>\s+(/.+?)\s+\(0x[0-9a-f]+\)", line)
        if match:
            rows.append((match[1], Path(match[2])))
            continue
        match = re.fullmatch(r"(/.+?)\s+\(0x[0-9a-f]+\)", line)
        if match:
            rows.append((Path(match[1]).name, Path(match[1])))
            continue
        raise Refusal(f"{label}: unresolved or unrecognized ELF loader row: {line[:500]}")
    return rows


def closure(root: Path, host: str, compat: list[Path]) -> dict:
    return _closure(root, host, compat, ("trustc", "cargo"))


def external_bootstrap_closure(root: Path, host: str) -> dict:
    """Observe a pinned external compiler; never admit it as a Trust seed."""
    result = _closure(root, host, [], ("rustc", "cargo"))
    return {**result, "admission": "external-bootstrap-root-only",
            "counts_as_trust_stage0_evidence": False}


def _closure(root: Path, host: str, compat: list[Path], required: tuple[str, ...]) -> dict:
    if compat:
        raise Refusal("Linux --compat-lib is unsupported; dependencies must be internal or OS files")
    root = root.resolve(strict=True)
    observations = {}
    for name in ("/etc/ld.so.cache", "/etc/ld.so.preload"):
        path = Path(name)
        observations[name] = digest(path) if path.exists() else None
        if name.endswith("preload") and path.exists() and path.read_text().strip():
            raise Refusal("nonempty /etc/ld.so.preload is not admitted")
    files = []
    for sub in ("bin", "lib", "libexec"):
        base = root / sub
        if not base.is_dir():
            continue
        for path in sorted(base.rglob("*")):
            if path.is_file() and not path.is_symlink():
                with path.open("rb") as stream:
                    if stream.read(4) == b"\x7fELF":
                        files.append(path)
    descriptions = {path: metadata(path, host) for path in files}
    if any(root / "bin" / name not in descriptions for name in required):
        raise Refusal("Linux stage0 requires native ELF " + " and ".join(required))
    interpreters = {row["interpreter"] for row in descriptions.values() if row["interpreter"]}
    if len(interpreters) != 1:
        raise Refusal("Linux stage0 needs one actual native glibc interpreter")
    named_loader = Path(interpreters.pop())
    loader = named_loader.resolve(strict=True)
    if not named_loader.is_absolute() or not is_system(loader) or named_loader.name != LOADER_NAMES.get(host):
        raise Refusal(f"unadmitted Linux ELF interpreter: {named_loader}")
    native_elf(loader, host)
    observations[str(loader)] = digest(loader)
    links = {str(named_loader): str(loader)}
    rows = []
    covered = set()
    for binary, description in descriptions.items():
        observations[str(binary)] = digest(binary)
        if not description["dynamic"] or binary in covered:
            continue
        for load, named in loader_rows(command([str(loader), "--list", str(binary)], role="elf-loader"), binary,
                                       needed=description["needed"]):
            provider = named.resolve(strict=True)
            native_elf(provider, host)
            # glibc optionally prints the queried ELF's own initial mapping.
            # Its bytes are already bound above; it is not a DT_NEEDED edge.
            # Retaining that optional row makes identical closures differ and
            # changes which subsequent ELF objects the covered set skips.
            if provider == binary:
                continue
            kind = "internal" if provider.is_relative_to(root) else "system" if is_system(provider) else "unresolved"
            observations[str(provider)] = digest(provider)
            links[str(named)] = str(provider)
            covered.add(provider)
            rows.append({"binary": str(binary.relative_to(root)), "load": load, "kind": kind,
                         "provider": str(provider), "provider_sha256": observations[str(provider)]})
    return {"checked": True, "format": "elf", "host": host,
            "scope": "native-ELF-DT_NEEDED-loader-list-v1", "loader": str(loader),
            "observations": observations, "links": links,
            "system": [r for r in rows if r["kind"] == "system"],
            "non_system": [r for r in rows if r["kind"] != "system"],
            "unresolved": [r for r in rows if r["kind"] == "unresolved"], "compat": []}


def unchanged(receipt: dict) -> None:
    if receipt.get("checked") is not True or receipt.get("format") != "elf" or not receipt.get("observations"):
        raise Refusal("Linux ELF runtime closure was not checked")
    for name, expected in receipt["observations"].items():
        path = Path(name)
        actual = digest(path) if path.exists() else None
        if actual != expected:
            raise Refusal(f"Linux runtime input changed: {path}")
    for name, expected in receipt.get("links", {}).items():
        if str(Path(name).resolve(strict=True)) != expected:
            raise Refusal(f"Linux runtime provider path changed: {name}")


def stat_identity(pid: int) -> tuple[int, str]:
    text = Path(f"/proc/{pid}/stat").read_text()
    fields = text[text.rfind(")") + 2:].split()
    return int(fields[1]), fields[19]  # /proc/PID/stat: ppid (4), starttime (22)


def tick_listing() -> str:
    rows = []
    for entry in Path("/proc").iterdir():
        if not entry.name.isdigit():
            continue
        pid = int(entry.name)
        try:
            before = stat_identity(pid)
            exe = os.readlink(entry / "exe")
            if before == stat_identity(pid):
                rows.append(f"{pid} {before[0]} ticks:{before[1]} {exe}\n")
        except (FileNotFoundError, ProcessLookupError, PermissionError):
            continue  # a process gone or inaccessible before this observation
    return "".join(rows)


def environment_listing(pids: list[int]) -> str:
    rows = []
    for pid in pids:
        try:
            before = stat_identity(pid)
            raw = Path(f"/proc/{pid}/environ").read_bytes()
            if before == stat_identity(pid):
                rows.append(f"{pid} " + raw.replace(b"\0", b" ").decode("utf-8", "replace") + "\n")
        except (FileNotFoundError, ProcessLookupError):
            continue
    return "".join(rows)


def mapped_libraries(pid: int) -> list[str]:
    before = stat_identity(pid)
    paths = set()
    for line in Path(f"/proc/{pid}/maps").read_text().splitlines():
        columns = line.split(None, 5)
        if len(columns) == 6 and columns[5].startswith("/") and ".so" in Path(columns[5]).name:
            path = Path(columns[5])
            if not is_system(path.resolve()):
                paths.add(str(path))
    if before != stat_identity(pid):
        raise Refusal("PID changed during mapped-library observation")
    return sorted(paths)
