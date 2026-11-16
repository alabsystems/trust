"""Trust: cache identity shared by stage0 extraction and its evidence readers.

This discriminator grants no seed admission: the download owners still validate
archive checksums, and the evidence owners still check compiler/host identity.
Rust's matching implementation is in bootstrap's core/download.rs.
"""

import hashlib
import os
import stat


DOMAIN = "trust-stage0-extraction-v3"
METADATA_KEYS = (
    "compiler_channel_manifest_hash", "compiler_date", "compiler_dist_channel",
    "compiler_git_commit_hash", "compiler_version",
    "rustfmt_channel_manifest_hash", "rustfmt_date", "rustfmt_dist_channel",
    "rustfmt_git_commit_hash", "rustfmt_version",
)


STAGE0_EXTRA_COMPONENTS = (
    ("trustfmt", "trustfmt"),
    ("tippy", "tippy"),
    ("trust-analyzer", "trust-analyzer"),
)
# Existing checksum-pinned seeds predate the final Tippy component spelling.
# Treat those names strictly as an admitted input format: after extraction the
# legacy binaries are translated to the canonical surface and removed. New
# producers must continue to emit only `tippy` / `tippy-preview`.
STAGE0_LEGACY_EXTRA_COMPONENTS = {
    "tippy": ("trust-clippy", "trust-clippy-preview"),
}
# The admitted 2026-06-23 seed predates the tcargo -> targo archive rename.
# These are checksum-key aliases only, never network fallbacks or produced
# names. Extracted public leaves are normalized before surface admission.
STAGE0_LEGACY_TARGO_COMPONENTS = {
    "targo": "tcargo",
    "targo-trust": "tcargo-trust",
}

def select_stage0_extra_component(
    stage0_data, date, toolchain_suffix, component, pattern
):
    """Select a canonical stage0 component, or an explicitly admitted legacy pin."""
    filename = "{}-{}".format(component, toolchain_suffix)
    download_path = "dist/{}/{}".format(date, filename)
    if download_path in stage0_data:
        return filename, pattern, False

    legacy = STAGE0_LEGACY_EXTRA_COMPONENTS.get(component)
    if legacy is not None:
        legacy_component, legacy_pattern = legacy
        legacy_filename = "{}-{}".format(legacy_component, toolchain_suffix)
        legacy_download_path = "dist/{}/{}".format(date, legacy_filename)
        if legacy_download_path in stage0_data:
            return legacy_filename, legacy_pattern, True

    # Preserve the canonical missing-checksum diagnostic when neither format
    # is pinned instead of silently broadening the fallback surface.
    return filename, pattern, False


def select_stage0_targo_component(stage0_data, date, toolchain_suffix, component):
    """Prefer a canonical Targo archive; admit only its checksum-pinned legacy name."""
    if component not in STAGE0_LEGACY_TARGO_COMPONENTS:
        raise ValueError("not a Targo stage0 component: {}".format(component))

    filename = "{}-{}".format(component, toolchain_suffix)
    download_path = "dist/{}/{}".format(date, filename)
    if download_path in stage0_data:
        return filename, component, False

    legacy_component = STAGE0_LEGACY_TARGO_COMPONENTS[component]
    legacy_filename = "{}-{}".format(legacy_component, toolchain_suffix)
    legacy_download_path = "dist/{}/{}".format(date, legacy_filename)
    if legacy_download_path in stage0_data:
        return legacy_filename, legacy_component, True

    # Preserve the canonical checksum-miss diagnostic when neither spelling is
    # pinned. Ambient or merely present legacy archives are never considered.
    return filename, component, False


def component_archives(stage0_data, date, version, host, suffix):
    """The complete SAME Bootstrap refresh selection, returning only DATA.

    Checksum admission, extraction, legacy translation and final surface checks
    remain with their existing owners. Missing rows still select the canonical
    spelling so the normal download path keeps its missing-checksum refusal.
    """
    toolchain_suffix = "{}-{}{}".format(version, host, suffix)
    tarballs = [("trust-std-{}".format(toolchain_suffix), "trust-std-{}".format(host)),
                ("trustc-{}".format(toolchain_suffix), "trustc")]
    legacy_targo = []
    legacy_tippy = False
    for component in ("targo", "targo-trust"):
        filename, pattern, legacy = select_stage0_targo_component(
            stage0_data, date, toolchain_suffix, component)
        tarballs.append((filename, pattern))
        if legacy:
            legacy_targo.append(component)
    for component, pattern in STAGE0_EXTRA_COMPONENTS:
        filename, selected, legacy = select_stage0_extra_component(
            stage0_data, date, toolchain_suffix, component, pattern)
        tarballs.append((filename, selected))
        if component == "tippy" and legacy:
            legacy_tippy = True
    return tarballs, legacy_targo, legacy_tippy


def component_projection(name, package, component):
    """Bootstrap's exact package/component-to-sysroot path rule.

    A selected component is a complete path segment, never a text prefix.
    The caller still authenticates the archive and owns the destination; this
    rule creates neither a seed nor a source or output capability.
    """
    def parts(value):
        if not isinstance(value, str) or not value or "\\" in value or "\0" in value:
            raise ValueError("noncanonical stage0 component path")
        result = value.rstrip("/").split("/")
        if any(not part or part in (".", "..") for part in result):
            raise ValueError("noncanonical stage0 component path")
        return result

    root = parts(package)
    if len(root) != 1:
        raise ValueError("stage0 package root is not one component")
    selected = [] if component is None else parts(component)
    path = parts(name)
    if path[:1] != root:
        raise ValueError("stage0 member is outside its exact package root")
    path = path[1:]
    if path[:len(selected)] != selected:
        return None
    relative = "/".join(path[len(selected):])
    # rust-installer's per-component instruction table is not installed data.
    # Distinct components have different tables and must not overwrite one
    # another at the sysroot root. Nested files with this name remain files.
    return None if selected and relative == "manifest.in" else relative


def extraction_stamp(stage0):
    """Hash UTF-8 domain + sorted key=value lines, including a final newline.

    The exact ten metadata fields above always occur; absent fields equal empty
    fields, as in Rust's parsed Stage0. Include every dist/ checksum row, so a
    repack of the same compiler commit changes the key. Mirrors/comments and
    unknown metadata do not change the extracted bytes and are excluded.
    """
    rows = {key: stage0.get(key, "") for key in METADATA_KEYS}
    rows.update((key, value) for key, value in stage0.items() if key.startswith("dist/"))
    digest = hashlib.sha256((DOMAIN + "\n").encode("utf-8"))
    for key, value in sorted(rows.items()):
        if not isinstance(value, str) or any(c in key + value for c in "\r\n\0"):
            raise ValueError("stage0 extraction identity requires single-line text records")
        digest.update((key + "=" + value + "\n").encode("utf-8"))
    return DOMAIN + ":" + digest.hexdigest()


def paired_linker(root, host, materialize=False):
    """Bind a Darwin native role in fresh authenticated staging, never PATH.

    Evidence readers use materialize=False. Retained directory descriptors
    confine all writes even if a lexical directory role changes during I/O.
    Legacy seeds without LLD gain no capability. No existing seed is repaired.
    """
    import contextlib
    if not host.endswith("-apple-darwin"):
        return None
    if not host or any(not (c.isascii() and (c.isalnum() or c in "_.-")) for c in host):
        raise ValueError("noncanonical paired linker host")
    root = os.fspath(root)
    source_relative = "lib/rustlib/{}/bin/rust-lld".format(host)
    destination_relative = "bin/rust-lld"
    source = os.path.join(root, source_relative)
    destination = os.path.join(root, destination_relative)
    if not os.path.lexists(source):
        if os.path.lexists(destination):
            raise ValueError("paired linker root role lacks its archived host image")
        return None

    def key(info):
        return (info.st_dev, info.st_ino, info.st_mode, info.st_uid, info.st_gid,
                info.st_size, info.st_mtime_ns, info.st_ctime_ns)

    flags = (getattr(os, "O_NOFOLLOW", 0) | getattr(os, "O_NONBLOCK", 0)
             | getattr(os, "O_CLOEXEC", 0))
    directory_flags = os.O_RDONLY | os.O_DIRECTORY | flags
    with contextlib.ExitStack() as custody:
        directories = {}

        def retain_directory(path, fd):
            custody.callback(os.close, fd)
            info = os.fstat(fd)
            named = os.lstat(path)
            if not stat.S_ISDIR(info.st_mode) or key(info)[:5] != key(named)[:5]:
                raise ValueError("paired linker directory is not confined and regular")
            directories[path] = (fd, key(info)[:5])
            return fd

        root_fd = retain_directory(root, os.open(root, directory_flags))

        def parent(relative):
            fd, path = root_fd, root
            for component in relative.split("/")[:-1]:
                path = os.path.join(path, component)
                if path in directories:
                    fd = directories[path][0]
                else:
                    fd = retain_directory(path, os.open(component, directory_flags, dir_fd=fd))
            return fd

        source_parent = parent(source_relative)
        selected_parent = parent(destination_relative)

        def open_image(relative, directory_fd):
            name = relative.rsplit("/", 1)[1]
            named = os.stat(name, dir_fd=directory_fd, follow_symlinks=False)
            if not stat.S_ISREG(named.st_mode):
                raise ValueError("paired linker path is not confined and regular: " + relative)
            if not named.st_mode & 0o111:
                raise ValueError("paired linker is not executable: " + relative)
            image = custody.enter_context(os.fdopen(
                os.open(name, os.O_RDONLY | flags, dir_fd=directory_fd), "rb"))
            if key(os.fstat(image.fileno())) != key(named):
                raise ValueError("paired linker image changed before opening")
            return image, named

        original, source_before = open_image(source_relative, source_parent)
        try:
            os.stat("rust-lld", dir_fd=selected_parent, follow_symlinks=False)
            exists = True
        except FileNotFoundError:
            exists = False
        if materialize and not exists:
            fd = os.open("rust-lld", os.O_WRONLY | os.O_CREAT | os.O_EXCL | flags,
                         0o600, dir_fd=selected_parent)
            with os.fdopen(fd, "wb") as output:
                for chunk in iter(lambda: original.read(1024 * 1024), b""):
                    output.write(chunk)
                os.fchmod(output.fileno(), stat.S_IMODE(source_before.st_mode))
            original.seek(0)
        selected, selected_before = open_image(destination_relative, selected_parent)
        if ((source_before.st_dev, source_before.st_ino)
                == (selected_before.st_dev, selected_before.st_ino)):
            raise ValueError("paired linker roles must have distinct executable inodes")
        if stat.S_IMODE(source_before.st_mode) != stat.S_IMODE(selected_before.st_mode):
            raise ValueError("paired linker role modes differ")

        def digest(image, before, directory_fd):
            value = hashlib.sha256()
            for chunk in iter(lambda: image.read(1024 * 1024), b""):
                value.update(chunk)
            if (key(os.fstat(image.fileno())) != key(before)
                    or key(os.stat("rust-lld", dir_fd=directory_fd,
                                   follow_symlinks=False)) != key(before)):
                raise ValueError("paired linker role changed during binding")
            return value.hexdigest()
        original_digest = digest(original, source_before, source_parent)
        if original_digest != digest(selected, selected_before, selected_parent):
            raise ValueError("paired linker root role differs from its archived host image")
        for path, (fd, expected) in directories.items():
            if key(os.fstat(fd))[:5] != expected or key(os.lstat(path))[:5] != expected:
                raise ValueError("paired linker directory role changed during binding")
    return {"schema": "trust.seed-paired-linker.v1", "source": source_relative,
            "destination": destination_relative, "sha256": original_digest,
            "mode": stat.S_IMODE(source_before.st_mode), "distinct_inodes": True}
