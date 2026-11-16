"""Optional working DATA cache for a fresh, independently acquired Git checkout.

The caller authenticates/fetches the target and owns Git execution/custody. This
module never reads donor Git metadata. It only prepares byte-identical regular
files with Darwin's native CoW clone; Git still materializes every other entry
and performs the caller's original HEAD transition. A cache miss is ordinary
checkout, never missing source. No physical allocation bound is implied.
"""
from __future__ import annotations

import contextlib
import ctypes
import errno
import gzip
import hashlib
import json
import os
from pathlib import Path
import stat
import subprocess
import sys
import tempfile


ATTRIBUTES = ("filter", "ident", "text", "eol", "working-tree-encoding")


class CustodyRefused(RuntimeError):
    retain_source_working_cache = True


def _identity(info):
    return (info.st_dev, info.st_ino, info.st_mode, info.st_nlink, info.st_uid,
            info.st_gid, info.st_size, info.st_mtime_ns, info.st_ctime_ns,
            getattr(info, "st_flags", 0))


def _binding(info):
    return (info.st_dev, info.st_ino, info.st_mode)


def _parts(raw):
    parts = raw.split(b"/")
    if any(not p or p in (b".", b"..") or p.lower() == b".git" for p in parts):
        raise RuntimeError("cache target inventory contains an unsafe path")
    return parts


@contextlib.contextmanager
def _directory(path):
    """No symlink in the absolute path, including parents; hold each binding."""
    path = Path(os.path.abspath(path))
    descriptors = [os.open(path.anchor, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW)]
    bindings = []
    try:
        for part in path.parts[1:]:
            parent = descriptors[-1]
            child = os.open(part, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW, dir_fd=parent)
            descriptors.append(child)
            bindings.append((parent, os.fsencode(part), child))
        def check():
            for parent, name, child in bindings:
                if _binding(os.stat(name, dir_fd=parent, follow_symlinks=False)) != _binding(os.fstat(child)):
                    raise CustodyRefused("working cache directory binding changed")
        check.ancestors = tuple(_binding(os.fstat(fd))[:2] for fd in descriptors)
        check()
        yield descriptors[-1], check
        check()
    finally:
        for fd in reversed(descriptors):
            os.close(fd)


@contextlib.contextmanager
def _parent(root, raw, *, create=False):
    descriptors = []
    bindings = []
    current = root
    try:
        for part in _parts(raw)[:-1]:
            if create:
                try:
                    os.mkdir(part, 0o777, dir_fd=current)
                except FileExistsError:
                    pass
            child = os.open(part, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW, dir_fd=current)
            descriptors.append(child)
            bindings.append((current, part, child))
            current = child
        def check():
            for parent, name, child in bindings:
                if _binding(os.stat(name, dir_fd=parent, follow_symlinks=False)) != _binding(os.fstat(child)):
                    raise CustodyRefused("working cache path ancestor changed")
        check()
        yield current, _parts(raw)[-1], check
        check()
    finally:
        for fd in reversed(descriptors):
            os.close(fd)


def _native():
    if sys.platform != "darwin":
        return None
    lib = ctypes.CDLL(None, use_errno=True)
    try:
        clone = lib.fclonefileat
        rename = lib.renameatx_np
        xattrs = lib.flistxattr
        get = lib.fgetxattr
        remove = lib.fremovexattr
        get_acl, acl_text, acl_free = lib.acl_get_fd_np, lib.acl_to_text, lib.acl_free
        get_attributes, set_attributes = lib.fgetattrlist, lib.fsetattrlist
    except AttributeError:
        return None
    clone.argtypes = [ctypes.c_int, ctypes.c_int, ctypes.c_char_p, ctypes.c_uint]
    clone.restype = ctypes.c_int
    rename.argtypes = [ctypes.c_int, ctypes.c_char_p, ctypes.c_int, ctypes.c_char_p, ctypes.c_uint]
    rename.restype = ctypes.c_int
    xattrs.argtypes = [ctypes.c_int, ctypes.c_void_p, ctypes.c_size_t, ctypes.c_int]
    xattrs.restype = ctypes.c_ssize_t
    get.argtypes = [ctypes.c_int, ctypes.c_char_p, ctypes.c_void_p, ctypes.c_size_t, ctypes.c_uint, ctypes.c_int]
    get.restype = ctypes.c_ssize_t
    remove.argtypes = [ctypes.c_int, ctypes.c_char_p, ctypes.c_int]
    remove.restype = ctypes.c_int
    get_acl.argtypes = [ctypes.c_int, ctypes.c_int]
    get_acl.restype = ctypes.c_void_p
    acl_text.argtypes = [ctypes.c_void_p, ctypes.POINTER(ctypes.c_ssize_t)]
    acl_text.restype = ctypes.c_void_p
    acl_free.argtypes = [ctypes.c_void_p]
    acl_free.restype = ctypes.c_int
    class AttributeList(ctypes.Structure):
        _fields_ = [("bitmapcount", ctypes.c_ushort), ("reserved", ctypes.c_ushort),
                    ("common", ctypes.c_uint32), ("volume", ctypes.c_uint32),
                    ("directory", ctypes.c_uint32), ("file", ctypes.c_uint32),
                    ("fork", ctypes.c_uint32)]
    class TimeSpec(ctypes.Structure):
        _fields_ = [("seconds", ctypes.c_long), ("nanoseconds", ctypes.c_long)]
    for operation in (get_attributes, set_attributes):
        operation.argtypes = [ctypes.c_int, ctypes.c_void_p, ctypes.c_void_p,
                              ctypes.c_size_t, ctypes.c_ulong]
        operation.restype = ctypes.c_int
    def birthtime(fd, value=None):
        attributes = AttributeList(5, 0, 0x00000200, 0, 0, 0, 0)  # ATTR_CMN_CRTIME
        if value is not None:
            stamp = TimeSpec(value // 10**9, value % 10**9)
            if set_attributes(fd, ctypes.byref(attributes), ctypes.byref(stamp), ctypes.sizeof(stamp), 0):
                raise OSError("cannot normalize working cache creation time")
        size = ctypes.sizeof(ctypes.c_uint32) + ctypes.sizeof(TimeSpec)
        buffer = ctypes.create_string_buffer(size)
        if get_attributes(fd, ctypes.byref(attributes), buffer, size, 0):
            raise OSError("cannot inspect working cache creation time")
        if ctypes.c_uint32.from_buffer_copy(buffer.raw[:4]).value != size:
            raise OSError("unexpected working cache creation-time layout")
        stamp = TimeSpec.from_buffer_copy(buffer.raw[4:])
        return stamp.seconds * 10**9 + stamp.nanoseconds
    def native_clone(source, destination, name):
        # NOOWNERCOPY; ACL copying is opt-in and is deliberately not requested.
        if clone(source, destination, name, 0x0002):
            error = ctypes.get_errno()
            raise OSError(error, os.strerror(error))
    def exclusive_move(source, name, destination, leaf):
        if rename(source, name, destination, leaf, 0x0004):  # RENAME_EXCL
            error = ctypes.get_errno()
            raise OSError(error, os.strerror(error))
    def metadata(fd, *, clear=False):
        # SHOWCOMPRESSION: include com.apple.decmpfs. Bind donor metadata while
        # removing ALL copied attributes from the private clone before install.
        size = xattrs(fd, None, 0, 0x0020)
        if size < 0 or size > 1024 * 1024:
            raise OSError("unavailable or oversized working cache attributes")
        names = ctypes.create_string_buffer(size)
        if xattrs(fd, names, size, 0x0020) != size:
            raise OSError("working cache attributes changed")
        result = []
        total = size
        for name in names.raw.split(b"\0"):
            if not name:
                continue
            size = get(fd, name, None, 0, 0, 0)
            total += max(size, 0)
            if size < 0 or total > 1024 * 1024:
                raise OSError("unavailable or oversized working cache attribute value")
            value = ctypes.create_string_buffer(size)
            if get(fd, name, value, size, 0, 0) != size:
                raise OSError("working cache attribute value changed")
            result.append((name.hex(), hashlib.sha256(value.raw).hexdigest()))
            if clear and remove(fd, name, 0):
                raise OSError("cannot remove inherited working cache attribute")
        ctypes.set_errno(0)
        acl = get_acl(fd, 0x00000100)  # ACL_TYPE_EXTENDED is separate from xattrs.
        if not acl:
            if ctypes.get_errno() == errno.ENOENT:  # Darwin: no extended ACL.
                return {"xattrs": sorted(result), "extended_acl_sha256": None, "birthtime_ns": birthtime(fd)}
            raise OSError("cannot inspect working cache ACL")
        text = None
        try:
            length = ctypes.c_ssize_t()
            text = acl_text(acl, ctypes.byref(length))
            if not text or not 0 <= length.value <= 1024 * 1024:
                raise OSError("unavailable or oversized working cache ACL")
            acl_sha = hashlib.sha256(ctypes.string_at(text, length.value)).hexdigest()
        finally:
            if text:
                acl_free(text)
            acl_free(acl)
        return {"xattrs": sorted(result), "extended_acl_sha256": acl_sha, "birthtime_ns": birthtime(fd)}
    metadata.birthtime = birthtime
    return native_clone, exclusive_move, metadata


def _digests(fd, object_format):
    info = os.fstat(fd)
    blob = hashlib.new(object_format)
    blob.update(b"blob " + str(info.st_size).encode() + b"\0")
    sha = hashlib.sha256()
    os.lseek(fd, 0, os.SEEK_SET)
    remaining = info.st_size
    while remaining:
        data = os.read(fd, min(1024 * 1024, remaining))
        if not data:
            raise OSError("cache file shortened while hashing")
        remaining -= len(data)
        blob.update(data)
        sha.update(data)
    if os.read(fd, 1):
        raise OSError("cache file grew while hashing")
    return blob.hexdigest(), sha.hexdigest()


class CheckoutCache:
    def __init__(self, repository, commit, donor, git_command, environment, timeout, verify_physical):
        self.repository, self.commit = Path(repository), commit
        self.donor = Path(donor) if donor is not None else None
        self.git_command, self.environment, self.timeout = git_command, environment, timeout
        self.verify_physical = verify_physical
        self.clones = []
        self.record = {"schema": 1, "target": commit, "donor_data_only": str(donor),
                       "method": "normal-checkout", "cloned": 0, "commands": []}

    def git(self, *args, data=None, allowed=(0,)):
        command = [*self.git_command, "-C", str(self.repository), *args]
        result = subprocess.run(command, input=data, env=self.environment, capture_output=True,
                                timeout=self.timeout, check=False)
        self.record["commands"].append({"argv": command, "exit": result.returncode,
             "stdin_sha256": hashlib.sha256(data).hexdigest() if data is not None else None,
             "stdout_sha256": hashlib.sha256(result.stdout).hexdigest(),
             "stderr": result.stderr.decode("utf-8", "backslashreplace")})
        if result.returncode not in allowed:
            raise RuntimeError("working cache controlled Git operation failed: " + args[0])
        return result.stdout

    def prepare(self):
        if self.donor is not None:
            source = self.donor.resolve()
            target = self.repository.resolve()
            if source.is_relative_to(target) or target.is_relative_to(source):
                raise CustodyRefused("working DATA cache and destination overlap")
        native = _native()
        if native is None or self.donor is None:
            return self
        # Only a new empty source tree. Existing snapshots retain the original route.
        if any(p.name != ".git" for p in self.repository.iterdir()):
            return self
        if self.git("rev-parse", "--verify", "HEAD", allowed=(0, 128)).strip():
            return self
        try:
            with _directory(self.donor) as donor:
                with _directory(self.repository) as destination:
                    if (_binding(os.fstat(donor[0]))[:2] in destination[1].ancestors
                            or _binding(os.fstat(destination[0]))[:2] in donor[1].ancestors):
                        raise CustodyRefused("working DATA cache and destination physically overlap")
                    self._prepare(native, donor, destination)
        except OSError as error:
            # No donor root was opened and no source/index write has started.
            if self.record["method"] != "normal-checkout":
                raise
            self.record["unavailable_donor"] = str(error)
        return self

    def _prepare(self, native, donor, destination):
        clone, move, metadata = native
        raw = self.git("ls-tree", "-rz", "--full-tree", self.commit)
        self.record["inventory_sha256"] = hashlib.sha256(raw).hexdigest()
        entries = []
        seen = set()
        for row in raw.split(b"\0"):
            if not row:
                continue
            header, path = row.split(b"\t", 1)
            mode, kind, oid = header.split()
            _parts(path)
            if path in seen or mode not in (b"100644", b"100755", b"120000", b"160000"):
                raise RuntimeError("working cache inventory is not a complete supported Git tree")
            seen.add(path)
            entries.append((mode, kind, oid, path))
        self.record["entries"] = len(entries)
        self.entries = entries
        object_format = self.git("rev-parse", "--show-object-format").decode().strip()
        if object_format not in ("sha1", "sha256"):
            raise RuntimeError("unsupported working cache object format")
        self.record["method"] = "native-clone-with-complete-git-fallback"
        self.record["timestamp_policy"] = (
            "atime/mtime/birthtime from independent same-parent fresh creation; "
            "ctime from actual new-inode mutations; validation reads may advance atime")
        self.git("read-tree", self.commit)
        eligible = set()
        regular = [p for mode, _, _, p in entries if mode in (b"100644", b"100755")]
        # --cached resolves authenticated tree attributes, not dirty donor attributes.
        for start in range(0, len(regular), 1024):
            paths = regular[start:start + 1024]
            values = self.git("check-attr", "--cached", "-z", "--stdin", *ATTRIBUTES,
                              data=b"\0".join(paths) + b"\0").split(b"\0")
            if values[-1:] != [b""] or len(values) != len(paths) * len(ATTRIBUTES) * 3 + 1:
                raise RuntimeError("working cache attribute inventory is incomplete")
            for offset, path in enumerate(paths):
                rows = values[offset * 15:offset * 15 + 15]
                if any(rows[i * 3:i * 3 + 2] != [path, a.encode()] for i, a in enumerate(ATTRIBUTES)):
                    raise RuntimeError("working cache attribute inventory changed paths")
                # Even an explicit text/eol setting is left to native Git.
                if all(rows[i * 3 + 2] == b"unspecified" for i in range(5)):
                    eligible.add(path)
        fallback = []
        with _directory(self.repository / ".git") as (temp_parent, temp_parent_check):
            temp = Path(tempfile.mkdtemp(prefix="trust-working-data-", dir=self.repository / ".git"))
            expected_temp = _binding(os.stat(temp.name, dir_fd=temp_parent, follow_symlinks=False))
            try:
                with _directory(temp) as temporary:
                    for mode, kind, oid, path in entries:
                        row = None
                        if path in eligible:
                            row = self._clone_one(donor, destination, temporary, native,
                                                  path, mode, oid, object_format)
                        if row is None:
                            fallback.append(path)
                        else:
                            self.clones.append(row)
            finally:
                # Pin the parent and original directory; never follow a replaced
                # path or remove an unknown EMPTY directory during refusal.
                try:
                    temp_parent_check()
                    if _binding(os.stat(temp.name, dir_fd=temp_parent, follow_symlinks=False)) != expected_temp:
                        raise CustodyRefused("working cache temporary directory replaced; preserving it")
                    fd = os.open(temp.name, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW, dir_fd=temp_parent)
                    try:
                        if _binding(os.fstat(fd)) != expected_temp:
                            raise CustodyRefused("working cache cleanup directory changed; preserving it")
                        if not os.listdir(fd):
                            temp_parent_check()
                            if _binding(os.stat(temp.name, dir_fd=temp_parent, follow_symlinks=False)) != expected_temp:
                                raise CustodyRefused("working cache temporary directory changed before removal")
                            os.rmdir(temp.name, dir_fd=temp_parent)
                    finally:
                        os.close(fd)
                except OSError as error:
                    raise CustodyRefused("working cache cleanup cannot revalidate original directory") from error
        # Bind clone stat entries first, then have Git perform its normal conversions,
        # symlink creation and gitlink placeholder handling for EVERY remaining path.
        self.git("update-index", "--ignore-missing", "--refresh", allowed=(0, 1))
        for start in range(0, len(fallback), 1024):
            self.git("checkout-index", "-z", "--stdin",
                     data=b"\0".join(fallback[start:start + 1024]) + b"\0")
        self.record["cloned"] = len(self.clones)
        self.record["fallback"] = len(fallback)

    def _clone_one(self, donor, destination, temporary, native, path, mode, oid, object_format):
        clone, move, metadata = native
        source_root, source_check = donor
        dest_root, dest_check = destination
        temp_root, temp_check = temporary
        name = b"candidate"
        candidate_identity = None
        copied = None
        installation_started = False
        # Donor failures never grant authority, and fall back to authenticated objects.
        try:
            with _parent(source_root, path) as (parent, leaf, parent_check):
                fd = os.open(leaf, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK, dir_fd=parent)
                try:
                    before = os.fstat(fd)
                    if (not stat.S_ISREG(before.st_mode) or before.st_nlink != 1
                            or before.st_uid != os.getuid() or before.st_mode & 0o7022
                            or getattr(before, "st_flags", 0)):
                        return None
                    expected_mode = 0o755 if mode == b"100755" else 0o644
                    if stat.S_IMODE(before.st_mode) != expected_mode:
                        return None
                    source_metadata = metadata(fd)
                    blob, sha = _digests(fd, object_format)
                    if blob.encode() != oid or _identity(os.fstat(fd)) != _identity(before):
                        return None
                    clone(fd, temp_root, name)
                    candidate_identity = _binding(os.stat(name, dir_fd=temp_root, follow_symlinks=False))
                    copied = os.open(name, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK, dir_fd=temp_root)
                    info = os.fstat(copied)
                    if _binding(info) != candidate_identity:
                        raise CustodyRefused("clone candidate replaced before opening; preserving it")
                    if (not stat.S_ISREG(info.st_mode) or info.st_nlink != 1
                            or (info.st_dev, info.st_ino) == (before.st_dev, before.st_ino)
                            or info.st_uid != os.getuid() or getattr(info, "st_flags", 0)):
                        return None
                    if (_digests(copied, object_format) != (blob, sha)
                            or _identity(os.fstat(fd)) != _identity(before)
                            or metadata(fd) != source_metadata
                            or _identity(os.stat(leaf, dir_fd=parent, follow_symlinks=False)) != _identity(before)):
                        return None
                    source_check(); parent_check(); dest_check(); temp_check()
                    with _parent(dest_root, path, create=True) as (target, target_leaf, target_check):
                        # Baseline is independent of donor DATA and created in
                        # the SAME working parent, including its inherited ACL.
                        control = (b".trust-normal-metadata-" + os.urandom(16).hex().encode())
                        baseline = os.open(control, os.O_RDWR | os.O_CREAT | os.O_EXCL | os.O_NOFOLLOW,
                                           0o777 if mode == b"100755" else 0o666, dir_fd=target)
                        base_stat = os.fstat(baseline)
                        try:
                            base_stat = os.fstat(baseline)
                            if (base_stat.st_nlink != 1 or base_stat.st_uid != os.getuid()
                                    or getattr(base_stat, "st_flags", 0)):
                                return None
                            normal_metadata = metadata(baseline)
                            metadata(copied, clear=True)
                            os.fchmod(copied, stat.S_IMODE(base_stat.st_mode))
                            # Donor DATA has no freshness authority. Match the
                            # actual normal new-file creation context, never
                            # carry old/future donor timestamps into a build.
                            os.utime(copied, ns=(base_stat.st_atime_ns, base_stat.st_mtime_ns))
                            metadata.birthtime(copied, normal_metadata["birthtime_ns"])
                            # OS process provenance may reappear after removal;
                            # only exact normal new-file metadata is accepted.
                            if metadata(copied) != normal_metadata:
                                return None
                            copy_stat = os.fstat(copied)
                            if ((copy_stat.st_uid, copy_stat.st_gid, stat.S_IMODE(copy_stat.st_mode), getattr(copy_stat, "st_flags", 0)) !=
                                    (base_stat.st_uid, base_stat.st_gid, stat.S_IMODE(base_stat.st_mode), getattr(base_stat, "st_flags", 0))):
                                return None
                            if (_identity(os.fstat(baseline)) != _identity(base_stat)
                                    or metadata(baseline) != normal_metadata
                                    or _identity(os.stat(control, dir_fd=target, follow_symlinks=False)) != _identity(base_stat)):
                                raise CustodyRefused("working cache metadata control changed")
                        finally:
                            try:
                                if (_identity(os.stat(control, dir_fd=target, follow_symlinks=False)) != _identity(base_stat)
                                        or _identity(os.fstat(baseline)) != _identity(base_stat)):
                                    raise CustodyRefused("metadata control changed; preserving unknown leaf")
                                os.unlink(control, dir_fd=target)
                            finally:
                                os.close(baseline)
                        if (_identity(os.fstat(fd)) != _identity(before)
                                or metadata(fd) != source_metadata):
                            return None
                        source_check(); parent_check(); target_check(); dest_check()
                        installation_started = True
                        move(temp_root, name, target, target_leaf)
                        target_check(); dest_check()
                        after = os.fstat(copied)
                        if _identity(os.stat(target_leaf, dir_fd=target, follow_symlinks=False)) != _identity(after):
                            raise CustodyRefused("working cache installed clone binding changed; preserving it")
                    return {"path": os.fsdecode(path), "blob": blob, "sha256": sha,
                            "source_metadata": source_metadata, "normal_metadata": normal_metadata,
                            "normal_times_ns": {"atime": base_stat.st_atime_ns, "mtime": base_stat.st_mtime_ns},
                            "destination_atime_ns": after.st_atime_ns,
                            "source": list(_identity(before)), "destination": list(_identity(after))}
                finally:
                    os.close(fd)
        except OSError as error:
            if installation_started:
                raise CustodyRefused("working cache installation lost custody; preserving destination") from error
            return None
        finally:
            # Keep the known-created inode held across our own metadata changes.
            # A path replacement still differs from this descriptor and survives.
            try:
                try:
                    current = os.stat(name, dir_fd=temp_root, follow_symlinks=False)
                    expected = candidate_identity
                    if copied is not None:
                        held = _binding(os.fstat(copied))
                        if expected is None or held[:2] != expected[:2]:
                            raise CustodyRefused("held clone candidate lost custody; preserving it")
                        expected = held
                    if expected is None or _binding(current) != expected:
                        raise CustodyRefused("clone candidate has unknown custody; preserving it")
                    os.unlink(name, dir_fd=temp_root)
                except FileNotFoundError:
                    pass
            finally:
                if copied is not None:
                    os.close(copied)

    def verify(self):
        if self.record["method"] == "normal-checkout":
            return self.record
        try:
            return self._verify_prepared()
        except CustodyRefused:
            raise
        except (OSError, RuntimeError) as error:
            # A prepared tree contains installed clones. A failed final audit
            # cannot establish which source leaves still belong to this owner.
            raise CustodyRefused("working cache final audit refused; preserving destination: " + str(error)) from error

    def _verify_prepared(self):
        # Bind the native operations once for this audit. Each file's actual
        # metadata is still read and checked below; rebinding ctypes for every
        # source leaf adds no custody evidence. Prepared clones cannot fall
        # back to an unclassified error if their native audit API is lost.
        native = _native()
        if native is None and self.clones:
            raise CustodyRefused("working cache native audit API unavailable; preserving prepared source")
        if self.git("rev-parse", "HEAD").decode().strip() != self.commit:
            raise RuntimeError("working cache checkout selected a different commit")
        if self.git("write-tree").strip() != self.git("rev-parse", self.commit + "^{tree}").strip():
            raise RuntimeError("working cache checkout lost the complete authenticated index")
        flags = self.git("ls-files", "-v", "-z").split(b"\0")
        fsmonitor = self.git("ls-files", "-f", "-z").split(b"\0")
        if any(row and not row.startswith(b"H ") for row in flags + fsmonitor):
            raise RuntimeError("working cache index contains sparse/assume-unchanged entries")
        self.git("update-index", "--refresh")
        if self.git("status", "--porcelain=v1", "--untracked-files=all", "--ignored", "--ignore-submodules=all").strip():
            raise RuntimeError("working cache final source tree is incomplete or changed")
        object_format = self.git("rev-parse", "--show-object-format").decode().strip()
        physical_bindings = {}
        with _directory(self.repository) as (root, check):
            for mode, kind, oid, path in self.entries:
                with _parent(root, path) as (parent, leaf, parent_check):
                    info = os.stat(leaf, dir_fd=parent, follow_symlinks=False)
                    if mode in (b"100644", b"100755"):
                        if (not stat.S_ISREG(info.st_mode) or info.st_nlink != 1
                                or bool(info.st_mode & 0o111) != (mode == b"100755")
                                or info.st_mode & 0o7000):
                            raise RuntimeError("complete working cache tree has aliased or wrong-mode source")
                    elif mode == b"120000":
                        if not stat.S_ISLNK(info.st_mode):
                            raise RuntimeError("complete working cache tree lost a source symlink")
                    elif not stat.S_ISDIR(info.st_mode):
                        raise RuntimeError("complete working cache tree lost a gitlink placeholder")
                    physical_bindings[path] = _identity(info)
                    parent_check(); check()
            for row in self.clones:
                with _parent(root, os.fsencode(row["path"])) as (parent, leaf, parent_check):
                    fd = os.open(leaf, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK, dir_fd=parent)
                    try:
                        if (list(_identity(os.fstat(fd))) != row["destination"]
                                or _digests(fd, object_format) != (row["blob"], row["sha256"])
                                or native[2](fd) != row["normal_metadata"]
                                or list(_identity(os.fstat(fd))) != row["destination"]
                                or list(_identity(os.stat(leaf, dir_fd=parent, follow_symlinks=False))) != row["destination"]):
                            raise RuntimeError("normal checkout rewrote or changed a verified clone")
                        parent_check(); check()
                    finally:
                        os.close(fd)
        self.record["physical_snapshot"] = self.verify_physical(self.repository)
        with _directory(self.repository) as (root, check):
            for path, expected in physical_bindings.items():
                with _parent(root, path) as (parent, leaf, parent_check):
                    if _identity(os.stat(leaf, dir_fd=parent, follow_symlinks=False)) != expected:
                        raise RuntimeError("complete physical source changed during byte audit")
                    parent_check(); check()
        if self.git("write-tree").strip() != self.git("rev-parse", self.commit + "^{tree}").strip():
            raise RuntimeError("working cache index changed during physical source audit")
        self.record["complete_checkout_verified"] = True
        book = self.repository / ".git/trust-source-working-cache.jsonl.gz"
        decoded = hashlib.sha256()
        with book.open("xb") as raw:
            with gzip.GzipFile(fileobj=raw, mode="wb", mtime=0) as stream:
                for row in self.clones:
                    line = (json.dumps(row, sort_keys=True) + "\n").encode()
                    decoded.update(line)
                    stream.write(line)
        self.record["clone_book"] = {"path": ".git/" + book.name,
            "sha256": hashlib.sha256(book.read_bytes()).hexdigest(),
            "decoded_sha256": decoded.hexdigest(), "records": len(self.clones)}
        # Generated evidence only; never consulted as source/ownership authority.
        receipt = self.repository / ".git/trust-source-working-cache.json"
        with receipt.open("x") as stream:
            json.dump(self.record, stream, sort_keys=True)
            stream.write("\n")
        return self.record


def prepare_checkout(repository, commit, donor, *, git_command, environment, verify_physical, timeout=600):
    return CheckoutCache(repository, commit, donor, git_command, environment, timeout, verify_physical).prepare()
