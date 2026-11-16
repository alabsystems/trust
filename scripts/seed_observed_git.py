"""Concrete P03 reader to P02 flat raw-payload materialization seam.

No Git launch or complete graph is inferred from a payload directory. The
source-bound caller must select/observe exact HEAD/resolver/lock authority and
traverse every committed edge before P02 replay. No capability is issued here.
"""
from __future__ import annotations
import hashlib
import os
from pathlib import Path
import re

HERE = Path(__file__).resolve().parent
commands = __trust_source_loader__.module('trust_seed_observed_commands', HERE / 'seed_observed_commands.py')
io = commands.io
HEX40 = re.compile('[0-9a-f]{40}')


def capture_object(reader, oid, kind, raw_root, account):
    """Capture one requested object through actual retained, bounded Git IO.

    P02's concrete Account is charged here and reused for replay; neither its
    counters nor its original endpoint may be reset between these operations.
    """
    try:
        p02 = __trust_source_loader__.module('trust_seed_dependency_objects', HERE / 'seed_dependency_objects.py')
        p02.checked_account(account)
        io.require(type(reader) is commands.ChildReader and reader.pidfd is not None
                   and not reader.finished and not reader.owner.poisoned
                   and reader.spec['role'] == 'git' and reader.spec['callsite'] == 'initialize.git'
                   and reader.spec['argv'][0] == '/usr/bin/git', 'actual concrete observed Git reader required')
        io.require(account.end == reader.owner.work_end, 'materialization Account is not original work endpoint')
        io.require(type(oid) is str and HEX40.fullmatch(oid) and kind in ('commit', 'tree', 'blob'),
                   'object request is not an exact locked-graph edge')
        root = Path(raw_root)
        io.require(root.is_absolute() and root.resolve(strict=True) == root and root.is_dir(),
                   'raw payload root is not canonical')
        reader.write_input((oid + '\n').encode())
        head = reader.read_object_line(256)
        fields = head.rstrip(b'\n').split(b' ')
        io.require(len(fields) == 3 and fields[:2] == [oid.encode(), kind.encode()]
                   and fields[2].isdigit() and str(int(fields[2])).encode() == fields[2],
                   'observed cat-file header differs from exact requested edge')
        size = int(fields[2])
        maximum = p02.byte.LIMIT_FILE_BYTES if kind == 'blob' else p02.byte.LIMIT_OBJECT_METADATA_BYTES
        io.require(0 <= size <= maximum, 'actual raw object exceeds unchanged P02 bounds')
        account.debit(entries=1)
        fd = os.open(root / oid, os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_NOFOLLOW | os.O_CLOEXEC, 0o600)
        value = hashlib.sha1(kind.encode() + b' ' + fields[2] + b'\0')
        sha, copied = hashlib.sha256(), 0
        try:
            while copied < size:
                block = reader.read_object_exact(min(1024 * 1024, size - copied))
                account.debit(len(block))
                view = memoryview(block)
                while view:
                    count = os.write(fd, view)
                    io.require(count > 0, 'flat raw object short write')
                    view = view[count:]
                value.update(block)
                sha.update(block)
                copied += len(block)
            io.require(reader.read_object_exact(1) == b'\n' and value.hexdigest() == oid,
                       'observed raw object/trailer does not authenticate exact OID')
            os.fsync(fd)
        finally:
            os.close(fd)
        account.debit()
        return {'oid': oid, 'kind': kind, 'bytes': copied, 'sha256': sha.hexdigest(),
                'raw_path': str(root / oid), 'reader_command': reader.number,
                'scope_closed': False, 'completed_capability': False}
    except BaseException as error:
        if type(reader) is commands.ChildReader:
            reader.abort(error)
            raise io.CustodyFailure(str(error), reader.owner) from error
        raise
