"""Direct fixture shebangs for the exact running Python, including spaced paths.

Darwin's protected /bin/sh and /usr/bin/env strip DYLD_* before a trampoline
can exec Python. Keep a private direct alias instead, retained until process
exit, so the fixture preserves its caller's complete replay environment.
"""
import sys
import tempfile
import atexit
from pathlib import Path

_ALIASES = {}


def fixture_shebang():
    original = Path(sys.executable).resolve(strict=True)
    if not any(character.isspace() for character in str(original)):
        return "#!" + str(original) + "\n"
    identity = original.stat()
    key = (str(original), identity.st_dev, identity.st_ino, identity.st_size, identity.st_mtime_ns)
    if key not in _ALIASES:
        directory = tempfile.TemporaryDirectory(prefix="trust-fixture-python-", dir="/tmp")
        alias = Path(directory.name) / "python"
        alias.symlink_to(original)
        atexit.register(directory.cleanup)
        _ALIASES[key] = (directory, alias)
    return "#!" + str(_ALIASES[key][1]) + "\n"
