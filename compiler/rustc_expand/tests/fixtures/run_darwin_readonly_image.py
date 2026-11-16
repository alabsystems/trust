#!/usr/bin/env python3
"""Explicit native-DSO restriction diagnostic; no proof/admission authority."""
import argparse
import hashlib
import os
from pathlib import Path
import plistlib
import re
import shutil
import subprocess
import tempfile


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--test-binary", type=Path, required=True)
    parser.add_argument("--dso", type=Path, required=True)
    parser.add_argument("--sha256", required=True)
    parser.add_argument("--declaration-symbol", required=True)
    parser.add_argument("--constructor-control", action="store_true")
    args = parser.parse_args()
    if sha256(args.dso) != args.sha256:
        parser.error("native fixture DSO digest mismatch")
    scratch = Path(tempfile.gettempdir()) / ".ubd"
    scratch.mkdir(exist_ok=True)
    with tempfile.TemporaryDirectory(prefix="trust-native-image-", dir=scratch) as temporary:
        return run(args, Path(temporary))


def run(args, root):
    # Both constructor sides use a fresh private probe directory. An unrelated
    # file in a shared temporary directory must not impersonate policy denial.
    root = root.resolve()
    (root / ".ubd").mkdir(mode=0o700)
    environment = os.environ.copy()
    environment.update(TMPDIR=str(root), TRUST_D21_PRIVATE_TMPDIR=str(root),
                       TRUST_D21_NATIVE_DSO=str(args.dso.resolve()),
                       TRUST_D21_NATIVE_DSO_SYMBOL=args.declaration_symbol)
    if args.constructor_control:
        baseline = subprocess.run([
            str(args.test_binary.resolve()),
            "real_proc_macro_dso_preserves_declared_client_and_native_tokens",
            "--ignored", "--nocapture", "--test-threads=1",
        ], env=environment, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        print(baseline.stdout.decode(errors="replace"), flush=True)
        expected = ('Some("wrong_constructor_state_2_tmp_' + os.fsencode(root).hex() + '")').encode()
        if baseline.returncode != 101 or expected not in baseline.stdout:
            raise RuntimeError("unrestricted initializer did not create its probe in the runner's private TMPDIR: "
                               + expected.decode())
    source = root / "source"
    source.mkdir()
    shutil.copyfile(args.dso, source / "macro.dylib")
    assert sha256(source / "macro.dylib") == args.sha256
    image = root / "image.dmg"
    subprocess.run([
        "/usr/bin/hdiutil", "create", "-format", "UDRO", "-fs", "HFS+",
        "-volname", "TrustNativeMacroFixture", "-srcfolder", str(source), str(image),
    ], check=True)
    mount = root / ('mounted" parameter \\')
    mount.mkdir()
    attached = subprocess.run([
        "/usr/bin/hdiutil", "attach", "-readonly", "-nobrowse",
        "-mountpoint", str(mount), "-plist", str(image),
    ], check=True, stdout=subprocess.PIPE)
    device = str(mount)
    try:
        entries = plistlib.loads(attached.stdout)["system-entities"]
        devices = [e["dev-entry"] for e in entries
                   if re.fullmatch(r"/dev/disk[0-9]+", e.get("dev-entry", ""))]
        if len(devices) != 1:
            raise RuntimeError("native image did not yield exactly one owned disk")
        device = devices[0]
        image.unlink()
        assert os.statvfs(mount).f_flag & os.ST_RDONLY
        dso = mount / "macro.dylib"
        assert sha256(dso) == args.sha256
        environment["TRUST_D21_NATIVE_DSO"] = str(dso)
        result = subprocess.run([
            str(args.test_binary.resolve()),
            ("darwin_constructor_uses_private_tmpdir_before_client_entry" if args.constructor_control
             else "darwin_readonly_image_runs_native_client_after_fixed_restrictions"),
            "--ignored", "--nocapture", "--test-threads=1",
        ], env=environment)
        assert sha256(dso) == args.sha256
    finally:
        subprocess.run(["/usr/bin/hdiutil", "detach", device], check=True)
    return result.returncode


if __name__ == "__main__":
    raise SystemExit(main())
