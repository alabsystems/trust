"""The real native-authority capture and producer agree on CPU admission."""
import os
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import recreate_bootstrap as bootstrap


class BootstrapResourceAdmissionTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)

    def capture(self, environment):
        bound = {"name": "tool", "status": "bound", "resolved_local_path": "/tool",
                 "resolved_real_path": "/tool", "sha256": "a" * 64, "identity": "tool"}
        with patch.dict(os.environ, environment, clear=True), \
                patch.object(bootstrap.Path, "home", return_value=self.root), \
                patch.object(bootstrap, "which", return_value="/tool"), \
                patch.object(bootstrap, "_native_tool_record", return_value=bound), \
                patch.object(bootstrap.platform, "system", return_value="Linux"):
            return bootstrap.capture_build_authority(self.root, "test-host", None)

    def test_positive_held_share_reaches_capture_without_changing_native_identity(self):
        base = self.capture({})
        for share, canonical in [("1", "1"), ("6", "6"), ("4294967295", "4294967295"),
                                 ("0" * 5000 + "6", "6")]:
            with self.subTest(share=share):
                env = {"BUILD_SLOT_HELD": "1", "CARGO_BUILD_JOBS": share}
                captured = self.capture(env)
                self.assertEqual(captured["status"], "ready", captured["errors"])
                self.assertEqual(captured["authority_sha256"], base["authority_sha256"])
                self.assertEqual(bootstrap._build_slot_cpu_share(env), canonical)

    def test_missing_invalid_or_overflow_share_refuses_both_boundaries(self):
        for share in [None, "", "0", "-1", "1.5", " 6", "6 ", "4294967296", "arbitrary", "9" * 5000]:
            with self.subTest(share=share):
                env = {"BUILD_SLOT_HELD": "1"}
                if share is not None:
                    env["CARGO_BUILD_JOBS"] = share
                with self.assertRaisesRegex(RuntimeError, "positive u32"):
                    bootstrap._build_slot_cpu_share(env)
                with patch.dict(os.environ, env, clear=True):
                    with self.assertRaisesRegex(RuntimeError, "positive u32"):
                        bootstrap.xpy_environment(self.root, "test-host", seed_mode=False)
                captured = self.capture(env)
                self.assertEqual(captured["status"], "rejected")
                self.assertTrue(any("positive u32" in error for error in captured["errors"]))

    def test_unadmitted_cargo_jobs_remains_an_ambient_override(self):
        for marker in [None, "0", "true"]:
            env = {"CARGO_BUILD_JOBS": "6"}
            if marker is not None:
                env["BUILD_SLOT_HELD"] = marker
            self.assertEqual(set(bootstrap._ambient_build_authority_overrides(env)), {"CARGO_BUILD_JOBS"})
            self.assertEqual(self.capture(env)["status"], "rejected")

    def test_cpu_share_cannot_hide_compiler_sdk_library_or_cargo_flags(self):
        env = {"BUILD_SLOT_HELD": "1", "CARGO_BUILD_JOBS": "6", "RUSTC": "/other",
               "CPATH": "/other", "LIBRARY_PATH": "/other", "SDKROOT": "/other",
               "CARGO_ENCODED_RUSTFLAGS": "--cfg hostile"}
        self.assertEqual(set(bootstrap._ambient_build_authority_overrides(env)),
                         set(env) - {"BUILD_SLOT_HELD", "CARGO_BUILD_JOBS"})
        self.assertEqual(self.capture(env)["status"], "rejected")


if __name__ == "__main__":
    unittest.main()
