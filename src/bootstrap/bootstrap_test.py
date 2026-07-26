"""Bootstrap tests

Run these with `x test bootstrap`, or `python -m unittest src/bootstrap/bootstrap_test.py`."""

from __future__ import absolute_import, division, print_function
import os
import subprocess
import unittest
from unittest.mock import patch
import tempfile
import hashlib
import sys
from pathlib import Path

from shutil import rmtree

# Allow running this from the top-level directory.
bootstrap_dir = os.path.dirname(os.path.abspath(__file__))
# For the import below, have Python search in src/bootstrap first.
sys.path.insert(0, bootstrap_dir)
import bootstrap  # noqa: E402
import configure  # noqa: E402


def serialize_and_parse(configure_args, bootstrap_args=None):
    from io import StringIO

    if bootstrap_args is None:
        bootstrap_args = bootstrap.FakeArgs()

    section_order, sections, targets = configure.parse_args(configure_args)
    buffer = StringIO()
    configure.write_config_toml(buffer, section_order, targets, sections)
    build = bootstrap.RustBuild(config_toml=buffer.getvalue(), args=bootstrap_args)

    try:
        import tomllib

        # Verify this is actually valid TOML.
        tomllib.loads(build.config_toml)
    except ImportError:
        print(
            "WARNING: skipping TOML validation, need at least python 3.11",
            file=sys.stderr,
        )
    return build


class VerifyTestCase(unittest.TestCase):
    """Test Case for verify"""

    def setUp(self):
        self.container = tempfile.mkdtemp()
        self.src = os.path.join(self.container, "src.txt")
        self.bad_src = os.path.join(self.container, "bad.txt")
        content = "Hello world"

        self.expected = hashlib.sha256(content.encode("utf-8")).hexdigest()

        with open(self.src, "w") as src:
            src.write(content)
        with open(self.bad_src, "w") as bad:
            bad.write("Hello!")

    def tearDown(self):
        rmtree(self.container)

    def test_valid_file(self):
        """Check if the sha256 sum of the given file is valid"""
        self.assertTrue(bootstrap.verify(self.src, self.expected, False))

    def test_invalid_file(self):
        """Should verify that the file is invalid"""
        self.assertFalse(bootstrap.verify(self.bad_src, self.expected, False))


class FileUrlDownloadTestCase(unittest.TestCase):
    """Test repo-local bootstrap artifact downloads."""

    def setUp(self):
        self.container = tempfile.mkdtemp()
        self.src = os.path.join(self.container, "trust stage0.txt")
        self.dst = os.path.join(self.container, "downloaded.txt")
        with open(self.src, "w") as src:
            src.write("local trust stage0")

    def tearDown(self):
        rmtree(self.container)

    def test_file_url_download_copies_local_artifact(self):
        bootstrap.download(self.dst, Path(self.src).as_uri(), False, False)
        with open(self.dst) as dst:
            self.assertEqual(dst.read(), "local trust stage0")

    def test_trust_root_file_url_resolves_to_checkout(self):
        expected = os.path.join(
            os.path.abspath(os.path.join(__file__, "../../..")),
            "build",
            "trust-stage0",
            "artifact.tar.xz",
        )
        self.assertEqual(
            bootstrap.file_url_to_path(
                "file://{trust-root}/build/trust-stage0/artifact.tar.xz"
            ),
            expected,
        )

    def test_rustup_dist_server_does_not_override_trust_stage0(self):
        with patch.dict(
            os.environ,
            {"RUSTUP_DIST_SERVER": "https://static.rust-lang.org"},
            clear=False,
        ):
            os.environ.pop("TRUST_DIST_SERVER", None)
            build = bootstrap.RustBuild()
        self.assertEqual(build.download_url, build.stage0_data["dist_server"])

    def test_trust_dist_server_does_not_override_stage0(self):
        with patch.dict(os.environ, {"TRUST_DIST_SERVER": "file:///tmp/trust-dist"}, clear=False):
            build = bootstrap.RustBuild()
        self.assertEqual(build.download_url, build.stage0_data["dist_server"])

    def test_download_rejects_static_rust_lang_org(self):
        with self.assertRaisesRegex(RuntimeError, "inherited upstream Rust download host"):
            bootstrap.download(
                self.dst,
                "https://static.rust-lang.org/dist/archive.tar.xz",
                False,
                False,
            )

    def test_download_rejects_ci_artifacts_rust_lang_org(self):
        with self.assertRaisesRegex(RuntimeError, "ci-artifacts.rust-lang.org"):
            bootstrap.download(
                self.dst,
                "https://ci-artifacts.rust-lang.org/rustc-builds/archive.tar.xz",
                False,
                False,
            )

    def test_stage0_dist_server_rejects_upstream_rust_domain(self):
        with patch.dict(
            os.environ,
            {"TRUST_DIST_SERVER": "https://static.rust-lang.org"},
            clear=False,
        ):
            build = bootstrap.RustBuild()
        self.assertEqual(build.download_url, build.stage0_data["dist_server"])

    def test_file_url_with_rust_lang_text_is_allowed(self):
        path = os.path.join(self.container, "static.rust-lang.org.txt")
        with open(path, "w") as src:
            src.write("not a remote host")
        bootstrap.download(self.dst, Path(path).as_uri(), False, False)
        with open(self.dst) as dst:
            self.assertEqual(dst.read(), "not a remote host")

    def test_get_diagnoses_missing_checksum_pinned_file_payload(self):
        base = Path(os.path.join(self.container, "trust-stage0")).as_uri()
        payload = "dist/2026-04-24/trustc-1.96.0-trust-aarch64-apple-darwin.tar.xz"
        expected_sha256 = "0" * 64
        resolved_payload = os.path.join(
            self.container,
            "trust-stage0",
            "dist",
            "2026-04-24",
            "trustc-1.96.0-trust-aarch64-apple-darwin.tar.xz",
        )

        with self.assertRaises(RuntimeError) as ctx:
            bootstrap.get(
                base,
                payload,
                self.dst,
                {payload: expected_sha256},
                verbose=False,
            )

        message = str(ctx.exception)
        self.assertIn("missing checksum-pinned Trust stage0 payload", message)
        self.assertIn("dist_server={}".format(base), message)
        self.assertIn("payload={}".format(payload), message)
        self.assertIn("resolved_payload={}".format(resolved_payload), message)
        self.assertIn("expected_sha256={}".format(expected_sha256), message)
        self.assertNotIn("Pre-built artifacts", message)
        self.assertNotIn("rust-lang.org", message)
        self.assertNotIn("fallback", message)

    @unittest.skipIf(sys.platform == "win32", "POSIX shell shim")
    def test_seed_payload_self_materializes_from_ledger_release(self):
        # Trust: a missing pinned payload under the repo-local seed dist root
        # is fetched from the seed-ledger-declared gh release before failing,
        # via a temp staging dir + os.replace (no partial file at the pinned
        # path on interruption).
        root = os.path.join(self.container, "repo")
        os.makedirs(os.path.join(root, "bootstrap", "trust-stage0"))
        ledger = os.path.join(root, "bootstrap", "trust-stage0", "seed-ledger.toml")
        with open(ledger, "w") as handle:
            handle.write(
                'scope = "internal"\n'
                "[release]\n"
                'repo = "example/trust"\n'
                'tag = "trust-stage0-2026-04-24"\n'
            )
        resolved = os.path.join(
            root, "bootstrap", "trust-stage0", "dist", "2026-04-24", "payload.tar.xz"
        )
        args_log = os.path.join(self.container, "gh-args")
        gh = os.path.join(self.container, "fake-gh")
        with open(gh, "w") as shim:
            # argv: release download TAG --repo REPO --pattern FILE --dir DIR
            shim.write(
                "#!/bin/sh\n"
                'echo "$@" > "{}"\n'.format(args_log) + 'printf seeded > "$9/$7"\n'
            )
        os.chmod(gh, 0o755)

        seeded_sha256 = hashlib.sha256(b"seeded").hexdigest()
        # A wrong pin must refuse to place ANY file at the pinned path — the
        # digest-pinned dist root only ever holds verified bytes.
        self.assertFalse(
            bootstrap.try_materialize_trust_seed_payload(
                resolved, "0" * 64, gh=gh, repo_root=root
            )
        )
        self.assertFalse(os.path.exists(resolved))

        self.assertTrue(
            bootstrap.try_materialize_trust_seed_payload(
                resolved, seeded_sha256, gh=gh, repo_root=root
            )
        )
        with open(resolved) as payload:
            self.assertEqual(payload.read(), "seeded")
        with open(args_log) as recorded:
            args = recorded.read().split()
        self.assertEqual(args[:3], ["release", "download", "trust-stage0-2026-04-24"])
        self.assertIn("example/trust", args)
        self.assertIn("payload.tar.xz", args)
        # the staging dirs must not survive either outcome
        dist_dir = os.path.dirname(resolved)
        self.assertEqual(
            [entry for entry in os.listdir(dist_dir) if entry.startswith(".seed-fetch-")],
            [],
        )

    def test_seed_materialization_declines_outside_seed_dist_root(self):
        # Payload paths outside <repo>/bootstrap/trust-stage0 must keep the
        # strict missing-payload behavior (no fetch attempt at all).
        self.assertFalse(
            bootstrap.try_materialize_trust_seed_payload(
                os.path.join(self.container, "elsewhere", "payload.tar.xz"),
                "0" * 64,
                gh="/nonexistent-gh",
                repo_root=os.path.join(self.container, "repo-without-ledger"),
            )
        )

    def test_stage0_tippy_component_uses_legacy_pin_only_when_canonical_is_absent(self):
        date = "2026-06-23"
        suffix = "1.96.0-trust-aarch64-apple-darwin.tar.xz"
        legacy_path = "dist/{}/trust-clippy-{}".format(date, suffix)
        canonical_path = "dist/{}/tippy-{}".format(date, suffix)

        self.assertEqual(
            bootstrap.select_stage0_extra_component(
                {legacy_path: "0" * 64}, date, suffix, "tippy", "tippy-preview"
            ),
            ("trust-clippy-{}".format(suffix), "trust-clippy-preview", True),
        )
        self.assertEqual(
            bootstrap.select_stage0_extra_component(
                {legacy_path: "0" * 64, canonical_path: "1" * 64},
                date,
                suffix,
                "tippy",
                "tippy-preview",
            ),
            ("tippy-{}".format(suffix), "tippy-preview", False),
        )

    def test_stage0_targo_components_prefer_canonical_and_require_explicit_legacy_pins(self):
        date = "2026-06-23"
        suffix = "1.96.0-trust-aarch64-apple-darwin.tar.xz"
        for canonical, legacy in (("targo", "tcargo"), ("targo-trust", "tcargo-trust")):
            canonical_path = "dist/{}/{}-{}".format(date, canonical, suffix)
            legacy_path = "dist/{}/{}-{}".format(date, legacy, suffix)

            self.assertEqual(
                bootstrap.select_stage0_targo_component(
                    {legacy_path: "0" * 64}, date, suffix, canonical
                ),
                ("{}-{}".format(legacy, suffix), legacy, True),
            )
            self.assertEqual(
                bootstrap.select_stage0_targo_component(
                    {legacy_path: "0" * 64, canonical_path: "1" * 64},
                    date,
                    suffix,
                    canonical,
                ),
                ("{}-{}".format(canonical, suffix), canonical, False),
            )
            self.assertEqual(
                bootstrap.select_stage0_targo_component(
                    {}, date, suffix, canonical
                ),
                ("{}-{}".format(canonical, suffix), canonical, False),
            )

    @unittest.skipIf(bootstrap.platform_is_win32(), "legacy pin is Unix-only")
    def test_legacy_stage0_targo_payload_is_semantically_translated_without_public_alias_leaves(
        self,
    ):
        bin_root = os.path.join(self.container, "stage0-targo")
        bin_dir = os.path.join(bin_root, "bin")
        os.makedirs(bin_dir)

        tcargo = os.path.join(bin_dir, "tcargo")
        with open(tcargo, "w", encoding="utf-8") as tool:
            tool.write(
                """#!/bin/sh
case "${1-}" in
    --version|-V|-vV)
        printf '%s\n' 'tcargo 1.96.0-trust' 'binary: tcargo'
        exit 0
        ;;
esac
printf '%s\n' "$(basename "$0")" "$@" >"$TARGO_ARG_LOG"
"""
            )
        os.chmod(tcargo, 0o755)

        cargo = os.path.join(bin_dir, "cargo")
        with open(cargo, "w", encoding="utf-8") as tool:
            tool.write("#!/bin/sh\nexit 0\n")
        os.chmod(cargo, 0o755)
        for compiler_tool in ("trustc", "trustdoc"):
            path = os.path.join(bin_dir, compiler_tool)
            with open(path, "w", encoding="utf-8") as tool:
                tool.write("#!/bin/sh\nprintf '%s\\n' {}\n".format(compiler_tool))
            os.chmod(path, 0o755)
        legacy_fmt = os.path.join(bin_dir, "tcargo-fmt")
        with open(legacy_fmt, "w", encoding="utf-8") as tool:
            tool.write("#!/bin/sh\nprintf '%s\\n' legacy-fmt\n")
        os.chmod(legacy_fmt, 0o755)
        for retired in ("cargo-fmt", "rustfmt", "rustdoc", "rust-analyzer"):
            with open(os.path.join(bin_dir, retired), "wb") as alias:
                alias.write(b"retired alias")
        libexec_dir = os.path.join(bin_root, "libexec")
        os.makedirs(libexec_dir)
        with open(
            os.path.join(libexec_dir, "rust-analyzer-proc-macro-srv"), "wb"
        ) as alias:
            alias.write(b"retired helper alias")

        tcargo_trust = os.path.join(bin_dir, "tcargo-trust")
        with open(tcargo_trust, "w", encoding="utf-8") as tool:
            tool.write(
                """#!/bin/sh
if [ "${1-}" = "trust" ]; then shift; fi
case "${1-}" in
    --version|-V)
        printf '%s\n' 'tcargo-trust 1.96.0-trust' \\
            'trust.identity=tcargo trust' 'trust.package=tcargo-trust'
        exit 0
        ;;
esac
printf '%s\n' "$@" >"$TARGO_TRUST_ARG_LOG"
"""
            )
        os.chmod(tcargo_trust, 0o755)
        with open(os.path.join(bin_dir, "cargo-trust"), "wb") as alias:
            alias.write(b"retired alias")

        bootstrap.translate_legacy_targo_stage0_surface(
            bin_root, ("targo", "targo-trust")
        )

        targo = os.path.join(bin_dir, "targo")
        version = subprocess.run(
            [targo, "--version"], check=True, text=True, stdout=subprocess.PIPE
        ).stdout
        self.assertEqual(version, "targo 1.96.0-trust\nbinary: targo\n")

        arg_log = os.path.join(self.container, "targo-args.log")
        trust_arg_log = os.path.join(self.container, "targo-trust-args.log")
        env = dict(
            os.environ,
            TARGO_ARG_LOG=arg_log,
            TARGO_TRUST_ARG_LOG=trust_arg_log,
        )
        subprocess.run([targo, "--unverified", "build", "--locked"], env=env, check=True)
        with open(arg_log, encoding="utf-8") as log:
            self.assertEqual(log.read().splitlines(), ["tcargo", "build", "--locked"])

        subprocess.run([targo, "check", "--unverified", "--locked"], env=env, check=True)
        with open(arg_log, encoding="utf-8") as log:
            self.assertEqual(log.read().splitlines(), ["tcargo", "check", "--locked"])

        implicit = subprocess.run(
            [targo, "build"], env=env, text=True, stderr=subprocess.PIPE
        )
        self.assertEqual(implicit.returncode, 101)
        self.assertIn("implicitly unverified artifact", implicit.stderr)

        legacy_marker = subprocess.run(
            [targo, "metadata"],
            env=dict(env, TRUST_BOOTSTRAP_NO_VERIFY="0"),
            text=True,
            stderr=subprocess.PIPE,
        )
        self.assertEqual(legacy_marker.returncode, 101)
        self.assertIn("do not authorize branded Targo", legacy_marker.stderr)

        targo_trust = os.path.join(bin_dir, "targo-trust")
        version = subprocess.run(
            [targo_trust, "--version"],
            env=env,
            check=True,
            text=True,
            stdout=subprocess.PIPE,
        ).stdout
        self.assertIn("targo-trust 1.96.0-trust", version)
        self.assertIn("trust.identity=targo trust", version)
        self.assertNotIn("tcargo", version)

        private_dispatch = os.path.join(
            bin_root,
            bootstrap.STAGE0_LEGACY_TARGO_BACKEND_DIR,
            "tcargo-trust",
        )
        version = subprocess.run(
            [private_dispatch, "trust", "--version"],
            env=env,
            check=True,
            text=True,
            stdout=subprocess.PIPE,
        ).stdout
        self.assertIn("targo-trust 1.96.0-trust", version)
        self.assertNotIn("tcargo", version)

        self.assertTrue(os.path.exists(cargo))
        self.assertTrue(os.path.exists(os.path.join(bin_dir, "targo-fmt")))
        self.assertTrue(os.path.exists(os.path.join(bin_dir, "trustfmt")))
        self.assertTrue(os.path.exists(os.path.join(bin_dir, "trust-analyzer")))
        fmt_output = subprocess.run(
            [os.path.join(bin_root, "libexec", "tcargo-fmt")],
            check=True,
            text=True,
            stdout=subprocess.PIPE,
        ).stdout
        self.assertEqual(fmt_output, "legacy-fmt\n")
        for compiler_tool in ("trustc", "trustdoc"):
            forwarded = subprocess.run(
                [
                    os.path.join(
                        bin_root,
                        bootstrap.STAGE0_LEGACY_TARGO_BACKEND_DIR,
                        compiler_tool,
                    )
                ],
                check=True,
                text=True,
                stdout=subprocess.PIPE,
            ).stdout
            self.assertEqual(forwarded, compiler_tool + "\n")
        for legacy in (
            "tcargo",
            "tcargo-trust",
            "tcargo-fmt",
            "cargo-trust",
            "cargo-fmt",
            "rustfmt",
            "rustdoc",
            "rust-analyzer",
        ):
            self.assertFalse(os.path.exists(os.path.join(bin_dir, legacy)))
        self.assertFalse(
            os.path.exists(
                os.path.join(libexec_dir, "rust-analyzer-proc-macro-srv")
            )
        )
        self.assertTrue(
            os.path.exists(
                os.path.join(libexec_dir, "trust-analyzer-proc-macro-srv")
            )
        )

    @unittest.skipIf(bootstrap.platform_is_win32(), "legacy pin is Unix-only")
    def test_legacy_stage0_tippy_payload_is_semantically_translated_without_alias_leaves(self):
        bin_root = os.path.join(self.container, "stage0")
        bin_dir = os.path.join(bin_root, "bin")
        os.makedirs(bin_dir)
        legacy_names = ("trust-clippy", "cargo-clippy", "trust-clippy-driver", "clippy-driver")
        frontend = """#!/bin/sh
printf '%s\n' "$@" >"$TIPPY_ARG_LOG"
case "$0" in
  */*) frontend_dir=${0%/*} ;;
  *) frontend_dir=. ;;
esac
test -x "$frontend_dir/trust-clippy-driver" || exit 97
"$frontend_dir/trust-clippy-driver" --frontend-probe
"$CARGO" --frontend-cargo-probe
case " $* " in
  *" --version "*|*" -V "*|*" -vV "*|*" -Vv "*)
    printf 'cargo-clippy 0.1.0\nbinary: cargo-clippy\n'
    ;;
esac
"""
        for name in ("trust-clippy", "cargo-clippy"):
            path = os.path.join(bin_dir, name)
            with open(path, "w", encoding="utf-8") as tool:
                tool.write(frontend)
            os.chmod(path, 0o755)
        driver = """#!/bin/sh
case " $* " in
  *" -vV "*|*" -Vv "*)
    printf 'rustc 1.96.0\nbinary: rustc\nhost: test-host\n'
    ;;
  *" --version "*|*" -V "*)
    printf 'clippy-driver 0.1.0\nbinary: clippy-driver\n'
    ;;
  *) printf '%s\n' "$@" >"$TIPPY_DRIVER_ARG_LOG" ;;
esac
"""
        for name in ("trust-clippy-driver", "clippy-driver"):
            path = os.path.join(bin_dir, name)
            with open(path, "w", encoding="utf-8") as tool:
                tool.write(driver)
            os.chmod(path, 0o755)
        canonical_targo = os.path.join(bin_dir, "targo")
        with open(canonical_targo, "w", encoding="utf-8") as tool:
            tool.write(
                '#!/bin/sh\nif [ -n "${TIPPY_TARGO_ARG_LOG-}" ]; then\n'
                '    printf \'%s\\n\' "$@" >"$TIPPY_TARGO_ARG_LOG"\nfi\n'
            )
        os.chmod(canonical_targo, 0o755)

        bootstrap.translate_legacy_tippy_stage0_surface(bin_root)

        arg_log = os.path.join(self.container, "tippy-args.log")
        driver_arg_log = os.path.join(self.container, "tippy-driver-args.log")
        targo_arg_log = os.path.join(self.container, "tippy-targo-args.log")
        ambient_cargo_sentinel = os.path.join(self.container, "ambient-cargo-was-used")
        ambient_cargo = os.path.join(self.container, "ambient-cargo")
        with open(ambient_cargo, "w", encoding="utf-8") as tool:
            tool.write('#!/bin/sh\nprintf used >"$TIPPY_CARGO_SENTINEL"\nexit 98\n')
        os.chmod(ambient_cargo, 0o755)
        env = dict(
            os.environ,
            TIPPY_ARG_LOG=arg_log,
            TIPPY_DRIVER_ARG_LOG=driver_arg_log,
            TIPPY_TARGO_ARG_LOG=targo_arg_log,
            TIPPY_CARGO_SENTINEL=ambient_cargo_sentinel,
            CARGO=ambient_cargo,
        )
        subprocess.run([os.path.join(bin_dir, "tippy"), "--workspace"], env=env, check=True)
        with open(arg_log, encoding="utf-8") as log:
            self.assertEqual(log.read().splitlines(), ["clippy", "--workspace"])
        with open(driver_arg_log, encoding="utf-8") as log:
            self.assertEqual(log.read().splitlines(), ["--frontend-probe"])
        with open(targo_arg_log, encoding="utf-8") as log:
            self.assertEqual(log.read().splitlines(), ["--frontend-cargo-probe"])
        self.assertFalse(os.path.exists(ambient_cargo_sentinel))
        subprocess.run(
            [os.path.join(bin_dir, "targo-tippy"), "tippy", "--all-targets"],
            env=env,
            check=True,
        )
        with open(arg_log, encoding="utf-8") as log:
            self.assertEqual(log.read().splitlines(), ["clippy", "--all-targets"])

        subprocess.run(
            [os.path.join(bin_dir, "tippy-driver"), "--edition", "2024", "input.rs"],
            env=env,
            check=True,
        )
        with open(driver_arg_log, encoding="utf-8") as log:
            self.assertEqual(log.read().splitlines(), ["--edition", "2024", "input.rs"])

        malicious_path = os.path.join(self.container, "malicious-path")
        os.makedirs(malicious_path)
        sed_sentinel = os.path.join(self.container, "ambient-sed-was-used")
        with open(os.path.join(malicious_path, "sed"), "w", encoding="utf-8") as tool:
            tool.write(
                "#!/bin/sh\n"
                "printf used >\"$TIPPY_SED_SENTINEL\"\n"
                "exit 99\n"
            )
        os.chmod(os.path.join(malicious_path, "sed"), 0o755)
        env["PATH"] = os.pathsep.join((bin_dir, malicious_path))
        env["TIPPY_SED_SENTINEL"] = sed_sentinel

        version_queries = (
            ("--version",),
            ("-V",),
            ("-vV",),
            ("-Vv",),
            ("--version", "--verbose"),
            ("--verbose", "--version"),
        )
        for query in version_queries:
            for name, marker in (
                ("tippy", ()),
                ("targo-tippy", ("tippy",)),
                ("tippy-driver", ()),
            ):
                output = subprocess.run(
                    [os.path.join(bin_dir, name), *marker, *query],
                    env=env,
                    check=True,
                    text=True,
                    stdout=subprocess.PIPE,
                ).stdout
                if name == "tippy-driver" and query in (("-vV",), ("-Vv",)):
                    self.assertTrue(output.startswith("rustc "), (name, query, output))
                    self.assertIn("binary: rustc\n", output)
                else:
                    self.assertTrue(output.startswith("tippy "), (name, query, output))
                    self.assertIn("binary: {}\n".format(name), output)
        path_output = subprocess.run(
            ["tippy", "--version"],
            cwd=self.container,
            env=env,
            check=True,
            text=True,
            stdout=subprocess.PIPE,
        ).stdout
        self.assertTrue(path_output.startswith("tippy "), path_output)
        self.assertFalse(os.path.exists(sed_sentinel))
        self.assertTrue(
            os.path.exists(
                os.path.join(bin_root, "libexec", bootstrap.STAGE0_TIPPY_BACKEND)
            )
        )
        self.assertTrue(
            os.path.exists(
                os.path.join(
                    bin_root, "libexec", bootstrap.STAGE0_TIPPY_DRIVER_BACKEND
                )
            )
        )
        for name in legacy_names:
            self.assertFalse(os.path.exists(os.path.join(bin_dir, name + bootstrap.EXE_SUFFIX)))
        for private_protocol in ("trust-clippy-driver", "clippy-driver"):
            self.assertTrue(
                os.path.isfile(os.path.join(bin_root, "libexec", private_protocol))
            )

    def test_get_diagnoses_stage0_checksum_metadata_miss_without_upstream_text(self):
        base = Path(os.path.join(self.container, "trust-stage0")).as_uri()
        payload = "dist/2026-04-24/targo-1.96.0-trust-aarch64-apple-darwin.tar.xz"

        with self.assertRaises(RuntimeError) as ctx:
            bootstrap.get(base, payload, self.dst, {}, verbose=False)

        message = str(ctx.exception)
        self.assertIn("src/stage0 does not contain a checksum", message)
        self.assertIn("Trust stage0 payload", message)
        self.assertIn("dist_server={}".format(base), message)
        self.assertIn("payload={}".format(payload), message)
        self.assertNotIn("Pre-built artifacts", message)
        self.assertNotIn("rust-lang.org", message)


class ProgramOutOfDate(unittest.TestCase):
    """Test if a program is out of date"""

    def setUp(self):
        self.container = tempfile.mkdtemp()
        os.mkdir(os.path.join(self.container, "stage0"))
        self.build = bootstrap.RustBuild()
        self.build.date = "2017-06-15"
        self.build.build_dir = self.container
        self.rustc_stamp_path = os.path.join(self.container, "stage0", ".rustc-stamp")
        self.key = self.build.date + str(None)

    def tearDown(self):
        rmtree(self.container)

    def test_stamp_path_does_not_exist(self):
        """Return True when the stamp file does not exist"""
        if os.path.exists(self.rustc_stamp_path):
            os.unlink(self.rustc_stamp_path)
        self.assertTrue(self.build.program_out_of_date(self.rustc_stamp_path, self.key))

    def test_dates_are_different(self):
        """Return True when the dates are different"""
        with open(self.rustc_stamp_path, "w") as rustc_stamp:
            rustc_stamp.write("2017-06-14None")
        self.assertTrue(self.build.program_out_of_date(self.rustc_stamp_path, self.key))

    def test_same_dates(self):
        """Return False both dates match"""
        with open(self.rustc_stamp_path, "w") as rustc_stamp:
            rustc_stamp.write("2017-06-15None")
        self.assertFalse(
            self.build.program_out_of_date(self.rustc_stamp_path, self.key)
        )


class ParseArgsInConfigure(unittest.TestCase):
    """Test if `parse_args` function in `configure.py` works properly"""

    @patch("configure.err")
    def test_unknown_args(self, err):
        # It should be print an error message if the argument doesn't start with '--'
        configure.parse_args(["enable-full-tools"])
        err.assert_called_with("Option 'enable-full-tools' is not recognized")
        err.reset_mock()
        # It should be print an error message if the argument is not recognized
        configure.parse_args(["--some-random-flag"])
        err.assert_called_with("Option '--some-random-flag' is not recognized")

    @patch("configure.err")
    def test_need_value_args(self, err):
        """It should print an error message if a required argument value is missing"""
        configure.parse_args(["--target"])
        err.assert_called_with("Option '--target' needs a value (--target=val)")

    @patch("configure.err")
    def test_option_checking(self, err):
        # Options should be checked even if `--enable-option-checking` is not passed
        configure.parse_args(["--target"])
        err.assert_called_with("Option '--target' needs a value (--target=val)")
        err.reset_mock()
        # Options should be checked if `--enable-option-checking` is passed
        configure.parse_args(["--enable-option-checking", "--target"])
        err.assert_called_with("Option '--target' needs a value (--target=val)")
        err.reset_mock()
        # Options should not be checked if `--disable-option-checking` is passed
        configure.parse_args(["--disable-option-checking", "--target"])
        err.assert_not_called()

    @patch("configure.parse_example_config", lambda known_args, _: known_args)
    def test_known_args(self):
        # It should contain known and correct arguments
        known_args = configure.parse_args(["--enable-full-tools"])
        self.assertTrue(known_args["full-tools"][0][1])
        known_args = configure.parse_args(["--disable-full-tools"])
        self.assertFalse(known_args["full-tools"][0][1])
        # It should contain known arguments and their values
        known_args = configure.parse_args(["--target=x86_64-unknown-linux-gnu"])
        self.assertEqual(known_args["target"][0][1], "x86_64-unknown-linux-gnu")
        known_args = configure.parse_args(["--target", "x86_64-unknown-linux-gnu"])
        self.assertEqual(known_args["target"][0][1], "x86_64-unknown-linux-gnu")


class GenerateAndParseConfig(unittest.TestCase):
    """Test that we can serialize and deserialize a bootstrap.toml file"""

    def test_no_args(self):
        build = serialize_and_parse([])
        self.assertEqual(build.get_toml("profile"), "dist")
        self.assertIsNone(build.get_toml("llvm.download-ci-llvm"))

    def test_local_trust_root_uses_cargo_compatibility_identity(self):
        build = serialize_and_parse(["--local-rust-root=/opt/trust"])
        self.assertEqual(build.get_toml("rustc", section="build"), "/opt/trust/bin/trustc")
        self.assertEqual(build.get_toml("cargo", section="build"), "/opt/trust/bin/cargo")

    def test_set_section(self):
        build = serialize_and_parse(["--set", "llvm.download-ci-llvm"])
        self.assertEqual(build.get_toml("download-ci-llvm", section="llvm"), "true")

    def test_set_target(self):
        build = serialize_and_parse(["--set", "target.x86_64-unknown-linux-gnu.cc=gcc"])
        self.assertEqual(
            build.get_toml("cc", section="target.x86_64-unknown-linux-gnu"), "gcc"
        )

    def test_set_top_level(self):
        build = serialize_and_parse(["--set", "profile=compiler"])
        self.assertEqual(build.get_toml("profile"), "compiler")

    def test_set_codegen_backends(self):
        build = serialize_and_parse(["--set", "rust.codegen-backends=trust-cg"])
        self.assertNotEqual(
            build.config_toml.find("codegen-backends = ['trust-cg']"), -1
        )
        build = serialize_and_parse(["--set", "rust.codegen-backends=trust-cg,llvm"])
        self.assertNotEqual(
            build.config_toml.find("codegen-backends = ['trust-cg', 'llvm']"), -1
        )
        build = serialize_and_parse(["--enable-full-tools"])
        self.assertNotEqual(build.config_toml.find("codegen-backends = ['llvm']"), -1)


class GetTomlDottedKeys(unittest.TestCase):
    """Test that get_toml understands the dotted-table key syntax that a
    hand-written bootstrap.toml may use (e.g. `build.cargo = "..."`), and that
    it checks the table a key belongs to. See issue #156948."""

    def parse(self, config_toml):
        return bootstrap.RustBuild(config_toml=config_toml, args=bootstrap.FakeArgs())

    def test_dotted_key(self):
        build = self.parse('build.cargo = "/path/to/cargo"')
        self.assertEqual(build.get_toml("cargo", "build"), "/path/to/cargo")

    def test_dotted_key_matches_section_form(self):
        dotted = self.parse('build.cargo = "/path/to/cargo"')
        section = self.parse('[build]\ncargo = "/path/to/cargo"')
        self.assertEqual(
            dotted.get_toml("cargo", "build"), section.get_toml("cargo", "build")
        )

    def test_dotted_key_wrong_section(self):
        # A `cargo` key in some other table must not be picked up for `build`.
        build = self.parse('[foo]\ncargo = "false"')
        self.assertIsNone(build.get_toml("cargo", "build"))

    def test_program_config_requires_build_table(self):
        # A cargo/rustc key outside [build] must be ignored; program_config
        # falls back to the stage0 default path — Trust's bootstrap-safe
        # compatibility name (STAGE0_PROGRAM_NAMES) — rather than the
        # misplaced value.
        wrong = self.parse('[foo]\ncargo = "/wrong/cargo"')
        cargo_default = os.path.join(
            wrong.bin_root(),
            "bin",
            bootstrap.STAGE0_PROGRAM_NAMES["cargo"] + bootstrap.EXE_SUFFIX,
        )
        self.assertEqual(wrong.cargo(), cargo_default)
        self.assertEqual(os.path.basename(cargo_default), "cargo" + bootstrap.EXE_SUFFIX)

        wrong_rustc = self.parse('[foo]\nrustc = "/wrong/rustc"')
        rustc_default = os.path.join(
            wrong_rustc.bin_root(),
            "bin",
            bootstrap.STAGE0_PROGRAM_NAMES["rustc"] + bootstrap.EXE_SUFFIX,
        )
        self.assertEqual(wrong_rustc.rustc(), rustc_default)

        # A dotted key in the build table is honored.
        right = self.parse('build.cargo = "/path/to/cargo"')
        self.assertEqual(right.cargo(), "/path/to/cargo")

    def test_dotted_target_key(self):
        build = self.parse('target.x86_64-unknown-linux-gnu.cc = "gcc"')
        self.assertEqual(build.get_toml("cc", "target.x86_64-unknown-linux-gnu"), "gcc")

    def test_dotted_key_inside_section(self):
        # A dotted key nested under a `[section]` header composes with that
        # section's name; it is equivalent to the fully top-level dotted form.
        nested = self.parse('[target]\nx86_64-unknown-linux-gnu.cc = "gcc"')
        self.assertEqual(
            nested.get_toml("cc", "target.x86_64-unknown-linux-gnu"), "gcc"
        )
        top_level = self.parse('target.x86_64-unknown-linux-gnu.cc = "gcc"')
        self.assertEqual(
            nested.get_toml("cc", "target.x86_64-unknown-linux-gnu"),
            top_level.get_toml("cc", "target.x86_64-unknown-linux-gnu"),
        )

    def test_dotted_prefix_does_not_alias_other_section(self):
        # `build.cargo` inside `[foo]` is `foo.build.cargo`, not the top-level
        # `[build]` table, so it must not be returned for section "build".
        build = self.parse('[foo]\nbuild.cargo = "false"')
        self.assertIsNone(build.get_toml("cargo", "build"))


class BuildBootstrap(unittest.TestCase):
    """Test that we generate the appropriate arguments when building bootstrap"""

    def build_args(self, configure_args=None, args=None, env=None):
        if configure_args is None:
            configure_args = []
        if args is None:
            args = []
        if env is None:
            env = {}

        # This test ends up invoking build_bootstrap_cmd, which searches for
        # the Cargo binary and errors out if it cannot be found. This is not a
        # problem in most cases, but there is a scenario where it would cause
        # the test to fail.
        #
        # When a custom local Cargo is configured in bootstrap.toml (with the
        # build.cargo setting), no Cargo is downloaded to any location known by
        # bootstrap, and bootstrap relies on that setting to find it.
        #
        # In this test though we are not using the bootstrap.toml of the caller:
        # we are generating a blank one instead. If we don't set build.cargo in
        # it, the test will have no way to find Cargo, failing the test.
        cargo_bin = os.environ.get("BOOTSTRAP_TEST_CARGO_BIN")
        if cargo_bin is not None:
            configure_args += ["--set", "build.cargo=" + cargo_bin]
        rustc_bin = os.environ.get("BOOTSTRAP_TEST_RUSTC_BIN")
        if rustc_bin is not None:
            configure_args += ["--set", "build.rustc=" + rustc_bin]

        env = env.copy()
        env["PATH"] = os.environ["PATH"]

        parsed = bootstrap.parse_args(args)
        build = serialize_and_parse(configure_args, parsed)
        # Make these optional so that `python -m unittest` works when run manually.
        build_dir = os.environ.get("BUILD_DIR")
        if build_dir is not None:
            build.build_dir = build_dir
        build_platform = os.environ.get("BUILD_PLATFORM")
        if build_platform is not None:
            build.build = build_platform
        return build.build_bootstrap_cmd(env), env

    def test_cargoflags(self):
        args, _ = self.build_args(env={"CARGOFLAGS": "--timings"})
        self.assertTrue("--timings" in args)

    def test_warnings(self):
        for toml_warnings in ["false", "true", None]:
            configure_args = []
            if toml_warnings is not None:
                configure_args = ["--set", "rust.deny-warnings=" + toml_warnings]

            args, env = self.build_args(configure_args, args=["--warnings=warn"])
            self.assertFalse("CARGO_BUILD_WARNINGS" in env)

            args, env = self.build_args(configure_args, args=["--warnings=deny"])
            self.assertEqual("deny", env["CARGO_BUILD_WARNINGS"])


class TrustBootstrapCompilerPolicy(unittest.TestCase):
    def test_stock_driver_is_left_untouched(self):
        env = {"RUSTFLAGS_BOOTSTRAP": "-Zthreads=2"}
        with patch.object(
            bootstrap, "rustc_supports_trust_bootstrap_no_verify", return_value=False
        ):
            self.assertFalse(bootstrap.apply_trust_bootstrap_compiler_policy("rustc", env))
        self.assertEqual(env, {"RUSTFLAGS_BOOTSTRAP": "-Zthreads=2"})

    def test_trust_driver_gets_exact_flag_in_plain_and_encoded_lanes(self):
        env = {
            "RUSTFLAGS_BOOTSTRAP": "-Zthreads=2",
            "CARGO_ENCODED_RUSTFLAGS": "-Cdebuginfo=0",
        }
        with patch.object(
            bootstrap, "rustc_supports_trust_bootstrap_no_verify", return_value=True
        ):
            self.assertTrue(bootstrap.apply_trust_bootstrap_compiler_policy("trustc", env))
        self.assertEqual(
            env["RUSTFLAGS_BOOTSTRAP"], "-Zthreads=2 -Ztrust-verify=off"
        )
        self.assertEqual(
            env["CARGO_ENCODED_RUSTFLAGS"],
            "-Cdebuginfo=0\x1f-Ztrust-verify=off",
        )

    def test_conflicting_verifier_controls_are_rejected(self):
        for name, value in (
            ("RUSTFLAGS", "-Ztrust-verify-full"),
            ("RUSTFLAGS_BOOTSTRAP", "-Ztrust-verify=on"),
            ("CARGO_ENCODED_RUSTFLAGS", "-Cdebuginfo=0\x1f-Ztrust-policy=advisory"),
        ):
            with self.subTest(name=name), patch.object(
                bootstrap, "rustc_supports_trust_bootstrap_no_verify", return_value=True
            ):
                with self.assertRaises(RuntimeError):
                    bootstrap.apply_trust_bootstrap_compiler_policy(
                        "trustc", {name: value}
                    )

    def test_capability_probe_requires_successful_exact_help_surface(self):
        supported = subprocess.CompletedProcess(
            ["trustc", "-Z", "help"], 0, stdout="-Z trust-verify=val"
        )
        unsupported = subprocess.CompletedProcess(
            ["rustc", "-Z", "help"], 0, stdout="-Z threads=val"
        )
        spoofed = subprocess.CompletedProcess(
            ["rustc", "-Z", "help"],
            0,
            stdout="note: trust-verify is unsupported\n-Z trust-verify-extra=val",
        )
        with patch.object(bootstrap.subprocess, "run", return_value=supported):
            self.assertTrue(
                bootstrap.rustc_supports_trust_bootstrap_no_verify("trustc", {})
            )
        with patch.object(bootstrap.subprocess, "run", return_value=unsupported):
            self.assertFalse(
                bootstrap.rustc_supports_trust_bootstrap_no_verify("rustc", {})
            )
        with patch.object(bootstrap.subprocess, "run", return_value=spoofed):
            self.assertFalse(
                bootstrap.rustc_supports_trust_bootstrap_no_verify("rustc", {})
            )

    def test_runtime_driver_inherits_the_same_capability_gated_policy(self):
        base = {"RUSTFLAGS_BOOTSTRAP": "-Zthreads=2", "UNRELATED": "preserved"}
        with patch.object(
            bootstrap, "rustc_supports_trust_bootstrap_no_verify", return_value=True
        ):
            env = bootstrap.bootstrap_runtime_env("trustc", base)
        self.assertEqual(
            env["RUSTFLAGS_BOOTSTRAP"], "-Zthreads=2 -Ztrust-verify=off"
        )
        self.assertEqual(env["UNRELATED"], "preserved")
        self.assertEqual(env["BOOTSTRAP_PYTHON"], sys.executable)
        self.assertEqual(
            base,
            {"RUSTFLAGS_BOOTSTRAP": "-Zthreads=2", "UNRELATED": "preserved"},
        )
