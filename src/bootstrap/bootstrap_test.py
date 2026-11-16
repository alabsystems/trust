"""Bootstrap tests

Run these with `x test bootstrap`, or `python -m unittest src/bootstrap/bootstrap_test.py`."""

from __future__ import absolute_import, division, print_function
import io
import json
import os
import subprocess
import shlex
import tarfile
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


class UnpackProjectionTestCase(unittest.TestCase):
    def test_public_unpack_uses_exact_component_segments_and_shared_projection(self):
        with tempfile.TemporaryDirectory() as directory:
            archive = Path(directory) / 'fixture.tar.xz'
            destination = Path(directory) / 'seed'; destination.mkdir()
            with tarfile.open(archive, 'w:xz') as bundle:
                for name, raw in (('trustc/manifest.in', b'file:bin/trustc\n'),
                                  ('trustc/bin/trustc', b'compiler'),
                                  ('trustc-preview/bin/decoy', b'decoy')):
                    member = tarfile.TarInfo('fixture/' + name); member.size = len(raw)
                    bundle.addfile(member, io.BytesIO(raw))
            with patch.object(bootstrap._identity_owner, 'component_projection',
                              wraps=bootstrap._identity_owner.component_projection) as shared:
                bootstrap.unpack(str(archive), '.tar.xz', str(destination), match='trustc')
            self.assertEqual((destination / 'bin/trustc').read_bytes(), b'compiler')
            self.assertFalse((destination / 'bin/decoy').exists())
            self.assertFalse((destination / 'manifest.in').exists())
            self.assertEqual(shared.call_count, 3)

    def test_projection_rejects_noncanonical_roots_selectors_and_member_paths(self):
        project = bootstrap._identity_owner.component_projection
        for name, top, component in (('../fixture/trustc/bin/a', 'fixture', 'trustc'),
                                     ('fixture/trustc/bin/a', '../fixture', 'trustc'),
                                     ('fixture/trustc/bin/a', 'fixture', '../trustc'),
                                     ('fixture/trustc/../bin/a', 'fixture', 'trustc'),
                                     ('other/trustc/bin/a', 'fixture', 'trustc')):
            with self.assertRaises(ValueError):
                project(name, top, component)


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
        # is fetched from the seed-ledger-declared agh release before failing,
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
        args_log = os.path.join(self.container, "agh-args")
        agh = os.path.join(self.container, "fake-agh")
        with open(agh, "w") as shim:
            # argv: release download REPO TAG --asset FILE --dir DIR
            shim.write(
                "#!/bin/sh\n"
                'echo "$@" > "{}"\n'.format(args_log) + 'printf seeded > "$8/$6"\n'
            )
        os.chmod(agh, 0o755)

        seeded_sha256 = hashlib.sha256(b"seeded").hexdigest()
        # A wrong pin must refuse to place ANY file at the pinned path — the
        # digest-pinned dist root only ever holds verified bytes.
        self.assertFalse(
            bootstrap.try_materialize_trust_seed_payload(
                resolved, "0" * 64, agh=agh, repo_root=root
            )
        )
        self.assertFalse(os.path.exists(resolved))

        self.assertTrue(
            bootstrap.try_materialize_trust_seed_payload(
                resolved, seeded_sha256, agh=agh, repo_root=root
            )
        )
        with open(resolved) as payload:
            self.assertEqual(payload.read(), "seeded")
        with open(args_log) as recorded:
            args = recorded.read().split()
        self.assertEqual(
            args[:4], ["release", "download", "example/trust", "trust-stage0-2026-04-24"]
        )
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
                agh="/nonexistent-agh",
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


class ConfigIncludes(unittest.TestCase):
    """bootstrap.py reads a config's `include` chain as config.rs merges it: the
    pack cut's generated configs override a few keys and include bootstrap.toml,
    and bootstrap was built with `rust.deny-warnings` unread (2026-10-22)."""

    def setUp(self):
        self.dir = tempfile.mkdtemp()

    def tearDown(self):
        rmtree(self.dir)

    def write(self, name, text):
        path = os.path.join(self.dir, name)
        os.makedirs(os.path.dirname(path), exist_ok=True)
        with open(path, "w", encoding="utf-8") as handle:
            handle.write(text)
        return path

    def load(self, path):
        with open(path, encoding="utf-8") as handle:
            text = bootstrap.config_with_includes(handle.read(), path)
        return bootstrap.RustBuild(config_toml=text, args=bootstrap.FakeArgs())

    def test_a_generated_config_reads_the_included_checkout_config(self):
        source = self.write(
            "checkout/bootstrap.toml",
            'profile = "compiler"\n[build]\nrustc = "/seed/rustc"\n'
            "[rust]\ndeny-warnings = false\n",
        )
        generated = self.write(
            "work/bootstrap.ddc.toml",
            "include = [{}]\n\n[build]\nrustc = \"/ddc/rustc\"\n\n[rust]\n"
            'channel = "trust"\n'.format(json.dumps(source)),
        )
        build = self.load(generated)
        self.assertEqual(build.get_toml("deny-warnings", "rust"), "false")
        # The including config's own key wins over the included one.
        self.assertEqual(build.get_toml("rustc", "build"), "/ddc/rustc")
        self.assertEqual(build.get_toml("profile"), "compiler")

    def test_precedence_and_relative_paths_follow_the_rust_loader(self):
        self.write("a.toml", '[build]\njobs = "1"\nverbose = "1"\nvendor = true\n')
        self.write("b.toml", 'include = ["sub/c.toml"]\n[build]\njobs = "2"\n')
        self.write("sub/c.toml", '[build]\njobs = "3"\nverbose = "3"\nlocked-deps = true\n')
        main = self.write(
            "main.toml",
            "include = [\n  'a.toml', # the base\n  \"b.toml\",\n]\n[llvm]\nninja = true\n",
        )
        build = self.load(main)
        # The last include beats an earlier one, a file beats its own includes.
        self.assertEqual(build.get_toml("jobs", "build"), "2")
        self.assertEqual(build.get_toml("verbose", "build"), "3")
        self.assertEqual(build.get_toml("vendor", "build"), "true")
        self.assertEqual(build.get_toml("locked-deps", "build"), "true")

    def test_an_included_top_level_key_is_not_read_into_the_last_section(self):
        self.write("base.toml", 'deny-warnings = "top"\n')
        main = self.write("main.toml", 'include = ["base.toml"]\n[rust]\nchannel = "trust"\n')
        self.assertIsNone(self.load(main).get_toml("deny-warnings", "rust"))

    def test_quoted_comments_are_not_included_files(self):
        # Trust: comments may quote names and brackets, while a real filename may
        # contain '#'. Only array strings are paths, including on its final line.
        self.write("base # one.toml", '[build]\njobs = "2"\n')
        self.write("second.toml", '[build]\nverbose = "3"\n')
        main = self.write(
            "main.toml",
            'include = [ # "missing-one.toml" ]\n'
            '  "base # one.toml", # \'missing-two.toml\'\n'
            '  \'second.toml\',\n'
            '] # "missing-three.toml"\n',
        )
        build = self.load(main)
        self.assertEqual(build.get_toml("jobs", "build"), "2")
        self.assertEqual(build.get_toml("verbose", "build"), "3")

    def test_no_include_leaves_the_config_alone(self):
        text = '[build]\ninclude-mingw = "x"\n[dist]\ninclude = ["not/top/level"]\n'
        self.assertEqual(bootstrap.config_with_includes(text, self.write("c.toml", text)), text)

    def test_a_cyclic_include_is_refused(self):
        self.write("x.toml", 'include = ["y.toml"]\n')
        y = self.write("y.toml", 'include = ["x.toml"]\n')
        with self.assertRaises(Exception):
            self.load(y)


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

    def build_args(self, configure_args=None, args=None, env=None, policy=None):
        """Assemble the bootstrap command. `policy`, when given, is the side
        effect standing in for the compiler policy (default: a no-op mock)."""
        if configure_args is None:
            configure_args = []
        if args is None:
            args = []
        if env is None:
            env = {}

        env = env.copy()
        env["PATH"] = os.environ["PATH"]

        # This fixture assembles a command, never selects or executes an SDK.
        # Supply a real private regular Cargo input through the normal config;
        # compiler admission and native lane discovery have separate controls.
        with tempfile.TemporaryDirectory() as temporary:
            cargo = Path(temporary) / "NONEXECUTED.targo"
            cargo.touch()
            configure_args = list(configure_args) + ["--set", "build.cargo=" + str(cargo)]
            parsed = bootstrap.parse_args(args)
            build = serialize_and_parse(configure_args, parsed)
            build_dir = os.environ.get("BUILD_DIR")
            if build_dir is not None:
                build.build_dir = build_dir
            build_platform = os.environ.get("BUILD_PLATFORM")
            if build_platform is not None:
                build.build = build_platform
            with (
                patch.object(build, "bootstrap_rustc", return_value="NONEXECUTED.rustc"),
                patch.object(build, "targo_supports_unverified_lane", return_value=True),
                patch.object(bootstrap, "apply_trust_bootstrap_compiler_policy",
                             side_effect=policy),
            ):
                return build.build_bootstrap_cmd(env), env

    def test_cargoflags(self):
        args, _ = self.build_args(env={"CARGOFLAGS": "--timings"})
        self.assertTrue("--timings" in args)

    # Trust: the seed request itself enforces locks/offline, independently of
    # configuration and any earlier readiness diagnostic.
    def test_bootstrap_producer_is_always_frozen(self):
        for locked in ("false", "true"):
            for vendor in ("false", "true"):
                with self.subTest(locked=locked, vendor=vendor):
                    args, _ = self.build_args(
                        configure_args=["--set", "build.locked-deps=" + locked,
                                        "--set", "build.vendor=" + vendor],
                        env={"CARGO_NET_OFFLINE": "false"})
                    self.assertEqual(args.count("--frozen"), 1)
                    self.assertEqual("--locked" in args, locked == "true")

    def build(self, configure_args=None):
        configure_args = list(configure_args or [])
        cargo_bin = os.environ.get("BOOTSTRAP_TEST_CARGO_BIN")
        if cargo_bin is not None:
            configure_args += ["--set", "build.cargo=" + cargo_bin]
        rustc_bin = os.environ.get("BOOTSTRAP_TEST_RUSTC_BIN")
        if rustc_bin is not None:
            configure_args += ["--set", "build.rustc=" + rustc_bin]
        build = serialize_and_parse(configure_args, bootstrap.parse_args([]))
        build_dir = os.environ.get("BUILD_DIR")
        if build_dir is not None:
            build.build_dir = build_dir
        return build

    # Trust: these are the producer's native fetch commands, not a Python
    # prediction of the dependency envelope for the eventual native request.
    def frozen_hint_commands(self, build, env):
        hint = build.frozen_source_hint(env)
        lines = hint.splitlines()
        self.assertEqual(len(lines), 3)
        commands = []
        for line in lines[1:]:
            argv = shlex.split(line)
            self.assertEqual(argv[:3], ["cd", os.path.abspath(build.rust_root), "&&"])
            commands.append(argv[3:])
        self.assertNotIn("bootstrap_dependency_closure.py", hint)
        self.assertIn("does not prepare the full toolchain", hint)
        return commands

    def test_frozen_failure_names_only_the_selected_bootstrap_manifest(self):
        for driver, selected in (("seed tools/targo", "/source root/seed tools/targo"),
                                 ("/seed tools/cargo", "/seed tools/cargo"),
                                 ("targo", "targo")):
            with self.subTest(driver=driver):
                build = self.build()
                build.rust_root = "/source root"
                build.config_toml = '[build]\ncargo = "{}"\n'.format(driver)
                env = {"CARGO_HOME": "/cargo home", "CARGO_BUILD_WARNINGS": "deny"}
                online, offline = self.frozen_hint_commands(build, env)
                expected = [
                    "env", "-u", "CARGO_BUILD_WARNINGS", "-u", "TARGO_BUILD_WARNINGS",
                    "-u", "CARGO_NET_OFFLINE", "CARGO_HOME=/cargo home",
                    "CARGO_BUILD_WARNINGS=deny", selected,
                    "fetch", "--locked", "--manifest-path",
                    "/source root/src/bootstrap/Cargo.toml",
                ]
                self.assertEqual(online, expected)
                self.assertEqual(offline, expected + ["--offline"])

    def test_frozen_failure_binds_relative_paths_and_default_cargo_home(self):
        build = self.build()
        build.rust_root = "relative source"
        build.config_toml = '[build]\ncargo = "seed tools/targo"\n'
        root = os.path.abspath(build.rust_root)
        for home, expected_home in (
            ("private home", os.path.join(root, "private home")),
            (None, os.path.join(os.path.expanduser("~"), ".cargo")),
        ):
            with self.subTest(home=home):
                env = {} if home is None else {"CARGO_HOME": home}
                online, offline = self.frozen_hint_commands(build, env)
                self.assertIn("CARGO_HOME=" + expected_home, online)
                self.assertEqual(online[-5:], [os.path.join(root, "seed tools/targo"),
                                              "fetch", "--locked", "--manifest-path",
                                              os.path.join(root, "src/bootstrap/Cargo.toml")])
                self.assertEqual(offline, online + ["--offline"])

    def test_frozen_failure_preserves_warning_and_caller_offline_policy(self):
        build = self.build()
        for policy in ({}, {"CARGO_BUILD_WARNINGS": "deny"},
                       {"TARGO_BUILD_WARNINGS": "", "CARGO_NET_OFFLINE": "true"},
                       {"CARGO_BUILD_WARNINGS": "warn", "TARGO_BUILD_WARNINGS": "deny",
                        "CARGO_NET_OFFLINE": "false"}):
            with self.subTest(policy=policy):
                online, offline = self.frozen_hint_commands(build, policy)
                for key in ("CARGO_BUILD_WARNINGS", "TARGO_BUILD_WARNINGS",
                            "CARGO_NET_OFFLINE"):
                    self.assertIn(["-u", key], [online[i:i + 2]
                                               for i in range(len(online) - 1)])
                    values = [part for part in online if part.startswith(key + "=")]
                    self.assertEqual(values, [key + "=" + policy[key]] if key in policy else [])
                self.assertEqual(offline, online + ["--offline"])

    def test_vendored_frozen_failure_names_vendor_not_the_cargo_home(self):
        build = self.build()
        build.use_vendored_sources = True
        hint = build.frozen_source_hint({"CARGO_HOME": "/cargo home"})
        self.assertIn("x.py vendor", hint)
        self.assertNotIn("bootstrap_dependency_closure.py", hint)
        self.assertNotIn(" fetch ", hint)

    def test_frozen_failure_prints_the_hint_and_exits(self):
        build = self.build()
        calls = []

        def producer_args(env):
            env["CARGO_HOME"] = "/failed producer home"
            env["TARGO_BUILD_WARNINGS"] = "deny"
            env["CARGO_NET_OFFLINE"] = "true"
            return [build.cargo(), "build", "--frozen"]

        def failing_run(args, **kwargs):
            calls.append((args, kwargs))
            raise RuntimeError("failed to run: cargo build --frozen")

        stderr = io.StringIO()
        with patch.object(bootstrap, "run", failing_run), \
                patch.object(build, "build_bootstrap_cmd", producer_args), \
                patch.object(sys, "stderr", stderr):
            with self.assertRaises(SystemExit) as exit:
                build.build_bootstrap()
        self.assertEqual(str(exit.exception), "failed to run: cargo build --frozen")
        self.assertEqual(len(calls), 1)
        self.assertEqual(calls[0][0], [build.cargo(), "build", "--frozen"])
        self.assertTrue(calls[0][1]["exception"])
        self.assertEqual(calls[0][1]["cwd"], build.rust_root)
        self.assertNotIn("bootstrap_dependency_closure.py", stderr.getvalue())
        self.assertIn("fetch --locked --manifest-path", stderr.getvalue())
        self.assertIn("Cargo.toml --offline", stderr.getvalue())
        self.assertEqual(stderr.getvalue().count("'CARGO_HOME=/failed producer home'"), 2)
        self.assertEqual(stderr.getvalue().count("TARGO_BUILD_WARNINGS=deny"), 2)
        self.assertEqual(stderr.getvalue().count("CARGO_NET_OFFLINE=true"), 2)

    def test_warnings(self):
        for toml_warnings in ["false", "true", None]:
            configure_args = []
            if toml_warnings is not None:
                configure_args = ["--set", "rust.deny-warnings=" + toml_warnings]

            args, env = self.build_args(configure_args, args=["--warnings=warn"])
            self.assertFalse("CARGO_BUILD_WARNINGS" in env)

            args, env = self.build_args(configure_args, args=["--warnings=deny"])
            self.assertEqual("deny", env["CARGO_BUILD_WARNINGS"])

    def test_admitted_bootstrap_command_caps_default_toml_and_cli_jobs(self):
        # Only assemble the real command; no seed/compiler/tool probe is needed.
        with (
            patch.object(bootstrap, "get_cpus", return_value=28),
            patch.object(bootstrap, "apply_trust_bootstrap_compiler_policy"),
            patch.object(bootstrap.RustBuild, "bootstrap_rustc", return_value="NONEXECUTED"),
            patch.object(bootstrap.RustBuild, "targo_supports_unverified_lane", return_value=True),
            patch.object(bootstrap.os.path, "isfile", return_value=True),
        ):
            for configured, cli, expected in [
                (None, [], 7), ("28", [], 7), ("2", [], 2), ("0", [], 7),
                ("28", ["--jobs=2"], 2), ("2", ["-j28"], 7),
                ("28", ["--jobs", "0"], 7),
            ]:
                with self.subTest(configured=configured, cli=cli):
                    configure = [] if configured is None else ["--set", "build.jobs=" + configured]
                    args, env = self.build_args(configure, cli, {
                        "BUILD_SLOT_HELD": "1", "CARGO_BUILD_JOBS": "7"
                    })
                    self.assertIn("--jobs=" + str(expected), args)
                    self.assertEqual(env["CARGO_BUILD_JOBS"], "7")

    def test_unflagged_bootstrap_build_allows_only_the_trust_std_features(self):
        # Trust (BOOTSTRAP-SEED-PROBE-ADMISSION-1): every policy branch that
        # leaves RUSTFLAGS empty -- a stock driver, a retired-spelling seed, the
        # unanswered-probe fallback -- gets the allow-list of exactly the Trust
        # std features bootstrap's dependencies select. It was empty, so a Trust
        # seed on the fallback failed trust-resource-controller with E0725.
        def fallback(_rustc, env):
            env["TRUST_NO_VERIFY"] = "1"
            return False

        def answered(_rustc, env):
            env["RUSTFLAGS_BOOTSTRAP"] = "-Ztrust-verify=off"
            return True

        for policy, flags in ((fallback, "-Zallow-features=trust_process_inherit_fds "),
                              (lambda _rustc, _env: False,
                               "-Zallow-features=trust_process_inherit_fds "),
                              (answered, " -Wrust_2018_idioms")):
            with self.subTest(policy=policy):
                _, env = self.build_args(policy=policy)
                self.assertTrue(env["RUSTFLAGS"].startswith(flags), env["RUSTFLAGS"])
                if policy is answered:
                    self.assertNotIn("allow-features", env["RUSTFLAGS"])
                    self.assertTrue(env["RUSTFLAGS"].endswith(" -Ztrust-verify=off"))

    def test_invalid_admitted_share_refuses_before_cleanup_or_tool_probe(self):
        build = bootstrap.RustBuild()
        build.clean = True
        with (
            patch.object(bootstrap.shutil, "rmtree", side_effect=AssertionError("cleaned")),
            patch.object(
                bootstrap.RustBuild, "bootstrap_rustc", side_effect=AssertionError("adapter opened")
            ),
            patch.object(
                bootstrap, "apply_trust_bootstrap_compiler_policy",
                side_effect=AssertionError("tool probed"),
            ),
        ):
            for share in [None, "", "0", "-1", "+7", "7.0", " 7", "７", "4294967296"]:
                with self.subTest(share=share):
                    env = {"BUILD_SLOT_HELD": "1"}
                    if share is not None:
                        env["CARGO_BUILD_JOBS"] = share
                    with self.assertRaisesRegex(RuntimeError, "positive u32 CARGO_BUILD_JOBS"):
                        build.build_bootstrap_cmd(env)

    def test_outside_admission_preserves_python_jobs_semantics(self):
        for marker in [None, "0", "true"]:
            env = {"CARGO_BUILD_JOBS": "invalid"}
            if marker is not None:
                env["BUILD_SLOT_HELD"] = marker
            self.assertEqual(bootstrap.bootstrap_jobs("default", 2, env), "default")
            self.assertEqual(bootstrap.bootstrap_jobs("28", 2, env), "28")


STOCK_Z_HELP = "    -Z threads=val -- use a thread pool with N threads\n"
TRUST_Z_HELP = "    -Z trust-verify=val -- batteries-on verification (on/off)\n"
RETIRED_Z_HELP = "    -Z no-trust-verify=val -- disable batteries-on verification\n"


def completed_z_help(stdout, returncode=0, rustc="rustc"):
    return subprocess.CompletedProcess([rustc, "-Z", "help"], returncode, stdout=stdout)


def z_help_timeout(rustc="rustc"):
    return subprocess.TimeoutExpired([rustc, "-Z", "help"], 10)


class TrustBootstrapCompilerPolicy(unittest.TestCase):
    def setUp(self):
        # Probe answers are memoized per process; every test starts unasked.
        bootstrap.clear_stage0_z_help_cache()
        self.addCleanup(bootstrap.clear_stage0_z_help_cache)
        # Trust: transparent unit-only bridge; no native admission is claimed.
        if os.name == "posix":
            scratch = tempfile.TemporaryDirectory()
            self.addCleanup(scratch.cleanup)
            bridge = Path(scratch.name) / "bridge"
            bridge.write_text('#!/bin/sh\nshift\nexec "$@"\n')
            bridge.chmod(0o700)
            transport = patch.object(bootstrap.bootstrap_serial_owner(),
                                     "managed_serial_executor", return_value=bridge)
            transport.start()
            self.addCleanup(transport.stop)

    def test_applicable_pin_failure_never_queries_or_tries_another_owner(self):
        import seed_compiler_identity
        for error in (seed_compiler_identity.SeedIdentityError("wrong member"),
                      FileNotFoundError("missing archive")):
            with self.subTest(error=type(error).__name__), patch.object(
                    seed_compiler_identity, "pinned_compiler_binding", side_effect=error), \
                    patch.object(bootstrap, "bootstrap_capability_command") as query:
                with self.assertRaisesRegex(RuntimeError, "pinned Stage0 identity unavailable"):
                    bootstrap._probe_stage0_z_help("selected", {})
                query.assert_not_called()

    def test_changed_pinned_compiler_does_not_retry_a_help_answer(self):
        import seed_compiler_identity
        binding = object()
        with patch.object(seed_compiler_identity, "pinned_compiler_binding",
                          return_value=binding), \
                patch.object(seed_compiler_identity, "check_compiler_snapshot", side_effect=[
                    None,
                    seed_compiler_identity.SeedIdentityError("changed after help"),
                ]) as check, \
                patch.object(bootstrap, "bootstrap_capability_command",
                             return_value=completed_z_help(TRUST_Z_HELP)) as query:
            with self.assertRaisesRegex(seed_compiler_identity.SeedIdentityError,
                                        "changed after help"):
                bootstrap._probe_stage0_z_help("selected", {})
            self.assertEqual(check.call_count, 2)
            query.assert_called_once_with(["selected", "-Z", "help"], env={},
                                          timeout=bootstrap.STAGE0_Z_HELP_TIMEOUTS[0], serial=True)

    def test_pinned_help_retry_rechecks_same_compiler_and_exact_query(self):
        import seed_compiler_identity
        binding = object()
        with patch.object(seed_compiler_identity, "pinned_compiler_binding",
                          return_value=binding), \
                patch.object(seed_compiler_identity, "check_compiler_snapshot") as check, \
                patch.object(bootstrap, "bootstrap_capability_command", side_effect=[
                    z_help_timeout("selected"), completed_z_help(TRUST_Z_HELP)]) as query:
            self.assertEqual(bootstrap._probe_stage0_z_help("selected", {"DATA": "kept"}),
                             TRUST_Z_HELP)
            self.assertEqual(check.call_count, 3)
            self.assertEqual([call.args[0] for call in query.call_args_list],
                             [["selected", "-Z", "help"]] * 2)
            self.assertTrue(all(call.kwargs["env"] == {"DATA": "kept"}
                                for call in query.call_args_list))

    def test_nonpinned_help_keeps_the_existing_direct_driver_contract(self):
        import seed_compiler_identity
        with patch.object(seed_compiler_identity, "pinned_compiler_binding", return_value=None), \
                patch.object(seed_compiler_identity, "check_compiler_snapshot") as check, \
                patch.object(bootstrap, "bootstrap_capability_command",
                             return_value=completed_z_help(STOCK_Z_HELP)) as query:
            self.assertEqual(bootstrap._probe_stage0_z_help("stock driver ü", {}), STOCK_Z_HELP)
            check.assert_not_called()
            query.assert_called_once_with(["stock driver ü", "-Z", "help"], env={},
                                          timeout=bootstrap.STAGE0_Z_HELP_TIMEOUTS[0], serial=True)

    def test_windows_help_preserves_direct_query_without_posix_archive_admission(self):
        import seed_compiler_identity
        with patch.object(bootstrap, "platform_is_win32", return_value=True), \
                patch.object(seed_compiler_identity, "pinned_compiler_binding") as admission, \
                patch.object(bootstrap, "bootstrap_capability_command",
                             return_value=completed_z_help(STOCK_Z_HELP)) as query:
            self.assertEqual(
                bootstrap._probe_stage0_z_help("C:/build/host/stage0/bin/rustc.exe", {}),
                STOCK_Z_HELP)
            admission.assert_not_called()
            self.assertEqual(query.call_count, 1)

    def test_refused_or_empty_probe_never_becomes_a_stock_answer(self):
        for code, text in ((75, ""), (75, TRUST_Z_HELP), (0, ""),
                           (1, "permission denied")):
            with self.subTest(code=code, text=text):
                bootstrap.clear_stage0_z_help_cache()
                env = {}
                with patch.object(bootstrap, "bootstrap_capability_command",
                                  return_value=completed_z_help(text, code)) as run:
                    self.assertFalse(bootstrap.apply_trust_bootstrap_compiler_policy("rustc", env))
                    self.assertIsNone(bootstrap.stage0_z_help("rustc", env))
                    self.assertEqual(run.call_count, 1)
                self.assertEqual(env["TRUST_NO_VERIFY"], "1")

    @unittest.skipUnless(os.name == "posix", "original POSIX descriptor transport")
    def test_capability_bridge_preserves_exact_argv_and_original_descriptor(self):
        with tempfile.TemporaryDirectory() as scratch:
            program = Path(scratch) / "probe.py"
            program.write_text(
                'import os,sys,json\n'
                'fds=[int(os.environ["TRUST_CPU_IMPLICIT_FD"])]+'
                '[int(x) for x in os.environ["MAKEFLAGS"].split("=")[1].split(",")]\n'
                'print(json.dumps([sys.argv[1:],[os.fstat(fd).st_ino for fd in fds]]))\n')
            with (Path(scratch) / "lease").open("w+b") as lease, \
                    (Path(scratch) / "read").open("w+b") as read, \
                    (Path(scratch) / "write").open("w+b") as write:
                env = dict(os.environ, TRUST_CPU_IMPLICIT_FD=str(lease.fileno()),
                           MAKEFLAGS="--jobserver-auth={},{}".format(read.fileno(), write.fileno()))
                result = bootstrap.bootstrap_capability_command(
                    [sys.executable, str(program), "-Z", "help"], env, 60, serial=True)
                self.assertEqual(result.returncode, 0)
                self.assertEqual(json.loads(result.stdout), [["-Z", "help"],
                                 [os.fstat(f.fileno()).st_ino for f in (lease, read, write)]])

    # Trust (BOOTSTRAP-SEED-PROBE-ADMISSION-1): the managed serial owner lends an
    # already-admitted caller's execution and refuses every other caller, so only
    # a build-slot caller borrows it; outside admission the query runs directly.
    def test_only_an_admitted_caller_borrows_the_serial_owner(self):
        owner = bootstrap.bootstrap_serial_owner()
        cases = (({}, False), ({"BUILD_SLOT_HELD": "0"}, False),
                 ({"BUILD_SLOT_HELD": "true"}, False), ({"BUILD_SLOT_HELD": "1"}, True))
        for env, borrowed in cases:
            with self.subTest(env=env), \
                    patch.object(bootstrap, "platform_is_win32", return_value=False), \
                    patch.object(bootstrap.sys, "platform", "darwin"), \
                    patch.object(owner, "managed_serial_executor",
                                 return_value=Path("/owner/trust-serial-command")) as admit, \
                    patch.object(owner, "run_custodied_command",
                                 return_value=completed_z_help(TRUST_Z_HELP)) as run:
                bootstrap.bootstrap_capability_command(["/seed/trustc", "-Z", "help"], env, 10,
                                                       serial=True)
                expected = ["/seed/trustc", "-Z", "help"]
                if borrowed:
                    expected = ["/owner/trust-serial-command", "--"] + expected
                    admit.assert_called_once_with(env)
                else:
                    admit.assert_not_called()
                self.assertEqual(run.call_args.args[0], expected)
                self.assertIs(run.call_args.kwargs["env"], env)
                self.assertEqual(run.call_args.kwargs["timeout"], 10)
        # A non-serial query never borrows, admitted or not.
        with patch.object(owner, "managed_serial_executor") as admit, \
                patch.object(owner, "run_custodied_command",
                             return_value=completed_z_help("--unverified")) as run:
            bootstrap.bootstrap_capability_command(["/seed/targo", "--help"],
                                                   {"BUILD_SLOT_HELD": "1"}, 10)
            admit.assert_not_called()
            self.assertEqual(run.call_args.args[0], ["/seed/targo", "--help"])

    @unittest.skipUnless(sys.platform in ("linux", "darwin"), "managed serial route")
    def test_unadmitted_caller_gets_the_answer_the_refusing_owner_withheld(self):
        # REGRESSION, measured 2026-11-10 on origin e66b24d03d: a plain
        # `x.py build` outside build-slot sent `-Z help` through
        # trust-serial-command, which refused (exit 75, "command requires an
        # already-admitted caller"). The policy read that as "could not probe"
        # and took the TRUST_NO_VERIFY fallback, whose empty allow-list then
        # failed trust-resource-controller with E0725. This owner refuses
        # exactly as the real one does, and the compiler answers like a
        # current Trust seed.
        import seed_compiler_identity
        with tempfile.TemporaryDirectory() as scratch:
            owner = Path(scratch) / "trust-serial-command"
            owner.write_text(
                '#!/bin/sh\n'
                'if [ "${BUILD_SLOT_HELD:-}" != 1 ]; then\n'
                '  echo "trust-serial-command: refused: command requires an already-admitted '
                'caller; this launcher grants no CPU/memory" >&2\n'
                '  exit 75\n'
                'fi\n'
                'shift\n'
                'exec "$@"\n')
            owner.chmod(0o700)
            compiler = Path(scratch) / "trustc"
            compiler.write_text("#!/bin/sh\nprintf '%s' '{}'\n".format(TRUST_Z_HELP.rstrip("\n")))
            compiler.chmod(0o700)
            for admitted in (False, True):
                with self.subTest(admitted=admitted), \
                        patch.object(bootstrap.bootstrap_serial_owner(),
                                     "managed_serial_executor", return_value=owner), \
                        patch.object(seed_compiler_identity, "pinned_compiler_binding",
                                     return_value=None):
                    bootstrap.clear_stage0_z_help_cache()
                    env = dict(os.environ)
                    env.pop("BUILD_SLOT_HELD", None)
                    if admitted:
                        env["BUILD_SLOT_HELD"] = "1"
                    for name in ("RUSTFLAGS", "RUSTFLAGS_BOOTSTRAP", "CARGO_ENCODED_RUSTFLAGS",
                                 "TRUST_NO_VERIFY"):
                        env.pop(name, None)
                    self.assertTrue(
                        bootstrap.apply_trust_bootstrap_compiler_policy(str(compiler), env))
                    self.assertEqual(env["RUSTFLAGS_BOOTSTRAP"], "-Ztrust-verify=off")
                    self.assertNotIn("TRUST_NO_VERIFY", env)
            # Control: the owner really refuses an unadmitted caller, so the
            # unadmitted subtest above did not pass through it.
            refused = subprocess.run([str(owner), "--", str(compiler), "-Z", "help"],
                                     env={k: v for k, v in os.environ.items()
                                          if k != "BUILD_SLOT_HELD"},
                                     capture_output=True, text=True)
            self.assertEqual(refused.returncode, 75)
            self.assertIn("already-admitted caller", refused.stderr)

    def test_unanswered_probe_warning_names_the_refusal_and_the_fix(self):
        refusal = ("trust-serial-command: refused: command requires an already-admitted "
                   "caller; this launcher grants no CPU/memory\n")
        for code, text, hint in ((75, refusal, True), (1, "permission denied\n", False)):
            with self.subTest(code=code):
                bootstrap.clear_stage0_z_help_cache()
                env = {}
                stderr = io.StringIO()
                with patch.object(bootstrap, "bootstrap_capability_command",
                                  return_value=completed_z_help(text, code)), \
                        patch.object(bootstrap.sys, "stderr", stderr):
                    self.assertFalse(bootstrap.apply_trust_bootstrap_compiler_policy("rustc", env))
                self.assertEqual(env["TRUST_NO_VERIFY"], "1")
                self.assertEqual(bootstrap.stage0_z_help_unavailable_reason("rustc", env),
                                 "exit {}: {}".format(code, text.strip()))
                warning = stderr.getvalue()
                self.assertIn("could not probe the Stage0 driver's Trust flag surface "
                              "(rustc: exit {}: {})".format(code, text.strip()), warning)
                self.assertEqual("scripts/build-slot" in warning, hint)
        # An exception's text is the reason too, after the retry.
        bootstrap.clear_stage0_z_help_cache()
        with patch.object(bootstrap, "bootstrap_capability_command",
                          side_effect=[z_help_timeout(), RuntimeError("owner unavailable")]), \
                patch.object(bootstrap.sys, "stderr", io.StringIO()):
            self.assertIsNone(bootstrap.stage0_z_help("rustc", {}))
        self.assertEqual(bootstrap.stage0_z_help_unavailable_reason("rustc", {}),
                         "RuntimeError: owner unavailable")
        bootstrap.clear_stage0_z_help_cache()
        self.assertIsNone(bootstrap.stage0_z_help_unavailable_reason("rustc", {}))

    def test_bootstrap_std_feature_allow_list_is_the_dependency_graph_s(self):
        # The initial bootstrap build's allow-list must name every unstable
        # feature a path dependency of src/bootstrap can enable, and nothing
        # else: a missing one is E0725 on every Trust seed whose policy leaves
        # RUSTFLAGS empty (the probe fallback, a retired-spelling seed).
        import re
        import tomllib
        root = Path(bootstrap_dir).parents[1]
        seen, pending, features = set(), [root / "src/bootstrap"], set()

        def path_deps(manifest):
            tables = [manifest.get(key, {}) for key in
                      ("dependencies", "build-dependencies")]
            for target in manifest.get("target", {}).values():
                tables += [target.get(key, {}) for key in ("dependencies", "build-dependencies")]
            for patches in manifest.get("patch", {}).values():
                tables.append(patches)
            for table in tables:
                for spec in table.values():
                    if isinstance(spec, dict) and "path" in spec:
                        yield spec["path"]

        while pending:
            crate = pending.pop().resolve()
            if crate in seen:
                continue
            seen.add(crate)
            manifest = tomllib.loads((crate / "Cargo.toml").read_text())
            for dep in path_deps(manifest):
                pending.append(crate / dep)
            lib = crate / manifest.get("lib", {}).get("path", "src/lib.rs")
            if crate == (root / "src/bootstrap").resolve() or not lib.is_file():
                continue
            text = lib.read_text()
            for start in (m.start() for m in re.finditer(r"#!\[", text)):
                depth, end = 0, start + 2
                while end < len(text):
                    depth += {"[": 1, "]": -1}.get(text[end], 0)
                    if depth == 0:
                        break
                    end += 1
                for listed in re.findall(r"\bfeature\s*\(([^)]*)\)", text[start:end + 1]):
                    features.update(name.strip() for name in listed.split(",") if name.strip())
        self.assertIn((root / "crates/trust-resource-controller").resolve(), seen)
        self.assertEqual(features, set(bootstrap.TRUST_BOOTSTRAP_STD_FEATURES))

    def test_windows_query_does_not_require_a_posix_owner_or_drop_custody(self):
        owner = bootstrap.bootstrap_serial_owner()
        with patch.object(bootstrap, "platform_is_win32", return_value=True), \
                patch.object(owner.landing_targo, "resource_fds", return_value=()), \
                patch.object(owner, "run_custodied_command",
                             side_effect=AssertionError("POSIX wait")), \
                patch.object(bootstrap.subprocess, "run",
                             return_value=completed_z_help(STOCK_Z_HELP)) as run:
            result = bootstrap.bootstrap_capability_command(["selected", "-Z", "help"], {}, 60,
                                                            serial=True)
            self.assertEqual(result.stdout, STOCK_Z_HELP)
            self.assertEqual(run.call_args.args[0], ["selected", "-Z", "help"])
            self.assertEqual(run.call_args.kwargs["timeout"], 60)
        with patch.object(bootstrap, "platform_is_win32", return_value=True), \
                patch.object(owner.landing_targo, "resource_fds", return_value=(7,)), \
                patch.object(bootstrap.subprocess, "run",
                             side_effect=AssertionError("lost custody")):
            with self.assertRaisesRegex(RuntimeError, "cannot inherit"):
                bootstrap.bootstrap_capability_command(["selected", "--help"], {}, 60)

    def test_targo_unavailable_help_cannot_cache_a_legacy_lane(self):
        build = bootstrap.RustBuild()
        with patch.object(build, "cargo", return_value="selected-targo"), \
                patch.object(bootstrap, "bootstrap_capability_command",
                             side_effect=[completed_z_help("--unverified", 75),
                                          completed_z_help("--unverified")]) as run:
            with self.assertRaises(RuntimeError):
                build.targo_supports_unverified_lane()
            self.assertFalse(hasattr(build, "_targo_unverified_lane"))
            self.assertTrue(build.targo_supports_unverified_lane())
            self.assertTrue(build.targo_supports_unverified_lane())
            self.assertEqual(run.call_count, 2)

    def test_stock_driver_is_left_untouched(self):
        # A driver the probe ANSWERED FOR, advertising neither spelling, is
        # stock upstream: no Trust machinery, nothing to disable. Note the
        # probe must be recorded as having succeeded — "answered, no Trust
        # flags" and "could not ask" are different facts, and only the first
        # one licenses leaving the environment alone.
        env = {"RUSTFLAGS_BOOTSTRAP": "-Zthreads=2"}
        with patch.object(bootstrap, "stage0_z_help", return_value=STOCK_Z_HELP):
            self.assertFalse(bootstrap.apply_trust_bootstrap_compiler_policy("rustc", env))
        self.assertEqual(env, {"RUSTFLAGS_BOOTSTRAP": "-Zthreads=2"})

    def test_stable_driver_rejecting_z_is_an_answer_not_a_failure(self):
        # A stable rustc answers `-Z help` by exiting 1. That is a definitive
        # "no Trust surface", and must leave the environment alone: planting
        # TRUST_NO_VERIFY here leaks it into compiletest (red-145).
        env = {"RUSTFLAGS_BOOTSTRAP": "-Zthreads=2"}
        rejected = completed_z_help(
            "error: the option `Z` is only accepted on the nightly compiler\n", 1
        )
        with patch.object(bootstrap, "bootstrap_capability_command", return_value=rejected) as run:
            self.assertFalse(bootstrap.apply_trust_bootstrap_compiler_policy("rustc", env))
        self.assertEqual(run.call_count, 1)
        self.assertEqual(env, {"RUSTFLAGS_BOOTSTRAP": "-Zthreads=2"})

    def test_unanswerable_probe_fails_closed_via_the_env_transport(self):
        # REGRESSION, measured 2026-08-04. `stage0_z_help` returning None means
        # "could not ask" — a subprocess with a bounded timeout against a binary
        # x.py may be extracting concurrently. That used to fall through to the
        # stock-upstream path and apply NO policy, so a batteries-on Trust seed
        # then verified the whole third-party bootstrap dependency tree: one
        # `--stage 2` run burned 1:18:20 and 582,226 log lines inside "Building
        # bootstrap" and died on `memchr` with 694 verification errors without
        # reaching a single compiler step.
        #
        # The fallback must be the ENV transport, never an argv spelling: the
        # current and retired `-Z` spellings each abort the other's vintage
        # with `unknown unstable option`, whereas an unknown env var is inert
        # for a stock driver.
        env = {"RUSTFLAGS_BOOTSTRAP": "-Zthreads=2"}
        with patch.object(bootstrap, "stage0_z_help", return_value=None):
            self.assertFalse(
                bootstrap.apply_trust_bootstrap_compiler_policy("rustc", env)
            )
        self.assertEqual(env["TRUST_NO_VERIFY"], "1")
        self.assertEqual(env["RUSTFLAGS_BOOTSTRAP"], "-Zthreads=2")
        self.assertNotIn("CARGO_ENCODED_RUSTFLAGS", env)

    def test_cold_driver_answering_late_still_fails_closed(self):
        # REGRESSION, measured 2026-09-28. A freshly extracted stage0 trustc
        # takes ~40s on its first exec (macOS first-run scan). The policy used
        # to probe THREE times, independently: the first two probes timed out
        # (None -> "no current spelling", "no retired spelling"), the third
        # answered (-> "the probe could answer"), and the combination selected
        # the stock-upstream branch -- no policy, batteries-on verification of
        # the whole bootstrap dependency tree. The driver is now asked once
        # (with one retry); when no attempt answers, every decision reads the
        # same "could not ask" and the fail-closed transport is taken.
        env = {"RUSTFLAGS_BOOTSTRAP": "-Zthreads=2"}
        answers = [z_help_timeout()] * len(bootstrap.STAGE0_Z_HELP_TIMEOUTS) + [
            completed_z_help(STOCK_Z_HELP)
        ]
        with patch.object(bootstrap, "bootstrap_capability_command", side_effect=answers) as run:
            self.assertFalse(bootstrap.apply_trust_bootstrap_compiler_policy("rustc", env))
            self.assertEqual(run.call_count, len(bootstrap.STAGE0_Z_HELP_TIMEOUTS))
            # Every later decision about this driver reads the same answer and
            # asks nothing new.
            self.assertFalse(bootstrap.stage0_trust_surface_available("rustc", env))
            self.assertFalse(
                bootstrap.rustc_supports_trust_bootstrap_no_verify("rustc", env)
            )
            self.assertFalse(bootstrap.rustc_advertises_retired_no_verify("rustc", env))
            self.assertEqual(run.call_count, len(bootstrap.STAGE0_Z_HELP_TIMEOUTS))
        self.assertEqual(env["TRUST_NO_VERIFY"], "1")
        self.assertEqual(env["RUSTFLAGS_BOOTSTRAP"], "-Zthreads=2")

    def test_timed_out_probe_is_retried_once_with_a_longer_timeout(self):
        # A retry that outlasts the first-exec scan recovers the real answer,
        # so a capable seed gets the exact argv off-switch rather than the
        # env transport (which leaks further than bootstrap).
        env = {"RUSTFLAGS_BOOTSTRAP": "-Zthreads=2"}
        answers = [z_help_timeout("trustc"), completed_z_help(TRUST_Z_HELP, rustc="trustc")]
        with patch.object(bootstrap, "bootstrap_capability_command", side_effect=answers) as run:
            self.assertTrue(bootstrap.apply_trust_bootstrap_compiler_policy("trustc", env))
        self.assertEqual(
            [call.kwargs["timeout"] for call in run.call_args_list],
            list(bootstrap.STAGE0_Z_HELP_TIMEOUTS),
        )
        self.assertGreaterEqual(bootstrap.STAGE0_Z_HELP_TIMEOUTS[-1], 60)
        self.assertEqual(env["RUSTFLAGS_BOOTSTRAP"], "-Zthreads=2 -Ztrust-verify=off")
        self.assertNotIn("TRUST_NO_VERIFY", env)

    def test_probe_is_memoized_per_driver_and_environment(self):
        with patch.object(
            bootstrap, "bootstrap_capability_command", return_value=completed_z_help(STOCK_Z_HELP)
        ) as run:
            for _ in range(3):
                self.assertEqual(bootstrap.stage0_z_help("rustc", {"A": "1"}), STOCK_Z_HELP)
            self.assertEqual(run.call_count, 1)
            bootstrap.stage0_z_help("rustc", {"A": "2"})
            bootstrap.stage0_z_help("other-rustc", {"A": "1"})
            self.assertEqual(run.call_count, 3)
            bootstrap.clear_stage0_z_help_cache()
            bootstrap.stage0_z_help("rustc", {"A": "1"})
            self.assertEqual(run.call_count, 4)

    def test_fake_cold_stage0_first_exec_times_out(self):
        # End to end against a real process: a fake stage0 whose FIRST probe
        # exec hangs past the probe timeout (standing in for the macOS
        # first-run scan) and whose later execs answer as a capable Trust
        # driver.
        if os.name != "posix":
            self.skipTest("fake stage0 driver is a POSIX shell script")
        tmp = tempfile.mkdtemp()
        self.addCleanup(rmtree, tmp)
        counter = os.path.join(tmp, "execs")
        rustc = os.path.join(tmp, "trustc")
        with open(rustc, "w") as f:
            f.write(
                "#!/bin/sh\n"
                'if [ -n "$FAKE_STAGE0_WARMUP" ]; then exit 0; fi\n'
                'echo x >> "{counter}"\n'
                'if [ "$(wc -l < "{counter}")" -le "$COLD_EXECS" ]; then exec sleep 60; fi\n'
                "printf '%s' '{help}'\n".format(counter=counter, help=TRUST_Z_HELP)
            )
        os.chmod(rustc, 0o755)
        # macOS really does scan a brand-new executable on its first exec (this
        # script can take tens of seconds there): pay that once, untimed, so
        # the timed attempts below see only the scripted coldness.
        subprocess.run([rustc], env=dict(os.environ, FAKE_STAGE0_WARMUP="1"), check=True)

        def execs():
            with open(counter) as f:
                return len(f.readlines())

        # Trust: only PATH from the caller's environment. Under `x.py test
        # bootstrap-py` the ambient environment carries x.py's own
        # RUSTFLAGS_BOOTSTRAP=-Ztrust-verify=off, which the fail-closed
        # assertion below would read as the policy's doing.
        hermetic = {"PATH": os.environ["PATH"]}

        # One cold exec: the retry answers, the capable-seed policy applies.
        env = dict(hermetic, COLD_EXECS="1")
        with patch.object(bootstrap, "STAGE0_Z_HELP_TIMEOUTS", (1, 60)):
            self.assertTrue(bootstrap.apply_trust_bootstrap_compiler_policy(rustc, env))
        self.assertEqual(execs(), 2)
        self.assertIn("-Ztrust-verify=off", env["RUSTFLAGS_BOOTSTRAP"])
        self.assertNotIn("TRUST_NO_VERIFY", env)

        # Every attempt cold: fail closed, and every later decision about the
        # driver reads the same "could not ask" without executing it again.
        os.remove(counter)
        bootstrap.clear_stage0_z_help_cache()
        env = dict(hermetic, COLD_EXECS="1000")
        with patch.object(bootstrap, "STAGE0_Z_HELP_TIMEOUTS", (0.5, 0.5)):
            self.assertFalse(bootstrap.apply_trust_bootstrap_compiler_policy(rustc, env))
            probed = execs()
            self.assertFalse(bootstrap.stage0_trust_surface_available(rustc, env))
            self.assertFalse(bootstrap.rustc_supports_trust_bootstrap_no_verify(rustc, env))
        self.assertEqual(execs(), probed)
        self.assertEqual(env["TRUST_NO_VERIFY"], "1")
        self.assertNotIn("-Ztrust-verify=off", env.get("RUSTFLAGS_BOOTSTRAP", ""))

    def test_probe_availability_preserves_help_and_stable_rejection(self):
        # Trust: successful help and the known stable rejection are answers;
        # execution failures remain unavailable instead of proving absence.
        answered = completed_z_help("-Z threads=val")
        rejected = completed_z_help(
            "error: the option `Z` is only accepted on the nightly compiler", 1
        )
        with patch.object(bootstrap, "bootstrap_capability_command", return_value=answered):
            self.assertTrue(bootstrap.stage0_trust_surface_available("rustc", {}))
        bootstrap.clear_stage0_z_help_cache()
        with patch.object(bootstrap, "bootstrap_capability_command", return_value=rejected):
            self.assertTrue(bootstrap.stage0_trust_surface_available("rustc", {}))
        bootstrap.clear_stage0_z_help_cache()
        with patch.object(bootstrap, "bootstrap_capability_command",
                          side_effect=OSError("boom")) as run:
            self.assertFalse(bootstrap.stage0_trust_surface_available("rustc", {}))
        self.assertEqual(run.call_count, len(bootstrap.STAGE0_Z_HELP_TIMEOUTS))
        bootstrap.clear_stage0_z_help_cache()
        with patch.object(bootstrap, "bootstrap_capability_command", side_effect=z_help_timeout()):
            self.assertFalse(bootstrap.stage0_trust_surface_available("rustc", {}))

    def test_pre_rename_trust_seed_gets_the_env_transport(self):
        # A Trust seed OLDER than the flag rename advertises only the retired
        # `-Zno-trust-verify`: appending the current spelling would abort it
        # with `unknown unstable option` at the first build script, and
        # appending the retired one would abort every post-rename seed. The
        # policy must reach for the version-invariant nested-process
        # transport instead, and must NOT append any argv spelling.
        env = {"RUSTFLAGS_BOOTSTRAP": "-Zthreads=2"}
        with patch.object(bootstrap, "stage0_z_help", return_value=RETIRED_Z_HELP):
            self.assertFalse(bootstrap.apply_trust_bootstrap_compiler_policy("rustc", env))
        self.assertEqual(env["TRUST_NO_VERIFY"], "1")
        self.assertEqual(env["RUSTFLAGS_BOOTSTRAP"], "-Zthreads=2")
        self.assertNotIn("CARGO_ENCODED_RUSTFLAGS", env)

    def test_trust_driver_gets_exact_flag_in_plain_and_encoded_lanes(self):
        env = {
            "RUSTFLAGS_BOOTSTRAP": "-Zthreads=2",
            "CARGO_ENCODED_RUSTFLAGS": "-Cdebuginfo=0",
        }
        with patch.object(bootstrap, "stage0_z_help", return_value=TRUST_Z_HELP):
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
                bootstrap, "stage0_z_help", return_value=TRUST_Z_HELP
            ):
                with self.assertRaises(RuntimeError):
                    bootstrap.apply_trust_bootstrap_compiler_policy(
                        "trustc", {name: value}
                    )

    def test_fallback_policy_rejects_conflicts_before_mutating_environment(self):
        # Trust: an unavailable probe and a pre-rename Trust seed both select
        # the environment transport. Neither may bypass the conflict refusal.
        for help_text in (None, RETIRED_Z_HELP):
            for name, value in (
                ("RUSTFLAGS", "-Ztrust-verify-full"),
                ("RUSTFLAGS_BOOTSTRAP", "-Ztrust-verify=on"),
                ("CARGO_ENCODED_RUSTFLAGS", "-Cdebuginfo=0\x1f-Ztrust-policy=advisory"),
            ):
                env = {name: value, "UNRELATED": "preserved"}
                original = env.copy()
                with self.subTest(help_text=help_text, name=name), patch.object(
                    bootstrap, "stage0_z_help", return_value=help_text
                ) as probe:
                    with self.assertRaisesRegex(RuntimeError, name):
                        bootstrap.apply_trust_bootstrap_compiler_policy("trustc", env)
                    probe.assert_called_once()
                    self.assertEqual(env, original)

    def test_capability_probe_requires_successful_exact_help_surface(self):
        supported = completed_z_help("-Z trust-verify=val", rustc="trustc")
        unsupported = completed_z_help("-Z threads=val")
        spoofed = completed_z_help(
            "note: trust-verify is unsupported\n-Z trust-verify-extra=val"
        )
        with patch.object(bootstrap, "bootstrap_capability_command", return_value=supported):
            self.assertTrue(
                bootstrap.rustc_supports_trust_bootstrap_no_verify("trustc", {})
            )
        with patch.object(bootstrap, "bootstrap_capability_command", return_value=unsupported):
            self.assertFalse(
                bootstrap.rustc_supports_trust_bootstrap_no_verify("rustc", {})
            )
        bootstrap.clear_stage0_z_help_cache()
        with patch.object(bootstrap, "bootstrap_capability_command", return_value=spoofed):
            self.assertFalse(
                bootstrap.rustc_supports_trust_bootstrap_no_verify("rustc", {})
            )

    def test_runtime_driver_inherits_the_same_capability_gated_policy(self):
        base = {"RUSTFLAGS_BOOTSTRAP": "-Zthreads=2", "UNRELATED": "preserved"}
        with patch.object(bootstrap, "stage0_z_help", return_value=TRUST_Z_HELP):
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


class Stage0FailClosedRefresh(unittest.TestCase):
    """The stage0 refresh must never destroy a working seed.

    Regression suite for the 2026-07-29 incident: a refresh triggered by a
    stale legacy `cargo = .../bin/tcargo` bootstrap.toml pin deleted the
    entire stage0 seed and reinstalled only the need-scoped Targo half,
    leaving the tree without any working trustc. The refresh now stages the
    complete replacement surface, verifies it, and atomically swaps it in;
    every failure mode must abort with the existing seed untouched.
    """

    BUILD = "test-triple"
    DATE = "2026-01-01"
    VERSION = "9.9.9-test"

    def setUp(self):
        self.container = tempfile.mkdtemp()
        self.build_dir = os.path.join(self.container, "build")
        self.dist_root = os.path.join(self.container, "dist-server")

    def tearDown(self):
        rmtree(self.container)

    def make_build(self, config_toml=""):
        build = bootstrap.RustBuild(config_toml=config_toml, args=bootstrap.FakeArgs())
        build.build_dir = self.build_dir
        build.build = self.BUILD
        build.stage0_compiler = bootstrap.Stage0Toolchain(self.DATE, self.VERSION)
        build.download_url = "file://" + self.dist_root
        build.stage0_data = {
            "compiler_date": self.DATE,
            "compiler_version": self.VERSION,
            "compiler_git_commit_hash": "1" * 40,
            "compiler_channel_manifest_hash": "a" * 64,
        }
        build.verbose = 0
        return build

    def write_seed(self, build):
        """Materialize a complete, valid stage0 surface (the working seed)."""
        bin_root = build.bin_root()
        bin_dir = os.path.join(bin_root, "bin")
        libexec = os.path.join(bin_root, "libexec")
        os.makedirs(bin_dir)
        os.makedirs(libexec)
        for name in bootstrap.STAGE0_REQUIRED_BINS:
            with open(os.path.join(bin_dir, name + bootstrap.EXE_SUFFIX), "w") as f:
                f.write("old-" + name)
        for name in bootstrap.STAGE0_REQUIRED_LIBEXEC_BINS:
            with open(os.path.join(libexec, name + bootstrap.EXE_SUFFIX), "w") as f:
                f.write("old-" + name)
        os.makedirs(os.path.join(bin_root, "lib"))
        with open(os.path.join(bin_root, "lib", "sentinel"), "w") as f:
            f.write("old-lib")
        return bin_root

    def write_stamp(self, build, key=None):
        with open(build.rustc_stamp(), "w") as f:
            stamp = key if key is not None else bootstrap.stage0_extraction_stamp(build.stage0_data)
            f.write(stamp)

    def snapshot(self, root):
        """Map every file under root to its content."""
        state = {}
        for dirpath, _dirnames, filenames in os.walk(root):
            for filename in filenames:
                path = os.path.join(dirpath, filename)
                with open(path, "r") as f:
                    state[os.path.relpath(path, root)] = f.read()
        return state

    def component_plan(self, build):
        std_image = "trust-std-{}".format(build.build)
        return {
            "trust-std": (
                std_image,
                ["lib/rustlib/{}/lib/libstd.rlib".format(build.build)],
            ),
            "trustc": (
                "trustc",
                [
                    "bin/trustc",
                    "bin/rustc",
                    "bin/trustdoc",
                    "libexec/trust-analyzer-proc-macro-srv",
                    "lib/libtrustc-driver.dylib",
                ],
            ),
            "targo": ("targo", ["bin/targo", "bin/cargo"]),
            "targo-trust": ("targo-trust", ["bin/targo-trust"]),
            "trustfmt": ("trustfmt", ["bin/trustfmt", "bin/targo-fmt"]),
            "tippy": ("tippy", ["bin/tippy", "bin/targo-tippy", "bin/tippy-driver"]),
            "trust-analyzer": ("trust-analyzer", ["bin/trust-analyzer"]),
        }

    def make_archives(self, build, omit=(), drop_files=(), marker="new"):
        """Publish pinned component archives on the file:// dist server."""
        suffix = ".tar.gz" if bootstrap.lzma is None else ".tar.xz"
        mode = "w:gz" if bootstrap.lzma is None else "w:xz"
        toolchain_suffix = "{}-{}{}".format(
            build.stage0_compiler.version, build.build, suffix
        )
        dist_dir = os.path.join(
            self.dist_root, "dist", build.stage0_compiler.date
        )
        os.makedirs(dist_dir, exist_ok=True)
        for component, (image, files) in self.component_plan(build).items():
            if component in omit:
                continue
            filename = "{}-{}".format(component, toolchain_suffix)
            top = filename.replace(suffix, "")
            tar_path = os.path.join(dist_dir, filename)
            with tarfile.open(tar_path, mode) as tar:
                for rel in files:
                    if rel in drop_files:
                        continue
                    data = "{}-{}".format(marker, os.path.basename(rel)).encode("utf-8")
                    info = tarfile.TarInfo("{}/{}/{}".format(top, image, rel))
                    info.size = len(data)
                    tar.addfile(info, io.BytesIO(data))
            with open(tar_path, "rb") as f:
                digest = hashlib.sha256(f.read()).hexdigest()
            build.stage0_data[
                "dist/{}/{}".format(build.stage0_compiler.date, filename)
            ] = digest

    def assert_no_refresh_residue(self, build):
        bin_root = build.bin_root()
        self.assertFalse(os.path.exists(bin_root + ".staging"))
        self.assertFalse(os.path.exists(bin_root + ".previous"))

    def test_actual_refresh_uses_the_same_complete_source_selection_as_native_planning(self):
        build = self.make_build()
        self.make_archives(build)
        with patch.object(bootstrap._identity_owner, "component_archives",
                          wraps=bootstrap._identity_owner.component_archives) as shared:
            build.download_toolchain()
        self.assertEqual(shared.call_count, 1)
        rows, legacy_targo, legacy_tippy = bootstrap._identity_owner.component_archives(
            build.stage0_data, build.stage0_compiler.date, build.stage0_compiler.version,
            build.build, ".tar.gz" if bootstrap.lzma is None else ".tar.xz")
        self.assertEqual(len(rows), 7)
        self.assertEqual(legacy_targo, [])
        self.assertFalse(legacy_tippy)
        build.assert_stage0_tool_surface()
        self.assert_no_refresh_residue(build)

    def test_same_day_changed_pin_reextracts_instead_of_reusing_old_seed(self):
        build = self.make_build()
        self.make_archives(build)
        build.download_toolchain()
        build.stage0_data["compiler_git_commit_hash"] = "2" * 40
        self.make_archives(build, marker="next")
        build.download_toolchain()
        with open(build.rustc()) as stream:
            self.assertEqual(stream.read(), "next-trustc")
        self.assert_no_refresh_residue(build)

    def test_same_commit_changed_archive_digest_reextracts_and_checks_existing_cache(self):
        build = self.make_build()
        self.make_archives(build)
        build.download_toolchain()
        self.make_archives(build, marker="repacked")
        build.download_toolchain()
        with open(build.rustc()) as stream:
            self.assertEqual(stream.read(), "repacked-trustc")
        self.assert_no_refresh_residue(build)

    def test_identical_pin_reuses_the_extracted_seed_without_download_or_unpack(self):
        build = self.make_build()
        self.make_archives(build)
        build.download_toolchain()
        before = self.snapshot(build.bin_root())
        with patch.object(
            bootstrap, "download_component", side_effect=AssertionError("unchanged pin downloaded")
        ), patch.object(
            bootstrap, "unpack_component", side_effect=AssertionError("unchanged pin unpacked")
        ):
            build.download_toolchain()
        self.assertEqual(self.snapshot(build.bin_root()), before)

    def test_date_only_legacy_stamp_refreshes_and_upgrades_once(self):
        build = self.make_build()
        self.make_archives(build)
        build.download_toolchain()
        self.write_stamp(build, key=self.DATE)
        with patch.object(
            bootstrap, "download_component", wraps=bootstrap.download_component
        ) as download:
            build.download_toolchain()
        self.assertGreater(download.call_count, 0)
        with open(build.rustc_stamp()) as stream:
            self.assertEqual(stream.read(), bootstrap.stage0_extraction_stamp(build.stage0_data))
        with patch.object(
            bootstrap, "download_component", side_effect=AssertionError("second refresh")
        ):
            build.download_toolchain()

    def test_tampered_stamp_and_wrong_cached_archive_preserve_the_live_seed(self):
        build = self.make_build()
        self.make_archives(build)
        build.download_toolchain()
        self.write_stamp(build, key="tampered-stamp")
        before = self.snapshot(build.bin_root())
        pinned = dict(build.stage0_data)
        self.make_archives(build, marker="unadmitted")
        build.stage0_data = pinned
        suffix = ".tar.gz" if bootstrap.lzma is None else ".tar.xz"
        name = "trustc-{}-{}{}".format(self.VERSION, self.BUILD, suffix)
        source = Path(self.dist_root) / "dist" / self.DATE / name
        cached = Path(self.build_dir) / "cache" / self.DATE / name
        cached.write_bytes(source.read_bytes())
        with self.assertRaisesRegex(RuntimeError, "failed verification"):
            build.download_toolchain()
        self.assertEqual(self.snapshot(build.bin_root()), before)
        self.assert_no_refresh_residue(build)

    def test_healthy_seed_with_fresh_stamp_is_untouched(self):
        build = self.make_build()
        bin_root = self.write_seed(build)
        self.write_stamp(build)
        before = self.snapshot(bin_root)
        build.download_toolchain()
        self.assertEqual(self.snapshot(bin_root), before)
        self.assert_no_refresh_residue(build)

    def test_forbidden_legacy_tool_pin_fails_closed(self):
        # The incident trigger: bootstrap.toml pinning cargo to the legacy
        # tcargo spelling, which a refresh can never produce. The old code
        # looped destructively; the trigger must now be rejected with the
        # seed untouched.
        build = self.make_build()
        legacy_pin = os.path.join(build.bin_root(), "bin", "tcargo")
        build = self.make_build(
            config_toml='[build]\ncargo = "{}"\n'.format(legacy_pin)
        )
        bin_root = self.write_seed(build)
        self.write_stamp(build)
        before = self.snapshot(bin_root)
        with self.assertRaisesRegex(RuntimeError, "tcargo"):
            build.download_toolchain()
        self.assertEqual(self.snapshot(bin_root), before)
        self.assert_no_refresh_residue(build)

    def test_missing_archives_abort_before_seed_deletion(self):
        build = self.make_build()
        bin_root = self.write_seed(build)
        self.write_stamp(build, key="1970-01-01")  # stale -> refresh fires
        before = self.snapshot(bin_root)
        with self.assertRaisesRegex(RuntimeError, "checksum"):
            build.download_toolchain()
        self.assertEqual(self.snapshot(bin_root), before)
        self.assert_no_refresh_residue(build)

    def test_incident_shape_missing_compiler_archive_leaves_seed_intact(self):
        # 2026-07-29 regression: everything BUT the compiler half of the
        # surface is available. The old code deleted the seed and installed
        # the partial surface; now the refresh must abort first.
        build = self.make_build()
        bin_root = self.write_seed(build)
        self.write_stamp(build, key="1970-01-01")
        self.make_archives(build, omit=("trustc",))
        before = self.snapshot(bin_root)
        with self.assertRaisesRegex(RuntimeError, "trustc"):
            build.download_toolchain()
        self.assertEqual(self.snapshot(bin_root), before)
        trustc = os.path.join(bin_root, "bin", "trustc" + bootstrap.EXE_SUFFIX)
        with open(trustc, "r") as f:
            self.assertEqual(f.read(), "old-trustc")
        self.assert_no_refresh_residue(build)

    def test_incomplete_extraction_fails_before_swap(self):
        # All archives download and unpack, but the staged surface is
        # missing bin/trustc: the pre-swap assertion must reject it and the
        # working seed must survive.
        build = self.make_build()
        bin_root = self.write_seed(build)
        self.write_stamp(build, key="1970-01-01")
        self.make_archives(build, drop_files=("bin/trustc",))
        before = self.snapshot(bin_root)
        with self.assertRaisesRegex(RuntimeError, "missing required"):
            build.download_toolchain()
        self.assertEqual(self.snapshot(bin_root), before)
        self.assert_no_refresh_residue(build)

    def test_refresh_replaces_seed_atomically(self):
        # A forbidden legacy leftover in the live surface (the realistic
        # migration trigger) causes a refresh; the complete staged surface
        # must swap in, the leftover must be gone, and the stamp written.
        build = self.make_build()
        bin_root = self.write_seed(build)
        with open(os.path.join(bin_root, "bin", "tcargo"), "w") as f:
            f.write("legacy-leftover")
        self.write_stamp(build)
        self.make_archives(build)
        self.assertTrue(build.stage0_tool_surface_needs_refresh())
        build.download_toolchain()
        for name in bootstrap.STAGE0_REQUIRED_BINS:
            path = os.path.join(bin_root, "bin", name + bootstrap.EXE_SUFFIX)
            with open(path, "r") as f:
                self.assertEqual(f.read(), "new-" + name, name)
        for name in bootstrap.STAGE0_REQUIRED_LIBEXEC_BINS:
            path = os.path.join(bin_root, "libexec", name + bootstrap.EXE_SUFFIX)
            with open(path, "r") as f:
                self.assertEqual(f.read(), "new-" + name, name)
        self.assertFalse(os.path.exists(os.path.join(bin_root, "bin", "tcargo")))
        self.assertFalse(os.path.exists(os.path.join(bin_root, "lib", "sentinel")))
        with open(build.rustc_stamp(), "r") as f:
            self.assertEqual(f.read(), bootstrap.stage0_extraction_stamp(build.stage0_data))
        self.assertFalse(build.stage0_tool_surface_needs_refresh())
        self.assert_no_refresh_residue(build)


class Stage0ExtractionIdentity(unittest.TestCase):
    def fixture(self):
        data = {}
        for component in ("compiler", "rustfmt"):
            data.update({
                component + "_date": "2026-10-19",
                component + "_version": "0.11.0-trust",
                component + "_dist_channel": "trust",
                component + "_git_commit_hash": "1" * 40,
                component + "_channel_manifest_hash": "a" * 64,
            })
        for component, digest in (("targo", "c"), ("trustc", "b")):
            archive = "dist/2026-10-19/{}-0.11.0-trust-aarch64-apple-darwin.tar.xz".format(
                component
            )
            data[archive] = digest * 64
        return data

    def test_fixed_vectors_match_the_rust_download_owner(self):
        data = self.fixture()
        prefix = "trust-stage0-extraction-v3:"
        self.assertEqual(
            bootstrap.stage0_extraction_stamp(data),
            prefix + "3ac64c7fe74e195c373d0d0b32f6cfcad11d660f22f5f05e1d0e807546b40442",
        )
        data["compiler_git_commit_hash"] = "2" * 40
        self.assertEqual(
            bootstrap.stage0_extraction_stamp(data),
            prefix + "009d583019415ba13fdccd4df8b60059c7d64ac02343545a7f2712d41755c387",
        )
        data["compiler_git_commit_hash"] = "1" * 40
        data["dist/2026-10-19/trustc-0.11.0-trust-aarch64-apple-darwin.tar.xz"] = "d" * 64
        self.assertEqual(
            bootstrap.stage0_extraction_stamp(data),
            prefix + "766ef09828a7e771bf7a75738e1e49d4ad79a6cd115078720caf109bc4432eac",
        )

    def test_mirrors_and_order_do_not_change_identity_and_missing_equals_empty(self):
        data = self.fixture()
        expected = bootstrap.stage0_extraction_stamp(data)
        data = dict(reversed(list(data.items())))
        data["dist_server"] = "https://another.example/seed"
        self.assertEqual(bootstrap.stage0_extraction_stamp(data), expected)
        data.pop("rustfmt_dist_channel")
        absent = bootstrap.stage0_extraction_stamp(data)
        data["rustfmt_dist_channel"] = ""
        self.assertEqual(bootstrap.stage0_extraction_stamp(data), absent)

    def test_multiline_records_are_not_a_cache_identity(self):
        data = self.fixture()
        data["compiler_date"] += "\ninjected=record"
        with self.assertRaisesRegex(ValueError, "single-line"):
            bootstrap.stage0_extraction_stamp(data)
