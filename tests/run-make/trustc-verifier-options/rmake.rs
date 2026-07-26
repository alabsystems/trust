//@ needs-symlink

use std::path::PathBuf;

use run_make_support::{bin_name, cmd, rfs, rustc_path, serde_json};

const TRUST_VANILLA_REAL_RUSTC_ENV: &str = "__COMPILETEST_TRUST_VANILLA_REAL_RUSTC";

fn read_and_assert_direct_ir_artifacts(
    directory: &str,
    crate_name: &str,
    required_function: &str,
) -> [Vec<u8>; 3] {
    let base = PathBuf::from(directory);
    let [binary, text, coverage_bytes] =
        ["trust-ir.bin", "trust-ir.txt", "coverage.json"].map(|suffix| {
            let artifact = format!("{crate_name}.{suffix}");
            assert!(base.join(&artifact).is_file(), "missing {artifact}");
            std::fs::read(base.join(artifact)).expect("read direct TrustIr artifact")
        });

    let direct_module = std::str::from_utf8(&text).expect("TrustIr text artifact must be UTF-8");
    assert!(
        direct_module.contains("; #producer: trust"),
        "Rust direct-frontend functions lack Producer::TRust provenance:\n{direct_module}"
    );
    assert!(
        direct_module.contains(required_function),
        "contract-bearing `{required_function}` was absent from direct TrustIr:\n{direct_module}"
    );

    let coverage: serde_json::Value =
        serde_json::from_slice(&coverage_bytes).expect("parse TrustIr coverage");
    assert_eq!(coverage["schema"], "trust.thir-lower.crate-module.coverage.v2");
    assert_eq!(coverage["direct_obligation_capability"], "structural-parity-only-v1");
    assert_eq!(coverage["proof_authority"], false);
    assert_eq!(coverage["native_verification_requests"], false);
    for field in ["bodies", "lowered", "spliced"] {
        assert!(
            coverage["totals"][field].as_u64().is_some_and(|count| count > 0),
            "direct TrustIr coverage total `{field}` was not positive: {coverage}"
        );
    }
    let known_verdict =
        |verdict: &str| matches!(verdict, "agreed" | "mismatch" | "unsupported" | "not-run");
    for body in coverage["bodies"].as_array().expect("coverage body inventory") {
        let differentials = body["differentials"]
            .as_object()
            .expect("every body must carry typed differential evidence");
        for channel in ["interpreter", "derived_mir"] {
            let verdict = differentials[channel]["verdict"]
                .as_str()
                .expect("differential verdict must be typed text");
            assert!(known_verdict(verdict), "unknown {channel} verdict `{verdict}`");
        }
        let deferred =
            differentials["deferred_to_seam"].as_bool().expect("seam ownership must be explicit");
        let state = differentials["seam"]["state"].as_str().expect("seam state must be explicit");
        if deferred {
            assert_eq!(state, "resolved");
            let verdict = differentials["seam"]["verdict"]
                .as_str()
                .expect("resolved seam must carry a typed verdict");
            assert!(known_verdict(verdict), "unknown seam verdict `{verdict}`");
        } else {
            assert_eq!(state, "not-applicable");
        }
    }

    [binary, text, coverage_bytes]
}

fn read_and_assert_mir_compat_contract_order(
    directory: &str,
    required_function: &str,
    expected: &[(&str, &str)],
    exact_bodies: bool,
) {
    let mut functions = Vec::new();
    for entry in rfs::read_dir(directory) {
        let entry = entry.expect("read MIR-compat dump directory entry");
        let json = rfs::read_to_string(entry.path());
        let value: serde_json::Value =
            serde_json::from_str(&json).expect("parse MIR-compat VerifiableFunction dump");
        if value["def_path"].as_str().is_some_and(|def_path| def_path == required_function) {
            functions.push(value);
        }
    }

    assert_eq!(
        functions.len(),
        1,
        "expected exactly one MIR-compat dump for `{required_function}`, got {functions:#?}"
    );
    let contracts = functions[0]["contracts"]
        .as_array()
        .expect("MIR-compat VerifiableFunction must expose a contract inventory");
    assert_eq!(
        contracts.len(),
        expected.len(),
        "every expected contract clause must survive for `{required_function}`"
    );
    for (ordinal, (contract, (expected_kind, expected_marker))) in
        contracts.iter().zip(expected.iter().copied()).enumerate()
    {
        assert_eq!(
            contract["kind"], expected_kind,
            "contract {ordinal} did not retain its function-wide authored kind: {contract}"
        );
        let body = contract["body"].as_str().expect("contract body must be public text");
        if exact_bodies {
            assert_eq!(
                body, expected_marker,
                "typed contract {ordinal} was not lowered from its exact HIR predicate"
            );
        } else {
            assert!(
                body.contains(expected_marker),
                "contract {ordinal} lost its lane-unique authored payload `{expected_marker}`: {body}"
            );
        }
    }
}

fn main() {
    if std::env::var_os(TRUST_VANILLA_REAL_RUSTC_ENV).is_some() {
        return;
    }

    let rustc = PathBuf::from(rustc_path());
    let trustc = rustc.with_file_name(bin_name("trustc"));
    let trustc = if trustc.exists() { trustc } else { rustc };
    rfs::write("empty.rs", "fn main() {}\n");

    for (flag, expected) in [
        ("-Ztrust-verify-level=3", "one of `0`, `1`, or `2`"),
        ("-Ztrust-verify-output=jsonl", "one of `human`, `json`, or `both`"),
        ("-Ztrust-verify-session=", "a non-empty session identifier"),
        ("-Ztrust-verify-crate-role=workspace", "one of `unscoped`"),
        ("-Ztrust-verify-timeout-ms=0", "a positive integer"),
        ("-Ztrust-verify-worker-threads=257", "an integer from 0 through 256"),
        ("-Ztrust-cg-output-gate=permissive", "one of `allow-unknown`"),
        // Policy is one domain, so the settings cannot be combined at all:
        // the invalid pair is now rejected by the parser, not by a downstream
        // cross-check that had to be kept in step with the callers.
        ("-Ztrust-policy=memory-safe,advisory", "one of `strict`, `advisory`, or `memory-safe`"),
        ("-Ztrust-policy=survey", "one of `strict`, `advisory`, or `memory-safe`"),
        ("-Ztrust-verify", "requires one of `on` or `off`"),
        ("-Ztrust-verify=yes", "one of `on` or `off`"),
        ("-Ztrust-witness=mint", "one of `auto`, `off`, `mint:<dir>`, or `replay:<dir>`"),
        ("-Ztrust-witness=mint:", "one of `auto`, `off`, `mint:<dir>`, or `replay:<dir>`"),
    ] {
        let mut command = cmd(&trustc);
        for arg in flag.split_whitespace() {
            command.arg(arg);
        }
        command.arg("empty.rs").run_fail().assert_stderr_contains(expected);
    }

    // A declared reachable panic is conditional evidence, never proof. Raw
    // strict trustc and the narrow memory-safe policy must fail; only the
    // explicit broad advisory lanes may reclassify it for Targo's conditional
    // bucket. Keep this at the compiler front door so Targo cannot mask a raw
    // trustc policy disagreement.
    rfs::write(
        "contract-panic.rs",
        r#"#![crate_type = "lib"]
#![feature(register_tool)]
#![register_tool(trust)]

#[trust::contract_panic(message_contains = "capacity is")]
pub fn push_slot(len: usize) -> usize {
    if len >= 8 {
        panic!("ArrayVec overflow: capacity is 8");
    }
    len
}
"#,
    );
    cmd(&trustc)
        .arg("-Ztrust-verify-output=json")
        .arg("--emit=metadata")
        .arg("contract-panic.rs")
        .arg("-o")
        .arg("contract-panic-strict.rmeta")
        .run_fail()
        .assert_stderr_contains("Trust Level 0 safety verification incomplete")
        .assert_stderr_not_contains("contract-panic:matched");
    cmd(&trustc)
        .arg("-Ztrust-policy=memory-safe")
        .arg("-Ztrust-verify-output=json")
        .arg("--emit=metadata")
        .arg("contract-panic.rs")
        .arg("-o")
        .arg("contract-panic-memory-safe.rmeta")
        .run_fail()
        .assert_stderr_contains("Trust memory-safe verification failed")
        .assert_stderr_not_contains("contract-panic:matched");
    cmd(&trustc)
        .arg("-Ztrust-policy=advisory")
        .arg("-Ztrust-verify-output=json")
        .arg("--emit=metadata")
        .arg("contract-panic.rs")
        .arg("-o")
        .arg("contract-panic-survey.rmeta")
        .run()
        .assert_stderr_contains("contract-panic:matched");

    // Unit roles are a three-field frontend protocol. A raw caller cannot
    // select dependency/build-script scope with a lone role flag and thereby
    // turn batteries-on verification into a second public off-switch.
    for role in ["dependency", "build-script"] {
        cmd(&trustc)
            .arg(format!("-Ztrust-verify-crate-role={role}"))
            .arg("empty.rs")
            .run_fail()
            .assert_stderr_contains("requires both -Ztrust-verify-package-name");
    }
    cmd(&trustc)
        .arg("-Ztrust-verify-package-name=pkg")
        .arg("empty.rs")
        .run_fail()
        .assert_stderr_contains("requires -Ztrust-verify-session");
    // Raw/single-file frontends use a session-only freshness nonce without a
    // Cargo package envelope; that cannot weaken the strict unscoped role.
    // A session also promises a coverage row, so exercise an analyzed metadata
    // compile instead of an early-exit `--print` request that cannot honor it.
    cmd(&trustc)
        .arg("-Ztrust-verify-session=raw-session")
        .arg("--emit=metadata")
        .arg("empty.rs")
        .arg("-o")
        .arg("raw-session.rmeta")
        .run();
    cmd(&trustc)
        .arg("-Ztrust-verify-crate-role=primary")
        .arg("-Ztrust-verify-package-name=pkg")
        .arg("-Ztrust-verify-session=session")
        .arg("--emit=metadata")
        .arg("empty.rs")
        .arg("-o")
        .arg("primary-session.rmeta")
        .run();

    // Cargo/rustc JSON mode must carry crate-level coverage through a
    // compiler-owned diagnostic envelope. A raw TRUST_JSON stderr line has no
    // Cargo package/target provenance and Targo deliberately rejects it.
    let json_stderr = cmd(&trustc)
        .arg("-Ztrust-verify-output=json")
        .arg("-Ztrust-verify-crate-role=primary")
        .arg("-Ztrust-verify-package-name=coverage-package")
        .arg("-Ztrust-verify-session=coverage-session")
        .arg("--error-format=json")
        .arg("--crate-name=coverage_envelope_probe")
        .arg("empty.rs")
        .arg("-o")
        .arg("coverage-envelope-probe")
        .run()
        .stderr_utf8();
    let coverage_lines: Vec<_> =
        json_stderr.lines().filter(|line| line.contains("coverage_summary")).collect();
    assert!(!coverage_lines.is_empty(), "missing coverage summary:\n{json_stderr}");
    for line in coverage_lines {
        assert!(line.starts_with('{'), "coverage escaped the JSON diagnostic envelope: {line}");
        assert!(
            line.contains("trust_verification_transport_v1"),
            "coverage diagnostic lacks the compiler transport code: {line}"
        );
        for expected in [
            r#"\"crate_name\":\"coverage_envelope_probe\""#,
            r#"\"package_name\":\"coverage-package\""#,
            r#"\"primary_package\":true"#,
            r#"\"verification_session\":\"coverage-session\""#,
        ] {
            assert!(
                line.contains(expected),
                "coverage diagnostic lacks authenticated identity {expected}: {line}"
            );
        }
        assert!(
            !line.starts_with("TRUST_JSON:"),
            "coverage was emitted as unauthenticated raw stderr: {line}"
        );
    }

    // Raw trustc is strict batteries-on without relying on Targo to inject the
    // trust-cg gate. `off` is an explicit contradiction and is rejected before
    // backend selection.
    cmd(&trustc)
        .arg("-Ztrust-cg-output-gate=off")
        .arg("empty.rs")
        .run_fail()
        .assert_stderr_contains("incompatible with batteries-on strict Trust verification");

    // Strict verification owns the effective safety-check policy. Cargo release
    // profiles and direct callers can spell these flags as `no`, but they must
    // not be able to remove the MIR assertions before Trust analyzes the body.
    // `--print cfg` observes the Session values after driver callbacks and is a
    // lightweight end-to-end probe of the actual trustc option path.
    let strict_cfg = cmd(&trustc)
        .arg("-Cdebug-assertions=no")
        .arg("-Coverflow-checks=no")
        .arg("--print=cfg")
        .run()
        .stdout_utf8();
    for required in ["debug_assertions", "overflow_checks"] {
        assert!(
            strict_cfg.lines().any(|line| line == required),
            "strict verification did not force `{required}` on; cfg output:\n{strict_cfg}"
        );
    }

    let vanilla_cfg = cmd(&trustc)
        .arg("-Ztrust-verify=off")
        .arg("-Cdebug-assertions=no")
        .arg("-Coverflow-checks=no")
        .arg("--print=cfg")
        .run()
        .stdout_utf8();
    for forbidden in ["debug_assertions", "overflow_checks"] {
        assert!(
            vanilla_cfg.lines().all(|line| line != forbidden),
            "vanilla compilation did not preserve `{forbidden}=no`; cfg output:\n{vanilla_cfg}"
        );
    }

    // Evidence outputs must be paired with the compiler route that can
    // actually produce them. Reject mismatches before compilation instead of
    // succeeding with an empty/missing output directory.
    for (flag, expected) in [
        (
            "-Ztrust-verify=off -Ztrust-dump=ir:orphan-ir",
            "-Ztrust-dump=ir:<dir> requires batteries-on verification or -Ztrust-ir-lower",
        ),
        (
            "-Ztrust-verify=off -Ztrust-dump=mir:orphan-mir",
            "require batteries-on Trust verification",
        ),
        (
            "-Ztrust-verify=off -Ztrust-dump=native-bundle:orphan-native",
            "require batteries-on Trust verification",
        ),
        ("-Ztrust-dump=mir-only", "incorrect value `mir-only` for unstable option `trust-dump`"),
        ("-Ztrust-dump=mir:a -Ztrust-dump=mir-only:b", "incorrect value `mir-only:b`"),
        (
            "-Ztrust-dump=mir-only:dump-only-strict",
            "skips proof dispatch and therefore requires the nonfatal",
        ),
    ] {
        let mut command = cmd(&trustc);
        for arg in flag.split_whitespace() {
            command.arg(arg);
        }
        command.arg("empty.rs").run_fail().assert_stderr_contains(expected);
    }

    // Dump-only is an explicit dependency-tracked compiler policy, not an
    // ambient shortcut. Its valid envelope both publishes MIR and remains
    // visibly nonfatal/unknown instead of claiming a proof.
    cmd(&trustc)
        .arg("-Ztrust-policy=advisory")
        .arg("-Ztrust-dump=mir-only:dump-only-mir")
        .arg("empty.rs")
        .arg("-o")
        .arg("dump-only-probe")
        .run();
    assert!(
        std::fs::read_dir("dump-only-mir").expect("dump-only MIR directory").next().is_some(),
        "did not publish any requested MIR input"
    );

    // Trust: explicitly requested proof-input dumps must fail loudly. A
    // successful compiler exit with missing evidence is unsafe for every
    // downstream consumer, not just `targo trust prove --source`.
    rfs::write("not-a-directory", "occupied\n");
    cmd(&trustc)
        .arg("-Ztrust-dump=mir-only:not-a-directory")
        .arg("empty.rs")
        .arg("-o")
        .arg("dump-probe")
        .run_fail()
        .assert_stderr_contains("failed to create -Ztrust-dump=mir:<dir> directory");

    // The crate-level TrustIr finalizer must surface publication failures as a
    // compiler error. It used to hide them in a debug-only summary.
    rfs::write("ir-not-a-directory", "occupied\n");
    cmd(&trustc)
        .arg("-Ztrust-dump=ir:ir-not-a-directory")
        .arg("--crate-name=ir_dump_failure_probe")
        .arg("empty.rs")
        .arg("-o")
        .arg("ir-dump-failure-probe")
        .run_fail()
        .assert_stderr_contains("trust-ir-lower artifact target preparation failed");

    // Drive one clause through each of the six physical AST lanes, in a
    // deliberately non-grouped function-wide order. The MIR-compat dump below
    // is a stable compiler-level seam after source parsing, AST -> HIR lowering,
    // the public `trust_contracts` query, and conversion to the public
    // VerifiableFunction inventory. Lane-unique parameter names let the test
    // distinguish every clause without depending on expression pretty-printing.
    rfs::write(
        "contract-order.rs",
        r#"#![feature(contracts)]
#![feature(contracts_internals)]
#![crate_type = "lib"]

pub fn ordered(
    lane0: bool,
    lane1: bool,
    lane2: bool,
    lane3: bool,
    lane4: bool,
    lane5: bool,
) -> bool
trust_contract_ensures { move |ret| *ret == lane0 }
requires lane1
trust_contract_requires { forall(i, 0..1, lane2) }
ensures result == lane3
contract_requires { lane4 }
trust_contract_ensures { result == lane5 }
{
    lane0 && lane1 && lane2 && lane3 && lane4 && lane5
}

// `cfg_attr`/macro expansion is permitted to give clause payloads enclosing
// or source-equal spans. These four typed clauses must remain bound to their
// exact AST/HIR expression identities, not whichever expression happens to be
// the first span match in the lowered body.
macro_rules! define_exact_attribute_identity {
    () => {
        #[cfg_attr(all(), core::contracts::requires(first))]
        #[cfg_attr(all(), core::contracts::ensures({
            let unrelated = |_: &bool| false;
            let _ = unrelated;
            move |ret: &bool| *ret == first
        }))]
        #[cfg_attr(all(), core::contracts::requires(second))]
        #[cfg_attr(all(), core::contracts::ensures(move |ret: &bool| *ret == second))]
        pub fn exact_attribute_identity(first: bool, second: bool) -> bool {
            first && second
        }
    };
}
define_exact_attribute_identity!();
"#,
    );

    // Artifact-only TrustIr output is explicit, dependency-accounted, and
    // actually reaches the per-Session crate registry. Batteries-on trustc
    // enables the direct producer without a redundant `-Ztrust-ir-lower`.
    // The direct Rust/THIR artifact remains structural/parity-only even though
    // the retained MIR-compatibility path sees a real, ordered contract
    // inventory: direct SSA contract ownership is not wired yet.
    cmd(&trustc)
        .arg("-Ztrust-dump=ir:ir-dump")
        .arg("-Ztrust-policy=advisory")
        .arg("-Ztrust-dump=mir-only:mir-compat-dump")
        .arg("-Cincremental=ir-dump-incremental")
        .arg("--crate-name=ir_dump_probe")
        .arg("contract-order.rs")
        .arg("-o")
        .arg("ir-dump-probe")
        .run();
    let first_direct_artifacts =
        read_and_assert_direct_ir_artifacts("ir-dump", "ir_dump_probe", "fn @ordered(");
    read_and_assert_mir_compat_contract_order(
        "mir-compat-dump",
        "ir_dump_probe::ordered",
        &[
            ("Ensures", "lane0"),
            ("Requires", "lane1"),
            ("Requires", "lane2"),
            ("Ensures", "lane3"),
            ("Requires", "lane4"),
            ("Ensures", "lane5"),
        ],
        false,
    );
    read_and_assert_mir_compat_contract_order(
        "mir-compat-dump",
        "ir_dump_probe::exact_attribute_identity",
        &[
            ("Requires", "__trust_lowered_compiler_contract__:first"),
            ("Ensures", "__trust_lowered_compiler_contract__:(result) == (first)"),
            ("Requires", "__trust_lowered_compiler_contract__:second"),
            ("Ensures", "__trust_lowered_compiler_contract__:(result) == (second)"),
        ],
        true,
    );

    // A green incremental query must replay its per-Session direct-lowering
    // registry into a freshly cleared publication directory. Otherwise a
    // successful rebuild can silently publish no canonical TrustIr evidence.
    rfs::remove_dir_all("ir-dump");
    cmd(&trustc)
        .arg("-Ztrust-dump=ir:ir-dump")
        .arg("-Ztrust-policy=advisory")
        .arg("-Ztrust-dump=mir-only:mir-compat-dump")
        .arg("-Cincremental=ir-dump-incremental")
        .arg("--crate-name=ir_dump_probe")
        .arg("contract-order.rs")
        .arg("-o")
        .arg("ir-dump-probe")
        .run();
    let replayed_direct_artifacts =
        read_and_assert_direct_ir_artifacts("ir-dump", "ir_dump_probe", "fn @ordered(");
    for (suffix, (first, replayed)) in ["trust-ir.bin", "trust-ir.txt", "coverage.json"]
        .into_iter()
        .zip(first_direct_artifacts.iter().zip(&replayed_direct_artifacts))
    {
        assert!(
            first == replayed,
            "green-query replay changed `{suffix}` instead of reproducing the exact artifact"
        );
    }
}
