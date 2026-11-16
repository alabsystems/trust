// Tests `rustc --help` and similar invocations against snapshots and each other.

// FIXME: Once GCC backend is fixed, remove this `ignore-backends`.
//@ ignore-backends: gcc

use run_make_support::{bare_rustc, diff, similar};

/// Trust: the help text names the driver that was INVOKED — `Usage: trustc` on
/// the branded lane, `Usage: rustc` under `--trust-vanilla`, which runs through
/// a wrapper so upstream-compatibility output stays byte-for-byte upstream.
/// BOTH lanes compare against the SAME snapshot, so no single spelling can
/// satisfy them: measured, `trustc` fails vanilla and `rustc` fails verified.
///
/// The snapshots therefore stay upstream-pristine and the invocation-derived
/// name is folded here, per test, rather than in `run_make_support::diff` —
/// a fold in the shared helper would blind EVERY run-make snapshot to a
/// drop-in naming regression, which is a release gate for this fork.
const INVOKED_DRIVER: (&str, &str) = (r"\btrustc\b", "rustc");

fn main() {
    // `rustc --help`
    let help = bare_rustc().arg("--help").run().stdout_utf8();
    diff()
        .expected_file("help.stdout")
        .actual_text("(rustc --help)", &help)
        .normalize(INVOKED_DRIVER.0, INVOKED_DRIVER.1)
        .run();

    // `rustc` should be the same as `rustc --help`
    let bare = bare_rustc().run().stdout_utf8();
    diff().expected_text("(rustc --help)", &help).actual_text("(rustc)", &bare).run();

    // `rustc --help -v` should give a similar but longer help message
    let help_v = bare_rustc().arg("--help").arg("-v").run().stdout_utf8();
    diff()
        .expected_file("help-v.stdout")
        .actual_text("(rustc --help -v)", &help_v)
        .normalize(INVOKED_DRIVER.0, INVOKED_DRIVER.1)
        .run();

    // Check the diff between `rustc --help` and `rustc --help -v`.
    let help_v_diff = similar::TextDiff::from_lines(&help, &help_v).unified_diff().to_string();
    // The diff BODY also carries the driver name: the `--help -v` row that
    // `--help` lacks reads "the full set of options <driver> accepts".
    diff()
        .expected_file("help-v.diff")
        .actual_text("actual", &help_v_diff)
        .normalize(INVOKED_DRIVER.0, INVOKED_DRIVER.1)
        .run();

    // Check that all help options can be invoked at once
    let codegen_help = bare_rustc().arg("-Chelp").run().stdout_utf8();
    let unstable_help = bare_rustc().arg("-Zhelp").run().stdout_utf8();

    let polonius_help =
        format!("{}\n", unstable_help.lines().find(|line| line.contains("polonius=val")).unwrap());
    let version = bare_rustc().arg("--version").run().stdout_utf8();
    let expected_file = if version.contains("-nightly") || version.contains("-dev") {
        "polonius-help.stdout"
    } else {
        "polonius-help-stable.stdout"
    };
    diff()
        .expected_file(expected_file)
        .actual_text("rustc -Zhelp (polonius)", &polonius_help)
        .run();

    let lints_help = bare_rustc().arg("-Whelp").run().stdout_utf8();
    let expected_all = format!("{help}{codegen_help}{unstable_help}{lints_help}");
    let all_help = bare_rustc().args(["--help", "-Chelp", "-Zhelp", "-Whelp"]).run().stdout_utf8();
    diff()
        .expected_text(
            "(rustc --help && rustc -Chelp && rustc -Zhelp && rustc -Whelp)",
            &expected_all,
        )
        .actual_text("(rustc --help -Chelp -Zhelp -Whelp)", &all_help)
        .run();

    // Check that the ordering of help options is respected
    // Note that this is except for `-Whelp`, which always comes last
    let expected_ordered_help = format!("{unstable_help}{codegen_help}{help}{lints_help}");
    let ordered_help =
        bare_rustc().args(["-Whelp", "-Zhelp", "-Chelp", "--help"]).run().stdout_utf8();
    diff()
        .expected_text(
            "(rustc -Whelp && rustc -Zhelp && rustc -Chelp && rustc --help)",
            &expected_ordered_help,
        )
        .actual_text("(rustc -Whelp -Zhelp -Chelp --help)", &ordered_help)
        .run();

    // Test that `rustc --help` does not suppress invalid flag errors
    let help = bare_rustc().arg("--help --invalid-flag").run_fail().stdout_utf8();
}
