// Calling rustdoc with no arguments, which should bring up a help menu, used to
// cause an error as rustdoc expects an input file. Fixed in #98331, this test
// ensures the output of rustdoc's help menu is as expected.
// See https://github.com/rust-lang/rust/issues/88756

use run_make_support::{bare_rustdoc, diff};

fn main() {
    let out = bare_rustdoc().run().stdout_utf8();
    diff()
        .expected_file("output-default.stdout")
        .actual_text("actual", out)
        // replace the channel type in the URL with $CHANNEL
        .normalize(r"nightly/|beta/|stable/|1\.[0-9]+\.[0-9]+/", "$$CHANNEL/")
        // Trust: the usage line names the driver that was INVOKED -- `trustdoc`
        // on the branded lane, `rustdoc` under `--trust-vanilla` -- and one
        // snapshot is compared by both lanes, so it stays pristine and the name
        // is folded here. The OTHER Trust wording in this snapshot (`--cfg to
        // trustc`, "this documentation tool's version") is static in
        // src/librustdoc/lib.rs, identical in both lanes, and is ledgered
        // rather than folded.
        .normalize(r"(?m)^trustdoc \[options\]", "rustdoc [options]")
        .normalize(r"documentation for trustdoc\.", "documentation for rustdoc.")
        .run();
}
