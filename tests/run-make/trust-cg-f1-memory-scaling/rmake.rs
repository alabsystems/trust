//! Trust (plan item K, 2026-10-01): F1's peak memory does not grow with the
//! number of functions times the module size.
//!
//! Every F1 function used to carry its own full clone of the crate module until
//! emission, so peak RSS grew quadratically: 3,200 one-line functions took
//! 23.6 GB (fixed by `a3be88bbde`; the per-function function-table copy in
//! `assembled_internal_object_globals` by `dc4eab4d29`). Extrapolated from that
//! measurement, the old code adds about 1.4 GB between the 200- and 800-function
//! crates below; the fixed code adds about 30 MB on both lanes (measured
//! 2026-10-02: 253 MB -> 284 MB handoff, 253 MB -> 281 MB crate-module). The
//! bound is 300 MB of growth: far above today's cost, far below the old one.
//! Memory, not time, because it does not depend on machine load.
//!
//! NEGATIVE CONTROL, run 2026-10-02: restoring the per-function deep clone on the
//! crate-module lane only made that lane grow 1,353 MB (342 MB -> 1,695 MB) and this
//! recipe fail with its message, while the handoff lane stayed at 28 MB.

//@ needs-trust-cg-backend
//@ only-apple
//@ only-aarch64

use run_make_support::{cmd, rfs, rustc_path};

fn crate_of(n: usize) -> String {
    let mut src = String::from("#![crate_name = \"k\"]\n");
    for i in 0..n {
        src.push_str(&format!("pub fn f{i}(x: u32) -> u32 {{ (x ^ {i}) & 0xff }}\n"));
    }
    src
}

/// Peak RSS in bytes of one F1 compile, from `/usr/bin/time -l`.
fn peak_rss(n: usize, crate_module_lane: bool) -> u64 {
    let input = format!("c{n}.rs");
    rfs::write(&input, crate_of(n));
    let out = format!("out_{n}_{crate_module_lane}");
    rfs::create_dir(&out);
    let mut time = cmd("/usr/bin/time");
    time.arg("-l")
        .arg(rustc_path())
        .arg(&input)
        .args(["--crate-type", "lib", "--edition", "2021", "-Cpanic=abort"])
        .args(["-Zunstable-options", "-Zcodegen-backend=trust-cg", "-Ztrust-verify=off"])
        .args(["-Ztrust-ir-lower", "-Ztrust-cg-frontend=trust-ir"])
        .args(["--out-dir", &out]);
    if crate_module_lane {
        time.arg("-Ztrust-ir-crate-module");
    }
    let output = time.run();
    let stderr = output.stderr_utf8();
    stderr
        .lines()
        .find(|line| line.contains("maximum resident set size"))
        .and_then(|line| line.split_whitespace().next())
        .and_then(|bytes| bytes.parse().ok())
        .unwrap_or_else(|| panic!("no peak RSS in /usr/bin/time output:\n{stderr}"))
}

fn main() {
    const BOUND: u64 = 300 * 1024 * 1024;
    for crate_module_lane in [false, true] {
        let small = peak_rss(200, crate_module_lane);
        let large = peak_rss(800, crate_module_lane);
        let growth = large.saturating_sub(small);
        eprintln!(
            "F1_MEMORY_SCALING lane={} rss200={}MB rss800={}MB growth={}MB",
            if crate_module_lane { "crate-module" } else { "handoff" },
            small >> 20,
            large >> 20,
            growth >> 20
        );
        assert!(
            growth < BOUND,
            "F1 peak RSS grew {}MB from 200 to 800 functions (bound {}MB): a per-function \
             whole-module copy is back (plan item K)",
            growth >> 20,
            BOUND >> 20
        );
    }
}
