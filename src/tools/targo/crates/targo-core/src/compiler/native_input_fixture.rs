// SPDX-License-Identifier: MIT OR Apache-2.0
// Copyright 2026 Andrew Yates

//! Trust: a real native image for data/custody controls, without the test
//! binary's Git/TLS runtime dependencies. It is not a managed SDK, compiler
//! admission, or verification fixture.

use std::path::{Path, PathBuf};

pub(crate) fn materialize(root: &Path) -> PathBuf {
    let program = root.join("bin/native-input-fixture");
    std::fs::create_dir_all(program.parent().unwrap()).unwrap();
    // These Mac ARM controls observe native image DATA and system-runtime
    // dependencies, not compiler execution or SDK support. A real immutable
    // OS image supplies those inputs without compiling a new program per test.
    // Held native inputs deliberately require one unambiguous arm64 image.
    // The system tool is universal; extract its actual arm64e member without
    // broadening that validator or creating synthetic Mach-O bytes.
    let output = std::process::Command::new("/usr/bin/lipo")
        .args(["/usr/bin/true", "-thin", "arm64e", "-output"])
        .arg(&program)
        .output()
        .expect("extract the actual system-runtime image");
    assert!(
        output.status.success(),
        "native image extraction failed: {output:?}"
    );
    program
}
