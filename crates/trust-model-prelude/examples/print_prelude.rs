// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Print the served prelude: every module of `MODULES`, in order, concatenated.
//! Each module is preceded by a `-- module <name>` comment line, so the output
//! elaborates as one Clean unit and still says where each module starts.

fn main() {
    let mut out = String::new();
    for (name, _, source) in trust_model_prelude::MODULES {
        out.push_str("-- module ");
        out.push_str(name);
        out.push('\n');
        out.push_str(source);
        if !source.ends_with('\n') {
            out.push('\n');
        }
    }
    print!("{out}");
}
