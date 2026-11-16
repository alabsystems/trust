//@ needs-symlink

use std::path::{Path, PathBuf};

use run_make_support::{bin_name, cmd, rfs, rustc_path};

fn trustc() -> PathBuf {
    let rustc = PathBuf::from(rustc_path());
    let candidate = rustc.with_file_name(bin_name("trustc"));
    if candidate.exists() { candidate } else { rustc }
}

fn write_source(name: &str, body: &str) -> String {
    let path = format!("{name}.rs");
    rfs::write(&path, body);
    path
}

fn compile_fail(name: &str, body: &str, expected: &str) {
    let source = write_source(name, body);
    cmd(trustc())
        // A CLAIMING lane, and that is the whole point of this helper. Since
        // `eac9434f541` (2026-09-22) `-Ztrust-verify=off` is the master off-switch:
        // a lane that claims no proof demotes a crate-level trust-ir finalization
        // failure to a WARNING and exits 0, which is deliberate and is pinned by
        // `tests/ui/trust/verify_off_invalid_module_is_a_warning.rs`. Under
        // `-Ztrust-verify=off` this helper's `.run_fail()` was asserting a fatality
        // the off lane does not promise, and it failed with `command unexpectedly
        // succeeded` the moment the run-make suite could run again.
        //
        // `-Ztrust-policy=strict` is required as well as `=on`, not decoration:
        // `trust_proof_claimed_by_flags` is `verify.is_on() && !policy.is_advisory()`
        // (compiler/rustc_session/src/session.rs), so `=advisory` would leave the
        // refusal a warning and make the assertions below vacuous. Same spelling as
        // the compiler-side control,
        // `tests/ui/trust/advisory_invalid_module_strict_control.rs`.
        .arg("-Ztrust-verify=on")
        .arg("-Ztrust-policy=strict")
        .arg("-Ztrust-ir-lower")
        .arg("--crate-type=lib")
        .arg(format!("--crate-name={name}"))
        .arg("--emit=metadata")
        .arg(&source)
        .arg("-o")
        .arg(format!("{name}.rmeta"))
        .run_fail()
        .assert_stderr_contains("trust-ir-lower semantic finalization failed")
        .assert_stderr_contains(expected);
}

fn anchor_function_id(text: &str, machine: &str, action: &str) -> usize {
    let prefix = format!("anchor machine \"{machine}\" action \"{action}\" function ");
    let line = text
        .lines()
        .find(|line| line.trim_start().starts_with(&prefix))
        .unwrap_or_else(|| panic!("missing typed anchor `{prefix}` in:\n{text}"));
    let tail = line.trim_start().strip_prefix(&prefix).unwrap();
    tail.split_whitespace().next().unwrap().parse().expect("numeric FuncId")
}

fn main() {
    let grid = write_source(
        "temporal_grid",
        r#"#![feature(register_tool)]
#![register_tool(trust)]
#![allow(dead_code)]

pub mod terminal {
    pub struct GridStorage {
        padding: u8,
        #[trust::var(name = "scrollback", kind = "Seq")]
        scrollback: u64,
    }

    pub struct Grid {
        prefix: u16,
        storage: GridStorage,
    }

    // Ordinary embeddings above an explicit action owner are uses, not competing
    // machine ownership. Two such wrappers must not make Grid ambiguous.
    pub struct LeftView { grid: Grid }
    pub struct RightView { grid: Grid }

    impl Grid {
        #[trust::action(name = "Erase", guard = "enabled", ghost = "scrollback' = empty")]
        pub fn erase(&mut self) {}
    }
}
"#,
    );
    cmd(trustc())
        .arg("-Ztrust-verify=off")
        .arg("-Ztrust-ir-lower")
        .arg("-Ztrust-dump=ir:grid-ir")
        .arg("--crate-type=lib")
        .arg("--crate-name=temporal_grid")
        .arg("--emit=metadata")
        .arg(&grid)
        .arg("-o")
        .arg("temporal_grid.rmeta")
        .run();

    let text_path = Path::new("grid-ir").join("temporal_grid.trust-ir.txt");
    let text = rfs::read_to_string(text_path);
    assert!(
        text.lines().any(|line| line == "module \"temporal_grid\""),
        "crate identity must be carried by Module.name:\n{text}"
    );
    let machine = "terminal::Grid";
    let block_start = text
        .find(&format!("spec_module \"{machine}\""))
        .unwrap_or_else(|| panic!("missing full-def-path Grid machine:\n{text}"));
    let block = &text[block_start..];
    assert_eq!(
        text.matches(&format!("spec_module \"{machine}\"")).count(),
        1,
        "Grid actions/descendant vars must be in one module:\n{text}"
    );
    assert!(
        !text.contains("spec_module \"terminal::GridStorage\""),
        "nested storage must not become a detached machine:\n{text}"
    );
    for required in [
        // The direct THIR temporal lane carries the authored projection/action
        // map but does NOT yet establish the behavioral contracts needed for
        // TrustIR's certifying `Linked` state, so `direct_temporal_spec_module`
        // (crate_module.rs) emits `design-only` — explicitly non-certifying until
        // that authority seam is wired and independently validated (hasty Linked
        // authority is exactly the forgeable-authority risk the roadmap flags).
        // This asserts the sound conservative state; flip to `linked` once the
        // authority lane lands with its own validation.
        "enforcement design-only",
        "var \"scrollback\" : \"Seq\"",
        "action \"Erase\"",
        "invariant \"scrollback.path\" : \"1,1\"",
        "invariant \"Erase.guard\" : \"enabled\"",
        "invariant \"Erase.ghost\" : \"scrollback' = empty\"",
        "project \"trust-ir.temporal-field-paths.v1\"",
        "target temporal-field-paths-v1",
    ] {
        assert!(block.contains(required), "missing `{required}` from Grid module:\n{block}");
    }
    assert!(
        !block.contains("Erase.fn"),
        "action identity must not use the legacy string invariant:\n{block}"
    );

    let function_id = anchor_function_id(&text, machine, "Erase");
    // WS5.2: `Function.name` is the link-time symbol; the annotated method is found by its
    // def path, carried as the function's `; #display-path:` directive.
    let function_offsets: Vec<usize> = text
        .match_indices('\n')
        .map(|(at, _)| at + 1)
        .chain(std::iter::once(0))
        .filter(|&at| text[at..].split('\n').next().is_some_and(|line| line.contains("fn @")))
        .collect::<std::collections::BTreeSet<_>>()
        .into_iter()
        .collect();
    let exact_path = "; #display-path: \"terminal::Grid::erase\"\n";
    let exact_index = function_offsets
        .iter()
        .position(|&at| {
            let end = text[at..].find("\n}\n").map_or(text.len(), |end| at + end);
            text[at..end].contains(exact_path)
        })
        .unwrap_or_else(|| panic!("missing exact action function `{exact_path}`:\n{text}"));
    assert_eq!(
        function_id, exact_index,
        "typed anchor FuncId must resolve to the annotated method"
    );
    let header_offset = function_offsets[exact_index];
    let action_body =
        &text[header_offset..text[header_offset..].find("\n}\n").unwrap() + header_offset];
    assert!(
        action_body.contains("bb0"),
        "typed action target must be a body-bearing function, not a declaration:\n{action_body}"
    );
    // WS5.2: the anchor's rust symbol is the bound function's NAME, its link-time symbol (the
    // spec link compares the two), while the def path is that function's display path above.
    let action_name = action_body
        .split_once("fn @")
        .and_then(|(_, tail)| tail.split_once('('))
        .map(|(name, _)| name.trim_matches('"'))
        .expect("the action function's header names it");
    assert!(action_name.starts_with("_R"), "a v0 link-time symbol: {action_name}");
    assert!(
        block.contains(&format!("rust \"{action_name}\"")),
        "the anchor must carry the bound function's link-time symbol `{action_name}`:\n{block}"
    );

    // A failed replacement with the same crate/output identity must invalidate
    // the preceding successful generation before semantic finalization. The
    // old binary/text/coverage set must not survive and masquerade as output
    // from this failed invocation.
    let stale_replacement = write_source(
        "temporal_grid_stale_replacement",
        r#"#![feature(register_tool)]
#![register_tool(trust)]
struct Detached { #[trust::var(name = "state", kind = "Int")] state: u64 }
"#,
    );
    cmd(trustc())
        // The claiming lane, for the same reason as `compile_fail` above: this
        // invocation asserts that the replacement REFUSES and that it purges the
        // earlier dump, and only a proof-claiming lane makes the finalization
        // failure fatal. The SUCCESSFUL invocation above deliberately stays on
        // `-Ztrust-verify=off` — it is measuring the off lane's own dump.
        .arg("-Ztrust-verify=on")
        .arg("-Ztrust-policy=strict")
        .arg("-Ztrust-ir-lower")
        .arg("-Ztrust-dump=ir:grid-ir")
        .arg("--crate-type=lib")
        .arg("--crate-name=temporal_grid")
        .arg("--emit=metadata")
        .arg(&stale_replacement)
        .arg("-o")
        .arg("temporal_grid_stale_replacement.rmeta")
        .run_fail()
        .assert_stderr_contains("trust-ir-lower semantic finalization failed")
        .assert_stderr_contains("has no #[trust::action] owner");
    for suffix in ["trust-ir.bin", "trust-ir.txt", "coverage.json"] {
        let path = Path::new("grid-ir").join(format!("temporal_grid.{suffix}"));
        assert!(
            !path.exists(),
            "failed replacement left stale direct-TrustIR artifact `{}` looking current",
            path.display()
        );
    }

    // Semantic annotation failures are fatal even without -Ztrust-dump=ir:<dir>.
    compile_fail(
        "temporal_malformed",
        r#"#![feature(register_tool)]
#![register_tool(trust)]
struct Machine { #[trust::var(name = "state")] state: u64 }
impl Machine { #[trust::action(name = "Step")] fn step(&mut self) {} }
"#,
        "missing required argument `kind`",
    );
    compile_fail(
        "temporal_duplicate_attr",
        r#"#![feature(register_tool)]
#![register_tool(trust)]
struct Machine { #[trust::var(name = "state", kind = "Int")] state: u64 }
impl Machine {
    #[trust::action(name = "Step")]
    #[trust::action(name = "Other")]
    fn step(&mut self) {}
}
"#,
        "attribute appears more than once",
    );
    compile_fail(
        "temporal_free_action",
        r#"#![feature(register_tool)]
#![register_tool(trust)]
#[trust::action(name = "Step")]
fn step() {}
"#,
        "#[trust::action] is only supported on methods in impl blocks",
    );
    compile_fail(
        "temporal_wrong_target_var",
        r#"#![feature(register_tool)]
#![register_tool(trust)]
#[trust::var(name = "state", kind = "Int")]
struct Machine { state: u64 }
"#,
        "#[trust::var] is only supported on fields of local structs",
    );
    compile_fail(
        "temporal_statement_var",
        r#"#![feature(register_tool, stmt_expr_attributes)]
#![register_tool(trust)]
fn misplaced() {
    #[trust::var(name = "state", kind = "Int")]
    let _state = 0_u64;
}
"#,
        "#[trust::var] is only supported on fields of local structs",
    );
    compile_fail(
        "temporal_ambiguous",
        r#"#![feature(register_tool)]
#![register_tool(trust)]
struct Storage { #[trust::var(name = "state", kind = "Int")] state: u64 }
struct Left { storage: Storage }
struct Right { storage: Storage }
impl Left { #[trust::action(name = "Step")] fn step(&mut self) {} }
"#,
        "ambiguous temporal owner",
    );
    compile_fail(
        "temporal_deep",
        r#"#![feature(register_tool)]
#![register_tool(trust)]
struct Inner { #[trust::var(name = "state", kind = "Int")] state: u64 }
struct Middle { inner: Inner }
struct Outer { middle: Middle }
impl Outer { #[trust::action(name = "Step")] fn step(&mut self) {} }
"#,
        "2 ownership edges below its action owner",
    );
}
