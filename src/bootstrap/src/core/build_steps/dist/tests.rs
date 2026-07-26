use super::*;

#[test]
fn cargo_dist_exposes_targo_and_cargo_bins() {
    let target = TargetSelection::from_user("x86_64-unknown-linux-gnu");

    assert_eq!(cargo_dist_bin_names(target), ["targo".to_string(), "cargo".to_string()]);
}

#[test]
fn compiler_dist_keeps_only_required_compiler_compatibility_alias() {
    let target = TargetSelection::from_user("x86_64-unknown-linux-gnu");

    assert_eq!(compiler_dist_bin_names(target), ["trustc".to_string(), "rustc".to_string()]);
}

#[test]
fn compiler_dist_uses_trust_only_secondary_tool_names() {
    let target = TargetSelection::from_user("x86_64-unknown-linux-gnu");

    assert_eq!(trustdoc_dist_bin_names(target), ["trustdoc".to_string()]);
    assert_eq!(
        rust_analyzer_proc_macro_dist_bin_names(target),
        ["trust-analyzer-proc-macro-srv".to_string()]
    );
}

#[test]
fn tippy_dist_exposes_direct_subcommand_and_driver_bins() {
    let target = TargetSelection::from_user("x86_64-unknown-linux-gnu");

    assert_eq!(
        tippy_dist_bin_names(target),
        ["tippy".to_string(), "targo-tippy".to_string(), "tippy-driver".to_string()]
    );
}

#[test]
fn debugger_scripts_install_only_canonical_trust_entrypoints() {
    let linux = TargetSelection::from_user("x86_64-unknown-linux-gnu");
    let linux_names = debugger_script_entrypoints(linux)
        .into_iter()
        .map(|(_, destination)| destination)
        .collect::<Vec<_>>();
    assert_eq!(linux_names, ["trust-gdb", "trust-gdbgui", "trust-lldb"]);

    let windows = TargetSelection::from_user("x86_64-pc-windows-msvc");
    let windows_names = debugger_script_entrypoints(windows)
        .into_iter()
        .map(|(_, destination)| destination)
        .collect::<Vec<_>>();
    assert_eq!(windows_names, ["trust-windbg.cmd", "trust-gdb", "trust-gdbgui", "trust-lldb"]);

    assert!(linux_names.iter().all(|name| !name.starts_with("rust-")));
    assert!(windows_names.iter().all(|name| !name.starts_with("rust-")));
}
