use std::collections::HashSet;

use super::should_install_extended_tool_for_tool_settings;

const MACOS_DISTRIBUTION: &str =
    include_str!(concat!(env!("CARGO_MANIFEST_DIR"), "/../etc/installer/pkg/Distribution.xml"));
const WINDOWS_INSTALLER: &str =
    include_str!(concat!(env!("CARGO_MANIFEST_DIR"), "/../etc/installer/msi/rust.wxs"));

fn opening_xml_element<'a>(document: &'a str, marker: &str) -> &'a str {
    let start =
        document.find(marker).unwrap_or_else(|| panic!("missing XML marker `{marker}`"));
    let remaining = &document[start..];
    let end =
        remaining.find('>').unwrap_or_else(|| panic!("unterminated XML element `{marker}`"));
    &remaining[..=end]
}

#[test]
fn rust_compatible_config_names_select_trust_install_tools() {
    for (config_tool, package_tool) in [
        ("cargo", "targo"),
        ("cargo-trust", "targo-trust"),
        ("rustdoc", "trustdoc"),
        ("rustfmt", "trustfmt"),
        ("cargo-fmt", "trustfmt"),
        ("clippy", "tippy"),
        ("cargo-clippy", "tippy"),
        ("clippy-driver", "tippy"),
        ("rust-analyzer", "trust-analyzer"),
        ("miri", "trust-miri"),
        ("cargo-miri", "trust-miri"),
        ("llvm-tools", "trust-llvm-tools"),
    ] {
        let tools = HashSet::from_iter([config_tool.to_string()]);
        assert!(
            should_install_extended_tool_for_tool_settings(true, Some(&tools), package_tool),
            "config tool `{config_tool}` should select Trust install package `{package_tool}`"
        );
    }
}

#[test]
fn trust_companion_binary_names_select_their_install_package() {
    for (config_tool, package_tool) in [
        ("targo-fmt", "trustfmt"),
        ("tippy", "tippy"),
        ("targo-tippy", "tippy"),
        ("tippy-driver", "tippy"),
        ("targo-miri", "trust-miri"),
    ] {
        let tools = HashSet::from_iter([config_tool.to_string()]);
        assert!(
            should_install_extended_tool_for_tool_settings(true, Some(&tools), package_tool),
            "config tool `{config_tool}` should select Trust install package `{package_tool}`"
        );
    }
}

#[test]
fn install_tool_selection_still_requires_extended_builds() {
    let tools = HashSet::from_iter(["cargo".to_string()]);

    assert!(!should_install_extended_tool_for_tool_settings(false, Some(&tools), "targo"));
    assert!(should_install_extended_tool_for_tool_settings(true, None, "targo"));
}

#[test]
fn macos_verifier_and_linter_choices_force_their_runtime_components() {
    for dependency in ["trustc", "trust-std", "targo"] {
        let choice =
            opening_xml_element(MACOS_DISTRIBUTION, &format!("<choice id=\"{dependency}\""));
        assert!(
            choice.contains("choices['targo-trust'].selected"),
            "macOS `{dependency}` choice must be forced by targo-trust: {choice}"
        );
        assert!(
            choice.contains("choices['tippy'].selected"),
            "macOS `{dependency}` choice must be forced by tippy: {choice}"
        );
    }
}

#[test]
fn windows_required_runtime_components_are_mandatory() {
    for dependency in ["Rustc", "Std", "Cargo"] {
        let feature =
            opening_xml_element(WINDOWS_INSTALLER, &format!("<Feature Id=\"{dependency}\""));
        assert!(
            feature.contains("Absent=\"disallow\""),
            "Windows `{dependency}` feature must be mandatory: {feature}"
        );
    }
}
