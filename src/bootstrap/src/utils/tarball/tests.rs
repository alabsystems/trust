use super::OverlayKind;

#[test]
fn targo_trust_overlay_uses_component_readme() {
    assert_eq!(
        OverlayKind::TCargoTrust.legal_and_readme(),
        &["COPYRIGHT", "LICENSE-APACHE", "LICENSE-MIT", "targo-trust/README.md"]
    );
}
