use super::{OutputType, OutputTypes};

#[test]
fn trust_ir_output_kind_remains_analysis_only() {
    assert_eq!(OutputType::from_shorthand("trust-ir"), Some(OutputType::TrustIr));

    let trust_ir = OutputTypes::new(&[(OutputType::TrustIr, None)]);
    assert!(trust_ir.trust_ir_only());
    assert!(!trust_ir.should_codegen());
    assert!(!trust_ir.should_link());

    let with_dep_info =
        OutputTypes::new(&[(OutputType::TrustIr, None), (OutputType::DepInfo, None)]);
    assert!(with_dep_info.trust_ir_only());
    assert!(!with_dep_info.should_codegen());
    assert!(!with_dep_info.should_link());

    let mixed = OutputTypes::new(&[(OutputType::TrustIr, None), (OutputType::Metadata, None)]);
    assert!(!mixed.trust_ir_only());
}
