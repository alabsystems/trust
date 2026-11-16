use super::*;

#[test]
fn actual_scalar_extension_and_pointer_facts_are_preserved_without_legacy_attributes() {
    let mut attrs = ArgAttributes::new();
    attrs.arg_ext = ArgExtension::Sext;
    attrs.set(ArgAttribute::InReg | ArgAttribute::NoUndef | ArgAttribute::NonNull
        | ArgAttribute::ReadOnly | ArgAttribute::CapturesReadOnly);
    attrs.pointee_size = rustc_abi::Size::from_bytes(23);
    attrs.pointee_align = Some(rustc_abi::Align::from_bytes(8).unwrap());
    let carried = lower_attributes(&attrs);
    assert_eq!(carried.extension, AbiExtension::Sign);
    assert!(carried.in_reg && carried.no_undef && carried.nonnull && carried.readonly);
    assert_eq!(carried.capture, AbiCapture::ReadOnly);
    assert_eq!(carried.pointee_size, 23);
    assert_eq!(carried.pointee_align, Some(8));
    assert!(!carried.no_alias && !carried.writable && !carried.no_free);
    attrs.regular |= ArgAttribute::CapturesNone;
    assert_eq!(lower_attributes(&attrs).capture, AbiCapture::None);
}
