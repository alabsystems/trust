fn main() {
    match std::env::args().nth(1).as_deref() {
        Some("assert") => {
            checked(false);
            return;
        }
        Some("oob") => {
            unit_oob();
            return;
        }
        Some("zero") => {
            unit_zero_index();
            return;
        }
        Some("dynamic") => {
            indexed_dynamic(4);
            return;
        }
        _ => {}
    }
    assert_eq!(once(), 1);
    assert_eq!(zero(), 1);
    assert_eq!(looped(), 3);
    assert_eq!(branches(true), 2);
    assert_eq!(branches(false), 5);
    assert_eq!(nested(), 3);
    assert_eq!(many(), 1);
    assert_eq!(early_return(), 7);
    assert_eq!(from_named(), 1);
    assert_eq!(indexed(), 1);
    assert_eq!(checked(true), 1);
    assert_eq!(one(), 1);
    assert_eq!(indexed_dynamic(0), 3);
    assert_eq!(indexed_dynamic(3), 3);
    assert_eq!(index_base_and_index(), 2);
    assert_eq!(array_reassign_during_index(), 1);
    assert_eq!(rest(), 12);
    assert_eq!(local_slice_len(), 14);
    assert_eq!(inline_slice_len(), 14);
}
