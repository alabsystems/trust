
fn main() {
    if std::env::args().nth(1).as_deref() == Some("creates-overflow") {
        let _ = rhs_creates_overflow();
        panic!("missing arithmetic overflow");
    }
    assert_eq!(by_ref_capture(), 11);
    assert_eq!(by_value_capture(), 11);
    assert_eq!(rhs_removes_overflow(), 1);
    assert_eq!(unchanged_control(), 2);
}
