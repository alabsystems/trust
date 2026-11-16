//! Booking DATA controls only; no actual compiler/pause/native issuer fixture.
use super::*;
fn request(generation: u64, member: u8) -> PairedLinkerRequest {
    let mut value = crate::bootstrap_graph::compilation::compiler::tests::linker();
    value.generation = generation;
    value.member = [member; 16];
    value
}
#[test]
fn one_original_primary_cannot_be_lent_twice_or_refunded_by_a_foreign_generation() {
    let mut loans = Loans::default();
    let first = request(1, 61);
    loans.begin(&first).unwrap();
    assert!(loans.begin(&request(1, 62)).is_err());
    assert!(loans.begin(&request(2, 62)).is_err());
    assert!(loans.end(&request(2, 62).retirement()).is_err());
    loans.end(&first.retirement()).unwrap();
    assert!(loans.begin(&first).is_err());
    assert!(loans.begin(&request(2, 61)).is_err(), "member nonce survives closure");
    loans.begin(&request(5, 62)).unwrap();
    assert_eq!(loans.active, Some((5, [62; 16])));
}
