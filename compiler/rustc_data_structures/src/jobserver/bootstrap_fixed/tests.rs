// Trust: these real local transport checks confer no native compiler authority.
use super::*;
#[test]
fn original_gnu_witnesses_preserve_credit_population_and_reject_a_foreign_pool() {
    let original = jobserver_crate::Client::new(2).unwrap();
    let before = original.available().unwrap();
    let (descriptions, identity) = witnesses(&original).unwrap();
    check_gnu_identity(&identity, &descriptions.each_ref().map(AsFd::as_fd)).unwrap();
    assert_eq!(original.available().unwrap(), before);
    let foreign = jobserver_crate::Client::new(2).unwrap();
    let (other, _) = witnesses(&foreign).unwrap();
    assert!(check_gnu_identity(&identity, &other.each_ref().map(AsFd::as_fd)).is_err());
    drop(descriptions);
    assert_eq!(original.available().unwrap(), before);
}
