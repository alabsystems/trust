extern crate source_claim_dep;
pub fn check(x: u64, y: u64) -> (u64, u64, u64, u64, u64) {
    (
        source_claim_dep::identity(x),
        source_claim_dep::double(x),
        source_claim_dep::pair(x, y),
        source_claim_dep::statements(x),
        source_claim_dep::located(x),
    )
}
