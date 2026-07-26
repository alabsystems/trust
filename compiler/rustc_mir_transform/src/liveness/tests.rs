//! Tokenized, position-aware matching of a contract clause's source text
//! against a local's name. The helper is private because a looser match
//! would silently keep a clause-mentioned local live; these cases pin the
//! exact boundary it draws.

use super::contract_source_mentions_identifier;

#[test]
fn trust_clause_source_matching_is_tokenized_and_position_aware() {
    assert!(contract_source_mentions_identifier("requires x > 0", "x"));
    assert!(contract_source_mentions_identifier("requires *x > 0", "x"));
    assert!(contract_source_mentions_identifier("requires xs.len() > 0", "xs"));
    assert!(contract_source_mentions_identifier("decreases n", "n"));
    assert!(contract_source_mentions_identifier("requires r#value > 0", "value"));
    assert!(!contract_source_mentions_identifier("requires max > 0", "x"));
    assert!(!contract_source_mentions_identifier("requires αx > 0", "x"));
    assert!(!contract_source_mentions_identifier("requires holder.x > 0", "x"));
    assert!(!contract_source_mentions_identifier("requires Type::x > 0", "x"));
    assert!(!contract_source_mentions_identifier("requires x::VALUE > 0", "x"));
    assert!(!contract_source_mentions_identifier("requires value == \"x\"", "x"));
    assert!(!contract_source_mentions_identifier("requires value > 0 // x", "x"));
}
