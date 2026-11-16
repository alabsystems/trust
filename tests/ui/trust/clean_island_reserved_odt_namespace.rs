//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=off
//@ check-fail
//@ dont-require-annotations: NOTE
//! TG16 (after TG11): the namespaces the compiler's E6 ODT reader mints into —
//! the readable aliases `trust_type_*` and the nominal identities `TrustOdt.*` —
//! are reserved against island declarations, as `trust_import_*` and
//! `trust_checked_*` are. Before TG16 these islands were accepted, and an island
//! that squatted a name the reader later generates turned the build's ODT
//! admission into a spanless fatal `DuplicateName` that named neither the island
//! nor a reservation. Each refusal is now at the declaration and names the
//! namespace. These islands are checked by the resolver's batch; the deferred
//! lane is `clean_island_reserved_odt_namespace_deferred.rs`. The names that only
//! contain a reserved spelling (`my_trust_type_helper`, `TrustOdtish`) are the
//! controls that the reservation is on the leading namespace: they are accepted.

clean {
    def my_trust_type_helper : Nat := 0
    def TrustOdtish : Nat := 1
}

clean {
    def trust_type_clean_island_reserved_odt_namespace__Phase.toTag (n : Nat) : UInt8 := 0
}
//~^^ ERROR declares into the compiler's ODT readable-alias namespace (`trust_type_*`)

clean {
    structure TrustOdt.Bar where
      x : UInt8
}
//~^^^ ERROR declares into the compiler's ODT nominal-type namespace (`TrustOdt.*`)

fn main() {}
