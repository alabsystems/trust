#![feature(type_alias_impl_trait)]
#![allow(dead_code)]

// Trust: share the unchanged tracked public receiver/GAT shapes with run-make.
#[path = "../../../../tests/run-make/trust-ir-shared-receiver-storage/subject.rs"]
mod fixture;

// Analysis already knows the hidden value is Freeze; the producer must not
// borrow that fact by revealing an opaque with no source Freeze bound.
type Hidden = impl Sized;
#[define_opaque(Hidden)]
fn make_hidden() -> Hidden {
    7usize
}
struct HiddenField {
    value: Hidden,
}
fn opaque_root(_: &Hidden) {}
fn opaque_field(_: &HiddenField) {}
