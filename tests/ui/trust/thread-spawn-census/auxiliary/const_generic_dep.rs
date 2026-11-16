//@ compile-flags: --crate-type=rlib -Ztrust-verify=off
//@ edition: 2021
//@ no-prefer-dynamic
//! A dependency whose const-generic functions drop a `[_; N]` of a type that
//! needs a drop, for `const_generic_drop_at_instance.rs`. Their MIR is in this
//! crate's metadata (they are generic), so the consuming crate's census walks
//! them at its instances. `node` is ay-chc's `dt`, in ay-chc's edition (2021,
//! where the array's `into_iter` is by value): the array is dropped on the
//! path where `to_string` unwinds. `drop_fields` and `drop_launchers` drop it
//! on return, and `Launcher`'s `#[inline]` `Drop` impl starts a thread.

pub enum Field {
    Leaf(u8),
    Node(String, Vec<Field>),
}

pub fn node<const N: usize>(ctor: &str, fields: [Field; N]) -> Field {
    Field::Node(ctor.to_string(), fields.into_iter().collect())
}

pub fn drop_fields<const N: usize>(_fields: [Field; N]) {}

pub struct Launcher;

impl Drop for Launcher {
    #[inline]
    fn drop(&mut self) {
        let _handle = std::thread::spawn(|| {});
    }
}

pub fn drop_launchers<const N: usize>(_launchers: [Launcher; N]) {}
