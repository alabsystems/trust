//@ compile-flags: --crate-type=rlib -Ztrust-verify=off
//@ no-prefer-dynamic
//! A dependency whose `PhantomData<T>` is a type tag, not a promise to drop a
//! `T`: `Handle<T>`'s `Drop` impl never touches a `T`, and `Id<T>` / `Holder<T>`
//! hold none. `Pair<T>` really holds a `T` by value.
use std::marker::PhantomData;
pub struct Id<T>(pub u32, pub PhantomData<T>);
pub struct Holder<T> {
    pub id: Id<T>,
    pub name: String,
}
pub struct Handle<T> {
    pub id: u32,
    pub _m: PhantomData<T>,
}
impl<T> Drop for Handle<T> {
    fn drop(&mut self) {
        self.id = 0;
    }
}
pub struct Pair<T>(pub T, pub String);
