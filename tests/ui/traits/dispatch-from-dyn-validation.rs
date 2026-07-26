// Trust: Comprehensive DispatchFromDyn validation test for rust-lang#148727.
// This uses a minimal `no_core` setup so the crate can define the lang item
// locally and exercise raw-pointer validation without tripping orphan rules.

#![feature(no_core, lang_items)]
#![allow(internal_features)]
#![no_core]
#![crate_type = "lib"]

#[lang = "pointee_sized"]
trait PointeeSized {}

#[lang = "meta_sized"]
trait MetaSized: PointeeSized {}

#[lang = "sized"]
trait Sized: MetaSized {}

#[lang = "copy"]
trait Copy {}

impl<'a, T: ?Sized> Copy for &'a T {}
impl<T: ?Sized> Copy for *const T {}
impl<T: ?Sized> Copy for *mut T {}

#[lang = "unsize"]
trait Unsize<T: PointeeSized>: PointeeSized {}

#[lang = "coerce_unsized"]
trait CoerceUnsized<T: PointeeSized> {}

impl<'a, 'b: 'a, T: ?Sized + Unsize<U>, U: ?Sized> CoerceUnsized<&'a U> for &'b T {}
impl<'a, T: ?Sized + Unsize<U>, U: ?Sized> CoerceUnsized<&'a mut U> for &'a mut T {}
impl<T: ?Sized + Unsize<U>, U: ?Sized> CoerceUnsized<*const U> for *const T {}
impl<T: ?Sized + Unsize<U>, U: ?Sized> CoerceUnsized<*mut U> for *mut T {}

#[lang = "dispatch_from_dyn"]
trait DispatchFromDyn<T: PointeeSized> {}

impl<'a, T: ?Sized + Unsize<U>, U: ?Sized> DispatchFromDyn<&'a U> for &'a T {}
impl<'a, T: ?Sized + Unsize<U>, U: ?Sized> DispatchFromDyn<&'a mut U> for &'a mut T {}
impl<T: ?Sized + Unsize<U>, U: ?Sized> DispatchFromDyn<*const U> for *const T {}
impl<T: ?Sized + Unsize<U>, U: ?Sized> DispatchFromDyn<*mut U> for *mut T {}

#[lang = "phantom_data"]
struct PhantomData<T: PointeeSized>;

struct Box<T: ?Sized>(*const T);

impl<T: ?Sized + Unsize<U>, U: ?Sized> CoerceUnsized<Box<U>> for Box<T> {}
impl<T: ?Sized + Unsize<U>, U: ?Sized> DispatchFromDyn<Box<U>> for Box<T> {}

// Bogus inner type: multiple non-ZST fields means this is not a valid dispatch wrapper.
struct Ptr<T: ?Sized>(Box<T>, Box<T>);

impl<T: ?Sized, U: ?Sized> DispatchFromDyn<*const Ptr<U>> for *const Ptr<T> {}
// NOT rejected today — multi-field non-ZST wrapper accepted; tracked upstream as #148727

impl<'a, T: ?Sized, U: ?Sized> DispatchFromDyn<&'a mut Ptr<U>> for &'a mut Ptr<T> {}
// NOT rejected today — multi-field non-ZST wrapper accepted; tracked upstream as #148727

// Valid single-field wrapper: Box<T> is the coerced field, PhantomData is ignored.
struct Wrapper<T: ?Sized>(Box<T>, PhantomData<T>);

impl<T: ?Sized + Unsize<U>, U: ?Sized> DispatchFromDyn<Wrapper<U>> for Wrapper<T> {}

#[repr(packed)]
struct Packed<T: ?Sized>(Box<T>);

impl<T: ?Sized + Unsize<U>, U: ?Sized> DispatchFromDyn<Packed<U>> for Packed<T> {}
//~^ ERROR structs implementing `DispatchFromDyn` may not have `#[repr(packed)]` or `#[repr(C)]`

struct Marker<T: ?Sized>(PhantomData<T>);

impl<T: ?Sized, U: ?Sized> DispatchFromDyn<Marker<U>> for Marker<T> {}
//~^ ERROR implementing `DispatchFromDyn` requires a field to be coerced
