//@ needs-trust-verify
//@ revisions: tls_accessor callable_type_arg
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=certify --crate-type lib
//@[tls_accessor] rustc-env:TRUST_SYSROOT_CENSUS_DEBUG=1
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-fail
//[tls_accessor]~? RAW a call through a function pointer in `std::thread::local::LocalKey::<T>::try_with`
//! Trust (2026-09-28, std-absent-callee; re-pinned 2026-10-08): a call through a
//! FUNCTION POINTER inside a std body is a panic site for the sysroot panic
//! census, whatever the pointer holds.
//!
//! * `tls_accessor` (the pin). `LocalKey::<T>::try_with` reaches the slot through
//!   `(self.inner)(None)`, a pointer to the accessor `thread_local!` generates in
//!   THIS crate, and for a lazily initialized key that accessor runs the
//!   initializer — here `init`, which panics. No argument or type argument of the
//!   call names the pointer (`try_with::<fn item Cell::get, u8>`), so the census's
//!   function-pointer arm is the only thing between `read_boom` and a proof: with
//!   that arm treated as total, the census derived `try_with` total and
//!   `read_boom` certified, while a runtime build of the same shape panics
//!   (`tls init`, exit 101). The `RAW` line pins the census's own reason (the
//!   pointer call in `try_with`), so this stays a test of that arm and not of
//!   whatever else refuses the call. `read_quiet` (a non-panicking lazy
//!   initializer) is refused too: the census tracks no pointer VALUE, the same
//!   value-independence residual as `load_relaxed` in
//!   `certify_sysroot_callee_reaching_panic_refused.rs` — sound incompleteness.
//! * `callable_type_arg`: the fixture's first shape (2026-09-28),
//!   `Option::<u8>::map::<u8, fn(u8) -> u8>` handed a panicking `boom`. Since
//!   origin/main's callable-type-argument gate (`sysroot_callable_item`) refuses a
//!   sysroot call instantiated at an unresolved `fn` pointer type on its own, this
//!   revision no longer isolates the census arm; it stays as a refusal pin of the
//!   shape (a runtime build panics, `fnptr`, exit 101).

#[cfg(tls_accessor)]
pub mod tls_accessor {
    use std::cell::Cell;

    fn init() -> u8 {
        panic!("tls init")
    }

    thread_local! {
        static X: Cell<u8> = Cell::new(init());
        static Q: Cell<u8> = Cell::new(7);
    }

    pub fn read_boom() -> Option<u8> {
        //[tls_accessor]~^ ERROR Trust strict verification failed for `certify_fn_pointer_call_in_std_body_refused::tls_accessor::read_boom`
        X.try_with(Cell::get).ok()
    }

    pub fn read_quiet() -> Option<u8> {
        //[tls_accessor]~^ ERROR Trust strict verification failed for `certify_fn_pointer_call_in_std_body_refused::tls_accessor::read_quiet`
        Q.try_with(Cell::get).ok()
    }
}

#[cfg(callable_type_arg)]
pub mod callable_type_arg {
    pub fn apply(x: Option<u8>, f: fn(u8) -> u8) -> Option<u8> {
        //[callable_type_arg]~^ ERROR Trust strict verification failed for `certify_fn_pointer_call_in_std_body_refused::callable_type_arg::apply`
        x.map(f)
    }

    fn boom(_: u8) -> u8 {
        panic!("fnptr")
    }

    fn inc(x: u8) -> u8 {
        x.wrapping_add(1)
    }

    pub fn apply_boom() -> Option<u8> {
        //[callable_type_arg]~^ ERROR Trust strict verification failed for `certify_fn_pointer_call_in_std_body_refused::callable_type_arg::apply_boom`
        apply(Some(1), boom)
    }

    pub fn apply_inc() -> Option<u8> {
        //[callable_type_arg]~^ ERROR Trust strict verification failed for `certify_fn_pointer_call_in_std_body_refused::callable_type_arg::apply_inc`
        apply(Some(1), inc)
    }
}
