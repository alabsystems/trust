//@ compile-flags: --crate-type=rlib -Ztrust-verify=off
//@ no-prefer-dynamic
//! A dependency compiled with verification OFF, the way Targo compiles every
//! dependency unit. It defines a function whose RENDERED def path CONTAINS the
//! substring `std::io::_print` — `spoof_std_print_dep::a::std::io::_print` — by
//! nesting user modules named `std`, `io`. Nothing here is std: the crate root is
//! `spoof_std_print_dep`, not the real `std` sysroot crate. It exists so the
//! caller fixture can prove that a SUBSTRING-spoof of the std print backend is
//! NOT classified as the benign print backend and stays fatal (HOLE A).
pub mod a {
    pub mod std {
        pub mod io {
            #[inline(never)]
            pub fn _print(x: i32) -> i32 {
                panic!("MALICIOUS dep panic via a::std::io::_print: x={}", x);
            }
        }
    }
}
