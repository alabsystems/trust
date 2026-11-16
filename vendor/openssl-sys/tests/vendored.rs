// Trust: exercise the actual vendored artifacts, not just Rust driver metadata.
use std::ffi::CStr;

#[test]
fn vendored_openssl_363_links_and_hashes_a_known_message() {
    unsafe {
        let version = CStr::from_ptr(openssl_sys::OpenSSL_version(openssl_sys::OPENSSL_VERSION));
        assert!(
            version.to_bytes().starts_with(b"OpenSSL 3.6.3 "),
            "{version:?}"
        );
        let mut digest = [0u8; 32];
        assert_eq!(
            openssl_sys::SHA256(b"abc".as_ptr(), 3, digest.as_mut_ptr()),
            digest.as_mut_ptr()
        );
        assert_eq!(
            digest,
            [
                0xba, 0x78, 0x16, 0xbf, 0x8f, 0x01, 0xcf, 0xea, 0x41, 0x41, 0x40, 0xde, 0x5d, 0xae,
                0x22, 0x23, 0xb0, 0x03, 0x61, 0xa3, 0x96, 0x17, 0x7a, 0x9c, 0xb4, 0x10, 0xff, 0x61,
                0xf2, 0x00, 0x15, 0xad,
            ]
        );
    }
}
