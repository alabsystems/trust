pub(crate) fn unsafe_ffi_boundary() {
    let mut value = 0u8;
    let raw = &mut value as *mut u8;
    unsafe {
        let _ = raw.add(0);
        let _ = crate::getenv(c"PATH".as_ptr());
    }
}
