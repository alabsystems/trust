pub fn push_all(dst: &mut Vec<u8>, src: &[u8]) {
    dst.extend_from_slice(src);
}
