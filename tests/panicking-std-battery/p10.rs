pub fn f(c: char) -> usize {
    let mut b = [0u8; 1];
    c.encode_utf8(&mut b).len()
}
