extern crate foreign_call_value_dep as dep;

pub fn at_cap(c: &dep::Cap) -> bool {
    c.len() + 1 == 16
}

pub fn split_fields(mut rest: &[u8], out: &mut [usize; 4]) -> usize {
    let mut n = 0usize;
    while n < 3 {
        match rest.iter().position(|&b| b == b';') {
            Some(k) => {
                out[n] = rest[..k].len();
                rest = &rest[k + 1..];
            }
            None => break,
        }
        n += 1;
    }
    n
}

pub fn always_overflows() -> u8 {
    255u8 + (dep::val() | 1)
}

pub fn after_semicolon(s: &[u8]) -> u8 {
    if let Some(k) = s.iter().position(|&b| b == b';') { s[k + 1] } else { 0 }
}
