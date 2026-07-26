// char/u8 ascii predicate extension family probe.

#[inline(never)]
pub fn w_u8_is_ascii_graphic(b: u8) -> bool {
    b.is_ascii_graphic()
}

#[inline(never)]
pub fn w_u8_is_ascii_punctuation(b: u8) -> bool {
    b.is_ascii_punctuation()
}

#[inline(never)]
pub fn w_u8_is_ascii_control(b: u8) -> bool {
    b.is_ascii_control()
}

#[inline(never)]
pub fn w_u8_to_ascii_lowercase(b: u8) -> u8 {
    b.to_ascii_lowercase()
}

#[inline(never)]
pub fn w_u8_to_ascii_uppercase(b: u8) -> u8 {
    b.to_ascii_uppercase()
}

#[inline(never)]
pub fn w_u8_eq_ignore_ascii_case(a: u8, b: u8) -> bool {
    a.eq_ignore_ascii_case(&b)
}

#[inline(never)]
pub fn w_char_is_ascii(c: char) -> bool {
    c.is_ascii()
}

#[inline(never)]
pub fn w_char_is_ascii_digit(c: char) -> bool {
    c.is_ascii_digit()
}

#[inline(never)]
pub fn w_char_is_ascii_alphabetic(c: char) -> bool {
    c.is_ascii_alphabetic()
}

fn main() {
    let n = std::env::args().count() as u8;
    let b = n.wrapping_add(60);
    let c = char::from(b);
    let mut acc = 0u32;
    acc += w_u8_is_ascii_graphic(b) as u32;
    acc += w_u8_is_ascii_punctuation(b) as u32;
    acc += w_u8_is_ascii_control(b) as u32;
    acc += w_u8_to_ascii_lowercase(b) as u32;
    acc += w_u8_to_ascii_uppercase(b) as u32;
    acc += w_u8_eq_ignore_ascii_case(b, b.wrapping_add(32)) as u32;
    acc += w_char_is_ascii(c) as u32;
    acc += w_char_is_ascii_digit(c) as u32;
    acc += w_char_is_ascii_alphabetic(c) as u32;
    println!("acc={acc}");
}
