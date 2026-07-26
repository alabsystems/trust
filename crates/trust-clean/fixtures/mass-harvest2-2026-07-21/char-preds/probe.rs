// char predicate breadth harvest — Trust certifier lanes
// wrappers are #[inline(never)] and CALLED from main; inputs derived from args().count()

#[inline(never)]
fn w_is_ascii_digit(c: char) -> bool {
    c.is_ascii_digit()
}

#[inline(never)]
fn w_is_ascii_alphabetic(c: char) -> bool {
    c.is_ascii_alphabetic()
}

#[inline(never)]
fn w_is_ascii_uppercase(c: char) -> bool {
    c.is_ascii_uppercase()
}

#[inline(never)]
fn w_is_ascii_lowercase(c: char) -> bool {
    c.is_ascii_lowercase()
}

#[inline(never)]
fn w_is_ascii_hexdigit(c: char) -> bool {
    c.is_ascii_hexdigit()
}

#[inline(never)]
fn w_is_ascii_whitespace(c: char) -> bool {
    c.is_ascii_whitespace()
}

#[inline(never)]
fn w_to_ascii_lowercase(c: char) -> char {
    c.to_ascii_lowercase()
}

#[inline(never)]
fn w_to_ascii_uppercase(c: char) -> char {
    c.to_ascii_uppercase()
}

#[inline(never)]
fn w_eq_ignore_ascii_case(a: char, b: char) -> bool {
    a.eq_ignore_ascii_case(&b)
}

// composed wrappers over the same surface
#[inline(never)]
fn w_is_ascii_alphanumeric_composed(c: char) -> bool {
    c.is_ascii_digit() || c.is_ascii_alphabetic()
}

#[inline(never)]
fn w_case_roundtrip(c: char) -> bool {
    c.to_ascii_uppercase().to_ascii_lowercase() == c.to_ascii_lowercase()
}

fn main() {
    let n = std::env::args().count() as u32;
    let a = (b'A' + (n % 26) as u8) as char;
    let b = (b'a' + ((n / 26) % 26) as u8) as char;

    let mut acc: u32 = 0;
    acc += w_is_ascii_digit(a) as u32;
    acc += w_is_ascii_alphabetic(a) as u32;
    acc += w_is_ascii_uppercase(a) as u32;
    acc += w_is_ascii_lowercase(b) as u32;
    acc += w_is_ascii_hexdigit(a) as u32;
    acc += w_is_ascii_whitespace(b) as u32;
    acc += w_to_ascii_lowercase(a) as u32;
    acc += w_to_ascii_uppercase(b) as u32;
    acc += w_eq_ignore_ascii_case(a, b) as u32;
    acc += w_is_ascii_alphanumeric_composed(a) as u32;
    acc += w_case_roundtrip(b) as u32;

    std::process::exit((acc % 64) as i32);
}
