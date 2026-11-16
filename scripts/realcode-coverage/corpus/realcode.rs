// Curated, hand-authored synthetic fixture spanning common Rust patterns.
// It was not shaped for the verifier's synthesizer, but it is not an uncurated
// or representative sample of downstream projects. ~45 source functions.
#![allow(dead_code, unused_variables, unused_mut, clippy::all)]
use std::collections::HashMap;

// ---- 1. plain scalar arithmetic ----
pub fn add(a: i32, b: i32) -> i32 {
    a + b
}
pub fn avg3(a: i64, b: i64, c: i64) -> i64 {
    (a + b + c) / 3
}
pub fn abs_diff(a: u32, b: u32) -> u32 {
    if a > b { a - b } else { b - a }
}
pub fn clamp(x: i32, lo: i32, hi: i32) -> i32 {
    if x < lo {
        lo
    } else if x > hi {
        hi
    } else {
        x
    }
}

// ---- 2. counter / accumulator loops ----
pub fn sum_to(n: u32) -> u32 {
    let mut acc = 0u32;
    let mut i = 0u32;
    while i < n {
        acc += i;
        i += 1;
    }
    acc
}
pub fn factorial(n: u64) -> u64 {
    let mut f = 1u64;
    let mut i = 1u64;
    while i <= n {
        f *= i;
        i += 1;
    }
    f
}
pub fn count_down(mut n: i32) -> i32 {
    let mut steps = 0;
    while n > 0 {
        n -= 1;
        steps += 1;
    }
    steps
}

// ---- 3. slice / array iteration ----
pub fn sum_slice(xs: &[i32]) -> i32 {
    let mut total = 0;
    for &x in xs {
        total += x;
    }
    total
}
pub fn max_slice(xs: &[i32]) -> i32 {
    let mut m = i32::MIN;
    for &x in xs {
        if x > m {
            m = x;
        }
    }
    m
}
pub fn index_get(xs: &[u8], i: usize) -> u8 {
    xs[i]
}
pub fn first_two(xs: &[i32]) -> i32 {
    xs[0] + xs[1]
}
pub fn array_sum(a: [i32; 4]) -> i32 {
    a[0] + a[1] + a[2] + a[3]
}
pub fn reverse_in_place(xs: &mut [i32]) {
    let n = xs.len();
    let mut i = 0;
    while i < n / 2 {
        xs.swap(i, n - 1 - i);
        i += 1;
    }
}

// ---- 4. iterator-combinator style ----
pub fn sum_even(xs: &[i32]) -> i32 {
    xs.iter().filter(|&&x| x % 2 == 0).sum()
}
pub fn doubled(xs: &[i32]) -> Vec<i32> {
    xs.iter().map(|&x| x * 2).collect()
}
pub fn count_positive(xs: &[i32]) -> usize {
    xs.iter().filter(|&&x| x > 0).count()
}
pub fn find_first_gt(xs: &[i32], t: i32) -> Option<i32> {
    xs.iter().copied().find(|&x| x > t)
}

// ---- 5. structs + methods ----
#[derive(Clone, Copy)]
pub struct Point {
    x: i32,
    y: i32,
}
impl Point {
    pub fn new(x: i32, y: i32) -> Point {
        Point { x, y }
    }
    pub fn manhattan(&self) -> i32 {
        self.x.abs() + self.y.abs()
    }
    pub fn translate(&self, dx: i32, dy: i32) -> Point {
        Point { x: self.x + dx, y: self.y + dy }
    }
    pub fn dot(&self, o: &Point) -> i32 {
        self.x * o.x + self.y * o.y
    }
}

pub struct Rect {
    w: u32,
    h: u32,
}
impl Rect {
    pub fn area(&self) -> u32 {
        self.w * self.h
    }
    pub fn perimeter(&self) -> u32 {
        2 * (self.w + self.h)
    }
}

// ---- 6. enums + match-heavy ----
pub enum Shape {
    Circle(f64),
    Square(f64),
    Rectangle(f64, f64),
}
pub fn shape_area(s: &Shape) -> f64 {
    match s {
        Shape::Circle(r) => 3.14159 * r * r,
        Shape::Square(a) => a * a,
        Shape::Rectangle(w, h) => w * h,
    }
}
pub enum Op {
    Add,
    Sub,
    Mul,
    Div,
}
pub fn apply_op(op: Op, a: i32, b: i32) -> i32 {
    match op {
        Op::Add => a + b,
        Op::Sub => a - b,
        Op::Mul => a * b,
        Op::Div => a / b,
    }
}

// ---- 7. error handling / Result / Option ----
pub fn safe_div(a: i32, b: i32) -> Result<i32, String> {
    if b == 0 { Err("divide by zero".to_string()) } else { Ok(a / b) }
}
pub fn parse_and_add(s: &str) -> Result<i32, std::num::ParseIntError> {
    let n: i32 = s.parse()?;
    Ok(n + 1)
}
pub fn first_char(s: &str) -> Option<char> {
    s.chars().next()
}
pub fn unwrap_or_zero(o: Option<i32>) -> i32 {
    o.unwrap_or(0)
}

// ---- 8. generics ----
pub fn max_generic<T: PartialOrd>(a: T, b: T) -> T {
    if a > b { a } else { b }
}
pub fn identity<T>(x: T) -> T {
    x
}
pub fn pair<A, B>(a: A, b: B) -> (A, B) {
    (a, b)
}
pub fn swap<T>(t: (T, T)) -> (T, T) {
    (t.1, t.0)
}

// ---- 9. trait + dyn ----
pub trait Animal {
    fn legs(&self) -> u32;
}
pub struct Dog;
pub struct Spider;
impl Animal for Dog {
    fn legs(&self) -> u32 {
        4
    }
}
impl Animal for Spider {
    fn legs(&self) -> u32 {
        8
    }
}
pub fn total_legs(animals: &[Box<dyn Animal>]) -> u32 {
    let mut t = 0;
    for a in animals {
        t += a.legs();
    }
    t
}

// ---- 10. closures ----
pub fn apply<F: Fn(i32) -> i32>(f: F, x: i32) -> i32 {
    f(x)
}
pub fn make_adder(n: i32) -> impl Fn(i32) -> i32 {
    move |x| x + n
}
pub fn fold_sum(xs: &[i32]) -> i32 {
    xs.iter().fold(0, |acc, &x| acc + x)
}

// ---- 11. string processing ----
pub fn count_words(s: &str) -> usize {
    s.split_whitespace().count()
}
pub fn is_palindrome(s: &str) -> bool {
    let bytes = s.as_bytes();
    let n = bytes.len();
    let mut i = 0;
    while i < n / 2 {
        if bytes[i] != bytes[n - 1 - i] {
            return false;
        }
        i += 1;
    }
    true
}
pub fn to_upper_count(s: &str) -> usize {
    s.chars().filter(|c| c.is_uppercase()).count()
}

// ---- 12. common algorithms ----
pub fn gcd(mut a: u64, mut b: u64) -> u64 {
    while b != 0 {
        let t = b;
        b = a % b;
        a = t;
    }
    a
}
pub fn fib(n: u32) -> u64 {
    let (mut a, mut b) = (0u64, 1u64);
    let mut i = 0;
    while i < n {
        let t = a + b;
        a = b;
        b = t;
        i += 1;
    }
    a
}
pub fn binary_search(xs: &[i32], target: i32) -> Option<usize> {
    let mut lo = 0usize;
    let mut hi = xs.len();
    while lo < hi {
        let mid = lo + (hi - lo) / 2;
        if xs[mid] == target {
            return Some(mid);
        } else if xs[mid] < target {
            lo = mid + 1;
        } else {
            hi = mid;
        }
    }
    None
}
pub fn bubble_pass(xs: &mut [i32]) {
    let n = xs.len();
    let mut i = 1;
    while i < n {
        if xs[i - 1] > xs[i] {
            xs.swap(i - 1, i);
        }
        i += 1;
    }
}

// ---- 13. nested loops ----
pub fn count_pairs(xs: &[i32]) -> usize {
    let mut c = 0;
    let n = xs.len();
    let mut i = 0;
    while i < n {
        let mut j = i + 1;
        while j < n {
            if xs[i] + xs[j] == 0 {
                c += 1;
            }
            j += 1;
        }
        i += 1;
    }
    c
}

// ---- 14. HashMap / collections ----
pub fn word_freq(words: &[&str]) -> HashMap<String, u32> {
    let mut m = HashMap::new();
    for w in words {
        *m.entry(w.to_string()).or_insert(0) += 1;
    }
    m
}

// ---- 15. bit manipulation ----
pub fn popcount(mut x: u32) -> u32 {
    let mut c = 0;
    while x != 0 {
        c += x & 1;
        x >>= 1;
    }
    c
}
pub fn is_power_of_two(x: u32) -> bool {
    x != 0 && (x & (x - 1)) == 0
}

// ---- 16. float math ----
pub fn hypot(a: f64, b: f64) -> f64 {
    (a * a + b * b).sqrt()
}
pub fn lerp(a: f64, b: f64, t: f64) -> f64 {
    a + (b - a) * t
}
