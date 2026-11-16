pub fn widen(x: u8) -> u32 {
    x as u32 + 1
}

#[derive(Clone, Copy)]
pub enum Dir {
    North,
    East,
    South,
    West,
}

pub fn index(d: Dir) -> usize {
    d as usize
}

pub fn capped(n: u32) -> u32 {
    let mut i = 0;
    while i < n && i < 10 {
        i += 1;
    }
    i
}

pub fn wraps(x: u32) -> u32 {
    x.wrapping_sub(1)
}

pub fn same(x: u32) -> u32 {
    x
}

pub fn clamp10(n: u32) -> u32 {
    if n > 10 { 10 } else { n }
}

// Bodies the interval domain cannot follow (`return_interval_admissible`).
pub union U {
    pub a: i8,
    pub b: u8,
}

pub fn union_reread(v: u8) -> i8 {
    let mut u = U { b: 0 };
    u.a = 5;
    u.b = v;
    unsafe { u.a }
}

pub fn select_write(v: u8, c: bool) -> u8 {
    let mut x: u8 = v / 50;
    let mut y: u8 = v / 50;
    let r = if c { &mut x } else { &mut y };
    *r = 200;
    x
}

pub struct Guard<'a>(pub &'a mut u8);

impl Drop for Guard<'_> {
    fn drop(&mut self) {
        *self.0 = 200;
    }
}

pub fn guarded(v: u8) -> u8 {
    let mut x: u8 = v / 50;
    {
        let _g = Guard(&mut x);
    }
    x
}
