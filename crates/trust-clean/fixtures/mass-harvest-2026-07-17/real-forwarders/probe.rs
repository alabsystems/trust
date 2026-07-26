// Family: REALISTIC struct-method forwarders — struct methods that call
// certified stdlib leaves through self fields. Measures end-to-end real-code reach.
use std::cmp::{max, min};

pub struct Config {
    pub name: Option<i32>,
    pub count: u32,
}

pub struct Buf {
    pub data_len: usize,
    pub cap: usize,
}

pub struct State {
    pub mode: Option<u8>,
    pub retries: u8,
}

impl Config {
    #[inline(never)]
    pub fn has_name(&self) -> bool {
        self.name.is_some()
    }

    #[inline(never)]
    pub fn name_or_zero(&self) -> i32 {
        self.name.unwrap_or(0)
    }

    #[inline(never)]
    pub fn capped_count(&self, buf: &Buf) -> u32 {
        self.count.min(buf.cap as u32)
    }
}

impl Buf {
    #[inline(never)]
    pub fn used(&self) -> usize {
        min(self.data_len, self.cap)
    }

    #[inline(never)]
    pub fn larger_dim(&self) -> usize {
        self.data_len.max(self.cap)
    }

    #[inline(never)]
    pub fn grow_target(&self) -> usize {
        max(self.cap, 8)
    }
}

impl State {
    #[inline(never)]
    pub fn mode_or_default(&self) -> u8 {
        self.mode.unwrap_or(0)
    }

    #[inline(never)]
    pub fn has_mode(&self) -> bool {
        self.mode.is_some()
    }

    #[inline(never)]
    pub fn retries_at_least_one(&self) -> u8 {
        self.retries.max(1)
    }

    #[inline(never)]
    pub fn retries_capped(&self, cap: u8) -> u8 {
        self.retries.min(cap)
    }
}

fn main() {
    // Derive inputs from argc so nothing const-folds away.
    let n = std::env::args().count();

    let cfg = Config {
        name: if n > 1 { Some(n as i32) } else { None },
        count: n as u32,
    };
    let buf = Buf {
        data_len: n,
        cap: n + 4,
    };
    let st = State {
        mode: if n % 2 == 0 { Some(n as u8) } else { None },
        retries: n as u8,
    };

    let mut acc: u64 = 0;
    acc += cfg.has_name() as u64;
    acc += cfg.name_or_zero() as u64;
    acc += cfg.capped_count(&buf) as u64;
    acc += buf.used() as u64;
    acc += buf.larger_dim() as u64;
    acc += buf.grow_target() as u64;
    acc += st.mode_or_default() as u64;
    acc += st.has_mode() as u64;
    acc += st.retries_at_least_one() as u64;
    acc += st.retries_capped(3) as u64;
    println!("acc={acc}");
}
