#![crate_type = "lib"]
//! Fixture for `rmake.rs`: every function here has a source loop, and on main f5dd1d805a
//! (2026-10-01) the wave-ER for-loop summary lowered seven of them with the loop GONE —
//! spliced, licensed for codegen and passing `-Ztrust-ir-lower=strict`. The comment on each
//! says what main emitted.
use std::sync::atomic::{AtomicU32, Ordering};

unsafe extern "C" {
    fn close(fd: i32) -> i32;
    fn fcntl(fd: i32, cmd: i32, ...) -> i32;
}

const F_SETFD: i32 = 2;
const FD_CLOEXEC: i32 = 1;

/// main: `ret` — every `close` erased.
pub fn close_range(lo: i32, hi: i32) {
    for fd in lo..hi {
        unsafe {
            close(fd);
        }
    }
}

/// main: `ret` — every variadic `fcntl` erased.
pub fn cloexec_range(lo: i32, hi: i32) {
    for fd in lo..hi {
        unsafe {
            fcntl(fd, F_SETFD, FD_CLOEXEC);
        }
    }
}

#[inline(never)]
fn mark_listed(bound: i32) -> i32 {
    bound / 2
}

#[derive(Clone, Copy)]
pub struct InheritStrip {
    bound: i32,
}

/// aterm `spawnfd::InheritStrip::apply`, reduced (aterm 4ba80b2b6, `spawnfd.rs:1009`).
/// main: `call mark_listed; ret` — the strip loop erased.
impl InheritStrip {
    pub fn apply(self) {
        let from = mark_listed(self.bound);
        for fd in from..self.bound {
            unsafe {
                fcntl(fd, F_SETFD, FD_CLOEXEC);
            }
        }
    }
}

/// main: `%s = undef u32; ret %s`.
pub fn sum_range(n: u32) -> u32 {
    let mut s = 0u32;
    for i in 0..n {
        s = s.wrapping_add(i);
    }
    s
}

/// main: `%s = undef u32; ret %s` — the `println!` erased.
pub fn sum_and_print(n: u32) -> u32 {
    let mut s = 0u32;
    for i in 0..n {
        println!("{i}");
        s = s.wrapping_add(i);
    }
    s
}

pub static TICKS: AtomicU32 = AtomicU32::new(0);

/// main: declined (`PendingStatic`) — the atomic static kept the summary out.
pub fn sum_and_tick(n: u32) -> u32 {
    let mut s = 0u32;
    for i in 0..n {
        TICKS.fetch_add(1, Ordering::Relaxed);
        s = s.wrapping_add(i);
    }
    s
}

pub static mut LAST: u32 = 0;

/// main: faithful — the write to a `static` was the one effect the summary's scan saw.
pub fn sum_and_store_static(n: u32) -> u32 {
    let mut s = 0u32;
    for i in 0..n {
        unsafe {
            LAST = i;
        }
        s = s.wrapping_add(i);
    }
    s
}

#[inline(never)]
pub unsafe fn poke(p: *mut u32, v: u32) {
    unsafe { *p = v }
}

/// main: `ret` — the local `unsafe fn` call erased.
pub fn poke_range(p: *mut u32, n: u32) {
    for i in 0..n {
        unsafe { poke(p, i) };
    }
}

/// main: `%s = undef u32; ret %s`.
pub fn count_slice(v: &[u32]) -> u32 {
    let mut s = 0u32;
    for x in v {
        s = s.wrapping_add(*x);
    }
    s
}

pub struct PageStore {
    next: u32,
}

impl PageStore {
    pub fn new() -> Self {
        PageStore { next: 0 }
    }
}

pub struct Row {
    cols: u16,
    page: u32,
}

impl Row {
    /// # Safety
    /// `pages` must outlive the row.
    pub unsafe fn new(cols: u16, pages: &mut PageStore) -> Row {
        let page = pages.next;
        pages.next = pages.next.wrapping_add(1);
        Row { cols, page }
    }

    pub fn copy_from(&mut self, other: &Row) {
        self.cols = other.cols;
    }
}

pub struct Storage {
    rows: Vec<Row>,
    pages: PageStore,
    visible_rows: u16,
    cols: u16,
    ring_head: usize,
    total_lines: usize,
    scrollback_clear_gen: u32,
}

pub struct Grid {
    storage: Storage,
}

/// The erase ring-rebuild shape the summary was written for (aterm-grid `erase_scrollback`,
/// reduced). main: declined at `new_rows.push(row)` (`Borrow(&mut slot missing)`): since
/// ce36363804 (2026-09-07) the summary refused to havoc the `Vec` carrier, so the ring rebuild
/// already took the faithful lane.
impl Grid {
    pub fn erase_scrollback(&mut self) {
        self.storage.scrollback_clear_gen = self.storage.scrollback_clear_gen.wrapping_add(1);
        let scrollback =
            self.storage.total_lines.saturating_sub(self.storage.visible_rows as usize);
        if scrollback == 0 {
            return;
        }
        let live_top = (self.storage.ring_head + scrollback) % self.storage.rows.len();
        let mut new_pages = PageStore::new();
        let mut new_rows = Vec::with_capacity(self.storage.visible_rows as usize);
        for i in 0..self.storage.visible_rows {
            let idx = (live_top + i as usize) % self.storage.rows.len();
            let mut row = unsafe { Row::new(self.storage.cols, &mut new_pages) };
            row.copy_from(&self.storage.rows[idx]);
            new_rows.push(row);
        }
        self.storage.rows = new_rows;
        self.storage.pages = new_pages;
        self.storage.total_lines = self.storage.visible_rows as usize;
        self.storage.ring_head = 0;
    }
}

/// Control. main: the closure body is a faithful loop — the summary refused its upvars.
pub fn closure_close(lo: i32, hi: i32) -> impl Fn() {
    move || {
        for fd in lo..hi {
            unsafe {
                close(fd);
            }
        }
    }
}
