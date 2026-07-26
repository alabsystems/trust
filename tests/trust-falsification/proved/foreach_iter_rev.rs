#![crate_type = "lib"]
// A total iterator ADAPTER over a slice: `for &x in s.iter().rev() { … }`. The
// `Rev<slice::Iter>` adapter only reverses the reference order — it runs no user
// code and cannot panic — so the native CHC proves the loop panic-free under
// the default strict policy. Exercises: the total-adapter recognizer (Rev/Copied/
// Take/Skip/Enumerate/Peekable over a slice base) and the stack-pointer-safe store
// (the opaque `Rev` struct is stored to an Alloca'd slot to take the `&mut` for
// `next()` — a safe owned-stack access, left untracked rather than fail-closed).
pub fn foreach_iter_rev(s: &[i32]) -> i32 {
    let mut t = 0i32;
    for &x in s.iter().rev() {
        t = t.wrapping_add(x);
    }
    t
}
