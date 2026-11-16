//! Built by the DEFAULT backend; calls `va`'s functions, built by whichever backend is under test.
#![feature(rustc_private)]
extern crate libc;
extern crate va;

fn main() {
    let mut fds = [0i32; 2];
    // `pipe` (unlike std's constructors) leaves FD_CLOEXEC clear on both ends.
    assert_eq!(unsafe { libc::pipe(fds.as_mut_ptr()) }, 0);
    let [r, w] = fds;
    let host = |fd: i32| unsafe { libc::fcntl(fd, libc::F_GETFD) };
    let before = (host(r), va::f1_getfd(r));
    let set = va::f1_setfd_cloexec(r);
    let after = (host(r), va::f1_getfd(r));
    // `other`: the flag landed on `r` and nowhere else.
    let other = host(w);
    println!("before={}/{} set={set} after={}/{} other={other}", before.0, before.1, after.0, after.1);
}
