use std::ffi::OsStr;

pub(crate) fn trust_domain_ordering_boundary(
    root: &OsStr,
    user: &OsStr,
    group: &OsStr,
    plugin: &OsStr,
) {
    chroot(root);
    get_user_by_name(user);
    getpwnam(user);
    getgrnam(group);
    dlopen(plugin);
    setgid(0);
    setuid(0);
}

fn chroot(_root: &OsStr) {}

fn get_user_by_name(_user: &OsStr) {}

fn getpwnam(_user: &OsStr) {}

fn getgrnam(_group: &OsStr) {}

fn dlopen(_plugin: &OsStr) {}

fn setgid(_gid: u32) {}

fn setuid(_uid: u32) {}
