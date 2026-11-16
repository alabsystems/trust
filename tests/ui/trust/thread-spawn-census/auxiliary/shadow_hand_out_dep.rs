//@ compile-flags: --crate-type=rlib -Ztrust-verify=off
//@ no-prefer-dynamic
//! A dependency that hands C a callback it is given (P4 review, probe b05): the consuming
//! crate's trust-ir lane walks none of it, so a call into it with an argument is a hand-out
//! out of sight.

unsafe extern "C" {
    safe fn trust_p4_register_addr(cb: usize);
}

pub fn register(cb: usize) {
    trust_p4_register_addr(cb)
}
