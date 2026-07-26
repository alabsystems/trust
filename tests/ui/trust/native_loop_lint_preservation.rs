//@ compile-flags: -Z trust-verify=off
//@ check-pass

#![deny(while_true)]

fn main() {
    while true
        invariant true
    {
        break;
    }
}
