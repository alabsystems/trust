//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-fail
#![crate_type = "lib"]
//! The refusing twin of `no_drop_glue_member_drop_is_an_edge.rs`: the closure
//! captures a value whose `Drop` panics on 7, so the `Map` DOES have drop glue and
//! its drop keeps the fail-closed row. `bomb_max(&[1, 2], 7)` panics while the
//! adapter is dropped.

pub struct Bomb(pub u32);

impl Drop for Bomb {
    fn drop(&mut self) {
        if self.0 == 7 {
            panic!("boom");
        }
    }
}

pub fn bomb_max(v: &[u8], k: u32) -> Option<u8> { //~ ERROR failed for `no_drop_glue_member_drop_is_an_edge_refused::bomb_max`
    let b = Bomb(k);
    v.windows(2)
        .map(move |w| {
            let _keep = &b;
            w[0]
        })
        .max()
}
