// Trust (TG3, COMPILE-TIME-FACTS-1): the positive twin of
// kernel-obligations-deferred-island.rs. A true theorem about an imported body
// documents cleanly, and the kernel check says it ran: without this twin, a rustdoc
// lane that refused every deferred island would pass the negative test vacuously.
//
//@ check-pass
//@ compile-flags: -Ztrust-verify=off

pub fn ident(x: u64) -> u64 {
    x
}

clean {
    theorem ident_same (x : UInt64) : trust_import_kernel_obligations_deferred_true__ident x = x := rfl
}
