// Trust (TG3, COMPILE-TIME-FACTS-1): documenting a crate checks its Clean islands
// and kernel obligations as compiling it does. rustdoc runs no `analysis`, so before
// TG3 it saw only what the resolver seam checks: an island the seam cannot check — a
// deferred `trust_import_*` suffix, or one a macro introduced — went unchecked, and a
// false theorem in it documented with no diagnostic (reported by aterm's PF1 worker,
// 2026-11-05, under `targo --unverified doc`). This file is the macro-introduced case; its
// twin kernel-obligations-deferred-island.rs is the deferred case. Each states a
// theorem that is false and must be refused.
//
//@ check-fail
//@ compile-flags: -Ztrust-verify=off

macro_rules! island {
    ($($body:tt)*) => { $($body)* };
}

// A macro-introduced island: the resolver seam cannot check it.
island! {
    clean {
        theorem one_is_two : (1 : Nat) = 2 := rfl
    }
}
//~^^^ ERROR did not elaborate
