//@ revisions: default certify memsafe
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@[certify] compile-flags: -Ztrust-policy=certify
//@[memsafe] compile-flags: -Ztrust-policy=memory-safe
//@ check-fail
//@ dont-check-compiler-stderr
//! A function that is merely NAMED `min` is not `Ord::min`, and its result is not
//! bounded by its constant argument.
//!
//! `loop_bounds::local_min_upper_bound` decided "this call is `Ord::min`" with
//! `callee.ends_with("::min")` and nothing else. Every function below therefore got
//! the global fact `dest <= 10`, which `build_global_invariant_facts` conjoins onto
//! every VC of the body, including the `+ 1` overflow VC. The Clean kernel re-checked
//! that VC under the false hypothesis, the row became kernel-certified, and
//! `elide_kernel_certified_checks` deleted the overflow check: `f(u32::MAX)` returned
//! 0 where vanilla Rust panics with `attempt to add with overflow`.
//!
//! BEFORE (stage 1 of `1ab78ed8e8`, `scratchpad/stage1-w10`; each revision's own
//! flags with `--emit=metadata`, diagnostics matched as compiletest matches them;
//! measured 2026-10-03): all three revisions built exit 0 with no error and no
//! warning. `f`, `g`, `h` and `k` each reported every obligation proved, and none of
//! the annotations below fired.
//!
//! AFTER (predicted; it held on the stage 1 of `936573497e`, 2026-10-04): the recognizer is `call_facts::is_ord_min_call`,
//! which accepts only a `core::cmp::`/`std::cmp::`-rooted path or the qualified
//! `<T as core::cmp::Ord>::min` / `<T as std::cmp::Ord>::min`. None of the four user
//! callees gets a fact. The annotations were derived on the same stage 1 from two
//! twins of this file in which only the four user callees are renamed (to `mn`, and
//! to `max`, which the old string test already refused); both twins produced exactly
//! the diagnostics annotated here. Under memory-safe, `f` and `k` are a REFUTED
//! overflow whose runtime check stays, so they are a warning and not an error; the
//! lie that revision pins is the missing warning.
//!
//! `std_min` is the control: genuine `x.min(10) + 1` keeps its bound and proves in
//! every revision, so it carries no annotation (compiletest requires every ERROR and
//! WARN to be annotated, and this file does not relax that).

pub mod util {
    // A user helper that happens to be called `min`. It returns its first
    // argument, so `util::min(u32::MAX, 10) + 1` overflows.
    pub fn min(a: u32, _b: u32) -> u32 {
        a
    }
}

pub mod util2 {
    pub fn min(_a: u32, _b: u32) -> u32 {
        std::hint::black_box(u32::MAX)
    }
}

pub mod spoof {
    // A user trait named `Ord`: `<u32 as …::spoof::Ord>::min`.
    pub trait Ord {
        fn min(self, other: Self) -> Self;
    }
    impl Ord for u32 {
        fn min(self, _other: u32) -> u32 {
            self
        }
    }
    // A user path that spells `core::cmp::min` below the crate root.
    pub mod core {
        pub mod cmp {
            pub fn min(a: u32, _b: u32) -> u32 {
                a
            }
        }
    }
}

pub fn f(x: u32) -> u32 {
    //[default,certify]~^ ERROR Trust Level 0 safety verification incomplete
    //[default,certify]~^^ ERROR Trust strict verification failed
    //[memsafe]~^^^ WARN Trust Level 0 safety verification incomplete
    util::min(x, 10) + 1
}

pub fn g(x: u32) -> u32 {
    //[default,certify]~^ ERROR Trust Level 0 safety verification incomplete
    //[default,certify]~^^ ERROR Trust strict verification failed
    //[memsafe]~^^^ WARN Trust Level 0 safety verification incomplete
    //[memsafe]~^^^^ ERROR Trust memory-safe verification failed
    util2::min(x, 10) + 1
}

pub fn h(x: u32) -> u32 {
    //[default,certify]~^ ERROR Trust Level 0 safety verification incomplete
    //[default,certify]~^^ ERROR Trust strict verification failed
    //[memsafe]~^^^ WARN Trust Level 0 safety verification incomplete
    //[memsafe]~^^^^ ERROR Trust memory-safe verification failed
    spoof::Ord::min(x, 10) + 1
}

pub fn k(x: u32) -> u32 {
    //[default,certify]~^ ERROR Trust Level 0 safety verification incomplete
    //[default,certify]~^^ ERROR Trust strict verification failed
    //[memsafe]~^^^ WARN Trust Level 0 safety verification incomplete
    spoof::core::cmp::min(x, 10) + 1
}

pub fn std_min(x: u32) -> u32 {
    x.min(10) + 1
}
