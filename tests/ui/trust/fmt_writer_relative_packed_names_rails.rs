//@ needs-trust-verify
//@ edition: 2021
//@ revisions: malformed runtime_names safe_alias safe_alias_alignment
//@ compile-flags: -Ztrust-verify=on --crate-type lib -Copt-level=0
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
#![feature(fmt_helpers_for_derive, pointer_is_aligned_to)]

use std::fmt;

pub struct Bad { pub names: &'static str }

impl fmt::Debug for Bad {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        //~^ ERROR Trust strict verification failed
        //[safe_alias_alignment]~| ERROR Trust Level 0 safety verification incomplete
        #[cfg(safe_alias_alignment)]
        {
            let mut alignment = 8usize;
            let slot = &mut alignment;
            *slot = 3;
            if (self as *const Self).is_aligned_to(alignment) {
                return f.write_str("aligned");
            }
            return f.write_str("unaligned");
        }
        #[cfg(not(safe_alias_alignment))]
        {
            #[cfg(malformed)]
            let names = "Bad first";
            #[cfg(runtime_names)]
            let names = self.names;
            #[cfg(safe_alias)]
            let mut names = "Good first second";
            #[cfg(safe_alias)]
            {
                let slot = &mut names;
                *slot = "Bad first";
            }
            f.debug_struct_field2_finish(names, &1u64, &2u64)
        }
    }
}
