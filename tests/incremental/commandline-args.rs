// Test that changing a tracked commandline argument invalidates
// the cache while changing an untracked one doesn't.
// Trust: scripts/tests/internal_lint_incremental_process.py also checks these
// lint-mode transitions through ordinary Targo and its real jobserver custody.

//@ revisions:rpass1 rpass2 rpass3 rpass4 rpass5 rpass6 rpass7 rpass8
//@ compile-flags: -Z query-dep-graph -Zincremental-verify-ich=yes

#![feature(rustc_attrs)]
// Trust: these specs exist only while the internal lint store is enabled.
#![allow(rustc::default_hash_types, rustc::potential_query_instability)]

#![rustc_partition_codegened(module="commandline_args", cfg="rpass2")]
#![rustc_partition_reused(module="commandline_args", cfg="rpass3")]
#![rustc_partition_codegened(module="commandline_args", cfg="rpass4")]
// Trust: toggling internal lint registration requires cache invalidation in both directions.
#![rustc_partition_codegened(module="commandline_args", cfg="rpass5")]
#![rustc_partition_reused(module="commandline_args", cfg="rpass6")]
#![rustc_partition_codegened(module="commandline_args", cfg="rpass7")]
#![rustc_partition_reused(module="commandline_args", cfg="rpass8")]

// Between revisions 1 and 2, we are changing the debuginfo-level, which should
// invalidate the cache. Between revisions 2 and 3, we are adding `--diagnostic-width`
// which should have no effect on the cache. Between revisions, we are adding
// `--remap-path-prefix` which should invalidate the cache:
//@[rpass1] compile-flags: -C debuginfo=0
//@[rpass2] compile-flags: -C debuginfo=2
//@[rpass3] compile-flags: -C debuginfo=2 --diagnostic-width=80
//@[rpass4] compile-flags: -C debuginfo=2 --diagnostic-width=80 --remap-path-prefix=/home/bors/r=src
// Regression test for https://github.com/rust-lang/rust/issues/156182.
// Trust: `-Zunstable-options` enables internal lints and changes these root specs.
// It must invalidate the cache without changing crate identity. Repeating the
// enabled state reuses codegen; disabling invalidates; repeating disabled reuses.
//@[rpass5] compile-flags: -C debuginfo=2 --diagnostic-width=80 --remap-path-prefix=/home/bors/r=src -Zunstable-options
//@[rpass6] compile-flags: -C debuginfo=2 --diagnostic-width=80 --remap-path-prefix=/home/bors/r=src -Zunstable-options
//@[rpass7] compile-flags: -C debuginfo=2 --diagnostic-width=80 --remap-path-prefix=/home/bors/r=src
//@[rpass8] compile-flags: -C debuginfo=2 --diagnostic-width=80 --remap-path-prefix=/home/bors/r=src
//@ ignore-backends: gcc

pub fn main() {
    // empty
}
