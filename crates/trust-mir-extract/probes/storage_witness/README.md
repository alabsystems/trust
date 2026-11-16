# Exact compiler storage witness controls

The native rustc-private observer calls the published compiler constructor for
11 actual source types, in fresh epoch-scoped contexts. Five real MaybeUninit
payloads have exact scalar8/8, array16/8, unit0/1, empty-array0/8, aligned32/32
geometry. Six refusals cover a physical-layout lookalike union, ManuallyDrop,
a plain struct, a pointer to MaybeUninit, generic T and an unrevealed Free alias
to the fixture's opaque declaration. No source values are read or constructed.

The initial opaque-flag premise failed after ten passing cases. The real
signature retains Alias(No, Free Hidden), so has_opaque_types is false. Keep
that failed diagnostic. The maintained control explicitly asserts an original
alias is still present, expects refusal and does not claim direct opaque-kind
coverage. All11 final controls pass and ordinary Rust analysis continues to
completion, with metadata only and the dummy backend. No native source function
is emitted or invoked and no formal/source/native grade follows.

Compile observer.rs as a standalone rustc-private binary against the coherent
published MirExtract528f7c component and matching repeated native+rmeta extern
pairs. The retained engineering recipe is
<home>/trust-storage-representation/build_witness_controls.py; it uses
seed29ebb with its own sysroot and the immutable source component. Run with
SDKffa stage1+stage0 lib on DYLD_LIBRARY_PATH, fixture.rs as source, the actual
stage1 sysroot, and -Zno-codegen -Zcodegen-backend=dummy -Zthreads=1
-Ztrust-verify=off -Ztrust-ir-lower=no --emit=metadata. Every heavy command used
build-slot. SDK/defaults/pins and production source were unchanged.
