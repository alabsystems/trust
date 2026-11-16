# Live Rust nominal parameter custody controls

`observer.rs` includes the **exact new production module**, not a mock TyCtxt,
reimplementation, parsed JSON, or emitted-module surrogate. It compiles against
one matching private compiler namespace and runs actual Rustc `after_analysis`
queries on the unchanged original `fixture.rs`. It checks 28 assertions,
including owner/argument identity, alias equality, distinct same-shaped enums,
by-value/type/generic/payload refusals, explicit arity/variant bounds and a
signed/noncontiguous declared enum. It never queries optimized MIR or a layout.

`same_crate_names.rs` uses TWO genuinely distinct Cargo packages. Both compile
**the same `external_kind.rs` bytes**, with library name `duplicated_kind`.
Pass their separate full `.rmeta` files as `--extern left=...` / `--extern right=...`.
Their canonical crate/item QNames agree; actual Rustc keys and live nominal
identities differ. Four assertions check that distinction. `def_path_str` may
render dependency aliases as left/right, so the test uses the compiler's
canonical crate name plus original DefPath rather than assuming its diagnostic
renderer uses canonical names.

The three `*_refusal.rs` files MUST fail compilation with the expected
error: private-field construction E0451, cloning E0277, transferring the live
observation to another compiler's Send callback E0277. A nonzero exit alone is
not a pass. The observation explicitly uses an Rc PhantomData thread-affinity
marker; no unsafe Send/Sync implementation or fabricated context is allowed.

Use the `Cargo.toml.in` template in a new owned external workspace. Qualify with
`targo --unverified rustc` and affected `targo tippy ... --no-deps`. Select the
compiler that produced the private metadata, its matching sysroot, and a complete
matching metadata/native namespace. For each explicit compiler extern, pass BOTH
the full `.rmeta` and its native `.rlib`/`.dylib` using repeated `--extern` entries.
The compiler's actual `parse_externs`/locator supports this exact-path pairing;
a native stub alone cannot replace full metadata, and full metadata alone is
not a native link input. Never guess a native pair or bypass the loader's checks.

The qualified engineering run used immutable SDK ffa141, its Trust seed29ebb,
private driver96f842ecb14a5047, and the exact Cargo fingerprint dependency closure
of that driver. Runtime input compilation uses that driver's SDK sysroot; building
the observer uses the seed's sysroot. Root private externs are rustc_driver,
rustc_data_structures, rustc_hir, rustc_interface, rustc_middle and rustc_span.
The live driver runs with `-Zno-codegen -Zcodegen-backend=dummy -Zthreads=1`.
Capture inherited GNU jobserver transport as the observer's first operation;
all builds/runs use `build-slot`. This is standalone component qualification,
not rebuilding or promoting an SDK, a verified Targo lane, a source/body
correspondence theorem or evidence that historical JSON has this live origin.
