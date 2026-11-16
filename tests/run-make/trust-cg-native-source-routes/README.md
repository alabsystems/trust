# Strict closure-free source-native regression

This fixture compiles six real Rust sources through the native fullCompiler
backend at O0 and O3. It supplies no artificial closure or FnOnce anchor and no
positive output-gate flag; the default Strict policy must ship every object.
The source-contract pass is off for this output-refinement fixture, as in the
existing compiler-lane recipes. The independent CER output gate remains strict.

The constant, identity, non-inlined typed local helper, C-u8, and original
C-u16 identity and raw-pointer identity cases must produce exactly
1 + 1 + 2 + 1 + 1 + 1 function
certificates per optimization level.
The test independently reads each object's actual defined function symbols,
checks their exact certificate/kernel-closure set and whole object/function
byte hashes, and pins the complete actual placement map. The byte's placement
stays width8/Zext with a full32 physical contract; the original `wide_byte.rs`
stays width16/Zext with its own exact placement digest and u16 schema. A changed width, erased
extension, extra function/anchor, missing helper, solver-only closure, Unknown,
or stale certificate cannot satisfy the checks.

A C driver links the six actual compiler objects and checks full64 scalar
results plus all 256 C-u8 values. Assembly wrappers retain the full W0 result,
including for legal inputs with dirty X0 high32. Their protocol is reused from
`trust-cg-source-c-u8-abi`; that fixture's subject and anchor are not included.
A separately hand-authored bad-W0 discriminator has the right low byte and
wrong high bits, ensuring the observer itself has not become a byte-only check.
It is test sensitivity evidence, not compiler output or proof authority.
The original C-u16 program also runs boundary values through a full-W0 assembly
observer, including legal inputs with dirty X0 high32. The dedicated
`trust-cg-source-c-u16-abi` fixture owns the complete u16 value sweep.
The raw-pointer case checks the complete address word, including null and
nonzero high32 bits, without dereferencing or converting it to a reference.

The signed-byte extension input must retain its current named source
ABI refusal and emit no object/certificate. Requesting output-gate off must
also refuse. These are negative policy/contract controls, never permissive
positive compiles. The previously refused unsigned16 program remains in the
same corpus as a newly supported positive, with its complete physical contract;
it is not removed when support advances. The isolated engineering695 baseline
recorded named source-ABI refusals for both C-i8 and C-u16. This fixture never
relaxes a refusal or adds fallback merely to make the test pass.

Run only after a completed SDK/backend built from a source revision containing
the source-native primitive routing and C-u8 proof changes is bound to bootstrap:

```sh
build-slot -- python3 x.py test --stage 1 tests/run-make/trust-cg-native-source-routes
```

The compiletest summary must confirm this fixture actually executed, rather
than being skipped for a missing backend or mismatched host. This is the focused
future execution command, not a claimed run. Preparing or
host-typechecking `rmake.rs`, syntax-checking its C/assembly, or compiling with
an older installed compiler does not establish the regression passed against
the patched source compiler. Preserve the SDK/source binding, stdout/stderr,
objects, certificates and native drivers from the actual run. No default-backend
change, MIR removal, source-to-IR refinement theorem or release completion is
claimed by this one fixture.
