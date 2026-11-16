# Native proc-macro Client fixture

`native_worker_client.rs` is a real proc-macro crate, with two compiler-generated
Client declarations. Its second entry includes the same 32-method exercise as
the ordinary Dispatcher tests; no second token or span model is introduced.

Build it with the matching Trust toolchain using a temporary standalone Targo
manifest whose `[lib]` has `proc-macro = true` and `path` names this source.
Use `targo generate-lockfile --offline` and `targo --unverified build --locked
--offline` for that manifest. Retain the source/tool/runtime hashes and the
actual compiler-reported DSO. Read its generated
`__rustc_proc_macro_decls_<id>__` symbol from the native symbol table; a guessed
symbol or a manually constructed Client array is not this fixture.

Run the already-built `rustc_expand` test binary with
`real_proc_macro_dso_preserves_declared_client_and_native_tokens --ignored
--nocapture --test-threads=1`, setting `TRUST_D21_NATIVE_DSO` to that DSO and
`TRUST_D21_NATIVE_DSO_SYMBOL` to the generated symbol. The test has no
missing-fixture success path. Its ordinary ignored status is not qualification.

The DSO is loaded only by the disposable child, not by the compiler parent.
This checks the actual native ABI and protocol. It does not install a sandbox,
authenticate a general native closure, enable proc-macro proof authority or
establish the semantics of arbitrary macro expansions.

On Darwin, `run_darwin_readonly_image.py --test-binary <test binary> --dso <DSO>
--sha256 <exact DSO digest> --declaration-symbol <generated symbol>` runs the
separate fixed-policy diagnostic. Run it through the normal build-slot owner.
It creates and mounts only its own read-only image, unlinks the backing image
name, runs the real native Client under the canonical deny-default policy, and
detaches that owned image after child teardown. The mount path deliberately
contains policy-sensitive characters. Source bytes, compiler/runtime identities
and this explicit test result remain necessary qualification inputs.

This tests one real native image and OS restriction. It does not close ambient
descriptors, authenticate a full native dependency graph, establish resource
limits or add any production loader/PM-1 authority.

Build `native_worker_constructor.rs` the same way and add
`--constructor-control` to the runner to exercise an actual Mach-O initializer.
The unrestricted Client must return `wrong_constructor_state_2_tmp_<hex>`, where
the hex bytes name the runner-created directory. This demonstrates that its
initializer received the explicit private TMPDIR and could create its witness.
The child keeps a cleared environment; only the separately named, validated
0700 owner directory becomes its TMPDIR. The pre-restriction probe also requires
that directory, and the restricted Client returns its actual constructor path.
Under the fixed
policy, both entries require state1 (actual EPERM/EACCES), so an initializer
that never ran, or failed for another reason, cannot pass. The restricted second
entry then executes the shared 32-method test. Original DSO bytes and every
failed diagnostic remain separate from this additional fixture.
