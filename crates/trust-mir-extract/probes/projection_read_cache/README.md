# Completed projection reader controls

These are native compiler callbacks over ordinary Rust inputs. Build observers
with the same compiler-private native/metadata closure as the selected complete
MirExtract component, and compile fixtures against that compiler's target std.
Use an explicit unverified engineering lane. They request no layouts and grant
no byte, active-field, ABI, source-proof or certificate authority.

`fixture.rs` and `observer.rs` check six source cases: recursive repeated reads,
an unsafe later sibling, distinct generic arguments, a nonleaf constant RHS,
growing instantiations, and a named leaf RHS. The leaf case enters an unnamed
freeze after a successful read: both the retained context and a fresh context
must refuse; dropping that frame must permit independent reproving. A context
may reset and reprove after an epoch change, so permanent context death is not
an expectation. The initial contrary test failed and is retained in the
qualification evidence. These six cases pass both before and after the result
cache; they are safety controls, not its causal positive discriminator.

`foreign_fixture.rs` and `foreign_observer.rs` use the actual `smallvec` crate
with its `union` and `const_generics` features. Supply its matching target
metadata as an ordinary `--extern smallvec=...` fixture dependency. The source
parameters explicitly expose independent Leaf, Expr and reached Arc types; the
observer checks Leaf and Expr before Arc, matching the measured original query
order. The initial fixture omitted Leaf priming and failed before reaching Arc;
that losing row remains recorded.

With `TRUST_COMPLETED_READER_CONFIRMED=1`, the two foreign cases require the
repeated Arc query to succeed and its unsafe-sibling counterpart to refuse.
The same source/order/flag failed on the pre-cache component with Arc false and
passed on the hardened result-cache component with Arc true. Without the flag,
the observer retains the historical Arc-refusal expectation. This is a bounded
query result comparison, not an original-model completion or speed claim.

The initial producer qualification used current partial compiler `5b1138a921`,
its declared `82bb867e` seed/private closure and target std, current IR R2, and
the existing Clean-C1 target `smallvec` metadata (1.15.1; `const_generics`,
`drain_filter`, `may_dangle`, `union`). No SDK, dependency pin or compiler default
was changed. Durable local commands, input hashes and losing/green logs are in
`trust-current-native-storage-component-evidence/projection-read-cache-*` and
`foreign-projection-read-cache-*` alongside the native component handoff.
