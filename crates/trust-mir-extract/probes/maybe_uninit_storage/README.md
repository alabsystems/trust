# Source-bound MaybeUninit geometry

`original_clean.rs` is an engineering rustc-private observer over the actual
Clean `MonadInst::uv` source. Build it against the same source version of
MirExtract and a coherent compiler-private native/metadata closure. Invoke it
with the original crate's exact compiler arguments, dependency identities and
matching source compiler sysroot. It stops after expansion; it is not a whole
crate build, native body qualification or source certification.

The observer retains original rustc type identity, selects the `[Level; 2]`
payload by exact element type, and checks actual source geometry 80/8. It also
rejects the original parent and Level types as storage witnesses. Traversal is
a diagnostic inventory capped at 1024 distinct types, not an authority path.
The production constructor grants only addressable storage geometry; it grants
no active union field, initialized value, drop, call ABI, provenance or access
permission. The associated IR storage type must reject all by-value traffic.

Recorded engineering compiler: immutable SDK ffa141252dceb40e74d991218b336ce0f3516e6d;
private component compiler: matching seed29ebb403de7a102850d6cb10a62d5cc3baf723ed.
The ordinary source input was Clean7f25ef5deae5f41637d9c24ed512aea6a07ac310.
No installed SDK or dependency pins were altered by this probe.
