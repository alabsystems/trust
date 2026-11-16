# trust-resource-provenance

`program::HeldProgram` retains original executable/runtime files and selected
directory observations for the new bounded metadata purpose. Its supported
profile reads thin arm64 Mach-O load commands directly, including weak,
reexport, lazy and upward loads; admits only checked sysroot `@rpath` leaves
and OS dependencies; and regenerates the sole loader search path. It binds
the actual suspended main image through the existing kernel reader. Keep it
through real target retirement and validate its original inputs before
accepting a comparison.

This is explicitly held load-command input observation, with a local same-UID
no-name-writer assumption and the OS loader/shared cache in the TCB. It is not
an atomic DLL/namespace snapshot or the C cache's stronger runtime byte
attestation. Outside-root ancestors keep original identity, ownership, mode
and ACL checks; selected root/runtime directories and files keep full original
stamps. Unrelated sibling activity cannot replace the original input. Do not
use this new observation profile to relax existing authenticated test, compile
or immutable cached-image validation. It supplies no CPU, GNU, memory, process,
build, writer, source or proof authority.

Read-only native discovery for the retained aterm resource custodian. Trust and
aterm share this reader and the version-one Book/Record/FileId wire schema.
The host remains responsible for publishing its immutable cache and account
instance book. This crate never creates or repairs account state.

`Store::open_account()?.connect_ancestor(deadline)` pins the original private
store directories, version, lock and immutable image; validates its complete
SHA-256; then connects to the recorded socket and checks native PID, platform
birth, UID, exec identity, loaded image path/inode, host, boot and bounded
ancestry. Socket and backing identities are checked again through the original
connection. A changed or ambiguous observation refuses. Original image handles
and complete metadata stamps avoid hashing the same immutable image at every
subsequent protocol check.

Callers keep `Host` alive, use its connected stream for a bounded exchange,
call `revalidate(deadline)` after the response, and send the protocol's ACK
before dropping it. The retained host keeps the connection open through that
ACK so Darwin's native peer credentials remain observable. The returned path
or JSON by itself grants no admission, memory entitlement, subgroup launch or
settlement. Those require the host's separate checked job/member protocol.

The native adapter supports macOS and Linux; unknown OS observations refuse.
The macOS source was execution-qualified with native identity/image/peer and
ancestry cases. Shared-reader cases exercise an actual cached ancestor with a
different loaded client image, post-reply image mutation, replaced backing,
strict duplicate-free book parsing, bounded private files and Apple ACLs.
Linux source has no execution qualification in this work.

A native consumer can consume discovery with `Host::into_helper(deadline)`.
`PinnedHelper` retains the original immutable image, account backing, socket
parent and native host identity while closing the unused pre-HELLO stream.
The actual helper reconnects for its operation. Cache this selection per root,
then use `validate_child(&Child, deadline)` before delivering private data: the
caller must hold the actual unreaped local helper, whose direct native parent,
lifetime and loaded original image are checked. The local helper is never the
hosted target. These checks grant no memory, CPU or launch authority.

For a read-only operation the actual native producer can use
`PinnedHelper::connect(deadline)` directly. It reconnects to the same original
native peer and clones held image/socket backing instead of rehashing or
selecting another record. Keep the returned `Host` alive through reply,
post-response revalidation and ACK. This path needs no helper process or parent
proof relay and carries no resource grant by itself.
# Held metadata program observations

`program::HeldProgram` retains selected executable/runtime inputs for bounded
native metadata execution and checks the original held image against an actual
native child. These are input observations, not source/writer authentication,
an atomic loader namespace, resource authority or proof. Its explicit policy
retains the system runtime as a TCB input and assumes no concurrent same-UID
name writers. Existing custodian discovery and `PinnedProgram` authority checks
remain unchanged. The maintained module was imported from aterm `77bd657741`
alongside the canonical metadata controller.

`program::produced::HeldOutputRoot` retains the original output directory before
compilation. After the custodian has retired active compiler writers, it can
retain an exact native UnitOutput with `program`, preserving the same original
SDK and output descriptions through loaded-image validation and retirement.
This distinct profile supports bound output runtime directories and original
SDK libraries. It rejects symlink/hard-link aliases, ambiguous libraries, OS
shadowing, escaping search paths and changed input backing. The existing SDK
metadata profile retains its original `root/bin` restriction.

`open_with_evidence` additionally prepares create-only raw failure evidence under
the original output root, after checking the original SDK is disjoint and the
output is not a source root. Each attempt has a separate namespace. The writer
enforces per-file and shared aggregate bounds (at most 1 GiB and 4,096 files),
checks original directory/file identities, and exposes `sync_prefix` before an
owning-custody Unknown abort. Short writes and quota/IO errors remain explicit
incomplete evidence. Evidence never overwrites an earlier attempt or establishes
successful execution, retirement, compilation or proof.

Native qualification at source `d05d1ea123` passed all 30 crate tests, including
the explicitly selected real SDK compiler/Targo input case and actual loaded
child identity. Composed source `8f0ac9ea71` passed nine focused produced/evidence
tests, including exact binary-prefix survival after a real writer exits without
destructors, shared quota exhaustion, source/SDK write refusal and retargeted
backing. Both runs had no ignored tests; their exact source/images/logs are under
`~/.cache/trust/native-reuse-evidence.noindex/native-produced-inputs-881978bf48/`.

Independent review then found a direct-load override gap: the generated
`DYLD_LIBRARY_PATH` also searches by basename before absolute/loader-relative
install names, as implemented by [Apple's dyld path overrides](https://github.com/apple-oss-distributions/dyld/blob/main/dyld/DyldProcessConfig.cpp).
Native source `346ccf4551` reproduced both missing refusals (zero passes, two
failures). Source `84e16dd01c` checks all possible leaf overrides for direct
loads too, requires their exact original path, and passes all eleven focused
produced/evidence controls. Positive direct loads without shadows still bind.
The failed image/source/log and the exact primary dyld source blob
`fd2897555ae887e92433aa113bb3a27fc712d8eb` remain in the same evidence root.

These input/evidence APIs supply no CPU/GNU/memory, source or build authority.
Native workload execution still requires the separate live cooperative-root,
compiler-quiescence and retained foreign-phase implementation. Its positive
Ready and produced-member admission remain unavailable until qualified.
