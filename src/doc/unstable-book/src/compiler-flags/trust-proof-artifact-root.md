# `trust-proof-artifact-root`

The tracking issue for this feature is internal to Trust.

------------------------

`-Z trust-proof-artifact-root=<absolute-path>` writes externalized proof
materializations beneath an explicit private root instead of carrying them
inline.

Without it, proof bytes stay inline (bounded) in the transport and `trustc`
writes **no** proof store at all. That is the point of requiring the option: a
compiler that fell back to an ambient working-directory store would be writing
proof authority to a location nobody named.

The path must be absolute and non-empty; a relative or empty value is rejected,
including when a compiler embedding injects it through a callback. The root must
*already* exist, already be canonical, and on Unix already be owner-private
(mode 0700) — the compiler validates it rather than creating it, so it cannot be
talked into provisioning a world-readable proof store. Each directory component
is opened without traversing a pre-existing symlink (`create_dir_all` is
deliberately not used, because it follows intermediate symlinks), and a store
that canonicalizes outside the configured root is an error.

Entries are content-addressed by SHA-256 and installed through a temporary file
plus hard link, so a concurrent writer cannot publish partial bytes. An existing
entry whose length disagrees with the materialization, or that is not a
non-symlink regular file, is an error rather than something to overwrite.

The location is untracked: it selects where evidence lands, not what was proved.
`targo trust` provisions a session-scoped root and reads the evidence back from
it, which is why `TRUSTFLAGS` refuses this option — redirecting the root would
sever artifact collection from the run that produced it.
