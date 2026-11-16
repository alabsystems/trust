# `trust-drop-rlib-objects`

The tracking issue for this feature is internal to Trust.

------------------------

`-Z trust-drop-rlib-objects` deletes, on Apple targets with
`-C split-debuginfo=unpacked`, the numbered object files (`*.rcgu.o`) of a
compilation whose only output is an rlib, once the rlib holds them as members.

With unpacked split debuginfo an Apple link writes no DWARF into its output. The
output's debug map (`N_OSO` stabs) records where each object's DWARF lives, and a
link that pulls in an rlib records the rlib's *member*
(`libfoo-<hash>.rlib(<object>)`), never the loose copy beside it. So `lldb`,
`dsymutil` and backtraces read the member, and the loose copies only take disk.

Without the flag rustc keeps them, as upstream rustc does. Which files a
compilation leaves beside its outputs is something a build system, a test or a
directory listing can see, and Trust compiles valid Rust identically to upstream
except for reviewed soundness changes (ruling EW18-DROPIN-1 in
`docs/DECISION_QUEUE.md`).

The flag changes nothing else. Executables, dylibs, `cdylib`s, proc macros and an
`rlib,dylib` compilation keep their objects, since their own debug maps name them.
A `staticlib` keeps them too: a link that uses one records its member, as with an
rlib, but no measurement covered that case, so upstream's rule decides. So does an
rlib compilation that asks for objects with `--emit=obj`, and every target that is
not Apple: ELF split DWARF names the loose `.o`/`.dwo` by path. The option is
untracked: it decides what is deleted after the link, not a byte of any output. An
embedded frontend that Trust deauthorizes (tippy, trustdoc) resets it to the default.

`tests/run-make/apple-rlib-split-debuginfo-objects` pins the default, and
`tests/run-make/trust-apple-rlib-split-debuginfo-objects` the flag.
