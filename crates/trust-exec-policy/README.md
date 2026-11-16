# Native final-exec policy

`FootprintLimit` prepares equal positive active/inactive fatal footprint limits
using Apple's native spawn-attribute setter. It does not launch, reserve memory,
measure RSS, install a sandbox, or manufacture a policy receipt. The launch owner
must apply it at the final payload exec and retain actual child custody.

The ABI and fatal flags follow Apple's maintained
[libsyscall setter](https://github.com/apple-oss-distributions/xnu/blob/main/libsyscall/wrappers/spawn/posix_spawn.c)
and [spawn attributes](https://github.com/apple-oss-distributions/xnu/blob/main/bsd/sys/spawn_internal.h).
Setter success alone is no evidence of a live child's installed policy or of a
hard RSS quota. Unsupported native policy must remain an explicit refusal.

On macOS, `ExecutionSeal` installs one of two fixed self-restrictions: no fork,
or no fork and no exec. There is no caller-supplied sandbox profile. Installation
is irreversible; an error is not a rollback and must not trigger an ordinary
payload fallback. `fork_denied(pid)` is only a native observation and requires
separate process-lifetime authentication. There is deliberately no global
no-exec query API: `sandbox_check(process-exec)` returned EINVAL on the qualified
Mac with both no filter and a path filter. The fixed no-exec profile is instead
qualified by an actual owned child's rejected fork and `/usr/bin/true` exec.
Neither its local installation result nor an observation grants resources.

Native qualification also found that installing a second sandbox after the
no-fork profile is refused. Managed final-payload integration must not assume
that a prelude's first sandbox can be tightened after exec.

`restrict_current_to_readonly_image` supplies a separate fixed deny-default
policy for a trusted native-worker entry. It requires an already-open regular
file, an `O_RDONLY` descriptor, and `MNT_RDONLY` from `fstatfs` on that descriptor.
It uses the descriptor's native `F_GETPATH` and its exact `/dev/fd/N` alias as
parameters to `sandbox_init_with_parameters`; pathname bytes are never inserted
into policy source. The parameter ABI is also used by
[Chromium](https://chromium.googlesource.com/chromium/src/+/master/sandbox/mac/seatbelt.cc).
The returned guard retains the descriptor for the native loader.

This is a local OS restriction, not a complete worker or immutable-artifact
receipt. The caller must authenticate bytes and the complete runtime, retain
the read-only mount and descriptor through the child lifetime, close ambient
descriptors, set resource limits, and own cancellation/kill/reap. The policy
does not make existing descriptors harmless. It must precede native
constructors; installation failure is terminal, with no ordinary fallback.
The compiler's PM-1 refusal is unchanged.

`restrict_current_to_macro_worker` is the fixed deny-default policy of the
compiler's proc-macro worker (D21, `-Ztrust-proc-macro-isolation`). The worker
calls it before it opens a proc-macro dylib. It grants file reads and mappings,
writes under one private 0700 directory passed as a parameter, `sysctl` reads
and signals to itself; it denies every other file write, network, fork, exec
and IPC lookup. Its test runs the policy in an owned child and requires each
denial and each grant. It is containment for macro code: it authenticates no
dylib, closes no descriptor and bounds no resource.

Darwin refuses the measured ad-hoc-signed DSO when its own file is unlinked
before `dlopen`. The qualified fixture instead leaves that file linked inside
a read-only mounted image and unlinks the image's backing pathname. The native
test requires actual file-read/write, network, fork and exec denials before
loading the real proc-macro DSO, then exercises all 32 bridge methods. Its
runner also puts quotes and a backslash in the mount path to exercise native
parameter handling. This establishes that bounded case, not general loader or
production macro admission.
