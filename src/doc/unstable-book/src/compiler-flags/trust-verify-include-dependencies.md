# `trust-verify-include-dependencies`

The tracking issue for this feature is internal to Trust.

------------------------

`-Z trust-verify-include-dependencies` (default: off) brings authenticated
dependency-crate MIR into the Trust verification scope.

By default a compilation verifies the crate in front of it. A body reached
through a dependency — non-local MIR, or a function skipped as external
dependency scope — is left out, so an ordinary Cargo graph stays buildable
without every transitive crate having to prove closed.

The flag changes what that omission *means*. With dependency scope excluded, an
`ExternalDependencyScope` or `NonLocalMir` skip is not a coverage failure; with
this flag set, it is, and the build fails closed on it like any other in-scope
gap. Turning it on is therefore a scope widening rather than a reporting
preference, which is why it is tracked into the crate hash: a build that proved
more must not share an artifact identity with one that proved less. It also
enters the verification cache key, so an included-dependencies run cannot reuse
a cached excluded-dependencies verdict.

