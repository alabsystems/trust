# `trust-verify-crate-role`

The tracking issue for this feature is internal to Trust.

------------------------

This is a reserved Targo-to-compiler protocol field. Targo sets `primary`,
`dependency`, or `build-script` together with both
`-Z trust-verify-package-name` and `-Z trust-verify-session`. The compiler
rejects any non-`unscoped` role unless that complete metadata tuple is present.

Direct compiler invocations leave the default role, `unscoped`, unchanged.
That role is strict, so this option is not a user-facing way to weaken or select
verification scope. Dependencies remain outside strict proof scope unless the
separate include-dependencies policy explicitly includes them; build scripts
remain outside proof scope.
