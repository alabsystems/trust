# `trust-verify-package-name`

The tracking issue for this feature is internal to Trust.

------------------------

This is the non-empty Cargo package identity in Targo's reserved
role/package/session metadata tuple. The compiler rejects a package name unless
`-Z trust-verify-session` is also present, and every non-`unscoped` crate role
requires both fields.

Direct compiler invocations should omit this option. A raw `unscoped` compile
may use a session-only nonce for freshness without claiming a Cargo unit role.
