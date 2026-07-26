# `trust-verify-session`

The tracking issue for this feature is internal to Trust.

------------------------

This is a frontend-to-compiler freshness token used by `targo trust` and by
direct single-file verification workflows:

```text
trustc -Z trust-verify-session=unique-nonce your_file.rs
```

The non-empty value has no language or code-generation semantics. It changes the
incremental dependency hash but deliberately does not change the crate hash.
That lets a proof frontend force execution of the requested compiler invocation
without destructively deleting the user's target directory or changing the
crate identity seen by downstream dependencies.

For Cargo unit roles, Targo pairs the session with its reserved package and role
metadata. Every non-`unscoped` role requires the complete role/package/session
tuple, and a package name is rejected without a session. A raw `unscoped`
direct compile may use a session-only nonce because it remains strict and
cannot use freshness metadata to escape verification. Do not set the role or
package protocol fields by hand.
