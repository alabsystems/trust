# `trust-option-flag-lanes`

The tracking issue for this feature is internal to Trust.

------------------------

`-Ztrust-option-flag-lanes` defaults to `on`. During direct Trust-IR lowering,
opaque `Option<T>` lanes can retain the discriminant as `Bool` even when the
payload cannot be represented. Literal `Some` and `None` stores then retain
the discriminant; the payload is still opaque and existing effect and
verification refusals apply.

`-Ztrust-option-flag-lanes=off` selects the existing conservative `Unit` spelling
for these lanes. This option selects a representation, not proof authority;
it does not authorize verification or suppress unsupported-operation evidence.
The direct lowering controls still determine whether lowering runs at all.

Both the crate hash and incremental dependency identity track this option,
because the two settings produce different Trust-IR. The former
`TRUST_OPTION_FLAG_LANES` environment variable remains rejected as an untracked
semantic/codegen control. Use the explicit `on` and `off` boolean spellings.
