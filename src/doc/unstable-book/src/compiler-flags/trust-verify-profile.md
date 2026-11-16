# Trust verification profile

The tracking issue for this feature is internal to Trust.

------------------------

`-Z trust-verify-profile=<name>` names the verification profile that selects
which proof obligations a compilation generates. It is the **single carrier** of
the hardened boundary obligation set: there is no separate boolean, and no
environment variable, that can turn hardened obligations on or off.

## Registered hardened profiles

`hardened`, `unix_hardened`, `coreutils_hardened` (`-` and `_` are the same
separator; matching is case-insensitive). **Anything else is an error.**

The registry is closed by design. Hardened obligations are fail-closed proof
requirements on `unwrap`/`expect`, path re-resolution, byte/text boundary loss,
discarded errors, and privilege transitions — which profiles demand them is a
recorded decision, not a consequence of a profile name happening to mention a
platform.

## Why an unregistered name is refused

An unregistered name used to be accepted as "an ordinary profile label" that
generated the ordinary obligation set. Because this flag selects the hardened
obligation set **and has no other consumer in the compiler**, that made a typo
— `unix_hardend`, `unix_hardened_v2` — verify exactly what passing no profile
verifies, while the front end that supplied the label went on announcing
``hardened profile `<name>` enabled`` and writing that name into the proof
record. The gate was weaker than every visible signal said it was.

So the flag is fail-closed on its value: a compilation that names a profile
gets that profile or no verdict. A compilation that wants no hardened
obligations omits the flag, which is what `targo trust --no-hardened` and
`[trust] hardened = false` do. Falling back to a registered profile was
rejected: silently verifying something other than what the command line asked
for is the same surprise in the other direction.

## Why one carrier

Hardened used to be decided by `-Z trust-verify-hardened` OR-ed with a lexical
rule over the profile name. The compiler defaulted the boolean to off and
`targo trust check` defaulted it to on, so raw `trustc` and the Cargo front door
generated different obligation sets for the same source with nothing on either
command line to say so.

Now the obligation set follows the profile and only the profile.
`targo trust check` supplies `unix_hardened` from project policy (`--hardened`
is its explicit spelling, `--no-hardened` opts out, `--trust-profile <name>`
selects another), and `trustc -Z trust-verify-profile=unix_hardened` generates
exactly the same obligations. A compilation with no profile has no hardened
obligations on either path; a compilation with a profile nobody registered
has no verdict at all.
