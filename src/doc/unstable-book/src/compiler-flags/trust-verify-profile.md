# Trust verification profile

The tracking issue for this feature is internal to Trust.

------------------------

`-Z trust-verify-profile=<name>` names the verification profile that selects
which proof obligations a compilation generates. It is the **single carrier** of
the hardened boundary obligation set: there is no separate boolean, and no
environment variable, that can turn hardened obligations on or off.

## Registered hardened profiles

`hardened`, `unix_hardened`, `coreutils_hardened` (`-` and `_` are the same
separator; matching is case-insensitive). Anything else is an ordinary profile
label and generates the ordinary obligation set.

The registry is closed by design. Hardened obligations are fail-closed proof
requirements on `unwrap`/`expect`, path re-resolution, byte/text boundary loss,
discarded errors, and privilege transitions — which profiles demand them is a
recorded decision, not a consequence of a profile name happening to mention a
platform.

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
obligations on either path.
