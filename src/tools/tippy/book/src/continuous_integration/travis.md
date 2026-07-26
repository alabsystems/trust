# Travis CI

After selecting the project-pinned Trust toolchain, run Tippy the same way you
use it locally:

```yml
script:
  - targo tippy
  # if you want the build job to fail when encountering warnings, use
  - targo tippy -- -D warnings
  # in order to also check tests and non-default crate features, use
  - targo tippy --all-targets --all-features -- -D warnings
  - targo --unverified test
  # etc.
```
