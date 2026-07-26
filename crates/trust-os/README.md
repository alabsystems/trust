# trust-os

`trust-os` provides a small hardened filesystem wrapper surface for Trust.

The first API centers operations on `DirFd`, a directory file descriptor anchor.
After an anchor is opened, opening, creating, removing, and identifying files
through `DirFd` keeps lookup relative to that already-open directory and rejects
absolute paths, `..`, empty paths, and NUL bytes before issuing Unix `*at`
syscalls. For multi-component leaf operations, `trust-os` resolves each
intermediate component by opening it relative to the previous descriptor with
`O_DIRECTORY`, `O_NOFOLLOW`, and `O_CLOEXEC`. An intermediate symlink therefore
makes the operation fail instead of becoming the parent directory for remaining
components, preserving path-beneath behavior under the anchor. Final-leaf
handling is operation-specific: `open_file`, `create_file`, and `metadata` do
not follow leaf symlinks; `identity` identifies the leaf without following it;
and `remove_file` unlinks the leaf name.

```rust
use std::io::{Read, Write};
use trust_os::{DirFd, UnixMode};

let dir = DirFd::open("/var/lib/trust")?;
let mut file = dir.create_file("result.json", UnixMode::OWNER_READ_WRITE)?;
file.write_all(br#"{"status":"ok"}"#)?;

let identity = dir.identity("result.json")?;
let mut reopened = dir.open_file("result.json")?;

let mut contents = String::new();
reopened.read_to_string(&mut contents)?;
# std::io::Result::Ok(())
```

On non-Unix targets, the API is present but returns
`std::io::ErrorKind::Unsupported`.
