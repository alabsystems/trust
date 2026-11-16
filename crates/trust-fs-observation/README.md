# trust-fs-observation

The canonical bounded content observer and opened-file identity implementation
used by Targo and future compiler consumers. Snapshot version 1, digest framing,
limits, symlink resolution, ancestor checks and work telemetry retain their
existing behavior. Live windows retain original namespace and file change stamps; serialized
snapshots convey data and cannot recreate a live window.

This is filesystem consistency machinery, not proof, hermeticity, process
authentication or authority to move/delete artifacts. The runtime dependency
graph contains no Cargo implementation. `test-support` exposes the existing
isolated test-world helper and is enabled by Targo only as a dev-dependency.
Ordinary builds do not require tempfile for that helper.

Licensed under the repository's MIT OR Apache-2.0 licenses.
