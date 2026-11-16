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

The `declared_inputs` example measures an existing declared graph through the
same public window and content observers. Its JSON input has exactly `root`,
`paths` and `recursive` fields, for example:

```json
{"root":"/absolute/package","paths":["src","/absolute/shared/schema"],"recursive":true}
```

Run it from the canonical workspace with the normal build admission wrapper:

```sh
targo --unverified run --locked -p trust-fs-observation --example declared_inputs -- inputs.json
```

It retains an original window, captures the complete declared content twice,
checks both against that window and compares their snapshots. Its JSON output
includes actual work counters. Unavailable custody or changed content returns an
error; no limit is changed. A successful measurement supplies no cache admission
or proof claim and does not establish undeclared-input completeness.

Licensed under the repository's MIT OR Apache-2.0 licenses.
