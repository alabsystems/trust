"""Prove bounded Cargo input deltas from two immutable Git trees.

This is deliberately not a resolver. Only additions of already-locked local
dependency edges are understood. Package identity, source, feature definitions, targets,
workspace policy and every other input must remain unchanged. Unknown deltas
retain land_select's global rule. Activated dependency packages are included in
the impact set: a new edge can activate their features in a shared build.
"""
from __future__ import annotations

import copy
import posixpath
import tomllib


def scoped_inputs(graph, base, changed):
    """Return path -> affected package dirs, or leave unproved paths absent.

    The lock change and its manifest changes are accepted together, never by
    path alone. All lock identities/metadata and all preexisting edges must be
    exact. This conservative first case needs a changed canonical Cargo.lock.
    """
    from land_select import TreeIndex, _index_spellings, fold

    if "Cargo.lock" not in changed:
        return {}
    try:
        before = TreeIndex.load(graph.index.repo, base)
        after = graph.index
        # Root/workspace policy is not part of the bounded case.
        if before.entries.get("Cargo.toml") != after.entries.get("Cargo.toml"):
            return {}
        manifests = [p for p in changed if p.endswith("/Cargo.toml")]
        if not manifests:
            return {}

        def document(index, path):
            if index.entries.get(path, (None,))[0] not in ("100644", "100755"):
                raise ValueError("not an existing regular Cargo input")
            return tomllib.loads(index.read_blobs([path])[path].decode("utf-8"))

        old_lock, new_lock = document(before, "Cargo.lock"), document(after, "Cargo.lock")

        def rows(lock):
            result = {}
            for row in lock.get("package", []):
                key = (row["name"], row["version"], row.get("source", ""))
                if key in result:
                    raise ValueError("ambiguous lock identity")
                deps = row.get("dependencies", [])
                if not isinstance(deps, list) or len(deps) != len(set(deps)):
                    raise ValueError("invalid lock edges")
                result[key] = row
            return result

        old_rows, new_rows = rows(old_lock), rows(new_lock)
        if old_rows.keys() != new_rows.keys():
            return {}
        if {k: v for k, v in old_lock.items() if k != "package"} != {
                k: v for k, v in new_lock.items() if k != "package"}:
            return {}

        def resolve(edge):
            words = edge.split()
            if not 1 <= len(words) <= 3 or (len(words) == 3 and not (words[2].startswith("(") and words[2].endswith(")"))):
                raise ValueError("unrecognized lock edge")
            candidates = [key for key in old_rows if key[0] == words[0]
                          and (len(words) < 2 or key[1] == words[1])
                          and (len(words) < 3 or key[2] == words[2].strip("()"))]
            if len(candidates) != 1:
                raise ValueError("ambiguous lock edge")
            return candidates[0]

        def activation_readers(keys):
            # The lock closure includes registry/git identities and optional,
            # build, dev and target edges. A name-only consumer match is an
            # intentional superset across versions/sources/resolver contexts.
            # It cannot miss a downstream shared feature instance merely
            # because our source graph represents only local packages.
            closure, pending = set(), list(keys)
            while pending:
                key = pending.pop()
                if key in closure:
                    continue
                closure.add(key)
                pending.extend(resolve(edge) for edge in old_rows[key].get("dependencies", []))
            names = {key[0] for key in closure}
            return {p.dir for p in graph.packages.values() if p.name in names or p.dep_names & names}

        expected = {}
        impacts = {}
        for path in manifests:
            owner = posixpath.dirname(path)
            if owner not in graph.packages:
                return {}
            old, new = document(before, path), document(after, path)
            # Target tables, feature maps, workspace inheritance/patching and
            # package metadata are exact; only ordinary dependency additions.
            old_rest, new_rest = copy.deepcopy(old), copy.deepcopy(new)
            old_deps = old_rest.pop("dependencies", {})
            new_deps = new_rest.pop("dependencies", {})
            if not isinstance(old_deps, dict) or not isinstance(new_deps, dict):
                return {}
            if old_rest != new_rest or any(new_deps.get(k) != v for k, v in old_deps.items()):
                return {}
            added = new_deps.keys() - old_deps.keys()
            if not added:
                return {}
            package = new.get("package", {})
            owner_key = (package.get("name"), package.get("version"), "")
            if (owner_key not in old_rows or owner_key in expected
                    or graph.by_name.get(owner_key[0]) != {owner}):
                return {}
            targets = set()
            affected = {owner}
            for name in added:
                spec = new_deps[name]
                if not isinstance(spec, dict) or "path" not in spec or set(spec) - {"path", "version", "package"}:
                    return {}
                target = posixpath.normpath(posixpath.join(owner, spec["path"]))
                if target.startswith(("../", "/")) or target == "..":
                    return {}
                # Check the ORIGINAL traversal before normpath erases a
                # symlink/.. or an untracked directory. Every traversed
                # directory must be an unambiguous tracked-tree directory.
                parts = owner.split("/")
                spellings = _index_spellings(graph)
                for segment in spec["path"].split("/"):
                    if segment in ("", "."):
                        continue
                    if segment == "..":
                        if not parts:
                            return {}
                        parts.pop()
                    else:
                        parts.append(segment)
                        prefix = "/".join(parts)
                        if prefix in after.entries or spellings.get(fold(prefix)) != {prefix}:
                            return {}
                target_manifest = target + "/Cargo.toml"
                if before.entries.get(target_manifest) != after.entries.get(target_manifest):
                    return {}
                # An aliasing/symlink path cannot prove a unique local input.
                parts = target_manifest.split("/")
                if any(after.entries.get("/".join(parts[:i]), (None,))[0] == "120000"
                       for i in range(1, len(parts) + 1)):
                    return {}
                target_doc = document(after, target_manifest).get("package", {})
                target_key = (target_doc.get("name"), target_doc.get("version"), "")
                if (target_key not in old_rows or target_key[0] != spec.get("package", name)
                        or graph.by_name.get(target_key[0]) != {target}):
                    return {}
                if "version" in spec and spec["version"] != "=" + target_key[1]:
                    return {}
                targets.add(target_key)
                # Defaults may forward activation through several local
                # dependencies. Every consumer of every such package must be
                # reached, not just consumers of the immediate new target.
                affected.update(graph.closure({target}))
            affected.update(activation_readers(targets))
            expected[owner_key] = targets
            impacts[path] = affected

        actual = {}
        for key, old in old_rows.items():
            new = new_rows[key]
            if {k: v for k, v in old.items() if k != "dependencies"} != {
                    k: v for k, v in new.items() if k != "dependencies"}:
                return {}
            old_edges, new_edges = set(old.get("dependencies", [])), set(new.get("dependencies", []))
            if not old_edges <= new_edges:
                return {}
            if new_edges != old_edges:
                actual[key] = {resolve(edge) for edge in new_edges - old_edges}
        if actual != expected:
            return {}
        impacts["Cargo.lock"] = set().union(*impacts.values())
        return impacts
    except (RuntimeError, UnicodeError, ValueError, TypeError, KeyError):
        return {}


def existing_local_lock_repair(graph, base, path):
    """Prove a lock-only catch-up to unchanged, already-declared local edges.

    This supplies source-component eligibility only. It changes neither the
    full diagnostic selection nor Cargo's required locked/frozen execution.
    External identities, checksums, metadata and old edges remain exact.
    """
    from land_select import TreeIndex, _collect_dep_tables, _index_spellings, fold

    try:
        if not path.endswith('/Cargo.lock'):
            return False
        before, after = TreeIndex.load(graph.index.repo, base), graph.index
        spellings = _index_spellings(graph)

        def document(index, name):
            if index.entries.get(name, (None,))[0] not in ('100644', '100755'):
                raise ValueError('nonregular Cargo input')
            parts = name.split('/')
            if any('/'.join(parts[:i]) in index.entries for i in range(1, len(parts))):
                raise ValueError('indirected Cargo input')
            return tomllib.loads(index.read_blobs([name])[name].decode('utf-8'))

        workspace = posixpath.dirname(path) + '/Cargo.toml'
        if before.entries.get(workspace) != after.entries.get(workspace):
            return False
        if not isinstance(document(after, workspace).get('workspace'), dict):
            return False
        manifests = {p for p in before.entries.keys() | after.entries.keys() if p.endswith('/Cargo.toml') or p == 'Cargo.toml'}
        for manifest in manifests:
            if before.entries.get(manifest) == after.entries.get(manifest):
                continue
            if document(before, manifest).get('workspace') != document(after, manifest).get('workspace'):
                return False
        configs = {p for p in before.entries.keys() | after.entries.keys()
                   if p.endswith(('.cargo/config', '.cargo/config.toml', 'rust-toolchain', 'rust-toolchain.toml'))}
        if any(before.entries.get(p) != after.entries.get(p) for p in configs):
            return False
        old, new = document(before, path), document(after, path)
        if {k: v for k, v in old.items() if k != 'package'} != {k: v for k, v in new.items() if k != 'package'}:
            return False

        def rows(lock):
            result = {}
            for row in lock['package']:
                key = row['name'], row['version'], row.get('source', '')
                edges = row.get('dependencies', [])
                if key in result or not isinstance(edges, list) or any(not isinstance(e, str) for e in edges) or len(set(edges)) != len(edges):
                    raise ValueError('ambiguous lock record')
                result[key] = row
            return result

        old_rows, new_rows = rows(old), rows(new)
        if old_rows.keys() != new_rows.keys():
            return False

        def local_manifest(key):
            if key[2] or len(graph.by_name.get(key[0], set())) != 1:
                raise ValueError('not a unique local package')
            owner = next(iter(graph.by_name[key[0]]))
            name = owner + '/Cargo.toml'
            if before.entries.get(name) != after.entries.get(name) or graph.opaque_owner(name):
                raise ValueError('changed or unknown local manifest')
            doc = document(after, name)
            package = doc.get('package', {})
            if 'workspace' in package:
                raise ValueError('explicit workspace routing is not proved')
            version = package.get('version')
            if version == {'workspace': True}:
                roots = [root for root, members in graph.workspace_members.items()
                         if owner in members and (not root or owner.startswith(root + '/'))]
                if len(roots) != 1:
                    raise ValueError('ambiguous inherited package version')
                manifest = (roots[0] + '/' if roots[0] else '') + 'Cargo.toml'
                if before.entries.get(manifest) != after.entries.get(manifest):
                    raise ValueError('changed inherited package inputs')
                version = document(after, manifest).get('workspace', {}).get('package', {}).get('version')
            if not isinstance(version, str) or (package.get('name'), version) != key[:2]:
                raise ValueError('unproved package identity')
            return owner, doc

        added = False
        for key, row in old_rows.items():
            other = new_rows[key]
            if {k: v for k, v in row.items() if k != 'dependencies'} != {k: v for k, v in other.items() if k != 'dependencies'}:
                return False
            old_edges, new_edges = set(row.get('dependencies', [])), set(other.get('dependencies', []))
            if not old_edges <= new_edges:
                return False
            for edge in new_edges - old_edges:
                words = edge.split()
                if not 1 <= len(words) <= 2:
                    return False
                targets = [k for k in old_rows if k[0] == words[0] and (len(words) == 1 or k[1] == words[1])]
                if len(targets) != 1:
                    return False
                target_key = targets[0]
                target, _ = local_manifest(target_key)
                owner, doc = local_manifest(key)
                matched = False
                for table in _collect_dep_tables(doc):
                    for alias, spec in table.items():
                        if not isinstance(spec, dict) or not isinstance(spec.get('path'), str) or set(spec) - {'path', 'version', 'package'}:
                            continue
                        if spec['path'].startswith('/') or '\\' in spec['path']:
                            continue
                        if spec.get('package', alias) != target_key[0] or ('version' in spec and spec['version'] != '=' + target_key[1]):
                            continue
                        parts = owner.split('/')
                        for segment in spec['path'].split('/'):
                            if segment in ('', '.'):
                                continue
                            if segment == '..':
                                if not parts:
                                    raise ValueError('dependency escapes repository')
                                parts.pop()
                            else:
                                parts.append(segment)
                                prefix = '/'.join(parts)
                                if prefix in after.entries or spellings.get(fold(prefix)) != {prefix}:
                                    raise ValueError('dependency traversal is not a tracked directory')
                        matched |= '/'.join(parts) == target
                if not matched:
                    return False
                added = True
        return added
    except (OSError, RuntimeError, UnicodeError, ValueError, TypeError, KeyError, AttributeError):
        return False
