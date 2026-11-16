use super::*;

fn node(path: &str, kind: AuthorityKind) -> AuthorityNode {
    AuthorityNode {
        path: path.into(),
        kind,
        device: 1,
        inode: 1,
        uid: 0,
        gid: 0,
        mode: 0o755,
        link: None,
    }
}
fn tree() -> BTreeMap<String, AuthorityNode> {
    ["/", "/usr", "/usr/lib"]
        .into_iter()
        .map(|path| (path.into(), node(path, AuthorityKind::Directory)))
        .collect()
}
fn check(
    path: &str,
    kind: AuthorityKind,
    nodes: &BTreeMap<String, AuthorityNode>,
) -> Result<PathAuthority, String> {
    resolve(path, kind, &mut |path| Ok(nodes.get(path.to_str().expect("test path")).cloned()))
}

#[test]
fn missing_target_retains_the_nearest_immutable_existing_parent() {
    let record = check("/usr/lib/not-installed/libx.so", AuthorityKind::Object, &tree())
        .expect("immutable negative source");
    assert!(!record.present);
    assert_eq!(record.target, "/usr/lib/not-installed/libx.so");
    assert_eq!(record.nodes.last().expect("nearest existing parent").path, "/usr/lib");
}

#[test]
fn missing_cache_target_under_another_user_or_writable_parent_refuses() {
    for (uid, mode) in [(1001, 0o755), (0, 0o777), (0, 0o775)] {
        let mut nodes = tree();
        let mut parent = node("/usr/lib/cache-source", AuthorityKind::Directory);
        parent.uid = uid;
        parent.mode = mode;
        nodes.insert(parent.path.clone(), parent);
        assert!(check("/usr/lib/cache-source/libx.so", AuthorityKind::Object, &nodes).is_err());
    }
}

#[test]
fn unselected_hwcaps_directory_and_existing_leaf_authority_are_checked() {
    let mut nodes = tree();
    for path in ["/usr/lib/glibc-hwcaps", "/usr/lib/glibc-hwcaps/x86-64-v3"] {
        nodes.insert(path.into(), node(path, AuthorityKind::Directory));
    }
    nodes.get_mut("/usr/lib/glibc-hwcaps/x86-64-v3").expect("cap directory").mode = 0o775;
    assert!(check("/usr/lib/glibc-hwcaps/x86-64-v3", AuthorityKind::Directory, &nodes).is_err());
    nodes.get_mut("/usr/lib/glibc-hwcaps/x86-64-v3").expect("cap directory").mode = 0o755;
    let mut leaf = node("/usr/lib/glibc-hwcaps/x86-64-v3/libx.so", AuthorityKind::Object);
    leaf.uid = 1001;
    nodes.insert(leaf.path.clone(), leaf);
    assert!(
        check("/usr/lib/glibc-hwcaps/x86-64-v3/libx.so", AuthorityKind::Object, &nodes).is_err()
    );
}

#[test]
fn symlink_aliases_bind_both_the_link_and_canonical_target_chains() {
    let mut nodes = tree();
    let mut alias = node("/lib", AuthorityKind::Symlink);
    alias.link = Some("usr/lib".into());
    alias.mode = 0o777;
    nodes.insert(alias.path.clone(), alias);
    nodes.insert("/usr/lib/libx.so".into(), node("/usr/lib/libx.so", AuthorityKind::Object));
    let record =
        check("/lib/libx.so", AuthorityKind::Object, &nodes).expect("root-owned system alias");
    assert!(record.present);
    assert_eq!(record.target, "/usr/lib/libx.so");
    assert!(record.nodes.iter().any(|node| node.path == "/lib"));
    nodes.get_mut("/lib").expect("alias").uid = 1001;
    assert!(check("/lib/libx.so", AuthorityKind::Object, &nodes).is_err());
}

#[test]
fn dangling_symlink_target_requires_its_actual_nearest_parent_authority() {
    let mut nodes = tree();
    let mut alias = node("/usr/lib/libx.so", AuthorityKind::Symlink);
    alias.link = Some("/other/missing/libx.so".into());
    nodes.insert(alias.path.clone(), alias);
    let mut other = node("/other", AuthorityKind::Directory);
    other.uid = 1001;
    nodes.insert(other.path.clone(), other);
    assert!(check("/usr/lib/libx.so", AuthorityKind::Object, &nodes).is_err());
    nodes.get_mut("/other").expect("other parent").uid = 0;
    let record = check("/usr/lib/libx.so", AuthorityKind::Object, &nodes)
        .expect("root-protected missing symlink target");
    assert!(!record.present);
    assert_eq!(record.target, "/other/missing/libx.so");
}

#[test]
fn parent_traversal_waits_for_preceding_symlinks_before_resolving() {
    let mut nodes = tree();
    nodes.insert("/usr/alternate".into(), node("/usr/alternate", AuthorityKind::Directory));
    nodes.insert("/usr/alternate/sub".into(), node("/usr/alternate/sub", AuthorityKind::Directory));
    let mut a = node("/usr/lib/a", AuthorityKind::Symlink);
    a.link = Some("/usr/alternate/sub".into());
    let mut b = node("/usr/lib/b", AuthorityKind::Symlink);
    b.link = Some("a/../libx.so".into());
    nodes.insert(a.path.clone(), a);
    nodes.insert(b.path.clone(), b);
    nodes.insert(
        "/usr/alternate/libx.so".into(),
        node("/usr/alternate/libx.so", AuthorityKind::Object),
    );
    let record = check("/usr/lib/b", AuthorityKind::Object, &nodes)
        .expect("kernel-order symlink/parent semantics");
    assert_eq!(record.target, "/usr/alternate/libx.so");
}

#[test]
fn symlink_cycles_role_conflicts_and_observation_changes_refuse() {
    let mut nodes = tree();
    let mut link = node("/usr/lib/loop", AuthorityKind::Symlink);
    link.link = Some("loop".into());
    nodes.insert(link.path.clone(), link);
    assert!(check("/usr/lib/loop", AuthorityKind::Object, &nodes).is_err());
    assert!(check("/usr/lib", AuthorityKind::Object, &nodes).is_err());
    let mut calls = 0;
    assert!(
        resolve("/usr/lib/loop", AuthorityKind::Object, &mut |path| {
            let mut result = nodes.get(path.to_str().expect("test path")).cloned();
            if path == Path::new("/") {
                calls += 1;
                if calls > 1 {
                    result.as_mut().expect("root").inode = 2;
                }
            }
            Ok(result)
        })
        .is_err()
    );
}
