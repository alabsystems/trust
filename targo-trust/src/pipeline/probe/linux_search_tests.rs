use super::*;

const INTERPRETER: &str = "/lib64/ld-linux-x86-64.so.2";

fn diagnostic() -> String {
    concat!(
        "dl_hwcaps_subdirs=\"x86-64-v4:x86-64-v3:x86-64-v2\"\n",
        "dl_hwcaps_subdirs_active=0x3\npath.prefix=\"/usr\"\n",
        "path.rtld=\"/lib64/ld-linux-x86-64.so.2\"\npath.sysconfdir=\"/etc\"\n",
        "path.system_dirs[0x0]=\"/lib/x86_64-linux-gnu/\"\n",
        "path.system_dirs[0x1]=\"/usr/lib/\"\nversion.version=\"2.39\"\n",
        "auxv[0x0].a_val=0x1234\n"
    )
    .to_owned()
}
fn parse(output: &str) -> Result<LoaderSearch, String> {
    diagnostics(output, INTERPRETER)
}

#[test]
fn diagnostics_bind_actual_defaults_and_all_hwcaps_even_when_inactive() {
    let result = parse(&diagnostic()).expect("known GNU search semantics");
    assert_eq!(result.system_directories, ["/lib/x86_64-linux-gnu", "/usr/lib"]);
    assert_eq!(result.hwcaps_subdirectories.len(), 3);
    let requests = requests(&result, INTERPRETER, &[], &[], &["libx.so".into()])
        .expect("complete lookup inventory");
    assert!(
        requests
            .contains(&("/usr/lib/glibc-hwcaps/x86-64-v4/libx.so".into(), AuthorityKind::Object))
    );
    assert!(requests.contains(&("/lib/x86_64-linux-gnu/libx.so".into(), AuthorityKind::Object)));
}

#[test]
fn diagnostics_refuse_unknown_semantics_sparse_or_duplicate_sources() {
    for (old, new) in [
        ("2.39", "2.40"),
        ("/etc", "/custom/etc"),
        ("system_dirs[0x1]", "system_dirs[0x2]"),
        ("x86-64-v4:x86-64-v3", "../escape:x86-64-v3"),
        ("0x3\npath.prefix", "0xff\npath.prefix"),
        ("/usr/lib/", "/home/user/lib/"),
    ] {
        assert!(parse(&diagnostic().replace(old, new)).is_err(), "accepted replacement {new}");
    }
    let mut repeated = diagnostic();
    repeated.push_str("version.version=\"2.39\"\n");
    assert!(parse(&repeated).is_err());
    assert!(parse(&diagnostic().replace("path.prefix", "path.custom_search")).is_err());
}

#[test]
fn diagnostics_require_interpreter_and_complete_unescaped_search_fields() {
    assert!(diagnostics(&diagnostic(), "/lib/foreign.so").is_err());
    assert!(parse(&diagnostic().replace("dl_hwcaps_subdirs_active=0x3\n", "")).is_err());
    assert!(parse(&diagnostic().replace("/usr/lib/", "/usr/\\154ib/")).is_err());
}

#[test]
fn lookup_plan_keeps_foreign_cached_paths_for_authority_refusal_not_filtering() {
    let search = parse(&diagnostic()).expect("loader");
    let entry = CacheEntry {
        name: "libx.so".into(),
        path: "/tmp/other-user/libx.so".into(),
        flags: 0,
        hwcap: 0,
    };
    let result = requests(&search, INTERPRETER, &[entry], &[], &[])
        .expect("enumerate before validating authority");
    assert!(result.contains(&("/tmp/other-user/libx.so".into(), AuthorityKind::Object)));
    assert!(result.contains(&("/etc/ld.so.preload".into(), AuthorityKind::Object)));
}

#[test]
fn directory_census_must_be_ordered_unique_and_within_loader_search_roots() {
    let search = parse(&diagnostic()).expect("loader");
    let entry = SearchDirectoryEntry {
        directory: "/usr/lib".into(),
        name: "unrelated.so".into(),
        kind: AuthorityKind::Object,
    };
    let result = requests(&search, INTERPRETER, &[], &[entry.clone()], &[])
        .expect("all eligible leaves retained");
    assert!(result.contains(&("/usr/lib/unrelated.so".into(), AuthorityKind::Object)));
    assert!(requests(&search, INTERPRETER, &[], &[entry.clone(), entry.clone()], &[]).is_err());
    let mut foreign = entry;
    foreign.directory = "/home/user".into();
    assert!(requests(&search, INTERPRETER, &[], &[foreign], &[]).is_err());
}

#[test]
fn lookup_plan_protects_the_original_interpreter_outside_default_search_roots() {
    let search = parse(&diagnostic()).expect("known GNU loader");
    assert!(!directories(&search).expect("search roots").iter().any(|path| path == "/lib64"));
    let result =
        requests(&search, INTERPRETER, &[], &[], &[]).expect("no cached or requested DSOs");
    assert!(result.contains(&(INTERPRETER.into(), AuthorityKind::Object)));
    assert!(requests(&search, "/usr/local/foreign-loader", &[], &[], &[]).is_err());
}
