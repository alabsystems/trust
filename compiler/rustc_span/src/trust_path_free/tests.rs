use super::*;
use crate::source_map::FilePathMapping;
use crate::{Hash64, RemapPathScopeComponents};

// Takes a unix-style path and returns a platform specific path.
fn path(p: &str) -> PathBuf {
    #[cfg(not(windows))]
    {
        p.into()
    }
    #[cfg(windows)]
    {
        let mut path = p.replace('/', "\\");
        if let Some(rest) = path.strip_prefix('\\') {
            path = ["X:\\", rest].concat();
        }
        path.into()
    }
}

fn rules(rules: &[(&str, &str)], scopes: RemapPathScopeComponents) -> FilePathMapping {
    FilePathMapping::new(rules.iter().map(|(from, to)| (path(from), path(to))).collect(), scopes)
}

/// The session's name of `file`, resolved against the working directory `/work`, and the
/// form `encode_source_map` writes into metadata.
fn session_and_exported(mapping: &FilePathMapping, file: &str) -> (RealFileName, RealFileName) {
    let working_directory = mapping.to_real_filename(&RealFileName::empty(), path("/work"));
    let session = mapping.to_real_filename(&working_directory, path(file));
    let mut exported = session.clone();
    exported.update_for_crate_metadata();
    (session, exported)
}

/// Nothing a test's rule writes is on the host: `/virtual`, `/crates`, `/work`.
fn off_host(_: &Path) -> bool {
    false
}

fn judge(mapping: &FilePathMapping, file: &str) -> Option<(HostPathOrigin, PathBuf)> {
    let (session, exported) = session_and_exported(mapping, file);
    session.trust_unrewritten_host_path(&exported, &off_host)
}

#[test]
fn a_relative_name_under_a_remapped_working_directory_is_path_free() {
    let mapping = rules(&[("/work", "/virtual")], RemapPathScopeComponents::all());
    assert_eq!(judge(&mapping, "src/lib.rs"), None);
    // The remap to an empty or relative prefix (what trim-paths passes) is path-free too.
    let mapping = mapping_to_dot();
    assert_eq!(judge(&mapping, "src/lib.rs"), None);
}

fn mapping_to_dot() -> FilePathMapping {
    rules(&[("/work", ".")], RemapPathScopeComponents::all())
}

#[test]
fn a_relative_name_under_an_unremapped_working_directory_names_it() {
    // Negative control for the case above: drop the rule and the working directory,
    // which every field of the exported name carries, is refused.
    let mapping = rules(&[], RemapPathScopeComponents::all());
    assert_eq!(
        judge(&mapping, "src/lib.rs"),
        Some((HostPathOrigin::WorkingDirectory, path("/work")))
    );
    // A rule for some other prefix does not help.
    let mapping = rules(&[("/elsewhere", "/virtual")], RemapPathScopeComponents::all());
    assert_eq!(
        judge(&mapping, "src/lib.rs"),
        Some((HostPathOrigin::WorkingDirectory, path("/work")))
    );
}

#[test]
fn an_absolute_name_is_path_free_only_when_its_rule_and_the_working_directory_s_rule_apply() {
    let both =
        rules(&[("/work", "/virtual"), ("/registry", "/crates")], RemapPathScopeComponents::all());
    assert_eq!(judge(&both, "/registry/dep/src/lib.rs"), None);

    // The file's own prefix is remapped but the working directory, which the exported
    // name also carries, is not.
    let file_only = rules(&[("/registry", "/crates")], RemapPathScopeComponents::all());
    assert_eq!(
        judge(&file_only, "/registry/dep/src/lib.rs"),
        Some((HostPathOrigin::WorkingDirectory, path("/work")))
    );

    // No rule at all: the name itself is named first.
    let none = rules(&[], RemapPathScopeComponents::all());
    assert_eq!(
        judge(&none, "/registry/dep/src/lib.rs"),
        Some((HostPathOrigin::SourceFileName, path("/registry/dep/src/lib.rs")))
    );
}

#[test]
fn remap_scopes_are_not_evidence_of_a_rewrite() {
    // The working directory matches a rule, the file matches none. `to_real_filename`
    // still marks the file fully remapped, so a check on scopes would pass it; the
    // exported name nevertheless carries `/quux/src/main.rs` as it is.
    let mapping = rules(&[("/work", "/virtual")], RemapPathScopeComponents::all());
    let (session, exported) = session_and_exported(&mapping, "/quux/src/main.rs");
    assert!(exported.was_fully_remapped(), "the premise of this negative control moved");
    assert_eq!(exported.local, None);
    assert_eq!(
        session.trust_unrewritten_host_path(&exported, &off_host),
        Some((HostPathOrigin::SourceFileName, path("/quux/src/main.rs")))
    );
}

#[test]
fn a_partially_scoped_remap_keeps_the_host_form_in_metadata() {
    // Under `--remap-path-scope=macro` the exported name keeps its local part.
    let partial = rules(&[("/work", "/virtual")], RemapPathScopeComponents::MACRO);
    let (session, exported) = session_and_exported(&partial, "/work/src/lib.rs");
    assert!(exported.local.is_some());
    assert_eq!(
        session.trust_unrewritten_host_path(&exported, &off_host),
        Some((HostPathOrigin::SourceFileName, path("/work/src/lib.rs")))
    );
    // Control: the same rule with every scope exports no local part and passes.
    let full = rules(&[("/work", "/virtual")], RemapPathScopeComponents::all());
    assert_eq!(judge(&full, "/work/src/lib.rs"), None);
}

#[test]
fn a_rule_that_maps_a_prefix_to_itself_rewrites_nothing() {
    let identity = rules(&[("/work", "/work")], RemapPathScopeComponents::all());
    assert_eq!(
        judge(&identity, "/work/src/lib.rs"),
        Some((HostPathOrigin::SourceFileName, path("/work/src/lib.rs")))
    );
}

#[test]
fn a_name_without_a_local_form_cannot_show_its_rewrite() {
    // What a proc-macro crate re-exports from another crate's metadata.
    let imported = RealFileName::from_virtual_path(&path("/rustc/0123/library/core/src/lib.rs"));
    assert_eq!(
        imported.trust_unrewritten_host_path(&imported, &off_host),
        Some((HostPathOrigin::SourceFileName, path("/rustc/0123/library/core/src/lib.rs")))
    );
    let relative = RealFileName::from_virtual_path(&path("library/core/src/lib.rs"));
    assert_eq!(relative.trust_unrewritten_host_path(&relative, &off_host), None);
}

#[test]
fn file_name_variants() {
    let mapping = rules(&[], RemapPathScopeComponents::all());
    let (session, exported) = session_and_exported(&mapping, "/work/src/lib.rs");
    let refused = Some((HostPathOrigin::SourceFileName, path("/work/src/lib.rs")));
    assert_eq!(
        FileName::Real(session.clone())
            .trust_unrewritten_host_path(&FileName::Real(exported), &off_host),
        refused
    );
    // A doctest name is written as it is, local part and all.
    let doctest = FileName::DocTest(session.clone(), 3);
    assert_eq!(doctest.trust_unrewritten_host_path(&doctest, &off_host), refused);

    let absolute = FileName::Custom(path("/work/generated.rs").to_string_lossy().into_owned());
    assert_eq!(
        absolute.trust_unrewritten_host_path(&absolute, &off_host),
        Some((HostPathOrigin::SourceFileName, path("/work/generated.rs")))
    );
    let relative = FileName::Custom("generated.rs".into());
    assert_eq!(relative.trust_unrewritten_host_path(&relative, &off_host), None);
    let anon = FileName::Anon(Hash64::new(7));
    assert_eq!(anon.trust_unrewritten_host_path(&anon, &off_host), None);

    // Mismatched variants prove no rewrite.
    let remapped = mapping_to_dot();
    let (_, exported) = session_and_exported(&remapped, "/work/src/lib.rs");
    let custom = FileName::Custom("x".into());
    assert_eq!(custom.trust_unrewritten_host_path(&FileName::Real(exported), &off_host), None);
    let none = rules(&[], RemapPathScopeComponents::all());
    let (_, exported) = session_and_exported(&none, "src/lib.rs");
    assert_eq!(
        custom.trust_unrewritten_host_path(&FileName::Real(exported), &off_host),
        Some((HostPathOrigin::WorkingDirectory, path("/work")))
    );
}

#[test]
fn a_rule_that_rewrites_into_another_host_path_rewrites_nothing() {
    // `/work=/home`: the name changed, but `/home` is a directory of this host, so the
    // value still names it (the user and checkout layout stay readable).
    let on_host = |p: &Path| p == path("/home");
    let into_host = rules(&[("/work", "/home")], RemapPathScopeComponents::all());
    let (session, exported) = session_and_exported(&into_host, "/work/src/lib.rs");
    assert_eq!(
        session.trust_unrewritten_host_path(&exported, &on_host),
        Some((HostPathOrigin::SourceFileName, path("/home/src/lib.rs")))
    );
    // `/work=/work/../work`: a different spelling of the same host path.
    let on_host = |p: &Path| p == path("/work");
    let respelled = rules(&[("/work", "/work/../work")], RemapPathScopeComponents::all());
    let (session, exported) = session_and_exported(&respelled, "/work/src/lib.rs");
    assert!(session.trust_unrewritten_host_path(&exported, &on_host).is_some());
    // Control: the same rewrite into a root this host does not have passes.
    let (session, exported) = session_and_exported(&into_host, "/work/src/lib.rs");
    assert_eq!(session.trust_unrewritten_host_path(&exported, &off_host), None);
    // A rule into the bare root writes a working directory with no host directory in it,
    // and a name under a root this host does not have.
    let only_root = |p: &Path| p.parent().is_none();
    let to_root = rules(&[("/work", "/")], RemapPathScopeComponents::all());
    let (session, exported) = session_and_exported(&to_root, "src/lib.rs");
    assert_eq!(session.trust_unrewritten_host_path(&exported, &only_root), None);
}

fn prefixes(candidates: &[&str]) -> HostPrefixes {
    HostPrefixes::new(&path("/work"), candidates.iter().map(|c| path(c)))
}

fn sep() -> char {
    std::path::MAIN_SEPARATOR
}

#[test]
fn host_prefixes_match_whole_directories() {
    let hosts = prefixes(&["/work", "/home/someone", "target"]);
    let text = |p: &str| path(p).to_string_lossy().into_owned();
    // A relative candidate is made absolute against the working directory.
    let bytes = format!("x{}\u{0}{}\"", text("/work/target/out"), text("/home/someone"));
    let found = hosts.occurrences(bytes.as_bytes());
    assert_eq!(found.len(), 2, "{found:?}");
    assert_eq!(found[0].offset, 1);
    // The most specific prefix names the occurrence, and it is counted once.
    assert_eq!(found[0].prefix, text("/work/target").into_bytes());
    assert_eq!(found[0].path, text("/work/target/out").into_bytes());
    assert_eq!(found[1].prefix, text("/home/someone").into_bytes());
    // Negative controls: a sibling directory sharing the spelling is a different path.
    assert!(hosts.occurrences(text("/work2/src").as_bytes()).is_empty());
    assert!(hosts.occurrences(text("/home/someone-else").as_bytes()).is_empty());
    assert!(hosts.occurrences(format!("{}{}", text("/work"), sep()).as_bytes()).len() == 1);
    // A root names every path, a virtual one included, and is never a prefix.
    let roots = prefixes(&["/"]);
    assert!(roots.is_empty());
    assert!(roots.occurrences(text("/virtual/src/lib.rs").as_bytes()).is_empty());
}

#[test]
fn env_values() {
    let none = HostPrefixes::default();
    let refused = |v: &str| host_path_in_value(v, &none);
    let checkout = path("<home>/checkout").to_string_lossy().into_owned();
    assert_eq!(refused(&checkout).as_deref(), Some(checkout.as_str()));
    assert_eq!(
        refused(&path("/").to_string_lossy()).as_deref(),
        Some(&*path("/").to_string_lossy())
    );
    // A path anywhere in the value, not only a value that is one.
    assert_eq!(refused("--sysroot=<home>/w/sysroot").as_deref(), Some("<home>/w/sysroot"));
    assert_eq!(refused("file://<home>/w/x").as_deref(), Some("<home>/w/x"));
    assert_eq!(refused(" <home>/w").as_deref(), Some("<home>/w"));
    assert_eq!(refused("/usr/bin:/bin").as_deref(), Some("/usr/bin"));
    assert_eq!(refused("/c<home>").as_deref(), Some("/c<home>"));
    assert_eq!(refused("dir=C:\\Users\\a").as_deref(), Some("C:\\Users\\a"));
    assert_eq!(refused("x\\\\server\\share").as_deref(), Some("\\\\server\\share"));
    // Negative controls: no path in them.
    for value in
        ["relative/dir", "1.2.3", "", "https://example.com/a/b", "and/or", "a / b", "x86_64"]
    {
        assert_eq!(refused(value), None, "{value}");
    }
    // A host prefix is found wherever it is, even inside a token.
    let hosts = prefixes(&["/work"]);
    let inside = format!("-L{}", path("/work/lib").to_string_lossy());
    assert_eq!(refused(&inside), None);
    assert_eq!(
        host_path_in_value(&inside, &hosts).as_deref(),
        Some(&*path("/work/lib").to_string_lossy())
    );
}

#[test]
fn record_is_one_json_line() {
    assert_eq!(
        record("working-directory", &[], &RecordPath::from_bytes(b"/work"), 0),
        r#"trust-path-free-v1 {"origin":"working-directory","path":"/work","further":0}"#
    );
    assert_eq!(
        record(
            "env",
            &[("var", "CARGO_MANIFEST_DIR")],
            &RecordPath::from_bytes("/a \"b\"\\c\n\u{1}".as_bytes()),
            2
        ),
        "trust-path-free-v1 {\"origin\":\"env\",\"var\":\"CARGO_MANIFEST_DIR\",\
         \"path\":\"/a \\\"b\\\"\\\\c\\n\\u0001\",\"further\":2}"
    );
    // A path that is not UTF-8 keeps its bytes.
    assert_eq!(
        record("source-file", &[("file", "lib.rs")], &RecordPath::from_bytes(b"/w/\xff"), 0),
        "trust-path-free-v1 {\"origin\":\"source-file\",\"file\":\"lib.rs\",\
         \"path\":\"/w/\u{fffd}\",\"path_bytes\":\"2f772fff\",\"further\":0}"
    );
}
