use std::fs;
use std::path::{Path, PathBuf};
use std::time::{Duration, SystemTime};

use tempfile::TempDir;

use super::*;
use crate::utils::exec::ExecutionContext;
use crate::utils::tests::git::{GitCtx, git_test};

const HOST: &str = "aarch64-apple-darwin";

fn inputs<'a>(identity: &'a str, env: &[(&str, &str)]) -> KeyInputs<'a> {
    KeyInputs {
        host: HOST,
        identity,
        stage0: "trust-stage0-extraction-v1:abc",
        tools: vec![("{src}/build/aarch64-apple-darwin/stage0/bin/trustc".into(), "11".into())],
        env: env.iter().map(|(name, value)| (name.to_string(), value.to_string())).collect(),
        flags: vec![("set".into(), "[]".into())],
    }
}

#[test]
fn a_key_is_its_inputs_and_a_refusal_names_the_input_that_differs() {
    let (a, b) = ("a".repeat(40), "b".repeat(40));
    let own = Key::new(&inputs(&a, &[("PATH", "/usr/bin")]));
    let same = Key::new(&inputs(&a, &[("PATH", "/usr/bin")]));
    assert_eq!(own, same);
    assert_eq!(own.digest(), same.digest());
    assert!(differing_fields(&own, &same).is_empty());

    let edited = Key::new(&inputs(&b, &[("PATH", "/usr/bin")]));
    assert_ne!(own.digest(), edited.digest());
    assert_eq!(differing_fields(&own, &edited), ["identity"]);

    let path = Key::new(&inputs(&a, &[("PATH", "/opt/bin")]));
    assert_eq!(differing_fields(&own, &path), ["env PATH"]);
    let more = Key::new(&inputs(&a, &[("PATH", "/usr/bin"), ("RUSTFLAGS", "-Cdebuginfo=0")]));
    assert_eq!(differing_fields(&own, &more), ["env RUSTFLAGS"]);

    let mut tool = inputs(&a, &[("PATH", "/usr/bin")]);
    tool.tools[0].1 = "12".into();
    let tool = Key::new(&tool);
    assert_eq!(
        differing_fields(&own, &tool),
        ["tool \"{src}/build/aarch64-apple-darwin/stage0/bin/trustc\""]
    );
    let mut flags = inputs(&a, &[("PATH", "/usr/bin")]);
    flags.flags[0].1 = "[\"rust.debug=true\"]".into();
    assert_eq!(differing_fields(&own, &Key::new(&flags)), ["flag set"]);
    let mut stage0 = inputs(&a, &[("PATH", "/usr/bin")]);
    stage0.stage0 = "trust-stage0-extraction-v1:def";
    assert_eq!(differing_fields(&own, &Key::new(&stage0)), ["stage0"]);
}

fn head(ctx: &GitCtx, path: &Path) -> crate::utils::channel::Info {
    let sha = ctx.run_git(&["-C", path.to_str().unwrap(), "rev-parse", "HEAD"]);
    crate::utils::channel::Info {
        short_sha: sha[..9].to_owned(),
        sha,
        commit_date: "2026-11-05".to_owned(),
    }
}

/// The identity a tree's key carries, as a build there names it: its own configuration
/// file, naming paths in its own tree, digested with that tree's root as a token.
fn identity_of(ctx: &GitCtx, tree: &Path) -> String {
    let config = tree.join("bootstrap.toml");
    let digest = trust_source_identity::config_digest(Some(&config), tree);
    let exec = ExecutionContext::new(0, false);
    trust_source_identity::of_sources(&exec, tree, &digest, &head(ctx, tree))
        .expect("git names the sources")
        .info
        .sha
}

/// The acceptance's two cases on git's own worktrees: a fresh worktree at the donor's
/// commit, configured alike in its own tree, has the donor's key; one compiler source
/// edited there gives it another key, and the refusal names the source identity.
#[test]
fn a_fresh_worktree_matches_and_one_edited_compiler_file_is_refused() {
    git_test(|ctx| {
        ctx.write("compiler/rustc/src/main.rs", "fn main() {}");
        ctx.write("library/core/src/lib.rs", "#![no_core]");
        ctx.write(".gitignore", "/bootstrap.toml\n/build\n");
        ctx.commit();
        let donor = ctx.get_path().canonicalize().unwrap();
        let recipient = donor
            .with_file_name(format!("{}-recipient", donor.file_name().unwrap().to_str().unwrap()));
        ctx.run_git(&["worktree", "add", "-q", "--detach", recipient.to_str().unwrap()]);
        for tree in [&donor, &recipient] {
            fs::write(
                tree.join("bootstrap.toml"),
                format!("[build]\nbuild-dir = \"{}/build\"\n", tree.display()),
            )
            .unwrap();
        }
        let key = |tree: &Path| {
            Key::new(&inputs(&identity_of(ctx, tree), &[("RUSTFLAGS", "-L{src}/build")]))
        };
        assert_eq!(key(&donor), key(&recipient), "a fresh worktree has the donor's key");

        fs::write(recipient.join("compiler/rustc/src/main.rs"), "fn main() { () }").unwrap();
        let (own, theirs) = (key(&recipient), key(&donor));
        assert_ne!(own.digest(), theirs.digest());
        assert_eq!(differing_fields(&own, &theirs), ["identity"]);

        fs::remove_dir_all(&recipient).unwrap();
        ctx.run_git(&["worktree", "prune"]);
    });
}

#[test]
fn the_keyed_environment_names_each_root_by_its_token_and_leaves_the_invocation_out() {
    let roots = Roots { src: "/w/tree".into(), git_dir: Some("/g/worktrees/tree".into()) };
    let tokens = root_tokens(&roots);
    let vars = [
        ("RUSTFLAGS", "-L/w/tree/build/lib -L/w/tree2/lib --cfg=x{y}"),
        ("PATH", "/usr/bin:/w/tree/bin"),
        ("CARGO_HOME", "/g/worktrees/tree/cargo"),
        ("CC", "clang"),
        ("CFLAGS", "{src}"),
        ("TRUST_BUILD_LOCK_TOKEN", "x"),
        ("TRUST_NATIVE_REPO_PARENT_PID", "1"),
        ("RUST_BACKTRACE", "1"),
        ("CARGO_LOG", "targo_core::compiler::fingerprint=info"),
        ("CARGO_LOG_PROFILE", "1"),
        ("HOME", "<home>"),
        ("TARGET_CC", "clang"),
        ("TERM", "xterm"),
    ];
    let env = key_env(vars.iter().map(|(n, v)| ((*n).into(), (*v).into())), &tokens);
    let expected: Vec<(String, String)> = [
        ("CARGO_HOME", "{git}/cargo"),
        // A trace file is something the run writes; a log filter is not.
        ("CARGO_LOG_PROFILE", "1"),
        ("CC", "clang"),
        // A value that spells a token itself never reads as one.
        ("CFLAGS", "{{src}}"),
        ("HOME", "<home>"),
        ("PATH", "/usr/bin:{src}/bin"),
        ("RUSTFLAGS", "-L{src}/build/lib -L/w/tree2/lib --cfg=x{{y}}"),
        ("TARGET_CC", "clang"),
    ]
    .into_iter()
    .map(|(name, value)| (name.to_owned(), value.to_owned()))
    .collect();
    assert_eq!(env, expected);
    assert!(keyed_env("CARGO_TARGET_DIR") && keyed_env("SDKROOT") && keyed_env("AR"));
    assert!(keyed_env("HOST_CFLAGS") && keyed_env("OPENSSL_DIR") && keyed_env("XDG_CONFIG_HOME"));
    assert!(!keyed_env("ARCH") && !keyed_env("USER") && !keyed_env("CARGO_LOG"));
    assert!(keyed_env("CARGO_LOG_PROFILE") && keyed_env("RUSTC_LOG"));

    // Two roots never share a token: the source tree and a git directory outside it.
    assert_eq!(key_value(b"/w/tree/x:/g/worktrees/tree/y", &tokens), "{src}/x:{git}/y");
    let inside = Roots { src: "/m".into(), git_dir: Some("/m/.git".into()) };
    assert_eq!(key_value(b"/m/.git/x", &root_tokens(&inside)), "{src}/.git/x");

    // A value that is not UTF-8 is written by its bytes, which no text spells, and so is
    // a name: neither collides with a value or name that spells the same characters.
    assert_eq!(
        key_value(b"/w/tree/\xff", &tokens),
        format!("{{bytes:{}}}", hex_encode(b"\0src\0/\xff"))
    );
    assert_ne!(key_value(b"\xff", &tokens), key_value(b"[255]", &tokens));
    assert_ne!(key_value(b"\xff", &tokens), key_value(b"{bytes:ff}", &tokens));
    #[cfg(unix)]
    {
        use std::os::unix::ffi::OsStringExt;
        let odd = std::ffi::OsString::from_vec(b"RUSTFLAGS\xff".to_vec());
        let env =
            key_env([(odd, "x".into()), ("RUSTFLAGS".into(), "x".into())].into_iter(), &tokens);
        assert_eq!(env.len(), 2, "{env:?}");
        assert_ne!(env[0].0, env[1].0);
    }
    // The stage-0 stamp is written escaped: a line break in it cannot add a field.
    let identity = "a".repeat(40);
    let mut stamped = inputs(&identity, &[]);
    stamped.stage0 = "s\ntool x y";
    assert!(Key::new(&stamped).record.contains("stage0 \"s\\ntool x y\"\n"));
}

#[test]
fn the_flags_that_shape_a_build_are_keyed_and_how_it_runs_is_not() {
    use crate::core::config::flags::Flags;
    let tokens = root_tokens(&Roots { src: "/w/tree".into(), git_dir: None });
    let flags = |args: &[&str]| {
        let args: Vec<String> = args.iter().map(|arg| (*arg).to_owned()).collect();
        key_flags(&Flags::parse(&args), &tokens)
    };
    let own = flags(&["build", "--stage", "1", "--set", "b=1", "--set", "a=1", "-j", "8"]);
    let config = own.iter().find(|(name, _)| name == "config").unwrap();
    assert_eq!(config.1, "None");
    assert_eq!(
        own,
        flags(&["build", "-j", "2", "--set", "a=1", "--set", "b=1", "-v", "compiler"]),
        "the paths, jobs, verbosity and the order of `--set` change nothing"
    );
    let key = |flags: Vec<(String, String)>| {
        let mut inputs = inputs("a", &[]);
        inputs.flags = flags;
        Key::new(&inputs)
    };
    let set = flags(&["build", "--set", "a=2", "--set", "b=1"]);
    assert_eq!(differing_fields(&key(own.clone()), &key(set)), ["flag set"]);
    let config = flags(&["build", "--set", "a=1", "--set", "b=1", "--config", "/w/tree/b.toml"]);
    assert!(config.contains(&("config".to_owned(), "Some(\"{src}/b.toml\")".to_owned())));
    assert_eq!(differing_fields(&key(own.clone()), &key(config)), ["flag config"]);
    let target =
        flags(&["build", "--set", "a=1", "--set", "b=1", "--target", "x86_64-apple-darwin"]);
    assert_eq!(differing_fields(&key(own), &key(target)), ["flag target"]);
}

fn record(src: &Path) -> Record {
    Record {
        key: Key::new(&inputs("a".repeat(40).as_str(), &[])),
        roots: Roots { src: src.to_owned(), git_dir: Some(src.join(".git")) },
    }
}

/// Only x.py's own stage-0 extraction is keyed, by its stamp: a `rustc` or `cargo`
/// configured elsewhere makes the tree neither a donor nor a recipient.
#[cfg(unix)]
#[test]
fn only_the_extracted_stage0_is_keyed() {
    let dir = TempDir::new().unwrap();
    let base = dir.path().canonicalize().unwrap();
    let host_dir = base.join(HOST);
    let bin = host_dir.join("stage0/bin");
    fs::create_dir_all(&bin).unwrap();
    let (rustc, cargo) = (bin.join("trustc"), bin.join("cargo"));
    fs::write(&rustc, "").unwrap();
    fs::write(&cargo, "").unwrap();
    assert!(!stage0_is_extracted(&host_dir, [&rustc, &cargo]), "no stamp: not x.py's");
    fs::write(host_dir.join("stage0/.rustc-stamp"), "abc").unwrap();
    assert!(stage0_is_extracted(&host_dir, [&rustc, &cargo]));
    let link = base.join("rustc-link");
    std::os::unix::fs::symlink(&rustc, &link).unwrap();
    assert!(stage0_is_extracted(&host_dir, [&link, &cargo]), "the extraction's own rustc");
    let elsewhere = base.join("elsewhere");
    fs::write(&elsewhere, "").unwrap();
    assert!(!stage0_is_extracted(&host_dir, [&elsewhere, &cargo]));
    assert!(!stage0_is_extracted(&host_dir, [&rustc, &elsewhere]));
}

#[test]
fn a_record_reads_back_and_a_damaged_one_is_refused() {
    let record = record(Path::new("/w/donor"));
    let text = record.render();
    assert_eq!(Record::parse(&text), Ok(record.clone()));

    let tampered = text.replace("host aarch64-apple-darwin", "host x86_64-apple-darwin");
    assert!(Record::parse(&tampered).unwrap_err().contains("digest"));
    assert!(
        Record::parse(&text.replacen("trust-stage1-seed/v1", "trust-stage1-seed/v0", 1)).is_err()
    );
    assert!(Record::parse(&text.replace("root /w/donor", "root w/donor")).is_err());
    assert!(Record::parse(&text.replace("\n--\n", "\n")).is_err());
    let none = Record { roots: Roots { src: "/w/donor".into(), git_dir: None }, ..record };
    assert_eq!(Record::parse(&none.render()), Ok(none));
}

#[test]
fn worktrees_are_read_from_git_porcelain() {
    let porcelain = "worktree /a\nHEAD 1\nbranch refs/heads/main\n\nworktree /b c\nHEAD 2\n\
                     detached\n\nworktree /p\nbare\n";
    assert_eq!(worktrees(porcelain), [PathBuf::from("/a"), "/b c".into(), "/p".into()]);
}

fn old() -> SystemTime {
    SystemTime::UNIX_EPOCH + Duration::from_secs(1_600_000_000)
}

fn mtime(path: &Path) -> SystemTime {
    fs::symlink_metadata(path).unwrap().modified().unwrap()
}

/// What a carry compares with: cloned outputs from `newest`, and every fixture entry
/// written before now.
fn moments(newest: SystemTime) -> Moments<'static> {
    Moments {
        newest: stamp(newest),
        settled: stamp(SystemTime::now() + Duration::from_millis(1)),
        donor_times: &NO_TIMES,
    }
}

/// A donor that was never seeded.
static NO_TIMES: DonorTimes = DonorTimes(BTreeMap::new());

#[cfg(unix)]
fn entry_of(path: &Path, carried: SystemTime) -> TableEntry {
    use std::os::unix::fs::MetadataExt;
    let meta = fs::symlink_metadata(path).unwrap();
    TableEntry {
        dev: meta.dev(),
        ino: meta.ino(),
        size: meta.len(),
        mtime: (meta.mtime(), meta.mtime_nsec()),
        ctime: (meta.ctime(), meta.ctime_nsec()),
        carried: stamp(carried),
    }
}

/// An unchanged file reads to Targo as the donor's does, and the recipient's own time is
/// never moved back; a changed one, or one the donor no longer has, reads later than every
/// cloned output whatever its own time was.
#[cfg(unix)]
#[test]
fn an_unchanged_file_reads_as_the_donors_and_a_changed_one_reads_later() {
    let dir = TempDir::new().unwrap();
    let (donor, own) = (dir.path().join("donor"), dir.path().join("own"));
    fs::write(&donor, "fn f() {}").unwrap();
    fs::write(&own, "fn f() {}").unwrap();
    set_mtime(&donor, old(), true).unwrap();
    let newest = old() + Duration::from_secs(10);
    let checked_out = mtime(&own);
    assert_eq!(
        carry_time(&donor, &own, moments(newest)).unwrap(),
        Carried::Table(entry_of(&own, old()))
    );
    assert_eq!(mtime(&own), checked_out, "a time is never set back on the file");

    let earlier = old() - Duration::from_secs(100);
    set_mtime(&own, earlier, true).unwrap();
    assert_eq!(carry_time(&donor, &own, moments(newest)).unwrap(), Carried::Same);
    assert_eq!(mtime(&own), old(), "an older recipient time moves forward to the donor's");
    assert_eq!(carry_time(&donor, &own, moments(newest)).unwrap(), Carried::Same);

    // Other bytes of the same length, older than every cloned output (a checkout made
    // before the donor last built): it must read later, or Targo would keep the donor's
    // output for it.
    fs::write(&own, "fn g() {}").unwrap();
    set_mtime(&own, earlier, true).unwrap();
    assert_eq!(carry_time(&donor, &own, moments(newest)).unwrap(), Carried::Differs);
    assert!(mtime(&own) > newest, "a differing file reads later than every cloned output");
    let later = mtime(&own);
    assert_eq!(carry_time(&donor, &own, moments(newest)).unwrap(), Carried::Differs);
    assert_eq!(mtime(&own), later, "a time already later is kept");
    fs::write(&own, "fn g() { }\n").unwrap();
    assert_eq!(carry_time(&donor, &own, moments(newest)).unwrap(), Carried::Differs);

    set_mtime(&own, earlier, true).unwrap();
    fs::remove_file(&donor).unwrap();
    assert_eq!(carry_time(&donor, &own, moments(newest)).unwrap(), Carried::Differs);
    assert!(mtime(&own) > newest, "a file the donor no longer has reads later");
    fs::remove_file(&own).unwrap();
    assert_eq!(
        carry_time(&donor, &own, moments(newest)).unwrap(),
        Carried::Differs,
        "a missing file: Targo finds none either and rebuilds"
    );
}

/// A file whose status changed after the moment the seed counts as settled may still be
/// being written, and is never given an entry that could outlive that write.
#[cfg(unix)]
#[test]
fn a_file_still_being_written_is_never_given_the_donors_time() {
    let dir = TempDir::new().unwrap();
    let (donor, own) = (dir.path().join("donor"), dir.path().join("own"));
    fs::write(&donor, "x").unwrap();
    set_mtime(&donor, old(), true).unwrap();
    let settled = SystemTime::now() - Duration::from_secs(60);
    fs::write(&own, "x").unwrap();
    let moments = Moments { newest: stamp(old()), settled: stamp(settled), donor_times: &NO_TIMES };
    assert_eq!(carry_time(&donor, &own, moments).unwrap(), Carried::Differs);
}

#[cfg(unix)]
#[test]
fn links_compare_by_target_and_directories_by_their_entries() {
    let dir = TempDir::new().unwrap();
    let (donor, own) = (dir.path().join("donor"), dir.path().join("own"));
    for tree in [&donor, &own] {
        fs::create_dir_all(tree.join("d")).unwrap();
        fs::write(tree.join("d/a.rs"), "a").unwrap();
        std::os::unix::fs::symlink("a.rs", tree.join("d/l")).unwrap();
    }
    set_mtime(&donor.join("d/l"), old(), false).unwrap();
    set_mtime(&donor.join("d"), old(), false).unwrap();
    let newest = old() + Duration::from_secs(10);
    let link = own.join("d/l");
    assert_eq!(
        carry_time(&donor.join("d/l"), &link, moments(newest)).unwrap(),
        Carried::Table(entry_of(&link, old()))
    );
    assert_eq!(
        carry_time(&donor.join("d"), &own.join("d"), moments(newest)).unwrap(),
        Carried::Table(entry_of(&own.join("d"), old()))
    );

    fs::write(own.join("d/new.rs"), "").unwrap();
    let now = mtime(&own.join("d"));
    assert_eq!(
        carry_time(&donor.join("d"), &own.join("d"), moments(newest)).unwrap(),
        Carried::Differs
    );
    assert_eq!(mtime(&own.join("d")), now, "a directory with another entry keeps its later time");
    fs::remove_file(&link).unwrap();
    std::os::unix::fs::symlink("new.rs", &link).unwrap();
    assert_eq!(carry_time(&donor.join("d/l"), &link, moments(newest)).unwrap(), Carried::Differs);
    assert_eq!(
        carry_time(&donor.join("d/a.rs"), &own.join("d"), moments(newest)).unwrap(),
        Carried::Differs
    );
}

/// Targo takes the newest time under a watched directory, following links: every entry
/// under it is compared, and so is what a link in it names, outside it too.
#[cfg(unix)]
#[test]
fn a_watched_directory_compares_everything_targo_reads_under_it() {
    let dir = TempDir::new().unwrap();
    // Canonical, as a seed's roots are.
    let base = dir.path().canonicalize().unwrap();
    let (donor, own) = (base.join("donor"), base.join("own"));
    for tree in [&donor, &own] {
        fs::create_dir_all(tree.join("w/sub")).unwrap();
        fs::write(tree.join("w/sub/x.rs"), "x").unwrap();
        fs::write(tree.join("w/y.rs"), "y").unwrap();
        fs::write(tree.join("outside.rs"), "o").unwrap();
        std::os::unix::fs::symlink("../outside.rs", tree.join("w/link")).unwrap();
    }
    fs::write(own.join("w/y.rs"), "Y").unwrap();
    fs::write(own.join("outside.rs"), "O").unwrap();
    for path in ["w/sub/x.rs", "w/y.rs", "w/sub", "w", "outside.rs"] {
        set_mtime(&donor.join(path), old(), false).unwrap();
    }
    set_mtime(&donor.join("w/link"), old(), false).unwrap();
    let earlier = old() - Duration::from_secs(100);
    set_mtime(&own.join("outside.rs"), earlier, false).unwrap();
    let roots = |src: &Path| Roots { src: src.to_owned(), git_dir: None };
    let newest = old() + Duration::from_secs(10);
    let mut report = Report::default();
    let table = carry_times(
        vec![(donor.join("w"), own.join("w"))],
        &roots(&donor),
        &roots(&own),
        HOST,
        moments(newest),
        &mut report,
    )
    .unwrap();
    assert_eq!((report.carried, report.differing), (4, 2));
    let mut expected: Vec<TableEntry> = ["w/sub/x.rs", "w/sub", "w", "w/link"]
        .into_iter()
        .map(|path| entry_of(&own.join(path), old()))
        .collect();
    expected.sort();
    assert_eq!(table, expected);
    assert!(mtime(&own.join("w/y.rs")) > newest, "the edited file reads later");
    assert!(
        mtime(&own.join("outside.rs")) > newest,
        "a link's target outside the directory is compared, and reads later when it differs"
    );
}

/// One recipient file reached as two inputs (a hard link) that are each the same as their
/// donor file gets one entry, with the later donor time, so no unit reads it as older than
/// its own donor input; one that differs from either reads its own, later time.
#[cfg(unix)]
#[test]
fn a_file_reached_twice_carries_the_later_donor_time_or_none() {
    let dir = TempDir::new().unwrap();
    let base = dir.path().canonicalize().unwrap();
    let (donor, own) = (base.join("donor"), base.join("own"));
    for tree in [&donor, &own] {
        fs::create_dir_all(tree).unwrap();
        fs::write(tree.join("a.rs"), "x").unwrap();
        fs::write(tree.join("c.rs"), "z").unwrap();
    }
    fs::write(donor.join("b.rs"), "x").unwrap();
    fs::write(donor.join("d.rs"), "Z").unwrap();
    fs::hard_link(own.join("a.rs"), own.join("b.rs")).unwrap();
    fs::hard_link(own.join("c.rs"), own.join("d.rs")).unwrap();
    for (path, after) in [("a.rs", 0), ("b.rs", 1), ("c.rs", 0), ("d.rs", 1)] {
        set_mtime(&donor.join(path), old() + Duration::from_secs(after), true).unwrap();
    }
    let roots = |src: &Path| Roots { src: src.to_owned(), git_dir: None };
    let mut report = Report::default();
    let pairs = ["a.rs", "b.rs", "c.rs", "d.rs"].map(|p| (donor.join(p), own.join(p))).to_vec();
    let newest = old() + Duration::from_secs(10);
    let table =
        carry_times(pairs, &roots(&donor), &roots(&own), HOST, moments(newest), &mut report)
            .unwrap();
    assert_eq!(table, [entry_of(&own.join("a.rs"), old() + Duration::from_secs(1))]);
    assert_eq!((report.carried, report.differing), (2, 2));
    assert!(mtime(&own.join("c.rs")) > newest, "a file that differs from one input reads later");
}

/// The spellings of one file (`sub/../a.rs`, `a.rs`, a path through a linked directory)
/// are compared once, as the file the system resolves them to.
#[cfg(unix)]
#[test]
fn every_spelling_of_a_file_is_compared_as_that_file() {
    let dir = TempDir::new().unwrap();
    let base = dir.path().canonicalize().unwrap();
    let (donor, own) = (base.join("donor"), base.join("own"));
    for tree in [&donor, &own] {
        fs::create_dir_all(tree.join("sub")).unwrap();
        fs::write(tree.join("a.rs"), "x").unwrap();
        std::os::unix::fs::symlink(".", tree.join("here")).unwrap();
    }
    set_mtime(&donor.join("a.rs"), old(), true).unwrap();
    let roots = |src: &Path| Roots { src: src.to_owned(), git_dir: None };
    let mut report = Report::default();
    let pairs = ["a.rs", "sub/../a.rs", "here/a.rs"].map(|p| (donor.join(p), own.join(p))).to_vec();
    let newest = old() + Duration::from_secs(10);
    let table =
        carry_times(pairs, &roots(&donor), &roots(&own), HOST, moments(newest), &mut report)
            .unwrap();
    assert_eq!(table, [entry_of(&own.join("a.rs"), old())]);
    assert_eq!((report.carried, report.differing), (1, 0));
}

/// What a cloned entry holds keeps its cloned time; an input elsewhere under `build/` is
/// compared when this tree has it; a path that resolves outside this tree must be the
/// donor's file, or the seed fails.
#[cfg(unix)]
#[test]
fn build_inputs_are_compared_and_one_resolved_outside_the_tree_must_be_the_donors() {
    let dir = TempDir::new().unwrap();
    let base = dir.path().canonicalize().unwrap();
    let (donor, own, outside) = (base.join("donor"), base.join("own"), base.join("outside"));
    fs::create_dir_all(outside.join("other")).unwrap();
    fs::write(outside.join("o.rs"), "o").unwrap();
    fs::write(outside.join("other/o.rs"), "o").unwrap();
    for tree in [&donor, &own] {
        fs::create_dir_all(tree.join(format!("build/{HOST}/stage0-sysroot"))).unwrap();
        fs::create_dir_all(tree.join(format!("build/{HOST}/stage1-rustc"))).unwrap();
        fs::write(tree.join(format!("build/{HOST}/stage0-sysroot/libstd.rlib")), "std").unwrap();
        fs::write(tree.join(format!("build/{HOST}/stage1-rustc/x.rlib")), "x").unwrap();
    }
    fs::write(own.join(format!("build/{HOST}/stage0-sysroot/libstd.rlib")), "STD").unwrap();
    std::os::unix::fs::symlink(&outside, donor.join("ext")).unwrap();
    std::os::unix::fs::symlink(&outside, own.join("ext")).unwrap();
    let roots = |src: &Path| Roots { src: src.to_owned(), git_dir: None };
    let newest = old() + Duration::from_secs(10);
    let carry = |paths: &[&str]| {
        let pairs = paths.iter().map(|p| (donor.join(p), own.join(p))).collect();
        let mut report = Report::default();
        carry_times(pairs, &roots(&donor), &roots(&own), HOST, moments(newest), &mut report)
            .map(|table| (table, report.carried, report.differing))
    };
    let sysroot = format!("build/{HOST}/stage0-sysroot/libstd.rlib");
    let cloned = format!("build/{HOST}/stage1-rustc/x.rlib");
    let missing = format!("build/{HOST}/stage0-sysroot/libcore.rlib");
    assert_eq!(carry(&[&sysroot, &cloned, &missing, "ext/o.rs"]).unwrap(), (vec![], 0, 1));
    assert!(mtime(&own.join(&sysroot)) > newest, "a differing build input reads later");

    fs::remove_file(own.join("ext")).unwrap();
    std::os::unix::fs::symlink(outside.join("other"), own.join("ext")).unwrap();
    let error = carry(&["ext/o.rs"]).unwrap_err();
    assert!(error.contains("resolves outside this tree"), "{error}");
}

/// A donor that was itself seeded has its Targo read the times of its own table: those are
/// the times a recipient carries, for as long as the donor's entry is as it was compared.
#[cfg(unix)]
#[test]
fn a_seeded_donors_carried_times_are_the_times_it_reads() {
    let dir = TempDir::new().unwrap();
    let (donor, own) = (dir.path().join("donor"), dir.path().join("own"));
    fs::write(&donor, "x").unwrap();
    fs::write(&own, "x").unwrap();
    set_mtime(&donor, old() + Duration::from_secs(5), true).unwrap();
    set_mtime(&own, old() + Duration::from_secs(3), true).unwrap();
    let donor_entry = entry_of(&donor, old());
    write_table(dir.path(), &[donor_entry]).unwrap();
    let donor_times = DonorTimes::read(dir.path()).unwrap();
    assert_eq!(
        donor_times,
        DonorTimes(BTreeMap::from([((donor_entry.dev, donor_entry.ino), donor_entry)]))
    );
    let newest = old() + Duration::from_secs(10);
    let moments = Moments { donor_times: &donor_times, ..moments(newest) };
    assert_eq!(carry_time(&donor, &own, moments).unwrap(), Carried::Table(entry_of(&own, old())));
    assert_eq!(mtime(&own), old() + Duration::from_secs(3), "no time is set back");

    // Once the donor's file changed, its table entry no longer holds, and its own (later)
    // time is the one its Targo reads.
    set_mtime(&donor, old() + Duration::from_secs(5), true).unwrap();
    assert_eq!(carry_time(&donor, &own, moments).unwrap(), Carried::Same);
    assert_eq!(mtime(&own), old() + Duration::from_secs(5));

    assert_eq!(DonorTimes::read(&dir.path().join("none")).unwrap(), DonorTimes::default());
    for damaged in ["trust-carried-times/v0\n", "trust-carried-times/v1\n1 2 3\n"] {
        fs::write(dir.path().join(CARRIED_TIMES), damaged).unwrap();
        assert!(DonorTimes::read(dir.path()).is_err(), "{damaged}");
    }
}

/// A unit is rebuilt by removing its fingerprint, its build-script directory and its
/// outputs, every file of its hash; a dependent then finds it missing and rebuilds in
/// the same build. Other units, and the uplifted copies outside `deps/`, are kept.
#[test]
fn a_rebuilt_unit_takes_its_outputs_with_it() {
    let dir = TempDir::new().unwrap();
    let profile = dir.path().join("release");
    let (gone, kept) = ("0123456789abcdef", "fedcba9876543210");
    let files = [
        format!(".fingerprint/a-{gone}/lib-a.json"),
        format!("build/a-{gone}/output"),
        format!("build/a-{gone}/out/generated.rs"),
        format!("deps/liba-{gone}.rlib"),
        format!("deps/liba-{gone}.rmeta"),
        format!("deps/a-{gone}.d"),
        format!("deps/a-{gone}.a.1234-cgu.0.rcgu.o"),
        format!("deps/a-{gone}.dSYM/Contents/Info.plist"),
        format!("examples/x-{gone}"),
        format!(".fingerprint/b-{kept}/lib-b.json"),
        format!("build/b-{kept}/output"),
        format!("deps/libb-{kept}.rlib"),
        "liba.rlib".to_owned(),
    ];
    for file in &files {
        let path = profile.join(file);
        fs::create_dir_all(path.parent().unwrap()).unwrap();
        fs::write(path, "").unwrap();
    }
    let mut report = Report::default();
    rebuild_units(BTreeSet::from([(profile.clone(), gone.to_owned())]), &mut report).unwrap();
    for file in &files {
        assert_eq!(profile.join(file).exists(), !file.contains(gone), "{file}");
    }
    assert_eq!(report.rebuilt, BTreeSet::from(["a".to_owned()]));
}

/// A build script's `rerun-if-changed` values are read as Targo reads them.
#[test]
fn rerun_if_changed_is_read_as_targo_reads_it() {
    let output = b"cargo:rerun-if-changed=a\n  cargo::rerun-if-changed=b  \n\ttargo::rerun-if-changed= c\n\
targo:rerun-if-changed=d\r\ncargo:rerun-if-env-changed=E\ncargo:rustc-cfg=x\ncargo:rerun-if-changed=f\xff\n\
cargo:rerun-if-changed=g";
    // Targo trims the line, then the value at its end only: ` c` names a file whose name
    // begins with a space.
    assert_eq!(rerun_if_changed(output), ["a", "b", " c", "d", "g"]);
}

/// A relative `rerun-if-changed` path is relative to its package: the one whose manifest
/// names the build script its dependency file names first. One whose package the seed
/// cannot name fails the seed rather than leave what it names uncompared, and so does one
/// whose build script is not a file of this tree (a dependency file written by a build run
/// in another directory, relative to it) or is not its manifest's build script.
#[test]
fn a_relative_watched_path_is_read_under_its_package_or_the_seed_fails() {
    let dir = TempDir::new().unwrap();
    let own_src = dir.path().join("own");
    let file = |path: &str, text: &str| {
        let path = own_src.join(path);
        fs::create_dir_all(path.parent().unwrap()).unwrap();
        fs::write(path, text).unwrap();
    };
    file("Cargo.toml", "[workspace]\n");
    file("tools/pkg/Cargo.toml", "[package]\nname = \"pkg\"\nbuild = \"build/main.rs\"\n");
    file("tools/pkg/build/main.rs", "fn main() {}");
    file("tools/pkg/build.rs", "fn main() {}");
    file("tools/abs/Cargo.toml", "[package]\nname = \"abs\"\n");
    file("tools/abs/build.rs", "fn main() {}");
    file("tools/nobuild/Cargo.toml", "[package]\nname = \"nobuild\"\nbuild = false\n");
    file("tools/nobuild/build.rs", "fn main() {}");
    file("loose/build.rs", "fn main() {}");
    let donor = Roots { src: "/w/donor".into(), git_dir: None };
    let own = Roots { src: own_src, git_dir: None };
    let script = |tokens: &[&str]| {
        let mut roots = ScriptRoots::default();
        roots.note(&tokens.iter().map(|t| t.to_string()).collect::<Vec<_>>(), &donor, &own);
        roots
    };
    let exe = "/w/donor/build/x/build/pkg-0123456789abcdef/build_script_build-0123456789abcdef";
    let scripts = BTreeMap::from([
        ("rel".to_owned(), script(&[exe, "tools/pkg/build/main.rs", "loose/gen.rs"])),
        ("abs".to_owned(), script(&[exe, "/w/donor/tools/abs/build.rs"])),
        ("reg".to_owned(), script(&[exe, "/home/u/.cargo/registry/src/reg-1.0/build.rs"])),
        // Not the build script its manifest names (that is `build/main.rs`).
        ("other".to_owned(), script(&[exe, "tools/pkg/build.rs"])),
        ("nobuild".to_owned(), script(&[exe, "tools/nobuild/build.rs"])),
        // No manifest above it names it: the root's is a workspace.
        ("loose".to_owned(), script(&[exe, "loose/build.rs"])),
        // Relative to the directory a nested build ran in: no such file in this tree.
        ("elsewhere".to_owned(), script(&[exe, "build.rs"])),
        ("none".to_owned(), script(&[exe])),
    ]);
    let read =
        |pkg: &str, value: &str| rerun_inputs(vec![(pkg.to_owned(), value.to_owned())], &scripts);
    assert_eq!(read("rel", "data.txt").unwrap(), ["tools/pkg/data.txt"]);
    assert_eq!(read("abs", "data.txt").unwrap(), ["tools/abs/data.txt"]);
    assert_eq!(read("rel", "/w/donor/x").unwrap(), ["/w/donor/x"]);
    assert!(read("reg", "data.txt").unwrap().is_empty(), "the registry's is one file for both");
    for pkg in ["other", "nobuild", "loose", "elsewhere", "none", "unknown"] {
        let error = read(pkg, "data.txt").unwrap_err();
        assert!(error.contains(pkg) && error.contains("data.txt"), "{error}");
    }
}

/// A dependency file the seed cannot read names inputs it would not compare: the seed
/// fails, and the tree builds cold.
#[cfg(target_os = "macos")]
#[test]
fn a_dependency_file_that_cannot_be_read_fails_the_seed() {
    use std::os::unix::fs::PermissionsExt;
    let Trees { _dir, donor, own, record } = trees();
    let host_dir = own.src.join(format!("build/{HOST}"));
    let (names, donor_times) = match clone_from(&donor.src, &record, HOST, &host_dir) {
        Ok(cloned) => cloned,
        Err(Refused::Held(why) | Refused::Busy(why) | Refused::Failed(why)) => panic!("{why}"),
    };
    let depinfo =
        host_dir.join(format!("stage1-rustc{PARTIAL}/release/deps/foo-0123456789abcdef.d"));
    fs::set_permissions(&depinfo, fs::Permissions::from_mode(0o000)).unwrap();
    let settled = SystemTime::now() + Duration::from_millis(1);
    let failed = fix_clone(&host_dir, &names, &donor_times, &donor, &own, HOST, settled);
    fs::set_permissions(&depinfo, fs::Permissions::from_mode(0o644)).unwrap();
    let error = failed.unwrap_err();
    assert!(error.contains("foo-0123456789abcdef.d"), "{error}");
}

/// A fingerprint that holds a path package's newest time compares a time no seed carries.
#[test]
fn a_fingerprint_of_a_package_time_is_recognized() {
    assert!(names_a_package_time(
        r#"{"local":[{"Precalculated":"1793908529.586150895s (src/lib.rs)"}]}"#
    ));
    assert!(!names_a_package_time(r#"{"local":[{"Precalculated":"1.0.0"}]}"#));
    assert!(!names_a_package_time(
        r#"{"local":[{"RerunIfChanged":{"output":"x","paths":["a"]}}]}"#
    ));
    assert!(!names_a_package_time(r#"{"local":[{"Precalculated":"1.2s"}]}"#));
}

/// A rename that fails leaves the marker naming only what this seed placed, so undoing it
/// never removes an entry another run made.
#[test]
fn a_seed_that_cannot_place_its_entries_undoes_only_what_it_placed() {
    let dir = TempDir::new().unwrap();
    let host_dir = dir.path();
    fs::create_dir(host_dir.join(format!("bootstrap-tools{PARTIAL}"))).unwrap();
    fs::create_dir(host_dir.join(format!("stage1-rustc{PARTIAL}"))).unwrap();
    // Another run's entry, which the second rename cannot replace.
    fs::create_dir(host_dir.join("stage1-rustc")).unwrap();
    fs::write(host_dir.join("stage1-rustc/theirs"), "").unwrap();
    let names = ["bootstrap-tools".to_owned(), "stage1-rustc".to_owned()];
    let lines = marker_lines(host_dir, &names).unwrap();
    assert!(rename_into_place(host_dir, &names).is_err());
    assert_eq!(fs::read_to_string(host_dir.join(INCOMPLETE)).unwrap(), lines[0]);
    undo_incomplete(host_dir);
    assert!(!host_dir.join("bootstrap-tools").exists());
    assert!(!host_dir.join(format!("stage1-rustc{PARTIAL}")).exists());
    assert!(host_dir.join("stage1-rustc/theirs").exists());
}

/// A seed killed between its renames leaves the marker naming every entry. A run that
/// bypasses the lock then builds the entries it lacks, and the next run that holds the
/// lock undoes the seed: it removes the entries the seed placed (the marker's inodes)
/// and keeps the ones the other run made in their place.
#[test]
fn an_undo_removes_only_the_entries_the_seed_placed() {
    let dir = TempDir::new().unwrap();
    let host_dir = dir.path();
    let names = ["stage1-rustc".to_owned(), "stage1-std".to_owned()];
    for name in &names {
        fs::create_dir(host_dir.join(format!("{name}{PARTIAL}"))).unwrap();
    }
    fs::write(host_dir.join(INCOMPLETE), marker_lines(host_dir, &names).unwrap().join("\n"))
        .unwrap();
    fs::rename(host_dir.join(format!("stage1-rustc{PARTIAL}")), host_dir.join("stage1-rustc"))
        .unwrap();
    // Killed here. The run that bypasses the lock:
    fs::create_dir(host_dir.join("stage1-std")).unwrap();
    fs::write(host_dir.join("stage1-std/built"), "").unwrap();
    undo_incomplete(host_dir);
    assert!(!host_dir.join("stage1-rustc").exists(), "the seed placed it");
    assert!(host_dir.join("stage1-std/built").exists(), "another run made it");
    assert!(!host_dir.join(format!("stage1-std{PARTIAL}")).exists());
    assert!(!host_dir.join(INCOMPLETE).exists());
}

#[test]
fn inputs_are_paired_by_tree() {
    let donor = Roots { src: "/w/a".into(), git_dir: Some("/g/worktrees/a".into()) };
    let own = Roots { src: "/w/b".into(), git_dir: Some("/g/worktrees/b".into()) };
    let inputs: BTreeSet<String> = [
        "compiler/rustc/src/main.rs",
        "/w/a/first-party/ay/src/lib.rs",
        "/g/worktrees/a/modules/first-party/ay/HEAD",
        "/w/a/build/aarch64-apple-darwin/stage0-sysroot/lib/libstd.rlib",
        "build/x",
        "<home>/.cargo/registry/src/a/lib.rs",
        "/w/ab/lib.rs",
    ]
    .into_iter()
    .map(str::to_owned)
    .collect();
    let pairs = input_pairs(&inputs, &donor, &own);
    let pairs: BTreeSet<(PathBuf, PathBuf)> = pairs.into_iter().collect();
    let expected: BTreeSet<(PathBuf, PathBuf)> = [
        ("/w/a/compiler/rustc/src/main.rs", "/w/b/compiler/rustc/src/main.rs"),
        ("/w/a/first-party/ay/src/lib.rs", "/w/b/first-party/ay/src/lib.rs"),
        (
            "/g/worktrees/a/modules/first-party/ay/HEAD",
            "/g/worktrees/b/modules/first-party/ay/HEAD",
        ),
        (
            "/w/a/build/aarch64-apple-darwin/stage0-sysroot/lib/libstd.rlib",
            "/w/b/build/aarch64-apple-darwin/stage0-sysroot/lib/libstd.rlib",
        ),
        ("/w/a/build/x", "/w/b/build/x"),
    ]
    .into_iter()
    .map(|(a, b)| (a.into(), b.into()))
    .collect();
    assert_eq!(pairs, expected);
}

#[test]
fn dependency_files_are_read_as_rustc_writes_them() {
    let text = "# comment\n/w/a/build/x/deps/libfoo-0123456789abcdef.rmeta: src/lib.rs \
                src/a\\ b.rs /abs/c.rs\n\nsrc/lib.rs:\nsrc/a\\ b.rs:\n";
    assert_eq!(
        depinfo_paths(text),
        [
            "/w/a/build/x/deps/libfoo-0123456789abcdef.rmeta",
            "src/lib.rs",
            "src/a b.rs",
            "/abs/c.rs",
            "src/lib.rs",
            "src/a b.rs",
        ]
    );
}

#[test]
fn a_file_is_owned_by_the_unit_its_path_names() {
    let unit = |path: &str| unit_of(Path::new(path));
    let hash = "0123456789abcdef";
    assert_eq!(
        unit(&format!("stage1-rustc/{HOST}/release/deps/libfoo-{hash}.rlib")),
        Some(Unit {
            profile: format!("stage1-rustc/{HOST}/release").into(),
            hash: hash.into(),
            within: None,
            fingerprint: false,
        })
    );
    assert_eq!(
        unit(&format!("stage1-rustc/release/deps/foo-{hash}.foo.abc-cgu.0.rcgu.o")).unwrap().hash,
        hash
    );
    assert_eq!(
        unit(&format!("stage1-rustc/release/deps/foo-{hash}.dSYM/Contents/Resources/DWARF/x"))
            .unwrap()
            .hash,
        hash
    );
    let output =
        unit(&format!("stage1-rustc/release/build/foo-{hash}/out/build/bar-fedcba9876543210/x"))
            .unwrap();
    assert_eq!((output.hash.as_str(), output.fingerprint), (hash, false));
    assert_eq!(output.within, Some("out/build/bar-fedcba9876543210/x".into()));
    let fingerprint =
        unit(&format!("bootstrap-tools/release/.fingerprint/foo-{hash}/lib-foo.json")).unwrap();
    assert!(fingerprint.fingerprint);
    assert_eq!(fingerprint.profile, PathBuf::from("bootstrap-tools/release"));
    assert_eq!(unit("stage1-tools-bin/targo"), None);
    assert_eq!(unit("stage1-rustc/release/deps/libfoo-0123456789ABCDEF.rlib"), None);
    assert_eq!(unit(&format!("stage1-rustc/release/build/foo-{hash}")), None);
}

/// A minimal 64-bit Mach-O object: one segment command holding `sections` (segment,
/// section, bytes) and a symbol table whose strings are `strings`.
fn macho(sections: &[(&str, &str, &[u8])], strings: &[u8]) -> (Vec<u8>, Vec<usize>, usize) {
    let header = 32;
    let segment = 72 + 80 * sections.len();
    let symtab = 24;
    let mut data_at = header + segment + symtab;
    let mut out = Vec::new();
    let u32le = |out: &mut Vec<u8>, v: u32| out.extend_from_slice(&v.to_le_bytes());
    let u64le = |out: &mut Vec<u8>, v: u64| out.extend_from_slice(&v.to_le_bytes());
    let name = |out: &mut Vec<u8>, text: &str| {
        let mut field = [0u8; 16];
        field[..text.len()].copy_from_slice(text.as_bytes());
        out.extend_from_slice(&field);
    };
    u32le(&mut out, 0xfeed_facf);
    u32le(&mut out, 0x0100_000c);
    u32le(&mut out, 0);
    u32le(&mut out, 1);
    u32le(&mut out, 2);
    u32le(&mut out, (segment + symtab) as u32);
    u32le(&mut out, 0);
    u32le(&mut out, 0);
    let total: usize = sections.iter().map(|s| s.2.len()).sum();
    u32le(&mut out, 0x19);
    u32le(&mut out, segment as u32);
    name(&mut out, "");
    u64le(&mut out, 0);
    u64le(&mut out, total as u64);
    u64le(&mut out, data_at as u64);
    u64le(&mut out, total as u64);
    u32le(&mut out, 7);
    u32le(&mut out, 7);
    u32le(&mut out, sections.len() as u32);
    u32le(&mut out, 0);
    let mut offsets = Vec::new();
    for (segname, sectname, bytes) in sections {
        name(&mut out, sectname);
        name(&mut out, segname);
        u64le(&mut out, 0);
        u64le(&mut out, bytes.len() as u64);
        u32le(&mut out, data_at as u32);
        offsets.push(data_at);
        for _ in 0..5 {
            u32le(&mut out, 0);
        }
        u32le(&mut out, 0);
        u32le(&mut out, 0);
        data_at += bytes.len();
    }
    u32le(&mut out, 0x2);
    u32le(&mut out, symtab as u32);
    u32le(&mut out, 0);
    u32le(&mut out, 0);
    u32le(&mut out, data_at as u32);
    u32le(&mut out, strings.len() as u32);
    for (_, _, bytes) in sections {
        out.extend_from_slice(bytes);
    }
    out.extend_from_slice(strings);
    (out, offsets, data_at)
}

fn offsets_of(data: &[u8], needle: &[u8]) -> Vec<(usize, usize)> {
    memchr::memmem::find_iter(data, needle).map(|offset| (offset, 0)).collect()
}

#[test]
fn only_debug_information_may_name_the_donors_tree() {
    let donor = Roots { src: "/w/donor".into(), git_dir: None };
    let root = b"/w/donor/first-party/x/src/lib.rs\0";
    let (object, _, _) = macho(
        &[("__DWARF", "__debug_str", root), ("__TEXT", "__text", b"\0\0\0\0")],
        b"\0/w/donor/build/deps/x.o\0",
    );
    let ranges = debug_ranges(&object);
    assert_eq!(ranges.len(), 2);
    let offsets = offsets_of(&object, b"/w/donor");
    assert_eq!(offsets.len(), 2);
    let deps = format!("stage1-rustc/{HOST}/release/deps/libx-0123456789abcdef.rlib");
    let classify_at = |entry: &str, path: &str, data: &[u8], relocated: bool| {
        classify(
            entry,
            Path::new(path),
            data,
            &offsets_of(data, b"/w/donor"),
            &donor,
            HOST,
            relocated,
        )
    };
    assert_eq!(classify_at("stage1-rustc", &deps, &object, false), Finding::Kept);

    // A path compiled into code (`__cstring`), into an rlib's metadata (`.rmeta`, which
    // rustc keeps in the `__DWARF` segment) or into embedded bitcode (the module's code
    // with its debug metadata) rebuilds the unit.
    for (segname, sectname) in
        [("__TEXT", "__cstring"), ("__DWARF", ".rmeta"), ("__LLVM", "__bitcode")]
    {
        let (object, _, _) = macho(&[(segname, sectname, root)], b"\0");
        assert_eq!(
            classify_at("stage1-rustc", &deps, &object, false),
            Finding::Rebuild {
                profile: format!("stage1-rustc/{HOST}/release").into(),
                hash: "0123456789abcdef".into()
            },
            "{segname},{sectname}"
        );
    }

    // In an rlib, a member's debug information is found at the member's offset.
    let mut archive = b"!<arch>\n".to_vec();
    let header =
        format!("{:<16}{:<12}{:<6}{:<6}{:<8}{:<10}`\n", "x.o/", 0, 0, 0, 644, object.len());
    archive.extend_from_slice(header.as_bytes());
    archive.extend_from_slice(&object);
    if archive.len() % 2 == 1 {
        archive.push(b'\n');
    }
    assert_eq!(debug_ranges(&archive).len(), 2);
    assert_eq!(classify_at("stage1-rustc", &deps, &archive, false), Finding::Kept);
    let mut text = archive.clone();
    text.extend_from_slice(b"/w/donor/oops");
    assert!(matches!(classify_at("stage1-rustc", &deps, &text, false), Finding::Rebuild { .. }));
}

#[test]
fn each_kind_of_file_that_names_the_donors_tree_has_one_disposition() {
    let donor = Roots { src: "/w/donor".into(), git_dir: Some("/g/worktrees/donor".into()) };
    let hash = "0123456789abcdef";
    let rebuild = || Finding::Rebuild { profile: "stage1-rustc/release".into(), hash: hash.into() };
    let at = |entry: &str, path: &str, data: &[u8], relocated: bool| {
        let offsets: Vec<(usize, usize)> = donor
            .needles()
            .iter()
            .enumerate()
            .flat_map(|(index, needle)| {
                memchr::memmem::find_iter(data, needle).map(move |offset| (offset, index))
            })
            .collect();
        classify(entry, Path::new(path), data, &offsets, &donor, HOST, relocated)
    };
    let build = format!("stage1-rustc/release/build/foo-{hash}");
    assert_eq!(
        at("stage1-rustc", &format!("{build}/root-output"), b"/w/donor/x", false),
        Finding::Kept
    );
    assert_eq!(at("stage1-rustc", &format!("{build}/stderr"), b"/w/donor/x", false), Finding::Kept);
    assert_eq!(at("stage1-rustc", &format!("{build}/output"), b"/w/donor/x", true), Finding::Kept);
    assert_eq!(at("stage1-rustc", &format!("{build}/output"), b"/w/donor/x", false), rebuild());
    assert_eq!(at("stage1-rustc", &format!("{build}/out/gen.rs"), b"/w/donor/x", true), rebuild());
    let fingerprint = format!("stage1-rustc/release/.fingerprint/foo-{hash}");
    assert_eq!(
        at("stage1-rustc", &format!("{fingerprint}/output-lib-foo"), b"/w/donor/x", false),
        Finding::Rewrite
    );
    assert_eq!(
        at(
            "stage1-rustc",
            &format!("{fingerprint}/lib-foo.json"),
            b"/g/worktrees/donor/HEAD",
            false
        ),
        rebuild()
    );
    assert_eq!(
        at(
            "stage1-rustc",
            &format!("stage1-rustc/release/deps/foo-{hash}.d"),
            b"/w/donor/x",
            false
        ),
        Finding::Rewrite
    );
    assert_eq!(
        at("stage1-rustc", "stage1-rustc/.librustc.stamp", b"/w/donor/x", false),
        Finding::Rewrite
    );
    let unremap = br#"{"v":1,"workspace_root":"/w/donor","remaps":[{"to":"/w/donor/build"}]}"#;
    for path in [
        format!("stage1-rustc/release/deps/libfoo-{hash}.rlib.trim-paths.json"),
        "stage1-rustc/release/libfoo.rlib.trim-paths.json".to_owned(),
    ] {
        assert_eq!(at("stage1-rustc", &path, unremap, false), Finding::Rewrite, "{path}");
    }
    assert_eq!(
        at("stage1-rustc", "stage1-rustc/release/.rustc_info.json", b"/w/donor", false),
        Finding::Delete
    );
    assert_eq!(
        at("stage1-tools-bin", "stage1-tools-bin/targo", b"/w/donor/x", false),
        Finding::Delete
    );

    let llvm_build =
        format!("/w/donor/build/{HOST}/llvm/build/lib\0/w/donor/src/llvm-project/llvm\0");
    assert_eq!(at("llvm", "llvm/bin/llvm-config", llvm_build.as_bytes(), false), Finding::Kept);
    assert_eq!(
        at("llvm", "llvm/bin/llvm-config", b"/w/donor/src/llvm-projectx", false),
        Finding::Refuse
    );
    assert_eq!(
        at("llvm", "llvm/bin/llvm-config", b"/w/donor/first-party/x", false),
        Finding::Refuse
    );
    assert_eq!(at("llvm", "llvm/lib/x", b"/g/worktrees/donor/HEAD", false), Finding::Refuse);
}

#[test]
fn only_roots_spelled_in_bytes_no_escaping_changes_are_used() {
    let roots = |src: &str, git_dir: Option<&str>| Roots {
        src: src.into(),
        git_dir: git_dir.map(PathBuf::from),
    };
    assert!(
        roots("<home>/fixwt.noindex/wt/trust-ew9_b-2", Some(".git")).spellable()
    );
    // A JSON string, a URL, a shell word or a `-Z` list spells each of these differently.
    for odd in ["/w/a b", "/w/a\"b", "/w/a\\b", "/w/a%20b", "/w/a,b", "/w/é", "/w/a+b", "/w/a'b"] {
        assert!(!roots(odd, None).spellable(), "{odd}");
        assert!(!roots("/w/a", Some(odd)).spellable(), "git directory {odd}");
    }
}

#[test]
fn a_rewrite_moves_the_git_directory_before_the_tree_that_holds_it() {
    let donor = Roots { src: "/m".into(), git_dir: Some("/m/.git".into()) };
    let own = Roots { src: "/w/b".into(), git_dir: Some("/m/.git/worktrees/b".into()) };
    assert_eq!(
        relocated(b"/m/.git/modules/ay/HEAD /m/src/lib.rs /m.old", &donor, &own),
        b"/m/.git/worktrees/b/modules/ay/HEAD /w/b/src/lib.rs /m.old".to_vec()
    );
}

/// A donor tree and a fresh recipient tree on one APFS volume, as two worktrees are.
#[cfg(target_os = "macos")]
struct Trees {
    _dir: TempDir,
    donor: Roots,
    own: Roots,
    record: Record,
}

#[cfg(target_os = "macos")]
fn trees() -> Trees {
    let dir = TempDir::new().unwrap();
    let base = dir.path().canonicalize().unwrap();
    let (donor, own) = (base.join("donor"), base.join("own"));
    let hash = "0123456789abcdef";
    let release = |tree: &Path| tree.join(format!("build/{HOST}/stage1-rustc/release"));
    for tree in [&donor, &own] {
        fs::create_dir_all(tree.join(format!("build/{HOST}/stage0"))).unwrap();
        fs::write(tree.join("build/lock"), "").unwrap();
        fs::create_dir_all(tree.join("src")).unwrap();
        fs::write(tree.join("src/lib.rs"), "pub fn f() {}").unwrap();
        fs::write(tree.join("src/edited.rs"), "pub fn g() {}").unwrap();
    }
    fs::write(own.join("src/edited.rs"), "pub fn g() { }").unwrap();
    set_mtime(&donor.join("src/lib.rs"), old(), true).unwrap();
    set_mtime(&donor.join("src/edited.rs"), old(), true).unwrap();
    let d = donor.display();
    let files = [
        (format!(".fingerprint/foo-{hash}/lib-foo.json"), "{}".to_owned()),
        (format!("deps/libfoo-{hash}.rlib"), format!("const DIR: &str = \"{d}/src\";")),
        (
            format!("deps/foo-{hash}.d"),
            format!("{d}/build/x/libfoo.rlib: src/lib.rs src/edited.rs\n"),
        ),
        (".fingerprint/bar-fedcba9876543210/lib-bar.json".to_owned(), "{}".to_owned()),
        ("deps/libbar-fedcba9876543210.rlib".to_owned(), "plain".to_owned()),
        ("build/baz-1111111111111111/root-output".to_owned(), format!("{d}/build/out")),
        ("build/baz-1111111111111111/output".to_owned(), format!("cargo:rustc-env=X={d}/y\n")),
        (".fingerprint/baz-1111111111111111/run-build-script".to_owned(), "{}".to_owned()),
        // Recorded under the donor's roots: Targo re-roots its output.
        ("build/qux-2222222222222222/output".to_owned(), format!("cargo:rustc-env=X={d}/y\n")),
        (
            "build/qux-2222222222222222/root-relocation".to_owned(),
            format!("trust-relocation-roots-v1\0{d}\0\0"),
        ),
        (".fingerprint/qux-2222222222222222/run-build-script".to_owned(), "{}".to_owned()),
        // Recorded under other roots: its output cannot be re-rooted from here.
        ("build/quux-3333333333333333/output".to_owned(), format!("cargo:rustc-env=X={d}/y\n")),
        (
            "build/quux-3333333333333333/root-relocation".to_owned(),
            "trust-relocation-roots-v1\0/elsewhere\0\0".to_owned(),
        ),
        (".fingerprint/quux-3333333333333333/run-build-script".to_owned(), "{}".to_owned()),
        // A build script that names no input: its fingerprint is its package's newest time.
        (
            ".fingerprint/tim-4444444444444444/run-build-script-build-script-build.json".to_owned(),
            r#"{"local":[{"Precalculated":"1600000000.000000000s (src/lib.rs)"}]}"#.to_owned(),
        ),
        (
            ".fingerprint/ver-5555555555555555/lib-ver.json".to_owned(),
            r#"{"local":[{"Precalculated":"1.0.0"}]}"#.to_owned(),
        ),
        ("incremental/foo-1/s-1/dep-graph.bin".to_owned(), d.to_string()),
        ("../.librustc.stamp".to_owned(), format!("h{d}/build/x/libfoo.rlib\0")),
    ];
    for (path, text) in &files {
        let path = release(&donor).join(path);
        fs::create_dir_all(path.parent().unwrap()).unwrap();
        fs::write(path, text).unwrap();
    }
    set_mtime(&release(&donor).join("../.librustc.stamp"), old(), true).unwrap();
    std::os::unix::fs::symlink(donor.join("src"), release(&donor).join("src-link")).unwrap();
    let llvm = donor.join(format!("build/{HOST}/llvm"));
    fs::create_dir_all(llvm.join("build")).unwrap();
    fs::create_dir_all(llvm.join("bin")).unwrap();
    fs::write(llvm.join("build/CMakeCache.txt"), format!("{d}/build")).unwrap();
    fs::write(llvm.join("bin/llvm-config"), format!("{d}/src/llvm-project/llvm\0")).unwrap();
    fs::create_dir_all(donor.join(format!("build/{HOST}/stage2-tools-bin"))).unwrap();
    // Bootstrap's `Sysroot` step deletes and rebuilds it on every build.
    let sysroot = donor.join(format!("build/{HOST}/stage0-sysroot/lib"));
    fs::create_dir_all(&sysroot).unwrap();
    fs::write(sysroot.join("libx.rmeta"), format!("{d}/compiler")).unwrap();

    let donor = Roots { src: donor, git_dir: None };
    let own = Roots { src: own, git_dir: None };
    let record =
        Record { key: Key::new(&inputs("a".repeat(40).as_str(), &[])), roots: donor.clone() };
    record.write(&donor.src.join(format!("build/{HOST}"))).unwrap();
    Trees { _dir: dir, donor, own, record }
}

#[cfg(target_os = "macos")]
#[test]
fn a_seed_clones_carries_times_and_rebuilds_what_names_the_donor() {
    let Trees { _dir, donor, own, record } = trees();
    let host_dir = own.src.join(format!("build/{HOST}"));
    let (names, donor_times) = match clone_from(&donor.src, &record, HOST, &host_dir) {
        Ok(cloned) => cloned,
        Err(Refused::Held(why) | Refused::Busy(why) | Refused::Failed(why)) => panic!("{why}"),
    };
    assert_eq!(
        names,
        ["llvm", "stage1-rustc"],
        "stage0, the stage0-sysroot and stage2 are never cloned"
    );
    assert!(!donor.src.join(".trust-build-lock").exists(), "the donor's lock is released");
    let settled = SystemTime::now() + Duration::from_millis(1);
    let report = fix_clone(&host_dir, &names, &donor_times, &donor, &own, HOST, settled).unwrap();
    rename_into_place(&host_dir, &names).unwrap();

    let release = host_dir.join("stage1-rustc/release");
    assert!(!release.join("incremental").exists());
    assert!(!host_dir.join("llvm/build").exists());
    assert!(host_dir.join("llvm/bin/llvm-config").exists());
    assert!(!host_dir.join("stage2-tools-bin").exists());
    assert!(!host_dir.join("stage0-sysroot").exists());
    assert!(!host_dir.join(INCOMPLETE).exists());
    assert_eq!(report.rebuilt, BTreeSet::from(["baz", "foo", "quux", "tim"].map(str::to_owned)));
    assert!(!release.join(".fingerprint/foo-0123456789abcdef").exists());
    assert!(!release.join(".fingerprint/baz-1111111111111111").exists());
    assert!(!release.join(".fingerprint/quux-3333333333333333").exists());
    assert!(release.join(".fingerprint/qux-2222222222222222/run-build-script").exists());
    assert!(release.join(".fingerprint/bar-fedcba9876543210/lib-bar.json").exists());
    assert!(!release.join(".fingerprint/tim-4444444444444444").exists());
    // A rebuilt unit's outputs go with its fingerprint, so what depends on it rebuilds in
    // the same build; another unit's are kept.
    assert!(!release.join("deps/libfoo-0123456789abcdef.rlib").exists());
    assert!(!release.join("deps/foo-0123456789abcdef.d").exists());
    assert!(!release.join("build/baz-1111111111111111").exists());
    assert!(!release.join("build/quux-3333333333333333").exists());
    assert!(release.join("build/qux-2222222222222222/output").exists());
    assert!(release.join("deps/libbar-fedcba9876543210.rlib").exists());
    assert!(release.join(".fingerprint/ver-5555555555555555/lib-ver.json").exists());

    // The unchanged source keeps its own time and reads to Targo as the donor's, from the
    // table; the edited one, written before the donor's outputs, reads later than them.
    let lib = own.src.join("src/lib.rs");
    assert_ne!(mtime(&lib), old(), "a time is never set back on a source");
    let table = fs::read_to_string(host_dir.join(CARRIED_TIMES)).unwrap();
    assert_eq!(table, format!("trust-carried-times/v1\n{}", entry_of(&lib, old()).line()));
    assert_eq!((report.carried, report.table, report.differing), (1, 1, 1));
    let cloned = release.join(".fingerprint/bar-fedcba9876543210/lib-bar.json");
    assert!(mtime(&own.src.join("src/edited.rs")) > mtime(&cloned), "an edited one reads later");
    let stamp = host_dir.join("stage1-rustc/.librustc.stamp");
    assert_eq!(
        fs::read_to_string(&stamp).unwrap(),
        format!("h{}/build/x/libfoo.rlib\0", own.src.display())
    );
    assert_eq!(mtime(&stamp), old(), "a rewritten stamp keeps its time");
    assert_eq!(fs::read_link(release.join("src-link")).unwrap(), own.src.join("src"));
    let cloned = fs::metadata(release.join("deps/libbar-fedcba9876543210.rlib")).unwrap();
    let original = fs::metadata(
        donor
            .src
            .join(format!("build/{HOST}/stage1-rustc/release/deps/libbar-fedcba9876543210.rlib")),
    )
    .unwrap();
    use std::os::unix::fs::MetadataExt;
    assert_ne!(cloned.ino(), original.ino(), "a clone, never a link");
}

#[cfg(target_os = "macos")]
#[test]
fn a_busy_or_changed_donor_is_refused() {
    let Trees { _dir, donor, own, record } = trees();
    let host_dir = own.src.join(format!("build/{HOST}"));
    let refused = |record: &Record| match clone_from(&donor.src, record, HOST, &host_dir) {
        Err(Refused::Held(why)) => ("held", why),
        Err(Refused::Busy(why)) => ("busy", why),
        Ok(_) => panic!("a busy donor was cloned"),
        Err(Refused::Failed(why)) => panic!("{why}"),
    };

    fs::create_dir(donor.src.join(".trust-build-lock")).unwrap();
    let (how, why) = refused(&record);
    assert!(how == "held" && why.contains("build/measurement lock"), "{how}: {why}");
    fs::remove_dir(donor.src.join(".trust-build-lock")).unwrap();

    let held = fs::OpenOptions::new().write(true).open(donor.src.join("build/lock")).unwrap();
    held.lock().unwrap();
    let (how, why) = refused(&record);
    assert!(how == "held" && why.contains("build/lock"), "{how}: {why}");
    drop(held);

    let mut other = record.clone();
    other.key = Key::new(&inputs("b".repeat(40).as_str(), &[]));
    let (how, why) = refused(&other);
    assert!(how == "busy" && why.contains("record changed"), "{how}: {why}");
    assert!(fs::read_dir(&host_dir).unwrap().flatten().all(|entry| entry.file_name() == "stage0"));
}

/// Native acquisition waits for the exact purpose the independent donor seed
/// lease writes, even with no explicitly requested wait budget.
#[cfg(target_os = "macos")]
#[test]
fn native_acquisition_waits_for_the_lease_a_seed_takes() {
    let dir = TempDir::new().unwrap();
    let root = dir.path().canonicalize().unwrap();
    crate::utils::trust_repo_lock::namespace_tests::assert_seed_wait(&root);
}

/// A donor whose lease or `build/lock` is held is waited for only while its record
/// stands: one whose record is gone has begun a build, will not serve, and is refused at
/// once rather than tried again for a minute.
#[cfg(target_os = "macos")]
#[test]
fn a_held_donor_whose_record_is_gone_is_not_waited_for() {
    let Trees { _dir, donor, own, record } = trees();
    let host_dir = own.src.join(format!("build/{HOST}"));
    let donor_record = donor.src.join(format!("build/{HOST}/{RECORD}"));
    let refused = || match clone_from(&donor.src, &record, HOST, &host_dir) {
        Err(Refused::Held(why)) => ("held", why),
        Err(Refused::Busy(why)) => ("busy", why),
        Ok(_) => panic!("a busy donor was cloned"),
        Err(Refused::Failed(why)) => panic!("{why}"),
    };

    let lease = donor.src.join(".trust-build-lock");
    fs::create_dir(&lease).unwrap();
    fs::remove_file(&donor_record).unwrap();
    let (how, why) = refused();
    assert!(how == "busy" && why.contains("record changed"), "{how}: {why}");
    fs::remove_dir(&lease).unwrap();

    let held = fs::OpenOptions::new().write(true).open(donor.src.join("build/lock")).unwrap();
    held.lock().unwrap();
    let (how, why) = refused();
    assert!(how == "busy" && why.contains("record changed"), "{how}: {why}");
    record.write(&donor.src.join(format!("build/{HOST}"))).unwrap();
    let (how, why) = refused();
    assert!(how == "held" && why.contains("build/lock"), "{how}: {why}");
    drop(held);
    assert!(fs::read_dir(&host_dir).unwrap().flatten().all(|entry| entry.file_name() == "stage0"));
}

/// Trust: EW-9 (22). `ps -o lstart=` for `pid`, as the lease writer reads it: in this
/// process's zone and locale, or (`utc`) in none.
#[cfg(target_os = "macos")]
fn start_of(pid: u32, utc: bool) -> String {
    let mut ps = std::process::Command::new("ps");
    ps.args(["-o", "lstart=", "-p", &pid.to_string()]);
    if utc {
        ps.env("LC_ALL", "C").env("TZ", "UTC0").env_remove("LANG").env_remove("LC_TIME");
    }
    let output = ps.output().unwrap();
    assert!(output.status.success(), "{output:?}");
    String::from_utf8(output.stdout).unwrap().trim().to_owned()
}

/// Trust: EW-9 (22). A process that ran and has been reaped: its pid, and its start read
/// while it ran (zoned and zone-free), as a seed killed while it cloned leaves them.
#[cfg(target_os = "macos")]
fn reaped_process() -> (u32, String, String) {
    let mut child = std::process::Command::new("/bin/cat")
        .stdin(std::process::Stdio::piped())
        .stdout(std::process::Stdio::null())
        .spawn()
        .unwrap();
    let pid = child.id();
    let starts = (start_of(pid, false), start_of(pid, true));
    drop(child.stdin.take());
    assert!(child.wait().unwrap().success());
    (pid, starts.0, starts.1)
}

/// Trust: EW-9 (22). A lease record field and what replaces its value (`None`: left out).
#[cfg(target_os = "macos")]
type Field<'a> = (&'a str, Option<&'a str>);

/// Trust: EW-9 (22). Puts on `tree` the lease record the seed's own writer makes, each of
/// `fields` replaced. The writer takes and releases a real lease for it, so the record's
/// layout is the writer's.
#[cfg(target_os = "macos")]
fn put_seed_lease(tree: &Path, fields: &[Field<'_>]) -> PathBuf {
    let lease = build_helper::trust_repo_lock::BuildLease::acquire_independent(
        tree,
        SEED_SOURCE,
        "bootstrap stage-1 seed",
    )
    .unwrap();
    let directory = tree.join(".trust-build-lock");
    let written = fs::read_to_string(directory.join("info")).unwrap();
    drop(lease);
    assert!(!directory.exists());
    let mut record = String::new();
    for line in written.lines() {
        let key = line.split_once('=').unwrap().0;
        match fields.iter().find(|(name, _)| *name == key) {
            Some((name, Some(value))) => record.push_str(&format!("{name}={value}\n")),
            Some((_, None)) => {}
            None => record.push_str(&format!("{line}\n")),
        }
    }
    fs::create_dir(&directory).unwrap();
    fs::write(directory.join("info"), record).unwrap();
    directory
}

/// Trust: EW-9 (22). A lease directory's identity, and its record's identity and bytes.
#[cfg(target_os = "macos")]
type LeaseState = (u64, u64, Option<(u64, u64)>, Option<Vec<u8>>);

/// Trust: EW-9 (22). The identity and bytes of a lease: refusing a donor never reclaims,
/// removes or changes it.
#[cfg(target_os = "macos")]
fn lease_state(directory: &Path) -> LeaseState {
    use std::os::unix::fs::MetadataExt;
    let named = fs::symlink_metadata(directory).unwrap();
    let info = fs::symlink_metadata(directory.join("info")).ok();
    (
        named.dev(),
        named.ino(),
        info.as_ref().map(|info| (info.dev(), info.ino())),
        fs::read(directory.join("info")).ok(),
    )
}

/// Trust: EW-9 (22). A seed killed while it held a donor's lease leaves the lease, which
/// only the donor's next build reclaims. A donor whose lease record is that seed's and
/// proves its holder gone is refused as busy at once, not waited for a minute, and the
/// lease is left exactly as it was.
#[cfg(target_os = "macos")]
#[test]
fn a_donor_whose_seed_holder_is_gone_is_not_waited_for() {
    let Trees { _dir, donor, own, record } = trees();
    let host_dir = own.src.join(format!("build/{HOST}"));
    let (pid, start, start_utc) = reaped_process();
    let pid_text = pid.to_string();
    let lease = put_seed_lease(
        &donor.src,
        &[("pid", Some(&pid_text)), ("pstart", Some(&start)), ("pstart_utc", Some(&start_utc))],
    );
    let before = lease_state(&lease);
    match clone_from(&donor.src, &record, HOST, &host_dir) {
        Err(Refused::Busy(why)) => {
            assert!(
                why.contains(&format!("seed that held its lease (pid {pid}) is gone")),
                "{why}"
            );
            // The acquire's own refusal is kept beside the verdict.
            assert!(why.contains("cannot acquire the existing build/measurement lock"), "{why}");
        }
        Err(Refused::Held(why) | Refused::Failed(why)) => panic!("{why}"),
        Ok(_) => panic!("a donor whose lease stands was cloned"),
    }
    // As the seed's own search meets it: refused at once, not tried again after a pause.
    let (patience, pause) = (Duration::from_secs(60), Duration::from_secs(5));
    let started = std::time::Instant::now();
    let served = first_served(
        vec![(donor.src.clone(), record.clone())],
        (patience, pause),
        |tree, record| clone_from(tree, record, HOST, &host_dir).map(|_| ()),
    );
    let why = served.unwrap_err();
    assert!(why.starts_with("every matching worktree is busy") && why.contains("is gone"), "{why}");
    assert!(started.elapsed() < pause, "waited {:?} for a gone holder", started.elapsed());
    assert_eq!(lease_state(&lease), before, "the lease is never reclaimed, removed or changed");
    assert!(fs::read_dir(&host_dir).unwrap().flatten().all(|entry| entry.file_name() == "stage0"));
}

/// Trust: EW-9 (22). Any doubt keeps the wait: a live seed holder, a gone holder whose
/// record is not a seed's, and a symlinked or malformed record are each held, and each
/// lease is left exactly as it was.
#[cfg(target_os = "macos")]
#[test]
fn a_donor_whose_lease_holder_is_not_provably_a_gone_seed_is_held() {
    let Trees { _dir, donor, own, record } = trees();
    let host_dir = own.src.join(format!("build/{HOST}"));
    let held = |why: &str| match clone_from(&donor.src, &record, HOST, &host_dir) {
        Err(Refused::Held(held)) => {
            assert!(held.contains("build/measurement lock"), "{why}: {held}")
        }
        Err(Refused::Busy(busy)) => panic!("{why}: busy: {busy}"),
        Err(Refused::Failed(failed)) => panic!("{why}: {failed}"),
        Ok(_) => panic!("{why}: a donor whose lease stands was cloned"),
    };

    // A live holder: a real seed lease, held by this process.
    let live = build_helper::trust_repo_lock::BuildLease::acquire_independent(
        &donor.src,
        SEED_SOURCE,
        "bootstrap stage-1 seed",
    )
    .unwrap();
    let lease = donor.src.join(".trust-build-lock");
    let before = lease_state(&lease);
    held("a live seed holder");
    assert_eq!(lease_state(&lease), before);
    drop(live);
    assert!(!lease.exists());

    let (pid, start, start_utc) = reaped_process();
    let pid_text = pid.to_string();
    let gone = [
        ("pid", Some(pid_text.as_str())),
        ("pstart", Some(&start)),
        ("pstart_utc", Some(&start_utc)),
    ];
    let cases: [(&str, &[Field<'_>]); 3] = [
        ("another purpose", &[("purpose", Some("donor x.py"))]),
        ("no zone-free start", &[("pstart_utc", None)]),
        ("no pid", &[("pid", None)]),
    ];
    for (why, change) in cases {
        let mut fields = gone.to_vec();
        fields.retain(|(name, _)| change.iter().all(|(changed, _)| changed != name));
        fields.extend_from_slice(change);
        let lease = put_seed_lease(&donor.src, &fields);
        let before = lease_state(&lease);
        held(why);
        assert_eq!(lease_state(&lease), before, "{why}");
        fs::remove_file(lease.join("info")).unwrap();
        fs::remove_dir(&lease).unwrap();
    }

    // The seed's record of a gone holder, but not UTF-8, or reached through a link.
    let lease = put_seed_lease(&donor.src, &gone);
    let record_bytes = fs::read(lease.join("info")).unwrap();
    let mut invalid = record_bytes.clone();
    invalid.extend_from_slice(b"cmd=\xff\n");
    fs::write(lease.join("info"), &invalid).unwrap();
    let before = lease_state(&lease);
    held("a record that is not UTF-8");
    assert_eq!(lease_state(&lease), before);
    let elsewhere = donor.src.join("elsewhere-info");
    fs::write(&elsewhere, &record_bytes).unwrap();
    fs::remove_file(lease.join("info")).unwrap();
    std::os::unix::fs::symlink(&elsewhere, lease.join("info")).unwrap();
    let before = lease_state(&lease);
    held("a symlinked record");
    assert_eq!(lease_state(&lease), before);
    assert_eq!(fs::read(&elsewhere).unwrap(), record_bytes);
    // The control: the same bytes as the regular record are judged gone.
    fs::remove_file(lease.join("info")).unwrap();
    fs::write(lease.join("info"), &record_bytes).unwrap();
    match clone_from(&donor.src, &record, HOST, &host_dir) {
        Err(Refused::Busy(why)) => assert!(why.contains("is gone"), "{why}"),
        Err(Refused::Held(why) | Refused::Failed(why)) => {
            panic!("the control should be refused as a gone seed's lease: {why}")
        }
        Ok(_) => panic!("the control should be refused as a gone seed's lease; it was served"),
    }
    assert!(fs::read_dir(&host_dir).unwrap().flatten().all(|entry| entry.file_name() == "stage0"));
}

/// A run that ignores the locks removes the donor's record as it starts: one removed while
/// the clone was being made refuses the donor and leaves nothing behind.
#[cfg(target_os = "macos")]
#[test]
fn a_record_removed_while_the_clone_is_made_refuses_the_donor() {
    let Trees { _dir, donor, own, record } = trees();
    let host_dir = own.src.join(format!("build/{HOST}"));
    let donor_record = donor.src.join(format!("build/{HOST}/{RECORD}"));
    let cloned = || fs::remove_file(&donor_record).unwrap();
    match clone_from_with(&donor.src, &record, HOST, &host_dir, cloned) {
        Err(Refused::Busy(why)) => assert!(why.contains("while it was cloned"), "{why}"),
        Err(Refused::Held(why) | Refused::Failed(why)) => panic!("{why}"),
        Ok(_) => panic!("a donor whose record went away was used"),
    }
    assert!(fs::read_dir(&host_dir).unwrap().flatten().all(|entry| entry.file_name() == "stage0"));
}

/// Trust: unchanged record bytes cannot authorize a donor whose actual output
/// lock was replaced while its original descriptor remained held.
#[cfg(target_os = "macos")]
#[test]
fn a_replaced_output_lock_while_cloning_refuses_the_donor_and_discards_partials() {
    let Trees { _dir, donor, own, record } = trees();
    let host_dir = own.src.join(format!("build/{HOST}"));
    let lock = donor.src.join("build/lock");
    let cloned = || {
        fs::remove_file(&lock).unwrap();
        fs::write(&lock, b"replacement").unwrap();
    };
    match clone_from_with(&donor.src, &record, HOST, &host_dir, cloned) {
        Err(Refused::Busy(why)) => assert!(why.contains("output ownership changed"), "{why}"),
        Err(Refused::Held(why) | Refused::Failed(why)) => panic!("{why}"),
        Ok(_) => panic!("a donor with a replacement output lock was accepted"),
    }
    assert!(fs::read_dir(&host_dir).unwrap().flatten().all(|entry| entry.file_name() == "stage0"));
    assert_eq!(fs::read(&lock).unwrap(), b"replacement", "never remove another owner's sentinel");
    assert!(!donor.src.join(".trust-build-lock").exists(), "only our own holder is released");
}

/// Trust: unchanged record bytes and output ownership cannot authorize a donor
/// whose independently acquired build-tree holder has been replaced.
#[cfg(target_os = "macos")]
#[test]
fn a_replaced_build_tree_holder_while_cloning_refuses_the_donor_and_discards_partials() {
    use std::os::unix::fs::MetadataExt;

    for replace_directory in [false, true] {
        let Trees { _dir, donor, own, record } = trees();
        let host_dir = own.src.join(format!("build/{HOST}"));
        let holder = donor.src.join(".trust-build-lock");
        let cloned = || {
            let info = fs::read(holder.join("info")).unwrap();
            if replace_directory {
                fs::rename(&holder, donor.src.join("original-holder")).unwrap();
                fs::create_dir(&holder).unwrap();
            } else {
                fs::rename(holder.join("info"), donor.src.join("original-holder-info")).unwrap();
            }
            // Preserve exact diagnostic bytes: only the actually acquired
            // holder identity distinguishes this replacement from ours.
            fs::write(holder.join("info"), info).unwrap();
        };
        match clone_from_with(&donor.src, &record, HOST, &host_dir, cloned) {
            Err(Refused::Busy(why)) => {
                assert!(why.contains("build-tree ownership changed"), "{why}")
            }
            Err(Refused::Held(why) | Refused::Failed(why)) => panic!("{why}"),
            Ok(_) => panic!("a donor with a replacement build-tree holder was accepted"),
        }
        assert!(
            fs::read_dir(&host_dir).unwrap().flatten().all(|entry| entry.file_name() == "stage0")
        );
        let replacement = fs::metadata(holder.join("info")).unwrap();
        let original = fs::metadata(if replace_directory {
            donor.src.join("original-holder/info")
        } else {
            donor.src.join("original-holder-info")
        })
        .unwrap();
        assert_ne!((original.dev(), original.ino()), (replacement.dev(), replacement.ino()));
        assert_eq!(
            fs::read(holder.join("info")).unwrap(),
            fs::read(if replace_directory {
                donor.src.join("original-holder/info")
            } else {
                donor.src.join("original-holder-info")
            })
            .unwrap(),
            "never remove or rewrite a replacement holder"
        );
    }
}

/// A donor held by another seed is waited for a while; one whose record changed is not,
/// and a failure ends the search.
#[test]
fn a_held_donor_is_tried_again_and_a_changed_one_is_not() {
    let candidates = vec![
        (PathBuf::from("/w/changed"), record(Path::new("/w/changed"))),
        (PathBuf::from("/w/held"), record(Path::new("/w/held"))),
    ];
    let patience = (Duration::from_secs(5), Duration::from_millis(1));
    let mut tries = Vec::new();
    let served = first_served(candidates.clone(), patience, |tree, _| {
        tries.push(tree.to_owned());
        match tree.to_str().unwrap() {
            "/w/changed" => Err(Refused::Busy("its record changed".into())),
            _ if tries.len() < 4 => Err(Refused::Held("its bootstrap holds build/lock".into())),
            _ => Ok("served"),
        }
    });
    assert_eq!(served, Ok("served"));
    let held = PathBuf::from("/w/held");
    assert_eq!(tries, [PathBuf::from("/w/changed"), held.clone(), held.clone(), held]);

    let none = (Duration::ZERO, Duration::from_millis(1));
    let busy = first_served(candidates.clone(), none, |_, _| -> Result<(), _> {
        Err(Refused::Held("held".into()))
    });
    assert!(busy.unwrap_err().starts_with("every matching worktree is busy"));
    let failed = first_served(candidates, patience, |_, _| -> Result<(), _> {
        Err(Refused::Failed("cannot clone".into()))
    });
    assert_eq!(failed, Err("cannot clone".to_owned()));
}

#[cfg(target_os = "macos")]
#[test]
fn an_interrupted_seed_is_undone() {
    let dir = TempDir::new().unwrap();
    let host_dir = dir.path();
    fs::create_dir_all(host_dir.join("stage1-rustc/release")).unwrap();
    fs::create_dir_all(host_dir.join(format!("stage1-std{PARTIAL}"))).unwrap();
    fs::create_dir_all(host_dir.join("stage0")).unwrap();
    fs::write(host_dir.join(CARRIED_TIMES), "trust-carried-times/v1\n").unwrap();
    fs::write(host_dir.join(INCOMPLETE), "stage1-rustc\nstage0").unwrap();
    undo_incomplete(host_dir);
    let left: Vec<_> = fs::read_dir(host_dir).unwrap().flatten().map(|e| e.file_name()).collect();
    assert_eq!(left, ["stage0"], "only the entries a seed makes are removed, its table with them");
}

/// Every invocation removes the record; only one holding the tree's lock undoes a seed,
/// which may be in progress under that lock. A table outlives its seed only while a
/// seeded entry is left to use it.
#[test]
fn only_a_run_holding_the_lock_undoes_a_seed() {
    let dir = TempDir::new().unwrap();
    let host_dir = dir.path();
    let partial = host_dir.join(format!("stage1-rustc{PARTIAL}"));
    fs::create_dir_all(&partial).unwrap();
    fs::write(host_dir.join(RECORD), "").unwrap();
    fs::write(host_dir.join(CARRIED_TIMES), "").unwrap();
    reset(host_dir, false);
    assert!(!host_dir.join(RECORD).exists());
    assert!(partial.exists() && host_dir.join(CARRIED_TIMES).exists(), "a bypassing run");
    reset(host_dir, true);
    assert!(!partial.exists() && !host_dir.join(CARRIED_TIMES).exists());

    fs::create_dir_all(host_dir.join("stage1-std")).unwrap();
    fs::write(host_dir.join(CARRIED_TIMES), "").unwrap();
    reset(host_dir, true);
    assert!(host_dir.join(CARRIED_TIMES).exists(), "the seeded entries still read it");
    fs::remove_dir_all(host_dir.join("stage1-std")).unwrap();
    reset(host_dir, true);
    assert!(!host_dir.join(CARRIED_TIMES).exists(), "no seeded entry is left to read it");
}

/// Targo is given the table only for the target directories a seed clones.
#[test]
fn only_a_cloned_target_directory_reads_the_table() {
    let dir = TempDir::new().unwrap();
    let host_dir = dir.path();
    assert_eq!(carried_times(&host_dir.join("stage1-rustc")), None);
    fs::write(host_dir.join(CARRIED_TIMES), "").unwrap();
    for cloned in ["stage1-rustc", "stage1-std", "bootstrap-tools"] {
        assert_eq!(carried_times(&host_dir.join(cloned)), Some(host_dir.join(CARRIED_TIMES)));
    }
    for other in ["stage0-rustc", "stage2-std", "stage1"] {
        assert_eq!(carried_times(&host_dir.join(other)), None, "{other}");
    }
}

#[test]
fn the_relocation_record_is_the_one_targo_writes_for_canonical_roots() {
    let roots = Roots { src: "/w/a".into(), git_dir: Some("/g/worktrees/a".into()) };
    assert_eq!(relocation_record(&roots), b"trust-relocation-roots-v1\0/w/a\0\0/g/worktrees/a\0\0");
    let one = Roots { src: "/w/a".into(), git_dir: None };
    assert_eq!(relocation_record(&one), b"trust-relocation-roots-v1\0/w/a\0\0");
}

/// A record names the sources as the build began; one edited while it built is not
/// recorded.
#[test]
fn a_build_whose_sources_moved_while_it_ran_is_not_recorded() {
    git_test(|ctx| {
        ctx.write("compiler/rustc/src/main.rs", "fn main() {}");
        ctx.commit();
        let tree = ctx.get_path().canonicalize().unwrap();
        let config = tree.join("bootstrap.toml");
        // The identity as bootstrap named it when it began, in its own execution context
        // (whose `git` answers are cached for the rest of the run).
        let exec = ExecutionContext::new(0, false);
        let digest = trust_source_identity::config_digest(Some(&config), &tree);
        let named = trust_source_identity::of_sources(&exec, &tree, &digest, &head(ctx, &tree));
        let identity = named.unwrap().info.sha;
        let moved =
            |identity: &str| sources_moved_at(&tree, Some(&config), &head(ctx, &tree), identity);
        assert_eq!(moved(&identity), None);
        fs::write(tree.join("compiler/rustc/src/main.rs"), "fn main() { () }").unwrap();
        assert_eq!(moved(&identity).as_deref(), Some("the sources changed while it built"));
        // The control: the run's own context still answers as it began.
        let cached = trust_source_identity::of_sources(&exec, &tree, &digest, &head(ctx, &tree));
        assert_eq!(cached.unwrap().info.sha, identity, "bootstrap's git answers are cached");
    });
}

#[test]
fn the_version_stamp_is_what_e0514_compares() {
    let vv =
        "rustc 1.101.0-dev (c50c1e566 2026-11-05) (trustc 0.12.0+gc50c1e566)\nbinary: trustc\n";
    assert_eq!(version_stamp(vv), Some("rustc 1.101.0-dev (c50c1e566 2026-11-05)"));
    assert_eq!(version_stamp("binary: trustc\n"), None);
    assert_eq!(version_stamp(""), None);
}

#[cfg(unix)]
#[test]
fn a_stage1_whose_compiler_refuses_its_std_is_never_recorded() {
    use std::os::unix::fs::PermissionsExt;
    let dir = TempDir::new().unwrap();
    let stage1 = dir.path().join("stage1");
    let lib = stage1.join(format!("lib/rustlib/{HOST}/lib"));
    fs::create_dir_all(stage1.join("bin")).unwrap();
    fs::create_dir_all(&lib).unwrap();
    let rustc = stage1.join("bin/rustc");
    fs::write(
        &rustc,
        "#!/bin/sh\necho 'rustc 1.101.0-dev (c50c1e566 2026-11-05) (trustc 0.12.0)'\n",
    )
    .unwrap();
    fs::set_permissions(&rustc, fs::Permissions::from_mode(0o755)).unwrap();
    let why = stage1_sysroot_mismatch(dir.path(), HOST).unwrap();
    assert!(why.ends_with("holds no std"), "a stage 1 with no std is not one: {why}");

    let current = b"rust\0\0\0\x0arustc 1.101.0-dev (c50c1e566 2026-11-05)\0std";
    fs::write(lib.join("libstd-0123456789abcdef.rlib"), current).unwrap();
    let why = stage1_sysroot_mismatch(dir.path(), HOST).unwrap();
    assert!(why.ends_with("holds no core"), "{why}");
    fs::write(lib.join("libcore-0123456789abcdef.rlib"), current).unwrap();
    assert_eq!(stage1_sysroot_mismatch(dir.path(), HOST), None);

    // The previous compiler's std, left beside a rebuilt compiler (E0514).
    let previous = b"rust\0\0\0\x0arustc 1.101.0-dev (ba01f3085 2026-11-05)\0std";
    fs::write(lib.join("libstd-0123456789abcdef.rlib"), previous).unwrap();
    let why = stage1_sysroot_mismatch(dir.path(), HOST).unwrap();
    assert!(why.contains("libstd-0123456789abcdef.rlib was not built by"), "{why}");

    fs::write(&rustc, "#!/bin/sh\nexit 1\n").unwrap();
    assert_eq!(
        stage1_sysroot_mismatch(dir.path(), HOST).as_deref(),
        Some("the stage-1 compiler does not run")
    );
}

/// Carrying times makes git's cached stat data stale; the seed refreshes every index at
/// once, so a later `git status` (the record's identity, a build script's dirty check)
/// does not rewrite an index a build script watches.
#[test]
fn carried_times_leave_no_index_for_a_later_git_status_to_rewrite() {
    git_test(|ctx| {
        let sub_repo = TempDir::new().unwrap();
        let sub = |args: &[&str]| {
            let status = std::process::Command::new("git")
                .args([
                    "-c",
                    "user.name=t",
                    "-c",
                    "user.email=t@t",
                    "-c",
                    "init.defaultBranch=main",
                ])
                .args(args)
                .current_dir(sub_repo.path())
                .status()
                .unwrap();
            assert!(status.success(), "{args:?}");
        };
        sub(&["init", "-q"]);
        fs::write(sub_repo.path().join("lib.rs"), "pub fn f() {}").unwrap();
        sub(&["add", "lib.rs"]);
        sub(&["commit", "-q", "-m", "sub"]);
        ctx.write("compiler/rustc/src/main.rs", "fn main() {}");
        ctx.commit();
        ctx.run_git(&[
            "-c",
            "protocol.file.allow=always",
            "submodule",
            "add",
            "-q",
            sub_repo.path().to_str().unwrap(),
            "first-party/sub",
        ]);
        ctx.commit();
        let root = ctx.get_path().canonicalize().unwrap();
        let index_of = |dir: &str| {
            let out = ctx.run_git(&[
                "-C",
                root.join(dir).to_str().unwrap(),
                "rev-parse",
                "--git-path",
                "index",
            ]);
            let path = PathBuf::from(out.trim());
            if path.is_absolute() { path } else { root.join(dir).join(path) }
        };
        let indexes = [index_of("."), index_of("first-party/sub")];
        let modified = |path: &Path| fs::metadata(path).unwrap().modified().unwrap();
        // Every tracked file, as a seeded tree's are: one only milliseconds older than its
        // index is racily clean, and git rewrites the index for that whatever the seed does.
        let carry = || {
            let old = SystemTime::UNIX_EPOCH + Duration::from_secs(1_600_000_000);
            for dir in [".", "first-party/sub"] {
                let listed = ctx.run_git(&["-C", root.join(dir).to_str().unwrap(), "ls-files"]);
                for file in listed.lines().filter(|file| *file != "first-party/sub") {
                    let path = root.join(dir).join(file);
                    fs::File::options().write(true).open(path).unwrap().set_modified(old).unwrap();
                }
            }
        };
        let status_rewrites = || {
            let before = indexes.each_ref().map(|index| modified(index));
            for dir in [".", "first-party/sub"] {
                ctx.run_git(&["-C", root.join(dir).to_str().unwrap(), "status", "--porcelain"]);
            }
            indexes.iter().zip(before).filter(|(index, before)| modified(index) != *before).count()
        };

        carry();
        assert_eq!(status_rewrites(), 2, "control: stale stat data makes git status rewrite both");

        carry();
        assert_eq!(refresh_indexes(&root), Vec::<String>::new());
        assert_eq!(status_rewrites(), 0, "a refreshed index is left as it is");
    });
}
