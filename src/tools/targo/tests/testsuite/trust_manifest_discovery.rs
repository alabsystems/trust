//! Trust: a `[trust]` table is policy only for the workspace being built, and a
//! broken manifest is fatal in a manifest the build uses and silent in one git
//! discovery merely walked past.
//!
//! A manifest keeps its `[trust]` table as written, and `Workspace` reads it,
//! strictly, for its root and its members alone: a misspelled or retired key
//! there is refused by name. The same key in a path dependency that belongs to
//! another workspace, in that workspace's root, or in a git dependency is never
//! read, as Cargo ignores `[profile]` outside the root. Trust's own workspaces
//! are that case: they path-depend on the first-party siblings' crates, so they
//! read the siblings' root manifests, whose `[trust]` tables govern the
//! siblings' builds and not Trust's.
//!
//! Cargo reads every `Cargo.toml` in a git checkout to find the requested
//! package and keeps a malformed one's error for the case where the requested
//! package is not found. The diagnostic itself used to be printed at parse
//! time, so a committed fixture in a dependency's repository (first-party/ty's
//! `unknown-key` discovery control, a misspelled `[trust]` key back when every
//! manifest's table was read) put `error: unknown field` on every dependent's
//! invocation while the command exited 0. The discovery tests break a manifest
//! with a field of the wrong type instead, which fails in any manifest.

use crate::prelude::*;
use cargo_test_support::{basic_manifest, git, project, str};

/// A `[package]` manifest with a misspelled `[trust]` key.
fn misspelled_trust_manifest(name: &str) -> String {
    format!(
        r#"
            [package]
            name = "{name}"
            version = "0.1.0"
            edition = "2015"

            [trust]
            compiler_timeuot_secs = 60
        "#
    )
}

/// The `[trust]` keys BUDGET-1 retired, as the first-party siblings' root
/// manifests still declared them at the T8 pins.
const RETIRED_TRUST_KEYS: &str = "function_budget_ms = 3000\ntimeout_ms = 5000";

/// A `[package]` manifest that does not deserialize, in any workspace:
/// `autobins` must be a boolean.
fn broken_manifest(name: &str) -> String {
    format!(
        r#"
            [package]
            name = "{name}"
            version = "0.1.0"
            edition = "2015"
            autobins = "yes"
        "#
    )
}

fn depends_on_git(dep: &str, url: impl std::fmt::Display) -> String {
    format!(
        r#"
            [package]
            name = "foo"
            version = "0.1.0"
            edition = "2015"

            [dependencies]
            {dep} = {{ git = '{url}' }}
        "#
    )
}

#[cargo_test]
fn a_nested_git_fixture_with_a_broken_manifest_is_not_reported() {
    let dep = git::new("dep", |project| {
        project
            .file("Cargo.toml", &basic_manifest("dep", "0.1.0"))
            .file("src/lib.rs", "")
            .file("fixtures/broken/Cargo.toml", &broken_manifest("fixture"))
            .file("fixtures/broken/src/lib.rs", "")
    });

    let p = project()
        .file("Cargo.toml", &depends_on_git("dep", dep.url()))
        .file("src/lib.rs", "")
        .build();

    p.cargo("generate-lockfile")
        .with_stderr_data(str![[r#"
[UPDATING] git repository `[ROOTURL]/dep`
[LOCKING] 1 package to highest compatible version

"#]])
        .run();
}

/// A git dependency is not a member of the workspace being built, so its
/// `[trust]` table is not this build's policy and is never read: neither a
/// retired key nor a misspelling stops the build.
#[cargo_test]
fn a_git_dependencys_trust_table_is_not_read() {
    let dep = git::new("dep", |project| {
        project
            .file(
                "Cargo.toml",
                &format!(
                    "{}\n{RETIRED_TRUST_KEYS}\nlevl = \"L1\"\n",
                    misspelled_trust_manifest("dep")
                ),
            )
            .file("src/lib.rs", "")
    });

    let p = project()
        .file("Cargo.toml", &depends_on_git("dep", dep.url()))
        .file("src/lib.rs", "")
        .build();

    p.cargo("check")
        .with_stderr_data(str![[r#"
[UPDATING] git repository `[ROOTURL]/dep`
[LOCKING] 1 package to highest compatible version
[CHECKING] dep v0.1.0 ([ROOTURL]/dep#[..])
...
[CHECKING] foo v0.1.0 ([ROOT]/foo)
...
[FINISHED] `dev` profile [unoptimized + debuginfo] target(s) in [ELAPSED]s

"#]])
        .run();
}

#[cargo_test]
fn a_broken_selected_git_package_is_an_error() {
    let dep = git::new("dep", |project| {
        project
            .file("Cargo.toml", &broken_manifest("dep"))
            .file("src/lib.rs", "")
    });

    let p = project()
        .file("Cargo.toml", &depends_on_git("dep", dep.url()))
        .file("src/lib.rs", "")
        .build();

    p.cargo("generate-lockfile")
        .with_status(101)
        .with_stderr_data(str![[r#"
[UPDATING] git repository `[ROOTURL]/dep`
[ERROR] invalid type: string "yes", expected a boolean
 --> ../home/.cargo/git/checkouts/dep-[HASH]/[..]/Cargo.toml:6:24
  |
6 |             autobins = "yes"
  |                        ^^^^^
[ERROR] failed to get `dep` as a dependency of package `foo v0.1.0 ([ROOT]/foo)`
...
"#]])
        .run();
}

/// The selected package's manifest is unreadable but the checkout holds other,
/// readable packages, so discovery succeeds; the deferred error must still be
/// what the query for `dep` reports, not a bare "no matching package".
#[cargo_test]
fn a_broken_selected_git_package_beside_others_is_an_error() {
    let dep = git::new("dep", |project| {
        project
            .file("Cargo.toml", &broken_manifest("dep"))
            .file("src/lib.rs", "")
            .file("other/Cargo.toml", &basic_manifest("other", "0.1.0"))
            .file("other/src/lib.rs", "")
    });

    let p = project()
        .file("Cargo.toml", &depends_on_git("dep", dep.url()))
        .file("src/lib.rs", "")
        .build();

    p.cargo("generate-lockfile")
        .with_status(101)
        .with_stderr_data(str![[r#"
[UPDATING] git repository `[ROOTURL]/dep`
[ERROR] invalid type: string "yes", expected a boolean
 --> ../home/.cargo/git/checkouts/dep-[HASH]/[..]/Cargo.toml:6:24
  |
6 |             autobins = "yes"
  |                        ^^^^^
[ERROR] failed to get `dep` as a dependency of package `foo v0.1.0 ([ROOT]/foo)`
...
"#]])
        .run();
}

#[cargo_test]
fn a_misspelled_trust_key_in_a_workspace_member_is_an_error() {
    let p = project()
        .file(
            "Cargo.toml",
            r#"
                [workspace]
                members = ["member"]
            "#,
        )
        .file("member/Cargo.toml", &misspelled_trust_manifest("member"))
        .file("member/src/lib.rs", "")
        .build();

    p.cargo("generate-lockfile")
        .with_status(101)
        .with_stderr_data(str![[r#"
[ERROR] unknown field `compiler_timeuot_secs`, expected one of `enabled`, `level`, `effort`, `backstop`, `skip_functions`, `codegen_backend`, `hardened`, `trust_profile`, `intent`, `require_dep_evidence`
 --> member/Cargo.toml:8:13
  |
8 |             compiler_timeuot_secs = 60
  |             ^^^^^^^^^^^^^^^^^^^^^
...
"#]])
        .run();
}

/// A workspace member's `[trust]` table is policy, so a retired key in it is
/// refused by name, as any unknown key is.
#[cargo_test]
fn a_retired_trust_key_in_a_workspace_member_is_an_error() {
    let p = project()
        .file(
            "Cargo.toml",
            r#"
                [workspace]
                members = ["member"]
            "#,
        )
        .file(
            "member/Cargo.toml",
            &format!(
                "{}\n[trust]\n{RETIRED_TRUST_KEYS}\n",
                basic_manifest("member", "0.1.0")
            ),
        )
        .file("member/src/lib.rs", "")
        .build();

    p.cargo("generate-lockfile")
        .with_status(101)
        .with_stderr_data(str![[r#"
[ERROR] unknown field `function_budget_ms`, expected one of `enabled`, `level`, `effort`, `backstop`, `skip_functions`, `codegen_backend`, `hardened`, `trust_profile`, `intent`, `require_dep_evidence`
 --> member/Cargo.toml:9:1
  |
9 | function_budget_ms = 3000
  | ^^^^^^^^^^^^^^^^^^
[ERROR] failed to read the `[trust]` policy of workspace member `[ROOT]/foo/member/Cargo.toml`

"#]])
        .run();
}

/// T7b: `compiler_timeout_secs` folded into `backstop`. A member's table that
/// still names it is refused at the key, naming the replacement -- not as an
/// unknown field, which a newer `targo` would otherwise read as "this toolchain
/// predates the key".
#[cargo_test]
fn a_key_retired_into_another_is_refused_naming_its_replacement() {
    let p = project()
        .file(
            "Cargo.toml",
            r#"
                [workspace]
                members = ["member"]
            "#,
        )
        .file(
            "member/Cargo.toml",
            &format!(
                "{}\n[trust]\ncompiler_timeout_secs = 72000\n",
                basic_manifest("member", "0.1.0")
            ),
        )
        .file("member/src/lib.rs", "")
        .build();

    p.cargo("generate-lockfile")
        .with_status(101)
        .with_stderr_data(str![[r#"
[ERROR] `[trust]` key `compiler_timeout_secs` was retired on 2026-10-11: `[trust] backstop` in the workspace root's table is the one wall-clock backstop, [..]
 --> member/Cargo.toml:9:1
  |
9 | compiler_timeout_secs = 72000
  | ^^^^^^^^^^^^^^^^^^^^^
[ERROR] failed to read the `[trust]` policy of workspace member `[ROOT]/foo/member/Cargo.toml`

"#]])
        .run();
}

/// The workspace root's `[trust]` table is policy too: a virtual root that
/// declares a retired key is refused by name.
#[cargo_test]
fn a_retired_trust_key_in_the_workspace_root_is_an_error() {
    let p = project()
        .file(
            "Cargo.toml",
            &format!("[workspace]\nmembers = [\"member\"]\n\n[trust]\n{RETIRED_TRUST_KEYS}\n"),
        )
        .file("member/Cargo.toml", &basic_manifest("member", "0.1.0"))
        .file("member/src/lib.rs", "")
        .build();

    p.cargo("generate-lockfile")
        .with_status(101)
        .with_stderr_data(str![[r#"
[ERROR] unknown field `function_budget_ms`, expected one of `enabled`, `level`, `effort`, `backstop`, `skip_functions`, `codegen_backend`, `hardened`, `trust_profile`, `intent`, `require_dep_evidence`
 --> Cargo.toml:5:1
  |
5 | function_budget_ms = 3000
  | ^^^^^^^^^^^^^^^^^^
[ERROR] failed to read the `[trust]` policy of the workspace root `[ROOT]/foo/Cargo.toml`

"#]])
        .run();
}

/// A path dependency's own workspace: a virtual root whose `[trust]` table
/// carries the retired keys and a budget, and a member `bar` that inherits its
/// version from that root and declares retired and misspelled keys of its
/// own. The first-party siblings have this shape at the T8 pins.
fn other_workspace(
    project: cargo_test_support::ProjectBuilder,
) -> cargo_test_support::ProjectBuilder {
    project
        .file(
            "Cargo.toml",
            &format!(
                "[workspace]\nmembers = [\"crates/bar\"]\n\n\
                 [workspace.package]\nversion = \"0.1.0\"\n\n\
                 [trust]\n{RETIRED_TRUST_KEYS}\neffort = 99\nbackstop = 500\n"
            ),
        )
        .file(
            "crates/bar/Cargo.toml",
            &format!(
                "[package]\nname = \"bar\"\nversion.workspace = true\nedition = \"2015\"\n\n\
                 [trust]\n{RETIRED_TRUST_KEYS}\nlevl = \"L1\"\neffort = 98\n"
            ),
        )
        .file("crates/bar/src/lib.rs", "")
}

/// A package `name` that depends on `bar` at `bar_path`, with `trust` as its
/// `[trust]` table when given.
fn depends_on_path(name: &str, bar_path: &str, trust: Option<&str>) -> String {
    let trust = trust
        .map(|trust| format!("\n[trust]\n{trust}\n"))
        .unwrap_or_default();
    format!(
        "[package]\nname = \"{name}\"\nversion = \"0.1.0\"\nedition = \"2015\"\n\n\
         [dependencies]\nbar = {{ path = \"{bar_path}\" }}\n{trust}"
    )
}

/// A path dependency outside the workspace belongs to another workspace, so
/// neither its `[trust]` table nor its workspace root's is this build's
/// policy: the retired keys in both are never read, and the build loads and
/// builds.
#[cargo_test]
fn a_path_dependency_in_another_workspace_is_not_read_as_policy() {
    let _other = other_workspace(project().at("other")).build();

    let p = project()
        .file(
            "Cargo.toml",
            &depends_on_path("foo", "../other/crates/bar", None),
        )
        .file("src/lib.rs", "")
        .build();

    p.cargo("metadata --format-version 1").run();
    p.cargo("check")
        .with_stderr_data(str![[r#"
[CHECKING] bar v0.1.0 ([ROOT]/other/crates/bar)
...
[CHECKING] foo v0.1.0 ([ROOT]/foo)
...
[FINISHED] `dev` profile [unoptimized + debuginfo] target(s) in [ELAPSED]s

"#]])
        .run();
}

/// Trust's own layout: the other workspace sits beneath this workspace's root
/// but is excluded from it (`first-party/*`), so it is still not a member and
/// its tables are still not read.
#[cargo_test]
fn an_excluded_nested_workspace_is_not_read_as_policy() {
    let p = project()
        .file(
            "Cargo.toml",
            "[workspace]\nmembers = [\"app\"]\nexclude = [\"first-party\"]\n",
        )
        .file(
            "app/Cargo.toml",
            &depends_on_path("app", "../first-party/other/crates/bar", None),
        )
        .file("app/src/lib.rs", "")
        .build();
    let _other = other_workspace(project().at("foo/first-party/other")).build();

    p.cargo("metadata --format-version 1").run();
    p.cargo("check")
        .with_stderr_data(str![[r#"
[CHECKING] bar v0.1.0 ([ROOT]/foo/first-party/other/crates/bar)
...
[CHECKING] app v0.1.0 ([ROOT]/foo/app)
...
[FINISHED] `dev` profile [unoptimized + debuginfo] target(s) in [ELAPSED]s

"#]])
        .run();
}

/// The workspace root's budget is this build's policy: `effort` and
/// `backstop` are read from its table.
#[cargo_test]
fn the_roots_effort_and_backstop_are_this_builds_policy() {
    let p = project()
        .file(
            "Cargo.toml",
            &format!(
                "{}\n[trust]\neffort = 6\nbackstop = 2000\n",
                basic_manifest("foo", "0.1.0")
            ),
        )
        .file("src/lib.rs", "")
        .build();

    p.cargo("check")
        .with_stderr_data(str![[r#"
[NOTE] this project declares a Trust policy that an unverified build does not apply: effort = 6, backstop = 2000 (from [ROOT]/foo/Cargo.toml)
[CHECKING] foo v0.1.0 ([ROOT]/foo)
...
[FINISHED] `dev` profile [unoptimized + debuginfo] target(s) in [ELAPSED]s

"#]])
        .run();
}

/// A virtual root whose table writes `level = "L1"`, `effort = 7` and
/// `backstop = 2000`, and a member `b` whose own table is `member_trust`, or
/// which has none.
fn root_policy_workspace(member_trust: Option<&str>) -> cargo_test_support::Project {
    let member_table = member_trust
        .map(|trust| format!("\n[trust]\n{trust}\n"))
        .unwrap_or_default();
    project()
        .file(
            "Cargo.toml",
            "[workspace]\nmembers = [\"b\"]\n\n\
             [trust]\nlevel = \"L1\"\neffort = 7\nbackstop = 2000\n",
        )
        .file(
            "b/Cargo.toml",
            &format!("{}{member_table}", basic_manifest("b", "0.1.0")),
        )
        .file("b/src/lib.rs", "")
        .build()
}

/// The refusal of member `b`'s own table, naming `keys`.
fn member_table_refused(keys: &str) -> String {
    format!(
        "[ERROR] failed to read the `[trust]` policy of workspace member `[ROOT]/foo/b/Cargo.toml`

Caused by:
  this workspace member declares a `[trust]` table ({keys}), but `[trust]` is workspace policy: one workspace has one policy, the workspace root's, whichever member a command starts in or selects. Move it to the workspace root's `[trust]` table in `[ROOT]/foo/Cargo.toml`, or make this package a workspace of its own
"
    )
}

/// One workspace, one policy: the root's (DECISION_QUEUE T7c-4). A member's
/// own `[trust]` table is refused, naming its keys, whichever package the
/// command selects: from the root, with `-p b`, and from the member's own
/// directory. `targo trust` run from the root, or with `--workspace`, reads
/// only the root's table, so before this refusal a member's table governed a
/// run started in it and was silently ignored by every other run. The budget
/// keys were the first refused this way (BUDGET-1); now every key is.
#[cargo_test]
fn a_members_trust_table_is_refused() {
    let p = root_policy_workspace(Some("effort = 99\nbackstop = 500"));
    let refused = member_table_refused("`effort`, `backstop`");
    p.cargo("generate-lockfile")
        .with_status(101)
        .with_stderr_data(refused.clone())
        .run();
    p.cargo("check -p b")
        .with_status(101)
        .with_stderr_data(refused.clone())
        .run();
    p.cargo("check")
        .cwd("b")
        .with_status(101)
        .with_stderr_data(refused)
        .run();

    // A key that is not a budget, and an empty table, are refused alike.
    let level = root_policy_workspace(Some("level = \"L0\""));
    level
        .cargo("metadata --format-version 1")
        .with_status(101)
        .with_stderr_data(member_table_refused("`level`"))
        .run();
    let empty = root_policy_workspace(Some(""));
    empty
        .cargo("check --workspace")
        .with_status(101)
        .with_stderr_data(member_table_refused("no keys"))
        .run();
}

/// The refusal of a deprecated `trust.toml` beside member `b`, naming `keys`.
fn member_trust_file_refused(keys: &str) -> String {
    format!(
        "[ERROR] failed to read the `[trust]` policy of workspace member `[ROOT]/foo/b/Cargo.toml`

Caused by:
  this workspace member has a deprecated `trust.toml` beside its manifest (`[ROOT]/foo/b/trust.toml`: {keys}), but `[trust]` is workspace policy: one workspace has one policy, the workspace root's, whichever member a command starts in or selects. Move its keys to the workspace root's `[trust]` table in `[ROOT]/foo/Cargo.toml`, or make this package a workspace of its own
"
    )
}

/// A deprecated `trust.toml` beside a member is the member's own policy as
/// much as a `[trust]` table in its manifest is (DECISION_QUEUE T7c-4), and
/// it is refused alike, whichever package the command selects. `targo trust`
/// refuses it when a run starts in the member; a run from the root, with
/// `--workspace` (the A9 call) or `-p b`, reads only the root's policy, so
/// before this refusal the member's `level = "L0"` governed one run and was
/// silently ignored by the next.
#[cargo_test]
fn a_members_trust_toml_is_refused() {
    let p = root_policy_workspace(None);
    p.change_file("b/trust.toml", "level = \"L0\"\nhardened = false\n");
    let refused = member_trust_file_refused("`level`, `hardened`");
    p.cargo("check --workspace")
        .with_status(101)
        .with_stderr_data(refused.clone())
        .run();
    p.cargo("check -p b")
        .with_status(101)
        .with_stderr_data(refused.clone())
        .run();
    p.cargo("metadata --format-version 1")
        .with_status(101)
        .with_stderr_data(refused.clone())
        .run();
    p.cargo("check")
        .cwd("b")
        .with_status(101)
        .with_stderr_data(refused)
        .run();

    // An empty file, and one that is not TOML, are refused alike.
    p.change_file("b/trust.toml", "");
    p.cargo("check --workspace")
        .with_status(101)
        .with_stderr_data(member_trust_file_refused("no keys"))
        .run();
    p.change_file("b/trust.toml", "level = \n");
    p.cargo("check --workspace")
        .with_status(101)
        .with_stderr_data(member_trust_file_refused("not readable as TOML"))
        .run();
}

/// A workspace root's own `trust.toml` is the root's policy, which
/// `targo trust` reads (for one more release); it is no member's, so targo's
/// workspace load leaves it alone.
#[cargo_test]
fn the_roots_trust_toml_is_not_a_members() {
    let p = project()
        .file("Cargo.toml", "[workspace]\nmembers = [\"b\"]\n")
        .file("trust.toml", "level = \"L0\"\n")
        .file("b/Cargo.toml", &basic_manifest("b", "0.1.0"))
        .file("b/src/lib.rs", "")
        .build();
    p.cargo("check --workspace")
        .with_stderr_data(str![[r#"
[CHECKING] b v0.1.0 ([ROOT]/foo/b)
[FINISHED] `dev` profile [unoptimized + debuginfo] target(s) in [ELAPSED]s

"#]])
        .run();
}

/// A member with no table of its own runs at the root's policy, as
/// `targo trust` applies it: the policy note names the root's keys, read from
/// the root's manifest.
#[cargo_test]
fn a_member_runs_at_the_roots_policy() {
    let p = root_policy_workspace(None);

    p.cargo("check")
        .cwd("b")
        .with_stderr_data(str![[r#"
[NOTE] this project declares a Trust policy that an unverified build does not apply: level = L1, effort = 7, backstop = 2000 (from [ROOT]/foo/Cargo.toml)
[CHECKING] b v0.1.0 ([ROOT]/foo/b)
[FINISHED] `dev` profile [unoptimized + debuginfo] target(s) in [ELAPSED]s

"#]])
        .run();
}

/// A path dependency in another workspace declares `effort = 98` in its own
/// table, and its root `effort = 99` and `backstop = 500`: that budget is the
/// other workspace's. This build's policy stays the root's own (`effort = 6`,
/// `backstop = 2000`), or none at all when the root declares none.
#[cargo_test]
fn a_non_members_effort_and_backstop_are_not_this_builds_policy() {
    let _other = other_workspace(project().at("other")).build();

    let p = project()
        .file(
            "Cargo.toml",
            &depends_on_path(
                "foo",
                "../other/crates/bar",
                Some("effort = 6\nbackstop = 2000"),
            ),
        )
        .file("src/lib.rs", "")
        .build();

    p.cargo("check")
        .with_stderr_does_not_contain("[..]effort = 9[..]")
        .with_stderr_does_not_contain("[..]backstop = 500[..]")
        .with_stderr_data(str![[r#"
[NOTE] this project declares a Trust policy that an unverified build does not apply: effort = 6, backstop = 2000 (from [ROOT]/foo/Cargo.toml)
[LOCKING] 1 package to highest compatible version
[CHECKING] bar v0.1.0 ([ROOT]/other/crates/bar)
...
[CHECKING] foo v0.1.0 ([ROOT]/foo)
...
[FINISHED] `dev` profile [unoptimized + debuginfo] target(s) in [ELAPSED]s

"#]])
        .run();

    let bare = project()
        .at("bare")
        .file(
            "Cargo.toml",
            &depends_on_path("bare", "../other/crates/bar", None),
        )
        .file("src/lib.rs", "")
        .build();

    bare.cargo("check")
        .with_stderr_does_not_contain("[..]Trust policy[..]")
        .with_stderr_data(str![[r#"
[LOCKING] 1 package to highest compatible version
[CHECKING] bar v0.1.0 ([ROOT]/other/crates/bar)
...
[CHECKING] bare v0.1.0 ([ROOT]/bare)
...
[FINISHED] `dev` profile [unoptimized + debuginfo] target(s) in [ELAPSED]s

"#]])
        .run();
}

/// A path dependency *inside* the git checkout is found by the same discovery
/// walk as the fixtures, but the selected package uses it, so its broken
/// manifest must still stop the build.
#[cargo_test]
fn a_broken_manifest_in_a_git_packages_own_path_dependency_is_an_error() {
    let dep = git::new("dep", |project| {
        project
            .file(
                "Cargo.toml",
                r#"
                    [package]
                    name = "dep"
                    version = "0.1.0"
                    edition = "2015"

                    [dependencies]
                    sub = { path = "sub" }
                "#,
            )
            .file("src/lib.rs", "")
            .file("sub/Cargo.toml", &broken_manifest("sub"))
            .file("sub/src/lib.rs", "")
    });

    let p = project()
        .file("Cargo.toml", &depends_on_git("dep", dep.url()))
        .file("src/lib.rs", "")
        .build();

    p.cargo("generate-lockfile")
        .with_status(101)
        .with_stderr_data(str![[r#"
[UPDATING] git repository `[ROOTURL]/dep`
[ERROR] invalid type: string "yes", expected a boolean
 --> ../home/.cargo/git/checkouts/dep-[HASH]/[..]/sub/Cargo.toml:6:24
  |
6 |             autobins = "yes"
  |                        ^^^^^
[ERROR] failed to get `sub` as a dependency of package `dep v0.1.0 ([ROOTURL]/dep#[..])`
    ... which satisfies git dependency `dep` of package `foo v0.1.0 ([ROOT]/foo)`

Caused by:
  failed to load source for dependency `sub`

Caused by:
  unable to update [ROOTURL]/dep

"#]])
        .run();
}

/// A readable manifest elsewhere in the checkout that declares the same name
/// must not stand in for the selected package whose manifest is broken: that
/// would drop what its author wrote and switch the build to a different
/// manifest without a word.
#[cargo_test]
fn a_same_named_readable_copy_does_not_shadow_a_broken_selected_git_package() {
    let dep = git::new("dep", |project| {
        project
            .file("Cargo.toml", &broken_manifest("dep"))
            .file("src/lib.rs", "")
            .file("fixtures/copy/Cargo.toml", &basic_manifest("dep", "0.1.0"))
            .file("fixtures/copy/src/lib.rs", "")
    });

    let p = project()
        .file("Cargo.toml", &depends_on_git("dep", dep.url()))
        .file("src/lib.rs", "")
        .build();

    p.cargo("generate-lockfile")
        .with_status(101)
        .with_stderr_data(str![[r#"
[UPDATING] git repository `[ROOTURL]/dep`
[ERROR] invalid type: string "yes", expected a boolean
 --> ../home/.cargo/git/checkouts/dep-[HASH]/[..]/Cargo.toml:6:24
  |
6 |             autobins = "yes"
  |                        ^^^^^
[ERROR] failed to get `dep` as a dependency of package `foo v0.1.0 ([ROOT]/foo)`
...
"#]])
        .run();
}

/// The same shadowing through a TOML syntax error: the selected package's
/// name is still recovered from the unparsable text, so the readable copy
/// cannot stand in for it.
#[cargo_test]
fn a_same_named_readable_copy_does_not_shadow_a_selected_git_package_with_a_syntax_error() {
    let dep = git::new("dep", |project| {
        project
            .file(
                "Cargo.toml",
                r#"
                    [package]
                    name = "dep"
                    version = "0.1.0"
                    edition = "2015"

                    [dependencies
                "#,
            )
            .file("src/lib.rs", "")
            .file("fixtures/copy/Cargo.toml", &basic_manifest("dep", "0.1.0"))
            .file("fixtures/copy/src/lib.rs", "")
    });

    let p = project()
        .file("Cargo.toml", &depends_on_git("dep", dep.url()))
        .file("src/lib.rs", "")
        .build();

    p.cargo("generate-lockfile")
        .with_status(101)
        .with_stderr_data(str![[r#"
[UPDATING] git repository `[ROOTURL]/dep`
[ERROR] unclosed table, expected `]`
 --> ../home/.cargo/git/checkouts/dep-[HASH]/[..]/Cargo.toml:7:34
  |
7 |                     [dependencies
  |                                  ^
[ERROR] failed to get `dep` as a dependency of package `foo v0.1.0 ([ROOT]/foo)`
...
"#]])
        .run();
}

/// Nothing in the checkout can be read: every deferred diagnostic is shown, in
/// walk order, so the selected package's own error is not replaced by
/// whichever unrelated fixture happened to be read last.
#[cargo_test]
fn every_diagnostic_is_shown_when_no_git_package_can_be_read() {
    let dep = git::new("dep", |project| {
        project
            .file(
                "Cargo.toml",
                r#"
                    [package]
                    name = "dep"
                    version = "0.1.0"
                    edition = "2015"
                    autolib = "x"
                "#,
            )
            .file("src/lib.rs", "")
            .file("fixtures/broken/Cargo.toml", &broken_manifest("fixture"))
            .file("fixtures/broken/src/lib.rs", "")
    });

    let p = project()
        .file("Cargo.toml", &depends_on_git("dep", dep.url()))
        .file("src/lib.rs", "")
        .build();

    p.cargo("generate-lockfile")
        .with_status(101)
        .with_stderr_data(str![[r#"
[UPDATING] git repository `[ROOTURL]/dep`
[ERROR] invalid type: string "x", expected a boolean
 --> ../home/.cargo/git/checkouts/dep-[HASH]/[..]/Cargo.toml:6:31
  |
6 |                     autolib = "x"
  |                               ^^^
[ERROR] invalid type: string "yes", expected a boolean
 --> ../home/.cargo/git/checkouts/dep-[HASH]/[..]/fixtures/broken/Cargo.toml:6:24
  |
6 |             autobins = "yes"
  |                        ^^^^^
[ERROR] failed to get `dep` as a dependency of package `foo v0.1.0 ([ROOT]/foo)`
...
"#]])
        .run();
}

/// A manifest too broken to say which package it declares: when the
/// requested package is then missing from the checkout, its reason is shown
/// before the "no matching package" error instead of being lost.
#[cargo_test]
fn an_unattributable_broken_git_manifest_is_shown_when_the_package_is_missing() {
    let dep = git::new("dep", |project| {
        project
            .file(
                "Cargo.toml",
                r#"
                    [package]
                    name = dep
                    version = "0.1.0"
                "#,
            )
            .file("src/lib.rs", "")
            .file("other/Cargo.toml", &basic_manifest("other", "0.1.0"))
            .file("other/src/lib.rs", "")
    });

    let p = project()
        .file("Cargo.toml", &depends_on_git("dep", dep.url()))
        .file("src/lib.rs", "")
        .build();

    p.cargo("generate-lockfile")
        .with_status(101)
        .with_stderr_data(str![[r#"
[UPDATING] git repository `[ROOTURL]/dep`
[ERROR] string values must be quoted, expected literal string
 --> ../home/.cargo/git/checkouts/dep-[HASH]/[..]/Cargo.toml:3:28
  |
3 |                     name = dep
  |                            ^^^
[ERROR] no matching package named `dep` found
location searched: Git repository [ROOTURL]/dep
required by package `foo v0.1.0 ([ROOT]/foo)`

"#]])
        .run();
}

/// A manifest too broken to say which package it declares could be the one
/// the query selects, so it blocks even when a readable package answers the
/// query: the readable one must not stand in for it. Fail-closed by design.
#[cargo_test]
fn an_unattributable_broken_git_manifest_blocks_a_query_the_checkout_answers() {
    let dep = git::new("dep", |project| {
        project
            .file("Cargo.toml", &basic_manifest("dep", "0.1.0"))
            .file("src/lib.rs", "")
            .file(
                "fixtures/broken/Cargo.toml",
                r#"
                    [package]
                    name = unquoted
                "#,
            )
    });

    let p = project()
        .file("Cargo.toml", &depends_on_git("dep", dep.url()))
        .file("src/lib.rs", "")
        .build();

    p.cargo("generate-lockfile")
        .with_status(101)
        .with_stderr_data(str![[r#"
[UPDATING] git repository `[ROOTURL]/dep`
[ERROR] string values must be quoted, expected literal string
 --> ../home/.cargo/git/checkouts/dep-[HASH]/[..]/fixtures/broken/Cargo.toml:3:28
  |
3 |                     name = unquoted
  |                            ^^^^^^^^
[ERROR] failed to get `dep` as a dependency of package `foo v0.1.0 ([ROOT]/foo)`
...
"#]])
        .run();
}

/// A misspelled `[package]` header leaves a manifest that parses but declares
/// no package and is no workspace root either: its name cannot be
/// determined, so it could be the selected `dep` and its broken `[lib]` table
/// blocks the query rather than letting the readable copy stand in.
#[cargo_test]
fn a_manifest_with_a_misspelled_package_header_blocks_the_git_query() {
    let dep = git::new("dep", |project| {
        project
            .file(
                "Cargo.toml",
                r#"
                    [pakage]
                    name = "dep"
                    version = "0.1.0"

                    [lib]
                    test = "yes"
                "#,
            )
            .file("src/lib.rs", "")
            .file("fixtures/dep/Cargo.toml", &basic_manifest("dep", "0.1.0"))
            .file("fixtures/dep/src/lib.rs", "")
    });

    let p = project()
        .file("Cargo.toml", &depends_on_git("dep", dep.url()))
        .file("src/lib.rs", "")
        .build();

    p.cargo("generate-lockfile")
        .with_status(101)
        .with_stderr_data(str![[r#"
[UPDATING] git repository `[ROOTURL]/dep`
[ERROR] invalid type: string "yes", expected a boolean
 --> ../home/.cargo/git/checkouts/dep-[HASH]/[..]/Cargo.toml:7:28
  |
7 |                     test = "yes"
  |                            ^^^^^
[ERROR] failed to get `dep` as a dependency of package `foo v0.1.0 ([ROOT]/foo)`
...
"#]])
        .run();
}

/// A virtual workspace root declares no package, so its broken TOML can never
/// be what a query selects: a broken fixture workspace root with no members
/// stays silent.
#[cargo_test]
fn a_git_fixture_virtual_root_with_a_broken_field_is_not_reported() {
    let dep = git::new("dep", |project| {
        project
            .file("Cargo.toml", &basic_manifest("dep", "0.1.0"))
            .file("src/lib.rs", "")
            .file(
                "fixtures/ws/Cargo.toml",
                r#"
                    [workspace]
                    resolver = 2
                "#,
            )
    });

    let p = project()
        .file("Cargo.toml", &depends_on_git("dep", dep.url()))
        .file("src/lib.rs", "")
        .build();

    p.cargo("generate-lockfile")
        .with_stderr_data(str![[r#"
[UPDATING] git repository `[ROOTURL]/dep`
[LOCKING] 1 package to highest compatible version

"#]])
        .run();
}

/// A broken `[package]` manifest at `version`.
fn broken_manifest_at(name: &str, version: &str) -> String {
    broken_manifest(name).replace(r#"version = "0.1.0""#, &format!(r#"version = "{version}""#))
}

/// A git workspace whose virtual root is broken (`resolver` must be a string)
/// and whose member `a` inherits its version from that root.
const BROKEN_WORKSPACE_ROOT: &str = r#"
    [workspace]
    members = ["a"]
    exclude = ["fixtures"]
    resolver = 2

    [workspace.package]
    version = "0.1.0"
"#;

const INHERITING_MEMBER_A: &str = r#"
    [package]
    name = "a"
    version.workspace = true
    edition = "2015"
"#;

/// The selected package fails not in its own TOML but while inheriting its
/// version from a broken workspace root. That failure is attributed to `a` all
/// the same, so the readable fixture copy of `a` cannot stand in for it.
#[cargo_test]
fn a_same_named_readable_copy_does_not_shadow_a_git_member_inheriting_from_a_broken_root() {
    let dep = git::new("dep", |project| {
        project
            .file("Cargo.toml", BROKEN_WORKSPACE_ROOT)
            .file("a/Cargo.toml", INHERITING_MEMBER_A)
            .file("a/src/lib.rs", "")
            .file("fixtures/a/Cargo.toml", &basic_manifest("a", "0.1.0"))
            .file("fixtures/a/src/lib.rs", "")
    });

    let p = project()
        .file("Cargo.toml", &depends_on_git("a", dep.url()))
        .file("src/lib.rs", "")
        .build();

    p.cargo("generate-lockfile")
        .with_status(101)
        .with_stderr_data(str![[r#"
[UPDATING] git repository `[ROOTURL]/dep`
[ERROR] invalid type: integer `2`, expected a string
 --> ../home/.cargo/git/checkouts/dep-[HASH]/[..]/Cargo.toml:5:16
  |
5 |     resolver = 2
  |                ^
[ERROR] failed to get `a` as a dependency of package `foo v0.1.0 ([ROOT]/foo)`

Caused by:
  failed to load source for dependency `a`

Caused by:
  unable to update [ROOTURL]/dep

Caused by:
  failed to parse manifest at `[ROOT]/home/.cargo/git/checkouts/dep-[HASH]/[..]/a/Cargo.toml`

Caused by:
  error inheriting `version` from workspace root manifest's `workspace.package.version`
...
"#]])
        .run();
}

/// A fixture workspace in the checkout whose root is broken, with a member
/// inheriting from it: nothing asks for the member, so neither the root's own
/// failure nor the member's inherited one is printed.
#[cargo_test]
fn a_git_fixture_member_inheriting_from_a_broken_root_is_not_reported() {
    let dep = git::new("dep", |project| {
        project
            .file("Cargo.toml", &basic_manifest("dep", "0.1.0"))
            .file("src/lib.rs", "")
            .file("fixtures/ws/Cargo.toml", BROKEN_WORKSPACE_ROOT)
            .file("fixtures/ws/a/Cargo.toml", INHERITING_MEMBER_A)
            .file("fixtures/ws/a/src/lib.rs", "")
    });

    let p = project()
        .file("Cargo.toml", &depends_on_git("dep", dep.url()))
        .file("src/lib.rs", "")
        .build();

    p.cargo("generate-lockfile")
        .with_stderr_data(str![[r#"
[UPDATING] git repository `[ROOTURL]/dep`
[LOCKING] 1 package to highest compatible version

"#]])
        .run();
}

/// A broken same-named copy at a LOWER version than a valid package blocks
/// the query too. Deliberate fail-closed trade-off: attribution is by name
/// only, because the version the resolver selects cannot be predicted from
/// discovery (MSRV-aware fallback and `-Zminimal-versions` both prefer a lower
/// version; see the tests below), and every prediction tried was a fail-open.
/// A broken copy nothing would ever build is therefore an error as well.
#[cargo_test]
fn a_lower_version_broken_copy_blocks_the_git_query() {
    let dep = git::new("dep", |project| {
        project
            .file("Cargo.toml", &basic_manifest("dep", "0.1.0"))
            .file("src/lib.rs", "")
            .file(
                "fixtures/copy/Cargo.toml",
                &broken_manifest_at("dep", "0.0.1"),
            )
            .file("fixtures/copy/src/lib.rs", "")
    });

    let p = project()
        .file("Cargo.toml", &depends_on_git("dep", dep.url()))
        .file("src/lib.rs", "")
        .build();

    p.cargo("generate-lockfile")
        .with_status(101)
        .with_stderr_data(str![[r#"
[UPDATING] git repository `[ROOTURL]/dep`
[ERROR] invalid type: string "yes", expected a boolean
 --> ../home/.cargo/git/checkouts/dep-[HASH]/[..]/fixtures/copy/Cargo.toml:6:24
  |
6 |             autobins = "yes"
  |                        ^^^^^
[ERROR] failed to get `dep` as a dependency of package `foo v0.1.0 ([ROOT]/foo)`
...
"#]])
        .run();
}

/// A `dep` manifest at `version` with an optional `rust-version`, whose
/// `autobins` is `autobins` (a boolean, or a broken string).
fn dep_manifest(version: &str, rust_version: Option<&str>, autobins: &str) -> String {
    let rust_version = rust_version
        .map(|v| format!("rust-version = \"{v}\""))
        .unwrap_or_default();
    format!(
        r#"
[package]
name = "dep"
version = "{version}"
edition = "2021"
autobins = {autobins}
{rust_version}
"#
    )
}

/// An app with MSRV 1.70 under resolver 3, whose default MSRV-aware
/// `fallback` prefers a rust-version-compatible `dep` over a higher one.
fn msrv_app(url: impl std::fmt::Display) -> String {
    format!(
        r#"
            [package]
            name = "foo"
            version = "0.1.0"
            edition = "2021"
            rust-version = "1.70"
            resolver = "3"

            [dependencies]
            dep = {{ git = '{url}' }}
        "#
    )
}

const BROKEN: &str = r#""yes""#;
const READABLE: &str = "true";

/// MSRV-aware resolution selects the LOWER, compatible version: the root
/// `dep` 0.1.0 (rust-version 1.60, broken) over the readable fixture
/// `dep` 0.2.0 (rust-version 1.999). The broken manifest is the one the build
/// uses, so the higher readable copy must not take its place.
#[cargo_test]
fn msrv_fallback_selecting_a_lower_broken_git_package_is_an_error() {
    let dep = git::new("dep", |project| {
        project
            .file("Cargo.toml", &dep_manifest("0.1.0", Some("1.60"), BROKEN))
            .file("src/lib.rs", "")
            .file(
                "fixtures/dep/Cargo.toml",
                &dep_manifest("0.2.0", Some("1.999"), READABLE),
            )
            .file("fixtures/dep/src/lib.rs", "")
    });

    let p = project()
        .file("Cargo.toml", &msrv_app(dep.url()))
        .file("src/lib.rs", "")
        .build();

    p.cargo("generate-lockfile")
        .with_status(101)
        .with_stderr_data(str![[r#"
[UPDATING] git repository `[ROOTURL]/dep`
[ERROR] invalid type: string "yes", expected a boolean
 --> ../home/.cargo/git/checkouts/dep-[HASH]/[..]/Cargo.toml:6:12
  |
6 | autobins = "yes"
  |            ^^^^^
[ERROR] failed to get `dep` as a dependency of package `foo v0.1.0 ([ROOT]/foo)`
...
"#]])
        .run();
}

/// Control for the test above: readable, the same layout resolves the ROOT
/// `dep` 0.1.0, so the broken manifest is the one used.
#[cargo_test]
fn msrv_fallback_selects_the_lower_git_package_when_it_is_readable() {
    let dep = git::new("dep", |project| {
        project
            .file("Cargo.toml", &dep_manifest("0.1.0", Some("1.60"), READABLE))
            .file("src/lib.rs", "")
            .file(
                "fixtures/dep/Cargo.toml",
                &dep_manifest("0.2.0", Some("1.999"), READABLE),
            )
            .file("fixtures/dep/src/lib.rs", "")
    });

    let p = project()
        .file("Cargo.toml", &msrv_app(dep.url()))
        .file("src/lib.rs", "")
        .build();

    p.cargo("generate-lockfile").run();
    p.cargo("pkgid dep")
        .with_stdout_data(str![[r#"
git+[ROOTURL]/dep#0.1.0

"#]])
        .run();
}

/// The same with the broken copy in the fixture: the readable root `dep`
/// 0.1.0 needs Rust 1.999, so MSRV-aware fallback prefers the broken fixture
/// `dep` 0.0.1, which declares no rust-version.
#[cargo_test]
fn msrv_fallback_selecting_a_lower_broken_git_fixture_is_an_error() {
    let dep = git::new("dep", |project| {
        project
            .file(
                "Cargo.toml",
                &dep_manifest("0.1.0", Some("1.999"), READABLE),
            )
            .file("src/lib.rs", "")
            .file(
                "fixtures/copy/Cargo.toml",
                &dep_manifest("0.0.1", None, BROKEN),
            )
            .file("fixtures/copy/src/lib.rs", "")
    });

    let p = project()
        .file("Cargo.toml", &msrv_app(dep.url()))
        .file("src/lib.rs", "")
        .build();

    p.cargo("generate-lockfile")
        .with_status(101)
        .with_stderr_data(str![[r#"
[UPDATING] git repository `[ROOTURL]/dep`
[ERROR] invalid type: string "yes", expected a boolean
 --> ../home/.cargo/git/checkouts/dep-[HASH]/[..]/fixtures/copy/Cargo.toml:6:12
  |
6 | autobins = "yes"
  |            ^^^^^
[ERROR] failed to get `dep` as a dependency of package `foo v0.1.0 ([ROOT]/foo)`
...
"#]])
        .run();
}

/// Control for the test above: readable, MSRV-aware fallback locks the
/// fixture's `dep` 0.0.1.
#[cargo_test]
fn msrv_fallback_selects_the_lower_git_fixture_when_it_is_readable() {
    let dep = git::new("dep", |project| {
        project
            .file(
                "Cargo.toml",
                &dep_manifest("0.1.0", Some("1.999"), READABLE),
            )
            .file("src/lib.rs", "")
            .file(
                "fixtures/copy/Cargo.toml",
                &dep_manifest("0.0.1", None, READABLE),
            )
            .file("fixtures/copy/src/lib.rs", "")
    });

    let p = project()
        .file("Cargo.toml", &msrv_app(dep.url()))
        .file("src/lib.rs", "")
        .build();

    p.cargo("generate-lockfile").run();
    p.cargo("pkgid dep")
        .with_stdout_data(str![[r#"
git+[ROOTURL]/dep#0.0.1

"#]])
        .run();
}

/// `-Zminimal-versions` selects the lowest matching version: the broken
/// fixture `dep` 0.0.1 over the readable root `dep` 0.1.0.
#[cargo_test]
fn minimal_versions_selecting_a_lower_broken_git_fixture_is_an_error() {
    let dep = git::new("dep", |project| {
        project
            .file("Cargo.toml", &dep_manifest("0.1.0", None, READABLE))
            .file("src/lib.rs", "")
            .file(
                "fixtures/copy/Cargo.toml",
                &dep_manifest("0.0.1", None, BROKEN),
            )
            .file("fixtures/copy/src/lib.rs", "")
    });

    let p = project()
        .file("Cargo.toml", &depends_on_git("dep", dep.url()))
        .file("src/lib.rs", "")
        .build();

    p.cargo("generate-lockfile -Zminimal-versions")
        .masquerade_as_nightly_cargo(&["minimal-versions"])
        .with_status(101)
        .with_stderr_data(str![[r#"
[UPDATING] git repository `[ROOTURL]/dep`
[ERROR] invalid type: string "yes", expected a boolean
 --> ../home/.cargo/git/checkouts/dep-[HASH]/[..]/fixtures/copy/Cargo.toml:6:12
  |
6 | autobins = "yes"
  |            ^^^^^
[ERROR] failed to get `dep` as a dependency of package `foo v0.1.0 ([ROOT]/foo)`
...
"#]])
        .run();
}

/// Control for the test above: readable, `-Zminimal-versions` locks the
/// fixture's `dep` 0.0.1.
#[cargo_test]
fn minimal_versions_selects_the_lower_git_fixture_when_it_is_readable() {
    let dep = git::new("dep", |project| {
        project
            .file("Cargo.toml", &dep_manifest("0.1.0", None, READABLE))
            .file("src/lib.rs", "")
            .file(
                "fixtures/copy/Cargo.toml",
                &dep_manifest("0.0.1", None, READABLE),
            )
            .file("fixtures/copy/src/lib.rs", "")
    });

    let p = project()
        .file("Cargo.toml", &depends_on_git("dep", dep.url()))
        .file("src/lib.rs", "")
        .build();

    p.cargo("generate-lockfile -Zminimal-versions")
        .masquerade_as_nightly_cargo(&["minimal-versions"])
        .run();
    p.cargo("pkgid dep")
        .with_stdout_data(str![[r#"
git+[ROOTURL]/dep#0.0.1

"#]])
        .run();
}

/// A broken same-named copy at a HIGHER version would have been the selected
/// package had it been readable, so its error is the query's answer.
#[cargo_test]
fn a_higher_version_broken_copy_blocks_the_git_query() {
    let dep = git::new("dep", |project| {
        project
            .file("Cargo.toml", &basic_manifest("dep", "0.1.0"))
            .file("src/lib.rs", "")
            .file(
                "fixtures/copy/Cargo.toml",
                &broken_manifest_at("dep", "0.2.0"),
            )
            .file("fixtures/copy/src/lib.rs", "")
    });

    let p = project()
        .file("Cargo.toml", &depends_on_git("dep", dep.url()))
        .file("src/lib.rs", "")
        .build();

    p.cargo("generate-lockfile")
        .with_status(101)
        .with_stderr_data(str![[r#"
[UPDATING] git repository `[ROOTURL]/dep`
[ERROR] invalid type: string "yes", expected a boolean
 --> ../home/.cargo/git/checkouts/dep-[HASH]/[..]/fixtures/copy/Cargo.toml:6:24
  |
6 |             autobins = "yes"
  |                        ^^^^^
[ERROR] failed to get `dep` as a dependency of package `foo v0.1.0 ([ROOT]/foo)`
...
"#]])
        .run();
}

/// `cargo add --git` with no package named enumerates the checkout and picks
/// among what it could read. It cannot tell that the root manifest the user
/// pointed at was skipped, so that manifest's error is shown.
#[cargo_test]
fn cargo_add_from_git_shows_the_broken_manifest_it_skipped() {
    let dep = git::new("dep", |project| {
        project
            .file("Cargo.toml", &broken_manifest("dep"))
            .file("src/lib.rs", "")
            .file(
                "fixtures/helper/Cargo.toml",
                &basic_manifest("helper", "0.1.0"),
            )
            .file("fixtures/helper/src/lib.rs", "")
    });

    let p = project()
        .file("Cargo.toml", &basic_manifest("foo", "0.1.0"))
        .file("src/lib.rs", "")
        .build();

    p.cargo("add --git")
        .arg(dep.url().to_string())
        .with_stderr_data(str![[r#"
[UPDATING] git repository `[ROOTURL]/dep`
[ERROR] invalid type: string "yes", expected a boolean
 --> ../home/.cargo/git/checkouts/dep-[HASH]/[..]/Cargo.toml:6:24
  |
6 |             autobins = "yes"
  |                        ^^^^^
...
"#]])
        .run();
}

/// A `[package]` manifest whose feature enables a dependency it does not
/// declare. Its TOML is well formed; the manifest only fails when its
/// features are resolved, and that diagnostic has its own printer.
fn missing_dep_feature_manifest(name: &str) -> String {
    format!(
        r#"
            [package]
            name = "{name}"
            version = "0.1.0"
            edition = "2015"

            [features]
            f = ["nope/x"]
        "#
    )
}

/// The feature-names-a-missing-dependency diagnostic follows the same
/// deferred rule as a TOML error: a nested fixture declaring another name is
/// walked past silently, on every command that loads the checkout.
#[cargo_test]
fn a_nested_git_fixture_with_a_feature_on_a_missing_dependency_is_not_reported() {
    let dep = git::new("dep", |project| {
        project
            .file("Cargo.toml", &basic_manifest("dep", "0.1.0"))
            .file("src/lib.rs", "")
            .file(
                "fixtures/missing-dep/Cargo.toml",
                &missing_dep_feature_manifest("fixture"),
            )
            .file("fixtures/missing-dep/src/lib.rs", "")
    });

    let p = project()
        .file("Cargo.toml", &depends_on_git("dep", dep.url()))
        .file("src/lib.rs", "")
        .build();

    p.cargo("generate-lockfile")
        .with_stderr_data(str![[r#"
[UPDATING] git repository `[ROOTURL]/dep`
[LOCKING] 1 package to highest compatible version

"#]])
        .run();

    p.cargo("tree")
        .with_stdout_data(str![[r#"
foo v0.1.0 ([ROOT]/foo)
└── dep v0.1.0 ([ROOTURL]/dep#[..])

"#]])
        .with_stderr_data(str![""])
        .run();

    p.cargo("metadata --format-version 1")
        .with_stderr_data(str![""])
        .run();
}

#[cargo_test]
fn a_feature_on_a_missing_dependency_in_the_selected_git_package_is_an_error() {
    let dep = git::new("dep", |project| {
        project
            .file("Cargo.toml", &missing_dep_feature_manifest("dep"))
            .file("src/lib.rs", "")
            .file("other/Cargo.toml", &basic_manifest("other", "0.1.0"))
            .file("other/src/lib.rs", "")
    });

    let p = project()
        .file("Cargo.toml", &depends_on_git("dep", dep.url()))
        .file("src/lib.rs", "")
        .build();

    p.cargo("generate-lockfile")
        .with_status(101)
        .with_stderr_data(str![[r#"
[UPDATING] git repository `[ROOTURL]/dep`
[ERROR] feature `f` includes `nope/x`, but `nope` is not a dependency
 --> ../home/.cargo/git/checkouts/dep-[HASH]/[..]/Cargo.toml:8:17
  |
8 |             f = ["nope/x"]
  |                 ^^^^^^^^^^
[ERROR] failed to get `dep` as a dependency of package `foo v0.1.0 ([ROOT]/foo)`

Caused by:
  failed to load source for dependency `dep`

Caused by:
  unable to update [ROOTURL]/dep

Caused by:
  failed to parse manifest at `[ROOT]/home/.cargo/git/checkouts/dep-[HASH]/[..]/Cargo.toml`

"#]])
        .run();
}

#[cargo_test]
fn a_feature_on_a_missing_dependency_in_a_workspace_member_is_an_error() {
    let p = project()
        .file(
            "Cargo.toml",
            r#"
                [workspace]
                members = ["member"]
            "#,
        )
        .file("member/Cargo.toml", &missing_dep_feature_manifest("member"))
        .file("member/src/lib.rs", "")
        .build();

    p.cargo("generate-lockfile")
        .with_status(101)
        .with_stderr_data(str![[r#"
[ERROR] feature `f` includes `nope/x`, but `nope` is not a dependency
 --> member/Cargo.toml:8:17
  |
8 |             f = ["nope/x"]
  |                 ^^^^^^^^^^
[ERROR] failed to load manifest for workspace member `[ROOT]/foo/member`
referenced by workspace at `[ROOT]/foo/Cargo.toml`

Caused by:
  failed to parse manifest at `[ROOT]/foo/member/Cargo.toml`

"#]])
        .run();
}

/// A deferred root error must not leave the root's workspace half cached: a
/// member inheriting from a broken root would then load from the cache while
/// the root's own diagnostic, attributed only to the root's name, is never
/// shown. The member fails while inheriting, exactly as it does when the
/// root's TOML itself does not parse.
#[cargo_test]
fn a_git_member_inheriting_from_a_root_with_a_feature_on_a_missing_dependency_is_an_error() {
    let dep = git::new("dep", |project| {
        project
            .file(
                "Cargo.toml",
                r#"
                    [package]
                    name = "wsroot"
                    version = "0.1.0"
                    edition = "2015"

                    [workspace]
                    members = ["mem"]

                    [workspace.package]
                    version = "0.3.0"

                    [features]
                    f = ["nope/x"]
                "#,
            )
            .file("src/lib.rs", "")
            .file(
                "mem/Cargo.toml",
                r#"
                    [package]
                    name = "mem"
                    version.workspace = true
                    edition = "2015"
                "#,
            )
            .file("mem/src/lib.rs", "")
    });

    let p = project()
        .file("Cargo.toml", &depends_on_git("mem", dep.url()))
        .file("src/lib.rs", "")
        .build();

    p.cargo("generate-lockfile")
        .with_status(101)
        .with_stderr_data(str![[r#"
[UPDATING] git repository `[ROOTURL]/dep`
[ERROR] feature `f` includes `nope/x`, but `nope` is not a dependency
  --> ../home/.cargo/git/checkouts/dep-[HASH]/[..]/Cargo.toml:14:25
   |
14 |                     f = ["nope/x"]
   |                         ^^^^^^^^^^
[ERROR] failed to get `mem` as a dependency of package `foo v0.1.0 ([ROOT]/foo)`

Caused by:
  failed to load source for dependency `mem`

Caused by:
  unable to update [ROOTURL]/dep

Caused by:
  failed to parse manifest at `[ROOT]/home/.cargo/git/checkouts/dep-[HASH]/[..]/mem/Cargo.toml`

Caused by:
  error inheriting `version` from workspace root manifest's `workspace.package.version`

Caused by:
  failed searching for potential workspace
  package manifest: `[ROOT]/home/.cargo/git/checkouts/dep-[HASH]/[..]/mem/Cargo.toml`
  invalid potential workspace manifest: `[ROOT]/home/.cargo/git/checkouts/dep-[HASH]/[..]/Cargo.toml`

  [HELP] to avoid searching for a non-existent workspace, add `[workspace]` to the package manifest

Caused by:
  failed to parse manifest at `[ROOT]/home/.cargo/git/checkouts/dep-[HASH]/[..]/Cargo.toml`

"#]])
        .run();

    p.cargo("tree")
        .with_status(101)
        .with_stderr_data(str![[r#"
[UPDATING] git repository `[ROOTURL]/dep`
[ERROR] feature `f` includes `nope/x`, but `nope` is not a dependency
  --> ../home/.cargo/git/checkouts/dep-[HASH]/[..]/Cargo.toml:14:25
   |
14 |                     f = ["nope/x"]
   |                         ^^^^^^^^^^
[ERROR] failed to get `mem` as a dependency of package `foo v0.1.0 ([ROOT]/foo)`

Caused by:
  failed to load source for dependency `mem`

Caused by:
  unable to update [ROOTURL]/dep

Caused by:
  failed to parse manifest at `[ROOT]/home/.cargo/git/checkouts/dep-[HASH]/[..]/mem/Cargo.toml`

Caused by:
  error inheriting `version` from workspace root manifest's `workspace.package.version`

Caused by:
  failed searching for potential workspace
  package manifest: `[ROOT]/home/.cargo/git/checkouts/dep-[HASH]/[..]/mem/Cargo.toml`
  invalid potential workspace manifest: `[ROOT]/home/.cargo/git/checkouts/dep-[HASH]/[..]/Cargo.toml`

  [HELP] to avoid searching for a non-existent workspace, add `[workspace]` to the package manifest

Caused by:
  failed to parse manifest at `[ROOT]/home/.cargo/git/checkouts/dep-[HASH]/[..]/Cargo.toml`

"#]])
        .run();
}
