mod common_metadata;
// Trust: `trust_external_dependency_source` joins this family because it reads
// the same `cargo metadata` the with-deps lane already fetches.
mod external_dependency_source;
mod feature_name;
mod lint_groups_priority;
mod multiple_crate_versions;
mod wildcard_dependencies;

use cargo_metadata::MetadataCommand;
use clippy_config::Conf;
use clippy_utils::diagnostics::span_lint;
use clippy_utils::is_lint_allowed;
use rustc_data_structures::fx::FxHashSet;
use rustc_hir::hir_id::CRATE_HIR_ID;
use rustc_lint::{LateContext, LateLintPass, Lint};
use rustc_session::impl_lint_pass;
use rustc_span::DUMMY_SP;

declare_clippy_lint! {
    /// ### What it does
    /// Checks to see if all common metadata is defined in
    /// `Cargo.toml`. See: https://rust-lang-nursery.github.io/api-guidelines/documentation.html#cargotoml-includes-all-common-metadata-c-metadata
    ///
    /// ### Why is this bad?
    /// It will be more difficult for users to discover the
    /// purpose of the crate, and key information related to it.
    ///
    /// ### Example
    /// ```toml
    /// # This `Cargo.toml` is missing a description field:
    /// [package]
    /// name = "clippy"
    /// version = "0.0.212"
    /// repository = "https://github.com/rust-lang/rust-clippy"
    /// readme = "README.md"
    /// license = "MIT OR Apache-2.0"
    /// keywords = ["clippy", "lint", "plugin"]
    /// categories = ["development-tools", "development-tools::cargo-plugins"]
    /// ```
    ///
    /// Should include a description field like:
    ///
    /// ```toml
    /// # This `Cargo.toml` includes all common metadata
    /// [package]
    /// name = "clippy"
    /// version = "0.0.212"
    /// description = "A bunch of helpful lints to avoid common pitfalls in Rust"
    /// repository = "https://github.com/rust-lang/rust-clippy"
    /// readme = "README.md"
    /// license = "MIT OR Apache-2.0"
    /// keywords = ["clippy", "lint", "plugin"]
    /// categories = ["development-tools", "development-tools::cargo-plugins"]
    /// ```
    #[clippy::version = "1.32.0"]
    pub CARGO_COMMON_METADATA,
    cargo,
    "common metadata is defined in `Cargo.toml`"
}

declare_clippy_lint! {
    /// ### What it does
    /// Checks for lint groups with the same priority as lints in the `Cargo.toml`
    /// [`[lints]` table](https://doc.rust-lang.org/cargo/reference/manifest.html#the-lints-section).
    ///
    /// This lint will be removed once [cargo#12918](https://github.com/rust-lang/cargo/issues/12918)
    /// is resolved.
    ///
    /// ### Why is this bad?
    /// The order of lints in the `[lints]` is ignored, to have a lint override a group the
    /// `priority` field needs to be used, otherwise the sort order is undefined.
    ///
    /// ### Known problems
    /// Does not check lints inherited using `lints.workspace = true`
    ///
    /// ### Example
    /// ```toml
    /// # Passed as `--allow=clippy::similar_names --warn=clippy::pedantic`
    /// # which results in `similar_names` being `warn`
    /// [lints.clippy]
    /// pedantic = "warn"
    /// similar_names = "allow"
    /// ```
    /// Use instead:
    /// ```toml
    /// # Passed as `--warn=clippy::pedantic --allow=clippy::similar_names`
    /// # which results in `similar_names` being `allow`
    /// [lints.clippy]
    /// pedantic = { level = "warn", priority = -1 }
    /// similar_names = "allow"
    /// ```
    #[clippy::version = "1.78.0"]
    pub LINT_GROUPS_PRIORITY,
    correctness,
    "a lint group in `Cargo.toml` at the same priority as a lint"
}

declare_clippy_lint! {
    /// ### What it does
    /// Checks to see if multiple versions of a crate are being
    /// used.
    ///
    /// ### Why is this bad?
    /// This bloats the size of targets, and can lead to
    /// confusing error messages when structs or traits are used interchangeably
    /// between different versions of a crate.
    ///
    /// ### Known problems
    /// Because this can be caused purely by the dependencies
    /// themselves, it's not always possible to fix this issue.
    /// In those cases, you can allow that specific crate using
    /// the `allowed-duplicate-crates` configuration option.
    ///
    /// ### Example
    /// ```toml
    /// # This will pull in both winapi v0.3.x and v0.2.x, triggering a warning.
    /// [dependencies]
    /// ctrlc = "=3.1.0"
    /// ansi_term = "=0.11.0"
    /// ```
    #[clippy::version = "pre 1.29.0"]
    pub MULTIPLE_CRATE_VERSIONS,
    cargo,
    "multiple versions of the same crate being used"
}

declare_clippy_lint! {
    /// ### What it does
    /// Checks for negative feature names with prefix `no-` or `not-`
    ///
    /// ### Why is this bad?
    /// Features are supposed to be additive, and negatively-named features violate it.
    ///
    /// ### Example
    /// ```toml
    /// # The `Cargo.toml` with negative feature names
    /// [features]
    /// default = []
    /// no-abc = []
    /// not-def = []
    ///
    /// ```
    /// Use instead:
    /// ```toml
    /// [features]
    /// default = ["abc", "def"]
    /// abc = []
    /// def = []
    ///
    /// ```
    #[clippy::version = "1.57.0"]
    pub NEGATIVE_FEATURE_NAMES,
    cargo,
    "usage of a negative feature name"
}

declare_clippy_lint! {
    /// ### What it does
    /// Checks for feature names with prefix `use-`, `with-` or suffix `-support`
    ///
    /// ### Why is this bad?
    /// These prefixes and suffixes have no significant meaning.
    ///
    /// ### Example
    /// ```toml
    /// # The `Cargo.toml` with feature name redundancy
    /// [features]
    /// default = ["use-abc", "with-def", "ghi-support"]
    /// use-abc = []  // redundant
    /// with-def = []   // redundant
    /// ghi-support = []   // redundant
    /// ```
    ///
    /// Use instead:
    /// ```toml
    /// [features]
    /// default = ["abc", "def", "ghi"]
    /// abc = []
    /// def = []
    /// ghi = []
    /// ```
    ///
    #[clippy::version = "1.57.0"]
    pub REDUNDANT_FEATURE_NAMES,
    cargo,
    "usage of a redundant feature name"
}

// Trust: lint added by Trust; see docs/DESIGN_PHILOSOPHY.md §7 "we own the
// supply chain" and the lint/proof boundary in docs/TIPPY_REBRAND.md.
declare_clippy_lint! {
    /// ### What it does
    /// Reports each direct dependency that cargo resolves from outside this
    /// tree — from a registry or from a git repository — rather than from a
    /// directory in it.
    ///
    /// ### Why is this bad?
    /// Trust verifies what it compiles, and it compiles what is in the tree. A
    /// dependency fetched from a registry or a git URL arrives as a finished
    /// artifact: nothing in it states an obligation you chose, its source is
    /// not yours to annotate, and when something in it is wrong the repairs
    /// available are a version bump, a fork, or a patch section — never an edit
    /// where the defect is. The same code brought in-tree — a path dependency,
    /// a workspace member, or a vendored copy — compiles under `trustc`
    /// alongside the code you wrote, so it can carry contracts and be fixed in
    /// place.
    ///
    /// The report is a structural fact and nothing more: cargo resolves this
    /// package from a source that is not in this tree. It is not a verification
    /// result, and it is not evidence of one. A lint may report what the
    /// verifier found; a lint may never be proof authority — and lint passes
    /// run long before `TrustVerify`, so this pass cannot know whether anything
    /// about this dependency was proved, failed, or was never attempted. Read
    /// the output as an inventory of what your build pulls in from elsewhere.
    ///
    /// ### Known problems
    /// Only the direct dependencies of the package being compiled are reported.
    /// The transitive graph is usually hundreds of packages, none of which can
    /// be brought in-tree before the direct dependency that pulls it in.
    ///
    /// The package is matched to a workspace member by crate name, so a target
    /// whose crate name differs from its package name — a renamed `[[bin]]`, or
    /// a build script — reports nothing at all.
    ///
    /// A vendored directory kept outside the workspace root is still reported,
    /// because the manifest cargo reads for it is then not in this tree.
    ///
    /// ### Example
    /// ```toml
    /// [dependencies]
    /// regex = "1"
    /// ```
    /// Use instead:
    /// ```toml
    /// [dependencies]
    /// regex = { path = "vendor/regex" }
    /// ```
    #[clippy::version = "1.99.0"]
    pub TRUST_EXTERNAL_DEPENDENCY_SOURCE,
    restriction,
    "a dependency resolved from a registry or a git repository rather than from this tree"
}

declare_clippy_lint! {
    /// ### What it does
    /// Checks for wildcard dependencies in the `Cargo.toml`.
    ///
    /// ### Why is this bad?
    /// [As the edition guide says](https://rust-lang-nursery.github.io/edition-guide/rust-2018/cargo-and-crates-io/crates-io-disallows-wildcard-dependencies.html),
    /// it is highly unlikely that you work with any possible version of your dependency,
    /// and wildcard dependencies would cause unnecessary breakage in the ecosystem.
    ///
    /// ### Example
    /// ```toml
    /// [dependencies]
    /// regex = "*"
    /// ```
    /// Use instead:
    /// ```toml
    /// [dependencies]
    /// # allow patch updates, but not minor or major version changes
    /// some_crate_1 = "~1.2.3"
    ///
    /// # pin the version to a specific version
    /// some_crate_2 = "=1.2.3"
    /// ```
    #[clippy::version = "1.32.0"]
    pub WILDCARD_DEPENDENCIES,
    cargo,
    "wildcard dependencies being used"
}

impl_lint_pass!(Cargo => [
    CARGO_COMMON_METADATA,
    LINT_GROUPS_PRIORITY,
    MULTIPLE_CRATE_VERSIONS,
    NEGATIVE_FEATURE_NAMES,
    REDUNDANT_FEATURE_NAMES,
    // Trust: added with `trust_external_dependency_source`.
    TRUST_EXTERNAL_DEPENDENCY_SOURCE,
    WILDCARD_DEPENDENCIES,
]);

pub struct Cargo {
    allowed_duplicate_crates: FxHashSet<String>,
    ignore_publish: bool,
}

impl Cargo {
    pub fn new(conf: &'static Conf) -> Self {
        Self {
            allowed_duplicate_crates: conf.allowed_duplicate_crates.iter().cloned().collect(),
            ignore_publish: conf.cargo_ignore_publish,
        }
    }
}

impl LateLintPass<'_> for Cargo {
    fn check_crate(&mut self, cx: &LateContext<'_>) {
        static NO_DEPS_LINTS: &[&Lint] = &[
            CARGO_COMMON_METADATA,
            REDUNDANT_FEATURE_NAMES,
            NEGATIVE_FEATURE_NAMES,
            WILDCARD_DEPENDENCIES,
        ];
        // Trust: `trust_external_dependency_source` needs the resolved graph, not
        // the declared dependency list. A `[patch]` pointing at a local path, and
        // a `cargo vendor` source replacement, both leave the declared source
        // naming the registry they replaced; only the resolved package says where
        // cargo reads the code from.
        static WITH_DEPS_LINTS: &[&Lint] = &[MULTIPLE_CRATE_VERSIONS, TRUST_EXTERNAL_DEPENDENCY_SOURCE];

        lint_groups_priority::check(cx);

        if !NO_DEPS_LINTS
            .iter()
            .all(|&lint| is_lint_allowed(cx, lint, CRATE_HIR_ID))
        {
            match MetadataCommand::new().no_deps().exec() {
                Ok(metadata) => {
                    common_metadata::check(cx, &metadata, self.ignore_publish);
                    feature_name::check(cx, &metadata);
                    wildcard_dependencies::check(cx, &metadata);
                },
                Err(e) => {
                    for lint in NO_DEPS_LINTS {
                        span_lint(cx, lint, DUMMY_SP, format!("could not read cargo metadata: {e}"));
                    }
                },
            }
        }

        if !WITH_DEPS_LINTS
            .iter()
            .all(|&lint| is_lint_allowed(cx, lint, CRATE_HIR_ID))
        {
            match MetadataCommand::new().exec() {
                Ok(metadata) => {
                    multiple_crate_versions::check(cx, &metadata, &self.allowed_duplicate_crates);
                    // Trust: see `WITH_DEPS_LINTS` above.
                    external_dependency_source::check(cx, &metadata);
                },
                Err(e) => {
                    for lint in WITH_DEPS_LINTS {
                        span_lint(cx, lint, DUMMY_SP, format!("could not read cargo metadata: {e}"));
                    }
                },
            }
        }
    }
}
