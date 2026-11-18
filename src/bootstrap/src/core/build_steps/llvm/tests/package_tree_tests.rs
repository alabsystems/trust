// Copyright 2026 Andrew Yates
// The LLVM build tree as an atpkg package (DC-16c). A builder's checkout and a worktree at
// another path each observe their own LLVM sources and form their own stamp with the LLVM
// step's functions; the builder's completed tree is laid in a store as atpkg lays a keyed tree
// (its links materialized as hard links, as `atpkg-publish pack-tree` does, a directory
// read-only), and the worktree takes it by its own key.
use std::os::unix::fs::{MetadataExt, PermissionsExt};

use super::super::reuse_evidence::{
    CmakeGeneration, FRESH_CMAKE_ROOT, begin_cmake_miss, observe_cmake_sources,
};
use super::super::source_recipe::OwnSourceGeneration;
use super::super::{SourceRecipeKey, fixture_install_manifest};
use super::*;
use crate::utils::build_stamp::BuildStamp;
use crate::utils::tests::TestCtx;

const HOST: &str = "aarch64-apple-darwin";

fn compilers() -> Compilers {
    Compilers {
        cc: "Apple clang version 17.0.0 (clang-1700.4.4.1)".into(),
        cxx: "Apple clang version 17.0.0 (clang-1700.4.4.1)".into(),
        target: "arm64-apple-macosx15.0.0".into(),
        sdk: "15.5".into(),
    }
}

/// The request the `[llvm]` table makes; the request's own independence of the checkout's
/// paths is `a_package_key_names_no_checkout_path`'s.
fn recipe() -> SourceRecipeKey {
    SourceRecipeKey { request: "c".repeat(64), dependency: "none".into(), link_shared: false }
}

/// The same LLVM sources in the checkout `checkout`.
fn lay_sources(checkout: &Path) {
    let llvm = checkout.join("src/llvm-project/llvm");
    fs::create_dir_all(llvm.join("lib/IR")).unwrap();
    fs::write(llvm.join("CMakeLists.txt"), b"project(LLVM)\n").unwrap();
    fs::write(llvm.join("lib/IR/Core.cpp"), b"int core;\n").unwrap();
    std::os::unix::fs::symlink("CMakeLists.txt", llvm.join("Alias.txt")).unwrap();
}

/// The checkout `checkout`'s LLVM step: its own source observation, its root and its stamp.
fn step(checkout: &Path) -> (OwnSourceGeneration, BuildStamp) {
    let source = checkout.join("src/llvm-project");
    let host_dir = checkout.join("build").join(HOST);
    fs::create_dir_all(&host_dir).unwrap();
    let root = host_dir.canonicalize().unwrap().join("llvm");
    let generation = OwnSourceGeneration {
        observed: observe_cmake_sources(&source, &root).unwrap(),
        source,
        anchor: checkout.join("build"),
        output: root,
    };
    assert!(generation.observed.is_some());
    let stamp = generation.stamp("llvm", HOST, Some(&recipe()));
    (generation, stamp)
}

/// The builder's own LLVM build in `checkout`, completed by the LLVM step's functions with an
/// installed link (`bin/llvm-ranlib` to `llvm-ar`, as LLVM installs it), and its key inputs.
fn build(checkout: &Path) -> String {
    lay_sources(checkout);
    let (generation, stamp) = step(checkout);
    assert!(!begin_cmake_miss(&stamp, CmakeGeneration::Known).unwrap());
    let root = &generation.output;
    for dir in ["bin", "lib", "include/llvm", "build"] {
        fs::create_dir_all(root.join(dir)).unwrap();
    }
    fs::write(root.join("bin/llvm-config"), b"#!/bin/sh\n").unwrap();
    fs::write(root.join("bin/llvm-ar"), b"the builder's llvm-ar").unwrap();
    std::os::unix::fs::symlink("llvm-ar", root.join("bin/llvm-ranlib")).unwrap();
    fs::write(root.join("lib/libLLVMCore.a"), b"archive of the builder's LLVM").unwrap();
    fs::write(root.join("include/llvm/Core.h"), b"// header\n").unwrap();
    fs::write(
        root.join("build/CMakeCache.txt"),
        format!("CMAKE_HOME_DIRECTORY={}\n", root.display()),
    )
    .unwrap();
    let members = [
        "bin/llvm-config",
        "bin/llvm-ar",
        "bin/llvm-ranlib",
        "lib/libLLVMCore.a",
        "include/llvm/Core.h",
    ]
    .map(|member| root.join(member));
    fixture_install_manifest(root, &members.iter().map(PathBuf::as_path).collect::<Vec<_>>());
    assert!(generation.complete(&stamp, || true).unwrap(), "the builder's tree completes");
    let inputs = key_inputs(HOST, &compilers(), stamp.stamp()).unwrap();
    record(root, Some(&inputs)).unwrap();
    inputs
}

/// Lays the builder's tree in the store `prefix` under its key as atpkg lays a signed tree:
/// whole, every link materialized as a hard link to its target, `include` read-only, then
/// `<key>.ready`. The builder's checkout is removed, as it is on any other Mac.
fn pack(builder: &Path, inputs: &str, prefix: &Path) -> PathBuf {
    let store = store_dir(prefix, HOST);
    fs::create_dir_all(&store).unwrap();
    let tree = store.join(key(inputs));
    let built = builder.join("build").join(HOST).join("llvm");
    let status = std::process::Command::new("cp").arg("-R").arg(&built).arg(&tree).status();
    assert!(status.unwrap().success());
    let ranlib = tree.join("bin/llvm-ranlib");
    assert!(fs::symlink_metadata(&ranlib).unwrap().file_type().is_symlink());
    fs::remove_file(&ranlib).unwrap();
    fs::hard_link(tree.join("bin/llvm-ar"), &ranlib).unwrap();
    fs::set_permissions(tree.join("include"), fs::Permissions::from_mode(0o555)).unwrap();
    fs::write(store.join(format!("{}.ready", key(inputs))), "ok\nplatform=aarch64-macos\n")
        .unwrap();
    fs::remove_dir_all(builder).unwrap();
    tree
}

/// Gives the owner back write permission on everything under the test's directory, so it is
/// removed however the test ended.
struct Writable<'a>(&'a TestCtx);

impl Drop for Writable<'_> {
    fn drop(&mut self) {
        let _ = owner_writable(self.0.dir());
    }
}

/// What the LLVM step does on a miss of `stamp` in `root` before it builds: begins the root
/// afresh, and where it did, clears it and takes the store's tree of this build's key.
fn miss_and_take(stamp: &BuildStamp, root: &Path, prefix: &Path) -> Result<Taken, String> {
    assert!(!begin_cmake_miss(stamp, CmakeGeneration::Known).unwrap(), "a fresh root");
    for entry in fs::read_dir(root).unwrap() {
        assert!(FRESH_CMAKE_ROOT.iter().any(|name| entry.as_ref().unwrap().file_name() == *name));
    }
    fs::remove_dir_all(root).unwrap();
    let inputs = key_inputs(HOST, &compilers(), stamp.stamp()).unwrap();
    take(&store_dir(prefix, HOST), &inputs, root)
}

#[test]
fn a_package_tree_seeds_llvm_when_no_worktree_matches() {
    let ctx = TestCtx::new();
    let _writable = Writable(&ctx);
    let prefix = ctx.dir().join("pkg");
    let inputs = build(&ctx.dir().join("builder"));
    let tree = pack(&ctx.dir().join("builder"), &inputs, &prefix);

    // A worktree at another path observes the same sources and forms the same key itself.
    let worktree = ctx.dir().join("Developer/worktree");
    lay_sources(&worktree);
    let (generation, stamp) = step(&worktree);
    assert_eq!(key_inputs(HOST, &compilers(), stamp.stamp()).as_deref(), Some(inputs.as_str()));
    assert!(!generation.cache_matches("llvm", &stamp, &generation.output.join("bin/llvm-config")));

    let root = generation.output.clone();
    let taken = miss_and_take(&stamp, &root, &prefix).unwrap();
    assert_eq!(taken.key, key(&inputs));
    assert_eq!(taken.files, 12);

    // The LLVM step's own reuse checks pass on the clone: the stamp is this build's, the
    // CMake generation is the stamp's, and the installed outputs it records are all there.
    assert!(generation.cache_matches("llvm", &stamp, &root.join("bin/llvm-config")));
    let manifest = fs::read_to_string(root.join("build/install_manifest.txt")).unwrap();
    assert!(manifest.lines().all(|line| line.starts_with(&format!("{}/", root.display()))));
    assert_eq!(manifest.lines().count(), 5);
    assert_eq!(fs::read_to_string(root.join(KEY_FILE)).unwrap(), inputs);
    // The clone is this worktree's own: writable where the store's is not.
    assert_eq!(fs::metadata(tree.join("include")).unwrap().permissions().mode() & 0o777, 0o555);
    assert_eq!(fs::metadata(root.join("include")).unwrap().permissions().mode() & 0o700, 0o700);
    // The take is the tree's use, which keeps it from `aterm pkg gc`.
    assert!(store_dir(&prefix, HOST).join(format!("{}.used", taken.key)).is_file());
    // Nothing is left beside it.
    let names: Vec<_> =
        fs::read_dir(root.parent().unwrap()).unwrap().flatten().map(|e| e.file_name()).collect();
    assert_eq!(names, ["llvm"]);

    // The CMake build directory the tree carries was configured in the builder's checkout,
    // which CMake refuses to reuse anywhere else: a later miss of the same generation here
    // begins the root afresh instead of keeping it.
    assert!(!begin_cmake_miss(&stamp, CmakeGeneration::Known).unwrap());
    assert!(!root.join("build").exists());
    // A build this worktree configured itself is kept by the next miss of its generation.
    fs::create_dir_all(root.join("build")).unwrap();
    assert!(begin_cmake_miss(&stamp, CmakeGeneration::Known).unwrap());
    assert!(root.join("build").is_dir());
}

#[test]
fn a_package_tree_of_another_llvm_key_builds_llvm_and_names_the_input() {
    let ctx = TestCtx::new();
    let _writable = Writable(&ctx);
    let prefix = ctx.dir().join("pkg");
    let store = store_dir(&prefix, HOST);
    let worktree = ctx.dir().join("worktree");
    lay_sources(&worktree);
    fs::write(worktree.join("src/llvm-project/llvm/lib/IR/Core.cpp"), b"int changed;\n").unwrap();
    let (generation, stamp) = step(&worktree);
    let root = generation.output.clone();
    let own = key_inputs(HOST, &compilers(), stamp.stamp()).unwrap();

    // An empty store: no tree, and it says so.
    let why = miss_and_take(&stamp, &root, &prefix).unwrap_err();
    assert!(why.contains("holds no llvm-tree at"), "{why}");
    assert!(fs::symlink_metadata(&root).is_err());

    // The store holds the tree of other LLVM sources: refused, naming the input.
    let theirs = build(&ctx.dir().join("builder"));
    pack(&ctx.dir().join("builder"), &theirs, &prefix);
    assert_ne!(key(&theirs), key(&own));
    let why = miss_and_take(&stamp, &root, &prefix).unwrap_err();
    assert!(why.contains(&format!("{} differs in source", &key(&theirs)[..12])), "{why}");
    assert!(fs::symlink_metadata(&root).is_err());

    // Other host compilers, or another deployment target or SDK, are another key, named.
    let their_stamp = stamp_of(&theirs).unwrap();
    for (other, input) in [
        (Compilers { cxx: "Apple clang version 16.0.0".into(), ..compilers() }, "cxx"),
        (Compilers { cc: "Apple clang version 16.0.0".into(), ..compilers() }, "cc"),
        (Compilers { target: "arm64-apple-macosx14.0.0".into(), ..compilers() }, "cxx-target"),
        (Compilers { sdk: "14.5".into(), ..compilers() }, "sdk"),
    ] {
        let asked = key_inputs(HOST, &other, their_stamp).unwrap();
        let why = take(&store, &asked, &root).unwrap_err();
        assert!(why.contains(&format!("differs in {input}")), "{input}: {why}");
    }

    // A tree laid under this key whose own key inputs or stamp are another tree's is refused
    // after the clone, and the clone is gone.
    let forged = store.join(key(&own));
    let status = std::process::Command::new("cp")
        .arg("-R")
        .arg(store.join(key(&theirs)))
        .arg(&forged)
        .status();
    assert!(status.unwrap().success());
    fs::write(store.join(format!("{}.ready", key(&own))), "ok\n").unwrap();
    let why = take(&store, &own, &root).unwrap_err();
    assert!(why.contains("differs in source"), "{why}");
    assert!(fs::symlink_metadata(&root).is_err());
    assert_eq!(fs::read_dir(root.parent().unwrap()).unwrap().count(), 0);

    // An unmarked tree of the key (an install atpkg has not finished) is not taken.
    fs::remove_file(store.join(format!("{}.ready", key(&own)))).unwrap();
    let why = take(&store, &own, &root).unwrap_err();
    assert!(why.contains("of this key"), "{why}");
}

/// The clone family of `path` (`ATTR_CMNEXT_CLONEID`): a copy-on-write clone shares its
/// source's, which a byte copy or a new file never does.
fn clone_id(path: &Path) -> u64 {
    use std::os::unix::ffi::OsStrExt;
    #[repr(C, packed(4))]
    struct Reply {
        length: u32,
        returned: libc::attribute_set_t,
        clone_id: u64,
    }
    let name = std::ffi::CString::new(path.as_os_str().as_bytes()).unwrap();
    let mut asked = libc::attrlist {
        bitmapcount: libc::ATTR_BIT_MAP_COUNT,
        reserved: 0,
        commonattr: libc::ATTR_CMN_RETURNED_ATTRS,
        volattr: 0,
        dirattr: 0,
        fileattr: 0,
        forkattr: libc::ATTR_CMNEXT_CLONEID,
    };
    let mut reply = std::mem::MaybeUninit::<Reply>::zeroed();
    // SAFETY: `name` is NUL-terminated, `asked` is a valid attrlist, and `reply` is a buffer
    // of the size passed, which getattrlist(2) writes at most.
    let status = unsafe {
        libc::getattrlist(
            name.as_ptr(),
            (&raw mut asked).cast(),
            reply.as_mut_ptr().cast(),
            size_of::<Reply>(),
            libc::FSOPT_ATTR_CMN_EXTENDED | libc::FSOPT_NOFOLLOW,
        )
    };
    assert_eq!(status, 0, "getattrlist {}: {}", path.display(), io::Error::last_os_error());
    // SAFETY: getattrlist succeeded and wrote the reply; it was zeroed before.
    let reply = unsafe { reply.assume_init() };
    let returned = reply.returned.forkattr;
    assert_ne!(returned & libc::ATTR_CMNEXT_CLONEID, 0, "{} has no clone id", path.display());
    reply.clone_id
}

#[test]
fn a_package_tree_is_cloned_and_never_linked() {
    let ctx = TestCtx::new();
    let _writable = Writable(&ctx);
    let prefix = ctx.dir().join("pkg");
    let inputs = build(&ctx.dir().join("builder"));
    let tree = pack(&ctx.dir().join("builder"), &inputs, &prefix);
    let dest = ctx.dir().join("worktree/build").join(HOST).join("llvm");
    fs::create_dir_all(dest.parent().unwrap()).unwrap();
    take(&store_dir(&prefix, HOST), &inputs, &dest).unwrap();

    // The store's materialized link is one inode under two names; the clone holds two files.
    let store_ar = fs::metadata(tree.join("bin/llvm-ar")).unwrap();
    assert_eq!(store_ar.nlink(), 2);
    assert_eq!(store_ar.ino(), fs::metadata(tree.join("bin/llvm-ranlib")).unwrap().ino());
    let mut compared = 0;
    for entry in walkdir::WalkDir::new(&tree) {
        let entry = entry.unwrap();
        let relative = entry.path().strip_prefix(&tree).unwrap();
        let ours = fs::symlink_metadata(dest.join(relative)).unwrap();
        let store = fs::symlink_metadata(entry.path()).unwrap();
        assert!(!ours.file_type().is_symlink(), "{} is a link", relative.display());
        assert_ne!(ours.ino(), store.ino(), "{} shares the store's inode", relative.display());
        if store.is_file() {
            assert_eq!(ours.nlink(), 1, "{} is linked", relative.display());
            compared += 1;
            if relative == Path::new("build/install_manifest.txt") {
                // The one file the take writes: its own bytes, not the store's.
                continue;
            }
            // A copy-on-write clone of the store's file: never a byte copy.
            assert_eq!(
                clone_id(&dest.join(relative)),
                clone_id(entry.path()),
                "{} is not a clone of the store's",
                relative.display()
            );
        }
    }
    assert_eq!(compared, 12);
    assert!(!fs::symlink_metadata(&dest).unwrap().file_type().is_symlink());
    // A write to the clone is the worktree's own: the store's bytes stay.
    fs::write(dest.join("lib/libLLVMCore.a"), b"rebuilt here").unwrap();
    assert_eq!(fs::read(tree.join("lib/libLLVMCore.a")).unwrap(), b"archive of the builder's LLVM");
    let manifest = fs::read_to_string(tree.join("build/install_manifest.txt")).unwrap();
    assert!(!manifest.contains("worktree"), "the store's manifest was written: {manifest}");

    // A store tree that holds a link is refused, and nothing is left at the destination.
    owner_writable(&tree).unwrap();
    std::os::unix::fs::symlink("libLLVMCore.a", tree.join("lib/libLLVM.a")).unwrap();
    let other = ctx.dir().join("second/build").join(HOST);
    fs::create_dir_all(&other).unwrap();
    let why = take(&store_dir(&prefix, HOST), &inputs, &other.join("llvm")).unwrap_err();
    assert!(why.contains("neither a file nor a directory"), "{why}");
    assert_eq!(fs::read_dir(&other).unwrap().count(), 0);
}

#[test]
fn a_clang_driver_names_its_target_and_sdk() {
    let jobs = r#"Apple clang version 21.0.0 (clang-2100.4.1.1)
 "/usr/bin/clang" "-cc1" "-triple" "arm64-apple-macosx27.2.0" "-target-sdk-version=27.2" "-x" "c++"
"#;
    assert_eq!(driver_target(jobs), ("arm64-apple-macosx27.2.0".into(), "27.2".into()));
    assert_eq!(driver_target(" \"cc1plus\" \"-quiet\"\n"), ("unreported".into(), "none".into()));
}

// The request the `[llvm]` table makes, prepared as the LLVM step prepares it, is the same
// from two checkouts: it names neither's build directory, so their trees share a key.
#[test]
fn a_package_key_names_no_checkout_path() {
    use super::super::{
        Builder, LlvmCmakeRequest, llvm_cmake_config_with_tools, llvm_output_dir, source_recipe_key,
    };
    use crate::core::session::Session;
    let request = |ctx: &TestCtx| {
        let mut session = Session::new(ctx.config("build").create_config());
        // The host's own compilers, selected as a real build selects them; nothing is run.
        crate::utils::cc_detect::fill_compilers(&mut session);
        session.config.set_dry_run(crate::core::config::DryRun::Disabled);
        let builder = Builder::new(&session);
        let target = builder.host_target;
        let native = target.to_string();
        let output = llvm_output_dir(&builder, target);
        assert!(output.starts_with(ctx.dir()), "{}", output.display());
        let source = builder.src.join("src/llvm-project/llvm");
        let request = LlvmCmakeRequest {
            source: &source,
            output: &output,
            target_native: &native,
            link_shared: false,
        };
        let recipe = llvm_cmake_config_with_tools(&builder, target, request, None).unwrap();
        let prepared = recipe.config.try_prepare().unwrap();
        // The host compilers answer what the key names of them: the deployment target the
        // driver compiles for and the SDK it compiles against.
        let compilers =
            Compilers::query(&builder.cc_tool(target), &builder.cxx_tool(target)).unwrap();
        assert!(compilers.target.contains("-apple-macosx"), "{compilers:?}");
        assert_ne!(compilers.sdk, "none", "{compilers:?}");
        (source_recipe_key(&prepared, &[], false).unwrap().request, compilers)
    };
    let (first, second) = (TestCtx::new(), TestCtx::new());
    assert_eq!(request(&first), request(&second));
}
