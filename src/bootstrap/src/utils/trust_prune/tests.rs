// Trust: this file is Trust-owned. It pins the native prune of bootstrap's build trees
// (`trust_prune.rs`): every prune check of `scripts/tests/slim_build_test.py`'s
// `PruneTests`, ported, and what only the native prune does (this run's cargo reports, the
// tree stamp, the per-tree refusals). The mapping from each slim test to its port is in
// `docs/DECISION_QUEUE.md`, NATIVE-PRUNE-1.

use std::collections::BTreeMap;
use std::fs::{self, File};
use std::os::unix::fs::{PermissionsExt, symlink};
use std::path::{Path, PathBuf};
use std::time::{Duration, UNIX_EPOCH};

use super::*;

const HOST: &str = "x86_64-test-host";
const MACHO: [u8; 4] = [0xcf, 0xfa, 0xed, 0xfe];
const ELF: [u8; 4] = [0x7f, b'E', b'L', b'F'];

fn write(path: &Path, data: &[u8]) -> PathBuf {
    fs::create_dir_all(path.parent().unwrap()).unwrap();
    fs::write(path, data).unwrap();
    path.to_owned()
}

fn set_mtime(path: &Path, secs: f64) {
    let when = UNIX_EPOCH + Duration::from_secs_f64(secs);
    File::options().append(true).open(path).unwrap().set_modified(when).unwrap();
}

fn chmod(path: &Path, mode: u32) {
    fs::set_permissions(path, fs::Permissions::from_mode(mode)).unwrap();
}

fn is_root() -> bool {
    // SAFETY: geteuid has no preconditions.
    unsafe { libc::geteuid() == 0 }
}

/// A deterministic 32-bit hash, standing in for slim's `zlib.crc32`.
fn hash32(text: &str) -> u64 {
    text.bytes().fold(0x811c9dc5u64, |h, b| ((h ^ u64::from(b)) * 0x01000193) & 0xffff_ffff)
}

/// A Unix archive: BSD `#1/<len>` names as Darwin writes them, or GNU names, a long one
/// through the `//` table as `/<offset>`.
fn ar_archive(members: &[(String, Vec<u8>)], bsd: bool) -> Vec<u8> {
    let header = |name: &str, size: usize| {
        format!("{:<16}{:<12}{:<6}{:<6}{:<8}{:<10}`\n", name, "0", "0", "0", "644", size)
            .into_bytes()
    };
    let mut out = b"!<arch>\n".to_vec();
    let mut table = Vec::new();
    let mut heads = BTreeMap::new();
    if !bsd {
        for (name, _) in members {
            if name.len() > 15 {
                heads.insert(name.clone(), format!("/{}", table.len()));
                table.extend_from_slice(name.as_bytes());
                table.extend_from_slice(b"/\n");
            } else {
                heads.insert(name.clone(), format!("{name}/"));
            }
        }
        if !table.is_empty() {
            out.extend(header("//", table.len()));
            out.extend(&table);
            if table.len() % 2 == 1 {
                out.push(b'\n');
            }
        }
    }
    for (name, data) in members {
        let (head, body) = if bsd {
            let mut body = name.as_bytes().to_vec();
            body.extend(data);
            (format!("#1/{}", name.len()), body)
        } else {
            (heads[name].clone(), data.clone())
        };
        out.extend(header(&head, body.len()));
        out.extend(&body);
        if body.len() % 2 == 1 {
            out.push(b'\n');
        }
    }
    out
}

/// One unit's description; `U::default()` is a finished library with an identity.
#[derive(Clone)]
struct U {
    kind: &'static str,
    krate: Option<&'static str>,
    deps: Vec<u64>,
    depinfo: Vec<PathBuf>,
    finished: bool,
    objects: usize,
    output: &'static str,
    mtime: Option<f64>,
    profile: Option<PathBuf>,
    magic: [u8; 4],
    version: &'static str,
    features: &'static str,
    profile_hash: u64,
    identity: bool,
}

impl Default for U {
    fn default() -> Self {
        U {
            kind: "lib",
            krate: None,
            deps: Vec::new(),
            depinfo: Vec::new(),
            finished: true,
            objects: 0,
            output: "rlib",
            mtime: None,
            profile: None,
            magic: MACHO,
            version: "1.0.0",
            features: "[]",
            profile_hash: 1,
            identity: true,
        }
    }
}

/// What [`CargoTree::unit`] made.
#[derive(Clone, Debug, Default)]
struct Made {
    hash: u64,
    rlib: Option<PathBuf>,
    rmeta: Option<PathBuf>,
    dylib: Option<PathBuf>,
    bin: Option<PathBuf>,
    objects: Vec<PathBuf>,
    dir: Option<PathBuf>,
    out: PathBuf,
}

impl Made {
    fn rlib(&self) -> &Path {
        self.rlib.as_deref().unwrap()
    }
    fn bin(&self) -> &Path {
        self.bin.as_deref().unwrap()
    }
}

/// A fake cargo target tree, in the legacy (`deps/`, `.fingerprint/`) or the new
/// (`build/<pkg>/<id>/{fingerprint,out}`) layout, with what bootstrap writes beside it.
struct CargoTree {
    profile: PathBuf,
    new_layout: bool,
    next_hash: u64,
}

impl CargoTree {
    fn new(tree: &Path, target: Option<&str>, new_layout: bool) -> Self {
        write(&tree.join("CACHEDIR.TAG"), b"Signature: 8a477f597d28d172789f06886806bc55\n");
        let profile = match target {
            Some(target) => tree.join(target).join("release"),
            None => tree.join("release"),
        };
        write(&profile.join(".cargo-lock"), b"");
        CargoTree { profile, new_layout, next_hash: 0x1000 }
    }

    fn unit(&mut self, pkg: &str, uid: &str, u: U) -> Made {
        let krate = u.krate.map(str::to_owned).unwrap_or_else(|| pkg.replace('-', "_"));
        let profile = u.profile.clone().unwrap_or_else(|| self.profile.clone());
        self.next_hash += 1;
        let digest = self.next_hash;
        let (base, fingerprint, out) = if self.new_layout {
            let base = profile.join("build").join(pkg).join(uid);
            (Some(base.clone()), base.join("fingerprint"), base.join("out"))
        } else {
            (None, profile.join(".fingerprint").join(format!("{pkg}-{uid}")), profile.join("deps"))
        };
        let name = format!("{}-{krate}", u.kind);
        if u.finished {
            let hash_file = write(&fingerprint.join(&name), le_hex(digest).as_bytes());
            let deps: Vec<String> = u
                .deps
                .iter()
                .enumerate()
                .map(|(i, d)| format!("[7,\"dep{i}\",false,{d}]"))
                .collect();
            let mut json = format!("{{\"rustc\":1,\"deps\":[{}]", deps.join(","));
            if u.identity && u.kind.starts_with("run-") {
                // Cargo builds a run unit's fingerprint from `Fingerprint::new()`.
                json +=
                    ",\"path\":0,\"target\":0,\"features\":\"\",\"profile\":0,\"compile_kind\":0";
            } else if u.identity {
                json += &format!(
                    concat!(
                        ",\"path\":{},\"target\":{},\"features\":{:?},",
                        "\"profile\":{},\"compile_kind\":0"
                    ),
                    hash32(&format!("{pkg}-{}", u.version)),
                    hash32(&name),
                    u.features,
                    u.profile_hash
                );
            }
            json += "}";
            write(&fingerprint.join(format!("{name}.json")), json.as_bytes());
            if let Some(mtime) = u.mtime {
                set_mtime(&hash_file, mtime);
            }
        }
        let objects: Vec<PathBuf> = (0..u.objects)
            .map(|i| {
                let mut data = u.magic.to_vec();
                data.extend(std::iter::repeat_n(65 + i as u8, 999 + i));
                write(&out.join(format!("{krate}-{uid}.{krate}.abcd-cgu.{i:02}.rcgu.o")), &data)
            })
            .collect();
        let mut made = Made {
            hash: digest,
            objects: objects.clone(),
            dir: base,
            out: out.clone(),
            ..Made::default()
        };
        match u.output {
            "rlib" => {
                let mut members: Vec<(String, Vec<u8>)> = objects
                    .iter()
                    .map(|o| {
                        (
                            o.file_name().unwrap().to_string_lossy().into_owned(),
                            fs::read(o).unwrap(),
                        )
                    })
                    .collect();
                members.push(("lib.rmeta".into(), b"meta".to_vec()));
                made.rlib = Some(write(
                    &out.join(format!("lib{krate}-{uid}.rlib")),
                    &ar_archive(&members, true),
                ));
                write(&out.join(format!("lib{krate}-{uid}.rmeta")), b"meta");
            }
            "rmeta" => {
                made.rmeta = Some(write(&out.join(format!("lib{krate}-{uid}.rmeta")), b"meta"))
            }
            "dylib" => {
                made.dylib = Some(write(&out.join(format!("lib{krate}-{uid}.dylib")), b"dylib"))
            }
            "bin" => {
                // The legacy layout names a binary with its unit id; the new layout, inside
                // the unit's own directory, without it.
                let name = if self.new_layout {
                    krate.replace('-', "_")
                } else {
                    format!("{krate}-{uid}")
                };
                let exe = write(&out.join(name), b"#!/bin/sh\n");
                chmod(&exe, 0o755);
                made.bin = Some(exe);
            }
            _ => {}
        }
        let lines: Vec<String> = u.depinfo.iter().map(|p| p.display().to_string()).collect();
        write(
            &out.join(format!("{krate}-{uid}.d")),
            format!("{}/lib{krate}-{uid}.rlib: src/lib.rs {}\n", out.display(), lines.join(" "))
                .as_bytes(),
        );
        made
    }

    fn stamp(&self, name: &str, paths: &[&Path]) -> PathBuf {
        let mut data = Vec::new();
        for path in paths {
            data.push(b't');
            data.extend(path.as_os_str().as_bytes());
            data.push(0);
        }
        write(&self.profile.join(name), &data)
    }
}

/// A build directory: `build/<HOST>` with a stage-1 sysroot (a std hard-linked from
/// `stage1-std`'s deps, which is no unit), the trees that are never pruned, and scratch.
struct Fixture {
    _tmp: tempfile::TempDir,
    root: PathBuf,
    build: PathBuf,
    host: PathBuf,
}

impl Fixture {
    fn new() -> Self {
        let tmp = tempfile::tempdir().unwrap();
        let root = tmp.path().canonicalize().unwrap();
        let build = root.join("build");
        let host = build.join(HOST);
        let std = write(
            &host.join("stage1-std").join(HOST).join("release/deps/libstd-abc.rlib"),
            &b"std".repeat(30000),
        );
        let sysroot_std = host.join("stage1/lib/rustlib").join(HOST).join("lib/libstd-abc.rlib");
        fs::create_dir_all(sysroot_std.parent().unwrap()).unwrap();
        fs::hard_link(&std, &sysroot_std).unwrap();
        let trustc = write(&host.join("stage1/bin/trustc"), b"#!/bin/sh\necho trustc\n");
        chmod(&trustc, 0o755);
        // The compiler library, hard-linked from its rustc target tree.
        let driver = write(
            &host.join("stage1-rustc").join(HOST).join("release/deps/librustc_driver.dylib"),
            &b"driver".repeat(20000),
        );
        fs::hard_link(&driver, host.join("stage1/lib/librustc_driver.dylib")).unwrap();
        let tidy = write(&host.join("bootstrap-tools/release/tidy"), &[b'x'; 65536]);
        fs::create_dir_all(host.join("bootstrap-tools/release/deps")).unwrap();
        fs::hard_link(&tidy, host.join("bootstrap-tools/release/deps/tidy-0123")).unwrap();
        write(
            &host.join("stage1-tools").join(HOST).join("release/rustdoc_tool_binary"),
            &[b'x'; 65536],
        );
        write(&host.join("stage2-tools").join(HOST).join("release/cargo"), &[b'x'; 65536]);
        write(&host.join("stage3-tools").join(HOST).join("release/trustup"), &[b'x'; 65536]);
        for rustc in ["stage1-rustc", "stage2-rustc"] {
            write(
                &host.join(rustc).join(HOST).join("release/incremental/cache.bin"),
                &[b'x'; 65536],
            );
        }
        for (name, when) in [("old", 1_000_000.0), ("new", 2_000_000.0)] {
            let lib = write(
                &host
                    .join("rustc-private-sysroots")
                    .join(format!("rustc-private-tool-{name}"))
                    .join("lib.rlib"),
                &[b'x'; 65536],
            );
            File::open(lib.parent().unwrap())
                .unwrap()
                .set_modified(UNIX_EPOCH + Duration::from_secs_f64(when))
                .unwrap();
        }
        for keep in [
            "llvm",
            "stage0",
            "stage0-sysroot",
            "stage1-tools-bin",
            "stage2-tools-bin",
            "stage3-tools-bin",
        ] {
            write(&host.join(keep).join("keep.bin"), b"keep");
        }
        write(&build.join("tmp/scratch.bin"), b"x");
        Fixture { _tmp: tmp, root, build, host }
    }

    fn tree(&self, name: &str, target: Option<&str>, new_layout: bool) -> CargoTree {
        CargoTree::new(&self.host.join(name), target, new_layout)
    }

    fn prune(&self) -> Summary {
        prune(&self.build, &self.host, &[], &Options { objects: true, observe: None })
    }

    fn prune_with(&self, streamed: &[Streamed]) -> Summary {
        prune(&self.build, &self.host, streamed, &Options { objects: true, observe: None })
    }

    /// stage1-rustc in the new layout: a stamped compiler graph beside the dead variants
    /// older builds left.
    fn warm_compiler_tree(&self) -> (CargoTree, BTreeMap<&'static str, Made>) {
        let mut t = self.tree("stage1-rustc", Some(HOST), true);
        let mut u = BTreeMap::new();
        let script = |mtime: Option<f64>| U {
            kind: "build-script",
            krate: Some("build-script-build"),
            output: "bin",
            mtime,
            ..U::default()
        };
        u.insert("bs_compile", t.unit("serde", "c0c0c0c0c0c0c0c0", script(None)));
        let bs_compile = u["bs_compile"].hash;
        u.insert(
            "bs_run",
            t.unit(
                "serde",
                "e0e0e0e0e0e0e0e0",
                U {
                    kind: "run-build-script",
                    krate: Some("build-script-build"),
                    output: "none",
                    deps: vec![bs_compile],
                    ..U::default()
                },
            ),
        );
        let bs_run = u["bs_run"].hash;
        u.insert(
            "serde",
            t.unit("serde", "1111111111111111", U { deps: vec![bs_run], ..U::default() }),
        );
        let serde = u["serde"].clone();
        u.insert(
            "middle",
            t.unit(
                "rustc_middle",
                "2222222222222222",
                U {
                    depinfo: vec![serde.rlib().to_owned()],
                    deps: vec![serde.hash],
                    ..U::default()
                },
            ),
        );
        let middle = u["middle"].clone();
        // An OLDER variant that the stamp names, and a NEWER one that nothing names but
        // that was built before the stamp was written: the last completed build chose the
        // older one, so the newer one is superseded.
        u.insert(
            "driver",
            t.unit(
                "rustc_driver",
                "3333333333333333",
                U { deps: vec![middle.hash], mtime: Some(1_000_000.0), ..U::default() },
            ),
        );
        u.insert(
            "driver_newer_unnamed",
            t.unit(
                "rustc_driver",
                "4444444444444444",
                U { mtime: Some(2_000_000.0), ..U::default() },
            ),
        );
        t.stamp(".librustc-stamp", &[u["driver"].rlib(), middle.rlib()]);
        // What older builds left, built before the stamp.
        u.insert(
            "middle_old",
            t.unit("rustc_middle", "5555555555555555", U { mtime: Some(500.0), ..U::default() }),
        );
        u.insert(
            "serde_old",
            t.unit("serde", "6666666666666666", U { mtime: Some(500.0), ..U::default() }),
        );
        u.insert("bs_compile_old", t.unit("serde", "c1c1c1c1c1c1c1c1", script(Some(500.0))));
        let old_script = u["bs_compile_old"].hash;
        u.insert(
            "bs_run_old",
            t.unit(
                "serde",
                "e1e1e1e1e1e1e1e1",
                U {
                    kind: "run-build-script",
                    krate: Some("build-script-build"),
                    output: "none",
                    mtime: Some(500.0),
                    deps: vec![old_script],
                    ..U::default()
                },
            ),
        );
        u.insert(
            "unfinished",
            t.unit("rustc_ast", "7777777777777777", U { finished: false, ..U::default() }),
        );
        (t, u)
    }
}

fn assert_unit(unit: &Made, present: bool) {
    for path in [&unit.rlib, &unit.bin, &unit.dylib, &unit.rmeta].into_iter().flatten() {
        assert_eq!(path.exists(), present, "{}", path.display());
    }
    if let Some(dir) = &unit.dir {
        assert_eq!(dir.exists(), present, "{}", dir.display());
    }
}

/// Every path under `root` with its size, modification time and (small) bytes.
fn snapshot(root: &Path) -> BTreeMap<PathBuf, (u64, i128, Vec<u8>)> {
    let mut out = BTreeMap::new();
    let mut stack = vec![root.to_owned()];
    while let Some(dir) = stack.pop() {
        let Ok(read) = fs::read_dir(&dir) else { continue };
        for entry in read.flatten() {
            let path = entry.path();
            let meta = fs::symlink_metadata(&path).unwrap();
            if meta.is_dir() {
                stack.push(path.clone());
            }
            let data = if meta.is_file() && meta.len() < 1024 {
                fs::read(&path).unwrap_or_default()
            } else {
                Vec::new()
            };
            out.insert(
                path.strip_prefix(root).unwrap().to_owned(),
                (meta.len(), mtime_ns(&meta), data),
            );
        }
    }
    out
}

fn left(summary: &Summary) -> String {
    summary
        .skipped
        .iter()
        .map(|(tree, why)| format!("{}: {why}", tree.display()))
        .collect::<Vec<_>>()
        .join("\n")
}

// ---- the rules ---------------------------------------------------------------------------

/// Trust: asserts `lock` is released: no open descriptor of this process names it
/// (every one /dev/fd lists, whatever the descriptor limit), and it can be locked at
/// once. Only an isolated test (crate::utils::tests::isolated) can assert the second:
/// in a shared test process a process another thread starts can hold the released
/// description: a fork until it execs or exits, and on macOS (measured there only) a
/// posix_spawn for the spawn itself
/// (LAND-GATE-EW1-FOLLOWUP-REVIEW-4 (12)).
fn assert_released(lock: &Path) {
    use std::os::unix::fs::MetadataExt;
    assert!(crate::utils::tests::in_isolated_child(), "assert_released needs an isolated test");
    let target = fs::metadata(lock).unwrap();
    let open: Vec<i32> = fs::read_dir("/dev/fd")
        .unwrap()
        .map(|entry| entry.unwrap().file_name().to_str().unwrap().parse().unwrap())
        .collect();
    for fd in open {
        let mut stat = std::mem::MaybeUninit::<libc::stat>::uninit();
        // SAFETY: fstat writes one stat for a descriptor number, or fails.
        if unsafe { libc::fstat(fd, stat.as_mut_ptr()) } == 0 {
            // SAFETY: fstat succeeded, so it initialized `stat`.
            let stat = unsafe { stat.assume_init() };
            let names = stat.st_dev as u64 == target.dev() && stat.st_ino as u64 == target.ino();
            assert!(!names, "descriptor {fd} still names {lock:?}");
        }
    }
    File::open(lock).unwrap().try_lock().unwrap();
}

#[test]
fn a_released_lock_looks_held_while_a_spawned_child_shares_it_and_a_held_descriptor_is_refused() {
    crate::utils::tests::isolated(|| {
        use std::io::{Read, Write};
        use std::os::fd::AsRawFd;
        use std::os::unix::process::CommandExt;
        let tmp = tempfile::tempdir().unwrap();
        let lock = write(&tmp.path().join(".cargo-lock"), b"");
        // A descriptor this process keeps open is refused, locked or not: the try alone
        // would pass an unlocked one.
        let kept = File::open(&lock).unwrap();
        assert!(std::panic::catch_unwind(|| assert_released(&lock)).is_err());
        drop(kept);
        assert_released(&lock);
        let held = File::open(&lock).unwrap();
        held.lock().unwrap();
        assert!(std::panic::catch_unwind(|| assert_released(&lock)).is_err());
        // A child forked while the lock is held shares its description until it execs. This
        // one execs only when told to, after this process has closed its holder and tried.
        let (mut ready, ready_signal) = std::io::pipe().unwrap();
        let (go_wait, mut go) = std::io::pipe().unwrap();
        let (ready_fd, wait_fd, go_fd) =
            (ready_signal.as_raw_fd(), go_wait.as_raw_fd(), go.as_raw_fd());
        let mut command = std::process::Command::new("/usr/bin/true");
        // SAFETY: the child calls only the async-signal-safe close, write and read.
        unsafe {
            command.pre_exec(move || {
                libc::close(go_fd);
                libc::write(ready_fd, b"r".as_ptr().cast(), 1);
                let mut byte = 0_u8;
                libc::read(wait_fd, (&raw mut byte).cast(), 1);
                Ok(())
            });
        }
        // The spawner keeps the ready pipe's only other writer, so a spawn that fails ends
        // the wait below at once instead of at the isolated test's watchdog.
        let spawner = std::thread::spawn(move || {
            let status = command.status();
            drop(ready_signal);
            status.unwrap()
        });
        let mut byte = [0];
        ready.read_exact(&mut byte).unwrap();
        drop(held);
        // The old assertion: an immediate try fails though this process closed its holder.
        let probe = File::open(&lock).unwrap();
        assert!(matches!(probe.try_lock(), Err(fs::TryLockError::WouldBlock)));
        drop(probe);
        // No descriptor of this process names the lock now: only the try refuses it.
        assert!(std::panic::catch_unwind(|| assert_released(&lock)).is_err());
        go.write_all(b"g").unwrap();
        assert!(spawner.join().unwrap().success());
        assert_released(&lock);
    });
}

#[test]
fn a_stamped_variant_is_kept_and_the_superseded_ones_go() {
    crate::utils::tests::isolated(|| {
        let f = Fixture::new();
        let (t, u) = f.warm_compiler_tree();
        let summary = f.prune();
        assert!(summary.skipped.is_empty(), "{}", left(&summary));
        for live in ["bs_compile", "bs_run", "serde", "middle", "driver"] {
            assert_unit(&u[live], true);
        }
        // The stamp names the older driver; the newer, unnamed one is the dead one.
        for dead in [
            "driver_newer_unnamed",
            "middle_old",
            "serde_old",
            "bs_run_old",
            "bs_compile_old",
            "unfinished",
        ] {
            assert_unit(&u[dead], false);
        }
        let listing = summary.listing.join("\n");
        assert!(listing.contains("superseded"), "{listing}");
        assert!(listing.contains("never finished"), "{listing}");
        assert_eq!(summary.units, 6, "{listing}");
        assert!(summary.bytes > 0);
        // Every stamp record still exists, no whole tree went, and the sysroot is whole.
        for record in fs::read(t.profile.join(".librustc-stamp")).unwrap().split(|b| *b == 0) {
            if !record.is_empty() {
                assert!(Path::new(OsStr::from_bytes(&record[1..])).exists());
            }
        }
        assert!(f.host.join("stage1-rustc").is_dir());
        assert_eq!(
            fs::read(f.host.join("stage1/lib/rustlib").join(HOST).join("lib/libstd-abc.rlib"))
                .unwrap(),
            b"std".repeat(30000)
        );
        for keep in [
            "llvm",
            "stage0",
            "stage0-sysroot",
            "stage1-tools-bin",
            "stage2-tools-bin",
            "stage3-tools-bin",
            "stage1-std",
            "bootstrap-tools",
        ] {
            assert!(f.host.join(keep).is_dir(), "{keep}");
        }
        assert_eq!(
            fs::read(f.host.join("stage1/lib/librustc_driver.dylib")).unwrap(),
            b"driver".repeat(20000)
        );
        // Incremental session files are not units, and stay.
        assert!(
            f.host.join("stage1-rustc").join(HOST).join("release/incremental/cache.bin").is_file()
        );
    });
}

#[test]
fn a_plan_lists_each_dead_unit_with_its_reason_and_changes_nothing() {
    crate::utils::tests::isolated(|| {
        // slim's `--dry-run`: the judge's plan is the dry run of the native prune.
        let f = Fixture::new();
        let (t, _) = f.warm_compiler_tree();
        let before = snapshot(&f.root);
        let tree = f.host.join("stage1-rustc");
        let plan = plan_tree(&tree, &profile_dirs(&tree).unwrap(), &[], true).unwrap();
        assert_eq!(snapshot(&f.root), before);
        let listing = plan.listing(&f.build);
        let dead: Vec<&String> = listing.iter().filter(|l| l.starts_with("dead ")).collect();
        assert_eq!(dead.len(), 6, "{listing:#?}");
        for line in &dead {
            assert!(line.contains("superseded: ") || line.contains("never finished: "), "{line}");
        }
        assert!(
            dead.iter().any(|l| l.contains("rustc_middle-5555555555555555")
                && l.contains("live variant 2222222222222222")),
            "{dead:#?}"
        );
        assert_eq!(plan.tree, tree);
        assert!(plan.units.iter().all(|u| u.profile == t.profile));
    });
}

#[test]
fn the_stamp_check_refuses_a_plan_that_would_delete_a_stamped_path() {
    crate::utils::tests::isolated(|| {
        // The safety net does not trust the judge: mark everything dead, and the stamp check,
        // which reads the stamps again, refuses before anything is deleted.
        let f = Fixture::new();
        let (t, _) = f.warm_compiler_tree();
        let tree = f.host.join("stage1-rustc");
        let profiles = profile_dirs(&tree).unwrap();
        let plan = plan_tree(&tree, &profiles, &[], true).unwrap();
        let everything: Vec<PathBuf> = plan.units.iter().flat_map(|u| u.paths.clone()).collect();
        let hits = stamped_in_plan(&everything, &profiles);
        assert!(hits.iter().any(|h| h.contains(".librustc-stamp names")), "{hits:#?}");
        // ...and what the judge planned is clear of every stamp.
        assert_eq!(stamped_in_plan(&plan.paths(), &profiles), Vec::<String>::new());
        assert!(t.profile.join(".librustc-stamp").exists());
    });
}

#[test]
fn a_binary_built_against_live_units_is_kept_beside_a_newer_one() {
    crate::utils::tests::isolated(|| {
        // An uplifted binary names no unit id (on macOS it is a clone of the unit's output),
        // so a binary nothing names is kept when it was built against live units. The stamp
        // says the last build chose the LIBRARY, not this binary, so a variant built after it
        // stays too; only an uplift with its bytes says which one is current.
        for uplifted in [false, true] {
            let f = Fixture::new();
            let mut t = f.tree("stage2-tools", Some(HOST), false);
            let lib = t.unit("cargo", "1010101010101010", U::default());
            let old_lib =
                t.unit("cargo", "2020202020202020", U { mtime: Some(500.0), ..U::default() });
            t.stamp(".tool-check-stamp", &[lib.rlib()]);
            let current = t.unit(
                "cargo",
                "3030303030303030",
                U {
                    kind: "bin",
                    output: "bin",
                    deps: vec![lib.hash],
                    mtime: Some(1_000_000.0),
                    ..U::default()
                },
            );
            fs::write(current.bin(), b"#!/bin/sh\n# current\n").unwrap();
            let old = t.unit(
                "cargo",
                "4040404040404040",
                U {
                    kind: "bin",
                    output: "bin",
                    deps: vec![old_lib.hash],
                    mtime: Some(2_000_000.0),
                    ..U::default()
                },
            );
            if uplifted {
                let up = write(&t.profile.join("cargo"), &fs::read(current.bin()).unwrap());
                chmod(&up, 0o755);
            }
            let summary = f.prune();
            assert!(summary.skipped.is_empty(), "{}", left(&summary));
            assert!(current.bin().exists());
            assert!(t.profile.join(".fingerprint/cargo-3030303030303030").is_dir());
            assert!(lib.rlib().exists());
            assert_eq!(!old.bin().exists(), uplifted, "{:#?}", summary.listing);
            assert_eq!(!t.profile.join(".fingerprint/cargo-4040404040404040").exists(), uplifted);
            assert_eq!(!old_lib.rlib().exists(), uplifted);
        }
    });
}

#[test]
fn a_test_built_against_live_units_does_not_supersede_the_last_test_build() {
    crate::utils::tests::isolated(|| {
        let f = Fixture::new();
        let mut t = f.tree("stage2-tools", Some(HOST), false);
        let lib = t.unit("tidy", "6161616161616161", U::default());
        t.stamp(".tool-check-stamp", &[lib.rlib()]);
        let dev_lib =
            t.unit("tidy", "6262626262626262", U { mtime: Some(1_500_000.0), ..U::default() });
        let older = t.unit(
            "tidy",
            "6363636363636363",
            U {
                kind: "test-lib",
                output: "bin",
                deps: vec![lib.hash],
                mtime: Some(1_000_000.0),
                ..U::default()
            },
        );
        let last = t.unit(
            "tidy",
            "6464646464646464",
            U {
                kind: "test-lib",
                output: "bin",
                deps: vec![dev_lib.hash],
                mtime: Some(2_000_000.0),
                ..U::default()
            },
        );
        let summary = f.prune();
        for unit in [&older, &last] {
            assert!(unit.bin().exists(), "{:#?}", summary.listing);
        }
        assert!(dev_lib.rlib().exists());
        assert!(lib.rlib().exists());
        assert_eq!(summary.units, 0, "{:#?}", summary.listing);
    });
}

#[test]
fn a_target_nothing_names_keeps_its_newest_variant_and_what_that_uses() {
    crate::utils::tests::isolated(|| {
        let f = Fixture::new();
        let mut t = f.tree("stage2-tools", Some(HOST), false);
        let live = t.unit("proptest", "1212121212121212", U::default());
        t.stamp(".tool-check-stamp", &[live.rlib()]);
        let dev_variant =
            t.unit("proptest", "3434343434343434", U { mtime: Some(500.0), ..U::default() });
        let newest = t.unit(
            "tidy",
            "5656565656565656",
            U {
                kind: "test-lib",
                output: "bin",
                deps: vec![dev_variant.hash],
                mtime: Some(2_000_000.0),
                ..U::default()
            },
        );
        let oldest = t.unit(
            "tidy",
            "7878787878787878",
            U { kind: "test-lib", output: "bin", mtime: Some(1_000_000.0), ..U::default() },
        );
        f.prune();
        assert!(newest.bin().exists());
        assert!(dev_variant.rlib().exists());
        assert!(!oldest.bin().exists());
    });
}

#[test]
fn host_directory_units_are_not_variants_of_target_directory_units() {
    crate::utils::tests::isolated(|| {
        let f = Fixture::new();
        let mut t = f.tree("stage1-rustc", Some(HOST), true);
        let live = t.unit("rustc_lexer", "abababababababab", U::default());
        t.stamp(".librustc-stamp", &[live.rlib()]);
        let mut host = CargoTree::new(&f.host.join("stage1-rustc"), None, false);
        let leftover =
            host.unit("rustc_lexer", "cdcdcdcdcdcdcdcd", U { mtime: Some(500.0), ..U::default() });
        f.prune();
        assert!(live.rlib().exists());
        assert!(leftover.rlib().exists());
        assert!(host.profile.join(".fingerprint/rustc_lexer-cdcdcdcdcdcdcdcd").exists());
    });
}

#[test]
fn a_failed_build_keeps_both_its_host_and_target_units() {
    crate::utils::tests::isolated(|| {
        let f = Fixture::new();
        let mut t = f.tree("stage1-rustc", Some(HOST), false);
        let stamped =
            t.unit("proc-macro2", "7171717171717171", U { mtime: Some(500.0), ..U::default() });
        let stamp = t.stamp(".librustc-stamp", &[stamped.rlib()]);
        set_mtime(&stamp, 1_000.0);
        let target_new = t.unit(
            "proc-macro2",
            "7272727272727272",
            U { mtime: Some(3_000_000.0), ..U::default() },
        );
        let mut host = CargoTree::new(&f.host.join("stage1-rustc"), None, false);
        let host_new = host.unit(
            "proc-macro2",
            "7373737373737373",
            U { mtime: Some(2_000_000.0), ..U::default() },
        );
        f.prune();
        assert!(target_new.rlib().exists());
        assert!(host_new.rlib().exists());
        assert!(stamped.rlib().exists());
    });
}

#[test]
fn uplifted_dep_info_roots_a_build_without_a_stamp() {
    crate::utils::tests::isolated(|| {
        let f = Fixture::new();
        let mut t = f.tree("bootstrap-tools", None, false);
        let lib = t.unit("tidy", "9090909090909090", U::default());
        let old = t.unit("tidy", "9191919191919191", U::default());
        write(
            &t.profile.join("tidy.d"),
            format!("{}/tidy: src/main.rs {}\n", t.profile.display(), lib.rlib().display())
                .as_bytes(),
        );
        f.prune();
        assert!(lib.rlib().exists());
        assert!(!old.rlib().exists());
    });
}

#[test]
fn rlib_objects_go_only_when_the_rlib_holds_them() {
    crate::utils::tests::isolated(|| {
        let f = Fixture::new();
        let mut t = f.tree("stage2-rustc", Some(HOST), true);
        let rlib_only = t.unit("rustc_span", "1313131313131313", U { objects: 3, ..U::default() });
        let dylib = t.unit(
            "rustc_driver",
            "1414141414141414",
            U { objects: 2, output: "dylib", ..U::default() },
        );
        let foreign = t.unit("rustc_errors", "1515151515151515", U { objects: 2, ..U::default() });
        // An object the rlib does not hold, and one whose size differs from its member.
        let stray = write(
            &foreign.out.join("rustc_errors-1515151515151515.stray.rcgu.o"),
            &[&MACHO[..], &[b's'; 64]].concat(),
        );
        fs::write(&foreign.objects[0], [&MACHO[..], b"changed"].concat()).unwrap();
        let gnu = t.unit("rustc_index", "1616161616161616", U { objects: 2, ..U::default() });
        let members: Vec<(String, Vec<u8>)> = gnu
            .objects
            .iter()
            .map(|o| (o.file_name().unwrap().to_string_lossy().into_owned(), fs::read(o).unwrap()))
            .collect();
        fs::write(gnu.rlib(), ar_archive(&members, false)).unwrap();
        t.stamp(
            ".librustc-stamp",
            &[rlib_only.rlib(), dylib.dylib.as_deref().unwrap(), foreign.rlib(), gnu.rlib()],
        );
        let rlib_bytes = fs::read(rlib_only.rlib()).unwrap();
        let summary = f.prune();
        assert!(summary.skipped.is_empty(), "{}", left(&summary));
        for object in rlib_only.objects.iter().chain(&gnu.objects) {
            assert!(!object.exists(), "{}", object.display());
        }
        assert_eq!(fs::read(rlib_only.rlib()).unwrap(), rlib_bytes);
        for object in &dylib.objects {
            assert!(object.exists(), "a dylib's debug map names its objects");
        }
        assert!(stray.exists());
        assert!(foreign.objects[0].exists(), "a changed object is not the member");
        assert!(!foreign.objects[1].exists());
        assert_eq!(summary.objects, 6);
        // Every unit is stamped, so none goes.
        assert!(t.profile.join("build/rustc_span/1313131313131313").is_dir());
        assert_eq!(summary.units, 0);
    });
}

#[test]
fn ar_members_reads_bsd_and_gnu_names() {
    crate::utils::tests::isolated(|| {
        let tmp = tempfile::tempdir().unwrap();
        for bsd in [true, false] {
            let members = vec![
                ("x-cgu.0.rcgu.o".to_owned(), b"abc".to_vec()),
                ("lib.rmeta".to_owned(), b"m".repeat(10)),
            ];
            let path = write(&tmp.path().join(format!("a{bsd}.rlib")), &ar_archive(&members, bsd));
            let found = ar_members(&path).unwrap();
            assert_eq!(
                found,
                HashMap::from([("x-cgu.0.rcgu.o".to_owned(), 3), ("lib.rmeta".to_owned(), 10)])
            );
        }
        // A long GNU name, through the `//` table.
        let members = vec![("a-very-long-member-name.rcgu.o".to_owned(), b"abcd".to_vec())];
        let path = write(&tmp.path().join("long.rlib"), &ar_archive(&members, false));
        assert_eq!(
            ar_members(&path).unwrap(),
            HashMap::from([("a-very-long-member-name.rcgu.o".to_owned(), 4)])
        );
        assert!(ar_members(&write(&tmp.path().join("not.rlib"), b"nope")).is_none());
    });
}

#[test]
fn elf_objects_are_kept_even_when_the_rlib_holds_them() {
    crate::utils::tests::isolated(|| {
        let f = Fixture::new();
        let mut t = f.tree("stage1-rustc", Some("x86_64-unknown-linux-gnu"), true);
        let elf =
            t.unit("rustc_span", "1313131313131313", U { objects: 3, magic: ELF, ..U::default() });
        let members: Vec<(String, Vec<u8>)> = elf
            .objects
            .iter()
            .map(|o| (o.file_name().unwrap().to_string_lossy().into_owned(), fs::read(o).unwrap()))
            .collect();
        fs::write(elf.rlib(), ar_archive(&members, false)).unwrap();
        let macho = t.unit("rustc_index", "1414141414141414", U { objects: 2, ..U::default() });
        t.stamp(".librustc-stamp", &[elf.rlib(), macho.rlib()]);
        let summary = f.prune();
        for object in &elf.objects {
            assert!(object.exists());
        }
        for object in &macho.objects {
            assert!(!object.exists());
        }
        assert!(!summary.listing.join("\n").contains("rustc_span"));
    });
}

#[test]
fn a_tree_without_roots_keeps_the_variant_its_uplifted_binary_is() {
    crate::utils::tests::isolated(|| {
        // build/bootstrap writes no stamp and no binary dep-info, and on macOS the uplifted
        // binary is a clone. The last build reused the OLDER variant, so the newest-built rule
        // alone would delete it: the uplifted copy's bytes name it.
        let f = Fixture::new();
        let mut trees = Vec::new();
        for (new_layout, name, c) in [(true, "bootstrap", "a"), (false, "bootstrap-legacy", "b")] {
            let mut t = CargoTree::new(&f.build.join(name), None, new_layout);
            t.next_hash += 0x1000 * u64::from(new_layout);
            let id = |c: &str, d: &str| format!("{c}{}", d.repeat(15));
            let serde = t.unit("serde", &id(c, "5"), U { mtime: Some(500_000.0), ..U::default() });
            let tracing =
                t.unit("tracing", &id(c, "7"), U { mtime: Some(1_900_000.0), ..U::default() });
            let lib_plain = t.unit(
                "bootstrap",
                &id(c, "0"),
                U { deps: vec![serde.hash], mtime: Some(1_000_000.0), ..U::default() },
            );
            let lib_traced = t.unit(
                "bootstrap",
                &id(c, "1"),
                U {
                    deps: vec![serde.hash, tracing.hash],
                    mtime: Some(2_000_000.0),
                    ..U::default()
                },
            );
            let plain = t.unit(
                "bootstrap",
                &id(c, "c"),
                U {
                    kind: "bin",
                    krate: Some("build_bootstrap"),
                    output: "bin",
                    deps: vec![lib_plain.hash],
                    mtime: Some(1_000_000.0),
                    ..U::default()
                },
            );
            let traced = t.unit(
                "bootstrap",
                &id(c, "d"),
                U {
                    kind: "bin",
                    krate: Some("build_bootstrap"),
                    output: "bin",
                    deps: vec![lib_traced.hash],
                    mtime: Some(2_000_000.0),
                    ..U::default()
                },
            );
            fs::write(plain.bin(), b"#!/bin/sh\n# plain  \n").unwrap();
            fs::write(traced.bin(), b"#!/bin/sh\n# traced \n").unwrap();
            // The uplifted copy keeps the binary's hyphen; its unit's output has `_`.
            let up = write(&t.profile.join("build-bootstrap"), &fs::read(plain.bin()).unwrap());
            chmod(&up, 0o755);
            trees.push((serde, lib_plain, lib_traced, plain, traced, up));
        }
        let summary = f.prune();
        assert!(summary.skipped.is_empty(), "{}", left(&summary));
        for (serde, lib_plain, lib_traced, plain, traced, up) in trees {
            for kept in [plain.bin(), lib_plain.rlib(), serde.rlib()] {
                assert!(kept.exists(), "{}\n{:#?}", kept.display(), summary.listing);
            }
            assert!(!traced.bin().exists());
            assert!(!lib_traced.rlib().exists());
            assert_eq!(fs::read(up).unwrap(), b"#!/bin/sh\n# plain  \n");
        }
    });
}

#[test]
fn an_uplifted_example_names_its_variant() {
    crate::utils::tests::isolated(|| {
        let f = Fixture::new();
        let mut t = f.tree("stage1-tools", Some(HOST), false);
        let mut variants = BTreeMap::new();
        for (uid, mtime, body) in
            [("e1e1e1e1e1e1e1e1", 1_000_000.0, "older"), ("e2e2e2e2e2e2e2e2", 2_000_000.0, "newer")]
        {
            t.unit(
                "demo",
                uid,
                U { kind: "example", output: "none", mtime: Some(mtime), ..U::default() },
            );
            let exe = write(
                &t.profile.join("examples").join(format!("demo-{uid}")),
                format!("#!/bin/sh\n# {body}").as_bytes(),
            );
            chmod(&exe, 0o755);
            variants.insert(uid, exe);
        }
        write(&t.profile.join("examples/demo"), &fs::read(&variants["e1e1e1e1e1e1e1e1"]).unwrap());
        f.prune();
        assert!(variants["e1e1e1e1e1e1e1e1"].exists());
        assert!(!variants["e2e2e2e2e2e2e2e2"].exists());
    });
}

#[test]
fn a_linked_deps_directory_is_not_followed() {
    crate::utils::tests::isolated(|| {
        let f = Fixture::new();
        let mut t = f.tree("stage2-tools", Some(HOST), false);
        let live = t.unit("cargo", "1010101010101010", U::default());
        t.unit("cargo", "2020202020202020", U::default());
        t.stamp(".tool-check-stamp", &[live.rlib()]);
        let outside = f.root.join("elsewhere-deps");
        fs::rename(t.profile.join("deps"), &outside).unwrap();
        symlink(&outside, t.profile.join("deps")).unwrap();
        let before = snapshot(&outside);
        f.prune();
        assert_eq!(snapshot(&outside), before);
        assert!(!t.profile.join(".fingerprint/cargo-2020202020202020").exists());
        assert!(t.profile.join(".fingerprint/cargo-1010101010101010").is_dir());
    });
}

#[test]
fn a_planned_path_that_resolves_outside_its_tree_is_refused() {
    crate::utils::tests::isolated(|| {
        // The scan follows no link; this pins the check behind it. A sibling whose name starts
        // with the tree's: a prefix is not containment.
        let f = Fixture::new();
        let (t, _) = f.warm_compiler_tree();
        let victim = write(&f.host.join("stage1-rustc-escape/victim.rlib"), b"keep me");
        symlink(victim.parent().unwrap(), t.profile.join("escape")).unwrap();
        let tree = f.host.join("stage1-rustc");
        let mut plan = plan_tree(&tree, &profile_dirs(&tree).unwrap(), &[], true).unwrap();
        let at = plan.units.iter().position(|u| u.unit_id == "5555555555555555").unwrap();
        plan.units[at].paths.push(t.profile.join("escape/victim.rlib"));
        let refusals = outside_trees(&plan);
        assert_eq!(refusals.len(), 1, "{refusals:#?}");
        assert!(refusals[0].contains("victim.rlib is outside"), "{refusals:#?}");
        assert!(victim.exists());
    });
}

#[test]
fn the_stamp_refusal_holds_for_a_root_spelled_in_another_case() {
    crate::utils::tests::isolated(|| {
        let f = Fixture::new();
        let spelled = PathBuf::from(
            f.root
                .to_string_lossy()
                .chars()
                .map(|c| {
                    if c.is_ascii_lowercase() {
                        c.to_ascii_uppercase()
                    } else {
                        c.to_ascii_lowercase()
                    }
                })
                .collect::<String>(),
        );
        if !spelled.exists()
            || fs::metadata(&spelled).unwrap().ino() != fs::metadata(&f.root).unwrap().ino()
        {
            eprintln!("SKIPPED: the temporary directory's volume is case-sensitive");
            return;
        }
        f.warm_compiler_tree();
        let tree = spelled.join("build").join(HOST).join("stage1-rustc");
        let profiles = profile_dirs(&tree).unwrap();
        let plan = plan_tree(&tree, &profiles, &[], true).unwrap();
        let everything: Vec<PathBuf> = plan.units.iter().flat_map(|u| u.paths.clone()).collect();
        let hits =
            stamped_in_plan(&everything, &profile_dirs(&f.host.join("stage1-rustc")).unwrap());
        assert!(hits.iter().any(|h| h.contains(".librustc-stamp names")), "{hits:#?}");
    });
}

#[test]
fn an_unreadable_directory_in_a_tree_leaves_it_as_it_is() {
    crate::utils::tests::isolated(|| {
        if is_root() {
            return;
        }
        // It may be a profile directory whose stamps cannot be read. Not searchable, a cargo
        // lock in it cannot be judged (slim reads that as no lock, and fails on the listing);
        // searchable but not listable, its stamps cannot be listed.
        for (mode, why) in
            [(0, "tmp-locked/.cargo-lock cannot be judged"), (0o311, "tmp-locked cannot be listed")]
        {
            let f = Fixture::new();
            let (_, u) = f.warm_compiler_tree();
            let locked = f.host.join("stage1-rustc/tmp-locked");
            fs::create_dir(&locked).unwrap();
            let before = snapshot(&f.root);
            chmod(&locked, mode);
            let summary = f.prune();
            chmod(&locked, 0o755);
            assert!(left(&summary).contains(why), "{mode:o}: {}", left(&summary));
            assert_eq!(snapshot(&f.root), before);
            assert_unit(&u["middle_old"], true);
        }
    });
}

#[test]
fn a_profile_directory_that_cannot_be_searched_or_listed_leaves_the_tree() {
    crate::utils::tests::isolated(|| {
        if is_root() {
            return;
        }
        // Its `.librustc-stamp` names a host proc macro (`h` record) in another profile
        // directory: skipping it would let the prune delete that dylib.
        for (target_is_profile, mode) in [(true, 0), (true, 0o311), (false, 0o311)] {
            let f = Fixture::new();
            let tree = f.host.join("stage1-rustc");
            let mut t = CargoTree::new(&tree, Some(HOST), true);
            let mut host = CargoTree::new(&tree, None, true);
            let old = host.unit(
                "serde_derive",
                "0101010101010101",
                U { output: "dylib", mtime: Some(1_000_000.0), ..U::default() },
            );
            host.unit(
                "serde_derive",
                "0202020202020202",
                U { output: "dylib", mtime: Some(2_000_000.0), ..U::default() },
            );
            let lib = t.unit(
                "rustc_middle",
                "0303030303030303",
                U { mtime: Some(1_000_000.0), ..U::default() },
            );
            let mut stamp = b"t".to_vec();
            stamp.extend(lib.rlib().as_os_str().as_bytes());
            stamp.extend(b"\0h");
            stamp.extend(old.dylib.as_deref().unwrap().as_os_str().as_bytes());
            stamp.push(0);
            write(&t.profile.join(".librustc-stamp"), &stamp);
            let target = if target_is_profile {
                t.profile.clone()
            } else {
                t.profile.parent().unwrap().to_owned()
            };
            chmod(&target, mode);
            let summary = f.prune();
            chmod(&target, 0o755);
            // Not searchable, its cargo lock cannot be judged before anything is listed.
            let why = if mode == 0 { ".cargo-lock cannot be judged" } else { "cannot be listed" };
            assert!(left(&summary).contains(why), "{mode:o}: {}", left(&summary));
            assert!(old.dylib.as_deref().unwrap().exists());
        }
    });
}

#[test]
fn the_cargo_locks_are_held_until_the_tree_is_done() {
    crate::utils::tests::isolated(|| {
        // A cargo that starts mid-prune waits: every lock of the tree is held, not probed.
        let f = Fixture::new();
        let (t, _) = f.warm_compiler_tree();
        let profiles = profile_dirs(&f.host.join("stage1-rustc")).unwrap();
        let held = CargoLocks::acquire(&profiles).unwrap();
        let probe = File::open(t.profile.join(".cargo-lock")).unwrap();
        assert!(matches!(probe.try_lock(), Err(fs::TryLockError::WouldBlock)));
        // A second prune meanwhile leaves the tree as it is.
        assert!(CargoLocks::acquire(&profiles).is_err());
        drop(probe);
        drop(held);
        assert_released(&t.profile.join(".cargo-lock"));
    });
}

#[test]
fn a_held_cargo_lock_leaves_its_tree_and_only_its_tree() {
    crate::utils::tests::isolated(|| {
        let f = Fixture::new();
        let (t, u) = f.warm_compiler_tree();
        let mut other = f.tree("stage2-tools", Some(HOST), false);
        let live = other.unit("cargo", "1010101010101010", U::default());
        let dead =
            other.unit("cargo", "2020202020202020", U { mtime: Some(500.0), ..U::default() });
        other.stamp(".tool-check-stamp", &[live.rlib()]);
        let holder = File::open(t.profile.join(".cargo-lock")).unwrap();
        holder.lock().unwrap();
        let before = snapshot(&f.host.join("stage1-rustc"));
        let summary = f.prune();
        assert!(
            left(&summary).contains(".cargo-lock is locked: a cargo is building in this tree"),
            "{}",
            left(&summary)
        );
        assert_eq!(snapshot(&f.host.join("stage1-rustc")), before);
        assert_unit(&u["middle_old"], true);
        assert!(!dead.rlib().exists(), "the other tree is pruned");
        drop(holder);
    });
}

#[test]
fn a_stamp_written_after_judging_is_read_before_deleting() {
    crate::utils::tests::isolated(|| {
        // The stamp check does not reuse what the judge read.
        let f = Fixture::new();
        let (t, u) = f.warm_compiler_tree();
        let tree = f.host.join("stage1-rustc");
        let profiles = profile_dirs(&tree).unwrap();
        let plan = plan_tree(&tree, &profiles, &[], true).unwrap();
        t.stamp(".libstd-check-stamp", &[u["middle_old"].rlib()]);
        let hits = stamped_in_plan(&plan.paths(), &profiles);
        assert!(hits.iter().any(|h| h.contains(".libstd-check-stamp names")), "{hits:#?}");
    });
}

#[test]
fn a_sysroot_link_into_a_dead_unit_leaves_the_tree() {
    crate::utils::tests::isolated(|| {
        let f = Fixture::new();
        let (_, u) = f.warm_compiler_tree();
        symlink(u["middle_old"].rlib(), f.host.join("stage1/lib/middle.rlib")).unwrap();
        let before = snapshot(&f.host.join("stage1-rustc"));
        let summary = f.prune();
        assert!(left(&summary).contains("links into"), "{}", left(&summary));
        assert_eq!(snapshot(&f.host.join("stage1-rustc")), before);
    });
}

#[test]
fn a_stamp_record_spelled_through_a_link_is_still_refused() {
    crate::utils::tests::isolated(|| {
        let f = Fixture::new();
        let (t, u) = f.warm_compiler_tree();
        let alias = t.profile.join("alias-out");
        symlink(&u["middle"].out, &alias).unwrap();
        t.stamp(".librustc-stamp", &[&alias.join(u["middle"].rlib().file_name().unwrap())]);
        let tree = f.host.join("stage1-rustc");
        let profiles = profile_dirs(&tree).unwrap();
        let plan = plan_tree(&tree, &profiles, &[], true).unwrap();
        let everything: Vec<PathBuf> = plan.units.iter().flat_map(|u| u.paths.clone()).collect();
        let hits = stamped_in_plan(&everything, &profiles);
        assert!(hits.iter().any(|h| h.contains(".librustc-stamp names")), "{hits:#?}");
    });
}

#[test]
fn an_unknown_unmarked_directory_refuses_discovery_before_any_removal() {
    crate::utils::tests::isolated(|| {
        if is_root() {
            return;
        }
        let f = Fixture::new();
        let (_, u) = f.warm_compiler_tree();
        let hidden = f.build.join("tmp-locked");
        fs::create_dir(&hidden).unwrap();
        let listable = f.host.join("stage1/lib/listable");
        write(&listable.join("inside.rlib"), b"x");
        chmod(&hidden, 0);
        chmod(&listable, 0o444);
        let summary = f.prune();
        chmod(&hidden, 0o755);
        chmod(&listable, 0o755);
        assert!(left(&summary).contains("tmp-locked"), "{}", left(&summary));
        assert!(summary.listing.is_empty());
        assert_eq!((summary.units, summary.objects), (0, 0));
        assert_unit(&u["middle_old"], true);
    });
}

#[test]
fn a_symlinked_cargo_lock_leaves_the_tree() {
    crate::utils::tests::isolated(|| {
        let f = Fixture::new();
        let (t, u) = f.warm_compiler_tree();
        let real = write(&f.root.join("elsewhere/.cargo-lock"), b"");
        fs::remove_file(t.profile.join(".cargo-lock")).unwrap();
        symlink(&real, t.profile.join(".cargo-lock")).unwrap();
        let before = snapshot(&f.host.join("stage1-rustc"));
        let summary = f.prune();
        assert!(left(&summary).contains(".cargo-lock is not a regular file"), "{}", left(&summary));
        assert_eq!(snapshot(&f.host.join("stage1-rustc")), before);
        assert_unit(&u["middle_old"], true);
    });
}

#[test]
fn a_cargo_lock_that_cannot_be_opened_leaves_the_tree() {
    crate::utils::tests::isolated(|| {
        if is_root() {
            return;
        }
        let f = Fixture::new();
        let (t, u) = f.warm_compiler_tree();
        chmod(&t.profile.join(".cargo-lock"), 0);
        let summary = f.prune();
        chmod(&t.profile.join(".cargo-lock"), 0o644);
        assert!(left(&summary).contains("so its holder cannot be judged"), "{}", left(&summary));
        assert_unit(&u["middle_old"], true);
    });
}

#[test]
fn an_unreadable_stamp_leaves_the_tree() {
    crate::utils::tests::isolated(|| {
        if is_root() {
            return;
        }
        // Its roots and its refusal would both be lost.
        let f = Fixture::new();
        let mut t = f.tree("stage1-std", Some(HOST), true);
        let stamped =
            t.unit("core", "1111111111111111", U { mtime: Some(1_000_000.0), ..U::default() });
        let stamp = t.stamp(".libstd-check-stamp", &[stamped.rlib()]);
        set_mtime(&stamp, 1_500_000.0);
        let current =
            t.unit("core", "2222222222222222", U { mtime: Some(2_000_000.0), ..U::default() });
        t.stamp(".libstd-stamp", &[current.rlib()]);
        chmod(&stamp, 0);
        let summary = f.prune();
        chmod(&stamp, 0o644);
        assert!(
            left(&summary).contains(".libstd-check-stamp cannot be read"),
            "{}",
            left(&summary)
        );
        assert!(stamped.rlib().exists());
    });
}

#[test]
fn a_stamp_that_is_not_a_regular_file_leaves_the_tree_without_a_hang() {
    crate::utils::tests::isolated(|| {
        // Reading a FIFO blocks until a writer comes, with every lock held.
        let f = Fixture::new();
        let mut t = f.tree("stage1-std", Some(HOST), true);
        let stamped =
            t.unit("core", "1111111111111111", U { mtime: Some(1_000_000.0), ..U::default() });
        let fifo = t.profile.join(".libstd-check-stamp");
        let c_path = std::ffi::CString::new(fifo.as_os_str().as_bytes()).unwrap();
        // SAFETY: a valid NUL-terminated path.
        assert_eq!(unsafe { libc::mkfifo(c_path.as_ptr(), 0o644) }, 0);
        let current =
            t.unit("core", "2222222222222222", U { mtime: Some(2_000_000.0), ..U::default() });
        t.stamp(".libstd-stamp", &[current.rlib()]);
        // Run it where a hang is seen: the test fails rather than waiting for a writer.
        let (done, wait) = std::sync::mpsc::channel();
        let (build, host) = (f.build.clone(), f.host.clone());
        std::thread::spawn(move || {
            let _ = done.send(prune(&build, &host, &[], &Options { objects: true, observe: None }));
        });
        let summary =
            wait.recv_timeout(Duration::from_secs(20)).expect("the prune opened a FIFO stamp");
        assert!(
            left(&summary).contains(".libstd-check-stamp cannot be read"),
            "{}",
            left(&summary)
        );
        assert!(left(&summary).contains("not a regular file"), "{}", left(&summary));
        assert!(stamped.rlib().exists());
    });
}

#[test]
fn two_versions_of_one_package_are_not_variants() {
    crate::utils::tests::isolated(|| {
        for new_layout in [true, false] {
            let f = Fixture::new();
            let mut t = f.tree("stage1-rustc", Some(HOST), new_layout);
            let one_old = t.unit(
                "syn",
                "a0a0a0a0a0a0a0a0",
                U { version: "1.0.109", mtime: Some(400.0), ..U::default() },
            );
            let two_old = t.unit(
                "syn",
                "b0b0b0b0b0b0b0b0",
                U { version: "2.0.87", mtime: Some(400.0), ..U::default() },
            );
            let stamp = t.stamp(".librustc-stamp", &[one_old.rlib(), two_old.rlib()]);
            set_mtime(&stamp, 500.0);
            let one = t.unit(
                "syn",
                "1111111111111111",
                U { version: "1.0.109", mtime: Some(1_000_000.0), ..U::default() },
            );
            let two = t.unit(
                "syn",
                "2222222222222222",
                U { version: "2.0.87", mtime: Some(2_000_000.0), ..U::default() },
            );
            f.prune();
            for unit in [&one, &two, &one_old, &two_old] {
                assert_unit(unit, true);
            }
        }
    });
}

#[test]
fn two_feature_sets_of_one_version_are_not_variants() {
    crate::utils::tests::isolated(|| {
        let f = Fixture::new();
        let mut t = f.tree("bootstrap-tools", None, false);
        let normal = t.unit(
            "serde",
            "3131313131313131",
            U { features: "[\"std\"]", mtime: Some(1_000_000.0), ..U::default() },
        );
        let build_dep = t.unit(
            "serde",
            "3232323232323232",
            U { features: "[\"derive\", \"std\"]", mtime: Some(2_000_000.0), ..U::default() },
        );
        f.prune();
        assert_unit(&normal, true);
        assert_unit(&build_dep, true);
    });
}

#[test]
fn a_rebuild_of_the_same_target_is_still_a_variant() {
    crate::utils::tests::isolated(|| {
        let f = Fixture::new();
        let mut t = f.tree("stage1-rustc", Some(HOST), false);
        let old = t.unit(
            "syn",
            "4141414141414141",
            U { version: "2.0.87", mtime: Some(500.0), ..U::default() },
        );
        let live = t.unit(
            "syn",
            "4242424242424242",
            U { version: "2.0.87", mtime: Some(1_000.0), ..U::default() },
        );
        t.stamp(".librustc-stamp", &[live.rlib()]);
        let other_version = t.unit(
            "syn",
            "4343434343434343",
            U { version: "1.0.109", mtime: Some(500.0), ..U::default() },
        );
        f.prune();
        assert_unit(&old, false);
        assert_unit(&live, true);
        assert_unit(&other_version, true);
    });
}

#[test]
fn a_unit_whose_fingerprint_names_no_target_is_no_variant() {
    crate::utils::tests::isolated(|| {
        let f = Fixture::new();
        let mut t = f.tree("stage1-rustc", Some(HOST), false);
        let anonymous = t.unit(
            "syn",
            "5151515151515151",
            U { identity: false, mtime: Some(500.0), ..U::default() },
        );
        let live = t.unit("syn", "5252525252525252", U::default());
        t.stamp(".librustc-stamp", &[live.rlib()]);
        f.prune();
        assert_unit(&anonymous, true);
        assert_unit(&live, true);
    });
}

#[test]
fn build_script_runs_of_two_versions_are_not_variants() {
    crate::utils::tests::isolated(|| {
        let f = Fixture::new();
        let mut t = f.tree("stage1-rustc", Some(HOST), true);
        let mut units = Vec::new();
        for (version, cid, rid, when) in [
            ("1.0.69", "c1c1c1c1c1c1c1c1", "e1e1e1e1e1e1e1e1", 1e6),
            ("2.0.12", "c2c2c2c2c2c2c2c2", "e2e2e2e2e2e2e2e2", 2e6),
        ] {
            let compiled = t.unit(
                "thiserror",
                cid,
                U {
                    kind: "build-script",
                    krate: Some("build-script-build"),
                    output: "bin",
                    version,
                    mtime: Some(when),
                    ..U::default()
                },
            );
            let ran = t.unit(
                "thiserror",
                rid,
                U {
                    kind: "run-build-script",
                    krate: Some("build-script-build"),
                    output: "none",
                    deps: vec![compiled.hash],
                    mtime: Some(when),
                    ..U::default()
                },
            );
            t.unit(
                "thiserror",
                &rid.replace('e', "f"),
                U { version, finished: false, ..U::default() },
            );
            units.push((compiled, ran));
        }
        f.prune();
        for (compiled, ran) in &units {
            assert_unit(compiled, true);
            assert_unit(ran, true);
        }
    });
}

#[test]
fn a_run_of_a_superseded_build_script_is_dead() {
    crate::utils::tests::isolated(|| {
        let f = Fixture::new();
        let mut t = f.tree("stage1-rustc", Some(HOST), true);
        let script = |mtime| U {
            kind: "build-script",
            krate: Some("build-script-build"),
            output: "bin",
            mtime: Some(mtime),
            ..U::default()
        };
        let old_script = t.unit("serde", "c3c3c3c3c3c3c3c3", script(500.0));
        let new_script = t.unit("serde", "c4c4c4c4c4c4c4c4", script(900.0));
        let run = |dep, mtime| U {
            kind: "run-build-script",
            krate: Some("build-script-build"),
            output: "none",
            deps: vec![dep],
            mtime: Some(mtime),
            ..U::default()
        };
        let old_run = t.unit("serde", "e3e3e3e3e3e3e3e3", run(old_script.hash, 500.0));
        let new_run = t.unit("serde", "e4e4e4e4e4e4e4e4", run(new_script.hash, 900.0));
        let lib = t.unit(
            "serde",
            "1414141414141414",
            U { deps: vec![new_run.hash], mtime: Some(1_000.0), ..U::default() },
        );
        t.stamp(".librustc-stamp", &[lib.rlib()]);
        let summary = f.prune();
        assert_unit(&old_script, false);
        assert_unit(&old_run, false);
        assert!(
            summary
                .listing
                .join("\n")
                .contains("the build script it ran (c3c3c3c3c3c3c3c3) is dead"),
            "{:#?}",
            summary.listing
        );
        assert_unit(&new_script, true);
        assert_unit(&new_run, true);
    });
}

#[test]
fn runs_of_one_build_script_for_two_profiles_are_both_kept() {
    crate::utils::tests::isolated(|| {
        let f = Fixture::new();
        let mut t = f.tree("stage1-rustc", Some(HOST), true);
        let host_profile = f.host.join("stage1-rustc/release");
        write(&host_profile.join(".cargo-lock"), b"");
        let script = t.unit(
            "ay",
            "c7c7c7c7c7c7c7c7",
            U {
                kind: "build-script",
                krate: Some("build-script-build"),
                output: "bin",
                mtime: Some(1e6),
                profile: Some(host_profile),
                ..U::default()
            },
        );
        let run = |when| U {
            kind: "run-build-script",
            krate: Some("build-script-build"),
            output: "none",
            deps: vec![script.hash],
            mtime: Some(when),
            ..U::default()
        };
        let check_run = t.unit("ay", "e7e7e7e7e7e7e7e7", run(1e6));
        t.unit("ay", "7171717171717171", U { output: "rmeta", finished: false, ..U::default() });
        let build_run = t.unit("ay", "e8e8e8e8e8e8e8e8", run(2e6));
        let lib = t.unit(
            "ay",
            "7272727272727272",
            U { profile_hash: 2, deps: vec![build_run.hash], mtime: Some(2e6), ..U::default() },
        );
        t.stamp(".librustc-stamp", &[lib.rlib()]);
        // The same in one host-only build: two runs of one script, neither library done.
        let mut h = f.tree("bootstrap-tools", None, false);
        let host_script = h.unit(
            "proc-macro2",
            "c8c8c8c8c8c8c8c8",
            U {
                kind: "build-script",
                krate: Some("build-script-build"),
                output: "bin",
                mtime: Some(1e6),
                ..U::default()
            },
        );
        let host_runs: Vec<Made> = [("e5e5e5e5e5e5e5e5", 1e6), ("e6e6e6e6e6e6e6e6", 2e6)]
            .into_iter()
            .map(|(rid, when)| {
                h.unit(
                    "proc-macro2",
                    rid,
                    U {
                        kind: "run-build-script",
                        krate: Some("build-script-build"),
                        output: "none",
                        deps: vec![host_script.hash],
                        mtime: Some(when),
                        ..U::default()
                    },
                )
            })
            .collect();
        for (uid, profile_hash) in [("8181818181818181", 1), ("8282828282828282", 2)] {
            h.unit("proc-macro2", uid, U { profile_hash, finished: false, ..U::default() });
        }
        f.prune();
        for unit in
            [&check_run, &build_run, &script, &lib, &host_script, &host_runs[0], &host_runs[1]]
        {
            assert_unit(unit, true);
        }
    });
}

#[test]
fn two_profiles_of_one_target_are_not_variants() {
    crate::utils::tests::isolated(|| {
        let f = Fixture::new();
        let mut t = f.tree("bootstrap-tools", None, false);
        let normal = t.unit(
            "proc-macro2",
            "3535353535353535",
            U { profile_hash: 1, mtime: Some(1_000_000.0), ..U::default() },
        );
        let other = t.unit(
            "proc-macro2",
            "3636363636363636",
            U { profile_hash: 2, mtime: Some(2_000_000.0), ..U::default() },
        );
        f.prune();
        assert_unit(&normal, true);
        assert_unit(&other, true);
    });
}

#[test]
fn a_host_tree_linked_outside_build_is_left_as_it_is() {
    crate::utils::tests::isolated(|| {
        let f = Fixture::new();
        let outside = tempfile::tempdir().unwrap();
        let moved = outside.path().canonicalize().unwrap().join(HOST);
        fs::rename(&f.host, &moved).unwrap();
        symlink(&moved, &f.host).unwrap();
        let mut t = CargoTree::new(&moved.join("stage1-rustc"), Some(HOST), true);
        let live = t.unit(
            "rustc_lexer",
            "abababababababab",
            U { mtime: Some(1_000_000.0), ..U::default() },
        );
        let old =
            t.unit("rustc_lexer", "cdcdcdcdcdcdcdcd", U { mtime: Some(500.0), ..U::default() });
        t.stamp(".librustc-stamp", &[live.rlib()]);
        let summary = f.prune();
        assert!(left(&summary).contains("outside"), "{}", left(&summary));
        assert!(old.rlib().exists());
    });
}

#[test]
fn a_failed_build_keeps_the_units_it_finished() {
    crate::utils::tests::isolated(|| {
        let f = Fixture::new();
        let mut t = f.tree("stage1-rustc", Some(HOST), true);
        let old_serde =
            t.unit("serde", "0000000000000001", U { mtime: Some(500.0), ..U::default() });
        let serde =
            t.unit("serde", "1111111111111111", U { mtime: Some(1_000_000.0), ..U::default() });
        let middle = t.unit(
            "rustc_middle",
            "2222222222222222",
            U { deps: vec![serde.hash], mtime: Some(1_000_000.0), ..U::default() },
        );
        let stamp = t.stamp(".librustc-stamp", &[serde.rlib(), middle.rlib()]);
        set_mtime(&stamp, 1_500_000.0);
        let new_serde =
            t.unit("serde", "3333333333333333", U { mtime: Some(2_000_000.0), ..U::default() });
        let new_middle = t.unit(
            "rustc_middle",
            "4444444444444444",
            U { deps: vec![new_serde.hash], mtime: Some(2_100_000.0), ..U::default() },
        );
        let failed =
            t.unit("rustc_driver", "5555555555555555", U { finished: false, ..U::default() });
        f.prune();
        for kept in [&serde, &middle, &new_serde, &new_middle] {
            assert_unit(kept, true);
        }
        assert_unit(&old_serde, false);
        assert_unit(&failed, false);
    });
}

#[test]
fn a_variant_built_before_the_stamp_that_names_another_is_superseded() {
    crate::utils::tests::isolated(|| {
        let f = Fixture::new();
        let mut t = f.tree("stage1-rustc", Some(HOST), true);
        let current =
            t.unit("serde", "1111111111111111", U { mtime: Some(1_000_000.0), ..U::default() });
        let toggled =
            t.unit("serde", "2222222222222222", U { mtime: Some(2_000_000.0), ..U::default() });
        let stamp = t.stamp(".librustc-stamp", &[current.rlib()]);
        set_mtime(&stamp, 3_000_000.0);
        let summary = f.prune();
        assert_unit(&current, true);
        assert_unit(&toggled, false);
        assert!(summary.listing.join("\n").contains("named by a root written after it was built"));
    });
}

#[test]
fn a_check_is_not_superseded_by_a_build_of_the_same_target() {
    crate::utils::tests::isolated(|| {
        let f = Fixture::new();
        let mut t = f.tree("bootstrap-tools", None, false);
        let built =
            t.unit("tidy", "1010101010101010", U { mtime: Some(1_000_000.0), ..U::default() });
        let depinfo = write(
            &t.profile.join("tidy.d"),
            format!("{}/tidy: src/main.rs {}\n", t.profile.display(), built.rlib().display())
                .as_bytes(),
        );
        set_mtime(&depinfo, 1_500_000.0);
        let checked = t.unit(
            "tidy",
            "2020202020202020",
            U { output: "rmeta", mtime: Some(1_200_000.0), ..U::default() },
        );
        let old_check = t.unit(
            "tidy",
            "3030303030303030",
            U { output: "rmeta", mtime: Some(1_100_000.0), ..U::default() },
        );
        f.prune();
        assert_unit(&built, true);
        assert_unit(&checked, true);
        assert_unit(&old_check, false);
    });
}

#[test]
fn a_revived_old_test_does_not_supersede_the_newest_test() {
    crate::utils::tests::isolated(|| {
        let f = Fixture::new();
        let mut t = f.tree("stage2-tools", Some(HOST), false);
        let lib_a =
            t.unit("gcore", "1010101010101010", U { mtime: Some(900_000.0), ..U::default() });
        let stamp = t.stamp(".tool-check-stamp", &[lib_a.rlib()]);
        set_mtime(&stamp, 1_500_000.0);
        let test_a = t.unit(
            "gcore",
            "2020202020202020",
            U {
                kind: "test-lib",
                output: "bin",
                deps: vec![lib_a.hash],
                mtime: Some(1_000_000.0),
                ..U::default()
            },
        );
        let lib_b =
            t.unit("gcore", "3030303030303030", U { mtime: Some(1_900_000.0), ..U::default() });
        let test_b = t.unit(
            "gcore",
            "4040404040404040",
            U {
                kind: "test-lib",
                output: "bin",
                deps: vec![lib_b.hash],
                mtime: Some(2_000_000.0),
                ..U::default()
            },
        );
        f.prune();
        for kept in [&lib_a, &test_a, &lib_b, &test_b] {
            assert_unit(kept, true);
        }
    });
}

#[test]
fn a_dead_unit_loses_its_fingerprint_before_anything_else() {
    crate::utils::tests::isolated(|| {
        if is_root() {
            return;
        }
        // Cargo trusts a run unit whose fingerprint is intact without looking at its OUT_DIR,
        // so the fingerprint must never outlive the outputs: when the rest cannot go, the
        // fingerprint is already gone.
        let f = Fixture::new();
        let (_, u) = f.warm_compiler_tree();
        let run_dir = u["bs_run_old"].dir.clone().unwrap();
        // The fingerprint is the first path of each unit's removal, in both layouts.
        assert_eq!(
            fingerprint_paths(std::slice::from_ref(&run_dir)),
            [run_dir.join("fingerprint")]
        );
        let legacy = f.root.join("legacy/release/.fingerprint/serde-0123456789abcdef");
        fs::create_dir_all(&legacy).unwrap();
        assert_eq!(
            fingerprint_paths(&[
                f.root.join("legacy/release/deps/libserde-0123456789abcdef.rlib"),
                legacy.clone()
            ]),
            [legacy]
        );
        // Its outputs cannot go: the fingerprint is gone all the same.
        let generated = write(&run_dir.join("out/gen.rs"), b"// generated\n");
        chmod(&run_dir.join("out"), 0o555);
        let summary = f.prune();
        chmod(&run_dir.join("out"), 0o755);
        assert!(!run_dir.join("fingerprint").exists());
        assert!(generated.exists());
        assert!(!summary.failures.is_empty());
    });
}

#[test]
fn a_unit_whose_fingerprint_cannot_go_keeps_its_outputs() {
    crate::utils::tests::isolated(|| {
        if is_root() {
            return;
        }
        let f = Fixture::new();
        let (_, u) = f.warm_compiler_tree();
        let fingerprint = u["bs_run_old"].dir.clone().unwrap().join("fingerprint");
        let out_dir = u["bs_run_old"].out.clone();
        write(&out_dir.join("gen.rs"), b"// generated\n");
        chmod(&fingerprint, 0o555);
        let summary = f.prune();
        chmod(&fingerprint, 0o755);
        assert!(
            summary
                .failures
                .iter()
                .any(|l| l.contains("kept the rest, its fingerprint did not go")),
            "{:#?}",
            summary.failures
        );
        assert!(out_dir.join("gen.rs").exists());
        assert_unit(&u["middle_old"], false);
        // A tree whose prune failed carries no stamp, so the next run judges it again.
        assert!(read_stamp(&f.host.join("stage1-rustc")).is_none());
    });
}

#[test]
fn a_run_units_out_dir_is_not_a_compilations_objects() {
    crate::utils::tests::isolated(|| {
        let f = Fixture::new();
        let mut t = f.tree("stage2-rustc", Some(HOST), true);
        let run = t.unit(
            "gen",
            "e0e0e0e0e0e0e0e0",
            U {
                kind: "run-build-script",
                krate: Some("build-script-build"),
                objects: 2,
                ..U::default()
            },
        );
        t.stamp(".librustc-stamp", &[run.rlib()]);
        f.prune();
        for object in &run.objects {
            assert!(object.exists());
        }
    });
}

// ---- the parts of slim's regular expressions ---------------------------------------------

#[test]
fn unit_refs_reads_both_layouts_as_slims_pattern_does() {
    crate::utils::tests::isolated(|| {
        let refs = |text: &str| unit_refs(text).into_iter().collect::<Vec<_>>();
        assert_eq!(refs("/t/release/deps/libserde-0123456789abcdef.rlib"), ["0123456789abcdef"]);
        assert_eq!(
            refs("/t/release/deps/serde_json-0123456789abcdef: src/lib.rs"),
            ["0123456789abcdef"]
        );
        assert_eq!(refs("/t/release/examples/demo-0123456789abcdef"), ["0123456789abcdef"]);
        // A hyphen is not a crate-name character in `deps/`.
        assert!(refs("/t/release/deps/foo-bar-0123456789abcdef.rlib").is_empty());
        // Seventeen hex digits are no id.
        assert!(refs("/t/release/deps/foo-0123456789abcdef0.rlib").is_empty());
        assert_eq!(
            refs("/t/release/.fingerprint/proc-macro2-0123456789abcdef/lib"),
            ["0123456789abcdef"]
        );
        assert_eq!(refs("/t/release/build/serde-0123456789abcdef/out"), ["0123456789abcdef"]);
        // The rightmost `-<id>` of a component that ends it or meets `:`.
        assert_eq!(refs("/t/build/a-1111111111111111-2222222222222222/out"), ["2222222222222222"]);
        assert_eq!(refs("/t/build/a-1111111111111111:x"), ["1111111111111111"]);
        // The new layout: build/<pkg>/<id>/.
        assert_eq!(
            refs("/t/release/build/serde/0123456789abcdef/out/libserde-0123456789abcdef.rlib"),
            ["0123456789abcdef"]
        );
        assert_eq!(
            refs("/t/deps/liba-1111111111111111.rlib /t/deps/libb-2222222222222222.rmeta\n"),
            ["1111111111111111", "2222222222222222"]
        );
        assert!(refs("/t/release/libserde.rlib").is_empty());
        assert_eq!(
            artifact_name("libserde-0123456789abcdef.rlib"),
            Some(("serde", "0123456789abcdef"))
        );
        assert_eq!(artifact_name("lib-0123456789abcdef.rlib"), Some(("lib", "0123456789abcdef")));
        assert_eq!(artifact_name("tidy-0123456789abcdef"), Some(("tidy", "0123456789abcdef")));
        assert_eq!(artifact_name("tidy-0123456789abcdefx"), None);
        assert_eq!(artifact_name("tidy"), None);
        assert_eq!(
            unit_dir_name("proc-macro2-0123456789abcdef"),
            Some(("proc-macro2", "0123456789abcdef"))
        );
        assert_eq!(unit_dir_name("-0123456789abcdef"), None);
        assert_eq!(le_hex(0x0102030405060708), "0807060504030201");
    });
}

// ---- what only the native prune does ------------------------------------------------------

#[test]
fn a_unit_this_runs_cargo_reported_is_live_and_supersedes_what_it_built_after() {
    crate::utils::tests::isolated(|| {
        // Tool builds write no stamp. A variant this run's cargo reported, fresh, is the one
        // the run chose: a newer variant built before the report is superseded, and the
        // reported one (built earliest) stays.
        let f = Fixture::new();
        let mut t = f.tree("stage1-tools", Some(HOST), false);
        let reported =
            t.unit("clippy", "1010101010101010", U { mtime: Some(1_000_000.0), ..U::default() });
        let newer =
            t.unit("clippy", "2020202020202020", U { mtime: Some(2_000_000.0), ..U::default() });
        let streamed = [Streamed {
            path: reported.rlib().to_owned(),
            when: now(),
            compiled: false,
            ran: false,
        }];
        let summary = f.prune_with(&streamed);
        assert_unit(&reported, true);
        assert_unit(&newer, false);
        assert!(
            summary.listing.join("\n").contains("named by a root written after it was built"),
            "{:#?}",
            summary.listing
        );
        // Without the report the newest variant is kept unjudged.
        let f = Fixture::new();
        let mut t = f.tree("stage1-tools", Some(HOST), false);
        let older =
            t.unit("clippy", "1010101010101010", U { mtime: Some(1_000_000.0), ..U::default() });
        let newest =
            t.unit("clippy", "2020202020202020", U { mtime: Some(2_000_000.0), ..U::default() });
        f.prune();
        assert_unit(&older, false);
        assert_unit(&newest, true);
    });
}

#[test]
fn an_uplifted_path_cargo_reported_names_the_unit_it_is() {
    crate::utils::tests::isolated(|| {
        let f = Fixture::new();
        let mut t = f.tree("stage1-tools", Some(HOST), false);
        let current = t.unit(
            "cargo",
            "3030303030303030",
            U { kind: "bin", output: "bin", mtime: Some(1_000_000.0), ..U::default() },
        );
        fs::write(current.bin(), b"#!/bin/sh\n# current\n").unwrap();
        let newer = t.unit(
            "cargo",
            "4040404040404040",
            U { kind: "bin", output: "bin", mtime: Some(2_000_000.0), ..U::default() },
        );
        let uplift = write(&t.profile.join("cargo"), &fs::read(current.bin()).unwrap());
        chmod(&uplift, 0o755);
        set_mtime(&uplift, 900.0); // an old uplift: only the report's time supersedes `newer`
        let streamed =
            [Streamed { path: uplift.clone(), when: now(), compiled: false, ran: false }];
        f.prune_with(&streamed);
        assert!(current.bin().exists());
        assert!(!newer.bin().exists());
    });
}

#[test]
fn a_build_script_run_cargo_reported_is_live() {
    crate::utils::tests::isolated(|| {
        let f = Fixture::new();
        let mut t = f.tree("stage1-rustc", Some(HOST), true);
        let script = t.unit(
            "serde",
            "c3c3c3c3c3c3c3c3",
            U {
                kind: "build-script",
                krate: Some("build-script-build"),
                output: "bin",
                mtime: Some(500.0),
                ..U::default()
            },
        );
        let run = t.unit(
            "serde",
            "e3e3e3e3e3e3e3e3",
            U {
                kind: "run-build-script",
                krate: Some("build-script-build"),
                output: "none",
                deps: vec![script.hash],
                mtime: Some(500.0),
                ..U::default()
            },
        );
        let newer_script = t.unit(
            "serde",
            "c4c4c4c4c4c4c4c4",
            U {
                kind: "build-script",
                krate: Some("build-script-build"),
                output: "bin",
                mtime: Some(900.0),
                ..U::default()
            },
        );
        let streamed =
            [Streamed { path: run.out.clone(), when: now(), compiled: false, ran: true }];
        let summary = f.prune_with(&streamed);
        assert!(summary.listing.join("\n").contains("c4c4c4c4c4c4c4c4"), "{:#?}", summary.listing);
        assert_unit(&run, true);
        assert_unit(&script, true);
        assert_unit(&newer_script, false);
    });
}

#[test]
fn an_unchanged_tree_is_not_judged_again_and_a_change_is() {
    crate::utils::tests::isolated(|| {
        let f = Fixture::new();
        let (mut t, u) = f.warm_compiler_tree();
        // What cargo uplifts beside the stamps: a binary and its dep-info.
        let depinfo = write(
            &t.profile.join("rustc-main.d"),
            format!("{}/rustc-main: {}\n", t.profile.display(), u["middle"].rlib().display())
                .as_bytes(),
        );
        let uplift = write(&t.profile.join("rustc-main"), b"#!/bin/sh\n# rustc-main\n");
        set_mtime(&uplift, 1_000_000.0);
        let first = f.prune();
        assert_eq!((first.judged, first.unchanged, first.units), (1, 0, 6));
        let stamp = fs::read_to_string(f.host.join("stage1-rustc").join(STAMP)).unwrap();
        // The schema, then a digest: no path, so a seed's audit of a cloned tree finds none.
        let lines: Vec<&str> = stamp.lines().collect();
        assert_eq!(lines.len(), 2, "{stamp}");
        assert_eq!(lines[0], "trust-prune/v1");
        assert!(lines[1].len() == 64 && lines[1].bytes().all(|b| b.is_ascii_hexdigit()), "{stamp}");
        let second = f.prune();
        assert_eq!((second.judged, second.unchanged, second.units), (0, 1, 0));
        // A stamp rewritten with the same bytes (bootstrap writes its stamps on every run) is
        // no change.
        let bytes = fs::read(t.profile.join(".librustc-stamp")).unwrap();
        fs::write(t.profile.join(".librustc-stamp"), &bytes).unwrap();
        assert_eq!(f.prune().unchanged, 1);
        // Nor is what cargo does on a run that compiles nothing (measured on m116): it rewrites
        // each uplifted dep-info with the same bytes, and clones each uplift again, a new inode
        // with the same size and time.
        let reclone = |path: &Path| {
            // A new file renamed over the old one: a new inode, whatever the file system.
            let bytes = fs::read(path).unwrap();
            let next = write(&path.with_extension("next"), &bytes);
            set_mtime(&next, 1_000_000.0);
            fs::rename(&next, path).unwrap();
        };
        let dep_bytes = fs::read(&depinfo).unwrap();
        for _ in 0..2 {
            let inode = fs::metadata(&uplift).unwrap().ino();
            fs::write(&depinfo, &dep_bytes).unwrap();
            set_mtime(&depinfo, 3_000_000.0);
            reclone(&uplift);
            assert_ne!(fs::metadata(&uplift).unwrap().ino(), inode);
            assert_eq!(f.prune().unchanged, 1);
        }
        // A dep-info that names other units, or an uplift of another variant, is a change.
        fs::write(
            &depinfo,
            format!("{}/rustc-main: {}\n", t.profile.display(), u["driver"].rlib().display()),
        )
        .unwrap();
        assert_eq!(f.prune().judged, 1);
        set_mtime(&uplift, 1_500_000.0);
        assert_eq!(f.prune().judged, 1);
        // A unit this run compiled in the tree is a change, whatever the directories say.
        let streamed = [Streamed {
            path: u["middle"].rlib().to_owned(),
            when: now(),
            compiled: true,
            ran: false,
        }];
        assert_eq!(f.prune_with(&streamed).judged, 1);
        // So is a new variant.
        let dead = t.unit("serde", "8888888888888888", U { mtime: Some(500.0), ..U::default() });
        let third = f.prune();
        assert_eq!((third.judged, third.units), (1, 1));
        assert_unit(&dead, false);
        // A stamp whose bytes changed is too.
        t.stamp(".librustc-stamp", &[u["driver"].rlib()]);
        assert_eq!(f.prune().judged, 1);
    });
}

#[test]
fn a_cloned_tree_is_judged_afresh() {
    crate::utils::tests::isolated(|| {
        // The stamp holds the tree's own inode numbers: a copy of the tree (a seeded worktree
        // clones `stage1-*`) never reads as unchanged.
        let f = Fixture::new();
        f.warm_compiler_tree();
        assert_eq!(f.prune().judged, 1);
        let tree = f.host.join("stage1-rustc");
        let copy = f.host.join("stage1-rustc-copy");
        let status =
            std::process::Command::new("cp").arg("-R").arg(&tree).arg(&copy).status().unwrap();
        assert!(status.success());
        fs::remove_dir_all(&tree).unwrap();
        fs::rename(&copy, &tree).unwrap();
        let summary = f.prune();
        assert_eq!((summary.judged, summary.unchanged), (1, 0));
    });
}

#[test]
fn the_summary_names_units_gib_and_seconds() {
    crate::utils::tests::isolated(|| {
        let f = Fixture::new();
        f.warm_compiler_tree();
        let line = f.prune().line();
        assert!(
            line.starts_with("Prune: removed 6 superseded units and 0 duplicate objects, "),
            "{line}"
        );
        assert!(line.contains(" GiB, in ") && line.contains(" s ("), "{line}");
    });
}

#[test]
fn cargo_messages_carry_fresh_and_the_build_script_out_dir() {
    crate::utils::tests::isolated(|| {
        use crate::core::build_steps::compile::CargoMessage;
        let artifact = concat!(
            r#"{"reason":"compiler-artifact","package_id":"p","manifest_path":"m","#,
            r#""target":{"kind":["lib"],"crate_types":["lib"],"name":"a","src_path":"s","#,
            r#""edition":"2021","doc":true,"doctest":true,"test":true},"profile":{},"#,
            r#""features":[],"filenames":["/t/release/deps/liba-0123456789abcdef.rlib"],"#,
            r#""executable":null,"fresh":true}"#
        );
        let CargoMessage::CompilerArtifact { filenames, fresh, .. } =
            serde_json::from_str(artifact).unwrap()
        else {
            panic!()
        };
        assert!(fresh);
        assert_eq!(filenames, ["/t/release/deps/liba-0123456789abcdef.rlib"]);
        let ran = concat!(
            r#"{"reason":"build-script-executed","package_id":"p","linked_libs":[],"#,
            r#""linked_paths":[],"cfgs":[],"env":[],"#,
            r#""out_dir":"/t/release/build/a-0123456789abcdef/out"}"#
        );
        let CargoMessage::BuildScriptExecuted { out_dir } = serde_json::from_str(ran).unwrap()
        else {
            panic!()
        };
        assert_eq!(out_dir.as_deref(), Some("/t/release/build/a-0123456789abcdef/out"));
        // An older cargo's message without `fresh` is a compiled unit.
        let old =
            r#"{"reason":"compiler-artifact","target":{"crate_types":["lib"]},"filenames":[]}"#;
        let CargoMessage::CompilerArtifact { fresh, .. } = serde_json::from_str(old).unwrap()
        else {
            panic!()
        };
        assert!(!fresh);
    });
}

#[test]
fn a_tree_slim_names_is_judged_and_the_kept_ones_are_not() {
    crate::utils::tests::isolated(|| {
        let f = Fixture::new();
        f.tree("stage1-rustc", Some(HOST), true);
        CargoTree::new(&f.build.join("bootstrap"), None, true);
        for never in ["stage1", "llvm", "stage1-tools-bin"] {
            write(&f.host.join(never).join("CACHEDIR.TAG"), b"x");
        }
        let names: Vec<String> = target_trees(&f.build, &f.host)
            .unwrap()
            .iter()
            .map(|t| t.file_name().unwrap().to_string_lossy().into_owned())
            .collect();
        assert_eq!(names, ["stage1-rustc", "bootstrap"]);
    });
}

#[test]
fn configuration_never_selects_unprotected_or_nonbuild_cleanup() {
    crate::utils::tests::isolated(|| {
        assert_eq!(gate(true, false, false, Kind::Build), Gate::Prune);
        for kind in [Kind::Check, Kind::Test, Kind::Doc, Kind::Dist, Kind::Install, Kind::Clippy] {
            assert_eq!(gate(true, false, false, kind), Gate::Prune, "{kind:?}");
        }
        assert_eq!(gate(false, false, false, Kind::Build), Gate::Off);
        assert_eq!(gate(true, true, false, Kind::Build), Gate::Off);
        assert_eq!(gate(true, false, true, Kind::Build), Gate::Off);
        for kind in [Kind::Clean, Kind::Setup, Kind::Format, Kind::Vendor] {
            assert_eq!(gate(true, false, false, kind), Gate::Off, "{kind:?}");
        }
    });
}

#[cfg(any(target_os = "macos", target_os = "linux"))]
fn command_ownership(f: &Fixture) -> crate::core::build_steps::frontend_runtime::CommandOwnership {
    crate::core::build_steps::frontend_runtime::CommandOwnership::new(native_prune_lease(f))
}

#[cfg(any(target_os = "macos", target_os = "linux"))]
fn native_prune_lease(f: &Fixture) -> build_helper::trust_repo_lock::management::Lease {
    use build_helper::trust_repo_lock::management::{Acquire, Kind, LeaseAcquisition, Manager};
    let request = Acquire {
        kind: Kind::Build,
        owner_pid: std::process::id(),
        purpose: "native prune original owner regression".into(),
        contract: "cleanup borrows the actual acquisition, never token text".into(),
        wait: Duration::ZERO,
        inherited_token: None,
        break_reason: None,
    };
    let LeaseAcquisition::Granted(lease) =
        Manager::open(&f.root).unwrap().acquire_lease(&request).unwrap()
    else {
        panic!("private fixture is held")
    };
    lease
}

#[cfg(any(target_os = "macos", target_os = "linux"))]
fn owned_prune(f: &Fixture, ownership: Option<Ownership<'_>>) -> Result<Summary, String> {
    prune_owned(
        &f.root,
        &f.build,
        &f.host,
        &[],
        &Options { objects: false, observe: None },
        ownership,
    )
}

#[test]
#[cfg(any(target_os = "macos", target_os = "linux"))]
fn direct_native_command_prunes_under_original_guards_without_token_authority() {
    crate::utils::tests::isolated(|| {
        let f = Fixture::new();
        let (_, live, dead) = legacy_tree_with_a_superseded_variant(&f);
        let command = command_ownership(&f);
        let output =
            build_helper::trust_output_lock::OutputLock::try_acquire(&f.build).unwrap().unwrap();
        let summary = owned_prune(&f, Some(Ownership::command(&output, &command))).unwrap();
        assert!(summary.failures.is_empty(), "{summary:?}");
        assert_unit(&live, true);
        assert_unit(&dead, false);
        assert!(
            build_helper::trust_output_lock::OutputLock::try_acquire(&f.build).unwrap().is_none()
        );
        command.with_pruning_lease(&f.root, || Ok(())).unwrap();
    });
}

#[test]
#[cfg(any(target_os = "macos", target_os = "linux"))]
fn original_repository_lease_also_permits_native_pruning() {
    crate::utils::tests::isolated(|| {
        let f = Fixture::new();
        let (_, live, dead) = legacy_tree_with_a_superseded_variant(&f);
        let repository = crate::utils::trust_repo_lock::BuildLease::acquire_independent(
            &f.root,
            "native prune regression",
            "actual independent repository guard",
        )
        .unwrap();
        let output =
            build_helper::trust_output_lock::OutputLock::try_acquire(&f.build).unwrap().unwrap();
        owned_prune(&f, Some(Ownership::repository(&output, &repository))).unwrap();
        assert_unit(&live, true);
        assert_unit(&dead, false);
        repository.check_current().unwrap();
    });
}

#[test]
#[cfg(any(target_os = "macos", target_os = "linux"))]
fn matching_holder_text_without_original_guards_never_prunes() {
    crate::utils::tests::isolated(|| {
        let f = Fixture::new();
        let (_, _, dead) = legacy_tree_with_a_superseded_variant(&f);
        write(&f.root.join(".trust-build-lock/info"), b"token=matching-token\nkind=build\n");
        let before = snapshot(&f.root);
        assert!(owned_prune(&f, None).unwrap_err().contains("no original native"));
        assert_unit(&dead, true);
        assert_eq!(snapshot(&f.root), before);
    });
}

#[test]
#[cfg(any(target_os = "macos", target_os = "linux"))]
fn changed_output_or_holder_refuses_before_any_prune_mutation() {
    crate::utils::tests::isolated(|| {
        for replace_output in [true, false] {
            let f = Fixture::new();
            let (_, _, dead) = legacy_tree_with_a_superseded_variant(&f);
            let command = command_ownership(&f);
            let output = build_helper::trust_output_lock::OutputLock::try_acquire(&f.build)
                .unwrap()
                .unwrap();
            let path = if replace_output {
                f.build.join("lock")
            } else {
                f.root.join(".trust-build-lock/info")
            };
            fs::rename(&path, path.with_extension("original")).unwrap();
            fs::write(&path, b"replacement").unwrap();
            let before = snapshot(&f.root);
            assert!(owned_prune(&f, Some(Ownership::command(&output, &command))).is_err());
            assert_unit(&dead, true);
            assert_eq!(snapshot(&f.root), before);
        }
    });
}

#[test]
#[cfg(any(target_os = "macos", target_os = "linux"))]
fn withheld_holder_is_exclusion_without_local_pruning_authority() {
    crate::utils::tests::isolated(|| {
        let f = Fixture::new();
        let (_, _, dead) = legacy_tree_with_a_superseded_variant(&f);
        let command = command_ownership(&f);
        let output =
            build_helper::trust_output_lock::OutputLock::try_acquire(&f.build).unwrap().unwrap();
        let withheld = command.withhold_original().unwrap();
        let before = snapshot(&f.root);
        let error = owned_prune(&f, Some(Ownership::command(&output, &command))).unwrap_err();
        assert!(error.contains("unwithheld"), "{error}");
        withheld.check_current().unwrap();
        assert_unit(&dead, true);
        assert_eq!(snapshot(&f.root), before);
    });
}

#[test]
#[cfg(any(target_os = "macos", target_os = "linux"))]
fn original_guards_for_another_tree_cannot_authorize_pruning() {
    crate::utils::tests::isolated(|| {
        for wrong_output in [true, false] {
            let a = Fixture::new();
            let b = Fixture::new();
            let (_, _, dead) = legacy_tree_with_a_superseded_variant(&b);
            let command_a = command_ownership(&a);
            let command_b = command_ownership(&b);
            let output_a = build_helper::trust_output_lock::OutputLock::try_acquire(&a.build)
                .unwrap()
                .unwrap();
            let output_b = build_helper::trust_output_lock::OutputLock::try_acquire(&b.build)
                .unwrap()
                .unwrap();
            let ownership = if wrong_output {
                Ownership::command(&output_a, &command_b)
            } else {
                Ownership::command(&output_b, &command_a)
            };
            let before = snapshot(&b.root);
            assert!(owned_prune(&b, Some(ownership)).is_err(), "foreign guard was accepted");
            assert_unit(&dead, true);
            assert_eq!(snapshot(&b.root), before);
        }
    });
}

// --------------------------------------------------------------------------------------
// The second hostile review: what read as empty, what was counted, and the wiring of
// `prune()` itself (locks, the outside-the-tree refusal and the stamp safety net), each
// pinned end to end.
// --------------------------------------------------------------------------------------

/// A legacy tree in `stage2-tools` with a stamped unit and the superseded variant it
/// replaced, and a build-script run's `OUT_DIR`.
fn legacy_tree_with_a_superseded_variant(f: &Fixture) -> (CargoTree, Made, Made) {
    let mut t = f.tree("stage2-tools", Some(HOST), false);
    let live = t.unit("cargo", "1010101010101010", U::default());
    let dead = t.unit("cargo", "2020202020202020", U { mtime: Some(500.0), ..U::default() });
    t.stamp(".tool-check-stamp", &[live.rlib()]);
    write(&t.profile.join("build/cargo-1010101010101010/out/generated.rs"), b"pub fn f() {}\n");
    (t, live, dead)
}

#[test]
fn a_directory_of_a_profile_that_cannot_be_listed_leaves_the_tree() {
    crate::utils::tests::isolated(|| {
        if is_root() {
            return;
        }
        // Read as empty, an unlistable `.fingerprint` made every unit "never finished": the
        // prune deleted their outputs and build-script `OUT_DIR`s while their fingerprints,
        // which cargo trusts, stayed, and the next build that read an `OUT_DIR` failed.
        for dir in [".fingerprint", "deps", "build"] {
            let f = Fixture::new();
            let (t, live, dead) = legacy_tree_with_a_superseded_variant(&f);
            let tree = f.host.join("stage2-tools");
            let before = snapshot(&tree);
            chmod(&t.profile.join(dir), 0o311);
            let summary = f.prune();
            chmod(&t.profile.join(dir), 0o755);
            let why = format!("{dir} cannot be listed");
            assert!(left(&summary).contains(&why), "{dir}: {}", left(&summary));
            assert_eq!(snapshot(&tree), before, "{dir}");
            assert!(live.rlib().exists() && dead.rlib().exists());
        }
        // A fingerprint file that cannot be read says neither the unit's kind nor its age.
        let f = Fixture::new();
        let (t, _, dead) = legacy_tree_with_a_superseded_variant(&f);
        let hash = t.profile.join(".fingerprint/cargo-1010101010101010/lib-cargo");
        chmod(&hash, 0);
        let summary = f.prune();
        chmod(&hash, 0o644);
        assert!(left(&summary).contains("lib-cargo cannot be read"), "{}", left(&summary));
        assert!(dead.rlib().exists());
    });
}

#[test]
fn a_unit_loses_its_fingerprint_first_even_when_the_judge_did_not_see_it() {
    crate::utils::tests::isolated(|| {
        let f = Fixture::new();
        let (t, _, dead) = legacy_tree_with_a_superseded_variant(&f);
        let tree = f.host.join("stage2-tools");
        let plan = plan_tree(&tree, &profile_dirs(&tree).unwrap(), &[], true).unwrap();
        let unit = plan.units.iter().find(|u| u.unit_id == "2020202020202020").unwrap();
        let fingerprint = t.profile.join(".fingerprint/cargo-2020202020202020");
        let unseen: Vec<PathBuf> =
            unit.paths.iter().filter(|p| **p != fingerprint).cloned().collect();
        assert!(unseen.len() < unit.paths.len());
        // A fingerprint directory that cannot be listed keeps the whole unit.
        if !is_root() {
            chmod(&t.profile.join(".fingerprint"), 0o311);
            let removal = remove_units(&[(unit, unseen.clone(), true)]);
            chmod(&t.profile.join(".fingerprint"), 0o755);
            assert_eq!(removal.units, 0);
            assert!(removal.failures.iter().any(|f| f.contains("cannot be listed")), "{removal:?}");
            assert!(fingerprint.is_dir() && dead.rlib().exists());
        }
        let removal = remove_units(&[(unit, unseen, true)]);
        assert!(removal.failures.is_empty(), "{removal:?}");
        assert_eq!(removal.units, 1);
        assert!(!fingerprint.exists() && !dead.rlib().exists());
    });
}

#[test]
fn a_unit_or_an_object_is_counted_only_when_it_went() {
    crate::utils::tests::isolated(|| {
        if is_root() {
            return;
        }
        let f = Fixture::new();
        let mut t = f.tree("stage2-tools", Some(HOST), false);
        let dead = t.unit("cargo", "2020202020202020", U { objects: 2, ..U::default() });
        let tree = f.host.join("stage2-tools");
        let plan = plan_tree(&tree, &profile_dirs(&tree).unwrap(), &[], true).unwrap();
        let unit = plan.units.iter().find(|u| u.unit_id == "2020202020202020").unwrap();
        let deps = t.profile.join("deps");
        chmod(&deps, 0o555);
        let removal =
            remove_units(&[(unit, dead.objects.clone(), false), (unit, unit.paths.clone(), true)]);
        chmod(&deps, 0o755);
        assert_eq!((removal.units, removal.objects), (0, 0), "{removal:?}");
        assert!(!removal.failures.is_empty());
        assert!(dead.rlib().exists() && dead.objects.iter().all(|o| o.exists()));
        // The fingerprint went first, so cargo rebuilds what is left.
        assert!(!t.profile.join(".fingerprint/cargo-2020202020202020").exists());
    });
}

#[test]
fn removing_a_unit_follows_no_link_inside_it() {
    crate::utils::tests::isolated(|| {
        let f = Fixture::new();
        let (t, _, dead) = legacy_tree_with_a_superseded_variant(&f);
        let outside = write(&f.root.join("outside/keep.rs"), b"keep");
        symlink(outside.parent().unwrap(), t.profile.join(".fingerprint/cargo-2020202020202020/l"))
            .unwrap();
        let summary = f.prune();
        assert!(summary.skipped.is_empty(), "{}", left(&summary));
        assert!(!dead.rlib().exists());
        assert_eq!(fs::read(&outside).unwrap(), b"keep");
    });
}

thread_local! {
    static SWAP_TO: std::cell::RefCell<Option<(PathBuf, PathBuf)>> =
        const { std::cell::RefCell::new(None) };
}

/// Once: moves the judged directory aside and puts a link to the target in its place.
fn swap_for_link(path: &Path) {
    if let Some((doomed, target)) = SWAP_TO.with(|swap| swap.borrow_mut().take()) {
        assert_eq!(path, doomed);
        fs::rename(&doomed, doomed.with_extension("aside")).unwrap();
        symlink(&target, &doomed).unwrap();
    }
}

/// A directory goes by `fs::remove_dir_all`, which follows no link, even one put in its
/// place after `remove_path` judged it a directory. The hook swaps it at the point where
/// the hand-written walk this replaced opened the path again (`read_dir`), followed the
/// link and removed `outside/keep.rs`. What the link reached is not counted either.
#[test]
fn removing_a_directory_follows_no_link_swapped_in_after_it_was_judged() {
    crate::utils::tests::isolated(|| {
        let f = Fixture::new();
        let outside = write(&f.root.join("outside/keep.rs"), b"keep");
        let doomed = f.root.join("doomed");
        write(&doomed.join("gone.rs"), b"gone");
        let target = outside.parent().unwrap().to_owned();
        SWAP_TO.with(|swap| *swap.borrow_mut() = Some((doomed.clone(), target)));
        AFTER_LSTAT.set(Some(swap_for_link));
        let (mut bytes, mut failures) = (0, Vec::new());
        let gone = remove_path(&doomed, &mut bytes, &mut failures);
        AFTER_LSTAT.set(None);
        assert_eq!(fs::read(&outside).unwrap(), b"keep");
        assert!(gone && failures.is_empty(), "{failures:?}");
        assert!(fs::symlink_metadata(&doomed).is_err(), "the link is gone");
        assert_eq!(fs::read(f.root.join("doomed.aside/gone.rs")).unwrap(), b"gone");
        assert_eq!(bytes, 0, "what the link reached is not counted");
    });
}

thread_local! {
    static SEEN: std::cell::RefCell<Vec<(PathBuf, Stage, Vec<bool>)>> =
        const { std::cell::RefCell::new(Vec::new()) };
    static DOOMED: std::cell::RefCell<Option<(PathBuf, PathBuf)>> =
        const { std::cell::RefCell::new(None) };
    static MANUAL_LOCKS: std::cell::RefCell<Vec<PathBuf>> = const { std::cell::RefCell::new(Vec::new()) };
}

fn note_manual_preparation(tree: &Path, stage: Stage) {
    let held = MANUAL_LOCKS.with(|paths| {
        paths
            .borrow()
            .iter()
            .map(|path| {
                matches!(File::open(path).unwrap().try_lock(), Err(fs::TryLockError::WouldBlock))
            })
            .collect()
    });
    SEEN.with(|seen| seen.borrow_mut().push((tree.to_owned(), stage, held)));
}

#[test]
fn manual_measurement_prepares_all_cross_tree_links_and_locks_before_first_deletion() {
    crate::utils::tests::isolated(|| {
        let f = Fixture::new();
        let (first, first_live, first_dead) = legacy_tree_with_a_superseded_variant(&f);
        let mut second = f.tree("stage3-tools", Some(HOST), false);
        let second_live = second.unit("cargo", "3030303030303030", U::default());
        let second_dead =
            second.unit("cargo", "4040404040404040", U { mtime: Some(500.0), ..U::default() });
        second.stamp(".tool-check-stamp", &[second_live.rlib()]);
        fs::remove_file(second_dead.rlib()).unwrap();
        fs::hard_link(first_dead.rlib(), second_dead.rlib()).unwrap();
        assert_eq!(fs::metadata(first_dead.rlib()).unwrap().nlink(), 2);
        let output =
            build_helper::trust_output_lock::OutputLock::try_acquire(&f.build).unwrap().unwrap();
        let directory = output.original_directory().unwrap();
        let trees = [&first, &second]
            .map(|tree| tree.profile.parent().unwrap().parent().unwrap().to_owned());
        let mut inventory = space::Accounting::new(&f.build, directory).unwrap();
        for tree in &trees {
            let profiles = profile_dirs(tree).unwrap();
            inventory.collect(&plan_tree(tree, &profiles, &[], false).unwrap().paths()).unwrap();
        }
        let expected = inventory.finish().unwrap();
        assert!(expected.counted_inodes > 0 && expected.allocated_upper_bytes > 0);
        MANUAL_LOCKS.with(|paths| {
            *paths.borrow_mut() =
                vec![first.profile.join(".cargo-lock"), second.profile.join(".cargo-lock")]
        });
        SEEN.with(|seen| seen.borrow_mut().clear());
        let options = Options { objects: false, observe: Some(note_manual_preparation) };
        let summary = prune_selected_measured(
            &f.build,
            &f.host,
            &[],
            &options,
            true,
            false,
            ManualObservation { directory, revalidate: None },
        );
        assert!(summary.skipped.is_empty() && summary.failures.is_empty(), "{summary:?}");
        assert!(summary.space_observation_errors.is_empty(), "{summary:?}");
        assert_eq!((summary.planned_units, summary.units), (2, 2));
        let observed = summary.space_estimate.unwrap();
        assert_eq!(observed.counted_inodes, expected.counted_inodes);
        assert_eq!(observed.allocated_upper_bytes, expected.allocated_upper_bytes);
        let seen = SEEN.with(|seen| seen.take());
        let first_delete = seen.iter().position(|(_, stage, _)| *stage == Stage::Deleting).unwrap();
        let last_judged = seen.iter().rposition(|(_, stage, _)| *stage == Stage::Judged).unwrap();
        assert!(last_judged < first_delete, "{seen:?}");
        for (_, stage, held) in seen {
            if stage == Stage::Deleting {
                assert_eq!(held, [true, true]);
            }
        }
        for path in MANUAL_LOCKS.with(|paths| paths.take()) {
            assert_released(&path);
        }
        output.check_current().unwrap();
        assert_unit(&first_dead, false);
        assert_unit(&second_dead, false);
        assert_unit(&first_live, true);
        assert_unit(&second_live, true);
    });
}

/// Notes, at each stage, whether another opener finds every cargo lock of `tree` held.
fn note_locks(tree: &Path, stage: Stage) {
    let held = profile_dirs(tree)
        .unwrap()
        .iter()
        .map(|profile| {
            let probe = File::open(profile.join(".cargo-lock")).unwrap();
            matches!(probe.try_lock(), Err(fs::TryLockError::WouldBlock))
        })
        .collect();
    SEEN.with(|seen| seen.borrow_mut().push((tree.to_owned(), stage, held)));
}

#[test]
fn prune_holds_every_cargo_lock_of_a_tree_while_it_deletes() {
    crate::utils::tests::isolated(|| {
        let f = Fixture::new();
        let (t, u) = f.warm_compiler_tree();
        let options = Options { objects: true, observe: Some(note_locks) };
        let summary = prune(&f.build, &f.host, &[], &options);
        assert!(summary.skipped.is_empty(), "{}", left(&summary));
        assert_unit(&u["middle_old"], false);
        let seen = SEEN.with(|seen| seen.take());
        let rustc: Vec<_> =
            seen.iter().filter(|(tree, ..)| tree.ends_with("stage1-rustc")).collect();
        let stages: Vec<Stage> = rustc.iter().map(|(_, stage, _)| *stage).collect();
        assert_eq!(stages, [Stage::Judged, Stage::Deleting]);
        for (_, stage, held) in rustc {
            assert!(!held.is_empty() && held.iter().all(|h| *h), "{stage:?}: {held:?}");
        }
        // ...and releases them when the tree is done.
        assert_released(&t.profile.join(".cargo-lock"));
    });
}

/// After judging stage1-rustc, writes a stamp naming the path [`DOOMED`] holds.
fn stamp_after_judging(tree: &Path, stage: Stage) {
    if stage == Stage::Judged && tree.ends_with("stage1-rustc") {
        let (stamp, named) = DOOMED.with(|d| d.borrow().clone()).unwrap();
        let mut data = b"t".to_vec();
        data.extend(named.as_os_str().as_bytes());
        data.push(0);
        fs::write(stamp, data).unwrap();
    }
}

#[test]
fn prune_reads_the_stamps_again_before_it_deletes() {
    crate::utils::tests::isolated(|| {
        // A stamp written after judging, in another tree, names a unit the judge doomed: the
        // safety net, which reads every tree's stamps again, refuses the deletion.
        let f = Fixture::new();
        let (_, u) = f.warm_compiler_tree();
        let other = f.tree("stage2-tools", Some(HOST), false);
        fs::create_dir_all(other.profile.join("deps")).unwrap();
        let stamp = other.profile.join(".tool-check-stamp");
        DOOMED.with(|d| *d.borrow_mut() = Some((stamp, u["middle_old"].rlib().to_owned())));
        let options = Options { objects: true, observe: Some(stamp_after_judging) };
        let summary = prune(&f.build, &f.host, &[], &options);
        assert!(left(&summary).contains(".tool-check-stamp names"), "{}", left(&summary));
        assert_unit(&u["middle_old"], true);
        assert_unit(&u["serde_old"], true);
    });
}

/// After judging stage1-rustc, moves its profile's `build/` outside the build directory
/// and leaves a link in its place, so each doomed path there resolves outside.
fn move_build_outside(tree: &Path, stage: Stage) {
    if stage == Stage::Judged && tree.ends_with("stage1-rustc") {
        let (outside, _) = DOOMED.with(|d| d.borrow().clone()).unwrap();
        let build = profile_dirs(tree).unwrap()[0].join("build");
        fs::create_dir_all(outside.parent().unwrap()).unwrap();
        fs::rename(&build, &outside).unwrap();
        symlink(&outside, &build).unwrap();
    }
}

#[test]
fn prune_refuses_a_doomed_path_that_resolves_outside_its_tree() {
    crate::utils::tests::isolated(|| {
        let f = Fixture::new();
        f.warm_compiler_tree();
        let outside = f.root.join("outside/build");
        DOOMED.with(|d| *d.borrow_mut() = Some((outside.clone(), PathBuf::new())));
        let options = Options { objects: true, observe: Some(move_build_outside) };
        let summary = prune(&f.build, &f.host, &[], &options);
        assert!(left(&summary).contains("is outside"), "{}", left(&summary));
        // The doomed unit, now behind the link, is whole: fingerprint and outputs.
        let moved = outside.join("rustc_middle/5555555555555555");
        assert!(moved.join("fingerprint").is_dir(), "{}", moved.display());
        assert!(moved.join("out/librustc_middle-5555555555555555.rlib").is_file());
    });
}

#[test]
fn manual_preview_keeps_every_artifact_and_never_marks_the_tree_clean() {
    crate::utils::tests::isolated(|| {
        let f = Fixture::new();
        let (_tree, live, old) = legacy_tree_with_a_superseded_variant(&f);
        let before = snapshot(&f.root);
        let options = Options { objects: false, observe: None };
        let preview = prune_selected(&f.build, &f.host, &[], &options, true, true);
        assert_eq!(preview.planned_units, 1);
        assert_eq!((preview.units, preview.objects, preview.bytes), (0, 0, 0));
        assert!(preview.skipped.is_empty(), "{preview:?}");
        // Cargo's exclusion sentinels can be created; artifact bytes and cleanup
        // stamps must be unchanged. Preview never writes the cache judgment.
        let after = snapshot(&f.root);
        for (path, value) in before {
            assert_eq!(after.get(&path), Some(&value), "{}", path.display());
        }
        for tree in target_trees(&f.build, &f.host).unwrap() {
            assert!(read_stamp(&tree).is_none(), "{}", tree.display());
        }
        assert_unit(&old, true);
        assert_unit(&live, true);
        let applied = prune_selected(&f.build, &f.host, &[], &options, true, false);
        assert_eq!(applied.units, 1, "{applied:?}");
        assert_unit(&old, false);
        assert_unit(&live, true);
    });
}

#[test]
fn an_objects_only_judgment_cannot_suppress_later_variant_cleanup() {
    crate::utils::tests::isolated(|| {
        let f = Fixture::new();
        let (_tree, live, old) = legacy_tree_with_a_superseded_variant(&f);
        let options = Options { objects: true, observe: None };
        let objects_only = prune_selected(&f.build, &f.host, &[], &options, false, false);
        assert_eq!(objects_only.units, 0);
        assert_unit(&old, true);
        let complete = prune_selected(&f.build, &f.host, &[], &options, true, false);
        assert_eq!(complete.units, 1, "{complete:?}");
        assert_eq!(complete.unchanged, 0);
        assert_unit(&old, false);
        assert_unit(&live, true);
    });
}

#[test]
#[cfg(any(target_os = "macos", target_os = "linux"))]
fn manual_cache_api_keeps_actual_original_guards_and_refuses_another_root() {
    crate::utils::tests::isolated(|| {
        let f = Fixture::new();
        let other = Fixture::new();
        let (_tree, live, old) = legacy_tree_with_a_superseded_variant(&f);
        let lease = native_prune_lease(&f);
        let output =
            build_helper::trust_output_lock::OutputLock::try_acquire(&f.build).unwrap().unwrap();
        let request =
            crate::cache::Request::new(&f.root, Path::new(HOST), true, false, true).unwrap();
        let preview = crate::cache::prune(&request, &lease, &output).unwrap();
        assert!(preview.dry_run && preview.is_complete(), "{preview:?}");
        assert_eq!((preview.planned_units, preview.removed_units), (1, 0));
        assert!(preview.space_observation_errors.is_empty(), "{preview:?}");
        let estimated = preview.planned_file_space.as_ref().unwrap().allocated_upper_bytes;
        assert!(estimated > 0, "the actual approved file inventory must be measured");
        assert!(preview.volume_space.is_some(), "the original output volume is held");
        assert_eq!(
            serde_json::to_value(&preview).unwrap()["planned_file_space"]["allocated_upper_bytes"],
            estimated,
        );
        assert_unit(&old, true);
        let foreign =
            crate::cache::Request::new(&other.root, Path::new(HOST), true, false, false).unwrap();
        assert!(crate::cache::prune(&foreign, &lease, &output).is_err());
        assert_unit(&old, true);
        let apply =
            crate::cache::Request::new(&f.root, Path::new(HOST), true, false, false).unwrap();
        let report = crate::cache::prune(&apply, &lease, &output).unwrap();
        assert!(report.is_complete(), "{report:?}");
        assert_eq!((report.planned_units, report.removed_units), (1, 1));
        assert!(report.space_observation_errors.is_empty(), "{report:?}");
        assert_eq!(report.planned_file_space.unwrap().allocated_upper_bytes, estimated);
        assert!(report.volume_space.is_some());
        lease.check_current().unwrap();
        output.check_current().unwrap();
        assert_unit(&old, false);
        assert_unit(&live, true);
    });
}

#[test]
fn manual_pruning_refuses_unknown_tree_census_and_preserves_cross_tree_stamp_roots() {
    crate::utils::tests::isolated(|| {
        assert!(!is_root(), "this native permissions control requires an ordinary account");
        for hide_host in [true, false] {
            let f = Fixture::new();
            let mut readable = CargoTree::new(&f.build.join("bootstrap-tools"), None, false);
            let live = readable.unit("retained", "1111111111111111", U::default());
            let protected = readable.unit(
                "retained",
                "2222222222222222",
                U { mtime: Some(500.0), ..U::default() },
            );
            readable.stamp(".tool-check-stamp", &[live.rlib()]);
            let hidden = f.tree("stage2-tools", Some(HOST), false);
            hidden.stamp(".librustc-stamp", &[protected.rlib()]);
            let lease = native_prune_lease(&f);
            let output = build_helper::trust_output_lock::OutputLock::try_acquire(&f.build)
                .unwrap()
                .unwrap();
            let request =
                crate::cache::Request::new(&f.root, Path::new(HOST), true, false, false).unwrap();
            let inaccessible = if hide_host { f.host.clone() } else { f.host.join("stage2-tools") };
            chmod(&inaccessible, 0);
            let result = crate::cache::prune(&request, &lease, &output);
            chmod(&inaccessible, 0o755);
            if !protected.rlib().exists() {
                let retained = f._tmp.keep();
                panic!(
                    "unknown tree census deleted a cross-tree stamped artifact; hide_host={hide_host}, failed inputs retained at {}",
                    retained.display()
                );
            }
            let report = result.unwrap();
            assert!(!report.is_complete(), "unknown census reported complete: {report:?}");
            assert_eq!((report.removed_units, report.removed_objects), (0, 0));
            assert_unit(&protected, true);
            assert_unit(&live, true);
            assert!(hidden.profile.join(".librustc-stamp").is_file());
        }
    });
}
