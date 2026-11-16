//! Regression tests for the two adversarial reviews of M2 (2026-10-01).
//!
//! The CHECKER review found programs the derivation passed although they are
//! dangerous (L2, L3, F1, F2, F3, F4: `Unknown` or no verdict) and correct
//! programs it refuted (L4, L4b, L5, L8, F5, F5b). The MODEL review found
//! Darwin behaviours the platform model lacked; the ones that change what a
//! derivation can reach are pinned here (the posix_spawn window, a waiting
//! FIFO open, a sleeping flock, a model deadlock reported instead of halted).
//! Every program is checked through NativeTyEngine (refutation-only payload),
//! as the acceptance fixtures are, and every refutation is explained and
//! RE-EXECUTED on the Rust model. False passes come first.

use trust_platform::call::FileAction;
use trust_platform::std_summaries::{CommandShape, CommandStd, StdioPlan};
use trust_platform::{Call, Errno, NodeKind, Oracle, darwin};
use trust_platform_derive::derive::{DeriveOptions, Derived};
use trust_platform_derive::env::EnvSpec;
use trust_platform_derive::fixtures::{self, m2_env};
use trust_platform_derive::interp::Role;
use trust_platform_derive::program::{
    Bind, BodyBuilder, EventProgram, Expr, FdInherit, Lane, Mutation, Operand, ProgramBuilder,
    StmtKind, VarId,
};
use trust_platform_derive::property;
use trust_platform_derive::trace::Replay;
use trust_router::full_verification::NativeTyEngine;
use trust_types::TY_TEMPORAL_MODEL_METADATA_KEY;
use trust_verifier_api::{
    BundleSubject, EvidenceStatus, MetadataEntry, ObligationKind, SourceLocation,
    TrustContractBundle, TrustObligation, VerificationEngine,
};

const L: &str = "adv-m2";
/// A canonical directory for the programs' files.
const DIR: &str = "/private/tmp/adv-m2";

fn ty(d: &Derived, formula: &str) -> (EvidenceStatus, Option<Vec<usize>>, Vec<String>) {
    let payload = d.payload(formula).unwrap_or_else(|e| panic!("`{formula}`: {e}"));
    let obligation = TrustObligation {
        obligation_id: format!("vc:adv-m2::{}:temporal_safety:{}", d.name(), formula.len()),
        kind: ObligationKind::TemporalSafety,
        contract_id: None,
        proof_item_id: None,
        source: SourceLocation::default(),
        description: format!("adv-m2 `{formula}`"),
        required_strength: None,
        summary_facts: Vec::new(),
        metadata: vec![MetadataEntry {
            key: TY_TEMPORAL_MODEL_METADATA_KEY.to_string(),
            value: payload.to_metadata_value().expect("serializes"),
        }],
    };
    let mut bundle = TrustContractBundle::empty(
        format!("bundle-{}", d.name()),
        BundleSubject::Function { crate_name: "adv".to_string(), path: d.name().clone() },
    );
    bundle.obligations.push(obligation.clone());
    let ev = NativeTyEngine::new().verify(&bundle, &[obligation]).remove(0);
    assert!(ev.proof_strength.is_none(), "a derived model never proves: {ev:?}");
    let trace = ev.counterexample.as_ref().and_then(|ce| {
        ce.data["trace"].as_array().map(|steps| {
            steps
                .iter()
                .map(|s| s["value"].as_str().and_then(|v| v.parse::<usize>().ok()).unwrap())
                .collect()
        })
    });
    (ev.status, trace, ev.diagnostics)
}

fn derive_ok(prog: &EventProgram, env: &EnvSpec) -> Derived {
    let d = trust_platform_derive::derive(prog, env, &DeriveOptions::default())
        .unwrap_or_else(|e| panic!("{}: derivation failed: {e}", prog.name));
    assert!(d.stats().encoding_exact, "{}: the scalar encoding must be injective", prog.name);
    d
}

#[derive(Clone, Copy)]
enum Prop {
    Lock,
    Ident,
}

fn formula(p: Prop) -> (String, &'static str, &'static str) {
    match p {
        Prop::Lock => {
            (property::lock_release_formula(), property::LOCK_LEAK, property::RELEASED_SHARED)
        }
        Prop::Ident => (
            property::fd_identity_formula(),
            property::FD_IDENTITY_VIOLATION,
            property::NUMBER_REUSED,
        ),
    }
}

/// Refuted by ty, and the trace re-executes to a state carrying the atom.
fn refuted(prog: &EventProgram, env: &EnvSpec, p: Prop) -> (Derived, Replay) {
    let d = derive_ok(prog, env);
    let (f, atom, _) = formula(p);
    let (status, trace, diags) = ty(&d, &f);
    assert_eq!(status, EvidenceStatus::Failed, "{}: `{f}` must be refuted: {diags:?}", d.name());
    let trace = trace.expect("a refutation carries a trace");
    let replay = d
        .replay(&trace, &[atom])
        .unwrap_or_else(|e| panic!("{}: the trace must re-execute: {e}", d.name()));
    assert!(!replay.findings.is_empty(), "{}: a refutation names its finding", d.name());
    (d, replay)
}

/// Not refuted (Unknown: refutation-only), and not vacuous: the dangerous
/// situation is reachable (a replayed refutation of `AG !<reach>`).
fn not_refuted(prog: &EventProgram, env: &EnvSpec, p: Prop) -> Derived {
    let d = derive_ok(prog, env);
    let (f, _, reach) = formula(p);
    let (status, _, diags) = ty(&d, &f);
    assert_eq!(
        status,
        EvidenceStatus::Unknown,
        "{}: `{f}` must not be refuted: {diags:?}",
        d.name()
    );
    let (status, trace, diags) = ty(&d, &format!("AG !{reach}"));
    assert_eq!(
        status,
        EvidenceStatus::Failed,
        "{}: `{reach}` must be reachable: {diags:?}",
        d.name()
    );
    d.replay(&trace.expect("a trace"), &[reach])
        .unwrap_or_else(|e| panic!("{}: the non-vacuity trace must re-execute: {e}", d.name()));
    d
}

fn events(r: &Replay) -> Vec<String> {
    r.steps.iter().flat_map(|s| s.events.clone()).collect()
}

fn path(name: &str) -> String {
    format!("{DIR}/{name}")
}

fn create(b: &mut BodyBuilder, file: &str, v: VarId, class: &str) {
    b.std_open(
        &format!("{L}: File::create({file})"),
        "std::fs::File::create",
        &path(file),
        darwin::O_WRONLY | darwin::O_CREAT | darwin::O_TRUNC,
        v,
        class,
    );
}

fn open_path(b: &mut BodyBuilder, loc: &str, file: &str, flags: i32, v: VarId, class: &str) {
    b.event_full(
        loc,
        "open",
        Call::OpenPath { at: None, path: path(file), flags },
        Bind::ret(v),
        vec![Oracle::Nominal],
        None,
        vec![class],
    );
}

fn flock(b: &mut BodyBuilder, loc: &str, fd: VarId, op: i32, rc: Option<VarId>) {
    b.event(
        loc,
        "flock",
        Call::Flock { fd: Operand::Var(fd), op },
        rc.map_or_else(Bind::none, Bind::ret),
    );
}

fn close(b: &mut BodyBuilder, loc: &str, fd: VarId) {
    b.event(loc, "close", Call::Close { fd: Operand::Var(fd) }, Bind::none());
}

fn getfd(b: &mut BodyBuilder, loc: &str, fd: Operand, out: VarId) {
    b.event(loc, "fcntl", Call::Fcntl { fd, cmd: darwin::F_GETFD, arg: 0 }, Bind::ret(out));
}

/// RL-HARNESS: a sibling test that forks a child which execs.
fn sibling_fork(p: &mut ProgramBuilder) -> usize {
    let site = p.site("sibling_spawn", &format!("{L}: sibling fork"), None);
    let pid = p.var("sibling.pid", -1);
    let child = p.body("sibling child", Vec::new(), |b| {
        b.event(&format!("{L}: sibling execvp"), "execvp", Call::Exec, Bind::none());
    });
    let body = p.body("sibling test", Vec::new(), |b| {
        b.fork(&format!("{L}: sibling fork"), child, site, Some(pid));
    });
    p.root("sibling test (RL-HARNESS)", body)
}

/// RL-HARNESS: a sibling test that opens /dev/null and drops it.
fn squatter(p: &mut ProgramBuilder, tag: &str) -> usize {
    let sq = p.var(&format!("{tag}.fd"), -1);
    let body = p.body(tag, Vec::new(), |b| {
        b.std_open(
            &format!("{L}: {tag}: File::open(/dev/null)"),
            "std::fs::File::open",
            "/dev/null",
            darwin::O_RDONLY,
            sq,
            tag,
        );
        close(b, &format!("{L}: {tag}: drop"), sq);
    });
    p.root(tag, body)
}

fn lock_env() -> EnvSpec {
    m2_env(&[])
}

fn null_env() -> EnvSpec {
    m2_env(&[("/dev/null", NodeKind::CharDevice)])
}

/// A held lock, let go by a bare close (the bug-1 shape), with a sibling fork.
fn bare_close_program(
    name: &str,
    release_how: impl FnOnce(&mut BodyBuilder, VarId),
) -> EventProgram {
    let mut p = ProgramBuilder::new(name);
    p.lock_release_policy();
    let fd = p.var("fd", -1);
    let main = p.body("main", Vec::new(), |b| {
        create(b, "lock", fd, "holder");
        flock(b, &format!("{L}: flock EX|NB"), fd, darwin::LOCK_EX | darwin::LOCK_NB, None);
        release_how(b, fd);
    });
    p.root("main", main);
    sibling_fork(&mut p);
    p.build()
}

// ===========================================================================
// FALSE PASSES (the checker's (a) list): dangerous programs that came back
// Unknown or with no verdict. Each must now be refuted.
// ===========================================================================

/// L2: the owner keeps a forgotten clone of the locked description, closes
/// the original and marks its release; the lock is still held (a probe of the
/// file reads LIVE). Before: `lock_leaks` skipped any description the owner
/// still referenced.
#[test]
fn l2_a_clone_the_owner_kept_holds_its_lock_past_its_release() {
    let mut p = ProgramBuilder::new("l2_owner_keeps_a_clone");
    p.lock_release_policy();
    let fd = p.var("fd", -1);
    let clone = p.var("clone", -1);
    let probe = p.var("probe", -1);
    let prc = p.var("probe.rc", 99);
    let main = p.body("main", Vec::new(), |b| {
        create(b, "lock", fd, "holder");
        flock(b, "l2: flock EX|NB", fd, darwin::LOCK_EX | darwin::LOCK_NB, None);
        b.std_row(
            "l2: file.try_clone()",
            "std::os::fd::BorrowedFd::try_clone_to_owned",
            vec![Operand::Var(fd)],
            vec![clone],
            vec!["holder"],
        );
        close(b, "l2: drop(file)", fd);
        b.release("l2: release point (the clone is forgotten in a struct)", &["holder"]);
        let flags = darwin::O_NOFOLLOW | darwin::O_NONBLOCK | darwin::O_CLOEXEC;
        open_path(b, "l2: probe open", "lock", flags, probe, "probe");
        flock(b, "l2: probe flock EX|NB", probe, darwin::LOCK_EX | darwin::LOCK_NB, Some(prc));
        close(b, "l2: probe close", probe);
    });
    p.root("main", main);
    let (_, r) = refuted(&p.build(), &lock_env(), Prop::Lock);
    assert!(r.findings[0].contains("the owner"), "{:?}", r.findings);
}

/// L3: bug 1's production shape — the owner process EXITS after a bare
/// close while a sibling's child holds the copy. Before: "unsupported: exec/
/// exit of the root process". The owner's exit lets go of everything.
#[test]
fn l3_the_owner_exits_and_its_childs_copy_keeps_the_lock() {
    let prog = bare_close_program("l3_owner_exits", |b, fd| {
        close(b, "l3: drop(file)", fd);
        b.event("l3: _exit(0)", "_exit", Call::Exit { status: 0 }, Bind::none());
    });
    let (_, r) = refuted(&prog, &lock_env(), Prop::Lock);
    let ev = events(&r);
    assert!(ev.iter().any(|e| e.contains("_exit(0)")), "{ev:#?}");
    assert!(r.findings[0].contains("child[sibling_spawn]"), "{:?}", r.findings);
}

/// F1: a hole below the retired number. `a = open; b = open; close(a);
/// close(b); F_GETFD(b)` with ONE squatter: lowest-free over the modeled
/// table always fills `a`'s slot, but on the kernel any unmodeled allocation
/// fills the hole and the squatter lands on `b`. Before: Unknown (0 of 52
/// states). RL-FOREIGN may now squat on any retired number.
#[test]
fn f1_a_retired_number_above_a_hole_is_reused() {
    let mut p = ProgramBuilder::new("f1_hole_below_the_retired_number");
    let a = p.var("a", -1);
    let bb = p.var("b", -1);
    let r = p.var("r", 99);
    let main = p.body("main", Vec::new(), |b| {
        b.std_open("f1: open a", "std::fs::File::open", "/dev/null", darwin::O_RDONLY, a, "a");
        b.std_open("f1: open b", "std::fs::File::open", "/dev/null", darwin::O_RDONLY, bb, "b");
        close(b, "f1: close(a)", a);
        close(b, "f1: close(b)", bb);
        getfd(b, "f1: F_GETFD(b) — 'b is closed'", Operand::Var(bb), r);
    });
    let m = p.root("main", main);
    p.fd_identity_policy(&[m]);
    squatter(&mut p, "squatter");
    let (_, r) = refuted(&p.build(), &null_env(), Prop::Ident);
    assert!(r.findings[0].contains("fd 4"), "{:?}", r.findings);
}

/// F2: aterm c88946be1's `adopt_refuses_what_cannot_be_a_lifeline` — the
/// scan finds 64 free (`F_GETFD(64)`), then `adopt(64)` `F_GETFD`s it again;
/// a test on another thread may take 64 in between (the race d5e08bf1b also
/// fixed). Before: Unknown — no modeled allocation could land on 64.
#[test]
fn f2_a_number_found_free_is_taken_before_it_is_used() {
    let mut p = ProgramBuilder::new("f2_adopt_refuses_found_free_number");
    let scan = p.var("scan.r", 99);
    let closed = p.var("closed", -1);
    let r = p.var("adopt.r", 99);
    let at = |line: &str| format!("aterm@c88946be1:crates/aterm-uds/src/lifeline.rs:{line}");
    let main = p.body("adopt_refuses_what_cannot_be_a_lifeline (tail)", Vec::new(), |b| {
        getfd(b, &at("847 fd_flags(64) == -1"), Operand::Lit(64), scan);
        b.assign(&at("846 closed = 64"), closed, Expr::Use(Operand::Lit(64)));
        getfd(b, &at("213 adopt: fcntl(number, F_GETFD)"), Operand::Var(closed), r);
    });
    let m = p.root("main", main);
    p.fd_identity_policy(&[m]);
    let (_, rep) = refuted(&p.build(), &null_env(), Prop::Ident);
    assert!(
        rep.findings[0].contains("fd 64") && rep.findings[0].contains(":213"),
        "{:?}",
        rep.findings
    );
    assert!(events(&rep).iter().any(|e| e.contains("RL-FOREIGN")), "{:#?}", events(&rep));
}

/// F3: a stale number handed across fork and exec — the descriptor is
/// closed, a squatter takes the number, then a forked child un-flags that
/// number for its image. Before: Unknown (a forked child started with no
/// bindings and was never checked). The posix_spawn `addinherit_np` form was
/// already refuted; both are now.
#[test]
fn f3_a_stale_number_is_handed_to_an_exec_d_image() {
    for spawn in [false, true] {
        let name =
            if spawn { "f3b_stale_number_posix_spawn" } else { "f3_stale_number_fork_child" };
        let mut p = ProgramBuilder::new(name);
        let fd = p.var("fd", -1);
        let pid = p.var("pid", -1);
        let site = p.site("handoff", "f3: fork", None);
        let child = p.body("child", Vec::new(), |b| {
            b.event(
                "f3: child fcntl(fd, F_SETFD, 0) — hand fd to the image",
                "fcntl",
                Call::Fcntl { fd: Operand::Var(fd), cmd: darwin::F_SETFD, arg: 0 },
                Bind::none(),
            );
            b.event("f3: child execve", "execve", Call::Exec, Bind::none());
        });
        let main = p.body("main", Vec::new(), |b| {
            b.std_open(
                "f3: open",
                "std::fs::File::open",
                "/dev/null",
                darwin::O_RDONLY,
                fd,
                "mine",
            );
            close(b, "f3: close(fd) (retired early)", fd);
            if spawn {
                b.event_full(
                    "f3b: posix_spawn(addinherit_np(fd))",
                    "posix_spawn",
                    Call::Spawn {
                        actions: vec![FileAction::Inherit { fd: Operand::Var(fd) }],
                        flags: darwin::POSIX_SPAWN_CLOEXEC_DEFAULT,
                    },
                    Bind::ret(pid),
                    vec![Oracle::Nominal],
                    Some(site),
                    Vec::new(),
                );
            } else {
                b.fork("f3: fork", child, site, Some(pid));
            }
        });
        let m = p.root("main", main);
        p.fd_identity_policy(&[m]);
        squatter(&mut p, "squatter");
        let (_, r) = refuted(&p.build(), &null_env(), Prop::Ident);
        if !spawn {
            assert!(r.findings[0].contains("child[handoff]"), "{:?}", r.findings);
        }
    }
}

/// F4: a checked thread started by an UNCHECKED creator uses a captured
/// number after the creator closed it. Before: Unknown (bindings were copied
/// only between two checked threads, so the first use bound whatever was
/// there).
#[test]
fn f4_a_checked_thread_inherits_an_unchecked_creators_bindings() {
    let mut p = ProgramBuilder::new("f4_unchecked_creator");
    let fd = p.var("fd", -1);
    let r = p.var("r", 99);
    let worker_body = p.body("worker", Vec::new(), |b| {
        getfd(b, "f4: worker F_GETFD(fd) (captured number)", Operand::Var(fd), r);
    });
    let w = p.thread("worker", worker_body);
    let main = p.body("main", Vec::new(), |b| {
        b.std_open("f4: open", "std::fs::File::open", "/dev/null", darwin::O_RDONLY, fd, "mine");
        b.spawn_thread("f4: spawn worker(fd)", w);
        close(b, "f4: close(fd)", fd);
        b.join("f4: join", w);
    });
    p.root("main", main);
    p.fd_identity_policy(&[w]);
    squatter(&mut p, "squatter");
    let (_, rep) = refuted(&p.build(), &null_env(), Prop::Ident);
    assert!(rep.findings[0].starts_with("worker"), "{:?}", rep.findings);
}

// ===========================================================================
// FALSE REFUTATIONS (the checker's (b) list): correct programs that were
// refuted. Each must now be Unknown, and not vacuously.
// ===========================================================================

/// L4: a DELIBERATE hand-off — the launcher locks, forks the daemon, whose
/// setup un-flags the lock's descriptor (declared) and execs; the launcher
/// closes its copy and returns. L4b: the launcher never locks; the child
/// takes the lock itself after the launcher let go (the child's lock, not
/// the owner's).
#[test]
fn l4_a_declared_hand_off_and_a_childs_own_lock_are_not_leaks() {
    for takeover in [false, true] {
        let name = if takeover { "l4b_child_takes_over_the_lock" } else { "l4_handoff_to_daemon" };
        let mut p = ProgramBuilder::new(name);
        p.lock_release_policy();
        let fd = p.var("fd", -1);
        let pid = p.var("pid", -1);
        let site = p.site("daemon", "l4: fork the daemon", None);
        let child = p.body("daemon child", Vec::new(), |b| {
            if takeover {
                flock(
                    b,
                    "l4b: child flock EX (takes over)",
                    fd,
                    darwin::LOCK_EX | darwin::LOCK_NB,
                    None,
                );
            }
            b.event(
                "l4: child fcntl(fd, F_SETFD, 0): the daemon inherits the lock",
                "fcntl",
                Call::Fcntl { fd: Operand::Var(fd), cmd: darwin::F_SETFD, arg: 0 },
                Bind::none(),
            );
            b.event("l4: child execve(daemon)", "execve", Call::Exec, Bind::none());
        });
        let main = p.body("launch_daemon_with_lock", Vec::new(), |b| {
            create(b, "instance.lock", fd, "instance_lock");
            if !takeover {
                flock(b, "l4: flock EX|NB", fd, darwin::LOCK_EX | darwin::LOCK_NB, None);
            }
            b.fork("l4: fork", child, site, Some(pid));
            close(b, "l4: drop(file) in the launcher", fd);
            b.release("l4: launch_daemon_with_lock returns", &["instance_lock"]);
        });
        p.root("launcher", main);
        not_refuted(&p.build(), &lock_env(), Prop::Lock);
    }
}

/// The control for L4: the same launcher whose child execs WITHOUT
/// un-flagging the descriptor — its copy is close-on-exec, so between the
/// fork and the exec it holds the owner's lock past the owner's release (bug
/// 1): still a leak.
#[test]
fn l4c_an_undeclared_copy_is_still_a_leak() {
    let mut p = ProgramBuilder::new("l4c_undeclared_copy");
    p.lock_release_policy();
    let fd = p.var("fd", -1);
    let pid = p.var("pid", -1);
    let site = p.site("helper", "l4c: fork a helper", None);
    let child = p.body("helper child", Vec::new(), |b| {
        b.event("l4c: child execve(helper)", "execve", Call::Exec, Bind::none());
    });
    let main = p.body("launch_helper", Vec::new(), |b| {
        create(b, "instance.lock", fd, "instance_lock");
        flock(b, "l4c: flock EX|NB", fd, darwin::LOCK_EX | darwin::LOCK_NB, None);
        b.fork("l4c: fork", child, site, Some(pid));
        close(b, "l4c: drop(file)", fd);
        b.release("l4c: returns", &["instance_lock"]);
    });
    p.root("launcher", main);
    refuted(&p.build(), &lock_env(), Prop::Lock);
}

/// The hand-off declared by the SITE (its policy lane names the lock's class
/// at the number the child holds it): not a leak at any point, before the
/// child's exec included.
#[test]
fn l4d_a_lane_declared_hand_off_is_not_a_leak() {
    let mut p = ProgramBuilder::new("l4d_lane_declared_hand_off");
    p.lock_release_policy();
    let fd = p.var("fd", -1);
    let pid = p.var("pid", -1);
    let lanes = vec![Lane { fd: 3, ofd_class: "instance_lock".to_string() }];
    let site = p.site("daemon", "l4d: fork the daemon", Some(FdInherit { lanes }));
    let child = p.body("daemon child", Vec::new(), |b| {
        b.event(
            "l4d: child fcntl(3, F_SETFD, 0)",
            "fcntl",
            Call::Fcntl { fd: Operand::Lit(3), cmd: darwin::F_SETFD, arg: 0 },
            Bind::none(),
        );
        b.event("l4d: child execve(daemon)", "execve", Call::Exec, Bind::none());
    });
    let main = p.body("launch_daemon_with_lock", Vec::new(), |b| {
        create(b, "instance.lock", fd, "instance_lock");
        flock(b, "l4d: flock EX|NB", fd, darwin::LOCK_EX | darwin::LOCK_NB, None);
        b.fork("l4d: fork", child, site, Some(pid));
        close(b, "l4d: drop(file)", fd);
        b.release("l4d: returns", &["instance_lock"]);
    });
    p.root("launcher", main);
    not_refuted(&p.build(), &lock_env(), Prop::Lock);
}

/// L5: the leaked lock is on a node no name reaches — unlinked before the
/// bare close (crash_signal::markers, atpkg::lease::take). Nobody can open the
/// file again to contend for the lock: not a leak anyone sees.
#[test]
fn l5_a_lock_on_an_unlinked_file_nobody_holds_open_is_unobservable() {
    let prog = bare_close_program("l5_unlink_then_bare_close", |b, fd| {
        b.event(
            "l5: remove_file(path)",
            "unlink",
            Call::Unlink { path: path("lock") },
            Bind::none(),
        );
        close(b, "l5: drop(file)", fd);
        b.release("l5: release point", &["holder"]);
    });
    not_refuted(&prog, &lock_env(), Prop::Lock);
}

/// L5's control: unlinked, but another description on the node (opened
/// before the unlink) can still contend: a leak someone sees.
#[test]
fn l5b_an_unlinked_file_someone_holds_open_still_shows_the_lock() {
    let mut p = ProgramBuilder::new("l5b_unlinked_but_open");
    p.lock_release_policy();
    let fd = p.var("fd", -1);
    let other = p.var("other", -1);
    let main = p.body("main", Vec::new(), |b| {
        create(b, "lock", fd, "holder");
        open_path(
            b,
            "l5b: another open",
            "lock",
            darwin::O_RDONLY | darwin::O_CLOEXEC,
            other,
            "other",
        );
        flock(b, "l5b: flock EX|NB", fd, darwin::LOCK_EX | darwin::LOCK_NB, None);
        b.event(
            "l5b: remove_file(path)",
            "unlink",
            Call::Unlink { path: path("lock") },
            Bind::none(),
        );
        close(b, "l5b: drop(file)", fd);
        b.release("l5b: release point", &["holder"]);
    });
    p.root("main", main);
    sibling_fork(&mut p);
    refuted(&p.build(), &lock_env(), Prop::Lock);
}

/// L8: the builder's own sweep fixture with only the done path's `LOCK_UN`
/// deleted (the lease was unlinked at 2150 before the drop at 2156): not a
/// leak anyone sees, so that `LOCK_UN` is not load-bearing.
#[test]
fn l8_the_sweeps_done_path_lock_un_is_not_load_bearing() {
    let f = fixtures::instance_lease::sweep_unlock_first();
    let mut prog =
        f.program.mutate(&Mutation::DeleteStmt("unlock_on_done".to_string())).expect("mutates");
    // validate_path_identity always succeeds: the continue path is dead.
    for body in &mut prog.bodies {
        for block in &mut body.blocks {
            for s in &mut block.stmts {
                if let StmtKind::Event(ev) = &mut s.kind
                    && ev.oracles.len() > 1
                {
                    ev.oracles = vec![Oracle::Nominal];
                }
            }
        }
    }
    prog.name = "l8_sweep_done_path_only".to_string();
    not_refuted(&prog, &f.env, Prop::Lock);
}

/// F5: a DELIBERATE re-bind ordered by `join` (a log reopened in place: the
/// helper `dup2`s the new log onto the log's number; main joins it, then uses
/// the number). Before: refuted — bindings ignored happens-before.
#[test]
fn f5_a_join_ordered_re_bind_is_not_a_violation() {
    for checked_helper in [false, true] {
        let name =
            if checked_helper { "f5b_rebind_helper_checked" } else { "f5_rebind_helper_unchecked" };
        let mut p = ProgramBuilder::new(name);
        let log = p.var("log", -1);
        let new = p.var("new", -1);
        let r = p.var("r", 99);
        let helper_body = p.body("reopen helper", Vec::new(), |b| {
            let flags = darwin::O_WRONLY | darwin::O_CREAT | darwin::O_CLOEXEC;
            open_path(b, "f5: open(log.1)", "log.1", flags, new, "log_new");
            b.event(
                "f5: dup2(new, log) — reopen in place",
                "dup2",
                Call::Dup2 { from: Operand::Var(new), to: Operand::Var(log) },
                Bind::none(),
            );
            close(b, "f5: close(new)", new);
        });
        let h = p.thread("reopen", helper_body);
        let main = p.body("main", Vec::new(), |b| {
            let flags = darwin::O_WRONLY | darwin::O_CREAT | darwin::O_CLOEXEC;
            open_path(b, "f5: open(log)", "log", flags, log, "log_old");
            getfd(b, "f5: use log (before)", Operand::Var(log), r);
            b.spawn_thread("f5: spawn reopen", h);
            b.join("f5: join reopen (happens-before)", h);
            getfd(b, "f5: use log (after: the new log, by design)", Operand::Var(log), r);
        });
        let m = p.root("main", main);
        if checked_helper {
            p.fd_identity_policy(&[m, h]);
        } else {
            p.fd_identity_policy(&[m]);
        }
        not_refuted(&p.build(), &lock_env(), Prop::Ident);
    }
}

/// F5's control: the same re-bind WITHOUT the join — main's use races the
/// helper's dup2: a violation.
#[test]
fn f5c_an_unordered_re_bind_is_a_violation() {
    let mut p = ProgramBuilder::new("f5c_rebind_unordered");
    let log = p.var("log", -1);
    let new = p.var("new", -1);
    let r = p.var("r", 99);
    let helper_body = p.body("reopen helper", Vec::new(), |b| {
        let flags = darwin::O_WRONLY | darwin::O_CREAT | darwin::O_CLOEXEC;
        open_path(b, "f5c: open(log.1)", "log.1", flags, new, "log_new");
        b.event(
            "f5c: dup2(new, log)",
            "dup2",
            Call::Dup2 { from: Operand::Var(new), to: Operand::Var(log) },
            Bind::none(),
        );
        close(b, "f5c: close(new)", new);
    });
    let h = p.thread("reopen", helper_body);
    let main = p.body("main", Vec::new(), |b| {
        let flags = darwin::O_WRONLY | darwin::O_CREAT | darwin::O_CLOEXEC;
        open_path(b, "f5c: open(log)", "log", flags, log, "log_old");
        b.spawn_thread("f5c: spawn reopen", h);
        getfd(b, "f5c: use log (unordered)", Operand::Var(log), r);
        b.join("f5c: join", h);
    });
    let m = p.root("main", main);
    p.fd_identity_policy(&[m]);
    refuted(&p.build(), &lock_env(), Prop::Ident);
}

// ===========================================================================
// The checker's controls, and the encoding note.
// ===========================================================================

#[test]
fn controls_stay_refuted() {
    // L0: bare close with a sibling fork.
    let l0 = bare_close_program("l0_control_bare_close", |b, fd| {
        close(b, "l0: drop(file)", fd);
        b.release("l0: release point", &["holder"]);
    });
    refuted(&l0, &lock_env(), Prop::Lock);
    // L1 / L1b: the lock taken through a dup, and through an fdesc alias (the
    // alias's operand spelled as the path's literal, as the census requires).
    for alias in [false, true] {
        let mut p = ProgramBuilder::new(if alias { "l1b_devfd_alias" } else { "l1_dup" });
        p.lock_release_policy();
        let fd = p.var("fd", -1);
        let d2 = p.var("d2", -1);
        let main = p.body("main", Vec::new(), |b| {
            create(b, "lock", fd, "holder");
            if alias {
                let flags = darwin::O_WRONLY | darwin::O_CLOEXEC;
                b.open(
                    "l1b: open(/dev/fd/3)",
                    "/dev/fd/3",
                    Call::OpenAlias { fd: Operand::Lit(3), flags },
                    Bind::ret(d2),
                    "holder",
                );
            } else {
                b.event("l1: dup(fd)", "dup", Call::Dup { fd: Operand::Var(fd) }, Bind::ret(d2));
            }
            flock(b, "l1: flock(d2) EX|NB", d2, darwin::LOCK_EX | darwin::LOCK_NB, None);
            close(b, "l1: close(d2)", d2);
            close(b, "l1: close(fd)", fd);
            b.release("l1: release point", &["holder"]);
        });
        p.root("main", main);
        sibling_fork(&mut p);
        refuted(&p.build(), &lock_env(), Prop::Lock);
    }
    // L6: O_EXLOCK taken by a creating open (now: create, then lock).
    let mut p = ProgramBuilder::new("l6_o_exlock_bare_close");
    p.lock_release_policy();
    let fd = p.var("fd", -1);
    let main = p.body("main", Vec::new(), |b| {
        let flags = darwin::O_RDWR
            | darwin::O_CREAT
            | darwin::O_EXLOCK
            | darwin::O_NONBLOCK
            | darwin::O_CLOEXEC;
        open_path(b, "l6: open(O_EXLOCK|O_NONBLOCK|O_CREAT)", "lock", flags, fd, "holder");
        close(b, "l6: close", fd);
        b.release("l6: release point", &["holder"]);
    });
    p.root("main", main);
    sibling_fork(&mut p);
    refuted(&p.build(), &lock_env(), Prop::Lock);
    // L7: the owner's logger thread re-takes the lock through a clone after
    // the release point.
    let mut p = ProgramBuilder::new("l7_relock_through_clone_after_release");
    p.lock_release_policy();
    let fd = p.var("fd", -1);
    let clone = p.var("clone", -1);
    let t_body = p.body("logger thread", Vec::new(), |b| {
        flock(b, "l7: logger flock(clone) EX", clone, darwin::LOCK_EX | darwin::LOCK_NB, None);
        close(b, "l7: logger drop(clone)", clone);
    });
    let t = p.thread("logger", t_body);
    let main = p.body("main", Vec::new(), |b| {
        create(b, "lock", fd, "holder");
        flock(b, "l7: flock EX|NB", fd, darwin::LOCK_EX | darwin::LOCK_NB, None);
        b.std_row(
            "l7: file.try_clone() for the logger",
            "std::os::fd::BorrowedFd::try_clone_to_owned",
            vec![Operand::Var(fd)],
            vec![clone],
            vec!["holder"],
        );
        b.spawn_thread("l7: spawn logger", t);
        flock(b, "l7: LOCK_UN", fd, darwin::LOCK_UN, None);
        close(b, "l7: drop(file)", fd);
        b.release("l7: release point", &["holder"]);
        b.join("l7: join logger", t);
    });
    p.root("main", main);
    sibling_fork(&mut p);
    refuted(&p.build(), &lock_env(), Prop::Lock);
    // F0: a retired lowest-free number taken by a squatter; F6: an fstat
    // check, then a use.
    for fstat_first in [false, true] {
        let mut p =
            ProgramBuilder::new(if fstat_first { "f6_fstat_then_use" } else { "f0_control" });
        let fd = p.var("fd", -1);
        let node = p.var("node", -1);
        let r = p.var("r", 99);
        let main = p.body("main", Vec::new(), |b| {
            b.std_open(
                "f0: open",
                "std::fs::File::open",
                "/dev/null",
                darwin::O_RDONLY,
                fd,
                "mine",
            );
            close(b, "f0: close(fd)", fd);
            if fstat_first {
                b.event(
                    "f6: fstat(fd): 'is it still ours?'",
                    "fstat",
                    Call::Fstat { fd: Operand::Var(fd) },
                    Bind { ret: Some(node), ret2: None, rlim_soft: None },
                );
            }
            getfd(b, "f0: act on fd", Operand::Var(fd), r);
        });
        let m = p.root("main", main);
        p.fd_identity_policy(&[m]);
        squatter(&mut p, "squatter");
        refuted(&p.build(), &null_env(), Prop::Ident);
    }
}

/// The checker's note: F1 with two squatters had a non-injective encoding
/// (the stored violation's text was not encoded). It is exact now.
#[test]
fn the_identity_violation_is_encoded() {
    let mut p = ProgramBuilder::new("f1_two_squatters");
    let a = p.var("a", -1);
    let bb = p.var("b", -1);
    let r = p.var("r", 99);
    let main = p.body("main", Vec::new(), |b| {
        b.std_open("f1: open a", "std::fs::File::open", "/dev/null", darwin::O_RDONLY, a, "a");
        b.std_open("f1: open b", "std::fs::File::open", "/dev/null", darwin::O_RDONLY, bb, "b");
        close(b, "f1: close(a)", a);
        close(b, "f1: close(b)", bb);
        getfd(b, "f1: F_GETFD(b)", Operand::Var(bb), r);
    });
    let m = p.root("main", main);
    p.fd_identity_policy(&[m]);
    squatter(&mut p, "squatter0");
    squatter(&mut p, "squatter1");
    refuted(&p.build(), &null_env(), Prop::Ident);
}

// ===========================================================================
// The model review's findings, where a derivation reaches them.
// ===========================================================================

/// F1 (HIGH): a bare close of a close-on-exec lock while another thread
/// spawns through std's plain `Command::spawn` (posix_spawn): the spawn's
/// child holds a copy of the whole table, close-on-exec entries included,
/// until its image is activated. Before: posix_spawn was one event, and the
/// lock-release check passed this program.
#[test]
fn mr_f1_a_posix_spawn_window_keeps_a_close_on_exec_lock() {
    for unlock_first in [false, true] {
        let name = if unlock_first { "mr_f1_unlock_then_close" } else { "mr_f1_spawn_window" };
        let mut p = ProgramBuilder::new(name);
        p.lock_release_policy();
        let fd = p.var("fd", -1);
        let main = p.body("main", Vec::new(), |b| {
            create(b, "lock", fd, "holder");
            flock(b, "mr-f1: flock EX|NB", fd, darwin::LOCK_EX | darwin::LOCK_NB, None);
            if unlock_first {
                flock(b, "mr-f1: LOCK_UN", fd, darwin::LOCK_UN, None);
            }
            close(b, "mr-f1: drop(file)", fd);
            b.release("mr-f1: release point", &["holder"]);
        });
        p.root("main", main);
        let site = p.site("spawner", "mr-f1: Command::new(\"/usr/bin/true\").spawn()", None);
        let pid = p.var("spawned", -1);
        let spawner = p.body("spawner thread", Vec::new(), |b| {
            b.spawn(
                "mr-f1: Command::new(\"/usr/bin/true\").spawn()",
                [StdioPlan::Inherit; 3],
                CommandShape::default().under(CommandStd::Upstream),
                Vec::new(),
                site,
                Some(pid),
            );
        });
        p.root("spawner", spawner);
        if unlock_first {
            not_refuted(&p.build(), &lock_env(), Prop::Lock);
        } else {
            let (_, r) = refuted(&p.build(), &lock_env(), Prop::Lock);
            let ev = events(&r);
            assert!(
                ev.iter().any(|e| e.contains("the child's copy of the table")),
                "the leak is the spawn's window: {ev:#?}"
            );
            assert!(r.findings[0].contains("child[spawner]"), "{:?}", r.findings);
        }
    }
}

/// F1, the CLOEXEC_DEFAULT lane spawner (aterm's `pspawn`), failing: the
/// window is there even for a spawn that fails.
#[test]
fn mr_f1_a_failing_cloexec_default_spawn_has_the_window_too() {
    let mut p = ProgramBuilder::new("mr_f1_failing_lane_spawn");
    p.lock_release_policy();
    let fd = p.var("fd", -1);
    let main = p.body("main", Vec::new(), |b| {
        create(b, "lock", fd, "holder");
        flock(b, "mr-f1: flock EX|NB", fd, darwin::LOCK_EX | darwin::LOCK_NB, None);
        close(b, "mr-f1: drop(file)", fd);
        b.release("mr-f1: release point", &["holder"]);
    });
    p.root("main", main);
    let site = p.site("lane", "mr-f1: posix_spawn(CLOEXEC_DEFAULT) of a missing image", None);
    let pid = p.var("spawned", -1);
    let spawner = p.body("lane spawner", Vec::new(), |b| {
        b.event_full(
            "mr-f1: posix_spawn(..., CLOEXEC_DEFAULT) of a missing image",
            "posix_spawn",
            Call::Spawn { actions: Vec::new(), flags: darwin::POSIX_SPAWN_CLOEXEC_DEFAULT },
            Bind::ret(pid),
            vec![Oracle::Fail(Errno::ENOENT)],
            Some(site),
            Vec::new(),
        );
    });
    p.root("lane spawner", spawner);
    refuted(&p.build(), &lock_env(), Prop::Lock);
}

/// F2: two threads rendezvous on a FIFO with BLOCKING opens (one reads, one
/// writes). Before: both opens were `Blocks` forever and the derivation
/// halted silently. Now both complete, and no state is stuck.
#[test]
fn mr_f2_blocking_fifo_opens_rendezvous() {
    let mut p = ProgramBuilder::new("mr_f2_fifo_rendezvous");
    let r = p.var("r", -1);
    let w = p.var("w", -1);
    let fifo = path("fifo");
    let writer = p.body("writer", Vec::new(), |b| {
        b.event(
            "mr-f2: open(fifo, O_WRONLY)",
            "open",
            Call::OpenPath {
                at: None,
                path: fifo.clone(),
                flags: darwin::O_WRONLY | darwin::O_CLOEXEC,
            },
            Bind::ret(w),
        );
    });
    let t = p.thread("writer", writer);
    let main = p.body("main", Vec::new(), |b| {
        b.event("mr-f2: mkfifo", "mkfifo", Call::Mkfifo { path: fifo.clone() }, Bind::none());
        b.spawn_thread("mr-f2: spawn writer", t);
        b.event(
            "mr-f2: open(fifo, O_RDONLY)",
            "open",
            Call::OpenPath {
                at: None,
                path: fifo.clone(),
                flags: darwin::O_RDONLY | darwin::O_CLOEXEC,
            },
            Bind::ret(r),
        );
        b.join("mr-f2: join writer", t);
    });
    p.root("main", main);
    let d = derive_ok(&p.build(), &lock_env());
    assert_eq!(d.stats().stuck_states, 0, "{:?}", d.notes());
    let both = d.graph().configs.iter().any(|c| {
        c.actors.iter().all(|a| a.done())
            && c.actors.iter().any(|a| a.role == Role::Thread(1) && a.vars[r] >= 3)
    });
    assert!(both, "both opens complete");
}

/// F2's other half: a model DEADLOCK is reported, not a silent halt — a
/// read open of a FIFO no one will ever write waits forever.
#[test]
fn mr_f2_a_stuck_state_is_named() {
    let mut p = ProgramBuilder::new("mr_f2_stuck");
    let r = p.var("r", -1);
    let fifo = path("lonely");
    let main = p.body("main", Vec::new(), |b| {
        b.event("mkfifo", "mkfifo", Call::Mkfifo { path: fifo.clone() }, Bind::none());
        b.event(
            "open(fifo, O_RDONLY): no writer, ever",
            "open",
            Call::OpenPath { at: None, path: fifo.clone(), flags: darwin::O_RDONLY },
            Bind::ret(r),
        );
    });
    p.root("main", main);
    let d = derive_ok(&p.build(), &lock_env());
    assert!(d.stats().stuck_states > 0);
    assert!(d.notes().iter().any(|n| n.starts_with("STUCK:")), "{:?}", d.notes());
}

/// F5: a thread sleeping in a blocking `flock` while another closes its
/// number: the close waits for the flock, which returns 0 (the lock taken on
/// the description being closed) once the holder lets go. Before: the close
/// went through at once and the re-evaluated flock returned EBADF — an outcome
/// Darwin never gives to a flock that was already sleeping.
#[test]
fn mr_f5_a_close_waits_for_a_sleeping_flock() {
    for releaser in [true, false] {
        let name = if releaser { "mr_f5_close_waits" } else { "mr_f5_close_deadlocks" };
        let mut p = ProgramBuilder::new(name);
        let a = p.var("a", -1);
        let w = p.var("w", -1);
        let rc = p.var("rc", 99);
        let sleeper = p.body("sleeper", Vec::new(), |b| {
            flock(b, "mr-f5: flock(w, LOCK_EX) sleeps", w, darwin::LOCK_EX, Some(rc));
        });
        let t = p.thread("sleeper", sleeper);
        let unlocker = p.body("releaser", Vec::new(), |b| {
            flock(b, "mr-f5: LOCK_UN a (another thread)", a, darwin::LOCK_UN, None);
        });
        let u = p.thread("releaser", unlocker);
        let main = p.body("main", Vec::new(), |b| {
            open_path(b, "mr-f5: open a", "s.lock", darwin::O_RDWR | darwin::O_CREAT, a, "holder");
            open_path(b, "mr-f5: open w", "s.lock", darwin::O_RDONLY, w, "waiter");
            flock(b, "mr-f5: flock(a, LOCK_EX)", a, darwin::LOCK_EX, None);
            b.spawn_thread("mr-f5: spawn sleeper", t);
            if releaser {
                b.spawn_thread("mr-f5: spawn releaser", u);
            }
            close(b, "mr-f5: close(w)", w);
            if !releaser {
                flock(b, "mr-f5: LOCK_UN a", a, darwin::LOCK_UN, None);
            }
            b.join("mr-f5: join", t);
        });
        let m = p.root("main", main);
        let d = derive_ok(&p.build(), &lock_env());
        // While the sleeper's flock is in flight, main's close(w) never fires.
        let close_at = d
            .core()
            .prog
            .stmts()
            .find(|(_, st)| st.loc.0 == "mr-f5: close(w)")
            .map(|(at, _)| at)
            .expect("the close");
        let sleeping = |c: &trust_platform_derive::interp::Config| {
            c.actors.iter().any(|x| x.role == Role::Thread(t) && x.pending.is_some())
        };
        let (mut closes, mut while_sleeping) = (0, 0);
        for (from, act, _) in &d.graph().edges {
            if let trust_platform_derive::explore::ActionKey::Event { role, at, .. } =
                &d.graph().actions[*act]
                && *role == Role::Thread(m)
                && *at == close_at
            {
                closes += 1;
                if sleeping(&d.graph().configs[*from]) {
                    while_sleeping += 1;
                }
            }
        }
        assert!(
            closes > 0 && while_sleeping == 0,
            "{closes} closes, {while_sleeping} while it sleeps"
        );
        if releaser {
            let granted = d.graph().configs.iter().any(|c| {
                c.actors.iter().any(|x| x.role == Role::Thread(t) && x.done() && x.vars[rc] == 0)
            });
            assert!(granted, "the sleeper is granted once a lets go");
        } else {
            // main closes w while the sleeper sleeps on it, before letting a
            // go: the close waits for the flock, which waits for a's lock — a
            // deadlock (MEASURED: a close waited 2004 ms for a holder, until it
            // let go). Named, not silent.
            assert!(
                d.stats().stuck_states > 0 && d.notes().iter().any(|n| n.starts_with("STUCK:"))
            );
        }
    }
}
