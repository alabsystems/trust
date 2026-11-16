//! Bug 2: aterm `crates/aterm-uds/src/lifeline.rs`, the `adopt` test
//! (plan §3 M2, fd-identity).
//!
//! `adopt(raw)` moves the lifeline to a close-on-exec copy and CLOSES `raw`.
//! The moment a number is closed, another thread's allocation may take it —
//! the kernel hands out the lowest free number (MEASURED, `trust-platform`
//! conformance). Code that still holds the old number then operates on a
//! stranger's description.
//!
//! * [`retired_number`] — aterm c88946be1 (= d5e08bf1b^): the test asserts
//!   "the original number is closed" with `F_GETFD` on `raw` after `adopt`
//!   closed it. A sibling test (RL-HARNESS: "a test on another thread may
//!   open a descriptor that takes the lowest free number"; d5e08bf1b's
//!   deterministic reproduction: "opening /dev/null right after adopt")
//!   squats on the number. MUST be refuted.
//! * [`identity`] — aterm d5e08bf1b: the test compares the number's node
//!   identity (`stat("/dev/fd/N")`'s device and inode) with the lifeline's:
//!   "closed, or a stranger's" both pass. Must NOT be refuted; turning that
//!   identity query back into the `F_GETFD` refutes it.
//!
//! Hand census (printed into the models' notes): `scratch()`/`remove_dir_all`
//! are not encoded (the namespace is flat; the FIFO is one name);
//! `std::fs::metadata(format!("/dev/fd/{fd}"))` (`node`) and
//! `copy.metadata()` are encoded as `fstat` — MEASURED, `stat("/dev/fd/N")`
//! answers N's inode under devfs's device and `EBADF` for a closed N, so two
//! such identities are equal exactly when the nodes are (inodes of two
//! devices could alias; not modeled); assertions are not encoded (fd-identity
//! is a property of the events); the final `wait_for_cut(adopted)` is not
//! encoded (a FIFO's end-of-file is not modeled; it reads only `adopted`).

use trust_platform::{Call, NodeKind, darwin};

use super::{M2Fixture, Property, loc, m2_env};
use crate::program::{
    Bind, BodyId, CmpOp, Cond, EventProgram, Expr, Mutation, Operand, ProgramBuilder, VarId,
};

const PATH: &str = "crates/aterm-uds/src/lifeline.rs";

/// aterm d5e08bf1b^ (the pre-fix test).
pub const PRE: &str = "c88946be1";
/// aterm d5e08bf1b (identity, not the number).
pub const FIX: &str = "d5e08bf1b";

/// The FIFO `Lifeline::open` makes (`<dir>/.aterm-lifeline-<pid>-<serial>`) in
/// the test's `scratch("adopt")` (`temp_dir()/aterm-uds-lifeline-adopt-<pid>`,
/// spelled canonically: temp_dir() is /var/folders/<..>/T).
const FIFO: &str = "/private/var/folders/T/aterm-uds-lifeline-adopt-PID/.aterm-lifeline-PID-0";

struct Vars {
    held: VarId,
    far: VarId,
    raw: VarId,
    adopted: VarId,
    // adopt's locals
    number: VarId,
    r: VarId,
    copy: VarId,
    node: VarId,
    ftype: VarId,
    flags: VarId,
    acc: VarId,
    null: VarId,
    // the test's
    fifo_node: VarId,
    probe: VarId,
    cx: VarId,
}

/// `Lifeline::open(dir)` (lifeline.rs:118-140, identical at both commits):
///
/// ```text
/// make_fifo(&path)?;                                         // mkfifo(path, 0o600)
/// let opened = std::fs::OpenOptions::new().read(true).write(true).open(&path)
///     .and_then(|held| File::open(&path).map(|far| (held, far)));
/// let unlinked = std::fs::remove_file(&path);
/// ```
fn lifeline_open(p: &mut ProgramBuilder, commit: &str, v: &Vars) -> BodyId {
    let l = |line: &str| loc(commit, PATH, line);
    let (held, far) = (v.held, v.far);
    p.body("Lifeline::open", Vec::new(), |b| {
        b.event(&l("183"), "mkfifo", Call::Mkfifo { path: FIFO.to_string() }, Bind::none());
        b.std_open(
            &l("130"),
            "std::fs::OpenOptions::open",
            FIFO,
            darwin::O_RDWR,
            held,
            "lifeline_held",
        );
        b.when(&l("134"), Cond::ne(Operand::Var(held), Operand::Lit(-1)), |b| {
            b.std_open(
                &l("134"),
                "std::fs::File::open",
                FIFO,
                darwin::O_RDONLY,
                far,
                "lifeline_far",
            );
        });
        b.event(&l("136"), "unlink", Call::Unlink { path: FIFO.to_string() }, Bind::none());
    })
}

/// `adopt(number)` (lifeline.rs:204-279, identical at both commits):
///
/// ```text
/// if number < 0 { return Err(..) }
/// if unsafe { fcntl(number, F_GETFD) } == -1 { return Err(..) }
/// let borrowed = unsafe { BorrowedFd::borrow_raw(number) };
/// let copy = File::from(borrowed.try_clone_to_owned()?);      // F_DUPFD_CLOEXEC(number, 3)
/// let kind = copy.metadata()?.file_type();                    // fstat(copy)
/// if !(kind.is_fifo() || kind.is_socket()) { return Err(..) } // drops copy
/// if kind.is_fifo() {
///     let flags = unsafe { fcntl(copy.as_raw_fd(), F_GETFL) };
///     if flags == -1 { return Err(..) }
///     if flags & O_ACCMODE != O_RDONLY { return Err(..) }
/// }
/// if number <= 2 {
///     let null = OpenOptions::new().read(true).write(true).open("/dev/null")?;
///     if unsafe { dup2(null.as_raw_fd(), number) } == -1 { return Err(..) }
/// } else {
///     unsafe { close(number) };
/// }
/// Ok(OwnedFd::from(copy))
/// ```
fn adopt(p: &mut ProgramBuilder, commit: &str, v: &Vars) -> BodyId {
    let l = |line: &str| loc(commit, PATH, line);
    let (number, r, copy, node, ftype, flags, acc, null) =
        (v.number, v.r, v.copy, v.node, v.ftype, v.flags, v.acc, v.null);
    let err = Operand::Lit(-1);
    p.body("adopt", vec![number], |b| {
        b.when(&l("205"), Cond::Cmp(CmpOp::Lt, Operand::Var(number), Operand::Lit(0)), |b| {
            b.ret(&l("206"), Some(err));
        });
        b.event(
            &l("213"),
            "fcntl",
            Call::Fcntl { fd: Operand::Var(number), cmd: darwin::F_GETFD, arg: 0 },
            Bind::ret(r),
        );
        b.when(&l("213"), Cond::eq(Operand::Var(r), Operand::Lit(-1)), |b| {
            b.ret(&l("215"), Some(err));
        });
        b.neutral(&l("223"), "std::os::fd::AsRawFd::as_raw_fd");
        b.std_row(
            &l("226"),
            "std::os::fd::BorrowedFd::try_clone_to_owned",
            vec![Operand::Var(number)],
            vec![copy],
            vec!["adopted_copy"],
        );
        b.when(&l("226"), Cond::eq(Operand::Var(copy), Operand::Lit(-1)), |b| {
            b.ret(&l("226"), Some(err));
        });
        b.event(
            &l("227"),
            "fstat",
            Call::Fstat { fd: Operand::Var(copy) },
            Bind { ret: Some(node), ret2: Some(ftype), rlim_soft: None },
        );
        let fifo = || Cond::eq(Operand::Var(ftype), Operand::Lit(i64::from(darwin::S_IFIFO)));
        let sock = || Cond::eq(Operand::Var(ftype), Operand::Lit(i64::from(darwin::S_IFSOCK)));
        b.when(&l("228"), Cond::Not(Box::new(Cond::or(fifo(), sock()))), |b| {
            b.event(&l("241"), "close", Call::Close { fd: Operand::Var(copy) }, Bind::none());
            b.ret(&l("241"), Some(err));
        });
        b.when(&l("245"), fifo(), |b| {
            b.event(
                &l("247"),
                "fcntl",
                Call::Fcntl { fd: Operand::Var(copy), cmd: darwin::F_GETFL, arg: 0 },
                Bind::ret(flags),
            );
            b.assign(
                &l("251"),
                acc,
                Expr::BitAnd(Operand::Var(flags), Operand::Lit(i64::from(darwin::O_ACCMODE))),
            );
            b.when(
                &l("248"),
                Cond::or(
                    Cond::eq(Operand::Var(flags), Operand::Lit(-1)),
                    Cond::ne(Operand::Var(acc), Operand::Lit(i64::from(darwin::O_RDONLY))),
                ),
                |b| {
                    b.event(
                        &l("257"),
                        "close",
                        Call::Close { fd: Operand::Var(copy) },
                        Bind::none(),
                    );
                    b.ret(&l("257"), Some(err));
                },
            );
        });
        b.if_(
            &l("261"),
            Cond::Cmp(CmpOp::Le, Operand::Var(number), Operand::Lit(2)),
            |b| {
                b.std_open(
                    &l("262"),
                    "std::fs::OpenOptions::open",
                    "/dev/null",
                    darwin::O_RDWR,
                    null,
                    "adopt_null",
                );
                b.event(
                    &l("269"),
                    "dup2",
                    Call::Dup2 { from: Operand::Var(null), to: Operand::Var(number) },
                    Bind::none(),
                );
                b.event(&l("272"), "close", Call::Close { fd: Operand::Var(null) }, Bind::none());
            },
            |b| {
                b.tag("adopt_close").event(
                    &l("276"),
                    "close",
                    Call::Close { fd: Operand::Var(number) },
                    Bind::none(),
                );
            },
        );
        b.ret(&l("278"), Some(Operand::Var(copy)));
    })
}

/// RL-HARNESS: a sibling `#[test]` of the `aterm-uds` lib tests (run at
/// `--test-threads 64`) that opens a descriptor and drops it — d5e08bf1b's
/// deterministic reproduction opened `/dev/null`.
fn add_squatter(p: &mut ProgramBuilder) {
    let at = |what: &str| format!("aterm-uds lib tests (RL-HARNESS): a sibling test: {what}");
    let sq = p.var("squatter.fd", -1);
    let body = p.body("sibling test", Vec::new(), |b| {
        b.std_open(
            &at("File::open(\"/dev/null\")"),
            "std::fs::File::open",
            "/dev/null",
            darwin::O_RDONLY,
            sq,
            "squatter",
        );
        b.event(&at("drop(file)"), "close", Call::Close { fd: Operand::Var(sq) }, Bind::none());
    });
    p.root("sibling test (RL-HARNESS)", body);
}

/// `adopt_moves_the_descriptor_and_retires_the_original` at `commit`.
///
/// c88946be1 (lifeline.rs:763-777):
/// ```text
/// let (lifeline, far) = Lifeline::open(&dir).expect("open");
/// let raw = IntoRawFd::into_raw_fd(far.as_fd().try_clone_to_owned().expect("dup"));
/// let adopted = adopt(raw).expect("adopt a FIFO");
/// assert_ne!(adopted.as_raw_fd(), raw);
/// assert!(adopted.as_raw_fd() >= 3);
/// assert_eq!(fd_flags(adopted.as_raw_fd()) & FD_CLOEXEC, FD_CLOEXEC);
/// assert_eq!(fd_flags(raw), -1, "the original number is closed");    // F_GETFD(raw)
/// drop(far);
/// drop(lifeline);
/// ```
///
/// d5e08bf1b (lifeline.rs:780-805) adds `let fifo = node(far)`, `node(raw)`
/// before the adopt, `node(adopted)`, and replaces the last check with
/// `assert_ne!(node(raw), Some(fifo), "the original number is closed")`.
fn adopt_test(fixed: bool) -> EventProgram {
    let commit = if fixed { FIX } else { PRE };
    let name = if fixed { "lifeline_identity" } else { "lifeline_retired_number" };
    let mut p = ProgramBuilder::new(name);
    p.provenance(
        "aterm",
        commit,
        PATH,
        "tests::adopt_moves_the_descriptor_and_retires_the_original, Lifeline::open, adopt",
    );
    p.disclose(
        "lifeline: scratch()/remove_dir_all are not encoded (flat namespace; temp_dir() is \
         spelled canonically, /private/var/folders/T, and the pid PID); node() \
         (std::fs::metadata(\"/dev/fd/N\")) and copy.metadata() are fstat (MEASURED: \
         stat(\"/dev/fd/N\") is N's inode under devfs's device, EBADF when N is closed); \
         assertions are not encoded; the final wait_for_cut(adopted) (a FIFO read to end of \
         file) is not encoded",
    );
    let l = |line: &str| loc(commit, PATH, line);
    let v = Vars {
        held: p.var("held", -1),
        far: p.var("far", -1),
        raw: p.var("raw", -1),
        adopted: p.var("adopted", -1),
        number: p.var("adopt.number", -1),
        r: p.var("adopt.r", -1),
        copy: p.var("adopt.copy", -1),
        node: p.var("adopt.node", -1),
        ftype: p.var("adopt.ftype", -1),
        flags: p.var("adopt.flags", -1),
        acc: p.var("adopt.acc", -1),
        null: p.var("adopt.null", -1),
        fifo_node: p.var("fifo", -1),
        probe: p.var("probe", -1),
        cx: p.var("cloexec", -1),
    };
    let open = lifeline_open(&mut p, commit, &v);
    let adopt_body = adopt(&mut p, commit, &v);
    let ln = |pre: &'static str, fix: &'static str| if fixed { fix } else { pre };
    let node_of = |b: &mut crate::program::BodyBuilder, line: &str, fd: VarId, out: VarId| {
        b.event(
            &loc(FIX, PATH, line),
            "fstat",
            Call::Fstat { fd: Operand::Var(fd) },
            Bind { ret: Some(out), ret2: None, rlim_soft: None },
        );
    };
    let main = p.body("adopt_moves_the_descriptor_and_retires_the_original", Vec::new(), |b| {
        b.call(&l(ln("765", "782")), open, Vec::new(), None);
        if fixed {
            node_of(b, "783", v.far, v.fifo_node);
        }
        b.std_row(
            &l(ln("767", "785")),
            "std::os::fd::BorrowedFd::try_clone_to_owned",
            vec![Operand::Var(v.far)],
            vec![v.raw],
            vec!["lifeline_far"],
        );
        b.neutral(&l(ln("766", "784")), "std::os::fd::IntoRawFd::into_raw_fd");
        if fixed {
            node_of(b, "787", v.raw, v.probe);
        }
        b.call(
            &l(ln("768", "791")),
            adopt_body,
            vec![(v.number, Operand::Var(v.raw))],
            Some(v.adopted),
        );
        b.event(
            &l(ln("771", "794")),
            "fcntl",
            Call::Fcntl { fd: Operand::Var(v.adopted), cmd: darwin::F_GETFD, arg: 0 },
            Bind::ret(v.cx),
        );
        if fixed {
            node_of(b, "796", v.adopted, v.probe);
            b.tag("retired_probe").event(
                &l("800"),
                "fstat",
                Call::Fstat { fd: Operand::Var(v.raw) },
                Bind { ret: Some(v.probe), ret2: None, rlim_soft: None },
            );
        } else {
            b.event(
                &l("772"),
                "fcntl",
                Call::Fcntl { fd: Operand::Var(v.raw), cmd: darwin::F_GETFD, arg: 0 },
                Bind::ret(v.probe),
            );
        }
        b.event(
            &l(ln("773", "801")),
            "close",
            Call::Close { fd: Operand::Var(v.far) },
            Bind::none(),
        );
        b.event(
            &l(ln("774", "802")),
            "close",
            Call::Close { fd: Operand::Var(v.held) },
            Bind::none(),
        );
    });
    let main_root = p.root("main", main);
    p.fd_identity_policy(&[main_root]);
    add_squatter(&mut p);
    p.build()
}

/// Bug 2 as shipped in the test before d5e08bf1b: MUST be refuted.
#[must_use]
pub fn retired_number() -> M2Fixture {
    M2Fixture {
        name: "lifeline_retired_number",
        program: adopt_test(false),
        env: m2_env(&[("/dev/null", NodeKind::CharDevice)]),
        property: Property::FdIdentity,
        expect_refuted: true,
        current_main: false,
        hygiene: Vec::new(),
    }
}

/// d5e08bf1b: must NOT be refuted; making the retired-number check an
/// `F_GETFD` again (the pre-fix check) refutes it.
#[must_use]
pub fn identity() -> M2Fixture {
    let program = adopt_test(true);
    let raw = program.var_id("raw").unwrap_or(usize::MAX);
    M2Fixture {
        name: "lifeline_identity",
        program,
        env: m2_env(&[("/dev/null", NodeKind::CharDevice)]),
        property: Property::FdIdentity,
        expect_refuted: false,
        current_main: false,
        hygiene: vec![Mutation::ReplaceCall {
            tag: "retired_probe".to_string(),
            symbol: "fcntl".to_string(),
            call: Call::Fcntl { fd: Operand::Var(raw), cmd: darwin::F_GETFD, arg: 0 },
        }],
    }
}
