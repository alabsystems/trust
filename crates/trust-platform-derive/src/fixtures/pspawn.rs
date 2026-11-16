//! `aterm_uds::pspawn::spawn_cloexec_default`
//! (`crates/aterm-uds/src/pspawn.rs`, added by aterm 184fb5613, unchanged on
//! aterm main 93b6d38f3): the current aterm spawn path that inherits nothing
//! but a `/dev/null` stdio, atomically.
//!
//! aterm main, pspawn.rs:81-137 (the Darwin arm):
//!
//! ```text
//! let rc = unsafe { posix_spawnattr_init(&mut attr) };
//! let rc = unsafe { posix_spawn_file_actions_init(&mut actions) };
//! let flags = POSIX_SPAWN_CLOEXEC_DEFAULT | POSIX_SPAWN_SETSIGDEF | POSIX_SPAWN_SETSIGMASK;
//! unsafe {
//!     for rc in [
//!         posix_spawnattr_setflags(&mut attr, flags),
//!         posix_spawnattr_setsigmask(&mut attr, &empty_mask),
//!         posix_spawnattr_setsigdefault(&mut attr, &all_signals),
//!         posix_spawn_file_actions_addopen(&mut actions, 0, dev_null.as_ptr(), O_RDWR, 0),
//!         posix_spawn_file_actions_addopen(&mut actions, 1, dev_null.as_ptr(), O_RDWR, 0),
//!         posix_spawn_file_actions_addopen(&mut actions, 2, dev_null.as_ptr(), O_RDWR, 0),
//!     ] { .. }
//! }
//! let rc = unsafe { posix_spawn(&mut pid, program_c.as_ptr(), &actions, &attr,
//!                               argv.as_ptr(), environ) };
//! unsafe {
//!     posix_spawn_file_actions_destroy(&mut actions);
//!     posix_spawnattr_destroy(&mut attr);
//! }
//! ```
//!
//! The builder calls touch no host state; their effect (three `addopen`s and
//! the flags) is written on the `posix_spawn` event by hand.

use trust_platform::call::FileAction;
use trust_platform::{Call, Errno, Oracle, darwin};

use super::{ATERM_MAIN, Fixture, add_racer, loc, pspawn_env};
use crate::program::{Bind, FdInherit, Mutation, Operand, ProgramBuilder};

const PATH: &str = "crates/aterm-uds/src/pspawn.rs";

/// Fixture 6: aterm main's `spawn_cloexec_default`: `posix_spawn` with
/// `POSIX_SPAWN_CLOEXEC_DEFAULT`. Must NOT be refuted — with no premise.
#[must_use]
pub fn cloexec_default() -> Fixture {
    let l = |line: &str| loc(ATERM_MAIN, PATH, line);
    let mut p = ProgramBuilder::new("cloexec_default");
    p.provenance("aterm", ATERM_MAIN, PATH, "spawn_cloexec_default (added by 184fb5613)");
    let site = p.site("keeper_open", &l("118"), Some(FdInherit { lanes: Vec::new() }));
    let pid = p.var("pid", -1);
    let main = p.body("spawn_cloexec_default", Vec::new(), |b| {
        b.neutral(&l("81"), "posix_spawnattr_init");
        b.neutral(&l("86"), "posix_spawn_file_actions_init");
        b.neutral(&l("101"), "posix_spawnattr_setflags");
        b.neutral(&l("102"), "posix_spawnattr_setsigmask");
        b.neutral(&l("103"), "posix_spawnattr_setsigdefault");
        b.neutral(&l("104"), "posix_spawn_file_actions_addopen");
        b.neutral(&l("105"), "posix_spawn_file_actions_addopen");
        b.neutral(&l("106"), "posix_spawn_file_actions_addopen");
        let actions = (0..3)
            .map(|fd| FileAction::Open { fd: Operand::Lit(fd), flags: darwin::O_RDWR })
            .collect();
        b.tag("posix_spawn").event_full(
            &l("118"),
            "posix_spawn",
            Call::Spawn {
                actions,
                flags: darwin::POSIX_SPAWN_CLOEXEC_DEFAULT
                    | darwin::POSIX_SPAWN_SETSIGDEF
                    | darwin::POSIX_SPAWN_SETSIGMASK,
            },
            Bind::ret(pid),
            vec![Oracle::Nominal, Oracle::Fail(Errno::ENOENT)],
            Some(site),
            vec!["devnull0", "devnull1", "devnull2"],
        );
        b.neutral(&l("133"), "posix_spawn_file_actions_destroy");
        b.neutral(&l("134"), "posix_spawnattr_destroy");
    });
    p.root("main", main);
    add_racer(&mut p);
    Fixture {
        name: "cloexec_default",
        program: p.build(),
        env: pspawn_env(),
        premises: Vec::new(),
        expect_refuted: false,
        hygiene: vec![Mutation::ClearSpawnFlag {
            tag: "posix_spawn".to_string(),
            flag: darwin::POSIX_SPAWN_CLOEXEC_DEFAULT,
        }],
    }
}
