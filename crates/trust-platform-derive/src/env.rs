//! The environment of a root (plan §2.2 rely clauses, SD-4).
//!
//! * **RL-INIT** — the table at `main` is arbitrary. It is enumerated as a
//!   finite family of initial tables: stdio open, each descriptor argument on
//!   each admissible slot, and — in a table of its own — ONE unflagged
//!   foreign descriptor at each candidate position of the partition
//!   ([`crate::partition::Partition::positions`]: every constant the program
//!   or environment compares descriptor numbers with, its neighbours, its
//!   additive shifts, and the lowest free number above the small points —
//!   where Metal's shader-cache descriptors sat, measured 2026-09-27 at fds
//!   8, 10, 11 and 17). Restrictions, printed into every model: stdio is
//!   open, at most one foreign descriptor, foreign descriptors are unflagged
//!   and of unknown kind. The foreign descriptor may sit at any number below
//!   `kern.maxfilesperproc` — ABOVE the soft `RLIMIT_NOFILE` too (a number
//!   inherited from a parent with a higher limit survives exec).
//! * **RL-FOREIGN** — foreign code may create descriptors with arbitrary
//!   close-on-exec at any time. M1 represents it by the RL-INIT foreign
//!   descriptors plus the program's own thread roots; a stateless
//!   create-anywhere generator at every interleaving point is not wired yet
//!   (stated in every derived model's notes).
//!
//! Every choice here is printed into the model ([`InitConfig::describe`] is
//! the event-map entry of the `init#k` action), so a reader sees exactly
//! which tables were explored.

use trust_platform::{Access, Host, NodeKind, OfdKind, Rlimit, darwin};

/// The real resource limits of the run.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Limits {
    pub soft: u64,
    pub hard: u64,
    pub max_files_per_proc: u64,
}

impl Limits {
    /// This machine (measured 2026-09-30): soft `RLIMIT_NOFILE` 1048576,
    /// hard `RLIM_INFINITY`, `kern.maxfilesperproc` 92160.
    #[must_use]
    pub fn measured_darwin() -> Limits {
        Limits { soft: 1_048_576, hard: darwin::RLIM_INFINITY, max_files_per_proc: 92_160 }
    }

    /// The first descriptor number the root cannot allocate at start.
    #[must_use]
    pub fn alloc_limit(&self) -> i64 {
        i64::try_from(self.soft.min(self.max_files_per_proc)).unwrap_or(i64::MAX)
    }

    /// The first number no descriptor can have: `kern.maxfilesperproc`
    /// (capped to `int`). RL-INIT's foreign descriptor may sit anywhere below
    /// it, the soft limit notwithstanding.
    #[must_use]
    pub fn foreign_limit(&self) -> i64 {
        i64::try_from(self.max_files_per_proc).unwrap_or(i64::MAX).min(i64::from(i32::MAX))
    }
}

/// Where RL-INIT may place a descriptor argument.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Slot {
    /// Exactly this number (a point of the partition: 3, 4).
    Exact(i32),
    /// Some number in the interval above the small points and below the
    /// first large constant (packed in order from its lowest number).
    Mid,
}

/// The environment of one fixture.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EnvSpec {
    pub limits: Limits,
    /// Slots each descriptor argument may occupy.
    pub param_slots: Vec<Slot>,
    /// Also explore tables holding one unflagged foreign descriptor at each
    /// candidate position of the partition.
    pub foreign: bool,
    /// Further positions of that one unflagged foreign descriptor — numbers a
    /// reproduction measured a real one at (aterm's fd 70000) — explored
    /// whether or not `foreign` enumerates the partition. A position RL-INIT
    /// cannot lay out (taken, or at or above the allocation limit) is skipped,
    /// as a partition position is.
    pub foreign_at: Vec<i64>,
    /// The fd-bound premise's cap, as the policy declares it ("every open
    /// fd < min(soft RLIMIT_NOFILE, cap)"; aterm's is 65536, the
    /// `inherited_fd_ceiling` CAP). `None`: the premise is not stated.
    pub fd_bound_cap: Option<i64>,
    /// RL-INIT's namespace (M2): the path names that exist before the program
    /// runs (`/dev/null`, a dead instance's lease file), each a fresh node of
    /// its kind.
    pub names: Vec<(String, NodeKind)>,
}

/// The fixed RL-INIT class names.
pub const STDIO_CLASSES: [&str; 3] = ["stdio0", "stdio1", "stdio2"];
pub const FOREIGN: &str = "foreign";

impl EnvSpec {
    /// Every class name RL-INIT can install.
    #[must_use]
    pub fn class_names(&self) -> Vec<&'static str> {
        let mut v: Vec<&'static str> = STDIO_CLASSES.to_vec();
        v.push(FOREIGN);
        v
    }

    /// Constants the partition must preserve.
    #[must_use]
    pub fn constants(&self) -> Vec<i64> {
        let as_i64 = |v: u64| i64::try_from(v).unwrap_or(i64::MAX);
        let mut v = vec![
            as_i64(self.limits.soft),
            as_i64(self.limits.hard),
            as_i64(self.limits.max_files_per_proc),
        ];
        v.extend(self.fd_bound_cap);
        for s in &self.param_slots {
            if let Slot::Exact(n) = s {
                v.push(i64::from(*n));
            }
        }
        v
    }
}

/// One installed descriptor of an initial table.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Placed {
    pub fd: i64,
    pub class: String,
    pub cloexec: bool,
    /// Index into the placement list of its socketpair peer.
    pub peer: Option<usize>,
    /// The descriptor argument it binds, if any.
    pub param: Option<usize>,
}

/// One RL-INIT table.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct InitConfig {
    /// Per descriptor argument, its slot.
    pub slots: Vec<Slot>,
    /// An unflagged foreign descriptor at this number, if any.
    pub foreign: Option<i64>,
}

/// What a descriptor argument is: the far end of a `UnixStream::pair()`
/// (close-on-exec after std's `FIOCLEX`), whose near end the root also holds.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ParamShape {
    pub class: String,
    pub peer_class: Option<String>,
}

/// A layout RL-INIT cannot make.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LayoutError {
    /// The foreign descriptor's number is taken by an argument or a peer.
    Occupied(i64),
    /// A number at or above the allocation limit.
    BeyondLimit(i64),
}

impl InitConfig {
    /// Every argument layout of the spec for `params` descriptor arguments.
    #[must_use]
    pub fn layouts(spec: &EnvSpec, params: usize) -> Vec<Vec<Slot>> {
        let mut out = Vec::new();
        let mut cur = Vec::new();
        Self::assign(spec, params, &mut cur, &mut out);
        out
    }

    fn assign(spec: &EnvSpec, left: usize, cur: &mut Vec<Slot>, out: &mut Vec<Vec<Slot>>) {
        if left == 0 {
            out.push(cur.clone());
            return;
        }
        for s in &spec.param_slots {
            if matches!(s, Slot::Exact(_)) && cur.contains(s) {
                continue;
            }
            cur.push(*s);
            Self::assign(spec, left - 1, cur, out);
            cur.pop();
        }
    }

    /// Lay the table out. `mid_lo` is the lowest number of the mid interval.
    /// Also returns the next free mid number (a candidate foreign position).
    pub fn layout(
        &self,
        spec: &EnvSpec,
        params: &[ParamShape],
        mid_lo: i64,
    ) -> Result<(Vec<Placed>, i64), LayoutError> {
        let mut placed: Vec<Placed> = (0..3)
            .map(|i| Placed {
                fd: i,
                class: STDIO_CLASSES[usize::try_from(i).unwrap_or(0)].to_string(),
                cloexec: false,
                peer: None,
                param: None,
            })
            .collect();
        let mut next_mid = mid_lo;
        let mut take_mid = || {
            let n = next_mid;
            next_mid += 1;
            n
        };
        let mut param_at = Vec::new();
        for (i, (slot, shape)) in self.slots.iter().zip(params).enumerate() {
            let fd = match slot {
                Slot::Exact(n) => i64::from(*n),
                Slot::Mid => take_mid(),
            };
            param_at.push(placed.len());
            placed.push(Placed {
                fd,
                class: shape.class.clone(),
                cloexec: true,
                peer: None,
                param: Some(i),
            });
        }
        for (i, shape) in params.iter().enumerate() {
            if let Some(pc) = &shape.peer_class {
                let fd = take_mid();
                let me = placed.len();
                placed.push(Placed {
                    fd,
                    class: pc.clone(),
                    cloexec: true,
                    peer: Some(param_at[i]),
                    param: None,
                });
                placed[param_at[i]].peer = Some(me);
            }
        }
        let limit = spec.limits.alloc_limit();
        if let Some(p) = placed.iter().find(|p| p.fd >= limit) {
            return Err(LayoutError::BeyondLimit(p.fd));
        }
        if let Some(at) = self.foreign {
            if placed.iter().any(|p| p.fd == at) {
                return Err(LayoutError::Occupied(at));
            }
            // A foreign descriptor may sit ABOVE the soft limit: numbers
            // inherited from a parent with a higher limit (or opened before
            // the limit was lowered) survive exec. Only the per-process
            // maximum bounds it (equal to `limit` when soft is above it).
            if at >= spec.limits.foreign_limit() {
                return Err(LayoutError::BeyondLimit(at));
            }
            placed.push(Placed {
                fd: at,
                class: FOREIGN.to_string(),
                cloexec: false,
                peer: None,
                param: None,
            });
        }
        Ok((placed, next_mid))
    }

    /// The `init#k` event-map text.
    #[must_use]
    pub fn describe(&self, placed: &[Placed], limits: &Limits) -> String {
        let mut s = format!(
            "RL-INIT: RLIMIT_NOFILE soft {} hard {}, kern.maxfilesperproc {}; table",
            limits.soft, limits.hard, limits.max_files_per_proc
        );
        for p in placed {
            s.push_str(&format!(
                " {}={}{}",
                p.fd,
                p.class,
                if p.cloexec { "(cloexec)" } else { "(unflagged)" }
            ));
        }
        s
    }

    /// Build the host: one root with `threads` threads and the table.
    pub fn host(
        placed: &[Placed],
        limits: &Limits,
        threads: u32,
    ) -> Result<(Host, Vec<(trust_platform::OfdId, String)>), String> {
        let mut host = Host::new(limits.max_files_per_proc);
        let root = host
            .add_root_with_threads(Rlimit { soft: limits.soft, hard: limits.hard }, threads.max(1));
        let mut ofds = vec![None; placed.len()];
        let mut classes = Vec::new();
        for (i, p) in placed.iter().enumerate() {
            let (kind, access) = if p.peer.is_some() {
                (
                    OfdKind::Socket { domain: darwin::AF_UNIX, ty: darwin::SOCK_STREAM },
                    Access::ReadWrite,
                )
            } else {
                (OfdKind::Opaque, Access::ReadWrite)
            };
            let fd = i32::try_from(p.fd).map_err(|_| format!("fd {} out of range", p.fd))?;
            let o = host
                .install_fresh(root, fd, kind, access, 0, p.cloexec)
                .map_err(|e| format!("{e:?}"))?;
            ofds[i] = Some(o);
            classes.push((o, p.class.clone()));
        }
        for (i, p) in placed.iter().enumerate() {
            if let (Some(j), Some(a)) = (p.peer, ofds[i])
                && j > i
                && let Some(b) = ofds[j]
            {
                host.link_peers(a, b).map_err(|e| format!("{e:?}"))?;
            }
        }
        Ok((host, classes))
    }
}
