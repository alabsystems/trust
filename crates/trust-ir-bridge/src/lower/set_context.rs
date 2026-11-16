//! Trust (2026-10-27): what a member's lowering reads of its SET, and the replay that
//! lets the compiler's survivor rounds skip re-lowering a member whose reads all
//! answer the same in the next round's set.
//!
//! # Why
//!
//! The compiler's fail-soft bundling retry (`trust_verify.rs`, "CONTEXT-AWARE survivor
//! pre-filter") probes every survivor of a round against the round's set, then drops
//! the members whose probe failed and, ONE CALL LEVEL PER ROUND, the members that call
//! a dropped candidate. A drop cascade of depth `d` therefore takes `d + 1` rounds, and
//! every round lowered every survivor again — `rounds × bundle size` member lowerings
//! per root, the dominant compiler-thread cost of verifying `ay-sat` (measured
//! 2026-10-27, `[SURVIVOR_COST]` / `[PROBE_COST]`; numbers in `docs/DECISION_QUEUE.md`,
//! "SURVIVOR-REPLAY-1").
//!
//! # What a probe reads of its set
//!
//! A probe lowers ONE member (`lower_function_into`) into a fresh scratch module with
//! a fresh type cache and tuple ledger, the survivor loop's FIXED expected-absent and
//! structural-drop sets, and empty sets for everything else. The only inputs that
//! depend on the set are the three set-wide structures [`super::ModuleProbeShared`]
//! holds: the name → `FuncId` map, the name → signature map, and the
//! closure-environment registry. `LoweringCtx` holds the first two only as
//! [`KnownFunctions`] / [`KnownSignatures`], whose maps are private to this module, so
//! every read of them goes through an accessor here; the registry is read only by
//! `LoweringCtx::new`, through [`ClosureEnvs::marker_type`]. When a probe passes a
//! [`SetReadRecorder`], each accessor appends what it was asked and what it answered.
//!
//! # EXACTNESS
//!
//! Lowering is deterministic: the same member, the same fixed inputs and the same
//! answer to every set read execute the same steps and return the same result. The
//! fixed inputs include the thread's ambient lowering state (the native callee-summary
//! frame the verifying function installed, the coroutine-frame witness): one survivor
//! loop runs inside one function's verification and forces no query between its
//! rounds, so that state is the same in every round. So if
//! replaying a member's recorded reads, in order, against the NEXT round's set gives
//! the same answer to every one of them, lowering it there would make exactly those
//! reads (by induction over the execution: the first read that answered differently
//! would be the first step to differ) and return what it returned before — `Ok`, since
//! only a member that passed keeps a log. [`replays`] asks each recorded read again
//! through the SAME accessor code that recorded it and compares the two records.
//!
//! One renaming is allowed: a round's `FuncId`s are positions in that round's
//! compacted survivor list, so dropping a member renumbers every member after it. Each
//! answer therefore records the member an id names (its ORIGIN, the index in the
//! survivor loop's original candidate list) instead of the id. A replay is exact under
//! that renaming because a lowering never inspects an id's NUMBER: an id read here is
//! only emitted as the callee of an `Inst::Call` into the scratch module (which the
//! probe discards and which holds no other function, so no lookup by id can succeed in
//! one round and fail in another), or compared for equality with another id read from
//! the same set ([`KnownSignatures::find_by_id`], [`KnownSignatures::
//! coroutine_resume_contract_by_id`]), or counted in a trace
//! ([`KnownFunctions::distinct_ids`]). Nothing sorts, hashes into iteration order,
//! offsets or bounds-checks one. `module_context_probe_tests` pins this
//! (`a_members_answer_does_not_depend_on_funcid_numbers`): reversing a set, or putting
//! members in front of it, renumbers its members and changes no member's answer; and
//! every round of arbitrary shrinking schedules answers what a fresh probe answers.
//!
//! A read whose answer names an id that is no member of the round (none is ever
//! registered) marks the log unreplayable, and a replay that would ask about a member
//! the round no longer holds fails: both lower the member again. A replay only ever
//! answers "lowers"; a failing probe is always a real lowering, with its
//! `TRUST_PROBE_TRACE` line.

use std::cell::{Cell, RefCell};

use trust_ir::value::FuncId;
use trust_types::Ty;
use trust_types::fx::FxHashMap;

use super::{ClosureEnvTypes, KnownFunctionSignature, closure_env_type_for_unsupported_marker};

/// One read of the set and its answer, with every `FuncId` replaced by its origin.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) enum SetRead {
    /// `KnownFunctions::get`: the origin of the member the key names, if any.
    FunctionId { key: String, answer: Option<usize> },
    /// `KnownFunctions::contains_key`.
    HasFunction { key: String, answer: bool },
    /// `KnownFunctions::distinct_ids` (a trace's member count).
    DistinctFunctionIds { answer: usize },
    /// `KnownSignatures::get`: the signature, its `id` replaced by its origin.
    Signature { key: String, answer: Option<KnownFunctionSignature> },
    /// `KnownSignatures::contains_key`.
    HasSignature { key: String, answer: bool },
    /// `KnownSignatures::find_by_id`, asked about the member `origin`.
    SignatureById { origin: usize, answer: Option<KnownFunctionSignature> },
    /// `KnownSignatures::coroutine_resume_contract_by_id`, asked about `origin`.
    CoroutineResumeById { origin: usize, answer: bool },
    /// `ClosureEnvs::marker_type`: the registry's environment for one of the member's
    /// unmodeled-closure locals.
    ClosureMarker { kind: String, detail: String, function_def_path: String, answer: Option<Ty> },
}

/// Records one lowering's set reads. `id_origins[id]` is the origin of the member
/// whose `FuncId` is `id` in the round being probed.
pub(super) struct SetReadRecorder<'o> {
    id_origins: &'o [usize],
    reads: RefCell<Vec<SetRead>>,
    unreplayable: Cell<bool>,
}

impl<'o> SetReadRecorder<'o> {
    pub(super) fn new(id_origins: &'o [usize]) -> Self {
        Self { id_origins, reads: RefCell::new(Vec::new()), unreplayable: Cell::new(false) }
    }

    /// The reads, or `None` when one of them named an id that is no member of the
    /// round (never replayed).
    pub(super) fn into_reads(self) -> Option<Vec<SetRead>> {
        (!self.unreplayable.get()).then(|| self.reads.into_inner())
    }

    fn origin(&self, id: FuncId) -> usize {
        match self.id_origins.get(id.as_usize()) {
            Some(&origin) => origin,
            None => {
                self.unreplayable.set(true);
                usize::MAX
            }
        }
    }

    fn signature(&self, signature: &KnownFunctionSignature) -> KnownFunctionSignature {
        KnownFunctionSignature {
            id: FuncId::new(u32::try_from(self.origin(signature.id)).unwrap_or(u32::MAX)),
            ..signature.clone()
        }
    }

    fn push(&self, read: SetRead) {
        self.reads.borrow_mut().push(read);
    }

    fn last_matches(&self, read: &SetRead) -> bool {
        !self.unreplayable.get() && self.reads.borrow().last() == Some(read)
    }
}

/// The set's name → `FuncId` map, read only through recording accessors.
#[derive(Clone, Copy)]
pub(super) struct KnownFunctions<'a> {
    map: &'a FxHashMap<String, FuncId>,
    recorder: Option<&'a SetReadRecorder<'a>>,
}

impl<'a> KnownFunctions<'a> {
    pub(super) fn new(
        map: &'a FxHashMap<String, FuncId>,
        recorder: Option<&'a SetReadRecorder<'a>>,
    ) -> Self {
        Self { map, recorder }
    }

    pub(super) fn get(&self, key: &str) -> Option<&'a FuncId> {
        let answer = self.map.get(key);
        if let Some(recorder) = self.recorder {
            let answer = answer.map(|id| recorder.origin(*id));
            recorder.push(SetRead::FunctionId { key: key.to_owned(), answer });
        }
        answer
    }

    pub(super) fn contains_key(&self, key: &str) -> bool {
        let answer = self.map.contains_key(key);
        if let Some(recorder) = self.recorder {
            recorder.push(SetRead::HasFunction { key: key.to_owned(), answer });
        }
        answer
    }

    /// How many distinct members the map names.
    pub(super) fn distinct_ids(&self) -> usize {
        let answer = self.map.values().copied().collect::<std::collections::BTreeSet<_>>().len();
        if let Some(recorder) = self.recorder {
            recorder.push(SetRead::DistinctFunctionIds { answer });
        }
        answer
    }
}

/// The set's name → signature map, read only through recording accessors.
#[derive(Clone, Copy)]
pub(super) struct KnownSignatures<'a> {
    map: &'a FxHashMap<String, KnownFunctionSignature>,
    recorder: Option<&'a SetReadRecorder<'a>>,
}

impl<'a> KnownSignatures<'a> {
    pub(super) fn new(
        map: &'a FxHashMap<String, KnownFunctionSignature>,
        recorder: Option<&'a SetReadRecorder<'a>>,
    ) -> Self {
        Self { map, recorder }
    }

    pub(super) fn get(&self, key: &str) -> Option<&'a KnownFunctionSignature> {
        let answer = self.map.get(key);
        if let Some(recorder) = self.recorder {
            let answer = answer.map(|signature| recorder.signature(signature));
            recorder.push(SetRead::Signature { key: key.to_owned(), answer });
        }
        answer
    }

    pub(super) fn contains_key(&self, key: &str) -> bool {
        let answer = self.map.contains_key(key);
        if let Some(recorder) = self.recorder {
            recorder.push(SetRead::HasSignature { key: key.to_owned(), answer });
        }
        answer
    }

    /// The first signature, in the map's iteration order, whose id is `id`.
    pub(super) fn find_by_id(&self, id: FuncId) -> Option<&'a KnownFunctionSignature> {
        let answer = self.map.values().find(|signature| signature.id == id);
        if let Some(recorder) = self.recorder {
            let origin = recorder.origin(id);
            let answer = answer.map(|signature| recorder.signature(signature));
            recorder.push(SetRead::SignatureById { origin, answer });
        }
        answer
    }

    /// Whether some signature whose id is `id` is a coroutine resume body.
    pub(super) fn coroutine_resume_contract_by_id(&self, id: FuncId) -> bool {
        let answer = self
            .map
            .values()
            .any(|signature| signature.id == id && signature.coroutine_resume_contract);
        if let Some(recorder) = self.recorder {
            let origin = recorder.origin(id);
            recorder.push(SetRead::CoroutineResumeById { origin, answer });
        }
        answer
    }
}

/// The set's closure-environment registry, read only through a recording accessor.
#[derive(Clone, Copy)]
pub(super) struct ClosureEnvs<'a> {
    map: &'a ClosureEnvTypes,
    recorder: Option<&'a SetReadRecorder<'a>>,
}

impl<'a> ClosureEnvs<'a> {
    pub(super) fn new(map: &'a ClosureEnvTypes, recorder: Option<&'a SetReadRecorder<'a>>) -> Self {
        Self { map, recorder }
    }

    /// [`closure_env_type_for_unsupported_marker`] against the registry.
    pub(super) fn marker_type(
        &self,
        kind: &str,
        detail: &str,
        function_def_path: &str,
    ) -> Option<Ty> {
        let answer =
            closure_env_type_for_unsupported_marker(kind, detail, function_def_path, self.map);
        if let Some(recorder) = self.recorder {
            recorder.push(SetRead::ClosureMarker {
                kind: kind.to_owned(),
                detail: detail.to_owned(),
                function_def_path: function_def_path.to_owned(),
                answer: answer.clone(),
            });
        }
        answer
    }
}

/// Does every read in `reads` answer the same against this set, whose members'
/// origins are `id_origins` (in `FuncId` order)? Each read is asked again through the
/// accessor that recorded it, and the two records are compared.
pub(super) fn replays(
    reads: &[SetRead],
    functions: &FxHashMap<String, FuncId>,
    signatures: &FxHashMap<String, KnownFunctionSignature>,
    closure_envs: &ClosureEnvTypes,
    id_origins: &[usize],
) -> bool {
    let recorder = SetReadRecorder::new(id_origins);
    let known_functions = KnownFunctions::new(functions, Some(&recorder));
    let known_signatures = KnownSignatures::new(signatures, Some(&recorder));
    let closure_envs = ClosureEnvs::new(closure_envs, Some(&recorder));
    let id_of = |origin: usize| {
        id_origins
            .iter()
            .position(|&member| member == origin)
            .and_then(|index| u32::try_from(index).ok())
            .map(FuncId::new)
    };
    for read in reads {
        match read {
            SetRead::FunctionId { key, .. } => {
                known_functions.get(key);
            }
            SetRead::HasFunction { key, .. } => {
                known_functions.contains_key(key);
            }
            SetRead::DistinctFunctionIds { .. } => {
                known_functions.distinct_ids();
            }
            SetRead::Signature { key, .. } => {
                known_signatures.get(key);
            }
            SetRead::HasSignature { key, .. } => {
                known_signatures.contains_key(key);
            }
            SetRead::SignatureById { origin, .. } => {
                let Some(id) = id_of(*origin) else { return false };
                known_signatures.find_by_id(id);
            }
            SetRead::CoroutineResumeById { origin, .. } => {
                let Some(id) = id_of(*origin) else { return false };
                known_signatures.coroutine_resume_contract_by_id(id);
            }
            SetRead::ClosureMarker { kind, detail, function_def_path, .. } => {
                closure_envs.marker_type(kind, detail, function_def_path);
            }
        }
        if !recorder.last_matches(read) {
            return false;
        }
    }
    true
}
