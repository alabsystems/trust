//! Trust: advance the actual input subgraph without closing its source/output.
use std::path::PathBuf;

use trust_resource_controller::bootstrap_graph::compilation::{Advanced, MemberRequest};
use trust_resource_controller::client::Delivery;
use trust_resource_controller::client::bootstrap_graph::{
    BootstrapMemberFailure, ResidentBootstrapCompilation, ResidentBootstrapMember,
    RetiredBootstrapMember,
};

use super::*;

mod configuration;
pub(crate) use configuration::{OriginalBootstrapConfiguration, Stage0Selection};

/// No data constructor. Only the SAME original native Advance may consume the
/// completed input work into this owner. Its original command, output lock,
/// protected scope/source, GNU and native enrollment stay live throughout.
#[must_use]
pub struct OriginalBootstrapCompilation {
    inputs: OriginalDependencyInputs,
    native: Arc<ResidentBootstrapCompilation>,
}
impl OriginalDependencyInputs {
    pub fn advance(
        self,
        work: ResidentDependencyInputs,
    ) -> Result<OriginalBootstrapCompilation, RefusedDependencyInputs> {
        let mut work = Some(work);
        let result = (|| {
            self.check_current()?;
            let selected = self.xpy.as_ref().ok_or_else(|| {
                io::Error::other("component input work cannot become a Full request")
            })?;
            let arguments =
                selected.arguments.iter().map(|word| word.as_bytes().to_vec()).collect();
            let mut state = lock(&self.graph.state, self.graph.deadline)?;
            if state.compilation.is_some() || state.compilation_failure.is_some() {
                return Err(io::Error::other("original compilation advance is already used"));
            }
            let Some(Phase::OutputBound(original)) = state.phase.take() else {
                return Err(io::Error::other("original input enrollment is absent"));
            };
            // The actual accepted enrollment and completed input owner move
            // together. Unknown keeps them in the retained native refusal;
            // neither component Close nor local source retirement runs here.
            let native = match original.advance_dependency_input_work(
                &state.client,
                work.take().expect("same completed original input work"),
                arguments,
                self.graph.deadline,
            ) {
                Ok(native) => Arc::new(native),
                Err(failure) => {
                    let error = io::Error::other(failure.to_string());
                    state.compilation_failure = Some(failure);
                    state.failed = true;
                    return Err(error);
                }
            };
            // Retain BEFORE the postcheck: a failed actual source/output guard
            // must never discard the original issued native continuation.
            state.compilation = Some(Arc::clone(&native));
            drop(state);
            self.check_current()?;
            Ok(native)
        })();
        match result {
            Ok(native) => Ok(OriginalBootstrapCompilation { inputs: self, native }),
            Err(error) => Err(RefusedDependencyInputs::new(error, (self, work))),
        }
    }
}
impl OriginalBootstrapCompilation {
    /// Trust: consume every local borrower, then the exact native all-work
    /// closure before joining/retiring the real source/output producers.
    pub fn finish(
        self: Arc<Self>,
    ) -> Result<RetiredOriginalDependencyInputs, RefusedDependencyInputs> {
        let owner = match Arc::try_unwrap(self) {
            Ok(owner) => owner,
            Err(owner) => {
                return Err(RefusedDependencyInputs::new(
                    io::Error::other("original Full compilation still has local borrowers"),
                    owner,
                ));
            }
        };
        let Self { inputs, native } = owner;
        let detach = (|| {
            inputs.check_current()?;
            let mut state = lock(&inputs.graph.state, inputs.graph.deadline)?;
            if state.compilation_failure.is_some()
                || !state.compilation.as_ref().is_some_and(|actual| Arc::ptr_eq(actual, &native))
            {
                return Err(io::Error::other("same original Full continuation is absent"));
            }
            // Remove ONLY this exact extra local native handle. A remaining
            // actual member/retirement borrower still makes finish refuse.
            drop(state.compilation.take());
            Ok(())
        })();
        if let Err(error) = detach {
            return Err(RefusedDependencyInputs::new(error, (inputs, native)));
        }
        let closed = match native.finish(inputs.graph.deadline) {
            Ok(closed) => closed,
            Err(failure) => {
                return Err(RefusedDependencyInputs::new(
                    io::Error::other(failure.to_string()),
                    (inputs, failure),
                ));
            }
        };
        inputs.retire_closed(closed)
    }
    pub fn data(&self) -> &Advanced {
        self.native.data()
    }
    pub fn original_deadline(&self) -> Instant {
        self.inputs.original_deadline()
    }
    pub fn original_scheduler(&self) -> &Jobserver {
        self.inputs.original_scheduler()
    }
    pub fn original_source(&self) -> io::Result<&Arc<OriginalSourceRoot>> {
        self.inputs.original_source()
    }
    pub fn selection(&self) -> (&[OsString], &InputLayout) {
        self.inputs.xpy_selection().expect("only actual full x.py inputs can advance")
    }
    pub fn check_current(&self) -> io::Result<()> {
        self.inputs.check_current()
    }
    pub(crate) fn same_graph(&self, graph: &OriginalHostGraph) -> bool {
        std::ptr::eq(Arc::as_ptr(&self.inputs.graph), graph)
    }
    // Trust: lend the SAME output/command guards to Session, without another
    // manager acquisition, output lock or protected scope.
    pub(crate) fn build_ownership(&self) -> io::Result<Arc<BuildOwnership>> {
        self.check_current()?;
        Ok(Arc::clone(&self.inputs.owners.output))
    }
    /// Restriction DATA from the SAME live retained Fixed owner. This number
    /// cannot reconstruct a CPU grant, queue guard or native member.
    pub fn cpu_ceiling(&self) -> io::Result<std::num::NonZeroU32> {
        self.check_current()?;
        let trust_resource_controller::Cpu::RetainedFixed { units, .. } =
            self.inputs.graph.context.context.cpu
        else {
            return Err(io::Error::other("original Full Root is not retained Fixed"));
        };
        std::num::NonZeroU32::new(units)
            .ok_or_else(|| io::Error::other("original Full Root has no Fixed budget"))
    }
    /// Selection DATA for the SAME control SDK which actually owns this Root.
    /// The private seed's Targo is a different input; neither this pathname nor
    /// the library parser constructs a Keeper or issues native execution.
    pub fn control_targo(&self) -> io::Result<PathBuf> {
        self.check_current()?;
        let sdk =
            self.inputs.graph.context.context.sdk.as_ref().ok_or_else(|| {
                io::Error::other("original Full Root has no retained control SDK")
            })?;
        let root = PathBuf::from(std::ffi::OsStr::from_bytes(&sdk.execution));
        if !root.is_absolute() {
            return Err(io::Error::other("original control SDK root is not absolute"));
        }
        self.check_current()?;
        Ok(root.join("bin/targo"))
    }
    pub(crate) fn install_execution_scope(&self) -> io::Result<()> {
        self.check_current()?;
        let dispatch = lock(&self.inputs.owners.scope, self.original_deadline())?
            .as_ref()
            .ok_or_else(|| io::Error::other("actual original Full scope is absent"))?
            .dispatcher();
        crate::utils::exec::install_protected_scope(dispatch)?;
        self.check_current()
    }
    pub fn scoped_work<T>(&self, work: impl FnOnce() -> io::Result<T>) -> io::Result<T> {
        self.inputs.scoped_input_work(work)
    }
    /// The wrapper, including every unknown delivery, strongly retains the
    /// actual source/output producers. No bare native member can escape it.
    pub fn member(
        self: &Arc<Self>,
        request: MemberRequest,
        descriptions: [OwnedFd; 5],
        deadline: Instant,
    ) -> Result<OriginalBootstrapMember, OriginalBootstrapMemberFailure> {
        self.check_current().map_err(|error| OriginalBootstrapMemberFailure {
            delivery: Delivery::BeforeRequest,
            error,
            _owner: Arc::clone(self),
            _member: None,
            request: request.clone(),
        })?;
        let original = request.clone();
        match self.native.member(request, descriptions, deadline) {
            Ok(member) => {
                Ok(OriginalBootstrapMember { owner: Arc::clone(self), member: Some(member) })
            }
            Err(failure) => {
                Err(OriginalBootstrapMemberFailure::native(Arc::clone(self), original, failure))
            }
        }
    }
}

#[must_use]
pub struct OriginalBootstrapMember {
    owner: Arc<OriginalBootstrapCompilation>,
    member: Option<ResidentBootstrapMember>,
}
impl Drop for OriginalBootstrapMember {
    fn drop(&mut self) {
        if self.member.is_some() {
            // Abandonment of a delivered member cannot let its actual source
            // and output producers drop before the native owning outcome.
            std::mem::forget(Arc::clone(&self.owner));
        }
    }
}
impl OriginalBootstrapMember {
    pub fn observation(&self) -> Option<&Status> {
        self.member.as_ref().expect("same actual member").observation()
    }
    pub fn request(&self) -> &MemberRequest {
        self.member.as_ref().expect("same actual member").request()
    }
    pub fn retire(
        mut self,
        deadline: Instant,
    ) -> Result<RetiredOriginalBootstrapMember, OriginalBootstrapMemberFailure> {
        let owner = Arc::clone(&self.owner);
        let member = self.member.take().expect("same actual member");
        let request = member.request().clone();
        // Native owning retirement must remain available on error: don't turn
        // a failed local precheck into dropping an actually delivered member.
        match member.retire(deadline) {
            Ok(retired) => {
                let closed = RetiredOriginalBootstrapMember { owner, retired };
                if let Err(error) = closed.owner.check_current() {
                    return Err(OriginalBootstrapMemberFailure {
                        delivery: Delivery::Unknown,
                        error,
                        _owner: Arc::clone(&closed.owner),
                        _member: Some(Box::new(MemberContinuation::Retired(closed))),
                        request,
                    });
                }
                Ok(closed)
            }
            Err(failure) => Err(OriginalBootstrapMemberFailure::native(owner, request, failure)),
        }
    }
}

/// Retains actual Rust producers beside the distinct private native issuer.
/// Only this reference can feed a matching Cargo queue's settlement check;
/// neither the observation nor the output artifact supplies that authority.
#[must_use]
pub struct RetiredOriginalBootstrapMember {
    owner: Arc<OriginalBootstrapCompilation>,
    retired: RetiredBootstrapMember,
}
impl RetiredOriginalBootstrapMember {
    /// Equality against the SAME actual producer guards, not only wire DATA.
    pub fn belongs_to(&self, owner: &Arc<OriginalBootstrapCompilation>) -> bool {
        Arc::ptr_eq(&self.owner, owner)
    }
    pub fn native_retirement(&self) -> &RetiredBootstrapMember {
        &self.retired
    }
    pub fn check_current(&self) -> io::Result<()> {
        self.owner.check_current()?;
        self.retired.revalidate(self.owner.original_deadline())
    }
}

/// Every refused/uncertain stage retains all actual source/output and member
/// owners. No observation or downcast converts this into local/native closure.
#[must_use]
pub struct OriginalBootstrapMemberFailure {
    delivery: Delivery,
    error: io::Error,
    _owner: Arc<OriginalBootstrapCompilation>,
    _member: Option<Box<MemberContinuation>>,
    request: MemberRequest,
}
enum MemberContinuation {
    Pending(BootstrapMemberFailure),
    Retired(RetiredOriginalBootstrapMember),
}
impl Drop for OriginalBootstrapMemberFailure {
    fn drop(&mut self) {
        if self.delivery == Delivery::Unknown && self._member.is_some() {
            std::mem::forget(Arc::clone(&self._owner));
            if let Some(member) = self._member.take() {
                std::mem::forget(member);
            }
        }
    }
}
impl OriginalBootstrapMemberFailure {
    fn native(
        owner: Arc<OriginalBootstrapCompilation>,
        request: MemberRequest,
        failure: BootstrapMemberFailure,
    ) -> Self {
        Self {
            delivery: failure.delivery(),
            error: io::Error::other(failure.to_string()),
            _owner: owner,
            _member: Some(Box::new(MemberContinuation::Pending(failure))),
            request,
        }
    }
    /// A lexical before-delivery error can refund only its SAME exact actual
    /// queue offer. Foreign or merely equal-looking producers cannot do so.
    pub fn belongs_to(
        &self,
        owner: &Arc<OriginalBootstrapCompilation>,
        request: &MemberRequest,
    ) -> bool {
        Arc::ptr_eq(&self._owner, owner) && &self.request == request
    }
    /// Recover ONLY the actual uncertain member for its SAME consuming Retire;
    /// this never reoffers execution or reconstructs it from a saved identity.
    pub fn into_member(mut self) -> Result<OriginalBootstrapMember, Self> {
        let Some(continuation) = self._member.take() else {
            return Err(self);
        };
        match *continuation {
            MemberContinuation::Pending(failure) => match failure.into_member() {
                Ok(member) => Ok(OriginalBootstrapMember {
                    owner: Arc::clone(&self._owner),
                    member: Some(member),
                }),
                Err(failure) => {
                    self._member = Some(Box::new(MemberContinuation::Pending(failure)));
                    Err(self)
                }
            },
            retired => {
                self._member = Some(Box::new(retired));
                Err(self)
            }
        }
    }
    /// A failed local source/output postcheck cannot erase actual native child
    /// closure. This opaque witness can settle only its matching queue loan;
    /// it grants neither valid artifacts nor a successful Full outcome.
    pub fn native_retirement(&self) -> Option<&RetiredBootstrapMember> {
        match self._member.as_deref()? {
            MemberContinuation::Retired(closed) => Some(&closed.retired),
            MemberContinuation::Pending(_) => None,
        }
    }
    pub fn delivery(&self) -> Delivery {
        self.delivery
    }
    pub fn error(&self) -> &io::Error {
        &self.error
    }
}
impl std::fmt::Debug for OriginalBootstrapMemberFailure {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("OriginalBootstrapMemberFailure")
            .field("delivery", &self.delivery)
            .field("error", &self.error)
            .finish_non_exhaustive()
    }
}
impl std::fmt::Display for OriginalBootstrapMemberFailure {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.error.fmt(f)
    }
}
impl std::error::Error for OriginalBootstrapMemberFailure {}
