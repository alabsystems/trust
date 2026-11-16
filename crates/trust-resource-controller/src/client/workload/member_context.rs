//! SAME live native member/controller/early SDK originals after authenticated
//! receipt. A saved Context, manifest, count or arbitrary File is not an owner.
use super::*;
use std::sync::{
    Arc,
    atomic::{AtomicBool, Ordering},
};

pub struct MemberOriginalContext {
    client: crate::client::Client,
    request: host::MemberOriginalRequest,
    context: crate::Context,
    sdk: crate::client::sdk::OriginalSdkKeeper,
    failed: AtomicBool,
}
impl MemberOriginalContext {
    // Only the authenticated member/worker receivers in this module tree can
    // issue this, after native peer/subject/SDK and original FD checks.
    pub(super) fn capture(
        client: crate::client::Client,
        request: host::MemberOriginalRequest,
        context: crate::Context,
        deadline: Instant,
    ) -> io::Result<Arc<Self>> {
        let sdk = crate::client::sdk::retain_sdk_keeper(&context)?;
        let original =
            Arc::new(Self { client, request, context, sdk, failed: AtomicBool::new(false) });
        original.validate(deadline)?;
        Ok(original)
    }
    pub fn observation(&self) -> &crate::Context {
        &self.context
    }
    pub fn request(&self) -> &host::MemberOriginalRequest {
        &self.request
    }
    pub fn controller(&self) -> &crate::client::Client {
        &self.client
    }
    pub fn validate(&self, deadline: Instant) -> io::Result<()> {
        let result = (|| {
            if self.failed.load(Ordering::Acquire) || Instant::now() >= deadline {
                return Err(refused());
            }
            self.request.encode()?;
            if self.context.root_attempt != self.request.query.binding.root_attempt
                || self.context.session != self.request.query.binding.session
                || !matches!(self.context.cpu, crate::Cpu::CooperativeShared { ceiling, .. } if ceiling > 0)
            {
                return Err(refused());
            }
            self.client.host.validate(deadline)?;
            live_context(&self.context, Some(self.request.member_attempt))?;
            self.sdk.validate(&self.context)?;
            self.client.host.validate(deadline)?;
            if Instant::now() >= deadline {
                return Err(io::ErrorKind::TimedOut.into());
            }
            Ok(())
        })();
        if result.is_err() {
            self.failed.store(true, Ordering::Release);
        }
        if self.failed.load(Ordering::Acquire) {
            return result.and_then(|()| Err(refused()));
        }
        result
    }
}
