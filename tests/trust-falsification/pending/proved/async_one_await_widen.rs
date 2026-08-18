#![crate_type = "lib"]
// PENDING proved-side fixture for the coroutine resume-state CONTRACT lane
// (piece #13 step-3): a ONE-AWAIT `async fn`. The coroutine's resume dispatch
// case set is {0 (unresumed), 1 (returned), 2 (poisoned), 3 (suspend#0)}, so
// the exported live set is {0, 3} — the entry contract must be the DISJUNCTION
// `state == 0 || state == 3`, and the ResumedAfter* sentinels must still be
// solver-proved unreachable under it. The data obligation is safe for every
// input: `(x as u16) + (y as u16)` with x, y: u8 caps at 510 < 65536.
//
// EXPECTED verdict (post-rebuild): the coroutine body publishes
// `contract:coroutine-resume-state` naming {0, 3}, sentinels PROVED; the
// across-await saved local stays havoc'd (no new data facts may leak from the
// state constraint — the mutant sibling pins this). It sits in pending/, not
// proved/, because the fixture ALSO contains the in-crate `YieldOnce` executor
// plumbing (`Poll`/`Context` absent callees) whose rows are expected red until
// the std-totality work lands — the gate's proved lane requires rc 0.
// PROMOTE to proved/ once the fixture verifies end-to-end.
use std::future::Future;
use std::pin::Pin;
use std::task::{Context, Poll};

pub struct YieldOnce(bool);

impl Future for YieldOnce {
    type Output = u8;
    fn poll(mut self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<u8> {
        if self.0 {
            Poll::Ready(7)
        } else {
            self.0 = true;
            cx.waker().wake_by_ref();
            Poll::Pending
        }
    }
}

pub async fn g(x: u8) -> u16 {
    let y = YieldOnce(false).await;
    (x as u16) + (y as u16)
}
