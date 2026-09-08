//@ check-pass
//@ compile-flags: -Ztrust-ir-lower -Ztrust-verify=off
//@ edition: 2021
// B5 stage 4, increment 1 (wave-FS4): the first async bodies with a real
// `.await` lower end to end. Two halves, each with its own argument:
//
// * The stage-2b `Yield(promoted local across suspend)` refusal is RE-KEYED
//   on the fact its own argument names — an ALLOCA-BACKED SLOT, which dies
//   with the activation. The await desugar's `__awaitee` is
//   promoted-COLLECTED but never slot-ALLOCATED (its opaque-carrier binding
//   is a plain SSA `set_local`): there is no dying memory, so it havocs to
//   Undef at the continuation exactly like every other live local (NotRun
//   stays forced — the unknown is never interpreted). A var WITH an Alloca
//   slot keeps the refusal verbatim.
// * In an ASYNC frame-pointer coroutine, an admissible promoted local takes
//   a FRAME-RESIDENT slot (`GEP frame + offset`, producer-defined 16-stride
//   layout from offset 16; `[state]` owns 0..8) instead of an Alloca — the
//   caller-owned frame survives suspends. The async-first fence (no caller
//   lane exists for `Desugared(Async)` kinds, no splice, NotRun) makes this
//   emission-only; plain coroutines keep the old behavior until the
//   stage-3a caller frame widens in the same increment (D3 coupling).
//
// The await's `_task_context = yield ()` assign then lowers too: the yield
// produces the continuation's resume param (the fresh context), which is
// exactly what the desugar stores back.

async fn leaf() {}

pub async fn one_await() {
    leaf().await
}

pub async fn two_awaits() {
    leaf().await;
    leaf().await
}

pub async fn await_in_sequence(n: i64) -> i64 {
    let mut acc = n;
    acc += 1;
    leaf().await;
    acc
}

// THE FRAME-HALF PIN: `acc` is `&mut`-borrowed (promoted) AND live across
// the suspend. Under the old Alloca path the re-keyed refusal would fire
// (`promoted_slot` present, not frame-resident); this body lowering is the
// witness that the promotion took the FRAME-RESIDENT slot.
fn bump(x: &mut i64) {
    *x += 1;
}
pub async fn carry_across(n: i64) -> i64 {
    let mut acc = n;
    bump(&mut acc);
    leaf().await;
    bump(&mut acc);
    acc
}
