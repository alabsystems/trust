// Trust: prepare contract diagnostics as ordered report DATA.
// Source-dependent queries run once at the original eager callpoint.

use super::*;

pub(super) fn prepare_coroutine_protocol_assumption(
    _tcx: TyCtxt<'_>,
    body: &Body<'_>,
    func_path: &str,
) -> PreparedLocatedDiagnostic {
    PreparedLocatedDiagnostic {
        span: body.span,
        diagnostic: PreparedDiagnostic {
            aborting: true,
            header: format!(
                "Trust strict verification failed for `{func_path}`: coroutine \
                 executor-protocol premise is unproved"
            ),
            children: vec![
                PreparedDiagnosticChild::Note(
                    "the compiler-generated ResumedAfterReturn/Panic/Drop sentinels are executor-protocol \
                     preconditions rather than user data-safety checks; supported user obligations were \
                     still verified and reported independently"
                        .into(),
                ),
                PreparedDiagnosticChild::Note(
                    "strict and memory-safe policy accept no unproved in-scope premise; use the explicit \
                     -Ztrust-policy=advisory advisory lane to retain this as conditional \
                     evidence"
                        .into(),
                ),
            ],
        },
    }
}

pub(super) fn prepare_entry_termination_dispatch(
    _tcx: TyCtxt<'_>,
    body: &Body<'_>,
    func_path: &str,
) -> PreparedLocatedDiagnostic {
    PreparedLocatedDiagnostic {
        span: body.span,
        diagnostic: PreparedDiagnostic {
            aborting: true,
            header: format!(
                "Trust certify verification failed for `{func_path}`: `main`'s return type is \
                 dispatched by `lang_start` through `<_ as Termination>::report` into foreign \
                 or dynamic code this compilation does not verify"
            ),
            children: vec![PreparedDiagnosticChild::Note(
                "under `-Ztrust-policy=certify` a reported gap is fatal; return `()`, `ExitCode`, \
                 or an error type whose `Debug`/`Drop` are verified in this crate, or build on the \
                 default lane where the row is reported and counted conditional"
                    .into(),
            )],
        },
    }
}

pub(super) fn prepare_global_alloc_dealloc_contract_refusal(
    tcx: TyCtxt<'_>,
    body: &Body<'_>,
    func_path: &str,
    refusal: GlobalAllocRefusal,
) -> PreparedLocatedDiagnostic {
    let interposer = match refusal {
        GlobalAllocRefusal::UserAllocator => user_allocator_interposer_only(tcx),
        GlobalAllocRefusal::AllocErrorHook => None,
    };
    match (refusal, interposer) {
        (GlobalAllocRefusal::UserAllocator, None) => PreparedLocatedDiagnostic {
            span: body.span,
            diagnostic: PreparedDiagnostic {
                aborting: true,
                header: format!(
                    "Trust strict verification failed for `{func_path}`: the \
                     `contract:global-alloc-dealloc-panic-free` caller contract is refused — a \
                     user `#[global_allocator]` is registered and its `dealloc` impl is not \
                     verified panic-free"
                ),
                children: vec![
                    PreparedDiagnosticChild::Note(
                        "this body drops an allocation-owning std container, whose drop glue calls the \
                         registered global allocator's `dealloc`; with the default `Global` allocator \
                         that call chain is panic-free by inspection, but a user `#[global_allocator]` \
                         replaces it with unverified code"
                            .into(),
                    ),
                    PreparedDiagnosticChild::Note(
                        "no discharge lane verifies a user `dealloc` impl yet, so this contract fails \
                         closed; remove the `#[global_allocator]` registration, avoid allocation-owning \
                         drops in verified code, or use the explicit -Ztrust-policy=advisory advisory \
                         lane to retain this as a recorded refused contract"
                            .into(),
                    ),
                ],
            },
        },
        (GlobalAllocRefusal::UserAllocator, Some(interposer)) => PreparedLocatedDiagnostic {
            span: body.span,
            diagnostic: PreparedDiagnostic {
                aborting: true,
                header: format!(
                    "Trust strict verification failed for `{func_path}`: the \
                     `contract:global-alloc-dealloc-panic-free` caller contract is refused — {}, \
                     and that definition is not verified panic-free",
                    interposer.clause()
                ),
                children: vec![
                    PreparedDiagnosticChild::Note(
                        "std's default global allocator `System` calls `malloc`/`calloc`/`realloc`/\
                         `free`/`posix_memalign` by their C names; a definition of one of them linked \
                         into this artifact runs in place of the platform's inside every allocation and \
                         dealloc this body can reach"
                            .into(),
                    ),
                    PreparedDiagnosticChild::Note(
                        "no discharge lane verifies such a definition yet, so this contract fails \
                         closed; drop the exported allocator symbol (or the global assembly), or use \
                         the explicit -Ztrust-policy=advisory advisory lane to retain this as a \
                         recorded refused contract"
                            .into(),
                    ),
                ],
            },
        },
        (GlobalAllocRefusal::AllocErrorHook, _) => PreparedLocatedDiagnostic {
            span: body.span,
            diagnostic: PreparedDiagnostic {
                aborting: true,
                header: format!(
                    "Trust strict verification failed for `{func_path}`: the \
                     `contract:global-alloc-dealloc-panic-free` caller contract is refused — a \
                     crate in the graph references `std::alloc::set_alloc_error_hook`, so an \
                     allocation this body can reach may fail into a hook that panics"
                ),
                children: vec![
                    PreparedDiagnosticChild::Note(
                        "`handle_alloc_error` runs std's `rust_oom`, which calls the installed \
                         allocation-error hook and aborts only if the hook returns; the hook may panic, \
                         and that unwind is catchable (`set_alloc_error_hook`'s documentation, and \
                         rustc's `tests/ui/panics/alloc_error_hook-unwind.rs`)"
                            .into(),
                    ),
                    PreparedDiagnosticChild::Note(
                        "no lane verifies an allocation-error hook, so this contract fails closed; do \
                         not install a hook in a graph whose allocating code is verified, or use the \
                         explicit -Ztrust-policy=advisory advisory lane to retain this as a recorded \
                         refused contract"
                            .into(),
                    ),
                ],
            },
        },
    }
}
