use rustc_ast as ast;
use rustc_ast::tokenstream::TokenStream;
use rustc_data_structures::AtomicRef;
use rustc_data_structures::profiling::TimingGuard;
use rustc_errors::ErrorGuaranteed;
use rustc_parse::parser::{AllowConstBlockItems, ForceCollect, Parser};
use rustc_proc_macro as pm;
use rustc_session::Session;
use rustc_session::config::ProcMacroExecutionStrategy;
use rustc_span::profiling::SpannedEventArgRecorder;
use rustc_span::{LocalExpnId, Span};

use crate::base::{self, *};
// Trust (D21): the sandboxed worker `-Ztrust-proc-macro-isolation` expands in.
use crate::proc_macro_server::isolation::launch::{self, Failure, Shape};
pub use crate::proc_macro_server::isolation::launch::{IsolatedClient, IsolatedDylib};
use crate::{diagnostics, proc_macro_server};

/// Trust (D21): where a proc macro's code runs. The crate loader decides once
/// per proc-macro crate, from `-Ztrust-proc-macro-isolation`.
#[derive(Clone, Copy)]
pub enum MacroClient {
    /// The dylib is loaded in this process and the macro is called through the
    /// native bridge (upstream behaviour).
    InProcess(pm::bridge::client::Client),
    /// No dylib is loaded in this process; a sandboxed worker runs the macro.
    Isolated(IsolatedClient),
}

/// Trust (D21): the canonical compiler executable's first act, before it reads
/// options or touches a descriptor. In the worker role
/// (`--trust-proc-macro-worker <dylib> <symbol>`, started only by the isolation
/// launcher) this runs the worker and returns its exit status. Otherwise it
/// records this executable as the one that runs workers and returns `None`.
pub fn trust_isolated_worker_entry() -> Option<std::process::ExitCode> {
    let mut arguments = std::env::args_os().skip(1);
    if arguments.next().is_some_and(|first| first == launch::WORKER_ARGUMENT) {
        return Some(proc_macro_server::isolation::worker::main(arguments.collect()));
    }
    #[cfg(target_os = "macos")]
    if let Ok(executable) = std::env::current_exe() {
        launch::register_worker_executable(executable);
    }
    None
}

// Trust (D21): the in-process strategy. An isolated client does not use it: its
// macro runs on the worker's own thread, in the worker's process.
fn exec_strategy(sess: &Session) -> impl pm::bridge::server::ExecutionStrategy + 'static {
    pm::bridge::server::MaybeCrossThread {
        cross_thread: sess.opts.unstable_opts.proc_macro_execution_strategy
            == ProcMacroExecutionStrategy::CrossThread,
    }
}

fn record_expand_proc_macro<'a>(
    ecx: &ExtCtxt<'a>,
    name: &'static str,
    span: Span,
) -> TimingGuard<'a> {
    ecx.sess.prof.generic_activity_with_arg_recorder(name, |recorder| {
        recorder.record_arg_with_span(ecx.sess.source_map(), ecx.expansion_descr(), span);
    })
}

pub struct BangProcMacro {
    pub client: MacroClient,
}

impl base::BangProcMacro for BangProcMacro {
    fn expand(
        &self,
        ecx: &mut ExtCtxt<'_>,
        span: Span,
        input: TokenStream,
    ) -> Result<TokenStream, ErrorGuaranteed> {
        let _timer = record_expand_proc_macro(ecx, "expand_proc_macro", span);

        let proc_macro_backtrace = ecx.ecfg.proc_macro_backtrace;
        // Trust (D21): one report for a panic, wherever the macro ran.
        let panicked = |ecx: &ExtCtxt<'_>, message: Option<String>| {
            ecx.dcx().emit_err(diagnostics::ProcMacroPanicked {
                span,
                message: message.map(|message| diagnostics::ProcMacroPanickedHelp { message }),
            })
        };
        let client = match self.client {
            MacroClient::InProcess(client) => client,
            MacroClient::Isolated(client) => {
                return launch::expand(ecx, span, client, Shape::Bang, vec![input]).map_err(
                    |failure| match failure {
                        Failure::Panicked(message) => panicked(ecx, message),
                        Failure::Refused(guaranteed) => guaranteed,
                    },
                );
            }
        };
        let strategy = exec_strategy(ecx.sess);
        let server = proc_macro_server::Rustc::new(ecx);
        client
            .run1(&strategy, server, input, proc_macro_backtrace)
            .map_err(|e| panicked(ecx, e.into_string()))
    }
}

pub struct AttrProcMacro {
    pub client: MacroClient,
}

impl base::AttrProcMacro for AttrProcMacro {
    fn expand(
        &self,
        ecx: &mut ExtCtxt<'_>,
        span: Span,
        annotation: TokenStream,
        annotated: TokenStream,
    ) -> Result<TokenStream, ErrorGuaranteed> {
        let _timer = record_expand_proc_macro(ecx, "expand_proc_macro", span);

        let proc_macro_backtrace = ecx.ecfg.proc_macro_backtrace;
        // Trust (D21): one report for a panic, wherever the macro ran.
        let panicked = |ecx: &ExtCtxt<'_>, message: Option<String>| {
            ecx.dcx().emit_err(diagnostics::CustomAttributePanicked {
                span,
                message: message
                    .map(|message| diagnostics::CustomAttributePanickedHelp { message }),
            })
        };
        let client = match self.client {
            MacroClient::InProcess(client) => client,
            MacroClient::Isolated(client) => {
                let inputs = vec![annotation, annotated];
                return launch::expand(ecx, span, client, Shape::Attr, inputs).map_err(|failure| {
                    match failure {
                        Failure::Panicked(message) => panicked(ecx, message),
                        Failure::Refused(guaranteed) => guaranteed,
                    }
                });
            }
        };
        let strategy = exec_strategy(ecx.sess);
        let server = proc_macro_server::Rustc::new(ecx);
        client
            .run2(&strategy, server, annotation, annotated, proc_macro_backtrace)
            .map_err(|e| panicked(ecx, e.into_string()))
    }
}

pub struct DeriveProcMacro {
    pub client: DeriveClient,
}

impl MultiItemModifier for DeriveProcMacro {
    fn expand(
        &self,
        ecx: &mut ExtCtxt<'_>,
        span: Span,
        _meta_item: &ast::MetaItem,
        item: Annotatable,
        _is_derive_const: bool,
    ) -> ExpandResult<Vec<Annotatable>, Annotatable> {
        let _timer = record_expand_proc_macro(ecx, "expand_derive_proc_macro_outer", span);

        // We need special handling for statement items
        // (e.g. `fn foo() { #[derive(Debug)] struct Bar; }`)
        let is_stmt = matches!(item, Annotatable::Stmt(..));

        let input = item.to_tokens();

        let invoc_id = ecx.current_expansion.id;

        let res = if ecx.sess.opts.incremental.is_some()
            && ecx.sess.opts.unstable_opts.cache_proc_macros
        {
            (*EXPAND_DERIVE_MACRO_CACHED)(invoc_id, input, ecx, self.client)
        } else {
            expand_derive_macro(invoc_id, input, ecx, self.client)
        };

        let Ok(output) = res else {
            // error will already have been emitted
            return ExpandResult::Ready(vec![]);
        };

        let error_count_before = ecx.dcx().err_count();
        let mut parser = Parser::new(&ecx.sess.psess, output, Some("proc-macro derive"));
        let mut items = vec![];

        loop {
            match parser.parse_item(
                ForceCollect::No,
                if is_stmt { AllowConstBlockItems::No } else { AllowConstBlockItems::Yes },
            ) {
                Ok(None) => break,
                Ok(Some(item)) => {
                    if is_stmt {
                        items.push(Annotatable::Stmt(Box::new(ecx.stmt_item(span, item))));
                    } else {
                        items.push(Annotatable::Item(item));
                    }
                }
                Err(err) => {
                    err.emit();
                    break;
                }
            }
        }

        // fail if there have been errors emitted
        if ecx.dcx().err_count() > error_count_before {
            ecx.dcx().emit_err(diagnostics::ProcMacroDeriveTokens { span });
        }

        ExpandResult::Ready(items)
    }
}

// Trust (D21): a derive runs wherever its crate's macros run.
pub type DeriveClient = MacroClient;

pub fn expand_derive_macro(
    invoc_id: LocalExpnId,
    input: TokenStream,
    ecx: &mut ExtCtxt<'_>,
    client: DeriveClient,
) -> Result<TokenStream, ()> {
    let _timer =
        ecx.sess.prof.generic_activity_with_arg_recorder("expand_proc_macro", |recorder| {
            let invoc_expn_data = invoc_id.expn_data();
            let span = invoc_expn_data.call_site;
            let event_arg = invoc_expn_data.kind.descr();
            recorder.record_arg_with_span(ecx.sess.source_map(), event_arg, span);
        });

    let proc_macro_backtrace = ecx.ecfg.proc_macro_backtrace;
    // Trust (D21): one report for a panic, wherever the macro ran.
    let panicked = |ecx: &ExtCtxt<'_>, message: Option<String>| {
        let invoc_expn_data = invoc_id.expn_data();
        let span = invoc_expn_data.call_site;
        ecx.dcx().emit_err({
            diagnostics::ProcMacroDerivePanicked {
                span,
                message: message
                    .map(|message| diagnostics::ProcMacroDerivePanickedHelp { message }),
            }
        });
    };
    let client = match client {
        MacroClient::InProcess(client) => client,
        MacroClient::Isolated(client) => {
            let span = invoc_id.expn_data().call_site;
            return launch::expand(ecx, span, client, Shape::Derive, vec![input]).map_err(
                |failure| match failure {
                    Failure::Panicked(message) => panicked(ecx, message),
                    // Already reported, as a derive's panic is.
                    Failure::Refused(_) => {}
                },
            );
        }
    };
    let strategy = exec_strategy(ecx.sess);
    let server = proc_macro_server::Rustc::new(ecx);

    match client.run1(&strategy, server, input, proc_macro_backtrace) {
        Ok(stream) => Ok(stream),
        Err(e) => {
            panicked(ecx, e.into_string());
            Err(())
        }
    }
}

pub static EXPAND_DERIVE_MACRO_CACHED: AtomicRef<
    fn(LocalExpnId, TokenStream, &mut ExtCtxt<'_>, DeriveClient) -> Result<TokenStream, ()>,
> = AtomicRef::new(
    &(|_, _, _: &mut ExtCtxt<'_>, _| -> Result<_, _> {
        panic!(
            "`EXPAND_DERIVE_MACRO_CACHED` callback was not setup; it must be set in `rustc_interface::callbacks`"
        )
    } as _),
);
