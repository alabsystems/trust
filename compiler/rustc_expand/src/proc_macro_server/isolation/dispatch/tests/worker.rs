//! Trust (D21): native client/worker/byte protocol/compiler round trips.
use std::cell::RefCell;

use rustc_proc_macro::bridge::client::Client;
use rustc_proc_macro as pm;
use trust_proc_macro_bridge::{Transport, Worker};
use trust_process_isolation::{decode, encode};

use super::*;

#[derive(Clone, Copy)]
enum Fault {
    None,
    Closed,
    Panic,
    Truncated,
    Binding,
    Id,
    Type,
    ReplayedStream,
    ForeignHandle,
    Finish,
    FinishPanic,
}
#[derive(Default)]
struct Observed {
    calls: Vec<Method>,
    closed: usize,
    finishes: usize,
    output: Option<String>,
    budget_calls: u64,
    drop_while_unwinding: bool,
}
struct Duplex<'a, 'b, 'c> {
    dispatcher: &'a mut Dispatcher<'b, 'c>,
    session: &'a mut Session,
    reply: Option<Vec<u8>>,
    observed: Rc<RefCell<Observed>>,
    fault: Fault,
    input: Handle,
}
impl Transport for Duplex<'_, '_, '_> {
    fn send(&mut self, bytes: &[u8], budget: &Budget) -> Result<(), Error> {
        let envelope = decode(bytes, budget)?;
        if matches!(envelope.message, Message::Finish { .. })
            && matches!(self.fault, Fault::FinishPanic)
        {
            panic!("finish-only transport panic");
        }
        if matches!(envelope.message, Message::Finish { .. }) && matches!(self.fault, Fault::Finish)
        {
            return Err(Error::InvalidWire("closed during finish"));
        }
        match self.session.receive(envelope)? {
            Admission::Call(call) => {
                self.observed.borrow_mut().calls.push(call.method);
                if call.method == Method::TsDrop && std::thread::panicking() {
                    self.observed.borrow_mut().drop_while_unwinding = true;
                }
                let id = call.id;
                let value = self.dispatcher.dispatch(self.session, call)?;
                let mut reply = self.session.reply(id, value)?;
                match self.fault {
                    Fault::Binding => reply.binding.unit = [99; 32],
                    Fault::Id => {
                        if let Message::Reply { id, .. } = &mut reply.message {
                            *id += 1;
                        }
                    }
                    Fault::Type => {
                        if let Message::Reply { value, .. } = &mut reply.message {
                            *value = Value::Unit;
                        }
                    }
                    Fault::ReplayedStream | Fault::ForeignHandle => {
                        if let Message::Reply { value, .. } = &mut reply.message {
                            if let Value::Stream(h) = value {
                                if matches!(self.fault, Fault::ReplayedStream) {
                                    *h = self.input;
                                } else {
                                    h.invocation += 1;
                                }
                            }
                        }
                    }
                    _ => {}
                }
                let mut bytes = encode(&reply, budget)?;
                if matches!(self.fault, Fault::Truncated) {
                    bytes.pop();
                }
                self.reply = Some(bytes);
            }
            Admission::Finished(output) => {
                let mut observed = self.observed.borrow_mut();
                observed.finishes += 1;
                observed.output = Some(match output {
                    Some(h) => {
                        let stream = self.dispatcher.tokens.stream(h)?;
                        self.dispatcher.server.ts_to_string(&stream)
                    }
                    None => String::new(),
                });
            }
            _ => return Err(Error::Phase),
        }
        Ok(())
    }
    fn receive(&mut self, _: &Budget) -> Result<Vec<u8>, Error> {
        if matches!(self.fault, Fault::Panic) {
            panic!("transport panic fixture");
        }
        if matches!(self.fault, Fault::Closed) {
            return Err(Error::InvalidWire("closed transport"));
        }
        self.reply.take().ok_or(Error::InvalidWire("missing reply"))
    }
    fn close(&mut self) {
        self.observed.borrow_mut().closed += 1;
        self.observed.borrow_mut().budget_calls = self.session.budget().usage().unwrap().calls;
        self.reply = None;
        self.dispatcher.tokens.values.clear();
        if self.session.phase() != Phase::Terminal {
            self.session.cancel();
        }
    }
}

fn run(client: Client, fault: Fault, kind: u8) -> (Result<(), Error>, Rc<RefCell<Observed>>) {
    run_table(&[client], 0, fault, kind)
}

fn run_table(
    declarations: &[Client],
    declaration: u32,
    fault: Fault,
    kind: u8,
) -> (Result<(), Error>, Rc<RefCell<Observed>>) {
    let observed = Rc::new(RefCell::new(Observed::default()));
    let mut result = Ok(());
    with_dispatcher(|d, s, _, _| {
        let input = d.server.ts_from_str("alpha beta").unwrap();
        let input = d.store_input(input).unwrap();
        let inputs = if kind == 1 {
            let b = d.server.ts_from_str("attribute").unwrap();
            vec![input, d.store_input(b).unwrap()]
        } else {
            vec![input]
        };
        let begin = Envelope {
            binding: s.binding().clone(),
            message: Message::Begin { declaration, kind, inputs, globals: d.globals },
        };
        let budget = s.budget().clone();
        let transport = Duplex {
            dispatcher: d,
            session: s,
            reply: None,
            observed: observed.clone(),
            fault,
            input,
        };
        let mut worker = Worker::from_begin(begin, budget.clone(), transport).unwrap();
        result =
            std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                worker.run_declared(declarations, false)
            }))
            .expect("Worker::run_declared must contain the transport unwind");
        if let Err(error) = &result {
            assert!(budget.check().is_err());
            assert_eq!(observed.borrow().closed, 1, "close must precede Worker drop");
            assert_eq!(worker.run_declared(declarations, false), Err(error.clone()));
            assert_eq!(observed.borrow().closed, 1, "retry must remain terminal");
        }
        drop(worker);
        if result.is_ok() {
            assert_eq!(budget.check(), Ok(()));
        } else {
            assert!(budget.check().is_err());
        }
        assert_eq!(d.tokens.values.live(), 0);
    });
    (result, observed)
}

#[test]
fn native_client_uses_the_compiler_selected_declaration() {
    let declarations = [
        Client::expand1(|_| "first_declaration".parse().unwrap()),
        Client::expand1(|_| "selected_declaration".parse().unwrap()),
    ];
    let (result, observed) = run_table(&declarations, 1, Fault::None, 0);
    result.unwrap();
    let observed = observed.borrow();
    assert_eq!(observed.output.as_deref(), Some("selected_declaration"));
    assert_eq!(observed.finishes, 1);
}

#[test]
fn invalid_declaration_refuses_before_entering_native_client() {
    let declarations = [Client::expand1(|_| panic!("invalid index entered native client"))];
    for (table, index) in [(&declarations[..], 1), (&declarations[..], u32::MAX), (&[][..], 0)] {
        let (result, observed) = run_table(table, index, Fault::None, 0);
        assert_eq!(result, Err(Error::InvalidWire("native macro declaration index")));
        let observed = observed.borrow();
        assert_eq!(observed.finishes, 0);
        assert!(observed.calls.is_empty());
    }
}

#[path = "native_client_methods.rs"]
mod native_client_methods;
pub(super) use native_client_methods::all_methods;

#[test]
fn exact_native_client_forwards_all_32_methods_through_b1_and_real_compiler() {
    let (result, observed) = run(Client::expand1(all_methods), Fault::None, 0);
    result.unwrap();
    let o = observed.borrow();
    assert_eq!(o.closed, 1);
    assert_eq!(o.finishes, 1);
    assert_eq!(o.budget_calls, o.calls.len() as u64);
    assert_eq!(o.output.as_deref(), Some("alpha beta"));
    let mut tags = o.calls.iter().map(|m| m.tag()).collect::<Vec<_>>();
    tags.sort_unstable();
    tags.dedup();
    assert_eq!(tags, Method::ALL.iter().map(|m| m.tag()).collect::<Vec<_>>());
}

#[test]
fn native_attribute_abi_preserves_both_inputs_and_empty_result() {
    let client = Client::expand2(|a, b| {
        assert_eq!(a.to_string(), "alpha beta");
        assert_eq!(b.to_string(), "attribute");
        pm::TokenStream::new()
    });
    let (result, o) = run(client, Fault::None, 1);
    result.unwrap();
    assert_eq!(o.borrow().output.as_deref(), Some(""));
    assert_eq!(o.borrow().finishes, 1);
}

#[test]
fn native_macro_cannot_catch_protocol_failure_and_finish_successfully() {
    for fault in
        [Fault::Closed, Fault::Panic, Fault::Truncated, Fault::Binding, Fault::Id, Fault::Type]
    {
        let client = Client::expand1(|input| {
            assert!(std::panic::catch_unwind(|| input.to_string()).is_err());
            let _ = std::panic::catch_unwind(|| pm::tracked::path("must-not-dispatch"));
            pm::TokenStream::new()
        });
        let (result, o) = run(client, fault, 0);
        assert!(result.is_err());
        let o = o.borrow();
        assert_eq!(o.closed, 1);
        assert_eq!(o.finishes, 0);
        assert_eq!(o.calls.len(), 1);
    }
}

#[test]
fn native_worker_rejects_replayed_and_foreign_result_handles() {
    for fault in [Fault::ReplayedStream, Fault::ForeignHandle] {
        let client = Client::expand1(|input| input.clone());
        let (result, o) = run(client, fault, 0);
        assert!(result.is_err());
        assert_eq!(o.borrow().finishes, 0);
        assert_eq!(o.borrow().closed, 1);
    }
}

#[test]
fn native_panic_and_final_transport_loss_never_send_success() {
    let (result, o) = run(Client::expand1(|_| panic!("native fixture panic")), Fault::None, 0);
    assert!(result.is_err());
    assert_eq!(o.borrow().finishes, 0);
    assert_eq!(o.borrow().closed, 1);
    let (result, o) = run(Client::expand1(|s| s), Fault::Finish, 0);
    assert!(result.is_err());
    assert_eq!(o.borrow().finishes, 0);
    assert_eq!(o.borrow().closed, 1);
}

#[test]
fn first_transport_failure_during_native_unwind_is_cleanup_not_double_panic() {
    for fault in [Fault::Closed, Fault::Panic] {
        let (result, observed) = run(
            Client::expand1(|input| {
                let _keep_input = input;
                panic!("native fixture before drop")
            }),
            fault,
            0,
        );
        assert!(result.is_err());
        assert_eq!(observed.borrow().finishes, 0);
        assert_eq!(observed.borrow().closed, 1);
        assert_eq!(observed.borrow().calls, vec![Method::TsDrop]);
        assert!(observed.borrow().drop_while_unwinding);
    }
}

struct Sink(Rc<Cell<usize>>);
impl Transport for Sink {
    fn send(&mut self, _: &[u8], _: &Budget) -> Result<(), Error> {
        panic!("constructor sent a frame")
    }
    fn receive(&mut self, _: &Budget) -> Result<Vec<u8>, Error> {
        panic!("constructor read a frame")
    }
    fn close(&mut self) {
        self.0.set(self.0.get() + 1);
    }
}
fn begin_fixture() -> Envelope {
    let span = Handle {
        invocation: 17,
        kind: trust_process_isolation::HandleKind::Span,
        slot: 0,
        generation: 1,
    };
    let stream = Handle { kind: trust_process_isolation::HandleKind::Stream, slot: 1, ..span };
    Envelope {
        binding: binding(),
        message: Message::Begin {
            declaration: 0,
            kind: 0,
            inputs: vec![stream],
            globals: [span; 3],
        },
    }
}
#[test]
fn decoded_begin_does_not_spend_wire_bytes_again() {
    let sender = Budget::new(limits(), Instant::now() + Duration::from_secs(30)).unwrap();
    let receiver = Budget::new(limits(), sender.deadline()).unwrap();
    let encoded = encode(&begin_fixture(), &sender).unwrap();
    let begin = decode(&encoded, &receiver).unwrap();
    let before = receiver.usage().unwrap();
    let closed = Rc::new(Cell::new(0));
    let worker = Worker::from_begin(begin, receiver.clone(), Sink(closed.clone())).unwrap();
    assert_eq!(receiver.usage().unwrap().wire_bytes, before.wire_bytes);
    assert!(receiver.usage().unwrap().allocation_bytes > before.allocation_bytes);
    assert!(receiver.usage().unwrap().work > before.work);
    assert_eq!(receiver.usage().unwrap().calls, 0);
    drop(worker);
    assert_eq!(closed.get(), 1);
}
#[test]
fn invalid_begin_closes_without_starting_native_client_or_transport() {
    for fault in 0..5 {
        let mut begin = begin_fixture();
        let Message::Begin { kind, inputs, globals, .. } = &mut begin.message else {
            unreachable!()
        };
        match fault {
            0 => *kind = 3,
            1 => inputs.clear(),
            2 => inputs[0].invocation += 1,
            3 => globals[0].generation = 0,
            _ => inputs[0].kind = trust_process_isolation::HandleKind::Span,
        }
        let budget = Budget::new(limits(), Instant::now() + Duration::from_secs(30)).unwrap();
        let closed = Rc::new(Cell::new(0));
        assert!(Worker::from_begin(begin, budget.clone(), Sink(closed.clone())).is_err());
        assert!(budget.check().is_err());
        assert_eq!(closed.get(), 1);
    }
}

#[test]
fn invalid_quoted_span_refusal_stays_terminal_across_native_catch_unwind() {
    let client = Client::expand1(|input| {
        assert!(
            std::panic::catch_unwind(|| pm::Span::recover_proc_macro_span(usize::MAX)).is_err()
        );
        input
    });
    let (result, observed) = run(client, Fault::None, 0);
    assert!(result.is_err());
    assert_eq!(observed.borrow().calls, vec![Method::SpanRecoverProcMacroSpan]);
    assert_eq!(observed.borrow().finishes, 0);
    assert_eq!(observed.borrow().closed, 1);
}

#[test]
fn finish_transport_panic_refuses_before_worker_is_dropped() {
    let (result, observed) = run(Client::expand1(|input| input), Fault::FinishPanic, 0);
    assert_eq!(result, Err(Error::InvalidWire("native worker operation panicked")));
    assert_eq!(observed.borrow().finishes, 0);
    assert_eq!(observed.borrow().closed, 1);
}
