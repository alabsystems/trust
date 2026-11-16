use super::*;
use crate::workload::host::produced::tests as fixtures;
use crate::{CompletionCause, MetadataCompletion, Outcome, Status, StatusFrame};

pub(crate) fn request() -> Request {
    Request {
        operation: [21; 16],
        gnu: FileIdentity { device: 11, inode: 17 },
        produced: fixtures::request(),
    }
}
pub(crate) fn completion() -> Completion {
    Completion {
        operation: [21; 16],
        request_sha256: [19; 32],
        gnu: request().gnu,
        completion: ProducedCompletion {
            phase: request().produced.key.ordinal,
            kind: request().produced.kind,
            completed: MetadataCompletion {
                finished: StatusFrame {
                    root_attempt: [1; 16],
                    member_attempt: [8; 16],
                    status: Status::Finished {
                        outcome: Outcome::Exit(0),
                        cause: CompletionCause::Exited,
                        runtime_ns: 17,
                    },
                },
                inputs_unchanged: Ok(()),
            },
            observation: crate::accounting::Observation::uncollected(),
        },
    }
}
#[test]
fn exact_mode_preserves_full_produced_request_and_cross_refuses_legacy() {
    let request = request();
    assert!(Request::decode(&request.encode().unwrap()).unwrap() == request);
    assert!(Request::decode(&request.produced.encode().unwrap()).is_err());
    assert!(ProducedRequest::decode(&request.encode().unwrap()).is_err());
    assert!(std::str::from_utf8(&request.hello().unwrap()).unwrap().contains(PURPOSE));
    let preimage = request.binding_preimage().unwrap();
    assert!(preimage.starts_with(BINDING_DOMAIN));
    assert!(preimage.ends_with(&request.encode().unwrap()));
    let mut bytes = request.encode().unwrap();
    bytes.push(0);
    assert!(Request::decode(&bytes).is_err());
}
#[test]
fn native_completion_data_is_exactly_operation_root_member_gnu_phase_bound() {
    let request = request();
    let completion = completion();
    assert_eq!(
        Completion::decode(&completion.encode().unwrap(), &request, [19; 32]).unwrap(),
        completion
    );
    assert!(
        Completion::decode(&completion.completion.encode().unwrap(), &request, [19; 32]).is_err()
    );
    for which in 0..7 {
        let mut wrong = completion.clone();
        match which {
            0 => wrong.operation[0] ^= 1,
            1 => wrong.request_sha256[0] ^= 1,
            2 => wrong.gnu.inode += 1,
            3 => wrong.completion.phase += 1,
            4 => wrong.completion.kind = super::super::MemberKind::Sample,
            5 => wrong.completion.completed.finished.root_attempt[0] ^= 1,
            _ => wrong.completion.completed.finished.member_attempt[0] ^= 1,
        }
        assert!(Completion::decode(&wrong.encode().unwrap(), &request, [19; 32]).is_err());
    }
    let mut bytes = completion.encode().unwrap();
    bytes.push(0);
    assert!(Completion::decode(&bytes, &request, [19; 32]).is_err());
}
#[test]
fn operation_nonce_and_complete_bounded_fifo_observation_are_required() {
    for which in 0..6 {
        let mut wrong = request();
        match which {
            0 => wrong.operation = [0; 16],
            1 => wrong.operation = wrong.produced.member.member_attempt,
            2 => wrong.operation = wrong.produced.key.root_attempt,
            3 => wrong.operation = wrong.produced.key.phase,
            4 => wrong.operation = wrong.produced.key.output,
            _ => wrong.gnu.inode = 0,
        }
        assert!(wrong.encode().is_err());
    }
}
