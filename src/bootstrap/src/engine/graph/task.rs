//! Actual in-process producer/validator/test tasks in the original native scope.
//! A task result is data, never a proof grade, Host close or source-finalization owner.

use std::collections::BTreeSet;
use std::sync::Arc;
use std::time::Instant;

use super::{CapturedInputs, GraphError, InputObservation, OpenGraph};
use crate::engine::Outcome;

const MAX_DEPENDENCIES: usize = 64;
const MAX_ANCESTORS: usize = 1024;

struct Record<'owner> {
    inputs: CapturedInputs<'owner>,
    dependencies: Vec<Arc<Record<'owner>>>,
}

/// An actual successfully joined callback and its retained original input/dependency owners.
/// There is no constructor from a status, report, saved result or source digest.
/// This owner says nothing about the meaning or proof grade of the callback's return value.
pub struct TaskCompletion<'owner> {
    original: Arc<Record<'owner>>,
}

/// Returned only after the actual callback and original input/dependency bookends succeed.
/// Non-Clone; dependencies share the same private input owners without reopening files.
pub struct CompletedTask<'owner, T> {
    completion: TaskCompletion<'owner>,
    value: T,
}
impl<'owner, T> CompletedTask<'owner, T> {
    pub fn value(&self) -> &T {
        &self.value
    }
    pub fn completion(&self) -> &TaskCompletion<'owner> {
        &self.completion
    }
}

#[derive(Debug)]
pub enum TaskError<E> {
    Graph(GraphError),
    Work(E),
    WorkAndGraph { work: E, graph: GraphError },
}

/// Keeps this same attempted task's original inputs and prior dependency owners.
/// Neither a failed callback nor a failed bookend can become a completed dependency.
pub struct TaskFailure<'owner, T, E> {
    original: Arc<Record<'owner>>,
    error: TaskError<E>,
    returned: Option<T>,
}
impl<T, E> TaskFailure<'_, T, E> {
    pub fn error(&self) -> &TaskError<E> {
        &self.error
    }
    pub fn observations(&self) -> &[InputObservation] {
        self.original.inputs.observations()
    }
    /// Actual callback output retained after a failed final bookend. This is data only;
    /// it cannot be used as a successful task dependency or an input/proof judgment.
    pub fn returned_value(&self) -> Option<&T> {
        self.returned.as_ref()
    }
}
impl<T, E: std::fmt::Debug> std::fmt::Debug for TaskFailure<'_, T, E> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("TaskFailure").field("error", &self.error).finish_non_exhaustive()
    }
}

/// A lexical callback view; exports bytes only, never a path reopen or raw descriptor.
/// Its constructor and lifetime are private to the actual admitted native worker.
pub struct TaskInputs<'task, 'owner> {
    original: &'task CapturedInputs<'owner>,
    deadline: Instant,
}
impl TaskInputs<'_, '_> {
    pub fn observations(&self) -> &[InputObservation] {
        self.original.observations()
    }
    /// Read the exact captured file positionally and verify its original bytes and parents.
    /// This does not advance the held file cursor or replace its descriptor flags.
    pub fn read(&self, index: usize) -> Result<Vec<u8>, GraphError> {
        #[cfg(any(target_os = "macos", target_os = "linux"))]
        {
            super::native::read_input(self.original, index, self.deadline)
        }
        #[cfg(not(any(target_os = "macos", target_os = "linux")))]
        {
            let _ = (index, self.deadline);
            Err(super::unavailable())
        }
    }
}

impl<'owner> OpenGraph<'owner> {
    /// Execute one actual Rust callback under the original protected/GNU native worker.
    /// All predecessor input owners are recursively revalidated before and after the work.
    /// A callback returns ordinary data; success cannot mint Certified, SDK or Host closure.
    /// This joins the registered callback only. Trusted coordinator code must separately
    /// register and settle any work it starts; escaped threads/processes gain no completion.
    pub fn run_source_task<T: Send, E: Send>(
        &self,
        inputs: CapturedInputs<'owner>,
        dependencies: &[&TaskCompletion<'owner>],
        deadline: Instant,
        work: impl for<'task> FnOnce(TaskInputs<'task, 'owner>) -> Result<T, E> + Send,
    ) -> Result<CompletedTask<'owner, T>, TaskFailure<'owner, T, E>> {
        let original = Arc::new(Record {
            inputs,
            dependencies: if dependencies.len() > MAX_DEPENDENCIES {
                Vec::new()
            } else {
                dependencies.iter().map(|prior| Arc::clone(&prior.original)).collect()
            },
        });
        let failed =
            |error, returned| TaskFailure { original: Arc::clone(&original), error, returned };
        let preflight = || {
            if dependencies.len() > MAX_DEPENDENCIES {
                return Err(GraphError::InvalidDependencies("too many direct predecessors"));
            }
            let mut seen = BTreeSet::new();
            for prior in dependencies {
                if !seen.insert(Arc::as_ptr(&prior.original)) {
                    return Err(GraphError::InvalidDependencies("duplicate predecessor"));
                }
                if !std::ptr::eq(self.owner, prior.original.inputs.owner) {
                    return Err(GraphError::WrongDependencyOwner);
                }
            }
            check_owners(self.owner, &original)
        };
        preflight().map_err(|error| failed(TaskError::Graph(error), None))?;
        // The actual lexical join makes this caller-owned slot observable even when
        // the worker's final bookend or the outer original-owner bookend fails.
        #[cfg(any(target_os = "macos", target_os = "linux"))]
        let mut returned = None;
        #[cfg(not(any(target_os = "macos", target_os = "linux")))]
        let returned: Option<Result<T, E>> = None;
        #[cfg(any(target_os = "macos", target_os = "linux"))]
        let result = super::native::run(self.owner, deadline, |effective| {
            validate(self.owner, &original, effective)?;
            returned = Some(work(TaskInputs { original: &original.inputs, deadline: effective }));
            // A callback failure still receives the same final input/dependency bookend.
            validate(self.owner, &original, effective)
        });
        #[cfg(not(any(target_os = "macos", target_os = "linux")))]
        let result: Result<(), GraphError> = {
            let _ = (deadline, work);
            Err(super::unavailable())
        };
        let value = match (result, returned) {
            (Ok(()), Some(Ok(value))) => value,
            (Ok(()), Some(Err(error))) => return Err(failed(TaskError::Work(error), None)),
            (Err(graph), Some(Err(work))) => {
                return Err(failed(TaskError::WorkAndGraph { work, graph }, None));
            }
            (Err(error), Some(Ok(value))) => {
                return Err(failed(TaskError::Graph(error), Some(value)));
            }
            (Err(error), None) => return Err(failed(TaskError::Graph(error), None)),
            (Ok(()), None) => {
                return Err(failed(
                    TaskError::Graph(GraphError::OriginalOwner(
                        "native callback delivered no actual result".into(),
                    )),
                    None,
                ));
            }
        };
        Ok(CompletedTask { completion: TaskCompletion { original }, value })
    }
}

fn visit<'a, 'owner>(
    original: &'a Arc<Record<'owner>>,
    mut check: impl FnMut(&'a Record<'owner>) -> Result<(), GraphError>,
) -> Result<(), GraphError> {
    let mut pending = vec![original];
    let mut seen = BTreeSet::new();
    while let Some(record) = pending.pop() {
        if !seen.insert(Arc::as_ptr(record)) {
            continue;
        }
        if seen.len() > MAX_ANCESTORS {
            return Err(GraphError::InvalidDependencies("transitive predecessor bound exceeded"));
        }
        check(record)?;
        pending.extend(&record.dependencies);
    }
    Ok(())
}
fn check_owners(owner: &Outcome, original: &Arc<Record<'_>>) -> Result<(), GraphError> {
    visit(original, |record| {
        if std::ptr::eq(owner, record.inputs.owner) { Ok(()) } else { Err(GraphError::WrongOwner) }
    })
}
#[cfg(any(target_os = "macos", target_os = "linux"))]
fn validate(
    owner: &Outcome,
    original: &Arc<Record<'_>>,
    deadline: Instant,
) -> Result<(), GraphError> {
    check_owners(owner, original)?;
    visit(original, |record| super::native::validate(owner, &record.inputs, deadline))
}
