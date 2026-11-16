//! One case with one compiler: the compiles its row asks for, and the verdict
//! they make.
//!
//! A case that has only a pin is one compile, and its verdict is that
//! compile's exit status: `verifies` (0), `refuses` (1), `crash:<status>`
//! (anything else), or not judged (no exit inside the bound). A row of
//! `tests/corpora.toml` can ask three more things of a case, each as the
//! corpus script it came from asks it:
//!
//! * **A text its output must hold** (`log_contains`; a ladder file's
//!   `//@ trust-ladder-row:`). Looked for only when the compile ended as
//!   pinned, as a fixed string on one line of the compile's output. Without it
//!   the verdict is `verifies-otherwise` or `refuses-otherwise`: the pinned
//!   exit status, and not the pinned row.
//! * **A `conditional` pin.** The case is `conditional` when its compile
//!   exits 0, its output holds its disclosure (its own text, or its corpus's),
//!   and a second compile, with the corpus's certify arguments after the
//!   case's and without the case's `env`, exits non-zero with the certify
//!   refusal in its output. With exit 0 and any of the rest missing it is
//!   `verifies`, which a `conditional` pin ranks as a possible false proof,
//!   and its cause says which part is missing. The certify compile is not run
//!   when the first half already failed: it could not change the verdict.
//! * **A dependency.** The crate is built once for a side, before the first
//!   case that uses it, into a directory of its own, and each such case is
//!   compiled with `--extern <name>=<dir>/lib<name>.rlib -L <dir>` after its
//!   own arguments. A dependency is not a case and has no record. When it
//!   refuses, or exits 0 and leaves no rlib, each case built against it is
//!   `blocked` whatever its pin: a case that was to refuse has not refused for
//!   its own reason. When it crashes or runs past the bound, so does each case
//!   built against it.
//!
//! Every compile is bounded by `--case-seconds` on its own.

use std::collections::BTreeMap;
use std::fs;
use std::path::{Path, PathBuf};
use std::time::Duration;

use super::run::{self, CaseExit, CaseRunner, CaseSpec};
use super::table::{Case, Corpus};
use super::{Pin, Verdict};

/// What a refusal with no `error` line is said to have printed.
const NO_ERROR_LINE: &str = "no `error` line in its output";

/// Where one compiler compiles one corpus.
pub(super) struct Ground<'a> {
    pub(super) compiler: &'a Path,
    pub(super) corpus: &'a Corpus,
    /// The side's logs for the corpus.
    pub(super) out: PathBuf,
    /// Scratch for what the compiler writes: the corpus's own compiles share
    /// it, and a dependency or a certify compile has a directory inside it.
    pub(super) work: PathBuf,
    /// How long one compile may take.
    pub(super) bound: Duration,
    /// Whether `out` outlives the run (`--keep`).
    pub(super) kept: bool,
}

/// A case's verdict, and the cause its record carries.
pub(super) type Judged = (Verdict, String);

/// What a side made of a dependency.
#[derive(Clone)]
enum Built {
    Ready {
        rlib: String,
        dir: String,
    },
    /// The verdict of every case built against it.
    Not(Judged),
    /// The runner made no record of it, so none of its cases is recorded.
    Unrecorded,
}

/// Judges a corpus's cases for one side, building each dependency once.
pub(super) struct Judge<'a> {
    ground: Ground<'a>,
    built: BTreeMap<String, Built>,
}

impl<'a> Judge<'a> {
    pub(super) fn new(ground: Ground<'a>) -> Self {
        Self { ground, built: BTreeMap::new() }
    }

    /// The verdict of `case`; `None` when the runner made no record of it. An
    /// error is a compile that could not be started or read, named by its
    /// corpus and case.
    pub(super) fn case(
        &mut self,
        case: &Case,
        runner: &mut dyn CaseRunner,
    ) -> Result<Option<Judged>, String> {
        let mut args = case.args.clone();
        if let Some(used) = &case.dependency {
            match self.dependency(&used.name, runner)? {
                Built::Unrecorded => return Ok(None),
                Built::Not(judged) => return Ok(Some(judged)),
                Built::Ready { rlib, dir } => {
                    args.extend(["--extern".to_owned(), format!("{}={rlib}", used.name)]);
                    args.extend(["-L".to_owned(), dir]);
                }
            }
            args.extend(used.then_args.iter().cloned());
        }
        let work = self.ground.work.clone();
        let compile =
            Compile { id: &case.id, source: &case.source, args: args.clone(), env: &case.env };
        let (exit, log) = self.compile(runner, compile, &work, "log")?;
        let Some(exit) = exit else {
            return Ok(None);
        };
        let verdict = self.exit_verdict(exit, &case.id)?;
        let pinned_exit = matches!(
            (verdict, case.pin),
            (Verdict::Verifies, Some(Pin::Verifies)) | (Verdict::Refuses, Some(Pin::Refuses))
        );
        Ok(Some(match (verdict, case.pin) {
            (Verdict::NotJudged, _) => (verdict, self.unjudged(&log)),
            (Verdict::Verifies, Some(Pin::Conditional)) => {
                return self.conditional(case, args, &log, runner);
            }
            _ => match &case.log_contains {
                Some(needle) if pinned_exit && !self.holds(&log, needle, &case.id)? => {
                    let otherwise = match verdict {
                        Verdict::Verifies => Verdict::VerifiesOtherwise,
                        _ => Verdict::RefusesOtherwise,
                    };
                    (otherwise, format!("its output has no {needle:?}"))
                }
                _ if verdict == Verdict::Verifies => (verdict, String::new()),
                _ => (verdict, run::first_error_line(&log)),
            },
        }))
    }

    /// The second half of a case pinned `conditional`, whose compile (with
    /// `args`, its output in `log`) exited 0.
    fn conditional(
        &self,
        case: &Case,
        mut args: Vec<String>,
        log: &Path,
        runner: &mut dyn CaseRunner,
    ) -> Result<Option<Judged>, String> {
        let (Some(disclosure), Some(certify)) = (&case.log_contains, &case.certify) else {
            return Err(self.named(&case.id, "it is pinned conditional with no certify compile"));
        };
        if !self.holds(log, disclosure, &case.id)? {
            let cause = format!("exit 0, and its output has no {disclosure:?}");
            return Ok(Some((Verdict::Verifies, cause)));
        }
        args.extend(certify.args.iter().cloned());
        let work = self.ground.work.join(format!("{}.certify", case.id));
        let compile = Compile { id: &case.id, source: &case.source, args, env: &[] };
        let (exit, certify_log) = self.compile(runner, compile, &work, "certify.log")?;
        let ended = match exit {
            None => return Ok(None),
            Some(CaseExit::Failed(error)) => return Err(self.named(&case.id, &error)),
            Some(CaseExit::PastBound) => {
                return Ok(Some((Verdict::NotJudged, self.unjudged(&certify_log))));
            }
            Some(CaseExit::Exited(0)) => {
                return Ok(Some((Verdict::Verifies, "its certify compile accepts it".into())));
            }
            Some(CaseExit::Exited(code)) => format!("exited {code}"),
            Some(CaseExit::Signalled(signal)) => format!("was ended by signal {signal}"),
        };
        if self.holds(&certify_log, &certify.refusal, &case.id)? {
            return Ok(Some((Verdict::Conditional, String::new())));
        }
        let mut cause = format!("its certify compile {ended} without {:?}", certify.refusal);
        let error = run::first_error_line(&certify_log);
        if !error.is_empty() {
            cause.push_str(": ");
            cause.push_str(&error);
        }
        Ok(Some((Verdict::Verifies, cause)))
    }

    /// The dependency `name`, built at most once for this side.
    fn dependency(&mut self, name: &str, runner: &mut dyn CaseRunner) -> Result<Built, String> {
        if let Some(built) = self.built.get(name) {
            return Ok(built.clone());
        }
        let corpus = self.ground.corpus;
        let Some(dependency) = corpus.dependencies.iter().find(|built| built.name == name) else {
            return Err(format!("{}: a case is built against {name}, which it has not", corpus.id));
        };
        let id = dependency.id.as_str();
        let dir = self.ground.work.join(format!("{id}.dependency"));
        let compile =
            Compile { id, source: &dependency.source, args: dependency.args.clone(), env: &[] };
        let (exit, log) = self.compile(runner, compile, &dir, "dependency.log")?;
        let error_line = |log: &Path| match run::first_error_line(log) {
            line if line.is_empty() => NO_ERROR_LINE.to_owned(),
            line => line,
        };
        let built = match exit {
            None => Built::Unrecorded,
            Some(exit) => match self.exit_verdict(exit, id)? {
                Verdict::Verifies => {
                    let rlib = dir.join(format!("lib{name}.rlib"));
                    match (rlib.to_str(), dir.to_str()) {
                        (Some(rlib), Some(dir)) if Path::new(rlib).is_file() => {
                            Built::Ready { rlib: rlib.to_owned(), dir: dir.to_owned() }
                        }
                        (Some(_), Some(_)) => Built::Not((
                            Verdict::Blocked,
                            format!("its dependency {id} exited 0 and left no lib{name}.rlib"),
                        )),
                        _ => {
                            return Err(self.named(id, "its scratch directory is not UTF-8"));
                        }
                    }
                }
                Verdict::Refuses => Built::Not((
                    Verdict::Blocked,
                    format!("its dependency {id} did not build: {}", error_line(&log)),
                )),
                Verdict::NotJudged => Built::Not((
                    Verdict::NotJudged,
                    format!("its dependency {id}: {}", self.unjudged(&log)),
                )),
                crash => Built::Not((crash, format!("its dependency {id}: {}", error_line(&log)))),
            },
        };
        self.built.insert(name.to_owned(), built.clone());
        Ok(built)
    }

    /// Run one compile in `work`, its output in `<out>/<id>.<log>`.
    fn compile(
        &self,
        runner: &mut dyn CaseRunner,
        compile: Compile<'_>,
        work: &Path,
        log: &str,
    ) -> Result<(Option<CaseExit>, PathBuf), String> {
        let log = self.ground.out.join(format!("{}.{log}", compile.id));
        for directory in [log.parent(), Some(work)].into_iter().flatten() {
            fs::create_dir_all(directory)
                .map_err(|error| format!("cannot create {}: {error}", directory.display()))?;
        }
        let spec = CaseSpec {
            compiler: self.ground.compiler.to_path_buf(),
            corpus: self.ground.corpus.id.clone(),
            case: compile.id.to_owned(),
            args: compile.args,
            env: compile.env.to_vec(),
            source: compile.source.to_path_buf(),
            work: work.to_path_buf(),
            log: log.clone(),
            bound: self.ground.bound,
        };
        Ok((runner.run(&spec), log))
    }

    /// An exit as the verdict of the compile alone.
    fn exit_verdict(&self, exit: CaseExit, id: &str) -> Result<Verdict, String> {
        match exit {
            CaseExit::Exited(code) => Ok(Verdict::of_exit(code)),
            CaseExit::Signalled(signal) => Ok(Verdict::Crash(128 + signal)),
            CaseExit::PastBound => Ok(Verdict::NotJudged),
            CaseExit::Failed(error) => Err(self.named(id, &error)),
        }
    }

    fn holds(&self, log: &Path, needle: &str, id: &str) -> Result<bool, String> {
        run::log_contains(log, needle).map_err(|error| {
            self.named(id, &format!("cannot read its output {}: {error}", log.display()))
        })
    }

    fn named(&self, id: &str, error: &str) -> String {
        format!("{}/{id}: {error}", self.ground.corpus.id)
    }

    /// Why a compile past its bound has no verdict. Without `--keep` the log
    /// goes with the run's scratch, so the cause names how to hold it, not a
    /// path that is gone.
    fn unjudged(&self, log: &Path) -> String {
        let seconds = self.ground.bound.as_secs();
        if self.ground.kept {
            format!("no verdict within {seconds}s (log: {})", log.display())
        } else {
            format!("no verdict within {seconds}s (--keep DIR holds its log)")
        }
    }
}

/// One compile of a case: what a [`CaseSpec`] takes from its row.
struct Compile<'a> {
    id: &'a str,
    source: &'a Path,
    args: Vec<String>,
    env: &'a [(String, String)],
}
