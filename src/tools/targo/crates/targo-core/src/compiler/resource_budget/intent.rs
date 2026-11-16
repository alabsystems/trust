//! Trust: keep generated CPU hints distinct from user caps and memory policy.

use std::ffi::OsStr;

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct MemoryPolicy {
    pub per_worker_bytes: u64,
    pub reserve_bytes: u64,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct ResourceIntent {
    pub initial_jobs: u32,
    pub ceiling: u32,
    pub automatic: bool,
    pub memory: Option<MemoryPolicy>,
}

impl ResourceIntent {
    pub fn fixed(jobs: u32) -> Self {
        Self {
            initial_jobs: jobs,
            ceiling: jobs,
            automatic: false,
            memory: None,
        }
    }

    pub fn resolve<'a>(
        jobs: u32,
        host: u32,
        configured: bool,
        cli_jobs: bool,
        file_cap: Option<u32>,
        env: impl Fn(&str) -> Option<&'a OsStr>,
    ) -> Result<Self, String> {
        let text = |name: &str| -> Result<Option<&str>, String> {
            env(name)
                .map(|value| value.to_str().ok_or_else(|| format!("{name} is not UTF-8")))
                .transpose()
                .map(|value| value.filter(|value| !value.is_empty()))
        };
        let number = |name: &str, zero: bool| -> Result<Option<u64>, String> {
            text(name)?
                .map(|value| {
                    value
                        .parse::<u64>()
                        .ok()
                        .filter(|&n| zero || n > 0)
                        .ok_or_else(|| {
                            format!(
                                "{name} must be a {}integer",
                                if zero { "nonnegative " } else { "positive " }
                            )
                        })
                })
                .transpose()
        };
        let raw = text("CARGO_BUILD_JOBS")?;
        let planned = text("TARGO_PLANNED_JOBS")?;
        number("TARGO_PLANNED_JOBS", false)?;
        let caller = number("TARGO_CALLER_JOBS", false)?
            .map(|n| {
                u32::try_from(n)
                    .map_err(|_| "TARGO_CALLER_JOBS exceeds the CPU count range".to_string())
            })
            .transpose()?;
        let generated = raw.and_then(|value| value.parse::<u32>().ok()) == Some(jobs)
            && (raw == planned
                || (text("BUILD_SLOT_CPU_SOURCE")? == Some("available-slots")
                    && raw == text("BUILD_SLOT_CPU_BUDGET")?));
        let automatic = !cli_jobs && (generated || !configured);
        let ceiling = if automatic {
            caller.unwrap_or(host)
        } else {
            caller.map_or(jobs, |cap| cap.min(jobs))
        }
        .min(if cli_jobs { u32::MAX } else { file_cap.unwrap_or(u32::MAX) })
        .min(host)
        .max(1);
        let memory = match (
            number("TARGO_JOB_MEMORY_BYTES", false)?,
            number("TARGO_MEMORY_RESERVE_BYTES", true)?,
        ) {
            (None, None) => None,
            (Some(per_worker_bytes), Some(reserve_bytes)) => Some(MemoryPolicy {
                per_worker_bytes,
                reserve_bytes,
            }),
            _ => return Err(
                "TARGO_JOB_MEMORY_BYTES and TARGO_MEMORY_RESERVE_BYTES must be supplied together"
                    .into(),
            ),
        };
        Ok(Self {
            initial_jobs: jobs.min(ceiling),
            ceiling,
            automatic,
            memory,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn resolve(jobs: u32, cli: bool, vars: &[(&str, &str)]) -> ResourceIntent {
        ResourceIntent::resolve(jobs, 28, true, cli, None, |key| {
            vars.iter()
                .find(|(name, _)| *name == key)
                .map(|(_, value)| OsStr::new(value))
        })
        .unwrap()
    }

    #[test]
    fn generated_hint_can_grow_but_original_cap_and_cli_still_win() {
        let mut vars = vec![("CARGO_BUILD_JOBS", "7"), ("TARGO_PLANNED_JOBS", "7")];
        let automatic = resolve(7, false, &vars);
        assert!(automatic.automatic);
        assert_eq!((automatic.initial_jobs, automatic.ceiling), (7, 28));
        vars.push(("TARGO_CALLER_JOBS", "12"));
        assert_eq!(resolve(7, false, &vars).ceiling, 12);
        assert_eq!(resolve(3, true, &vars).ceiling, 3);
        vars[0].1 = "2"; // A user's later override must not match stale provenance.
        assert_eq!(resolve(2, false, &vars).ceiling, 2);
    }

    #[test]
    fn existing_gate_provenance_and_separate_memory_estimate_are_retained() {
        let vars = [
            ("CARGO_BUILD_JOBS", "14"),
            ("BUILD_SLOT_CPU_SOURCE", "available-slots"),
            ("BUILD_SLOT_CPU_BUDGET", "14"),
            ("TARGO_JOB_MEMORY_BYTES", "690262893"),
            ("TARGO_MEMORY_RESERVE_BYTES", "8192"),
        ];
        let intent = resolve(14, false, &vars);
        assert_eq!(intent.ceiling, 28);
        assert_eq!(intent.memory.unwrap().per_worker_bytes, 690262893);
        assert_eq!(resolve(4, false, &[]).ceiling, 4);
    }

    #[test]
    fn a_real_file_or_config_override_caps_a_generated_environment_hint() {
        let vars = [("CARGO_BUILD_JOBS", "7"), ("TARGO_PLANNED_JOBS", "7")];
        let intent = ResourceIntent::resolve(7, 28, true, false, Some(4), |key| {
            vars.iter().find(|(name, _)| *name == key).map(|(_, value)| OsStr::new(value))
        }).unwrap();
        assert_eq!((intent.initial_jobs, intent.ceiling), (4, 4));
    }
}
