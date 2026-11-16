// The elastic default substitutes direct paired LLD for the target's CC
// driver. Preserve that default driver's explicit linker-forwarding semantics
// without treating arbitrary CC options as linker options. Argument order is
// retained; empty comma components are omitted like the native CC driver.
pub(super) fn direct_link_args(args: &[String]) -> Result<Vec<String>, &'static str> {
    let mut direct = Vec::new();
    let mut iter = args.iter();
    while let Some(arg) = iter.next() {
        if let Some(forwarded) = arg.strip_prefix("-Wl,") {
            direct.extend(forwarded.split(',').filter(|arg| !arg.is_empty()).map(str::to_owned));
        } else if arg == "-Xlinker" {
            direct.push(
                iter.next().ok_or("missing argument after explicit -Xlinker forwarding")?.clone(),
            );
        } else {
            direct.push(arg.clone());
        }
    }
    Ok(direct)
}

// Trust: preserve explicit linker thread ceilings when adapting the live budget.
pub(super) fn thread_limit(args: &[String], default: usize) -> Result<usize, &'static str> {
    let args: Vec<_> = args
        .iter()
        .flat_map(|arg| {
            arg.strip_prefix("-Wl,")
                .map_or_else(|| vec![arg.as_str()], |args| args.split(',').collect())
        })
        .collect();
    let mut limit = default;
    let mut iter = args.iter().copied();
    while let Some(arg) = iter.next() {
        if arg.starts_with('@')
            && !["@rpath/", "@loader_path/", "@executable_path/"]
                .iter()
                .any(|prefix| arg.starts_with(prefix))
        {
            return Err("native elastic linking cannot inspect an opaque linker response file");
        }
        let value = if matches!(arg, "--threads" | "--thinlto-jobs") {
            Some(iter.next().ok_or("missing explicit linker thread count")?)
        } else {
            arg.strip_prefix("--threads=")
                .or_else(|| arg.strip_prefix("--thinlto-jobs="))
                .or_else(|| arg.strip_prefix("/threads:"))
        };
        if let Some(value) = value {
            let count = value.parse::<usize>().map_err(|_| "invalid linker thread count")?;
            if count == 0 {
                return Err("zero linker thread count does not declare a bounded width");
            }
            limit = limit.min(count);
        }
        if let Some(value) = arg.strip_prefix("--read-workers=")
            && value != "0"
        {
            return Err("independent linker read workers need a separately declared CPU budget");
        }
    }
    Ok(limit)
}

// Trust: out-of-line unit tests, as tidy's `unit_tests` check requires.
#[cfg(test)]
#[path = "link_resource/tests.rs"]
mod tests;
