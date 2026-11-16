//! A gate verb's arguments: `--name value` or `--name=value`, and bare flags.
//! Nothing is positional, so a mistyped option is never read as an operand.

use std::collections::BTreeMap;

/// What the caller wrote, by option name.
#[derive(Debug, Default)]
pub(super) struct Arguments {
    values: BTreeMap<&'static str, String>,
    flags: Vec<&'static str>,
}

impl Arguments {
    pub(super) fn value(&self, name: &str) -> Option<&str> {
        self.values.get(name).map(String::as_str)
    }

    pub(super) fn flag(&self, name: &str) -> bool {
        self.flags.contains(&name)
    }
}

/// Parse `args` against the options that take a value (`valued`) and those
/// that take none (`flags`). `Ok(None)` is a request for help.
pub(super) fn parse(
    args: &[String],
    valued: &[&'static str],
    flags: &[&'static str],
) -> Result<Option<Arguments>, String> {
    let mut parsed = Arguments::default();
    let mut index = 0;
    while let Some(argument) = args.get(index) {
        index += 1;
        let (name, inline) = argument
            .split_once('=')
            .map_or((argument.as_str(), None), |(name, value)| (name, Some(value)));
        if matches!(name, "--help" | "-h") && inline.is_none() {
            return Ok(None);
        }
        if let Some(flag) = flags.iter().copied().find(|flag| *flag == name) {
            if inline.is_some() {
                return Err(format!("{name} takes no value"));
            }
            if parsed.flags.contains(&flag) {
                return Err(format!("{name} is given twice"));
            }
            parsed.flags.push(flag);
            continue;
        }
        let Some(option) = valued.iter().copied().find(|option| *option == name) else {
            return Err(format!("unknown argument {argument:?}"));
        };
        let value = match inline {
            Some(value) => value,
            None => {
                let value = args.get(index).ok_or_else(|| format!("{name} requires a value"))?;
                index += 1;
                value.as_str()
            }
        };
        if value.is_empty() || value.starts_with('-') {
            return Err(format!("{name} requires a value"));
        }
        if parsed.values.insert(option, value.to_owned()).is_some() {
            return Err(format!("{name} is given twice"));
        }
    }
    Ok(Some(parsed))
}
