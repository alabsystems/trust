// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright 2026 Andrew Yates

//! Native session registration preserves the admitted child's PID, descriptors
//! and process group. Discovery chooses reporting only; it grants no resources.

use std::collections::BTreeMap;
use std::ffi::{OsStr, OsString};
use std::os::unix::ffi::OsStringExt as _;
use std::os::unix::fs::PermissionsExt as _;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::{Duration, Instant};

use anyhow::{Context as _, Result, ensure};
use cargo_util::{ProcessBuilder, StreamingOutputLimits};

const STATUS_LIMIT: usize = 8192;

pub(super) fn command(
    context: &crate::GlobalContext,
    inner: Command,
    deadline: Option<Instant>,
) -> Result<Command> {
    if ![
        "ATERM_CHILD",
        "ATERM_PARENT_SESSION_ID",
        "ATERM_SESSION_ID",
        "ATERM_EDGE_TOKENS",
    ]
    .iter()
    .any(|key| {
        context
            .get_env_os(key)
            .is_some_and(|value| !value.is_empty())
    }) {
        return Ok(inner);
    }
    let path = context
        .get_env_os("PATH")
        .context("native session reporting needs PATH")?;
    let cli = std::env::split_paths(path)
        .map(|directory| {
            if directory.is_absolute() {
                directory
            } else {
                context.cwd().join(directory)
            }
        })
        .map(|directory| directory.join("aterm"))
        .find(|candidate| {
            candidate
                .metadata()
                .is_ok_and(|meta| meta.is_file() && meta.permissions().mode() & 0o111 != 0)
        })
        .context(
            "native fixed admission cannot resolve aterm session reporting; no target started",
        )?;
    let mut probe = ProcessBuilder::new(&cli);
    probe
        .args(&["ctl", "@self", "resources", "capabilities"])
        .cwd(context.cwd());
    let timeout = deadline.map_or(Duration::from_secs(5), |until| {
        until
            .saturating_duration_since(Instant::now())
            .min(Duration::from_secs(5))
    });
    ensure!(
        !timeout.is_zero(),
        "native fixed admission timed out before session discovery; no target started"
    );
    let output = probe.exec_with_capture(
        StreamingOutputLimits::new(STATUS_LIMIT, STATUS_LIMIT)
            .with_timeout(timeout)
            .with_child_exit_cleanup(),
    );
    ensure!(
        output.succeeded(),
        "aterm session discovery did not finish with complete bounded output and retired scope; no target started"
    );
    let runner = runner(&output.stdout)?;
    let mut outer = Command::new(runner);
    outer.args([
        OsStr::new("resource-run"),
        OsStr::new("--session"),
        OsStr::new("@self"),
        OsStr::new("--job"),
    ]);
    outer.arg(label(context.cwd(), inner.get_program()));
    outer
        .arg("--")
        .arg(inner.get_program())
        .args(inner.get_args());
    // Called BEFORE original GNU/claim configuration: those real inherited
    // descriptions are applied to this final command, never replaced/copied
    // from a partially configured std::process::Command.
    ensure!(
        inner.get_envs().next().is_none(),
        "attribution must precede original command environment configuration"
    );
    Ok(outer)
}

fn runner(bytes: &[u8]) -> Result<PathBuf> {
    ensure!(
        bytes.len() <= STATUS_LIMIT,
        "aterm resource capability record exceeds bound"
    );
    let text =
        std::str::from_utf8(bytes).context("aterm resource capability record is not UTF-8")?;
    let mut words = text.split_whitespace();
    ensure!(
        words.next() == Some("OK") && words.next() == Some("resources"),
        "aterm resource capability record has an unsupported prefix"
    );
    let mut fields = BTreeMap::new();
    for word in words {
        let (name, value) = word
            .split_once('=')
            .context("malformed aterm resource capability field")?;
        ensure!(
            !name.is_empty() && fields.insert(name, value).is_none(),
            "duplicate or empty aterm resource capability field"
        );
    }
    ensure!(
        fields.get("version") == Some(&"1")
            && fields.get("available") == Some(&"1")
            && fields.get("self_register") == Some(&"peer-pid-start")
            && fields.get("group_signals") == Some(&"exec-inherit"),
        "aterm does not offer original-PID session registration/exec; no target started"
    );
    let encoded = fields
        .get("runner")
        .context("aterm resource capability has no runner")?;
    let mut decoded = Vec::with_capacity(encoded.len());
    let mut input = encoded.as_bytes().iter().copied();
    while let Some(byte) = input.next() {
        decoded.push(if byte == b'%' {
            let high = input
                .next()
                .and_then(hex)
                .context("malformed runner escape")?;
            let low = input
                .next()
                .and_then(hex)
                .context("malformed runner escape")?;
            high * 16 + low
        } else {
            byte
        });
    }
    ensure!(!decoded.contains(&0), "aterm runner contains NUL");
    let path = PathBuf::from(OsString::from_vec(decoded));
    ensure!(path.is_absolute(), "aterm runner must be absolute");
    let meta = path.metadata().context("aterm runner is unavailable")?;
    ensure!(
        meta.is_file() && meta.permissions().mode() & 0o111 != 0,
        "aterm runner is not an executable file"
    );
    Ok(path)
}

fn hex(byte: u8) -> Option<u8> {
    match byte {
        b'0'..=b'9' => Some(byte - b'0'),
        b'a'..=b'f' => Some(byte - b'a' + 10),
        b'A'..=b'F' => Some(byte - b'A' + 10),
        _ => None,
    }
}

fn label(cwd: &Path, program: &OsStr) -> String {
    let name = cwd.file_name().unwrap_or_else(|| OsStr::new("/"));
    let program = Path::new(program).file_name().unwrap_or(program);
    let text = format!("{}: {}", name.to_string_lossy(), program.to_string_lossy());
    let mut result = String::new();
    for character in text.chars() {
        let character = if character.is_control() {
            '?'
        } else {
            character
        };
        if result.len() + character.len_utf8() > 200 {
            break;
        }
        result.push(character);
    }
    result
}

#[cfg(test)]
#[path = "attribution/tests.rs"]

mod tests;
