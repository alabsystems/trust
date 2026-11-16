//! Closed non-producing compiler queries used by the normal metadata resolver.
//! Classification is data validation, never admission or permission to spawn.

use std::io;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ResolverCrateType {
    Bin,
    Rlib,
    Dylib,
    Cdylib,
    Staticlib,
    ProcMacro,
}

impl ResolverCrateType {
    pub fn argument(self) -> &'static [u8] {
        match self {
            Self::Bin => b"bin",
            Self::Rlib => b"rlib",
            Self::Dylib => b"dylib",
            Self::Cdylib => b"cdylib",
            Self::Staticlib => b"staticlib",
            Self::ProcMacro => b"proc-macro",
        }
    }

    fn parse(argument: &[u8]) -> io::Result<Self> {
        [Self::Bin, Self::Rlib, Self::Dylib, Self::Cdylib, Self::Staticlib, Self::ProcMacro]
            .into_iter()
            .find(|kind| kind.argument() == argument)
            .ok_or_else(unsupported)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ResolverQueryKind {
    CompilerVersion,
    Sysroot,
    TargetInfo { unverified: bool },
    DefaultCfg,
    CrateFileNames { unverified: bool, crate_type: ResolverCrateType },
}

fn unsupported() -> io::Error {
    io::Error::new(
        io::ErrorKind::Unsupported,
        "compiler command is outside the closed native resolver query profile",
    )
}

fn equal(arguments: &[Vec<u8>], expected: &[&[u8]]) -> bool {
    arguments.len() == expected.len()
        && arguments.iter().zip(expected).all(|(actual, expected)| actual == expected)
}

/// Accept exact current Targo query forms. No source file, target JSON,
/// producing output, wrapper, custom backend, argfile or extra print mode can
/// enter by appending a benign-looking print flag. Stdin is separately empty.
pub fn classify_resolver_query(arguments: &[Vec<u8>]) -> io::Result<ResolverQueryKind> {
    if arguments.len() > 32 || arguments.iter().any(|arg| arg.len() > 4096 || arg.contains(&0)) {
        return Err(unsupported());
    }
    if equal(arguments, &[b"-vV"]) {
        return Ok(ResolverQueryKind::CompilerVersion);
    }
    if equal(arguments, &[b"--print=sysroot"]) {
        return Ok(ResolverQueryKind::Sysroot);
    }
    if equal(arguments, &[b"-", b"--crate-name", b"___", b"--print=cfg"]) {
        return Ok(ResolverQueryKind::DefaultCfg);
    }
    let prefix: &[&[u8]] = &[b"-", b"--crate-name", b"___", b"--print=file-names"];
    if arguments.len() < prefix.len() || !equal(&arguments[..prefix.len()], prefix) {
        return Err(unsupported());
    }
    let mut remaining = &arguments[prefix.len()..];
    let unverified = remaining.first().is_some_and(|arg| arg == b"-Ztrust-verify=off");
    if unverified {
        remaining = &remaining[1..];
    }
    if let [flag, crate_type] = remaining
        && flag == b"--crate-type"
    {
        return Ok(ResolverQueryKind::CrateFileNames {
            unverified,
            crate_type: ResolverCrateType::parse(crate_type)?,
        });
    }
    let expected: &[&[u8]] = &[
        b"--crate-type",
        b"bin",
        b"--crate-type",
        b"rlib",
        b"--crate-type",
        b"dylib",
        b"--crate-type",
        b"cdylib",
        b"--crate-type",
        b"staticlib",
        b"--crate-type",
        b"proc-macro",
        b"--print=sysroot",
        b"--print=split-debuginfo",
        b"--print=crate-name",
        b"--print=cfg",
        b"-Wwarnings",
    ];
    if equal(remaining, expected) {
        Ok(ResolverQueryKind::TargetInfo { unverified })
    } else {
        Err(unsupported())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn argv(arguments: &[&[u8]]) -> Vec<Vec<u8>> {
        arguments.iter().map(|arg| arg.to_vec()).collect()
    }
    pub(super) fn target_info(unverified: bool) -> Vec<Vec<u8>> {
        let mut arguments = argv(&[b"-", b"--crate-name", b"___", b"--print=file-names"]);
        if unverified {
            arguments.push(b"-Ztrust-verify=off".to_vec());
        }
        arguments.extend(argv(&[
            b"--crate-type",
            b"bin",
            b"--crate-type",
            b"rlib",
            b"--crate-type",
            b"dylib",
            b"--crate-type",
            b"cdylib",
            b"--crate-type",
            b"staticlib",
            b"--crate-type",
            b"proc-macro",
            b"--print=sysroot",
            b"--print=split-debuginfo",
            b"--print=crate-name",
            b"--print=cfg",
            b"-Wwarnings",
        ]));
        arguments
    }

    #[test]
    fn resolver_profile_accepts_only_normal_nonproducing_query_families() {
        assert_eq!(
            classify_resolver_query(&argv(&[b"-vV"])).unwrap(),
            ResolverQueryKind::CompilerVersion
        );
        assert_eq!(
            classify_resolver_query(&argv(&[b"--print=sysroot"])).unwrap(),
            ResolverQueryKind::Sysroot
        );
        assert_eq!(
            classify_resolver_query(&argv(&[b"-", b"--crate-name", b"___", b"--print=cfg"]))
                .unwrap(),
            ResolverQueryKind::DefaultCfg
        );
        for unverified in [false, true] {
            assert_eq!(
                classify_resolver_query(&target_info(unverified)).unwrap(),
                ResolverQueryKind::TargetInfo { unverified }
            );
            let mut single = argv(&[b"-", b"--crate-name", b"___", b"--print=file-names"]);
            if unverified {
                single.push(b"-Ztrust-verify=off".to_vec());
            }
            single.extend(argv(&[b"--crate-type", b"rlib"]));
            assert_eq!(
                classify_resolver_query(&single).unwrap(),
                ResolverQueryKind::CrateFileNames {
                    unverified,
                    crate_type: ResolverCrateType::Rlib
                }
            );
        }
    }

    #[test]
    fn resolver_profile_refuses_producing_custom_and_mixed_print_commands() {
        for extra in [
            b"--emit=link".as_slice(),
            b"input.rs",
            b"@arguments",
            b"--print=link-args",
            b"-Zcodegen-backend=/foreign/plugin",
            b"--target=custom.json",
            b"-Cllvm-args=-load=/foreign/plugin",
            b"--out-dir=/outside",
            b"-Ztrust-verify=on",
        ] {
            let mut arguments = target_info(true);
            arguments.push(extra.to_vec());
            assert_eq!(
                classify_resolver_query(&arguments).unwrap_err().kind(),
                io::ErrorKind::Unsupported
            );
        }
        for arguments in [
            argv(&[b"wrapper", b"-vV"]),
            argv(&[b"--version"]),
            argv(&[b"--print=target-list"]),
            argv(&[b"--print=target-spec-json", b"-Zunstable-options"]),
            argv(&[b"-", b"--crate-name", b"___", b"--print=cfg", b"--target", b"custom.json"]),
        ] {
            assert!(classify_resolver_query(&arguments).is_err());
        }
    }
}
