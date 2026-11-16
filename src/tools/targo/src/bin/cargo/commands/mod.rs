use crate::command_prelude::*;

pub fn builtin() -> Vec<Command> {
    let commands = vec![
        add::cli(),
        bench::cli(),
        build::cli(),
        check::cli(),
        clean::cli(),
        config::cli(),
        doc::cli(),
        fetch::cli(),
        fix::cli(),
        generate_lockfile::cli(),
        git_checkout::cli(),
        help::cli(),
        info::cli(),
        init::cli(),
        install::cli(),
        locate_project::cli(),
        login::cli(),
        logout::cli(),
        metadata::cli(),
        new::cli(),
        owner::cli(),
        package::cli(),
        pkgid::cli(),
        publish::cli(),
        read_manifest::cli(),
        resource_epoch::cli(), // Trust: private host-owned transport qualification.
        remove::cli(),
        report::cli(),
        run::cli(),
        rustc::cli(),
        rustdoc::cli(),
        search::cli(),
        source_check::cli(),
        test::cli(),
        tree::cli(),
        uninstall::cli(),
        update::cli(),
        vendor::cli(),
        verify_project::cli(),
        version::cli(),
        yank::cli(),
    ];
    // Trust: native admission belongs only to the branded Targo surface.
    #[cfg(any(target_os = "linux", target_os = "macos"))]
    let commands = {
        let mut commands = commands;
        if targo::is_targo_invocation() {
            let resource = crate::resource_fixed::help_command();
            #[cfg(all(target_os = "macos", target_arch = "aarch64"))]
            let resource = resource
                .subcommand(crate::bootstrap_runtime::help_command())
                .subcommand(crate::bootstrap_runtime::scope_help_command());
            commands.push(resource);
        }
        commands
    };
    commands
}

pub type Exec = fn(&mut GlobalContext, &ArgMatches) -> CliResult;

pub fn builtin_exec(cmd: &str) -> Option<Exec> {
    let f = match cmd {
        "add" => add::exec,
        "bench" => bench::exec,
        "build" => build::exec,
        "check" => check::exec,
        "clean" => clean::exec,
        "config" => config::exec,
        "doc" => doc::exec,
        "fetch" => fetch::exec,
        "fix" => fix::exec,
        "generate-lockfile" => generate_lockfile::exec,
        "git-checkout" => git_checkout::exec,
        "help" => help::exec,
        "info" => info::exec,
        "init" => init::exec,
        "install" => install::exec,
        "locate-project" => locate_project::exec,
        "login" => login::exec,
        "logout" => logout::exec,
        "metadata" => metadata::exec,
        "new" => new::exec,
        "owner" => owner::exec,
        "package" => package::exec,
        "pkgid" => pkgid::exec,
        "publish" => publish::exec,
        "read-manifest" => read_manifest::exec,
        // Trust: aliases cannot create a new standalone resource root.
        #[cfg(any(target_os = "linux", target_os = "macos"))]
        "resource" if targo::is_targo_invocation() => crate::resource_fixed::reject_alias_dispatch,
        "__resource-epoch" => resource_epoch::exec, // Trust: private native helper.
        "remove" => remove::exec,
        "report" => report::exec,
        "run" => run::exec,
        "rustc" => rustc::exec,
        "rustdoc" => rustdoc::exec,
        "search" => search::exec,
        "source-check" => source_check::exec,
        "test" => test::exec,
        "tree" => tree::exec,
        "uninstall" => uninstall::exec,
        "update" => update::exec,
        "vendor" => vendor::exec,
        "verify-project" => verify_project::exec,
        "version" => version::exec,
        "yank" => yank::exec,
        _ => return None,
    };
    Some(f)
}

pub mod add;
pub mod bench;
pub mod build;
pub mod check;
pub mod clean;
pub mod config;
pub mod doc;
pub mod fetch;
pub mod fix;
pub mod generate_lockfile;
pub mod git_checkout;
pub mod help;
pub mod info;
pub mod init;
pub mod install;
pub mod locate_project;
pub mod login;
pub mod logout;
pub mod metadata;
pub mod new;
pub mod owner;
pub mod package;
pub mod pkgid;
pub mod publish;
pub mod read_manifest;
pub mod remove;
pub mod report;
pub mod resource_epoch; // Trust: host policy remains outside this transport helper.
pub mod run;
pub mod rustc;
pub mod rustdoc;
pub mod search;
pub mod source_check;
pub mod test;
pub mod tree;
pub mod uninstall;
pub mod update;
pub mod vendor;
pub mod verify_project;
pub mod version;
pub mod yank;
