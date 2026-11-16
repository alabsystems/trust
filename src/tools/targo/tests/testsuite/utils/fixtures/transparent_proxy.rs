// Trust: these single-threaded test proxies open no live nonstdio resource
// before delegation. Exec preserves their already bounded incoming table;
// it is not an implicit-inheritance test or a blanket spawn opt-out.
pub fn status(command: &mut std::process::Command) -> std::io::Result<std::process::ExitStatus> {
    #[cfg(unix)]
    {
        use std::os::unix::process::CommandExt;
        Err(command.exec())
    }
    #[cfg(not(unix))]
    {
        command.status()
    }
}
