//! Shared frontend argument transport. Rustc option grammar stays in the driver.

#[derive(Debug, PartialEq, Eq)]
pub(crate) struct FrontendArgs {
    pub verb: &'static str,
    pub args: Vec<String>,
    pub no_deps: bool,
    pub compiler_args: Vec<String>,
}

impl FrontendArgs {
    pub fn parse(args: impl IntoIterator<Item = String>) -> Self {
        let mut input = args.into_iter();
        let mut parsed = Self {
            verb: "check",
            args: Vec::new(),
            no_deps: false,
            compiler_args: Vec::new(),
        };
        for arg in input.by_ref() {
            match arg.as_str() {
                "--fix" => parsed.verb = "fix",
                "--no-deps" => parsed.no_deps = true,
                "--" => break,
                _ => parsed.args.push(arg),
            }
        }
        parsed.no_deps |= parsed.verb == "fix";
        parsed.compiler_args.extend(input);
        parsed
    }
}
