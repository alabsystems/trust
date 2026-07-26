//@ run-pass
// Test that the Callbacks interface to the compiler works.

//@ ignore-cross-compile
//@ ignore-remote

#![feature(rustc_private)]

extern crate rustc_driver;
extern crate rustc_interface;

use rustc_interface::interface;

struct TestCalls<'a> {
    count: &'a mut u32,
}

impl rustc_driver::Callbacks for TestCalls<'_> {
    fn config(&mut self, config: &mut interface::Config) {
        assert!(config.opts.unstable_opts.no_trust_verify);
        assert_eq!(config.opts.unstable_opts.trust_ir_lower, Some(false));
        *self.count *= 2;
    }
}

fn main() {
    let mut count = 1;
    let args = vec!["compiler-calls".to_string(), "foo.rs".to_string()];
    rustc_driver::catch_fatal_errors(|| -> interface::Result<()> {
        rustc_driver::run_compiler(&args, &mut TestCalls { count: &mut count });
        Ok(())
    })
    .ok();
    assert_eq!(count, 2);

    let nonce = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    let publication = std::env::temp_dir().join(format!(
        "embedded-must-not-publish-{}-{nonce}",
        std::process::id(),
    ));
    assert!(!publication.exists(), "publication test path collision");
    let mut forbidden_count = 1;
    let forbidden_args = vec![
        "compiler-calls".to_string(),
        "-Ztrust-ir-lower".to_string(),
        format!("-Ztrust-dump=ir:{}", publication.display()),
        "--crate-name=embedded_must_not_publish".to_string(),
        "foo.rs".to_string(),
    ];
    let rejection = rustc_driver::catch_fatal_errors(|| -> interface::Result<()> {
        rustc_driver::run_compiler(
            &forbidden_args,
            &mut TestCalls { count: &mut forbidden_count },
        );
        Ok(())
    });
    assert!(rejection.is_err(), "embedded Trust controls must be rejected");
    assert_eq!(forbidden_count, 1, "Trust controls must fail before callbacks");
    assert!(!publication.exists(), "embedded compiler published official TrustIR");
}
