((rustic-mode
  .((eglot-workspace-configuration
     . (:rust-analyzer
        ( :check ( :invocationStrategy "once"
                                       :overrideCommand ["python3"
                                                         "x.py"
                                                         "check"
                                                         "--build-dir"
                                                         "build-rust-analyzer"
                                                         "--json-output"])
                 :linkedProjects ["Cargo.toml"
                                  "library/Cargo.toml"
                                  "src/bootstrap/Cargo.toml"
                                  "src/tools/rust-analyzer/Cargo.toml"]
                 :rustfmt ( :overrideCommand ["build-rust-analyzer/host/rustfmt/bin/rustfmt"
                                              "--edition=2024"])
                 :procMacro ( :server "build-rust-analyzer/host/stage0/libexec/trust-analyzer-proc-macro-srv"
                                      :enable t)
                 :cargo ( :buildScripts ( :enable t
                                                  :invocationLocation "root"
                                                  :invocationStrategy "once"
                                                  :overrideCommand ["python3"
                                                                    "x.py"
                                                                    "check"
                                                                    "--build-dir"
                                                                    "build-rust-analyzer"
                                                                    "--json-output"
                                                                    "--compile-time-deps"])
                                        :sysrootSrc "./library"
                                        :extraEnv (:RUSTC_BOOTSTRAP "1"))
                 :rustc ( :source "./Cargo.toml" )))))))
