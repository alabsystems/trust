use super::*;

#[test]
fn native_engineering_frontend_does_not_assemble_a_compiler_or_std() {
    for stage in [1, 2] {
        let context = crate::utils::tests::TestCtx::new();
        let config = context
            .config("build")
            .stage(stage)
            .args(&["--set", "build.extended=true", "--set", "rust.omit-git-hash=false"])
            .path("targo-native-build-tool")
            .create_config();
        let session = crate::core::session::Session::new(config);
        let builder = Builder::new(&session);
        builder.execute_cli();
        let cache = builder.step_cache();
        assert!(cache.contains::<TargoNativeBuildTool>());
        assert!(!cache.contains::<compile::Rustc>());
        assert!(!cache.contains::<compile::Std>());
        assert!(!cache.contains::<Cargo>());
        assert!(
            cache
                .inspect_all_steps_of_type::<compile::Assemble, _>(|step, _| step
                    .target_compiler
                    .stage)
                .iter()
                .all(|stage| *stage == 0)
        );
        assert!(
            cache
                .inspect_all_steps_of_type::<ToolBuild, _>(|step, _| (
                    step.build_compiler.stage,
                    step.output_compiler.stage
                ))
                .iter()
                .all(|pair| *pair == (0, 0))
        );
    }
}
