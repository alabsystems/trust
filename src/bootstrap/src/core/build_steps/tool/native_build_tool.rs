//! Explicit engineering frontend production; never an assembled SDK step.
use super::*;

pub(super) fn recipe(compiler: Compiler, target: TargetSelection) -> ToolBuild {
    ToolBuild {
        artifact_kind: ToolArtifactKind::NativeEngineeringBinary,
        ..targo_tool_build_recipe(compiler, compiler, target)
    }
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct TargoNativeBuildTool {
    target: TargetSelection,
}

impl CommandLineStep for TargoNativeBuildTool {
    type Output = ToolBuildResult;
    const IS_HOST: bool = true;

    fn should_run(run: ShouldRun<'_>) -> ShouldRun<'_> {
        run.alias("targo-native-build-tool")
    }
    fn is_default_step(_builder: &Builder<'_>) -> bool {
        false
    }
    fn make_run(run: RunConfig<'_>) {
        run.builder.ensure(Self { target: run.target });
    }
    fn run(self, builder: &Builder<'_>) -> Self::Output {
        assert_eq!(self.target, builder.host_target, "native engineering frontend is host-only");
        assert!(
            cfg!(all(target_os = "macos", target_arch = "aarch64")),
            "native engineering pairing requires macOS arm64"
        );
        builder.version_info().sha().expect("native engineering frontend requires source identity");
        builder.sess.require_submodule("src/tools/targo", None);
        // No Compiler/Assemble or std step: this consumes the explicitly
        // configured initial compiler and its original snapshot libraries.
        let compiler = Compiler::new(0, builder.host_target);
        builder.ensure(recipe(compiler, self.target))
    }
}

#[cfg(all(test, target_os = "macos", target_arch = "aarch64"))]
mod tests {
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
}
