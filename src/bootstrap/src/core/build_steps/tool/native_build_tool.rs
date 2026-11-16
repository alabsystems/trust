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
#[path = "native_build_tool/tests.rs"]
mod tests;
