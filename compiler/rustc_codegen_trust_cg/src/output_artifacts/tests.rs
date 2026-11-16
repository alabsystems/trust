use std::path::PathBuf;
use std::sync::atomic::{AtomicUsize, Ordering};

use rustc_codegen_ssa::CompiledModule;
use rustc_session::config::OutFileName;

use super::*;

static NEXT_DIRECTORY: AtomicUsize = AtomicUsize::new(0);

struct Scratch(PathBuf);

impl Scratch {
    fn new() -> Self {
        let path = std::env::temp_dir().join(format!(
            "trust-cg-output-publication-{}-{}",
            std::process::id(),
            NEXT_DIRECTORY.fetch_add(1, Ordering::Relaxed)
        ));
        // Create-only: never adopt another invocation's files as this test's.
        fs::create_dir(&path).unwrap();
        Self(path)
    }

    fn outputs(&self, requested: &[OutputType]) -> OutputFilenames {
        OutputFilenames::new(
            self.0.clone(),
            "crate_name".into(),
            "source-name".into(),
            None,
            None,
            None,
            None,
            String::new(),
            OutputTypes::new(&requested.iter().map(|kind| (*kind, None)).collect::<Vec<_>>()),
        )
    }
}

impl Drop for Scratch {
    fn drop(&mut self) {
        // The directory was created exclusively by this exact test above.
        fs::remove_dir_all(&self.0).unwrap();
    }
}

fn regular(outputs: &OutputFilenames, name: &str) -> CompiledModule {
    CompiledModule {
        name: name.into(),
        kind: ModuleKind::Regular,
        object: Some(outputs.temp_path_for_cgu(OutputType::Object, name)),
        global_asm_object: None,
        dwarf_object: None,
        bytecode: None,
        assembly: None,
        llvm_ir: None,
    }
}

fn compiled(module: CompiledModule) -> CompiledModules {
    CompiledModules { modules: vec![module], allocator_module: None }
}

#[test]
fn exact_nonempty_object_inventory_is_accepted_without_mutating_files() {
    let scratch = Scratch::new();
    let outputs = scratch.outputs(&[OutputType::Object]);
    let module = regular(&outputs, "crate_name.codegen_unit.0");
    let temporary = module.object.as_ref().unwrap().clone();
    // This is only a filesystem-inventory test, not emitted-code evidence.
    fs::write(&temporary, b"already emitted object bytes").unwrap();
    let final_path = outputs.path(OutputType::Object);
    fs::write(final_path.as_path(), b"previous compilation").unwrap();
    assert_eq!(validate_requested_object(&compiled(module), &outputs), Ok(()));
    assert_eq!(fs::read(&temporary).unwrap(), b"already emitted object bytes");
    assert_eq!(fs::read(final_path.as_path()).unwrap(), b"previous compilation");
}

#[test]
fn missing_cgu_refuses_object_but_preserves_empty_archive_and_analysis_lanes() {
    let scratch = Scratch::new();
    let empty = CompiledModules { modules: vec![], allocator_module: None };
    let outputs = scratch.outputs(&[OutputType::Object]);
    assert!(validate_requested_object(&empty, &outputs).unwrap_err().contains("found 0"));
    for requested in [
        vec![OutputType::Exe],
        vec![OutputType::Mir, OutputType::Metadata, OutputType::DepInfo],
        vec![],
    ] {
        assert_eq!(validate_requested_object(&empty, &scratch.outputs(&requested)), Ok(()));
    }
}

#[test]
fn multiple_cgus_refuse_before_publishing_any_requested_object() {
    let scratch = Scratch::new();
    let outputs = scratch.outputs(&[OutputType::Object]);
    let modules = ["first", "second"].map(|name| regular(&outputs, name));
    for module in &modules {
        fs::write(module.object.as_ref().unwrap(), module.name.as_bytes()).unwrap();
    }
    let compiled = CompiledModules { modules: modules.into(), allocator_module: None };
    assert!(validate_requested_object(&compiled, &outputs).unwrap_err().contains("found 2"));
    assert!(!outputs.path(OutputType::Object).as_path().exists());
    for module in &compiled.modules {
        assert_eq!(fs::read(module.object.as_ref().unwrap()).unwrap(), module.name.as_bytes());
    }
}

#[test]
fn missing_object_record_cannot_publish_a_stale_file_at_the_expected_path() {
    let scratch = Scratch::new();
    let outputs = scratch.outputs(&[OutputType::Object]);
    let mut module = regular(&outputs, "cgu");
    let stale = module.object.take().unwrap();
    fs::write(&stale, b"stale").unwrap();
    assert!(
        validate_requested_object(&compiled(module), &outputs)
            .unwrap_err()
            .contains("did not emit a requested object")
    );
    assert_eq!(fs::read(stale).unwrap(), b"stale");
}

#[test]
fn missing_object_file_refuses_instead_of_reporting_an_artifact() {
    let scratch = Scratch::new();
    let outputs = scratch.outputs(&[OutputType::Object]);
    assert!(
        validate_requested_object(&compiled(regular(&outputs, "cgu")), &outputs)
            .unwrap_err()
            .contains("cannot inspect emitted object")
    );
    assert!(!outputs.path(OutputType::Object).as_path().exists());
}

#[test]
fn recorded_path_must_match_the_shared_publishers_recomputed_path() {
    let scratch = Scratch::new();
    let outputs = scratch.outputs(&[OutputType::Object]);
    let mut module = regular(&outputs, "cgu");
    fs::write(module.object.as_ref().unwrap(), b"unrelated expected-path bytes").unwrap();
    let other = scratch.0.join("other.o");
    fs::write(&other, b"recorded bytes").unwrap();
    module.object = Some(other.clone());
    assert!(
        validate_requested_object(&compiled(module), &outputs)
            .unwrap_err()
            .contains("but rustc would publish")
    );
    assert_eq!(fs::read(other).unwrap(), b"recorded bytes");
}

#[test]
fn empty_object_file_is_an_explicit_refusal() {
    let scratch = Scratch::new();
    let outputs = scratch.outputs(&[OutputType::Object]);
    let module = regular(&outputs, "cgu");
    fs::write(module.object.as_ref().unwrap(), b"").unwrap();
    assert!(
        validate_requested_object(&compiled(module), &outputs)
            .unwrap_err()
            .contains("not a nonempty regular file")
    );
}

#[test]
fn object_path_directory_is_an_explicit_refusal() {
    let scratch = Scratch::new();
    let outputs = scratch.outputs(&[OutputType::Object]);
    let module = regular(&outputs, "cgu");
    fs::create_dir(module.object.as_ref().unwrap()).unwrap();
    assert!(
        validate_requested_object(&compiled(module), &outputs)
            .unwrap_err()
            .contains("not a nonempty regular file")
    );
}

#[cfg(unix)]
#[test]
fn object_path_symlink_cannot_substitute_another_file() {
    let scratch = Scratch::new();
    let outputs = scratch.outputs(&[OutputType::Object]);
    let module = regular(&outputs, "cgu");
    let target = scratch.0.join("other.o");
    fs::write(&target, b"not this CGU").unwrap();
    std::os::unix::fs::symlink(&target, module.object.as_ref().unwrap()).unwrap();
    assert!(
        validate_requested_object(&compiled(module), &outputs)
            .unwrap_err()
            .contains("not a nonempty regular file")
    );
    assert_eq!(fs::read(target).unwrap(), b"not this CGU");
}

#[test]
fn allocator_is_not_a_substitute_for_a_regular_object() {
    let scratch = Scratch::new();
    let outputs = scratch.outputs(&[OutputType::Object]);
    let mut module = regular(&outputs, "allocator");
    fs::write(module.object.as_ref().unwrap(), b"allocator bytes").unwrap();
    module.kind = ModuleKind::Allocator;
    assert!(
        validate_requested_object(&compiled(module), &outputs)
            .unwrap_err()
            .contains("requires a regular codegen unit")
    );
}

#[test]
fn final_paths_use_rustcs_output_filenames_without_a_parallel_naming_rule() {
    let scratch = Scratch::new();
    let mut outputs = scratch.outputs(&[OutputType::Object]);
    assert_eq!(outputs.path(OutputType::Object).as_path(), scratch.0.join("source-name.o"));
    let module = regular(&outputs, "cgu");
    let temporary = module.object.as_ref().unwrap().clone();
    fs::write(&temporary, b"object bytes").unwrap();

    outputs.single_output_file = Some(OutFileName::Real(scratch.0.join("single-name")));
    assert_eq!(outputs.path(OutputType::Object).as_path(), scratch.0.join("single-name"));
    outputs.outputs = OutputTypes::new(&[
        (OutputType::Object, Some(OutFileName::Real(scratch.0.join("explicit-object")))),
        (OutputType::Metadata, None),
        (OutputType::DepInfo, None),
    ]);
    assert_eq!(outputs.path(OutputType::Object).as_path(), scratch.0.join("explicit-object"));
    assert_eq!(validate_requested_object(&compiled(module), &outputs), Ok(()));
    assert_eq!(fs::read(&temporary).unwrap(), b"object bytes");
    outputs.outputs = OutputTypes::new(&[(OutputType::Object, Some(OutFileName::Stdout))]);
    assert_eq!(outputs.path(OutputType::Object), OutFileName::Stdout);
}

fn assert_final_alias_refused(scratch: &Scratch, alias: impl FnOnce(&PathBuf) -> PathBuf) {
    let mut outputs = scratch.outputs(&[OutputType::Object]);
    let module = regular(&outputs, "cgu");
    let temporary = module.object.as_ref().unwrap().clone();
    fs::write(&temporary, b"emitted object must not be truncated or removed").unwrap();
    let final_path = alias(&temporary);
    outputs.outputs =
        OutputTypes::new(&[(OutputType::Object, Some(OutFileName::Real(final_path)))]);
    assert!(
        validate_requested_object(&compiled(module), &outputs)
            .unwrap_err()
            .contains("aliases temporary CGU object")
    );
    assert_eq!(fs::read(temporary).unwrap(), b"emitted object must not be truncated or removed");
}

#[test]
fn explicit_final_path_cannot_be_the_cgu_temporary() {
    let scratch = Scratch::new();
    assert_final_alias_refused(&scratch, Clone::clone);
}

#[test]
fn normalized_final_path_alias_cannot_be_the_cgu_temporary() {
    let scratch = Scratch::new();
    assert_final_alias_refused(&scratch, |temporary| {
        // A real extra directory makes the .. spelling valid on every host.
        fs::create_dir(scratch.0.join("nested")).unwrap();
        scratch.0.join("nested").join("..").join(temporary.file_name().unwrap())
    });
}

#[test]
fn hardlinked_final_path_cannot_truncate_the_cgu_temporary() {
    let scratch = Scratch::new();
    assert_final_alias_refused(&scratch, |temporary| {
        let alias = scratch.0.join("hardlinked-final.o");
        fs::hard_link(temporary, &alias).unwrap();
        alias
    });
}

#[cfg(unix)]
#[test]
fn symlinked_final_path_cannot_truncate_the_cgu_temporary() {
    let scratch = Scratch::new();
    assert_final_alias_refused(&scratch, |temporary| {
        let alias = scratch.0.join("symlinked-final.o");
        std::os::unix::fs::symlink(temporary, &alias).unwrap();
        alias
    });
}
