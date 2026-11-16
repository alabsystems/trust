// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright 2026 Andrew Yates

//! The test-support patched-prelude API (lane B1a, B1A-01b; B1A-D53). A `[[test]]`
//! target with `required-features = ["test-support"]`; the lane's helpers always pass
//! that feature. Release-only like every test that elaborates the prelude (B1A-D42).

use trust_spec_temporal::CleanTemporalCertificateError;
use trust_spec_temporal::model_prelude::{
    ModelPreludeError, ModulePatch, check_model_theorem, elaborate_model_suffix,
    with_model_prelude, with_model_prelude_patched,
};

fn patch(module: &str, find: &str, replace: &str) -> ModulePatch {
    ModulePatch { module: module.to_owned(), find: find.to_owned(), replace: replace.to_owned() }
}

const EP_VERSION_DEF: &str = "def epVersion : Nat := 1";

fn door(version: u32) -> Result<(), ModelPreludeError> {
    with_model_prelude(move |mut prelude| door_in(&mut prelude, version))?
}

fn door_in(
    prelude: &mut trust_spec_temporal::model_prelude::ModelPrelude,
    version: u32,
) -> Result<(), ModelPreludeError> {
    let name = format!("epVersionIs{version}");
    elaborate_model_suffix(
        prelude,
        &format!("theorem {name} : Nat.beq Trust.Model.epVersion {version} = true := rfl\n"),
        "epVersion door",
    )?;
    check_model_theorem(prelude.environment(), &name)
}

/// A patch takes effect only in its own call: the patched prelude decides the door
/// the other way, and the cached prelude is untouched afterwards.
#[test]
#[cfg_attr(debug_assertions, ignore = "release-only: kernel reduction")]
fn a_patch_changes_only_its_own_prelude() {
    let patched = with_model_prelude_patched(
        vec![patch("Trust.Model.Value", EP_VERSION_DEF, "def epVersion : Nat := 2")],
        |mut prelude| (door_in(&mut prelude, 2), door_in(&mut prelude, 1)),
    )
    .expect("the patched prelude elaborates");
    assert_eq!(patched.0, Ok(()));
    assert!(matches!(patched.1, Err(ModelPreludeError::Clean(_))), "{:?}", patched.1);
    assert_eq!(door(1), Ok(()));
    assert!(matches!(door(2), Err(ModelPreludeError::Clean(_))));
}

/// An ill-typed module in the prelude itself refuses the whole prelude.
#[test]
#[cfg_attr(debug_assertions, ignore = "release-only: kernel reduction")]
fn an_ill_typed_prelude_module_is_refused() {
    let refused = with_model_prelude_patched(
        vec![patch("Trust.Model.Value", EP_VERSION_DEF, "def epVersion : Nat := true")],
        |_| (),
    );
    assert!(
        matches!(
            refused,
            Err(ModelPreludeError::Clean(CleanTemporalCertificateError::Elaborate {
                unit: "Trust.Model.Value",
                ..
            }))
        ),
        "{refused:?}"
    );
}

/// A patch must name a served module and match exactly once.
#[test]
fn a_patch_must_match_exactly_once() {
    assert_eq!(
        with_model_prelude_patched(vec![patch("Trust.Model.Nope", "x", "y")], |_| ()),
        Err(ModelPreludeError::UnknownModule("Trust.Model.Nope".to_owned()))
    );
    for find in ["no such text", "", "Trust"] {
        let refused =
            with_model_prelude_patched(vec![patch("Trust.Model.Value", find, "y")], |_| ());
        assert!(
            matches!(refused, Err(ModelPreludeError::PatchMismatch { ref module, occurrences, .. })
                if module == "Trust.Model.Value" && occurrences != 1),
            "{find:?}: {refused:?}"
        );
    }
}
