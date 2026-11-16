#!/usr/bin/env python3
"""Focused regression controls for the retired compatibility WP native API."""

import importlib.util
import copy
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[2]
SPEC = importlib.util.spec_from_file_location(
    "manifest_alignment", ROOT / "scripts" / "check_cargo_manifest_alignment.py"
)
POLICY = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(POLICY)


class NativeFacadeRetirement(unittest.TestCase):
    def test_current_sources_and_reintroduction_controls(self):
        self.assertEqual(POLICY.wp_retirement_self_check(), [])


class RouterBackendDependencyScope(unittest.TestCase):
    def setUp(self):
        self.manifests = {name: POLICY.load_manifest(path)
                          for name, path in POLICY.FANOUT_POLICY_MANIFESTS.items()}

    def test_current_test_only_core_fixture_keeps_production_retirement(self):
        router = self.manifests["trust-router"]
        self.assertIn("trust-wp-core", router["dev-dependencies"])
        self.assertEqual(POLICY.check_dependency_fanout_policy(self.manifests), [])

    def test_dev_dependencies_allow_direct_and_workspace_package_aliases(self):
        for target in (None, "cfg(unix)"):
            for alias in ("trust-wp-core", "fixture-core"):
                case = copy.deepcopy(self.manifests)
                scope = case["trust-router"]
                if target is not None:
                    scope = scope.setdefault("target", {}).setdefault(target, {})
                scope.setdefault("dev-dependencies", {})[alias] = {"workspace": True}
                case["root"].setdefault("workspace", {}).setdefault("dependencies", {})[alias] = {
                    "package": "trust-wp-core", "path": "canonical-fixture"
                }
                with self.subTest(target=target, alias=alias):
                    self.assertEqual(POLICY.check_dependency_fanout_policy(case), [])

    def test_normal_build_and_target_dependencies_refuse_all_package_spellings(self):
        for target in (None, "cfg(unix)"):
            for section in ("dependencies", "build-dependencies"):
                for spelling in ("direct", "alias", "workspace-alias"):
                    case = copy.deepcopy(self.manifests)
                    scope = case["trust-router"]
                    if target is not None:
                        scope = scope.setdefault("target", {}).setdefault(target, {})
                    alias = "trust-wp-core" if spelling == "direct" else "backend-core"
                    declaration = {"version": "1", "optional": True}
                    if spelling == "alias":
                        declaration["package"] = "trust-wp-core"
                    if spelling == "workspace-alias":
                        declaration = {"workspace": True, "optional": True}
                        case["root"].setdefault("workspace", {}).setdefault("dependencies", {})[alias] = {
                            "package": "trust-wp-core", "path": "canonical-core"
                        }
                    scope.setdefault(section, {})[alias] = declaration
                    with self.subTest(target=target, section=section, spelling=spelling):
                        self.assertTrue(any("retired TrustWP backend dependency" in error
                                            for error in POLICY.check_dependency_fanout_policy(case)))

    def test_dev_fixture_does_not_permit_the_retired_feature_or_default_backend(self):
        for feature in ("trust-wp-backend", "ay-backend"):
            case = copy.deepcopy(self.manifests)
            features = case["trust-router"].setdefault("features", {})
            if feature == "trust-wp-backend":
                features[feature] = []
                expected = "retired parsed TrustWP backend feature"
            else:
                features["default"] = [feature]
                expected = "default features must not enable native solver backends"
            with self.subTest(feature=feature):
                self.assertTrue(any(expected in error for error
                                    in POLICY.check_dependency_fanout_policy(case)))


def codec_fixture():
    manifests = {owner: {"dependencies": {"trust-ir-contract": {"workspace": True, "features": ["proof-json"]}}}
                 for owner in POLICY.FORMULA_CODEC_PATHS}
    workspaces = {owner: {"workspace": {"dependencies": {"trust-ir-contract": {"path": "canonical-ir-contract"}}}}
                  for owner in manifests}
    sources = {
        "trust-types": """
use trust_ir_contract::{proof_json::UniqueJsonValue,
    trust_formula_v1::{validate_value, DecodePolicy}};
pub fn canonical_arithmetic_free_trust_formula_v1_payload(value: &Value) {
    validate_value(value, DecodePolicy::CanonicalArithmeticFree);
    serde_json::json!({"body": {"op": "eq"}});
}
pub fn parse_unique_proof_json_payload(payload: &str) {
    crate::json_depth::from_str_deep::<UniqueJsonValue>(payload)
        .map(UniqueJsonValue::into_value)
}
""",
        "trust-wp-core": """
use trust_ir_contract::proof_json::UniqueJsonValue;
use trust_ir_contract::trust_formula_v1::{self as wire, DecodePolicy};
pub fn decode_trust_formula_v1_declared_claim(value: &Value) {
    decode_trust_formula_v1_declared_claim_and_value(value)
}
pub fn decode_trust_formula_v1_declared_claim_and_value(value: &Value) {
    wire::decode_value::<PureExprAlgebra>(value, DecodePolicy::NativeReplay)
}
fn parse_unique_json(payload: &str) {
    let value = UniqueJsonValue::deserialize(&mut decoder)?;
    decoder.end()?;
    Ok(value.into_value())
}
""",
    }
    return manifests, workspaces, sources


class SharedFormulaCodecRetirement(unittest.TestCase):
    def test_retirement_guard_is_a_required_push_row(self):
        listing = subprocess.check_output(
            ["bash", str(ROOT / "tests/run_trust_comprehensive_harness.sh"), "--list", "push"],
            cwd=ROOT, text=True,
        )
        rows = [line.split("\t") for line in listing.splitlines()
                if line.startswith("fast.cargo-manifest-alignment\t")]
        self.assertEqual(len(rows), 1)
        self.assertEqual(rows[0][2], "true")
        self.assertEqual(rows[0][4], "python3 scripts/check_cargo_manifest_alignment.py")

    def test_maintained_self_check_exercises_reintroduction_controls(self):
        with patch.object(POLICY, "shared_formula_codec_inputs", return_value=codec_fixture()):
            self.assertEqual(POLICY.shared_formula_codec_self_check(), [])
            with patch.object(POLICY, "check_shared_formula_codec", return_value=[]):
                self.assertEqual(len(POLICY.shared_formula_codec_self_check()), 6)

    def test_canonical_delegation_and_local_entry_policies(self):
        self.assertEqual(POLICY.check_shared_formula_codec(*codec_fixture()), [])

    def test_import_and_dependency_aliases_remain_typed(self):
        manifests, workspaces, sources = codec_fixture()
        for owner in manifests:
            dependency = manifests[owner]["dependencies"].pop("trust-ir-contract")
            # Cargo can enable the feature at either normal workspace layer.
            dependency.pop("features")
            manifests[owner]["dependencies"]["wire-contract"] = dependency
            workspaces[owner]["workspace"]["dependencies"] = {"wire-contract": {
                "package": "trust-ir-contract", "path": "canonical", "features": ["proof-json"]}}
            sources[owner] = sources[owner].replace("trust_ir_contract", "wire_contract").replace(
                "proof_json::UniqueJsonValue", "proof_json::UniqueJsonValue as Json")
            sources[owner] = sources[owner].replace("::<UniqueJsonValue>", "::<Json>").replace(
                "UniqueJsonValue::", "Json::")
        sources["trust-types"] = sources["trust-types"].replace("validate_value,", "validate_value as validate,").replace(
            "    validate_value(", "    validate(")
        self.assertEqual(POLICY.check_shared_formula_codec(manifests, workspaces, sources), [])

    def test_comments_strings_and_test_only_oracles_do_not_restore_grammar(self):
        manifests, workspaces, sources = codec_fixture()
        oracle = '''
// struct UniqueJsonVisitor; fn decode_expr() { value.get("body"); }
const TEXT: &str = r#"enum WireSort {} value.get("schema")"#;
#[cfg(test)] mod oracle {
    struct UniqueJsonVisitor;
    enum WireSort {}
    struct Binding;
    fn decode_expr() { value.get("body"); }
}
'''
        for owner in sources:
            sources[owner] += oracle
        self.assertEqual(POLICY.check_shared_formula_codec(manifests, workspaces, sources), [])

    def test_missing_delegates_cannot_be_spoofed_by_comments_or_tests(self):
        manifests, workspaces, sources = codec_fixture()
        for owner, delegate in (("trust-types", "validate_value"), ("trust-wp-core", "decode_value")):
            with self.subTest(owner=owner):
                case = copy.deepcopy(sources)
                case[owner] = case[owner].replace(delegate + "(", "local_copy(").replace(
                    delegate + "::<", "local_copy::<")
                case[owner] += f"\n// {delegate}(value, DecodePolicy::NativeReplay);\n"
                case[owner] += f"#[cfg(test)] fn oracle() {{ {delegate}(value); }}\n"
                self.assertTrue(any("must delegate" in error for error in
                                    POLICY.check_shared_formula_codec(manifests, workspaces, case)))

    def test_restored_grammar_declarations_are_refused(self):
        manifests, workspaces, sources = codec_fixture()
        for declaration in ("struct UniqueJsonVisitor;", "struct UniqueJsonValue;", "enum WireSort {}", "struct Binding;",
                            "fn decode_expr() {}", "fn decode_sort() {}", "enum TrustFormulaV1Sort {}",
                            "fn validate_arithmetic_free_trust_formula_v1() {}"):
            for owner in sources:
                with self.subTest(owner=owner, declaration=declaration):
                    case = {**sources, owner: sources[owner] + declaration}
                    self.assertTrue(any("retired local grammar" in error for error in
                                        POLICY.check_shared_formula_codec(manifests, workspaces, case)))

    def test_raw_semantic_fields_are_refused_including_raw_strings(self):
        manifests, workspaces, sources = codec_fixture()
        for field in ('"schema"', 'r#"body"#', '"variables"', '"s\\u{6f}rt"'):
            for owner in sources:
                with self.subTest(owner=owner, field=field):
                    case = {**sources, owner: sources[owner] + f"fn private_copy() {{ value.get(/* key */ {field}); }}"}
                    self.assertTrue(any("raw JSON field reads" in error for error in
                                        POLICY.check_shared_formula_codec(manifests, workspaces, case)))

    def test_normal_dependency_feature_and_canonical_identity_are_required(self):
        for mutation in ("dev", "optional", "feature", "foreign", "explicit"):
            manifests, workspaces, sources = codec_fixture()
            for owner in manifests:
                dependencies = manifests[owner]["dependencies"]
                declaration = dependencies["trust-ir-contract"]
                if mutation == "dev":
                    manifests[owner]["dev-dependencies"] = dependencies.copy()
                    dependencies.clear()
                elif mutation == "optional":
                    declaration["optional"] = True
                elif mutation == "feature":
                    declaration["features"] = []
                elif mutation == "foreign":
                    workspaces[owner]["workspace"]["dependencies"]["trust-ir-contract"]["package"] = "foreign-contract"
                else:
                    declaration["path"] = "private-copy"
            with self.subTest(mutation=mutation):
                errors = POLICY.check_shared_formula_codec(manifests, workspaces, sources)
                self.assertTrue(any("workspace trust-ir-contract dependency" in error for error in errors))

    def test_foreign_types_unused_imports_shadowing_and_policy_refuse(self):
        manifests, workspaces, sources = codec_fixture()
        mutations = (
            lambda text: text.replace("proof_json::UniqueJsonValue", "foreign::UniqueJsonValue"),
            lambda text: text.replace("DecodePolicy::", "LocalPolicy::"),
            lambda text: text.replace("DecodePolicy::CanonicalArithmeticFree", "DecodePolicy::NativeReplay"),
            lambda text: text + "\nmod trust_ir_contract {}",
            lambda text: text.replace("validate_value(value,", "private::validate_value(value,"),
        )
        for mutation in mutations:
            with self.subTest(mutation=mutation):
                case = {**sources, "trust-types": mutation(sources["trust-types"])}
                self.assertTrue(POLICY.check_shared_formula_codec(manifests, workspaces, case))

    def test_unused_canonical_json_type_does_not_authorize_private_parser(self):
        manifests, workspaces, sources = codec_fixture()
        sources["trust-types"] = sources["trust-types"].replace(
            "crate::json_depth::from_str_deep::<UniqueJsonValue>(payload)",
            "private_json_parser(payload); sizeof::<UniqueJsonValue>()")
        self.assertTrue(any("must parse with canonical" in error for error in
                            POLICY.check_shared_formula_codec(manifests, workspaces, sources)))

    def test_missing_source_and_duplicate_entrypoint_refuse(self):
        manifests, workspaces, sources = codec_fixture()
        self.assertTrue(POLICY.check_shared_formula_codec(manifests, workspaces, {}))
        sources["trust-types"] += "\nfn canonical_arithmetic_free_trust_formula_v1_payload() {}"
        self.assertTrue(any("must delegate" in error for error in
                            POLICY.check_shared_formula_codec(manifests, workspaces, sources)))

    def test_wp_wrapper_cannot_bypass_shared_decoded_value_entrypoint(self):
        manifests, workspaces, sources = codec_fixture()
        sources["trust-wp-core"] = sources["trust-wp-core"].replace(
            "    decode_trust_formula_v1_declared_claim_and_value(value)", "    private_decoder(value)")
        self.assertTrue(any("wrapper must delegate" in error for error in
                            POLICY.check_shared_formula_codec(manifests, workspaces, sources)))


class NativeSpSplitterRetirement(unittest.TestCase):
    def test_restored_production_splitters_are_refused(self):
        for name in ("split_trust_formula_body", "flatten_trust_formula_conjunction"):
            for declaration in (f"fn {name}() {{}}", f"pub(crate) fn r#{name}<T>() {{}}",
                                f"unsafe fn /* gap */ {name}\n() {{}}"):
                with self.subTest(declaration=declaration):
                    errors = POLICY.check_native_sp_splitter_retirement(declaration)
                    self.assertEqual(len(errors), 1)
                    self.assertIn("retired raw JSON splitters", errors[0])
                    self.assertIn(name, errors[0])

    def test_comments_strings_and_test_only_oracles_remain_allowed(self):
        source = '''
// fn split_trust_formula_body() {}
/* fn flatten_trust_formula_conjunction() {} */
const TEXT: &str = r#"fn split_trust_formula_body() {}"#;
#[cfg(test)] mod oracle {
    fn split_trust_formula_body() {}
    fn flatten_trust_formula_conjunction() {}
}
#[cfg(all(test, feature = "oracle"))]
fn flatten_trust_formula_conjunction() {}
fn current_sp_projection() {}
'''
        self.assertEqual(POLICY.check_native_sp_splitter_retirement(source), [])

    def test_json_projection_serialization_and_other_names_remain_allowed(self):
        source = '''
fn project_original_atom(value: &Value, path: &str) {
    let original = value.pointer(path);
    let metadata = value.get("body");
    serde_json::to_string(original);
    serde_json::json!({"body": metadata, "op": "and"});
}
fn split_trust_formula_body_projection() {}
fn flatten_trust_formula_conjunction_paths() {}
'''
        self.assertEqual(POLICY.check_native_sp_splitter_retirement(source), [])

    def test_missing_native_input_refuses_and_loader_reads_exact_owner_path(self):
        for source in ("", " \n\t"):
            self.assertTrue(any("native SP source is missing" in error for error in
                                POLICY.check_native_sp_splitter_retirement(source)))
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            with patch.object(POLICY, "REPO_ROOT", root):
                self.assertEqual(POLICY.native_sp_source(), "")
                path = root / POLICY.NATIVE_SP_SOURCE_PATH
                path.parent.mkdir(parents=True)
                source = "fn flatten_trust_formula_conjunction() {}\n"
                path.write_text(source, encoding="utf-8")
                self.assertEqual(POLICY.native_sp_source(), source)
                self.assertTrue(POLICY.check_native_sp_splitter_retirement(POLICY.native_sp_source()))

    def test_maintained_self_check_requires_both_hostile_controls_and_missing_input(self):
        with patch.object(POLICY, "native_sp_source", return_value="fn project_original_atom() {}"):
            self.assertEqual(POLICY.native_sp_splitter_self_check(), [])
            with patch.object(POLICY, "check_native_sp_splitter_retirement", return_value=[]):
                self.assertEqual(len(POLICY.native_sp_splitter_self_check()), 3)


if __name__ == "__main__":
    unittest.main()
