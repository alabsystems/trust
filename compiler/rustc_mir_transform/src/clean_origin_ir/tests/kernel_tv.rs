// Trust (CLEAN-TV-SOURCE-DICTIONARY-ENV-1): the kernel-TV companion of a
// carrier-gated `+`/`-`/`*` row, minted from REAL elaborated island source and
// re-checked the way the join seam re-checks it.
//
// The four ui fixtures that went red with the Clean 16ef16da pin
// (`clean_origin_wrapping_verify_on`, `clean_origin_forwarding_def_verify_on`,
// `e9_cited_island_def_discharge`, `e9_release_mode_discharge#release`) died at
// semantic finalization on "the expected kernel-TV companion is missing ...
// source instance dictionary did not resolve to `HAdd.mk`": the elaborator spells
// `a + b` as `HAdd.hAdd UIntW UIntW UIntW <named dictionary> a b`, Clean now
// denotes a dispatcher by the stored field of its ACTUAL dictionary, and a named
// dictionary resolves only in the environment the source was checked in. The mint
// asked the environment-free reader. These tests pin the mint against the
// elaborator's own spelling, so a reader that cannot see the dictionary fails here
// in seconds rather than in a stage-1 ui run.

use clean_kernel::{Environment, Name};
use clean_reflect::RecordVocab;
use trust_ir::value::{FuncId, FuncTyId};

use super::super::{mint_kernel_tv, shape_tag};

/// Every arithmetic dispatcher the wrapping planner admits, at three widths and
/// both operand spellings (parameter and numeral), plus a forwarding `def` whose
/// companion reads its source through the helper expansion (the second reader
/// call in `mint_kernel_tv`).
const ISLAND: &str = "\
def wsum (a : UInt64) (b : UInt64) : UInt64 := a + b
def winc (a : UInt64) : UInt64 := a + 1
def wdiff (a : UInt32) (b : UInt32) : UInt32 := a - b
def wprod (a : UInt8) (b : UInt8) : UInt8 := a * b
def wsub64 (a : UInt64) (b : UInt64) : UInt64 := a - b
def inc (x : UInt64) : UInt64 := x + 1
def incAlias (x : UInt64) : UInt64 := inc x
";

/// Written directly, so carrier-gate targets: a missing companion is fatal.
const GATED: &[&str] = &["wsum", "winc", "wdiff", "wprod", "wsub64", "inc"];
/// Reached through a Lean helper: untargeted (`gate_targets`' direct-source
/// condition), so a missing companion silently left it at tier structural.
const FORWARDING: &[&str] = &["incAlias"];

fn island() -> Environment {
    let mut environment = Environment::with_prelude();
    environment.init_io_ops().expect("initialize the actual Clean prelude");
    let patterns = clean_elab::tactic::builtins::builtin_tactic_patterns();
    let parsed =
        clean_parser::parse_file_with_tactics(ISLAND, &patterns).expect("parse the island");
    let mut context = clean_elab::FileContext::new();
    for declaration in parsed {
        let processed = clean_elab::preprocess_decl_with_context(&declaration, &mut context);
        let registered = clean_elab::elaborate_decl_and_register_with_context_and_warning(
            &mut environment,
            &processed,
            &mut context,
        )
        .expect("elaborate and kernel-check the island");
        assert!(registered.warning.is_none(), "the island must need no trust warning");
    }
    environment
}

struct Emitted {
    shape: &'static str,
    signature: trust_ir::ty::FuncTy,
    function: trust_ir::Function,
}

/// The collector's own steps for one row: plan, signature, emitted body.
fn emit(environment: &Environment, name: &str, targeted: bool) -> Emitted {
    let declaration = Name::from_string(name);
    // The collector's planner entry, with this island's (empty) Rust callee table.
    let plan = trust_clean_origin::plan_clean_origin_body_with_rust_callees_for_name(
        environment,
        &declaration,
        &[],
    )
    .unwrap_or_else(|refusal| panic!("`{name}` plans: {}", refusal.note()));
    // A gate target with no companion is the fatal these fixtures died on.
    assert_eq!(trust_clean_ir_gate::gate_targets(&plan), targeted, "`{name}` targeting");
    let signature = trust_clean_ir::trust_ir_func_ty(plan.signature())
        .unwrap_or_else(|refusal| panic!("`{name}` has a carrier signature: {refusal:?}"));
    let function =
        trust_clean_ir::emit_clean_origin_function(&plan, FuncId::new(0), FuncTyId::new(0))
            .unwrap_or_else(|refusal| panic!("`{name}` emits: {refusal:?}"));
    Emitted { shape: shape_tag(plan.shape()), signature, function }
}

/// The mini-module the join seam re-checks (`clean_origin_join::tv_mini_module`).
fn recheck(emitted: &Emitted, mint: &trust_thir_lower::clean_origin_join::CleanTvMint) -> usize {
    let mut mini = trust_ir::Module::new("clean-origin-validate::kernel-tv-test".to_string());
    mini.func_types.push(emitted.signature.clone());
    mini.functions.push(emitted.function.clone());
    mini.proof_obligations.push(mint.obligation.clone());
    mini.proof_certificates.push(mint.certificate.clone());
    trust_ir_build::validate_module(&mini).len()
}

#[test]
fn gated_wrapping_rows_mint_a_companion_the_join_recheck_accepts() {
    let environment = island();
    let rows = GATED.iter().map(|name| (*name, true));
    for (name, targeted) in rows.chain(FORWARDING.iter().map(|name| (*name, false))) {
        let emitted = emit(&environment, name, targeted);
        let (mint, note) = mint_kernel_tv(
            &environment,
            &Name::from_string(name),
            name,
            emitted.shape,
            &emitted.signature,
            &emitted.function,
        );
        let mint = mint.unwrap_or_else(|| panic!("`{name}` mints no companion: {note:?}"));
        assert_eq!(note, None, "`{name}`");
        assert_eq!(recheck(&emitted, &mint), 0, "`{name}`: the kernel re-check refuses");
    }
}

/// Control: the dictionary is why the environment is load-bearing. The
/// environment-free reader refuses each of these exact definitions on its named
/// dictionary, so reverting the mint to it reproduces the four fatals.
#[test]
fn the_environment_free_reader_refuses_the_named_dictionaries() {
    let environment = island();
    for &(name, width) in
        &[("wsum", 64), ("winc", 64), ("wdiff", 32), ("wprod", 8), ("wsub64", 64), ("inc", 64)]
    {
        let definition = environment
            .get_const(&Name::from_string(name))
            .and_then(|constant| constant.value.clone())
            .expect("an accepted definition");
        let refusal = clean_reflect::denote_source(&definition, width, &[], &RecordVocab::empty())
            .expect_err("a named dictionary has no meaning without its environment");
        assert!(refusal.to_string().contains("source instance dictionary"), "`{name}`: {refusal}");
        clean_reflect::denote_source_in_environment(
            &definition,
            width,
            &[],
            &RecordVocab::empty(),
            &environment,
        )
        .unwrap_or_else(|refusal| panic!("`{name}` denotes in its environment: {refusal}"));
    }
}

/// Control: the re-check judges the carried source. A companion minted from
/// another declaration's source (subtraction, same width and arity) against the
/// emitted addition is refused, so the test above passes because the equation
/// holds, not because nothing is checked.
#[test]
fn a_companion_carrying_another_source_is_refused_by_the_recheck() {
    let environment = island();
    let emitted = emit(&environment, "wsum", true);
    let (mint, note) = mint_kernel_tv(
        &environment,
        &Name::from_string("wsub64"),
        "wsum",
        emitted.shape,
        &emitted.signature,
        &emitted.function,
    );
    let mint = mint.unwrap_or_else(|| panic!("the mismatched mint is still built: {note:?}"));
    assert_ne!(recheck(&emitted, &mint), 0, "an add body re-checked against a sub source");
}
