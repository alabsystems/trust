// Trust: the general lane's refusal reasons carry Clean's Display text, exactly
// (Clean R80; Clean R151 consumer (3); `docs/DECISION_QUEUE.md`
// R80-CONSUMERS-1). The refusal is the one R80 added, the order record's, which
// `constant_to_decl` returns for every declaration of such an environment and
// the batch pipeline returns for the batch. It names its own options, so the
// lane appends none; a refusal that names none gets the lane's.

use clean_compiler::CompilerError;
use clean_compiler::pass_manager::PipelineError;
use clean_kernel::Name;

use super::{general_batch_refusal, general_declaration_refusal};

// Trust (CLEAN-TV-SOURCE-DICTIONARY-ENV-1): `mint_kernel_tv` over real elaborated
// island source, re-checked as the join seam re-checks it.
mod kernel_tv;

fn order_refusal(via: &str) -> CompilerError {
    CompilerError::ImplementedByOrder {
        referrer: Name::from_string("caller"),
        rebound: Name::from_string("slow"),
        via: Name::from_string(via),
    }
}

fn order_text(reach: &str) -> String {
    format!(
        "an `attribute [implemented_by]` command rebound `slow` after code that reaches it \
         was added ({reach}). Pinned Lean compiled that code before the binding, and which \
         body it runs is decided by Lean's inliner, which Clean does not model, so no \
         declaration of this environment is lowered (implemented-by-order). Options: write \
         the attribute on the declaration, or before every use of it."
    )
}

/// A refusal that names no options of its own.
fn unsupported() -> CompilerError {
    CompilerError::Unsupported("`Float.ofScientific`".to_owned())
}

#[test]
fn general_declaration_refusal_prints_the_display_text() {
    assert_eq!(
        general_declaration_refusal(&order_refusal("slow")),
        format!(
            "the general L5CNF lowering refused this declaration: {}",
            order_text("`caller` names `slow`")
        )
    );
}

#[test]
fn general_declaration_refusal_adds_the_lane_options_to_a_refusal_without_its_own() {
    assert_eq!(
        general_declaration_refusal(&unsupported()),
        "the general L5CNF lowering refused this declaration: unsupported expression: \
         `Float.ofScientific`. Options: spell the definition inside the supported \
         computational surface, or leave it PROOF-side — recording is not calling, and \
         nothing breaks."
    );
}

#[test]
fn general_batch_refusal_prints_the_display_text() {
    assert_eq!(
        general_batch_refusal(&PipelineError::Compiler(order_refusal("helper"))),
        format!(
            "the general pipeline refused the island batch: {}",
            order_text("`caller` reaches `slow` through `helper`")
        )
    );
}

#[test]
fn general_batch_refusal_adds_the_lane_options_to_a_refusal_without_its_own() {
    assert_eq!(
        general_batch_refusal(&PipelineError::Compiler(unsupported())),
        "the general pipeline refused the island batch: unsupported expression: \
         `Float.ofScientific`. Options: the refusal names the declaration and construct — \
         spell it inside the compilable surface, split the island so the refusing \
         declaration stands alone, or leave it PROOF-side."
    );
}
