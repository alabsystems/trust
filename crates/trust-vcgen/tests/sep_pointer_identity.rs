// Regression: the separation engine must not charge an `[unsafe:sep:*]`
// memory-safety obligation to code that performs NO unsafe operation.
//
// Two projection/type-blind propagations in `sep_engine` made safe Rust
// refute under the hardened profile:
//
//  1. `local_to_ptr` (MIR local -> abstract allocation name) was propagated
//     through `Rvalue::Use` with no regard for the DESTINATION local's type.
//     A load THROUGH a reference argument -- `_3 = copy (*_12)[_2]`, an `f32`
//     -- therefore inherited `arg_1`'s pointer identity, and the following
//     `_0 = Add(move _3, move _6)` (an `f32 + f32`) was routed to
//     `interpret_ptr_offset`, emitting
//     `[unsafe:sep:offset] pointer offset out of bounds for `arg_1``.
//
//  2. `interpret_drop` freed `local_to_ptr[place.local]` while IGNORING the
//     place's projections. `steps[i] = ..; steps[j] = ..` on a `&mut [T]`
//     lowers to `drop((*_1)[_i])` then `drop((*_1)[_j])`; both resolved to
//     `arg_1`, so the second reported
//     `[unsafe:sep:free] double-free of `arg_1`` with the undischargeable
//     `Formula::Bool(true)` -- a definite violation no solver can clear.
//
// Fixtures are the REAL extracted MIR (`-Ztrust-dump=mir:<dir>`) of:
//   value_add_closure: |i| tail[i] + head[i]              (no `unsafe` at all)
//   slice_elem_stores: fn(steps: &mut [String], i: usize) (no `unsafe` at all)
//   real_offset_from_ref: unsafe { *s.as_ptr().add(i) }   (genuine, unguarded)
//   real_offset_raw:     unsafe { *p.add(i) }             (genuine, unguarded)
use trust_types::*;
use trust_vcgen::generate_vcs;

fn sep_messages(vcs: &[VerificationCondition], tag: &str) -> Vec<String> {
    vcs.iter()
        .filter_map(|vc| match &vc.kind {
            VcKind::Assertion { message } if message.contains(tag) => Some(message.clone()),
            _ => None,
        })
        .collect()
}

fn load(json: &str) -> VerifiableFunction {
    serde_json::from_str(json).expect("fixture MIR must deserialize")
}

#[test]
fn value_add_through_a_reference_is_not_pointer_arithmetic() {
    let func = load(include_str!("fixtures/sep_value_add_closure_mir.json"));
    let vcs = generate_vcs(&func);
    let offsets = sep_messages(&vcs, "[unsafe:sep:offset]");
    assert!(
        offsets.is_empty(),
        "`tail[i] + head[i]` is an f32 addition, not a pointer offset; the closure \
         contains no unsafe operation, so it must carry no offset obligation: {offsets:#?}"
    );
}

#[test]
fn dropping_two_elements_of_one_slice_is_not_a_double_free() {
    let func = load(include_str!("fixtures/sep_slice_elem_stores_mir.json"));
    let vcs = generate_vcs(&func);
    let frees = sep_messages(&vcs, "[unsafe:sep:free]");
    assert!(
        frees.is_empty(),
        "`steps[i] = ..; steps[j] = ..` drops two distinct ELEMENTS of `*steps`, \
         not the slice's own allocation twice; safe Rust cannot double-free: {frees:#?}"
    );
}

#[test]
fn genuine_unguarded_offset_off_a_reference_is_still_refuted() {
    // SOUNDNESS: the fix must not silence a real obligation. `s.as_ptr()` IS a
    // pointer-typed destination, so the identity still propagates and the
    // unguarded `.add(i)` still carries its bounds obligation.
    let func = load(include_str!("fixtures/sep_real_offset_from_ref_mir.json"));
    let vcs = generate_vcs(&func);
    let sep = sep_messages(&vcs, "[unsafe:sep:");
    assert!(
        !sep.is_empty(),
        "an unguarded `*s.as_ptr().add(i)` must still carry an unsafe-operation \
         obligation"
    );
}

#[test]
fn genuine_unguarded_raw_pointer_offset_is_still_refuted() {
    let func = load(include_str!("fixtures/sep_real_offset_raw_mir.json"));
    let vcs = generate_vcs(&func);
    let sep = sep_messages(&vcs, "[unsafe:sep:");
    assert!(
        !sep.is_empty(),
        "an unguarded `*p.add(i)` must still carry an unsafe-operation obligation"
    );
}

// `wrapping_add` / `wrapping_offset` are SAFE: producing an out-of-allocation
// pointer with them is defined behaviour, so they must not mint an in-bounds
// `[unsafe:sep:offset]` row (measured 2026-09-24 on stage 1 `4e9fe36bf`:
// `s.as_ptr().wrapping_add(s.len() + 10)`, never dereferenced, was REFUSED
// with a FAILED offset row). They still propagate provenance and the byte
// offset, so a later dereference is checked. Fixtures (`-Ztrust-dump=mir:`):
//   sep_wrapping_add_past_end:  fn(s: &[u8]) -> *const u8 { s.as_ptr().wrapping_add(s.len() + 10) }
//   sep_wrapping_add_then_deref: fn(s: &[u8], i) -> u8 { unsafe { *s.as_ptr().wrapping_add(i) } }
//   sep_add_past_end:            fn(s: &[u8], i) -> *const u8 { unsafe { s.as_ptr().add(i) } }

#[test]
fn a_wrapping_offset_mints_no_in_bounds_row() {
    let func = load(include_str!("fixtures/sep_wrapping_add_past_end_mir.json"));
    let vcs = generate_vcs(&func);
    let offsets = sep_messages(&vcs, "[unsafe:sep:offset]");
    assert!(
        offsets.is_empty(),
        "`wrapping_add` is safe and may leave the allocation; computing the \
         pointer is not an unsafe operation: {offsets:#?}"
    );
}

#[test]
fn a_dereference_through_a_wrapping_offset_is_still_charged() {
    // SOUNDNESS: dropping the offset row must not drop the deref's own
    // obligation — the pointer is still tracked through the wrapping step.
    let func = load(include_str!("fixtures/sep_wrapping_add_then_deref_mir.json"));
    let vcs = generate_vcs(&func);
    let sep = sep_messages(&vcs, "[unsafe:sep:");
    assert!(
        !sep.is_empty(),
        "`*s.as_ptr().wrapping_add(i)` dereferences an unchecked pointer and must \
         carry an unsafe-operation obligation"
    );
}

#[test]
fn an_unsafe_add_keeps_its_in_bounds_row() {
    // Control: `add` requires the result in bounds (UB otherwise), so its row stays.
    let func = load(include_str!("fixtures/sep_add_past_end_mir.json"));
    let vcs = generate_vcs(&func);
    let offsets = sep_messages(&vcs, "[unsafe:sep:offset]");
    assert!(!offsets.is_empty(), "`s.as_ptr().add(i)` must keep its in-bounds obligation");
}
