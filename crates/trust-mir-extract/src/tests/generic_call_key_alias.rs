// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: MIT OR Apache-2.0

//! GENERIC-CALL-KEY-ALIAS-1 (2026-10-06): the call-site name of an open trait
//! dispatch from a generic body must not equal a local blanket impl's DEFINITION
//! key. Before the fix, `fn open_t<T: Tr>(x: &T) { x.m() }` was named
//! `<T as k::Tr>::m`, which is also the key of the body of
//! `impl<T: Marker> Tr for T`. Every by-name lane then took that body for the
//! call (`direct_call_def_path` residual 1). These tests pin the names only;
//! they make no claim about a proof verdict. The verdict half is
//! `tests/ui/trust/generic_call_key_alias_blanket_impl.rs`.
//!
//! GCKA-SELF-CALL-2 (2026-10-10): the tag also caught a generic trait impl's
//! direct call to ITSELF, whose name is its own body's key, and the bridge lost
//! the bind. The names now take the caller; the self-call tests below pin that a
//! self call keeps its key WITH its caller and is tagged without one. The verdict
//! half is `tests/ui/trust/generic_call_key_alias_self_call.rs`.
//!
//! CALL-REACH-1 x GCKA-SELF-CALL-2 (2026-10-10, the merge of main `6432f8a3b8`):
//! the compiler's call-reach record keys a call with no `CalleeIdentity` by its
//! NAME, and the bridge looks it up by the name the extractor stamps, so the
//! record must name the call with the same caller the extractor passes.

use super::*;

const FIXTURE_PATH: &str = "generic_call_key_alias_fixture.rs";
const CRATE_NAME: &str = "generic_call_key_alias_fixture";
const FIXTURE_SOURCE: &str = r#"
#![feature(min_specialization)]
#![allow(dead_code, private_bounds)]

trait Marker {}
trait Tr { fn m(&self) -> u32; }
impl<T: Marker> Tr for T { fn m(&self) -> u32 { 1 } }
pub struct Foo;
impl Tr for Foo { fn m(&self) -> u32 { u32::MAX } }

// The alias: the caller's own parameter is spelled `T`.
pub fn open_t<T: Tr>(x: &T) -> u32 { x.m() }
// The sound twin. Under `T: Marker` the blanket IS the target, but it prints
// byte-identically, so it pays the fail-closed cost.
pub fn sound_t<T: Marker>(x: &T) -> u32 { x.m() }
// Rename control: `<U as k::Tr>::m` is no definition key.
pub fn open_u<U: Tr>(x: &U) -> u32 { x.m() }
// Concrete control: resolves to Foo's impl, which renders the call's key.
pub fn concrete(x: &Foo) -> u32 { x.m() }

// A generic impl's call to its own sibling trait method.
trait Tr2 { fn a(&self) -> u32; fn b(&self) -> u32; }
impl<T: Marker> Tr2 for T {
    fn a(&self) -> u32 { self.b() }
    fn b(&self) -> u32 { 1 }
}

// Inherent control: the `FnDef` is the target whatever the caller.
pub struct W<X>(pub X);
impl<X> W<X> { pub fn get(&self) -> u32 { 2 } }
pub fn inherent_t<T>(w: &W<T>) -> u32 { w.get() }

// GCKA-SELF-CALL-2: a generic impl's direct call to itself, and a blanket impl's.
pub trait Depth { fn depth(&self, n: u32) -> u32; }
impl<X> Depth for W<X> {
    fn depth(&self, n: u32) -> u32 { if n == 0 { 0 } else { self.depth(n - 1) } }
}
trait Rec { fn r(&self, n: u32) -> u32; }
impl<T: Marker> Rec for T {
    fn r(&self, n: u32) -> u32 { if n == 0 { 0 } else { self.r(n - 1) } }
}
// A where-clause candidate: `try_resolve` declines it, and it runs this body.
pub trait Wc { fn wc(n: u32) -> u32 where Self: Wc; }
impl<X> Wc for W<X> {
    fn wc(n: u32) -> u32 where Self: Wc { if n == 0 { 0 } else { <W<X> as Wc>::wc(n - 1) } }
}
// A specializable `default fn`, and the impl that specializes it. `V<u8>` never
// runs the default body, so the default body's self call runs the default body.
pub struct V<X>(pub X);
pub trait Spec { fn s(&self, n: u32) -> u32; }
impl<X> Spec for V<X> {
    default fn s(&self, n: u32) -> u32 { if n == 0 { 0 } else { self.s(n - 1) } }
}
impl Spec for V<u8> {
    fn s(&self, n: u32) -> u32 { if n == 0 { 7 } else { V(0u8).s(n - 1) } }
}
// A generic impl's call to the SAME trait item at another self type is no self
// call. It prints `Inner`'s key (the parameter is spelled `X` in both impls) and
// runs `Inner`'s body, but its target is not its caller, so it stays tagged.
pub struct Outer<X>(pub Inner<X>);
pub struct Inner<X>(pub X);
pub trait Fwd { fn fwd(&self) -> u32; }
impl<X> Fwd for Inner<X> { fn fwd(&self) -> u32 { 3 } }
impl<X> Fwd for Outer<X> { fn fwd(&self) -> u32 { self.0.fwd() } }

// CALL-REACH-1 x GCKA-SELF-CALL-2: a generic impl of a SYSROOT trait whose item
// calls itself. Its callee is core's trait item, which the compiler's call-reach
// record judges, and its arguments name `X`, so it has no `CalleeIdentity`.
pub struct Sh<X>(pub X);
impl<X> core::ops::Shl<u32> for Sh<X> {
    type Output = u32;
    fn shl(self, n: u32) -> u32 { if n == 0 { 0 } else { self << (n - 1) } }
}
"#;

struct FixtureFileLoader;

impl rustc_span::source_map::FileLoader for FixtureFileLoader {
    fn file_exists(&self, path: &Path) -> bool {
        path == Path::new(FIXTURE_PATH)
    }

    fn read_file(&self, path: &Path) -> io::Result<String> {
        if self.file_exists(path) {
            Ok(FIXTURE_SOURCE.into())
        } else {
            Err(io::Error::other("unexpected generic call-key alias fixture path"))
        }
    }

    fn read_binary_file(&self, _path: &Path) -> io::Result<Arc<[u8]>> {
        Err(io::Error::other("binary source reads are not supported in alias fixture"))
    }

    fn current_directory(&self) -> io::Result<PathBuf> {
        std::env::current_dir()
    }
}

/// How the call resolves under the CALLER's own typing environment: the
/// discriminator the naming seam does not have.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Resolution {
    Error,
    Open,
    Item(DefId),
    Other,
}

struct CallRecord {
    /// `func_operand_name` with the caller passed, the name every by-name lane sees.
    name: String,
    /// `func_operand_name` with NO caller (GCKA-SELF-CALL-2): what every lane saw
    /// before the caller was passed.
    name_without_caller: String,
    /// The plain render (`direct_call_def_path` over `safe_def_path_str_with_args`),
    /// i.e. the spelling before the alias tag.
    direct: String,
    resolution: Resolution,
    /// `callee_identity_for` over the call's `(DefId, args)`: the key the
    /// compiler's call-reach record and the bridge use when there is one.
    identity: Option<trust_types::CalleeIdentity>,
    /// The crate of the callee `DefId` (the trait item for a trait call).
    callee_crate: String,
    /// The `func` the extractor stamps on this call's `Terminator::Call`
    /// (`extract_function` over the same body). Read for the `shl` body only.
    extracted: Option<String>,
}

#[derive(Default)]
struct Fixture {
    /// Caller label -> its one selected call. The label is the item name, or the
    /// definition key for a trait impl item (two of them may share a name).
    calls: BTreeMap<String, CallRecord>,
    /// Every local fn body's definition key -> its `DefId`.
    keys: BTreeMap<String, DefId>,
}

#[derive(Default)]
struct AliasCallbacks {
    fixture: Fixture,
}

impl rustc_driver::Callbacks for AliasCallbacks {
    fn config(&mut self, config: &mut Config) {
        config.file_loader = Some(Box::new(FixtureFileLoader));
    }

    fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        tcx.sess.dcx().abort_if_errors();
        for owner in tcx.hir_body_owners() {
            let did = owner.to_def_id();
            if !matches!(
                tcx.def_kind(did),
                rustc_hir::def::DefKind::Fn | rustc_hir::def::DefKind::AssocFn
            ) {
                continue;
            }
            assert!(
                self.fixture.keys.insert(crate::safe_def_path_str(tcx, did), did).is_none(),
                "every fixture body renders its own definition key"
            );
            let Some(name) = tcx.opt_item_name(did) else { continue };
            let (label, leaf) = match name.as_str() {
                "open_t" | "sound_t" | "open_u" | "concrete" => (name.to_string(), "m"),
                "a" => (name.to_string(), "b"),
                "inherent_t" => (name.to_string(), "get"),
                "depth" | "r" | "wc" | "s" | "fwd" => {
                    (crate::safe_def_path_str(tcx, did), name.as_str())
                }
                "shl" => (name.to_string(), "shl"),
                _ => continue,
            };
            let body = tcx.optimized_mir(did);
            let extracted = (leaf == "shl").then(|| crate::extract_function(tcx, body));
            let calls = body
                .basic_blocks
                .iter_enumerated()
                .filter_map(|(block, data)| {
                    let mir::TerminatorKind::Call { func, .. } = &data.terminator().kind else {
                        return None;
                    };
                    let (callee, generic_args) = func.const_fn_def()?;
                    if tcx.item_name(callee).as_str() != leaf {
                        return None;
                    }
                    let direct = crate::convert::direct_call_def_path(
                        tcx,
                        callee,
                        generic_args,
                        crate::safe_def_path_str_with_args(tcx, callee, generic_args),
                    );
                    let resolution = match ty::Instance::try_resolve(
                        tcx,
                        body.typing_env(tcx),
                        callee,
                        generic_args,
                    ) {
                        Err(_) => Resolution::Error,
                        Ok(None) => Resolution::Open,
                        Ok(Some(instance)) => match instance.def {
                            ty::InstanceKind::Item(item) => Resolution::Item(item),
                            _ => Resolution::Other,
                        },
                    };
                    let extracted = extracted.as_ref().map(|function| {
                        let terminator = &function
                            .body
                            .blocks
                            .iter()
                            .find(|entry| entry.id == BlockId(block.as_usize()))
                            .expect("the extraction keeps the MIR block")
                            .terminator;
                        let Terminator::Call { func, .. } = terminator else {
                            panic!("the extracted `shl` call stays a Call: {terminator:?}");
                        };
                        func.clone()
                    });
                    Some(CallRecord {
                        name: crate::convert::func_operand_name_in_body(tcx, body, func),
                        name_without_caller: crate::convert::func_operand_name(tcx, None, func),
                        direct,
                        resolution,
                        identity: crate::convert::callee_identity_for(tcx, callee, generic_args),
                        callee_crate: tcx.crate_name(callee.krate).to_string(),
                        extracted,
                    })
                })
                .collect::<Vec<_>>();
            if leaf == "fwd" && calls.is_empty() {
                // `Inner`'s `fwd` calls nothing; `Outer`'s is the one selected.
                continue;
            }
            assert_eq!(calls.len(), 1, "`{label}` keeps exactly one `{leaf}` call");
            let record = calls.into_iter().next().expect("one call");
            assert!(self.fixture.calls.insert(label, record).is_none());
        }
        Compilation::Stop
    }
}

fn compile_fixture() -> Fixture {
    let mut callbacks = AliasCallbacks::default();
    let args = vec![
        "rustc".into(),
        FIXTURE_PATH.into(),
        "--crate-name".into(),
        CRATE_NAME.into(),
        "--crate-type=lib".into(),
        "--edition=2021".into(),
        "-Zmir-opt-level=0".into(),
        "-Zinline-mir=no".into(),
        "-Zno-codegen".into(),
        "-Zcodegen-backend=dummy".into(),
        "--sysroot".into(),
        compiler_sysroot(),
    ];
    let result = rustc_driver::catch_fatal_errors(|| -> rustc_interface::interface::Result<()> {
        rustc_driver::run_compiler(&args, &mut callbacks);
        Ok(())
    });
    assert!(result.is_ok(), "failed to compile the generic call-key alias fixture");
    let mut expected = ["a", "concrete", "inherent_t", "open_t", "open_u", "shl", "sound_t"]
        .map(String::from)
        .to_vec();
    expected.extend([
        depth_key(),
        rec_key(),
        wc_key(),
        spec_default_key(),
        spec_u8_key(),
        format!("<{CRATE_NAME}::Outer<X> as {CRATE_NAME}::Fwd>::fwd"),
    ]);
    expected.sort();
    assert_eq!(callbacks.fixture.calls.keys().cloned().collect::<Vec<_>>(), expected);
    callbacks.fixture
}

fn depth_key() -> String {
    format!("<{CRATE_NAME}::W<X> as {CRATE_NAME}::Depth>::depth")
}

fn rec_key() -> String {
    format!("<T as {CRATE_NAME}::Rec>::r")
}

fn wc_key() -> String {
    format!("<{CRATE_NAME}::W<X> as {CRATE_NAME}::Wc>::wc")
}

fn spec_default_key() -> String {
    format!("<{CRATE_NAME}::V<X> as {CRATE_NAME}::Spec>::s")
}

fn spec_u8_key() -> String {
    format!("<{CRATE_NAME}::V<u8> as {CRATE_NAME}::Spec>::s")
}

fn blanket_m_key() -> String {
    format!("<T as {CRATE_NAME}::Tr>::m")
}

fn assert_alias_tagged(record: &CallRecord, key: &str) {
    assert_name_alias_tagged(&record.name, key);
}

fn assert_name_alias_tagged(name: &str, key: &str) {
    assert_ne!(name, key, "the call must not wear the body's definition key");
    let tag = name
        .strip_prefix(key)
        .unwrap_or_else(|| panic!("`{name}` keeps its rendered prefix `{key}`"));
    assert!(
        tag.starts_with("::<__trust_alias@") && tag.ends_with('>'),
        "`{name}` carries the non-source-spellable alias tag"
    );
}

/// The lie, closed. The render still aliases (`direct` IS the blanket body's key,
/// and the dispatch is open under the caller's env), but the name every lane
/// sees is tagged, so no lane can match the call to that body. Fails before the
/// fix: the name was returned unchanged.
#[test]
fn an_open_dispatch_spelled_like_a_blanket_impl_key_is_tagged() {
    let fixture = compile_fixture();
    let key = blanket_m_key();
    assert!(fixture.keys.contains_key(&key), "the blanket impl's `m` renders `{key}`");
    let open = &fixture.calls["open_t"];
    assert_eq!(open.direct, key, "precondition: the render aliases the blanket body");
    assert_eq!(open.resolution, Resolution::Open, "`T: Tr` leaves the dispatch open");
    assert_alias_tagged(open, &key);
}

/// The measured capability cost. The sound twin resolves to the blanket body
/// under its OWN env, which a caller-aware resolution could use to keep the name
/// (the recorded follow-up). The seam has the caller since GCKA-SELF-CALL-2, but
/// it keeps a name only for a direct self call, so this is tagged too. So is a
/// generic impl's call to its own sibling trait method.
#[test]
fn the_sound_twin_and_a_sibling_call_pay_the_fail_closed_cost() {
    let fixture = compile_fixture();
    let key = blanket_m_key();
    let sound = &fixture.calls["sound_t"];
    assert_eq!(sound.direct, key);
    assert_eq!(sound.resolution, Resolution::Item(fixture.keys[&key]));
    assert_alias_tagged(sound, &key);

    let sibling_key = format!("<T as {CRATE_NAME}::Tr2>::b");
    assert!(fixture.keys.contains_key(&sibling_key));
    let sibling = &fixture.calls["a"];
    assert_eq!(sibling.direct, sibling_key);
    assert_alias_tagged(sibling, &sibling_key);
}

/// Controls that keep their names: a parameter spelling that is no definition
/// key, a concrete call that resolves to the body it names, and an inherent call
/// from a generic body (its `FnDef` is its target).
#[test]
fn calls_that_reach_or_name_no_local_body_keep_their_names() {
    let fixture = compile_fixture();
    let open_u = &fixture.calls["open_u"];
    assert_eq!(open_u.direct, format!("<U as {CRATE_NAME}::Tr>::m"));
    assert!(!fixture.keys.contains_key(&open_u.direct));
    assert_eq!(open_u.name, open_u.direct);

    let foo_key = format!("<{CRATE_NAME}::Foo as {CRATE_NAME}::Tr>::m");
    let concrete = &fixture.calls["concrete"];
    assert_eq!(concrete.resolution, Resolution::Item(fixture.keys[&foo_key]));
    assert_eq!(concrete.name, foo_key);

    let inherent = &fixture.calls["inherent_t"];
    assert!(!inherent.name.contains("__trust_alias"), "`{}` is untagged", inherent.name);
}

/// GCKA-SELF-CALL-2. A generic impl's direct call to ITSELF, a blanket impl's,
/// one through a where-clause candidate, and a specializable `default fn`'s each
/// keep their own body's key when the caller is passed, and each is tagged
/// without it (the wave-20 name, which cost the bridge its bind). Fails before
/// the fix (with `identity_self_call_of_caller` answering `None`): every `name`
/// below is tagged.
#[test]
fn a_generic_impls_direct_self_call_keeps_its_own_key_with_its_caller() {
    let fixture = compile_fixture();
    for key in [depth_key(), rec_key(), wc_key(), spec_default_key()] {
        let record = &fixture.calls[&key];
        assert_eq!(record.direct, key, "precondition: the self call renders its own key");
        assert_eq!(record.name, key, "the self call keeps its body's key");
        assert_name_alias_tagged(&record.name_without_caller, &key);
    }
    // What rustc's own resolution says, under the caller's env: an item for the
    // two impl candidates, nothing for the where-clause candidate and the
    // specializable default. The identity reading holds for all four.
    assert_eq!(
        fixture.calls[&depth_key()].resolution,
        Resolution::Item(fixture.keys[&depth_key()])
    );
    assert_eq!(fixture.calls[&rec_key()].resolution, Resolution::Item(fixture.keys[&rec_key()]));
    assert_eq!(fixture.calls[&wc_key()].resolution, Resolution::Open);
    assert_eq!(fixture.calls[&spec_default_key()].resolution, Resolution::Open);
}

/// The caller does not reopen the alias. The open dispatch, the sound twin, the
/// sibling call and a call to the same trait item at another self type stay
/// tagged WITH their callers: none is a trait impl item's call to the item it
/// implements at its own arguments. A concrete self call keeps its key whatever
/// the caller.
#[test]
fn the_caller_keeps_every_other_call_on_its_wave_20_name() {
    let fixture = compile_fixture();
    let key = blanket_m_key();
    for label in ["open_t", "sound_t"] {
        let record = &fixture.calls[label];
        assert_eq!(record.name, record.name_without_caller);
        assert_alias_tagged(record, &key);
    }
    let sibling = &fixture.calls["a"];
    assert_eq!(sibling.name, sibling.name_without_caller);
    assert_alias_tagged(sibling, &format!("<T as {CRATE_NAME}::Tr2>::b"));

    let outer = &fixture.calls[&format!("<{CRATE_NAME}::Outer<X> as {CRATE_NAME}::Fwd>::fwd")];
    assert_eq!(outer.name, outer.name_without_caller);
    assert_alias_tagged(outer, &format!("<{CRATE_NAME}::Inner<X> as {CRATE_NAME}::Fwd>::fwd"));

    let concrete = &fixture.calls[&spec_u8_key()];
    assert_eq!(concrete.name, spec_u8_key());
    assert_eq!(concrete.name_without_caller, spec_u8_key());
}

/// CALL-REACH-1 x GCKA-SELF-CALL-2 (2026-10-10, the merge of main `6432f8a3b8`).
/// `record_body_call_reach` (rustc_mir_transform) withdraws an open call under its
/// `CalleeIdentity`, or under its NAME when it has none, and the bridge's lookup
/// uses what the extractor stamps on the same call. A generic impl of a sysroot
/// trait whose item calls itself is judged by that record (its callee is core's
/// trait item) and has no identity (its arguments name `X`), so the name is the
/// key, and it is exactly the name the caller decides: with the body's own item,
/// as `extract_body` passes it, it keeps its definition key; with `None` it is
/// tagged, a key no extracted call carries. So the record names the call with
/// `func_operand_name_in_body`, never with `None`.
#[test]
fn a_sysroot_trait_self_call_is_keyed_by_the_name_its_caller_gives_it() {
    let fixture = compile_fixture();
    let record = &fixture.calls["shl"];
    assert_eq!(record.callee_crate, "core", "precondition: the callee is core's trait item");
    assert_eq!(record.identity, None, "a call at the caller's parameter has no identity");
    assert!(
        fixture.keys.contains_key(&record.direct),
        "precondition: the self call `{}` renders its own body's definition key",
        record.direct
    );
    // `call_site_reach`'s step 1 judges a sysroot `FnDef` whose instance resolves,
    // under the body's own environment, to something other than a virtual call.
    assert_eq!(
        record.resolution,
        Resolution::Item(fixture.keys[&record.direct]),
        "precondition: the call resolves to its own body, so the record judges it"
    );
    assert_eq!(record.name, record.direct, "with its caller it keeps that key");
    assert_eq!(
        record.extracted.as_deref(),
        Some(record.name.as_str()),
        "the extractor stamps the name taken with the body's own item"
    );
    assert_name_alias_tagged(&record.name_without_caller, &record.direct);
}
