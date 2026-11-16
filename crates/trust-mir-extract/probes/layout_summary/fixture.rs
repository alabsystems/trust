//! Adversarial ordinary Rust types for one invocation-local layout-safety walk.
//! No layout is requested and no byte offset or source authority is supplied.
#![feature(type_alias_impl_trait, pattern_types, pattern_type_macro)]
#![allow(dead_code)]

pub type Hidden = impl Copy;
#[define_opaque(Hidden)]
pub fn define_hidden() -> Hidden {
    0u8
}

pub struct Leaf(pub u64);
pub struct Recursive {
    pub next: *const Recursive,
    pub leaf: Leaf,
}
pub struct A(pub Recursive);
pub struct B(pub A);
pub struct C(pub B);
pub struct D(pub C);
pub struct E(pub D);
// The later Recursive arrives at depth6. Its earlier independently complete
// exact-type proof may be reused; this is the legitimate admission target.
pub struct ClosedReuse {
    pub earlier: Recursive,
    pub later: E,
}
pub fn case_closed_reuse(_: &ClosedReuse) {}

pub struct Generic<T> {
    pub next: *const Generic<T>,
    pub payload: T,
}
pub struct DistinctArgs {
    pub safe: Generic<u64>,
    pub unsafe_: Generic<Hidden>,
}
pub fn case_distinct_args(_: &DistinctArgs) {}

pub struct UnsafeParent {
    pub recursive: *const UnsafeChild,
    pub unsafe_: Hidden,
}
pub struct UnsafeChild {
    pub parent: *const UnsafeParent,
}
pub fn case_unsafe_parent(_: &UnsafeParent) {}
pub fn case_unsafe_child(_: &UnsafeChild) {}

pub struct Outer {
    pub first: ConditionalChild,
    pub later: OuterE,
}
pub struct ConditionalChild {
    pub parent: *const Outer,
}
pub struct OuterA(pub ConditionalChild);
pub struct OuterB(pub OuterA);
pub struct OuterC(pub OuterB);
pub struct OuterD(pub OuterC);
pub struct OuterE(pub OuterD);
// The first child's success depends on the OUTER active ancestor. If cached as
// closed, its later depth6 occurrence would bypass the unchanged depth cap.
pub fn case_outer_dependent(_: &Outer) {}

pub struct Deep0(pub u64);
pub struct Deep1(pub Deep0);
pub struct Deep2(pub Deep1);
pub struct Deep3(pub Deep2);
pub struct Deep4(pub Deep3);
pub struct Deep5(pub Deep4);
pub struct Deep6(pub Deep5);
pub struct Deep7(pub Deep6);
pub fn case_depth_fallback(_: &Deep7) {}
pub fn case_short(_: &Deep2) {}

pub const fn calls_mir_body() -> usize {
    4
}
pub struct NonLeafCtfe(pub [u8; calls_mir_body()]);
pub fn case_nonleaf_ctfe(_: &NonLeafCtfe) {}
pub struct OpaqueField(pub Hidden);
pub fn case_opaque(_: &OpaqueField) {}
pub fn case_generic<T>(_: &Generic<T>) {}
pub fn case_bound<'a>(_: &'a u8) {}
pub struct Hrtb(pub for<'a> fn(&'a u8));
pub fn case_hrtb(_: &Hrtb) {}

pub struct Marker<const N: usize>(pub u8);

// More distinct completed keys than the bounded cache can retain.
pub struct CapSafe {
    pub f0: Marker<0>,
    pub f1: Marker<1>,
    pub f2: Marker<2>,
    pub f3: Marker<3>,
    pub f4: Marker<4>,
    pub f5: Marker<5>,
    pub f6: Marker<6>,
    pub f7: Marker<7>,
    pub f8: Marker<8>,
    pub f9: Marker<9>,
    pub f10: Marker<10>,
    pub f11: Marker<11>,
    pub f12: Marker<12>,
    pub f13: Marker<13>,
    pub f14: Marker<14>,
    pub f15: Marker<15>,
    pub f16: Marker<16>,
    pub f17: Marker<17>,
    pub f18: Marker<18>,
    pub f19: Marker<19>,
    pub f20: Marker<20>,
    pub f21: Marker<21>,
    pub f22: Marker<22>,
    pub f23: Marker<23>,
    pub f24: Marker<24>,
    pub f25: Marker<25>,
    pub f26: Marker<26>,
    pub f27: Marker<27>,
    pub f28: Marker<28>,
    pub f29: Marker<29>,
    pub f30: Marker<30>,
    pub f31: Marker<31>,
    pub f32: Marker<32>,
    pub f33: Marker<33>,
    pub f34: Marker<34>,
    pub f35: Marker<35>,
    pub f36: Marker<36>,
    pub f37: Marker<37>,
    pub f38: Marker<38>,
    pub f39: Marker<39>,
    pub f40: Marker<40>,
    pub f41: Marker<41>,
    pub f42: Marker<42>,
    pub f43: Marker<43>,
    pub f44: Marker<44>,
    pub f45: Marker<45>,
    pub f46: Marker<46>,
    pub f47: Marker<47>,
    pub f48: Marker<48>,
    pub f49: Marker<49>,
    pub f50: Marker<50>,
    pub f51: Marker<51>,
    pub f52: Marker<52>,
    pub f53: Marker<53>,
    pub f54: Marker<54>,
    pub f55: Marker<55>,
    pub f56: Marker<56>,
    pub f57: Marker<57>,
    pub f58: Marker<58>,
    pub f59: Marker<59>,
    pub f60: Marker<60>,
    pub f61: Marker<61>,
    pub f62: Marker<62>,
    pub f63: Marker<63>,
    pub f64: Marker<64>,
    pub f65: Marker<65>,
    pub f66: Marker<66>,
    pub f67: Marker<67>,
    pub f68: Marker<68>,
    pub f69: Marker<69>,
    pub f70: Marker<70>,
    pub f71: Marker<71>,
    pub f72: Marker<72>,
    pub f73: Marker<73>,
    pub f74: Marker<74>,
    pub f75: Marker<75>,
    pub f76: Marker<76>,
    pub f77: Marker<77>,
    pub f78: Marker<78>,
    pub f79: Marker<79>,
    pub f80: Marker<80>,
    pub f81: Marker<81>,
    pub f82: Marker<82>,
    pub f83: Marker<83>,
    pub f84: Marker<84>,
    pub f85: Marker<85>,
    pub f86: Marker<86>,
    pub f87: Marker<87>,
    pub f88: Marker<88>,
    pub f89: Marker<89>,
    pub f90: Marker<90>,
    pub f91: Marker<91>,
    pub f92: Marker<92>,
    pub f93: Marker<93>,
    pub f94: Marker<94>,
    pub f95: Marker<95>,
    pub f96: Marker<96>,
    pub f97: Marker<97>,
    pub f98: Marker<98>,
    pub f99: Marker<99>,
    pub f100: Marker<100>,
    pub f101: Marker<101>,
    pub f102: Marker<102>,
    pub f103: Marker<103>,
    pub f104: Marker<104>,
    pub f105: Marker<105>,
    pub f106: Marker<106>,
    pub f107: Marker<107>,
    pub f108: Marker<108>,
    pub f109: Marker<109>,
    pub f110: Marker<110>,
    pub f111: Marker<111>,
    pub f112: Marker<112>,
    pub f113: Marker<113>,
    pub f114: Marker<114>,
    pub f115: Marker<115>,
    pub f116: Marker<116>,
    pub f117: Marker<117>,
    pub f118: Marker<118>,
    pub f119: Marker<119>,
    pub f120: Marker<120>,
    pub f121: Marker<121>,
    pub f122: Marker<122>,
    pub f123: Marker<123>,
    pub f124: Marker<124>,
    pub f125: Marker<125>,
    pub f126: Marker<126>,
    pub f127: Marker<127>,
    pub f128: Marker<128>,
    pub f129: Marker<129>,
    pub f130: Marker<130>,
    pub f131: Marker<131>,
    pub f132: Marker<132>,
    pub f133: Marker<133>,
    pub f134: Marker<134>,
    pub f135: Marker<135>,
    pub f136: Marker<136>,
    pub f137: Marker<137>,
    pub f138: Marker<138>,
    pub f139: Marker<139>,
    pub f140: Marker<140>,
    pub f141: Marker<141>,
    pub f142: Marker<142>,
    pub f143: Marker<143>,
    pub f144: Marker<144>,
    pub f145: Marker<145>,
    pub f146: Marker<146>,
    pub f147: Marker<147>,
    pub f148: Marker<148>,
    pub f149: Marker<149>,
    pub f150: Marker<150>,
    pub f151: Marker<151>,
    pub f152: Marker<152>,
    pub f153: Marker<153>,
    pub f154: Marker<154>,
    pub f155: Marker<155>,
    pub f156: Marker<156>,
    pub f157: Marker<157>,
    pub f158: Marker<158>,
    pub f159: Marker<159>,
    pub f160: Marker<160>,
    pub f161: Marker<161>,
    pub f162: Marker<162>,
    pub f163: Marker<163>,
    pub f164: Marker<164>,
    pub f165: Marker<165>,
    pub f166: Marker<166>,
    pub f167: Marker<167>,
    pub f168: Marker<168>,
    pub f169: Marker<169>,
    pub f170: Marker<170>,
    pub f171: Marker<171>,
    pub f172: Marker<172>,
    pub f173: Marker<173>,
    pub f174: Marker<174>,
    pub f175: Marker<175>,
    pub f176: Marker<176>,
    pub f177: Marker<177>,
    pub f178: Marker<178>,
    pub f179: Marker<179>,
    pub f180: Marker<180>,
    pub f181: Marker<181>,
    pub f182: Marker<182>,
    pub f183: Marker<183>,
    pub f184: Marker<184>,
    pub f185: Marker<185>,
    pub f186: Marker<186>,
    pub f187: Marker<187>,
    pub f188: Marker<188>,
    pub f189: Marker<189>,
    pub f190: Marker<190>,
    pub f191: Marker<191>,
    pub f192: Marker<192>,
    pub f193: Marker<193>,
    pub f194: Marker<194>,
    pub f195: Marker<195>,
    pub f196: Marker<196>,
    pub f197: Marker<197>,
    pub f198: Marker<198>,
    pub f199: Marker<199>,
    pub f200: Marker<200>,
    pub f201: Marker<201>,
    pub f202: Marker<202>,
    pub f203: Marker<203>,
    pub f204: Marker<204>,
    pub f205: Marker<205>,
    pub f206: Marker<206>,
    pub f207: Marker<207>,
    pub f208: Marker<208>,
    pub f209: Marker<209>,
    pub f210: Marker<210>,
    pub f211: Marker<211>,
    pub f212: Marker<212>,
    pub f213: Marker<213>,
    pub f214: Marker<214>,
    pub f215: Marker<215>,
    pub f216: Marker<216>,
    pub f217: Marker<217>,
    pub f218: Marker<218>,
    pub f219: Marker<219>,
    pub f220: Marker<220>,
    pub f221: Marker<221>,
    pub f222: Marker<222>,
    pub f223: Marker<223>,
    pub f224: Marker<224>,
    pub f225: Marker<225>,
    pub f226: Marker<226>,
    pub f227: Marker<227>,
    pub f228: Marker<228>,
    pub f229: Marker<229>,
    pub f230: Marker<230>,
    pub f231: Marker<231>,
    pub f232: Marker<232>,
    pub f233: Marker<233>,
    pub f234: Marker<234>,
    pub f235: Marker<235>,
    pub f236: Marker<236>,
    pub f237: Marker<237>,
    pub f238: Marker<238>,
    pub f239: Marker<239>,
    pub f240: Marker<240>,
    pub f241: Marker<241>,
    pub f242: Marker<242>,
    pub f243: Marker<243>,
    pub f244: Marker<244>,
    pub f245: Marker<245>,
    pub f246: Marker<246>,
    pub f247: Marker<247>,
    pub f248: Marker<248>,
    pub f249: Marker<249>,
    pub f250: Marker<250>,
    pub f251: Marker<251>,
    pub f252: Marker<252>,
    pub f253: Marker<253>,
    pub f254: Marker<254>,
    pub f255: Marker<255>,
    pub f256: Marker<256>,
    pub f257: Marker<257>,
    pub f258: Marker<258>,
    pub f259: Marker<259>,
    pub f260: Marker<260>,
    pub f261: Marker<261>,
    pub f262: Marker<262>,
    pub f263: Marker<263>,
    pub f264: Marker<264>,
    pub f265: Marker<265>,
    pub f266: Marker<266>,
    pub f267: Marker<267>,
    pub f268: Marker<268>,
    pub f269: Marker<269>,
    pub f270: Marker<270>,
    pub f271: Marker<271>,
    pub f272: Marker<272>,
    pub f273: Marker<273>,
    pub f274: Marker<274>,
    pub f275: Marker<275>,
    pub f276: Marker<276>,
    pub f277: Marker<277>,
    pub f278: Marker<278>,
    pub f279: Marker<279>,
    pub f280: Marker<280>,
    pub f281: Marker<281>,
    pub f282: Marker<282>,
    pub f283: Marker<283>,
    pub f284: Marker<284>,
    pub f285: Marker<285>,
    pub f286: Marker<286>,
    pub f287: Marker<287>,
    pub f288: Marker<288>,
    pub f289: Marker<289>,
    pub f290: Marker<290>,
    pub f291: Marker<291>,
    pub f292: Marker<292>,
    pub f293: Marker<293>,
    pub f294: Marker<294>,
    pub f295: Marker<295>,
    pub f296: Marker<296>,
    pub f297: Marker<297>,
    pub f298: Marker<298>,
    pub f299: Marker<299>,
}
pub fn case_cap_safe(_: &CapSafe) {}
pub struct CapUnsafe {
    pub completed: CapSafe,
    pub unsafe_: Hidden,
}
pub fn case_cap_unsafe(_: &CapUnsafe) {}

// Associated-type selection must receive only independently closed exact facts.
pub trait Pick {
    type Out;
}
impl<T> Pick for Generic<T> {
    type Out = u8;
}
pub struct Projection<T: Pick>(pub T::Out);
pub struct ProjectionA<T: Pick>(pub Projection<T>);
pub struct ProjectionB<T: Pick>(pub ProjectionA<T>);
pub struct ProjectionC<T: Pick>(pub ProjectionB<T>);
pub struct ProjectionD<T: Pick>(pub ProjectionC<T>);
pub struct ProjectionReuse {
    pub earlier: Generic<u64>,
    pub later: ProjectionD<Generic<u64>>,
}
pub fn case_projection_reuse(_: &ProjectionReuse) {}
pub struct ProjectionDifferentArgs {
    pub earlier: Generic<u64>,
    pub later: ProjectionD<Generic<Hidden>>,
}
pub fn case_projection_distinct_args(_: &ProjectionDifferentArgs) {}

// Layout may be closed even when a phantom argument is unsuitable for selection.
pub struct Carrier<T: ?Sized>(pub std::marker::PhantomData<T>);
impl<T: ?Sized> Pick for Carrier<T> {
    type Out = u8;
}
macro_rules! projection_case {
    ($root:ident, $case:ident, $input:ty) => {
        pub struct $root {
            pub earlier: $input,
            pub later: ProjectionD<$input>,
        }
        pub fn $case(_: &$root) {}
    };
}
projection_case!(PhantomFunction, case_phantom_function, Carrier<fn(u8) -> u8>);
projection_case!(PhantomDynamic, case_phantom_dynamic, Carrier<dyn Send>);
projection_case!(PhantomOpaque, case_phantom_opaque, Carrier<Hidden>);

pub struct ConstCarrier<const N: usize>;
impl<const N: usize> Pick for ConstCarrier<N> {
    type Out = u8;
}
projection_case!(NonLeafConstArg, case_nonleaf_const_argument, ConstCarrier<{ calls_mir_body() }>);

pub union UnionInput {
    pub byte: u8,
    pub word: u64,
}
impl Pick for UnionInput {
    type Out = u8;
}
projection_case!(UnionProjection, case_union_projection, UnionInput);

pub struct WhereInput<T>(pub std::marker::PhantomData<T>);
impl<T> Pick for WhereInput<T>
where
    Hidden: Copy,
{
    type Out = u8;
}
projection_case!(OpaqueWhere, case_opaque_where, WhereInput<u8>);

// A DefId-only recursive shortcut must not establish exact closed facts for
// successively growing instantiations, even though their pointer layout is finite.
pub struct Growing<T> {
    pub next: *const Growing<(T,)>,
    pub marker: std::marker::PhantomData<T>,
}
impl<T> Pick for Growing<T> {
    type Out = u8;
}
projection_case!(GrowingProjection, case_growing_projection, Growing<u8>);

extern crate layout_summary_foreign;
impl Pick for layout_summary_foreign::ForeignOpaque {
    type Out = u8;
}
projection_case!(
    ForeignOpaqueProjection,
    case_foreign_opaque_projection,
    layout_summary_foreign::ForeignOpaque
);

projection_case!(PhantomPlain, case_phantom_plain_projection, Carrier<u8>);
projection_case!(ValueConstArg, case_value_const_projection, ConstCarrier<7>);

// Supported boundary: ProjectionC is field depth4, so its associated-type field
// reaches reader depth5 and the argument walk carries depth6. ProjectionD above
// deliberately retains the original depth6 reader refusal.
macro_rules! supported_projection_case {
    ($root:ident, $case:ident, $input:ty) => {
        pub struct $root {
            pub earlier: $input,
            pub later: ProjectionC<$input>,
        }
        pub fn $case(_: &$root) {}
    };
}
supported_projection_case!(SupportedRecursive, case_supported_recursive, Generic<u64>);
supported_projection_case!(SupportedPlain, case_supported_plain, Carrier<u8>);
supported_projection_case!(SupportedConst, case_supported_const, ConstCarrier<7>);
supported_projection_case!(SupportedFunction, case_supported_function, Carrier<fn(u8) -> u8>);
supported_projection_case!(SupportedDynamic, case_supported_dynamic, Carrier<dyn Send>);
supported_projection_case!(SupportedOpaque, case_supported_opaque, Carrier<Hidden>);
supported_projection_case!(SupportedCtfe, case_supported_ctfe, ConstCarrier<{ calls_mir_body() }>);
supported_projection_case!(SupportedUnion, case_supported_union, UnionInput);
supported_projection_case!(SupportedWhere, case_supported_where, WhereInput<u8>);
supported_projection_case!(SupportedGrowing, case_supported_growing, Growing<u8>);
supported_projection_case!(
    SupportedForeign,
    case_supported_foreign,
    layout_summary_foreign::ForeignOpaque
);

pub trait LiteralStorage {
    type Out;
}
impl LiteralStorage for u8 {
    type Out = [u8; 2];
}
pub trait NamedStorage {
    type Out;
}
pub const WRITTEN_LENGTH: usize = 2;
impl NamedStorage for u8 {
    type Out = [u8; WRITTEN_LENGTH];
}
pub struct LiteralLengthInput {
    pub field: <u8 as LiteralStorage>::Out,
}
pub struct NamedLengthInput {
    pub field: <u8 as NamedStorage>::Out,
}
impl Pick for LiteralLengthInput {
    type Out = u8;
}
impl Pick for NamedLengthInput {
    type Out = u8;
}
pub fn case_literal_length_input(_: &LiteralLengthInput) {}
pub fn case_named_length_input(_: &NamedLengthInput) {}
supported_projection_case!(
    LiteralLengthProjection,
    case_literal_length_projection,
    LiteralLengthInput
);
supported_projection_case!(NamedLengthProjection, case_named_length_projection, NamedLengthInput);

pub struct ForeignCopyInput {
    pub field: <u8 as layout_summary_foreign::PrimitiveStorage>::Out,
}
pub struct ForeignOpaqueBoundInput {
    pub field: <u8 as layout_summary_foreign::OpaqueStorage>::Out,
}
pub struct ForeignNominalBoundInput {
    pub field: <layout_summary_foreign::Nominal as layout_summary_foreign::NominalStorage>::Out,
}
pub struct NonNullInput {
    pub field: std::ptr::NonNull<u8>,
}
pub struct RangeInput {
    pub field: std::pat::pattern_type!(u8 is 1..=7),
}
pub struct OrInput {
    pub field: std::pat::pattern_type!(i8 is ..=-1 | 1..),
}
macro_rules! input_pick {
    ($($input:ty),*) => { $(impl Pick for $input { type Out = u8; })* };
}
input_pick!(
    ForeignCopyInput,
    ForeignOpaqueBoundInput,
    ForeignNominalBoundInput,
    NonNullInput,
    RangeInput,
    OrInput
);
supported_projection_case!(ForeignCopyProjection, case_foreign_copy_projection, ForeignCopyInput);
supported_projection_case!(
    ForeignOpaqueBoundProjection,
    case_foreign_opaque_bound_projection,
    ForeignOpaqueBoundInput
);
supported_projection_case!(
    ForeignNominalBoundProjection,
    case_foreign_nominal_bound_projection,
    ForeignNominalBoundInput
);
supported_projection_case!(NonNullProjection, case_nonnull_projection, NonNullInput);
supported_projection_case!(RangeProjection, case_range_projection, RangeInput);
supported_projection_case!(OrProjection, case_or_projection, OrInput);
