//@ revisions: quiet control
//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory --crate-type lib
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@[quiet] forbid-output:UnmodeledThreadSpawnEffect
//! W11 transitive spawn census: no depth or size budget may mint a refusal.
//!
//! The first bounded port of the transitive census walked each call site's
//! local callees up to 16 levels deep and 128 bodies wide, and turned hitting
//! either bound (`TraversalLimit`) — or a withheld body at 16 nested
//! `TrustVerify` frames (`LocalBodyUnavailable`) — into an always-SAT
//! `UnmodeledThreadSpawnEffect` refusal. That refused programs that never spawn:
//!
//! * `deep_quiet_caller` reaches a 21-deep local chain (`chain_00`..`chain_20`);
//! * `wide_root`'s one call to `wide_hub` reaches 140 closures plus 140 local
//!   leaves (280 bodies) behind a single call site.
//!
//! The crate-level census (`trust_spawn_census`, trust-ir's reachability
//! engine since design 2026-09-29-spawn-census-by-construction P2) has no
//! bound, so `quiet` must carry no `UnmodeledThreadSpawnEffect` row
//! anywhere (the forbidden pattern is the row kind, which no annotation here
//! spells, so a source snippet echoing an annotation cannot trip it).
//! `control` is the same graph with ONE spawn added at the far end of each
//! (`chain_20`, `leaf_139`): both roots must then be refused, which shows
//! these flags do print the rows. The pattern is written with NO space after
//! the colon: compiletest keeps a directive's value verbatim, and the kind is
//! only ever printed after a backtick, so `forbid-output: Unmodeled...` (with
//! the space) could never match and forbade nothing (measured 2026-09-29).
//!
//! `-Ztrust-policy=advisory` keeps rows unrelated to this census (e.g. the
//! closure hub's lowering gap) non-fatal so the pass/fail is about the census.

#![allow(dead_code)]

#[inline(never)]
pub fn deep_quiet_caller() { //[control]~ NOTE local callee reaches a std thread spawn through calls and drops; caller effect is unmodeled
    chain_00();
}

#[inline(never)]
pub fn wide_root() { //[control]~ NOTE local callee reaches a std thread spawn through calls and drops; caller effect is unmodeled
    wide_hub();
}

#[inline(never)]
pub fn chain_20() {
    #[cfg(control)]
    let _handle = std::thread::spawn(|| {});
}

#[inline(never)]
pub fn leaf_139() {
    #[cfg(control)]
    let _handle = std::thread::spawn(|| {});
}

#[inline(never)]
pub fn chain_00() { chain_01(); }
#[inline(never)]
pub fn chain_01() { chain_02(); }
#[inline(never)]
pub fn chain_02() { chain_03(); }
#[inline(never)]
pub fn chain_03() { chain_04(); }
#[inline(never)]
pub fn chain_04() { chain_05(); }
#[inline(never)]
pub fn chain_05() { chain_06(); }
#[inline(never)]
pub fn chain_06() { chain_07(); }
#[inline(never)]
pub fn chain_07() { chain_08(); }
#[inline(never)]
pub fn chain_08() { chain_09(); }
#[inline(never)]
pub fn chain_09() { chain_10(); }
#[inline(never)]
pub fn chain_10() { chain_11(); }
#[inline(never)]
pub fn chain_11() { chain_12(); }
#[inline(never)]
pub fn chain_12() { chain_13(); }
#[inline(never)]
pub fn chain_13() { chain_14(); }
#[inline(never)]
pub fn chain_14() { chain_15(); }
#[inline(never)]
pub fn chain_15() { chain_16(); }
#[inline(never)]
pub fn chain_16() { chain_17(); }
#[inline(never)]
pub fn chain_17() { chain_18(); }
#[inline(never)]
pub fn chain_18() { chain_19(); }
#[inline(never)]
pub fn chain_19() { chain_20(); }
#[inline(never)]
pub fn leaf_000() {}
#[inline(never)]
pub fn leaf_001() {}
#[inline(never)]
pub fn leaf_002() {}
#[inline(never)]
pub fn leaf_003() {}
#[inline(never)]
pub fn leaf_004() {}
#[inline(never)]
pub fn leaf_005() {}
#[inline(never)]
pub fn leaf_006() {}
#[inline(never)]
pub fn leaf_007() {}
#[inline(never)]
pub fn leaf_008() {}
#[inline(never)]
pub fn leaf_009() {}
#[inline(never)]
pub fn leaf_010() {}
#[inline(never)]
pub fn leaf_011() {}
#[inline(never)]
pub fn leaf_012() {}
#[inline(never)]
pub fn leaf_013() {}
#[inline(never)]
pub fn leaf_014() {}
#[inline(never)]
pub fn leaf_015() {}
#[inline(never)]
pub fn leaf_016() {}
#[inline(never)]
pub fn leaf_017() {}
#[inline(never)]
pub fn leaf_018() {}
#[inline(never)]
pub fn leaf_019() {}
#[inline(never)]
pub fn leaf_020() {}
#[inline(never)]
pub fn leaf_021() {}
#[inline(never)]
pub fn leaf_022() {}
#[inline(never)]
pub fn leaf_023() {}
#[inline(never)]
pub fn leaf_024() {}
#[inline(never)]
pub fn leaf_025() {}
#[inline(never)]
pub fn leaf_026() {}
#[inline(never)]
pub fn leaf_027() {}
#[inline(never)]
pub fn leaf_028() {}
#[inline(never)]
pub fn leaf_029() {}
#[inline(never)]
pub fn leaf_030() {}
#[inline(never)]
pub fn leaf_031() {}
#[inline(never)]
pub fn leaf_032() {}
#[inline(never)]
pub fn leaf_033() {}
#[inline(never)]
pub fn leaf_034() {}
#[inline(never)]
pub fn leaf_035() {}
#[inline(never)]
pub fn leaf_036() {}
#[inline(never)]
pub fn leaf_037() {}
#[inline(never)]
pub fn leaf_038() {}
#[inline(never)]
pub fn leaf_039() {}
#[inline(never)]
pub fn leaf_040() {}
#[inline(never)]
pub fn leaf_041() {}
#[inline(never)]
pub fn leaf_042() {}
#[inline(never)]
pub fn leaf_043() {}
#[inline(never)]
pub fn leaf_044() {}
#[inline(never)]
pub fn leaf_045() {}
#[inline(never)]
pub fn leaf_046() {}
#[inline(never)]
pub fn leaf_047() {}
#[inline(never)]
pub fn leaf_048() {}
#[inline(never)]
pub fn leaf_049() {}
#[inline(never)]
pub fn leaf_050() {}
#[inline(never)]
pub fn leaf_051() {}
#[inline(never)]
pub fn leaf_052() {}
#[inline(never)]
pub fn leaf_053() {}
#[inline(never)]
pub fn leaf_054() {}
#[inline(never)]
pub fn leaf_055() {}
#[inline(never)]
pub fn leaf_056() {}
#[inline(never)]
pub fn leaf_057() {}
#[inline(never)]
pub fn leaf_058() {}
#[inline(never)]
pub fn leaf_059() {}
#[inline(never)]
pub fn leaf_060() {}
#[inline(never)]
pub fn leaf_061() {}
#[inline(never)]
pub fn leaf_062() {}
#[inline(never)]
pub fn leaf_063() {}
#[inline(never)]
pub fn leaf_064() {}
#[inline(never)]
pub fn leaf_065() {}
#[inline(never)]
pub fn leaf_066() {}
#[inline(never)]
pub fn leaf_067() {}
#[inline(never)]
pub fn leaf_068() {}
#[inline(never)]
pub fn leaf_069() {}
#[inline(never)]
pub fn leaf_070() {}
#[inline(never)]
pub fn leaf_071() {}
#[inline(never)]
pub fn leaf_072() {}
#[inline(never)]
pub fn leaf_073() {}
#[inline(never)]
pub fn leaf_074() {}
#[inline(never)]
pub fn leaf_075() {}
#[inline(never)]
pub fn leaf_076() {}
#[inline(never)]
pub fn leaf_077() {}
#[inline(never)]
pub fn leaf_078() {}
#[inline(never)]
pub fn leaf_079() {}
#[inline(never)]
pub fn leaf_080() {}
#[inline(never)]
pub fn leaf_081() {}
#[inline(never)]
pub fn leaf_082() {}
#[inline(never)]
pub fn leaf_083() {}
#[inline(never)]
pub fn leaf_084() {}
#[inline(never)]
pub fn leaf_085() {}
#[inline(never)]
pub fn leaf_086() {}
#[inline(never)]
pub fn leaf_087() {}
#[inline(never)]
pub fn leaf_088() {}
#[inline(never)]
pub fn leaf_089() {}
#[inline(never)]
pub fn leaf_090() {}
#[inline(never)]
pub fn leaf_091() {}
#[inline(never)]
pub fn leaf_092() {}
#[inline(never)]
pub fn leaf_093() {}
#[inline(never)]
pub fn leaf_094() {}
#[inline(never)]
pub fn leaf_095() {}
#[inline(never)]
pub fn leaf_096() {}
#[inline(never)]
pub fn leaf_097() {}
#[inline(never)]
pub fn leaf_098() {}
#[inline(never)]
pub fn leaf_099() {}
#[inline(never)]
pub fn leaf_100() {}
#[inline(never)]
pub fn leaf_101() {}
#[inline(never)]
pub fn leaf_102() {}
#[inline(never)]
pub fn leaf_103() {}
#[inline(never)]
pub fn leaf_104() {}
#[inline(never)]
pub fn leaf_105() {}
#[inline(never)]
pub fn leaf_106() {}
#[inline(never)]
pub fn leaf_107() {}
#[inline(never)]
pub fn leaf_108() {}
#[inline(never)]
pub fn leaf_109() {}
#[inline(never)]
pub fn leaf_110() {}
#[inline(never)]
pub fn leaf_111() {}
#[inline(never)]
pub fn leaf_112() {}
#[inline(never)]
pub fn leaf_113() {}
#[inline(never)]
pub fn leaf_114() {}
#[inline(never)]
pub fn leaf_115() {}
#[inline(never)]
pub fn leaf_116() {}
#[inline(never)]
pub fn leaf_117() {}
#[inline(never)]
pub fn leaf_118() {}
#[inline(never)]
pub fn leaf_119() {}
#[inline(never)]
pub fn leaf_120() {}
#[inline(never)]
pub fn leaf_121() {}
#[inline(never)]
pub fn leaf_122() {}
#[inline(never)]
pub fn leaf_123() {}
#[inline(never)]
pub fn leaf_124() {}
#[inline(never)]
pub fn leaf_125() {}
#[inline(never)]
pub fn leaf_126() {}
#[inline(never)]
pub fn leaf_127() {}
#[inline(never)]
pub fn leaf_128() {}
#[inline(never)]
pub fn leaf_129() {}
#[inline(never)]
pub fn leaf_130() {}
#[inline(never)]
pub fn leaf_131() {}
#[inline(never)]
pub fn leaf_132() {}
#[inline(never)]
pub fn leaf_133() {}
#[inline(never)]
pub fn leaf_134() {}
#[inline(never)]
pub fn leaf_135() {}
#[inline(never)]
pub fn leaf_136() {}
#[inline(never)]
pub fn leaf_137() {}
#[inline(never)]
pub fn leaf_138() {}
#[inline(never)]
pub fn wide_hub() {
    let c0 = || leaf_000();
    c0();
    let c1 = || leaf_001();
    c1();
    let c2 = || leaf_002();
    c2();
    let c3 = || leaf_003();
    c3();
    let c4 = || leaf_004();
    c4();
    let c5 = || leaf_005();
    c5();
    let c6 = || leaf_006();
    c6();
    let c7 = || leaf_007();
    c7();
    let c8 = || leaf_008();
    c8();
    let c9 = || leaf_009();
    c9();
    let c10 = || leaf_010();
    c10();
    let c11 = || leaf_011();
    c11();
    let c12 = || leaf_012();
    c12();
    let c13 = || leaf_013();
    c13();
    let c14 = || leaf_014();
    c14();
    let c15 = || leaf_015();
    c15();
    let c16 = || leaf_016();
    c16();
    let c17 = || leaf_017();
    c17();
    let c18 = || leaf_018();
    c18();
    let c19 = || leaf_019();
    c19();
    let c20 = || leaf_020();
    c20();
    let c21 = || leaf_021();
    c21();
    let c22 = || leaf_022();
    c22();
    let c23 = || leaf_023();
    c23();
    let c24 = || leaf_024();
    c24();
    let c25 = || leaf_025();
    c25();
    let c26 = || leaf_026();
    c26();
    let c27 = || leaf_027();
    c27();
    let c28 = || leaf_028();
    c28();
    let c29 = || leaf_029();
    c29();
    let c30 = || leaf_030();
    c30();
    let c31 = || leaf_031();
    c31();
    let c32 = || leaf_032();
    c32();
    let c33 = || leaf_033();
    c33();
    let c34 = || leaf_034();
    c34();
    let c35 = || leaf_035();
    c35();
    let c36 = || leaf_036();
    c36();
    let c37 = || leaf_037();
    c37();
    let c38 = || leaf_038();
    c38();
    let c39 = || leaf_039();
    c39();
    let c40 = || leaf_040();
    c40();
    let c41 = || leaf_041();
    c41();
    let c42 = || leaf_042();
    c42();
    let c43 = || leaf_043();
    c43();
    let c44 = || leaf_044();
    c44();
    let c45 = || leaf_045();
    c45();
    let c46 = || leaf_046();
    c46();
    let c47 = || leaf_047();
    c47();
    let c48 = || leaf_048();
    c48();
    let c49 = || leaf_049();
    c49();
    let c50 = || leaf_050();
    c50();
    let c51 = || leaf_051();
    c51();
    let c52 = || leaf_052();
    c52();
    let c53 = || leaf_053();
    c53();
    let c54 = || leaf_054();
    c54();
    let c55 = || leaf_055();
    c55();
    let c56 = || leaf_056();
    c56();
    let c57 = || leaf_057();
    c57();
    let c58 = || leaf_058();
    c58();
    let c59 = || leaf_059();
    c59();
    let c60 = || leaf_060();
    c60();
    let c61 = || leaf_061();
    c61();
    let c62 = || leaf_062();
    c62();
    let c63 = || leaf_063();
    c63();
    let c64 = || leaf_064();
    c64();
    let c65 = || leaf_065();
    c65();
    let c66 = || leaf_066();
    c66();
    let c67 = || leaf_067();
    c67();
    let c68 = || leaf_068();
    c68();
    let c69 = || leaf_069();
    c69();
    let c70 = || leaf_070();
    c70();
    let c71 = || leaf_071();
    c71();
    let c72 = || leaf_072();
    c72();
    let c73 = || leaf_073();
    c73();
    let c74 = || leaf_074();
    c74();
    let c75 = || leaf_075();
    c75();
    let c76 = || leaf_076();
    c76();
    let c77 = || leaf_077();
    c77();
    let c78 = || leaf_078();
    c78();
    let c79 = || leaf_079();
    c79();
    let c80 = || leaf_080();
    c80();
    let c81 = || leaf_081();
    c81();
    let c82 = || leaf_082();
    c82();
    let c83 = || leaf_083();
    c83();
    let c84 = || leaf_084();
    c84();
    let c85 = || leaf_085();
    c85();
    let c86 = || leaf_086();
    c86();
    let c87 = || leaf_087();
    c87();
    let c88 = || leaf_088();
    c88();
    let c89 = || leaf_089();
    c89();
    let c90 = || leaf_090();
    c90();
    let c91 = || leaf_091();
    c91();
    let c92 = || leaf_092();
    c92();
    let c93 = || leaf_093();
    c93();
    let c94 = || leaf_094();
    c94();
    let c95 = || leaf_095();
    c95();
    let c96 = || leaf_096();
    c96();
    let c97 = || leaf_097();
    c97();
    let c98 = || leaf_098();
    c98();
    let c99 = || leaf_099();
    c99();
    let c100 = || leaf_100();
    c100();
    let c101 = || leaf_101();
    c101();
    let c102 = || leaf_102();
    c102();
    let c103 = || leaf_103();
    c103();
    let c104 = || leaf_104();
    c104();
    let c105 = || leaf_105();
    c105();
    let c106 = || leaf_106();
    c106();
    let c107 = || leaf_107();
    c107();
    let c108 = || leaf_108();
    c108();
    let c109 = || leaf_109();
    c109();
    let c110 = || leaf_110();
    c110();
    let c111 = || leaf_111();
    c111();
    let c112 = || leaf_112();
    c112();
    let c113 = || leaf_113();
    c113();
    let c114 = || leaf_114();
    c114();
    let c115 = || leaf_115();
    c115();
    let c116 = || leaf_116();
    c116();
    let c117 = || leaf_117();
    c117();
    let c118 = || leaf_118();
    c118();
    let c119 = || leaf_119();
    c119();
    let c120 = || leaf_120();
    c120();
    let c121 = || leaf_121();
    c121();
    let c122 = || leaf_122();
    c122();
    let c123 = || leaf_123();
    c123();
    let c124 = || leaf_124();
    c124();
    let c125 = || leaf_125();
    c125();
    let c126 = || leaf_126();
    c126();
    let c127 = || leaf_127();
    c127();
    let c128 = || leaf_128();
    c128();
    let c129 = || leaf_129();
    c129();
    let c130 = || leaf_130();
    c130();
    let c131 = || leaf_131();
    c131();
    let c132 = || leaf_132();
    c132();
    let c133 = || leaf_133();
    c133();
    let c134 = || leaf_134();
    c134();
    let c135 = || leaf_135();
    c135();
    let c136 = || leaf_136();
    c136();
    let c137 = || leaf_137();
    c137();
    let c138 = || leaf_138();
    c138();
    let c139 = || leaf_139();
    c139();
}
