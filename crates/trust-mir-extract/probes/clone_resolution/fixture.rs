#![feature(type_alias_impl_trait)]
#![allow(dead_code)]
type Hidden = impl Copy;
#[define_opaque(Hidden)]
fn hidden() -> Hidden {
    7u8
}
#[derive(Clone)]
enum E {
    A,
    B(u8),
}
struct OpaqueBound;
impl Clone for OpaqueBound
where
    Hidden: Copy,
{
    fn clone(&self) -> Self {
        Self
    }
}
const fn nonleaf() -> usize {
    1 + 2
}
trait Marker {}
impl Marker for [(); 3] {}
struct ConstBound;
impl Clone for ConstBound
where
    [(); nonleaf()]: Marker,
{
    fn clone(&self) -> Self {
        Self
    }
}
struct Generic<T>(T);
impl<T: Clone> Clone for Generic<T> {
    fn clone(&self) -> Self {
        Self(self.0.clone())
    }
}
fn case_adt(_: &E) {}
fn case_opaque_bound(_: &OpaqueBound) {}
fn case_nonleaf_bound(_: &ConstBound) {}
fn case_tuple(_: &(u8, u8)) {}
fn case_fnptr(_: &fn()) {}
fn case_opaque(_: &Hidden) {}
fn case_generic<T: Clone>(_: &Generic<T>) {}

trait Wide<const N: usize> {}
struct Leaf;
impl<const N: usize> Wide<N> for Leaf {}
struct ManyBounds;
impl Clone for ManyBounds
where
    Leaf: Wide<0>
        + Wide<1>
        + Wide<2>
        + Wide<3>
        + Wide<4>
        + Wide<5>
        + Wide<6>
        + Wide<7>
        + Wide<8>
        + Wide<9>
        + Wide<10>
        + Wide<11>
        + Wide<12>
        + Wide<13>
        + Wide<14>
        + Wide<15>
        + Wide<16>
        + Wide<17>
        + Wide<18>
        + Wide<19>
        + Wide<20>
        + Wide<21>
        + Wide<22>
        + Wide<23>
        + Wide<24>
        + Wide<25>
        + Wide<26>
        + Wide<27>
        + Wide<28>
        + Wide<29>
        + Wide<30>
        + Wide<31>
        + Wide<32>
        + Wide<33>
        + Wide<34>
        + Wide<35>
        + Wide<36>
        + Wide<37>
        + Wide<38>
        + Wide<39>
        + Wide<40>
        + Wide<41>
        + Wide<42>
        + Wide<43>
        + Wide<44>
        + Wide<45>
        + Wide<46>
        + Wide<47>
        + Wide<48>
        + Wide<49>
        + Wide<50>
        + Wide<51>
        + Wide<52>
        + Wide<53>
        + Wide<54>
        + Wide<55>
        + Wide<56>
        + Wide<57>
        + Wide<58>
        + Wide<59>
        + Wide<60>
        + Wide<61>
        + Wide<62>
        + Wide<63>
        + Wide<64>
        + Wide<65>
        + Wide<66>
        + Wide<67>
        + Wide<68>
        + Wide<69>
        + Wide<70>
        + Wide<71>
        + Wide<72>
        + Wide<73>
        + Wide<74>
        + Wide<75>
        + Wide<76>
        + Wide<77>
        + Wide<78>
        + Wide<79>
        + Wide<80>
        + Wide<81>
        + Wide<82>
        + Wide<83>
        + Wide<84>
        + Wide<85>
        + Wide<86>
        + Wide<87>
        + Wide<88>
        + Wide<89>
        + Wide<90>
        + Wide<91>
        + Wide<92>
        + Wide<93>
        + Wide<94>
        + Wide<95>
        + Wide<96>
        + Wide<97>
        + Wide<98>
        + Wide<99>
        + Wide<100>
        + Wide<101>
        + Wide<102>
        + Wide<103>
        + Wide<104>
        + Wide<105>
        + Wide<106>
        + Wide<107>
        + Wide<108>
        + Wide<109>
        + Wide<110>
        + Wide<111>
        + Wide<112>
        + Wide<113>
        + Wide<114>
        + Wide<115>
        + Wide<116>
        + Wide<117>
        + Wide<118>
        + Wide<119>
        + Wide<120>
        + Wide<121>
        + Wide<122>
        + Wide<123>
        + Wide<124>
        + Wide<125>
        + Wide<126>
        + Wide<127>
        + Wide<128>
        + Wide<129>
        + Wide<130>
        + Wide<131>
        + Wide<132>
        + Wide<133>
        + Wide<134>
        + Wide<135>
        + Wide<136>
        + Wide<137>
        + Wide<138>
        + Wide<139>
        + Wide<140>
        + Wide<141>
        + Wide<142>
        + Wide<143>
        + Wide<144>
        + Wide<145>
        + Wide<146>
        + Wide<147>
        + Wide<148>
        + Wide<149>
        + Wide<150>
        + Wide<151>
        + Wide<152>
        + Wide<153>
        + Wide<154>
        + Wide<155>
        + Wide<156>
        + Wide<157>
        + Wide<158>
        + Wide<159>
        + Wide<160>
        + Wide<161>
        + Wide<162>
        + Wide<163>
        + Wide<164>
        + Wide<165>
        + Wide<166>
        + Wide<167>
        + Wide<168>
        + Wide<169>
        + Wide<170>
        + Wide<171>
        + Wide<172>
        + Wide<173>
        + Wide<174>
        + Wide<175>
        + Wide<176>
        + Wide<177>
        + Wide<178>
        + Wide<179>
        + Wide<180>
        + Wide<181>
        + Wide<182>
        + Wide<183>
        + Wide<184>
        + Wide<185>
        + Wide<186>
        + Wide<187>
        + Wide<188>
        + Wide<189>
        + Wide<190>
        + Wide<191>
        + Wide<192>
        + Wide<193>
        + Wide<194>
        + Wide<195>
        + Wide<196>
        + Wide<197>
        + Wide<198>
        + Wide<199>
        + Wide<200>
        + Wide<201>
        + Wide<202>
        + Wide<203>
        + Wide<204>
        + Wide<205>
        + Wide<206>
        + Wide<207>
        + Wide<208>
        + Wide<209>
        + Wide<210>
        + Wide<211>
        + Wide<212>
        + Wide<213>
        + Wide<214>
        + Wide<215>
        + Wide<216>
        + Wide<217>
        + Wide<218>
        + Wide<219>
        + Wide<220>
        + Wide<221>
        + Wide<222>
        + Wide<223>
        + Wide<224>
        + Wide<225>
        + Wide<226>
        + Wide<227>
        + Wide<228>
        + Wide<229>
        + Wide<230>
        + Wide<231>
        + Wide<232>
        + Wide<233>
        + Wide<234>
        + Wide<235>
        + Wide<236>
        + Wide<237>
        + Wide<238>
        + Wide<239>
        + Wide<240>
        + Wide<241>
        + Wide<242>
        + Wide<243>
        + Wide<244>
        + Wide<245>
        + Wide<246>
        + Wide<247>
        + Wide<248>
        + Wide<249>
        + Wide<250>
        + Wide<251>
        + Wide<252>
        + Wide<253>
        + Wide<254>
        + Wide<255>
        + Wide<256>
        + Wide<257>
        + Wide<258>
        + Wide<259>,
{
    fn clone(&self) -> Self {
        Self
    }
}
fn case_many_bounds(_: &ManyBounds) {}
