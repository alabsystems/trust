extern crate legacy_site_fixture as upstream;
pub fn case_super4() -> u64 { upstream::typed::<dyn upstream::Child<4, Assoc=u64> + Send>() }
pub fn case_super5() -> u64 { upstream::typed::<dyn upstream::Child<5, Assoc=u64> + Send>() }
