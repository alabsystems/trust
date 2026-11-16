// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// How often is `parse -> serialize` NOT a fixpoint? This is a property of the
// INCUMBENT's deliberately-imprecise default float parse, faithfully
// reproduced by trust-json -- so it is not a divergence. It matters anyway,
// because this tree hashes serialized JSON and moves proof bundles between
// processes: a bundle that makes two hops can hash differently from one that
// makes one.

use incumbent_serde_json as inc;
use trust_json as tj;

struct Lcg(u64);
impl Lcg {
    fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        let x = self.0;
        x ^ (x >> 31)
    }
    fn below(&mut self, n: u64) -> u64 {
        self.next_u64() % n
    }
}

fn main() {
    // Named cases first.
    println!("named cases (tj || inc, one hop -> two hops):");
    for src in [
        "1e-30",
        "1e-5",
        "1e-6",
        "1e30",
        "0.1",
        "1.1",
        "1e-323",
        "123456789012345678901",
        "1.7976931348623157e308",
        "2.2250738585072014e-308",
    ] {
        let a = tj::to_string(&tj::from_str(src).unwrap()).unwrap();
        let a2 = tj::to_string(&tj::from_str(&a).unwrap()).unwrap();
        let b = inc::to_string(&inc::from_str::<inc::Value>(src).unwrap()).unwrap();
        let b2 = inc::to_string(&inc::from_str::<inc::Value>(&b).unwrap()).unwrap();
        let agree = a == b && a2 == b2;
        let stable = a == a2;
        println!("  {src:<24} hop1={a:<26} hop2={a2:<26} stable={stable:<5} tj==inc={agree}");
    }

    let mut rng = Lcg(0x452821E638D01377);
    let (mut n, mut unstable, mut disagree, mut hop3_unstable) = (0u64, 0u64, 0u64, 0u64);
    for _ in 0..500_000 {
        let mut s = String::new();
        if rng.below(2) == 0 {
            s.push('-');
        }
        let d = 1 + rng.below(30);
        for k in 0..d {
            let c = if k == 0 { b'1' + rng.below(9) as u8 } else { b'0' + rng.below(10) as u8 };
            s.push(c as char);
        }
        if rng.below(2) == 0 {
            s.push('.');
            for _ in 0..(1 + rng.below(25)) {
                s.push((b'0' + rng.below(10) as u8) as char);
            }
        }
        if rng.below(2) == 0 {
            s.push('e');
            if rng.below(2) == 0 {
                s.push('-');
            }
            for _ in 0..(1 + rng.below(3)) {
                s.push((b'0' + rng.below(10) as u8) as char);
            }
        }
        let (Ok(a0), Ok(b0)) = (tj::from_str(&s), inc::from_str::<inc::Value>(&s)) else {
            continue;
        };
        n += 1;
        let a = tj::to_string(&a0).unwrap();
        let b = inc::to_string(&b0).unwrap();
        if a != b {
            disagree += 1;
            continue;
        }
        let a2 = tj::to_string(&tj::from_str(&a).unwrap()).unwrap();
        if a != a2 {
            unstable += 1;
            let a3 = tj::to_string(&tj::from_str(&a2).unwrap()).unwrap();
            if a2 != a3 {
                hop3_unstable += 1;
            }
        }
    }
    println!();
    println!("random number texts accepted by both: {n}");
    println!("  tj vs inc one-hop DISAGREEMENTS      : {disagree}");
    println!(
        "  hop1 != hop2 (NOT a fixpoint)        : {unstable}  ({:.3}%)",
        100.0 * unstable as f64 / n as f64
    );
    println!("  ... and hop2 != hop3 (still moving)  : {hop3_unstable}");
    assert_eq!(disagree, 0, "trust-json and the incumbent disagreed");
}
