//! Census of `[unsafe:sep:*]` obligations over a directory of extracted MIR
//! (`-Ztrust-dump=mir:<dir>`). Measurement aid: run it against the SAME
//! fixtures before and after a sep-engine change to see exactly which rows
//! moved. Prints one line per obligation plus a per-tag tally.
use std::collections::BTreeMap;

use trust_types::{VcKind, VerifiableFunction};
use trust_vcgen::generate_vcs;

fn main() {
    let dir = std::env::args().nth(1).expect("usage: sep_census <mir-dump-dir>");
    let mut tally: BTreeMap<String, usize> = BTreeMap::new();
    let mut rows: Vec<String> = Vec::new();
    let mut entries: Vec<_> = std::fs::read_dir(&dir)
        .expect("mir dump directory must be readable")
        .filter_map(Result::ok)
        .map(|e| e.path())
        .filter(|p| p.extension().is_some_and(|x| x == "json"))
        .collect();
    entries.sort();
    for path in entries {
        let text = std::fs::read_to_string(&path).expect("fixture must be readable");
        let Ok(func) = serde_json::from_str::<VerifiableFunction>(&text) else {
            continue;
        };
        for vc in generate_vcs(&func) {
            let VcKind::Assertion { message } = &vc.kind else { continue };
            let Some(rest) = message.split("[unsafe:sep:").nth(1) else { continue };
            let Some(tag) = rest.split(']').next() else { continue };
            *tally.entry(tag.to_string()).or_default() += 1;
            rows.push(format!("{tag}\t{}\t{message}", func.def_path));
        }
    }
    rows.sort();
    for r in &rows {
        println!("{r}");
    }
    println!("---");
    for (tag, n) in &tally {
        println!("{tag}\t{n}");
    }
    println!("TOTAL\t{}", rows.len());
}
