// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Diagnostic only: measure the reference fence over extracted island bodies.
//! Input is one JSON object per line, with `path` and `sources` fields.
use std::io::{self, BufRead};

use clean_kernel::{Expr, Level, Name, ReferenceKernel};
use trust_certify::clean_island::CleanIslandSession;

fn main() {
    for line in io::stdin().lock().lines() {
        let input: serde_json::Value =
            serde_json::from_str(&line.expect("input line")).expect("JSON");
        let sources: Vec<&str> = input["sources"]
            .as_array()
            .expect("sources")
            .iter()
            .map(|s| s.as_str().expect("source string"))
            .collect();
        let start = std::time::Instant::now();
        let mut session = CleanIslandSession::new();
        let batch = session.check_all(&sources);
        let elaboration_ms = start.elapsed().as_millis();
        eprintln!(
            "TG8 path={} phase=elaborated ms={} rejected={}",
            input["path"],
            elaboration_ms,
            batch.is_rejected()
        );
        let mut errors = Vec::new();
        for outcome in &batch.outcomes {
            errors.extend(outcome.errors.iter().map(|e| e.message.clone()));
        }
        let mut checked = 0;
        let mut refused = Vec::new();
        let mut unmeasured = Vec::new();
        let start = std::time::Instant::now();
        if let Some(env) = session.environment() {
            let kernel = ReferenceKernel::new(env.clone());
            for outcome in &batch.outcomes {
                for spelling in &outcome.registered {
                    eprintln!("TG8 path={} phase=reference declaration={spelling}", input["path"]);
                    let name = Name::from_string(spelling);
                    if let Some(info) = env.get_const(&name) {
                        // Citing the constant forces the entry's base recheck,
                        // including its value; a type-only check is insufficient.
                        let levels = vec![Level::zero(); info.level_params.len()];
                        let ty =
                            info.type_.instantiate_level_params_direct(&info.level_params, &levels);
                        let term = Expr::const_(name, levels);
                        match kernel.as_ref().map_err(|e| format!("{e:?}")).and_then(|k| {
                            k.check_closed_term(&ty, &term).map_err(|e| format!("{e:?}"))
                        }) {
                            Ok(_) => checked += 1,
                            Err(e) => refused.push(format!("{spelling}: {e:?}")),
                        }
                    } else {
                        unmeasured.push(spelling.clone());
                    }
                }
            }
        }
        println!(
            "{}",
            serde_json::json!({"path":input["path"], "elaboration_ms":elaboration_ms,
            "reference_ms":start.elapsed().as_millis(), "checked":checked, "refused":refused,
            "errors":errors,"unmeasured":unmeasured,"cycles":batch.cycles.len()})
        );
    }
}
