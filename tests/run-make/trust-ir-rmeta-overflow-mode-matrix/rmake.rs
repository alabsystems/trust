//! Actual canonical producer/consumer schema-5 overflow-mode protocol matrix.
//! This reads channel C; it grants no F1 admission or codegen proof authority.
//@ ignore-cross-compile

use run_make_support::{rfs, rustc};

fn mode(value: bool) -> &'static str { if value { "on" } else { "off" } }

fn row<'a>(stderr: &'a str, definition: &str) -> &'a str {
    let rows: Vec<_> = stderr.lines().filter(|line| {
        line.starts_with("TRUST-WALLA-PROBE C sym=")
            && line.contains(&format!(" def=mode_dep::{definition} "))
    }).collect();
    assert_eq!(rows.len(), 1, "one actual upstream row for {definition}:\n{stderr}");
    rows[0]
}

fn main() {
    for producer in [false, true] {
        let producer_out = format!("producer-{}", mode(producer));
        rfs::create_dir_all(&producer_out);
        rustc().input("producer.rs").crate_name("mode_dep").crate_type("lib")
            .edition("2021").arg("-Copt-level=0")
            .arg(format!("-Coverflow-checks={}", mode(producer)))
            .arg("-Ztrust-verify=off").arg("-Ztrust-ir-lower")
            .arg("--emit=metadata,link").out_dir(&producer_out).run();
        for consumer in [false, true] {
            let consumer_out = format!("consumer-p{}-c{}", mode(producer), mode(consumer));
            rfs::create_dir_all(&consumer_out);
            let result = rustc().input("consumer.rs").crate_name("mode_user")
                .crate_type("lib").edition("2021").arg("-Copt-level=0")
                .arg("-Ccodegen-units=1")
                .arg(format!("-Coverflow-checks={}", mode(consumer)))
                .arg("-Ztrust-verify=off").arg("-Ztrust-ir-lower")
                .arg("-Ztrust-instance-flip-probe=*")
                .extern_("mode_dep", format!("{producer_out}/libmode_dep.rlib"))
                .out_dir(&consumer_out).run();
            let stderr = result.stderr_utf8();
            for definition in ["mix", "identity"] {
                let row = row(&stderr, definition);
                if producer == consumer {
                    assert!(row.contains("rmeta=entry(digest-ok,functions=1,"),
                        "matching actual sessions require a real entry: {row}");
                } else {
                    let expected = format!(
                        "rmeta=entry-refused(overflow-check-mode(producer_{producer},_consumer_{consumer}))"
                    );
                    assert!(row.contains(&expected), "actual consumer mode mismatch: {row}");
                }
            }
            let inherited = row(&stderr, "inherited");
            assert!(inherited.contains("rmeta=absent(inherited-overflow-checks)"),
                "caller-dependent overflow semantics must not be exported: {inherited}");
        }
    }
}
