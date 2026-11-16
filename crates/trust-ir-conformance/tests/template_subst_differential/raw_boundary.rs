// Copyright 2026 Andrew Yates | Apache-2.0
//! Raw parsing correspondence only: no module-validity, source, layout or
//! execution authority. Original generators, goldens and ratchets are untouched.
use super::*;
use sha2::{Digest, Sha256};
use std::sync::atomic::{AtomicUsize, Ordering};
use trust_ir::Module;

fn invoke_raw(exe: &Path, text: &str, label: &str) -> Json {
    static NEXT: AtomicUsize = AtomicUsize::new(0);
    let directory = std::env::var_os("TRUST_IR_ORACLE_EVIDENCE_DIR")
        .map(PathBuf::from)
        .unwrap_or_else(|| Path::new(env!("CARGO_TARGET_TMPDIR")).join("raw-boundary-evidence"));
    std::fs::create_dir_all(&directory).unwrap();
    let stem = format!(
        "raw-boundary-{}-{}-{label}",
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed)
    );
    let input = directory.join(format!("{stem}.request.json"));
    std::fs::write(&input, text.as_bytes()).unwrap();
    let output = Command::new(exe).arg(&input).output().unwrap();
    std::fs::write(
        directory.join(format!("{stem}.response.json")),
        &output.stdout,
    )
    .unwrap();
    std::fs::write(directory.join(format!("{stem}.stderr.txt")), &output.stderr).unwrap();
    assert!(
        output.status.success(),
        "{label}: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    serde_json::from_slice(&output.stdout).unwrap()
}

fn raw_error(value: &Json) -> bool {
    value.as_object().is_some_and(|fields| {
        fields.len() == 1
            && fields
                .get("error")
                .and_then(Json::as_str)
                .is_some_and(|s| s.starts_with("raw serde:"))
    })
}

#[test]
fn sealed_raw_numeric_and_duplicate_inputs_follow_actual_serde_domain() {
    let Some(exe) = oracle() else { return };
    let cases: Vec<Json> =
        serde_json::from_str(include_str!("raw_boundary/sealed30.json")).unwrap();
    assert_eq!(cases.len(), 30);
    let mut rows = Vec::new();
    let mut accepts = 0;
    for case in &cases {
        let raw = case["raw"].as_str().unwrap();
        assert_eq!(
            format!("{:x}", Sha256::digest(raw.as_bytes())),
            case["raw_sha256"]
        );
        let parsed = serde_json::from_str::<Ty>(raw);
        assert_eq!(
            parsed.is_ok(),
            case["rust_accepts"].as_bool().unwrap(),
            "{}: {parsed:?}",
            case["label"]
        );
        if let Ok(ty) = parsed {
            assert_eq!(serde_json::to_value(ty).unwrap(), case["expected"]);
            accepts += 1;
        }
        rows.push(format!(
            r#"{{"ty":{raw},"params":[],"holes":[],"expected":{}}}"#,
            case["expected"]
        ));
    }
    assert_eq!(accepts, 9);
    let reply = invoke_raw(
        exe,
        &format!(r#"{{"template_subst":[{}]}}"#, rows.join(",")),
        "sealed30",
    );
    let outcomes = reply.as_array().unwrap();
    assert_eq!(outcomes.len(), 30);
    for (case, value) in cases.iter().zip(outcomes) {
        if case["rust_accepts"] == true {
            assert_eq!(value, &json!({"agree": true}), "{}", case["label"]);
        } else {
            assert!(raw_error(value), "{}: {value}", case["label"]);
        }
    }
    eprintln!("raw_boundary_sealed: rows=30 accepted=9 refused=21 unsupported=0");
}

fn materialize(module: &Json, raw: &str) -> String {
    let text = serde_json::to_string(module).unwrap();
    assert_eq!(text.matches("\"__RAW_BOUNDARY_VALUE__\"").count(), 1);
    text.replace("\"__RAW_BOUNDARY_VALUE__\"", raw)
}

fn ordinary(module: &str) -> String {
    format!(r#"{{"fuel":10,"call_depth":10,"batches":[{{"module":{module},"runs":[]}}]}}"#)
}

#[test]
fn raw_checks_cover_actual_type_and_constant_ingress() {
    let Some(exe) = oracle() else { return };
    let routes: Vec<Json> =
        serde_json::from_str(include_str!("raw_boundary/type-routes.json")).unwrap();
    let constants: Vec<Json> =
        serde_json::from_str(include_str!("raw_boundary/constant-routes.json")).unwrap();
    assert_eq!(routes.len(), 49);
    assert_eq!(constants.len(), 27);
    let canonical_storage = r#"{"Storage":{"size_bytes":8,"align_bytes":8}}"#;
    let unknown_storage = r#"{"Storage":{"size_bytes":8,"align_bytes":8,"unused":{"FnItem":11e0},"unused":{"Storage":[-0,8]}}}"#;
    let bad_storage = r#"{"Storage":{"size_bytes":8e0,"align_bytes":8}}"#;
    let canonical_item = r#"{"FnItem":11}"#;
    let bad_item = r#"{"FnItem":11e0}"#;
    let mut observations = 0;
    for route in &routes {
        let label = route["label"].as_str().unwrap();
        let wire = materialize(&route["module"], canonical_storage);
        serde_json::from_str::<Module>(&wire)
            .unwrap_or_else(|e| panic!("{label}: actual Rust shape: {e}"));
        let baseline = invoke_raw(exe, &ordinary(&wire), &format!("{label}-storage"));
        assert!(!raw_error(&baseline), "{label}: {baseline}");
        let wire = materialize(&route["module"], unknown_storage);
        serde_json::from_str::<Module>(&wire)
            .unwrap_or_else(|e| panic!("{label}: ignored unknown fields: {e}"));
        assert_eq!(
            invoke_raw(exe, &ordinary(&wire), &format!("{label}-unknown")),
            baseline
        );
        for (kind, raw) in [("bad-storage", bad_storage), ("bad-item", bad_item)] {
            let wire = materialize(&route["module"], raw);
            let error = serde_json::from_str::<Module>(&wire)
                .unwrap_err()
                .to_string();
            assert!(error.contains("floating point"), "{label}/{kind}: {error}");
            assert!(
                raw_error(&invoke_raw(
                    exe,
                    &ordinary(&wire),
                    &format!("{label}-{kind}")
                )),
                "{label}/{kind}"
            );
        }
        let wire = materialize(&route["module"], canonical_item);
        serde_json::from_str::<Module>(&wire)
            .unwrap_or_else(|e| panic!("{label}: item serde: {e}"));
        assert!(!raw_error(&invoke_raw(
            exe,
            &ordinary(&wire),
            &format!("{label}-item")
        )));
        observations += 5;
    }
    for route in &constants {
        let label = route["label"].as_str().unwrap();
        let wire = materialize(&route["module"], canonical_item);
        serde_json::from_str::<Module>(&wire)
            .unwrap_or_else(|e| panic!("{label}: actual constant shape: {e}"));
        assert!(!raw_error(&invoke_raw(exe, &ordinary(&wire), label)));
        let wire = materialize(&route["module"], bad_item);
        let error = serde_json::from_str::<Module>(&wire)
            .unwrap_err()
            .to_string();
        assert!(error.contains("floating point"), "{label}: {error}");
        assert!(raw_error(&invoke_raw(
            exe,
            &ordinary(&wire),
            &format!("{label}-bad")
        )));
        observations += 2;
    }
    assert_eq!(observations, 299);
    eprintln!("raw_boundary_routes: type_positions=49 constant_positions=27 observations=299");
}
