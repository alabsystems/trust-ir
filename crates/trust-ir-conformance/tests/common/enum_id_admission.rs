// Copyright 2026 Andrew Yates | Apache-2.0 OR MIT
//! Functional cross-language ID admission. This does not prove Rust validator refinement.
use super::*;
use trust_ir::ty::{EnumDef, EnumVariant};
use trust_ir::value::EnumId;
use trust_ir_build::ValidationError;

fn row(id: u32) -> EnumDef {
    EnumDef::new(
        EnumId::new(id),
        "Original enum row",
        vec![EnumVariant {
            name: "Unit".into(),
            fields: vec![],
            field_names: vec![],
        }],
    )
}

#[test]
fn enum_id_admission_matches_original_validator() {
    let Oracle::Ready(exe) = oracle() else { return };
    let mut altered = row(7);
    altered.name = "Different definition".into();
    altered.variants[0].fields = vec![Ty::Never];
    let mut invalid_discriminants = row(7);
    invalid_discriminants
        .variants
        .push(invalid_discriminants.variants[0].clone());
    invalid_discriminants.discriminants = vec![Some(0), Some(0)];
    let cases = [
        ("empty", vec![], true),
        ("sparse", vec![row(u32::MAX), row(0), row(65537)], true),
        ("permuted", vec![row(65537), row(u32::MAX), row(0)], true),
        ("identical duplicate", vec![row(7), row(7)], false),
        ("altered duplicate", vec![row(7), altered], false),
        (
            "nonadjacent duplicate",
            vec![row(7), row(u32::MAX), row(7)],
            false,
        ),
        ("multiple duplicates", vec![row(7), row(7), row(7)], false),
        // ID admission must not become a whole-module validity claim.
        (
            "unique ID with invalid discriminants",
            vec![invalid_discriminants],
            true,
        ),
    ];
    let modules: Vec<_> = cases
        .iter()
        .map(|(label, rows, _)| {
            let mut module = Module::new(*label);
            module.enums = rows.clone();
            module
        })
        .collect();
    let mut request = String::from("{\"enum_id_admission\":[");
    for (index, module) in modules.iter().enumerate() {
        if index != 0 {
            request.push(',');
        }
        request.push_str(&serde_json::to_string(module).expect("original module serializes"));
    }
    let mut out_of_range = serde_json::to_value(&modules[1]).expect("original sparse source");
    assert!(serde_json::from_value::<Module>(out_of_range.clone()).is_ok());
    out_of_range["enums"][0]["id"] = json!(1u64 << 32);
    assert!(
        serde_json::from_value::<Module>(out_of_range.clone()).is_err(),
        "Rust u32 ID boundary"
    );
    request.push(',');
    request.push_str(&serde_json::to_string(&out_of_range).unwrap());
    request.push_str("]}");
    let path = std::env::temp_dir().join(format!(
        "trustir-enum-id-admission-{}.json",
        std::process::id()
    ));
    fs::write(&path, request.as_bytes()).expect("write original module bytes");
    let output = Command::new(exe)
        .arg(&path)
        .output()
        .expect("run Lean ID admission");
    fs::remove_file(&path).expect("remove own request");
    if let Some(directory) = std::env::var_os("TRUST_IR_ORACLE_EVIDENCE_DIR") {
        let directory = PathBuf::from(directory);
        fs::create_dir_all(&directory).expect("create admission evidence directory");
        fs::write(
            directory.join("enum-id-admission.request.json"),
            request.as_bytes(),
        )
        .unwrap();
        fs::write(
            directory.join("enum-id-admission.response.json"),
            &output.stdout,
        )
        .unwrap();
        fs::write(
            directory.join("enum-id-admission.stderr.txt"),
            &output.stderr,
        )
        .unwrap();
    }
    assert!(
        output.status.success(),
        "Lean admission process failed: {output:?}"
    );
    let replies: Json = serde_json::from_slice(&output.stdout).expect("Lean JSON response");
    let replies = replies
        .as_array()
        .expect("one ID result per original module");
    assert_eq!(replies.len(), cases.len() + 1);
    for (index, ((label, _, expected), module)) in cases.iter().zip(&modules).enumerate() {
        let errors = trust_ir_build::validate_module(module);
        let rust_admitted = !errors
            .iter()
            .any(|error| matches!(error, ValidationError::DuplicateEnumId(_)));
        assert_eq!(
            rust_admitted, *expected,
            "Rust ID diagnostic: {label}: {errors:?}"
        );
        assert_eq!(
            replies[index],
            json!({"enum_ids_admitted": rust_admitted}),
            "original source: {label}"
        );
        if index == cases.len() - 1 {
            assert!(
                !errors.is_empty(),
                "invalid discriminants must remain a whole-module refusal"
            );
        }
    }
    assert_eq!(
        replies[cases.len()],
        json!({"enum_ids_admitted": false}),
        "Lean u32 ID boundary"
    );
    eprintln!("ENUM_ID_ADMISSION_DIFFERENTIAL_PASS cases=9");
}
