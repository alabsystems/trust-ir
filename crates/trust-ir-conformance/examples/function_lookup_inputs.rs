// Copyright 2026 Andrew Yates | Apache-2.0 OR MIT
//! Validate deterministic lookup benchmark inputs and retain cold codec requests.
//! Run through scripts/run-targo.sh run --locked -p trust-ir-conformance
//! --example function_lookup_inputs -- REQUEST_DIRECTORY OUTPUT_DIRECTORY.
use std::path::Path;
use trust_ir::Module;
use trust_ir::interpret::{InterpretValueKind, Interpreter};
use trust_ir::value::FuncId;

fn checked(
    module: &Module,
    label: &str,
    iterations: usize,
    sequence: bool,
) -> Vec<trust_ir::interpret::InterpretValue> {
    let errors = trust_ir_build::validate_module(module);
    assert!(errors.is_empty(), "{label}: {errors:?}");
    let outcome = Interpreter::with_module(module)
        .execute_func(FuncId::new(0), [])
        .unwrap_or_else(|error| panic!("{label}: {error:?}"));
    assert_eq!(outcome.host_calls, 0, "{label}");
    assert_eq!(outcome.returns.len(), 1, "{label}");
    if sequence {
        let InterpretValueKind::Sequence(values) = &outcome.returns[0].kind else {
            panic!("{label}: expected sequence")
        };
        assert_eq!(values.len() as usize, iterations, "{label}");
        for value in values.iter() {
            assert_eq!(value.as_int().expect("I8 lane").as_unsigned(), 7, "{label}");
        }
    } else {
        assert_eq!(
            outcome.returns[0]
                .as_int()
                .expect("I32 result")
                .as_unsigned(),
            42,
            "{label}"
        );
    }
    outcome.returns
}

fn main() {
    let args: Vec<_> = std::env::args_os().collect();
    assert_eq!(args.len(), 3, "expected request and output directories");
    let input = Path::new(&args[1]);
    let output = Path::new(&args[2]);
    std::fs::create_dir_all(output).expect("output directory");
    let inventory: serde_json::Value =
        serde_json::from_slice(&std::fs::read(input.join("inventory.json")).expect("inventory"))
            .expect("inventory JSON");
    let mut reports = Vec::new();
    let mut accepted = 0;
    let mut text_refusals = 0;
    for row in inventory.as_array().expect("inventory array") {
        let filename = row["path"].as_str().expect("filename");
        let mut request: serde_json::Value =
            serde_json::from_slice(&std::fs::read(input.join(filename)).expect("request"))
                .expect("request JSON");
        let module: Module =
            serde_json::from_value(request["batches"][0]["module"].clone()).expect("module schema");
        let iterations = row["iterations"].as_u64().expect("iterations") as usize;
        let sequence = row["kind"] == "seqmap";
        let expected = checked(&module, filename, iterations, sequence);
        let binary = trust_ir::binary::serialize_module(&module).expect("binary encode");
        let json = serde_json::to_vec(&module).expect("JSON encode");
        let msgpack = rmp_serde::to_vec(&module).expect("MessagePack encode");
        let mut carriers = vec![
            ("original", module.clone()),
            (
                "binary",
                trust_ir::binary::deserialize_module(&binary).expect("binary decode"),
            ),
            ("json", serde_json::from_slice(&json).expect("JSON decode")),
            (
                "msgpack",
                rmp_serde::from_slice(&msgpack).expect("MessagePack decode"),
            ),
        ];
        if row["sparse"] == true {
            let refusal = trust_ir::format::text_checked(&module)
                .expect_err("sparse IDs are not text-representable");
            assert!(
                refusal
                    .losses
                    .iter()
                    .all(|loss| matches!(loss, trust_ir::format::TextLoss::FunctionId { .. })),
                "{filename}: {refusal:?}"
            );
            text_refusals += 1;
        } else {
            let text = trust_ir::format::text_checked(&module).expect("dense checked text");
            carriers.push((
                "text",
                trust_ir::parser::parse_module(&text).expect("text decode"),
            ));
        }
        for (carrier, decoded) in carriers {
            let label = format!("{filename}.{carrier}");
            assert_eq!(
                decoded.functions.iter().map(|f| f.id).collect::<Vec<_>>(),
                module.functions.iter().map(|f| f.id).collect::<Vec<_>>(),
                "{label}: source order"
            );
            assert_eq!(
                checked(&decoded, &label, iterations, sequence),
                expected,
                "{label}: reference values"
            );
            request["batches"][0]["module"] =
                serde_json::to_value(decoded).expect("cold serde module");
            let retained = output.join(format!("{filename}.{carrier}.json"));
            std::fs::write(
                &retained,
                serde_json::to_vec(&request).expect("request serialization"),
            )
            .expect("retain cold request");
            reports.push(serde_json::json!({"path": retained.file_name().expect("retained name").to_str().expect("UTF-8 retained name"), "carrier": carrier, "reference_ok": true}));
            accepted += 1;
        }
    }
    let summary = serde_json::json!({"validated_and_reference_ok": accepted, "checked_text_id_refusals": text_refusals, "cases": reports});
    std::fs::write(
        output.join("validation.json"),
        serde_json::to_vec_pretty(&summary).expect("summary"),
    )
    .expect("retain summary");
    println!("validated/reference Ok: {accepted}; checked-text ID refusals: {text_refusals}");
}
