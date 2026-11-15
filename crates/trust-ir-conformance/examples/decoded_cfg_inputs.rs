// Copyright 2026 Andrew Yates | Apache-2.0 OR MIT
//! Validate reachable decoded-CFG requests and retain lossless cold carriers.
//! Run via scripts/run-targo.sh run --locked -p trust-ir-conformance
//! --example decoded_cfg_inputs -- REQUEST_DIRECTORY OUTPUT_DIRECTORY.
//! This uses only the Rust reference interpreter, with no Lean/native oracle or timing job.
use std::path::Path;

use serde_json::{Value, json};
use sha2::{Digest, Sha256};
use trust_ir::interpret::{InterpretErrorCode, InterpretOptions, InterpretValue, Interpreter};
use trust_ir::value::FuncId;
use trust_ir::{Module, Ty};

fn sha256(bytes: &[u8]) -> String {
    format!("{:x}", Sha256::digest(bytes))
}

#[derive(Clone, Copy)]
struct Execution {
    options: InterpretOptions,
    expected_reference_out_of_fuel: bool,
}

fn checked(module: &Module, label: &str, execution: Execution) -> Result<Value, String> {
    let errors = trust_ir_build::validate_module(module);
    if !errors.is_empty() {
        return Err(format!("{label}: validation: {errors:?}"));
    }
    let outcome = match Interpreter::with_module(module)
        .with_options(execution.options)
        .execute_func(FuncId::new(0), [])
    {
        Ok(outcome) => outcome,
        Err(error)
            if execution.expected_reference_out_of_fuel
                && error.code == InterpretErrorCode::OutOfFuel =>
        {
            return Ok(
                json!({"kind": "reference_only_out_of_fuel", "value_admission_credit": false,
                "error_code": format!("{:?}", error.code), "error_debug": format!("{error:?}"),
                "fuel": execution.options.fuel, "call_depth": execution.options.max_call_depth,
                "cross_engine_fuel_agreement_claim": false}),
            );
        }
        Err(error) => return Err(format!("{label}: reference execution: {error:?}")),
    };
    if execution.expected_reference_out_of_fuel {
        return Err(format!(
            "{label}: expected the original reference fuel refusal"
        ));
    }
    let expected = vec![InterpretValue::int(Ty::I32, 42).expect("exact I32 reference value")];
    if outcome.host_calls != 0 || outcome.returns != expected {
        return Err(format!(
            "{label}: expected exactly [I32(42)] and zero host calls, got {outcome:?}"
        ));
    }
    let value = &outcome.returns[0];
    let integer = value.as_int().expect("checked exact integer value");
    Ok(json!({
        "kind": "exact_i32_42", "value_admission_credit": true,
        "returns": [{"type": format!("{:?}", value.ty), "kind": "Int", "bits": integer.bits,
            "signed": integer.signed, "raw": integer.raw.to_string(),
            "signed_value": integer.as_signed().to_string()}],
        "return_count": outcome.returns.len(), "host_calls": outcome.host_calls,
        "steps": outcome.steps, "fuel": execution.options.fuel,
        "call_depth": execution.options.max_call_depth,
    }))
}

fn preserved(original: &Module, decoded: &Module, label: &str) -> Result<(), String> {
    if original.functions.iter().map(|f| f.id).collect::<Vec<_>>()
        != decoded.functions.iter().map(|f| f.id).collect::<Vec<_>>()
    {
        return Err(format!("{label}: source function IDs/order changed"));
    }
    for (source, target) in original.functions.iter().zip(&decoded.functions) {
        if source.entry != target.entry || source.blocks != target.blocks {
            return Err(format!(
                "{label}: exact entry/block IDs/order/parameters/instructions/CFG changed"
            ));
        }
    }
    if original != decoded {
        return Err(format!("{label}: lossless module AST changed"));
    }
    Ok(())
}

fn retain(
    output: &Path,
    filename: &str,
    carrier: &str,
    original: &Module,
    decoded: &Module,
    source_request: (&Value, &[u8]),
    execution: Execution,
) -> Result<Value, String> {
    let (request, original_bytes) = source_request;
    let label = format!("{filename}.{carrier}");
    preserved(original, decoded, &label)?;
    let observed = checked(decoded, &label, execution)?;
    let stem = filename.strip_suffix(".json").unwrap_or(filename);
    let relative = format!("requests/{stem}.{carrier}.request.json");
    let bytes = if carrier == "original" {
        original_bytes.to_vec()
    } else {
        let mut cold = request.clone();
        cold["batches"][0]["module"] =
            serde_json::to_value(decoded).map_err(|error| format!("{label}: {error}"))?;
        serde_json::to_vec(&cold).map_err(|error| format!("{label}: {error}"))?
    };
    std::fs::write(output.join(&relative), &bytes)
        .map_err(|error| format!("{label}: retain: {error}"))?;
    Ok(
        json!({"source_case": filename, "carrier": carrier, "request": relative,
        "request_sha256": sha256(&bytes), "request_bytes": bytes.len(),
        "validated_before_execution": true, "exact_module_and_cfg_preserved": true,
        "reference": observed}),
    )
}

fn run(input: &Path, output: &Path, original_resource_controls: bool) -> Result<usize, String> {
    for name in ["requests", "carriers", "refusals"] {
        std::fs::create_dir_all(output.join(name)).map_err(|error| error.to_string())?;
    }
    let inventory_bytes = std::fs::read(input.join("inventory.json"))
        .map_err(|error| format!("inventory read: {error}"))?;
    let inventory: Value = serde_json::from_slice(&inventory_bytes)
        .map_err(|error| format!("inventory JSON: {error}"))?;
    if original_resource_controls
        && sha256(&inventory_bytes)
            != "6d2bf2a528c0c5b3d9fd6f7b8f96dcccf5e1344a054027c22da63fdeaeaeff94"
    {
        return Err("original resource mode requires the exact frozen V1 inventory".into());
    }
    let cases = inventory["cases"]
        .as_array()
        .ok_or("expected inventory.cases")?;
    let mut accepted = Vec::new();
    let mut failures = Vec::new();
    let mut refusals = Vec::new();
    let mut sources = Vec::new();
    for row in cases {
        let filename = row["path"].as_str().ok_or("missing input path")?;
        let bytes = std::fs::read(input.join(filename)).map_err(|error| error.to_string())?;
        if row["sha256"] != sha256(&bytes) || row["bytes"] != bytes.len() {
            return Err(format!("{filename}: frozen source bytes/hash mismatch"));
        }
        let request: Value = serde_json::from_slice(&bytes).map_err(|error| error.to_string())?;
        let fuel = request["fuel"].as_u64().ok_or("missing request fuel")?;
        let max_call_depth = request["call_depth"]
            .as_u64()
            .ok_or("missing request depth")?;
        let runs = request["batches"][0]["runs"]
            .as_array()
            .ok_or("missing runs")?;
        if request["batches"]
            .as_array()
            .is_none_or(|batches| batches.len() != 1)
            || runs.len() != 1
            || runs[0]["function"] != 0
            || runs[0]["args"]
                .as_array()
                .is_none_or(|args| !args.is_empty())
            || runs[0]["float_zero_choices"]
                .as_array()
                .is_none_or(|choices| !choices.is_empty())
        {
            return Err(format!(
                "{filename}: expected one argument-free integer run and empty choices"
            ));
        }
        if original_resource_controls && (fuel != 10_000 || max_call_depth != 8) {
            return Err(format!("{filename}: original request budget changed"));
        }
        let execution = Execution {
            options: InterpretOptions {
                fuel,
                max_call_depth,
                ..InterpretOptions::default()
            },
            expected_reference_out_of_fuel: original_resource_controls
                && row["blocks"] == 4096
                && row["iterations"] == 1000,
        };
        let module: Module = match serde_json::from_value(request["batches"][0]["module"].clone()) {
            Ok(module) => module,
            Err(error) => {
                failures.push(json!({"case": filename, "phase": "source_schema", "error": error.to_string(), "executed": false}));
                continue;
            }
        };
        let shape = module.functions.len() == 1
            && module.functions[0].id == FuncId::new(0)
            && module.functions[0]
                .blocks
                .first()
                .is_some_and(|block| module.functions[0].entry == block.id)
            && module.functions[0].blocks.len() as u64 == row["blocks"].as_u64().unwrap_or(0)
            && module.target_info.as_ref().is_some_and(|target| {
                u64::from(target.pointer_size) * 8 == row["bits"].as_u64().unwrap_or(0)
            });
        if !shape {
            failures.push(json!({"case": filename, "phase": "source_shape", "executed": false}));
            continue;
        }
        match retain(
            output,
            filename,
            "original",
            &module,
            &module,
            (&request, &bytes),
            execution,
        ) {
            Ok(report) => accepted.push(report),
            Err(error) => {
                failures.push(json!({"case": filename, "phase": "source_validation_or_reference", "error": error}));
                continue;
            }
        }
        sources.push(json!({"case": filename, "sha256": sha256(&bytes), "bytes": bytes.len(),
            "bits": row["bits"], "blocks": row["blocks"], "iterations": row["iterations"], "sparse": row["sparse"],
            "function_ids": module.functions.iter().map(|f| f.id.index()).collect::<Vec<_>>(),
            "block_ids": module.functions[0].blocks.iter().map(|b| b.id.index()).collect::<Vec<_>>(),
            "function_ast_sha256": sha256(&serde_json::to_vec(&module.functions).expect("function AST JSON")),
            "validated_before_execution": true,
            "reference_kind": accepted.last().expect("source observation")["reference"]["kind"],
            "fuel": fuel, "call_depth": max_call_depth}));
        let stem = filename.strip_suffix(".json").unwrap_or(filename);
        let binary = trust_ir::binary::serialize_module(&module)
            .map_err(|error| format!("{filename}: binary encode: {error:?}"))?;
        let json_bytes = serde_json::to_vec(&module).map_err(|error| error.to_string())?;
        let msgpack = rmp_serde::to_vec(&module).map_err(|error| error.to_string())?;
        let mut carriers = vec![
            (
                "binary",
                "tmbc",
                binary.clone(),
                trust_ir::binary::deserialize_module(&binary).map_err(|error| format!("{error:?}")),
            ),
            (
                "json",
                "json",
                json_bytes.clone(),
                serde_json::from_slice(&json_bytes).map_err(|error| error.to_string()),
            ),
            (
                "msgpack",
                "mpk",
                msgpack.clone(),
                rmp_serde::from_slice(&msgpack).map_err(|error| error.to_string()),
            ),
        ];
        match trust_ir::format::text_checked(&module) {
            Ok(text) => {
                let decoded =
                    trust_ir::parser::parse_module(&text).map_err(|error| format!("{error:?}"));
                carriers.push(("text", "tir", text.into_bytes(), decoded));
            }
            Err(error) => {
                let report = json!({"case": filename, "sparse": row["sparse"], "admission_credit": false,
                    "executed": false, "error": error.to_string(),
                    "losses": error.losses.iter().map(|loss| json!({"kind": format!("{:?}", loss.kind()),
                        "display": loss.to_string(), "debug": format!("{loss:?}")})).collect::<Vec<_>>()});
                std::fs::write(
                    output.join(format!("refusals/{stem}.text.json")),
                    serde_json::to_vec_pretty(&report).expect("refusal JSON"),
                )
                .map_err(|error| error.to_string())?;
                refusals.push(report);
            }
        }
        for (carrier, extension, wire, decoded) in carriers {
            let relative = format!("carriers/{stem}.{carrier}.{extension}");
            std::fs::write(output.join(&relative), &wire).map_err(|error| error.to_string())?;
            match decoded {
                Ok(decoded) => match retain(
                    output,
                    filename,
                    carrier,
                    &module,
                    &decoded,
                    (&request, &bytes),
                    execution,
                ) {
                    Ok(mut report) => {
                        report["wire"] = json!(relative);
                        report["wire_sha256"] = json!(sha256(&wire));
                        report["wire_bytes"] = json!(wire.len());
                        accepted.push(report);
                    }
                    Err(error) => failures.push(json!({"case": filename, "carrier": carrier,
                        "phase": "transport_validation_or_reference", "error": error})),
                },
                Err(error) => failures.push(json!({"case": filename, "carrier": carrier,
                    "phase": "carrier_decode", "error": error, "executed": false})),
            }
        }
    }
    let exact_values = accepted
        .iter()
        .filter(|r| r["reference"]["kind"] == "exact_i32_42")
        .count();
    let fuel_controls = accepted
        .iter()
        .filter(|r| r["reference"]["kind"] == "reference_only_out_of_fuel")
        .count();
    let summary = json!({"input_inventory_sha256": sha256(&inventory_bytes),
        "input_source_cases": cases.len(), "source_modules_validated": sources.len(),
        "retained_carrier_modules_validated": accepted.len(), "exact_i32_42_carriers": exact_values,
        "reference_only_out_of_fuel_controls": fuel_controls,
        "original_resource_control_mode": original_resource_controls,
        "checked_text_refusals": refusals.len(), "failures": failures,
        "source_cases": sources, "accepted": accepted, "text_refusals": refusals,
        "reference_only_unverified_lane": true, "Lean_or_native_oracle_or_timing_executed": false});
    std::fs::write(
        output.join("validation.json"),
        serde_json::to_vec_pretty(&summary).expect("validation JSON"),
    )
    .map_err(|error| error.to_string())?;
    println!(
        "{} source cases; {} validated carriers ({} exact I32(42), {} reference-only OOF); {} checked-text refusals; {} failures",
        cases.len(),
        accepted.len(),
        exact_values,
        fuel_controls,
        refusals.len(),
        failures.len()
    );
    Ok(failures.len())
}

fn main() {
    let args: Vec<_> = std::env::args_os().collect();
    if !(args.len() == 3 || (args.len() == 4 && args[3] == "--original-resource-controls")) {
        eprintln!(
            "usage: decoded_cfg_inputs REQUEST_DIRECTORY OUTPUT_DIRECTORY [--original-resource-controls]"
        );
        std::process::exit(2);
    }
    match run(Path::new(&args[1]), Path::new(&args[2]), args.len() == 4) {
        Ok(0) => {}
        Ok(_) => std::process::exit(1),
        Err(error) => {
            eprintln!("{error}");
            std::process::exit(1);
        }
    }
}
