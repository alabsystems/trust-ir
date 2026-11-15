// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;

#[test]
fn empty_physical_function_table_returns_exact_empty_loop_diagnostics() {
    assert!(
        run(&Module::new("empty"), ImportPolicy::Structural)
            .0
            .is_empty()
    );
}
#[test]
fn summary_then_body_effect_then_rust_vararg_keep_exact_original_order() {
    let m = fixture();
    let out = run(&m, ImportPolicy::Structural).0;
    assert_eq!(
        out,
        vec![
            summary_error("requires clause 0 has an empty schema"),
            ValidationError::EffectSummaryViolated {
                function: "firstλ\0".into(),
                effect: "allocates",
                block: 7,
                inst: "heapalloc".into()
            },
            ValidationError::RustAbiVararg {
                function: 7,
                detail: format!(
                    "{:?} declares the Rust calling convention with variadic functy.0 (0 fixed parameter(s))",
                    "firstλ\0"
                )
            },
        ]
    );
}
#[test]
fn duplicate_physical_ids_never_deduplicate_or_reorder_function_rows() {
    let mut m = fixture();
    m.functions.push(function(7, "second尾", true));
    let out = run(&m, ImportPolicy::Structural).0;
    assert_eq!(out.len(), 6);
    for (part, name) in out.as_chunks::<3>().0.iter().zip(["firstλ\0", "second尾"]) {
        assert_eq!(
            part[0],
            summary_error("requires clause 0 has an empty schema")
        );
        assert!(
            matches!(&part[1], ValidationError::EffectSummaryViolated {function,effect:"allocates",block:7,inst} if function==name && inst=="heapalloc")
        );
        assert!(
            matches!(&part[2], ValidationError::RustAbiVararg {function:7,detail} if detail.starts_with(&format!("{name:?} declares")))
        );
    }
}
#[test]
fn absent_summary_skips_its_body_effects_but_preserves_the_independent_abi_rule() {
    let mut m = fixture();
    m.functions[0].summary = None;
    let out = run(&m, ImportPolicy::Refuse).0;
    assert_eq!(out.len(), 1);
    assert!(matches!(
        &out[0],
        ValidationError::RustAbiVararg { function: 7, .. }
    ));
    m.functions[0].summary = Some(FunctionSummary::new());
    assert_eq!(run(&m, ImportPolicy::Structural).0, out);
}
#[test]
fn declaration_and_missing_signature_paths_preserve_each_original_guard() {
    let mut m = fixture();
    m.functions[0].blocks.clear();
    assert_eq!(run(&m, ImportPolicy::Structural).0.len(), 2); // Schema + ABI, no body effect.
    m.functions[0].calling_conv = CallingConv::C;
    assert_eq!(
        run(&m, ImportPolicy::Refuse).0,
        vec![summary_error("requires clause 0 has an empty schema")]
    );
    m.functions[0].summary = None;
    m.functions[0].calling_conv = CallingConv::Rust;
    m.functions[0].ty = FuncTyId::new(u32::MAX);
    assert!(run(&m, ImportPolicy::Structural).0.is_empty());
}
#[test]
fn the_same_import_policy_reaches_the_actual_complete_summary_child() {
    let mut m = fixture();
    m.func_types[0].is_vararg = false;
    m.functions[0].blocks.clear();
    let s = m.functions[0].summary.as_mut().unwrap();
    s.requires = vec![ProofFormula::new("opaque", "raw clause")];
    s.proved = true;
    s.backed_by = Some(ExternRef::new(ImportId::new(0), "far").relying_on(ProofId::new(1)));
    m.imports
        .push(ModuleImport::new("dep", ProofDigest::sha256([4; 32])));
    assert!(run(&m, ImportPolicy::Structural).0.is_empty());
    assert_eq!(run(&m, ImportPolicy::Refuse).0.len(), 1);
    let auth = crate::linked::AuthenticatedImports::default();
    assert_eq!(run(&m, ImportPolicy::Authenticated(&auth)).0.len(), 1);
    assert!(auth.digests().is_empty() && auth.authenticated_inheritances().is_empty());
}
#[test]
fn full_raw_function_text_reaches_effect_and_debug_abi_errors_without_extra_rules() {
    let mut m = fixture();
    let name = "λ\0'\"\\\n尾".repeat(600) + "FUNCTIONTAIL";
    m.functions[0].name = name.clone();
    m.functions[0].display_path = Some("unread metadata".repeat(1000));
    let out = run(&m, ImportPolicy::Structural).0;
    assert_eq!(out.len(), 3);
    assert!(
        matches!(&out[1], ValidationError::EffectSummaryViolated {function,..} if function==&name)
    );
    assert!(
        matches!(&out[2], ValidationError::RustAbiVararg {detail,..} if detail==&format!("{name:?} declares the Rust calling convention with variadic functy.0 (0 fixed parameter(s))"))
    );
}
