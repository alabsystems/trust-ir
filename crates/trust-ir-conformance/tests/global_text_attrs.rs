// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! The global-symbol portion of WS4.5: text preserves link-time attributes
//! without weakening the refusals for fields it still cannot carry.

use trust_ir::binary::serialize_module;
use trust_ir::format::{TextLoss, canonical_checked, canonicalize, text_losses};
use trust_ir::parser::parse_module;
use trust_ir::ty::Ty;
use trust_ir::{Global, Linkage, Module, TlsModel, Visibility};

fn module() -> Module {
    let mut m = Module::new("globals");
    m.globals.push(Global {
        name: "REGISTRY".into(),
        ty: Ty::U64,
        mutable: true,
        initializer: None,
        linkage: Linkage::Internal,
        tls: Some(TlsModel::LocalExec),
        align: Some(16),
        section: None,
        visibility: Visibility::Default,
        retained: false,
    });
    m
}

#[test]
fn global_attributes_preserve_structure_binary_and_digest_through_text() {
    let sections = [
        None,
        Some(""),
        Some("__DATA,__mysection"),
        Some("quotes\" and \\ slashes; #retained: false\n\r\t\0\u{1}\u{7f} λ🦀"),
        Some("\") retained @INJECTED u64\nglobal @EXTRA u64"),
    ];
    for section in sections {
        for visibility in [
            Visibility::Default,
            Visibility::Hidden,
            Visibility::Protected,
        ] {
            for retained in [false, true] {
                let mut m = module();
                m.globals[0].section = section.map(str::to_owned);
                m.globals[0].visibility = visibility;
                m.globals[0].retained = retained;
                let canonical = canonicalize(&m);
                let text = canonical_checked(&m).expect("all global fields have spellings");
                let back = parse_module(&text).expect("global text parses");
                assert_eq!(back, canonical, "{text}");
                assert_eq!(
                    serialize_module(&back).expect("serialize_module: test fixture"),
                    serialize_module(&canonical).expect("serialize_module: test fixture")
                );
                assert_eq!(back.stable_digest(), canonical.stable_digest());
                assert_eq!(canonical_checked(&back).unwrap(), text);
            }
        }
    }
}

#[test]
fn legacy_global_syntax_keeps_defaults_and_canonical_bytes() {
    let m = module();
    let text = canonical_checked(&m).unwrap();
    assert!(text.contains("global internal tls(local_exec) mut align(16) @REGISTRY u64"));
    assert!(!text.contains("visibility("));
    assert!(!text.contains("section("));
    assert!(!text.contains("retained"));
    assert_eq!(parse_module(&text).unwrap(), canonicalize(&m));

    // Explicit default visibility reads as the same value; printing stays
    // sparse, so adding this grammar does not churn legacy text goldens.
    let explicit = text.replace("@REGISTRY", "visibility(default) @REGISTRY");
    assert_eq!(
        canonical_checked(&parse_module(&explicit).unwrap()).unwrap(),
        text
    );
}

#[test]
fn malformed_duplicate_and_unknown_global_attributes_are_refused() {
    let base = canonical_checked(&module()).unwrap();
    for attrs in [
        "visibility(unknown)",
        "visibility()",
        "visibility(hidden",
        "visibility(hidden) visibility(default)",
        "section(unquoted)",
        "section(\"unterminated)",
        "section(\"one\") section(\"two\")",
        "retained retained",
        "retained(false)",
        "retained_extra",
        "retained visibility(hidden)",
        "unknown(\"attribute\")",
    ] {
        let text = base.replace("@REGISTRY", &format!("{attrs} @REGISTRY"));
        assert!(parse_module(&text).is_err(), "accepted {attrs}: {text}");
    }
}

#[test]
fn dropping_any_global_attribute_changes_the_binary_identity() {
    let mut m = module();
    m.globals[0].section = Some("registry".into());
    m.globals[0].visibility = Visibility::Hidden;
    m.globals[0].retained = true;
    let text = canonical_checked(&m).unwrap();
    for clause in [" visibility(hidden)", " section(\"registry\")", " retained"] {
        assert_eq!(text.matches(clause).count(), 1);
        let mutant = parse_module(&text.replace(clause, "")).unwrap();
        assert_ne!(mutant.globals, m.globals, "{clause}");
        assert_ne!(
            serialize_module(&mutant).expect("serialize_module: test fixture"),
            serialize_module(&m).expect("serialize_module: test fixture"),
            "{clause}"
        );
        assert_ne!(mutant.stable_digest(), m.stable_digest(), "{clause}");
    }
}

/// WS4.5: global assembly is CARRIED beside the global attributes (it was a
/// `#lossy` refusal until then). Two blocks keep their order, the module
/// round-trips exactly, and the `GlobalAsmNotConsumable { blocks: 2 }`
/// codegen refusal survives the text round trip.
#[test]
fn global_assembly_is_carried_with_global_attributes() {
    let mut m = module();
    m.globals[0].section = Some("registry".into());
    m.globals[0].visibility = Visibility::Protected;
    m.globals[0].retained = true;
    m.global_asm.push(".globl external_symbol".into());
    m.global_asm.push("external_symbol:\n  ret".into());
    assert_eq!(text_losses(&m), Vec::<TextLoss>::new());
    let text = canonical_checked(&m).expect("carried");
    let back = parse_module(&text).expect("parses");
    assert_eq!(back, trust_ir::format::canonicalize(&m));
    assert_eq!(back.global_asm, m.global_asm);
    assert_eq!(back.stable_digest(), m.stable_digest());
    let refusal = |module: &trust_ir::Module| {
        trust_ir_build::validate_module_for_codegen(module)
            .into_iter()
            .any(|e| {
                matches!(
                    e,
                    trust_ir_build::ValidationError::GlobalAsmNotConsumable { blocks: 2 }
                )
            })
    };
    assert!(refusal(&m) && refusal(&back));
    // Block ORDER is identity: swapping the two lines is a different module.
    let swapped = parse_module(
        &text
            .replacen("global_asm \".globl external_symbol\"\n", "", 1)
            .replacen(
                "global_asm \"external_symbol:\\n  ret\"\n",
                "global_asm \"external_symbol:\\n  ret\"\nglobal_asm \".globl external_symbol\"\n",
                1,
            ),
    )
    .expect("parses");
    assert_eq!(swapped.global_asm.len(), 2);
    assert_ne!(swapped.global_asm, m.global_asm);
}
