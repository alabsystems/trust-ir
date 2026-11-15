// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// WS4.19 / F-082: the lexical-scope INLINING CHAIN (`ScopeData.inlined_at`).
//
// Before this increment `grep inlined_at crates/trust-ir/src` was empty: a
// scope could say where it opened but never that it was the body of an
// inlined callee, so after cross-language inlining a bounds-check obligation
// sited inside a Clean island had no way to say "inlined from caller.rs:12"
// and debug info attributed the island to its Rust caller's scope. The two
// proof-program rows below asserted exactly that absence; they flip here.
//
// What this file pins:
//   * the chain round-trips LOSSLESSLY through the text, JSON and MessagePack
//     formats (positive fixture);
//   * the BINARY format has no carrier yet (the wire part of WS4.19 is a
//     member of the next open wire batch, reserved first per
//     `docs/wire-allocation.md`), and every binary entry point REFUSES the
//     module with the named `InlinedScopeChainUnencodable` instead of
//     dropping the chain — the ratchet this row will flip again when the
//     wire batch lands;
//   * a module WITHOUT a chain keeps its exact pre-WS4.19 JSON and
//     MessagePack bytes (sole trailing skipped field), and a pre-WS4.19
//     positional `[parent, span]` array decodes with no chain;
//   * the text directive refuses a link with no callee (negative twin);
//   * `trust_ir::diff` treats a changed link as DEBUG metadata: excluded by
//     default, reported as the `scopes` row under `include_debug`
//     (mutation control, WS4.13).

use trust_ir::diff::{DiffOptions, diff_with};
use trust_ir::{InlinedAt, Module, Producer, ScopeData, SourceSpan, Ty};
use trust_ir_build::{ModuleBuilder, validate_module};

const CALLEE: &str = "clean::island::checked_index \"quoted\"";

/// `fn caller(x: u32) -> u32 { checked_index(x) }` after the Clean island
/// `checked_index` was inlined: the add sits in scope #1, whose chain link
/// says it came from `CALLEE` at `caller.rs:12:9`; the island's own source
/// position (`island.clean:3:1`) is scope #1's opening span.
fn module_with_chain() -> Module {
    let mut mb = ModuleBuilder::new("ws4_19_chain");
    let caller_rs = mb.intern_file("src/caller.rs");
    let island = mb.intern_file("src/island.clean");
    let sig = mb.add_func_type(vec![Ty::U32], vec![Ty::U32]);
    let mut fb = mb.function("caller", sig);
    fb.set_producer(Producer::TRust);
    fb.set_display_path("demo::caller");
    fb.set_scopes(vec![
        ScopeData::new(
            None,
            Some(SourceSpan {
                file: caller_rs,
                line: 10,
                col: 1,
            }),
        ),
        ScopeData {
            parent: Some(0),
            span: Some(SourceSpan {
                file: island,
                line: 3,
                col: 1,
            }),
            inlined_at: Some(InlinedAt {
                span: SourceSpan {
                    file: caller_rs,
                    line: 12,
                    col: 9,
                },
                callee: CALLEE.to_string(),
            }),
        },
    ]);
    let entry = fb.create_block();
    let x = fb.add_block_param(entry, Ty::U32);
    fb.switch_to_block(entry);
    fb.set_scope(1);
    fb.set_span(SourceSpan {
        file: island,
        line: 4,
        col: 5,
    });
    let one = fb.iconst(Ty::U32, 1);
    let sum = fb.add(Ty::U32, x, one);
    fb.set_scope(0);
    fb.set_span(SourceSpan {
        file: caller_rs,
        line: 13,
        col: 1,
    });
    fb.ret(vec![sum]);
    fb.set_value_names(vec![(x, "x".to_string()), (sum, "index".to_string())]);
    fb.build();
    mb.build().expect("ModuleBuilder::build: test fixture")
}

fn chain_of(m: &Module) -> &InlinedAt {
    m.functions[0].scopes.as_ref().expect("scopes")[1]
        .inlined_at
        .as_ref()
        .expect("scope #1 carries the chain link")
}

/// Proof-program row `trust-ir-self-declared/debug-info-inlining-chain`
/// (GAP -> PASS): the call-site chain IS recordable, validates, and survives
/// the three formats that carry it exactly.
#[test]
fn ratchet_debug_info_inlining_chain() {
    let m = module_with_chain();
    assert!(
        validate_module(&m).is_empty(),
        "a well-formed chain validates: {:?}",
        validate_module(&m)
    );
    let link = chain_of(&m);
    assert_eq!(link.callee, CALLEE);
    assert_eq!(m.files[link.span.file as usize], "src/caller.rs");
    assert_eq!((link.span.line, link.span.col), (12, 9));

    // Text: the `; #scope:` directive spells the link, and the parser reads
    // it back. Canonical text is idempotent over it.
    let text = m.to_string();
    assert!(
        text.contains("; #scope: 1 parent=0 at 1 3 1 inlined-at 0 12 9 callee \"clean::island::checked_index \\\"quoted\\\"\""),
        "text directive must spell the chain link:\n{text}"
    );
    let from_text = trust_ir::parser::parse_module(&text).expect("text parse");
    assert_eq!(from_text.functions[0].scopes, m.functions[0].scopes);
    let canon = trust_ir::format::canonical(&m);
    let from_canon = trust_ir::parser::parse_module(&canon).expect("canonical parse");
    assert_eq!(canon, trust_ir::format::canonical(&from_canon));
    assert_eq!(from_canon.functions[0].scopes, m.functions[0].scopes);

    // JSON and MessagePack: lossless.
    let json = serde_json::to_string(&m).expect("json");
    let from_json: Module = serde_json::from_str(&json).expect("json decode");
    assert_eq!(from_json, m);
    let mp = rmp_serde::to_vec(&m).expect("msgpack");
    let from_mp: Module = rmp_serde::from_slice(&mp).expect("msgpack decode");
    assert_eq!(from_mp, m);
}

/// Proof-program row `small-designs/OMET-06-debug-and-provenance-carriers`
/// (partial -> PASS for the inlining-chain debt): every node carries a span
/// AND a scope, locals are named, the producer tag is stamped, and the scope
/// tree with its chain link crosses text / JSON / MessagePack unchanged. The
/// coverage-map carrier stays a documented non-goal (DECIDE deferred to the
/// trust-cg debug-info owner: a sidecar keyed by `executable_content_digest_v1`).
#[test]
fn ratchet_omet06_debug_and_provenance_carriers() {
    let m = module_with_chain();
    let f = &m.functions[0];
    assert_eq!(f.producer, Some(Producer::TRust));
    assert_eq!(f.display_path.as_deref(), Some("demo::caller"));
    let names = f.value_names.as_ref().expect("value names");
    assert_eq!(names.len(), 2);
    for block in &f.blocks {
        for node in &block.body {
            assert!(node.span.is_some(), "every node carries a span");
            assert!(node.scope.is_some(), "every node names its scope");
        }
    }
    // The node inside the inlined body resolves, through its scope's chain
    // link, to "inlined from src/caller.rs:12:9 (callee)".
    let add_scope = f.blocks[0].body[0].scope.expect("scope");
    let scopes = f.scopes.as_ref().expect("scopes");
    let link = scopes[add_scope as usize]
        .inlined_at
        .as_ref()
        .expect("the inlined body's scope carries its chain link");
    assert_eq!(m.files[link.span.file as usize], "src/caller.rs");
    // And the walk up `parent` ends at the caller's own (un-inlined) root.
    let root = scopes[add_scope as usize].parent.expect("non-root");
    assert!(scopes[root as usize].inlined_at.is_none());

    for (name, back) in [
        (
            "text",
            trust_ir::parser::parse_module(&m.to_string()).expect("text"),
        ),
        (
            "json",
            serde_json::from_str(&serde_json::to_string(&m).expect("json")).expect("json"),
        ),
        (
            "msgpack",
            rmp_serde::from_slice(&rmp_serde::to_vec(&m).expect("msgpack")).expect("msgpack"),
        ),
    ] {
        let g = &back.functions[0];
        assert_eq!(g.scopes, f.scopes, "{name}: scope tree + chain");
        assert_eq!(g.value_names, f.value_names, "{name}: value names");
        assert_eq!(g.producer, f.producer, "{name}: producer");
        for (a, b) in f.blocks[0].body.iter().zip(&g.blocks[0].body) {
            assert_eq!(a.span, b.span, "{name}: node span");
            assert_eq!(a.scope, b.scope, "{name}: node scope");
        }
    }
}

/// The binary format has NO carrier for the chain yet, and it says so by
/// name rather than dropping the link: the fallible projection returns
/// `InlinedScopeChainUnencodable`, and the infallible writers panic with the
/// same message. (Flips to a lossless round trip when the wire batch lands.)
#[test]
fn binary_refuses_inlined_scope_chain_by_name() {
    use trust_ir::binary::{
        BinaryProjectionError, ModuleBinaryOptions, ProjectedModuleBinaryPlan,
        first_inlined_scope_chain,
    };
    let m = module_with_chain();
    assert_eq!(first_inlined_scope_chain(&m), Some((0, 1)));
    let err = ProjectedModuleBinaryPlan::try_new(&m, ModuleBinaryOptions::default())
        .err()
        .expect("projection must refuse the chain");
    assert_eq!(
        err,
        BinaryProjectionError::InlinedScopeChainUnencodable {
            function: 0,
            scope: 1
        }
    );
    assert!(err.to_string().contains("ScopeData.inlined_at"));

    // The blob entry refuses with the same typed refusal, never a panic (D1b).
    let refused = std::panic::catch_unwind(|| trust_ir::binary::serialize_module(&m))
        .expect("serialize_module never panics")
        .expect_err("serialize_module must refuse rather than drop the chain");
    assert_eq!(refused, err, "the blob entry names the same refusal");

    // Control: the same module with the link removed encodes at the legacy
    // header and round-trips — the refusal is about the chain, nothing else.
    let mut plain = m.clone();
    plain.functions[0].scopes.as_mut().unwrap()[1].inlined_at = None;
    assert_eq!(first_inlined_scope_chain(&plain), None);
    let bytes = trust_ir::binary::serialize_module(&plain).expect("serialize_module: test fixture");
    let back = trust_ir::binary::deserialize_module(&bytes).expect("decode");
    assert_eq!(back.functions[0].scopes, plain.functions[0].scopes);
}

/// A module without a chain keeps its pre-WS4.19 serde bytes: the field is
/// the sole trailing conditionally-skipped one, so JSON carries no
/// `inlined_at` key and the positional MessagePack array stops at `span`.
/// A pre-WS4.19 two-element array decodes with no chain.
#[test]
fn absent_chain_keeps_legacy_serde_shape() {
    let plain = ScopeData::new(Some(0), None);
    let json = serde_json::to_string(&plain).expect("json");
    assert_eq!(json, r#"{"parent":0,"span":null}"#);
    let mp = rmp_serde::to_vec(&plain).expect("msgpack");
    // fixarray(2) [ 0, nil ]
    assert_eq!(mp, vec![0x92, 0x00, 0xc0]);
    let back: ScopeData = rmp_serde::from_slice(&mp).expect("legacy positional array");
    assert_eq!(back, plain);
    let back: ScopeData = serde_json::from_str(r#"{"parent":0,"span":null}"#).expect("legacy json");
    assert_eq!(back, plain);

    // With a link, the third element appears and round-trips.
    let linked = ScopeData {
        inlined_at: Some(InlinedAt {
            span: SourceSpan {
                file: 0,
                line: 1,
                col: 2,
            },
            callee: "f".into(),
        }),
        ..plain
    };
    let mp = rmp_serde::to_vec(&linked).expect("msgpack");
    assert_eq!(
        mp[0], 0x93,
        "three positional elements once the link is set"
    );
    let back: ScopeData = rmp_serde::from_slice(&mp).expect("decode");
    assert_eq!(back, linked);
    let json = serde_json::to_string(&linked).expect("json");
    assert!(json.contains(r#""inlined_at":{"span":{"file":0,"line":1,"col":2},"callee":"f"}"#));
}

/// Negative twin (text): a link that names no callee is refused by the
/// parser — it is not decoded with a placeholder callee.
#[test]
fn text_refuses_inlined_at_without_callee() {
    let m = module_with_chain();
    let text = m.to_string();
    let needle = " callee \"clean::island::checked_index \\\"quoted\\\"\"";
    assert!(text.contains(needle));
    let truncated = text.replacen(needle, "", 1);
    let err = trust_ir::parser::parse_module(&truncated)
        .expect_err("inlined-at without callee must be refused");
    assert!(
        err.to_string().contains("callee"),
        "refusal names the missing clause: {err}"
    );
    // Control: the untouched text parses.
    trust_ir::parser::parse_module(&text).expect("control parses");
}

/// Mutation control (WS4.13): a changed chain link is DEBUG metadata. The
/// default diff ignores it (so does `--ignore-proofs`); `include_debug`
/// reports it as the `scopes` row and nothing else.
#[test]
fn diff_reports_changed_inlined_at_only_under_include_debug() {
    let a = module_with_chain();
    let mut b = a.clone();
    let link = b.functions[0].scopes.as_mut().unwrap()[1]
        .inlined_at
        .as_mut()
        .unwrap();
    link.span.line = 99;
    link.callee = "clean::island::other".into();

    for opts in [
        DiffOptions::default(),
        DiffOptions {
            ignore_proofs: true,
            ..DiffOptions::default()
        },
    ] {
        let d = diff_with(&a, &b, opts);
        assert!(
            d.is_empty(),
            "a chain link is excluded by default (ignore_proofs={}): {}",
            opts.ignore_proofs,
            d.to_text()
        );
    }

    let d = diff_with(
        &a,
        &b,
        DiffOptions {
            include_debug: true,
            ..DiffOptions::default()
        },
    );
    assert!(!d.is_empty(), "include_debug must surface the changed link");
    let text = d.to_text();
    assert!(
        text.contains("scopes"),
        "reported as the scopes row: {text}"
    );
    assert!(
        text.contains("inlined-at 0 99 9") && text.contains("clean::island::other"),
        "the row renders the new link: {text}"
    );
    // Only the debug row moved: no block or instruction change is reported.
    let json = d.to_json();
    assert!(json.contains("\"scopes\""), "{json}");
    assert!(
        !json.contains("\"body_gate\""),
        "authority rows untouched: {json}"
    );

    // Control for the lane: with the SAME module on both sides, include_debug
    // reports nothing — the option adds a row only when the tree differs.
    assert!(
        diff_with(
            &a,
            &a,
            DiffOptions {
                include_debug: true,
                ..DiffOptions::default()
            }
        )
        .is_empty()
    );
}
