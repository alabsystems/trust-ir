// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// Roadmap WS4.2 (finding F-065; interim guard for F-064 / F-070 / F-072):
// text fails closed until it is total.
//
// Before WS4.2 a text round trip SILENTLY dropped every field the grammar
// could not carry, and the parser skipped every line / directive / node clause
// it did not know. The permissive case: `global_asm` vanished, and with it
// the `GlobalAsmNotConsumable` codegen refusal. Now `format::text_losses`
// names every such field, `format::canonical_checked` refuses, the human
// `Display` dump carries a `; #lossy:` marker, and the parser refuses the
// marker and every unknown directive.
//
// This file ports the proof-program ratchet rows that flip GAP -> PASS here
// (archived at reports/2026-09-17-two-language-proof-program/): each test is
// named after its row. It runs in standing gate 8 (`wire-format-goldens`).
//
//   * positive      — `c08_t0_control`: a loss-free module prints through
//                     `canonical_checked` and keeps its digest through text;
//   * negative twin — the c08 T1 module (ONE `global_asm` block) was refused
//                     with the named `GlobalAsm { blocks: 1 }` loss until
//                     WS4.5 CARRIED the block (`global_asm "<escaped>"`); it
//                     now round-trips EXACTLY and keeps its codegen refusal;
//   * mutation      — `strict_parser_refuses_a_newer_printers_directive`: a
//                     `; #contract:` line a newer printer might write is a
//                     `ParseError`, not `Ok` with the field missing.
//
// WS4.4 (F-064, F-070) CLOSES the two interim `b7.text.flip.*` rows: the
// summary and the kernel re-check directive are now CARRIED, so the refusal
// (resp. the certification) SURVIVES a text round trip instead of being
// refused at print time. Those rows, with their mutation controls, live only
// in gate 11's ledger (`two_language/b7_codec_and_semantics_gaps.rs`).

use trust_ir::format::{TextLoss, canonical, canonical_checked, text_losses};
use trust_ir::parser::parse_module;
use trust_ir::proof::ProofEvidence;
use trust_ir::ty::{FuncTy, Ty};
use trust_ir::value::{FuncId, ProofId};
use trust_ir::{BodyGate, Endianness, Function, Module, ModuleImport, Producer, TargetInfo};
use trust_ir_build::{
    ModuleBuilder, ValidationError, validate_module, validate_module_for_codegen,
};

/// The parser's refusal of a `#lossy` text, asserted by substring.
const LOSSY_REFUSAL: &str = "this text was printed LOSSILY (";

/// `fn <name>() -> u64 { 41 }` carrying `gate`.
fn gated_module(name: &str, gate: BodyGate) -> Module {
    let mut mb = ModuleBuilder::new("c08");
    let ft = mb.add_func_type(vec![], vec![Ty::U64]);
    let mut fb = mb.function(name, ft);
    fb.set_producer(Producer::TRust);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let v = fb.uconst(Ty::U64, 41);
    fb.ret(vec![v]);
    fb.build();
    let mut m = mb.build().expect("ModuleBuilder::build: test fixture");
    m.functions[0].body_gate = Some(gate);
    m
}

fn licensed() -> Module {
    gated_module(
        "entry",
        BodyGate::Gated {
            authority: "trust-verify".into(),
            evidence: None,
        },
    )
}

fn with_asm(mut m: Module) -> Module {
    m.global_asm.push(".globl _sneaky\n_sneaky:\n  ret".into());
    m
}

fn refused_as_lossy(text: &str) {
    let err = parse_module(text).expect_err("a #lossy text must not parse");
    assert!(
        err.message.contains(LOSSY_REFUSAL)
            && err
                .message
                .contains("re-emit from the binary/serde artifact"),
        "{err}"
    );
}

fn asm_refusal(errors: &[ValidationError]) -> bool {
    matches!(
        errors,
        [ValidationError::GlobalAsmNotConsumable { blocks: 1 }]
    )
}

// ---------------------------------------------------------------------------
// verify.c08 (both lenses) and b7.text.flip.global_asm_refusal_laundered
// ---------------------------------------------------------------------------

/// Positive control (c08 T0): a module with nothing text cannot carry prints
/// through `canonical_checked`, parses back EXACTLY, and keeps its digest.
#[test]
fn c08_t0_control_loss_free_module_keeps_its_digest() {
    let m = licensed();
    assert!(validate_module_for_codegen(&m).is_empty());
    assert!(text_losses(&m).is_empty());
    let text = canonical_checked(&m).expect("loss-free");
    assert!(!text.contains("#lossy"));
    let back = parse_module(&text).expect("parses");
    assert_eq!(back, trust_ir::format::canonicalize(&m));
    assert_eq!(back.stable_digest(), m.stable_digest());
}

/// Row `verify.c08.L1` (independent-reproduction lens, test T1), GAP -> PASS.
/// GAP asserted: `validate_module_for_codegen` = `[GlobalAsmNotConsumable {
/// blocks: 1 }]` before a text round trip and `[]` after, with the parse
/// reporting NO error. PASS (WS4.2): the refusal could not be laundered
/// because the text was refused as `#lossy`. PASS (WS4.5, final): text
/// CARRIES the block — `canonical_checked` is `Ok`, the parse is EXACT
/// (same module, same `stable_digest`), and the codegen refusal is the same
/// after the round trip as before it, exactly as through the three other
/// transports.
#[test]
fn verify_c08_l1_global_asm_refusal_cannot_be_laundered_through_text() {
    let m = with_asm(licensed());
    assert!(
        validate_module(&m).is_empty(),
        "carrying asm is well-formed"
    );
    assert!(asm_refusal(&validate_module_for_codegen(&m)));

    assert!(text_losses(&m).is_empty(), "{:?}", text_losses(&m));
    let text = canonical_checked(&m).expect("WS4.5: text carries global_asm");
    assert!(!text.contains("#lossy"), "{text}");
    assert!(
        text.contains("global_asm \".globl _sneaky\\n_sneaky:\\n  ret\"\n"),
        "{text}"
    );
    let back = parse_module(&text).expect("parses");
    assert_eq!(back, trust_ir::format::canonicalize(&m));
    assert_eq!(back.stable_digest(), m.stable_digest());
    assert!(
        asm_refusal(&validate_module_for_codegen(&back)),
        "text kept the refusal"
    );
    // The human dump is the same image: no marker, and it parses back too.
    let dump = m.to_string();
    assert!(!dump.contains("#lossy"), "{dump}");
    assert!(asm_refusal(&validate_module_for_codegen(
        &parse_module(&dump).expect("dump parses")
    )));

    // Controls: binary, JSON and MessagePack keep the block AND the refusal.
    let bin = trust_ir::binary::deserialize_module(
        &trust_ir::binary::serialize_module(&m).expect("serialize_module: test fixture"),
    )
    .expect("binary");
    let json: Module =
        serde_json::from_str(&serde_json::to_string(&m).expect("json")).expect("json back");
    let msgpack: Module =
        rmp_serde::from_slice(&rmp_serde::to_vec(&m).expect("msgpack")).expect("msgpack back");
    for (format, decoded) in [("binary", bin), ("json", json), ("msgpack", msgpack)] {
        assert!(
            asm_refusal(&validate_module_for_codegen(&decoded)),
            "{format} lost the refusal"
        );
    }
}

/// Mutation control: the codegen refusal after the text round trip is CAUSED
/// by the carried `global_asm` line — delete that one line from the text and
/// the parsed module is the asm-free twin, which codegen admits. So a parser
/// that dropped the line (the pre-WS4.2 behaviour) would be caught by the
/// exact-equality leg of the test above.
#[test]
fn verify_c08_l1_mutation_control_asm_free_twin_is_accepted() {
    let twin = licensed();
    assert!(validate_module_for_codegen(&twin).is_empty());
    let text = canonical_checked(&with_asm(twin.clone())).expect("carried");
    let dropped: String = text
        .lines()
        .filter(|line| !line.starts_with("global_asm "))
        .map(|line| format!("{line}\n"))
        .collect();
    assert_ne!(dropped, text);
    let back = parse_module(&dropped).expect("parses");
    assert_eq!(back, trust_ir::format::canonicalize(&twin));
    assert!(validate_module_for_codegen(&back).is_empty());
    assert_ne!(back.stable_digest(), with_asm(twin).stable_digest());
}

/// Row `verify.c08.L2` (by-design lens, test e1), GAP -> PASS. GAP asserted:
/// "global_asm is dropped" by text (and the other codegen refusal, the
/// `body_gate` license, survives because text carries it). PASS (WS4.2): the
/// asm was no longer dropped — it was REFUSED at print time. PASS (WS4.5,
/// final): the asm is CARRIED, like the license, and both refusals survive a
/// text round trip unchanged.
#[test]
fn verify_c08_l2_asm_is_refused_not_dropped_and_the_license_refusal_survives() {
    let m = with_asm(licensed());
    let back = parse_module(&canonical_checked(&m).expect("carried")).expect("parses");
    assert_eq!(back.global_asm, m.global_asm);
    assert!(asm_refusal(&validate_module_for_codegen(&back)));

    // Control: the license refusal is carried (unchanged from the GAP run).
    let ungated = gated_module("entry", BodyGate::Ungated);
    let before = validate_module_for_codegen(&ungated);
    assert!(!before.is_empty());
    let back = parse_module(&canonical_checked(&ungated).expect("loss-free")).expect("parses");
    assert_eq!(validate_module_for_codegen(&back), before);

    // Text is unauthenticated: a human who deletes the `global_asm` line gets
    // a parseable module WITHOUT the asm. For a dependency, the next layer
    // still catches that edit — the text image no longer matches the digest
    // its importer recorded (the by-design lens's e3).
    let edited: String = canonical(&m)
        .lines()
        .filter(|line| !line.starts_with("global_asm "))
        .map(|line| format!("{line}\n"))
        .collect();
    let laundered = parse_module(&edited).expect("the edited text parses");
    assert!(laundered.global_asm.is_empty());
    let mut root = Module::new("root");
    let id = root
        .intern_import(
            ModuleImport::new(m.name.clone(), m.stable_digest()).with_producer(Producer::TRust),
        )
        .expect("Module::intern_import: test fixture");
    let verdict = root.verify_import(id, &laundered).map(|_| ());
    assert!(
        format!("{verdict:?}").contains("DigestMismatch"),
        "{verdict:?}"
    );
}

// ---------------------------------------------------------------------------
// The strict parser (step 5)
// ---------------------------------------------------------------------------

/// Mutation control for the strict half: a `; #contract:` line a newer
/// printer might write returns `ParseError`, not `Ok` with the field missing.
/// Its control twin — the same text without the line — parses exactly.
/// (`#summary` was the example until WS4.4 gave it a grammar; a `#summary`
/// line in another spelling is refused by that grammar.)
#[test]
fn strict_parser_refuses_a_newer_printers_directive() {
    let m = licensed();
    let text = canonical_checked(&m).expect("loss-free");
    assert_eq!(
        parse_module(&text).expect("control"),
        trust_ir::format::canonicalize(&m)
    );
    let anchor = "    ; #body-gate: gated \"trust-verify\"\n";
    assert!(text.contains(anchor), "{text}");
    let newer = text.replacen(
        anchor,
        &format!("{anchor}    ; #contract: ensures \"(= 1 1)\" proved\n"),
        1,
    );
    let err = parse_module(&newer).expect_err("an unknown directive is refused");
    assert!(
        err.message
            .contains("unknown directive `#contract` — refusing rather than dropping it"),
        "{err}"
    );
    let misspelled = text.replacen(
        anchor,
        &format!("{anchor}    ; #summary: ensures \"(= 1 1)\" proved\n"),
        1,
    );
    assert!(
        parse_module(&misspelled)
            .expect_err("a malformed #summary line is refused")
            .message
            .contains("expected `proved` or `unproved` after #summary")
    );
    // The same for an unknown top-level line and an unknown node clause.
    // (`global_asm` was the example until WS4.5 gave it a spelling.)
    let top = format!("{text}\nmodule_asm \".globl _x\"\n");
    assert!(
        parse_module(&top)
            .expect_err("unknown top-level line")
            .message
            .contains("unknown directive `module_asm`")
    );
    let node = text.replacen("ret %0", "ret %0  ; #weight: 3", 1);
    assert_ne!(node, text);
    assert!(
        parse_module(&node)
            .expect_err("unknown node clause")
            .message
            .contains("unknown directive `#weight`")
    );
}

// ---------------------------------------------------------------------------
// WS4.2 adversarial review: losses the landing list missed
// ---------------------------------------------------------------------------
//
// Each input below had `text_losses(m) == []`, so `canonical_checked` said
// `Ok` — yet the text either parsed back to a DIFFERENT module (the NaN case:
// silent, and a miscompile once the constant is bitcast) or did not parse
// back at all (the non-finite bound and kernel-goal cases: the CLI's
// `convert --to text` wrote a file it could not read). Each is now a named
// loss, and each has a loss-free twin that round-trips EXACTLY.

/// `fn f() -> f64 { <value> }` as a raw module (no builder canonicalization).
fn float_const_module(value: f64) -> Module {
    use trust_ir::{Block, BlockId, Constant, Inst, InstrNode, ValueId};
    let mut m = Module::new("float_bits");
    let ft = m
        .add_func_type(FuncTy {
            abi: None,
            params: vec![],
            returns: vec![Ty::F64],
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut f = Function::new(FuncId::new(0), "f", ft, BlockId::new(0));
    let mut b = Block::new(BlockId::new(0));
    b.body.push(
        InstrNode::new(Inst::Const {
            ty: Ty::F64,
            value: Constant::Float(value),
        })
        .with_result(ValueId::new(0)),
    );
    b.body.push(InstrNode::new(Inst::Return {
        values: vec![ValueId::new(0)],
    }));
    f.blocks.push(b);
    m.try_add_function(f)
        .expect("Module::try_add_function: test fixture");
    m
}

fn float_global(value: f64) -> trust_ir::Global {
    trust_ir::Global {
        name: "g".into(),
        ty: Ty::F64,
        mutable: false,
        initializer: Some(trust_ir::Constant::Aggregate(vec![
            trust_ir::Constant::Float(value),
        ])),
        linkage: trust_ir::Linkage::External,
        tls: None,
        align: None,
        section: None,
        visibility: Default::default(),
        retained: false,
    }
}

fn assert_exact_text_round_trip(m: &Module) {
    let text = canonical_checked(m).expect("loss-free twin");
    assert!(!text.contains("#lossy"), "{text}");
    assert_eq!(
        parse_module(&text).expect("loss-free twin parses"),
        trust_ir::format::canonicalize(m)
    );
}

/// A NaN whose sign bit or payload is not `f64::NAN`'s prints as `NaN`, and
/// the parser rebuilds `f64::NAN`: before this review the round trip returned
/// `Ok` with a DIFFERENT constant (`-NaN` bitcast to `i64` is negative, the
/// rebuilt one positive). `Constant` equality is bit-exact, so this is a lost
/// field, and it is now refused with the named site.
#[test]
fn review_nan_sign_and_payload_are_refused_not_silently_canonicalized() {
    use trust_ir::format::FloatSite;
    for bits in [
        (-f64::NAN).to_bits(),
        0x7ff8_0000_0000_0001,
        0x7ff0_0000_0000_0001,
    ] {
        let value = f64::from_bits(bits);
        assert!(value.is_nan());
        // In an instruction constant.
        let m = float_const_module(value);
        let err = canonical_checked(&m).expect_err("non-canonical NaN is refused");
        assert_eq!(
            err.losses,
            vec![TextLoss::UnspellableFloat {
                site: FloatSite::FunctionBody,
                index: 0
            }],
            "{bits:#x}"
        );
        let dump = canonical(&m);
        assert!(dump.contains("; #lossy: unspellable-float(fn 0)"), "{dump}");
        refused_as_lossy(&dump);
        // In a (nested) global initializer.
        let mut m = Module::new("float_bits_global");
        m.globals.push(float_global(value));
        assert_eq!(
            text_losses(&m),
            vec![TextLoss::UnspellableFloat {
                site: FloatSite::GlobalConstant,
                index: 0
            }]
        );
        refused_as_lossy(&canonical(&m));
    }
    // Loss-free twins: the canonical NaN, the infinities and a signed zero
    // are spelled exactly and round-trip bit-for-bit.
    for value in [f64::NAN, f64::INFINITY, f64::NEG_INFINITY, -0.0, 5e-324] {
        assert_exact_text_round_trip(&float_const_module(value));
        let mut m = Module::new("float_bits_global");
        m.globals.push(float_global(value));
        assert_exact_text_round_trip(&m);
    }
}

/// `bounded_output(lo, hi)` and `gamma_crown <epsilon>` read their numbers
/// with a finite-only reader, so an `inf` / `NaN` there printed a text that
/// did NOT parse (`expected f64`) while `canonical_checked` returned `Ok` — a
/// `convert --to text` output its own reader refused. Now a named loss.
#[test]
fn review_non_finite_proof_floats_are_refused_not_printed_unparseable() {
    use trust_ir::format::FloatSite;
    use trust_ir::proof::{ProofAnnotation, ProofCertificate};
    for (lo, hi) in [
        (0.0, f64::INFINITY),
        (f64::NEG_INFINITY, 1.0),
        (0.0, f64::NAN),
    ] {
        // Function-level and node-level annotations are both walked.
        for on_node in [false, true] {
            let mut m = float_const_module(1.0);
            let bound = ProofAnnotation::BoundedOutput { lo, hi };
            if on_node {
                m.functions[0].blocks[0].body[0].proofs.push(bound);
            } else {
                m.functions[0].proofs.push(bound);
            }
            let err = canonical_checked(&m).expect_err("non-finite bound is refused");
            assert_eq!(
                err.losses,
                vec![TextLoss::UnspellableFloat {
                    site: FloatSite::FunctionBody,
                    index: 0
                }]
            );
            refused_as_lossy(&canonical(&m));
        }
    }
    let certificate = |epsilon: f64| ProofCertificate {
        obligation: ProofId::new(0),
        prover: "gamma".into(),
        evidence: ProofEvidence::GammaCrownBound {
            epsilon,
            verified_layers: 3,
        },
        assurance: None,
    };
    let mut m = Module::new("gamma");
    m.proof_certificates.push(certificate(0.5));
    m.proof_certificates.push(certificate(f64::INFINITY));
    assert_eq!(
        text_losses(&m),
        vec![TextLoss::UnspellableFloat {
            site: FloatSite::Certificate,
            index: 1
        }]
    );
    refused_as_lossy(&canonical(&m));
    // Loss-free twins: finite bounds and epsilons (signed zero, extremes).
    m.proof_certificates[1] = certificate(-0.0);
    assert_exact_text_round_trip(&m);
    let mut m = float_const_module(1.0);
    m.functions[0].proofs.push(ProofAnnotation::BoundedOutput {
        lo: -0.0,
        hi: 1e300,
    });
    assert_exact_text_round_trip(&m);
}

// ---------------------------------------------------------------------------
// WS4.5 (enum half): the `layout(..)` clause — F-072's enum-layout residue
// ---------------------------------------------------------------------------
//
// `EnumLayoutDescriptor` is NORMATIVE where present: a consumer must use its
// byte layout instead of synthesizing trust-ir's canonical tagged union. Text
// used to carry none of it, so `enum-layout(enum N)` refused every module the
// rustc-derived producer emits — measured on the two-language battery, where
// `convert --from bin --to text` failed on six fixtures naming only this.
// Text now carries every field of the descriptor, and refuses exactly the
// descriptors that contradict their own enum.

/// One enum per tag encoding, each with the descriptor shape the producer
/// really emits.
fn layout_enums() -> Module {
    use trust_ir::ty::{EnumDef, EnumLayoutDescriptor, EnumTagEncoding, EnumTagRepr, EnumVariant};
    use trust_ir::value::EnumId;
    let variant = |name: &str, fields: Vec<Ty>| EnumVariant {
        name: name.to_string(),
        fields,
        field_names: Vec::new(),
    };
    let mut m = Module::new("enum_layouts");
    // DIRECT, `repr(u64)`: tag at 0, payloads after it (the `Shape` fixture).
    m.add_enum(EnumDef {
        id: EnumId::new(0),
        name: "Shape".into(),
        variants: vec![
            variant("Circle", vec![Ty::U64]),
            variant("Rect", vec![Ty::U64, Ty::U64]),
            variant("Empty", vec![]),
        ],
        discriminants: Vec::new(),
        repr: Some(EnumTagRepr::U64),
        layout: Some(EnumLayoutDescriptor {
            encoding: EnumTagEncoding::Direct { tag_offset: 0 },
            size: 24,
            align: 8,
            variant_field_offsets: vec![vec![8], vec![8, 16], vec![]],
        }),
        origin: None,
    });
    // NICHE: `none` is a reserved value of the 4-byte payload lane.
    m.add_enum(EnumDef {
        id: EnumId::new(1),
        name: "OptIdx".into(),
        variants: vec![variant("some", vec![Ty::U32]), variant("none", vec![])],
        discriminants: Vec::new(),
        repr: None,
        layout: Some(EnumLayoutDescriptor {
            encoding: EnumTagEncoding::Niche {
                untagged_variant: 0,
                niche_variants_start: 1,
                niche_variants_end: 1,
                niche_start: 0xFFFF_FF01,
                niche_offset: 0,
                niche_ty: EnumTagRepr::U32,
            },
            size: 4,
            align: 4,
            variant_field_offsets: vec![vec![0], vec![]],
        }),
        origin: None,
    });
    // v37 UNTAGGED: no tag lane; the image IS the sole variant's payload.
    m.add_enum(EnumDef {
        id: EnumId::new(2),
        name: "Wrapper".into(),
        variants: vec![variant("only", vec![Ty::U64])],
        discriminants: Vec::new(),
        repr: None,
        layout: Some(EnumLayoutDescriptor {
            encoding: EnumTagEncoding::Untagged,
            size: 8,
            align: 8,
            variant_field_offsets: vec![vec![0]],
        }),
        origin: None,
    });
    m
}

/// All three tag encodings print a `layout(..)` clause, the module is
/// loss-free, and the text parses back structurally equal — including the
/// SHAPE each descriptor implies, which is the fact a consumer acts on.
#[test]
fn enum_layout_descriptors_are_carried_by_text() {
    use trust_ir::ty::Ty as T;
    let m = layout_enums();
    assert!(text_losses(&m).is_empty(), "{:?}", text_losses(&m));
    let text = canonical_checked(&m).expect("loss-free");
    assert!(!text.contains("#lossy"), "{text}");
    assert!(
        text.contains("layout(direct tag@0 size=24 align=8 offsets=[[8], [8, 16], []])")
            && text.contains(
                "layout(niche untagged=0 variants=1..=1 start=4294967041 lane=u32@0 \
                 size=4 align=4 offsets=[[0], []])"
            )
            && text.contains("layout(untagged size=8 align=8 offsets=[[0]])"),
        "{text}"
    );
    let back = parse_module(&text).expect("parses");
    assert_eq!(back, trust_ir::format::canonicalize(&m));
    // The descriptor is normative, so the fact worth pinning is the SIZE the
    // decoded module reports — 24 / 4 / 8, none of which the canonical
    // tagged-union recomputation would produce for these enums.
    for (id, bytes) in [(0u32, 24u64), (1, 4), (2, 8)] {
        let shape = back
            .ty_layout_shape(&T::Enum(trust_ir::value::EnumId::new(id)))
            .unwrap_or_else(|e| panic!("enum {id} has no shape after text: {e:?}"));
        assert_eq!(shape.size_bits / 8, bytes, "enum {id}");
    }
    // The three lossless transports agree with text, field for field.
    let bin = trust_ir::binary::deserialize_module(
        &trust_ir::binary::serialize_module(&m).expect("serialize_module: test fixture"),
    )
    .expect("binary");
    assert_eq!(bin.enums, back.enums);
}

/// The NARROWED residual, and the reason the loss arm stays: a descriptor that
/// contradicts its own enum is REFUSED (printed `#lossy`, no clause, parser
/// says no), never carried and never laundered. Each case below already makes
/// `Module::enum_layout_shape` fail closed, so nothing usable is refused.
#[test]
fn an_inconsistent_enum_layout_is_still_a_named_loss() {
    use trust_ir::ty::EnumTagEncoding;
    /// One way to contradict a descriptor: what it is called, and the edit.
    type Contradiction = (&'static str, fn(&mut Module));
    let mutate: &[Contradiction] = &[
        ("one offset list too few", |m| {
            m.enums[0]
                .layout
                .as_mut()
                .unwrap()
                .variant_field_offsets
                .pop();
        }),
        ("an offset outside the size", |m| {
            m.enums[0].layout.as_mut().unwrap().variant_field_offsets[0][0] = 4096;
        }),
        ("align is not a power of two", |m| {
            m.enums[0].layout.as_mut().unwrap().align = 3;
        }),
        ("the tag lane does not fit", |m| {
            m.enums[0].layout.as_mut().unwrap().encoding =
                EnumTagEncoding::Direct { tag_offset: 20 };
        }),
        ("the niche interval names no variant", |m| {
            if let EnumTagEncoding::Niche {
                niche_variants_end, ..
            } = &mut m.enums[1].layout.as_mut().unwrap().encoding
            {
                *niche_variants_end = 9;
            }
        }),
        ("untagged with two variants", |m| {
            let variant = m.enums[2].variants[0].clone();
            m.enums[2].variants.push(variant);
            m.enums[2]
                .layout
                .as_mut()
                .unwrap()
                .variant_field_offsets
                .push(vec![0]);
        }),
    ];
    for (what, break_it) in mutate {
        let mut m = layout_enums();
        break_it(&mut m);
        let losses = text_losses(&m);
        assert!(
            losses
                .iter()
                .any(|l| matches!(l, TextLoss::EnumLayout { .. })),
            "{what}: wanted a named EnumLayout loss, got {losses:?}"
        );
        let dump = canonical(&m);
        assert!(
            dump.contains("; #lossy: enum-layout(enum "),
            "{what}: {dump}"
        );
        refused_as_lossy(&dump);
        // Erasing exactly the refused field makes the module loss-free: the
        // loss list is COMPLETE for this module, not merely non-empty.
        let mut erased = trust_ir::format::canonicalize(&m);
        for loss in &losses {
            if let TextLoss::EnumLayout { enum_id } = loss {
                for e in erased.enums.iter_mut().filter(|e| e.id == *enum_id) {
                    e.layout = None;
                }
            }
        }
        assert!(text_losses(&erased).is_empty(), "{what}");
        assert_eq!(
            parse_module(&strip_lossy(&dump)).expect("marker-deleted text parses"),
            erased,
            "{what}: the grammar drops a field text_losses does not report"
        );
    }
}

/// Test-only: drop the `; #lossy:` marker line, which is a tripwire and not
/// integrity — exactly the edit a human could make.
fn strip_lossy(text: &str) -> String {
    text.lines()
        .filter(|line| !line.starts_with("; #lossy:"))
        .map(|line| format!("{line}\n"))
        .collect()
}

/// A `ProofAnnotation::Goal` (the Clean-kernel `Expr` a lowering stamps on a
/// node; `clean-expr`, on here through `trust-ir-build`'s default
/// `clean-tv-anchor`) printed as an opaque `goal(N hyps)` the parser has no
/// arm for: `canonical_checked` said `Ok` for a text that failed with
/// `unknown proof annotation: 'goal'`. Now a named `KernelGoal` loss.
#[test]
fn review_kernel_goal_is_refused_not_printed_unparseable() {
    use trust_ir::proof::ProofAnnotation;
    let goal = trust_ir::clean_expr_lowering::overflow_obligation(
        trust_ir::OverflowOp::AddOverflow,
        Ty::U8,
        trust_ir::ValueId::new(0),
        trust_ir::ValueId::new(1),
        (1, 2),
    )
    .expect("representable overflow goal");
    for on_node in [false, true] {
        let mut m = float_const_module(1.0);
        let annotation = ProofAnnotation::Goal(Box::new(goal.clone()));
        if on_node {
            m.functions[0].blocks[0].body[0].proofs.push(annotation);
        } else {
            m.functions[0].proofs.push(annotation);
        }
        let err = canonical_checked(&m).expect_err("a kernel goal is refused");
        assert_eq!(
            err.losses,
            vec![TextLoss::KernelGoal {
                func: FuncId::new(0)
            }]
        );
        let dump = canonical(&m);
        assert!(dump.contains("; #lossy: kernel-goal(fn 0)"), "{dump}");
        refused_as_lossy(&dump);
    }
    // Loss-free twin: the same module without the goal.
    assert_exact_text_round_trip(&float_const_module(1.0));
}

// ---------------------------------------------------------------------------
// WS4.5 (remainder): enum variant field names, the `Switch` exhaustiveness
// flag and `global_asm` are CARRIED — F-072's last enum residue and F-065
// ---------------------------------------------------------------------------

/// The shape of the archived part-A probe `p03_rust_struct_enum_match`
/// (`struct Pt { x, y }`, `enum Shape { Circle(u64), Rect(u64, u64), Empty }`,
/// `match`), built by hand with every layout fact a rustc-derived producer
/// records: named struct fields with offsets, a direct-tag enum descriptor,
/// per-variant field names, and a tag `switch` carrying the exhaustiveness
/// hint over a dead `[unreachable]` default.
fn struct_enum_match_module() -> Module {
    use trust_ir::inst::{Inst, SwitchCase};
    use trust_ir::ty::{
        EnumDef, EnumLayoutDescriptor, EnumTagEncoding, EnumTagRepr, EnumVariant, FieldDef,
        StructDef, StructRepr,
    };
    use trust_ir::value::{EnumId, StructId};
    use trust_ir::{Block, BlockId, Constant, InstrNode, ValueId};
    let mut m = Module::new("struct_enum_match");
    m.add_struct(StructDef {
        id: StructId::new(0),
        name: "Pt".into(),
        fields: vec![
            FieldDef {
                name: "x".into(),
                ty: Ty::U64,
                offset: Some(0),
            },
            FieldDef {
                name: "y".into(),
                ty: Ty::U64,
                offset: Some(8),
            },
        ],
        size: Some(16),
        align: Some(8),
        repr: StructRepr::Rust,
        origin: None,
    });
    let variant = |name: &str, fields: Vec<Ty>, names: &[&str]| EnumVariant {
        name: name.into(),
        fields,
        field_names: names.iter().map(|n| (*n).to_string()).collect(),
    };
    m.add_enum(EnumDef {
        id: EnumId::new(0),
        name: "Shape".into(),
        variants: vec![
            variant("Circle", vec![Ty::U64], &["0"]),
            variant("Rect", vec![Ty::U64, Ty::U64], &["0", "1"]),
            variant("Empty", vec![], &[]),
        ],
        discriminants: Vec::new(),
        repr: Some(EnumTagRepr::U64),
        layout: Some(EnumLayoutDescriptor {
            encoding: EnumTagEncoding::Direct { tag_offset: 0 },
            size: 24,
            align: 8,
            variant_field_offsets: vec![vec![8], vec![8, 16], vec![]],
        }),
        origin: None,
    });
    let ft = m
        .add_func_type(FuncTy {
            abi: None,
            params: vec![Ty::U64],
            returns: vec![Ty::U64],
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut f = Function::new(FuncId::new(0), "area_of_tag", ft, BlockId::new(0));
    f.producer = Some(Producer::TRust);
    let mut entry = Block::new(BlockId::new(0));
    entry.params.push((ValueId::new(0), Ty::U64));
    let case = |value: i128, target: u32| SwitchCase {
        value: Constant::Int(value),
        target: BlockId::new(target),
        args: vec![],
    };
    entry.body.push(InstrNode::new(Inst::Switch {
        value: ValueId::new(0),
        default: BlockId::new(4),
        default_args: vec![],
        cases: vec![case(0, 1), case(1, 2), case(2, 3)],
        exhaustive_enum_unreachable: true,
    }));
    f.blocks.push(entry);
    for (index, area) in [(1u32, 12i128), (2, 10), (3, 0)] {
        let mut arm = Block::new(BlockId::new(index));
        arm.body.push(
            InstrNode::new(Inst::Const {
                ty: Ty::U64,
                value: Constant::Int(area),
            })
            .with_result(ValueId::new(index)),
        );
        arm.body.push(InstrNode::new(Inst::Return {
            values: vec![ValueId::new(index)],
        }));
        f.blocks.push(arm);
    }
    let mut dead = Block::new(BlockId::new(4));
    dead.body.push(InstrNode::new(Inst::Unreachable));
    f.blocks.push(dead);
    m.try_add_function(f)
        .expect("Module::try_add_function: test fixture");
    m.global_asm
        .push(".globl _shape_tag\n_shape_tag:\n\t.quad 0".into());
    m
}

/// Ported row `a.rust.struct_enum_match.roundtrip` (part A, GAP -> PASS):
/// the archive measured "TEXT parses back but is LOSSY", losing
/// `/enums[0]/layout` and every struct field name and offset. All of it — and
/// the variant field names, the exhaustiveness hint and a `global_asm` block
/// besides — now survives text EXACTLY: `canonical_checked` is `Ok`, the parse
/// equals `canonicalize(m)` field for field with the same `stable_digest`,
/// both layouts are still computable at the same size, and `bin -> text ->
/// bin` (through the stored-form `text_checked`) is byte-identical.
#[test]
fn a_rust_struct_enum_match_roundtrip() {
    use trust_ir::value::{EnumId, StructId};
    let m = struct_enum_match_module();
    assert!(validate_module(&m).is_empty(), "{:?}", validate_module(&m));
    assert!(text_losses(&m).is_empty(), "{:?}", text_losses(&m));
    let text = canonical_checked(&m).expect("loss-free");
    for spelling in [
        "Circle(0: u64)",
        "Rect(0: u64, 1: u64)",
        "] exhaustive",
        "global_asm \".globl _shape_tag\\n_shape_tag:\\n\\t.quad 0\"",
    ] {
        assert!(text.contains(spelling), "{spelling}\n{text}");
    }
    let back = parse_module(&text).expect("parses");
    assert_eq!(back, trust_ir::format::canonicalize(&m));
    assert_eq!(back.stable_digest(), m.stable_digest());
    for module in [&m, &back] {
        assert_eq!(
            module
                .ty_layout_shape(&Ty::Enum(EnumId::new(0)))
                .map(|s| s.size_bits / 8)
                .ok(),
            Some(24)
        );
        assert_eq!(
            module
                .ty_layout_shape(&Ty::Struct(StructId::new(0)))
                .map(|s| s.size_bits / 8)
                .ok(),
            Some(16)
        );
    }
    let bytes = trust_ir::binary::serialize_module(&m).expect("serialize_module: test fixture");
    let decoded = trust_ir::binary::deserialize_module(&bytes).expect("binary");
    let stored = trust_ir::format::text_checked(&decoded).expect("loss-free as stored");
    let reparsed = parse_module(&stored).expect("stored text parses");
    assert_eq!(reparsed, decoded);
    assert_eq!(
        trust_ir::binary::serialize_module(&reparsed).expect("serialize_module: test fixture"),
        bytes
    );
}

/// Mutation controls for `a_rust_struct_enum_match_roundtrip`, one per
/// carried spelling: delete it from the text and the text still PARSES, but
/// to a different module (and digest) — so a printer arm or parser arm that
/// dropped the field would be caught by that test's exact-equality leg, not
/// waved through.
#[test]
fn a_rust_struct_enum_match_roundtrip_mutation_controls() {
    let m = struct_enum_match_module();
    let canon = trust_ir::format::canonicalize(&m);
    let text = canonical_checked(&m).expect("loss-free");
    for (what, from, to) in [
        (
            "variant field names",
            "Rect(0: u64, 1: u64)",
            "Rect(u64, u64)",
        ),
        ("struct offsets", "y: u64 @8", "y: u64"),
        ("exhaustive flag", "] exhaustive", "]"),
    ] {
        let mutant = text.replacen(from, to, 1);
        assert_ne!(mutant, text, "{what}: {from} not in\n{text}");
        let back = parse_module(&mutant).expect(what);
        assert_ne!(back, canon, "{what}");
        assert_ne!(back.stable_digest(), canon.stable_digest(), "{what}");
    }
    let no_asm: String = text
        .lines()
        .filter(|line| !line.starts_with("global_asm "))
        .map(|line| format!("{line}\n"))
        .collect();
    let back = parse_module(&no_asm).expect("asm-free text parses");
    assert!(back.global_asm.is_empty());
    assert_ne!(back.stable_digest(), canon.stable_digest());
}

/// Negative twins of the new spellings: a variant that mixes the named and
/// positional spellings, a near-miss of the `exhaustive` keyword, and a
/// `global_asm` block that is not a quoted string on its own line are each
/// REFUSED, never half-read; and a record field — records have no layout —
/// refuses the struct field's `@<offset>` suffix.
#[test]
fn ws45_new_spellings_refuse_their_malformed_twins() {
    let text = canonical_checked(&struct_enum_match_module()).expect("loss-free");
    for (from, to, needle) in [
        (
            "Rect(0: u64, 1: u64)",
            "Rect(0: u64, u64)",
            "mixes named (`field: ty`) and positional fields",
        ),
        ("] exhaustive", "] exhaustively", ""),
        (
            "global_asm \"",
            "global_asm .globl \"",
            "expected a quoted block",
        ),
    ] {
        let mutant = text.replacen(from, to, 1);
        assert_ne!(mutant, text, "{from}");
        let err = parse_module(&mutant).expect_err(from);
        assert!(err.message.contains(needle), "{from}: {err}");
    }
    let mut records = Module::new("record_offsets");
    records.add_record(trust_ir::RecordDef {
        id: trust_ir::RecordId::new(0),
        name: "R".into(),
        fields: vec![trust_ir::ty::FieldDef {
            name: "f".into(),
            ty: Ty::U64,
            offset: None,
        }],
    });
    let text = canonical_checked(&records).expect("loss-free");
    assert!(parse_module(&text).is_ok());
    let with_offset = text.replacen("f: u64", "f: u64 @0", 1);
    assert_ne!(with_offset, text);
    assert!(parse_module(&with_offset).is_err());
}

/// Ported row `small-designs/TREE-14-text-format-drops-enum-layout`
/// (GAP -> PASS): the paired two-language `Tree` enum's rustc byte layout
/// (its normative `EnumLayoutDescriptor`) must survive serialization; the
/// archive found text omitting it. With WS4.5 the descriptor AND the variant
/// field names round-trip, so the module is text-lossless and the layout is
/// the same after text as before — no fallback to the canonical tagged
/// union.
#[test]
fn small_designs_tree_14_text_format_drops_enum_layout() {
    use trust_ir::ty::{EnumDef, EnumLayoutDescriptor, EnumTagEncoding, EnumTagRepr, EnumVariant};
    use trust_ir::value::EnumId;
    let mut m = Module::new("tree_14");
    m.add_enum(EnumDef {
        id: EnumId::new(0),
        name: "Tree".into(),
        variants: vec![
            EnumVariant {
                name: "leaf".into(),
                fields: vec![Ty::U64],
                field_names: vec!["value".into()],
            },
            EnumVariant {
                name: "node".into(),
                fields: vec![Ty::Ptr, Ty::Ptr],
                field_names: vec!["left".into(), "right".into()],
            },
        ],
        discriminants: Vec::new(),
        repr: Some(EnumTagRepr::U8),
        layout: Some(EnumLayoutDescriptor {
            encoding: EnumTagEncoding::Direct { tag_offset: 16 },
            size: 24,
            align: 8,
            variant_field_offsets: vec![vec![0], vec![0, 8]],
        }),
        origin: None,
    });
    assert!(validate_module(&m).is_empty(), "{:?}", validate_module(&m));
    let text = canonical_checked(&m).expect("loss-free");
    assert!(
        text.contains("{ leaf(value: u64), node(left: ptr, right: ptr) }"),
        "{text}"
    );
    let back = parse_module(&text).expect("parses");
    assert_eq!(back, m);
    let size = |m: &Module| {
        m.ty_layout_shape(&Ty::Enum(EnumId::new(0)))
            .map(|s| s.size_bits / 8)
            .ok()
    };
    assert_eq!(size(&m), Some(24));
    assert_eq!(size(&back), Some(24));
}

/// The one machine both sides of the WS8.12 import row pin. The import
/// verifier's C6 never reads an absent target as agreement — not even two
/// absent ones — so an identity-transport fixture that wants its row to reach
/// `Ok` must pin a target on the importer AND the dependency. The text format
/// carries the pin (`target "<triple>" N endian abi=".."`).
fn pinned_target() -> TargetInfo {
    TargetInfo {
        triple: "aarch64-apple-darwin".into(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: Some("aapcs64".into()),
        struct_passing: Default::default(),
    }
}

/// `fn f(i64) -> i64` whose value ids INTERLEAVE the way a real producer's
/// do — bb0's parameter `%0`, bb0's result `%1`, only then bb1's parameter
/// `%2` — so it is legal, text-carryable and NOT in canonical form (canonical
/// numbering puts every block parameter first and would make bb1's `%1`).
/// It pins [`pinned_target`], as a dependency an import row authenticates
/// must.
fn interleaved_ids_module() -> Module {
    use trust_ir::Block;
    use trust_ir::inst::{BinOp, Inst};
    use trust_ir::node::InstrNode;
    use trust_ir::value::{BlockId, ValueId};

    let mut module = Module::new("interleaved");
    module.target_info = Some(pinned_target());
    let ft = module
        .add_func_type(FuncTy {
            abi: None,
            params: vec![Ty::I64],
            returns: vec![Ty::I64],
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut func = Function::new(FuncId::new(0), "f", ft, BlockId::new(0));
    func.producer = Some(Producer::TRust);
    let mut bb0 = Block::new(BlockId::new(0));
    bb0.params.push((ValueId::new(0), Ty::I64));
    bb0.body.push(
        InstrNode::new(Inst::BinOp {
            op: BinOp::Add,
            ty: Ty::I64,
            lhs: ValueId::new(0),
            rhs: ValueId::new(0),
        })
        .with_result(ValueId::new(1)),
    );
    bb0.body.push(InstrNode::new(Inst::Br {
        target: BlockId::new(1),
        args: vec![ValueId::new(1)],
    }));
    let mut bb1 = Block::new(BlockId::new(1));
    bb1.params.push((ValueId::new(2), Ty::I64));
    bb1.body.push(InstrNode::new(Inst::Return {
        values: vec![ValueId::new(2)],
    }));
    func.blocks.push(bb0);
    func.blocks.push(bb1);
    module
        .try_add_function(func)
        .expect("Module::try_add_function: test fixture");
    module
}

/// WS8.12 review (F-072, the `LIMITATIONS.md` text-spelling claim): only the
/// TRANSPORT text spelling is an identity-preserving path. On a legal,
/// loss-free module whose value ids are not canonical:
///
/// * `text_checked` (what `trust-ir convert --to text` writes) parses back
///   EQUAL, with the same `stable_digest`, and an import row recording the
///   original's digest authenticates the parsed module;
/// * `canonical_checked` (what `trust-ir-fmt` writes) parses back to
///   `canonicalize(m)`, a DIFFERENT module with a different `stable_digest`,
///   and the same import row refuses it as `DigestMismatch` — which is why the
///   limitation says never to record an import digest of canonical text.
///
/// Both modules pin the same target ([`pinned_target`]): the verifier's C6
/// refuses an absent pin on either side, so without it the transport row
/// would stop at `TargetMismatch` and never show that C1-C5 accept the
/// transported module.
///
/// Controls:
///
/// * on a module already in canonical form, the canonical spelling keeps the
///   digest too, so the refusal above is caused by the renumbering, not by
///   the printer;
/// * NEGATIVE: the transport text with ONE value id renumbered (`%2` -> `%3`,
///   bb1's parameter and its one use — the module stays the same function)
///   parses, and the same row refuses it as `DigestMismatch`, so the
///   transport's acceptance rests on it keeping the producer's numbering
///   exactly, not on a verifier that accepts any parse of the name;
/// * the target pin is load-bearing: the transported module with its pin
///   stripped is refused at C6 (`TargetMismatch`), so the `Ok` above passed
///   every check, C6 included.
#[test]
fn ws8_12_canonical_text_is_not_an_identity_transport() {
    use trust_ir::ImportVerificationError;
    use trust_ir::format::{canonicalize, text_checked};
    use trust_ir::value::ImportId;

    let m = interleaved_ids_module();
    assert_eq!(validate_module(&m), Vec::new());
    assert!(text_losses(&m).is_empty());
    assert_ne!(canonicalize(&m), m, "the fixture must be non-canonical");

    let mut importer = Module::new("root");
    importer.target_info = Some(pinned_target());
    importer
        .intern_import(
            ModuleImport::new("interleaved", m.stable_digest()).with_producer(Producer::TRust),
        )
        .expect("Module::intern_import: test fixture");
    let row = ImportId::new(0);

    // The transport spelling: exact, same identity, authenticates.
    let transport_text = text_checked(&m).expect("loss-free");
    let transported = parse_module(&transport_text).expect("parses");
    assert_eq!(transported, m);
    assert_eq!(transported.stable_digest(), m.stable_digest());
    importer
        .verify_import(row, &transported)
        .expect("transport text keeps the import identity");

    // Negative control: a transport that renumbered even ONE value would
    // lose the identity. bb1's parameter `%2` (and its one use) becomes `%3`.
    assert_eq!(
        transport_text.matches("%2").count(),
        2,
        "the fixture spells bb1's parameter `%2` exactly twice:\n{transport_text}"
    );
    assert!(!transport_text.contains("%3"), "{transport_text}");
    let renumbered = parse_module(&transport_text.replace("%2", "%3")).expect("parses");
    assert_ne!(renumbered, m);
    assert!(
        matches!(
            importer.verify_import(row, &renumbered),
            Err(ImportVerificationError::DigestMismatch { import: 0, .. })
        ),
        "one renumbered value id must break the import identity"
    );

    // The pin is load-bearing: the same bytes minus the target stop at C6.
    let mut unpinned = transported.clone();
    unpinned.target_info = None;
    let mut unpinned_importer = Module::new("root");
    unpinned_importer.target_info = Some(pinned_target());
    unpinned_importer
        .intern_import(
            ModuleImport::new("interleaved", unpinned.stable_digest())
                .with_producer(Producer::TRust),
        )
        .expect("Module::intern_import: test fixture");
    assert!(
        matches!(
            unpinned_importer.verify_import(row, &unpinned),
            Err(ImportVerificationError::TargetMismatch { import: 0, .. })
        ),
        "an absent dependency pin is never read as agreement"
    );

    // The canonical spelling: a renumbered module, a moved identity, refused.
    let canonical_back = parse_module(&canonical_checked(&m).expect("loss-free")).expect("parses");
    assert_eq!(canonical_back, canonicalize(&m));
    assert_ne!(canonical_back, m);
    assert_ne!(canonical_back.stable_digest(), m.stable_digest());
    assert!(
        matches!(
            importer.verify_import(row, &canonical_back),
            Err(ImportVerificationError::DigestMismatch { import: 0, .. })
        ),
        "an import digest of the original must not authenticate its canonical text"
    );

    // Mutation control: an already-canonical module keeps its identity
    // through the canonical spelling.
    let c = canonicalize(&m);
    assert_eq!(canonicalize(&c), c);
    let c_back = parse_module(&canonical_checked(&c).expect("loss-free")).expect("parses");
    assert_eq!(c_back, c);
    assert_eq!(c_back.stable_digest(), c.stable_digest());
}
