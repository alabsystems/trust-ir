//! b6 — DATA CARRIERS of the two-language (Rust + Lean/Clean) module.
//!
//! Every module here is what the producers SHOULD emit at the design's end
//! state: values of one type crossing between a `Producer::TRust` and a
//! `Producer::Clean` function. PASS rows = validate + 4-format round trip +
//! reference-interpreter execution, each with a close negative twin matched on
//! the SPECIFIC refusal. GAP rows are ratchets: the assertion is that the
//! limitation is present; each cites the trust-ir source line that causes it.
//!
//! Ported (roadmap WS8.6) from the archived Part B battery
//! `reports/2026-09-17-two-language-proof-program/partb/tests/b6_data_carriers.rs`, measured there
//! at trust-ir 4efb21bc and re-measured at the port. Every row is checked against
//! `RATCHETS.tsv` (see `harness.rs`). `file:line` citations are relative to
//! `crates/` and date from 4efb21bc: re-locate them by name.

mod common;

use common::{
    Expect, Outcome, RoundTrip, feature_check, feature_ratified, roundtrip_all, run_nullary,
    run_with_args,
};
use trust_ir::constant::Constant;
use trust_ir::inst::{AllocOrigin, AtomicRMWOp, CastOp, Inst, Ordering, SwitchCase, UnOp};
use trust_ir::interpret::{InterpretValue, InterpretValueKind};
use trust_ir::node::InstrNode;
use trust_ir::shape::TyLayoutKind;
use trust_ir::ty::{
    ClosureTy, EnumDef, EnumLayoutDescriptor, EnumTagEncoding, EnumTagRepr, EnumVariant,
    FatPtrKind, FieldDef, StructDef, Ty,
};
use trust_ir::value::{ClosureTyId, EnumId, GlobalId, StructId};
use trust_ir::{
    BodyGate, ClosureLayoutDescriptor, Endianness, Global, LayoutError, Linkage, Module, Producer,
    TargetInfo, TlsModel, TupleLayoutDescriptor,
};
use trust_ir_build::validate::STRUCT_FIELDS_OVERLAP_REASON;
use trust_ir_build::{
    ModuleBuilder, PointerConstantRefusal, ValidationError, validate_module,
    validate_module_for_codegen,
};

// ===========================================================================
// Local harness
// ===========================================================================

/// `<id>.validate` + `<id>.roundtrip` for a module that must be well-formed.
/// `text_lossless` is the MEASURED expectation for canonical text (binary /
/// JSON / MessagePack must always be lossless); a `false` here is backed by a
/// dedicated `b6.text.*` GAP row naming the lost field. Since WS4.2 a lossy
/// text is printed `#lossy` and REFUSED by the parser (never silently
/// dropped); its re-encode is then measured on the marker-deleted copy.
fn demo(id: &str, m: &Module, wire: u32, text_lossless: bool) -> RoundTrip {
    demo_with(id, m, wire, text_lossless, true)
}

/// The END-STATE form of a module: every function carries its producer's codegen
/// license (`BodyGate::Gated`). `validate_module_for_codegen` refuses a `None`
/// gate (`UnlicensedBodyForCodegen`, validate.rs:8357), so the strictest entry
/// point is only meaningful on the licensed clone. The UNLICENSED module is kept
/// for the wire-version measurement (a gate alone selects v41 and would mask the
/// v38/v40 selections).
fn license(m: &Module) -> Module {
    let mut m = m.clone();
    for f in &mut m.functions {
        if f.body_gate.is_none() && !f.blocks.is_empty() {
            // Not `clean-kernel-tv`: since WS1.5 that authority is bound to a
            // kernel-rechecked TV certificate per body, which these carrier
            // fixtures do not mint; the direct-lane authority is the
            // evidence-free Clean license.
            let authority = if f.producer == Some(Producer::Clean) {
                "trust-direct-lane-structural"
            } else {
                "trust-verify"
            };
            f.body_gate = Some(BodyGate::Gated {
                authority: authority.into(),
                evidence: None,
            });
        }
    }
    m
}

/// `lowerable = false` only for the closure module, whose exact codegen refusal
/// is asserted by its own GAP row.
fn demo_with(id: &str, m: &Module, wire: u32, text_lossless: bool, lowerable: bool) -> RoundTrip {
    let errors = validate_module(m);
    assert!(feature_check(
        &format!("{id}.validate"),
        errors.is_empty(),
        &format!("validate_module errors={errors:?}"),
    ));
    if lowerable {
        // STRICTEST entry point, on the licensed (end-state) clone; the licensed
        // clone must itself survive the three production transports at >= v41.
        let licensed = license(m);
        let codegen = validate_module_for_codegen(&licensed);
        let lrt = roundtrip_all(&licensed);
        assert!(feature_check(
            &format!("{id}.codegen_admitted"),
            codegen.is_empty() && lrt.lossless_production() && lrt.binary_version == wire.max(41),
            &format!(
                "validate_module_for_codegen(all functions Gated)={codegen:?}; licensed clone wire=v{} production-lossless={}",
                lrt.binary_version,
                lrt.lossless_production()
            ),
        ));
    }
    let rt = roundtrip_all(m);
    assert!(feature_check(
        &format!("{id}.roundtrip"),
        rt.lossless_production()
            && rt.binary_version == wire
            && rt.text.reencode_identical
            && rt.text.structurally_equal == text_lossless
            && if text_lossless {
                rt.text.decode_error.is_none()
            } else {
                rt.text.refused_as_lossy()
            },
        &format!(
            "expected wire v{wire}, text structurally_equal={text_lossless} (lossy => refused as #lossy): {}",
            rt.summary()
        ),
    ));
    rt
}

fn run_u(m: &Module, entry: &str) -> (Option<u128>, String) {
    let out = run_nullary(m, entry);
    let got = out
        .as_ref()
        .ok()
        .and_then(|v| v.first())
        .and_then(common::as_u128);
    (got, format!("{entry}() = {out:?}"))
}

fn interp(id: &str, m: &Module, entry: &str, expect: u128) {
    let (got, detail) = run_u(m, entry);
    assert!(feature_check(
        id,
        got == Some(expect),
        &format!("expected {expect}; {detail}")
    ));
}

/// Negative twin: `pred` must match one of the validator's errors.
fn twin(id: &str, m: &Module, what: &str, pred: impl Fn(&ValidationError) -> bool) {
    let errors = validate_module(m);
    assert!(feature_check(
        &format!("{id}.negative_twin"),
        errors.iter().any(pred),
        &format!("{what} => {errors:?}"),
    ));
}

// ===========================================================================
// Module builders
// ===========================================================================

fn tree_def(layout: Option<EnumLayoutDescriptor>) -> EnumDef {
    let mut def = EnumDef::new(
        EnumId::new(0),
        "Tree",
        vec![
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
    );
    def.layout = layout;
    def
}

fn tree_direct_layout() -> EnumLayoutDescriptor {
    EnumLayoutDescriptor {
        // NOT trust-ir's canonical tagged-union image (tag u8 @0, payload @8):
        // payload first, tag LAST -- the rustc-style reordering a producer reads
        // off `Variants::Multiple`. A raw U64 load at offset 0 of a `leaf` cell
        // therefore observes the payload, which distinguishes the two layouts.
        encoding: EnumTagEncoding::Direct { tag_offset: 16 },
        size: 24,
        align: 8,
        variant_field_offsets: vec![vec![0], vec![0, 8]],
    }
}

fn build_tree(layout: Option<EnumLayoutDescriptor>) -> Module {
    let tree = Ty::Enum(EnumId::new(0));
    let mut mb = ModuleBuilder::new("b6_tree");
    let sum_ty = mb.add_func_type(vec![Ty::Ptr], vec![Ty::U64]);
    let mk_ty = mb.add_func_type(vec![Ty::U64], vec![tree.clone()]);
    let nullary = mb.add_func_type(vec![], vec![Ty::U64]);

    let sum_id = mb
        .peek_next_func_id()
        .expect("peek_next_func_id: test fixture");
    {
        let mut fb = mb.function("clean_tree_sum", sum_ty);
        fb.set_producer(Producer::Clean);
        fb.set_display_path("Tree.sum");
        // The evidence-free Clean license (WS1.5: `clean-kernel-tv` needs an
        // in-module TV certificate, which this carrier fixture does not mint).
        fb.set_body_gate(BodyGate::Gated {
            authority: "trust-direct-lane-structural".into(),
            evidence: None,
        });
        let entry = fb.create_block();
        let leaf = fb.create_block();
        let node = fb.create_block();
        let dead = fb.create_block();
        let t = fb.add_block_param(entry, Ty::Ptr);
        fb.switch_to_block(entry);
        let v = fb.load(tree.clone(), t);
        let tag = fb.extract_field(Ty::U8, v, 0);
        fb.switch(
            tag,
            vec![
                SwitchCase {
                    value: Constant::Int(0),
                    target: leaf,
                    args: vec![],
                },
                SwitchCase {
                    value: Constant::Int(1),
                    target: node,
                    args: vec![],
                },
            ],
            dead,
            vec![],
        );
        fb.switch_to_block(leaf);
        let value = fb.extract_field(Ty::U64, v, 1);
        fb.ret(vec![value]);
        fb.switch_to_block(node);
        let l = fb.extract_field(Ty::Ptr, v, 1);
        let r = fb.extract_field(Ty::Ptr, v, 2);
        let a = fb.call(sum_id, vec![l]);
        let b = fb.call(sum_id, vec![r]);
        let s = fb.add(Ty::U64, a, b);
        fb.ret(vec![s]);
        fb.switch_to_block(dead);
        fb.unreachable();
        fb.build();
    }
    let mk_id = {
        let mut fb = mb.function("clean_mk_leaf", mk_ty);
        fb.set_producer(Producer::Clean);
        // The evidence-free Clean license (WS1.5: `clean-kernel-tv` needs an
        // in-module TV certificate, which this carrier fixture does not mint).
        fb.set_body_gate(BodyGate::Gated {
            authority: "trust-direct-lane-structural".into(),
            evidence: None,
        });
        let entry = fb.create_block();
        let x = fb.add_block_param(entry, Ty::U64);
        fb.switch_to_block(entry);
        let seed = fb.const_value(
            tree.clone(),
            Constant::Aggregate(vec![Constant::Int(0), Constant::Int(0)]),
        );
        let out = fb.insert_field(tree.clone(), seed, 1, x);
        fb.ret(vec![out]);
        fb.build()
    };
    {
        // Rust side reads the RAW byte image of a Clean-built leaf: offset 0 is
        // the payload under the declared descriptor.
        let mut fb = mb.function("rust_leaf_image", nullary);
        fb.set_producer(Producer::TRust);
        fb.set_body_gate(BodyGate::Gated {
            authority: "trust-verify".into(),
            evidence: None,
        });
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        let p = fb.alloca(tree.clone());
        let c40 = fb.uconst(Ty::U64, 40);
        let leaf = fb.call(mk_id, vec![c40]);
        fb.store(tree.clone(), p, leaf);
        let raw = fb.load(Ty::U64, p);
        fb.ret(vec![raw]);
        fb.build();
    }
    {
        let mut fb = mb.function("program", nullary);
        fb.set_producer(Producer::TRust);
        fb.set_body_gate(BodyGate::Gated {
            authority: "trust-verify".into(),
            evidence: None,
        });
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        let p1 = fb.alloca(tree.clone());
        let p2 = fb.alloca(tree.clone());
        let root = fb.alloca(tree.clone());
        let c40 = fb.uconst(Ty::U64, 40);
        let c2 = fb.uconst(Ty::U64, 2);
        let l1 = fb.call(mk_id, vec![c40]);
        let l2 = fb.call(mk_id, vec![c2]);
        fb.store(tree.clone(), p1, l1);
        fb.store(tree.clone(), p2, l2);
        let seed = fb.const_value(
            tree.clone(),
            Constant::Aggregate(vec![Constant::Int(1), Constant::Int(0), Constant::Int(0)]),
        );
        let n1 = fb.insert_field(tree.clone(), seed, 1, p1);
        let n2 = fb.insert_field(tree.clone(), n1, 2, p2);
        fb.store(tree.clone(), root, n2);
        let out = fb.call(sum_id, vec![root]);
        fb.ret(vec![out]);
        fb.build();
    }
    let mut m = mb.build().expect("ModuleBuilder::build: test fixture");
    m.add_enum(tree_def(layout));
    for b in &mut m.functions[0].blocks {
        for n in &mut b.body {
            if let Inst::Switch {
                exhaustive_enum_unreachable,
                ..
            } = &mut n.inst
            {
                *exhaustive_enum_unreachable = true;
            }
        }
    }
    m
}

fn target() -> TargetInfo {
    TargetInfo {
        triple: "x86_64-unknown-linux-gnu".into(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: None,
        struct_passing: trust_ir::StructPassingPolicy::Unclassified,
    }
}

fn global(
    name: &str,
    ty: Ty,
    mutable: bool,
    init: Option<Constant>,
    tls: Option<TlsModel>,
) -> Global {
    Global {
        name: name.into(),
        ty,
        mutable,
        initializer: init,
        linkage: Linkage::Internal,
        tls,
        align: None,
        section: None,
        visibility: Default::default(),
        retained: false,
    }
}

fn replace_inst(
    m: &mut Module,
    func: &str,
    pred: impl Fn(&Inst) -> bool,
    new: impl Fn(&Inst) -> Inst,
) -> usize {
    let mut n = 0;
    let f = m
        .functions
        .iter_mut()
        .find(|f| f.name == func)
        .expect("function");
    for b in &mut f.blocks {
        for node in &mut b.body {
            if pred(&node.inst) {
                node.inst = new(&node.inst);
                n += 1;
            }
        }
    }
    n
}

// ---------------- enum layouts: niche + untagged ----------------
fn build_enum_layouts() -> Module {
    let opt = Ty::Enum(EnumId::new(0));
    let wrap = Ty::Enum(EnumId::new(1));
    let mut mb = ModuleBuilder::new("b6_enum_layouts");
    let n32 = mb.add_func_type(vec![], vec![Ty::U32]);
    let n64 = mb.add_func_type(vec![], vec![Ty::U64]);
    {
        let mut fb = mb.function("niche_none_image", n32);
        fb.set_producer(Producer::TRust);
        let e = fb.create_block();
        fb.switch_to_block(e);
        let p = fb.alloca(opt.clone());
        let c = fb.const_value(opt.clone(), Constant::Aggregate(vec![Constant::Int(0)]));
        fb.store(opt.clone(), p, c);
        let raw = fb.load(Ty::U32, p);
        fb.ret(vec![raw]);
        fb.build();
    }
    {
        let mut fb = mb.function("niche_some_roundtrip", n32);
        fb.set_producer(Producer::Clean);
        let e = fb.create_block();
        fb.switch_to_block(e);
        let p = fb.alloca(opt.clone());
        let c = fb.const_value(
            opt.clone(),
            Constant::Aggregate(vec![Constant::Int(1), Constant::Int(7)]),
        );
        fb.store(opt.clone(), p, c);
        let v = fb.load(opt.clone(), p);
        let tag = fb.extract_field(Ty::U8, v, 0);
        let payload = fb.extract_field(Ty::U32, v, 1);
        let tag32 = fb.zext(Ty::U8, Ty::U32, tag);
        let hundred = fb.uconst(Ty::U32, 100);
        let t = fb.mul(Ty::U32, tag32, hundred);
        let out = fb.add(Ty::U32, t, payload);
        fb.ret(vec![out]);
        fb.build();
    }
    {
        let mut fb = mb.function("untagged_image", n64);
        fb.set_producer(Producer::TRust);
        let e = fb.create_block();
        fb.switch_to_block(e);
        let p = fb.alloca(wrap.clone());
        let c = fb.const_value(
            wrap.clone(),
            Constant::Aggregate(vec![Constant::Int(0), Constant::Int(99)]),
        );
        fb.store(wrap.clone(), p, c);
        let raw = fb.load(Ty::U64, p);
        let v = fb.load(wrap.clone(), p);
        let payload = fb.extract_field(Ty::U64, v, 1);
        let out = fb.add(Ty::U64, raw, payload);
        fb.ret(vec![out]);
        fb.build();
    }
    let mut m = mb.build().expect("ModuleBuilder::build: test fixture");
    let mut o = EnumDef::new(
        EnumId::new(0),
        "OptIdx",
        vec![
            EnumVariant {
                name: "none".into(),
                fields: vec![],
                field_names: vec![],
            },
            EnumVariant {
                name: "some".into(),
                fields: vec![Ty::U32],
                field_names: vec!["idx".into()],
            },
        ],
    );
    o.layout = Some(EnumLayoutDescriptor {
        encoding: EnumTagEncoding::Niche {
            untagged_variant: 1,
            niche_variants_start: 0,
            niche_variants_end: 0,
            niche_start: 0xFFFF_FF01,
            niche_offset: 0,
            niche_ty: EnumTagRepr::U32,
        },
        size: 4,
        align: 4,
        variant_field_offsets: vec![vec![], vec![0]],
    });
    m.add_enum(o);
    let mut w = EnumDef::new(
        EnumId::new(1),
        "Wrapper",
        vec![EnumVariant {
            name: "only".into(),
            fields: vec![Ty::U64],
            field_names: vec!["v".into()],
        }],
    );
    w.layout = Some(EnumLayoutDescriptor {
        encoding: EnumTagEncoding::Untagged,
        size: 8,
        align: 8,
        variant_field_offsets: vec![vec![0]],
    });
    m.add_enum(w);
    m
}

// ---------------- struct + tuple declared layouts ----------------
fn build_layouts(b_offset: u64, a_offset: u64, tuple_offsets: Vec<u64>) -> Module {
    let mut mb = ModuleBuilder::new_with_target_info("b6_layouts", target());
    let pair = Ty::Struct(StructId::new(0));
    mb.add_struct(StructDef {
        id: StructId::new(0),
        name: "Pair".into(),
        fields: vec![
            FieldDef {
                name: "a".into(),
                ty: Ty::U8,
                offset: Some(a_offset),
            },
            FieldDef {
                name: "b".into(),
                ty: Ty::U64,
                offset: Some(b_offset),
            },
        ],
        size: Some(16),
        align: Some(8),
        repr: Default::default(),
        origin: None,
    });
    let tuple = Ty::Tuple(vec![Ty::U8, Ty::U64, Ty::U8]);
    let tuple_type = mb.add_type(tuple.clone());
    let n64 = mb.add_func_type(vec![], vec![Ty::U64]);
    {
        let mut fb = mb.function("struct_image", n64);
        fb.set_producer(Producer::TRust);
        let e = fb.create_block();
        fb.switch_to_block(e);
        let p = fb.alloca(pair.clone());
        let c = fb.const_value(
            pair.clone(),
            Constant::Aggregate(vec![
                Constant::Int(17),
                Constant::Int(0x1122_3344_5566_7788),
            ]),
        );
        fb.store(pair.clone(), p, c);
        let raw = fb.load(Ty::U64, p);
        fb.ret(vec![raw]);
        fb.build();
    }
    {
        let mut fb = mb.function("tuple_image", n64);
        fb.set_producer(Producer::Clean);
        let e = fb.create_block();
        fb.switch_to_block(e);
        let p = fb.alloca(tuple.clone());
        let c = fb.const_value(
            tuple.clone(),
            Constant::Aggregate(vec![
                Constant::Int(17),
                Constant::Int(0x0102_0304_0506_0708),
                Constant::Int(34),
            ]),
        );
        fb.store(tuple.clone(), p, c);
        let raw = fb.load(Ty::U64, p);
        fb.ret(vec![raw]);
        fb.build();
    }
    let mut m = mb.build().expect("ModuleBuilder::build: test fixture");
    m.tuple_layouts.push(TupleLayoutDescriptor {
        tuple_type,
        size: 16,
        align: 8,
        field_offsets: tuple_offsets,
    });
    m
}

// ---------------- closure ----------------
fn build_closure(bad_target: bool) -> Module {
    let mut mb = ModuleBuilder::new("b6_closure");
    let physical = mb.add_func_type(vec![Ty::U64, Ty::U64], vec![Ty::U64]);
    let apparent = mb.add_func_type(vec![Ty::U64], vec![Ty::U64]);
    let clos = Ty::Closure(ClosureTyId::new(0));
    let apply_ty = mb.add_func_type(vec![clos.clone(), Ty::U64], vec![Ty::U64]);
    let nullary = mb.add_func_type(vec![], vec![Ty::U64]);
    let add_k = {
        let mut fb = mb.function("rust_add_k", physical);
        fb.set_producer(Producer::TRust);
        let e = fb.create_block();
        let k = fb.add_block_param(e, Ty::U64);
        let x = fb.add_block_param(e, Ty::U64);
        fb.switch_to_block(e);
        let s = fb.add(Ty::U64, k, x);
        fb.ret(vec![s]);
        fb.build()
    };
    let ident = {
        let mut fb = mb.function("rust_ident", apparent);
        fb.set_producer(Producer::TRust);
        let e = fb.create_block();
        let x = fb.add_block_param(e, Ty::U64);
        fb.switch_to_block(e);
        fb.ret(vec![x]);
        fb.build()
    };
    let apply = {
        let mut fb = mb.function("clean_apply", apply_ty);
        fb.set_producer(Producer::Clean);
        let e = fb.create_block();
        let f = fb.add_block_param(e, clos.clone());
        let x = fb.add_block_param(e, Ty::U64);
        fb.switch_to_block(e);
        let r = fb.call_indirect(f, apparent, vec![x]);
        fb.ret(vec![r]);
        fb.build()
    };
    {
        let mut fb = mb.function("program", nullary);
        fb.set_producer(Producer::TRust);
        let e = fb.create_block();
        fb.switch_to_block(e);
        // closure literal `move |x| k + x` with k = 5 frozen at literal time
        let lit = fb.const_value(
            clos.clone(),
            Constant::Closure {
                func: if bad_target { ident } else { add_k },
                captures: vec![Constant::Int(5)],
            },
        );
        let five = fb.uconst(Ty::U64, 5);
        // register-level construct lane: overwrite capture 0 with a RUNTIME value
        let c = fb.insert_field(clos.clone(), lit, 0, five);
        let cap = fb.extract_field(Ty::U64, c, 0);
        let x = fb.uconst(Ty::U64, 16);
        let a = fb.call_indirect(lit, apparent, vec![x]); // 21 (Rust applies it)
        let b = fb.call(apply, vec![c, x]); // 21 (Clean applies it)
        let s = fb.add(Ty::U64, a, b);
        let s2 = fb.sub(Ty::U64, s, cap); // 37
        let s3 = fb.add(Ty::U64, s2, cap); // 42
        fb.ret(vec![s3]);
        fb.build();
    }
    let mut m = mb.build().expect("ModuleBuilder::build: test fixture");
    m.add_closure_type(ClosureTy {
        func: apparent,
        captures: vec![Ty::U64],
    })
    .expect("Module::add_closure_type: test fixture");
    m
}

// ---------------- fat pointers ----------------
fn build_fatptr(bad_meta: bool) -> Module {
    let mut mb = ModuleBuilder::new("b6_fatptr");
    let u64_id = mb.add_type(Ty::U64);
    let u8_id = mb.add_type(Ty::U8);
    let slice = Ty::FatPtr(FatPtrKind::Slice(u64_id));
    let strp = Ty::FatPtr(FatPtrKind::Str);
    let clen = Ty::FatPtr(FatPtrKind::ContainerLen);
    let cvt = Ty::FatPtr(FatPtrKind::ContainerVtable);
    mb.add_global(global(
        "HELLO",
        Ty::Array(u8_id, 6),
        false,
        Some(Constant::str_bytes("héllo")),
        None,
    ));
    mb.add_global(global(
        "VTABLE",
        Ty::Array(u64_id, 1),
        false,
        Some(Constant::Array(vec![Constant::Int(7)])),
        None,
    ));
    let lens_ty = mb.add_func_type(
        vec![slice.clone(), strp.clone(), clen.clone(), cvt.clone()],
        vec![Ty::U64],
    );
    let nullary = mb.add_func_type(vec![], vec![Ty::U64]);
    let lens = {
        let mut fb = mb.function("clean_lens", lens_ty);
        fb.set_producer(Producer::Clean);
        let e = fb.create_block();
        let s = fb.add_block_param(e, slice.clone());
        let t = fb.add_block_param(e, strp.clone());
        let c = fb.add_block_param(e, clen.clone());
        let v = fb.add_block_param(e, cvt.clone());
        fb.switch_to_block(e);
        let sl = fb.ptr_metadata(slice.clone(), Ty::U64, s);
        let tl = fb.ptr_metadata(strp.clone(), Ty::U64, t);
        let cl = fb.ptr_metadata(clen.clone(), Ty::U64, c);
        let vt = fb.ptr_metadata(cvt.clone(), if bad_meta { Ty::U64 } else { Ty::Ptr }, v);
        // the ContainerVtable metadata word is a POINTER: read slot 0 through it
        let slot0 = fb.load(Ty::U64, vt);
        let data = fb.ptr_data(slice.clone(), s);
        let one = fb.iconst(Ty::I64, 1);
        let p1 = fb.gep(Ty::U64, data, vec![one]);
        let elem = fb.load(Ty::U64, p1);
        let a = fb.add(Ty::U64, sl, tl);
        let b = fb.add(Ty::U64, a, cl);
        let c2 = fb.add(Ty::U64, b, elem);
        let out = fb.add(Ty::U64, c2, slot0);
        fb.ret(vec![out]);
        fb.build()
    };
    {
        let mut fb = mb.function("program", nullary);
        fb.set_producer(Producer::TRust);
        let e = fb.create_block();
        fb.switch_to_block(e);
        let arr_ty = Ty::Array(u64_id, 3);
        let arr = fb.alloca(arr_ty.clone());
        let c = fb.const_value(
            arr_ty.clone(),
            Constant::Array(vec![
                Constant::Int(10),
                Constant::Int(23),
                Constant::Int(50),
            ]),
        );
        fb.store(arr_ty, arr, c);
        let three = fb.uconst(Ty::U64, 3);
        let six = fb.uconst(Ty::U64, 6);
        let s = fb.ptr_from_parts(slice.clone(), Ty::U64, arr, three);
        let hello = fb.global_addr(GlobalId::new(0));
        let t = fb.ptr_from_parts(strp.clone(), Ty::U64, hello, six);
        let c = fb.ptr_from_parts(clen.clone(), Ty::U64, hello, three);
        let vt = fb.global_addr(GlobalId::new(1));
        let v = fb.ptr_from_parts(cvt.clone(), Ty::Ptr, arr, vt);
        let out = fb.call(lens, vec![s, t, c, v]); // 3+6+3 + elem[1]=23 + vtable slot0=7 = 42
        fb.ret(vec![out]);
        fb.build();
    }
    mb.build().expect("ModuleBuilder::build: test fixture")
}

/// `len: None` = the null pair `[Int(0), Int(0)]`; `Some(n)` = the non-null
/// `&str` window `[SymbolAddr(HELLO), Int(n)]` over the 6-byte `HELLO`.
fn build_fatptr_const(len: Option<i128>) -> Module {
    let mut mb = ModuleBuilder::new("b6_fatptr_const");
    let u8_id = mb.add_type(Ty::U8);
    let strp = Ty::FatPtr(FatPtrKind::Str);
    mb.add_global(global(
        "HELLO",
        Ty::Array(u8_id, 6),
        false,
        Some(Constant::str_bytes("héllo")),
        None,
    ));
    let init = match len {
        Some(n) => Constant::Aggregate(vec![
            Constant::SymbolAddr {
                symbol: "HELLO".into(),
                addend: 0,
            },
            Constant::Int(n),
        ]),
        None => Constant::Aggregate(vec![Constant::Int(0), Constant::Int(0)]),
    };
    mb.add_global(global(
        "GREETING",
        strp.clone(),
        false,
        Some(init.clone()),
        None,
    ));
    let ft = mb.add_func_type(vec![], vec![strp.clone()]);
    let mut fb = mb.function("greeting", ft);
    fb.set_producer(Producer::TRust);
    let e = fb.create_block();
    fb.switch_to_block(e);
    let c = fb.const_value(strp, init);
    fb.ret(vec![c]);
    fb.build();
    mb.build().expect("ModuleBuilder::build: test fixture")
}

// ---------------- Ref/RefMut + borrow, Rc + retain/release ----------------
/// mode 0 good; 1 = `&mut` passed where the Clean callee takes `&`; 2 = a bare
/// `Ptr` passed where the Clean callee takes `Rc<u64>`; 3 = `Retain` of an
/// integer; 4 = `Borrow` of an integer, in the Clean callee (a function stamped
/// `Producer::TRust` carries no permission instruction at all: SPEC "A Rust
/// reference carries no permission instruction", so the operand rule is
/// exercised where the permission machine is the producer's own model).
fn build_borrow_rc(mode: u8) -> Module {
    let mut mb = ModuleBuilder::new("b6_borrow_rc");
    let refm = Ty::RefMut(Box::new(Ty::U64));
    let refs = Ty::Ref(Box::new(Ty::U64));
    let rc = Ty::Rc(Box::new(Ty::U64));
    let bump_ty = mb.add_func_type(vec![refm.clone()], vec![]);
    let read_ty = mb.add_func_type(vec![refs.clone()], vec![Ty::U64]);
    let rc_ty = mb.add_func_type(vec![rc.clone()], vec![Ty::U64]);
    let nullary = mb.add_func_type(vec![], vec![Ty::U64]);
    let bump = {
        // Spelled as a Rust producer spells it: the `&mut` parameter is used
        // directly, never re-borrowed through the permission machine.
        let mut fb = mb.function("rust_bump", bump_ty);
        fb.set_producer(Producer::TRust);
        let e = fb.create_block();
        let r = fb.add_block_param(e, refm.clone());
        fb.switch_to_block(e);
        let v = fb.load(Ty::U64, r);
        let one = fb.uconst(Ty::U64, 1);
        let s = fb.add(Ty::U64, v, one);
        fb.store(Ty::U64, r, s);
        fb.ret(vec![]);
        fb.build()
    };
    let read = {
        let mut fb = mb.function("clean_read", read_ty);
        fb.set_producer(Producer::Clean);
        let e = fb.create_block();
        let r = fb.add_block_param(e, refs.clone());
        fb.switch_to_block(e);
        if mode == 4 {
            let ten = fb.uconst(Ty::U64, 10);
            let _ = fb.borrow(ten);
        }
        let b = fb.borrow(r);
        let v = fb.load(Ty::U64, b);
        fb.end_borrow(b);
        fb.ret(vec![v]);
        fb.build()
    };
    let rc_get = {
        let mut fb = mb.function("clean_rc_get", rc_ty);
        fb.set_producer(Producer::Clean);
        let e = fb.create_block();
        let r = fb.add_block_param(e, rc.clone());
        fb.switch_to_block(e);
        fb.retain(r);
        let shared = fb.is_unique(r); // false: 2 owners
        let v = fb.load(Ty::U64, r);
        fb.release(r);
        let unique = fb.is_unique(r); // true
        let s = fb.zext(Ty::Bool, Ty::U64, shared);
        let u = fb.zext(Ty::Bool, Ty::U64, unique);
        let ten = fb.uconst(Ty::U64, 10);
        let s10 = fb.mul(Ty::U64, s, ten);
        let a = fb.add(Ty::U64, v, s10);
        let out = fb.add(Ty::U64, a, u);
        fb.ret(vec![out]);
        fb.build()
    };
    {
        let mut fb = mb.function("program", nullary);
        fb.set_producer(Producer::TRust);
        let e = fb.create_block();
        fb.switch_to_block(e);
        let slot = fb.alloca(Ty::U64);
        let c = fb.uconst(Ty::U64, 30);
        fb.store(Ty::U64, slot, c);
        let rm = fb.cast(CastOp::PtrToPtr, Ty::Ptr, refm.clone(), slot);
        fb.call_void(bump, vec![rm]);
        let rs = fb.cast(CastOp::PtrToPtr, Ty::Ptr, refs.clone(), slot);
        let got = fb.call(read, vec![if mode == 1 { rm } else { rs }]); // 31
        let cell = fb.heap_alloc(Ty::U64, None, None, AllocOrigin::CleanHeap);
        let ten = fb.uconst(Ty::U64, 10);
        fb.store(Ty::U64, cell, ten);
        let rcv = fb.cast(CastOp::PtrToPtr, Ty::Ptr, rc.clone(), cell);
        if mode == 3 {
            fb.retain(ten);
        }
        let r = fb.call(rc_get, vec![if mode == 2 { cell } else { rcv }]); // 10 + 0*10 + 1 = 11
        fb.release(cell);
        let out = fb.add(Ty::U64, got, r); // 42
        fb.ret(vec![out]);
        fb.build();
    }
    mb.build().expect("ModuleBuilder::build: test fixture")
}

// ---------------- constants ----------------
fn build_constants(variant: u8) -> Module {
    let mut mb = ModuleBuilder::new("b6_constants");
    let u8_id = mb.add_type(Ty::U8);
    let n128 = mb.add_func_type(vec![], vec![Ty::U128]);
    let nf = mb.add_func_type(vec![], vec![Ty::F64]);
    let n8 = mb.add_func_type(vec![], vec![Ty::U8]);
    let big = (i128::MAX as u128) + 2;
    mb.add_global(global(
        "BIG",
        Ty::U128,
        false,
        Some(Constant::u128(u128::MAX)),
        None,
    ));
    {
        let mut fb = mb.function("rust_u128", n128);
        fb.set_producer(Producer::TRust);
        let e = fb.create_block();
        fb.switch_to_block(e);
        if variant == 3 {
            // one ADDED, otherwise unused instruction: a canonical U128 typed u64
            let _ = fb.const_value(Ty::U64, Constant::U128(big));
        }
        let v = if variant == 1 {
            fb.const_value(Ty::U128, Constant::U128(5))
        } else {
            fb.uconst(Ty::U128, big)
        };
        let one = fb.uconst(Ty::U128, 1);
        let s = fb.add(Ty::U128, v, one);
        fb.ret(vec![s]);
        fb.build();
    }
    {
        let mut fb = mb.function("clean_float", nf);
        fb.set_producer(Producer::Clean);
        let e = fb.create_block();
        fb.switch_to_block(e);
        let a = if variant == 4 {
            fb.const_value(Ty::F64, Constant::Int(1))
        } else {
            fb.fconst(Ty::F64, 1.5)
        };
        let b = fb.fconst(Ty::F64, 28.0);
        let m = fb.fmul(Ty::F64, a, b);
        fb.ret(vec![m]);
        fb.build();
    }
    {
        let arr = Ty::Array(u8_id, 6);
        let mut fb = mb.function("rust_bytes", n8);
        fb.set_producer(Producer::TRust);
        let e = fb.create_block();
        fb.switch_to_block(e);
        let c = if variant == 2 {
            Constant::Bytes {
                data: vec![0xff, 0xfe, 0, 0, 0, 0],
                utf8: true,
            }
        } else {
            Constant::str_bytes("héllo")
        };
        let v = fb.const_value(arr, c);
        let idx = fb.iconst(Ty::I64, 5);
        let el = fb.extract_element(Ty::U8, v, idx);
        fb.ret(vec![el]);
        fb.build();
    }
    mb.build().expect("ModuleBuilder::build: test fixture")
}

// ---------------- SeqMap ----------------
fn build_seqmap(bad_fwd: bool) -> Module {
    let mut mb = ModuleBuilder::new("b6_seqmap");
    let u32_id = mb.add_type(Ty::U32);
    let seq = Ty::Sequence(u32_id);
    let elem_ty = if bad_fwd {
        mb.add_func_type(vec![Ty::RefMut(Box::new(Ty::U32))], vec![Ty::U32])
    } else {
        mb.add_func_type(vec![Ty::RefMut(Box::new(Ty::U32))], vec![])
    };
    let nullary = mb.add_func_type(vec![], vec![seq.clone()]);
    let fwd = {
        let mut fb = mb.function("clean_double_elem", elem_ty);
        fb.set_producer(Producer::Clean);
        let e = fb.create_block();
        let r = fb.add_block_param(e, Ty::RefMut(Box::new(Ty::U32)));
        fb.switch_to_block(e);
        let b = fb.borrow_mut(r);
        let v = fb.load(Ty::U32, b);
        let two = fb.uconst(Ty::U32, 2);
        let d = fb.mul(Ty::U32, v, two);
        fb.store(Ty::U32, b, d);
        fb.end_borrow(b);
        if bad_fwd {
            fb.ret(vec![d]);
        } else {
            fb.ret(vec![]);
        }
        fb.build()
    };
    {
        let mut fb = mb.function("program", nullary);
        fb.set_producer(Producer::TRust);
        let e = fb.create_block();
        fb.switch_to_block(e);
        let s = fb.const_value(
            seq.clone(),
            Constant::Sequence(vec![Constant::Int(1), Constant::Int(5), Constant::Int(15)]),
        );
        let mapped = fb.copy(seq.clone(), s); // replaced by SeqMap below
        fb.ret(vec![mapped]);
        fb.build();
    }
    let mut m = mb.build().expect("ModuleBuilder::build: test fixture");
    let n = replace_inst(
        &mut m,
        "program",
        |i| matches!(i, Inst::Copy { .. }),
        |i| match i {
            Inst::Copy { ty, operand } => Inst::SeqMap {
                ty: ty.clone(),
                seq: *operand,
                fwd,
            },
            _ => unreachable!(),
        },
    );
    assert_eq!(n, 1);
    m
}

// ---------------- atomics ----------------
fn build_atomics(bad: bool) -> Module {
    let mut mb = ModuleBuilder::new("b6_atomics");
    let nullary = mb.add_func_type(vec![], vec![Ty::U64]);
    let mut fb = mb.function("program", nullary);
    fb.set_producer(Producer::TRust);
    let e = fb.create_block();
    fb.switch_to_block(e);
    let p = fb.alloca(Ty::U64);
    let c40 = fb.uconst(Ty::U64, 40);
    fb.atomic_store(Ty::U64, p, c40, Ordering::SeqCst);
    let one = fb.uconst(Ty::U64, 1);
    let old = fb.atomic_rmw(AtomicRMWOp::Add, Ty::U64, p, one, Ordering::SeqCst); // 40, now 41
    let c41 = fb.uconst(Ty::U64, 41);
    let c42 = fb.uconst(Ty::U64, 42);
    let (seen, ok) = fb.cmpxchg(Ty::U64, p, c41, c42, Ordering::AcqRel, Ordering::Acquire);
    fb.fence(Ordering::SeqCst);
    let now = fb.atomic_load(
        Ty::U64,
        p,
        if bad {
            Ordering::Release
        } else {
            Ordering::Acquire
        },
    );
    fb.assert(ok);
    let d = fb.sub(Ty::U64, seen, old); // 1
    let s = fb.add(Ty::U64, now, d); // 43
    let out = fb.sub(Ty::U64, s, one); // 42
    fb.ret(vec![out]);
    fb.build();
    mb.build().expect("ModuleBuilder::build: test fixture")
}

// ---------------- Invoke / LandingPad / Resume ----------------
/// mode 0: good. 1: unwind dest has a param. 2: normal edge passes wrong type.
/// 3: unwind dest has NO landingpad. 4: callee panics (assert false).
fn build_eh(mode: u8) -> Module {
    let mut mb = ModuleBuilder::new("b6_eh");
    let unary = mb.add_func_type(vec![Ty::U64], vec![Ty::U64]);
    let nullary = mb.add_func_type(vec![], vec![Ty::U64]);
    let callee = {
        let mut fb = mb.function("clean_may_unwind", unary);
        fb.set_producer(Producer::Clean);
        let e = fb.create_block();
        let x = fb.add_block_param(e, Ty::U64);
        fb.switch_to_block(e);
        if mode == 4 {
            let f = fb.bool_const(false);
            fb.assert(f);
        }
        let one = fb.uconst(Ty::U64, 1);
        let s = fb.add(Ty::U64, x, one);
        fb.ret(vec![s]);
        fb.build()
    };
    {
        let mut fb = mb.function("program", nullary);
        fb.set_producer(Producer::TRust);
        let e = fb.create_block();
        let cont = fb.create_block();
        let pad = fb.create_block();
        let v = fb.add_block_param(cont, if mode == 2 { Ty::U32 } else { Ty::U64 });
        if mode == 1 {
            fb.add_block_param(pad, Ty::Ptr);
        }
        fb.switch_to_block(e);
        let c = fb.uconst(Ty::U64, 41);
        let r = fb.invoke(callee, vec![c], cont, vec![], pad);
        let _ = r;
        fb.switch_to_block(cont);
        fb.ret(vec![v]);
        fb.switch_to_block(pad);
        if mode == 3 {
            let n = fb.null_ptr();
            fb.resume(n);
        } else {
            let (exn, _sel) = fb.landingpad(true, vec![]);
            fb.resume(exn);
        }
        fb.build();
    }
    let mut m = mb.build().expect("ModuleBuilder::build: test fixture");
    // normal edge passes the invoke's own result to cont
    let f = m
        .functions
        .iter_mut()
        .find(|f| f.name == "program")
        .unwrap();
    let node = f.blocks[0].body.last_mut().unwrap();
    let result = node.results[0];
    if let Inst::Invoke { normal_args, .. } = &mut node.inst {
        normal_args.push(result);
    }
    m
}

/// A function whose ENTRY block is a landing pad followed by Resume.
fn build_resume_direct() -> Module {
    let mut mb = ModuleBuilder::new("b6_resume_direct");
    let nullary = mb.add_func_type(vec![], vec![Ty::U64]);
    let mut fb = mb.function("program", nullary);
    fb.set_producer(Producer::TRust);
    let e = fb.create_block();
    fb.switch_to_block(e);
    let (exn, _sel) = fb.landingpad(true, vec![]);
    fb.resume(exn);
    fb.build();
    mb.build().expect("ModuleBuilder::build: test fixture")
}

/// The one shape in which a VALIDATED module still reaches `Resume` under
/// interpretation (measured at the port, after WS2.5's placement rules): the
/// producer's shared-cleanup lowering, `store exn -> slot` in the pad and
/// `resume (load slot)` in a pad-free cleanup block, where the cleanup block
/// is ALSO entered from the normal continuation (a plain `Br` into a non-pad
/// block is legal). `invoke` of a callee that returns normally, the normal
/// edge stores a null into the slot and branches to the cleanup, which
/// resumes the reloaded value.
fn build_resume_via_normal_path() -> Module {
    let mut mb = ModuleBuilder::new("b6_resume_via_normal_path");
    let unary = mb.add_func_type(vec![Ty::U64], vec![Ty::U64]);
    let nullary = mb.add_func_type(vec![], vec![Ty::U64]);
    let callee = {
        let mut fb = mb.function("clean_may_unwind", unary);
        fb.set_producer(Producer::Clean);
        let e = fb.create_block();
        let x = fb.add_block_param(e, Ty::U64);
        fb.switch_to_block(e);
        let one = fb.uconst(Ty::U64, 1);
        let s = fb.add(Ty::U64, x, one);
        fb.ret(vec![s]);
        fb.build()
    };
    let mut fb = mb.function("program", nullary);
    fb.set_producer(Producer::TRust);
    let e = fb.create_block();
    let cont = fb.create_block();
    let pad = fb.create_block();
    let cleanup = fb.create_block();
    fb.switch_to_block(e);
    let slot = fb.alloca(Ty::Ptr);
    let c = fb.uconst(Ty::U64, 41);
    let _ = fb.invoke(callee, vec![c], cont, vec![], pad);
    fb.switch_to_block(cont);
    let n = fb.null_ptr();
    fb.store(Ty::Ptr, slot, n);
    fb.br(cleanup, vec![]);
    fb.switch_to_block(pad);
    let (exn, _sel) = fb.landingpad(true, vec![]);
    fb.store(Ty::Ptr, slot, exn);
    fb.br(cleanup, vec![]);
    fb.switch_to_block(cleanup);
    let reloaded = fb.load(Ty::Ptr, slot);
    fb.resume(reloaded);
    fb.build();
    mb.build().expect("ModuleBuilder::build: test fixture")
}

// ---------------- CoroSuspend ----------------
/// mode 0 good; 1 = state-1 suspend yields a Bool from a `-> u64` generator;
/// 2 = an instruction FOLLOWS the suspend (it is a terminator); 3 = the state-0
/// suspend names its yielded u64 as the FRAME pointer.
fn build_coro(mode: u8) -> Module {
    let mut mb = ModuleBuilder::new("b6_coro");
    let step_ty = mb.add_func_type(vec![Ty::Ptr], vec![Ty::U64]);
    let nullary = mb.add_func_type(vec![], vec![Ty::U64]);
    let step = {
        let mut fb = mb.function("clean_gen_step", step_ty);
        fb.set_producer(Producer::Clean);
        let e = fb.create_block();
        let s0 = fb.create_block();
        let s1 = fb.create_block();
        let done = fb.create_block();
        let frame = fb.add_block_param(e, Ty::Ptr);
        fb.switch_to_block(e);
        let st = fb.load(Ty::I64, frame);
        fb.switch(
            st,
            vec![
                SwitchCase {
                    value: Constant::Int(0),
                    target: s0,
                    args: vec![],
                },
                SwitchCase {
                    value: Constant::Int(1),
                    target: s1,
                    args: vec![],
                },
            ],
            done,
            vec![],
        );
        fb.switch_to_block(s0);
        let v = fb.uconst(Ty::U64, 10);
        fb.ret(vec![v]);
        fb.switch_to_block(s1);
        let v = if mode == 1 {
            fb.bool_const(true)
        } else {
            fb.uconst(Ty::U64, 30)
        };
        fb.ret(vec![v]);
        fb.switch_to_block(done);
        let z = fb.uconst(Ty::U64, 0);
        fb.ret(vec![z]);
        fb.build()
    };
    {
        let mut fb = mb.function("program", nullary);
        fb.set_producer(Producer::TRust);
        let e = fb.create_block();
        fb.switch_to_block(e);
        let frame = fb.alloca(Ty::I64);
        let zero = fb.iconst(Ty::I64, 0);
        fb.store(Ty::I64, frame, zero);
        let a = fb.call(step, vec![frame]); // 10
        let b = fb.call(step, vec![frame]); // 30
        let c = fb.call(step, vec![frame]); // 0 (done)
        let st = fb.load(Ty::I64, frame); // 2
        let st = fb.cast(CastOp::Bitcast, Ty::I64, Ty::U64, st);
        let ab = fb.add(Ty::U64, a, b);
        let abc = fb.add(Ty::U64, ab, c);
        let out = fb.add(Ty::U64, abc, st); // 42
        fb.ret(vec![out]);
        fb.build();
    }
    let mut m = mb.build().expect("ModuleBuilder::build: test fixture");
    let f = m
        .functions
        .iter_mut()
        .find(|f| f.name == "clean_gen_step")
        .unwrap();
    let frame = f.blocks[0].params[0].0;
    for (bi, next) in [(1usize, 1i64), (2, 2)] {
        let node = f.blocks[bi].body.last_mut().unwrap();
        let Inst::Return { values } = &node.inst else {
            panic!()
        };
        let value = values[0];
        let frame = if mode == 3 && bi == 1 { value } else { frame };
        *node = InstrNode::new(Inst::CoroSuspend {
            frame,
            state_slot: 0,
            next_state: next,
            value,
        });
        if mode == 2 && bi == 1 {
            f.blocks[bi].body.push(InstrNode::new(Inst::Return {
                values: vec![value],
            }));
        }
    }
    m
}

// ---------------- GlobalAddr + TLS ----------------
fn build_globals(bad: bool) -> Module {
    let mut mb = ModuleBuilder::new("b6_globals");
    mb.add_global(global(
        "TLS_COUNTER",
        Ty::U64,
        true,
        Some(Constant::Int(40)),
        Some(TlsModel::LocalExec),
    ));
    mb.add_global(global(
        "TLS_IE",
        Ty::U64,
        true,
        Some(Constant::Int(1)),
        Some(TlsModel::InitialExec),
    ));
    mb.add_global(global(
        "TLS_GD",
        Ty::U64,
        true,
        Some(Constant::Int(1)),
        Some(TlsModel::GeneralDynamic),
    ));
    mb.add_global(global(
        "TLS_LD",
        Ty::U64,
        true,
        Some(Constant::Int(0)),
        Some(TlsModel::LocalDynamic),
    ));
    let nullary = mb.add_func_type(vec![], vec![Ty::U64]);
    let bump = {
        let mut fb = mb.function("clean_bump_tls", nullary);
        fb.set_producer(Producer::Clean);
        let e = fb.create_block();
        fb.switch_to_block(e);
        let p = fb.global_addr(GlobalId::new(if bad { 9 } else { 0 }));
        let v = fb.load(Ty::U64, p);
        let one = fb.uconst(Ty::U64, 1);
        let s = fb.add(Ty::U64, v, one);
        fb.store(Ty::U64, p, s);
        fb.ret(vec![s]);
        fb.build()
    };
    {
        let mut fb = mb.function("program", nullary);
        fb.set_producer(Producer::TRust);
        let e = fb.create_block();
        fb.switch_to_block(e);
        let _ = fb.call(bump, vec![]);
        let b = fb.call(bump, vec![]); // 42
        let p = fb.global_addr(GlobalId::new(0));
        let v = fb.load(Ty::U64, p); // 42
        let same = fb.icmp(trust_ir::ICmpOp::Eq, Ty::U64, b, v);
        fb.assert(same);
        fb.ret(vec![v]);
        fb.build();
    }
    mb.build().expect("ModuleBuilder::build: test fixture")
}

// ---------------- bool not ----------------
/// The spellings of `fn clean_bnot(b: bool) -> bool { !b }` the row compares:
/// the ratified one (`bxor %b, true`, SPEC_RATIFICATIONS §3.2), the refused
/// bitwise `not bool %b`, and the `select %b, false, true` baseline.
#[derive(Clone, Copy)]
enum BoolNot {
    BXorTrue,
    ScalarNot,
    Select,
}

fn build_bool_not(spelling: BoolNot) -> Module {
    let mut mb = ModuleBuilder::new("b6_bool_not");
    let ft = mb.add_func_type(vec![Ty::Bool], vec![Ty::Bool]);
    let mut fb = mb.function("clean_bnot", ft);
    fb.set_producer(Producer::Clean);
    let e = fb.create_block();
    let x = fb.add_block_param(e, Ty::Bool);
    fb.switch_to_block(e);
    let out = match spelling {
        BoolNot::BXorTrue => {
            let t = fb.bool_const(true);
            fb.binop(trust_ir::inst::BinOp::BXor, Ty::Bool, x, t)
        }
        BoolNot::ScalarNot => fb.unop(UnOp::Not, Ty::Bool, x),
        BoolNot::Select => {
            let t = fb.bool_const(true);
            let f = fb.bool_const(false);
            fb.select(Ty::Bool, x, f, t)
        }
    };
    fb.ret(vec![out]);
    fb.build();
    mb.build().expect("ModuleBuilder::build: test fixture")
}

// ---------------- Sequence element read ----------------
/// `fn program() -> u32` reading element 1 of `[1, 5, 15]` carried as a
/// `Sequence` (or an `Array`), at an index typed `u64` — or `i64` when
/// `signed_index` is set, the spelling WS3.17 refuses on a sequence (a
/// sequence's length is a property of the value, so the index TYPE is the only
/// place non-negativity can be stated) and still admits on an array (the
/// static range check bounds it there).
fn build_elem_read(sequence: bool, signed_index: bool) -> Module {
    let mut mb = ModuleBuilder::new("b6_elem_read");
    let u32_id = mb.add_type(Ty::U32);
    let nullary = mb.add_func_type(vec![], vec![Ty::U32]);
    let mut fb = mb.function("program", nullary);
    fb.set_producer(Producer::Clean);
    let e = fb.create_block();
    fb.switch_to_block(e);
    let items = vec![Constant::Int(1), Constant::Int(5), Constant::Int(15)];
    let v = if sequence {
        fb.const_value(Ty::Sequence(u32_id), Constant::Sequence(items))
    } else {
        fb.const_value(Ty::Array(u32_id, 3), Constant::Array(items))
    };
    let i1 = if signed_index {
        fb.iconst(Ty::I64, 1)
    } else {
        fb.uconst(Ty::U64, 1)
    };
    let el = fb.extract_element(Ty::U32, v, i1);
    fb.ret(vec![el]);
    fb.build();
    mb.build().expect("ModuleBuilder::build: test fixture")
}

// ---------------- Switch exhaustiveness claim ----------------
/// `exhaustive_enum_unreachable: true` stamped on a switch that is NEITHER
/// exhaustive (one case of a two-variant tag) NOR defaulting to `Unreachable`.
fn build_false_exhaustive_claim() -> Module {
    let mut mb = ModuleBuilder::new("b6_false_exhaustive");
    let ft = mb.add_func_type(vec![Ty::U8], vec![Ty::U64]);
    let mut fb = mb.function("rust_match", ft);
    fb.set_producer(Producer::TRust);
    let e = fb.create_block();
    let a = fb.create_block();
    let other = fb.create_block();
    let tag = fb.add_block_param(e, Ty::U8);
    fb.switch_to_block(e);
    fb.switch(
        tag,
        vec![SwitchCase {
            value: Constant::Int(0),
            target: a,
            args: vec![],
        }],
        other,
        vec![],
    );
    fb.switch_to_block(a);
    let one = fb.uconst(Ty::U64, 1);
    fb.ret(vec![one]);
    fb.switch_to_block(other);
    let seven = fb.uconst(Ty::U64, 7);
    fb.ret(vec![seven]);
    fb.build();
    let mut m = mb.build().expect("ModuleBuilder::build: test fixture");
    let n = replace_inst(
        &mut m,
        "rust_match",
        |i| matches!(i, Inst::Switch { .. }),
        |i| {
            let mut i = i.clone();
            if let Inst::Switch {
                exhaustive_enum_unreachable,
                ..
            } = &mut i
            {
                *exhaustive_enum_unreachable = true;
            }
            i
        },
    );
    assert_eq!(n, 1);
    m
}

// ---------------- union: the ratified byte-overlap model ----------------
/// `union U { a: u64, b: f64 }` spelled the only way the format admits
/// (lowering-target-subset.md "Unions", trust-ir/tests/union_byte_overlap_model.rs):
/// an untyped `[u8; 8]` carrier + typed Load/Store at one address.
/// `too_wide` = read a U128 out of the 8-byte carrier.
fn build_union_bytes(too_wide: bool) -> Module {
    let mut mb = ModuleBuilder::new("b6_union_bytes");
    let u8_id = mb.add_type(Ty::U8);
    let nullary = mb.add_func_type(vec![], vec![Ty::U64]);
    let mut fb = mb.function("program", nullary);
    fb.set_producer(Producer::TRust);
    let e = fb.create_block();
    fb.switch_to_block(e);
    let cell = fb.alloca_aligned(Ty::Array(u8_id, 8), 8);
    let one = fb.fconst(Ty::F64, 1.0);
    fb.store(Ty::F64, cell, one);
    let out = if too_wide {
        let wide = fb.load(Ty::U128, cell);
        fb.trunc(Ty::U128, Ty::U64, wide)
    } else {
        fb.load(Ty::U64, cell)
    };
    fb.ret(vec![out]);
    fb.build();
    mb.build().expect("ModuleBuilder::build: test fixture")
}

// ===========================================================================
// 1. The Lean-inductive <-> Rust-enum TREE carrier: ONE EnumDef, both producers
// ===========================================================================

fn tree_carrier_shared_enum_direct_layout() {
    let m = build_tree(Some(tree_direct_layout()));

    // One EnumDef; functions of BOTH producers name `Ty::Enum(0)` in their bodies.
    let users = |p: Producer| {
        m.functions
            .iter()
            .filter(|f| {
                f.producer == Some(p.clone())
                    && format!("{:?}", f.blocks).contains("Enum(EnumId(0))")
            })
            .map(|f| f.name.clone())
            .collect::<Vec<_>>()
    };
    let (rust_users, clean_users) = (users(Producer::TRust), users(Producer::Clean));
    assert!(feature_check(
        "b6.enum.shared_by_both_producers",
        m.enums.len() == 1 && !rust_users.is_empty() && !clean_users.is_empty(),
        &format!(
            "enums={} TRust users={rust_users:?} Clean users={clean_users:?}",
            m.enums.len()
        ),
    ));
    // twin: "shared" is NOMINAL. A structurally identical copy (EnumId 1) on the
    // Clean constructor's signature is a different type at the Rust call site.
    let mut copy = m.clone();
    let mut second = tree_def(Some(tree_direct_layout()));
    second.id = EnumId::new(1);
    second.name = "TreeCopy".into();
    copy.add_enum(second);
    let mk_ty = copy.function_by_name("clean_mk_leaf").unwrap().ty;
    copy.func_types[mk_ty.as_usize()].returns = vec![Ty::Enum(EnumId::new(1))];
    twin(
        "b6.enum.shared_by_both_producers",
        &copy,
        "Clean ctor re-typed to a structurally-equal COPY of the enum",
        |e| matches!(e, ValidationError::ReturnTypeMismatch { expected, actual, .. } if expected == "enum.1" && actual == "enum.0"),
    );

    // Direct-tag descriptor (v31), payload-first / tag-last.
    demo("b6.enum.direct_layout", &m, 41, true);
    let mut bad = m.clone();
    bad.enums[0].layout.as_mut().unwrap().encoding = EnumTagEncoding::Direct { tag_offset: 0 };
    twin(
        "b6.enum.direct_layout",
        &bad,
        "tag moved onto the payload",
        |e| {
            matches!(e, ValidationError::ConstTypeMismatch { location, actual, .. }
            if location == "enum.0 (Tree) layout" && actual.contains("tag overlaps variant"))
        },
    );

    // Execution through both languages: Rust builds leaf(40), leaf(2), node(&l,&r)
    // in memory (leaves via the CLEAN constructor, by value), the recursive CLEAN
    // `sum` walks it through the declared byte image.
    interp("b6.enum.tree.interpret", &m, "program", 42);
    // The descriptor is NORMATIVE for the byte image: a raw U64 load at offset 0
    // of a leaf cell is the payload; under the canonical fallback it is not.
    let canonical = build_tree(None);
    let (direct_raw, d1) = run_u(&m, "rust_leaf_image");
    let (canon_raw, d2) = run_u(&canonical, "rust_leaf_image");
    assert!(feature_check(
        "b6.enum.direct_layout.normative_bytes",
        direct_raw == Some(40) && canon_raw != Some(40) && validate_module(&canonical).is_empty(),
        &format!("declared: {d1} | canonical fallback: {d2}"),
    ));

    // Switch { exhaustive_enum_unreachable: true } survives the three lossless
    // transports and executes.
    let flag = |module: &Module| {
        module.functions[0]
            .blocks
            .iter()
            .flat_map(|b| &b.body)
            .any(|n| {
                matches!(
                    n.inst,
                    Inst::Switch {
                        exhaustive_enum_unreachable: true,
                        ..
                    }
                )
            })
    };
    let rt = roundtrip_all(&m);
    assert!(feature_check(
        "b6.switch.exhaustive_enum_unreachable",
        flag(&m)
            && [&rt.binary, &rt.json, &rt.msgpack]
                .iter()
                .all(|t| t.decoded.as_ref().is_some_and(flag)),
        "flag=true on the Clean match over Tree's full tag set {0,1}, default -> Unreachable; decoded true from binary/json/msgpack",
    ));
    let mut dup = m.clone();
    for node in dup.functions[0].blocks.iter_mut().flat_map(|b| &mut b.body) {
        if let Inst::Switch { cases, .. } = &mut node.inst {
            cases[1].value = Constant::Int(0);
        }
    }
    twin(
        "b6.switch.exhaustive_enum_unreachable",
        &dup,
        "two arms for tag 0",
        |e| matches!(e, ValidationError::DuplicateSwitchCase { block: 0, value } if value == "0"),
    );

    // FLIPPED by WS4.5 (GAP -> PASS; F-072). The archived GAP: canonical text
    // dropped all three of the enum layout descriptor, the per-variant field
    // names and the switch's exhaustiveness flag. The enum half carried the
    // descriptor (`layout(direct tag@0 ..)`); the remainder carries the field
    // names (`leaf(value: u64)`) and the flag (`switch .. ] exhaustive`), so
    // the Tree module now round-trips through text EXACTLY: no `#lossy`
    // marker, `parse(canonical(m)) == canonicalize(m)`, same stable digest.
    let canon = trust_ir::format::canonicalize(&m);
    let text = rt.text.decoded.as_ref();
    let text_src = String::from_utf8_lossy(&rt.text.encoded).into_owned();
    // Mutation control: delete ONLY the ` exhaustive` keyword (one arm of the
    // printer) and the parsed module is no longer equal — the exact-equality
    // leg below would catch a parser or printer that dropped the flag.
    let dropped_flag = trust_ir::parser::parse_module(&text_src.replacen(" exhaustive", "", 1));
    assert!(feature_check(
        "b6.text.drops_enum_layout_field_names_and_exhaustive_flag",
        rt.text.lossless()
            && rt.text.lossy.is_none()
            && text.is_some_and(|text| {
                text.enums[0].layout.is_some()
                    && text.enums[0].layout == canon.enums[0].layout
                    && text.enums[0]
                        .variants
                        .iter()
                        .any(|v| !v.field_names.is_empty())
                    && text.enums[0].variants == canon.enums[0].variants
                    && flag(text)
                    && *text == canon
                    && text.stable_digest() == canon.stable_digest()
            })
            && dropped_flag.as_ref().is_ok_and(|d| !flag(d) && *d != canon),
        &format!(
            "WS4.5: text carries the Tree layout, field names {:?} and the exhaustive flag \
             (text {}); marker-free = {}; dropping ` exhaustive` alone gives a different module = {}",
            canon.enums[0]
                .variants
                .iter()
                .map(|v| &v.field_names)
                .collect::<Vec<_>>(),
            rt.text.summary(),
            rt.text.lossy.is_none(),
            dropped_flag.as_ref().is_ok_and(|d| *d != canon),
        ),
    ));

    // FLIPPED (closed upstream by WS2.2, aa74e1eb + cb3a011c + d35d4723; F-029, static
    // half). The archived GAP: the PAYLOAD PROJECTION of the match was unchecked —
    // `validate_field_access` returned early on `Ty::Enum(_)`, so ONE change to the
    // well-formed Tree module (the `leaf` arm projects field 2, which only `node` has)
    // validated, also for codegen, and only the interpreter refused at run time. WS2.2
    // types each enum lane against the variants that have it: the leaf arm's `u64`
    // projection of lane 2 is now exactly one `OperandTypeMismatch` naming the only
    // candidate (`node: ptr`). Positive: the unchanged module validates for codegen
    // (the `demo` rows above). The interpreter is now variant-aware too (the lane
    // belongs to no field of the active `leaf`). The wrong-variant-but-same-type lane
    // is NOT statically decidable and stays the ratified UB of WS2.2 item 4.
    let base_errors = validate_module_for_codegen(&m);
    let mut wrong_proj = m.clone();
    let n = replace_inst(
        &mut wrong_proj,
        "clean_tree_sum",
        |i| {
            matches!(
                i,
                Inst::ExtractField {
                    ty: Ty::U64,
                    field: 1,
                    ..
                }
            )
        },
        |i| match i {
            Inst::ExtractField { ty, aggregate, .. } => Inst::ExtractField {
                ty: ty.clone(),
                aggregate: *aggregate,
                field: 2,
            },
            _ => unreachable!(),
        },
    );
    assert_eq!(n, 1);
    let proj_errors = validate_module_for_codegen(&wrong_proj);
    let proj_run = run_nullary(&wrong_proj, "program");
    assert!(feature_check(
        "b6.enum.payload_projection_unchecked",
        base_errors.is_empty()
            && matches!(
                proj_errors.as_slice(),
                [ValidationError::OperandTypeMismatch { block: 1, op, role, expected, actual }]
                    if op == "extract_field" && role == "field"
                        && expected == "one of {node: ptr}" && actual == "u64"
            )
            && matches!(&proj_run, Err(e) if e.starts_with("UndefinedBehavior")
                && e.contains("lane 2 belongs to no field of active variant leaf")),
        &format!(
            "closed upstream by WS2.2: baseline validate_module_for_codegen={base_errors:?}; leaf arm projects field 2 of a `leaf` value: validate_module_for_codegen={proj_errors:?}; run={proj_run:?}"
        ),
    ));

    // FLIPPED (WS2.6, F-039). The archived GAP: the exhaustiveness claim was taken
    // on faith — inst.rs said it is set "only ... when the case values are EXACTLY
    // the enum's full discriminant tag set, and the default arm is Unreachable", and
    // no rule in trust-ir-build/src/validate.rs read the field. That blocked the CHC
    // translator, which conjoins `selector in {cases}` into the default arm, so a
    // false claim made a LIVE default arm vacuously provable. WS2.6 reads the flag:
    // (a) a live default is exactly `ExhaustiveSwitchDefaultReachable`; (b) the
    // Clean match over a Tree that gained an inhabited third variant is exactly
    // `ExhaustiveSwitchCasesIncomplete` naming it. The run-time behaviour is
    // unchanged (the interpreter still executes the live arm / reaches
    // Unreachable): the fix is that the module no longer validates.
    let lie = build_false_exhaustive_claim();
    let errors = validate_module_for_codegen(&license(&lie));
    let live = run_with_args(
        &lie,
        "rust_match",
        vec![InterpretValue::int(Ty::U8, 1).unwrap()],
    );
    // Second leg, derived from the WELL-FORMED Tree module by one change to the
    // ENUM (not the switch): Tree gains a third variant `empty`, so the Clean
    // match's case set {0,1} is no longer "EXACTLY the enum's full discriminant tag
    // set" while it still claims so. The Clean ctor is re-pointed at the new
    // variant so the uncovered tag is actually reached.
    let mut three = m.clone();
    three.enums[0].variants.push(EnumVariant {
        name: "empty".into(),
        fields: vec![],
        field_names: vec![],
    });
    three.enums[0]
        .layout
        .as_mut()
        .unwrap()
        .variant_field_offsets
        .push(vec![]);
    let three_errors = validate_module_for_codegen(&three);
    let n = replace_inst(
        &mut three,
        "clean_mk_leaf",
        |i| matches!(i, Inst::Const { .. } | Inst::InsertField { .. }),
        |i| match i {
            Inst::Const { ty, .. } => Inst::Const {
                ty: ty.clone(),
                value: Constant::Aggregate(vec![Constant::Int(2)]),
            },
            Inst::InsertField { ty, aggregate, .. } => Inst::Copy {
                ty: ty.clone(),
                operand: *aggregate,
            },
            _ => unreachable!(),
        },
    );
    assert_eq!(n, 2);
    let three_ctor_errors = validate_module_for_codegen(&three);
    let three_run = run_nullary(&three, "program");
    let tree_ty = Ty::Enum(EnumId::new(0)).to_string();
    let incomplete = |errors: &[ValidationError]| {
        matches!(
            errors,
            [ValidationError::ExhaustiveSwitchCasesIncomplete { block: 0, enum_ty, reason }]
                if *enum_ty == tree_ty
                    && reason == "no case for inhabited variant(s) {empty = 2}, so the default arm is reachable"
        )
    };
    assert!(feature_check(
        "b6.switch.exhaustive_claim_unchecked",
        matches!(
            errors.as_slice(),
            [ValidationError::ExhaustiveSwitchDefaultReachable { block: 0, reason }]
                if reason == "the default block bb2 is not exactly [unreachable] (2 instruction(s))"
        ) && live
            .as_ref()
            .ok()
            .and_then(|v| v.first())
            .and_then(common::as_u128)
            == Some(7)
            && incomplete(&three_errors)
            && incomplete(&three_ctor_errors)
            && matches!(&three_run, Err(e) if e.starts_with("UndefinedBehavior") && e.contains("unreachable")),
        &format!(
            "closed by WS2.6: (a) 1-of-2-case switch with a LIVE default and flag=true: validate_module_for_codegen={errors:?} (the arm still executes: {live:?}); \
             (b) Tree + third variant, Clean match still {{0,1}} + flag=true: validate_module_for_codegen={three_errors:?}/{three_ctor_errors:?}, run={three_run:?}"
        ),
    ));
}

// ===========================================================================
// 2. Niche + v37 untagged descriptors
// ===========================================================================

fn enum_niche_and_untagged_layouts() {
    let m = build_enum_layouts();
    let rt = demo("b6.enum.niche_and_untagged", &m, 38, true);
    // WS4.5 CLOSED THIS ROW. The enum half carried the two descriptors — a
    // NICHE encoding (reserved value, interval, lane type and offset) and a
    // v37 UNTAGGED one — through `layout(..)`; the remainder carries the
    // per-variant field names that were this module's last text residue. So
    // the module now round-trips EXACTLY with no marker: the `.roundtrip` row
    // above asserts `structurally_equal`, and this row asserts that the
    // descriptors are among what came back, not merely that the totals agree.
    let text = rt
        .text
        .decoded
        .as_ref()
        .expect("text decodes, no #lossy marker");
    let canon = trust_ir::format::canonicalize(&m);
    assert!(feature_check(
        "b6.text.drops_niche_and_untagged_descriptors",
        rt.text.lossy.is_none()
            && text.enums.len() == canon.enums.len()
            && canon.enums.iter().all(|e| e.layout.is_some())
            && text
                .enums
                .iter()
                .zip(&canon.enums)
                .all(|(got, want)| got.layout == want.layout)
            && *text == canon,
        &format!(
            "WS4.5: text carries the niche and untagged descriptors verbatim ({:?}) and, since \
             the remainder, the field names too — equal to canonicalize(original) with no \
             restoration: {}",
            text.enums.iter().map(|e| &e.layout).collect::<Vec<_>>(),
            *text == canon
        ),
    ));

    // niche: `none` is the reserved value 0xFFFF_FF01 of the u32 payload lane; the
    // image is 4 bytes, no tag word.
    interp(
        "b6.enum.niche.none_image",
        &m,
        "niche_none_image",
        0xFFFF_FF01,
    );
    // `some(7)` round-trips through the 4-byte image: tag 1 recovered, payload 7.
    interp(
        "b6.enum.niche.some_roundtrip",
        &m,
        "niche_some_roundtrip",
        107,
    );
    let mut bad = m.clone();
    bad.enums[0].variants.push(EnumVariant {
        name: "third".into(),
        fields: vec![],
        field_names: vec![],
    });
    bad.enums[0]
        .layout
        .as_mut()
        .unwrap()
        .variant_field_offsets
        .push(vec![]);
    twin(
        "b6.enum.niche",
        &bad,
        "a third variant the niche interval does not cover",
        |e| {
            matches!(e, ValidationError::ConstTypeMismatch { location, expected, .. }
            if location == "enum.0 (OptIdx) layout" && expected.contains("niche interval plus the untagged variant to cover every inhabited variant"))
        },
    );

    // untagged: the 8-byte image IS the payload (raw 99) and the sole variant's tag
    // is recovered on load (payload 99): 99 + 99.
    interp("b6.enum.untagged.image", &m, "untagged_image", 198);
    let mut bad = m.clone();
    bad.enums[1].variants.push(EnumVariant {
        name: "second".into(),
        fields: vec![],
        field_names: vec![],
    });
    bad.enums[1]
        .layout
        .as_mut()
        .unwrap()
        .variant_field_offsets
        .push(vec![]);
    twin(
        "b6.enum.untagged",
        &bad,
        "untagged image with TWO variants",
        |e| {
            matches!(e, ValidationError::ConstTypeMismatch { location, expected, actual }
            if location == "enum.1 (Wrapper) layout" && expected.contains("exactly one variant under the untagged encoding") && actual == "2 variants")
        },
    );
}

// ===========================================================================
// 3. Declared struct layout + v42 tuple layouts
// ===========================================================================

fn struct_and_tuple_declared_layouts() {
    // Pair { a: u8 @8, b: u64 @0 } (rustc field reordering); (u8,u64,u8) @ [8,0,9].
    let m = build_layouts(0, 8, vec![8, 0, 9]);
    // WS4.5 (struct half) FLIPPED `text_lossless` false -> true: the struct's
    // field NAMES and rustc-reordered OFFSETS (`a: u8 @8, b: u64 @0`) are now
    // carried by canonical text, so the dump is no longer `#lossy`-refused and
    // parses back structurally equal. The declared TUPLE layout is carried by
    // the v42 table and was never the text blocker here.
    let rt = demo("b6.layout.struct_and_tuple", &m, 42, true);
    interp(
        "b6.layout.struct.image",
        &m,
        "struct_image",
        0x1122_3344_5566_7788,
    );
    interp(
        "b6.layout.tuple_v42.image",
        &m,
        "tuple_image",
        0x0102_0304_0506_0708,
    );
    twin(
        "b6.layout.struct",
        &build_layouts(3, 8, vec![8, 0, 9]),
        "u64 field declared at byte 3",
        |e| matches!(e, ValidationError::StructLayoutInconsistent { struct_id: 0, reason } if reason.contains("effective alignment")),
    );
    twin(
        "b6.layout.tuple_v42",
        &build_layouts(0, 8, vec![0, 0, 9]),
        "tuple fields 0 and 1 both at byte 0",
        |e| matches!(e, ValidationError::TupleLayoutInconsistent { reason } if reason.contains("tuple layout ty.0") && reason.contains("incoherent")),
    );

    // The overlapping tuple descriptor at the CODEC boundary: the binary reader
    // refuses the blob outright; serde (JSON) decodes it and leaves the refusal to
    // the validator (same error as the twin above).
    let overlap = build_layouts(0, 8, vec![0, 0, 9]);
    let bin = trust_ir::binary::deserialize_module(
        &trust_ir::binary::serialize_module(&overlap).expect("serialize_module: test fixture"),
    );
    let via_json = serde_json::from_str::<Module>(&serde_json::to_string(&overlap).unwrap());
    assert!(feature_check(
        "b6.layout.tuple_v42.binary_reader_refuses_overlap",
        matches!(&bin, Err(e) if format!("{e:?}").contains("InvalidData") && format!("{e:?}").contains("tuple layout"))
            && matches!(&via_json, Ok(back) if validate_module(back).iter().any(|e| matches!(e, ValidationError::TupleLayoutInconsistent { .. }))),
        &format!(
            "binary read => {:?}; JSON read decodes and validate_module refuses it",
            bin.as_ref().err()
        ),
    ));

    // GAP (text): struct field NAMES and OFFSETS are dropped (tuple layouts are
    // kept). trust-ir-conformance/tests/conformance.rs:1013-1066
    // (`normalize_text_lossy_fields`).
    // WS4.2: refused as `#lossy`; the grammar's drop is measured on the
    // marker-deleted copy until WS4.5 carries the field.
    let text = rt
        .text
        .carried()
        .expect("text decodes once the #lossy marker is deleted");
    let canon = trust_ir::format::canonicalize(&m);
    let canonical_text = trust_ir::format::canonical(&m);
    // WS4.5 (struct half) CLOSED THIS ROW. Canonical text carries a struct
    // field's NAME and its OFFSET (`a: u8 @8, b: u64 @0`), so the dump is no
    // longer `#lossy`-refused and the decoded module is structurally equal
    // WITHOUT restoring anything. Before WS4.5 the fields came back with empty
    // names and no offsets, and the row's whole point was that restoring those
    // two things by hand was sufficient to make it equal — i.e. text was
    // dropping exactly them.
    //
    // The rustc-reordered offsets are the part worth keeping in view: `b` is at
    // 0 and `a` at 8, so a decoder that invented offsets positionally would
    // reproduce the WRONG layout and this row would still pass. It does not
    // invent them; it reads them.
    assert!(feature_check(
        "b6.text.drops_struct_field_names_and_offsets",
        rt.text.decode_error.is_none()
            && *text == canon
            && text.structs[0]
                .fields
                .iter()
                .all(|f| !f.name.is_empty() && f.offset.is_some())
            && text.structs[0].fields[0].offset == Some(8)
            && text.structs[0].fields[1].offset == Some(0)
            && text.tuple_layouts == m.tuple_layouts,
        &format!(
            "WS4.5: text-decoded Pair fields={:?}; equal to canonicalize(original) with NO \
             restoration: {}; tuple_layouts kept={}",
            text.structs[0].fields,
            *text == canon,
            text.tuple_layouts == m.tuple_layouts
        ),
    ));

    // NEGATIVE TWIN: the carrying is real, not a coincidence of ordering. Swap
    // the two offsets in the text and the decoded module must STOP matching —
    // if the parser were ignoring `@off` and assigning positionally, this would
    // still compare equal.
    {
        let forged = canonical_text.replace("a: u8 @8", "a: u8 @9");
        let reparsed =
            trust_ir::parser::parse_module(&forged).expect("the forged text still parses");
        assert_ne!(
            reparsed, canon,
            "WS4.5: a changed @offset must change the decoded module"
        );
        assert_eq!(reparsed.structs[0].fields[0].offset, Some(9));
    }
}

// ===========================================================================
// 4. union
// ===========================================================================

fn union_has_no_nominal_carrier() {
    // The RATIFIED spelling (lowering-target-subset.md "Unions";
    // trust-ir/tests/union_byte_overlap_model.rs): an untyped byte carrier and
    // typed accesses at one address. `u.b = 1.0; u.a` == 0x3FF0_0000_0000_0000.
    let m = build_union_bytes(false);
    demo("b6.union.byte_overlap_model", &m, 38, true);
    interp(
        "b6.union.byte_overlap_model.interpret",
        &m,
        "program",
        0x3FF0_0000_0000_0000,
    );
    // twin (execution level — the model has no validator-visible field list): a
    // field wider than the carrier is caught only when it runs.
    let wide = run_nullary(&build_union_bytes(true), "program");
    assert!(feature_check(
        "b6.union.byte_overlap_model.negative_twin",
        matches!(&wide, Err(e) if e.starts_with("UndefinedBehavior") && e.contains("access [0..16) is out of bounds for allocation size 8")),
        &format!("u128 read of an 8-byte carrier => {wide:?}"),
    ));

    // FLIPPED GAP -> PASS (WS3.18, F-050; G18-3 kept). There is no `Ty::Union` /
    // `UnionDef` by ratified design, and a union spelled as a StructDef whose
    // fields share offset 0 is refused everywhere: the layout authority
    // (`LayoutError::StructLayoutIncoherent`), the interpreter ("declared
    // layout has overlapping fields") and, since WS2.3, the validator
    // (`StructLayoutInconsistent { reason: "fields overlap" }`). What the row
    // measured as a gap was that this refusal was the END of the road: the
    // producer met "overlapping fields" and nothing said what to emit instead
    // ("requires a trust-ir union representation", trust-ir-bridge
    // lower.rs:15872-15881). The row now asserts the NAMED refusal and that
    // its rendered text, and the interpreter's, point at the byte-overlap
    // carrier (lowering-target-subset.md "Unions", producer guidance rules
    // 1-6; executable pins `tests/union_carrier.rs`). Mutation controls: the
    // disjoint baseline (b@8) has a layout and validates, and the carrier
    // spelling of the union (section 4 above) validates, so the refusal never
    // blocks the ratified spelling.
    let base = build_layouts(0, 8, vec![8, 0, 9]);
    let union_ = build_layouts(0, 0, vec![8, 0, 9]);
    let pair = Ty::Struct(StructId::new(0));
    let (base_shape, union_shape) = (base.ty_layout_shape(&pair), union_.ty_layout_shape(&pair));
    let union_run = run_nullary(&union_, "struct_image");
    let refused = validate_module(&union_);
    let rendered: Vec<String> = refused.iter().map(ToString::to_string).collect();
    let names_the_carrier = |text: &str| {
        text.contains("byte-overlap carrier") && text.contains("lowering-target-subset.md")
    };
    let carrier_errors = validate_module(&build_union_bytes(false));
    assert!(feature_check(
        "b6.union.overlapping_struct_fields_rejected",
        matches!(
            refused.as_slice(),
            [ValidationError::StructLayoutInconsistent { struct_id: 0, reason }]
                if *reason == STRUCT_FIELDS_OVERLAP_REASON
        ) && rendered.iter().all(|text| names_the_carrier(text))
            && matches!(union_shape, Err(LayoutError::StructLayoutIncoherent(id)) if id == StructId::new(0))
            && matches!(&union_run, Err(e) if e.starts_with("TypeError")
                && e.contains("overlapping fields 0 and 1") && names_the_carrier(e))
            && base_shape.is_ok()
            && validate_module(&base).is_empty()
            && carrier_errors.is_empty(),
        &format!(
            "Pair{{a@0,b@0}}: validate_module={rendered:?}; ty_layout_shape={union_shape:?}; \
             interpreter={union_run:?}; disjoint baseline shape ok={}; carrier spelling \
             validate_module={carrier_errors:?}",
            base_shape.is_ok()
        ),
    ));

    // FLIPPED (closed upstream by WS2.3, 3014ce2c, F-031). That refusal was NOT
    // a ValidationError: `validate_target_pinned_struct_layouts` never checked
    // pairwise overlap, so validate_module AND validate_module_for_codegen
    // accepted a struct the interpreter cannot run. Now one declared-struct-
    // layout coherence rule, shared with `shape`, runs in the validator: the
    // overlapping twin is exactly ONE named StructLayoutInconsistent on each
    // entry point. Mutation control: the disjoint baseline (b@8) validates on
    // both, so the rule refuses the overlap, not the declared offsets.
    let structural = validate_module(&union_);
    let codegen = validate_module_for_codegen(&license(&union_));
    let base_structural = validate_module(&base);
    let base_codegen = validate_module_for_codegen(&license(&base));
    let overlap = |errors: &[ValidationError]| {
        matches!(
            errors,
            [ValidationError::StructLayoutInconsistent { struct_id: 0, reason }] if *reason == "fields overlap"
        )
    };
    assert!(feature_check(
        "b6.union.overlap_is_not_a_validation_error",
        overlap(&structural)
            && overlap(&codegen)
            && base_structural.is_empty()
            && base_codegen.is_empty(),
        &format!(
            "closed upstream by 3014ce2c: target-pinned Pair{{a@0,b@0}}: validate_module={structural:?} validate_module_for_codegen(all functions Gated)={codegen:?}; disjoint baseline Pair{{a@0,b@8}}: {base_structural:?} / {base_codegen:?}"
        ),
    ));
}

// ===========================================================================
// 5. Closure
// ===========================================================================

fn closure_value_crosses_languages() {
    let m = build_closure(false);
    demo_with("b6.closure", &m, 38, true, false);
    // Rust applies the literal (5+16), Clean applies the re-captured value (5+16).
    interp("b6.closure.interpret", &m, "program", 42);
    twin(
        "b6.closure",
        &build_closure(true),
        "literal names a target lacking the capture parameter",
        |e| matches!(e, ValidationError::CallIndirectClosureTargetMismatch { target, .. } if target == "rust_ident"),
    );

    // FLIPPED by WS3.13 (F-055, wire v58). `Module.closure_layouts` carries the
    // environment frame's byte image, with the v42 tuple-table rules; the
    // codegen refusal is lifted for exactly the closure types that declare one.
    // The RIGHT-REASON twin is the same module WITHOUT the row: it still has no
    // layout and still earns both `UnlowerableForCodegen` refusals, so the rule
    // reads the declaration rather than having stopped refusing.
    let closure_refusals = |module: &Module| {
        validate_module_for_codegen(&license(module))
            .iter()
            .filter(|e| matches!(e, ValidationError::UnlowerableForCodegen { inst, detail, .. } if *inst == "CallIndirect" && detail.contains("Ty::Closure")))
            .count()
    };
    let closure_ty = Ty::Closure(ClosureTyId::new(0));
    let undeclared_shape = m.ty_layout_shape(&closure_ty);
    let undeclared_refusals = closure_refusals(&m);

    // The producer's declared frame: one `U64` capture at offset 0 in an
    // 8-byte, 8-aligned environment. A declared frame is sized against the
    // target's scalar layout, so the module names one (the undeclared
    // control above needs none: absence is not a layout claim).
    let mut declared = build_closure(false);
    declared.target_info = Some(target());
    declared.closure_layouts.push(ClosureLayoutDescriptor {
        origin: None,
        closure: ClosureTyId::new(0),
        size: 8,
        align: 8,
        capture_offsets: vec![0],
    });
    let declared_shape = declared.ty_layout_shape(&closure_ty);
    let declared_refusals = closure_refusals(&declared);
    let declared_structural = validate_module(&declared);
    assert!(feature_check(
        "b6.closure.no_layout_not_lowerable",
        matches!(undeclared_shape, Err(LayoutError::UnsupportedTyShape(_)))
            && undeclared_refusals == 2
            && matches!(
                &declared_shape,
                Ok(shape) if shape.size_bits == 64
                    && shape.align_bits == Some(64)
                    && matches!(&shape.kind, TyLayoutKind::Closure { captures, .. } if captures.len() == 1)
            )
            && declared_refusals == 0
            && declared_structural.is_empty(),
        &format!(
            "no layout row: ty_layout_shape={undeclared_shape:?}, CallIndirect refusals={undeclared_refusals} (one per producer); declared v58 row: ty_layout_shape={declared_shape:?}, refusals={declared_refusals}, validate_module={declared_structural:?}"
        ),
    ));

    // MUTATION CONTROL: the layout row must be READ, not merely counted. A
    // capture that runs past the declared frame is refused by the same rule
    // that admitted the honest row, and the codegen refusal comes back.
    let mut short = build_closure(false);
    short.target_info = Some(target());
    short.closure_layouts.push(ClosureLayoutDescriptor {
        origin: None,
        closure: ClosureTyId::new(0),
        size: 4,
        align: 8,
        capture_offsets: vec![0],
    });
    assert!(feature_check(
        "b6.closure.declared_layout_is_checked",
        matches!(
            short.ty_layout_shape(&closure_ty),
            Err(LayoutError::ClosureLayoutIncoherent(_))
        ) && validate_module(&short)
            .iter()
            .any(|e| matches!(e, ValidationError::TupleLayoutInconsistent { reason } if reason.starts_with(trust_ir_build::validate::CLOSURE_LAYOUT_TABLE_REASON_PREFIX))),
        &format!(
            "8-byte capture in a 4-byte frame: ty_layout_shape={:?}; validate_module={:?}",
            short.ty_layout_shape(&closure_ty),
            validate_module(&short)
        ),
    ));
}

// ===========================================================================
// 6. Fat pointers
// ===========================================================================

fn fat_pointers_all_four_kinds() {
    let m = build_fatptr(false);
    // ContainerVtable selects v40.
    demo(
        "b6.fatptr.slice_str_containerlen_containervtable",
        &m,
        40,
        true,
    );
    // Rust assembles &[u64;3], &str(6), ContainerLen(3), ContainerVtable; Clean reads
    // the three lengths + element [1] through the slice data pointer + slot 0 THROUGH
    // the ContainerVtable metadata pointer: 3+6+3+23+7.
    interp("b6.fatptr.interpret", &m, "program", 42);
    twin(
        "b6.fatptr",
        &build_fatptr(true),
        "ContainerVtable metadata read as a u64 length",
        |e| {
            matches!(e, ValidationError::PointerMetadataTypeMismatch { ptr_ty, expected, actual, .. }
            if ptr_ty == "fatptr<container_vtable>" && expected == "ptr" && actual == "u64")
        },
    );

    // FLIPPED (closed by WS3.8, F-049 constant half). The archived GAP: the
    // only `Ty::FatPtr` CONSTANT admitted was the null pair, so `static S: &str
    // = "..."`, const tables of slices and enum seeds holding a `&str` had no
    // spelling except erasing the fat type to an untyped `(ptr, u64)` tuple, and
    // `[SymbolAddr(HELLO), Int(6)]` typed `fatptr<str>` was refused as
    // `ConstTypeMismatch { expected: "fatptr<str>", actual: "aggregate[2]" }` at
    // both the global initializer and the function constant. The module-aware
    // constant walk now admits it as a window of one immutable, module-defined
    // UTF-8 array global. Negative twin (right reason): the same window one byte
    // too long (`Int(7)` over the 6-byte `HELLO`) is exactly one
    // `PointerConstantRefused { reason: WindowOutOfBounds { offset: 0, length:
    // 7, capacity: 6 } }` at each of the two positions. Mutation controls: the
    // null pair and the type-erased `(ptr, u64)` global still validate.
    let erased = {
        let mut mb = ModuleBuilder::new("b6_fatptr_const_erased");
        let u8_id = mb.add_type(Ty::U8);
        mb.add_global(global(
            "HELLO",
            Ty::Array(u8_id, 6),
            false,
            Some(Constant::str_bytes("héllo")),
            None,
        ));
        mb.add_global(global(
            "GREETING",
            Ty::Tuple(vec![Ty::Ptr, Ty::U64]),
            false,
            Some(Constant::Aggregate(vec![
                Constant::SymbolAddr {
                    symbol: "HELLO".into(),
                    addend: 0,
                },
                Constant::Int(6),
            ])),
            None,
        ));
        validate_module(&mb.build().expect("ModuleBuilder::build: test fixture"))
    };
    let null = validate_module(&build_fatptr_const(None));
    let non_null = validate_module(&build_fatptr_const(Some(6)));
    let overlong = validate_module(&build_fatptr_const(Some(7)));
    let window_refused = |loc: &str| {
        overlong
            .iter()
            .filter(|e| {
                matches!(e, ValidationError::PointerConstantRefused { location, symbol, ty, reason }
                if location.contains(loc)
                    && symbol == "HELLO"
                    && ty == "fatptr<str>"
                    && *reason == PointerConstantRefusal::WindowOutOfBounds {
                        offset: 0,
                        length: 7,
                        capacity: 6,
                    })
            })
            .count()
            == 1
    };
    let twin_exact = overlong.len() == 2
        && window_refused("global 'GREETING'")
        && window_refused("function 'greeting'");
    assert!(feature_check(
        "b6.fatptr.non_null_constant_rejected",
        non_null.is_empty() && null.is_empty() && erased.is_empty() && twin_exact,
        &format!(
            "closed by WS3.8: [SymbolAddr(HELLO), Int(6)] typed fatptr<str> => {non_null:?}; \
             null pair => {null:?}; type-erased (ptr,u64) tuple global => {erased:?}; \
             negative twin Int(7) over the 6-byte HELLO => {overlong:?}"
        ),
    ));
}

// ===========================================================================
// 7. Ref / RefMut + Borrow / EndBorrow; Rc + Retain / Release
// ===========================================================================

fn references_and_refcounts() {
    let m = build_borrow_rc(0);
    demo("b6.ref_refmut_rc", &m, 38, true);
    // Rust `&mut` bump 30->31, Clean `&` read = 31; Clean Rc<u64> retain/is_unique/
    // release = 10 + 10*0(shared) + 1(unique again) = 11.
    interp("b6.ref_refmut_rc.interpret", &m, "program", 42);
    twin(
        "b6.ref_refmut.borrow",
        &build_borrow_rc(1),
        "`&mut u64` passed to the Clean `&u64` parameter",
        |e| {
            matches!(e, ValidationError::CallArgTypeMismatch { callee, expected, actual, caller_producer: Some(c), callee_producer: Some(d), .. }
            if callee == "clean_read" && expected == "&u64" && actual == "&mut u64" && c == "trust" && d == "clean")
        },
    );
    twin(
        "b6.rc.typed_param",
        &build_borrow_rc(2),
        "bare Ptr passed to the Clean `Rc<u64>` parameter",
        |e| {
            matches!(e, ValidationError::CallArgTypeMismatch { callee, expected, actual, .. }
            if callee == "clean_rc_get" && expected == "Rc<u64>" && actual == "ptr")
        },
    );
    twin(
        "b6.rc.retain_release",
        &build_borrow_rc(3),
        "Retain of a u64",
        |e| matches!(e, ValidationError::OperandNotPointer { op, ty, .. } if *op == "retain" && ty == "u64"),
    );
    twin(
        "b6.ref_refmut.borrow_operand",
        &build_borrow_rc(4),
        "Borrow of a u64",
        |e| matches!(e, ValidationError::OperandNotPointer { op, ty, .. } if *op == "borrow" && ty == "u64"),
    );

    // SPLIT by WS2.7 (5f28fc7e, F-040). Borrow DISCIPLINE was carried but not
    // checked: the validator's only rule was "operand is a pointer", so a
    // `BorrowMut` taken THROUGH a `&u64` parameter, and a Borrow with no
    // EndBorrow, both validated (also for codegen) and executed. Baseline:
    // mode 0 above validates for codegen and runs to 42.
    let baseline = validate_module_for_codegen(&license(&m));
    let (r0, _) = run_u(&m, "program");
    let mut mut_through_shared = m.clone();
    let n = replace_inst(
        &mut mut_through_shared,
        "clean_read",
        |i| matches!(i, Inst::Borrow { .. }),
        |i| match i {
            Inst::Borrow { ptr } => Inst::BorrowMut { ptr: *ptr },
            _ => unreachable!(),
        },
    );
    assert_eq!(n, 1);
    let mut no_end = m.clone();
    let f = no_end
        .functions
        .iter_mut()
        .find(|f| f.name == "clean_read")
        .unwrap();
    f.blocks[0]
        .body
        .retain(|n| !matches!(n.inst, Inst::EndBorrow { .. }));
    let (e1, e2) = (
        validate_module_for_codegen(&license(&mut_through_shared)),
        validate_module_for_codegen(&license(&no_end)),
    );
    let (r2, _) = run_u(&no_end, "program");
    // Structural half FLIPPED: the `&mut` upgrade of the Clean `&u64` is exactly
    // one named BorrowMutThroughSharedRef; the unmutated baseline (mutation
    // control) stays valid.
    assert!(feature_check(
        "b6.ref_refmut.borrow_discipline_unchecked.structural_half",
        baseline.is_empty()
            && r0 == Some(42)
            && matches!(
                e1.as_slice(),
                [ValidationError::BorrowMutThroughSharedRef { block: 0 }]
            ),
        &format!(
            "closed upstream by 5f28fc7e: baseline => {baseline:?} run={r0:?}; BorrowMut through a `&u64` param: validate_module_for_codegen={e1:?}"
        ),
    ));
    // Liveness half RATIFIED-OUT (TRUST.md item 12: borrow LIVENESS is a
    // producer obligation): a Borrow with no EndBorrow still validates and
    // still runs. Held exactly, so a flow-sensitive borrow checker that starts
    // refusing it trips the row and forces the ratification to be amended.
    assert!(feature_ratified(
        "b6.ref_refmut.borrow_discipline_unchecked.liveness_half",
        Expect::Accepted,
        Outcome::of(&e2).given(&[("Borrow without EndBorrow executes to 42", r2 == Some(42))]),
        &format!("Borrow without EndBorrow: validate_module_for_codegen={e2:?} run={r2:?}"),
    ));
}

// ===========================================================================
// 8. Constants
// ===========================================================================

fn constants_u128_bytes_float() {
    let m = build_constants(0);
    demo("b6.const.u128_bytes_float", &m, 38, true);
    interp(
        "b6.const.u128.interpret",
        &m,
        "rust_u128",
        (i128::MAX as u128) + 3,
    );
    let f = run_nullary(&m, "clean_float");
    assert!(feature_check(
        "b6.const.float.interpret",
        matches!(f.as_deref(), Ok([v]) if v.kind == InterpretValueKind::FloatBits(42.0f64.to_bits())),
        &format!("1.5 * 28.0 = {f:?}"),
    ));
    interp(
        "b6.const.bytes.interpret",
        &m,
        "rust_bytes",
        u128::from(b'o'),
    );
    twin(
        "b6.const.u128",
        &build_constants(1),
        "non-canonical Constant::U128(5)",
        |e| matches!(e, ValidationError::ConstTypeMismatch { expected, .. } if expected.contains("canonical integer spelling")),
    );
    twin(
        "b6.const.u128.narrower_type",
        &build_constants(3),
        "canonical Constant::U128 typed u64",
        |e| matches!(e, ValidationError::ConstTypeMismatch { location, expected, .. } if location.contains("rust_u128") && expected == "u64"),
    );
    twin(
        "b6.const.bytes",
        &build_constants(2),
        "utf8=true over invalid UTF-8",
        |e| matches!(e, ValidationError::ConstTypeMismatch { expected, .. } if expected.contains("valid UTF-8")),
    );
    twin(
        "b6.const.float",
        &build_constants(4),
        "Constant::Int typed f64",
        |e| matches!(e, ValidationError::ConstTypeMismatch { location, expected, .. } if location.contains("clean_float") && expected == "f64"),
    );
}

// ===========================================================================
// 9. SeqMap
// ===========================================================================

fn seqmap_general_element_function() {
    let m = build_seqmap(false);
    demo("b6.seqmap", &m, 38, true);
    // Rust maps a Clean element function `fn(&mut u32) { *x *= 2 }` over [1,5,15].
    let out = run_nullary(&m, "program");
    let elems: Option<Vec<u128>> = match out.as_deref() {
        Ok(
            [
                InterpretValue {
                    kind: InterpretValueKind::Sequence(items),
                    ..
                },
            ],
        ) => items.iter().map(common::as_u128).collect(),
        _ => None,
    };
    assert!(feature_check(
        "b6.seqmap.interpret",
        elems == Some(vec![2, 10, 30]),
        &format!("program() = {out:?}")
    ));
    twin(
        "b6.seqmap",
        &build_seqmap(true),
        "element function returns a value",
        |e| matches!(e, ValidationError::SeqMapFwdSignatureMismatch { fwd, expected, .. } if fwd == "clean_double_elem" && expected == "fn(&mut u32)"),
    );

    // Closed by WS3.17 (F-051). The GAP found here: a `Ty::Sequence` VALUE had
    // no validated element read — `check_extract_element_operands` admitted
    // only `supports_element_ops()` = vector/array, yet the interpreter
    // executed ExtractElement over a Sequence, and the Lean model type-errored
    // on it. Now all three engines agree: the read over `seq<u32>` validates
    // with a result type exactly the element type and an UNSIGNED index, the
    // array baseline is unchanged beside it, and the interpreter still answers
    // 5. `Sequence` stays verification-level (no layout): the same body is
    // named by `codegen_lowerability_errors`, never lowered.
    let array = validate_module(&build_elem_read(false, false));
    let seq = validate_module(&build_elem_read(true, false));
    let (seq_run, detail) = run_u(&build_elem_read(true, false), "program");
    let codegen = validate_module_for_codegen(&license(&build_elem_read(true, false)));
    assert!(feature_check(
        "b6.sequence.no_validated_element_read",
        array.is_empty()
            && seq.is_empty()
            && seq_run == Some(5)
            && matches!(
                codegen.as_slice(),
                [ValidationError::UnlowerableForCodegen { inst: "ExtractElement", detail, .. }]
                    if detail.contains("Ty::Sequence") && detail.contains("no machine layout")
            ),
        &format!(
            "closed by WS3.17: array baseline={array:?}; sequence => {seq:?}; interpreter: \
             {detail}; validate_module_for_codegen={codegen:?}"
        ),
    ));
    // The right-reason twin: the SIGNED index the archived GAP row used is
    // refused on a sequence by name (and, as the array baseline above shows,
    // only there).
    let signed_array = validate_module(&build_elem_read(false, true));
    assert!(
        signed_array.is_empty(),
        "an i64 index into [u32; 3] must stay admitted: {signed_array:?}"
    );
    twin(
        "b6.sequence.no_validated_element_read",
        &build_elem_read(true, true),
        "extract_element over seq<u32> at an i64 index",
        |e| matches!(e, ValidationError::InvalidVectorElementOp { op, reason, .. } if op == "extract_element" && reason.contains("a sequence index must be an unsigned integer")),
    );
}

// ===========================================================================
// 10. Atomics
// ===========================================================================

fn atomics() {
    let m = build_atomics(false);
    demo("b6.atomics", &m, 38, true);
    interp("b6.atomics.interpret", &m, "program", 42);
    twin(
        "b6.atomics",
        &build_atomics(true),
        "AtomicLoad with a Release ordering",
        |e| matches!(e, ValidationError::IllegalAtomicOrdering { op, ordering, .. } if *op == "atomic_load" && ordering == "release"),
    );
}

// ===========================================================================
// 11. Invoke / LandingPad / Resume
// ===========================================================================

fn exception_handling() {
    let m = build_eh(0);
    demo("b6.eh.invoke_landingpad_resume", &m, 38, true);
    // Rust `invoke`s a Clean callee; normal edge carries the result to `cont`.
    interp("b6.eh.invoke.normal_edge.interpret", &m, "program", 42);
    twin(
        "b6.eh.invoke.unwind_edge",
        &build_eh(1),
        "landing-pad block with a parameter",
        |e| {
            matches!(
                e,
                ValidationError::BranchArgCountMismatch {
                    target: 2,
                    expected: 1,
                    actual: 0,
                    ..
                }
            )
        },
    );
    twin(
        "b6.eh.invoke.normal_edge",
        &build_eh(2),
        "u64 result passed to a u32 continuation parameter",
        |e| matches!(e, ValidationError::BranchArgTypeMismatch { target: 1, expected, actual, .. } if expected == "u32" && actual == "u64"),
    );

    // RATIFIED-OUT (panic=abort, docs/ub-numerics-policy.md §4 "Unwind
    // surface under panic=abort"; roadmap WS2.5 re-labels this row rather than
    // flipping it): `Invoke` never takes the unwind edge, and there is no
    // instruction that RAISES. A callee that panics surfaces as a whole-run
    // `Panic` error and the cleanup pad never runs -- which IS the ratified
    // panic=abort projection both engines execute. Baseline: mode 0 above
    // returns 42. Taking the unwind edge is the WS8 decision gate F-122. The
    // row still holds its exact shape, so an engine that starts taking unwind
    // edges trips it.
    let panicking = build_eh(4);
    let out = run_nullary(&panicking, "program");
    assert!(feature_ratified(
        "b6.eh.invoke_never_takes_unwind_edge",
        Expect::refused("Panic"),
        Outcome::of_message(&out).given(&[(
            "the panicking module validates",
            validate_module(&panicking).is_empty()
        )]),
        &format!("invoke of a panicking Clean callee with a cleanup pad => {out:?}"),
    ));

    // RATIFIED-OUT (same ratification): `Resume` is `UnsupportedInstruction`
    // under interpretation, because a re-raise is meaningful only after an
    // unwind edge was taken. Re-measured at the port: the archived way to
    // reach it -- a function whose ENTRY block is a landing pad -- no longer
    // validates (WS2.5 `MisplacedLandingPad`), and the interpreter now refuses
    // at the pad before the `Resume`. The one shape in which a VALIDATED
    // module still reaches `Resume` is a shared cleanup block (`resume (load
    // slot)`, the producer's lowering) that the normal path also enters; the
    // interpreter refuses it by name, fail-closed.
    let reachable = build_resume_via_normal_path();
    let out = run_nullary(&reachable, "program");
    let direct = build_resume_direct();
    let direct_errors = validate_module(&direct);
    let direct_run = run_nullary(&direct, "program");
    assert!(feature_ratified(
        "b6.eh.resume_unsupported_by_interpreter",
        Expect::refused_with(
            "UnsupportedInstruction",
            &["resume", "does not model in-flight host exceptions"]
        ),
        Outcome::of_message(&out).given(&[
            (
                "the shared-cleanup module validates",
                validate_module(&reachable).is_empty()
                    && validate_module_for_codegen(&license(&reachable)).is_empty()
            ),
            (
                "the entry-landing-pad module is refused as MisplacedLandingPad",
                matches!(
                    direct_errors.as_slice(),
                    [ValidationError::MisplacedLandingPad { block: 0, reason }]
                        if reason.contains("entry block")
                )
            ),
            (
                "the interpreter refuses the entry pad before the Resume",
                matches!(&direct_run, Err(e) if e.starts_with("UnsupportedInstruction")
                    && e.contains("landingpad entered without an unwind edge"))
            ),
        ]),
        &format!(
            "shared cleanup entered by the normal path => {out:?}; entry-pad module: \
             validate={direct_errors:?}, run={direct_run:?}"
        ),
    ));

    // FLIPPED (closed upstream by 5a945757 / b3a1b963, roadmap WS2.5): the
    // archived ratchet recorded that LandingPad PLACEMENT was unchecked -- an
    // `unwind_dest` with NO LandingPad validated, and so did a LandingPad as
    // the first instruction of a function's ENTRY block. PASS: under the
    // licensed codegen door, the pad-less unwind target is refused as
    // `UnwindDestWithoutLandingPad { block: 0, target: 2 }` (plus the Resume
    // rule's follow-on on the same pad-less block, since the function then has
    // no landingpad at all), and the entry-block pad as `MisplacedLandingPad`
    // naming the entry block -- nothing else. Negative-twin baseline: the
    // well-placed mode-0 module validates under the same door.
    let good = validate_module_for_codegen(&license(&build_eh(0)));
    let no_pad = validate_module_for_codegen(&license(&build_eh(3)));
    let entry_pad = validate_module_for_codegen(&license(&direct));
    let no_pad_named = no_pad.len() == 2
        && no_pad.iter().any(|e| {
            matches!(
                e,
                ValidationError::UnwindDestWithoutLandingPad {
                    block: 0,
                    target: 2
                }
            )
        })
        && no_pad.iter().any(|e| {
            matches!(e, ValidationError::MisplacedLandingPad { block: 2, reason }
                if reason.contains("resume of a value no landing pad produced")
                    && reason.contains("contains no landingpad"))
        });
    let entry_pad_named = matches!(
        entry_pad.as_slice(),
        [ValidationError::MisplacedLandingPad { block: 0, reason }] if reason.contains("entry block")
    );
    assert!(feature_check(
        "b6.eh.landingpad_placement_unchecked",
        good.is_empty() && no_pad_named && entry_pad_named,
        &format!(
            "closed upstream by 5a945757/b3a1b963: validate_module_for_codegen (all Gated) -- \
             well-placed baseline: {good:?}; unwind_dest without a LandingPad: {no_pad:?}; \
             LandingPad in the entry block: {entry_pad:?}"
        ),
    ));
}

// ===========================================================================
// 12. CoroSuspend
// ===========================================================================

fn coroutine_suspend() {
    let m = build_coro(0);
    demo("b6.coro_suspend", &m, 38, true);
    // Rust owns the frame; the Clean generator yields 10, 30, then completes (0),
    // leaving state 2 in the frame: 10+30+0+2.
    interp("b6.coro_suspend.interpret", &m, "program", 42);
    twin(
        "b6.coro_suspend",
        &build_coro(2),
        "an instruction after the suspend terminator",
        |e| matches!(e, ValidationError::MidBlockTerminator { op, .. } if op == "coro_suspend"),
    );

    // FLIPPED (closed upstream by WS2.1, d8e403d4 + e1c09924; F-028): the
    // archived ratchet recorded that the YIELDED value was not checked against
    // the function's return type -- the return-type rule matched `Inst::Return`
    // ONLY, although the instruction is DEFINED as `GEP + Store + Return(value)`
    // (inst.rs, the `CoroSuspend` doc comment), so a `-> u64` generator yielding
    // a Bool validated and failed only when the resumer used the value. PASS:
    // under the licensed codegen door the suspend is refused as exactly
    // `ReturnTypeMismatch { block: 2, expected: "u64", actual: "bool" }` --
    // the SAME finding the `Return` spelling of the same yield gets (mutation
    // control: one change, the terminator), so the two arms cannot drift.
    // Positive baseline: the well-typed generator (mode 0) validates under the
    // same door (its `demo` row above also runs it to 42).
    let good = validate_module_for_codegen(&license(&build_coro(0)));
    let bad = build_coro(1);
    let errors = validate_module_for_codegen(&license(&bad));
    let out = run_nullary(&bad, "program");
    let mut via_return = bad.clone();
    {
        let f = via_return
            .functions
            .iter_mut()
            .find(|f| f.name == "clean_gen_step")
            .unwrap();
        let node = f.blocks[2].body.last_mut().unwrap();
        let Inst::CoroSuspend { value, .. } = node.inst else {
            panic!("build_coro(1) suspends in block 2")
        };
        *node = InstrNode::new(Inst::Return {
            values: vec![value],
        });
    }
    let via_return_errors = validate_module_for_codegen(&license(&via_return));
    let yield_named = |e: &[ValidationError]| {
        matches!(e, [ValidationError::ReturnTypeMismatch { block: 2, expected, actual }]
            if expected == "u64" && actual == "bool")
    };
    assert!(feature_check(
        "b6.coro_suspend.yield_type_unchecked",
        good.is_empty() && yield_named(&errors) && yield_named(&via_return_errors),
        &format!(
            "closed upstream by WS2.1 (d8e403d4/e1c09924): validate_module_for_codegen (all Gated) -- \
             well-typed generator: {good:?}; `-> u64` generator yielding Bool via CoroSuspend: \
             {errors:?} (run={out:?}); the same yield via Return: {via_return_errors:?}"
        ),
    ));

    // FLIPPED (closed upstream by WS2.1, e1c09924; F-028): the archived
    // ratchet recorded that the FRAME operand was unchecked -- `CoroSuspend`
    // had no operand rule at all, although it is DEFINED as `GEP frame + Store
    // + Return`. PASS: one change to the good module (the state-0 suspend names
    // its u64 yield as the frame) is refused as exactly
    // `OperandNotPointer { block: 1, op: "coro_suspend", ty: "u64" }` -- the
    // GEP base rule, and nothing else (the yield itself is well typed).
    // Positive baseline: the Ptr-framed mode-0 module above validates.
    let bad = build_coro(3);
    let errors = validate_module_for_codegen(&license(&bad));
    let out = run_nullary(&bad, "program");
    assert!(feature_check(
        "b6.coro_suspend.frame_operand_unchecked",
        good.is_empty()
            && matches!(errors.as_slice(),
                [ValidationError::OperandNotPointer { block: 1, op, ty }]
                    if op == "coro_suspend" && ty == "u64"),
        &format!(
            "closed upstream by WS2.1 (e1c09924): CoroSuspend {{ frame: <u64 value> }}: \
             validate_module_for_codegen(all Gated)={errors:?}; run={out:?}; Ptr-framed baseline: {good:?}"
        ),
    ));
}

// ===========================================================================
// 13. GlobalAddr + TLS
// ===========================================================================

fn global_addr_and_tls() {
    let m = build_globals(false);
    let rt = demo("b6.global_addr_tls", &m, 38, true);
    // Clean bumps the thread-local twice (40 -> 42); Rust re-reads the same cell.
    interp("b6.global_addr_tls.interpret", &m, "program", 42);
    let models: Vec<_> = rt
        .text
        .decoded
        .as_ref()
        .unwrap()
        .globals
        .iter()
        .map(|g| g.tls)
        .collect();
    assert!(feature_check(
        "b6.tls.all_four_models_carried",
        models
            == vec![
                Some(TlsModel::LocalExec),
                Some(TlsModel::InitialExec),
                Some(TlsModel::GeneralDynamic),
                Some(TlsModel::LocalDynamic)
            ],
        &format!("decoded from TEXT (and equal in binary/json/msgpack): {models:?}"),
    ));
    twin(
        "b6.global_addr",
        &build_globals(true),
        "GlobalAddr of global 9 of 4",
        |e| matches!(e, ValidationError::GlobalNotFound { global_id: 9, .. }),
    );
    // TLS twin (codec level: the validator has no TLS rule): an unknown model is
    // refused by the JSON reader, never defaulted.
    let json = String::from_utf8(rt.json.encoded.clone())
        .unwrap()
        .replace("\"LocalExec\"", "\"EmulatedTls\"");
    let decoded = serde_json::from_str::<Module>(&json);
    assert!(feature_check(
        "b6.tls.negative_twin",
        matches!(&decoded, Err(e) if e.to_string().contains("unknown variant `EmulatedTls`")),
        &format!(
            "tls model `EmulatedTls` => {:?}",
            decoded.as_ref().err().map(|e| e.to_string())
        ),
    ));
}

// ===========================================================================
// 14. scalar Bool negation
// ===========================================================================

fn scalar_bool_not_is_rejected() {
    // FLIPPED GAP -> PASS "ratified single spelling" (WS2.21, F-033;
    // docs/SPEC_RATIFICATIONS.md §3.2). The row measured `UnOp::Not` at
    // `Ty::Bool` refused as the generic `BinOpRequiresInteger` while the
    // producer (trust-clean-ir) emitted exactly that and skipped `neg`. The
    // ratified resolution is ONE spelling, not a second one: boolean negation
    // is the Bool connective `bxor %b, true` (the 4b069189 doctrine: a Bool is
    // never negated through an overloaded integer op), and `not bool` is
    // refused BY NAME (`UnOpNotOnScalarBool`), its text naming the spelling to
    // emit. Mutation controls: the ratified spelling validates and computes
    // `!b` for both inputs, the select baseline still validates, and `not` on a
    // bool VECTOR is unchanged (`bool_logic_binop.rs`, and
    // `bool_negation_spelling.rs` beside this battery).
    let ratified = build_bool_not(BoolNot::BXorTrue);
    let ratified_errors = validate_module(&ratified);
    let select = validate_module(&build_bool_not(BoolNot::Select));
    let scalar = validate_module(&build_bool_not(BoolNot::ScalarNot));
    let rendered: Vec<String> = scalar.iter().map(ToString::to_string).collect();
    let negates = |input: bool| {
        matches!(
            run_with_args(&ratified, "clean_bnot", vec![InterpretValue::bool(input)]).as_deref(),
            Ok([v]) if v.as_bool() == Some(!input)
        )
    };
    assert!(feature_check(
        "b6.bool.scalar_not_rejected",
        matches!(
            scalar.as_slice(),
            [ValidationError::UnOpNotOnScalarBool { .. }]
        ) && rendered
            .iter()
            .all(|text| text.contains("boolean negation is `bxor %b, true`"))
            && ratified_errors.is_empty()
            && negates(true)
            && negates(false)
            && select.is_empty(),
        &format!(
            "UnOp::Not@Bool => {rendered:?}; bxor %b, true validates ({ratified_errors:?}), \
             !true={} !false={}; select baseline validates ({select:?})",
            negates(true),
            negates(false)
        ),
    ));
}

// 15. ABI facts with no slot: `b6.abi.*` are compile-time ratchets in
//     `field_ratchets.rs`.

// ===========================================================================
// 16. The BOXED form of the tree carrier: recursive fields typed `Rc<Tree>`
// ===========================================================================

/// `inductive Tree | leaf (v : UInt64) | node (l r : Tree)` as Clean's Perceus
/// heap sees it: every constructor cell lives on `AllocOrigin::CleanHeap` and the
/// recursive fields are TYPED `Rc<Tree>` (not the erased `Ty::Ptr` of section 1).
///
/// mode 0 good: the Clean ctor returns `Rc<Tree>`; Rust builds the `node` cell
///        through the MEMORY lane of the normative descriptor (whole-image init,
///        then field stores at offsets 0 / 8 and the tag byte at 16).
/// mode 1 twin: Rust hands the bare `Ptr` cell to the Clean `Rc<Tree>` parameter.
/// mode 2 twin: Rust builds the node at REGISTER level with the pre-WS3.5
///        `Const` seed + InsertField — stays refused (no constant inhabits `Rc<_>`).
/// mode 5 PASS: Rust builds the node at REGISTER level with WS3.5's
///        `make_aggregate enum.0 variant 1 (%l1, %l2)` over `(Rc<Tree>, Rc<Tree>)`.
/// mode 3 PASS: memory lane WITHOUT the whole-image init (padding bytes 17..24 of
///        the cell are never written) — rustc-style field-wise construction,
///        defined since WS2.14 (padding is don't-care on a typed aggregate load).
/// mode 4 twin: mode 3 without the `right` store at offset 8, a byte the ACTIVE
///        `node` variant's field covers — still undefined behaviour at offset 8.
fn build_rc_tree(mode: u8) -> Module {
    let tree = Ty::Enum(EnumId::new(0));
    let rc = Ty::Rc(Box::new(tree.clone()));
    let mut mb = ModuleBuilder::new("b6_rc_tree");
    let sum_ty = mb.add_func_type(vec![rc.clone()], vec![Ty::U64]);
    let mk_ty = mb.add_func_type(vec![Ty::U64], vec![rc.clone()]);
    let nullary = mb.add_func_type(vec![], vec![Ty::U64]);
    let sum_id = mb
        .peek_next_func_id()
        .expect("peek_next_func_id: test fixture");
    {
        let mut fb = mb.function("clean_rc_tree_sum", sum_ty);
        fb.set_producer(Producer::Clean);
        let entry = fb.create_block();
        let leaf = fb.create_block();
        let node = fb.create_block();
        let dead = fb.create_block();
        let t = fb.add_block_param(entry, rc.clone());
        fb.switch_to_block(entry);
        let v = fb.load(tree.clone(), t);
        let tag = fb.extract_field(Ty::U8, v, 0);
        fb.switch(
            tag,
            vec![
                SwitchCase {
                    value: Constant::Int(0),
                    target: leaf,
                    args: vec![],
                },
                SwitchCase {
                    value: Constant::Int(1),
                    target: node,
                    args: vec![],
                },
            ],
            dead,
            vec![],
        );
        fb.switch_to_block(leaf);
        let value = fb.extract_field(Ty::U64, v, 1);
        fb.ret(vec![value]);
        fb.switch_to_block(node);
        let l = fb.extract_field(rc.clone(), v, 1);
        let r = fb.extract_field(rc.clone(), v, 2);
        let a = fb.call(sum_id, vec![l]);
        let b = fb.call(sum_id, vec![r]);
        let s = fb.add(Ty::U64, a, b);
        fb.ret(vec![s]);
        fb.switch_to_block(dead);
        fb.unreachable();
        fb.build();
    }
    let mk_id = {
        // `clean_alloc_ctor`-shaped: allocate the cell on the Clean heap, fill it,
        // hand back the typed counted reference.
        let mut fb = mb.function("clean_rc_mk_leaf", mk_ty);
        fb.set_producer(Producer::Clean);
        let entry = fb.create_block();
        let x = fb.add_block_param(entry, Ty::U64);
        fb.switch_to_block(entry);
        let seed = fb.const_value(
            tree.clone(),
            Constant::Aggregate(vec![Constant::Int(0), Constant::Int(0)]),
        );
        let out = fb.insert_field(tree.clone(), seed, 1, x);
        let cell = fb.heap_alloc(tree.clone(), None, None, AllocOrigin::CleanHeap);
        fb.store(tree.clone(), cell, out);
        let h = fb.cast(CastOp::PtrToPtr, Ty::Ptr, rc.clone(), cell);
        fb.ret(vec![h]);
        fb.build()
    };
    {
        let mut fb = mb.function("program", nullary);
        fb.set_producer(Producer::TRust);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        let c40 = fb.uconst(Ty::U64, 40);
        let c2 = fb.uconst(Ty::U64, 2);
        let l1 = fb.call(mk_id, vec![c40]);
        let l2 = fb.call(mk_id, vec![c2]);
        let cell = fb.heap_alloc(tree.clone(), None, None, AllocOrigin::CleanHeap);
        if mode == 2 {
            let seed = fb.const_value(
                tree.clone(),
                Constant::Aggregate(vec![Constant::Int(1), Constant::Int(0), Constant::Int(0)]),
            );
            let n1 = fb.insert_field(tree.clone(), seed, 1, l1);
            let n2 = fb.insert_field(tree.clone(), n1, 2, l2);
            fb.store(tree.clone(), cell, n2);
        } else if mode == 5 {
            let node = fb.make_enum_variant(tree.clone(), 1, vec![l1, l2]);
            fb.store(tree.clone(), cell, node);
        } else {
            if mode != 3 && mode != 4 {
                let init = fb.const_value(
                    tree.clone(),
                    Constant::Aggregate(vec![Constant::Int(0), Constant::Int(0)]),
                );
                fb.store(tree.clone(), cell, init);
            }
            fb.store(rc.clone(), cell, l1);
            if mode != 4 {
                let p8 = fb.gep_byte_offset(cell, 8);
                fb.store(rc.clone(), p8, l2);
            }
            let p16 = fb.gep_byte_offset(cell, 16);
            let one = fb.uconst(Ty::U8, 1);
            fb.store(Ty::U8, p16, one);
        }
        let root = fb.cast(CastOp::PtrToPtr, Ty::Ptr, rc.clone(), cell);
        let out = fb.call(sum_id, vec![if mode == 1 { cell } else { root }]);
        fb.ret(vec![out]);
        fb.build();
    }
    let mut m = mb.build().expect("ModuleBuilder::build: test fixture");
    let mut def = tree_def(Some(tree_direct_layout()));
    def.variants[1].fields = vec![rc.clone(), rc];
    m.add_enum(def);
    m
}

fn tree_carrier_rc_typed_recursion() {
    let m = build_rc_tree(0);
    // Self-referential nominal type: enum.0's own variant names `Rc<enum.0>`.
    let recursive =
        m.enums[0].variants[1].fields == vec![Ty::Rc(Box::new(Ty::Enum(EnumId::new(0)))); 2];
    assert!(recursive);
    demo("b6.enum.tree_rc_typed", &m, 38, true);
    interp("b6.enum.tree_rc_typed.interpret", &m, "program", 42);
    twin(
        "b6.enum.tree_rc_typed",
        &build_rc_tree(1),
        "bare Ptr cell passed to the Clean `Rc<Tree>` parameter",
        |e| {
            matches!(e, ValidationError::CallArgTypeMismatch { callee, expected, actual, .. }
            if callee == "clean_rc_tree_sum" && expected == "Rc<enum.0>" && actual == "ptr")
        },
    );

    // Closed by WS3.5 (F-049, register-seed half; was a GAP found in review): an
    // enum (or any aggregate) value holding a TYPED reference can now be
    // originated at register level with `Inst::MakeAggregate` —
    // `make_aggregate enum.0 variant 1 (%l1, %l2)` over `(Rc<Tree>, Rc<Tree>)`
    // validates and sums to 42 (mode 5). The old spelling is the right-reason
    // twin and stays EXACTLY where the gap measured it: `Inst::Const` still
    // admits no constant at `Rc<_>` / `&_` / `&mut _` (a constant reference has
    // no provenance — the WS3.5 DECIDE's rejected alternative), so the
    // `[Int(1), Int(0), Int(0)]` seed (mode 2) is still exactly two
    // `ConstTypeMismatch` and the Ptr-erased seed still validates. No constant
    // rule was widened. Mode 5 is measured through validation, the licensed
    // codegen entry point and execution; the row was cut while the
    // instruction had no wire tag, and its four-format round trip is pinned
    // since the v51 INST wire batch by the conformance golden
    // `inst_wire_batch`, not here.
    let register = build_rc_tree(5);
    let register_errors = validate_module(&register);
    let register_codegen = validate_module_for_codegen(&license(&register));
    let (register_got, register_run) = run_u(&register, "program");
    let const_seed = build_rc_tree(2);
    let errors = validate_module(&const_seed);
    let seed_refused = errors
        .iter()
        .filter(|e| {
            matches!(e, ValidationError::ConstTypeMismatch { location, expected, actual }
            if location == "function 'program' bb0" && expected == "Rc<enum.0>" && actual == "int")
        })
        .count();
    let erased_baseline = validate_module(&build_tree(Some(tree_direct_layout())));
    assert!(feature_check(
        "b6.enum.typed_ref_payload_has_no_register_seed",
        register_errors.is_empty()
            && register_codegen.is_empty()
            && register_got == Some(42)
            && seed_refused == 2
            && errors.len() == 2
            && erased_baseline.is_empty(),
        &format!(
            "closed by WS3.5: make_aggregate enum.0 variant 1 (Rc<Tree>, Rc<Tree>): validate={register_errors:?}, validate_module_for_codegen(all Gated)={register_codegen:?}, {register_run}; Const-seed twin [Int(1), Int(0), Int(0)] => {errors:?} (expected exactly two ConstTypeMismatch Rc<enum.0>/int); Ptr-erased seed validates ({erased_baseline:?})"
        ),
    ));

    // Closed by WS2.14 (F-030; was a GAP found in review): a whole-aggregate
    // `Load` requires only the bytes a live field of the decoded value covers —
    // the tag lane plus the ACTIVE variant's fields — so rustc-style field-wise
    // construction (field stores + discriminant store, padding 17..24 never
    // written) followed by a whole-enum move is defined, and returns 42 like the
    // whole-image-init baseline (mode 0). Right-reason twin (mode 4): the same
    // construction without the `right` store leaves a COVERED byte (offset 8)
    // uninitialized, which is still exactly the uninit-read fault at offset 8.
    let uninit = build_rc_tree(3);
    let errors = validate_module_for_codegen(&license(&uninit));
    let out = run_nullary(&uninit, "program");
    let got = out
        .as_ref()
        .ok()
        .and_then(|v| v.first())
        .and_then(common::as_u128);
    let baseline = run_nullary(&build_rc_tree(0), "program");
    let baseline_got = baseline
        .as_ref()
        .ok()
        .and_then(|v| v.first())
        .and_then(common::as_u128);
    let covered = build_rc_tree(4);
    let covered_errors = validate_module_for_codegen(&license(&covered));
    let covered_out = run_nullary(&covered, "program");
    assert!(feature_check(
        "b6.enum.fieldwise_init_uninit_padding_is_ub_on_load",
        errors.is_empty()
            && got == Some(42)
            && baseline_got == Some(42)
            && covered_errors.is_empty()
            && matches!(&covered_out, Err(e) if e.starts_with("UndefinedBehavior")
                && e.contains("Load: reading uninitialized byte at offset 8")),
        &format!(
            "closed by WS2.14: field-wise node construction without whole-image init: validate_module_for_codegen(all Gated)={errors:?}; run={out:?}; baseline run={baseline:?}; covered-byte twin (right child never written): validate_module_for_codegen={covered_errors:?}, run={covered_out:?}"
        ),
    ));
}

#[test]
fn two_language_b6() {
    common::run_target(
        "b6",
        &[
            (
                "tree_carrier_shared_enum_direct_layout",
                tree_carrier_shared_enum_direct_layout,
            ),
            (
                "enum_niche_and_untagged_layouts",
                enum_niche_and_untagged_layouts,
            ),
            (
                "struct_and_tuple_declared_layouts",
                struct_and_tuple_declared_layouts,
            ),
            ("union_has_no_nominal_carrier", union_has_no_nominal_carrier),
            (
                "closure_value_crosses_languages",
                closure_value_crosses_languages,
            ),
            ("fat_pointers_all_four_kinds", fat_pointers_all_four_kinds),
            ("references_and_refcounts", references_and_refcounts),
            ("constants_u128_bytes_float", constants_u128_bytes_float),
            (
                "seqmap_general_element_function",
                seqmap_general_element_function,
            ),
            ("atomics", atomics),
            ("exception_handling", exception_handling),
            ("coroutine_suspend", coroutine_suspend),
            ("global_addr_and_tls", global_addr_and_tls),
            ("scalar_bool_not_is_rejected", scalar_bool_not_is_rejected),
            (
                "tree_carrier_rc_typed_recursion",
                tree_carrier_rc_typed_recursion,
            ),
        ],
    );
}
