// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// Amendment S (`docs/SPEC_RATIFICATIONS.md` §22): `validate_template`, rule by
// rule (T1–T9). Each rule has a template that breaks only it, refused by
// name, beside the golden corpus every rule admits.

#[path = "../../trust-ir-conformance/tests/generate/templates.rs"]
#[allow(dead_code)]
mod templates;

use templates::{hole, param};
use trust_ir::template::{
    HoleDef, HoleKind, HostKey, Template, TemplateArg, TemplateError, TemplateParam, TypeContract,
};
use trust_ir::{
    ClosureTy, DropGlueEntry, FieldDef, FuncId, FuncTyG, FuncTyId, InstG, InstrNodeG, Linkage,
    RecordDef, RecordId, TemplateRef, Ty, TyG, ValueId,
};
use trust_ir_build::template::{TemplateViolation, validate_template};
use trust_ir_build::validate::ValidationError;

fn structural(template: &Template) -> Vec<TemplateError> {
    validate_template(template)
        .into_iter()
        .filter_map(|v| match v {
            TemplateViolation::Structure(e) => Some(e),
            TemplateViolation::LevelR(_) => None,
        })
        .collect()
}

fn level_r(template: &Template) -> Vec<ValidationError> {
    validate_template(template)
        .into_iter()
        .filter_map(|v| match v {
            TemplateViolation::LevelR(e) => Some(e),
            TemplateViolation::Structure(_) => None,
        })
        .collect()
}

fn body_insts(template: &mut Template) -> &mut Vec<InstrNodeG<TemplateRef>> {
    &mut template.module.functions[0].blocks[0].body
}

fn push_before_return(template: &mut Template, node: InstrNodeG<TemplateRef>) {
    let body = body_insts(template);
    let at = body.len() - 1;
    body.insert(at, node);
}

#[test]
fn the_golden_corpus_passes_every_rule() {
    for (name, template) in templates::corpus().expect("template fixture") {
        assert_eq!(validate_template(&template), vec![], "{name}");
    }
}

#[test]
fn thin_pointer_contract_uses_pointer_skolems_but_opaque_comparison_stays_refused() {
    let mut t = templates::thin_pointer_compare().unwrap();
    assert!(
        validate_template(&t).is_empty(),
        "{:?}",
        validate_template(&t)
    );
    t.header.holes[0].kind = HoleKind::Type {
        contract: TypeContract::Opaque,
    };
    assert!(
        structural(&t)
            .iter()
            .any(|error| matches!(error, TemplateError::OpaqueOperation { .. }))
    );
}

#[test]
fn thin_pointer_contract_does_not_admit_invalid_pointer_arithmetic() {
    let mut t = templates::thin_pointer_compare().unwrap();
    t.module.func_types[0].returns = vec![hole(0)];
    body_insts(&mut t)[0].inst = InstG::BinOp {
        op: trust_ir::BinOp::Add,
        ty: hole(0),
        lhs: ValueId::new(0),
        rhs: ValueId::new(1),
    };
    assert!(
        !level_r(&t).is_empty(),
        "the ordinary R validator must still reject pointer addition"
    );
}

// T9
#[test]
fn an_empty_or_multiline_identity_is_refused() {
    for identity in ["", "a\nb"] {
        let mut t = templates::ident_param().expect("template fixture");
        t.header.identity = identity.into();
        assert!(
            structural(&t).contains(&TemplateError::InvalidIdentity),
            "{identity:?}"
        );
    }
}

// T1
#[test]
fn a_param_out_of_scope_is_refused() {
    let mut t = templates::ident_param().expect("template fixture");
    t.module.functions[0].blocks[0].params[0].1 = param(3);
    assert!(
        structural(&t)
            .iter()
            .any(|e| matches!(e, TemplateError::ParamOutOfScope { param: 3, .. }))
    );
}

#[test]
fn a_host_param_in_a_body_position_is_refused() {
    let mut t = templates::ident_param().expect("template fixture");
    t.header.params = vec![TemplateParam::Host];
    assert!(
        structural(&t)
            .iter()
            .any(|e| matches!(e, TemplateError::ParamKindMismatch { param: 0, .. }))
    );
}

#[test]
fn a_hole_out_of_scope_is_refused() {
    let mut t = templates::ident_param().expect("template fixture");
    t.module.functions[0].blocks[0].params[0].1 = hole(0);
    assert!(
        structural(&t)
            .iter()
            .any(|e| matches!(e, TemplateError::HoleOutOfScope { hole: 0, .. }))
    );
}

#[test]
fn a_const_hole_in_a_type_position_is_refused() {
    let mut t = templates::const_hole_size_of().expect("template fixture");
    t.module.func_types[0].returns = vec![hole(0)];
    assert!(
        structural(&t)
            .iter()
            .any(|e| matches!(e, TemplateError::HoleKindMismatch { hole: 0, .. }))
    );
}

// T2
#[test]
fn duplicate_holes_are_refused() {
    let mut t = templates::struct_contract_field_read().expect("template fixture");
    let copy = t.header.holes[1].clone();
    t.header.holes.push(copy);
    assert!(
        structural(&t)
            .iter()
            .any(|e| matches!(e, TemplateError::DuplicateHole { hole: 2, first: 1 }))
    );
}

#[test]
fn a_ground_hole_is_refused() {
    let mut t = templates::const_hole_size_of().expect("template fixture");
    t.header.holes[0].args = vec![TemplateArg::Type(TyG::U64)];
    assert!(structural(&t).contains(&TemplateError::GroundHole { hole: 0 }));
}

#[test]
fn an_invalid_host_key_namespace_is_refused() {
    let mut t = templates::const_hole_size_of().expect("template fixture");
    t.header.holes[0].key = HostKey::new("ru st", vec![]);
    assert!(structural(&t).contains(&TemplateError::InvalidHostKey { hole: 0 }));
}

#[test]
fn a_hole_may_not_name_a_later_hole_in_its_arguments() {
    let mut t = templates::struct_contract_field_read().expect("template fixture");
    // ?1's arguments name ?1's successor ... make ?0's arguments name ?1.
    t.header.holes[0].args = vec![TemplateArg::Type(hole(1))];
    assert!(structural(&t).contains(&TemplateError::HoleCycle { hole: 0, names: 1 }));
    // A contract may name a later hole (review R6): the corpus template does.
    assert_eq!(
        validate_template(&templates::struct_contract_field_read().expect("template fixture")),
        vec![]
    );
}

#[test]
fn a_callee_hole_and_its_row_must_agree() {
    let mut t = templates::callee_hole_trait_call().expect("template fixture");
    t.module.functions[1].name = "not_reserved".into();
    assert!(
        structural(&t)
            .iter()
            .any(|e| matches!(e, TemplateError::HoleRowMismatch { .. }))
    );
}

#[test]
fn an_unused_hole_is_refused() {
    let mut t = templates::ident_param().expect("template fixture");
    t.header.holes.push(HoleDef {
        kind: HoleKind::Type {
            contract: TypeContract::Opaque,
        },
        key: HostKey::new("rust", b"unused".to_vec()),
        args: vec![TemplateArg::Type(param(0))],
    });
    assert!(structural(&t).contains(&TemplateError::UnusedHole { hole: 0 }));
}

#[test]
fn a_parameter_dependent_declaration_must_be_a_hole_row() {
    let mut t = templates::callee_hole_trait_call().expect("template fixture");
    t.header.holes.clear();
    t.module.functions[1].name = "clone_of_t".into();
    assert!(
        structural(&t)
            .iter()
            .any(|e| matches!(e, TemplateError::GenericRowNotAHole { .. }))
    );
}

// T3
#[test]
fn an_alignment_literal_at_a_param_type_is_refused_but_one_is_admitted() {
    let mut t = templates::drop_at_param().expect("template fixture");
    if let InstG::Alloca { align, .. } = &mut body_insts(&mut t)[0].inst {
        *align = Some(8);
    }
    assert!(
        structural(&t)
            .iter()
            .any(|e| matches!(e, TemplateError::ParamDependentLiteral { .. }))
    );
    if let InstG::Alloca { align, .. } = &mut body_insts(&mut t)[0].inst {
        *align = Some(1);
    }
    assert_eq!(structural(&t), vec![]);
}

// T4
#[test]
fn arithmetic_on_an_opaque_param_is_refused() {
    let mut t = templates::ident_param().expect("template fixture");
    push_before_return(
        &mut t,
        InstrNodeG::new(InstG::BinOp {
            op: trust_ir::BinOp::Add,
            ty: param(0),
            lhs: ValueId::new(0),
            rhs: ValueId::new(0),
        })
        .with_result(ValueId::new(1)),
    );
    assert!(
        structural(&t)
            .iter()
            .any(|e| matches!(e, TemplateError::OpaqueOperation { .. }))
    );
}

#[test]
fn building_an_opaque_value_from_nothing_is_refused() {
    let mut t = templates::ident_param().expect("template fixture");
    push_before_return(
        &mut t,
        InstrNodeG::new(InstG::MakeAggregate {
            ty: param(0),
            variant: None,
            fields: vec![],
        })
        .with_result(ValueId::new(1)),
    );
    assert!(
        structural(&t)
            .iter()
            .any(|e| matches!(e, TemplateError::OpaqueOperation { .. }))
    );
}

#[test]
fn a_field_read_on_a_struct_contract_hole_typechecks_and_out_of_range_is_refused() {
    assert_eq!(
        validate_template(&templates::struct_contract_field_read().expect("template fixture")),
        vec![]
    );
    let mut t = templates::struct_contract_field_read().expect("template fixture");
    if let InstG::ExtractField { field, .. } = &mut body_insts(&mut t)[1].inst {
        *field = 5;
    }
    assert!(
        !level_r(&t).is_empty(),
        "lane 5 of a two-field contract is out of range"
    );
}

// T5
#[test]
fn a_parameter_in_a_ground_table_is_refused() {
    let mut t = templates::ident_param().expect("template fixture");
    let row = t
        .module
        .add_type(param(0))
        .expect("Module::add_type: test fixture");
    t.module.structs.push(trust_ir::StructDefG {
        id: trust_ir::StructId::new(0),
        name: "Holds".into(),
        fields: vec![trust_ir::FieldDefG {
            name: "x".into(),
            ty: TyG::Array(row, 2),
            offset: None,
        }],
        size: None,
        align: None,
        repr: trust_ir::StructRepr::Rust,
        origin: None,
    });
    assert!(structural(&t).contains(&TemplateError::ExtInGroundTable {
        table: "struct",
        index: 0
    }));
}

// T6
#[test]
fn a_level_r_rule_the_skolem_instance_breaks_is_refused() {
    // A drop at `&T` is a drop of a reference at EVERY instance: non-canonical
    // (§20 rule 5a), and the skolem instance shows it.
    let mut t = templates::drop_at_param().expect("template fixture");
    if let InstG::DropInvoke { ty, .. } = &mut body_insts(&mut t)[2].inst {
        *ty = TyG::Ref(Box::new(param(0)));
    }
    assert!(
        level_r(&t)
            .iter()
            .any(|e| matches!(e, ValidationError::NonCanonicalDrop { .. })),
        "{:?}",
        validate_template(&t)
    );
}

#[test]
fn a_type_mismatch_between_parameters_is_refused() {
    // `fn f<T, U>(x: T) -> U { x }`: equal only when T and U are, so the
    // skolem instance (distinct skolems) refuses it.
    let mut t = templates::ident_param().expect("template fixture");
    t.header.params.push(TemplateParam::Type);
    t.module.func_types[0].returns = vec![param(1)];
    assert!(!level_r(&t).is_empty());
}

// T7
#[test]
fn a_template_with_two_bodies_is_refused() {
    let mut t = templates::ident_param().expect("template fixture");
    let mut second = t.module.functions[0].clone();
    second.id = FuncId::new(7);
    second.name = "second".into();
    t.module.functions.push(second);
    assert!(
        structural(&t)
            .iter()
            .any(|e| matches!(e, TemplateError::TemplateBodyShape { .. }))
    );
}

#[test]
fn a_body_row_stating_a_host_fact_is_refused() {
    let mut t = templates::ident_param().expect("template fixture");
    t.module.functions[0].linkage = Linkage::Internal;
    assert!(
        structural(&t).iter().any(
            |e| matches!(e, TemplateError::TemplateBodyShape { why } if why.contains("linkage"))
        )
    );
}

#[test]
fn a_template_carrying_proof_surface_is_refused() {
    let mut t = templates::ident_param().expect("template fixture");
    t.module.global_asm.push("nop".into());
    assert!(
        structural(&t)
            .iter()
            .any(|e| matches!(e, TemplateError::TemplateUnsupported { .. }))
    );
}

// T8
#[test]
fn a_coroutine_suspend_is_refused() {
    let mut t = templates::ident_param().expect("template fixture");
    let body = body_insts(&mut t);
    body.pop();
    body.push(InstrNodeG::new(InstG::CoroSuspend {
        frame: ValueId::new(0),
        state_slot: 0,
        next_state: 1,
        value: ValueId::new(0),
    }));
    assert!(structural(&t).iter().any(
        |e| matches!(e, TemplateError::TemplateUnsupported { what } if what.contains("coroutine"))
    ));
}

#[test]
fn a_vector_over_a_parameter_is_refused() {
    let mut t = templates::ident_param().expect("template fixture");
    t.module
        .add_func_type(FuncTyG {
            abi: None,
            params: vec![TyG::Vector(Box::new(param(0)), 4)],
            returns: vec![],
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    assert!(structural(&t).iter().any(
        |e| matches!(e, TemplateError::TemplateUnsupported { what } if what.contains("vector"))
    ));
}

/// Every type former of SemR's type fragment (`lean/semr/TY_FRAGMENT.tsv`;
/// today `Tensor`) is refused wherever a template carries it, even over a
/// ground element: it has no `TemplateTy` constructor (`lean_schema_parity`'s
/// `template_ty_axis`), so a template that spelled one would instantiate to
/// a type the level-S model cannot state. Each occurrence site is tried alone.
#[test]
fn template_refuses_every_semr_fragment_type() {
    let ledger = std::fs::read_to_string(
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../lean/semr/TY_FRAGMENT.tsv"),
    )
    .expect("lean/semr/TY_FRAGMENT.tsv");
    let rows: Vec<&str> = ledger
        .lines()
        .filter(|l| !l.trim().is_empty() && !l.starts_with('#'))
        .map(|l| l.split('\t').next().expect("a variant column"))
        .collect();
    assert_eq!(
        rows,
        ["Tensor"],
        "this test spells a witness per fragment type"
    );
    let tensor = || TyG::Tensor(Box::new(TyG::I32), 2);
    let refused = |t: &Template| {
        structural(t).iter().any(|e| {
            matches!(e, TemplateError::TemplateUnsupported { what } if what.contains("a tensor"))
        })
    };
    // Control: the fixture alone is admitted.
    let base = templates::ident_param().expect("template fixture");
    assert!(!refused(&base), "the fixture carries no tensor");

    let mut at_signature = base.clone();
    at_signature
        .module
        .add_func_type(FuncTyG {
            abi: None,
            params: vec![tensor()],
            returns: vec![],
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    assert!(refused(&at_signature), "a tensor in a signature");

    let mut in_a_lane = base.clone();
    in_a_lane
        .module
        .add_func_type(FuncTyG {
            abi: None,
            params: vec![TyG::Tuple(vec![TyG::Bool, tensor()])],
            returns: vec![],
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    assert!(refused(&in_a_lane), "a tensor inside a tuple lane");

    let mut at_a_block_param = base.clone();
    at_a_block_param.module.functions[0].blocks[0]
        .params
        .push((ValueId::new(900), tensor()));
    assert!(refused(&at_a_block_param), "a tensor block parameter");

    let mut inline = base.clone();
    push_before_return(
        &mut inline,
        InstrNodeG::new(InstG::Undef { ty: tensor() }).with_result(ValueId::new(901)),
    );
    assert!(refused(&inline), "a tensor instruction type");

    let mut at_a_global = templates::const_param_value().expect("template fixture");
    assert!(
        !refused(&at_a_global),
        "the global fixture carries no tensor"
    );
    at_a_global.module.globals[0].ty = tensor();
    assert!(refused(&at_a_global), "a tensor global");

    let ground = || Ty::Tensor(Box::new(Ty::I32), 2);
    let mut in_a_record = base.clone();
    in_a_record.module.records.push(RecordDef {
        id: RecordId::new(0),
        name: "r".into(),
        fields: vec![FieldDef {
            name: "t".into(),
            ty: ground(),
            offset: None,
        }],
    });
    assert!(refused(&in_a_record), "a tensor record field");

    let mut in_a_capture = base.clone();
    in_a_capture.module.closure_types.push(ClosureTy {
        func: FuncTyId::new(0),
        captures: vec![ground()],
    });
    assert!(refused(&in_a_capture), "a tensor closure capture");

    let mut in_drop_glue = base.clone();
    in_drop_glue.module.drop_glue.push(DropGlueEntry {
        glue: FuncId::new(0),
        ty: ground(),
    });
    assert!(refused(&in_drop_glue), "a tensor drop-glue row");

    let mut contraction = base.clone();
    push_before_return(
        &mut contraction,
        InstrNodeG::new(InstG::TensorContract {
            ty: tensor(),
            lhs: ValueId::new(0),
            rhs: ValueId::new(0),
            batch: vec![],
            contract: vec![(1, 0)],
        })
        .with_result(ValueId::new(902)),
    );
    assert!(
        structural(&contraction).iter().any(|e| matches!(
            e,
            TemplateError::TemplateUnsupported { what } if what.contains("tensor contraction")
        )),
        "a tensor contraction"
    );

    // PKG-U13c: a map, a reduction and a view are refused by name likewise,
    // and (PKG-U13d) a gather and a scatter.
    let region: [(&str, InstG<TemplateRef>); 5] = [
        (
            "tensor map",
            InstG::TensorMap {
                ty: tensor(),
                args: vec![ValueId::new(0)],
                body: vec![trust_ir::TensorMapNode::UnOp {
                    op: trust_ir::inst::UnOp::Neg,
                    ty: TyG::I32,
                    operand: 0,
                }],
            },
        ),
        (
            "tensor reduction",
            InstG::TensorReduce {
                ty: tensor(),
                src: ValueId::new(0),
                op: trust_ir::TensorReduceOp::Add,
                axes: vec![],
                order: trust_ir::TensorReduceOrder::RowMajor,
            },
        ),
        (
            "tensor view",
            InstG::TensorView {
                ty: tensor(),
                src: ValueId::new(0),
                params: vec![],
                exprs: vec![],
                shape: vec![],
                index: vec![],
                fill: None,
            },
        ),
        (
            "tensor gather",
            InstG::TensorGather {
                ty: tensor(),
                data: ValueId::new(0),
                coords: vec![ValueId::new(0)],
            },
        ),
        (
            "tensor scatter",
            InstG::TensorScatter {
                ty: tensor(),
                init: ValueId::new(0),
                src: ValueId::new(0),
                coords: vec![ValueId::new(0)],
            },
        ),
    ];
    for (what, inst) in region {
        let mut t = base.clone();
        push_before_return(&mut t, InstrNodeG::new(inst).with_result(ValueId::new(902)));
        assert!(
            structural(&t).iter().any(|e| matches!(
                e,
                TemplateError::TemplateUnsupported { what: w } if w.contains(what)
            )),
            "a {what}"
        );
    }
}

#[test]
fn a_non_scalar_const_hole_is_refused() {
    let mut t = templates::const_hole_size_of().expect("template fixture");
    t.header.holes[0].kind = HoleKind::Const { ty: Ty::Ptr };
    t.module.func_types[0].returns = vec![TyG::Ptr];
    if let InstG::Const { ty, .. } = &mut body_insts(&mut t)[0].inst {
        *ty = TyG::Ptr;
    }
    assert!(structural(&t).iter().any(
        |e| matches!(e, TemplateError::TemplateUnsupported { what } if what.contains("non-scalar"))
    ));
}

#[test]
fn the_writer_refuses_what_the_structural_rules_refuse() {
    let mut t = templates::const_hole_size_of().expect("template fixture");
    t.header.holes[0].args = vec![TemplateArg::Type(TyG::U64)];
    // The identity is the blob's digest, so a template the writer refuses has
    // none: the same refusal, through the always-on path.
    assert_eq!(t.digest(), Err(TemplateError::GroundHole { hole: 0 }));
    #[cfg(feature = "binary")]
    assert_eq!(
        trust_ir::binary::serialize_template(&t),
        Err(TemplateError::GroundHole { hole: 0 })
    );
}
