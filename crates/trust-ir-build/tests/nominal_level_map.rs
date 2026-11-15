// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Shared nominal level mapping transports data; it grants no layout contract
//! or permission for a generic nominal row to enter a ground instance.

use trust_ir::template::{
    TEMPLATE_BODY_NAME, Template, TemplateError, TemplateHeader, TemplateParam,
};
use trust_ir::*;
use trust_ir_build::template::{TemplateViolation, skolem_instance, validate_template};

fn ground_nominals() -> Module {
    let mut module = Module::new("ground-nominal-level-map");
    module.structs.push(StructDef {
        id: StructId::new(0),
        name: "Packet".into(),
        fields: vec![FieldDef {
            name: "value".into(),
            ty: Ty::U8,
            offset: Some(0),
        }],
        size: Some(1),
        align: Some(1),
        repr: StructRepr::C,
        origin: None,
    });
    module.enums.push(EnumDef {
        id: EnumId::new(0),
        name: "Choice".into(),
        variants: vec![EnumVariant {
            name: "Some".into(),
            fields: vec![Ty::Struct(StructId::new(0))],
            field_names: vec!["value".into()],
        }],
        discriminants: vec![Some(7)],
        repr: Some(EnumTagRepr::U8),
        layout: None,
        origin: None,
    });
    let signature = module
        .add_func_type(FuncTy {
            params: vec![Ty::U8],
            returns: vec![Ty::U8],
            is_vararg: false,
            abi: None,
        })
        .unwrap();
    let mut function = Function::new(
        FuncId::new(0),
        TEMPLATE_BODY_NAME,
        signature,
        BlockId::new(0),
    );
    let mut block = Block::new(BlockId::new(0)).with_param(ValueId::new(0), Ty::U8);
    block.body.push(InstrNode::new(Inst::Return {
        values: vec![ValueId::new(0)],
    }));
    function.blocks.push(block);
    module.functions.push(function);
    module
}

fn template_of(source: &Module) -> Template {
    let module = source
        .try_map_level(
            &mut |ty| Ok::<TyG<TemplateRef>, core::convert::Infallible>(ty.embed()),
            &mut |constant, _| Ok(constant.embed()),
        )
        .unwrap();
    Template {
        header: TemplateHeader {
            identity: "ground-nominal-level-map".into(),
            params: vec![],
            holes: vec![],
        },
        module,
    }
}

#[test]
fn ground_nominal_rows_survive_the_shared_map_and_s_instantiation() {
    let source = ground_nominals();
    assert!(trust_ir_build::validate::validate_module(&source).is_empty());
    let template = template_of(&source);
    assert!(validate_template(&template).is_empty());
    let instance = skolem_instance(&template).unwrap();
    assert_eq!(instance.structs, source.structs);
    assert_eq!(instance.enums, source.enums);
    assert!(trust_ir_build::validate::validate_module(&instance).is_empty());
    let restored = template
        .module
        .try_map_level(
            &mut |ty| ty.try_map_ext(&mut |_| Err::<Ty, _>("extension in ground input")),
            &mut |constant, _| constant.try_map_ext(&mut |_| Err("extension in ground input")),
        )
        .unwrap();
    assert_eq!(restored, source);
    let text = template.to_string();
    assert_eq!(trust_ir::parser::parse_template(&text).unwrap(), template);
    assert_eq!(
        trust_ir::parser::parse_module(&source.to_string()).unwrap(),
        source
    );
}

#[test]
fn generic_nominal_fields_have_no_instantiation_or_wire_admission() {
    for is_enum in [false, true] {
        for through_row in [false, true] {
            let mut template = template_of(&ground_nominals());
            template.header.params.push(TemplateParam::Type);
            let generic = TyG::Ext(TemplateRef::Param(ParamId::new(0)));
            let ty = if through_row {
                template.module.types.push(generic);
                TyG::Array(TyId::new(0), 1)
            } else {
                generic
            };
            let table = if is_enum {
                template.module.enums[0].variants[0].fields[0] = ty;
                "enum"
            } else {
                template.module.structs[0].fields[0].ty = ty;
                "struct"
            };
            assert!(validate_template(&template).iter().any(|violation| matches!(violation,
                TemplateViolation::Structure(TemplateError::ExtInGroundTable { table: found, index: 0 }) if *found == table)));
            // The public skolem helper is diagnostic and deliberately runs
            // without structural validation. The real instantiator must stop
            // at T5 before asking even an empty scripted host for arguments.
            assert!(matches!(
                trust_ir_build::template::instantiate(
                    &template,
                    &mut trust_ir_build::template::ScriptedHost::default()
                ),
                Err(trust_ir_build::template::InstantiateError::TemplateInvalid(
                    _
                ))
            ));
            assert!(trust_ir::binary::serialize_template(&template).is_err());
            assert!(trust_ir::parser::parse_template(&template.to_string()).is_err());
        }
    }
}
