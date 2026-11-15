// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// The level-S must-refuse rows (amendment S, §8): every `TemplateError`,
// `TemplateViolation` and `InstantiateError` variant exhibited by an
// artifact a template consumer must refuse, beside the control it must
// accept. Rows live in `tests/fixtures/refuse_templates/` (their own
// manifest: a module consumer meets none of them), named by feature.
//
// Carriers:
//   * `template_bytes` — `<row>.tmbs`, a TRUST_IS blob the template reader
//     refuses;
//   * `template` — `<row>.json`, a decoded template `validate_template`
//     refuses (a structurally invalid template has no binary encoding: the
//     writer refuses it, so its wire form is the serde one);
//   * `instance` — `<row>.json` and `<row>.host.json`, a template and a
//     SCRIPTED host (answers as data) `instantiate` refuses;
//   * `control` — a template and host `instantiate` must ACCEPT.

use trust_ir::template::{
    HoleDef, HoleKind, HostKey, ScriptedAnswer, ScriptedHost, Template, TemplateArg, TemplateParam,
    TypeContract,
};
use trust_ir::{
    BinOp, BlockG, Constant, FuncId, FunctionG, InstG, InstrNodeG, Linkage, StructId, TemplateRef,
    Ty, TyG, ValueId,
};

use crate::fixtures::{FixtureError, OrFixture};
use crate::template_fixtures::{self as t, hole, param};

/// One template-corpus artifact.
pub enum Artifact {
    /// A TRUST_IS blob.
    Bytes(Vec<u8>),
    /// A template, with a scripted host for `instance` / `control` rows.
    Template(Box<Template>, Option<Box<ScriptedHost>>),
}

fn template(t: Template) -> Artifact {
    Artifact::Template(Box::new(t), None)
}

fn instance(t: Template, host: ScriptedHost) -> Artifact {
    Artifact::Template(Box::new(t), Some(Box::new(host)))
}

fn host_of(name: &str) -> Result<(Template, ScriptedHost), FixtureError> {
    let case = t::instances()
        .or_fixture("the template instance corpus")?
        .into_iter()
        .find(|case| case.name == name)
        .or_fixture("the named corpus instance")?;
    Ok((case.template, case.host))
}

/// Function `f` of a template's module.
fn function_mut(
    template: &mut Template,
    f: usize,
) -> Result<&mut FunctionG<TemplateRef>, FixtureError> {
    template
        .module
        .functions
        .get_mut(f)
        .or_fixture("a template function the row edits")
}

/// The entry block of function `f` of a template's module.
fn entry_mut(template: &mut Template, f: usize) -> Result<&mut BlockG<TemplateRef>, FixtureError> {
    function_mut(template, f)?
        .blocks
        .get_mut(0)
        .or_fixture("a template function's entry block")
}

/// Instruction `i` of function `f`'s entry block.
fn entry_inst_mut(
    template: &mut Template,
    f: usize,
    i: usize,
) -> Result<&mut InstG<TemplateRef>, FixtureError> {
    entry_mut(template, f)?
        .body
        .get_mut(i)
        .map(|node| &mut node.inst)
        .or_fixture("an entry-block instruction the row edits")
}

/// The type of the entry block's first parameter of function 0.
fn first_param_ty_mut(template: &mut Template) -> Result<&mut TyG<TemplateRef>, FixtureError> {
    entry_mut(template, 0)?
        .params
        .get_mut(0)
        .map(|(_, ty)| ty)
        .or_fixture("the entry block's first parameter")
}

/// Hole `h` of a template's header.
fn hole_mut(template: &mut Template, h: usize) -> Result<&mut HoleDef, FixtureError> {
    template
        .header
        .holes
        .get_mut(h)
        .or_fixture("a template hole the row edits")
}

/// Insert `node` before the entry block's last node, its return. An empty
/// block has no return: a broken golden, refused as such.
fn push_before_return(
    template: &mut Template,
    node: InstrNodeG<TemplateRef>,
) -> Result<(), FixtureError> {
    let body = &mut entry_mut(template, 0)?.body;
    let ret = body
        .pop()
        .or_fixture("the template's entry block ends in its return")?;
    body.push(node);
    body.push(ret);
    Ok(())
}

/// Every row's artifact, by row id, or the refusal of a golden the rows edit
/// that no longer has the shape they edit. The test decides (r11 item 7: this
/// file is compiled into the library the verified survey examines).
pub fn artifacts() -> Result<Vec<(&'static str, Artifact)>, FixtureError> {
    let ident_blob =
        trust_ir::binary::serialize_template(&t::ident_param().or_fixture("the template golden")?)
            .or_fixture("the golden encodes")?;
    let mut rows = vec![
        // --- the decoder ---
        (
            "template_reader_refuses_a_module_blob",
            Artifact::Bytes(
                trust_ir::binary::serialize_module(&trust_ir::Module::new("m"))
                    .or_fixture("serialize_module")?,
            ),
        ),
        ("template_below_its_version", {
            let mut bytes = ident_blob.clone();
            let below = trust_ir::binary::TEMPLATE_FORMAT_VERSION - 1;
            bytes
                .get_mut(8..12)
                .or_fixture("the template header's version field")?
                .copy_from_slice(&below.to_le_bytes());
            Artifact::Bytes(bytes)
        }),
        ("template_trailing_bytes", {
            let mut bytes = ident_blob.clone();
            bytes.push(0);
            Artifact::Bytes(bytes)
        }),
    ];

    // --- the structural rules (T1-T5, T7-T9) ---
    rows.push(("template_identity_empty", {
        let mut x = t::ident_param().or_fixture("the template golden")?;
        x.header.identity.clear();
        template(x)
    }));
    rows.push(("template_param_out_of_scope", {
        let mut x = t::ident_param().or_fixture("the template golden")?;
        *first_param_ty_mut(&mut x)? = param(3);
        template(x)
    }));
    rows.push(("template_host_param_in_a_body_position", {
        let mut x = t::ident_param().or_fixture("the template golden")?;
        x.header.params = vec![TemplateParam::Host];
        template(x)
    }));
    rows.push(("template_hole_out_of_scope", {
        let mut x = t::ident_param().or_fixture("the template golden")?;
        *first_param_ty_mut(&mut x)? = hole(0);
        template(x)
    }));
    rows.push(("template_const_hole_in_a_type_position", {
        let mut x = t::const_hole_size_of().or_fixture("the template golden")?;
        x.module
            .func_types
            .get_mut(0)
            .or_fixture("the template's first function type")?
            .returns = vec![hole(0)];
        template(x)
    }));
    rows.push(("template_duplicate_hole", {
        let mut x = t::struct_contract_field_read().or_fixture("the template golden")?;
        let copy = hole_mut(&mut x, 1)?.clone();
        x.header.holes.push(copy);
        template(x)
    }));
    rows.push(("template_ground_hole", {
        let mut x = t::const_hole_size_of().or_fixture("the template golden")?;
        hole_mut(&mut x, 0)?.args = vec![TemplateArg::Type(TyG::U64)];
        template(x)
    }));
    rows.push(("template_host_key_namespace_invalid", {
        let mut x = t::const_hole_size_of().or_fixture("the template golden")?;
        hole_mut(&mut x, 0)?.key = HostKey::new("ru st", vec![]);
        template(x)
    }));
    rows.push(("template_hole_names_a_later_hole", {
        let mut x = t::struct_contract_field_read().or_fixture("the template golden")?;
        hole_mut(&mut x, 0)?.args = vec![TemplateArg::Type(hole(1))];
        template(x)
    }));
    rows.push(("template_hole_row_mismatch", {
        let mut x = t::callee_hole_trait_call().or_fixture("the template golden")?;
        function_mut(&mut x, 1)?.name = "not_reserved".into();
        template(x)
    }));
    rows.push(("template_unused_hole", {
        let mut x = t::ident_param().or_fixture("the template golden")?;
        x.header.holes.push(HoleDef {
            kind: HoleKind::Type {
                contract: TypeContract::Opaque,
            },
            key: HostKey::new("rust", b"unused".to_vec()),
            args: vec![TemplateArg::Type(param(0))],
        });
        template(x)
    }));
    rows.push(("template_generic_declaration_not_a_hole", {
        let mut x = t::callee_hole_trait_call().or_fixture("the template golden")?;
        x.header.holes.clear();
        function_mut(&mut x, 1)?.name = "clone_of_t".into();
        template(x)
    }));
    rows.push(("template_alignment_literal_at_a_parameter", {
        let mut x = t::drop_at_param().or_fixture("the template golden")?;
        if let InstG::Alloca { align, .. } = entry_inst_mut(&mut x, 0, 0)? {
            *align = Some(8);
        }
        template(x)
    }));
    rows.push(("template_arithmetic_on_an_opaque_parameter", {
        let mut x = t::ident_param().or_fixture("the template golden")?;
        push_before_return(
            &mut x,
            InstrNodeG::new(InstG::BinOp {
                op: BinOp::Add,
                ty: param(0),
                lhs: ValueId::new(0),
                rhs: ValueId::new(0),
            })
            .with_result(ValueId::new(1)),
        )?;
        template(x)
    }));
    rows.push(("template_parameter_in_a_ground_table", {
        let mut x = t::ident_param().or_fixture("the template golden")?;
        let row = x.module.add_type(param(0)).or_fixture("Module::add_type")?;
        x.module.structs.push(trust_ir::StructDefG {
            id: StructId::new(0),
            name: "Holds".into(),
            fields: vec![trust_ir::FieldDefG {
                name: "x".into(),
                ty: trust_ir::TyG::Array(row, 2),
                offset: None,
            }],
            size: None,
            align: None,
            repr: trust_ir::StructRepr::Rust,
            origin: None,
        });
        template(x)
    }));
    rows.push(("template_body_states_a_host_fact", {
        let mut x = t::ident_param().or_fixture("the template golden")?;
        function_mut(&mut x, 0)?.linkage = Linkage::Internal;
        template(x)
    }));
    rows.push(("template_coroutine_suspend", {
        let mut x = t::ident_param().or_fixture("the template golden")?;
        let body = &mut entry_mut(&mut x, 0)?.body;
        body.pop();
        body.push(InstrNodeG::new(InstG::CoroSuspend {
            frame: ValueId::new(0),
            state_slot: 0,
            next_state: 1,
            value: ValueId::new(0),
        }));
        template(x)
    }));

    // --- T6: a level-R rule the skolem instance breaks ---
    rows.push(("template_skolem_instance_breaks_level_r", {
        let mut x = t::drop_at_param().or_fixture("the template golden")?;
        if let InstG::DropInvoke { ty, .. } = entry_inst_mut(&mut x, 0, 2)? {
            *ty = TyG::Ref(Box::new(param(0)));
        }
        template(x)
    }));

    // --- instantiation ---
    rows.push(("instance_of_an_invalid_template", {
        let (mut x, host) = host_of("ident_param<u64>")?;
        x.header.identity.clear();
        instance(x, host)
    }));
    rows.push(("instance_arity_mismatch", {
        let (x, mut host) = host_of("ident_param<u64>")?;
        host.arguments.clear();
        instance(x, host)
    }));
    rows.push(("instance_argument_kind", {
        let (x, mut host) = host_of("ident_param<u64>")?;
        host.arguments = vec![trust_ir::template::InstArg::Const(Constant::Int(1))];
        instance(x, host)
    }));
    rows.push(("instance_host_refused", {
        let (x, mut host) = host_of("const_hole_size_of<u64>")?;
        host.holes = vec![ScriptedAnswer::Refuse("T is unsized".into())];
        instance(x, host)
    }));
    rows.push(("instance_host_edits_the_instance", {
        let (x, mut host) = host_of("ident_param<u64>")?;
        host.tamper = true;
        instance(x, host)
    }));
    rows.push(("instance_answer_violates_struct_contract", {
        let (x, mut host) = host_of("struct_contract_field_read<u32>")?;
        host.structs
            .get_mut(1)
            .or_fixture("the host's second struct")?
            .fields
            .swap(0, 1);
        instance(x, host)
    }));
    rows.push(("instance_two_answers_one_symbol_different_signatures", {
        let (mut x, host) = host_of("callee_hole_trait_call<u64>")?;
        let other = x
            .module
            .add_func_type(trust_ir::FuncTyG {
                abi: None,
                params: vec![TyG::U8],
                returns: vec![TyG::U64],
                is_vararg: false,
            })
            .or_fixture("Module::add_func_type")?;
        let mut ground = trust_ir::FunctionG::new(
            FuncId::new(2),
            "clone_u64",
            other,
            trust_ir::BlockId::new(0),
        );
        ground.calling_conv = trust_ir::CallingConv::Rust;
        x.module.functions.push(ground);
        instance(x, host)
    }));
    rows.push(("instance_header_reserved_symbol", {
        let (x, mut host) = host_of("ident_param<u64>")?;
        if let Some(header) = &mut host.header {
            header.symbol = "!template_body".into();
        }
        instance(x, host)
    }));
    rows.push(("instance_output_fails_level_r_validation", {
        let (x, mut host) = host_of("ident_param<u64>")?;
        host.structs = vec![trust_ir::StructDef {
            id: StructId::new(t::HOST_STRUCT_BASE),
            name: "Unsized".into(),
            fields: vec![trust_ir::FieldDef {
                name: "x".into(),
                ty: Ty::Struct(StructId::new(t::HOST_STRUCT_BASE)),
                offset: None,
            }],
            size: None,
            align: None,
            repr: trust_ir::StructRepr::Rust,
            origin: None,
        }];
        host.arguments = vec![trust_ir::template::InstArg::Type(Ty::Struct(
            StructId::new(t::HOST_STRUCT_BASE),
        ))];
        instance(x, host)
    }));
    rows.push(("template_control_instantiates", {
        let (x, host) = host_of("drop_at_param<u32>")?;
        instance(x, host)
    }));
    Ok(rows)
}
