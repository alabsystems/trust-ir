// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// ══════════════════════════════════════════════════════════════════════════
// Roadmap WS2.4 (finding F-045) — by-value aggregate cycles, validator half.
// ══════════════════════════════════════════════════════════════════════════
//
// Row `exec-log-and-tcb/by-value-struct-cycle-robustness` of the 2026-09-17
// two-language proof program (a phase-1 source read; no partb GAP ratchet
// existed for it, so this file IS the row).
//
// Before this rule no validator pass looked at by-value containment, so
// `struct Node { next: Node }` validated, and the reference interpreter's
// `byte_size -> struct_layout -> aggregate_layout -> byte_size(field)` chain
// recursed on it until the host stack overflowed. `validate_module` now
// refuses every by-value containment cycle with
// `ValidationError::InlineAggregateCycle`, once per strongly connected
// component. The interpreter half (a fail-closed `TypeError` on an
// UNVALIDATED module, proved on a small stack) lives with the conformance
// interpreter guards in `trust-ir-conformance/tests/interpret_differential.rs`.
//
//   positive       `struct Node { next: *mut Node, v: u64 }` validates and runs;
//   negative twin  `struct Node { next: Node }` -> InlineAggregateCycle;
//   mutation       the cycle through a tuple + `TyId` row, through an enum
//                  variant, through `Refine`, through a declared-size struct,
//                  and a two-struct cycle are each caught (the last ONCE);
//                  `Rc<Node>` / `&Node` / `Sequence(Node)` are not flagged.

use trust_ir::Module;
use trust_ir::interpret::Interpreter;
use trust_ir::pred::Pred;
use trust_ir::ty::{EnumDef, EnumVariant, FieldDef, StructDef, Ty};
use trust_ir::value::{EnumId, FuncId, PredId, StructId, TyId};
use trust_ir_build::{ModuleBuilder, ValidationError, validate_module};

const NODE: StructId = StructId::new(0);

fn field(name: &str, ty: Ty) -> FieldDef {
    FieldDef {
        name: name.to_string(),
        ty,
        offset: None,
    }
}

fn struct_def(id: StructId, name: &str, fields: Vec<FieldDef>) -> StructDef {
    StructDef {
        id,
        name: name.to_string(),
        fields,
        size: None,
        align: None,
        repr: Default::default(),
        origin: None,
    }
}

/// `program() -> u64`: allocate a `Node`, write its `next` (null) and `v`
/// (42) lanes through byte offsets, load the WHOLE struct back (so both
/// `byte_size(Node)` and the struct decoder run), and return field 1.
fn node_program(node: StructDef, v_offset: u64) -> Module {
    let mut mb = ModuleBuilder::new("by_value_cycle");
    let sid = mb.add_struct(node);
    assert_eq!(sid, NODE);
    let node_ty = Ty::Struct(NODE);
    let sig = mb.add_func_type(vec![], vec![Ty::U64]);
    let mut fb = mb.function("program", sig);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let slot = fb.alloca(node_ty.clone());
    let null = fb.null_ptr();
    fb.store(Ty::Ptr, slot, null);
    let v_slot = fb.gep_byte_offset(slot, v_offset);
    let v = fb.uconst(Ty::U64, 42);
    fb.store(Ty::U64, v_slot, v);
    let loaded = fb.load(node_ty, slot);
    let out = fb.extract_field(Ty::U64, loaded, 1);
    fb.ret(vec![out]);
    fb.build();
    mb.build().expect("ModuleBuilder::build: test fixture")
}

fn cycles(module: &Module) -> Vec<String> {
    validate_module(module)
        .into_iter()
        .filter_map(|error| match error {
            ValidationError::InlineAggregateCycle { ty } => Some(ty),
            _ => None,
        })
        .collect()
}

/// A module holding only struct `Node` (id 0) with the given fields.
fn node_only(fields: Vec<FieldDef>) -> Module {
    let mut module = Module::new("by_value_cycle");
    module.add_struct(struct_def(NODE, "Node", fields));
    module
}

#[test]
fn positive_pointer_broken_self_reference_validates_and_executes() {
    let node = struct_def(
        NODE,
        "Node",
        vec![
            field("next", Ty::PtrMut(Box::new(Ty::Struct(NODE)))),
            field("v", Ty::U64),
        ],
    );
    let module = node_program(node, 8);
    assert_eq!(validate_module(&module), vec![]);
    let outcome = Interpreter::with_module(&module)
        .execute_func(FuncId::new(0), [])
        .expect("a pointer-broken self reference has a finite layout");
    let returned = outcome.returns[0].as_int().expect("u64 result");
    assert_eq!(returned.as_unsigned(), 42);
}

#[test]
fn negative_twin_by_value_self_reference_is_refused_by_name() {
    // One mutation: `next` holds the Node itself, not a pointer to it.
    let node = struct_def(
        NODE,
        "Node",
        vec![field("next", Ty::Struct(NODE)), field("v", Ty::U64)],
    );
    let module = node_program(node, 8);
    let errors = validate_module(&module);
    let cycle = ValidationError::InlineAggregateCycle {
        ty: "struct #0 'Node'".to_string(),
    };
    assert!(errors.contains(&cycle), "{errors:?}");
    assert_eq!(cycles(&module).len(), 1, "one SCC, one report: {errors:?}");
    assert_eq!(
        cycle.to_string(),
        "type struct #0 'Node' contains itself by value (no finite layout); \
         break the cycle with a pointer, reference or Rc"
    );
}

#[test]
fn mutation_cycle_through_tuple_and_type_row_is_caught() {
    // Row 0 is `(u8, [row0; 1])`: no struct at all, only a tuple (inline, no
    // identity) and an `Array(TyId)` that resolves back to its own row.
    let mut module = Module::new("tuple_row_cycle");
    module
        .types
        .push(Ty::Tuple(vec![Ty::U8, Ty::Array(TyId::new(0), 1)]));
    assert_eq!(
        cycles(&module),
        vec!["type #0 ((u8, [ty.0 x 1]))".to_string()]
    );

    // And a struct field that is a tuple holding the struct.
    let module = node_only(vec![field(
        "pair",
        Ty::Tuple(vec![Ty::U64, Ty::Struct(NODE)]),
    )]);
    assert_eq!(cycles(&module), vec!["struct #0 'Node'".to_string()]);
}

#[test]
fn mutation_cycle_through_enum_variant_is_caught() {
    let mut module = Module::new("enum_cycle");
    module.add_enum(EnumDef {
        id: EnumId::new(0),
        name: "E".to_string(),
        variants: vec![
            EnumVariant {
                name: "A".to_string(),
                fields: vec![Ty::U8],
                field_names: vec![],
            },
            EnumVariant {
                name: "B".to_string(),
                fields: vec![Ty::Enum(EnumId::new(0))],
                field_names: vec![],
            },
        ],
        discriminants: vec![],
        repr: None,
        layout: None,
        origin: None,
    });
    assert_eq!(cycles(&module), vec!["enum #0 'E'".to_string()]);
}

#[test]
fn mutation_cycle_through_refine_is_caught() {
    // `struct N { f: Refine(row0, p) }` with row 0 = `N`: a refinement is
    // representation-preserving, so its base is held by value.
    let mut module = node_only(vec![field("f", Ty::Refine(TyId::new(0), PredId::new(0)))]);
    module.types.push(Ty::Struct(NODE));
    module.predicates.push(Pred::NonZero);
    let found = cycles(&module);
    assert_eq!(found.len(), 1, "{found:?}");
    assert!(
        found[0].starts_with("struct #0 'Node' (cycle through type #0"),
        "{found:?}"
    );
}

#[test]
fn mutation_declared_size_struct_cycle_is_caught() {
    // A DECLARED layout does not exempt the struct: the declared path sizes
    // its fields too.
    let mut node = struct_def(NODE, "Node", vec![field("next", Ty::Struct(NODE))]);
    node.size = Some(8);
    node.align = Some(8);
    node.fields[0].offset = Some(0);
    let mut module = Module::new("declared_cycle");
    module.add_struct(node);
    assert_eq!(cycles(&module), vec!["struct #0 'Node'".to_string()]);
}

#[test]
fn mutation_two_struct_cycle_is_reported_once() {
    let mut module = Module::new("mutual");
    module.add_struct(struct_def(
        StructId::new(0),
        "A",
        vec![field("b", Ty::Struct(StructId::new(1)))],
    ));
    module.add_struct(struct_def(
        StructId::new(1),
        "B",
        vec![field("a", Ty::Struct(StructId::new(0)))],
    ));
    assert_eq!(
        cycles(&module),
        vec!["struct #0 'A' (cycle through struct #1 'B')".to_string()]
    );
}

#[test]
fn mutation_indirections_break_the_cycle() {
    for (label, next) in [
        ("Rc<Node>", Ty::Rc(Box::new(Ty::Struct(NODE)))),
        ("&Node", Ty::Ref(Box::new(Ty::Struct(NODE)))),
        ("*const Node", Ty::PtrConst(Box::new(Ty::Struct(NODE)))),
    ] {
        let module = node_only(vec![field("next", next), field("v", Ty::U64)]);
        assert_eq!(cycles(&module), Vec::<String>::new(), "{label}");
        assert_eq!(validate_module(&module), vec![], "{label}");
    }
    // Out-of-line storage through a type row: `Sequence(row0)`, row 0 = Node.
    let mut module = node_only(vec![field("items", Ty::Sequence(TyId::new(0)))]);
    module.types.push(Ty::Struct(NODE));
    assert_eq!(cycles(&module), Vec::<String>::new());
    // And an acyclic by-value chain is not a cycle.
    let mut module = node_only(vec![field("leaf", Ty::Struct(StructId::new(1)))]);
    module.add_struct(struct_def(
        StructId::new(1),
        "Leaf",
        vec![field("x", Ty::U8)],
    ));
    assert_eq!(cycles(&module), Vec::<String>::new());
}

// ── Review adversaries (WS2.4 review) ─────────────────────────────────────
//
// Shapes the implementer's fixtures did not write. Each runs the WHOLE
// validator on a deliberately small thread stack: the new rule is iterative,
// but every OTHER validator pass also sees the cyclic tables first, and a
// pass that recursed through by-value containment without a guard would
// abort the process before `InlineAggregateCycle` could be reported.

use trust_ir::ty::{ClosureTy, EnumLayoutDescriptor, EnumTagEncoding, FatPtrKind, RecordDef};
use trust_ir::value::RecordId;

const REVIEW_SMALL_STACK: usize = 512 * 1024;

fn validate_on_small_stack(module: Module) -> Vec<ValidationError> {
    std::thread::Builder::new()
        .name("ws2_4_review_small_stack".to_string())
        .stack_size(REVIEW_SMALL_STACK)
        .spawn(move || validate_module(&module))
        .expect("spawn the small-stack thread")
        .join()
        .expect("the validator terminated without overflowing its stack")
}

fn cycle_reports(errors: &[ValidationError]) -> Vec<String> {
    errors
        .iter()
        .filter_map(|error| match error {
            ValidationError::InlineAggregateCycle { ty } => Some(ty.clone()),
            _ => None,
        })
        .collect()
}

fn pinned(module: &mut Module) {
    module.target_info = Some(trust_ir::TargetInfo {
        triple: "x86_64-unknown-linux-gnu".into(),
        pointer_size: 8,
        endianness: trust_ir::Endianness::Little,
        abi: Some("sysv64".into()),
        struct_passing: trust_ir::StructPassingPolicy::NativeC,
    });
}

#[test]
fn review_self_refinement_and_self_array_rows_are_caught_without_overflow() {
    // Row 0 refines ITSELF: no struct, no tuple — the only edge is Refine's
    // base, and every refinement-walking pass sees it first.
    let mut module = Module::new("self_refine");
    module.types.push(Ty::Refine(TyId::new(0), PredId::new(0)));
    module.predicates.push(Pred::NonZero);
    let errors = validate_on_small_stack(module);
    assert_eq!(cycle_reports(&errors).len(), 1, "{errors:?}");

    // Row 0 is an array of ITSELF.
    let mut module = Module::new("self_array");
    module.types.push(Ty::Array(TyId::new(0), 1));
    let errors = validate_on_small_stack(module);
    assert_eq!(cycle_reports(&errors).len(), 1, "{errors:?}");
}

#[test]
fn review_record_and_closure_capture_cycles_are_caught() {
    let mut module = Module::new("record_cycle");
    module.add_record(RecordDef {
        id: RecordId::new(0),
        name: "R".to_string(),
        fields: vec![field("me", Ty::Record(RecordId::new(0)))],
    });
    let errors = validate_on_small_stack(module);
    assert_eq!(
        cycle_reports(&errors),
        vec!["record #0 'R'".to_string()],
        "{errors:?}"
    );

    let mut module = Module::new("closure_cycle");
    let sig = module
        .add_func_type(trust_ir::ty::FuncTy {
            params: vec![],
            returns: vec![],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    module
        .add_closure_type(ClosureTy {
            func: sig,
            captures: vec![Ty::Closure(trust_ir::value::ClosureTyId::new(0))],
        })
        .expect("Module::add_closure_type: test fixture");
    let errors = validate_on_small_stack(module);
    assert_eq!(
        cycle_reports(&errors),
        vec!["closure type #0".to_string()],
        "{errors:?}"
    );
}

#[test]
fn review_layout_bearing_cycles_in_a_pinned_module_are_caught_without_overflow() {
    // A pinned module runs the layout validators (struct and enum descriptor
    // checks, global / alloca sizing) over the same cyclic tables.
    let enum_e = EnumId::new(0);
    let mut module = Module::new("pinned_cycles");
    pinned(&mut module);
    let mut node = struct_def(NODE, "Node", vec![field("next", Ty::Struct(NODE))]);
    node.size = Some(8);
    node.align = Some(8);
    node.fields[0].offset = Some(0);
    module.add_struct(node);
    module.add_enum(EnumDef {
        id: enum_e,
        name: "E".to_string(),
        variants: vec![
            EnumVariant {
                name: "A".to_string(),
                fields: vec![],
                field_names: vec![],
            },
            EnumVariant {
                name: "B".to_string(),
                fields: vec![Ty::Enum(enum_e)],
                field_names: vec![],
            },
        ],
        discriminants: vec![],
        repr: None,
        layout: Some(EnumLayoutDescriptor {
            encoding: EnumTagEncoding::Direct { tag_offset: 0 },
            size: 16,
            align: 8,
            variant_field_offsets: vec![vec![], vec![8]],
        }),
        origin: None,
    });
    for (name, ty) in [("node", Ty::Struct(NODE)), ("e", Ty::Enum(enum_e))] {
        module.globals.push(trust_ir::Global {
            name: name.into(),
            ty,
            mutable: true,
            initializer: None,
            linkage: trust_ir::Linkage::Internal,
            tls: None,
            align: None,
            section: None,
            visibility: trust_ir::Visibility::Default,
            retained: false,
        });
    }
    let errors = validate_on_small_stack(module);
    let found = cycle_reports(&errors);
    assert!(
        found.contains(&"struct #0 'Node'".to_string()),
        "{errors:?}"
    );
    assert!(found.contains(&"enum #0 'E'".to_string()), "{errors:?}");
    assert_eq!(found.len(), 2, "{errors:?}");
}

#[test]
fn review_legitimate_recursive_shapes_are_not_flagged() {
    // Diamond sharing (A holds B twice, B holds C twice) is a DAG, not a cycle.
    let mut module = Module::new("diamond");
    module.add_struct(struct_def(
        StructId::new(0),
        "A",
        vec![
            field("l", Ty::Struct(StructId::new(1))),
            field("r", Ty::Struct(StructId::new(1))),
        ],
    ));
    module.add_struct(struct_def(
        StructId::new(1),
        "B",
        vec![
            field("l", Ty::Struct(StructId::new(2))),
            field("r", Ty::Struct(StructId::new(2))),
        ],
    ));
    module.add_struct(struct_def(StructId::new(2), "C", vec![field("x", Ty::U8)]));
    assert_eq!(validate_on_small_stack(module), vec![]);

    // `enum List { Nil, Cons(u64, *mut List) }`, a slice of Node inside Node,
    // and a function-pointer field typed over Node: all indirections.
    let list = EnumId::new(0);
    let mut module = node_only(vec![
        field("items", Ty::FatPtr(FatPtrKind::Slice(TyId::new(0)))),
        field("list", Ty::Enum(list)),
    ]);
    module.types.push(Ty::Struct(NODE));
    module.add_enum(EnumDef {
        id: list,
        name: "List".to_string(),
        variants: vec![
            EnumVariant {
                name: "Nil".to_string(),
                fields: vec![],
                field_names: vec![],
            },
            EnumVariant {
                name: "Cons".to_string(),
                fields: vec![Ty::U64, Ty::PtrMut(Box::new(Ty::Enum(list)))],
                field_names: vec![],
            },
        ],
        discriminants: vec![],
        repr: None,
        layout: None,
        origin: None,
    });
    let errors = validate_on_small_stack(module);
    assert_eq!(cycle_reports(&errors), Vec::<String>::new(), "{errors:?}");
}
